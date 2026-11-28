import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_45560
open PEqualNP.CircuitLowerBounds
abbrev Row := Fin 256
abbrev Wire := Row → Bool
def bin (d a b : Nat) : Nat :=
  match d with
  | 0 => a &&& b
  | 1 => a ||| b
  | 2 => a ^^^ (a &&& b)
  | _ => b ^^^ (a &&& b)
def flipOp (d : Nat) : Nat :=
  match d with
  | 2 => 3
  | 3 => 2
  | _ => d
lemma bin_comm_flip (d : Nat) (hd : d < 4) (a b : Nat) : bin d a b = bin (flipOp d) b a := by
  interval_cases d <;> simp [bin, flipOp, Nat.and_comm, Nat.or_comm]
lemma flipOp_lt {d : Nat} (hd : d < 4) : flipOp d < 4 := by
  interval_cases d <;> decide
lemma testBit_bin (d a b r : Nat) :
    (bin d a b).testBit r =
      match d with
      | 0 => a.testBit r && b.testBit r
      | 1 => a.testBit r || b.testBit r
      | 2 => a.testBit r && !b.testBit r
      | _ => !a.testBit r && b.testBit r := by
  rcases d with _ | _ | _ | d <;>
    simp [bin, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor] <;>
    cases a.testBit r <;> cases b.testBit r <;> rfl
lemma bin_lt (d a b : Nat) (ha : a < 2^256) (hb : b < 2^256) : bin d a b < 2^256 := by
  have h1 : ∀ x y : Nat, x < 2^256 → y < 2^256 → (x &&& y) < 2^256 := fun x y hx _ =>
    Nat.lt_of_le_of_lt Nat.and_le_left hx
  have h2 : ∀ x y : Nat, x < 2^256 → y < 2^256 → (x ||| y) < 2^256 := fun x y hx hy =>
    Nat.or_lt_two_pow hx hy
  have h3 : ∀ x y : Nat, x < 2^256 → y < 2^256 → (x ^^^ y) < 2^256 := fun x y hx hy =>
    Nat.xor_lt_two_pow hx hy
  rcases d with _ | _ | _ | d
  · exact h1 a b ha hb
  · exact h2 a b ha hb
  · exact h3 a (a &&& b) ha (h1 a b ha hb)
  · exact h3 b (a &&& b) hb (h1 a b ha hb)
lemma bin_bit0 (d a b : Nat) (ha : a.testBit 0 = false) (hb : b.testBit 0 = false) :
    (bin d a b).testBit 0 = false := by
  rw [testBit_bin]
  rcases d with _ | _ | _ | d <;> simp [ha, hb]
def Live (T : Nat) : Nat → Finset Nat → Prop
  | 0, S => S = {T} ∧ T ≠ 0
  | k + 1, S => ∃ (U : Finset Nat) (a b d : Nat),
      d < 4 ∧ S = insert a (insert b U) ∧ a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live T k (insert (bin d a b) U)
lemma live_nonzero {T k S} (h : Live T k S) : ∀ a ∈ S, a ≠ 0 := by
  induction k generalizing S with
  | zero => obtain ⟨rfl, hT⟩ := h; simpa using hT
  | succ k ih =>
    obtain ⟨U, a, b, d, _, rfl, ha, hb, _, _, tail⟩ := h
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ha
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hb
    exact ih tail x (Finset.mem_insert_of_mem hx)
lemma live_size {T k S} (h : Live T k S) : S.card ≤ k + 1 := by
  induction k generalizing S with
  | zero => obtain ⟨rfl, _⟩ := h; simp
  | succ k ih =>
    obtain ⟨U, a, b, d, _, rfl, _, _, _, hf, tail⟩ := h
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    have ht := ih tail
    rw [Finset.card_insert_of_notMem hu] at ht
    have h1 := Finset.card_insert_le a (insert b U)
    have h2 := Finset.card_insert_le b U
    omega
lemma live_sep {T k S} (h : Live T k S) {r s : Nat} (hd : T.testBit r ≠ T.testBit s) :
    ∃ a ∈ S, a.testBit r ≠ a.testBit s := by
  induction k generalizing S with
  | zero => obtain ⟨rfl, _⟩ := h; exact ⟨T, by simp, hd⟩
  | succ k ih =>
    obtain ⟨U, a, b, d, _, rfl, _, _, _, _, tail⟩ := h
    obtain ⟨v, hv, hvd⟩ := ih tail
    rcases Finset.mem_insert.mp hv with rfl | hv
    · by_cases ha : a.testBit r = a.testBit s
      · refine ⟨b, by simp, fun hb => hvd ?_⟩
        rw [testBit_bin, testBit_bin, ha, hb]
      · exact ⟨a, by simp, ha⟩
    · exact ⟨v, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hv), hvd⟩
abbrev SWire := Bool × Nat
def swZero : SWire := (false, 0)
def swFlip (a : SWire) : SWire := (!a.1, a.2)
def opIdx (s t : Bool) : Nat := if s then (if t then 1 else 3) else (if t then 2 else 0)
def swMeet (a b : SWire) : SWire := (a.1 && b.1, bin (opIdx a.1 b.1) a.2 b.2)
def swJoin (a b : SWire) : SWire := swFlip (swMeet (swFlip a) (swFlip b))
def swRead (j : Nat) (a : SWire) : Bool := a.1 != a.2.testBit j
lemma swRead_zero (j : Nat) : swRead j swZero = false := by simp [swRead, swZero]
lemma swRead_flip (j : Nat) (a : SWire) : swRead j (swFlip a) = !(swRead j a) := by
  cases a with | mk s v => cases s <;> cases h : v.testBit j <;> simp [swRead, swFlip, h]
lemma swRead_meet (j : Nat) (a b : SWire) : swRead j (swMeet a b) = (swRead j a && swRead j b) := by
  obtain ⟨s, u⟩ := a; obtain ⟨t, v⟩ := b
  cases s <;> cases t <;> cases hu : u.testBit j <;> cases hv : v.testBit j <;>
    simp [swRead, swMeet, opIdx, testBit_bin, hu, hv]
lemma swRead_join (j : Nat) (a b : SWire) : swRead j (swJoin a b) = (swRead j a || swRead j b) := by
  simp only [swJoin, swRead_flip, swRead_meet]
  cases swRead j a <;> cases swRead j b <;> rfl
def swGate (w : List SWire) (g : Gate) : SWire :=
  let arg := fun i => w.getD i swZero
  match g.op, g.inputs with
  | .not, xs => swFlip (arg (xs.headD w.length))
  | .and, [] => swFlip swZero
  | .or, [] => swZero
  | .and, [i] | .or, [i] => arg i
  | .and, i :: j :: _ => swMeet (arg i) (arg j)
  | .or, i :: j :: _ => swJoin (arg i) (arg j)
  | _, _ => swZero
def swExec (gs : List Gate) (w : List SWire) : List SWire :=
  gs.foldl (fun w g => w ++ [swGate w g]) w
def isBin (g : Gate) : Bool := match g.op with | .not => false | _ => true
def reps (w : List SWire) : List Nat := w.map Prod.snd
def simple (w : List SWire) (z : Nat) : Prop := z = 0 ∨ z ∈ reps w
def priced (w : List SWire) (paid : Bool) (z : Nat) : Prop :=
  simple w z ∨ (paid = true ∧ ∃ d < 4, ∃ a ∈ reps w, ∃ b ∈ reps w, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧ z = bin d a b)
lemma bin_eq_cases (d a b : Nat) (hd : d < 4) (h : a = 0 ∨ b = 0 ∨ a = b) :
    bin d a b = 0 ∨ bin d a b = a ∨ bin d a b = b := by
  rcases h with rfl | rfl | rfl <;> interval_cases d <;> simp [bin]
lemma opIdx_lt (s t : Bool) : opIdx s t < 4 := by cases s <;> cases t <;> decide
lemma get_simple (w : List SWire) (i : Nat) : simple w (w.getD i swZero).2 := by
  simp only [List.getD_eq_getElem?_getD]
  cases eq : w[i]? with
  | none => exact Or.inl rfl
  | some a => exact Or.inr (List.mem_map.mpr ⟨a, List.mem_of_getElem? eq, rfl⟩)
lemma made_priced (w : List SWire) (d : Nat) (a b : SWire) (hd : d < 4)
    (pa : simple w a.2) (pb : simple w b.2) : priced w true (bin d a.2 b.2) := by
  by_cases h : a.2 = 0 ∨ b.2 = 0 ∨ a.2 = b.2
  · rcases bin_eq_cases d a.2 b.2 hd h with e | e | e
    · exact Or.inl (Or.inl e)
    · rw [e]; exact Or.inl pa
    · rw [e]; exact Or.inl pb
  · push Not at h
    exact Or.inr ⟨rfl, d, hd, a.2, pa.resolve_left h.1, b.2, pb.resolve_left h.2.1, h.1, h.2.1, h.2.2, rfl⟩
lemma swGate_priced (w : List SWire) (g : Gate) : priced w (isBin g) (swGate w g).2 := by
  obtain ⟨op, xs⟩ := g
  cases op with
  | and =>
    rcases xs with _ | ⟨i, _ | ⟨j, t⟩⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (get_simple w i)
    · exact made_priced w _ _ _ (opIdx_lt _ _) (get_simple w i) (get_simple w j)
  | or =>
    rcases xs with _ | ⟨i, _ | ⟨j, t⟩⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (get_simple w i)
    · exact made_priced w _ _ _ (opIdx_lt _ _) (get_simple w i) (get_simple w j)
  | not => exact Or.inl (get_simple w _)
  | _ => exact Or.inl (Or.inl rfl)
lemma swGate_lt (w : List SWire) (hw : ∀ u ∈ w, u.2 < 2^256 ∧ u.2.testBit 0 = false) (g : Gate) :
    (swGate w g).2 < 2^256 ∧ (swGate w g).2.testBit 0 = false := by
  have hz : (0 : Nat) < 2^256 ∧ (0 : Nat).testBit 0 = false := ⟨by decide, by decide⟩
  have hg (i : Nat) : (w.getD i swZero).2 < 2^256 ∧ (w.getD i swZero).2.testBit 0 = false := by
    simp only [List.getD_eq_getElem?_getD]
    cases eq : w[i]? with
    | none => exact hz
    | some a => exact hw a (List.mem_of_getElem? eq)
  obtain ⟨op, xs⟩ := g
  cases op with
  | and =>
    rcases xs with _ | ⟨i, _ | ⟨j, t⟩⟩
    · exact hz
    · exact hg i
    · exact ⟨bin_lt _ _ _ (hg i).1 (hg j).1, bin_bit0 _ _ _ (hg i).2 (hg j).2⟩
  | or =>
    rcases xs with _ | ⟨i, _ | ⟨j, t⟩⟩
    · exact hz
    · exact hg i
    · exact ⟨bin_lt _ _ _ (hg i).1 (hg j).1, bin_bit0 _ _ _ (hg i).2 (hg j).2⟩
  | not => exact hg (xs.headD w.length)
  | _ => exact hz
lemma swExec_lt (gs : List Gate) (w : List SWire)
    (hw : ∀ u ∈ w, u.2 < 2^256 ∧ u.2.testBit 0 = false) :
    ∀ u ∈ swExec gs w, u.2 < 2^256 ∧ u.2.testBit 0 = false := by
  induction gs generalizing w with
  | nil => exact hw
  | cons g gs ih =>
    apply ih
    intro u hu
    rcases List.mem_append.mp hu with hu | hu
    · exact hw u hu
    · rw [List.mem_singleton.mp hu]; exact swGate_lt w hw g
lemma swRead_get (j : Nat) (w : List SWire) (i : Nat) :
    (w.map (swRead j)).getD i false = swRead j (w.getD i swZero) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> simp [swRead_zero]
lemma swGate_read (w : List SWire) (g : Gate)
    (legal : (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) (j : Nat) :
    swRead j (swGate w g) = g.op.eval (g.inputs.map fun i => (w.map (swRead j)).getD i false) := by
  simp_rw [swRead_get]
  obtain ⟨op, xs⟩ := g
  obtain ⟨hop, hlen⟩ := legal
  rcases hop with rfl | rfl | rfl <;>
    rcases xs with _ | ⟨i, _ | ⟨k, _ | ⟨h, rest⟩⟩⟩ <;>
    simp_all [swGate, GateOp.eval, swRead_flip, swRead_meet, swRead_join, swRead_zero]
lemma swExec_read (j : Nat) (gs : List Gate) (w : List SWire)
    (legal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) :
    (swExec gs w).map (swRead j) =
      gs.foldl (fun l g => l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)]) (w.map (swRead j)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (swExec gs (w ++ [swGate w g])).map (swRead j) = _
    rw [ih _ (fun v hv => legal v (List.mem_cons_of_mem _ hv))]
    simp [swGate_read w g (legal g List.mem_cons_self) j]
lemma pull_live {T k S w z p} (h : Live T k S) (op : priced w p z)
    (sub : ∀ a ∈ S, a ∈ reps w ++ [z]) :
    ∃ l V, l ≤ k + p.toNat ∧ Live T l V ∧ ∀ a ∈ V, a ∈ reps w := by
  by_cases needed : z ∈ S
  · by_cases avail : z ∈ reps w
    · refine ⟨k, S, by omega, h, fun a ha => ?_⟩
      rcases (by simpa using sub a ha : a ∈ reps w ∨ a = z) with old | rfl
      · exact old
      · exact avail
    · rcases op with easy | ⟨rfl, d, hd, a, ha, b, hb, na, nb, ab, rfl⟩
      · rcases easy with rfl | hm
        · exact (live_nonzero h 0 needed rfl).elim
        · exact (avail hm).elim
      · let U := S.erase (bin d a b)
        have tail : Live T k (insert (bin d a b) U) := by
          simpa [U, Finset.insert_erase needed] using h
        have old (x : Nat) (hx : x ∈ U) : x ∈ reps w := by
          obtain ⟨ne, mem⟩ := Finset.mem_erase.mp hx
          exact (by simpa using sub x mem : x ∈ reps w ∨ x = bin d a b).resolve_right ne
        have fresh : bin d a b ∉ insert a (insert b U) := by
          intro eq
          rcases Finset.mem_insert.mp eq with e | h'
          · exact avail (e.symm ▸ ha)
          rcases Finset.mem_insert.mp h' with e | u
          · exact avail (e.symm ▸ hb)
          · exact avail (old _ u)
        exact ⟨k + 1, insert a (insert b U), by simp,
          ⟨U, a, b, d, hd, rfl, na, nb, ab, fresh, tail⟩, by simpa using And.intro ha (And.intro hb old)⟩
  · exact ⟨k, S, by omega, h, fun a ha => (by simpa [show a ≠ z from fun e => needed (e ▸ ha)] using sub a ha)⟩
lemma extract_live {T} (hT : T ≠ 0) (gs : List Gate) (w : List SWire)
    (found : T ∈ reps (swExec gs w)) :
    ∃ k S, k ≤ gs.countP isBin ∧ Live T k S ∧ ∀ a ∈ S, a ∈ reps w := by
  induction gs generalizing w with
  | nil => exact ⟨0, {T}, by simp, ⟨rfl, hT⟩, by simpa [swExec] using found⟩
  | cons g gs ih =>
    obtain ⟨k, S, lim, h, sub⟩ := ih (w ++ [swGate w g]) found
    have sub' : ∀ a ∈ S, a ∈ reps w ++ [(swGate w g).2] := by simpa [reps] using sub
    obtain ⟨l, V, cost, hl, raw⟩ := pull_live h (swGate_priced w g) sub'
    refine ⟨l, V, ?_, hl, raw⟩
    rw [List.countP_cons]
    cases e : isBin g <;> simp [e] at cost ⊢ <;> omega
def invW (a : Wire) : Wire := fun r => !(a r)
def comb2 (isOr : Bool) (a b : Wire) : Wire :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def comb4 (d : Nat) (a b : Wire) : Wire :=
  match d with
  | 0 => comb2 false a b
  | 1 => comb2 true a b
  | 2 => comb2 false a (invW b)
  | _ => comb2 false (invW a) b
def Constant (a : Wire) : Prop := ∃ b : Bool, a = fun _ => b
noncomputable def wcost (a : Wire) : Nat := by classical exact if Constant a then 1 else 0
noncomputable def wmass (xs : List Wire) : Nat := (xs.map wcost).sum
def Avail (pool : List Wire) (v : Wire) : Prop := v ∈ pool ∨ Constant v ∨ invW v ∈ pool
def Supply (pool xs : List Wire) : Prop := ∀ a ∈ xs, Avail pool a
def Reach (roots : List Wire) : Nat → List Wire → Prop
  | 0, b => b = roots
  | p + 1, c => ∃ (op : Bool) (bank : List Wire) (a b : Wire),
      Reach roots p bank ∧ Avail bank a ∧ Avail bank b ∧ c = comb2 op a b :: bank
def kept {α : Type} (save : Bool) (x : α) (xs : List α) : List α := if save then x :: xs else xs
def Run (goal : Wire) : Nat → List Wire → Prop
  | 0, zs => List.Perm [goal] zs
  | s + 1, zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire) (rest : List Wire),
      op < 4 ∧ (a :: b :: rest).Perm zs ∧ Run goal s (comb4 op a b :: kept ka a (kept kb b rest))
lemma invW_inv (a : Wire) : invW (invW a) = a := by funext r; simp [invW]
lemma invW_const {a : Wire} (h : Constant a) : Constant (invW a) := by
  obtain ⟨v, rfl⟩ := h; exact ⟨!v, rfl⟩
lemma wcost_inv (a : Wire) : wcost (invW a) = wcost a := by
  have h : Constant (invW a) ↔ Constant a := ⟨fun hc => invW_inv a ▸ invW_const hc, invW_const⟩
  by_cases hc : Constant a
  · simp [wcost, hc, h.mpr hc]
  · simp [wcost, hc, mt h.mp hc]
lemma avail_inv {bank : List Wire} {a : Wire} (h : Avail bank a) : Avail bank (invW a) := by
  rcases h with h | h | h
  · exact Or.inr (Or.inr (by rwa [invW_inv]))
  · exact Or.inr (Or.inl (invW_const h))
  · exact Or.inl h
lemma avail_cons {bank : List Wire} {v : Wire} (w : Wire) (h : Avail bank v) : Avail (w :: bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (List.mem_cons_of_mem _))
lemma from_const (op : Bool) {a b : Wire} {bank : List Wire} (h : Constant a ∨ Constant b)
    (ha : Avail bank a) (hb : Avail bank b) : Avail bank (comb2 op a b) := by
  rcases h with ⟨v, rfl⟩ | ⟨v, rfl⟩ <;> cases op <;> cases v
  · exact Or.inr (Or.inl ⟨false, funext fun _ => by simp [comb2]⟩)
  · simpa [comb2] using hb
  · simpa [comb2] using hb
  · exact Or.inr (Or.inl ⟨true, funext fun _ => by simp [comb2]⟩)
  · exact Or.inr (Or.inl ⟨false, funext fun _ => by simp [comb2]⟩)
  · simpa [comb2] using ha
  · simpa [comb2] using ha
  · exact Or.inr (Or.inl ⟨true, funext fun _ => by simp [comb2]⟩)
lemma both_const (op : Bool) {a b : Wire} (ha : Constant a) (hb : Constant b) :
    Constant (comb2 op a b) := by
  obtain ⟨v, rfl⟩ := ha; obtain ⟨w, rfl⟩ := hb; cases op <;> exact ⟨_, rfl⟩
lemma extend_comb (roots : List Wire) {p bank a b} (d : Nat) (hd : d < 4)
    (hp : Reach roots p bank) (ha : Avail bank a) (hb : Avail bank b) :
    ∃ q next, Reach roots q next ∧ Avail next (comb4 d a b) ∧
      (∀ v, Avail bank v → Avail next v) ∧ q + wcost a + wcost b ≤ p + 1 + wcost (comb4 d a b) := by
  have hprep : ∃ op x y, comb4 d a b = comb2 op x y ∧ Avail bank x ∧ Avail bank y ∧
      wcost x = wcost a ∧ wcost y = wcost b := by
    interval_cases d
    · exact ⟨false, a, b, rfl, ha, hb, rfl, rfl⟩
    · exact ⟨true, a, b, rfl, ha, hb, rfl, rfl⟩
    · exact ⟨false, a, invW b, rfl, ha, avail_inv hb, rfl, wcost_inv b⟩
    · exact ⟨false, invW a, b, rfl, avail_inv ha, hb, wcost_inv a, rfl⟩
  obtain ⟨op, x, y, eq, hx, hy, cx, cy⟩ := hprep
  rw [eq, ← cx, ← cy]
  classical
  by_cases c : Constant x ∨ Constant y
  · refine ⟨p, bank, hp, from_const op c hx hy, fun _ h => h, ?_⟩
    by_cases hcx : Constant x <;> by_cases hcy : Constant y
    · simp [wcost, hcx, hcy, both_const op hcx hcy]
    · simp [wcost, hcx, hcy]
    · simp [wcost, hcx, hcy]
    · exact (c.elim hcx hcy).elim
  · have hcx : ¬Constant x := fun h => c (Or.inl h)
    have hcy : ¬Constant y := fun h => c (Or.inr h)
    exact ⟨p + 1, _, ⟨op, bank, x, y, hp, hx, hy, rfl⟩, Or.inl (by simp),
      fun _ h => avail_cons _ h, by simp [wcost, hcx, hcy]⟩
lemma wmass_kept (a : Wire) (xs : List Wire) (k : Bool) : wmass xs ≤ wmass (kept k a xs) := by
  cases k <;> simp [kept, wmass]
lemma contraction {goal : Wire} (nc : ¬Constant goal) {s ws} (h : Run goal s ws)
    (roots : List Wire) {p bank} (hp : Reach roots p bank) (hs : Supply bank ws) :
    ∃ q next, Reach roots q next ∧ Avail next goal ∧ q + wmass ws ≤ p + s := by
  classical
  induction s generalizing ws p bank with
  | zero =>
    have hmem : goal ∈ ws := h.mem_iff.mp (by simp)
    have hlen : wmass ws = wcost goal := by
      have := (h.map wcost).sum_eq
      simpa [wmass] using this.symm
    exact ⟨p, bank, hp, hs goal hmem, by simp [hlen, wcost, nc]⟩
  | succ s ih =>
    obtain ⟨op, ka, kb, a, b, rest, hd, perm, tail⟩ := h
    have hsa : Avail bank a := hs a (perm.mem_iff.mp (by simp))
    have hsb : Avail bank b := hs b (perm.mem_iff.mp (by simp))
    obtain ⟨r, T, hT, hz, inc, le⟩ := extend_comb roots op hd hp hsa hsb
    have ht : Supply T (comb4 op a b :: kept ka a (kept kb b rest)) := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hz
      · apply inc; apply hs; apply perm.mem_iff.mp
        cases ka <;> cases kb <;> simp [kept] at hv ⊢ <;> tauto
    obtain ⟨q, W, hW, hv, hl⟩ := ih tail hT ht
    have hm1 := wmass_kept a (kept kb b rest) ka
    have hm2 := wmass_kept b rest kb
    have hp_eq : wmass ws = wcost a + wcost b + wmass rest := by
      have := (perm.map wcost).sum_eq
      simpa [wmass, Nat.add_assoc] using this.symm
    have hcons : wmass (comb4 op a b :: kept ka a (kept kb b rest)) =
        wcost (comb4 op a b) + wmass (kept ka a (kept kb b rest)) := rfl
    rw [hcons] at hl
    exact ⟨q, W, hW, hv, by omega⟩
def restrictW (f : Row → Row) (a : Wire) : Wire := fun r => a (f r)
lemma restrict_run (f : Row → Row) {goal s ws} (h : Run goal s ws) :
    Run (restrictW f goal) s (ws.map (restrictW f)) := by
  induction s generalizing ws with
  | zero => exact h.map _
  | succ s ih =>
    obtain ⟨op, ka, kb, a, b, rest, hd, perm, tail⟩ := h
    have htail := ih tail
    have hk : ∀ (k : Bool) (x : Wire) (l : List Wire),
        (kept k x l).map (restrictW f) = kept k (restrictW f x) (l.map (restrictW f)) := by
      intro k x l; cases k <;> rfl
    have hc : restrictW f (comb4 op a b) = comb4 op (restrictW f a) (restrictW f b) := by
      funext r; rcases op with _ | _ | _ | op <;> rfl
    simp only [List.map_cons, hk, hc] at htail
    exact ⟨op, ka, kb, restrictW f a, restrictW f b, rest.map (restrictW f), hd,
      by simpa using perm.map (restrictW f), htail⟩
def obs (a : Nat) : Wire := fun r => a.testBit r.val
lemma obs_bin (d a b : Nat) : obs (bin d a b) = comb4 d (obs a) (obs b) := by
  funext r
  simp only [obs, testBit_bin, comb4, comb2, invW]
  rcases d with _ | _ | _ | d <;> rfl
lemma kept_nodup {α : Type} (c : Bool) (x : α) (l : List α) (hl : l.Nodup) (hx : x ∉ l) :
    (kept c x l).Nodup := by
  cases c <;> simp [kept, hl, hx]
lemma live_to_run {T k S} (h : Live T k S) (v : List Nat) (nd : v.Nodup) (eqv : v.toFinset = S) :
    Run (obs T) k (v.map obs) := by
  classical
  induction k generalizing S v with
  | zero =>
    obtain ⟨rfl, _⟩ := h
    have hp : [T].Perm v := List.perm_of_nodup_nodup_toFinset_eq (by simp) nd (by simp [eqv])
    exact hp.map obs
  | succ k ih =>
    obtain ⟨U, a, b, d, hd, rfl, _, _, hab, fresh, tail⟩ := h
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tl := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm : mid.Nodup := kept_nodup kb b rest hr br
    have am : a ∉ mid := by cases hkb : kb <;> simp [mid, kept, hkb, hab, ar]
    have ntl : tl.Nodup := kept_nodup ka a mid bm am
    have htl : tl.toFinset = U := by
      have kf (c : Bool) (x : Nat) (l : List Nat) : (kept c x l).toFinset = if c then insert x l.toFinset else l.toFinset := by
        cases c <;> simp [kept]
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kf, kf, er]
      ext j
      by_cases ha' : a ∈ U <;> by_cases hb' : b ∈ U <;> by_cases ja : j = a <;> by_cases jb : j = b <;>
        simp_all [ka, kb]
    have hf : bin d a b ∉ tl := fun hm =>
      fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (htl ▸ List.mem_toFinset.mpr hm)))
    have prog := ih tail (bin d a b :: tl) (List.nodup_cons.mpr ⟨hf, ntl⟩) (by simp [htl])
    have hk : ∀ (c : Bool) (x : Nat) (l : List Nat), (kept c x l).map obs = kept c (obs x) (l.map obs) := by
      intro c x l; cases c <;> rfl
    change Run (obs T) k ((bin d a b :: kept ka a (kept kb b rest)).map obs) at prog
    rw [List.map_cons, hk, hk, obs_bin] at prog
    have perm : (a :: b :: rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab, ar, br, hr]) nd
      ext j
      by_cases ja : j = a <;> by_cases jb : j = b <;> simp_all
    exact ⟨d, ka, kb, obs a, obs b, rest.map obs, hd, by simpa using perm.map obs, prog⟩
def normPack (f : Wire) : Nat :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => f r != f 0))).cast List.length_ofFn).toNat
lemma normPack_lt (f : Wire) : normPack f < 2^256 :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => f r != f 0))).cast List.length_ofFn).isLt
lemma testBit_normPack (f : Wire) (r : Nat) :
    (normPack f).testBit r = if h : r < 256 then (f ⟨r, h⟩ != f 0) else false := by
  change ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => f r != f 0))).cast List.length_ofFn).getLsbD r = _
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h : r < 256 <;> simp [h]
lemma normPack_eq_of_obs {a : Nat} (ha : a < 2^256) (h0 : a.testBit 0 = false) :
    normPack (obs a) = a := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack]
  by_cases hr : r < 256
  · simp [hr, obs, h0]
  · simp only [hr, dite_false]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega)))).symm
lemma normPack_inv (f : Wire) : normPack (invW f) = normPack f := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack, testBit_normPack]
  by_cases hr : r < 256
  · simp only [hr, dite_true, invW]
    cases f ⟨r, hr⟩ <;> cases f 0 <;> rfl
  · simp [hr]
lemma normPack_const {f : Wire} (h : Constant f) : normPack f = 0 := by
  obtain ⟨b, rfl⟩ := h
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack]
  by_cases hr : r < 256 <;> simp [hr]
lemma normPack_comb2 (op : Bool) (a b : Wire) :
    ∃ d < 4, normPack (comb2 op a b) = bin d (normPack a) (normPack b) := by
  refine ⟨opIdx (if op then !(a 0) else a 0) (if op then !(b 0) else b 0), opIdx_lt _ _, ?_⟩
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack, testBit_bin, testBit_normPack, testBit_normPack]
  by_cases hr : r < 256
  · simp only [hr, dite_true]
    cases op <;> cases ha0 : a 0 <;> cases hb0 : b 0 <;>
      cases har : a ⟨r, hr⟩ <;> cases hbr : b ⟨r, hr⟩ <;>
      simp [comb2, opIdx, ha0, hb0, har, hbr]
  · simp only [hr, dite_false]
    rcases opIdx _ _ with _ | _ | _ | d <;> rfl
lemma avail_normPack {bank : List Wire} {v : Wire} (h : Avail bank v) :
    normPack v = 0 ∨ normPack v ∈ bank.map normPack := by
  rcases h with hm | hc | hi
  · exact Or.inr (List.mem_map_of_mem hm)
  · exact Or.inl (normPack_const hc)
  · exact Or.inr (by rw [← normPack_inv v]; exact List.mem_map_of_mem hi)
set_option maxRecDepth 4000 in
lemma reach_to_live_sub {roots : List Wire} {p bank} (h : Reach roots p bank)
    {T k S} (run : Live T k S) (sub : ∀ a ∈ S, a ∈ bank.map normPack) :
    ∃ l V, l ≤ p + k ∧ Live T l V ∧ ∀ a ∈ V, a ∈ roots.map normPack := by
  induction p generalizing bank k S with
  | zero =>
    rcases h with rfl
    exact ⟨k, S, by omega, run, sub⟩
  | succ p ih =>
    obtain ⟨op, prev, a, b, hr, ha, hb, rfl⟩ := h
    obtain ⟨d, hd, eq⟩ := normPack_comb2 op a b
    let w := prev.map (fun f => (false, normPack f))
    have hreps : reps w = prev.map normPack := by simp [w, reps, List.map_map, Function.comp_def]
    have hp : priced w true (normPack (comb2 op a b)) := by
      rw [eq]
      have ha1 : simple w (normPack a) := (avail_normPack ha).imp id (fun hm => hreps.symm ▸ hm)
      have hb1 : simple w (normPack b) := (avail_normPack hb).imp id (fun hm => hreps.symm ▸ hm)
      exact made_priced w d (false, normPack a) (false, normPack b) hd ha1 hb1
    have hsub' : ∀ x ∈ S, x ∈ reps w ++ [normPack (comb2 op a b)] := by
      intro x hx
      rcases List.mem_cons.mp (sub x hx) with rfl | hm
      · simp
      · simp [hreps, hm]
    obtain ⟨k', S', hk', run', sub'⟩ := pull_live run hp hsub'
    obtain ⟨l, V, hl, run'', sub''⟩ := ih hr run' (by simpa [hreps] using sub')
    simp only [Bool.toNat_true] at hk'
    exact ⟨l, V, by omega, run'', sub''⟩
def Lower (roots : List Nat) (T : Nat) (L : Nat) : Prop :=
  ∀ p bank, Reach (roots.map obs) p bank → Avail bank (obs T) → L ≤ p
def Impossible (T : Nat) (cap : Nat) (S : Finset Nat) : Prop :=
  ∀ k ≤ cap, ¬Live T k S
def Essential (T : Nat) (roots : List Nat) (a : Nat) : Prop :=
  ∃ r s : Row, T.testBit r.val ≠ T.testBit s.val ∧ ∀ v ∈ roots, v ≠ a → v.testBit r.val = v.testBit s.val
lemma raw_required {T k S} (h : Live T k S) (roots : List Nat) (a : Nat)
    (sub : ∀ v ∈ S, v ∈ roots) (he : Essential T roots a) : a ∈ S := by
  obtain ⟨r, s, hd, hiso⟩ := he
  obtain ⟨v, hv, hvd⟩ := live_sep h hd
  by_cases veq : v = a
  · exact veq ▸ hv
  · exact (hvd (hiso v (sub v hv) veq)).elim
lemma lower_of_impossible {roots : List Nat} {T L : Nat}
    (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^256 ∧ a.testBit 0 = false)
    (ess : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible T L roots.toFinset) : Lower roots T (L + 1) := by
  intro p bank hr ha
  have hnormT : normPack (obs T) = T := normPack_eq_of_obs hTlt hTb0
  have hnz : normPack (obs T) ≠ 0 := by rwa [hnormT]
  have hm : T ∈ bank.map normPack := by
    have h1 := (avail_normPack ha).resolve_left hnz
    rwa [hnormT] at h1
  obtain ⟨k, S, hk, run, sub⟩ := reach_to_live_sub hr (T := T) (k := 0) (S := {T}) ⟨rfl, hT0⟩ (by simpa using hm)
  have hmap : (roots.map obs).map normPack = roots := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id roots]
    apply List.map_congr_left
    intro a ha'
    exact normPack_eq_of_obs (hR a ha').1 (hR a ha').2
  rw [hmap] at sub
  have heq : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    exact ⟨fun ha' => raw_required run roots a sub (ess a ha'), sub a⟩
  by_contra! small
  exact noRun k (by omega) (heq.symm ▸ run)
lemma obs_not_const {T : Nat} (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false) :
    ¬Constant (obs T) := by
  intro hc
  have h := normPack_const hc
  rw [normPack_eq_of_obs hTlt hTb0] at h
  exact hT0 h
def Slice (raw : List Nat) (T d : Nat) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Nat),
    (∀ r : Row, d.testBit (f r).val = true) ∧
    (∀ a ∈ raw, Avail (roots.map obs) (restrictW f (obs a))) ∧
    ¬Constant (restrictW f (obs T)) ∧
    ∀ p bank, Reach (roots.map obs) p bank → Avail bank (restrictW f (obs T)) → L ≤ p
def isConstM (d a : Nat) : Bool := (a &&& d == 0) || (a &&& d == d)
def availM (d : Nat) (pm : List Nat) (a : Nat) : Bool :=
  let m := a &&& d
  m == 0 || m == d || pm.contains m || pm.contains (d ^^^ m)
lemma masked_eq_obs {f : Row → Row} {d a b : Nat} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (eq : (a &&& d) = (b &&& d)) : restrictW f (obs a) = restrictW f (obs b) := by
  funext r
  have h := congrArg (fun x => x.testBit (f r).val) eq
  simpa [restrictW, obs, Nat.testBit_and, dom r] using h
lemma masked_zero_obs {f : Row → Row} {d a : Nat} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (eq : (a &&& d) = 0) : restrictW f (obs a) = fun _ => false := by
  funext r
  have h := congrArg (fun x => x.testBit (f r).val) eq
  simpa [restrictW, obs, Nat.testBit_and, dom r] using h
lemma masked_one_obs {f : Row → Row} {d a : Nat} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (eq : (a &&& d) = d) : restrictW f (obs a) = fun _ => true := by
  funext r
  have h := congrArg (fun x => x.testBit (f r).val) eq
  simpa [restrictW, obs, Nat.testBit_and, dom r] using h
lemma masked_comp_obs {f : Row → Row} {d a b : Nat} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (eq : (a &&& d) = (d ^^^ (b &&& d))) : restrictW f (obs a) = invW (restrictW f (obs b)) := by
  funext r
  have h := congrArg (fun x => x.testBit (f r).val) eq
  simp only [Nat.testBit_and, Nat.testBit_xor, dom r, Bool.and_true] at h
  simp only [restrictW, obs, invW, h]
  cases b.testBit (f r).val <;> rfl
def poolSupply (f : Row → Row) (bank : List Wire) (pool : List Nat) : Prop :=
  ∀ a ∈ pool, Avail bank (restrictW f (obs a))
lemma availM_sound {f : Row → Row} {d a : Nat} {bank : List Wire} {pool : List Nat}
    (dom : ∀ r : Row, d.testBit (f r).val = true)
    (hs : poolSupply f bank pool)
    (ok : availM d (pool.map (· &&& d)) a = true) :
    Avail bank (restrictW f (obs a)) := by
  simp only [availM, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq, List.mem_map] at ok
  rcases ok with ((h0 | h1) | ⟨v, hv, he⟩) | ⟨v, hv, he⟩
  · exact Or.inr (Or.inl ⟨false, masked_zero_obs dom h0⟩)
  · exact Or.inr (Or.inl ⟨true, masked_one_obs dom h1⟩)
  · exact (masked_eq_obs dom he.symm) ▸ hs v hv
  · have hinv := avail_inv (hs v hv)
    have hcomp : restrictW f (obs a) = invW (restrictW f (obs v)) := by
      have hx : (a &&& d) = d ^^^ (v &&& d) := by
        have := congrArg (d ^^^ ·) he
        simpa [Nat.xor_assoc, Nat.xor_comm, Nat.xor_self] using this.symm
      exact masked_comp_obs dom hx
    exact hcomp ▸ hinv
abbrev Choice := Nat × Nat × Nat
def choiceVal (c : Choice) : Nat := bin c.1 c.2.1 c.2.2
def choiceOK (d : Nat) (pm : List Nat) (c : Choice) : Bool :=
  decide (c.1 < 4) && availM d pm c.2.1 && availM d pm c.2.2
def makePool (d : Nat) (pool : List Nat) : List Choice → Option (List Nat)
  | [] => some pool
  | c :: cs => if choiceOK d (pool.map (· &&& d)) c then makePool d (choiceVal c :: pool) cs else none
lemma pay_choice {f : Row → Row} {d : Nat} {roots bank q} {pool : List Nat}
    (dom : ∀ r : Row, d.testBit (f r).val = true)
    (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (c : Choice) (valid : choiceOK d (pool.map (· &&& d)) c = true) :
    ∃ next, Reach roots (q + 1) next ∧ poolSupply f next (choiceVal c :: pool) := by
  simp only [choiceOK, Bool.and_eq_true, decide_eq_true_eq] at valid
  have ha := availM_sound dom hs valid.1.2
  have hb := availM_sound dom hs valid.2
  have hprep : ∃ op x y, comb4 c.1 (restrictW f (obs c.2.1)) (restrictW f (obs c.2.2)) = comb2 op x y ∧
      Avail bank x ∧ Avail bank y := by
    have hd := valid.1.1
    interval_cases c.1
    · exact ⟨false, _, _, rfl, ha, hb⟩
    · exact ⟨true, _, _, rfl, ha, hb⟩
    · exact ⟨false, _, _, rfl, ha, avail_inv hb⟩
    · exact ⟨false, _, _, rfl, avail_inv ha, hb⟩
  obtain ⟨op, x, y, eq, hx, hy⟩ := hprep
  refine ⟨comb2 op x y :: bank, ⟨op, bank, x, y, hp, hx, hy, rfl⟩, fun v hv => ?_⟩
  rcases List.mem_cons.mp hv with rfl | hv
  · have hcv : restrictW f (obs (choiceVal c)) = comb2 op x y := by
      rw [← eq]; funext r; simp only [choiceVal, restrictW, obs, testBit_bin, comb4, comb2, invW]
      rcases c.1 with _ | _ | _ | d' <;> rfl
    exact hcv ▸ Or.inl (by simp)
  · exact avail_cons _ (hs v hv)
lemma makePool_sound {d : Nat} {f : Row → Row} (dom : ∀ r : Row, d.testBit (f r).val = true)
    {roots bank q pool} (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (cs : List Choice) {res} (ok : makePool d pool cs = some res) :
    ∃ next, Reach roots (q + cs.length) next ∧ poolSupply f next res := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨bank, hp, hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next, hr, sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out, hr', sh'⟩ := ih hr sh ok
      exact ⟨out, by simpa [Nat.add_assoc, Nat.add_comm 1] using hr', sh'⟩
    next => contradiction
lemma count_constM {d : Nat} {f : Row → Row} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (ws : List Nat) : ws.countP (isConstM d) ≤ wmass ((ws.map obs).map (restrictW f)) := by
  classical
  induction ws with
  | nil => simp [wmass]
  | cons a ws ih =>
    simp only [List.countP_cons, List.map_cons, wmass, List.sum_cons] at ih ⊢
    cases h : isConstM d a
    · simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
      exact ih.trans (Nat.le_add_left _ _)
    · have hc : Constant (restrictW f (obs a)) := by
        simp only [isConstM, Bool.or_eq_true, beq_iff_eq] at h
        rcases h with h0 | h1
        · exact ⟨false, masked_zero_obs dom h0⟩
        · exact ⟨true, masked_one_obs dom h1⟩
      simp only [ite_true, wcost, hc]
      omega
structure BoundPool where
  dom : Nat
  lb : Nat
  paid : Nat
  wires : List Nat
  pm : List Nat
def ValidPool (_raw : List Nat) (T : Nat) (c : BoundPool) : Prop :=
  c.pm = c.wires.map (· &&& c.dom) ∧
  ∃ (f : Row → Row) (roots : List Nat) (bank : List Wire),
    (∀ r : Row, c.dom.testBit (f r).val = true) ∧ ¬Constant (restrictW f (obs T)) ∧
    (∀ q ws, Reach (roots.map obs) q ws → Avail ws (restrictW f (obs T)) → c.lb ≤ q) ∧
    Reach (roots.map obs) c.paid bank ∧ poolSupply f bank c.wires
def materialize (raw : List Nat) (cs : List Choice) (d lb : Nat) : Option BoundPool :=
  (makePool d raw cs).map fun pool => ⟨d, lb, cs.length, pool, pool.map (· &&& d)⟩
lemma materialize_sound {raw T d L cs c} (sl : Slice raw T d L)
    (h : materialize raw cs d L = some c) : ValidPool raw T c := by
  unfold materialize at h
  cases he : makePool d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he, Option.map_some, Option.some.injEq] at h
    subst c
    obtain ⟨f, roots, dom, base, nc, lo⟩ := sl
    obtain ⟨bank, hr, hs⟩ := makePool_sound dom (show Reach (roots.map obs) 0 (roots.map obs) from rfl) base cs he
    exact ⟨rfl, f, roots, bank, dom, nc, lo, by simpa using hr, hs⟩
def scalarPoolCut (c : BoundPool) (k : Nat) (rest : List Nat) (op : Choice) : Bool :=
  let z := choiceVal op
  let extra := !(availM c.dom c.pm z)
  decide (k + c.paid + extra.toNat < c.lb + (z :: rest).countP (isConstM c.dom)) &&
    rest.all (availM c.dom c.pm) && (!extra || choiceOK c.dom c.pm op)
lemma scalarPoolCut_sound {raw T c} (valid : ValidPool raw T c) {k rest op}
    (nd : (choiceVal op :: rest).Nodup) (cut : scalarPoolCut c k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  obtain ⟨hpm, f, roots, bank, dom, nc, lo, hp, hs⟩ := valid
  simp only [scalarPoolCut, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true] at cut
  intro t ht run
  have finish (n : Nat) (out : List Wire) (hr : Reach (roots.map obs) n out)
      (hsup : poolSupply f out (choiceVal op :: rest))
      (hle : n = c.paid + (!(availM c.dom c.pm (choiceVal op))).toNat) : False := by
    have hcov : Supply out (((choiceVal op :: rest).map obs).map (restrictW f)) := by
      intro v hv
      obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
      exact hsup a ha
    obtain ⟨q, next, hq, hav, hbound⟩ :=
      contraction nc (restrict_run f (live_to_run run (choiceVal op :: rest) nd rfl)) (roots.map obs) hr hcov
    have hlo := lo q next hq hav
    have hcm := count_constM dom (choiceVal op :: rest)
    have hineq := cut.1.1
    omega
  cases hav : availM c.dom c.pm (choiceVal op) with
  | true =>
    apply finish c.paid bank hp _ (by simp [hav])
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact availM_sound dom hs (hpm ▸ hav)
    · exact availM_sound dom hs (hpm ▸ cut.1.2 a ha)
  | false =>
    have hok : choiceOK c.dom (c.wires.map (· &&& c.dom)) op = true := by
      have h2 := cut.2
      simp only [hav, Bool.not_false, Bool.not_true, Bool.false_eq_true, false_or] at h2
      exact hpm ▸ h2
    obtain ⟨out, hr, hc⟩ := pay_choice dom hp hs op hok
    apply finish (c.paid + 1) out hr _ (by simp [hav])
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hc (choiceVal op) (by simp)
    · have hpt : poolSupply f out c.wires := fun v hv => hc v (List.mem_cons_of_mem _ hv)
      exact availM_sound dom hpt (hpm ▸ cut.1.2 a ha)
def fixRow (z o : Nat) (r : Row) : Row :=
  ⟨((r.val &&& (255 ^^^ z)) ||| o) % 256, Nat.mod_lt _ (by decide)⟩
def renameW (f : Row → Row) (a : Nat) : Nat :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).toNat
lemma testBit_renameW (f : Row → Row) (a : Nat) (r : Row) :
    (renameW f a).testBit r.val = a.testBit (f r).val := by
  change ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).getLsbD r.val = _
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn, r.isLt, dite_true, Option.getD_some]
lemma renameW_lt (f : Row → Row) (a : Nat) : renameW f a < 2^256 :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).isLt
lemma obs_renameW (f : Row → Row) (a : Nat) : obs (renameW f a) = restrictW f (obs a) := by
  funext r; exact testBit_renameW f a r
lemma renameW_bin (f : Row → Row) (d a b : Nat) :
    renameW f (bin d a b) = bin d (renameW f a) (renameW f b) := by
  apply Nat.eq_of_testBit_eq
  intro r
  by_cases hr : r < 256
  · rw [testBit_renameW f _ ⟨r, hr⟩, testBit_bin, testBit_bin, testBit_renameW f _ ⟨r, hr⟩, testBit_renameW f _ ⟨r, hr⟩]
  · have hlt (x : Nat) : (renameW f x).testBit r = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt f x) (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [hlt, testBit_bin, hlt, hlt]
    rcases d with _ | _ | _ | d <;> rfl
lemma renameW_zero (f : Row → Row) : renameW f 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 256
  · simpa using testBit_renameW f 0 ⟨r, hr⟩
  · rw [Nat.zero_testBit]
    exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt f 0) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 256 ≤ r)))
lemma renameW_inj (f : Row → Row) (onto : Function.Surjective f) {a b : Nat}
    (ha : a < 2^256) (hb : b < 2^256) (eq : renameW f a = renameW f b) : a = b := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 256
  · obtain ⟨q, hq⟩ := onto ⟨r, hr⟩
    have h := congrArg (fun x => x.testBit q.val) eq
    rw [testBit_renameW, testBit_renameW, hq] at h
    exact h
  · have hge : 256 ≤ r := by omega
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide : 0 < 2) hge)),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide : 0 < 2) hge))]
lemma live_renameW {T k S} (h : Live T k S) (hS : ∀ a ∈ S, a < 2^256) (f : Row → Row)
    (onto : Function.Surjective f) : Live (renameW f T) k (S.image (renameW f)) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl, hT⟩ := h
    have hTlt : T < 2^256 := hS T (by simp)
    refine ⟨by simp, fun hz => hT (renameW_inj f onto hTlt (by decide) (hz.trans (renameW_zero f).symm))⟩
  | succ k ih =>
    obtain ⟨U, a, b, d, hd, rfl, ha, hb, hab, fresh, tail⟩ := h
    have halt : a < 2^256 := hS a (by simp)
    have hblt : b < 2^256 := hS b (by simp)
    have hUlt : ∀ x ∈ U, x < 2^256 := fun x hx => hS x (by simp [hx])
    have hzlt : bin d a b < 2^256 := bin_lt d a b halt hblt
    have htail_lt : ∀ x ∈ insert (bin d a b) U, x < 2^256 := by
      intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx; exact hzlt; exact hUlt x hx
    have nr := ih tail htail_lt
    simp only [Finset.image_insert, renameW_bin] at nr ⊢
    refine ⟨U.image (renameW f), renameW f a, renameW f b, d, hd, rfl,
      fun hz => ha (renameW_inj f onto halt (by decide) (hz.trans (renameW_zero f).symm)),
      fun hz => hb (renameW_inj f onto hblt (by decide) (hz.trans (renameW_zero f).symm)),
      fun heq => hab (renameW_inj f onto halt hblt heq), ?_, nr⟩
    intro hm
    rw [← renameW_bin] at hm
    rcases Finset.mem_insert.mp hm with heq | hm
    · exact fresh (by rw [renameW_inj f onto hzlt halt heq]; simp)
    rcases Finset.mem_insert.mp hm with heq | hm
    · exact fresh (by rw [renameW_inj f onto hzlt hblt heq]; simp)
    obtain ⟨x, hx, heq⟩ := Finset.mem_image.mp hm
    exact fresh (by rw [renameW_inj f onto hzlt (hUlt x hx) heq.symm]; simp [hx])
lemma wmass_append (a b : List Wire) : wmass (a ++ b) = wmass a + wmass b := by simp [wmass]
lemma wmass_consts (xs : List Wire) (hc : ∀ x ∈ xs, Constant x) : wmass xs = xs.length := by
  classical
  induction xs with
  | nil => simp [wmass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [wmass, List.map_cons, List.sum_cons, List.length_cons, wcost, ha, ite_true]
    have := ih (fun x hx => hc x (by simp [hx]))
    simp only [wmass] at this
    omega
lemma lower_slice {roots other : List Nat} {T G : Nat}
    (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^256 ∧ a.testBit 0 = false)
    (hG0 : G ≠ 0) (hGlt : G < 2^256) (hGb0 : G.testBit 0 = false)
    (f : Row → Row) (eq : renameW f T = G)
    (covered : ∀ a ∈ roots, Avail (other.map obs) (restrictW f (obs a)))
    (singles : Finset Nat) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (restrictW f (obs a)))
    (L : Nat) (prior : Lower other G L) : Lower roots T (L + singles.card) := by
  classical
  intro p bank hr ha
  have hnormT : normPack (obs T) = T := normPack_eq_of_obs hTlt hTb0
  have hm : T ∈ bank.map normPack := by
    have h1 := (avail_normPack ha).resolve_left (by rwa [hnormT])
    rwa [hnormT] at h1
  obtain ⟨k, S, hk, run, sub⟩ := reach_to_live_sub hr (T := T) (k := 0) (S := {T}) ⟨rfl, hT0⟩ (by simpa using hm)
  have hmap : (roots.map obs).map normPack = roots := by
    rw [List.map_map]; conv_rhs => rw [← List.map_id roots]
    exact List.map_congr_left fun a ha' => normPack_eq_of_obs (hR a ha').1 (hR a ha').2
  rw [hmap] at sub
  have subS : singles ⊆ S := fun a hs => raw_required run roots a sub (necessary a hs)
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front, List.nodup_append]
    refine ⟨Finset.nodup_toList _, Finset.nodup_toList _, fun a ha b hb he => ?_⟩
    subst b; exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset = S := by ext a; simp [front, Finset.union_sdiff_of_subset subS]
  have gc : restrictW f (obs T) = obs G := (obs_renameW f T).symm.trans (congrArg obs eq)
  have hsup : Supply (other.map obs) ((front.map obs).map (restrictW f)) := by
    intro v hv
    obtain ⟨_, hm', rfl⟩ := List.mem_map.mp hv
    obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hm'
    exact covered a (sub a (fe ▸ List.mem_toFinset.mpr ha'))
  obtain ⟨q, next, hq, hav, hbound⟩ :=
    contraction (gc ▸ obs_not_const hG0 hGlt hGb0) (restrict_run f (live_to_run run front nd fe))
      (other.map obs) (show Reach (other.map obs) 0 (other.map obs) from rfl) hsup
  have hlo := prior q next hq (gc ▸ hav)
  have hmass : singles.card ≤ wmass ((front.map obs).map (restrictW f)) := by
    simp only [front, List.map_append, wmass_append]
    let xs := (singles.toList.map obs).map (restrictW f)
    have hc : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_, hm', rfl⟩ := List.mem_map.mp hv
      obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hm'
      exact constant a (Finset.mem_toList.mp ha')
    have hlen := wmass_consts xs hc
    simp only [xs, List.length_map, Finset.length_toList] at hlen
    change singles.card ≤ wmass xs + _
    rw [← hlen]
    exact Nat.le_add_right _ _
  have := hbound
  omega
lemma lower_count {roots : List Nat} {T : Nat}
    (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^256 ∧ a.testBit 0 = false)
    (singles : Finset Nat) (ess : ∀ a ∈ singles, Essential T roots a) :
    Lower roots T (singles.card - 1) := by
  intro p bank hr ha
  have hnormT : normPack (obs T) = T := normPack_eq_of_obs hTlt hTb0
  have hm : T ∈ bank.map normPack := by
    have h1 := (avail_normPack ha).resolve_left (by rwa [hnormT])
    rwa [hnormT] at h1
  obtain ⟨k, S, hk, run, sub⟩ := reach_to_live_sub hr (T := T) (k := 0) (S := {T}) ⟨rfl, hT0⟩ (by simpa using hm)
  have hmap : (roots.map obs).map normPack = roots := by
    rw [List.map_map]; conv_rhs => rw [← List.map_id roots]
    exact List.map_congr_left fun a ha' => normPack_eq_of_obs (hR a ha').1 (hR a ha').2
  rw [hmap] at sub
  have hsub : singles ⊆ S := fun a ha' => raw_required run roots a sub (ess a ha')
  have hle := (Finset.card_le_card hsub).trans (live_size run)
  omega
def VAR (i : Nat) : Nat :=
  match i with
  | 0 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
  | 1 => 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
  | 2 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
  | 3 => 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00
  | 4 => 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
  | 5 => 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000
  | 6 => 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
  | 7 => 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000
  | _ => 0
def ALL256 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def swapRow (i j : Nat) (r : Row) : Row :=
  let bi := r.val.testBit i
  let bj := r.val.testBit j
  if bi == bj then r
  else ⟨(r.val ^^^ (1 <<< i) ^^^ (1 <<< j)) % 256, Nat.mod_lt _ (by decide)⟩
def swapWord (i j : Nat) (w : Nat) : Nat :=
  let a := VAR i
  let b := VAR j
  let m10 := a ^^^ (a &&& b)
  let m01 := b ^^^ (a &&& b)
  let msame := ALL256 ^^^ (m10 ||| m01)
  let d := (1 <<< j) - (1 <<< i)
  (w &&& msame) ||| ((w &&& m10) <<< d) ||| ((w &&& m01) >>> d)
def permRow (swaps : List (Nat × Nat)) (r : Row) : Row :=
  swaps.foldl (fun x p => swapRow p.1 p.2 x) r
def permWord (swaps : List (Nat × Nat)) (w : Nat) : Nat :=
  swaps.foldr (fun p x => swapWord p.1 p.2 x) w
lemma swapRow_invol (i j : Nat) (hi : i < 8) (hj : j < 8) (r : Row) :
    swapRow i j (swapRow i j r) = r := by
  revert r
  interval_cases i <;> interval_cases j <;> decide +kernel
lemma swapWord_testBit (i j : Nat) (hij : i < j) (hj : j < 8) (w : Nat) (hw : w < 2^256) (r : Row) :
    (swapWord i j w).testBit r.val = w.testBit (swapRow i j r).val := by
  have hi : i < 8 := by omega
  have hspec : ∀ r : Row,
      let a := VAR i; let b := VAR j
      let m10 := a ^^^ (a &&& b); let m01 := b ^^^ (a &&& b); let msame := ALL256 ^^^ (m10 ||| m01)
      let d := (1 <<< j) - (1 <<< i)
      (msame.testBit r.val = true → (swapRow i j r).val = r.val ∧ (d ≤ r.val → m10.testBit (r.val - d) = false) ∧ m01.testBit (r.val + d) = false) ∧
      (msame.testBit r.val = false →
        (d ≤ r.val ∧ m10.testBit (r.val - d) = true ∧ (swapRow i j r).val = r.val - d ∧ m01.testBit (r.val + d) = false) ∨
        ((d ≤ r.val → m10.testBit (r.val - d) = false) ∧ m01.testBit (r.val + d) = true ∧ (swapRow i j r).val = r.val + d)) := by
    revert r; interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have hr := hspec r
  simp only [swapWord, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.add_comm]
  cases hms : (ALL256 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j)))).testBit r.val with
  | true =>
    obtain ⟨heq, h10, h01⟩ := hr.1 hms
    rw [heq]
    by_cases hd : (1 <<< j) - (1 <<< i) ≤ r.val
    · simp [hd, h10 hd, h01]
    · simp [hd, h01]
  | false =>
    rcases hr.2 hms with ⟨hd, h10, heq, h01⟩ | ⟨h10, h01, heq⟩
    · simp [hd, h10, heq, h01]
    · by_cases hd : (1 <<< j) - (1 <<< i) ≤ r.val
      · simp [hd, h10 hd, h01, heq]
      · simp [hd, h01, heq]
lemma swapWord_lt (i j : Nat) (hij : i < j) (hj : j < 8) (w : Nat) : swapWord i j w < 2^256 := by
  have hi : i < 8 := by omega
  have h1 : (ALL256 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j)))) < 2^256 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have h2 : ((VAR i ^^^ (VAR i &&& VAR j)) <<< ((1 <<< j) - (1 <<< i))) < 2^256 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have h3 : ((VAR j ^^^ (VAR i &&& VAR j)) >>> ((1 <<< j) - (1 <<< i))) < 2^256 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  unfold swapWord
  have e1 : (w &&& (ALL256 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j))))) < 2^256 :=
    Nat.lt_of_le_of_lt Nat.and_le_right h1
  have e2 : ((w &&& (VAR i ^^^ (VAR i &&& VAR j))) <<< ((1 <<< j) - (1 <<< i))) < 2^256 := by
    have hle : (w &&& (VAR i ^^^ (VAR i &&& VAR j))) ≤ (VAR i ^^^ (VAR i &&& VAR j)) := Nat.and_le_right
    calc ((w &&& (VAR i ^^^ (VAR i &&& VAR j))) <<< ((1 <<< j) - (1 <<< i)))
        = (w &&& (VAR i ^^^ (VAR i &&& VAR j))) * 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.shiftLeft_eq _ _
      _ ≤ (VAR i ^^^ (VAR i &&& VAR j)) * 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.mul_le_mul_right _ hle
      _ = ((VAR i ^^^ (VAR i &&& VAR j)) <<< ((1 <<< j) - (1 <<< i))) := (Nat.shiftLeft_eq _ _).symm
      _ < 2^256 := h2
  have e3 : ((w &&& (VAR j ^^^ (VAR i &&& VAR j))) >>> ((1 <<< j) - (1 <<< i))) < 2^256 := by
    have hle : (w &&& (VAR j ^^^ (VAR i &&& VAR j))) ≤ (VAR j ^^^ (VAR i &&& VAR j)) := Nat.and_le_right
    calc ((w &&& (VAR j ^^^ (VAR i &&& VAR j))) >>> ((1 <<< j) - (1 <<< i)))
        = (w &&& (VAR j ^^^ (VAR i &&& VAR j))) / 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.shiftRight_eq_div_pow _ _
      _ ≤ (VAR j ^^^ (VAR i &&& VAR j)) / 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.div_le_div_right hle
      _ = ((VAR j ^^^ (VAR i &&& VAR j)) >>> ((1 <<< j) - (1 <<< i))) := (Nat.shiftRight_eq_div_pow _ _).symm
      _ < 2^256 := h3
  exact Nat.or_lt_two_pow (Nat.or_lt_two_pow e1 e2) e3
lemma swapWord_eq_renameW (i j : Nat) (hij : i < j) (hj : j < 8) (w : Nat) (hw : w < 2^256) :
    swapWord i j w = renameW (swapRow i j) w := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 256
  · rw [swapWord_testBit i j hij hj w hw ⟨r, hr⟩, ← testBit_renameW (swapRow i j) w ⟨r, hr⟩]
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (swapWord_lt i j hij hj w) (Nat.pow_le_pow_right (by decide) (by omega))),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))]
def swapsValid (swaps : List (Nat × Nat)) : Bool :=
  swaps.all fun p => decide (p.1 < p.2) && decide (p.2 < 8)
lemma permWord_eq_renameW (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true)
    (w : Nat) (hw : w < 2^256) : permWord swaps w = renameW (permRow swaps) w := by
  induction swaps generalizing w with
  | nil =>
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr : r < 256
    · exact (testBit_renameW (permRow []) w ⟨r, hr⟩).symm
    · rw [show permWord [] w = w from rfl,
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))]
  | cons p ps ih =>
    simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hv
    have ihw := ih hv.2 w hw
    have hlt : permWord ps w < 2^256 := ihw ▸ renameW_lt _ w
    change swapWord p.1 p.2 (permWord ps w) = renameW (permRow (p :: ps)) w
    rw [swapWord_eq_renameW p.1 p.2 hv.1.1 hv.1.2 _ hlt, ihw]
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr : r < 256
    · rw [testBit_renameW _ _ ⟨r, hr⟩, testBit_renameW _ _ (swapRow p.1 p.2 ⟨r, hr⟩), testBit_renameW _ _ ⟨r, hr⟩]
      rfl
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide) (by omega)))]
lemma permRow_surj (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true) :
    Function.Surjective (permRow swaps) := by
  induction swaps with
  | nil => intro r; exact ⟨r, rfl⟩
  | cons p ps ih =>
    simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hv
    intro r
    obtain ⟨q, hq⟩ := ih hv.2 r
    refine ⟨swapRow p.1 p.2 q, ?_⟩
    change permRow ps (swapRow p.1 p.2 (swapRow p.1 p.2 q)) = r
    rw [swapRow_invol p.1 p.2 (by omega) hv.1.2, hq]
lemma permRow_rev_cancel (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true) (r : Row) :
    permRow swaps.reverse (permRow swaps r) = r := by
  induction swaps generalizing r with
  | nil => rfl
  | cons p ps ih =>
    simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hv
    have h1 : permRow (p :: ps).reverse (permRow (p :: ps) r) =
        swapRow p.1 p.2 (permRow ps.reverse (permRow ps (swapRow p.1 p.2 r))) := by
      simp [permRow, List.reverse_cons, List.foldl_append]
    rw [h1, ih hv.2, swapRow_invol p.1 p.2 (by omega) hv.1.2]
lemma rotate_impossible {T n : Nat} {ws : List Nat} (hi : Impossible T n ws.toFinset)
    (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true)
    (hT : T < 2^256) (hfix : permWord swaps T = T)
    (hw : ∀ a ∈ ws, a < 2^256) :
    Impossible T n (ws.map (permWord swaps)).toFinset := by
  intro k hk run
  have hr : ∀ a ∈ (ws.map (permWord swaps)).toFinset, a < 2^256 := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    rw [permWord_eq_renameW swaps hv x (hw x hx)]
    exact renameW_lt _ x
  have hvr : swapsValid swaps.reverse = true := by
    simp only [swapsValid, List.all_reverse]; exact hv
  have hinv_row2 : ∀ r : Row, permRow swaps (permRow swaps.reverse r) = r := by
    intro r; simpa using permRow_rev_cancel swaps.reverse hvr r
  have hinv_word : ∀ x : Nat, x < 2^256 → renameW (permRow swaps.reverse) (permWord swaps x) = x := by
    intro x hx
    rw [permWord_eq_renameW swaps hv x hx]
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hrr : r < 256
    · rw [testBit_renameW _ _ ⟨r, hrr⟩, testBit_renameW, hinv_row2]
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))]
  have run' := live_renameW run hr (permRow swaps.reverse) (permRow_surj swaps.reverse hvr)
  have hT' : renameW (permRow swaps.reverse) T = T := by
    conv_lhs => rw [← hfix]
    exact hinv_word T hT
  have hS' : (ws.map (permWord swaps)).toFinset.image (renameW (permRow swaps.reverse)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      rwa [hinv_word x (hw x hx)]
    · intro ha
      exact ⟨permWord swaps a, ⟨a, ha, rfl⟩, hinv_word a (hw a ha)⟩
  rw [hT', hS'] at run'
  exact hi k hk run'
abbrev Decor := Nat × Nat × Nat
def dbin (d : Nat) (x y : Decor) : Decor := (bin d x.1 y.1, bin d x.2.1 y.2.1, bin d x.2.2 y.2.2)
def dsep (x : Decor) : Nat := x.2.1 ^^^ x.2.2
def projBits (rows : List Nat) (w : Nat) : Nat :=
  rows.foldr (fun r acc => (acc <<< 1) ||| (if w.testBit r then 1 else 0)) 0
lemma testBit_projBits (rows : List Nat) (w i : Nat) :
    (projBits rows w).testBit i = match rows[i]? with | none => false | some r => w.testBit r := by
  induction rows generalizing i with
  | nil => simp [projBits]
  | cons r rs ih =>
    simp only [projBits, List.foldr_cons, Nat.testBit_or, Nat.testBit_shiftLeft]
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Nat.not_le.mpr (by decide : 0 < 1)]
      cases w.testBit r <;> rfl
    | succ i =>
      simp only [List.getElem?_cons_succ, Nat.le_add_left, decide_true, Bool.true_and, Nat.add_sub_cancel]
      have h0 : (if w.testBit r then (1 : Nat) else 0).testBit (i + 1) = false := by
        cases w.testBit r
        · simp
        · exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ i + 1)))
      rw [h0, Bool.or_false]
      exact ih i
lemma projBits_bin (rows : List Nat) (d a b : Nat) :
    projBits rows (bin d a b) = bin d (projBits rows a) (projBits rows b) := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [testBit_projBits, testBit_bin, testBit_projBits, testBit_projBits]
  cases rows[i]? with
  | none => rcases d with _ | _ | _ | d <;> rfl
  | some r => exact testBit_bin d a b r
def faithful (pos neg : List Nat) (x : Decor) : Prop :=
  x.2.1 = projBits pos x.1 ∧ x.2.2 = projBits neg x.1
lemma faithful_bin {pos neg x y} (d : Nat) (hx : faithful pos neg x) (hy : faithful pos neg y) :
    faithful pos neg (dbin d x y) :=
  ⟨by rw [dbin, hx.1, hy.1, projBits_bin], by rw [dbin, hx.2, hy.2, projBits_bin]⟩
def goodPairs (T : Nat) (pos neg : List Nat) : Prop :=
  pos.length = neg.length ∧ ∀ i < pos.length,
    T.testBit (pos.getD i 0) = true ∧ T.testBit (neg.getD i 0) = false
def fullMask (n : Nat) : Nat := (1 <<< n) - 1
abbrev Cov := Nat × Nat × Nat
def addCov (z : Nat) (c : Cov) : Cov :=
  (z ||| c.1, (z ^^^ (z &&& c.1)) ||| (c.2.1 ^^^ (c.2.1 &&& z)),
   (z &&& c.2.1) ||| (c.2.2 ^^^ (c.2.2 &&& z)))
def coverage (v : List Decor) : Cov := v.foldr (fun a c => addCov (dsep a) c) (0, 0, 0)
def takeOne (c : Cov) (a : Nat) : Nat := c.1 ^^^ (c.1 &&& (c.2.1 &&& a))
def takeTwo (c : Cov) (a b : Nat) : Nat :=
  c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
lemma cov_one (c : Cov) (a : Nat) : takeOne (addCov a c) a = c.1 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [takeOne, addCov, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor]
  cases a.testBit i <;> cases c.1.testBit i <;> cases c.2.1.testBit i <;> rfl
lemma cov_two (c : Cov) (a b : Nat) : takeTwo (addCov a (addCov b c)) a b = c.1 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [takeTwo, addCov, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
    cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> rfl
lemma addCov_swap (c : Cov) (a b : Nat) : addCov a (addCov b c) = addCov b (addCov a c) := by
  apply Prod.ext
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [addCov, Nat.testBit_or]; cases a.testBit i <;> cases b.testBit i <;> rfl
  · apply Prod.ext <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
      simp only [addCov, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor] <;>
      cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
      cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> rfl
lemma cov_perm {l r : List Decor} (h : l.Perm r) : coverage l = coverage r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (dsep a)) ih
  | swap _ _ _ => exact addCov_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2
def delOne (ws : List Decor) (a : Decor) (k : Bool) : List Decor := if k then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) : List Decor := delOne (delOne ws a ka) b kb
def restCov (c : Cov) (a b : Nat) (ka kb : Bool) : Nat :=
  if ka then (if kb then c.1 else takeOne c b) else if kb then takeOne c a else takeTwo c a b
lemma cov_delOne {ws : List Decor} (a : Decor) (ha : a ∈ ws) (k : Bool) :
    (coverage (delOne ws a k)).1 = if k then (coverage ws).1 else takeOne (coverage ws) (dsep a) := by
  cases k
  · change (coverage (ws.erase a)).1 = _
    rw [cov_perm (List.perm_cons_erase ha)]
    exact (cov_one _ _).symm
  · rfl
lemma cov_delTwo {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) (ka kb : Bool) :
    (coverage (delTwo ws a b ka kb)).1 = restCov (coverage ws) (dsep a) (dsep b) ka kb := by
  cases ka <;> cases kb
  · have hbm : b ∈ ws.erase a := (List.mem_erase_of_ne ne.symm).mpr hb
    have hp : ws.Perm (a :: b :: (ws.erase a).erase b) :=
      (List.perm_cons_erase ha).trans (List.Perm.cons _ (List.perm_cons_erase hbm))
    change (coverage ((ws.erase a).erase b)).1 = takeTwo (coverage ws) _ _
    rw [cov_perm hp]
    exact (cov_two _ _ _).symm
  · exact cov_delOne a ha false
  · exact cov_delOne b hb false
  · rfl
lemma cov_testBit (ws : List Decor) (i : Nat) :
    (coverage ws).1.testBit i = true ↔ ∃ x ∈ ws, (dsep x).testBit i = true := by
  induction ws with
  | nil => simp [coverage]
  | cons a ws ih =>
    change (dsep a ||| (coverage ws).1).testBit i = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, ih]
    simp
lemma cov_required {T k pos neg} {ws : List Decor}
    (gp : goodPairs T pos neg) (hf : ∀ x ∈ ws, faithful pos neg x)
    (h : Live T k (ws.map Prod.fst).toFinset) :
    ((coverage ws).1 &&& fullMask pos.length) = fullMask pos.length := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and]
  have hfm : (fullMask pos.length).testBit i = decide (i < pos.length) := by
    simp [fullMask, Nat.shiftLeft_eq, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < pos.length
  · have ⟨hp, hn⟩ := gp.2 i hi
    have hsep : T.testBit (pos.getD i 0) ≠ T.testBit (neg.getD i 0) := by rw [hp, hn]; decide
    obtain ⟨v, hv, hvd⟩ := live_sep h hsep
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
    have hfx := hf x hx
    have hpi : pos[i]? = some (pos.getD i 0) := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    have hni : neg[i]? = some (neg.getD i 0) := by
      have hi' : i < neg.length := gp.1 ▸ hi
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
    have hbit : (dsep x).testBit i = true := by
      simp only [dsep, Nat.testBit_xor, hfx.1, hfx.2, testBit_projBits, hpi, hni]
      have h12 : x.1.testBit (pos.getD i 0) ≠ x.1.testBit (neg.getD i 0) := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
        exact hvd
      cases h1 : x.1.testBit (pos.getD i 0) <;> cases h2 : x.1.testBit (neg.getD i 0)
      · exact absurd (h1.trans h2.symm) h12
      · rfl
      · rfl
      · exact absurd (h1.trans h2.symm) h12
    have hc := (cov_testBit ws i).mpr ⟨x, hx, hbit⟩
    simp [hfm, hi, hc]
  · simp [hfm, hi]
def insertNat (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b :: bs => if a ≤ b then a :: b :: bs else b :: insertNat a bs
def sortNats : List Nat → List Nat
  | [] => []
  | a :: bs => insertNat a (sortNats bs)
lemma insertNat_perm (a : Nat) (l : List Nat) : (insertNat a l).Perm (a :: l) := by
  induction l with
  | nil => exact .refl _
  | cons b bs ih =>
    by_cases h : a ≤ b
    · simp [insertNat, h]
    · exact by simpa [insertNat, h] using (List.Perm.cons b ih).trans (.swap a b bs)
lemma sortNats_perm (l : List Nat) : (sortNats l).Perm l := by
  induction l with
  | nil => exact .refl _
  | cons a bs ih => exact (insertNat_perm a (sortNats bs)).trans (.cons a ih)
lemma sortNats_toFinset (l : List Nat) : (sortNats l).toFinset = l.toFinset := by
  ext x; simpa only [List.mem_toFinset] using (sortNats_perm l).mem_iff
def childTwo (ws : List Nat) (a b d : Nat) (ka kb : Bool) : List Nat :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))
lemma erase_toFinset {l : List Nat} (nd : l.Nodup) (a : Nat) :
    (l.erase a).toFinset = l.toFinset.erase a := by
  ext x; simp [nd.mem_erase_iff]
lemma enum_step {T cap : Nat} {ws : List Nat} (nd : ws.Nodup) (out : T ∉ ws)
    (stepOK : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d < 4, ∀ ka kb : Bool,
      a ≠ b → bin d a b ≠ 0 → bin d a b ∉ ws → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible T (cap - 1) (childTwo ws a b d ka kb).toFinset) :
    Impossible T cap ws.toFinset := by
  classical
  intro k hk h
  cases k with
  | zero =>
    obtain ⟨hS, _⟩ := h
    exact out (List.mem_toFinset.mp (hS ▸ Finset.mem_singleton_self T))
  | succ k =>
    obtain ⟨U, a, b, d, hd, he, _, _, hab, hf, tail⟩ := h
    have am : a ∈ ws := List.mem_toFinset.mp (he ▸ Finset.mem_insert_self a _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self b _))
    have fresh : bin d a b ∉ ws := fun hm => hf (he ▸ List.mem_toFinset.mpr hm)
    have hnz : bin d a b ≠ 0 := live_nonzero tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest = (ws.erase a).erase b from rfl, erase_toFinset (nd.erase _) b, erase_toFinset nd a]
    have kf (c : Bool) (x : Nat) (l : List Nat) : (kept c x l).toFinset = if c then insert x l.toFinset else l.toFinset := by
      cases c <;> simp [kept]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kf, kf, er, he]; ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j = a <;> by_cases jb : j = b <;> simp_all [ka, kb]
    have rn : rest.Nodup := (nd.erase _).erase _
    have ar : a ∉ rest := fun h => nd.not_mem_erase (List.mem_of_mem_erase h)
    have br : b ∉ rest := (nd.erase a).not_mem_erase
    have nk := kept_nodup kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept, ar, hab]
    have ndc : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr hm))),
        kept_nodup ka a _ nk ax⟩
    have eqc : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b :: kept ka a (kept kb b rest)).toFinset = _; simp [ke]
    have sc := live_size tail
    have hlen : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [← List.toFinset_card_of_nodup ndc, eqc]; omega
    exact stepOK a am b bm d hd ka kb hab hnz fresh hlen k (by omega) (eqc.symm ▸ tail)
lemma delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k; exact List.erase_sublist; exact List.Sublist.refl _
lemma delTwo_sub (ws : List Decor) (a b : Decor) (ka kb : Bool) : (delTwo ws a b ka kb).Sublist ws :=
  (delOne_sub _ _ _).trans (delOne_sub _ _ _)
lemma delTwo_len (ws : List Decor) (a b : Decor) (ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) :
    (delTwo ws a b ka kb).length = ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne ne.symm).mpr hb
  cases ka <;> cases kb <;> simp [delTwo, delOne, List.length_erase_of_mem ha, List.length_erase_of_mem hb, List.length_erase_of_mem hm]
lemma unique_fst {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (eq : a.1 = b.1) : a = b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn, ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · rfl
    · exact (hn (eq ▸ List.mem_map_of_mem hb')).elim
    · exact (hn (eq.symm ▸ List.mem_map_of_mem ha')).elim
    · exact ih ht ha' hb'
lemma delTwo_map_toFinset {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (ne : a.1 ≠ b.1) (d : Nat) (ka kb : Bool) :
    ((dbin d a b).1 :: (delTwo ws a b ka kb).map Prod.fst).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  have wn : ws.Nodup := nd.of_map
  have dn : (delOne ws a ka).Nodup := wn.sublist (delOne_sub ws a ka)
  have m1 (l : List Decor) (hl : l.Nodup) (x y : Decor) (c : Bool) :
      y ∈ delOne l x c ↔ y ∈ l ∧ (y ≠ x ∨ c = true) := by
    cases c <;> simp [delOne, hl.mem_erase_iff, and_comm]
  have km (v : Nat) : v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
      v ∈ ws.map Prod.fst ∧ (v ≠ a.1 ∨ ka = true) ∧ (v ≠ b.1 ∨ kb = true) := by
    simp only [delTwo, List.mem_map, m1 _ wn, m1 _ dn]
    constructor
    · rintro ⟨w, ⟨⟨hw, h1⟩, h2⟩, rfl⟩
      exact ⟨⟨w, hw, rfl⟩, h1.imp (fun h e => h (unique_fst nd hw ha e)) id,
        h2.imp (fun h e => h (unique_fst nd hw hb e)) id⟩
    · rintro ⟨⟨w, hw, rfl⟩, h1, h2⟩
      exact ⟨w, ⟨⟨hw, h1.imp (fun h e => h (congrArg Prod.fst e)) id⟩,
        h2.imp (fun h e => h (congrArg Prod.fst e)) id⟩, rfl⟩
  have av := List.mem_map_of_mem (f := Prod.fst) ha
  have bv := List.mem_map_of_mem (f := Prod.fst) hb
  have hkeep (c : Bool) (x : Nat) (l : List Nat) (v : Nat) : v ∈ kept c x l ↔ (v = x ∧ c = true) ∨ v ∈ l := by
    cases c <;> simp [kept]
  ext v
  simp only [childTwo, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, km, hkeep,
    (nd.erase _).mem_erase_iff, nd.mem_erase_iff, dbin]
  by_cases va : v = a.1 <;> by_cases vb : v = b.1 <;> cases ka <;> cases kb <;> simp_all
lemma childTwo_swap (v : List Nat) (nd : v.Nodup) (a b : Nat) (d : Nat) (hd : d < 4) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  have hkeep (c : Bool) (x : Nat) (l : List Nat) (y : Nat) : y ∈ kept c x l ↔ (y = x ∧ c = true) ∨ y ∈ l := by
    cases c <;> simp [kept]
  ext x
  simp only [childTwo, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, hkeep,
    (nd.erase _).mem_erase_iff, nd.mem_erase_iff, bin_comm_flip d hd a b]
  tauto
def varsOf (m : Nat) : List Nat :=
  (List.range 8).filterMap fun i => if m.testBit i then some (VAR i) else none
def subcube (z o : Nat) : Nat :=
  (List.range 256).foldr (fun r acc =>
    if (r &&& z == 0) && (r &&& o == o) then acc ||| (1 <<< r) else acc) 0
def fixWord (z o w : Nat) : Nat :=
  (List.range 256).foldr (fun r acc =>
    let fr := ((r &&& (255 ^^^ z)) ||| o) % 256
    if w.testBit fr then acc ||| (1 <<< r) else acc) 0
lemma testBit_foldr_bits (p : Nat → Bool) (l : List Nat) (r : Nat) :
    (l.foldr (fun i acc => if p i then acc ||| (1 <<< i) else acc) 0).testBit r =
      (decide (r ∈ l) && p r) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons]
    by_cases hpa : p a = true
    · simp only [hpa, ite_true, Nat.testBit_or, ih, Nat.testBit_shiftLeft]
      by_cases hra : r = a
      · subst hra; simp [hpa]
      · have h1 : (decide (a ≤ r) && (1 : Nat).testBit (r - a)) = false := by
          by_cases hle : a ≤ r
          · have hpos : r - a ≠ 0 := by omega
            simp only [hle, decide_true, Bool.true_and]
            exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ r - a)))
          · simp [hle]
        simp [h1, hra]
    · have hpf : p a = false := Bool.eq_false_iff.mpr hpa
      simp only [hpf, Bool.false_eq_true, ite_false, ih]
      by_cases hra : r = a
      · subst hra; simp [hpf]
      · simp [hra]
lemma fixWord_eq_renameW (z o w : Nat) : fixWord z o w = renameW (fixRow z o) w := by
  apply Nat.eq_of_testBit_eq; intro r
  unfold fixWord
  rw [testBit_foldr_bits]
  by_cases hr : r < 256
  · rw [testBit_renameW (fixRow z o) w ⟨r, hr⟩]
    simp [hr, fixRow]
  · simp only [List.mem_range, hr, decide_false, Bool.false_and]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))).symm
lemma subcube_fixRow (z o : Nat) (hz : z < 256) (ho : o < 256) (hzo : (z &&& o) = 0) (r : Row) :
    (subcube z o).testBit (fixRow z o r).val = true := by
  unfold subcube
  rw [testBit_foldr_bits]
  have hmem : (fixRow z o r).val ∈ List.range 256 := List.mem_range.mpr (fixRow z o r).isLt
  simp only [hmem, decide_true, Bool.true_and, Bool.and_eq_true, beq_iff_eq]
  have h255 : ((r.val &&& (255 ^^^ z)) ||| o) < 256 := by
    have hr := r.isLt
    have hlt1 : (r.val &&& (255 ^^^ z)) < 256 := Nat.lt_of_le_of_lt Nat.and_le_left hr
    exact Nat.or_lt_two_pow (n := 8) hlt1 ho
  have hval : (fixRow z o r).val = ((r.val &&& (255 ^^^ z)) ||| o) := Nat.mod_eq_of_lt h255
  rw [hval]
  constructor
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, Nat.zero_testBit]
    have hzi : (z.testBit i && o.testBit i) = false := by
      have := congrArg (fun x => x.testBit i) hzo; simpa [Nat.testBit_and] using this
    by_cases hi : i < 8
    · have h7 : (255 : Nat).testBit i = true := by interval_cases i <;> decide
      cases hzb : z.testBit i <;> cases hob : o.testBit i <;> simp_all [h7]
    · have hzf : z.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 8 ≤ i)))
      simp [hzf]
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_or]
    cases o.testBit i <;> simp
def checkEss1 (T : Nat) (roots : List Nat) (a r s : Nat) : Bool :=
  decide (r < 256) && decide (s < 256) && (T.testBit r != T.testBit s) &&
    roots.all fun v => v == a || (v.testBit r == v.testBit s)
lemma checkEss1_sound {T roots a r s} (h : checkEss1 T roots a r s = true) : Essential T roots a := by
  simp only [checkEss1, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  exact ⟨⟨r, h.1.1.1⟩, ⟨s, h.1.1.2⟩, h.1.2, fun v hv hne => (h.2 v hv).resolve_left hne⟩
def freeIn (other : List Nat) (w : Nat) : Bool := w == 0 || w == ALL256 || other.contains w
lemma freeIn_sound {other : List Nat} {f : Row → Row} {a : Nat} (ok : freeIn other (renameW f a) = true) :
    Avail (other.map obs) (restrictW f (obs a)) := by
  rw [← obs_renameW]
  simp only [freeIn, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at ok
  rcases ok with (h0 | h1) | hm
  · exact Or.inr (Or.inl ⟨false, by rw [h0]; funext r; simp [obs]⟩)
  · exact Or.inr (Or.inl ⟨true, by rw [h1]; funext r; simp only [obs, ALL256]; have := r.isLt; exact Nat.testBit_two_pow_sub_one 256 r.val |> fun e => by simpa [this] using e⟩)
  · exact Or.inl (List.mem_map_of_mem hm)
def checkProper (w : Nat) : Bool := w != 0 && decide (w < 2^256) && !w.testBit 0
lemma checkProper_sound {w : Nat} (h : checkProper w = true) : w ≠ 0 ∧ w < 2^256 ∧ w.testBit 0 = false := by
  simp only [checkProper, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq, Bool.not_eq_true'] at h
  exact ⟨h.1.1, h.1.2, h.2⟩
def checkRoots (rs : List Nat) : Bool := rs.all fun a => decide (a < 2^256) && !a.testBit 0
lemma checkRoots_sound {rs : List Nat} (h : checkRoots rs = true) :
    ∀ a ∈ rs, a < 2^256 ∧ a.testBit 0 = false := by
  simp only [checkRoots, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  exact h
def carryOK (swaps : List (Nat × Nat)) (roots1 : List Nat) (T1 : Nat) (roots2 : List Nat) (T2 : Nat) : Bool :=
  swapsValid swaps && checkProper T1 && checkRoots roots1 && checkProper T2 &&
    (permWord swaps T1 == T2) && roots1.all (fun a => freeIn roots2 (permWord swaps a))
lemma carry_of {swaps roots1 T1 roots2 T2 L} (ok : carryOK swaps roots1 T1 roots2 T2 = true)
    (hL : Lower roots2 T2 L) : Lower roots1 T1 L := by
  simp only [carryOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨hsv, hT1⟩, hR1⟩, hT2⟩, heq⟩, hcov⟩ := ok
  have ⟨p1a, p1b, p1c⟩ := checkProper_sound hT1
  have ⟨p2a, p2b, p2c⟩ := checkProper_sound hT2
  have hR1' := checkRoots_sound hR1
  have heq' : renameW (permRow swaps) T1 = T2 := (permWord_eq_renameW swaps hsv T1 p1b).symm.trans heq
  have hcov' : ∀ a ∈ roots1, Avail (roots2.map obs) (restrictW (permRow swaps) (obs a)) := fun a ha =>
    freeIn_sound (permWord_eq_renameW swaps hsv a (hR1' a ha).1 ▸ hcov a ha)
  simpa using lower_slice p1a p1b p1c hR1' p2a p2b p2c (permRow swaps) heq' hcov' ∅ (by simp) (by simp) L hL
def countCheck (roots : List Nat) (T L : Nat) (essPairs : List (Nat × Nat × Nat)) : Bool :=
  checkProper T && checkRoots roots &&
    decide (essPairs.map Prod.fst).Nodup &&
    essPairs.all (fun e => checkEss1 T roots e.1 e.2.1 e.2.2) &&
    decide (L ≤ essPairs.length - 1)
lemma count_of {roots T L essPairs} (ok : countCheck roots T L essPairs = true) :
    Lower roots T L := by
  simp only [countCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨hT, hR⟩, hnd⟩, hess⟩, hle⟩ := ok
  have ⟨p1, p2, p3⟩ := checkProper_sound hT
  have hR' := checkRoots_sound hR
  have hl := lower_count p1 p2 p3 hR' (essPairs.map Prod.fst).toFinset (fun a ha => by
    obtain ⟨⟨v, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    exact checkEss1_sound (hess (v, r, s) hm))
  have hcard : (essPairs.map Prod.fst).toFinset.card = essPairs.length := by
    rw [List.toFinset_card_of_nodup hnd, List.length_map]
  rw [hcard] at hl
  exact fun p bank hr hav => hle.trans (hl p bank hr hav)
def goodPairsCheck (T : Nat) (pos neg : List Nat) : Bool :=
  (pos.length == neg.length) &&
    (List.range pos.length).all fun i => T.testBit (pos.getD i 0) && !(T.testBit (neg.getD i 0))
lemma goodPairs_of {T pos neg} (ok : goodPairsCheck T pos neg = true) : goodPairs T pos neg := by
  simp only [goodPairsCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, Bool.not_eq_true'] at ok
  exact ok
def autosCheck (T : Nat) (autos : List (List (Nat × Nat))) : Bool :=
  autos.all fun sw => swapsValid sw && (permWord sw T == T)
lemma autos_of {T autos} (ok : autosCheck T autos = true) :
    ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T := by
  simp only [autosCheck, List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at ok
  exact ok
def baseCheck (pos neg : List Nat) (base : List Decor) : Bool :=
  base.all fun x => (x.2.1 == projBits pos x.1) && (x.2.2 == projBits neg x.1) && decide (x.1 < 2^256)
lemma base_of {pos neg base} (ok : baseCheck pos neg base = true) :
    ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^256 := by
  simp only [baseCheck, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ok
  intro x hx
  have h := ok x hx
  exact ⟨⟨h.1.1, h.1.2⟩, h.2⟩
def forestRootCheck (roots : List Nat) (T : Nat) (essPairs : List (Nat × Nat × Nat)) : Bool :=
  checkProper T && checkRoots roots &&
    roots.all fun a => essPairs.any fun e => (e.1 == a) && checkEss1 T roots e.1 e.2.1 e.2.2
lemma faithful_zero (pos neg : List Nat) : faithful pos neg (0, 0, 0) := by
  constructor
  · apply Nat.eq_of_testBit_eq; intro i; rw [testBit_projBits]; cases pos[i]? <;> simp
  · apply Nat.eq_of_testBit_eq; intro i; rw [testBit_projBits]; cases neg[i]? <;> simp
lemma forall_cons {α : Type} {P : α → Prop} {a : α} {l : List α} (ha : P a) (hl : ∀ x ∈ l, P x) :
    ∀ x ∈ a :: l, P x := by
  intro x hx; rcases List.mem_cons.mp hx with rfl | hx; exact ha; exact hl x hx
abbrev PoolSpec := Nat × List (Nat × Nat × Nat)
abbrev NodeSpec := List Nat × List Nat × List Nat
lemma var_testBit (i : Fin 8) (r : Row) : (VAR i.val).testBit r.val = r.val.testBit i.val := by revert i r; decide +kernel
inductive BT (α : Type) where
  | empty : BT α
  | leaf : α → BT α
  | node : BT α → BT α → BT α
def btGet {α : Type} (d : α) : BT α → Nat → α
  | .empty, _ => d
  | .leaf x, _ => x
  | .node l r, i => if i &&& 1 == 0 then btGet d l (i >>> 1) else btGet d r (i >>> 1)
def btSet {α : Type} : Nat → BT α → Nat → α → BT α
  | 0, _, _, v => .leaf v
  | d + 1, .empty, i, v =>
    if i &&& 1 == 0 then .node (btSet d .empty (i >>> 1) v) .empty
    else .node .empty (btSet d .empty (i >>> 1) v)
  | d + 1, .leaf x, i, v =>
    if i &&& 1 == 0 then .node (btSet d (.leaf x) (i >>> 1) v) .empty
    else .node .empty (btSet d (.leaf x) (i >>> 1) v)
  | d + 1, .node l r, i, v =>
    if i &&& 1 == 0 then .node (btSet d l (i >>> 1) v) r
    else .node l (btSet d r (i >>> 1) v)
def btUpdate {α : Type} (d0 : α) : Nat → BT α → Nat → (α → α) → BT α
  | 0, .leaf x, _, f => .leaf (f x)
  | 0, _, _, f => .leaf (f d0)
  | d + 1, .empty, i, f =>
    if i &&& 1 == 0 then .node (btUpdate d0 d .empty (i >>> 1) f) .empty
    else .node .empty (btUpdate d0 d .empty (i >>> 1) f)
  | d + 1, .leaf x, i, f =>
    if i &&& 1 == 0 then .node (btUpdate d0 d (.leaf x) (i >>> 1) f) .empty
    else .node .empty (btUpdate d0 d (.leaf x) (i >>> 1) f)
  | d + 1, .node l r, i, f =>
    if i &&& 1 == 0 then .node (btUpdate d0 d l (i >>> 1) f) r
    else .node l (btUpdate d0 d r (i >>> 1) f)
inductive btAll {α : Type} (P : α → Prop) : BT α → Prop where
  | empty : btAll P .empty
  | leaf {x : α} : P x → btAll P (.leaf x)
  | node {l r : BT α} : btAll P l → btAll P r → btAll P (.node l r)
lemma btAll_get {α : Type} {P : α → Prop} {d : α} {t : BT α} (ht : btAll P t) (hd : P d) (i : Nat) :
    P (btGet d t i) := by
  induction ht generalizing i with
  | empty => exact hd
  | leaf hx => exact hx
  | node _ _ ihl ihr =>
    unfold btGet
    split
    · exact ihl _
    · exact ihr _
lemma btAll_set {α : Type} {P : α → Prop} {depth : Nat} {t : BT α} {i : Nat} {v : α}
    (ht : btAll P t) (hv : P v) : btAll P (btSet depth t i v) := by
  induction depth generalizing t i with
  | zero => exact .leaf hv
  | succ d ih =>
    cases ht with
    | empty =>
      unfold btSet; split
      · exact .node (ih .empty) .empty
      · exact .node .empty (ih .empty)
    | leaf hx =>
      unfold btSet; split
      · exact .node (ih (.leaf hx)) .empty
      · exact .node .empty (ih (.leaf hx))
    | node hl hr =>
      unfold btSet; split
      · exact .node (ih hl) hr
      · exact .node hl (ih hr)
lemma btAll_update {α : Type} {P : α → Prop} {d0 : α} {depth : Nat} {t : BT α} {i : Nat} {f : α → α}
    (ht : btAll P t) (hd0 : P d0) (hf : ∀ x, P x → P (f x)) : btAll P (btUpdate d0 depth t i f) := by
  induction depth generalizing t i with
  | zero =>
    cases ht with
    | leaf hx => exact .leaf (hf _ hx)
    | empty => exact .leaf (hf d0 hd0)
    | node _ _ => exact .leaf (hf d0 hd0)
  | succ d ih =>
    cases ht with
    | empty =>
      unfold btUpdate; split
      · exact .node (ih .empty) .empty
      · exact .node .empty (ih .empty)
    | leaf hx =>
      unfold btUpdate; split
      · exact .node (ih (.leaf hx)) .empty
      · exact .node .empty (ih (.leaf hx))
    | node hl hr =>
      unfold btUpdate; split
      · exact .node (ih hl) hr
      · exact .node hl (ih hr)
def btOfList {α : Type} (depth : Nat) (l : List α) : BT α :=
  (l.foldl (fun p x => (p.1 + 1, btSet depth p.2 p.1 x)) (0, BT.empty)).2
lemma btAll_ofList {α : Type} {P : α → Prop} {depth : Nat} {l : List α}
    (h : ∀ x ∈ l, P x) : btAll P (btOfList depth l) := by
  unfold btOfList
  have hgo : ∀ (xs : List α) (acc : Nat × BT α),
      (∀ x ∈ xs, P x) → btAll P acc.2 →
      btAll P (xs.foldl (fun p x => (p.1 + 1, btSet depth p.2 p.1 x)) acc).2 := by
    intro xs
    induction xs with
    | nil => intro acc _ hacc; exact hacc
    | cons x xs ih =>
      intro acc hx hacc
      exact ih (acc.1 + 1, btSet depth acc.2 acc.1 x)
        (fun y hy => hx y (List.mem_cons_of_mem _ hy))
        (btAll_set hacc (hx x (List.mem_cons_self ..)))
  exact hgo l (0, BT.empty) h .empty
def fastBitMask (z o i : Nat) : Nat :=
  if z.testBit i then ALL256 ^^^ VAR i else if o.testBit i then VAR i else ALL256
def subcubeFast (z o : Nat) : Nat :=
  fastBitMask z o 0 &&& fastBitMask z o 1 &&& fastBitMask z o 2 &&&
  fastBitMask z o 3 &&& fastBitMask z o 4 &&& fastBitMask z o 5 &&&
  fastBitMask z o 6 &&& fastBitMask z o 7
lemma fastBitMask_testBit (z o i : Nat) (hi : i < 8) (r : Row) :
    (fastBitMask z o i).testBit r.val =
      (if z.testBit i then !(r.val.testBit i) else if o.testBit i then r.val.testBit i else true) := by
  have hall : ALL256.testBit r.val = true := by
    simp only [ALL256]; have hr := r.isLt; simpa [hr] using Nat.testBit_two_pow_sub_one 256 r.val
  have hvar : (VAR i).testBit r.val = r.val.testBit i := var_testBit ⟨i, hi⟩ r
  unfold fastBitMask
  split
  · simp [Nat.testBit_xor, hall, hvar]
  · split
    · exact hvar
    · exact hall
lemma subcubeFast_eq_subcube (z o : Nat) (hz : z < 256) (ho : o < 256) (hzo : (z &&& o) = 0) :
    subcubeFast z o = subcube z o := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 256
  · have hsub : (subcube z o).testBit r = ((r &&& z == 0) && (r &&& o == o)) := by
      unfold subcube; rw [testBit_foldr_bits]; simp [hr]
    rw [hsub]
    unfold subcubeFast
    simp only [Nat.testBit_and,
      fastBitMask_testBit z o 0 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 1 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 2 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 3 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 4 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 5 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 6 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 7 (by decide) ⟨r, hr⟩]
    have hbit (i : Nat) (hi : i < 8) :
        ((r &&& z).testBit i = false ∧ (r &&& o).testBit i = o.testBit i) ↔
          (if z.testBit i then !r.testBit i else if o.testBit i then r.testBit i else true) = true := by
      have hzi : (z.testBit i && o.testBit i) = false := by
        have := congrArg (fun x => x.testBit i) hzo; simpa [Nat.testBit_and] using this
      simp only [Nat.testBit_and]
      cases hz' : z.testBit i <;> cases ho' : o.testBit i <;> cases hr' : r.testBit i <;> simp_all
    have heq_iff : (((r &&& z == 0) && (r &&& o == o)) = true) ↔
        ∀ i < 8, (r &&& z).testBit i = false ∧ (r &&& o).testBit i = o.testBit i := by
      simp only [Bool.and_eq_true, beq_iff_eq]
      constructor
      · rintro ⟨h1, h2⟩ i _; rw [h1, h2, Nat.zero_testBit]; exact ⟨rfl, rfl⟩
      · intro h
        constructor
        · apply Nat.eq_of_testBit_eq; intro i
          rw [Nat.zero_testBit]
          by_cases hi : i < 8
          · exact (h i hi).1
          · have hzf : z.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 8 ≤ i)))
            simp [Nat.testBit_and, hzf]
        · apply Nat.eq_of_testBit_eq; intro i
          by_cases hi : i < 8
          · exact (h i hi).2
          · have hof : o.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ho (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 8 ≤ i)))
            simp [Nat.testBit_and, hof]
    apply Bool.eq_iff_iff.mpr
    rw [heq_iff]
    simp only [Bool.and_eq_true]
    constructor
    · intro h i hi
      have := hbit i hi
      interval_cases i <;> tauto
    · intro h
      refine ⟨⟨⟨⟨⟨⟨⟨(hbit 0 (by decide)).mp (h 0 (by decide)), (hbit 1 (by decide)).mp (h 1 (by decide))⟩,
        (hbit 2 (by decide)).mp (h 2 (by decide))⟩, (hbit 3 (by decide)).mp (h 3 (by decide))⟩,
        (hbit 4 (by decide)).mp (h 4 (by decide))⟩, (hbit 5 (by decide)).mp (h 5 (by decide))⟩,
        (hbit 6 (by decide)).mp (h 6 (by decide))⟩, (hbit 7 (by decide)).mp (h 7 (by decide))⟩
  · have hlt_f (i : Nat) : (fastBitMask z o i).testBit r = false := by
      have hle : 256 ≤ r := by omega
      have ha : ALL256 < 2^256 := by decide
      have hv : VAR i < 2^256 := by
        unfold VAR; rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · change (0 : Nat) < 2^256; decide
      have hlt_m : fastBitMask z o i < 2^256 := by
        unfold fastBitMask; split
        · exact Nat.xor_lt_two_pow ha hv
        · split; exact hv; exact ha
      exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hlt_m (Nat.pow_le_pow_right (by decide : 0 < 2) hle))
    have hsub : (subcube z o).testBit r = false := by
      unfold subcube; rw [testBit_foldr_bits]; simp [hr]
    rw [hsub]
    unfold subcubeFast
    simp only [Nat.testBit_and, hlt_f]
    rfl
def hashWs64 (ws : List Nat) : Nat :=
  (ws.foldl (fun h w => h + (w % 1000003) * 31) 0) &&& 63
def bucketContainsBT (bks : BT (List (List Nat))) (ws : List Nat) : Bool :=
  let s := sortNats ws
  (btGet [] bks (hashWs64 s)).contains s
def closeChildBT (pools : List BoundPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (k : Nat) (rest : List Nat) (op : Choice) : Bool :=
  let ws := choiceVal op :: rest
  pools.any (fun c => scalarPoolCut c k rest op) ||
    autos.any (fun sw => bucketContainsBT prevBks (ws.map (permWord sw)))
lemma closeChildBT_sound {raw T pools autos prevBks k rest op}
    (hT : T < 2^256)
    (hPools : ∀ c ∈ pools, ValidPool raw T c)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : btAll (fun b => ∀ xs ∈ b, Impossible T k xs.toFinset) prevBks)
    (nd : (choiceVal op :: rest).Nodup)
    (hlt : ∀ x ∈ choiceVal op :: rest, x < 2^256)
    (h : closeChildBT pools autos prevBks k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChildBT, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with ⟨c, hc, hcut⟩ | ⟨sw, hsw, hhit⟩
  · exact scalarPoolCut_sound (hPools c hc) nd hcut
  · unfold bucketContainsBT at hhit
    have hmem := List.contains_iff_mem.mp hhit
    have hb : ∀ xs ∈ btGet [] prevBks (hashWs64 (sortNats ((choiceVal op :: rest).map (permWord sw)))),
        Impossible T k xs.toFinset :=
      btAll_get hPrev (fun _ hx => (List.not_mem_nil hx).elim) _
    have himp := hb _ hmem
    rw [sortNats_toFinset] at himp
    have ⟨hsv, hfix⟩ := hAutos sw hsw
    have hvr : swapsValid sw.reverse = true := by simp only [swapsValid, List.all_reverse]; exact hsv
    have hinv_row_gen : ∀ (l : List (Nat × Nat)), swapsValid l = true →
        ∀ r : Row, permRow l.reverse (permRow l r) = r := by
      intro l hl
      induction l with
      | nil => intro r; rfl
      | cons p ps ih =>
        simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hl
        intro r
        have h1 : permRow (p :: ps).reverse (permRow (p :: ps) r) =
            swapRow p.1 p.2 (permRow ps.reverse (permRow ps (swapRow p.1 p.2 r))) := by
          simp [permRow, List.reverse_cons, List.foldl_append]
        rw [h1, ih hl.2, swapRow_invol p.1 p.2 (by omega) hl.1.2]
    have hinv_row2 : ∀ r : Row, permRow sw (permRow sw.reverse r) = r := by
      simpa using hinv_row_gen sw.reverse hvr
    have hinv_w : ∀ x : Nat, x < 2^256 → permWord sw.reverse (permWord sw x) = x := by
      intro x hx
      have h1 := permWord_eq_renameW sw hsv x hx
      have h2 := permWord_eq_renameW sw.reverse hvr (permWord sw x) (h1 ▸ renameW_lt _ x)
      rw [h2, h1]
      apply Nat.eq_of_testBit_eq; intro r
      by_cases hrr : r < 256
      · rw [testBit_renameW _ _ ⟨r, hrr⟩, testBit_renameW, hinv_row2]
      · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))),
            Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))]
    have hfixr : permWord sw.reverse T = T := by
      have := hinv_w T hT; rwa [hfix] at this
    have hmap_lt : ∀ a ∈ (choiceVal op :: rest).map (permWord sw), a < 2^256 := by
      intro a ha
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      rw [permWord_eq_renameW sw hsv x (hlt x hx)]
      exact renameW_lt _ x
    have hrot := rotate_impossible himp sw.reverse hvr hT hfixr hmap_lt
    have hback : (((choiceVal op :: rest).map (permWord sw)).map (permWord sw.reverse)) = (choiceVal op :: rest) := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id (choiceVal op :: rest)]
      exact List.map_congr_left fun x hx => hinv_w x (hlt x hx)
    rwa [hback] at hrot
abbrev FastPool := BoundPool × List Nat × List Nat × Nat
def prepPool (vals : List Nat) (c : BoundPool) : Option FastPool :=
  let miss := vals.filter (fun w => !availM c.dom c.pm w)
  if miss.length > 2 then none
  else
    let consts := vals.filter (isConstM c.dom)
    some (c, miss, consts, consts.length)
def fastPoolCut (fp : FastPool) (k a b z : Nat) (ka kb : Bool) : Bool :=
  let c := fp.1
  let miss := fp.2.1
  let consts := fp.2.2.1
  let totC := fp.2.2.2
  if !miss.all (fun m => (!ka && m == a) || (!kb && m == b)) then false
  else
    let dropA := if !ka && consts.contains a then 1 else 0
    let dropB := if !kb && consts.contains b then 1 else 0
    let base := c.lb + (totC - dropA - dropB)
    if k + c.paid >= base + 1 then false
    else
      let m := z &&& c.dom
      if m == 0 || m == c.dom then true
      else if k + c.paid >= base then false
      else
        let okAB := !miss.contains a && !miss.contains b
        if k + c.paid + 1 < base && okAB then true
        else
          let zIn := c.pm.contains m || c.pm.contains (c.dom ^^^ m)
          if zIn then true
          else decide (k + c.paid + 1 < base) && okAB
lemma countP_erase {α : Type} [BEq α] [LawfulBEq α] (p : α → Bool) {l : List α} {x : α} (hx : x ∈ l) :
    (l.erase x).countP p + (if p x then 1 else 0) = l.countP p := by
  have hp := List.perm_cons_erase hx
  have h1 := List.Perm.countP_eq p hp
  simp only [List.countP_cons] at h1
  omega
lemma countP_delTwo_fst (p : Nat → Bool) {ws : List Decor} {a b : Decor}
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws) (hab : a.1 ≠ b.1) (ka kb : Bool) :
    ((delTwo ws a b ka kb).map Prod.fst).countP p =
      (ws.map Prod.fst).countP p - (if !ka && p a.1 then 1 else 0) - (if !kb && p b.1 then 1 else 0) := by
  have hne : a ≠ b := fun e => hab (congrArg Prod.fst e)
  have hmap_erase : ∀ (l : List Decor) (x : Decor), (l.map Prod.fst).Nodup → x ∈ l →
      (l.erase x).map Prod.fst = (l.map Prod.fst).erase x.1 := by
    intro l x hnd hx
    induction l with
    | nil => simp at hx
    | cons y ys ih =>
      simp only [List.map_cons, List.nodup_cons] at hnd
      by_cases hyx : y = x
      · subst hyx; simp
      · have hne1 : y.1 ≠ x.1 := by
          intro eq; apply hnd.1; rw [eq]
          exact List.mem_map_of_mem ((List.mem_cons.mp hx).resolve_left (Ne.symm hyx))
        have h1 : (y == x) = false := beq_false_of_ne hyx
        have h2 : (y.1 == x.1) = false := beq_false_of_ne hne1
        simp only [List.erase_cons, h1, h2, List.map_cons]
        exact congrArg (y.1 :: ·) (ih hnd.2 ((List.mem_cons.mp hx).resolve_left (Ne.symm hyx)))
  cases ka <;> cases kb
  · have hbm : b ∈ ws.erase a := (List.mem_erase_of_ne hne.symm).mpr hb
    have hnd1 : ((ws.erase a).map Prod.fst).Nodup := ((List.erase_sublist).map Prod.fst).nodup nd
    change (((ws.erase a).erase b).map Prod.fst).countP p = _
    rw [hmap_erase _ b hnd1 hbm, hmap_erase ws a nd ha]
    have ha1 : a.1 ∈ ws.map Prod.fst := List.mem_map_of_mem ha
    have hb1 : b.1 ∈ (ws.map Prod.fst).erase a.1 := (List.mem_erase_of_ne hab.symm).mpr (List.mem_map_of_mem hb)
    have c1 := countP_erase p ha1
    have c2 := countP_erase p hb1
    cases hpa : p a.1 <;> cases hpb : p b.1 <;> simp [hpa, hpb] at c1 c2 ⊢ <;> omega
  · change ((ws.erase a).map Prod.fst).countP p = _
    rw [hmap_erase ws a nd ha]
    have c1 := countP_erase p (List.mem_map_of_mem (f := Prod.fst) ha)
    cases hpa : p a.1 <;> simp [hpa] at c1 ⊢ <;> omega
  · change ((ws.erase b).map Prod.fst).countP p = _
    rw [hmap_erase ws b nd hb]
    have c1 := countP_erase p (List.mem_map_of_mem (f := Prod.fst) hb)
    cases hpb : p b.1 <;> simp [hpb] at c1 ⊢ <;> omega
  · simp [delTwo, delOne]
lemma fastPoolCut_sound {raw T ws a b d ka kb k c fp}
    (hP : ValidPool raw T c) (hprep : prepPool (ws.map Prod.fst) c = some fp)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws) (hab : a.1 ≠ b.1) (hd : d < 4)
    (ndc : (bin d a.1 b.1 :: (delTwo ws a b ka kb).map Prod.fst).Nodup)
    (hcut : fastPoolCut fp k a.1 b.1 (bin d a.1 b.1) ka kb = true) :
    Impossible T k (bin d a.1 b.1 :: (delTwo ws a b ka kb).map Prod.fst).toFinset := by
  unfold prepPool at hprep
  dsimp only at hprep
  split at hprep
  · simp at hprep
  · simp only [Option.some.injEq] at hprep
    subst hprep
    unfold fastPoolCut at hcut
    dsimp only at hcut
    split at hcut
    · simp at hcut
    · next hmiss =>
      simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true, List.mem_filter, Bool.not_eq_true'] at hmiss
      have hsub := (delTwo_sub ws a b ka kb).map Prod.fst
      have h_all_avail : ((delTwo ws a b ka kb).map Prod.fst).all (availM c.dom c.pm) = true := by
        rw [List.all_eq_true]; intro w hw
        by_contra hna
        have hnf : availM c.dom c.pm w = false := Bool.eq_false_iff.mpr hna
        have hmem_ws : w ∈ ws.map Prod.fst := hsub.subset hw
        have hm := hmiss w ⟨hmem_ws, hnf⟩
        simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hm
        have hmem_del : ∀ u ∈ delTwo ws a b ka kb, u.1 = w → (ka = false → u ≠ a) ∧ (kb = false → u ≠ b) := by
          intro u hu _
          constructor
          · intro hka; subst hka
            have hsub1 : (delTwo ws a b false kb).Sublist (ws.erase a) := by
              cases kb <;> simp [delTwo, delOne, List.erase_sublist]
            have hu1 := hsub1.subset hu
            intro heq; subst heq
            exact List.Nodup.not_mem_erase (List.Nodup.of_map Prod.fst nd) hu1
          · intro hkb; subst hkb
            have hnd_ws : ws.Nodup := List.Nodup.of_map Prod.fst nd
            have hnd2 : (delOne ws a ka).Nodup := by cases ka; exact hnd_ws.erase a; exact hnd_ws
            have h2 := List.Nodup.not_mem_erase hnd2 (a := b)
            exact fun heq => h2 (heq ▸ hu)
        obtain ⟨u, hu, huw⟩ := List.mem_map.mp hw
        have ⟨hna', hnb'⟩ := hmem_del u hu huw
        rcases hm with ⟨hka, hwa⟩ | ⟨hkb, hwb⟩
        · exact hna' hka (unique_fst nd ((delTwo_sub ws a b ka kb).subset hu) ha (huw.trans hwa))
        · exact hnb' hkb (unique_fst nd ((delTwo_sub ws a b ka kb).subset hu) hb (huw.trans hwb))
      have hcnt := countP_delTwo_fst (isConstM c.dom) nd ha hb hab ka kb
      have hlen_f : ((ws.map Prod.fst).filter (isConstM c.dom)).length = (ws.map Prod.fst).countP (isConstM c.dom) := by
        rw [List.countP_eq_length_filter]
      have hca : ((ws.map Prod.fst).filter (isConstM c.dom)).contains a.1 = isConstM c.dom a.1 := by
        apply Bool.eq_iff_iff.mpr
        simp only [List.contains_iff_mem, List.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨List.mem_map_of_mem ha, h⟩⟩
      have hcb : ((ws.map Prod.fst).filter (isConstM c.dom)).contains b.1 = isConstM c.dom b.1 := by
        apply Bool.eq_iff_iff.mpr
        simp only [List.contains_iff_mem, List.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨List.mem_map_of_mem hb, h⟩⟩
      have hma : (!((ws.map Prod.fst).filter (fun w => !availM c.dom c.pm w)).contains a.1) = availM c.dom c.pm a.1 := by
        cases h : availM c.dom c.pm a.1 <;> simp [List.contains_iff_mem, List.mem_filter, List.mem_map_of_mem ha, h]
      have hmb : (!((ws.map Prod.fst).filter (fun w => !availM c.dom c.pm w)).contains b.1) = availM c.dom c.pm b.1 := by
        cases h : availM c.dom c.pm b.1 <;> simp [List.contains_iff_mem, List.mem_filter, List.mem_map_of_mem hb, h]
      rw [hlen_f, hca, hcb, hma, hmb] at hcut
      apply scalarPoolCut_sound (op := (d, a.1, b.1)) (rest := (delTwo ws a b ka kb).map Prod.fst) hP ndc
      unfold scalarPoolCut choiceOK
      simp only [choiceVal, h_all_avail, Bool.and_true, List.countP_cons, Bool.and_eq_true, decide_eq_true_eq, hd, true_and]
      rw [hcnt]
      set z := bin d a.1 b.1
      set m := z &&& c.dom
      set restC := (ws.map Prod.fst).countP (isConstM c.dom) - (if !ka && isConstM c.dom a.1 then 1 else 0) - (if !kb && isConstM c.dom b.1 then 1 else 0)
      change (k + c.paid + (!availM c.dom c.pm z).toNat < c.lb + (restC + if isConstM c.dom z then 1 else 0)) ∧
        ((!(!availM c.dom c.pm z)) || (availM c.dom c.pm a.1 && availM c.dom c.pm b.1)) = true
      have hbase_le : ¬(k + c.paid ≥ c.lb + restC + 1) := by
        intro hge; simp only [hge, ↓reduceIte, Bool.false_eq_true] at hcut
      simp only [hbase_le, ↓reduceIte] at hcut
      by_cases hzc : (m == 0 || m == c.dom) = true
      · have hisc : isConstM c.dom z = true := hzc
        have havz : availM c.dom c.pm z = true := by
          unfold availM; dsimp only; rw [show (z &&& c.dom == 0 || z &&& c.dom == c.dom) = true from hzc]; simp
        simp only [hisc, havz, Bool.not_true, Bool.not_false, Bool.toNat_false, Bool.true_or, ite_true, and_true]
        omega
      · have hzc_f : (m == 0 || m == c.dom) = false := Bool.eq_false_iff.mpr hzc
        have hisc : isConstM c.dom z = false := hzc_f
        have hav_eq : availM c.dom c.pm z = (c.pm.contains m || c.pm.contains (c.dom ^^^ m)) := by
          unfold availM; dsimp only
          have hm0 : (m == 0) = false := by cases h1 : (m == 0) <;> simp [h1] at hzc_f ⊢
          have hmd : (m == c.dom) = false := by cases h1 : (m == c.dom) <;> simp [h1] at hzc_f ⊢
          change (m == 0 || m == c.dom || c.pm.contains m || c.pm.contains (c.dom ^^^ m)) = _
          simp [hm0, hmd]
        simp only [hzc_f, Bool.false_eq_true, ↓reduceIte] at hcut
        have hlt_b : ¬(k + c.paid ≥ c.lb + restC) := by
          intro hge; simp only [hge, ↓reduceIte, Bool.false_eq_true] at hcut
        simp only [hlt_b, ↓reduceIte] at hcut
        rw [hav_eq, hisc]
        simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
        by_cases hfast : (k + c.paid + 1 < c.lb + restC ∧ (availM c.dom c.pm a.1 && availM c.dom c.pm b.1) = true)
        · cases hpm : (c.pm.contains m || c.pm.contains (c.dom ^^^ m)) <;>
            simp only [Bool.not_true, Bool.not_false, Bool.toNat_true, Bool.toNat_false, Bool.true_or, Bool.false_or, hfast.2] <;>
            exact ⟨by omega, trivial⟩
        · have hfast_b : (decide (k + c.paid + 1 < c.lb + restC) && (availM c.dom c.pm a.1 && availM c.dom c.pm b.1)) = false := by
            rw [Bool.eq_false_iff]; intro h; simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            exact hfast ⟨h.1, (Bool.and_eq_true _ _).mpr h.2⟩
          simp only [hfast_b, Bool.false_eq_true, ↓reduceIte] at hcut
          cases hpm : (c.pm.contains m || c.pm.contains (c.dom ^^^ m))
          · simp only [hpm, Bool.false_eq_true, ↓reduceIte] at hcut
          · simp only [Bool.not_true, Bool.not_false, Bool.toNat_false, Bool.true_or]
            exact ⟨by omega, trivial⟩
def evalMoveBT (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat)))
    (d : Nat) (a b z : Decor) (ka kb : Bool) : Bool :=
  let len := 1 + (n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len > cap then true else
    let rs := restCov cov (dsep a) (dsep b) ka kb
    if ((rs ||| dsep z) &&& fmask) != fmask then true else
    if fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 z.1 ka kb) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChildBT [] autos prevBks (cap - 1) rest (d, a.1, b.1)
def testPairBT (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (a b : Decor) (d : Nat) : Bool :=
  if n > cap + 1 then true else
  let z := dbin d a b
  if z.1 == 0 || ws.any (fun v => v.1 == z.1) then true else
    let go := evalMoveBT cap n fmask ws cov fpools autos prevBks d a b z
    if n > cap then go false false
    else if n == cap then go false false && go true false && go false true
    else go false false && go true false && go false true && go true true
def testAllBT (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) : List Decor → Bool
  | [] => true
  | a :: bs =>
    bs.all (fun b => [0, 1, 2, 3].all (testPairBT cap n fmask ws cov fpools autos prevBks a b)) &&
      testAllBT cap n fmask ws cov fpools autos prevBks bs
lemma evalMoveBT_sound {raw T pos neg ws fpools autos prevBks cap a b d ka kb}
    (hT : T < 2^256) (gp : goodPairs T pos neg) (hf : ∀ w ∈ ws, faithful pos neg w)
    (nd : (ws.map Prod.fst).Nodup) (hlt : ∀ w ∈ ws, w.1 < 2^256)
    (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) (hcap : 0 < cap) (_hd : d < 4)
    (hPools : ∀ fp ∈ fpools, ValidPool raw T fp.1 ∧ prepPool (ws.map Prod.fst) fp.1 = some fp)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (cap - 1) xs.toFinset) prevBks)
    (hnz : bin d a.1 b.1 ≠ 0) (hfr : bin d a.1 b.1 ∉ ws.map Prod.fst)
    (test : evalMoveBT cap ws.length (fullMask pos.length) ws (coverage ws) fpools autos prevBks d a b (dbin d a b) ka kb = true) :
    Impossible T (cap - 1) ((dbin d a b :: delTwo ws a b ka kb).map Prod.fst).toFinset := by
  let z := dbin d a b
  let rest := delTwo ws a b ka kb
  let child := (z :: rest).map Prod.fst
  have sub : rest.Sublist ws := delTwo_sub ws a b ka kb
  have ndc : child.Nodup := by
    simp only [child, List.map_cons, List.nodup_cons]
    exact ⟨fun hm => hfr ((sub.map Prod.fst).subset hm), (sub.map Prod.fst).nodup nd⟩
  have hltc : ∀ x ∈ child, x < 2^256 := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact bin_lt d a.1 b.1 (hlt a ha) (hlt b hb)
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx; exact hlt w (sub.subset hw)
  have hleq : 1 + (ws.length - (if ka then 0 else 1) - (if kb then 0 else 1)) = child.length := by
    have hdl := delTwo_len ws a b ka kb ha hb ne
    simp only [child, rest, List.length_map, List.length_cons]
    omega
  intro k hk h
  have hsz := live_size h
  change child.toFinset.card ≤ k + 1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have hlen : child.length ≤ cap := by omega
  have hcov := cov_required gp (ws := z :: rest)
    (fun w hw => by rcases List.mem_cons.mp hw with rfl | hw; exact faithful_bin d (hf a ha) (hf b hb); exact hf w (sub.subset hw)) h
  have hcov_eq : (coverage (z :: rest)).1 = restCov (coverage ws) (dsep a) (dsep b) ka kb ||| dsep z := by
    change dsep z ||| (coverage rest).1 = _
    rw [cov_delTwo a b ha hb ne ka kb, Nat.or_comm]
  rw [hcov_eq] at hcov
  have hcov_b : (((restCov (coverage ws) (dsep a) (dsep b) ka kb ||| dsep z) &&& fullMask pos.length) != fullMask pos.length) = false := by
    simp [hcov]
  unfold evalMoveBT at test
  dsimp only at test
  have hnotgt : ¬(child.length > cap) := by omega
  dsimp only [z] at hcov_b
  simp only [hleq, hnotgt, ↓reduceIte, hcov_b, Bool.false_eq_true] at test
  dsimp only [dbin] at test
  have hab1 : a.1 ≠ b.1 := fun eq => ne (unique_fst nd ha hb eq)
  by_cases hfp : fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 (bin d a.1 b.1) ka kb) = true
  · obtain ⟨fp, hmem, hcut⟩ := List.any_eq_true.mp hfp
    have ⟨hv, hpr⟩ := hPools fp hmem
    exact fastPoolCut_sound hv hpr nd ha hb hab1 _hd ndc hcut k hk h
  · have hfp_f : fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 (bin d a.1 b.1) ka kb) = false := Bool.eq_false_iff.mpr hfp
    simp only [hfp_f, Bool.false_eq_true, ↓reduceIte] at test
    exact closeChildBT_sound (raw := raw) (op := (d, a.1, b.1)) (rest := rest.map Prod.fst) hT (fun _ hm => (List.not_mem_nil hm).elim) hAutos hPrev ndc hltc test k hk h
lemma testAllBT_pair {cap n fmask ws cov fpools autos prevBks l}
    (h : testAllBT cap n fmask ws cov fpools autos prevBks l = true)
    {a b : Decor} (ha : a ∈ l) (hb : b ∈ l) (ne : a ≠ b) :
    (∀ d < 4, testPairBT cap n fmask ws cov fpools autos prevBks a b d = true) ∨
    (∀ d < 4, testPairBT cap n fmask ws cov fpools autos prevBks b a d = true) := by
  induction l with
  | nil => simp at ha
  | cons w l ih =>
    simp only [testAllBT, Bool.and_eq_true, List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | ha'
    · have bm := (List.mem_cons.mp hb).resolve_left ne.symm
      exact Or.inl fun d hd => h.1 b bm d (by interval_cases d <;> decide)
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact Or.inr fun d hd => h.1 a ha' d (by interval_cases d <;> decide)
      · exact ih h.2 ha' hb'
lemma nodeBT_sound {raw T pos neg ws fpools autos prevBks cap}
    (hT : T < 2^256) (gp : goodPairs T pos neg)
    (hf : ∀ w ∈ ws, faithful pos neg w) (nd : (ws.map Prod.fst).Nodup)
    (hlt : ∀ w ∈ ws, w.1 < 2^256) (out : T ∉ ws.map Prod.fst)
    (hPools : ∀ fp ∈ fpools, ValidPool raw T fp.1 ∧ prepPool (ws.map Prod.fst) fp.1 = some fp)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (cap - 1) xs.toFinset) prevBks)
    (checks : cap = 0 ∨ testAllBT cap ws.length (fullMask pos.length) ws (coverage ws) fpools autos prevBks ws = true) :
    Impossible T cap (ws.map Prod.fst).toFinset := by
  rcases checks with rfl | hcheck
  · intro k hk h
    have hk0 : k = 0 := by omega
    subst hk0
    obtain ⟨hS, _⟩ := h
    exact out (List.mem_toFinset.mp (hS ▸ Finset.mem_singleton_self T))
  by_cases h0 : cap = 0
  · subst h0
    intro k hk h
    have hk0 : k = 0 := by omega
    subst hk0
    obtain ⟨hS, _⟩ := h
    exact out (List.mem_toFinset.mp (hS ▸ Finset.mem_singleton_self T))
  have hcap : 0 < cap := by omega
  apply enum_step nd out
  intro a ha b hb d hd ka kb ne hnz hfr _
  obtain ⟨a, haW, rfl⟩ := List.mem_map.mp ha
  obtain ⟨b, hbW, rfl⟩ := List.mem_map.mp hb
  have ab : a ≠ b := fun e => ne (congrArg Prod.fst e)
  have one (x y : Decor) (d' : Nat) (hd' : d' < 4) (hx : x ∈ ws) (hy : y ∈ ws) (nxy : x.1 ≠ y.1)
      (k1 k2 : Bool) (hnz' : bin d' x.1 y.1 ≠ 0) (hfr' : bin d' x.1 y.1 ∉ ws.map Prod.fst)
      (ht : testPairBT cap ws.length (fullMask pos.length) ws (coverage ws) fpools autos prevBks x y d' = true) :
      Impossible T (cap - 1) (childTwo (ws.map Prod.fst) x.1 y.1 d' k1 k2).toFinset := by
    rw [← delTwo_map_toFinset nd hx hy nxy d' k1 k2]
    have hem : evalMoveBT cap ws.length (fullMask pos.length) ws (coverage ws) fpools autos prevBks d' x y (dbin d' x y) k1 k2 = true := by
      have hnz_b : (bin d' x.1 y.1 == 0) = false := beq_false_of_ne hnz'
      have hfr_b : (ws.any (fun v => v.1 == bin d' x.1 y.1)) = false := by
        rw [Bool.eq_false_iff]; intro h; obtain ⟨v, hv, heq⟩ := List.any_eq_true.mp h
        exact hfr' ((beq_iff_eq.mp heq) ▸ List.mem_map_of_mem hv)
      by_cases hlen : 1 + (ws.length - (if k1 then 0 else 1) - (if k2 then 0 else 1)) > cap
      · unfold evalMoveBT; simp [hlen]
      · unfold testPairBT at ht
        dsimp only [dbin] at ht
        have hnot1 : ¬(ws.length > cap + 1) := by cases k1 <;> cases k2 <;> simp at hlen <;> omega
        simp only [hnot1, ↓reduceIte, hnz_b, hfr_b, Bool.false_or, Bool.false_eq_true] at ht
        by_cases hgt : ws.length > cap
        · simp only [hgt, ↓reduceIte] at ht
          cases k1 <;> cases k2
          · exact ht
          · simp at hlen; omega
          · simp at hlen; omega
          · simp at hlen; omega
        · simp only [hgt, ↓reduceIte] at ht
          by_cases heq : ws.length = cap
          · simp only [heq, beq_self_eq_true, ↓reduceIte, Bool.and_eq_true] at ht ⊢
            cases k1 <;> cases k2
            · exact ht.1.1
            · exact ht.2
            · exact ht.1.2
            · simp at hlen; omega
          · have hneq : (ws.length == cap) = false := beq_false_of_ne heq
            simp only [hneq, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at ht
            cases k1 <;> cases k2 <;> first | exact ht.1.1.1 | exact ht.1.2 | exact ht.1.1.2 | exact ht.2
    exact evalMoveBT_sound hT gp hf nd hlt hx hy (fun e => nxy (congrArg Prod.fst e)) hcap hd' hPools hAutos hPrev hnz' hfr' hem
  rcases testAllBT_pair hcheck haW hbW ab with hh | hh
  · exact one a b d hd haW hbW ne ka kb hnz hfr (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    have hfl := flipOp_lt hd
    exact one b a (flipOp d) hfl hbW haW ne.symm kb ka
      (bin_comm_flip d hd a.1 b.1 ▸ hnz) (bin_comm_flip d hd a.1 b.1 ▸ hfr) (hh _ hfl)
def buildWiresBT (depth : Nat) (base : List Decor) (steps : List (Nat × Nat × Nat)) : BT Decor :=
  let init := (base.length, btOfList depth base)
  (steps.foldl (fun p s =>
    let a := btGet (0, 0, 0) p.2 s.2.1
    let b := btGet (0, 0, 0) p.2 s.2.2
    (p.1 + 1, btSet depth p.2 p.1 (dbin s.1 a b))) init).2
lemma buildWiresBT_faithful {depth pos neg base steps}
    (hbase : ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^256) :
    btAll (fun x => faithful pos neg x ∧ x.1 < 2^256) (buildWiresBT depth base steps) := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^256 := ⟨faithful_zero pos neg, by decide⟩
  unfold buildWiresBT
  have h0 : btAll (fun x => faithful pos neg x ∧ x.1 < 2^256) (btOfList depth base) := btAll_ofList hbase
  have hgo : ∀ (ss : List (Nat × Nat × Nat)) (acc : Nat × BT Decor),
      btAll (fun x => faithful pos neg x ∧ x.1 < 2^256) acc.2 →
      btAll (fun x => faithful pos neg x ∧ x.1 < 2^256)
        (ss.foldl (fun p s => (p.1 + 1, btSet depth p.2 p.1 (dbin s.1 (btGet (0, 0, 0) p.2 s.2.1) (btGet (0, 0, 0) p.2 s.2.2)))) acc).2 := by
    intro ss
    induction ss with
    | nil => intro acc hacc; exact hacc
    | cons s ss ih =>
      intro acc hacc
      have ha := btAll_get hacc hdef s.2.1
      have hb := btAll_get hacc hdef s.2.2
      exact ih _ (btAll_set hacc ⟨faithful_bin s.1 ha.1 hb.1, bin_lt s.1 _ _ ha.2 hb.2⟩)
  exact hgo steps (base.length, btOfList depth base) h0
def nodupNats : List Nat → Bool
  | [] => true
  | x :: xs => !(xs.contains x) && nodupNats xs
lemma nodupNats_sound : ∀ {l : List Nat}, nodupNats l = true → l.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    simp only [nodupNats, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at h
    exact List.nodup_cons.mpr ⟨h.1, nodupNats_sound h.2⟩
def checkNodeBT (W : BT Decor) (T fmask : Nat)
    (poolTable : BT (Option BoundPool)) (autosTable : BT (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (k : Nat) (ns : NodeSpec) : Bool :=
  let ws := ns.1.map fun idx => btGet (0, 0, 0) W idx
  let vals := ws.map Prod.fst
  let fpools := ns.2.1.filterMap fun pIdx =>
    match btGet none poolTable pIdx with
    | none => none
    | some c => prepPool vals c
  let nodeAutos := ns.2.2.map fun aIdx => btGet [] autosTable aIdx
  nodupNats vals && !(vals.contains T) &&
    (k == 0 || testAllBT k ws.length fmask ws (coverage ws) fpools nodeAutos prevBks ws)
def checkNodesBT (W : BT Decor) (T fmask : Nat)
    (poolTable : BT (Option BoundPool)) (autosTable : BT (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (k : Nat) (nodes : List NodeSpec) : Bool :=
  nodes.all (checkNodeBT W T fmask poolTable autosTable prevBks k)
lemma checkNodeBT_sound {W : BT Decor} {raw pos neg T poolTable autosTable prevBks k ns}
    (hT : T < 2^256) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^256) W)
    (hPoolTable : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) poolTable)
    (hAutos : btAll (fun sw => swapsValid sw = true ∧ permWord sw T = T) autosTable)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (k - 1) xs.toFinset) prevBks)
    (ok : checkNodeBT W T (fullMask pos.length) poolTable autosTable prevBks k ns = true) :
    Impossible T k ((ns.1.map fun idx => (btGet (0, 0, 0) W idx).1).toFinset) := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^256 := ⟨faithful_zero pos neg, by decide⟩
  have hget (idx : Nat) : faithful pos neg (btGet (0, 0, 0) W idx) ∧ (btGet (0, 0, 0) W idx).1 < 2^256 :=
    btAll_get hW hdef idx
  unfold checkNodeBT at ok
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, Bool.or_eq_true, beq_iff_eq] at ok
  let ws := ns.1.map fun idx => btGet (0, 0, 0) W idx
  have hmap : ws.map Prod.fst = ns.1.map fun idx => (btGet (0, 0, 0) W idx).1 := by simp [ws, List.map_map, Function.comp_def]
  rw [← hmap]
  apply nodeBT_sound hT gp
    (fun w hw => by obtain ⟨idx, _, rfl⟩ := List.mem_map.mp hw; exact (hget idx).1)
    (nodupNats_sound ok.1.1)
    (fun w hw => by obtain ⟨idx, _, rfl⟩ := List.mem_map.mp hw; exact (hget idx).2)
    (of_decide_eq_false ok.1.2)
    (fun fp hfp => by
      obtain ⟨pIdx, _, hmat⟩ := List.mem_filterMap.mp hfp
      cases heq : btGet none poolTable pIdx with
      | none => simp [heq] at hmat
      | some c =>
        simp only [heq] at hmat
        have hvc := btAll_get hPoolTable (fun _ h => by simp at h) pIdx c heq
        have hfp_eq : fp.1 = c := by
          unfold prepPool at hmat
          dsimp only at hmat
          split at hmat
          · simp at hmat
          · simp only [Option.some.injEq] at hmat; rw [← hmat]
        rw [hfp_eq]
        exact ⟨hvc, hmat⟩)
    (fun sw hsw => by
      obtain ⟨aIdx, _, rfl⟩ := List.mem_map.mp hsw
      exact btAll_get hAutos ⟨rfl, rfl⟩ aIdx)
    hPrev ok.2
def nodeValsBT (W : BT Decor) (ns : NodeSpec) : List Nat :=
  sortNats (ns.1.map fun idx => (btGet (0, 0, 0) W idx).1)
def buildBucketsBT (W : BT Decor) (nodes : List NodeSpec) : BT (List (List Nat)) :=
  nodes.foldl (fun acc ns =>
    let xs := nodeValsBT W ns
    btUpdate [] 6 acc (hashWs64 xs) (fun b => if b.contains xs then b else xs :: b)) BT.empty
lemma buildBucketsBT_sound {W : BT Decor} {raw pos neg T poolTable autosTable prevBks k}
    {nodes : List NodeSpec}
    (hT : T < 2^256) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^256) W)
    (hPoolTable : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) poolTable)
    (hAutos : btAll (fun sw => swapsValid sw = true ∧ permWord sw T = T) autosTable)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (k - 1) xs.toFinset) prevBks)
    (hNodes : checkNodesBT W T (fullMask pos.length) poolTable autosTable prevBks k nodes = true) :
    btAll (fun bk => ∀ xs ∈ bk, Impossible T k xs.toFinset) (buildBucketsBT W nodes) := by
  have hmem : ∀ ns ∈ nodes, Impossible T k (nodeValsBT W ns).toFinset := fun ns hns => by
    unfold nodeValsBT; rw [sortNats_toFinset]
    exact checkNodeBT_sound hT gp hW hPoolTable hAutos hPrev (List.all_eq_true.mp hNodes ns hns)
  clear hNodes
  unfold buildBucketsBT
  have hinit : btAll (fun bk => ∀ xs ∈ bk, Impossible T k xs.toFinset) (BT.empty : BT (List (List Nat))) := .empty
  generalize (BT.empty : BT (List (List Nat))) = acc at hinit ⊢
  induction nodes generalizing acc with
  | nil => exact hinit
  | cons ns rest ih =>
    apply ih (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
    apply btAll_update hinit (fun _ h => (List.not_mem_nil h).elim)
    intro b hb ys hys
    split at hys
    · exact hb ys hys
    · rcases List.mem_cons.mp hys with rfl | hys'
      · exact hmem ns (List.mem_cons_self ..)
      · exact hb ys hys'
lemma lower_of_forestBT {roots T cap} {topBks : BT (List (List Nat))} {essPairs : List (Nat × Nat × Nat)}
    (ok : forestRootCheck roots T essPairs = true)
    (hTop : btAll (fun bk => ∀ xs ∈ bk, Impossible T cap xs.toFinset) topBks)
    (hRoot : bucketContainsBT topBks roots = true) :
    Lower roots T (cap + 1) := by
  simp only [forestRootCheck, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq] at ok
  obtain ⟨⟨hT, hR⟩, hess⟩ := ok
  have ⟨p1, p2, p3⟩ := checkProper_sound hT
  have hR' := checkRoots_sound hR
  have hEss' : ∀ a ∈ roots, Essential T roots a := fun a ha => by
    obtain ⟨⟨v, r, s⟩, _, rfl, he⟩ := hess a ha
    exact checkEss1_sound he
  have hImp : Impossible T cap (sortNats roots).toFinset := by
    unfold bucketContainsBT at hRoot
    exact btAll_get hTop (fun _ h => (List.not_mem_nil h).elim) _ _ (List.contains_iff_mem.mp hRoot)
  rw [sortNats_toFinset] at hImp
  exact lower_of_impossible p1 p2 p3 hR' hEss' hImp
def buildPoolsSubBT (pdepth : Nat) (W : BT Decor) (raw : List Nat) (slices : BT (Option (Nat × Nat)))
    (pspecs : BT (Option PoolSpec)) (used : List Nat) : BT (Option BoundPool) :=
  used.foldl (fun acc pIdx =>
    match btGet none pspecs pIdx with
    | none => acc
    | some (slIdx, chIdxs) =>
      match btGet none slices slIdx with
      | none => acc
      | some (dom, lb) =>
        let cs := chIdxs.map fun (op, ia, ib) => (op, (btGet (0, 0, 0) W ia).1, (btGet (0, 0, 0) W ib).1)
        btSet pdepth acc pIdx (materialize raw cs dom lb)) BT.empty
lemma buildPoolsSubBT_sound {pdepth} {W : BT Decor} {raw T} {slices : BT (Option (Nat × Nat))}
    {pspecs : BT (Option PoolSpec)} {used : List Nat}
    (hSlices : btAll (fun o => ∀ p, o = some p → Slice raw T p.1 p.2) slices) :
    btAll (fun o => ∀ c, o = some c → ValidPool raw T c) (buildPoolsSubBT pdepth W raw slices pspecs used) := by
  unfold buildPoolsSubBT
  have hinit : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) (BT.empty : BT (Option BoundPool)) := .empty
  generalize (BT.empty : BT (Option BoundPool)) = acc at hinit ⊢
  induction used generalizing acc with
  | nil => exact hinit
  | cons pIdx rest ih =>
    apply ih
    dsimp only
    cases hps : btGet none pspecs pIdx with
    | none => simp only [hps]; exact hinit
    | some spec =>
      cases hsl : btGet none slices spec.1 with
      | none => simp only [hps, hsl]; exact hinit
      | some sl =>
        simp only [hps, hsl]
        apply btAll_set hinit
        intro c hc
        exact materialize_sound (btAll_get (d := none) hSlices (fun _ h => by simp at h) spec.1 sl hsl) hc
lemma checkNodesBT_mem {W : BT Decor} {raw pos neg T poolTable autosTable prevBks k nodes}
    (hT : T < 2^256) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^256) W)
    (hPoolTable : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) poolTable)
    (hAutos : btAll (fun sw => swapsValid sw = true ∧ permWord sw T = T) autosTable)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (k - 1) xs.toFinset) prevBks)
    (hNodes : checkNodesBT W T (fullMask pos.length) poolTable autosTable prevBks k nodes = true) :
    ∀ ns ∈ nodes, Impossible T k (nodeValsBT W ns).toFinset := by
  intro ns hns
  unfold nodeValsBT; rw [sortNats_toFinset]
  exact checkNodeBT_sound hT gp hW hPoolTable hAutos hPrev (List.all_eq_true.mp hNodes ns hns)
lemma forall_append {α : Type} {P : α → Prop} {l1 l2 : List α}
    (h1 : ∀ x ∈ l1, P x) (h2 : ∀ x ∈ l2, P x) : ∀ x ∈ l1 ++ l2, P x := by
  intro x hx; rcases List.mem_append.mp hx with h | h; exact h1 x h; exact h2 x h
lemma buildBucketsBT_of_mem {W : BT Decor} {T k nodes}
    (hmem : ∀ ns ∈ nodes, Impossible T k (nodeValsBT W ns).toFinset) :
    btAll (fun bk => ∀ xs ∈ bk, Impossible T k xs.toFinset) (buildBucketsBT W nodes) := by
  unfold buildBucketsBT
  have hinit : btAll (fun bk => ∀ xs ∈ bk, Impossible T k xs.toFinset) (BT.empty : BT (List (List Nat))) := .empty
  generalize (BT.empty : BT (List (List Nat))) = acc at hinit ⊢
  induction nodes generalizing acc with
  | nil => exact hinit
  | cons ns rest ih =>
    apply ih (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
    apply btAll_update hinit (fun _ h => (List.not_mem_nil h).elim)
    intro b hb ys hys
    split at hys
    · exact hb ys hys
    · rcases List.mem_cons.mp hys with rfl | hys'
      · exact hmem ns (List.mem_cons_self ..)
      · exact hb ys hys'
lemma obs_all256_xor (G : Nat) : obs (ALL256 ^^^ G) = invW (obs G) := by
  funext r
  have hall : ALL256.testBit r.val = true := by
    simp only [ALL256]; have hr := r.isLt; simpa [hr] using Nat.testBit_two_pow_sub_one 256 r.val
  simp only [obs, invW, Nat.testBit_xor, hall, Bool.true_xor]
lemma lower_slice_flip {roots other : List Nat} {T G : Nat}
    (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^256 ∧ a.testBit 0 = false)
    (hG0 : G ≠ 0) (hGlt : G < 2^256) (hGb0 : G.testBit 0 = false)
    (f : Row → Row) (eq : renameW f T = G ∨ renameW f T = ALL256 ^^^ G)
    (covered : ∀ a ∈ roots, Avail (other.map obs) (restrictW f (obs a)))
    (singles : Finset Nat) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (restrictW f (obs a)))
    (L : Nat) (prior : Lower other G L) : Lower roots T (L + singles.card) := by
  rcases eq with heq | heq
  · exact lower_slice hT0 hTlt hTb0 hR hG0 hGlt hGb0 f heq covered singles necessary constant L prior
  · classical
    intro p bank hr ha
    have hnormT : normPack (obs T) = T := normPack_eq_of_obs hTlt hTb0
    have hm : T ∈ bank.map normPack := by
      have h1 := (avail_normPack ha).resolve_left (by rwa [hnormT])
      rwa [hnormT] at h1
    obtain ⟨k, S, hk, run, sub⟩ := reach_to_live_sub hr (T := T) (k := 0) (S := {T}) ⟨rfl, hT0⟩ (by simpa using hm)
    have hmap : (roots.map obs).map normPack = roots := by
      rw [List.map_map]; conv_rhs => rw [← List.map_id roots]
      exact List.map_congr_left fun a ha' => normPack_eq_of_obs (hR a ha').1 (hR a ha').2
    rw [hmap] at sub
    have subS : singles ⊆ S := fun a hs => raw_required run roots a sub (necessary a hs)
    let front := singles.toList ++ (S \ singles).toList
    have nd : front.Nodup := by
      simp only [front, List.nodup_append]
      refine ⟨Finset.nodup_toList _, Finset.nodup_toList _, fun a ha b hb he => ?_⟩
      subst b; exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
    have fe : front.toFinset = S := by ext a; simp [front, Finset.union_sdiff_of_subset subS]
    have gc : restrictW f (obs T) = invW (obs G) :=
      (obs_renameW f T).symm.trans ((congrArg obs heq).trans (obs_all256_xor G))
    have hnc : ¬Constant (invW (obs G)) := fun hc => obs_not_const hG0 hGlt hGb0 (invW_inv (obs G) ▸ invW_const hc)
    have hsup : Supply (other.map obs) ((front.map obs).map (restrictW f)) := by
      intro v hv
      obtain ⟨_, hm', rfl⟩ := List.mem_map.mp hv
      obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hm'
      exact covered a (sub a (fe ▸ List.mem_toFinset.mpr ha'))
    obtain ⟨q, next, hq, hav, hbound⟩ :=
      contraction (gc ▸ hnc) (restrict_run f (live_to_run run front nd fe))
        (other.map obs) (show Reach (other.map obs) 0 (other.map obs) from rfl) hsup
    have havG : Avail next (obs G) := by
      rw [gc] at hav; simpa [invW_inv] using avail_inv hav
    have hlo := prior q next hq havG
    have hmass : singles.card ≤ wmass ((front.map obs).map (restrictW f)) := by
      simp only [front, List.map_append, wmass_append]
      let xs := (singles.toList.map obs).map (restrictW f)
      have hc : ∀ v ∈ xs, Constant v := by
        intro v hv
        obtain ⟨_, hm', rfl⟩ := List.mem_map.mp hv
        obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hm'
        exact constant a (Finset.mem_toList.mp ha')
      have hlen := wmass_consts xs hc
      simp only [xs, List.length_map, Finset.length_toList] at hlen
      change singles.card ≤ wmass xs + _
      rw [← hlen]
      exact Nat.le_add_right _ _
    omega
def liftCheckF (z o : Nat) (roots : List Nat) (T : Nat) (other : List Nat) (G : Nat)
    (essPairs : List (Nat × Nat × Nat)) : Bool :=
  checkProper T && checkRoots roots && checkProper G &&
    decide (essPairs.map Prod.fst).Nodup &&
    (fixWord z o T == G || fixWord z o T == ALL256 ^^^ G) &&
    roots.all (fun a => freeIn other (fixWord z o a)) &&
    essPairs.all (fun e => checkEss1 T roots e.1 e.2.1 e.2.2 &&
      (fixWord z o e.1 == 0 || fixWord z o e.1 == ALL256))
lemma lift_of_f {z o roots T other G essPairs L} (ok : liftCheckF z o roots T other G essPairs = true)
    (hL : Lower other G L) : Lower roots T (L + essPairs.length) := by
  simp only [liftCheckF, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨⟨hT, hR⟩, hG⟩, hnd⟩, heq⟩, hcov⟩, hess⟩ := ok
  have ⟨p1a, p1b, p1c⟩ := checkProper_sound hT
  have ⟨p2a, p2b, p2c⟩ := checkProper_sound hG
  have hR' := checkRoots_sound hR
  have heq' : renameW (fixRow z o) T = G ∨ renameW (fixRow z o) T = ALL256 ^^^ G := by
    rw [← fixWord_eq_renameW]; exact heq
  have hcov' : ∀ a ∈ roots, Avail (other.map obs) (restrictW (fixRow z o) (obs a)) := fun a ha =>
    freeIn_sound ((fixWord_eq_renameW z o a).symm ▸ hcov a ha)
  have hcard : (essPairs.map Prod.fst).toFinset.card = essPairs.length := by
    rw [List.toFinset_card_of_nodup hnd, List.length_map]
  rw [← hcard]
  apply lower_slice_flip p1a p1b p1c hR' p2a p2b p2c (fixRow z o) heq' hcov' (essPairs.map Prod.fst).toFinset _ _ L hL
  · intro a ha
    obtain ⟨⟨v, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    exact checkEss1_sound (hess (v, r, s) hm).1
  · intro a ha
    obtain ⟨⟨v, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    have hc := (hess (v, r, s) hm).2
    simp only [fixWord_eq_renameW] at hc
    rw [← obs_renameW]
    rcases hc with h0 | h1
    · exact ⟨false, by rw [h0]; funext r'; simp [obs]⟩
    · exact ⟨true, by rw [h1]; funext r'; simp only [obs, ALL256]; have := r'.isLt; exact Nat.testBit_two_pow_sub_one 256 r'.val |> fun e => by simpa [this] using e⟩
def sliceDirectCheckF (z o : Nat) (raw : List Nat) (T : Nat) (qRoots : List Nat) (qGoal : Nat) : Bool :=
  decide (z < 256) && decide (o < 256) && ((z &&& o) == 0) &&
    checkProper qGoal && checkRoots qRoots &&
    (fixWord z o T == qGoal || fixWord z o T == ALL256 ^^^ qGoal) &&
    raw.all (fun a => freeIn qRoots (fixWord z o a))
lemma slice_fast_direct_f {z o raw T qRoots qGoal qL}
    (ok : sliceDirectCheckF z o raw T qRoots qGoal = true)
    (hPrior : Lower qRoots qGoal qL) :
    Slice raw T (subcubeFast z o) qL := by
  simp only [sliceDirectCheckF, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨⟨hz, ho⟩, hzo⟩, hGp⟩, hQR⟩, heq⟩, hcov⟩ := ok
  rw [subcubeFast_eq_subcube z o hz ho hzo]
  have ⟨g0, glt, gb0⟩ := checkProper_sound hGp
  rcases heq with heq | heq
  · refine ⟨fixRow z o, qRoots, subcube_fixRow z o hz ho hzo,
      fun a ha => freeIn_sound ((fixWord_eq_renameW z o a).symm ▸ hcov a ha),
      by rw [← obs_renameW, ← fixWord_eq_renameW, heq]; exact obs_not_const g0 glt gb0, ?_⟩
    rw [← obs_renameW, ← fixWord_eq_renameW, heq]
    exact hPrior
  · refine ⟨fixRow z o, qRoots, subcube_fixRow z o hz ho hzo,
      fun a ha => freeIn_sound ((fixWord_eq_renameW z o a).symm ▸ hcov a ha),
      by rw [← obs_renameW, ← fixWord_eq_renameW, heq, obs_all256_xor]; exact fun hc => obs_not_const g0 glt gb0 (invW_inv (obs qGoal) ▸ invW_const hc), ?_⟩
    rw [← obs_renameW, ← fixWord_eq_renameW, heq, obs_all256_xor]
    intro p bank hr hav
    exact hPrior p bank hr (by simpa [invW_inv] using avail_inv hav)
def identRow (u v : Nat) (r : Row) : Row :=
  if r.val.testBit u == r.val.testBit v then r
  else ⟨(r.val ^^^ (1 <<< v)) % 256, Nat.mod_lt _ (by decide)⟩
def identDom (u v : Nat) : Nat := ALL256 ^^^ (VAR u ^^^ VAR v)
def identWord (u v w : Nat) : Nat :=
  (List.range 256).foldr (fun r acc =>
    let fr := if r.testBit u == r.testBit v then r else (r ^^^ (1 <<< v)) % 256
    if w.testBit fr then acc ||| (1 <<< r) else acc) 0
lemma identWord_eq_renameW (u v w : Nat) : identWord u v w = renameW (identRow u v) w := by
  apply Nat.eq_of_testBit_eq; intro r
  unfold identWord
  rw [testBit_foldr_bits]
  by_cases hr : r < 256
  · rw [testBit_renameW (identRow u v) w ⟨r, hr⟩]
    simp only [List.mem_range, hr, decide_true, Bool.true_and, identRow]
    split <;> rfl
  · simp only [List.mem_range, hr, decide_false, Bool.false_and]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))).symm
lemma identDom_identRow (u v : Nat) (hu : u < 8) (hv : v < 8) (r : Row) :
    (identDom u v).testBit (identRow u v r).val = true := by
  revert r
  interval_cases u <;> interval_cases v <;> decide +kernel
def sliceIdentCheck (u v : Nat) (raw : List Nat) (T : Nat) (qRoots : List Nat) (qGoal : Nat) : Bool :=
  decide (u < 8) && decide (v < 8) &&
    checkProper qGoal && checkRoots qRoots &&
    (identWord u v T == qGoal || identWord u v T == ALL256 ^^^ qGoal) &&
    raw.all (fun a => freeIn qRoots (identWord u v a))
lemma slice_ident {u v raw T qRoots qGoal qL}
    (ok : sliceIdentCheck u v raw T qRoots qGoal = true)
    (hPrior : Lower qRoots qGoal qL) :
    Slice raw T (identDom u v) qL := by
  simp only [sliceIdentCheck, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨hu, hv⟩, hGp⟩, hQR⟩, heq⟩, hcov⟩ := ok
  have ⟨g0, glt, gb0⟩ := checkProper_sound hGp
  rcases heq with heq | heq
  · refine ⟨identRow u v, qRoots, identDom_identRow u v hu hv,
      fun a ha => freeIn_sound ((identWord_eq_renameW u v a).symm ▸ hcov a ha),
      by rw [← obs_renameW, ← identWord_eq_renameW, heq]; exact obs_not_const g0 glt gb0, ?_⟩
    rw [← obs_renameW, ← identWord_eq_renameW, heq]
    exact hPrior
  · refine ⟨identRow u v, qRoots, identDom_identRow u v hu hv,
      fun a ha => freeIn_sound ((identWord_eq_renameW u v a).symm ▸ hcov a ha),
      by rw [← obs_renameW, ← identWord_eq_renameW, heq, obs_all256_xor]; exact fun hc => obs_not_const g0 glt gb0 (invW_inv (obs qGoal) ▸ invW_const hc), ?_⟩
    rw [← obs_renameW, ← identWord_eq_renameW, heq, obs_all256_xor]
    intro p bank hr hav
    exact hPrior p bank hr (by simpa [invW_inv] using avail_inv hav)
def mkBase (pos neg : List Nat) (rs : List Nat) : List Decor :=
  rs.map fun w => (w, projBits pos w, projBits neg w)
lemma mkBase_ok {pos neg rs} (hR : checkRoots rs = true) :
    ∀ x ∈ mkBase pos neg rs, faithful pos neg x ∧ x.1 < 2^256 := by
  have hr := checkRoots_sound hR
  intro x hx
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
  exact ⟨⟨rfl, rfl⟩, (hr w hw).1⟩
def evalInput6 (r : Row) : Fin 6 → Bool := fun i => r.val.testBit i.val
def packInput6 (x : Fin 6 → Bool) : Row :=
  ⟨(x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat + 8 * (x 3).toNat +
   16 * (x 4).toNat + 32 * (x 5).toNat, by
    cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> cases x 5 <;> decide⟩
lemma evalInput6_packInput6 (x : Fin 6 → Bool) : evalInput6 (packInput6 x) = x := by
  funext i
  have h : ∀ (b0 b1 b2 b3 b4 b5 : Bool) (j : Fin 6),
      ((b0.toNat + 2 * b1.toNat + 4 * b2.toNat + 8 * b3.toNat +
        16 * b4.toNat + 32 * b5.toNat).testBit j.val) =
        ([b0, b1, b2, b3, b4, b5].getD j.val false) := by decide +kernel
  have hi := h (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) i
  fin_cases i <;> simpa [evalInput6, packInput6] using hi
lemma var_testBit6 (i : Fin 6) (r : Row) : (VAR i.val).testBit r.val = r.val.testBit i.val := by
  revert i r; decide +kernel
lemma sw_extract_full6 (T : Nat) (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false)
    (gs : List Gate) (o : Nat)
    (legal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (he : ∀ r : Row, Circuit.eval ⟨gs, o⟩ (List.ofFn (evalInput6 r)) = T.testBit r.val) :
    ∃ k S, k ≤ gs.countP isBin ∧ Live T k S ∧ ∀ a ∈ S, a ∈ varsOf 63 := by
  let seeds : List SWire := (varsOf 63).map (fun v => (false, v))
  have hseeds_lt : ∀ u ∈ seeds, u.2 < 2^256 ∧ u.2.testBit 0 = false := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
    have hall : (varsOf 63).all (fun a => decide (a < 2^256) && !a.testBit 0) = true := by decide +kernel
    have h1 := List.all_eq_true.mp hall v hv
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h1
    exact h1
  let final := swExec gs seeds
  let out := final.getD o swZero
  have hfinal_lt : out.2 < 2^256 ∧ out.2.testBit 0 = false := by
    simp only [out, List.getD_eq_getElem?_getD]
    cases eq : final[o]? with
    | none => exact ⟨by decide, by decide⟩
    | some a => exact swExec_lt gs seeds hseeds_lt a (List.mem_of_getElem? eq)
  have hread_seeds (r : Row) : seeds.map (swRead r.val) = List.ofFn (evalInput6 r) := by
    apply List.ext_getElem
    · simp only [seeds, List.length_map, List.length_ofFn]; decide
    · intro i hi1 hi2
      have hi6 : i < 6 := by simpa using hi2
      have hv : (varsOf 63)[i]? = some (VAR i) := by
        interval_cases i <;> decide
      simp only [List.getElem_map, List.getElem_ofFn, seeds, evalInput6, swRead, Bool.false_bne]
      have hget : (varsOf 63)[i]'(by simpa [seeds] using hi1) = VAR i := by
        have := List.getElem?_eq_some_iff.mp hv; exact this.2
      rw [hget]
      exact var_testBit6 ⟨i, hi6⟩ r
  have hev (r : Row) : swRead r.val out = T.testBit r.val := by
    have h1 := (swRead_get r.val final o).symm
    rw [show final = swExec gs seeds from rfl, swExec_read r.val gs seeds legal, hread_seeds r] at h1
    exact h1.trans (he r)
  have hout0 : out.1 = false := by
    have h0 := hev 0
    simp only [swRead, Fin.val_zero, hfinal_lt.2, hTb0, Bool.bne_false] at h0
    exact h0
  have hout2 : out.2 = T := by
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr : r < 256
    · have h := hev ⟨r, hr⟩
      simpa [swRead, hout0] using h
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hfinal_lt.1 (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hTlt (Nat.pow_le_pow_right (by decide) (by omega)))]
  have hfound : T ∈ reps final := by
    rw [← hout2]
    exact (get_simple final o).resolve_left (hout2.symm ▸ hT0)
  obtain ⟨k, S, hk, hlive, hsub⟩ := extract_live hT0 gs seeds hfound
  refine ⟨k, S, hk, hlive, ?_⟩
  simpa [reps, seeds, List.map_map, Function.comp_def] using hsub
lemma replace_of_lower6 (T : Nat) (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false)
    (L : Nat) (hLow : Lower (varsOf 63) T L)
    (wit : List Gate) (wo : Nat) (hwLen : wit.length ≤ L + 1)
    (hwMono : PEqualNP.MetaComplexity.Monotone2 ⟨wit, wo⟩)
    (tgt : (Fin 6 → Bool) → Bool)
    (hTgtT : ∀ r : Row, tgt (evalInput6 r) = T.testBit r.val)
    (hwEvalR : ∀ r : Row, Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput6 r)) = T.testBit r.val)
    (s : Nat) (hs : PEqualNP.MetaComplexity.HasCircuitSize 6 tgt s) :
    ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧
      ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = tgt x := by
  obtain ⟨⟨gates, o⟩, hfan, hsize, spec⟩ := hs
  have legal : ∀ g ∈ gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨hop, hlen⟩ := hfan g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    exact ⟨hop, hlen⟩
  have hwEval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wit, wo⟩ (List.ofFn x) = tgt x := by
    intro x
    have hx := evalInput6_packInput6 x
    rw [← hx]
    exact (hwEvalR (packInput6 x)).trans (hTgtT (packInput6 x)).symm
  by_cases hn : ∃ g ∈ gates, g.op = .not
  · have hlt : gates.countP isBin < gates.length := by
      apply Nat.lt_of_le_of_ne List.countP_le_length
      intro eq
      obtain ⟨g, hg, hop⟩ := hn
      have bad := List.countP_eq_length.mp eq g hg
      simp [isBin, hop] at bad
    obtain ⟨k, S, hk, hlive, hsub⟩ := sw_extract_full6 T hT0 hTlt hTb0 gates o legal (fun r => (spec (evalInput6 r)).trans (hTgtT r))
    have hnd : S.toList.Nodup := Finset.nodup_toList S
    have hrun := live_to_run hlive S.toList hnd (by simp)
    have hsup : Supply ((varsOf 63).map obs) (S.toList.map obs) := fun v hv => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
      exact Or.inl (List.mem_map_of_mem (hsub a (Finset.mem_toList.mp ha)))
    obtain ⟨q, next, hq, hav, hbound⟩ :=
      contraction (obs_not_const hT0 hTlt hTb0) hrun ((varsOf 63).map obs)
        (show Reach ((varsOf 63).map obs) 0 ((varsOf 63).map obs) from rfl) hsup
    have hlo := hLow q next hq hav
    have hcsz : (⟨wit, wo⟩ : Circuit).size = wit.length := rfl
    have hgsz : (⟨gates, o⟩ : Circuit).size = gates.length := rfl
    refine ⟨⟨wit, wo⟩, hwMono, ?_, hwEval⟩
    omega
  · refine ⟨⟨gates, o⟩, ?_, hsize, spec⟩
    intro g hg
    obtain ⟨hop, hlen⟩ := legal g hg
    refine ⟨?_, hlen⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hn ⟨g, hg, h⟩).elim
def q (sl : Nat) (cs : List Nat) : Option PoolSpec :=
  some (sl, cs.map fun x => (x % 4, (x / 4) % 1024, x / 4096))
def d (x : Nat) : Nat := x * 0x1000000000000000100000000000000010000000000000001
def r (a n : Nat) : List Nat := List.range' a n
def b6 : List Nat := [0,1,2,3,4,5]
def b5 : List Nat := [0,1,2,3,4]
def u6 (w p : List Nat) : NodeSpec := (b6 ++ w, p, [0])
def e6 (w p : List Nat) : NodeSpec := (b6 ++ w, p, [])
def a6 (w p a : List Nat) : NodeSpec := (b6 ++ w, p, a)
def u5 (w p : List Nat) : NodeSpec := (b5 ++ w, p, [0])
def e5 (w p : List Nat) : NodeSpec := (b5 ++ w, p, [])
def a5 (w p a : List Nat) : NodeSpec := (b5 ++ w, p, a)

def g_0 := (d 0xe8e8e8e8e8e8e8e8)
def r_0 : List Nat := varsOf 7
def p_0 : List Nat := [3,3,5,5,6,6]
def q_0 : List Nat := [2,1,4,1,4,2]
def F_0 : Nat := fullMask 6
set_option maxHeartbeats 0 in
lemma gp_0 : goodPairs g_0 p_0 q_0 := goodPairs_of (by decide +kernel)
def W_0 : BT Decor := buildWiresBT 2 (mkBase p_0 q_0 r_0) []
lemma W_0_ok : btAll (fun x => faithful p_0 q_0 x ∧ x.1 < 2^256) W_0 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_0 : List (List (Nat × Nat)) := [[]]
def A_0 : BT (List (Nat × Nat)) := btOfList 1 al_0
set_option maxHeartbeats 0 in
lemma A_0_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_0 = g_0) A_0 := btAll_ofList (autos_of (by decide +kernel))
def S_0 : BT (Option (Nat × Nat)) := btOfList 1 []
lemma S_0_ok : btAll (fun o => ∀ p, o = some p → Slice r_0 g_0 p.1 p.2) S_0 := btAll_ofList (fun _ h => (List.not_mem_nil h).elim)
def ps_0 : BT (Option PoolSpec) := btOfList 1 []
def B_0_2 : BT (List (List Nat)) := BT.empty
lemma B_0_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_0 2 xs.toFinset) B_0_2 := .empty
def U_0_3 : List Nat := []
def P_0_3 : BT (Option BoundPool) := buildPoolsSubBT 1 W_0 r_0 S_0 ps_0 U_0_3
def N_0_3 : List NodeSpec := [([0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_0_3 : checkNodesBT W_0 g_0 F_0 P_0_3 A_0 B_0_2 3 N_0_3 = true := by decide +kernel
def B_0_3 : BT (List (List Nat)) := buildBucketsBT W_0 N_0_3
set_option maxRecDepth 500000 in
lemma B_0_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_0 3 xs.toFinset) B_0_3 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok (buildPoolsSubBT_sound S_0_ok) A_0_ok B_0_2_ok C_0_3
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_0_ok : forestRootCheck r_0 g_0 [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_0_in : bucketContainsBT B_0_3 r_0 = true := by decide +kernel
lemma low_0 : Lower r_0 g_0 4 := lower_of_forestBT root_0_ok B_0_3_ok root_0_in
def g_1 := (d 0xfee8fee8fee8fee8)
def r_1 : List Nat := varsOf 15
def p_1 : List Nat := [3,3,5,5,6,6,9,9,10,10,12,12]
def q_1 : List Nat := [2,1,4,1,4,2,8,1,8,2,8,4]
def F_1 : Nat := fullMask 12
set_option maxHeartbeats 0 in
lemma gp_1 : goodPairs g_1 p_1 q_1 := goodPairs_of (by decide +kernel)
def W_1 : BT Decor := buildWiresBT 4 (mkBase p_1 q_1 r_1) [(1,0,1),(1,4,2),(2,5,3),(1,1,2),(1,3,1),(1,3,2),(2,4,3),(1,3,0)]
lemma W_1_ok : btAll (fun x => faithful p_1 q_1 x ∧ x.1 < 2^256) W_1 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_1 : List (List (Nat × Nat)) := [[],[(2,3)],[(1,2)],[(1,3),(2,3)],[(1,2),(2,3)],[(1,3)],[(0,2),(1,2)],[(0,3),(1,3),(2,3)],[(0,2),(1,2),(2,3)],[(0,3),(1,3)],[(0,1),(1,2)],[(0,2),(1,3)]]
def A_1 : BT (List (Nat × Nat)) := btOfList 4 al_1
set_option maxHeartbeats 0 in
lemma A_1_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_1 = g_1) A_1 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_1_0 : Slice r_1 g_1 (subcubeFast 1 0) 4 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_1_1 : Slice r_1 g_1 (subcubeFast 2 0) 4 := by
  have hc : Lower (varsOf 13) (d 0xfaa0faa0faa0faa0) 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_1_2 : Slice r_1 g_1 (subcubeFast 4 0) 4 := by
  have hc : Lower (varsOf 11) (d 0xee88ee88ee88ee88) 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_1_3 : Slice r_1 g_1 (subcubeFast 8 0) 4 := by
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) low_0
def S_1 : BT (Option (Nat × Nat)) := btOfList 2 [some (subcubeFast 1 0,4),some (subcubeFast 2 0,4),some (subcubeFast 4 0,4),some (subcubeFast 8 0,4)]
lemma S_1_ok : btAll (fun o => ∀ p, o = some p → Slice r_1 g_1 p.1 p.2) S_1 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_1_0) (forall_cons (fun _ h => by cases h; exact sl_1_1) (forall_cons (fun _ h => by cases h; exact sl_1_2) (forall_cons (fun _ h => by cases h; exact sl_1_3) (fun _ h => (List.not_mem_nil h).elim)))))
def ps_1 : BT (Option PoolSpec) := btOfList 2 [q 2 [],q 1 [],q 3 [],q 0 []]
def B_1_2 : BT (List (List Nat)) := BT.empty
lemma B_1_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_1 2 xs.toFinset) B_1_2 := .empty
def U_1_3 : List Nat := [0,1]
def P_1_3 : BT (Option BoundPool) := buildPoolsSubBT 2 W_1 r_1 S_1 ps_1 U_1_3
def N_1_3 : List NodeSpec := [([6,0,1,2],[],[]),([0,7,8,9],[0,1],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_1_3 : checkNodesBT W_1 g_1 F_1 P_1_3 A_1 B_1_2 3 N_1_3 = true := by decide +kernel
def B_1_3 : BT (List (List Nat)) := buildBucketsBT W_1 N_1_3
set_option maxRecDepth 500000 in
lemma B_1_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_1 3 xs.toFinset) B_1_3 :=
  buildBucketsBT_sound (by decide) gp_1 W_1_ok (buildPoolsSubBT_sound S_1_ok) A_1_ok B_1_2_ok C_1_3
def U_1_4 : List Nat := [1,2,3]
def P_1_4 : BT (Option BoundPool) := buildPoolsSubBT 2 W_1 r_1 S_1 ps_1 U_1_4
def N_1_4 : List NodeSpec := [([0,1,2,5,3],[2],[0]),([10,0,1,2,3],[],[]),([0,1,2,11,8],[1,3],[10])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_1_4 : checkNodesBT W_1 g_1 F_1 P_1_4 A_1 B_1_3 4 N_1_4 = true := by decide +kernel
def B_1_4 : BT (List (List Nat)) := buildBucketsBT W_1 N_1_4
set_option maxRecDepth 500000 in
lemma B_1_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_1 4 xs.toFinset) B_1_4 :=
  buildBucketsBT_sound (by decide) gp_1 W_1_ok (buildPoolsSubBT_sound S_1_ok) A_1_ok B_1_3_ok C_1_4
def U_1_5 : List Nat := (r 0 4)
def P_1_5 : BT (Option BoundPool) := buildPoolsSubBT 2 W_1 r_1 S_1 ps_1 U_1_5
def N_1_5 : List NodeSpec := [([0,1,4,2,3],(r 0 4),[0,1,3,5,7,9])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_1_5 : checkNodesBT W_1 g_1 F_1 P_1_5 A_1 B_1_4 5 N_1_5 = true := by decide +kernel
def B_1_5 : BT (List (List Nat)) := buildBucketsBT W_1 N_1_5
set_option maxRecDepth 500000 in
lemma B_1_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_1 5 xs.toFinset) B_1_5 :=
  buildBucketsBT_sound (by decide) gp_1 W_1_ok (buildPoolsSubBT_sound S_1_ok) A_1_ok B_1_4_ok C_1_5
def U_1_6 : List Nat := (r 0 4)
def P_1_6 : BT (Option BoundPool) := buildPoolsSubBT 2 W_1 r_1 S_1 ps_1 U_1_6
def N_1_6 : List NodeSpec := [([0,1,2,3],(r 0 4),[0,2,4,6,8,11])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_1_6 : checkNodesBT W_1 g_1 F_1 P_1_6 A_1 B_1_5 6 N_1_6 = true := by decide +kernel
def B_1_6 : BT (List (List Nat)) := buildBucketsBT W_1 N_1_6
set_option maxRecDepth 500000 in
lemma B_1_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_1 6 xs.toFinset) B_1_6 :=
  buildBucketsBT_sound (by decide) gp_1 W_1_ok (buildPoolsSubBT_sound S_1_ok) A_1_ok B_1_5_ok C_1_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_1_ok : forestRootCheck r_1 g_1 [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,1,9)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_1_in : bucketContainsBT B_1_6 r_1 = true := by decide +kernel
lemma low_1 : Lower r_1 g_1 7 := lower_of_forestBT root_1_ok B_1_6_ok root_1_in
def g_2 := (d 0xe880e880e880e880)
def r_2 : List Nat := varsOf 15
def p_2 : List Nat := [7,7,7,11,11,11,13,13,13,14,14,14]
def q_2 : List Nat := [6,5,3,10,9,3,12,9,5,12,10,6]
def F_2 : Nat := fullMask 12
set_option maxHeartbeats 0 in
lemma gp_2 : goodPairs g_2 p_2 q_2 := goodPairs_of (by decide +kernel)
def W_2 : BT Decor := buildWiresBT 4 (mkBase p_2 q_2 r_2) [(0,0,1),(0,0,2),(0,1,2),(0,6,3),(3,7,0),(0,2,3),(3,9,0),(0,4,2)]
lemma W_2_ok : btAll (fun x => faithful p_2 q_2 x ∧ x.1 < 2^256) W_2 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_2 : List (List (Nat × Nat)) := [[],[(2,3)],[(1,2)],[(1,2),(2,3)],[(0,1)],[(0,1),(2,3)],[(0,2),(1,2)],[(0,2),(1,2),(2,3)],[(0,2),(1,3)],[(0,1),(1,2),(2,3)],[(0,2),(1,3),(2,3)]]
def A_2 : BT (List (Nat × Nat)) := btOfList 4 al_2
set_option maxHeartbeats 0 in
lemma A_2_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_2 = g_2) A_2 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_2_0 : Slice r_2 g_2 (subcubeFast 0 1) 4 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_2_1 : Slice r_2 g_2 (subcubeFast 0 2) 4 := by
  have hc : Lower (varsOf 13) (d 0xfaa0faa0faa0faa0) 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_2_2 : Slice r_2 g_2 (subcubeFast 0 4) 4 := by
  have hc : Lower (varsOf 11) (d 0xee88ee88ee88ee88) 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_2_3 : Slice r_2 g_2 (subcubeFast 0 8) 4 := by
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) low_0
def S_2 : BT (Option (Nat × Nat)) := btOfList 2 [some (subcubeFast 0 1,4),some (subcubeFast 0 2,4),some (subcubeFast 0 4,4),some (subcubeFast 0 8,4)]
lemma S_2_ok : btAll (fun o => ∀ p, o = some p → Slice r_2 g_2 p.1 p.2) S_2 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_2_0) (forall_cons (fun _ h => by cases h; exact sl_2_1) (forall_cons (fun _ h => by cases h; exact sl_2_2) (forall_cons (fun _ h => by cases h; exact sl_2_3) (fun _ h => (List.not_mem_nil h).elim)))))
def ps_2 : BT (Option PoolSpec) := btOfList 2 [q 1 [],q 0 [],q 2 [],q 3 []]
def B_2_2 : BT (List (List Nat)) := BT.empty
lemma B_2_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 2 xs.toFinset) B_2_2 := .empty
def U_2_3 : List Nat := [0,1]
def P_2_3 : BT (Option BoundPool) := buildPoolsSubBT 2 W_2 r_2 S_2 ps_2 U_2_3
def N_2_3 : List NodeSpec := [([4,5,6,3],[0,1],[]),([8,1,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_2_3 : checkNodesBT W_2 g_2 F_2 P_2_3 A_2 B_2_2 3 N_2_3 = true := by decide +kernel
def B_2_3 : BT (List (List Nat)) := buildBucketsBT W_2 N_2_3
set_option maxRecDepth 500000 in
lemma B_2_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 3 xs.toFinset) B_2_3 :=
  buildBucketsBT_sound (by decide) gp_2 W_2_ok (buildPoolsSubBT_sound S_2_ok) A_2_ok B_2_2_ok C_2_3
def U_2_4 : List Nat := [0,2,3]
def P_2_4 : BT (Option BoundPool) := buildPoolsSubBT 2 W_2 r_2 S_2 ps_2 U_2_4
def N_2_4 : List NodeSpec := [([4,5,1,2,3],[0,2],[0]),([10,0,1,2,3],[],[]),([11,0,1,2,3],[3],[9])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_2_4 : checkNodesBT W_2 g_2 F_2 P_2_4 A_2 B_2_3 4 N_2_4 = true := by decide +kernel
def B_2_4 : BT (List (List Nat)) := buildBucketsBT W_2 N_2_4
set_option maxRecDepth 500000 in
lemma B_2_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 4 xs.toFinset) B_2_4 :=
  buildBucketsBT_sound (by decide) gp_2 W_2_ok (buildPoolsSubBT_sound S_2_ok) A_2_ok B_2_3_ok C_2_4
def U_2_5 : List Nat := (r 0 4)
def P_2_5 : BT (Option BoundPool) := buildPoolsSubBT 2 W_2 r_2 S_2 ps_2 U_2_5
def N_2_5 : List NodeSpec := [([4,0,1,2,3],(r 0 4),[0,1,4,5,8,10])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_2_5 : checkNodesBT W_2 g_2 F_2 P_2_5 A_2 B_2_4 5 N_2_5 = true := by decide +kernel
def B_2_5 : BT (List (List Nat)) := buildBucketsBT W_2 N_2_5
set_option maxRecDepth 500000 in
lemma B_2_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 5 xs.toFinset) B_2_5 :=
  buildBucketsBT_sound (by decide) gp_2 W_2_ok (buildPoolsSubBT_sound S_2_ok) A_2_ok B_2_4_ok C_2_5
def U_2_6 : List Nat := (r 0 4)
def P_2_6 : BT (Option BoundPool) := buildPoolsSubBT 2 W_2 r_2 S_2 ps_2 U_2_6
def N_2_6 : List NodeSpec := [([0,1,2,3],(r 0 4),[0,2,3,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_2_6 : checkNodesBT W_2 g_2 F_2 P_2_6 A_2 B_2_5 6 N_2_6 = true := by decide +kernel
def B_2_6 : BT (List (List Nat)) := buildBucketsBT W_2 N_2_6
set_option maxRecDepth 500000 in
lemma B_2_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 6 xs.toFinset) B_2_6 :=
  buildBucketsBT_sound (by decide) gp_2 W_2_ok (buildPoolsSubBT_sound S_2_ok) A_2_ok B_2_5_ok C_2_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_2_ok : forestRootCheck r_2 g_2 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_2_in : bucketContainsBT B_2_6 r_2 = true := by decide +kernel
lemma low_2 : Lower r_2 g_2 7 := lower_of_forestBT root_2_ok B_2_6_ok root_2_in
def g_3 := (d 0xffe8ffe8ffe8ffe8)
def r_3 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_3 : Lower r_3 g_3 5 := by
  exact lift_of_f (z := 8) (o := 0) (other := r_0) (G := g_0) (essPairs := [(VAR 3,0,8)]) (by decide +kernel) low_0
def g_4 := (d 0xf880f880f880f880)
def r_4 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_4 : Lower r_4 g_4 5 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,6,7)]) (by decide +kernel) hc
def g_5 := (d 0xffe8e880ffe8e880)
def r_5 : List Nat := varsOf 31
def p_5 : List Nat := [7,7,7,11,11,11,13,13,13,14,14,14,19,19,19,21,21,21,22,22,22,24,24,25,25,26,26,28,28]
def q_5 : List Nat := [6,5,3,10,9,3,12,9,5,12,10,6,18,17,3,20,17,5,20,18,6,16,8,17,9,18,10,20,12]
def F_5 : Nat := fullMask 29
set_option maxHeartbeats 0 in
lemma gp_5 : goodPairs g_5 p_5 q_5 := goodPairs_of (by decide +kernel)
def W_5 : BT Decor := buildWiresBT 6 (mkBase p_5 q_5 r_5) [(0,1,2),(1,5,3),(1,6,4),(3,5,7),(0,0,1),(0,0,2),(1,3,4),(0,0,11),(0,1,11),(0,5,11),(3,14,0),(1,9,3),(1,9,4),(0,9,2),(3,18,11),(1,18,4),(3,5,0),(0,2,11),(3,22,0),(2,16,4),(1,16,4),(2,2,4),(1,26,3),(0,9,11),(2,9,4),(2,0,4),(1,30,3),(2,30,3),(2,0,3),(2,2,3),(3,34,0),(2,1,3)]
lemma W_5_ok : btAll (fun x => faithful p_5 q_5 x ∧ x.1 < 2^256) W_5 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_5 : List (List (Nat × Nat)) := [[],[(3,4)],[(1,2)],[(0,1)],[(0,1),(3,4)],[(0,2),(1,2)],[(0,2),(1,2),(3,4)],[(0,1),(1,2)],[(0,1),(1,2),(3,4)],[(0,2)],[(0,2),(3,4)]]
def A_5 : BT (List (Nat × Nat)) := btOfList 4 al_5
set_option maxHeartbeats 0 in
lemma A_5_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_5 = g_5) A_5 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_5_0 : Slice r_5 g_5 (subcubeFast 0 1) 7 := by
  have hc : Lower (varsOf 30) (d 0xfffcfcc0fffcfcc0) 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_1 : Slice r_5 g_5 (subcubeFast 0 2) 7 := by
  have hc : Lower (varsOf 29) (d 0xfffafaa0fffafaa0) 7 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_2 : Slice r_5 g_5 (subcubeFast 16 0) 7 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_2
set_option maxHeartbeats 0 in
lemma sl_5_3 : Slice r_5 g_5 (subcubeFast 0 4) 7 := by
  have hc : Lower (varsOf 27) (d 0xffeeee88ffeeee88) 7 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_4 : Slice r_5 g_5 (subcubeFast 8 0) 7 := by
  have hc : Lower (varsOf 23) (d 0xe8e88080e8e88080) 7 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_5 : Slice r_5 g_5 (subcubeFast 0 16) 5 := by
  exact slice_fast_direct_f (z := 0) (o := 16) (by decide +kernel) low_3
set_option maxHeartbeats 0 in
lemma sl_5_6 : Slice r_5 g_5 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xffc0c000ffc0c000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_7 : Slice r_5 g_5 (subcubeFast 0 8) 5 := by
  have hc : Lower (varsOf 23) (d 0xffffe8e8ffffe8e8) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_8 : Slice r_5 g_5 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) (d 0xff888800ff888800) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_9 : Slice r_5 g_5 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xffa0a000ffa0a000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_10 : Slice r_5 g_5 (subcubeFast 16 8) 4 := by
  exact slice_fast_direct_f (z := 16) (o := 8) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_5_11 : Slice r_5 g_5 (subcubeFast 8 16) 4 := by
  exact slice_fast_direct_f (z := 8) (o := 16) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_5_12 : Slice r_5 g_5 (subcubeFast 8 2) 4 := by
  have hc : Lower (varsOf 21) (d 0xfafaa0a0fafaa0a0) 4 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 8) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_13 : Slice r_5 g_5 (subcubeFast 4 2) 4 := by
  have hc : Lower (varsOf 25) (d 0xffaaaa00ffaaaa00) 4 := carry_of (swaps := [(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_14 : Slice r_5 g_5 (subcubeFast 2 4) 4 := by
  have hc : Lower (varsOf 25) (d 0xffaaaa00ffaaaa00) 4 := carry_of (swaps := [(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 2) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_15 : Slice r_5 g_5 (subcubeFast 16 1) 4 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_16 : Slice r_5 g_5 (subcubeFast 4 1) 4 := by
  have hc : Lower (varsOf 26) (d 0xffcccc00ffcccc00) 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_17 : Slice r_5 g_5 (subcubeFast 1 4) 4 := by
  have hc : Lower (varsOf 26) (d 0xffcccc00ffcccc00) 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_18 : Slice r_5 g_5 (subcubeFast 1 2) 4 := by
  have hc : Lower (varsOf 28) (d 0xfff0f000fff0f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 2) (by decide +kernel) hc
def S_5 : BT (Option (Nat × Nat)) := btOfList 5 [some (subcubeFast 0 1,7),some (subcubeFast 0 2,7),some (subcubeFast 16 0,7),some (subcubeFast 0 4,7),some (subcubeFast 8 0,7),some (subcubeFast 0 16,5),some (subcubeFast 1 0,5),some (subcubeFast 0 8,5),some (subcubeFast 4 0,5),some (subcubeFast 2 0,5),some (subcubeFast 16 8,4),some (subcubeFast 8 16,4),some (subcubeFast 8 2,4),some (subcubeFast 4 2,4),some (subcubeFast 2 4,4),some (subcubeFast 16 1,4),some (subcubeFast 4 1,4),some (subcubeFast 1 4,4),some (subcubeFast 1 2,4)]
lemma S_5_ok : btAll (fun o => ∀ p, o = some p → Slice r_5 g_5 p.1 p.2) S_5 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_5_0) (forall_cons (fun _ h => by cases h; exact sl_5_1) (forall_cons (fun _ h => by cases h; exact sl_5_2) (forall_cons (fun _ h => by cases h; exact sl_5_3) (forall_cons (fun _ h => by cases h; exact sl_5_4) (forall_cons (fun _ h => by cases h; exact sl_5_5) (forall_cons (fun _ h => by cases h; exact sl_5_6) (forall_cons (fun _ h => by cases h; exact sl_5_7) (forall_cons (fun _ h => by cases h; exact sl_5_8) (forall_cons (fun _ h => by cases h; exact sl_5_9) (forall_cons (fun _ h => by cases h; exact sl_5_10) (forall_cons (fun _ h => by cases h; exact sl_5_11) (forall_cons (fun _ h => by cases h; exact sl_5_12) (forall_cons (fun _ h => by cases h; exact sl_5_13) (forall_cons (fun _ h => by cases h; exact sl_5_14) (forall_cons (fun _ h => by cases h; exact sl_5_15) (forall_cons (fun _ h => by cases h; exact sl_5_16) (forall_cons (fun _ h => by cases h; exact sl_5_17) (forall_cons (fun _ h => by cases h; exact sl_5_18) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))
def ps_5 : BT (Option PoolSpec) := btOfList 7 [q 1 [16397],q 0 [16397],q 7 [],q 5 [],q 2 [4096,45056,45060],q 2 [8196,45076,59],q 0 [],q 6 [8196],q 8 [4096],q 2 [4096,8192,8196],q 0 [12325,16421,16397],q 6 [],q 9 [],q 2 [4096,12325],q 2 [4096,8228,45131],q 1 [16397,45056],q 2 [4096,45056],q 0 [8228,16457],q 1 [8228,16457],q 3 [4096,16457],q 4 [4096,8228,16457],q 2 [8196,45079],q 4 [],q 8 [],q 16 [],q 1 [23],q 3 [23],q 2 [8196,23],q 0 [16397,45060],q 1 [],q 2 [45056,45060],q 3 [],q 0 [16397,45064],q 2 [45064,91],q 0 [12325,16450],q 0 [12325,16421],q 4 [4096],q 2 [4096],q 2 [],q 0 [8228],q 1 [8228],q 3 [4096],q 2 [4096,8228],q 4 [4096,16421],q 0 [16421,12305],q 0 [12325,16449],q 13 [],q 0 [8196],q 1 [8192],q 4 [4096,8192,8196],q 1 [16397,45079],q 3 [16397,45079],q 3 [16397],q 9 [8192],q 2 [4096,8192],q 3 [12393],q 4 [16394],q 11 [],q 0 [16394,12393],q 2 [4096,45092],q 4 [45056],q 3 [16397,45056],q 17 [],q 2 [45056],q 4 [4096,8228],q 4 [8196,23],q 0 [12325],q 1 [12325],q 3 [4096,12325],q 10 [],q 14 [],q 0 [16422],q 1 [16422],q 4 [4096,16422],q 3 [4096,16422],q 4 [4096,8192],q 0 [12409],q 1 [16386,12409],q 3 [16386,12409],q 4 [16386],q 2 [12409],q 0 [12410],q 2 [8196],q 15 [],q 1 [16386],q 4 [8196],q 2 [12290],q 5 [12290],q 1 [16386,12290],q 0 [12298],q 3 [139],q 4 [139],q 2 [12298,139],q 1 [12298,139],q 18 [],q 12 [],q 0 [12294],q 3 [12294],q 3 [16386]]
def B_5_3 : BT (List (List Nat)) := BT.empty
lemma B_5_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_5 3 xs.toFinset) B_5_3 := .empty
def U_5_4 : List Nat := []
def P_5_4 : BT (Option BoundPool) := buildPoolsSubBT 7 W_5 r_5 S_5 ps_5 U_5_4
def N_5_4 : List NodeSpec := [([8,9,10,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_5_4 : checkNodesBT W_5 g_5 F_5 P_5_4 A_5 B_5_3 4 N_5_4 = true := by decide +kernel
def B_5_4 : BT (List (List Nat)) := buildBucketsBT W_5 N_5_4
set_option maxRecDepth 500000 in
lemma B_5_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_5 4 xs.toFinset) B_5_4 :=
  buildBucketsBT_sound (by decide) gp_5 W_5_ok (buildPoolsSubBT_sound S_5_ok) A_5_ok B_5_3_ok C_5_4
def U_5_5 : List Nat := (r 0 15)
def P_5_5 : BT (Option BoundPool) := buildPoolsSubBT 7 W_5 r_5 S_5 ps_5 U_5_5
def N_5_5 : List NodeSpec := [([9,12,13,2,3,4],(r 0 5),[]),([15,1,2,3,4,11],[5],[]),([8,9,0,2,3,4],[6],[0]),([9,10,5,3,4,11],[0,1,7,8,9],[0,3,7]),e5 [8] [],([0,1,2,16,17,11],(r 10 4),[]),e5 [19] [14]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_5_5 : checkNodesBT W_5 g_5 F_5 P_5_5 A_5 B_5_4 5 N_5_5 = true := by decide +kernel
def B_5_5 : BT (List (List Nat)) := buildBucketsBT W_5 N_5_5
set_option maxRecDepth 500000 in
lemma B_5_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_5 5 xs.toFinset) B_5_5 :=
  buildBucketsBT_sound (by decide) gp_5 W_5_ok (buildPoolsSubBT_sound S_5_ok) A_5_ok B_5_4_ok C_5_5
def U_5_6 : List Nat := ([0,2,3]++r 6 4++[11,12,13]++r 15 45)
def P_5_6 : BT (Option BoundPool) := buildPoolsSubBT 7 W_5 r_5 S_5 ps_5 U_5_6
def N_5_6 : List NodeSpec := [([9,12,1,2,3,4,11],[0,2,3,6,15,16],[0]),([0,1,2,3,20],([3]++r 17 4),[]),e5 [8,11] [21,22,23],e5 [21,11] ([3,11,12]++r 24 4),u5 [12,13] [0,11,12,28,29,30],e5 [23,11] [6,11,31,32,33],e5 [24,9] [3,13,22,34],u5 [16,17] [2,3,35,36,37],u5 [18,11] ([2,3,11,12,22,23]++r 38 5),([9,0,1,2,3,17,11],[11,12,38,43,44],[0]),a5 [9,25] [29,41,45,46] [7],([9,10,5,3,4],[7,8,9,29,31,41,47,48,49],[0]),a5 [8] [6,11,21,22,31,50,51] [0,2],e5 [8,5] [3,29,31,50],([9,10,1,2,3,4,11],[0,8,11,41,48,52,53,54],[0,3,7]),e5 [9,27] ([2,11,23]++r 55 4),a5 [28,11] [22,38,52,59] [7]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_5_6 : checkNodesBT W_5 g_5 F_5 P_5_6 A_5 B_5_5 6 N_5_6 = true := by decide +kernel
def B_5_6 : BT (List (List Nat)) := buildBucketsBT W_5 N_5_6
set_option maxRecDepth 500000 in
lemma B_5_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_5 6 xs.toFinset) B_5_6 :=
  buildBucketsBT_sound (by decide) gp_5 W_5_ok (buildPoolsSubBT_sound S_5_ok) A_5_ok B_5_5_ok C_5_6
def U_5_7 : List Nat := (r 0 4++[6,11,12,13,15]++r 22 6++[29,31,36,37,38,40,41,42,46,47,48,52,54,57]++r 60 39)
def P_5_7 : BT (Option BoundPool) := buildPoolsSubBT 7 W_5 r_5 S_5 ps_5 U_5_7
def N_5_7 : List NodeSpec := [a5 [12,11] [0,1,3,15,38,52,60,61] [0,2,5,9],e5 [12] [1,3,11,12,23,29,31,60,62,63],a5 [18] [2,3,11,22,38,40,41,42,64] [0,1],u5 [21] [2,3,6,11,22,25,26,27,38,47,65],a5 [9,11] (r 0 4++[11,12,22,36,37,38,41,46,52]) [0,1,3,7],e5 [16] ([2,13,23,36]++r 66 4),a5 [9,16] [11,13,36,66,67,68,70] [0,1],e5 [29] ([2,3,22,23,31,57]++r 71 4),([9,10,1,2,3,4],[6,11,31,41,48,54,75],[0]),a5 [31] ([2,12,23]++r 76 5) [5],e5 [32] [3,12,23,29,31,62,79,81],a5 [30,5] ([3,23,24,62,69,79]++r 82 4) [5],([30,33,1,2,3,4],[11,22,62,79,86,87,88],[]),e5 [35] ([3,6,11,12,29,38]++r 89 6),e5 [30,36] ([2,3,24,46,57,69,84]++r 95 4)]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_5_7 : checkNodesBT W_5 g_5 F_5 P_5_7 A_5 B_5_6 7 N_5_7 = true := by decide +kernel
def B_5_7 : BT (List (List Nat)) := buildBucketsBT W_5 N_5_7
set_option maxRecDepth 500000 in
lemma B_5_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_5 7 xs.toFinset) B_5_7 :=
  buildBucketsBT_sound (by decide) gp_5 W_5_ok (buildPoolsSubBT_sound S_5_ok) A_5_ok B_5_6_ok C_5_7
def U_5_8 : List Nat := [0,1,3,6,11,22,29,31,36,37,38,41,52,70,79,83,84,98]
def P_5_8 : BT (Option BoundPool) := buildPoolsSubBT 7 W_5 r_5 S_5 ps_5 U_5_8
def N_5_8 : List NodeSpec := [a5 [30] [3,6,22,29,31,38,79,83,84,98] [0,2,6,10],a5 [11] [0,1,3,22,38,52] [0,2,3,5,7],a5 [9] [6,11,22,29,31,36,37,38,41,70] [0,1,3,7,8]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_5_8 : checkNodesBT W_5 g_5 F_5 P_5_8 A_5 B_5_7 8 N_5_8 = true := by decide +kernel
def B_5_8 : BT (List (List Nat)) := buildBucketsBT W_5 N_5_8
set_option maxRecDepth 500000 in
lemma B_5_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_5 8 xs.toFinset) B_5_8 :=
  buildBucketsBT_sound (by decide) gp_5 W_5_ok (buildPoolsSubBT_sound S_5_ok) A_5_ok B_5_7_ok C_5_8
def U_5_9 : List Nat := [6,22,29,31,38]
def P_5_9 : BT (Option BoundPool) := buildPoolsSubBT 7 W_5 r_5 S_5 ps_5 U_5_9
def N_5_9 : List NodeSpec := [a5 [] [6,22,29,31,38] [0,1,2,3,4,5,7,8]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_5_9 : checkNodesBT W_5 g_5 F_5 P_5_9 A_5 B_5_8 9 N_5_9 = true := by decide +kernel
def B_5_9 : BT (List (List Nat)) := buildBucketsBT W_5 N_5_9
set_option maxRecDepth 500000 in
lemma B_5_9_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_5 9 xs.toFinset) B_5_9 :=
  buildBucketsBT_sound (by decide) gp_5 W_5_ok (buildPoolsSubBT_sound S_5_ok) A_5_ok B_5_8_ok C_5_9
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_5_ok : forestRootCheck r_5 g_5 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_5_in : bucketContainsBT B_5_9 r_5 = true := by decide +kernel
lemma low_5 : Lower r_5 g_5 10 := lower_of_forestBT root_5_ok B_5_9_ok root_5_in
def g_6 := (d 0xe800e800e800e800)
def r_6 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_6 : Lower r_6 g_6 5 := by
  exact lift_of_f (z := 0) (o := 8) (other := r_0) (G := g_0) (essPairs := [(VAR 3,3,11)]) (by decide +kernel) low_0
def g_7 := (d 0xfec0fec0fec0fec0)
def r_7 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_7 : Lower r_7 g_7 5 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,8,9)]) (by decide +kernel) hc
def g_8 := (d 0xfee0fee0fee0fee0)
def r_8 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_8 : Lower r_8 g_8 5 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,4,5)]) (by decide +kernel) hc
def g_9 := (d 0xfe80fe80fe80fe80)
def r_9 : List Nat := varsOf 15
def p_9 : List Nat := [7,7,7,9,9,10,10,11,12,12,13,14]
def q_9 : List Nat := [6,5,3,8,1,8,2,3,8,4,5,6]
def F_9 : Nat := fullMask 12
set_option maxHeartbeats 0 in
lemma gp_9 : goodPairs g_9 p_9 q_9 := goodPairs_of (by decide +kernel)
def W_9 : BT Decor := buildWiresBT 5 (mkBase p_9 q_9 r_9) [(0,2,3),(1,2,3),(3,4,5),(0,1,2),(1,1,2),(3,7,8),(2,0,3),(3,0,3),(1,0,3),(3,2,12),(1,1,3),(0,0,14),(0,0,3),(1,16,2),(3,4,0),(2,0,2),(3,0,2),(2,2,1),(3,21,0),(2,0,1),(1,23,2),(0,0,1),(1,0,1),(3,2,3)]
lemma W_9_ok : btAll (fun x => faithful p_9 q_9 x ∧ x.1 < 2^256) W_9 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_9 : List (List (Nat × Nat)) := [[],[(1,2)],[(0,1)],[(0,2),(1,2)],[(0,1),(1,2)],[(0,2)]]
def A_9 : BT (List (Nat × Nat)) := btOfList 3 al_9
set_option maxHeartbeats 0 in
lemma A_9_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_9 = g_9) A_9 := btAll_ofList (autos_of (by decide +kernel))
def S_9 : BT (Option (Nat × Nat)) := btOfList 1 []
lemma S_9_ok : btAll (fun o => ∀ p, o = some p → Slice r_9 g_9 p.1 p.2) S_9 := btAll_ofList (fun _ h => (List.not_mem_nil h).elim)
def ps_9 : BT (Option PoolSpec) := btOfList 1 []
def B_9_1 : BT (List (List Nat)) := BT.empty
lemma B_9_1_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_9 1 xs.toFinset) B_9_1 := .empty
def U_9_2 : List Nat := []
def P_9_2 : BT (Option BoundPool) := buildPoolsSubBT 1 W_9 r_9 S_9 ps_9 U_9_2
def N_9_2 : List NodeSpec := [([6,0,1],[],[]),([9,0,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_9_2 : checkNodesBT W_9 g_9 F_9 P_9_2 A_9 B_9_1 2 N_9_2 = true := by decide +kernel
def B_9_2 : BT (List (List Nat)) := buildBucketsBT W_9 N_9_2
set_option maxRecDepth 500000 in
lemma B_9_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_9 2 xs.toFinset) B_9_2 :=
  buildBucketsBT_sound (by decide) gp_9 W_9_ok (buildPoolsSubBT_sound S_9_ok) A_9_ok B_9_1_ok C_9_2
def U_9_3 : List Nat := []
def P_9_3 : BT (Option BoundPool) := buildPoolsSubBT 1 W_9 r_9 S_9 ps_9 U_9_3
def N_9_3 : List NodeSpec := [([10,11,1,2],[],[3]),([13,0,1,3],[],[]),([15,1,2,3],[],[]),([16,1,2,12],[],[3]),([0,1,17,3],[],[]),([18,1,2,3],[],[]),([19,20,1,3],[],[2]),([22,1,2,3],[],[]),([0,1,24,3],[],[]),([25,26,2,3],[],[4])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_9_3 : checkNodesBT W_9 g_9 F_9 P_9_3 A_9 B_9_2 3 N_9_3 = true := by decide +kernel
def B_9_3 : BT (List (List Nat)) := buildBucketsBT W_9 N_9_3
set_option maxRecDepth 500000 in
lemma B_9_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_9 3 xs.toFinset) B_9_3 :=
  buildBucketsBT_sound (by decide) gp_9 W_9_ok (buildPoolsSubBT_sound S_9_ok) A_9_ok B_9_2_ok C_9_3
def U_9_4 : List Nat := []
def P_9_4 : BT (Option BoundPool) := buildPoolsSubBT 1 W_9 r_9 S_9 ps_9 U_9_4
def N_9_4 : List NodeSpec := [([27,0,1,2,3],[],[4]),([10,0,1,2,3],[],[0]),([0,1,2,3,12],[],[0,1,2,4]),([16,0,1,2,3],[],[0,1,3,5]),([19,0,1,2,3],[],[0,1,3]),([0,1,26,2,3],[],[0]),([25,0,1,2,3],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_9_4 : checkNodesBT W_9 g_9 F_9 P_9_4 A_9 B_9_3 4 N_9_4 = true := by decide +kernel
def B_9_4 : BT (List (List Nat)) := buildBucketsBT W_9 N_9_4
set_option maxRecDepth 500000 in
lemma B_9_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_9 4 xs.toFinset) B_9_4 :=
  buildBucketsBT_sound (by decide) gp_9 W_9_ok (buildPoolsSubBT_sound S_9_ok) A_9_ok B_9_3_ok C_9_4
def U_9_5 : List Nat := []
def P_9_5 : BT (Option BoundPool) := buildPoolsSubBT 1 W_9 r_9 S_9 ps_9 U_9_5
def N_9_5 : List NodeSpec := [([0,1,2,3],[],[0,1,2,3,4,5])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_9_5 : checkNodesBT W_9 g_9 F_9 P_9_5 A_9 B_9_4 5 N_9_5 = true := by decide +kernel
def B_9_5 : BT (List (List Nat)) := buildBucketsBT W_9 N_9_5
set_option maxRecDepth 500000 in
lemma B_9_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_9 5 xs.toFinset) B_9_5 :=
  buildBucketsBT_sound (by decide) gp_9 W_9_ok (buildPoolsSubBT_sound S_9_ok) A_9_ok B_9_4_ok C_9_5
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_9_ok : forestRootCheck r_9 g_9 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,1,9)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_9_in : bucketContainsBT B_9_5 r_9 = true := by decide +kernel
lemma low_9 : Lower r_9 g_9 6 := lower_of_forestBT root_9_ok B_9_5_ok root_9_in
def g_10 := (d 0xfc80fc80fc80fc80)
def r_10 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_10 : Lower r_10 g_10 5 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,6,7)]) (by decide +kernel) hc
def g_11 := (d 0xfac0fac0fac0fac0)
def r_11 : List Nat := varsOf 15
def p_11 : List Nat := [6,6,7,7,9,9,11,11,12,12,13,14]
def q_11 : List Nat := [4,2,5,3,8,1,10,3,8,4,5,10]
def F_11 : Nat := fullMask 12
set_option maxHeartbeats 0 in
lemma gp_11 : goodPairs g_11 p_11 q_11 := goodPairs_of (by decide +kernel)
def W_11 : BT Decor := buildWiresBT 2 (mkBase p_11 q_11 r_11) []
lemma W_11_ok : btAll (fun x => faithful p_11 q_11 x ∧ x.1 < 2^256) W_11 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_11 : List (List (Nat × Nat)) := [[]]
def A_11 : BT (List (Nat × Nat)) := btOfList 1 al_11
set_option maxHeartbeats 0 in
lemma A_11_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_11 = g_11) A_11 := btAll_ofList (autos_of (by decide +kernel))
def S_11 : BT (Option (Nat × Nat)) := btOfList 1 []
lemma S_11_ok : btAll (fun o => ∀ p, o = some p → Slice r_11 g_11 p.1 p.2) S_11 := btAll_ofList (fun _ h => (List.not_mem_nil h).elim)
def ps_11 : BT (Option PoolSpec) := btOfList 1 []
def B_11_2 : BT (List (List Nat)) := BT.empty
lemma B_11_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_11 2 xs.toFinset) B_11_2 := .empty
def U_11_3 : List Nat := []
def P_11_3 : BT (Option BoundPool) := buildPoolsSubBT 1 W_11 r_11 S_11 ps_11 U_11_3
def N_11_3 : List NodeSpec := [([0,1,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_11_3 : checkNodesBT W_11 g_11 F_11 P_11_3 A_11 B_11_2 3 N_11_3 = true := by decide +kernel
def B_11_3 : BT (List (List Nat)) := buildBucketsBT W_11 N_11_3
set_option maxRecDepth 500000 in
lemma B_11_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_11 3 xs.toFinset) B_11_3 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok (buildPoolsSubBT_sound S_11_ok) A_11_ok B_11_2_ok C_11_3
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_11_ok : forestRootCheck r_11 g_11 [(VAR 0,8,9),(VAR 1,4,6),(VAR 2,2,6),(VAR 3,1,9)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_11_in : bucketContainsBT B_11_3 r_11 = true := by decide +kernel
lemma low_11 : Lower r_11 g_11 4 := lower_of_forestBT root_11_ok B_11_3_ok root_11_in
def g_12 := (d 0xfec8e000fec8e000)
def r_12 : List Nat := varsOf 31
def p_12 : List Nat := [13,13,13,14,14,14,15,15,19,19,19,22,22,22,23,23,25,25,25,26,26,26,27,28,28,28,29]
def q_12 : List Nat := [12,9,5,12,10,6,11,7,18,17,3,20,18,6,21,7,24,17,9,24,18,10,11,24,20,12,21]
def F_12 : Nat := fullMask 27
set_option maxHeartbeats 0 in
lemma gp_12 : goodPairs g_12 p_12 q_12 := goodPairs_of (by decide +kernel)
def W_12 : BT Decor := buildWiresBT 7 (mkBase p_12 q_12 r_12) [(0,1,3),(0,2,4),(1,5,6),(1,1,3),(1,2,4),(0,8,9),(3,6,9),(3,5,8),(0,8,4),(0,2,13),(1,2,13),(3,14,15),(2,2,4),(3,2,4),(3,0,8),(0,11,8),(1,0,6),(0,21,8),(1,0,5),(2,2,13),(3,2,13),(0,3,9),(0,1,26),(1,0,27),(1,1,26),(3,6,8),(3,17,8),(0,23,4),(1,32,2),(0,21,3),(3,34,1),(3,6,23),(3,0,29),(0,23,9),(3,6,3),(2,1,3),(3,1,3),(0,3,4),(1,3,4),(3,42,43),(3,2,3),(3,1,4),(1,45,46),(1,17,40),(3,46,3),(3,40,9),(1,1,2),(0,51,3),(2,23,2),(2,51,42),(0,21,1),(2,23,4),(0,51,4),(3,57,3),(0,52,4),(1,17,5),(2,3,4),(3,3,4),(0,1,43),(3,2,42),(1,1,42),(0,1,2),(1,0,66),(3,2,8),(2,1,4),(1,69,0),(2,2,1),(3,71,3),(2,8,4),(0,1,9),(3,2,43),(1,1,4),(0,76,3),(3,17,3),(3,0,43),(0,1,4),(2,1,2),(1,2,3)]
lemma W_12_ok : btAll (fun x => faithful p_12 q_12 x ∧ x.1 < 2^256) W_12 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_12 : List (List (Nat × Nat)) := [[],[(1,2),(3,4)]]
def A_12 : BT (List (Nat × Nat)) := btOfList 1 al_12
set_option maxHeartbeats 0 in
lemma A_12_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_12 = g_12) A_12 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_12_0 : Slice r_12 g_12 (subcubeFast 1 0) 7 := by
  have hc : Lower (varsOf 30) (d 0xfcc0c000fcc0c000) 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_1 : Slice r_12 g_12 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xfa00a000fa00a000) 5 := carry_of (swaps := [(1,4),(2,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_2 : Slice r_12 g_12 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffaf000fffaf000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_3 : Slice r_12 g_12 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) (d 0xee880000ee880000) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_4 : Slice r_12 g_12 (subcubeFast 0 4) 5 := by
  have hc : Lower (varsOf 27) (d 0xffccee00ffccee00) 5 := carry_of (swaps := [(2,4)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_5 : Slice r_12 g_12 (subcubeFast 0 8) 5 := by
  have hc : Lower (varsOf 23) (d 0xfefee0e0fefee0e0) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_6 : Slice r_12 g_12 (subcubeFast 0 16) 5 := by
  have hc : Lower (varsOf 15) (d 0xfec8fec8fec8fec8) 5 := carry_of (swaps := [(1,2)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 0) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_7 : Slice r_12 g_12 (subcubeFast 4 16) 4 := by
  have hc : Lower (varsOf 11) (d 0xee88ee88ee88ee88) 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_8 : Slice r_12 g_12 (subcubeFast 2 8) 4 := by
  have hc : Lower (varsOf 21) (d 0xfafaa0a0fafaa0a0) 4 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 2) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_9 : Slice r_12 g_12 (subcubeFast 1 8) 4 := by
  have hc : Lower (varsOf 22) (d 0xfcfcc0c0fcfcc0c0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_10 : Slice r_12 g_12 (identDom 1 4) 6 := by
  have hc : Lower (varsOf 15) (d 0xecc8ecc8ecc8ecc8) 6 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_9
  exact slice_ident (u := 1) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_11 : Slice r_12 g_12 (identDom 2 3) 6 := by
  have hc : Lower (varsOf 23) (d 0xf8f8e0e0f8f8e0e0) 6 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_9
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_12 : Slice r_12 g_12 (identDom 0 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xeaeaa0a0eaeaa0a0) 5 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4)]) (by decide +kernel) low_10
  exact slice_ident (u := 0) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_13 : Slice r_12 g_12 (identDom 1 2) 5 := by
  have hc : Lower (varsOf 27) (d 0xeecccc00eecccc00) 5 := carry_of (swaps := [(1,3),(2,4)]) (by decide +kernel) low_10
  exact slice_ident (u := 1) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_14 : Slice r_12 g_12 (subcubeFast 0 1) 4 := by
  have hc : Lower (varsOf 30) (d 0xffccf000ffccf000) 4 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_11
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
def S_12 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 1 0,7),some (subcubeFast 2 0,5),some (subcubeFast 0 2,5),some (subcubeFast 4 0,5),some (subcubeFast 0 4,5),some (subcubeFast 0 8,5),some (subcubeFast 0 16,5),some (subcubeFast 4 16,4),some (subcubeFast 2 8,4),some (subcubeFast 1 8,4),some (identDom 1 4,6),some (identDom 2 3,6),some (identDom 0 3,5),some (identDom 1 2,5),some (subcubeFast 0 1,4)]
lemma S_12_ok : btAll (fun o => ∀ p, o = some p → Slice r_12 g_12 p.1 p.2) S_12 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_12_0) (forall_cons (fun _ h => by cases h; exact sl_12_1) (forall_cons (fun _ h => by cases h; exact sl_12_2) (forall_cons (fun _ h => by cases h; exact sl_12_3) (forall_cons (fun _ h => by cases h; exact sl_12_4) (forall_cons (fun _ h => by cases h; exact sl_12_5) (forall_cons (fun _ h => by cases h; exact sl_12_6) (forall_cons (fun _ h => by cases h; exact sl_12_7) (forall_cons (fun _ h => by cases h; exact sl_12_8) (forall_cons (fun _ h => by cases h; exact sl_12_9) (forall_cons (fun _ h => by cases h; exact sl_12_10) (forall_cons (fun _ h => by cases h; exact sl_12_11) (forall_cons (fun _ h => by cases h; exact sl_12_12) (forall_cons (fun _ h => by cases h; exact sl_12_13) (forall_cons (fun _ h => by cases h; exact sl_12_14) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))
def ps_12 : BT (Option PoolSpec) := btOfList 7 [q 7 [],q 0 [16392,16393,36891],q 0 [16396,16397,176299],q 8 [],q 0 [],q 5 [],q 2 [],q 4 [],q 3 [],q 0 [16394,16395],q 14 [],q 1 [],q 2 [20481],q 5 [20481],q 6 [],q 0 [12292,12293],q 0 [16393,36876],q 3 [36876],q 6 [24577],q 0 [12292],q 0 [16392,16393],q 0 [16393,12324],q 3 [12324],q 9 [],q 12 [],q 1 [32771],q 0 [16398,16399],q 0 [16397,176132],q 0 [16398,12535],q 0 [16396,16397],q 3 [16396],q 0 [16394],q 0 [16391,12475],q 0 [16395],q 0 [16392,12299],q 1 [12299],q 0 [16392,12315],q 0 [16392],q 0 [8196],q 0 [16393],q 0 [8197,12492],q 1 [12492],q 0 [12293,32779],q 1 [32779],q 0 [16390],q 0 [4106,12575],q 0 [12293],q 0 [12293,16418],q 1 [16418],q 0 [16393,36868],q 3 [36868],q 0 [12305,176139],q 0 [16389,12592],q 0 [8196,8197],q 13 [],q 0 [16394,12359],q 0 [16388,16389],q 10 [],q 0 [16398],q 0 [8197],q 0 [8198],q 0 [12299],q 11 [],q 0 [16388],q 0 [12297],q 0 [16396],q 0 [16397]]
def B_12_1 : BT (List (List Nat)) := BT.empty
lemma B_12_1_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 1 xs.toFinset) B_12_1 := .empty
def U_12_2 : List Nat := []
def P_12_2 : BT (Option BoundPool) := buildPoolsSubBT 7 W_12 r_12 S_12 ps_12 U_12_2
def N_12_2 : List NodeSpec := [([0,7,10],[],[]),([11,12,0],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_2 : checkNodesBT W_12 g_12 F_12 P_12_2 A_12 B_12_1 2 N_12_2 = true := by decide +kernel
def B_12_2 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_2
set_option maxRecDepth 500000 in
lemma B_12_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 2 xs.toFinset) B_12_2 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_1_ok C_12_2
def U_12_3 : List Nat := []
def P_12_3 : BT (Option BoundPool) := buildPoolsSubBT 7 W_12 r_12 S_12 ps_12 U_12_3
def N_12_3 : List NodeSpec := [([16,0,1,3],[],[]),([17,18,12,0],[],[0]),([0,7,8,9],[],[0]),([11,19,1,3],[],[]),([20,0,1,3],[],[]),([0,5,6,10],[],[0]),([11,0,5,8],[],[0]),([5,2,22,4],[],[]),([11,1,23,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_3 : checkNodesBT W_12 g_12 F_12 P_12_3 A_12 B_12_2 3 N_12_3 = true := by decide +kernel
def B_12_3 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_3
set_option maxRecDepth 500000 in
lemma B_12_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 3 xs.toFinset) B_12_3 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_2_ok C_12_3
def U_12_4 : List Nat := [0,1]
def P_12_4 : BT (Option BoundPool) := buildPoolsSubBT 7 W_12 r_12 S_12 ps_12 U_12_4
def N_12_4 : List NodeSpec := [([24,25,0,1,3],[],[0]),([1,28,2,26,4],[],[]),([0,1,2,26,13],[],[]),([0,27,2,29,4],[],[1]),([19,1,2,26,4],[],[]),([17,18,19,1,3],[],[0]),([17,18,0,5,8],[],[0]),([0,5,2,10,4],[],[0,1]),([30,0,1,3,9],[],[0]),([19,1,6,3,9],[],[0]),([18,0,1,3,31],[0],[]),([17,18,1,23,3],[],[0]),([0,1,7,3,9],[],[0]),([1,23,33,3,4],[],[]),([35,2,21,3,4],[],[]),([36,1,2,3,4],[],[]),([37,1,2,26,4],[],[]),([1,23,2,26,4],[],[]),([18,12,0,2,4],[],[0]),([1,38,2,3,4],[],[1]),([0,5,6,8,9],[],[0,1]),([39,0,1,2,13],[],[]),([17,40,18,41,0],[],[0,1]),([11,0,1,3,8],[0,1],[0]),([11,0,5,1,3],[1],[0]),([5,2,21,8,4],[],[0,1]),([17,12,0,2,4],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_4 : checkNodesBT W_12 g_12 F_12 P_12_4 A_12 B_12_3 4 N_12_4 = true := by decide +kernel
def B_12_4 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_4
set_option maxRecDepth 500000 in
lemma B_12_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 4 xs.toFinset) B_12_4 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_3_ok C_12_4
def U_12_5 : List Nat := (r 0 26)
def P_12_5 : BT (Option BoundPool) := buildPoolsSubBT 7 W_12 r_12 S_12 ps_12 U_12_5
def N_12_5 : List NodeSpec := [([44,0,1,2],[0,2,3],[]),e5 [47] [],([17,40,18,0,1,3],[],[0,1]),e5 [48] [],([25,0,1,2,3,13],[],[0]),([0,49,1,2,42,4],[4,5,6],[]),([24,0,1,2,3,13],[],[0]),([17,0,1,2,3,13],[7],[]),([17,18,41,0,1,3],[],[0,1]),([17,18,0,1,3,8],[0,7,8,9],[0]),a5 [50] [6,7] [1],a5 [10] [4,6,7,10,11] [0,1],([1,23,2,3,4,9],(r 10 4),[0,1]),([0,1,2,52,42,4],[6,7,14],[]),([5,1,2,21,3,4],[10],[0,1]),([17,1,23,2,3,4],[11,12],[0]),([0,5,2,8,4,9],[6,11,15],[0,1]),([0,1,2,26,8,4],[7,11,14,16,17],[0]),([1,32,23,2,3,4],[10],[0,1]),([53,1,23,2,3,4],[10],[]),([44,0,1,2,42],[0,2,3],[]),e5 [54] [],([39,41,0,1,2,4],[11],[]),([45,1,21,3,4],[8,18],[]),([55,1,2,21,3,4],[10],[]),([17,18,0,5,1,3],[9],[0]),([56,1,23,2,3,4],[10,11,19],[]),([39,0,1,2,8,4],[8,11],[0]),([11,0,1,3],[0,1],[0,1]),e5 [58] [],([0,5,1,6,3,9],[8,20],[0,1]),([18,0,5,2,8,4],[],[0]),([0,27,1,2,26,4],[7,21,22],[0,1]),([17,19,1,2,3,4],[],[0]),a5 [7] [4,10] [0,1],([19,1,6,2,3,4],[10,23],[0]),([0,1,2,26,29,4],[7,14,21,22],[0]),e5 [59] [4,6,11,24],([0,5,1,2,26,4],[6,7,14,16,17],[0,1]),([18,19,1,2,3,4],[],[0]),([18,0,1,2,3,13],[6,8],[]),u5 [30] [4,6,10],([18,1,23,2,3,4],[],[0]),([17,0,5,2,8,4],[],[0]),e5 [60] [],([19,1,2,3,4,9],[6,10,23,25],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_5 : checkNodesBT W_12 g_12 F_12 P_12_5 A_12 B_12_4 5 N_12_5 = true := by decide +kernel
def B_12_5 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_5
set_option maxRecDepth 500000 in
lemma B_12_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 5 xs.toFinset) B_12_5 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_4_ok C_12_5
def U_12_6 : List Nat := ([0]++r 3 9++[13,14,15,19,21,22,23]++r 26 32)
def P_12_6 : BT (Option BoundPool) := buildPoolsSubBT 7 W_12 r_12 S_12 ps_12 U_12_6
def N_12_6 : List NodeSpec := [([61,62,0,1,2],[0,5,14,26],[0]),([0,63,2,3,4],[5,11,14,27],[]),e5 [42] [0,3,4,6,7,8,11,28],([0,1,2,42,43],[0,3,5,29],[0]),a5 [64,42] [0,7,8] [1],a5 [45,42] [5,7,8,14,30] [1],u5 [45,46] [0,6,7,8,11],u5 [17,5] [6,7,8,11,31],e5 [42,65] [3,6],([1,23,2,3,4],[3,10,11,13,19],[0,1]),([0,5,2,8,4],[6,11,15],[0,1]),u5 [49] (r 3 6++[11,32]),a5 [18,41] [0,6,7] [0,1],a5 [18,5] [0,7,11,33] [0,1],([45,0,1,6,3,4],[5,7,8,14,34,35],[0]),u5 [39] ([0]++r 4 5++[11,36]),a5 [5,6] [8,11,19,37] [0,1],([1,67,2,3,4],[0,3,11,38],[]),a5 [5,9] (r 5 4++[11,14,19,39]) [0,1],a5 [52] [3,4,6,7,8,11,14,40,41] [0,1],([68,0,1,3,4],[5,6,7,42,43],[]),([70,1,2,3,4],[0,3,11,44],[]),e5 [72] [0,4,6,11,45],a5 [8,9] (r 5 4++[11,14,39,46]) [0,1],([73,0,1,2,3],[5,6,14,47,48],[]),a5 [51,42] [0,5,6,7,11] [0,1],([19,1,2,3,4],[6,23,46],[0]),([0,74,2,3,4],[7,11,14,49,50],[]),a5 [17,8] [6,7,8,14,31] [0,1],([75,0,1,3,4],[5,7,14,51],[]),e5 [77] [0,3,4,6,7,8,11,52],([0,1,2,26,4],[7,14,21,22],[0,1]),a5 [26] [6,7,8,11,14,21] [0,1],([0,66,51,3,4],[0,6,11,53,54],[]),u5 [18,8] [0,6,7,33],e5 [78] [6,8,11,14,55],a5 [17,40] [8,11] [0,1],a5 [17,41] [3,6] [0,1],([17,18,0,1,3],[7,8,9],[0]),([79,1,2,3,4],[0,3],[]),([0,80,2,3,76],[0,3,11,56,57],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_6 : checkNodesBT W_12 g_12 F_12 P_12_6 A_12 B_12_5 6 N_12_6 = true := by decide +kernel
def B_12_6 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_6
set_option maxRecDepth 500000 in
lemma B_12_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 6 xs.toFinset) B_12_6 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_5_ok C_12_6
def U_12_7 : List Nat := ([0]++r 3 6++[11,14,19,31,33,38,44,46,54]++r 57 10)
def P_12_7 : BT (Option BoundPool) := buildPoolsSubBT 7 W_12 r_12 S_12 ps_12 U_12_7
def N_12_7 : List NodeSpec := [u5 [61] [0,3,4,6,7,8,11,14,58],a5 [5] (r 3 6++[11,14,19]) [0,1],u5 [66] ([0]++r 3 4++[11,14,38]),a5 [51] ([0,3]++r 5 4++[11,14,59]) [0,1],a5 [8] (r 5 4++[14,46]) [0,1],a5 [18] ([0]++r 4 4++[11,33]) [0,1],a5 [81] (r 3 6++[11,14,54,60]) [1],a5 [45] [0,3,4,6,7,8,11,14,61,62] [0,1],u5 [80] ([0]++r 3 6++[11,63]),a5 [82] ([3]++r 5 4++[11,14,64]) [1],u5 [69] (r 3 6++[11,14,44,57]),a5 [42] [0,3,6,7,65] [0,1],u5 [17] (r 4 5++[11,14,31]),a5 [43] [0,5,6,11,66] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_7 : checkNodesBT W_12 g_12 F_12 P_12_7 A_12 B_12_6 7 N_12_7 = true := by decide +kernel
def B_12_7 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_7
set_option maxRecDepth 500000 in
lemma B_12_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 7 xs.toFinset) B_12_7 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_6_ok C_12_7
def U_12_8 : List Nat := [4]
def P_12_8 : BT (Option BoundPool) := buildPoolsSubBT 7 W_12 r_12 S_12 ps_12 U_12_8
def N_12_8 : List NodeSpec := [a5 [] [4] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_8 : checkNodesBT W_12 g_12 F_12 P_12_8 A_12 B_12_7 8 N_12_8 = true := by decide +kernel
def B_12_8 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_8
set_option maxRecDepth 500000 in
lemma B_12_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 8 xs.toFinset) B_12_8 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_7_ok C_12_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_12_ok : forestRootCheck r_12 g_12 [(VAR 0,12,13),(VAR 1,12,14),(VAR 2,9,13),(VAR 3,5,13),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_12_in : bucketContainsBT B_12_8 r_12 = true := by decide +kernel
lemma low_12 : Lower r_12 g_12 9 := lower_of_forestBT root_12_ok B_12_8_ok root_12_in
def g_13 := (d 0xffeef880ffeef880)
def r_13 : List Nat := varsOf 31
def p_13 : List Nat := [7,7,7,11,11,11,12,12,13,13,14,14,17,17,18,18,19,21,21,22,22,24,24,25,26,28]
def q_13 : List Nat := [6,5,3,10,9,3,8,4,9,5,10,6,16,1,16,2,3,20,5,20,6,16,8,9,10,20]
def F_13 : Nat := fullMask 26
set_option maxHeartbeats 0 in
lemma gp_13 : goodPairs g_13 p_13 q_13 := goodPairs_of (by decide +kernel)
def W_13 : BT Decor := buildWiresBT 8 (mkBase p_13 q_13 r_13) [(0,0,1),(1,5,3),(1,2,4),(0,6,7),(1,3,4),(0,1,4),(1,1,4),(3,10,11),(1,2,3),(2,0,3),(1,0,4),(0,1,15),(3,16,3),(0,5,7),(1,18,3),(3,2,3),(1,0,1),(3,20,21),(0,2,6),(1,23,4),(0,0,11),(1,25,3),(3,2,26),(3,5,9),(1,6,4),(3,20,0),(2,21,3),(3,5,3),(1,5,4),(2,2,4),(3,34,6),(3,2,6),(2,5,3),(1,37,4),(1,16,3),(0,0,7),(3,3,33),(3,5,13),(0,3,4),(3,43,9),(0,0,9),(0,1,7),(3,46,0),(0,0,13),(1,48,4),(3,1,4),(1,20,50),(3,20,15),(0,13,15),(3,1,15),(0,0,4),(1,20,55),(3,10,13),(1,30,4),(0,1,13),(1,55,3),(1,2,60),(3,10,0),(2,1,3),(3,63,15),(3,14,15),(1,55,1),(1,14,4),(3,63,0),(1,68,4),(1,0,3),(3,5,70),(2,0,4),(3,0,4),(2,5,4),(1,74,3),(2,0,1),(1,20,76),(1,25,2),(0,21,13),(1,5,2),(2,3,4),(1,81,5),(2,6,4),(0,1,3),(3,84,15),(2,1,0),(1,14,86),(3,73,13),(3,84,0),(1,89,4),(1,1,3),(3,2,60),(2,1,2),(3,93,0),(2,14,4),(1,20,5),(3,20,1),(3,5,7),(3,86,13),(1,94,4),(3,93,15),(0,0,91),(0,0,3),(1,103,4),(3,3,4),(1,105,2),(1,2,43),(1,20,4),(2,13,4),(1,50,3),(3,3,15),(3,81,0),(3,10,3),(1,1,43),(1,1,2),(0,0,115),(1,76,3),(3,0,3),(1,118,1),(2,0,43),(3,2,70),(3,1,3),(3,122,0),(3,14,1),(1,55,2),(1,14,1),(2,0,2),(1,127,4),(1,50,2),(3,2,4),(1,0,2)]
lemma W_13_ok : btAll (fun x => faithful p_13 q_13 x ∧ x.1 < 2^256) W_13 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_13 : List (List (Nat × Nat)) := [[],[(0,1)]]
def A_13 : BT (List (Nat × Nat)) := btOfList 1 al_13
set_option maxHeartbeats 0 in
lemma A_13_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_13 = g_13) A_13 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_13_0 : Slice r_13 g_13 (subcubeFast 4 0) 6 := by
  have hc : Lower (varsOf 27) (d 0xffee8800ffee8800) 6 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_1 : Slice r_13 g_13 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) (d 0xfffffcc0fffffcc0) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_2 : Slice r_13 g_13 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffffaa0fffffaa0) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_3 : Slice r_13 g_13 (subcubeFast 0 4) 5 := by
  have hc : Lower (varsOf 27) (d 0xffeeff88ffeeff88) 5 := carry_of (swaps := [(2,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_4 : Slice r_13 g_13 (subcubeFast 8 0) 5 := by
  have hc : Lower (varsOf 23) (d 0xeeee8080eeee8080) 5 := carry_of (swaps := [(0,1),(1,2),(3,4)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_5 : Slice r_13 g_13 (subcubeFast 16 0) 5 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_4
set_option maxHeartbeats 0 in
lemma sl_13_6 : Slice r_13 g_13 (subcubeFast 8 4) 4 := by
  have hc : Lower (varsOf 19) (d 0xeeee8888eeee8888) 4 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 8) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_7 : Slice r_13 g_13 (subcubeFast 16 2) 4 := by
  have hc : Lower (varsOf 13) (d 0xfaa0faa0faa0faa0) 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_8 : Slice r_13 g_13 (subcubeFast 16 1) 4 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_9 : Slice r_13 g_13 (identDom 0 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xeeeea8a8eeeea8a8) 5 := carry_of (swaps := [(0,3),(2,3),(3,4)]) (by decide +kernel) low_7
  exact slice_ident (u := 0) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_10 : Slice r_13 g_13 (identDom 1 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xeeeec8c8eeeec8c8) 5 := carry_of (swaps := [(0,1),(1,3),(2,3),(3,4)]) (by decide +kernel) low_7
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_11 : Slice r_13 g_13 (identDom 0 1) 5 := by
  have hc : Lower (varsOf 29) (d 0xffaafaa0ffaafaa0) 5 := carry_of (swaps := [(0,2),(1,4)]) (by decide +kernel) low_8
  exact slice_ident (u := 0) (v := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_12 : Slice r_13 g_13 (subcubeFast 2 0) 4 := by
  have hc : Lower (varsOf 29) (d 0xffaaf000ffaaf000) 4 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_11
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_13 : Slice r_13 g_13 (subcubeFast 1 0) 4 := by
  have hc : Lower (varsOf 30) (d 0xffccf000ffccf000) 4 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_11
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
def S_13 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 4 0,6),some (subcubeFast 0 1,5),some (subcubeFast 0 2,5),some (subcubeFast 0 4,5),some (subcubeFast 8 0,5),some (subcubeFast 16 0,5),some (subcubeFast 8 4,4),some (subcubeFast 16 2,4),some (subcubeFast 16 1,4),some (identDom 0 3,5),some (identDom 1 3,5),some (identDom 0 1,5),some (subcubeFast 2 0,4),some (subcubeFast 1 0,4)]
lemma S_13_ok : btAll (fun o => ∀ p, o = some p → Slice r_13 g_13 p.1 p.2) S_13 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_13_0) (forall_cons (fun _ h => by cases h; exact sl_13_1) (forall_cons (fun _ h => by cases h; exact sl_13_2) (forall_cons (fun _ h => by cases h; exact sl_13_3) (forall_cons (fun _ h => by cases h; exact sl_13_4) (forall_cons (fun _ h => by cases h; exact sl_13_5) (forall_cons (fun _ h => by cases h; exact sl_13_6) (forall_cons (fun _ h => by cases h; exact sl_13_7) (forall_cons (fun _ h => by cases h; exact sl_13_8) (forall_cons (fun _ h => by cases h; exact sl_13_9) (forall_cons (fun _ h => by cases h; exact sl_13_10) (forall_cons (fun _ h => by cases h; exact sl_13_11) (forall_cons (fun _ h => by cases h; exact sl_13_12) (forall_cons (fun _ h => by cases h; exact sl_13_13) (fun _ h => (List.not_mem_nil h).elim)))))))))))))))
def ps_13 : BT (Option PoolSpec) := btOfList 7 [q 0 [16388,16389,45099],q 0 [],q 2 [16405,16393],q 11 [12309,24587],q 8 [],q 7 [],q 0 [16396,16397,37039],q 6 [],q 5 [],q 1 [16393,16397],q 13 [],q 12 [],q 2 [],q 0 [16385,61492],q 0 [16385,61447],q 9 [],q 3 [],q 1 [],q 0 [16384,225361],q 0 [16388,53291],q 0 [16384,16385],q 1 [12509],q 0 [16384,12509],q 0 [16388,43],q 4 [],q 0 [16384,4317],q 1 [16389],q 0 [16389,45056],q 0 [16386,16387],q 2 [16405],q 5 [4096],q 11 [12297],q 0 [4096,4097],q 2 [16393],q 1 [16405,16393],q 11 [],q 11 [12311],q 0 [12294,255],q 11 [8213],q 4 [16393],q 11 [12299],q 10 [],q 2 [16394],q 4 [16394],q 0 [6,53595],q 0 [16385,61815],q 1 [4317],q 11 [12309],q 4 [8613],q 0 [16396,16397],q 0 [16398],q 1 [16394],q 0 [28672],q 1 [16393],q 0 [16465],q 0 [16438],q 0 [53248],q 0 [16391],q 0 [16385,61455],q 0 [16385],q 0 [16386],q 0 [16384],q 0 [16397],q 1 [16398],q 0 [16388,12331],q 0 [16396,176133],q 0 [4098],q 5 [6],q 3 [12290],q 0 [4096],q 0 [16398,16399],q 0 [4097],q 0 [471040],q 2 [16385],q 0 [4098,12593],q 0 [375],q 0 [12291,4569],q 0 [16396,176130],q 3 [12293],q 0 [83],q 4 [286731],q 2 [16386],q 1 [16405],q 0 [12295,491],q 1 [16893],q 1 [16397],q 0 [12290],q 0 [12288,12289],q 0 [12288],q 0 [12293],q 0 [12289],q 1 [16441],q 0 [16389],q 0 [16396],q 0 [16399],q 0 [12295]]
def B_13_2 : BT (List (List Nat)) := BT.empty
lemma B_13_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_13 2 xs.toFinset) B_13_2 := .empty
def U_13_3 : List Nat := []
def P_13_3 : BT (Option BoundPool) := buildPoolsSubBT 7 W_13 r_13 S_13 ps_13 U_13_3
def N_13_3 : List NodeSpec := [([0,1,8,9],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_13_3 : checkNodesBT W_13 g_13 F_13 P_13_3 A_13 B_13_2 3 N_13_3 = true := by decide +kernel
def B_13_3 : BT (List (List Nat)) := buildBucketsBT W_13 N_13_3
set_option maxRecDepth 500000 in
lemma B_13_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_13 3 xs.toFinset) B_13_3 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok (buildPoolsSubBT_sound S_13_ok) A_13_ok B_13_2_ok C_13_3
def U_13_4 : List Nat := (r 0 4)
def P_13_4 : BT (Option BoundPool) := buildPoolsSubBT 7 W_13 r_13 S_13 ps_13 U_13_4
def N_13_4 : List NodeSpec := [([12,0,2,3,13],[0],[]),([14,17,16,2,4],[],[]),([0,1,19,4,7],[],[]),([5,22,2,3,4],[],[]),([0,1,3,6,24],[],[]),([20,12,0,2,3],[0],[]),([0,1,6,7,9],[],[0]),([27,25,1,3,4],[],[]),([28,0,1,3,7],[],[]),([0,1,3,7,29],[1],[]),([0,1,3,8,4],[1],[0]),([30,16,2,3,4],[],[]),([31,5,2,6,4],[],[]),([31,32,5,2,4],[],[]),([14,1,3,33,7],[2],[]),([0,1,3,35,4],[],[]),([36,5,21,3,4],[3],[]),([0,1,3,38,7],[],[]),([14,16,2,39,4],[],[]),([40,1,3,33,7],[2],[]),([41,0,1,3,7],[],[]),([42,21,2,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_13_4 : checkNodesBT W_13 g_13 F_13 P_13_4 A_13 B_13_3 4 N_13_4 = true := by decide +kernel
def B_13_4 : BT (List (List Nat)) := buildBucketsBT W_13 N_13_4
set_option maxRecDepth 500000 in
lemma B_13_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_13 4 xs.toFinset) B_13_4 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok (buildPoolsSubBT_sound S_13_ok) A_13_ok B_13_3_ok C_13_4
def U_13_5 : List Nat := ([0,1,2]++r 4 44)
def P_13_5 : BT (Option BoundPool) := buildPoolsSubBT 7 W_13 r_13 S_13 ps_13 U_13_5
def N_13_5 : List NodeSpec := [([44,0,1,2],(r 4 4),[]),([45,0,1,3,7,9],[4,8,9],[]),([47,0,1,3,4,7],[],[]),e5 [49] [10,11,12],e5 [51] [1],e5 [52] [],([30,1,2,3,4,15],[],[0]),e5 [53] [13],([54,0,2,3,13,4],[14],[]),e5 [26] [1,15,16],([17,0,16,2,3,4],[5,11,17],[0]),e5 [56] [1,18],e5 [57] [1,19],e5 [58] [],([50,0,59,2,3,4],[16],[]),([55,1,2,3,13,15],[20],[1]),([20,0,1,2,60,4],[1],[]),([0,1,2,60,13,4],[1,15,21],[]),([0,1,2,60,61,4],[15,21,22],[]),([20,62,1,2,3,4],[23],[]),([62,1,2,3,13,4],[23],[]),e5 [64] [17],([14,16,1,2,3,4],[5,24],[]),([14,16,2,3,4],[4,5,17],[0]),([14,1,2,3,65,4],[17],[]),([20,0,66,2,3,4],[25],[]),([0,1,2,3,67,9],[15,24],[]),([34,68,0,1,3,4],[],[]),([20,54,0,2,3,4],[14],[]),([25,1,2,3,26,4],[10,12,26,27],[0,1]),e5 [69] [17],([71,5,1,2,3,4],[17],[]),([72,20,73,1,2,3],[28],[1]),([68,1,2,3,4,15],[11],[]),e5 [75] [1,16],([0,1,3,6,4,7],[8,16],[0]),([0,1,2,6,13,4],[1],[]),([14,1,2,3,4,33],[4,29,30],[0]),([5,21,2,3,13,4],[11,31,32],[0]),([5,40,1,3,4,7],[16,33],[0]),([5,0,1,3,33,7],[2,5,8,34],[]),e5 [77] [],([32,5,21,2,3,4],[11,17,35,36],[0]),([25,1,2,78,3,4],[27],[]),([31,5,2,3,4],[5,17,30,35],[0]),e5 [79] [],([34,37,0,1,3,4],[],[]),([68,1,2,3,70,4],[17,37],[]),([0,1,2,3,33,9],[4,5,10,11,24],[]),e5 [6] [1,16],u5 [38] [],([34,0,1,3,6,4],[1],[0]),([37,0,1,3,4,7],[8],[0]),([5,21,2,80,3,4],[32,38],[]),([36,5,0,1,3,4],[],[0]),([18,0,1,3,4,7],[1,8,39],[0]),([20,55,1,2,3,15],[20],[1]),e5 [82] [1,16],([25,1,2,3,13,4],[27],[]),e5 [83] [1,16],([20,5,21,2,3,4],[17,32,40],[0]),([0,1,2,3,33,7],[1,5,10,11],[]),([36,0,1,3,6,4],[1],[]),u5 [41] [],e5 [85] [17],([81,0,1,2,6,4],[],[]),([0,1,23,3,6,4],[16],[0]),([0,1,2,6,4,9],[8,15,41],[0]),([68,0,1,3,4,7],[],[]),([14,87,1,2,3,4],[17],[]),([0,1,3,33,7],[1,4,5,34],[0,1]),e5 [88] [1],e5 [90] [17],([20,0,1,2,6,4],[1],[]),([5,2,3,70,91,4],[17,24],[]),([14,5,2,3,91,4],[12,24],[]),([92,0,1,2,60,4],[22],[]),([14,63,5,2,3,4],[12,17,24],[]),([14,5,1,3,4,7],[33,39],[0]),([94,1,2,3,4,15],[11],[]),([34,14,5,1,3,4],[42,43],[]),([95,0,1,3,7,9],[4],[]),u5 [29] [1,12,16,17],e5 [96] [16],([76,0,97,2,3,4],[],[]),([98,0,1,3,4,7],[1,8],[]),([20,25,1,2,3,4],[12,27],[1]),e5 [98] [16],u5 [28] [],([44,0,1,2,9],(r 4 4++[24]),[]),([48,1,21,2,3,4],[11],[]),([89,1,2,3,4,15],[8,11],[]),u5 [42] [],([5,0,1,3,7,9],[4,5,39],[0]),u5 [22] [],e5 [99] [44],([34,89,0,1,3,4],[],[]),e5 [100] [17],([72,73,1,2,3,13],[28],[1]),e5 [101] [45],([12,0,2,3],[0,4,5],[0]),([0,66,2,3,13,4],[10,25,46],[]),([5,21,2,3,6,4],[11,17,32,47],[0]),([102,1,2,3,70,4],[17],[]),([0,1,2,3,104,11],[4,10,11],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_13_5 : checkNodesBT W_13 g_13 F_13 P_13_5 A_13 B_13_4 5 N_13_5 = true := by decide +kernel
def B_13_5 : BT (List (List Nat)) := buildBucketsBT W_13 N_13_5
set_option maxRecDepth 500000 in
lemma B_13_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_13 5 xs.toFinset) B_13_5 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok (buildPoolsSubBT_sound S_13_ok) A_13_ok B_13_4_ok C_13_5
def U_13_6 : List Nat := ([1,4,5,7,8,10,11,12]++r 14 4++r 20 14++[35,37]++r 39 5++[46]++r 48 45)
def P_13_6 : BT (Option BoundPool) := buildPoolsSubBT 7 W_13 r_13 S_13 ps_13 U_13_6
def N_13_6 : List NodeSpec := [([0,1,106,3,4],[5,7,16,48],[]),e5 [9] [4,5,7],e5 [45] [1,4,8,10,11,12,15,16,17],([0,1,2,43,9],[4,5,7,49],[0]),([0,1,3,107,4],[5,16,24],[]),([34,81,0,1,3,4],[1,4,5,8,42,43,50,51],[]),([0,1,3,4,7],[5,7],[]),e5 [40] [4,7,10,11,12,16,17,24,52],([40,0,1,3,4,7],[1,4,7,8,16,33,39,53],[0,1]),e5 [108] [10,11,12,16,17,24,54],e5 [109] [1,7,10,11,12,16,17,24,55],a5 [48] [7,8,10,11,12,16,17,56] [0,1],a5 [20,50] [1,12,16,57] [0,1],e5 [110] [1,4,12,16],([72,73,1,2,3],[4,5,28],[0,1]),e5 [111] [1,4,11,12,16,17,24,41,58],([0,1,3,4,7,9],[4,5,7,39],[]),a5 [20,15] [16,17,59] [0,1],u5 [72,20] [1,4,10,16,60],a5 [13,15] [16,17,59] [0,1],([54,0,2,3,4],[5,12,14,17],[0]),a5 [25] [1,4,5,10,12,15,16,17,24,26,27] [0,1],([25,1,2,3,4],[4,5,10,12,27],[0,1]),a5 [20,55] [1,8,16,24,61] [0,1],([34,0,1,3,4,9],[4,5,7,62],[]),a5 [55,13] [1,8,10,16,17,24,61] [0,1],([55,1,2,3,15],[5,8,17,20],[0,1]),e5 [112] [1,4,10,11,12,16,17,24,63],([113,0,1,2,4],[5,7,24,64],[]),([0,2,3,114,4],[7,8,12,65],[]),u5 [60] [4,5,16,22],([0,1,2,60,4],[4,5,21,22],[0]),([62,1,2,3,4],[4,5,23],[0]),([0,66,2,3,4],[4,12,25,46],[0]),u5 [20,76] [1,12,16,40,66],([14,86,1,2,3,4],[4,10,12,17,24,67,68],[0]),([0,1,3,7,9],[4,5,7,39],[0,1]),u5 [5,7] [1,5,8,10,11,16,17,69],([81,105,0,1,2],[5,7,8,24,70],[0]),u5 [5] [1,5,8,10,11,12,15,16,17,24],u5 [20,21] [1,16,17,71],u5 [37] [1,8,10,11,15,16],u5 [31] [1,5,8,12,16,17],e5 [116] [1,5,7,8,12,24,72],a5 [50,13] [1,12,16,57] [0,1],u5 [102] [1,5,8,12,15,16,17],([34,5,0,1,3,4],[1,4,5,43,51,69],[0,1]),a5 [103,11] [4,8,10,12,24] [0,1],([14,1,2,3,4,15],[4,8,17,24,68,73],[0]),e5 [117] [5,10,12,16,17,74],u5 [94] [1,7,8,10,11,16,17,24,75],([0,119,2,3,4],[5,7,12,17,24,76],[]),([120,1,2,3,4],[5,7,77],[]),a5 [21,13] [12,16,17,71] [0,1],e5 [14] [1,4,10,11,12,15,16,24],a5 [76,13] [10,12,16,17,31,66] [1],([14,0,1,3,4,7],[4,7,8,33,39,53],[0,1]),u5 [6] [1,8,10,11,12,16,17],u5 [32,5] [10,11,12,17,24],([5,0,2,3,91,4],[5,11,12,17,24,78],[0,1]),u5 [95,9] [4,15],a5 [30] [1,8,10,11,12,16,17,24,79] [0,1],([121,0,1,3,4],[4,7,16,17,80],[]),([72,14,1,2,3,4],[4,8,10,24,81],[]),([5,0,1,3,4,7],[4,5,8,16,33,39,53,69],[0,1]),a5 [33] [1,4,5,11,16,24,82] [0,1],e5 [72,93] [4,5,10,16],([105,0,1,3,7],[5,7,8],[]),e5 [123] [1,5,7,8,12,16,24,83],u5 [5,33] [5,11,29,82],u5 [20,5] [1,10,11,12,16,17,24,69],e5 [14,124] [10,12,15,17,24],([0,1,125,3,4],[5,7,16],[]),e5 [14,126] [10,11,15,17],([5,21,2,3,4],[5,11,32,35],[0]),e5 [128] [4,7,11,12,84],u5 [45,9] [4,8,15,85],u5 [81,5] [4,5,10,11,12,17,24],([34,14,0,1,3,4],[1,4,7,8,42,51,86],[0,1]),u5 [5,80] [16,69],([14,5,1,2,3,4],[4,10,12,17,24,30,68],[0]),u5 [74] [1,4,5,10,11,15,16,24],u5 [104] [4,7,11,12,24],([0,1,129,3,4],[7,8,12,16],[]),([103,1,2,70,4],[4,7,15,24,87],[]),u5 [5,13] [1,11,16,24,69],u5 [14,9] [4,7,8,15,85],u5 [89] [1,7,8,10,11,15,16,17,24],e5 [72,84] [4,5,10,24],([34,103,0,1,3,4],[1,4,7,42,88],[1]),u5 [68] [1,8,10,11,12,15,16,17,24,37],a5 [70,91] [7,12,17,24,89,90] [0,1],a5 [14,91] [7,12,15,17,24,86] [0,1],u5 [5,6] [10,11,12,17,24,69],e5 [14,67] [4,10,15,91],e5 [95] [1,4,11,12,15,16],a5 [127,11] [4,10,12,16,17,92] [1],u5 [67] [1,4,11,12,15,16,91],u5 [5,9] [4,5,8,10,11,24],a5 [14,11] [4,10,12,15] [1],u5 [14,63] [12,15,17,24,41],u5 [72,13] [4,10,16,60],e5 [72,63] [4,5,10,11,12,15],([123,1,2,3,4],[5,7,12,83],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_13_6 : checkNodesBT W_13 g_13 F_13 P_13_6 A_13 B_13_5 6 N_13_6 = true := by decide +kernel
def B_13_6 : BT (List (List Nat)) := buildBucketsBT W_13 N_13_6
set_option maxRecDepth 500000 in
lemma B_13_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_13 6 xs.toFinset) B_13_6 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok (buildPoolsSubBT_sound S_13_ok) A_13_ok B_13_5_ok C_13_6
def U_13_7 : List Nat := ([1,4,5,7,8,10,11,12,15,16,17,24,35,41,50,57]++r 59 4++[66,69,71,86,88,90,93,94,95])
def P_13_7 : BT (Option BoundPool) := buildPoolsSubBT 7 W_13 r_13 S_13 ps_13 U_13_7
def N_13_7 : List NodeSpec := [a5 [9] [4,5,7,62] [0,1],u5 [130] [1,4,5,7,12,16,17],a5 [43] [1,4,5,7,17,93] [0,1],a5 [7] [1,4,5,7,16] [0,1],a5 [20] [1,8,12,16,17,24] [0,1],([0,1,3,4,7],[1,4,5,7],[0,1]),a5 [13] [1,7,8,12,17,24] [0,1],u5 [21] [1,5,12,16,17,24,71],([34,0,1,3,4],[1,4,5],[0,1]),a5 [15] [4,5,16,17,24,59] [0,1],a5 [76] [1,5,10,12,16,17,24,35,66] [0,1],a5 [131] [1,4,7,12,17] [1],a5 [5] [1,4,5,8,10,11,12,16,17,24,69] [0,1],a5 [70] [1,4,7,12,17,90] [0,1],a5 [81] [1,4,5,7,12,16,17,24,50] [0,1],a5 [127] [1,4,7,8,10,12,16,17] [0,1],a5 [103] [1,4,7,8,10,12,16,17,24,88] [0,1],a5 [14] [1,4,7,8,10,12,15,16,17,24,86] [0,1],u5 [105] [1,4,5,7,8,12,16,17,94],a5 [122] [1,5,7,12,16,17,24,41,95] [0,1],a5 [55] [1,4,5,8,12,16,24,61] [0,1],u5 [72] [1,4,5,8,12,16,24,60],a5 [50] [1,4,12,16,17,24,57] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_13_7 : checkNodesBT W_13 g_13 F_13 P_13_7 A_13 B_13_6 7 N_13_7 = true := by decide +kernel
def B_13_7 : BT (List (List Nat)) := buildBucketsBT W_13 N_13_7
set_option maxRecDepth 500000 in
lemma B_13_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_13 7 xs.toFinset) B_13_7 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok (buildPoolsSubBT_sound S_13_ok) A_13_ok B_13_6_ok C_13_7
def U_13_8 : List Nat := [1]
def P_13_8 : BT (Option BoundPool) := buildPoolsSubBT 7 W_13 r_13 S_13 ps_13 U_13_8
def N_13_8 : List NodeSpec := [a5 [] [1] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_13_8 : checkNodesBT W_13 g_13 F_13 P_13_8 A_13 B_13_7 8 N_13_8 = true := by decide +kernel
def B_13_8 : BT (List (List Nat)) := buildBucketsBT W_13 N_13_8
set_option maxRecDepth 500000 in
lemma B_13_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_13 8 xs.toFinset) B_13_8 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok (buildPoolsSubBT_sound S_13_ok) A_13_ok B_13_7_ok C_13_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_13_ok : forestRootCheck r_13 g_13 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11),(VAR 4,1,17)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_13_in : bucketContainsBT B_13_8 r_13 = true := by decide +kernel
lemma low_13 : Lower r_13 g_13 9 := lower_of_forestBT root_13_ok B_13_8_ok root_13_in
def g_14 := (d 0xfffefcc0fffefcc0)
def r_14 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_14 : Lower r_14 g_14 8 := by
  have hc : Lower (varsOf 30) (d 0xfffcfcc0fffcfcc0) 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,16,17)]) (by decide +kernel) hc
def g_15 := (d 0xfffefec0fffefec0)
def r_15 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_15 : Lower r_15 g_15 8 := by
  have hc : Lower (varsOf 30) (d 0xfffcfcc0fffcfcc0) 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,8,9)]) (by decide +kernel) hc
def g_16 := (d 0xfec0c000fec0c000)
def r_16 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_16 : Lower r_16 g_16 8 := by
  have hc : Lower (varsOf 30) (d 0xfcc0c000fcc0c000) 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,24,25)]) (by decide +kernel) hc
def g_17 := (d 0xfffce880fffce880)
def r_17 : List Nat := varsOf 31
def p_17 : List Nat := [7,7,7,11,11,11,13,13,13,14,14,14,18,18,19,19,20,20,21,21,22,24,24,25,25,26,28]
def q_17 : List Nat := [6,5,3,10,9,3,12,9,5,12,10,6,16,2,17,3,16,4,17,5,6,16,8,17,9,10,12]
def F_17 : Nat := fullMask 27
set_option maxHeartbeats 0 in
lemma gp_17 : goodPairs g_17 p_17 q_17 := goodPairs_of (by decide +kernel)
def W_17 : BT Decor := buildWiresBT 3 (mkBase p_17 q_17 r_17) [(0,1,2),(1,1,2),(2,1,3)]
lemma W_17_ok : btAll (fun x => faithful p_17 q_17 x ∧ x.1 < 2^256) W_17 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_17 : List (List (Nat × Nat)) := [[],[(2,3)],[(1,2)],[(1,3),(2,3)],[(1,2),(2,3)],[(1,3)]]
def A_17 : BT (List (Nat × Nat)) := btOfList 3 al_17
set_option maxHeartbeats 0 in
lemma A_17_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_17 = g_17) A_17 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_17_0 : Slice r_17 g_17 (subcubeFast 0 1) 7 := by
  have hc : Lower (varsOf 30) (d 0xfffcfcc0fffcfcc0) 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_1 : Slice r_17 g_17 (subcubeFast 16 0) 7 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_2
set_option maxHeartbeats 0 in
lemma sl_17_2 : Slice r_17 g_17 (subcubeFast 1 0) 6 := by
  have hc : Lower (varsOf 30) (d 0xfffcc000fffcc000) 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_3 : Slice r_17 g_17 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xfff0a000fff0a000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_4 : Slice r_17 g_17 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffffaa0fffffaa0) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_5 : Slice r_17 g_17 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) (d 0xffcc8800ffcc8800) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_6 : Slice r_17 g_17 (subcubeFast 0 4) 5 := by
  have hc : Lower (varsOf 27) (d 0xffffee88ffffee88) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_7 : Slice r_17 g_17 (subcubeFast 8 0) 5 := by
  have hc : Lower (varsOf 23) (d 0xfcfc8080fcfc8080) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_8 : Slice r_17 g_17 (subcubeFast 0 8) 5 := by
  have hc : Lower (varsOf 23) (d 0xffffe8e8ffffe8e8) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_9 : Slice r_17 g_17 (identDom 1 2) 5 := by
  have hc : Lower (varsOf 27) (d 0xffcccc88ffcccc88) 5 := carry_of (swaps := [(1,3),(2,4)]) (by decide +kernel) low_7
  exact slice_ident (u := 1) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_10 : Slice r_17 g_17 (identDom 1 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xfcfcc8c8fcfcc8c8) 5 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_7
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
def S_17 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 0 1,7),some (subcubeFast 16 0,7),some (subcubeFast 1 0,6),some (subcubeFast 2 0,5),some (subcubeFast 0 2,5),some (subcubeFast 4 0,5),some (subcubeFast 0 4,5),some (subcubeFast 8 0,5),some (subcubeFast 0 8,5),some (identDom 1 2,5),some (identDom 1 3,5)]
lemma S_17_ok : btAll (fun o => ∀ p, o = some p → Slice r_17 g_17 p.1 p.2) S_17 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_17_0) (forall_cons (fun _ h => by cases h; exact sl_17_1) (forall_cons (fun _ h => by cases h; exact sl_17_2) (forall_cons (fun _ h => by cases h; exact sl_17_3) (forall_cons (fun _ h => by cases h; exact sl_17_4) (forall_cons (fun _ h => by cases h; exact sl_17_5) (forall_cons (fun _ h => by cases h; exact sl_17_6) (forall_cons (fun _ h => by cases h; exact sl_17_7) (forall_cons (fun _ h => by cases h; exact sl_17_8) (forall_cons (fun _ h => by cases h; exact sl_17_9) (forall_cons (fun _ h => by cases h; exact sl_17_10) (fun _ h => (List.not_mem_nil h).elim))))))))))))
def ps_17 : BT (Option PoolSpec) := btOfList 5 [q 0 [8196,8197],q 4 [],q 1 [8196,8197],q 9 [],q 3 [],q 0 [12294],q 6 [],q 5 [],q 1 [12294],q 10 [],q 7 [],q 8 [],q 0 [8197],q 2 [],q 1 [8197],q 0 [8196],q 1 [8196],q 0 [],q 1 []]
def B_17_5 : BT (List (List Nat)) := BT.empty
lemma B_17_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 5 xs.toFinset) B_17_5 := .empty
def U_17_6 : List Nat := (r 0 5)
def P_17_6 : BT (Option BoundPool) := buildPoolsSubBT 5 W_17 r_17 S_17 ps_17 U_17_6
def N_17_6 : List NodeSpec := [([0,5,6,3,4],(r 0 5),[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_6 : checkNodesBT W_17 g_17 F_17 P_17_6 A_17 B_17_5 6 N_17_6 = true := by decide +kernel
def B_17_6 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_6
set_option maxRecDepth 500000 in
lemma B_17_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 6 xs.toFinset) B_17_6 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_5_ok C_17_6
def U_17_7 : List Nat := ([1]++r 4 13)
def P_17_7 : BT (Option BoundPool) := buildPoolsSubBT 5 W_17 r_17 S_17 ps_17 U_17_7
def N_17_7 : List NodeSpec := [e5 [7] ([1]++r 4 8),u5 [6] ([1,4,6,7]++r 10 5),u5 [5] [1,4,7,10,11,15,16]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_7 : checkNodesBT W_17 g_17 F_17 P_17_7 A_17 B_17_6 7 N_17_7 = true := by decide +kernel
def B_17_7 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_7
set_option maxRecDepth 500000 in
lemma B_17_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 7 xs.toFinset) B_17_7 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_6_ok C_17_7
def U_17_8 : List Nat := [17,18]
def P_17_8 : BT (Option BoundPool) := buildPoolsSubBT 5 W_17 r_17 S_17 ps_17 U_17_8
def N_17_8 : List NodeSpec := [a5 [] [17,18] [0,1,2,3,4,5]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_8 : checkNodesBT W_17 g_17 F_17 P_17_8 A_17 B_17_7 8 N_17_8 = true := by decide +kernel
def B_17_8 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_8
set_option maxRecDepth 500000 in
lemma B_17_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 8 xs.toFinset) B_17_8 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_7_ok C_17_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_17_ok : forestRootCheck r_17 g_17 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11),(VAR 4,2,18)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_17_in : bucketContainsBT B_17_8 r_17 = true := by decide +kernel
lemma low_17 : Lower r_17 g_17 9 := lower_of_forestBT root_17_ok B_17_8_ok root_17_in
def g_18 := (d 0xffe8c000ffe8c000)
def r_18 : List Nat := varsOf 31
def p_18 : List Nat := [14,14,14,15,15,15,19,19,19,21,21,21,22,22,22,23,24,24,25,25,26,26,27,28,28,29]
def q_18 : List Nat := [12,10,6,13,11,7,18,17,3,20,17,5,20,18,6,7,16,8,17,9,18,10,11,20,12,13]
def F_18 : Nat := fullMask 26
set_option maxHeartbeats 0 in
lemma gp_18 : goodPairs g_18 p_18 q_18 := goodPairs_of (by decide +kernel)
def W_18 : BT Decor := buildWiresBT 5 (mkBase p_18 q_18 r_18) [(0,2,4),(3,5,1),(2,2,3),(3,7,1),(0,1,2),(0,1,4),(2,1,3),(0,9,4),(3,9,4),(1,9,3),(0,0,4),(2,0,3)]
lemma W_18_ok : btAll (fun x => faithful p_18 q_18 x ∧ x.1 < 2^256) W_18 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_18 : List (List (Nat × Nat)) := [[],[(1,2)]]
def A_18 : BT (List (Nat × Nat)) := btOfList 1 al_18
set_option maxHeartbeats 0 in
lemma A_18_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_18 = g_18) A_18 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_18_0 : Slice r_18 g_18 (subcubeFast 0 1) 6 := by
  have hc : Lower (varsOf 30) (d 0xfffcc000fffcc000) 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_1 : Slice r_18 g_18 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xffc0c000ffc0c000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_2 : Slice r_18 g_18 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffaf000fffaf000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_3 : Slice r_18 g_18 (subcubeFast 0 4) 5 := by
  have hc : Lower (varsOf 27) (d 0xffeecc00ffeecc00) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_4 : Slice r_18 g_18 (subcubeFast 8 0) 5 := by
  have hc : Lower (varsOf 23) (d 0xe8e80000e8e80000) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_5 : Slice r_18 g_18 (subcubeFast 0 16) 5 := by
  exact slice_fast_direct_f (z := 0) (o := 16) (by decide +kernel) low_3
set_option maxHeartbeats 0 in
lemma sl_18_6 : Slice r_18 g_18 (subcubeFast 8 16) 4 := by
  exact slice_fast_direct_f (z := 8) (o := 16) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_18_7 : Slice r_18 g_18 (subcubeFast 1 4) 4 := by
  have hc : Lower (varsOf 26) (d 0xffcccc00ffcccc00) 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_8 : Slice r_18 g_18 (identDom 2 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xf8f8c0c0f8f8c0c0) 5 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_10
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
def S_18 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 0 1,6),some (subcubeFast 1 0,5),some (subcubeFast 0 2,5),some (subcubeFast 0 4,5),some (subcubeFast 8 0,5),some (subcubeFast 0 16,5),some (subcubeFast 8 16,4),some (subcubeFast 1 4,4),some (identDom 2 3,5)]
lemma S_18_ok : btAll (fun o => ∀ p, o = some p → Slice r_18 g_18 p.1 p.2) S_18 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_18_0) (forall_cons (fun _ h => by cases h; exact sl_18_1) (forall_cons (fun _ h => by cases h; exact sl_18_2) (forall_cons (fun _ h => by cases h; exact sl_18_3) (forall_cons (fun _ h => by cases h; exact sl_18_4) (forall_cons (fun _ h => by cases h; exact sl_18_5) (forall_cons (fun _ h => by cases h; exact sl_18_6) (forall_cons (fun _ h => by cases h; exact sl_18_7) (forall_cons (fun _ h => by cases h; exact sl_18_8) (fun _ h => (List.not_mem_nil h).elim))))))))))
def ps_18 : BT (Option PoolSpec) := btOfList 4 [q 3 [],q 5 [],q 4 [],q 0 [],q 1 [],q 8 [],q 0 [16388],q 6 [],q 2 [],q 0 [12294],q 0 [8196],q 7 []]
def B_18_4 : BT (List (List Nat)) := BT.empty
lemma B_18_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_18 4 xs.toFinset) B_18_4 := .empty
def U_18_5 : List Nat := (r 0 6)
def P_18_5 : BT (Option BoundPool) := buildPoolsSubBT 4 W_18 r_18 S_18 ps_18 U_18_5
def N_18_5 : List NodeSpec := [e5 [6] [],e5 [8] [],([0,9,10,2,3,4],[0,1],[]),([11,0,9,2,3,4],[0,2],[]),e5 [12] (r 2 4),e5 [13] [3,4],e5 [14] [3,4]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_18_5 : checkNodesBT W_18 g_18 F_18 P_18_5 A_18 B_18_4 5 N_18_5 = true := by decide +kernel
def B_18_5 : BT (List (List Nat)) := buildBucketsBT W_18 N_18_5
set_option maxRecDepth 500000 in
lemma B_18_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_18 5 xs.toFinset) B_18_5 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok (buildPoolsSubBT_sound S_18_ok) A_18_ok B_18_4_ok C_18_5
def U_18_6 : List Nat := (r 0 12)
def P_18_6 : BT (Option BoundPool) := buildPoolsSubBT 4 W_18 r_18 S_18 ps_18 U_18_6
def N_18_6 : List NodeSpec := [a5 [10] [0,6,7,8] [0,1],a5 [11] [0,2,5,7,8,9] [0,1],a5 [9] [1,2,4,5,8,10,11] [0,1],([15,1,2,3,4],[4,7,11],[]),([16,1,2,3,4],[3,4,7,11],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_18_6 : checkNodesBT W_18 g_18 F_18 P_18_6 A_18 B_18_5 6 N_18_6 = true := by decide +kernel
def B_18_6 : BT (List (List Nat)) := buildBucketsBT W_18 N_18_6
set_option maxRecDepth 500000 in
lemma B_18_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_18 6 xs.toFinset) B_18_6 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok (buildPoolsSubBT_sound S_18_ok) A_18_ok B_18_5_ok C_18_6
def U_18_7 : List Nat := (r 0 4++[7,8])
def P_18_7 : BT (Option BoundPool) := buildPoolsSubBT 4 W_18 r_18 S_18 ps_18 U_18_7
def N_18_7 : List NodeSpec := [a5 [] (r 0 4++[7,8]) [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_18_7 : checkNodesBT W_18 g_18 F_18 P_18_7 A_18 B_18_6 7 N_18_7 = true := by decide +kernel
def B_18_7 : BT (List (List Nat)) := buildBucketsBT W_18 N_18_7
set_option maxRecDepth 500000 in
lemma B_18_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_18 7 xs.toFinset) B_18_7 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok (buildPoolsSubBT_sound S_18_ok) A_18_ok B_18_6_ok C_18_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_18_ok : forestRootCheck r_18 g_18 [(VAR 0,18,19),(VAR 1,12,14),(VAR 2,10,14),(VAR 3,6,14),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_18_in : bucketContainsBT B_18_7 r_18 = true := by decide +kernel
lemma low_18 : Lower r_18 g_18 8 := lower_of_forestBT root_18_ok B_18_7_ok root_18_in
def g_19 := (d 0xfef0c800fef0c800)
def r_19 : List Nat := varsOf 31
def p_19 : List Nat := [11,11,11,14,14,14,15,15,20,20,21,21,22,22,23,23,25,25,25,26,26,26,27,28,28,29]
def q_19 : List Nat := [10,9,3,12,10,6,13,7,16,4,17,5,18,6,19,7,24,17,9,24,18,10,19,24,12,13]
def F_19 : Nat := fullMask 26
set_option maxHeartbeats 0 in
lemma gp_19 : goodPairs g_19 p_19 q_19 := goodPairs_of (by decide +kernel)
def W_19 : BT Decor := buildWiresBT 3 (mkBase p_19 q_19 r_19) []
lemma W_19_ok : btAll (fun x => faithful p_19 q_19 x ∧ x.1 < 2^256) W_19 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_19 : List (List (Nat × Nat)) := [[]]
def A_19 : BT (List (Nat × Nat)) := btOfList 1 al_19
set_option maxHeartbeats 0 in
lemma A_19_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_19 = g_19) A_19 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_19_0 : Slice r_19 g_19 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xfcf0c000fcf0c000) 5 := carry_of (swaps := [(0,4),(1,4),(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_19_1 : Slice r_19 g_19 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) (d 0xfff0fa00fff0fa00) 5 := carry_of (swaps := [(1,4),(2,4)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_19_2 : Slice r_19 g_19 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) (d 0xee008800ee008800) 5 := carry_of (swaps := [(2,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_19_3 : Slice r_19 g_19 (subcubeFast 0 8) 5 := by
  have hc : Lower (varsOf 23) (d 0xfefec8c8fefec8c8) 5 := carry_of (swaps := [(1,2),(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
def S_19 : BT (Option (Nat × Nat)) := btOfList 2 [some (subcubeFast 1 0,5),some (subcubeFast 0 2,5),some (subcubeFast 4 0,5),some (subcubeFast 0 8,5)]
lemma S_19_ok : btAll (fun o => ∀ p, o = some p → Slice r_19 g_19 p.1 p.2) S_19 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_19_0) (forall_cons (fun _ h => by cases h; exact sl_19_1) (forall_cons (fun _ h => by cases h; exact sl_19_2) (forall_cons (fun _ h => by cases h; exact sl_19_3) (fun _ h => (List.not_mem_nil h).elim)))))
def ps_19 : BT (Option PoolSpec) := btOfList 2 [q 0 [],q 2 [],q 3 [],q 1 []]
def B_19_5 : BT (List (List Nat)) := BT.empty
lemma B_19_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_19 5 xs.toFinset) B_19_5 := .empty
def U_19_6 : List Nat := (r 0 4)
def P_19_6 : BT (Option BoundPool) := buildPoolsSubBT 2 W_19 r_19 S_19 ps_19 U_19_6
def N_19_6 : List NodeSpec := [e5 [] (r 0 4)]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_19_6 : checkNodesBT W_19 g_19 F_19 P_19_6 A_19 B_19_5 6 N_19_6 = true := by decide +kernel
def B_19_6 : BT (List (List Nat)) := buildBucketsBT W_19 N_19_6
set_option maxRecDepth 500000 in
lemma B_19_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_19 6 xs.toFinset) B_19_6 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok (buildPoolsSubBT_sound S_19_ok) A_19_ok B_19_5_ok C_19_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_19_ok : forestRootCheck r_19 g_19 [(VAR 0,10,11),(VAR 1,9,11),(VAR 2,10,14),(VAR 3,3,11),(VAR 4,4,20)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_19_in : bucketContainsBT B_19_6 r_19 = true := by decide +kernel
lemma low_19 : Lower r_19 g_19 7 := lower_of_forestBT root_19_ok B_19_6_ok root_19_in
def g_20 := (d 0xffe0c000ffe0c000)
def r_20 : List Nat := varsOf 31
def p_20 : List Nat := [14,14,14,15,15,15,21,21,21,22,22,22,23,23,24,24,25,25,26,26,27,27,28,28,29]
def q_20 : List Nat := [12,10,6,13,11,7,20,17,5,20,18,6,19,7,16,8,17,9,18,10,19,11,20,12,13]
def F_20 : Nat := fullMask 25
set_option maxHeartbeats 0 in
lemma gp_20 : goodPairs g_20 p_20 q_20 := goodPairs_of (by decide +kernel)
def W_20 : BT Decor := buildWiresBT 4 (mkBase p_20 q_20 r_20) [(0,3,4),(1,3,4),(3,5,6),(0,2,6),(2,3,4),(3,3,4),(2,2,5),(2,1,5)]
lemma W_20_ok : btAll (fun x => faithful p_20 q_20 x ∧ x.1 < 2^256) W_20 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_20 : List (List (Nat × Nat)) := [[]]
def A_20 : BT (List (Nat × Nat)) := btOfList 1 al_20
set_option maxHeartbeats 0 in
lemma A_20_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_20 = g_20) A_20 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_20_0 : Slice r_20 g_20 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) (d 0xfff0c000fff0c000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_20_1 : Slice r_20 g_20 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xffc0c000ffc0c000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_20_2 : Slice r_20 g_20 (subcubeFast 0 4) 5 := by
  have hc : Lower (varsOf 27) (d 0xffeecc00ffeecc00) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_20_3 : Slice r_20 g_20 (subcubeFast 0 3) 4 := by
  have hc : Lower (varsOf 28) (d 0xfff0f000fff0f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 0) (o := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_20_4 : Slice r_20 g_20 (identDom 1 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xececc0c0ececc0c0) 5 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_10
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
def S_20 : BT (Option (Nat × Nat)) := btOfList 3 [some (subcubeFast 0 1,5),some (subcubeFast 1 0,5),some (subcubeFast 0 4,5),some (subcubeFast 0 3,4),some (identDom 1 3,5)]
lemma S_20_ok : btAll (fun o => ∀ p, o = some p → Slice r_20 g_20 p.1 p.2) S_20 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_20_0) (forall_cons (fun _ h => by cases h; exact sl_20_1) (forall_cons (fun _ h => by cases h; exact sl_20_2) (forall_cons (fun _ h => by cases h; exact sl_20_3) (forall_cons (fun _ h => by cases h; exact sl_20_4) (fun _ h => (List.not_mem_nil h).elim))))))
def ps_20 : BT (Option PoolSpec) := btOfList 3 [q 1 [],q 0 [],q 4 [],q 3 [],q 2 []]
def B_20_2 : BT (List (List Nat)) := BT.empty
lemma B_20_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_20 2 xs.toFinset) B_20_2 := .empty
def U_20_3 : List Nat := []
def P_20_3 : BT (Option BoundPool) := buildPoolsSubBT 3 W_20 r_20 S_20 ps_20 U_20_3
def N_20_3 : List NodeSpec := [([7,0,1,2],[],[]),([0,1,8,5],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_20_3 : checkNodesBT W_20 g_20 F_20 P_20_3 A_20 B_20_2 3 N_20_3 = true := by decide +kernel
def B_20_3 : BT (List (List Nat)) := buildBucketsBT W_20 N_20_3
set_option maxRecDepth 500000 in
lemma B_20_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_20 3 xs.toFinset) B_20_3 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok (buildPoolsSubBT_sound S_20_ok) A_20_ok B_20_2_ok C_20_3
def U_20_4 : List Nat := []
def P_20_4 : BT (Option BoundPool) := buildPoolsSubBT 3 W_20 r_20 S_20 ps_20 U_20_4
def N_20_4 : List NodeSpec := [([9,10,0,1,2],[],[0]),([0,1,8,3,4],[],[0]),([0,1,2,5,6],[],[0]),([11,0,1,3,4],[],[]),([12,0,2,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_20_4 : checkNodesBT W_20 g_20 F_20 P_20_4 A_20 B_20_3 4 N_20_4 = true := by decide +kernel
def B_20_4 : BT (List (List Nat)) := buildBucketsBT W_20 N_20_4
set_option maxRecDepth 500000 in
lemma B_20_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_20 4 xs.toFinset) B_20_4 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok (buildPoolsSubBT_sound S_20_ok) A_20_ok B_20_3_ok C_20_4
def U_20_5 : List Nat := (r 0 5)
def P_20_5 : BT (Option BoundPool) := buildPoolsSubBT 3 W_20 r_20 S_20 ps_20 U_20_5
def N_20_5 : List NodeSpec := [u5 [10] [0,1],u5 [9] [0,1],u5 [6] (r 0 5),u5 [5] [0,1,3,4]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_20_5 : checkNodesBT W_20 g_20 F_20 P_20_5 A_20 B_20_4 5 N_20_5 = true := by decide +kernel
def B_20_5 : BT (List (List Nat)) := buildBucketsBT W_20 N_20_5
set_option maxRecDepth 500000 in
lemma B_20_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_20 5 xs.toFinset) B_20_5 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok (buildPoolsSubBT_sound S_20_ok) A_20_ok B_20_4_ok C_20_5
def U_20_6 : List Nat := [0,1,3,4]
def P_20_6 : BT (Option BoundPool) := buildPoolsSubBT 3 W_20 r_20 S_20 ps_20 U_20_6
def N_20_6 : List NodeSpec := [u5 [] [0,1,3,4]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_20_6 : checkNodesBT W_20 g_20 F_20 P_20_6 A_20 B_20_5 6 N_20_6 = true := by decide +kernel
def B_20_6 : BT (List (List Nat)) := buildBucketsBT W_20 N_20_6
set_option maxRecDepth 500000 in
lemma B_20_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_20 6 xs.toFinset) B_20_6 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok (buildPoolsSubBT_sound S_20_ok) A_20_ok B_20_5_ok C_20_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_20_ok : forestRootCheck r_20 g_20 [(VAR 0,20,21),(VAR 1,12,14),(VAR 2,10,14),(VAR 3,6,14),(VAR 4,5,21)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_20_in : bucketContainsBT B_20_6 r_20 = true := by decide +kernel
lemma low_20 : Lower r_20 g_20 7 := lower_of_forestBT root_20_ok B_20_6_ok root_20_in
def g_21 := (d 0xfffce800fffce800)
def r_21 : List Nat := varsOf 31
def p_21 : List Nat := [11,11,11,13,13,13,14,14,14,15,18,18,19,19,20,20,21,21,22,23,24,24,25,25,26,28]
def q_21 : List Nat := [10,9,3,12,9,5,12,10,6,7,16,2,17,3,16,4,17,5,6,7,16,8,17,9,10,12]
def F_21 : Nat := fullMask 26
set_option maxHeartbeats 0 in
lemma gp_21 : goodPairs g_21 p_21 q_21 := goodPairs_of (by decide +kernel)
def W_21 : BT Decor := buildWiresBT 4 (mkBase p_21 q_21 r_21) [(1,1,4),(3,2,5),(1,1,2),(2,7,4),(3,2,3),(1,9,1),(1,7,4),(0,7,3),(1,2,4),(1,0,4),(3,0,3)]
lemma W_21_ok : btAll (fun x => faithful p_21 q_21 x ∧ x.1 < 2^256) W_21 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_21 : List (List (Nat × Nat)) := [[],[(1,2)]]
def A_21 : BT (List (Nat × Nat)) := btOfList 1 al_21
set_option maxHeartbeats 0 in
lemma A_21_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_21 = g_21) A_21 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_21_0 : Slice r_21 g_21 (subcubeFast 1 0) 6 := by
  have hc : Lower (varsOf 30) (d 0xfffcc000fffcc000) 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_1 : Slice r_21 g_21 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) (d 0xfffcfc00fffcfc00) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_2 : Slice r_21 g_21 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xfff0a000fff0a000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_3 : Slice r_21 g_21 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) (d 0xffcc8800ffcc8800) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_4 : Slice r_21 g_21 (subcubeFast 0 8) 5 := by
  have hc : Lower (varsOf 23) (d 0xffffe8e8ffffe8e8) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_5 : Slice r_21 g_21 (subcubeFast 16 0) 5 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_6
set_option maxHeartbeats 0 in
lemma sl_21_6 : Slice r_21 g_21 (subcubeFast 16 8) 4 := by
  exact slice_fast_direct_f (z := 16) (o := 8) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_21_7 : Slice r_21 g_21 (subcubeFast 4 1) 4 := by
  have hc : Lower (varsOf 26) (d 0xffcccc00ffcccc00) 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_8 : Slice r_21 g_21 (identDom 2 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xfcfce0e0fcfce0e0) 5 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_7
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
def S_21 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 1 0,6),some (subcubeFast 0 1,5),some (subcubeFast 2 0,5),some (subcubeFast 4 0,5),some (subcubeFast 0 8,5),some (subcubeFast 16 0,5),some (subcubeFast 16 8,4),some (subcubeFast 4 1,4),some (identDom 2 3,5)]
lemma S_21_ok : btAll (fun o => ∀ p, o = some p → Slice r_21 g_21 p.1 p.2) S_21 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_21_0) (forall_cons (fun _ h => by cases h; exact sl_21_1) (forall_cons (fun _ h => by cases h; exact sl_21_2) (forall_cons (fun _ h => by cases h; exact sl_21_3) (forall_cons (fun _ h => by cases h; exact sl_21_4) (forall_cons (fun _ h => by cases h; exact sl_21_5) (forall_cons (fun _ h => by cases h; exact sl_21_6) (forall_cons (fun _ h => by cases h; exact sl_21_7) (forall_cons (fun _ h => by cases h; exact sl_21_8) (fun _ h => (List.not_mem_nil h).elim))))))))))
def ps_21 : BT (Option PoolSpec) := btOfList 4 [q 0 [],q 1 [],q 8 [],q 4 [],q 2 [],q 5 [],q 0 [12299],q 3 [],q 6 [],q 0 [16389],q 0 [8197],q 7 [],q 2 [16385],q 4 [16385],q 2 [12291]]
def B_21_4 : BT (List (List Nat)) := BT.empty
lemma B_21_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_21 4 xs.toFinset) B_21_4 := .empty
def U_21_5 : List Nat := (r 0 6)
def P_21_5 : BT (Option BoundPool) := buildPoolsSubBT 4 W_21 r_21 S_21 ps_21 U_21_5
def N_21_5 : List NodeSpec := [e5 [6] [],e5 [8] [0,1],e5 [10] [],e5 [11] (r 0 4),e5 [12] [0,1],([0,1,7,3,4,13],[4,5],[]),([9,0,1,7,3,4],[3,4],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_21_5 : checkNodesBT W_21 g_21 F_21 P_21_5 A_21 B_21_4 5 N_21_5 = true := by decide +kernel
def B_21_5 : BT (List (List Nat)) := buildBucketsBT W_21 N_21_5
set_option maxRecDepth 500000 in
lemma B_21_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_21 5 xs.toFinset) B_21_5 :=
  buildBucketsBT_sound (by decide) gp_21 W_21_ok (buildPoolsSubBT_sound S_21_ok) A_21_ok B_21_4_ok C_21_5
def U_21_6 : List Nat := (r 0 15)
def P_21_6 : BT (Option BoundPool) := buildPoolsSubBT 4 W_21 r_21 S_21 ps_21 U_21_6
def N_21_6 : List NodeSpec := [u5 [9] [0,2,4,6,7,8],a5 [5] [4,7,8,9] [0,1],a5 [7] (r 1 5++[10,11]) [0,1],([1,2,3,4,14],[8,11,12,13],[]),([15,1,2,3,4],[0,1,8,11,14],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_21_6 : checkNodesBT W_21 g_21 F_21 P_21_6 A_21 B_21_5 6 N_21_6 = true := by decide +kernel
def B_21_6 : BT (List (List Nat)) := buildBucketsBT W_21 N_21_6
set_option maxRecDepth 500000 in
lemma B_21_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_21 6 xs.toFinset) B_21_6 :=
  buildBucketsBT_sound (by decide) gp_21 W_21_ok (buildPoolsSubBT_sound S_21_ok) A_21_ok B_21_5_ok C_21_6
def U_21_7 : List Nat := [0,3,4,5,7,8]
def P_21_7 : BT (Option BoundPool) := buildPoolsSubBT 4 W_21 r_21 S_21 ps_21 U_21_7
def N_21_7 : List NodeSpec := [a5 [] [0,3,4,5,7,8] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_21_7 : checkNodesBT W_21 g_21 F_21 P_21_7 A_21 B_21_6 7 N_21_7 = true := by decide +kernel
def B_21_7 : BT (List (List Nat)) := buildBucketsBT W_21 N_21_7
set_option maxRecDepth 500000 in
lemma B_21_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_21 7 xs.toFinset) B_21_7 :=
  buildBucketsBT_sound (by decide) gp_21 W_21_ok (buildPoolsSubBT_sound S_21_ok) A_21_ok B_21_6_ok C_21_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_21_ok : forestRootCheck r_21 g_21 [(VAR 0,10,11),(VAR 1,9,11),(VAR 2,9,13),(VAR 3,3,11),(VAR 4,2,18)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_21_in : bucketContainsBT B_21_7 r_21 = true := by decide +kernel
lemma low_21 : Lower r_21 g_21 8 := lower_of_forestBT root_21_ok B_21_7_ok root_21_in
def g_22 := (d 0xfffef800fffef800)
def r_22 : List Nat := varsOf 31
def p_22 : List Nat := [11,11,11,12,12,13,13,14,14,15,17,17,18,18,19,20,20,21,22,23,24,24,25,26]
def q_22 : List Nat := [10,9,3,8,4,9,5,10,6,7,16,1,16,2,3,16,4,5,6,7,16,8,9,10]
def F_22 : Nat := fullMask 24
set_option maxHeartbeats 0 in
lemma gp_22 : goodPairs g_22 p_22 q_22 := goodPairs_of (by decide +kernel)
def W_22 : BT Decor := buildWiresBT 6 (mkBase p_22 q_22 r_22) [(0,3,4),(1,2,5),(1,0,6),(1,1,6),(1,3,4),(3,6,9),(3,5,9),(2,11,1),(3,2,9),(1,1,3),(1,14,4),(3,1,15),(1,0,3),(0,17,4),(1,2,18),(2,0,5),(1,1,5),(2,13,1),(2,13,0),(1,0,5),(0,0,9),(0,11,0),(2,0,6),(3,3,4),(1,28,0),(2,29,1),(2,3,4),(0,13,0),(3,0,3),(3,33,4),(3,1,4),(3,1,3),(1,36,4),(1,35,3),(1,33,1),(3,0,4),(1,40,3),(3,1,41),(1,1,18),(1,17,4),(3,2,44),(3,1,44),(3,2,38),(3,0,44),(0,14,4),(1,1,4),(1,31,0),(3,14,4),(2,17,4),(3,40,3),(1,0,4),(3,1,55),(0,3,55),(3,3,55)]
lemma W_22_ok : btAll (fun x => faithful p_22 q_22 x ∧ x.1 < 2^256) W_22 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_22 : List (List (Nat × Nat)) := [[],[(0,1)]]
def A_22 : BT (List (Nat × Nat)) := btOfList 1 al_22
set_option maxHeartbeats 0 in
lemma A_22_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_22 = g_22) A_22 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_22_0 : Slice r_22 g_22 (subcubeFast 4 0) 6 := by
  have hc : Lower (varsOf 27) (d 0xffee8800ffee8800) 6 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_1 : Slice r_22 g_22 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffaf000fffaf000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_2 : Slice r_22 g_22 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xfffcf000fffcf000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_3 : Slice r_22 g_22 (subcubeFast 3 0) 4 := by
  have hc : Lower (varsOf 28) (d 0xfff0f000fff0f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 3) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_4 : Slice r_22 g_22 (identDom 1 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xfefec8c8fefec8c8) 5 := carry_of (swaps := [(1,2),(3,4)]) (by decide +kernel) low_8
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_5 : Slice r_22 g_22 (identDom 0 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xfefea8a8fefea8a8) 5 := carry_of (swaps := [(0,2),(1,2),(3,4)]) (by decide +kernel) low_8
  exact slice_ident (u := 0) (v := 3) (by decide +kernel) hc
def S_22 : BT (Option (Nat × Nat)) := btOfList 3 [some (subcubeFast 4 0,6),some (subcubeFast 2 0,5),some (subcubeFast 1 0,5),some (subcubeFast 3 0,4),some (identDom 1 3,5),some (identDom 0 3,5)]
lemma S_22_ok : btAll (fun o => ∀ p, o = some p → Slice r_22 g_22 p.1 p.2) S_22 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_22_0) (forall_cons (fun _ h => by cases h; exact sl_22_1) (forall_cons (fun _ h => by cases h; exact sl_22_2) (forall_cons (fun _ h => by cases h; exact sl_22_3) (forall_cons (fun _ h => by cases h; exact sl_22_4) (forall_cons (fun _ h => by cases h; exact sl_22_5) (fun _ h => (List.not_mem_nil h).elim)))))))
def ps_22 : BT (Option PoolSpec) := btOfList 5 [q 0 [16396,16397,36887],q 0 [16396,16397],q 1 [],q 0 [16398,16399],q 2 [],q 0 [],q 3 [],q 0 [16397,36864],q 5 [],q 0 [16396,20485],q 0 [16397,36871],q 2 [16391],q 0 [12291,4229],q 0 [16396,20482],q 2 [12293],q 4 [],q 0 [16385,225287],q 2 [225287],q 0 [16399],q 0 [16398],q 0 [16397],q 0 [16396],q 0 [16391],q 0 [16385],q 0 [12295],q 1 [12289],q 0 [12289]]
def B_22_1 : BT (List (List Nat)) := BT.empty
lemma B_22_1_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 1 xs.toFinset) B_22_1 := .empty
def U_22_2 : List Nat := []
def P_22_2 : BT (Option BoundPool) := buildPoolsSubBT 5 W_22 r_22 S_22 ps_22 U_22_2
def N_22_2 : List NodeSpec := [([7,8,9],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_2 : checkNodesBT W_22 g_22 F_22 P_22_2 A_22 B_22_1 2 N_22_2 = true := by decide +kernel
def B_22_2 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_2
set_option maxRecDepth 500000 in
lemma B_22_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 2 xs.toFinset) B_22_2 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_1_ok C_22_2
def U_22_3 : List Nat := []
def P_22_3 : BT (Option BoundPool) := buildPoolsSubBT 5 W_22 r_22 S_22 ps_22 U_22_3
def N_22_3 : List NodeSpec := [([10,11,0,1],[],[]),([12,11,0,2],[],[]),([11,13,0,1],[],[]),([11,16,0,2],[],[]),([11,0,1,2],[],[]),([0,1,19,9],[],[]),([20,11,1,2],[],[]),([0,21,6,9],[],[]),([22,23,3,4],[],[]),([2,24,21,9],[],[]),([11,0,2,21],[],[]),([11,0,1,6],[],[]),([20,1,6,9],[],[]),([11,25,1,2],[],[]),([3,7,8,4],[],[0]),([10,0,1,9],[],[]),([25,1,6,9],[],[]),([16,0,6,9],[],[]),([26,11,1,2],[],[]),([0,6,8,9],[],[0]),([27,1,6,9],[],[]),([0,1,6,9],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_3 : checkNodesBT W_22 g_22 F_22 P_22_3 A_22 B_22_2 3 N_22_3 = true := by decide +kernel
def B_22_3 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_3
set_option maxRecDepth 500000 in
lemma B_22_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 3 xs.toFinset) B_22_3 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_2_ok C_22_3
def U_22_4 : List Nat := [0,1]
def P_22_4 : BT (Option BoundPool) := buildPoolsSubBT 5 W_22 r_22 S_22 ps_22 U_22_4
def N_22_4 : List NodeSpec := [([13,0,1,3,4],[],[]),([0,1,3,6,4],[],[0]),([22,13,0,3,4],[],[0]),([13,16,0,3,4],[],[]),([13,25,1,3,4],[],[]),([30,0,2,3,4],[],[]),([16,25,2,3,4],[],[]),([11,0,1,2,4],[],[]),([11,0,1,2,3],[],[]),([11,0,1,2],[0],[0,1]),([13,0,1,5,9],[],[0]),([16,0,2,5,9],[],[0]),([31,28,0,1,2],[],[0]),([32,13,1,3,4],[],[]),([25,1,2,5,9],[],[0]),([0,1,2,5,9],[],[0]),([0,1,5,6,9],[],[0,1]),([0,1,6,9],[1],[0,1]),([31,0,34,1,2],[],[]),([20,1,3,6,4],[],[0]),([35,0,2,3,37],[],[]),([28,11,0,1,2],[],[]),([0,1,3,6,9],[],[]),([36,0,2,38,4],[],[]),([0,39,2,4,9],[],[]),([28,0,1,3,6],[],[0]),([31,11,0,1,2],[],[]),([42,0,2,3,4],[],[]),([16,0,2,3,4],[],[]),([0,1,3,19,4],[],[0]),([11,0,1,2,5],[0],[0,1]),([0,2,3,43,4],[],[]),([45,0,1,3,4],[],[]),([0,1,2,18,9],[],[0]),([46,0,2,3,4],[],[]),([47,0,1,3,4],[],[]),([11,0,1,2,9],[0],[0,1]),([31,0,2,21,4],[],[]),([0,2,21,4,9],[],[]),([0,3,21,6,4],[],[0]),([16,48,2,3,4],[],[]),([20,2,3,21,4],[],[]),([31,0,39,2,4],[],[]),([0,2,5,21,9],[],[0]),([20,1,2,5,9],[],[0]),([2,3,24,21,4],[],[0]),([0,3,6,8,4],[],[0]),([0,2,3,49,50],[],[]),([31,0,1,6,4],[],[0]),([27,1,3,6,4],[],[0]),([0,1,6,4,9],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_4 : checkNodesBT W_22 g_22 F_22 P_22_4 A_22 B_22_3 4 N_22_4 = true := by decide +kernel
def B_22_4 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_4
set_option maxRecDepth 500000 in
lemma B_22_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 4 xs.toFinset) B_22_4 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_3_ok C_22_4
def U_22_5 : List Nat := (r 1 17)
def P_22_5 : BT (Option BoundPool) := buildPoolsSubBT 5 W_22 r_22 S_22 ps_22 U_22_5
def N_22_5 : List NodeSpec := [u5 [29] [2],([31,28,0,1,2,4],[],[0]),([31,28,0,1,2],[3],[0]),a5 [9] [2,4,5] [0,1],e5 [51] [],e5 [16] [],([13,0,1,3,4],[],[0,1]),([25,1,2,3,4,9],[6,7],[0,1]),([31,28,0,1,2,3],[],[0]),([0,1,2,5,3,9],[],[0]),u5 [28] [],([31,36,0,1,2,4],[2],[1]),a5 [18] [2,5,8] [0,1],([0,2,5,3,21,4],[2,9],[0]),([0,1,3,6,4],[],[0,1]),u5 [37] [],([36,0,1,2,4,9],[2],[1]),e5 [52] [],([28,0,1,2,4,9],[5],[0]),e5 [53] [],([16,0,2,3,4],[10],[]),e5 [54] [],([36,35,0,2,3,4],[11],[0]),a5 [44] [2,5] [0,1],a5 [38] [4,5] [0,1],([31,0,1,2,3,9],[5],[0]),([0,39,2,3,4],[12],[0]),([20,1,2,5,3,4],[6,8,13],[0]),([31,0,1,2,17,4],[4],[]),([16,0,2,3,4,9],[2,10],[0]),([35,0,2,3,4,50],[2,11],[]),([0,2,3,14,4,50],[14,15],[0]),e5 [24] [],u5 [34] [4],([31,0,1,2,5,4],[5],[0,1]),([0,1,2,17,4,9],[4],[0]),([56,0,2,3,4],[16],[]),([0,1,2,5,4,9],[],[0,1]),([0,2,3,21,4],[9],[0]),([56,0,2,3,4,55],[2,17],[]),u5 [5] [2,4,5,8,15],([0,1,2,5,9],[1],[0,1]),([0,1,5,3,6,4],[5],[0,1]),e5 [57] [8],e5 [58] [],u5 [31] [],([13,0,1,3,4,9],[5],[0,1]),([28,0,1,2,5,3],[5],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_5 : checkNodesBT W_22 g_22 F_22 P_22_5 A_22 B_22_4 5 N_22_5 = true := by decide +kernel
def B_22_5 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_5
set_option maxRecDepth 500000 in
lemma B_22_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 5 xs.toFinset) B_22_5 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_4_ok C_22_5
def U_22_6 : List Nat := ([2,4,5,6,8,15]++r 18 9)
def P_22_6 : BT (Option BoundPool) := buildPoolsSubBT 5 W_22 r_22 S_22 ps_22 U_22_6
def N_22_6 : List NodeSpec := [a5 [28] [2,4,5,18] [0,1],a5 [31] [2,4,5,8,15,19] [0,1],a5 [9] [2,4,20] [0,1],a5 [5] [2,4,8,15,21] [0,1],a5 [35] [4,5,6,15,22] [0,1],a5 [55] [6,8,23] [0,1],a5 [36] [4,6,15,24] [0,1],a5 [17] [4,6,8,25,26] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_6 : checkNodesBT W_22 g_22 F_22 P_22_6 A_22 B_22_5 6 N_22_6 = true := by decide +kernel
def B_22_6 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_6
set_option maxRecDepth 500000 in
lemma B_22_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 6 xs.toFinset) B_22_6 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_5_ok C_22_6
def U_22_7 : List Nat := [2,5,6]
def P_22_7 : BT (Option BoundPool) := buildPoolsSubBT 5 W_22 r_22 S_22 ps_22 U_22_7
def N_22_7 : List NodeSpec := [a5 [] [2,5,6] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_7 : checkNodesBT W_22 g_22 F_22 P_22_7 A_22 B_22_6 7 N_22_7 = true := by decide +kernel
def B_22_7 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_7
set_option maxRecDepth 500000 in
lemma B_22_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 7 xs.toFinset) B_22_7 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_6_ok C_22_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_22_ok : forestRootCheck r_22 g_22 [(VAR 0,10,11),(VAR 1,9,11),(VAR 2,8,12),(VAR 3,3,11),(VAR 4,1,17)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_22_in : bucketContainsBT B_22_7 r_22 = true := by decide +kernel
lemma low_22 : Lower r_22 g_22 8 := lower_of_forestBT root_22_ok B_22_7_ok root_22_in
def g_23 := (d 0xfffeffc8fce0c000)
def r_23 : List Nat := varsOf 63
def p_23 : List Nat := [14,14,14,15,15,15,21,21,21,22,22,22,23,23,26,26,26,27,27,27,28,28,28,29,29,35,35,35,38,38,38,39,39,40,40,41,41,42,42,43,44,44,45,45,49,49,49,50,50,50,51,52,52,52,53,56,56,57]
def q_23 : List Nat := [12,10,6,13,11,7,20,17,5,20,18,6,19,7,24,18,10,25,19,11,24,20,12,25,13,34,33,3,36,34,6,37,7,32,8,33,9,34,10,11,36,12,37,13,48,33,17,48,34,18,19,48,36,20,37,48,24,25]
def F_23 : Nat := fullMask 58
set_option maxHeartbeats 0 in
lemma gp_23 : goodPairs g_23 p_23 q_23 := goodPairs_of (by decide +kernel)
def W_23 : BT Decor := buildWiresBT 10 (mkBase p_23 q_23 r_23) [(0,1,2),(1,1,2),(3,6,7),(0,8,5),(1,8,5),(3,9,10),(0,11,4),(1,11,4),(3,12,13),(0,2,5),(1,2,5),(3,15,16),(0,1,4),(1,1,4),(3,18,19),(2,17,20),(3,17,20),(0,17,20),(1,17,20),(2,20,5),(2,25,2),(3,20,5),(1,26,27),(3,25,2),(3,11,4),(1,30,3),(0,20,5),(1,20,5),(3,32,33),(0,34,2),(1,34,2),(0,4,5),(1,4,5),(3,37,38),(0,39,8),(1,39,8),(2,11,4),(3,39,8),(1,43,3),(3,34,2),(1,45,3),(3,3,16),(3,47,20),(1,20,3),(3,48,49),(2,34,2),(0,25,2),(1,25,2),(3,52,53),(2,39,8),(1,52,27),(1,22,3),(1,26,3),(1,3,5),(0,2,59),(1,18,60),(1,2,59),(0,19,62),(3,60,62),(2,17,3),(2,20,3),(2,66,5),(1,67,3),(2,2,3),(1,69,5),(1,17,3),(1,2,3),(0,20,72),(1,73,5),(1,18,5),(3,3,75),(1,18,2),(3,18,71),(1,3,4),(0,8,79),(2,8,3),(0,81,5),(1,82,3),(0,8,59),(0,81,4),(1,85,3),(0,20,59),(0,20,2),(1,88,5),(1,3,37),(0,8,90),(1,8,3),(2,2,5),(3,93,20),(1,94,3),(1,0,3),(1,15,3),(0,20,97),(1,88,75),(3,3,99),(3,3,5),(2,77,3),(1,102,5),(1,88,3),(2,49,5),(2,20,2),(1,106,3),(2,107,5),(3,15,49),(1,32,3),(0,4,62),(1,1,111),(3,60,112),(2,17,1),(3,114,79),(0,17,1),(0,17,79),(2,39,1),(1,118,69),(1,39,1),(3,69,120),(0,1,5),(1,1,5),(3,122,123),(2,124,2),(3,125,79),(1,124,2),(0,127,79),(3,1,4),(3,129,71),(2,1,4),(3,60,19),(0,71,19),(3,18,59),(0,134,2),(1,134,2),(3,135,136),(3,3,4),(1,138,116),(0,19,16),(1,3,140),(2,141,5),(3,18,141),(1,18,15),(2,144,3),(1,18,3),(1,15,146),(3,18,97),(3,18,70),(1,88,18),(2,150,5),(0,20,62),(2,124,3),(3,2,4),(1,153,154),(1,93,3),(0,20,156),(2,20,15),(1,158,3),(0,20,16),(3,69,20),(1,161,5),(1,25,69),(2,72,5),(3,164,20),(3,116,79),(2,17,0),(3,131,17),(3,2,5),(2,66,169),(3,18,156),(0,20,70),(2,66,15),(3,93,49),(3,169,20),(1,175,3),(1,0,18),(2,92,37),(0,25,72),(2,39,2),(2,1,3),(1,180,181),(3,69,75),(1,1,3),(0,17,184),(0,17,4),(1,106,5),(1,138,114),(1,169,3),(0,20,189),(0,77,59),(3,18,5),(0,7,79),(0,193,5),(1,193,5),(3,194,195),(3,169,49),(2,17,4),(3,198,184),(3,3,89),(0,79,16),(0,1,201),(1,1,201),(3,202,203),(2,39,3),(3,205,7),(2,8,37),(0,7,59),(0,208,4),(1,208,4),(3,209,210),(2,77,5),(1,212,3),(1,198,181),(2,81,37),(3,93,66),(1,69,18),(2,217,5),(1,207,3),(1,167,3),(0,132,62),(1,39,2),(3,181,222),(3,8,5),(3,69,140),(1,39,3),(0,7,226),(3,154,124),(0,124,4),(1,69,229),(2,2,59),(3,2,59),(1,69,32),(3,0,70),(1,160,3),(3,8,4),(1,236,3),(3,32,72),(0,49,16),(1,81,37),(0,8,4),(3,241,59),(3,236,59),(1,181,186),(3,9,79),(3,224,79),(1,101,88),(2,102,5),(1,93,146),(3,131,71),(3,101,77),(1,101,18),(1,3,75),(3,88,59),(1,69,75),(0,17,96),(1,124,3),(3,154,257),(1,93,18),(2,259,3),(1,104,5),(2,25,69),(1,101,106),(1,228,0),(2,17,18),(1,88,192),(1,69,192),(2,20,0),(3,124,4),(1,69,269),(3,0,89),(0,66,16),(3,186,184),(0,20,96),(2,104,5),(1,107,5),(3,131,62),(0,19,59),(0,2,278),(1,2,278),(3,279,280),(3,25,72),(3,3,187),(3,106,59),(3,25,49),(1,268,3),(3,39,1),(0,39,1),(0,39,2),(0,4,59),(1,4,59),(3,290,291),(1,1,290),(2,1,111),(0,1,59),(1,1,59),(3,295,296),(3,297,4),(0,297,4),(1,17,4),(1,17,1),(3,122,1),(1,302,0),(3,1,5),(0,79,123),(3,2,305),(0,2,4),(1,122,307),(1,2,4),(0,124,79),(2,124,307),(3,69,124),(2,124,4),(0,124,2),(1,231,295),(1,231,131),(0,124,309),(2,17,129),(3,39,2),(3,231,19),(3,60,4),(1,231,278),(3,3,19),(1,323,5),(3,101,324),(0,17,19),(3,0,140),(3,134,2),(1,328,3),(0,18,59),(1,231,330),(1,0,97),(3,18,332),(1,0,144),(2,334,3),(3,18,62),(3,3,140),(3,17,1),(1,32,18),(3,101,20),(2,2,278),(3,2,278),(3,17,4),(3,138,17),(1,2,305),(1,27,2),(3,81,5),(0,2,75),(2,2,75),(3,18,2),(2,1,2),(2,39,351),(2,177,3),(0,39,7),(2,8,5),(2,193,5),(3,193,5),(3,4,5),(3,358,8),(3,181,17),(1,6,37),(3,3,361),(3,3,195),(3,1,59),(2,8,4),(1,308,3),(1,8,4),(0,96,140),(3,302,96),(0,309,59),(1,1,370),(2,2,4),(3,372,124),(3,134,16),(3,1,2),(3,37,4),(3,18,96),(3,144,96),(1,3,361),(3,124,2),(1,327,3),(2,292,1),(1,292,1),(3,6,90),(3,81,4),(2,39,6),(2,1,209),(0,2,291),(2,39,69),(2,134,2),(2,39,181),(3,1,370),(2,208,4),(3,208,4),(3,129,59),(3,131,59),(2,39,375),(3,27,2),(2,1,201),(3,1,201),(1,328,5),(1,224,3),(0,8,38),(1,192,3),(1,124,4),(1,20,2),(3,376,8),(2,406,5),(3,20,2),(1,364,18),(1,409,5),(2,303,3),(1,376,2),(3,2,90),(3,1,90),(0,1,90),(0,2,90),(1,231,290),(3,4,59),(3,1,62),(1,2,290),(1,376,1),(3,419,1),(3,2,291),(0,1,291),(3,364,4),(1,304,3),(1,307,5),(0,72,4),(1,122,429),(0,7,4),(3,419,296),(3,154,1),(0,7,38),(1,434,3),(1,6,5),(0,79,436),(3,358,436),(1,122,3),(3,93,19),(3,376,1),(0,1,309),(3,304,309),(3,302,4),(3,376,2),(1,304,307),(1,154,304),(3,3,123),(0,309,123),(3,431,59),(1,93,131),(3,419,7),(3,351,90),(0,7,90),(3,3,449),(2,181,5),(3,442,59),(1,376,3),(1,295,2),(3,375,90),(1,154,122),(1,6,290),(1,154,364),(3,154,123),(1,181,2),(3,376,465),(3,351,4),(1,467,3),(3,302,184),(3,364,309),(1,131,15),(3,181,5),(2,308,3),(3,131,16),(3,231,4),(0,4,16),(0,184,4),(1,15,477),(1,3,476),(3,304,428),(1,6,3),(1,0,481),(3,3,482),(2,7,3),(1,484,5),(1,358,3),(2,47,0),(1,302,3),(3,6,59),(1,181,4),(3,93,490),(3,351,59),(1,351,290),(0,1,72),(1,494,37),(1,307,472),(3,295,4),(3,18,16),(3,302,2),(1,129,3),(1,231,18),(3,154,59),(1,3,444),(3,0,428),(3,433,59),(1,138,1),(3,93,506),(2,7,290),(1,295,307),(1,131,60),(3,4,62),(0,1,428),(0,1,62),(1,3,449),(0,4,123),(1,302,2),(1,154,295),(1,302,4),(2,434,3),(3,3,309),(1,520,5),(0,1,79),(1,522,15),(3,93,4),(0,4,296),(2,138,5),(1,526,295),(1,441,3),(0,1,38),(1,529,3),(2,1,37),(1,531,3),(3,526,1),(3,3,38),(2,534,0),(3,231,1),(1,181,5),(2,184,5),(3,1,291),(3,138,1),(1,540,5),(2,506,5),(3,376,79),(1,522,5),(3,169,1),(1,545,3),(3,358,1),(1,547,3),(3,93,1),(0,1,16),(1,138,15),(3,15,79),(3,15,4),(2,1,15),(1,554,3),(1,154,5),(3,3,556),(1,154,3),(2,558,5),(3,169,4),(1,560,3),(1,433,5),(1,372,101),(3,372,59),(2,422,3),(1,372,3),(2,566,5),(1,566,5),(3,372,1),(1,569,5),(1,569,3),(2,309,5),(1,572,3),(2,520,5),(1,442,3),(1,307,3),(2,576,5),(1,576,5),(2,1,307),(1,579,3),(1,376,69),(3,69,38),(3,69,1),(2,1,60),(1,583,5),(3,376,72),(0,72,38),(2,72,37),(3,304,4),(2,79,5),(3,302,79),(1,579,5),(1,302,372),(3,302,309),(3,69,4),(1,302,69),(1,0,488),(3,138,16),(3,138,123),(1,550,3),(1,138,169),(0,72,123),(1,138,122),(3,122,79),(1,372,122),(3,122,309),(1,372,304),(3,122,4),(1,538,0),(1,477,5),(3,154,184),(1,372,5),(2,184,37),(3,304,79),(1,0,566),(3,456,4),(3,6,4),(1,617,3),(2,18,5),(1,619,3),(0,2,19),(3,375,79),(1,375,5),(3,0,623),(3,375,4),(1,625,5),(3,138,38),(1,375,3),(2,628,5),(3,3,428),(1,442,5),(1,129,15),(2,465,5),(3,372,184),(1,351,5),(3,3,635),(3,169,184),(1,376,351),(1,467,5),(1,138,6),(1,351,3),(1,641,5),(3,358,7),(3,376,7),(3,101,7),(2,481,5),(1,138,2),(2,647,5),(0,184,16),(1,358,6),(3,181,16),(1,138,5),(2,19,5),(3,138,7),(3,69,19),(2,7,5),(1,101,154),(3,122,72),(3,101,309),(1,3,515),(1,431,5),(1,433,3),(3,6,79),(3,6,38),(3,351,38),(1,431,3),(3,0,652),(1,181,307),(2,484,5),(0,184,309),(1,169,129),(3,307,59),(1,129,5),(3,0,673),(1,302,307),(1,375,37),(1,358,375),(3,169,79),(2,7,37),(1,358,181),(1,429,5),(3,307,184),(2,641,5),(3,93,184),(3,351,79),(1,653,3),(1,625,3),(2,490,5),(3,181,4),(3,375,38),(3,2,19),(1,69,129),(1,358,351),(1,656,3),(3,472,4),(1,131,101),(3,93,79),(1,494,5),(3,3,673),(1,0,146),(1,131,69),(1,376,375),(3,3,623),(1,131,3),(1,704,5),(3,129,16),(3,4,436),(3,304,72),(1,558,5),(0,181,4),(3,376,184),(3,375,59),(1,101,375),(1,481,5),(1,69,122),(2,323,5),(1,617,5),(0,4,436),(1,628,5),(0,465,4),(1,302,138),(1,101,6),(3,358,184),(0,184,38),(1,181,169),(1,689,5),(3,181,123),(3,69,123),(2,500,5),(3,181,309),(1,131,169),(1,372,181),(1,93,129),(1,181,154),(3,1,428),(1,93,181),(1,181,37),(1,376,181),(1,101,307),(1,101,351),(3,15,184),(3,101,19),(1,500,5),(1,69,37),(1,3,524),(2,146,5),(1,549,3),(1,138,304),(1,138,375),(1,595,5),(1,69,304),(3,3,436),(3,18,72),(3,358,72),(1,589,3),(1,169,18),(3,131,72),(3,129,72),(0,72,19),(1,93,138),(3,15,19),(3,181,38),(1,181,15),(3,169,19),(2,323,0),(1,358,69),(3,307,123),(1,710,5),(1,131,5),(3,3,769),(1,138,351),(3,302,72),(1,351,37),(3,3,612),(3,372,123),(1,553,3),(1,302,154),(2,704,5),(1,376,6),(1,101,129),(1,608,3),(3,101,1),(3,138,5),(3,138,2),(3,101,4),(3,181,2)]
lemma W_23_ok : btAll (fun x => faithful p_23 q_23 x ∧ x.1 < 2^256) W_23 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_23 : List (List (Nat × Nat)) := [[]]
def A_23 : BT (List (Nat × Nat)) := btOfList 1 al_23
set_option maxHeartbeats 0 in
lemma A_23_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_23 = g_23) A_23 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_23_0 : Slice r_23 g_23 (subcubeFast 1 0) 10 := by
  have hc : Lower (varsOf 62) (d 0xfffcffc0fcc0c000) 10 := carry_of (swaps := [(0,5),(1,5),(2,5),(4,5)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_1 : Slice r_23 g_23 (subcubeFast 8 0) 9 := by
  have hc : Lower (varsOf 55) (d 0xfefec8c8e0e00000) 9 := carry_of (swaps := [(3,5),(4,5)]) (by decide +kernel) low_12
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_2 : Slice r_23 g_23 (subcubeFast 0 1) 9 := by
  have hc : Lower (varsOf 62) (d 0xffffffccfcf0c000) 9 := carry_of (swaps := [(0,5),(1,5),(3,5),(4,5)]) (by decide +kernel) low_13
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_3 : Slice r_23 g_23 (subcubeFast 0 4) 8 := by
  have hc : Lower (varsOf 59) (d 0xffffffccffeecc00) 8 := carry_of (swaps := [(2,5),(3,5)]) (by decide +kernel) low_14
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_4 : Slice r_23 g_23 (subcubeFast 0 2) 8 := by
  have hc : Lower (varsOf 61) (d 0xfffffffafff0f000) 8 := carry_of (swaps := [(1,5),(2,5),(3,5),(4,5)]) (by decide +kernel) low_14
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_5 : Slice r_23 g_23 (subcubeFast 0 16) 8 := by
  have hc : Lower (varsOf 47) (d 0xfffefffefce0fce0) 8 := carry_of (swaps := [(2,3),(4,5)]) (by decide +kernel) low_15
  exact slice_fast_direct_f (z := 0) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_6 : Slice r_23 g_23 (subcubeFast 32 0) 8 := by
  have hc : Lower (varsOf 31) (d 0xfce0c000fce0c000) 8 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_16
  exact slice_fast_direct_f (z := 32) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_7 : Slice r_23 g_23 (identDom 0 5) 9 := by
  have hc : Lower (varsOf 31) (d 0xfeeaea88feeaea88) 9 := carry_of (swaps := [(0,4),(2,4),(3,4)]) (by decide +kernel) low_17
  exact slice_ident (u := 0) (v := 5) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_8 : Slice r_23 g_23 (subcubeFast 1 2) 7 := by
  have hc : Lower (varsOf 60) (d 0xfffffff0fff0f000) 7 := carry_of (swaps := [(0,4),(1,5),(2,4),(3,5)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 1) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_9 : Slice r_23 g_23 (subcubeFast 1 4) 7 := by
  have hc : Lower (varsOf 58) (d 0xffffffccffcccc00) 7 := carry_of (swaps := [(0,4),(1,4),(2,5),(3,4),(4,5)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 1) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_10 : Slice r_23 g_23 (subcubeFast 9 0) 7 := by
  have hc : Lower (varsOf 54) (d 0xfcfcc0c0c0c00000) 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,5)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 9) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_11 : Slice r_23 g_23 (subcubeFast 1 16) 7 := by
  have hc : Lower (varsOf 46) (d 0xfffcfffcfcc0fcc0) 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4),(4,5)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 1) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_12 : Slice r_23 g_23 (subcubeFast 33 0) 7 := by
  have hc : Lower (varsOf 30) (d 0xfcc0c000fcc0c000) 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 33) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_13 : Slice r_23 g_23 (subcubeFast 4 0) 8 := by
  have hc : Lower (varsOf 59) (d 0xffeeff88cc000000) 8 := carry_of (swaps := [(2,5),(4,5)]) (by decide +kernel) low_18
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_14 : Slice r_23 g_23 (subcubeFast 2 0) 7 := by
  have hc : Lower (varsOf 61) (d 0xfffaff00f0a00000) 7 := carry_of (swaps := [(1,5),(2,5),(3,5),(4,5)]) (by decide +kernel) low_19
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_15 : Slice r_23 g_23 (subcubeFast 16 0) 7 := by
  have hc : Lower (varsOf 47) (d 0xffc8ffc8c000c000) 7 := carry_of (swaps := [(1,2),(4,5)]) (by decide +kernel) low_20
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_16 : Slice r_23 g_23 (identDom 2 3) 8 := by
  have hc : Lower (varsOf 55) (d 0xfefef8f8f0f0c0c0) 8 := carry_of (swaps := [(2,4),(3,5)]) (by decide +kernel) low_21
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_17 : Slice r_23 g_23 (subcubeFast 4 1) 6 := by
  have hc : Lower (varsOf 58) (d 0xffffffcccc000000) 6 := carry_of (swaps := [(0,4),(1,4),(2,5),(3,4),(4,5)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 4) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_18 : Slice r_23 g_23 (identDom 2 4) 8 := by
  have hc : Lower (varsOf 47) (d 0xfff8fff8f0e0f0e0) 8 := carry_of (swaps := [(2,4),(3,4),(4,5)]) (by decide +kernel) low_22
  exact slice_ident (u := 2) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_19 : Slice r_23 g_23 (subcubeFast 12 32) 4 := by
  have hc : Lower (varsOf 19) (d 0xeeee8888eeee8888) 4 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 12) (o := 32) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_20 : Slice r_23 g_23 (subcubeFast 10 16) 4 := by
  have hc : Lower (varsOf 37) (d 0xfafafafaa0a0a0a0) 4 := carry_of (swaps := [(1,3),(2,3),(3,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 10) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_21 : Slice r_23 g_23 (subcubeFast 33 16) 4 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 33) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_22 : Slice r_23 g_23 (subcubeFast 9 32) 4 := by
  have hc : Lower (varsOf 22) (d 0xfcfcc0c0fcfcc0c0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 9) (o := 32) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_23 : Slice r_23 g_23 (subcubeFast 32 9) 4 := by
  have hc : Lower (varsOf 22) (d 0xfcfcc0c0fcfcc0c0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 32) (o := 9) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_24 : Slice r_23 g_23 (subcubeFast 33 4) 4 := by
  have hc : Lower (varsOf 26) (d 0xffcccc00ffcccc00) 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 33) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_25 : Slice r_23 g_23 (subcubeFast 5 16) 4 := by
  have hc : Lower (varsOf 42) (d 0xffccffcccc00cc00) 4 := carry_of (swaps := [(0,3),(1,3),(2,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 5) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_26 : Slice r_23 g_23 (subcubeFast 16 5) 4 := by
  have hc : Lower (varsOf 42) (d 0xffccffcccc00cc00) 4 := carry_of (swaps := [(0,3),(1,3),(2,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 5) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_27 : Slice r_23 g_23 (subcubeFast 17 4) 4 := by
  have hc : Lower (varsOf 42) (d 0xffccffcccc00cc00) 4 := carry_of (swaps := [(0,3),(1,3),(2,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 17) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_28 : Slice r_23 g_23 (subcubeFast 9 4) 4 := by
  have hc : Lower (varsOf 50) (d 0xffffcccccccc0000) 4 := carry_of (swaps := [(0,3),(1,3),(2,4),(3,5),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 9) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_29 : Slice r_23 g_23 (subcubeFast 32 3) 4 := by
  have hc : Lower (varsOf 28) (d 0xfff0f000fff0f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 32) (o := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_30 : Slice r_23 g_23 (subcubeFast 3 16) 4 := by
  have hc : Lower (varsOf 44) (d 0xfff0fff0f000f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 3) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_31 : Slice r_23 g_23 (subcubeFast 17 2) 4 := by
  have hc : Lower (varsOf 44) (d 0xfff0fff0f000f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 17) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_32 : Slice r_23 g_23 (subcubeFast 9 2) 4 := by
  have hc : Lower (varsOf 52) (d 0xfffff0f0f0f00000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 9) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_33 : Slice r_23 g_23 (subcubeFast 3 4) 4 := by
  have hc : Lower (varsOf 56) (d 0xffffff00ff000000) 4 := carry_of (swaps := [(0,3),(1,4),(2,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 3) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_34 : Slice r_23 g_23 (subcubeFast 5 2) 4 := by
  have hc : Lower (varsOf 56) (d 0xffffff00ff000000) 4 := carry_of (swaps := [(0,3),(1,4),(2,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 5) (o := 2) (by decide +kernel) hc
def S_23 : BT (Option (Nat × Nat)) := btOfList 6 [some (subcubeFast 1 0,10),some (subcubeFast 8 0,9),some (subcubeFast 0 1,9),some (subcubeFast 0 4,8),some (subcubeFast 0 2,8),some (subcubeFast 0 16,8),some (subcubeFast 32 0,8),some (identDom 0 5,9),some (subcubeFast 1 2,7),some (subcubeFast 1 4,7),some (subcubeFast 9 0,7),some (subcubeFast 1 16,7),some (subcubeFast 33 0,7),some (subcubeFast 4 0,8),some (subcubeFast 2 0,7),some (subcubeFast 16 0,7),some (identDom 2 3,8),some (subcubeFast 4 1,6),some (identDom 2 4,8),some (subcubeFast 12 32,4),some (subcubeFast 10 16,4),some (subcubeFast 33 16,4),some (subcubeFast 9 32,4),some (subcubeFast 32 9,4),some (subcubeFast 33 4,4),some (subcubeFast 5 16,4),some (subcubeFast 16 5,4),some (subcubeFast 17 4,4),some (subcubeFast 9 4,4),some (subcubeFast 32 3,4),some (subcubeFast 3 16,4),some (subcubeFast 17 2,4),some (subcubeFast 9 2,4),some (subcubeFast 3 4,4),some (subcubeFast 5 2,4)]
lemma S_23_ok : btAll (fun o => ∀ p, o = some p → Slice r_23 g_23 p.1 p.2) S_23 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_23_0) (forall_cons (fun _ h => by cases h; exact sl_23_1) (forall_cons (fun _ h => by cases h; exact sl_23_2) (forall_cons (fun _ h => by cases h; exact sl_23_3) (forall_cons (fun _ h => by cases h; exact sl_23_4) (forall_cons (fun _ h => by cases h; exact sl_23_5) (forall_cons (fun _ h => by cases h; exact sl_23_6) (forall_cons (fun _ h => by cases h; exact sl_23_7) (forall_cons (fun _ h => by cases h; exact sl_23_8) (forall_cons (fun _ h => by cases h; exact sl_23_9) (forall_cons (fun _ h => by cases h; exact sl_23_10) (forall_cons (fun _ h => by cases h; exact sl_23_11) (forall_cons (fun _ h => by cases h; exact sl_23_12) (forall_cons (fun _ h => by cases h; exact sl_23_13) (forall_cons (fun _ h => by cases h; exact sl_23_14) (forall_cons (fun _ h => by cases h; exact sl_23_15) (forall_cons (fun _ h => by cases h; exact sl_23_16) (forall_cons (fun _ h => by cases h; exact sl_23_17) (forall_cons (fun _ h => by cases h; exact sl_23_18) (forall_cons (fun _ h => by cases h; exact sl_23_19) (forall_cons (fun _ h => by cases h; exact sl_23_20) (forall_cons (fun _ h => by cases h; exact sl_23_21) (forall_cons (fun _ h => by cases h; exact sl_23_22) (forall_cons (fun _ h => by cases h; exact sl_23_23) (forall_cons (fun _ h => by cases h; exact sl_23_24) (forall_cons (fun _ h => by cases h; exact sl_23_25) (forall_cons (fun _ h => by cases h; exact sl_23_26) (forall_cons (fun _ h => by cases h; exact sl_23_27) (forall_cons (fun _ h => by cases h; exact sl_23_28) (forall_cons (fun _ h => by cases h; exact sl_23_29) (forall_cons (fun _ h => by cases h; exact sl_23_30) (forall_cons (fun _ h => by cases h; exact sl_23_31) (forall_cons (fun _ h => by cases h; exact sl_23_32) (forall_cons (fun _ h => by cases h; exact sl_23_33) (forall_cons (fun _ h => by cases h; exact sl_23_34) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))))))))))))))))))
set_option maxRecDepth 500000 in
def ps_23 : BT (Option PoolSpec) := btOfList 12 [q 1 [16388,16389,241672,245833,241673,254028],q 1 [16388,16389,77899,241672,241673,254195],q 0 [16388,16389,77899,20488,20489,65599],q 2 [16388,16389,77899,20488,20489,65599],q 1 [16388,16389,77899,20488,20489,65599],q 2 [16388,16389,77899,20562,20563,110693],q 0 [16388,16389,77899,20562,20563,110693],q 1 [16388,16389,77899,20562,20563,110693],q 6 [16388,16389,77899,8294],q 6 [16388,16389,77899,8292],q 2 [16388,16389,77899,20560,20561,135299],q 0 [16388,16389,77899,20560,20561,135299],q 1 [16388,16389,77899,20560,20561,135299],q 2 [8196,8197,28699,20496,20497,155799],q 0 [8196,8197,28699,20496,20497,155799],q 1 [8196,8197,28699,20496,20497,155799],q 2 [8196,8197,28699,20512,20513,40999],q 0 [8196,8197,28699,20512,20513,40999],q 1 [8196,8197,28699,20512,20513,40999],q 2 [20488,20489,65599],q 0 [20488,20489,65599],q 5 [20488,20489,65599,4164],q 23 [],q 4 [20488,20489,65599],q 1 [16390,16391,241672,241673,254195],q 1 [16388,16389,241672,241673,254195],q 4 [20489,573453,577611],q 0 [16388,16389,20488,20489,65599],q 2 [16388,16389,20488,20489,65599],q 1 [16388,16389,20488,20489,65599],q 2 [16388,16389,20488,61513,20489],q 0 [16388,16389,20488,61513,20489],q 1 [16388,16389,20488,61513,20489],q 14 [20488,20489,65599],q 2 [16388,16389,77899],q 0 [16388,16389,77899],q 1 [16388,16389,77899,241673,254032],q 13 [16388,16389,77899],q 1 [16388,16389,77899],q 3 [16388,16389,77899],q 26 [],q 6 [16388,16389,77899],q 20 [],q 0 [16388,16389,77899,20562,12390,82191],q 2 [16388,16389,77899,20562,20563],q 0 [16388,16389,77899,20562,20563],q 1 [16388,16389,77899,20562,20563],q 0 [16388,16389,77899,20562,8294,82027],q 0 [16388,16389,77899,20562,8292,82131],q 3 [16388,16389,77899,20560],q 0 [16388,16389,77899,20490,20491],q 2 [16388,16389,77899,20490,20491],q 1 [16388,16389,77899,20490,20491],q 1 [16388,16389,77899,20488,61522],q 3 [16388,20553,16389],q 7 [16388,16389,77899],q 27 [],q 13 [16388,16389],q 4 [20488,20489,65599,16452],q 5 [20488,20489,65599],q 0 [16390,16391,20488,20489,65599],q 2 [16390,16391,20488,20489,65599],q 1 [16390,16391,20488,20489,65599],q 3 [16388,12361,16389],q 0 [16388,16389,77899,20488,20489],q 2 [16388,16389,77899,20488,20489],q 1 [16388,16389,77899,20488,20489],q 6 [8196,8197,28699],q 0 [8196,8197,28699],q 1 [8196,8197,28699],q 1 [20489,65852,823300,823301,832299],q 2 [20496,20497,155799],q 0 [20496,20497,155799],q 1 [16388,16389,241672,245833,241673],q 1 [16388,16389,77899,241672,241673],q 15 [8196,8197,28699],q 2 [8196,8197,28699],q 1 [16389,241672,78067,241673,254480],q 1 [16388,16389,241672,241673,254028],q 6 [16388,16389,65612],q 19 [],q 10 [16388,16389,77899],q 2 [20484,20485,504299],q 10 [20484,20485,504299],q 1 [16388,16389,77899,241674,241675],q 5 [8196,8197,28699,20512],q 1 [16388,16389,77899,20489,65616],q 1 [8196,8197,28699,20496,151586],q 5 [8196,8197,28699],q 18 [12289,20484,20485,504299,12786],q 0 [16388,16389,77899,12370,20746,82191],q 1 [16388,16389,77899,20491,82599],q 3 [16388,16389,77899,20773],q 4 [],q 0 [20484,20485,504299],q 6 [16388,16389,77899,8272],q 1 [20488,20489,65599],q 30 [],q 1 [16388,16389,77899,20489,65800],q 1 [16388,20488,20489,65599,73798],q 6 [16388,16389,77899,8274],q 1 [16389,241740,1138696,1138697,1147999],q 1 [20496,20497,155799,4254],q 14 [20496,20497,155799],q 4 [20496,20497,155799],q 0 [20496,20497,155799,4254,4255],q 3 [20496,20497,155799],q 13 [20496,20497,155799],q 21 [],q 1 [241680,1187845,241681,1193099],q 1 [20496,20497,155799,8350],q 15 [20493,241672],q 1 [20489,65852,823300,823301],q 0 [20488,20489,65599,16397,323652],q 1 [20488,20489,65599,323652],q 0 [20488,20489,65599,16452,16453],q 15 [20488,20489,65599],q 18 [],q 1 [20488,20489,65599,16452,16453],q 33 [],q 0 [20488,20489,65599,4164,4165],q 0 [20488,20489,65599,4164],q 2 [20488,20489,65599,4164],q 4 [20488,20489,65599,70],q 5 [20488,20489,65599,70],q 5 [20486,1209,20487,1246393],q 2 [20486,20487,1246393,16880],q 13 [20486,1209,20487,1246393],q 3 [20486,1209,20487,1246393],q 1 [20486,1209,20487,1246393],q 29 [],q 0 [20484,20485,16392,1257961,16393],q 3 [20484,20485,1257961],q 5 [20484,20485,504299],q 0 [20484,20485,504299,16397,324080],q 13 [20484,20485,504299],q 3 [20484,20485,504299],q 1 [20484,20485,504299],q 1 [20484,20485,504299,324080],q 0 [20484,20485,504299,16392,16393],q 1 [20484,20485,504299,16392,16393],q 18 [20484,20485,504299],q 0 [20484,20485,504299,16392,1257970],q 15 [20484,20485,504299],q 0 [20484,20485,504299,12298,508183],q 1 [20484,20485,504299,508183],q 0 [20484,20485,504299,16882,16883],q 1 [20484,20485,504299,16882,16883],q 1 [20484,20485,504299,16880],q 2 [20484,20485,504299,8690],q 0 [20484,20485,504299,8690],q 31 [],q 1 [20484,20485,504299,8690],q 2 [20484,20485,504299,16880],q 0 [20484,20485,504299,16880],q 13 [16391,20493,241668],q 5 [],q 1 [16391,20488,20489,65599],q 0 [16391,20488,20489,65599],q 2 [16391,20488,20489,65599],q 2 [20484,20485,504299,8688],q 0 [20484,20485,504299,8688],q 2 [20484,20485,504299,16882],q 0 [20484,20485,504299,16882],q 0 [20484,20485,504299,16393,1266160],q 1 [16390,241672,241673,254195],q 3 [20493],q 0 [16390,20488,20489,65599],q 2 [16390,20488,20489,65599],q 1 [16390,20488,20489,65599],q 0 [16391,20488,20489,65599,528454],q 1 [16390,16391],q 3 [16390,16391],q 1 [16390,16391,241673,254479],q 0 [20496,20497,155799,8350,8351],q 1 [16389,241740,1138696,1138697],q 1 [16389,241674,78751,241675],q 13 [20493,253968],q 3 [],q 1 [16389,241673,253968,241740],q 1 [16389,241672,241673,254028],q 1 [16389,241740],q 0 [20493,241672,241673,254195],q 2 [20493,241672,241673,254195],q 1 [16389,241672,241673,254195],q 1 [16389,241672,78067,241673],q 1 [16389,241672,16627,241740],q 0 [],q 2 [],q 0 [16389,77839,21773,20495,1327511],q 4 [21773,20495,1327511],q 13 [],q 0 [16389,20488,20489,65599,77892],q 1 [16389,20488,20489,65599,77892],q 1 [16389,20488,20489,65599],q 0 [16389,20488,20489,65599],q 2 [16389,20488,20489,65599],q 0 [20488,20489,65599,12357],q 2 [20488,20489,65599,12357],q 0 [16388,20488,20489,65599],q 2 [16388,20488,20489,65599],q 1 [16388,20488,20489,65599],q 0 [20488,20489,65599,12358],q 0 [16388,20488,20489,65599,73798],q 12 [],q 2 [16388,20488,61513,20489],q 0 [16388,20488,61513,20489],q 1 [16388,20488,61513,20489],q 1 [16391,241672,241673,254195],q 0 [16388,20488,61513,13626],q 1 [16388,20488,61513,589825],q 1 [16388,16389,241674,241675],q 1 [16388,16389],q 3 [16388,16389],q 1 [16388,16389,241673,254028],q 1 [16388,16389,241673,254027],q 1 [16388,16389,241672,241673],q 13 [16388,16389,65612],q 1 [16388,16389,20489,65612],q 2 [16388,16389],q 0 [16388,16389],q 1 [16388,16389,20488,61513],q 0 [16390,16391],q 2 [16388,16389,20488,61513],q 0 [16388,16389,20488,61513],q 0 [16388,16389,12298,20489,65612],q 4 [12298,20489],q 0 [16388,16389,77899,20490,74101],q 0 [16388,16389,20489,65612],q 2 [16388,16389,20489,65612],q 4 [20489,573455],q 0 [16388,16389,77899,20490,82295],q 0 [16388,16389,77899,20488,12349],q 1 [16388,16389,77899,20488],q 14 [],q 0 [16388,16389,77899,20488,61522],q 0 [20488,20489,65599,4166,4167],q 0 [16388,16389,77899,12298,74005],q 3 [16388,16389,77899,74005],q 0 [16388,16389,77899,20560,73857],q 14 [8272,20560],q 0 [16390,20488,20489,65599,70159],q 0 [16388,16389,77899,8272,20833],q 0 [16388,16389,77899,8272,74081],q 0 [16388,16389,77899,20495,82327],q 1 [16388,16389,77899,82327],q 1 [16388,16389,77899,241674],q 0 [20496,20497,155799,4252,4253],q 2 [16388,16389,77899,20493],q 0 [16388,16389,77899,20493],q 1 [16388,16389,77899,241672],q 1 [16389,241740,1138698,1138699],q 0 [16388,16389,77899,20491,12965],q 0 [16388,16389,77899,20491,82599],q 1 [16388,16389,77899,20490],q 0 [20488,20489,65599,16454,16455],q 1 [20484,20485,504299,16395],q 18 [20484,20485,504299,12785],q 0 [16388,16389,77899,20489,65616],q 0 [20488,20489,65599,16399,70187],q 1 [20488,20489,65599,70187],q 0 [20493,241672,241673,253968],q 2 [20493,241672,241673,253968],q 1 [241672,241673,254195],q 1 [16388,241672,241673,254195],q 0 [16388,16389,77899,12298,20489],q 1 [16388,16389,77899,20489],q 0 [16388,16389,77899,12298,20757],q 1 [16388,16389,77899,20757],q 0 [16388,16389,77899,12298,82199],q 1 [16388,16389,77899,82199],q 0 [16388,16389,77899,12297,20490],q 0 [16388,16389,77899,12297,294992],q 1 [16388,16389,77899,294992],q 1 [16390,16391,241674,241675],q 0 [16388,16389,77899,20563,8301],q 0 [16388,16389,77899,20562],q 2 [16388,16389,77899,20562],q 1 [16388,16389,77899,20562],q 6 [16388,16389],q 1 [16390,16391,241672,241673],q 3 [16388,12361],q 0 [20488,20489,65599,16454],q 2 [20488,20489,65599,16454],q 3 [16388,16389,573453],q 4 [20489,573453],q 2 [16388,20553,16389],q 9 [16388,20553,16389],q 6 [16388,73729,16389,77899],q 13 [16388,73729,16389,77899],q 3 [16388,73729,16389,77899],q 1 [16388,73729,16389,77899],q 1 [16388,73729],q 0 [16388,12361,16389,77899,21065],q 1 [16388,241672,245833,241673],q 0 [16388,20553,12298,307477],q 3 [16388,73729],q 0 [16388,8265,16389,77899,20490],q 1 [16388,73729,20553,16389],q 4 [20488,61513,20489],q 22 [],q 0 [20484,20485,504299,8688,8689],q 1 [8196,8197,28699,20512],q 0 [8196,8197,28699,20512,12325],q 1 [16388,20553,16389,77899],q 0 [8198,20496,20497,155799,1437854],q 1 [20496,20497,155799],q 18 [20484,20485,504299,12786],q 6 [16388,73729,16389],q 1 [16388,16389,241672,245833],q 0 [16388,16389,77899,12998],q 0 [16388,16389,77899,20493,241744],q 1 [8197,20496,20497,155799],q 0 [8197,20496,20497,155799,28828],q 0 [8196,8197,28699,20514,20515],q 13 [16390,16391],q 2 [16388,16389,77899,20490],q 0 [16388,16389,77899,20490],q 0 [8196,8197,28699,20499,34203],q 1 [8196,8197,28699,16416],q 0 [8196,8197,28699,16416,13253],q 0 [16388,8265,12598,20889,20495],q 0 [12294,20488,20489,65599,70359],q 1 [8196,8197,20496,151577],q 0 [16388,16389,77899,20495,74133],q 1 [16388,8265,16389,77899],q 0 [8196,8197,28699,16418,16419],q 1 [8196,8197,28699,16418,16419],q 1 [16388,16389,77899,241739],q 3 [16388,20553],q 0 [8196,8197,28699,16397,323616],q 1 [8196,8197,28699,323616],q 13 [16388,16389,77899,82],q 3 [16388,16389,77899,82],q 0 [8196,8197,28699,16416,16417],q 1 [8196,8197,28699,16416,16417],q 4 [12289,20489,573824],q 0 [16388,16389,77899,20490,12661],q 5 [12289,20484,20485,504299],q 13 [12289,20484,20485,504299],q 3 [12289,20484,20485,504299],q 0 [20484,20485,504299,16394,509395],q 1 [],q 0 [16388,16389,77899,20488,61513],q 0 [16388,20553,16389,12998],q 4 [73729,20553,12998],q 1 [16388,73729,241671],q 0 [8198,8199,20496,20497,155799],q 1 [8198,8199,20496,20497,155799],q 0 [8196,8197,20496,151577,20497],q 3 [20496,151577,20497],q 0 [8196,8197,28699,20498,20499],q 0 [20484,20485,504299,16395,508523],q 0 [16388,20553,16389,77899],q 2 [16388,20553,16389,77899],q 3 [16388,12361,20553,16389],q 0 [16388,16389,77899,20560,12417],q 0 [20484,20485,504299,8690,8691],q 3 [12289,16388,16389,77899],q 13 [12289,16388,16389,77899],q 1 [16388,16389,77899,8272],q 2 [16388,16389,77899,8272],q 6 [12289,16388,16389,77899],q 4 [20489,573443,13597],q 1 [16389,20489,65612,573443],q 0 [16388,20555,16389,77899,20493],q 3 [16388,20555,16389,77899],q 0 [16388,16389,77899,20489],q 2 [16388,16389,77899,20489],q 0 [16388,16389,77899,20561],q 2 [16388,16389,77899,20561],q 0 [8196,20496,20497,155799,24734],q 0 [16388,16389,77899,12370,20746],q 5 [12289,20488,20489,65599],q 0 [8196,8197,28699,20496,20497],q 1 [8196,8197,28699,20496,20497],q 15 [20493,1191944],q 6 [16389,65612],q 0 [8196,8197,28699,20512,20513],q 1 [8196,8197,28699,20512,20513],q 0 [12298,20496,20497,155799,282782],q 1 [20496,20497,155799,282782],q 4 [12289,20488,20489,65599],q 1 [8196,8197,28699,16419],q 0 [8196,8197,28699,20493,241696],q 1 [16388,8267,16389,77899],q 0 [16388,20553,16389,20493],q 2 [16388,20553,16389,20493],q 4 [73729,20553,20493],q 3 [16388,73729,20553,16389],q 5 [12294,741534],q 14 [20498,20499,1467873],q 1 [16388,16389,77899,241737],q 2 [16388,16389,77899,12298],q 0 [8196,8197,28699,16416,16397],q 2 [20493,241668,241674,1209245],q 13 [20493,241668],q 0 [16388,16389,77899,8272],q 2 [20493,241671],q 0 [16388,16389,77899,12297,20770],q 1 [16388,16389,77899,20770],q 1 [8196,8197,28699,20496],q 0 [16388,20553,16389,77899,307215],q 0 [8196,8197,20496,20497,155799],q 1 [8196,8197,20496,20497,155799],q 0 [16388,20488,12349,397387],q 3 [16388,20553,16389,77899],q 0 [16388,12361,16389,77899,20493],q 3 [16388,12361,16389,77899],q 13 [16388],q 0 [16388,16389,77899,8274,12713],q 0 [8199,20496,20497,155799,1536158],q 0 [16388,16389,77899,12369],q 2 [16388,16389,77899,12369],q 2 [20484,20485,504299,16395],q 18 [12289,20484,20485,504299],q 1 [16388,16389,77899,82],q 6 [16388,16389,77899,82],q 0 [16388,16389,77899,20563,8303],q 1 [20489,65852,823302,823303],q 0 [16388,8265,16389,77899,12598],q 0 [16388,8265,16389,77899,20790],q 0 [16388,12361,16389,21065,1036363],q 10 [20488,20489,65599],q 25 [],q 0 [8196,8197,28699,20496,151586],q 0 [16388,20553,16389,77899,20493],q 0 [12294,20496,20497,155799,741534],q 1 [20496,20497,155799,741534],q 0 [16388,16389,77899,20488],q 2 [16388,16389,77899,20488],q 4 [20493,241739],q 0 [16388,16389,77899,20493,241739],q 1 [8196,8197,28699,20515],q 0 [16388,16389,77899,8274,20905],q 1 [16388,20553,241671],q 6 [16388,241671],q 0 [16388,16389,77899,20489,65551],q 2 [16388,12361,16389,77899],q 0 [16388,12361,16389,77899],q 2 [16388,16389,77899,12370],q 0 [16388,16389,77899,12370],q 0 [16388,16389,77899,8272,20489],q 0 [8196,8197,28699,20497,155680],q 0 [16388,20553,12298,20757,307215],q 13 [16388,20553,307215],q 0 [16388,20555,13057,16389,77899],q 1 [16388,20555,16389,77899],q 4 [20555,786514],q 0 [16388,20555,16389,77899,786514],q 0 [12293,20488,20489,65599,753732],q 1 [20488,20489,65599,753732],q 0 [20484,20485,504299,16880,16881],q 1 [16388,16389,77899,241673],q 0 [16388,16389,77899,8272,8273],q 0 [8196,8197,28699,20498,34275],q 0 [16388,16389,77899,8272,12641],q 2 [20493,241668],q 5 [20493,241672,245833],q 0 [16388,16389,77899,8272,12297],q 0 [20496,20497,155799,8348,8349],q 1 [16388,16389,77899,20491],q 0 [16388,16389,77899,20491],q 2 [16388,16389,77899,20491],q 4 [73729],q 0 [16388,16389,77899,8273,22106],q 0 [16388,16389,77899,8274,8275],q 1 [16388,16389,77899,241675],q 0 [16388,16389,77899,8274,20490],q 0 [16388,16389,77899,8275,22117],q 1 [16388,16389,77899,20678],q 0 [16388,16389,77899,12369,20678],q 0 [16388,16389,77899,20560,20561],q 0 [20486,13502,20487,1246393],q 0 [16388,16389,77899,20562,12389],q 1 [20498,20499,1467873],q 0 [20498,20499,1467873,12446],q 15 [12446],q 4 [20498,20499,1467873],q 13 [20498,20499,1467873],q 3 [20498,20499,1467873],q 5 [4252],q 0 [20498,20499,1467873,4252],q 15 [4252],q 0 [20498,9697,20499,1467873],q 0 [20496,20497,155799,12446],q 0 [20496,20497,155799,8351],q 0 [20496,20497,155799,8350],q 0 [20496,20497,155799,4253],q 1 [20496,20497,155799,4253],q 0 [20496,20497,155799,4252],q 2 [20496,151565,368648],q 0 [20496,151565,368648],q 2 [20496,151565,368644],q 0 [20496,151565,368644],q 24 [],q 4 [20496,151565],q 13 [20493,241680],q 1 [241680,241681,1193099],q 5 [20493],q 0 [20493,241680,241681,1193099],q 15 [20493],q 1 [241680,1187845,241681],q 0 [20493,241674,241680,1188765],q 5 [20493,241673],q 3 [454662],q 1 [241673,253968,454662],q 4 [20493,241683],q 0 [20493,241673,253959],q 0 [20493,241673,253959,241683],q 3 [20493,241683],q 1 [241673,253959],q 1 [241673,253959,241683],q 5 [20493,241673,253959],q 6 [241673,253959],q 3 [20493,241680],q 15 [],q 0 [20498,5601,20499,1467873],q 1 [20498,5601,20499,1467873],q 1 [241672,241680,1188081],q 0 [20493,241672,241680,1188081],q 6 [241672,241680,1188081],q 5 [20493,241672],q 1 [241672,241673,253968],q 6 [241672,241673,253968],q 14 [20493],q 1 [241671,241683,5775],q 13 [20493,241671],q 3 [20493,241671],q 0 [20493,241681,1191947],q 0 [20493,241671,241681,1191947],q 4 [20493,241681,1191947],q 1 [241671,241681,1191947],q 5 [20493,241671],q 6 [241681,1191947],q 0 [20493,241681,1191940],q 0 [20493,241671,241681,1191940],q 4 [20493,241681],q 3 [20493,241681,1191940],q 13 [20493,241681,1191940],q 1 [241671,241681,1191940],q 4 [20493,241680],q 1 [241671,241680,1187846],q 1 [241671,17843,241683],q 2 [16389,20489,65612],q 0 [16389,20489,65612],q 4 [20489,573443],q 6 [16389,65612,573443],q 13 [16389,65612,573443],q 0 [16388,16389,77899,8274],q 0 [16388,16389,77899,8273],q 4 [8265,12298],q 14 [12298],q 1 [16388,8265,16389],q 14 [13057],q 1 [16388,20555,16389],q 0 [16388,20555,13057,16389],q 4 [20555,13057],q 0 [20488,20489,65599,16399],q 4 [20553],q 1 [16388,20553],q 6 [16388],q 1 [16388,241739],q 3 [16388,74101],q 3 [16388],q 0 [16388,20553,12298,307215],q 0 [16388,20553,12298,20757],q 13 [16388,20553],q 6 [12298],q 0 [16388,16389,77899,20495],q 6 [],q 13 [16388,20555],q 3 [16388,74005],q 1 [16388,20553,16389],q 14 [307215],q 0 [16388,20553,16389,307215],q 4 [20553,307215],q 5 [20490,20491],q 4 [20490,20491],q 0 [16390,16391,20490,20491],q 0 [16388],q 0 [16388,12361,21065,1036303],q 28 [],q 5 [73729,20553],q 4 [73729,20553],q 1 [16388,73729,20553],q 0 [16388,12361,21065,1036295],q 13 [16389],q 1 [16389,241674,78751],q 4 [20493,241674],q 0 [16388,12361,20490,598389],q 2 [16388,8265,20490],q 0 [16388,8265,20490],q 1 [20487,16392,21709],q 0 [20487,13505,16392,21709],q 4 [16392,21709],q 2 [16388,20490,74101],q 0 [16388,20490,74101],q 1 [16388],q 4 [20555],q 0 [16388,20555,16389,77899],q 0 [16388,20553,12298,307479],q 4 [12361,21065],q 14 [21065],q 14 [20495],q 1 [16388,8267,16389],q 4 [8267],q 0 [16388,8267,16389,77899],q 0 [8196,8197,20496,20497],q 13 [20496,20497],q 3 [20496,20497],q 6 [8196,8197],q 1 [16389,241674,241740],q 2 [16388],q 0 [16388,20555,12298,786709],q 1 [20484,16672,1757673],q 0 [20484,12297,16672,1757673],q 4 [12297,16672,1757673],q 0 [16388,8265,20495,315799],q 6 [16388,8265],q 6 [16388,73729],q 13 [16388,73729],q 0 [16388,8265,12598,20889],q 1 [16388,8265,20889],q 5 [20491,12965],q 4 [20491,12965],q 1 [16390,16391,20491],q 0 [16390,16391,20491,12965],q 6 [16390,16391],q 1 [16388,8265,20490],q 0 [16388,8265,20490,12598],q 1 [8197,16412,241683],q 0 [16388,8265,12298,20757],q 0 [8196,8197,28699,20498],q 0 [20496,20497,155799,8349],q 1 [20496,20497,155799,8349],q 1 [241668,241680,1187845],q 0 [16388,8265,16389,20790],q 4 [8265,20790],q 14 [20790],q 16 [],q 0 [12298,20757],q 1 [241669,241683,1214095],q 0 [20493,241669,241683,1214095],q 3 [16388,20555,16389],q 1 [16388,16389,241674],q 5 [8265],q 1 [16389,20490,241740],q 6 [16389,241740],q 0 [8196,8197,28699,20497],q 1 [8196,8197,28699,20497],q 0 [20498,20499,1467873],q 15 [12289],q 2 [20498,20499,1467873],q 1 [16395,4715,241671],q 2 [16388,8265,20790],q 0 [16388,8265,20790],q 0 [16388,8265,20790,13137],q 2 [16388,12361],q 0 [16388,12361],q 2 [16388,20488,61513],q 0 [16388,20488,61513],q 2 [16388,16389,20490],q 0 [16388,16389,20490],q 1 [16388,16389,20490],q 4 [8265,20490],q 14 [20490],q 0 [16388,8265,16389,20490],q 0 [16388,12361,20488,12349],q 1 [20488],q 0 [20484,20485,16392,16393],q 6 [16392,16393],q 18 [20484,20485],q 5 [73729],q 5 [73729,20495,74133],q 1 [16388,73729,74133],q 0 [20496,20497,155799,4255],q 0 [16388,12361,20490,12661],q 13 [16388,12361],q 1 [20490],q 3 [20497],q 0 [20490,12661],q 1 [16388,73729,20490],q 0 [16388,16389,20493],q 4 [73729,20493],q 1 [16388,73729,16389],q 13 [16388,73729,16389],q 3 [16388,73729,16389],q 13 [16391],q 1 [16391],q 4 [73729,20490],q 2 [16388,16389,12298],q 4 [73729,12298],q 1 [241668,241680,1189021],q 0 [20493,241668,241680,1189021],q 5 [20493,241668],q 6 [241668,241680,1189021],q 2 [16388,20553],q 9 [16388,20553],q 2 [16388,20493,241739],q 0 [16388,20493,241739],q 4 [16880],q 5 [20486,20487,1246393],q 0 [20486,20487,1246393,16880],q 14 [16880],q 13 [20486,20487,1246393],q 3 [20486,20487,1246393],q 1 [20486,20487,1246393],q 3 [12289,20484,20485],q 6 [12289,16395],q 1 [20484,20485,16395],q 2 [20484,20485],q 2 [20484,20485,16395],q 13 [12289,20484,20485],q 4 [12289],q 4 [12289,16395],q 18 [12289,20484,20485],q 1 [16388,16389,21065],q 0 [16388,12361,16389,21065],q 1 [16388,241671],q 5 [12298,20489],q 0 [16390,16391,12298,20489],q 1 [16390,16391,20489],q 4 [73729,8265],q 1 [16388,73729,8265],q 1 [16388,74133],q 14 [12998],q 5 [73729,8265,20490],q 2 [16388,8265,12298],q 5 [73729,8265,12298],q 3 [12289,20486,20487],q 2 [20486,20487],q 2 [20486,20487,16395],q 0 [16388,20553,16389],q 1 [8196,20496,151577],q 0 [16388,20493,241736,242987],q 1 [16388,241736,242987],q 0 [12294,20498,20499,1467873],q 15 [12294],q 2 [12298,20757],q 0 [16390,4623],q 2 [16390,4623],q 3 [20757],q 4 [12298,20757],q 5 [12289],q 5 [12289,20490],q 4 [12289,20490],q 6 [12289,16390,16391],q 1 [16390,16391,20490],q 2 [16390,16391,20490],q 3 [12289,16390,16391],q 1 [8196,20505,1786172],q 0 [8196,20505,16397,1786172],q 14 [16397,1786172],q 5 [8196,20505],q 0 [8196,8197,28699,20496],q 6 [8196],q 3 [12289,20484,12777],q 4 [12289,12777],q 14 [12289],q 2 [20484,12777],q 2 [20484,12777,16395],q 0 [16388,16389,20495,74133],q 1 [16388,16389,74133],q 13 [12289,20496,151565],q 4 [12289,20496,151565],q 2 [20496,151565],q 9 [20496,151565],q 1 [20496],q 6 [12289],q 0 [16388,16389,77899,12297],q 1 [16389,20490,78199],q 2 [16389,20490,78199],q 6 [12289,16389,78199],q 3 [12289],q 0 [20498,5603,20499,1467873],q 5 [5603],q 4 [12289,16393],q 1 [20487,16393,1265668],q 2 [20487,16393,1265668],q 6 [12289,16393,1265668],q 5 [12289,20487],q 5 [73729,12298,74005],q 0 [16388,12298,74005],q 1 [16388,73729,74005],q 3 [16388,73729,74005],q 3 [12289,20487],q 1 [20487,16393,1266883],q 2 [20487,16393,1266883],q 0 [20484,20485,504299,16395],q 0 [16388,12361,12998],q 15 [12998],q 0 [8196,8197,28699,16416],q 4 [20496,20497],q 0 [8198,8199,20496,20497],q 6 [8198,8199],q 0 [16388,20555,12298,20757],q 0 [20486,17595,20487,1246393],q 15 [20486,20487,1246393],q 4 [12289,20553],q 6 [12289,16388,16389],q 0 [16388,20553,20493,307215],q 6 [16388,307215],q 0 [20498,9699,20499,1467873],q 2 [16388,16389,20493],q 1 [16388,16389,241673],q 4 [20493],q 14 [307213],q 0 [20493,241672,241673],q 2 [20493,241672,241673],q 13 [20493],q 1 [16389,241672,241673],q 4 [12289,16392],q 6 [12289,16392],q 1 [20487,16392,1258689],q 2 [20487,16392,1258689],q 0 [16388,8265,16389,77899],q 1 [20487,16395,1245801],q 2 [20487,16395,1245801],q 13 [12289],q 0 [16388,16389,20491,12965],q 2 [16390,20493,242191],q 0 [16390,20493,242191],q 4 [20493,242191],q 3 [12289,20485,503823],q 0 [16395],q 2 [20485,503823],q 2 [20485,16395,503823],q 0 [8197,20496,20497,155799],q 0 [20489,16397,65852],q 2 [20489,16397,65852],q 5 [20489],q 3 [16397],q 1 [20489,65852,823301],q 2 [16388,20553,20495],q 3 [16388,73729,20553],q 0 [8196,8197,28699,20512],q 2 [16389,20493,241740],q 0 [16389,20493,241740],q 4 [20493,241672],q 1 [16389,241672,241740],q 0 [16388,8265,20493,241972],q 1 [16388,8265,241972],q 4 [12289,20496,151577],q 0 [8196,20496,151577],q 0 [16388,16389,20493,241739],q 1 [16388,16389,241739],q 4 [20553,20495],q 0 [8196,8197,28699,20515],q 1 [20485,16393,505044],q 3 [12289,20485],q 6 [12289,16393,505044],q 0 [20485,16393,505044],q 2 [20485,16393,505044],q 1 [16388,8265],q 5 [12289,20490,20491],q 13 [12289,16390],q 3 [12289,16390],q 1 [16390,20490,20491],q 0 [8197,16412,20493,243391],q 4 [20493,243391],q 3 [20493,243391],q 1 [8197,16412,243391],q 0 [20488,20489,65599,4167],q 15 [20493,241668],q 1 [16390,20490,536949],q 2 [16390,20490,536949],q 1 [8197,241683,30351],q 5 [20488,61513,20489],q 14 [20488,20489],q 0 [12294,20488,20489,65599],q 14 [8272],q 0 [8197,20496,151565,368668],q 1 [8197,20496,368668],q 6 [8197,368668],q 0 [16390,16391,20493],q 2 [16390,16391,20493],q 3 [12289,20497],q 2 [8197,20497,155676],q 5 [73729,20488,61513],q 1 [241670,241680,1189665],q 4 [12289,16392,21709],q 2 [16392,21709],q 0 [20487,16392,21709],q 0 [8196,8197,28699,20513],q 1 [8196,8197,28699,20513],q 3 [20757,286723],q 13 [286723],q 6 [12298,286723],q 0 [16393,1265668,20493,243435],q 1 [16393,1265668,243435],q 5 [20493,243435],q 0 [16388,8265,20490,12661],q 0 [20490,12661,20493],q 2 [20490,12661,20493],q 3 [12661,20493],q 1 [16389],q 0 [20498,13793,20499,1467873],q 2 [20493,241680,1187846],q 3 [20493,241668],q 1 [20489,65852,823303],q 3 [12289,20484],q 14 [12289,16395],q 1 [20484,16395,500329],q 2 [20484,16395,500329],q 5 [12289,20484,500329],q 5 [8198,8199],q 3 [20498,20499],q 0 [8196,8197,28699,16397],q 13 [12289,20484],q 14 [12289,16392],q 4 [12289,16392,1257961],q 2 [20484,16392,1257961],q 3 [12289,20496,151565],q 2 [8196,20496,151565],q 10 [20496],q 5 [12289,151565],q 6 [12289,8196],q 1 [8196,241680,1187865],q 0 [8196,20493,241680,1187865],q 4 [20493,241680,1187865],q 3 [16390],q 1 [16390,241673,254479],q 1 [16395,241671,1491561],q 1 [20485,16395,504427],q 2 [20485,16395,504427],q 3 [12289,14157],q 2 [8198,17791,14157],q 14 [12289,14157],q 4 [12289,17791,14157],q 1 [8198,17791],q 5 [20493,241739],q 2 [16388,20555],q 10 [],q 0 [16388,20555],q 10 [16388,20555],q 5 [12289,393291],q 4 [12289,393291],q 6 [12289,16388,393291],q 3 [12289,16388,393291],q 13 [12289,16388,393291],q 2 [12293,20486,754875],q 1 [20486,1209,754875],q 0 [20486,20487,1246393],q 2 [20486,20487,1246393],q 1 [16388,73729,241739],q 0 [16388,12361,20488,598077],q 1 [16393,241671,1267123],q 4 [12289,20489],q 1 [16389,20489,65612],q 6 [12289,16389,65612],q 1 [16389,241740,1138696],q 4 [12289,16392,16393],q 13 [12289,20487],q 1 [20487,16392,16393],q 2 [16392,16393],q 2 [20487,16392,16393],q 6 [12289,16392,16393],q 18 [12289,20487],q 6 [12289,16390],q 4 [12289,20488,61965],q 5 [12289,20488],q 1 [16390,20488,61965],q 2 [16390,20488,61965],q 5 [8196,8197],q 0 [8196,8197,20498,20499],q 0 [16388,8265,20553,16389],q 4 [8265,20553],q 13 [16388,20790],q 0 [16388,8265,12298,20790],q 6 [16388,8267],q 0 [8196,8197,28699,16419],q 5 [12289,20488,20489],q 1 [16390,20488,20489],q 0 [12294,20496,20497,155799],q 13 [12289,20484,12777],q 2 [20484,12777,16392],q 6 [16388,8265,12598],q 0 [16388,8265,12598,20495],q 5 [12289,20489],q 0 [16390,20489,66063],q 1 [16390,20489,66063],q 2 [16390,20489,66063],q 2 [20493,241674,21405],q 0 [20493,241674,21405],q 3 [20493,21405],q 1 [241674,21405],q 0 [20488,12349],q 1 [16388,73729,20488],q 0 [8196,8197,28699,20493],q 0 [8196,8197,28699,12322],q 0 [8196,8197,28699,20499],q 0 [8196,8197,28699,20495],q 13 [16388,21350],q 0 [16388,12298,74005,21350],q 2 [16388,12361,16389],q 0 [16388,12361,16389],q 2 [16388,16389,20488],q 0 [16388,16389,20488],q 1 [16388,16389,20488],q 0 [16388,16389,20488,12349],q 14 [307208],q 0 [20496,20497,155799,4254],q 0 [16388,16389,77899,8275],q 13 [16390,65552],q 1 [16390,20489,65552],q 1 [20488,17120,1953853],q 0 [12293,20488,17120,1953853],q 4 [20488,1953853],q 0 [8196,8197,20497,155676],q 13 [20497,155676],q 0 [8198,20496,20497,155799],q 1 [8198,20496,20497,155799],q 0 [20493],q 2 [20493],q 1 [16389,241672,78067],q 0 [8196,20496,151565,368667],q 1 [8196,20496,368667],q 6 [8196,368667],q 0 [8197,20493,241692],q 2 [8197,20493,241692],q 3 [12289,1949709],q 2 [20489,65552,1949709],q 0 [8196,8197,20496,151577],q 13 [20493,241692],q 1 [8197,241692,241680],q 0 [20487,16392,21709,1754307],q 6 [16392],q 0 [20493,241668,241669,1213599],q 1 [241668,241669,1213599],q 0 [8196,20496,20497,155799],q 1 [8196,20496,20497,155799],q 0 [20493,241673,253968],q 0 [20493,241673,241683,253968],q 4 [20493,241673,253968],q 1 [241673,241683,253968],q 6 [241673,253968],q 0 [20484,20485,504299,16397],q 0 [8196,12313,1974287],q 14 [1970177,1974287],q 13 [1970177,1974287],q 1 [16390,16391,241674],q 0 [8196,8197,28699,20514],q 1 [8196,8197,28699,20514],q 3 [16388,12361,20553],q 0 [12293,20496,20497,155799],q 0 [16388,8265,12598,20890],q 1 [16388,8265,20890],q 0 [8197,12318,22417,20495],q 4 [22417,20495],q 3 [22417,20495],q 6 [8197,12318],q 1 [8197,16412,20499],q 0 [8197,16412],q 4 [20499,13721],q 15 [13721],q 6 [8197,16412],q 0 [8197,16397,323612],q 2 [8197,16397,323612],q 5 [8197],q 4 [16397],q 0 [16393],q 2 [20485,16393,503823],q 0 [16389],q 9 [16389],q 2 [20489,65551],q 13 [65551,190],q 4 [16393],q 3 [12294,20485],q 6 [16393,505044],q 4 [12297,20490],q 0 [16388,16389,12297,20490],q 0 [20486,13497,13502],q 14 [13502],q 3 [16399,20497],q 6 [8197,155676],q 6 [8197,241692],q 1 [8197,241692],q 5 [20489,65551],q 4 [20489,65551],q 0 [16390,16391,20489,65551],q 2 [16390,16391],q 3 [20493,241680,1187846],q 1 [8197,241680,1187846],q 5 [73729,20553,20493],q 2 [16388,20553,20493],q 3 [20493,241691],q 1 [8196,16395,241691],q 0 [20493,241668,241672,246941],q 1 [241668,241672,246941],q 6 [241668,241672,246941],q 13 [12294,17109],q 1 [17109,20490,2007415],q 0 [20496,151565],q 3 [20496,151565],q 0 [8198,8199,20496,151565],q 1 [8198,8199,20496],q 13 [20493,241683],q 4 [20493,243071],q 1 [16391,241674,241675],q 0 [20493,241673,253975],q 2 [20493,241673,253975],q 13 [20493,253975],q 3 [16389],q 1 [8198,241680,1189245],q 0 [16388,20488,61513,12866],q 1 [16388,20488,61513],q 0 [12293,20488,20489,65599],q 1 [294916,20496,153529],q 0 [12297,294916,20496,153529],q 3 [20496,153529],q 6 [12297,294916],q 14 [20496],q 0 [20488,20489,65599,16455],q 1 [16388,8267],q 0 [20484,20485,504299,8689],q 1 [20484,20485,504299,8689],q 13 [16389,65612],q 4 [20489,20493],q 0 [16388,16389,77899,20560],q 4 [12361,20493],q 6 [16388,241739],q 0 [16388,16389,77899,20563],q 0 [16388,16389,77899,12298],q 0 [16391,20493,242183],q 2 [16391,20493,242183],q 34 [],q 0 [20484,20485,504299,16392],q 1 [20484,20485,504299,16392],q 2 [20493,241668,17567],q 0 [20493,241668,17567],q 4 [20562],q 0 [12297,20496,20497,155799],q 0 [20496,20497,155799,8348],q 1 [20488,397313],q 5 [20488,12349,397313],q 12 [16390],q 0 [20484,20485,504299,16393],q 1 [20484,20485,504299,16393],q 0 [16388,16389,12297,20770],q 1 [16388,16389,20770],q 4 [12297,20770],q 0 [16388,16389,12298,74005],q 1 [16388,16389,74005],q 4 [12298,74005],q 1 [16390,241673,253968],q 14 [20488],q 13 [16388,65611],q 1 [16388,20489,65611],q 0 [16388,12298,20489,65611],q 0 [16388,16389,20488,20489],q 4 [20488,20489],q 0 [16388,12361,21065,1036363],q 1 [16388,21065,1036363],q 1 [16390,241672,241673],q 12 [16388],q 0 [20486,9403,20487,1246393],q 4 [9403],q 0 [16388,16389,20489,65551],q 1 [16388,16389,20489],q 4 [20489],q 13 [16390],q 1 [16390],q 0 [16388,16389,20490,74101],q 4 [20490,74101],q 0 [16388,16389,20490,12661],q 4 [20490,12661],q 10 [16388,16389],q 6 [16390,242191],q 1 [16390,242191],q 1 [16390,20489,242191],q 1 [16388,16389,241737],q 0 [8199,20496,20497,155799],q 1 [8199,20496,20497,155799],q 0 [20485,16392,16393,505044],q 3 [20485],q 4 [16392,16393],q 13 [20496,151565],q 0 [8196,8197,20496,151565],q 1 [8196,8197,20496],q 1 [16388,16389,241672],q 1 [16388,16389,241675],q 0 [20488,20489,65599,16453],q 0 [16388,12298,20757,286795],q 6 [16388,589825],q 5 [20488,61513,589825],q 13 [16388,589825],q 14 [20489],q 4 [20489,65611],q 1 [16388,20489,241739],q 0 [20489,20493,65551],q 14 [20489,65551],q 1 [16388,20490,74101],q 0 [16388,20490,74101,13326],q 0 [16388,20490,12661,639051],q 0 [20488,20489,65599,4166],q 4 [20493,241675],q 1 [16389,241675,241740],q 1 [16388,20490,241739],q 0 [20496,20497,155799,12445],q 2 [20493,241668,241674],q 5 [20493,241674],q 2 [20493,241672],q 0 [20493,241672],q 2 [16388,20493,241736],q 0 [16388,20493,241736],q 1 [241672],q 2 [20493,241674],q 0 [20493,241674],q 6 [241674],q 1 [241674],q 1 [241673],q 1 [16388,241739,241673],q 0 [16388,16389,20490,20491],q 1 [16388,241739,241675],q 2 [20493,241668,241672],q 2 [16388,20493,241668],q 0 [16388,20493,241668],q 0 [16389,12298,20489,65612],q 1 [16388,241671,75185],q 2 [20493,241673,253968],q 3 [454661],q 1 [241673,253968,454661],q 2 [20493,241671,241673],q 0 [16388,20493,241671],q 2 [16388,20493,241671],q 15 [20493,241671],q 2 [20493,241671,241675],q 1 [16388,241672,245833],q 5 [12297,20770],q 0 [16390,16391,12297,20770],q 1 [16390,16391,20770],q 1 [16388,241673,254027],q 6 [12289,16391,12805],q 13 [12289,16391,12805],q 1 [16388,241674,74653],q 0 [16388,12361,20493,241671],q 13 [20493,242283],q 3 [12289,16388,74101],q 2 [20489,20493,65551],q 13 [20493,65551],q 0 [16388,20553,20493,241671],q 1 [20489],q 14 [12289,1818637],q 4 [12289,17595,1818637],q 2 [20486,17595,1818637],q 0 [20484,20485,16397,504124],q 1 [20484,20485,504124],q 6 [16397,504124],q 5 [20484,20485],q 4 [16392,21709,1753091],q 13 [1753091],q 15 [1753091],q 1 [16395,4715,243399],q 0 [16389,20489,65612,573455],q 13 [16399,4649],q 1 [20490,4649,2072951],q 0 [8196,8197,28699,16417],q 1 [8196,8197,28699,16417],q 0 [16389,77839,21773,20495],q 4 [21773,20495],q 6 [16389,77839],q 0 [8196,8197,28699,12321],q 13 [16390,66063],q 1 [16389,241672,16627],q 4 [20493,241672,16627],q 1 [16389,241673,253968],q 1 [20489,65552],q 2 [16390,20489,65552],q 0 [16390,20489,65552],q 5 [73729,20493,241739],q 1 [16389,241673,241740],q 1 [16389,241673,254028],q 4 [20493,241673],q 0 [20493,241674,241675],q 2 [20493,241674,241675],q 1 [16389,241674,241675],q 5 [73729,20490,74101],q 1 [16389,241740,1138697],q 1 [16389,241740,1138698],q 1 [16389,241740,1138699],q 4 [12289,394427],q 1 [20486,394427,20487],q 10 [20486,20487],q 0 [16390,4623,20488,61513],q 4 [20488,61513],q 6 [16390,4623],q 1 [16390,241674,241675],q 2 [20488,12349],q 4 [20488,12349],q 1 [16390,20490,242191],q 1 [8197,241680,1187870],q 0 [20484,20485,504299,16881],q 1 [20484,20485,504299,16881],q 0 [8196,20496,151577,20497],q 4 [20496,151577,20497],q 2 [20490,12661],q 3 [12661],q 1 [241672,241673],q 1 [16388,241672,241673],q 5 [12297,20490],q 0 [16390,16391,12297,20490],q 5 [12298,20757],q 1 [16390,16391,20757],q 0 [16390,16391,12298,20757],q 5 [73729,8265,20790],q 0 [16388,20553],q 0 [16392,20493,241668,1258653],q 1 [16392,241668,1258653],q 14 [16392],q 1 [16388,74005],q 0 [16389,20489,65612,573453],q 1 [16390,241672,246285],q 5 [20488,20489],q 0 [16390,16391,20488,20489],q 5 [20493,242283],q 5 [20490,12661],q 0 [16390,16391,20490,12661],q 1 [16390,16391,241672],q 1 [16390,16391,241673],q 0 [16388,16389,12298,20757],q 1 [16388,16389,20757],q 1 [16390,16391,241675],q 5 [12298,20757,286723],q 0 [16390],q 1 [20489,65852,823302],q 4 [20493,241673,253971],q 0 [20493,241671,241673,253971],q 1 [241671,241673,253971],q 6 [241673,253971],q 5 [20493,241675],q 13 [12289,16388,16389],q 5 [20489,65551,190],q 9 [16390],q 1 [16391,20490,242183],q 6 [16391,242183],q 1 [16390,241674,537501],q 0 [20488,20489,65599,16452],q 1 [16391,20489,242183],q 6 [16391,241668],q 5 [20493,242183],q 2 [16391,20493,241668],q 0 [16391,20493,241668],q 0 [20484,20485,504299,12785],q 4 [20553,20493],q 1 [16391,241672,241673],q 8 [20496,151565],q 3 [16391],q 0 [20484,20485,504299,8691],q 4 [12298,20757,286723],q 0 [16391],q 0 [20484,20485,504299,12786],q 0 [16392,21709,1753092],q 2 [16392,21709,1753092],q 5 [21709,1753091],q 0 [20493,241680,241681,1191944],q 1 [241680,241681,1191944],q 0 [20484,20485,504299,16883],q 1 [20484,20485,504299,16883],q 0 [20484,20485,504299,12297],q 13 [16397,323612],q 0 [20484,20485,504299,12298],q 0 [20493,241673,253956],q 0 [20493,241671,241673,253956],q 13 [20493,253956],q 1 [241671,241673,253956],q 5 [20493,241673,253956],q 0 [20484,20485,504299,16394],q 0 [20484,20485,16392,1257961],q 5 [20484,20485,1257961],q 0 [20484,16392,1257961,16393],q 0 [16388,16389,12998],q 4 [73729,12998],q 4 [16392,1257961],q 3 [20484,1257961],q 0 [16388,8265,16389,12598],q 4 [8265,12598],q 14 [12598],q 1 [20485,241668,503824],q 0 [20485,20493,241668,503824],q 14 [503824],q 0 [20486,13502,20487],q 1 [20486,1209,20487],q 4 [1209,13502],q 0 [20486,9401,20487,1246393],q 1 [16395,241668,1208937],q 0 [20486,13497,20487,1246393],q 0 [20486,17593,20487,1246393],q 0 [20486,20487,1246393,12786],q 14 [12786],q 0 [20486,20487,16392,16393],q 18 [20486,20487],q 0 [16388,16389,12298,20489],q 0 [16392,16393],q 0 [20487,13505,16392,16393],q 3 [20487,13505],q 13 [20487,13505],q 18 [20487,13505],q 14 [13505],q 0 [16393,1265668],q 6 [16393,1265668],q 5 [20487,13505],q 0 [12298,20496,20497,155799],q 0 [16392,16393,20493,242900],q 1 [16392,16393,242900],q 13 [20493,242900],q 0 [16388,20488,61513,12865],q 1 [16393,1265668,241671],q 0 [16393,1265679,22561,20495],q 6 [16393,1265679],q 5 [22561,20495],q 1 [16388,241674,241675],q 14 [16395],q 0 [8196,8197,28699,16418],q 0 [20488,20489,65599,4165],q 0 [20488,20489,65599,16397],q 0 [20488,16397,323588,63529],q 5 [20488,63529],q 5 [20488,12349],q 1 [16390,16391,20488],q 0 [16390,16391,20488,12349],q 13 [16397,65852],q 1 [20489,65852],q 1 [20489,65852,823300],q 5 [12289,20488,61513],q 1 [241668,241669,1212432],q 0 [20493,241668,241669,1212432],q 6 [241668,241669,1212432],q 0 [20493,241668,241674,1209245],q 1 [241668,241674,1209245],q 0 [20493,241668,241682,1210425],q 1 [241668,241682,1210425],q 5 [9699],q 0 [20498,9699,20499],q 2 [20498,20499],q 13 [20498,20499],q 4 [20498,20499],q 0 [20498,5603,14053],q 1 [20498,5603],q 0 [20497,155652,14405],q 1 [20497,155652],q 5 [14405],q 0 [20496,151565,368651],q 1 [20496,368651],q 1 [20496,368648],q 0 [20496,151558,14413],q 1 [20496,151558],q 6 [14413],q 1 [241683,5775],q 0 [20493,241683,5775],q 6 [241683,5775],q 1 [241682,18491],q 0 [20493,241682,18491],q 0 [20493,241682,6203],q 1 [241682,6203],q 5 [20493,6203],q 0 [20493,241680,241681],q 1 [241680,241681],q 1 [241680,1187849],q 5 [20493,1187849],q 0 [20493,241680,1187846],q 1 [241680,1187846],q 6 [241680,1187846],q 5 [20493,1187846],q 5 [13793],q 1 [20498,20499],q 0 [20498,13793,20499],q 0 [20497,155663],q 2 [20497,155663],q 11 [],q 17 [],q 1 [241680,1187845],q 5 [20493,1187845],q 0 [20493,20498,13793],q 5 [20493,13793],q 0 [20493,20497,155652],q 4 [20493,20497],q 32 [],q 4 [20497],q 0 [20493,241680],q 0 [20493,241674,241680],q 1 [241674,241680],q 1 [241674,241675],q 1 [241674,17311],q 0 [20493,241674,17311],q 0 [20493,241674,5023],q 1 [241674,5023],q 1 [241673,253968],q 0 [20493,241673],q 0 [20493,241673,241683],q 1 [241673,241683],q 6 [241673],q 2 [20493,241683],q 2 [20493,241680],q 1 [241672,241680],q 0 [20493,241672,241680],q 6 [241672,241673],q 0 [20493,241672,16627],q 1 [241672,16627],q 3 [20493,16627],q 0 [20493,241671,241683],q 1 [241671,241683],q 6 [241671],q 6 [241683],q 0 [20493,241681],q 0 [20493,241671,241681],q 3 [20493,241681],q 13 [20493,241681],q 1 [241671,241681],q 6 [241681],q 0 [20493,241675],q 0 [20493,241671,241675],q 0 [20493,241671,241673],q 1 [241671,241673],q 0 [20493,241670],q 0 [20493,241670,241680],q 0 [20493,241670,22305],q 1 [241670,22305],q 4 [20493,22305],q 0 [20493,241670,5923],q 1 [241670,5923],q 0 [20493,241669,1212439],q 1 [241668,241680],q 6 [241668,241680],q 0 [20493,241668,241669],q 1 [241668,241669],q 0 [20493,241681,1191943],q 1 [241681,1191943],q 6 [241681,1191943],q 0 [20493,241668],q 0 [20493,241668,20498],q 1 [20498],q 1 [241668],q 14 [20498],q 1 [241668,20498],q 6 [241668],q 3 [20498],q 13 [20498],q 0 [16399,4651,22641],q 1 [4651,22641],q 15 [22641],q 5 [4651,22641],q 6 [16399,4651],q 15 [22506],q 0 [16399],q 0 [16399,4649,22506],q 13 [16399],q 3 [16399],q 1 [4649,22506],q 0 [16397,20498,325091],q 0 [16397,323588,22569],q 1 [323588,22569],q 6 [16397,323588],q 5 [22569],q 0 [20491,4775,14469],q 1 [20491,4775],q 0 [20499,5531,14477],q 1 [20499,5531],q 6 [14477],q 0 [20498,5603],q 0 [20490,20498,5603],q 5 [20490],q 6 [5603],q 15 [20490],q 0 [20497,155652],q 0 [20490,20497,155652],q 13 [20497,155652],q 6 [155652],q 0 [20490,20493,241680],q 1 [20490,241680],q 4 [20490],q 6 [241680],q 0 [20490,20493,241668],q 1 [20490,241668],q 13 [16399,4651],q 1 [20490,4651],q 0 [16397,323588],q 0 [20490,16397,323588],q 13 [16397,323588],q 1 [20490,323588],q 3 [16397,323588],q 2 [20490],q 13 [16397],q 0 [20490,20491,16397],q 1 [20490,20491],q 0 [20490,16759,20497],q 0 [20493,241668,241674],q 1 [241668,241674],q 1 [20490,16759],q 0 [20490,16759,20493],q 4 [20490,16759],q 3 [16759],q 0 [20490,4471],q 0 [20490,4471,20498],q 3 [4471],q 1 [20490,4471],q 6 [4471],q 0 [20489,65552,1949709],q 3 [1949709],q 0 [20489,65551],q 9 [],q 0 [20489,20493,65552],q 4 [20489,65552],q 13 [65552],q 0 [20489,16399,65551],q 15 [20489,65551],q 0 [20489,65540],q 0 [20489,65540,20498],q 13 [65540],q 15 [20489,65540],q 1 [20489,65540],q 6 [65540],q 0 [20489,65540,20493],q 0 [20488,16399,61993],q 1 [20488,61993],q 6 [16399],q 0 [20488,16397,323647],q 1 [20488,323647],q 0 [20488],q 2 [20488],q 2 [16397,323588],q 1 [20488,323588],q 4 [20488],q 5 [20488],q 0 [20488,20489],q 0 [20488,20489,16399],q 1 [20488,20489],q 15 [20488,20489],q 0 [20488,16447,16397],q 1 [20488,16447],q 4 [20488,16447],q 6 [16397],q 13 [397313],q 0 [20488,61446,14505],q 1 [20488,61446],q 13 [14505],q 0 [16395,20493,242283],q 1 [16395,242283],q 6 [16395,242283],q 0 [16395,21097,2277391],q 15 [2277391],q 5 [21097,2277391],q 0 [20493,20498,5603],q 0 [16395,12905,22714],q 15 [22714],q 5 [12905,22714],q 0 [20491,17063,14529],q 1 [20491,17063],q 3 [14529],q 0 [16395,4715,22213],q 5 [4715,22213],q 0 [16394,20495,415185],q 5 [20495],q 0 [16394,20493,243155],q 1 [16394,243155],q 1 [20498,5601],q 0 [20498,5601,13978],q 15 [13978],q 4 [20498],q 0 [16394,13777,22746],q 5 [22746],q 0 [16394,13777,22745],q 1 [16394,22745],q 13 [22745],q 5 [22745],q 6 [16394,13777],q 0 [16394,5587],q 0 [16394,5587,20495],q 6 [16394,5587],q 4 [20495],q 3 [20495],q 1 [16394,5587],q 0 [16394,5587,20493],q 0 [16394,5587,22757],q 5 [22757],q 0 [16394,5587,14565],q 13 [14565],q 5 [14565],q 0 [16393,21718,14577],q 1 [16393,21718],q 3 [14577],q 5 [14577],q 0 [16393,20493,242900],q 1 [16393,242900],q 6 [16393,242900],q 14 [16393],q 1 [16393,241671],q 0 [16393,1265679,22562],q 5 [22562],q 0 [16393,1265679,22561],q 1 [16393,22561],q 5 [22561],q 0 [16393,1265668,14057],q 1 [16393,1265668],q 3 [14057],q 0 [16392,21709,20495],q 1 [16392,21709],q 15 [20495],q 5 [21709,20495],q 0 [16392,21709,20493],q 5 [21709,20493],q 0 [16392,13517,22786],q 15 [22786],q 5 [13517,22786],q 0 [16392,13517,22785],q 1 [16392,22785],q 15 [22785],q 5 [13517,22785],q 0 [16392,13517,20493],q 5 [13517,20493],q 4 [16392,13517],q 0 [20488,20489,16397],q 6 [16392,1257478],q 0 [20495],q 0 [16392,1257478,20495],q 1 [16392,1257478],q 0 [16392,1257478,14605],q 13 [14605],q 15 [14605],q 4 [16392,14605],q 5 [1257478,14605],q 0 [20499,5531],q 0 [12298,20499,5531],q 13 [20499,5531],q 5 [12298],q 2 [12298],q 0 [12298,20498,5603],q 13 [20498,5603],q 4 [12298],q 15 [12298],q 0 [12298,20498,284129],q 5 [12298,284129],q 3 [20497,155663],q 0 [12298,20497,155663],q 13 [20497,155663],q 0 [12298,20497,155652],q 0 [12298,20497,155927],q 1 [20497,155927],q 13 [20497],q 13 [20496,151558],q 0 [12298,20496,151558],q 4 [20496],q 5 [151558],q 1 [20757,286723],q 0 [12298,4375],q 0 [12298,4375,20498],q 3 [4375],q 1 [4375],q 1 [4375,20498],q 6 [12298,4375],q 5 [12298,4375],q 0 [20496,151565,368647],q 1 [20496,368647],q 1 [16395,241672],q 0 [16395,20493,241672],q 0 [20496],q 0 [12298,4375,20496],q 1 [4375,20496],q 13 [20496],q 0 [20493,241672,245766],q 1 [241672,245766],q 0 [12298,4375,22813],q 1 [4375,22813],q 13 [22813],q 5 [12297],q 0 [12297,20498,20499],q 0 [12297,20498,296419],q 1 [20498,296419],q 15 [12297],q 5 [12297,296419],q 0 [12297,20497,155936],q 1 [20497,155936],q 0 [12297,20496,151842],q 3 [20496],q 5 [12297,151842],q 0 [12297,16672,20499],q 1 [16672,20499],q 3 [20499],q 6 [12297,16672],q 2 [20496],q 1 [294916,20496],q 0 [12297,294916],q 0 [12297,294916,20496],q 0 [20487,16395,1245801],q 3 [20487],q 4 [16395],q 5 [20487,1245801],q 15 [20487],q 0 [20487,16393,1265668],q 5 [20487],q 0 [20487,16392,16393],q 13 [20487],q 1 [16392,16393],q 18 [20487],q 3 [20487,21709],q 5 [20487,21709],q 0 [20487,17603,16397],q 1 [20487,17603],q 4 [20493,9373],q 1 [241668,9373],q 0 [20487,13505],q 0 [20487,13505,16395],q 1 [20487,16395],q 6 [16395],q 2 [20487,13505],q 4 [16394],q 1 [20487,16394],q 6 [16394],q 0 [16394],q 0 [20493,241681,1191959],q 0 [20487,13505,16392],q 1 [20487,16392],q 4 [16392],q 5 [20486],q 4 [16397,20798],q 0 [20486,16397,20798],q 0 [20486,16397,324795],q 1 [20486,324795],q 14 [16397],q 4 [16397,324795],q 6 [16397,324795],q 0 [20489,65552],q 2 [20489,65552],q 6 [65552],q 15 [20486],q 0 [20486],q 14 [20489,65552],q 0 [16395,12905],q 2 [16395,12905],q 6 [16395,12905],q 5 [12905],q 0 [16392,1257478,22797],q 0 [20486,16394,1524921],q 0 [20486,16393,1266875],q 6 [16393,1266875],q 3 [20486],q 0 [12298,16663],q 2 [12298,16663],q 6 [12298,16663],q 0 [20486,12298,16663],q 0 [20486,12298,283833],q 13 [20486],q 6 [12298,283833],q 1 [20486,283833],q 4 [12298,283833],q 14 [16399],q 4 [16399],q 0 [20486,20487],q 0 [20486,20487,16399],q 13 [20486,20487],q 3 [20486,20487],q 1 [20486,20487],q 0 [20486,20487,16397],q 0 [20486,20487,16392],q 5 [20486,20487],q 0 [16393,1265679,20495],q 0 [20486,20487,12298],q 4 [12297],q 0 [20486,20487,12297],q 4 [17595],q 0 [20486,17595,20487],q 1 [20486,17595],q 0 [20486,17595,20493],q 0 [20486,17595,1818637],q 14 [1818637],q 4 [17595,1818637],q 0 [20486,17595],q 0 [20486,17595,20490],q 13 [20486,17595],q 6 [17595],q 4 [13497],q 0 [20486,13497,20487],q 0 [16392,21709],q 5 [21709],q 15 [1753092],q 5 [21709,1753092],q 0 [20486,13497,20493],q 4 [13497,20493],q 14 [1998849],q 4 [13497,1998849],q 1 [20486,1998849],q 2 [20486,13497],q 0 [20486,20487,16393],q 0 [20486,9403,20487],q 0 [16395,4715,20493],q 1 [16395,4715],q 6 [16395,4715],q 5 [4715],q 0 [20486,13502],q 1 [20486,1209],q 6 [1209,13502],q 2 [20486],q 0 [20489,16399,66091],q 1 [20489,66091],q 2 [20486,17595],q 13 [20486,1209],q 3 [20486,1209],q 6 [1209,17595],q 0 [20490,16759],q 2 [20490,16759],q 6 [16759],q 0 [20486,20490,16759],q 0 [20486,17593],q 2 [20486,17593],q 6 [1209,17593],q 0 [20486,9401],q 2 [20486,9401],q 0 [20485,20498,5603],q 0 [20485,20497,155652],q 5 [20485],q 1 [20485,503824],q 0 [20485,20493,503824],q 5 [20485,20493],q 0 [20485,20493,503823],q 1 [20485],q 0 [20485,20493,241668],q 1 [20485,241668],q 5 [20485,503823],q 0 [20485,16399,503823],q 13 [20485,503823],q 15 [20485,503823],q 0 [20490,4471,20493],q 0 [20485,16399,504363],q 1 [20485,504363],q 0 [20485,16397,504124],q 1 [20485,504124],q 0 [20489,65540,14489],q 3 [14489],q 0 [20485,20490,4471],q 0 [20485,20489,65540],q 0 [20491,16399,692777],q 15 [20491],q 5 [20491,692777],q 3 [20485,503823],q 0 [20485,16395,503823],q 1 [16395],q 0 [20485,16395,504427],q 0 [20486,16392,16393],q 18 [20486],q 0 [20485,16392,16393],q 18 [20485],q 0 [20493,241673,253971],q 1 [241673,253971],q 0 [20485,16392,21709],q 0 [20489,20497,65552],q 0 [16392,16393,20493],q 18 [20493],q 0 [20485,12298,503823],q 0 [20485,12297,504096],q 1 [20485,504096],q 0 [20484,16399,500265],q 1 [241671,241680],q 0 [20484,16397,324075],q 4 [16397,324075],q 0 [20484,16394,501201],q 3 [20484,501201],q 0 [20493,20497,241680],q 1 [20497,241680],q 0 [20484,16393,1266155],q 3 [20484],q 1 [20484,16393,1266155],q 0 [20498,20499],q 0 [20498,5603,20499],q 0 [20484,16392,16393],q 13 [20484],q 18 [20484],q 0 [20484,16392,1257961],q 5 [20484,1257961],q 1 [20484,16392,1257961],q 15 [20484],q 0 [20484,12298,16663],q 1 [20484,16663],q 3 [16663],q 0 [20493,241668,241680],q 0 [20496,20497],q 0 [12298,20496,20497],q 1 [20496,20497],q 0 [20485],q 0 [20485,16393,1265679],q 4 [16393,1265679],q 1 [20485,16393],q 0 [12297,16672],q 0 [20484,12297,16672],q 1 [20484,16672],q 0 [20484,20485],q 0 [20484,20485,16395],q 3 [20484,20485],q 1 [20484,20485],q 13 [20484,20485],q 15 [20484,20485],q 0 [20484,20485,16393],q 0 [20487,16394,1246673],q 1 [20487,16394,1246673],q 0 [20484,20485,12298],q 0 [20484,20485,12297],q 6 [12297],q 0 [20496,16535,13793],q 1 [20496,16535],q 0 [20484,16875,16397],q 4 [16875,16397],q 5 [20484],q 1 [20484,16875],q 3 [20484,16875],q 0 [20484,16875,16393],q 4 [16875,16393],q 13 [20484,16875],q 0 [20484,16875,12298],q 0 [12293,21218,20496],q 6 [12293],q 0 [12293,21218],q 1 [21218,2153],q 4 [2153],q 0 [12293,17120,22389],q 1 [17120,22389],q 4 [22389],q 6 [12293,17120],q 0 [20484,16395,500329],q 4 [16395,500329],q 5 [20484,500329],q 2 [20499,5531],q 0 [12293,20488,20489],q 3 [12293],q 0 [12293,16395,754283],q 1 [16395,754283],q 13 [12293,754283],q 1 [8198,241680],q 5 [8198],q 1 [16394,21969],q 0 [16394,21969],q 0 [12293,16394,21969],q 4 [16394,21969],q 5 [12293],q 0 [12293,20496,152290],q 1 [20496,152290],q 0 [16390,20490,536949],q 4 [20490,536949],q 0 [16395,4715],q 0 [16395,4715,20495],q 0 [20487,16397,324803],q 1 [20487,324803],q 2 [20496,151558],q 13 [2318337],q 1 [16394,2318337],q 0 [8196,8197,16397],q 1 [8196,8197],q 0 [12293,16392,21709],q 2 [12293],q 15 [12293],q 1 [241668,17567],q 4 [20493,17567],q 6 [241668,17567],q 0 [16392,1257478,20493],q 5 [1257478],q 0 [12293,16392,13517],q 3 [12293,13517],q 1 [16392],q 5 [12293,13517],q 1 [241670,18211],q 0 [20493,241670,18211],q 5 [20493,241670],q 0 [16388,12361,20553],q 0 [12293,20496,151558],q 3 [20496,151558],q 5 [12293,151558],q 1 [16390,20490],q 6 [16390],q 0 [12293,16392,1257478],q 5 [12293,1257478],q 3 [12293,1257478],q 5 [12289,20491],q 1 [16390,20491],q 0 [8196,16411,14757],q 1 [8196,16411],q 3 [16411,14757],q 4 [16411,14757],q 14 [14757],q 13 [14757],q 0 [12293,16392,16393],q 13 [12293],q 18 [12293],q 0 [16388,20554,14765],q 1 [16388,20554],q 4 [1209],q 1 [20485,16395],q 13 [12294,20485],q 0 [16389,77832,20493],q 1 [16389,77832],q 6 [16389,77832],q 0 [20487,17603],q 0 [20487,17603,12298],q 13 [20487,17603],q 2 [16395,4715],q 13 [12289,4715],q 5 [12289,4715],q 0 [8199,16397,325087],q 1 [8199,325087],q 0 [8199,21981],q 0 [8199,21981,16399],q 3 [21981],q 5 [8199,21981],q 1 [8199,21981],q 6 [8199],q 2 [16399],q 3 [12289,20496],q 4 [12289,20496],q 1 [8196,20496],q 2 [8196,20496],q 13 [12289,20496],q 2 [8199,21981],q 4 [2551811],q 0 [8199,17887,22981],q 4 [22981],q 0 [16399,20497,156203],q 1 [20497,156203],q 0 [8199,13789,22994],q 1 [8199,22994],q 4 [22994],q 13 [22994],q 0 [16391,12298,20757],q 1 [16391,20757],q 2 [16391],q 0 [20485,16395,12905],q 4 [16395,12905],q 0 [20484,12777,12297],q 3 [20484,12777],q 1 [20484],q 14 [12297],q 4 [12777,12297],q 0 [16392,21709,1753103],q 15 [1753103],q 5 [21709,1753103],q 0 [8198,20496,20497],q 6 [8198],q 0 [16393,1265668,22249],q 5 [22249],q 2 [20488,61446],q 0 [8198,20496,151565],q 5 [151565],q 2 [16392],q 2 [20487,16392],q 0 [16388,12361,20493],q 0 [16390,12298,20489],q 1 [16390,20489],q 0 [16388,20489,65551],q 1 [16388,20489],q 0 [8198,16392,20493],q 1 [8198,16392],q 15 [8198],q 0 [8198,8199],q 0 [8198,8199,20495],q 1 [8198,8199],q 0 [16391,20488,61957],q 3 [16391,61957],q 6 [16391],q 0 [8198,8199,16399],q 15 [8198,8199],q 2 [20493,241673],q 0 [16388,20493],q 2 [16388,20493],q 1 [16388,241673],q 1 [16389,241674],q 14 [22342],q 13 [12294,22342],q 0 [12294],q 0 [12294,8917,22342],q 1 [8917,22342],q 5 [12294],q 3 [12294],q 0 [12293,16394,755155],q 1 [16394,755155],q 0 [8197,20496,20497],q 0 [8198,21885,2600975],q 14 [2600975],q 4 [21885,2600975],q 3 [2600975],q 5 [8199],q 0 [8199,20498,20499],q 0 [12293,20491,754343],q 4 [20491],q 0 [16388,20555,13057],q 1 [16388,20555],q 5 [20555,13057],q 0 [8198,20498,1439201],q 4 [20498,1439201],q 1 [8198,20498,1439201],q 0 [16388,20553,20490],q 1 [241669,1212432],q 0 [20493,241669,1212432],q 5 [20493,241669],q 2 [16388,20495],q 17 [20495],q 4 [73729,20495],q 0 [8198,17791],q 0 [8198,17791,20495],q 6 [8198,17791],q 4 [17791],q 17 [20493],q 0 [16388,8267,20493],q 0 [8198,17791,22349],q 14 [22349],q 4 [17791,22349],q 0 [8198,17791,14157],q 3 [14157],q 4 [17791,14157],q 14 [14157],q 0 [8196,16399,25129],q 1 [8196,25129],q 4 [16399,25129],q 0 [8198,13693,23045],q 1 [8198,23045],q 3 [23045],q 14 [23045],q 4 [13693,23045],q 0 [16388,16389,12297],q 0 [8197,20499,30107],q 1 [8197,20499,30107],q 0 [8198,8199,16397],q 0 [8197,20498,30179],q 0 [8197],q 0 [8197,20497,155663],q 2 [8197],q 4 [20497,155663],q 1 [8197],q 0 [8197,20495,29079],q 1 [8197,29079],q 0 [12293,20486],q 2 [12293,20486],q 0 [16393,1265668,20495],q 2 [20495],q 0 [8196,12313,22406],q 14 [22406],q 4 [12313,22406],q 0 [8198,8199,20496],q 15 [8197],q 1 [8197,241683],q 15 [23070],q 0 [16399,8745,23070],q 1 [8745,23070],q 0 [12293,20489,66272],q 1 [20489,66272],q 0 [8196,20499,26009],q 0 [12294,20489,66263],q 1 [20489,66263],q 4 [20489,66263],q 6 [12294,66263],q 0 [16399,21033],q 0 [8197,16399,21033],q 1 [8197,21033],q 3 [16399,21033],q 4 [16399,21033],q 5 [21033],q 2 [16389,20558],q 5 [9697],q 0 [20498,9697,20499],q 0 [8197,16399,29227],q 1 [8197,29227],q 0 [8196,16411,20497],q 3 [16411,20497],q 4 [16411,20497],q 5 [8196],q 1 [8196,16411,20497],q 0 [16389,12298,78103],q 1 [16389,78103],q 0 [20487,16393,1266883],q 0 [8199,17887],q 0 [8199,17887,20495],q 6 [8199,17887],q 1 [8199,17887],q 1 [8197,323612],q 0 [8197,20510,16399],q 5 [8197,20510],q 0 [8199,20493,241668],q 1 [8199,241668],q 6 [8199,241668],q 0 [8196,8197],q 0 [8196,8197,20499],q 13 [20499],q 0 [16395,20495,631189],q 5 [20495,631189],q 0 [16397],q 0 [8197,20510,16397],q 1 [8197,20510],q 0 [20489,20493],q 2 [20489,20493],q 0 [16389,20493],q 2 [16389,20493],q 6 [16389],q 0 [20485,503824],q 0 [20485,20490,503824],q 6 [503824],q 5 [12293,21218],q 0 [12293,21218,20498],q 0 [16388,20488,20489],q 2 [20488,20489],q 1 [16388,20488,20489],q 0 [20484,12297,295403],q 1 [20484,295403],q 4 [12297,295403],q 0 [16389,77839,20495],q 1 [20486,20487,16395],q 15 [20486,20487],q 0 [8197,16412,20495],q 1 [8197,16412],q 0 [20490,16399],q 2 [20490,16399],q 1 [20490,4649],q 0 [16393,20495,1266071],q 1 [16393,1266071],q 0 [8197,16412,16397],q 0 [20485,503824,2109453],q 4 [2109453],q 2 [16388,12298],q 0 [12298],q 5 [73729,12298],q 0 [20486,17595,20497],q 4 [17595,20497],q 0 [8197,16412,22205],q 4 [22205],q 0 [16395,4715,14021],q 3 [14021],q 5 [4715,14021],q 15 [14021],q 0 [8196,16397,323611],q 3 [16397,323611],q 4 [16397,323611],q 1 [8196,323611],q 0 [8196,20497,155675],q 0 [8198,20497,157055],q 0 [8197,16412,14013],q 3 [14013],q 4 [14013],q 0 [8198,21885],q 0 [8198,21885,16399],q 4 [21885],q 5 [8198,21885],q 1 [8198,21885],q 0 [16394,20493,241680],q 1 [16394,241680],q 0 [20484,12777],q 0 [20484,12777,16395],q 4 [12777],q 0 [16388,16389,12298],q 0 [8199,20496,20497],q 0 [16389,20490,20491],q 2 [20490,20491],q 0 [8197,12318,20495],q 2 [16399,21033],q 1 [21033,2670595],q 15 [2670595],q 5 [21033,2670595],q 0 [20484,20485,16399],q 0 [8196,8197,20498],q 1 [8196,8197,20498],q 0 [12297,20496,20497],q 0 [12294,16392,1258197],q 1 [16392,1258197],q 13 [12294],q 4 [16392,1258197],q 5 [12294,1258197],q 0 [8197,12318,22418],q 4 [22418],q 3 [22418],q 0 [12293,16393,1266400],q 1 [16393,1266400],q 5 [20488,61513],q 15 [20488],q 0 [8198,20493,243071],q 1 [8198,243071],q 0 [20490,20491],q 0 [12294,20490,20491],q 14 [20490,20491],q 0 [16388,8267,20495],q 0 [16391,20491,529061],q 3 [16447],q 5 [12289,21709],q 0 [16388,8265,12598],q 13 [16388,12598],q 5 [8265,12598],q 0 [16392,20493,242895],q 5 [20493,242895],q 0 [16388,20553,12298],q 0 [8197,16412,20493],q 1 [16391,20490],q 0 [20491,17063,16397],q 5 [20491],q 2 [16391,20997],q 4 [2756611],q 15 [2756611],q 5 [20997,2756611],q 0 [16388,12361,21065],q 1 [16388,21065],q 5 [12361,21065],q 0 [8198,8199,20498],q 1 [8198,8199,20498],q 1 [20487,16393],q 0 [20487,13505,16393],q 6 [16393],q 0 [16390,12297,20490],q 0 [16388,20553,20491],q 4 [20553,20491],q 5 [20553,20491],q 0 [12294,20490,16759],q 0 [20486,16392,1258681],q 4 [16392,1258681],q 4 [12289,16875],q 2 [20484,16875],q 5 [12289,20553],q 6 [12289,16388],q 0 [8199,20496,153053],q 3 [20496,153053],q 1 [8199,20496,153053],q 5 [8199,153053],q 15 [8199],q 0 [16389,20489,65551],q 2 [16389],q 1 [16389,20489],q 0 [8196,8197,20493],q 0 [16390,20493],q 2 [16390,20493],q 1 [16388,241674],q 0 [16390,4623,20495],q 3 [16390,4623],q 13 [16390,4623],q 1 [16390,4623],q 13 [12289,16391],q 2 [16391,20490],q 3 [12289,16391],q 0 [8199,20499,1537433],q 4 [20499],q 1 [8199,20499,1537433],q 1 [16391,20997],q 5 [12289,20997],q 6 [12289,16391],q 2 [20491,17063],q 0 [8196,12313],q 3 [12313,1970177],q 4 [12313,1970177],q 1 [8196,1970177],q 14 [1970177],q 13 [1970177],q 2 [8196,12313],q 0 [20491,16397,324263],q 1 [20491,324263],q 0 [16388,20495,74133],q 4 [20495,74133],q 5 [20495,74133],q 1 [16390,241674],q 6 [16397,65852],q 0 [20487,16392,1258689],q 5 [20487,1258689],q 3 [20487,1258689],q 0 [8197,20496,151582],q 1 [8197,20496,151582],q 2 [20487],q 2 [20487,16395],q 2 [8197,16412],q 1 [16395,21097],q 0 [16395,21097],q 0 [12293,16395,21097],q 4 [16395,21097],q 5 [21097],q 0 [12294,20499,742809],q 1 [20499,742809],q 4 [20499,742809],q 6 [12294],q 10 [16390],q 2 [16390],q 13 [12289,16388],q 1 [16388,20490],q 10 [20490],q 0 [12297,16672,22197],q 1 [16672,22197],q 4 [17593],q 0 [20486,17593,20487],q 0 [8198,13693],q 0 [8198,13693,20498],q 4 [13693],q 1 [8198],q 1 [8198,20498],q 0 [16391,20489,65540],q 0 [8196,20505,20495],q 1 [8196,20505],q 4 [20505,20495],q 0 [12293,16392,754895],q 1 [16392,754895],q 5 [12293,754895],q 3 [12293,754895],q 1 [20484,16395],q 2 [20484],q 2 [20484,16395],q 18 [12289,20484],q 2 [8199,17887],q 0 [8198,13693,23046],q 14 [23046],q 4 [13693,23046],q 1 [241681,1191947],q 0 [12293,20490,754039],q 1 [20490,754039],q 3 [12293,754039],q 0 [8199,20496,151565],q 1 [8199,20496],q 2 [16394,21969],q 6 [12289,16394],q 0 [8198,16397,324991],q 1 [8198,324991],q 13 [16397,324991],q 4 [16397,324991],q 0 [16389,20558,14901],q 1 [16389,20558],q 4 [14901],q 5 [14901],q 0 [8199,17887,14789],q 4 [14789],q 3 [17887,14789],q 13 [14789],q 0 [16391,20488,20489],q 2 [20488,16447],q 0 [8196,16395],q 0 [8196,16395,20495],q 6 [8196,16395],q 13 [20495],q 1 [8196,16395],q 15 [8196],q 0 [8197,20497,155676],q 1 [8197,20497,155676],q 13 [20493,243071],q 6 [8198,243071],q 14 [22442],q 0 [12294,17109,22442],q 13 [12294,17111],q 1 [17111,20490],q 0 [8196,20496,151565],q 0 [16390,12297,20770],q 1 [16390,20770],q 0 [8199,20497,155652],q 0 [16388,20553,307213],q 6 [16388,307213],q 0 [12293,20491,4775],q 13 [12289,17791],q 4 [12289,17791],q 2 [8198,17791],q 2 [16393,21718],q 3 [12293,21218],q 2 [16395],q 15 [12293,21218],q 0 [16388,20553,20493],q 0 [8196,20505,20499],q 4 [20505,20499],q 0 [12293,16393,1265668],q 0 [20485,12298,503824],q 3 [20485,503824],q 13 [20485,503824],q 4 [12289,20497],q 2 [8197,20497],q 5 [12289,8197],q 10 [8197],q 2 [20485],q 2 [20485,16395],q 13 [12289,20485],q 0 [12293],q 0 [12293,16393,21718],q 0 [8199,20497,157151],q 1 [16389,77835],q 2 [16389,77835],q 0 [20493,241682,22585],q 1 [241682,22585],q 5 [20493,22585],q 0 [16388,20553,307215],q 0 [8198,17791,20493],q 0 [8196,20505,20493],q 3 [20505,20493],q 4 [20505,20493],q 0 [12293,20490,20491],q 0 [12294,20490],q 2 [12294,20490],q 1 [17109,20490],q 0 [8198,21885,16397],q 1 [16389,241672],q 0 [20484,4587,13497],q 1 [20484,4587],q 2 [20498,5603],q 5 [12289,5603],q 0 [16391,12298,528661],q 1 [16391,528661],q 2 [8196,16395],q 15 [12289,8196],q 5 [12289,8196],q 2 [16394,5587],q 0 [12294,16395,21097],q 3 [12289,20486],q 1 [20486,16395],q 2 [20486,16395],q 10 [16395],q 2 [8197,20510],q 2 [8198,21885],q 4 [12289,21885],q 6 [12289,8198],q 0 [8196,20493,241691],q 4 [20493,241691],q 1 [8196,241691],q 13 [12294,21207],q 0 [16388,20490,20491],q 1 [16388,20490,20491],q 6 [8197],q 0 [16399,20497],q 0 [8197,16399,20497],q 0 [8198,20499,1439129],q 13 [20499,1439129],q 1 [8198,20499,1439129],q 1 [16391,241675],q 2 [16388,20490],q 0 [20490],q 5 [73729,20490],q 0 [20485,16394,503824],q 0 [20493,241682,241683],q 1 [241682,241683],q 0 [12293,20486,754875],q 0 [8197,20510,14913],q 3 [14913],q 4 [14913],q 14 [18275],q 0 [12294,21207,18275],q 1 [21207,18275],q 0 [16390,20495,414221],q 4 [20495,414221],q 0 [20490,16397,323959],q 1 [20490,323959],q 2 [16389,77832],q 4 [9401],q 0 [20486,9401,20487],q 2 [16393],q 2 [20487,16393],q 6 [12289,16393],q 3 [12289,16388],q 0 [12297,294916,22457],q 1 [294916,22457],q 3 [22457],q 1 [16389,20490],q 0 [16389,20490,12661],q 1 [241681,1191940],q 0 [20493,241675,241683],q 18 [12289],q 0 [16391,20997,2756623],q 4 [2756623],q 0 [20491,12965],q 0 [16391,20491,12965],q 1 [16391,20491],q 2 [20493,241675],q 1 [16388,241675],q 14 [598017],q 4 [12361,598017],q 1 [16388,598017],q 0 [8196,8197,20497],q 2 [8196,8197],q 1 [16388,20488],q 10 [20488],q 10 [16388],q 0 [20485,20497,503824],q 0 [16389,20488,20489],q 0 [8199,17887,20493],q 0 [16390,12298,283149],q 1 [16390,283149],q 4 [12298,283149],q 0 [16390,4623,12298],q 0 [8196,16411,16397],q 3 [16411,16397],q 4 [16411,16397],q 5 [73729,20493],q 0 [12293,20488,12349],q 0 [8197,20496,151558],q 1 [8197,20496,151558],q 10 [20489],q 10 [16389],q 1 [16391,242183],q 0 [8199,20498,1537505],q 1 [8199,20498,1537505],q 6 [12289,16389],q 2 [16389,20490],q 13 [12289,16389],q 3 [12289,16389],q 6 [12289,65552],q 0 [16390,20489,65551],q 2 [16393,1265668],q 0 [12294,20485],q 0 [12294,20485,16393],q 0 [8199,21981,2551823],q 4 [2551823],q 2 [20485,503824],q 0 [20484,4587],q 2 [20484,4587],q 2 [16395,21097],q 5 [12289,21097],q 2 [20490,20493],q 0 [16390,12813,23297],q 1 [16390,23297],q 14 [23297],q 4 [12813,23297],q 5 [23297],q 6 [16390,12813],q 2 [16391,12805],q 0 [12293,17120],q 0 [12293,20490,17120],q 1 [17120],q 1 [20490,17120],q 13 [12293,17120],q 3 [12293,17120],q 0 [16391,20489,66055],q 4 [12289,16394],q 10 [20487],q 2 [20487,16394],q 6 [12289,16759],q 0 [8196,20505],q 0 [8196,20505,1785875],q 4 [20505],q 3 [20505],q 14 [1785875],q 4 [20505,1785875],q 0 [20487,12297,296131],q 1 [20487,296131],q 1 [16388,8265,20790],q 1 [16390,20488],q 2 [16390,20488],q 0 [8197,20496,151565],q 1 [8197,20496],q 2 [20489,65540],q 2 [20490,4471],q 6 [12289,4471],q 0 [16395,12905,22713],q 1 [16395,22713],q 3 [22713],q 15 [22713],q 5 [12905,22713],q 13 [12294,17108],q 0 [12294,17108,20490],q 1 [17108,20490],q 3 [12294,17108],q 2 [20491,4775],q 0 [12293,20498,755171],q 1 [20498,755171],q 0 [8199,20493,243167],q 1 [8199,243167],q 0 [20498,13793],q 0 [8198,20498,13793],q 3 [20498,13793],q 13 [20498,13793],q 0 [8199,20495,1536405],q 2 [20497,155652],q 0 [20485,503823],q 0 [8196,12313,20493],q 4 [12313,20493],q 5 [8196,12313],q 0 [8196,20505,16397],q 1 [8196,241680],q 0 [8196],q 0 [8196,20493,241680],q 1 [8197,241680],q 0 [8196,12313,22405],q 1 [8196,22405],q 3 [12313,22405],q 4 [12313,22405],q 14 [22405],q 0 [16388,8267,12361],q 5 [12361],q 4 [12361],q 1 [16389,20488],q 0 [16389,20488,12349],q 3 [12349],q 1 [16390,241675],q 4 [12289,20498],q 3 [16397,20798],q 0 [8198,16397,20798],q 14 [16397,20798],q 0 [16390,16391,12298],q 0 [20493,241668,241672],q 1 [241668,241672],q 0 [16399,4651],q 0 [20490,16399,4651],q 5 [4651],q 3 [16399,4651],q 2 [8198,8199],q 0 [20484,12298,499989],q 1 [20484,499989],q 4 [12298,499989],q 3 [12289,20505],q 4 [12289,20505],q 2 [8196,20505],q 0 [16389,77839,21774],q 4 [21774],q 5 [21774],q 1 [16389,21774],q 3 [16397,20498],q 0 [8198,16397,20498],q 0 [8196,16411,22949],q 14 [22949],q 4 [16411,22949],q 0 [8196,16411,20493],q 4 [16411],q 0 [8196,20505,1785872],q 14 [1785872],q 4 [20505,1785872],q 0 [12294,17111],q 2 [12294,17111],q 6 [12294,17111],q 1 [17111,20488],q 0 [12294,17111,20488],q 4 [17111],q 6 [8196,16411],q 0 [8196,16411,20495],q 0 [16388,20489,65611],q 6 [16388,65611],q 0 [8196,20505,20497],q 0 [16388,20553,307208],q 6 [16388,307208],q 0 [8197,20498,13793],q 1 [8197,20498],q 4 [20498,13793],q 0 [16388,20554],q 0 [20485,16393],q 2 [20485,16393],q 0 [8199,13789,22993],q 1 [8199,22993],q 4 [22993],q 0 [12294,8917,18244],q 1 [8917,18244],q 14 [18244],q 2 [16392,1257478],q 3 [12289,1257478],q 5 [12289,1257478],q 0 [16390,20488,20489],q 0 [8196,8197,16399],q 15 [8196,8197],q 0 [8196,8197,20495],q 0 [20486,16399,566457],q 4 [16399,566457],q 0 [8198,8199,20493],q 0 [16388,20553,307210],q 6 [16388,307210],q 0 [8196,20495,24981],q 1 [8196,24981],q 3 [20495,24981],q 4 [20495,24981],q 4 [20489,66063],q 6 [16390,66063],q 0 [8197,16397,20798],q 0 [12293,20499,755099],q 1 [20499,755099],q 4 [20496,151577],q 3 [20496,151577],q 5 [8196,151577],q 0 [16388,12298,20757],q 1 [16388,20757],q 0 [8196,20505,16399],q 0 [12293,20496,151565],q 5 [12293,151565],q 0 [12293,20496,20497],q 0 [12294,21205],q 0 [12294,21205,16395],q 3 [12294,21205],q 4 [21205],q 1 [21205,16395],q 13 [12294,21205],q 2 [20487,17603],q 0 [12293,20497,156384],q 1 [20497,156384],q 0 [12293,20499,5531],q 0 [8199,21981,16397],q 2 [16397],q 1 [8917,20498],q 5 [5601],q 0 [20498,5601,20499],q 1 [20498,5601,20499],q 1 [241673,253956],q 0 [12294,20491,692949],q 1 [20491,692949],q 14 [20491],q 4 [20491,692949],q 0 [12294,17111,20490],q 3 [12294,17111],q 0 [12294,17111,23237],q 1 [17111,23237],q 14 [23237],q 4 [17111,23237],q 0 [8198,8199,20497],q 0 [16390,4623,20490],q 0 [12294,21206,22305],q 1 [21206,22305],q 0 [12294,20485,504535],q 6 [12294,504535],q 0 [20485,12298,504087],q 1 [20485,504087],q 13 [20485],q 0 [16391,12805,22482],q 1 [16391,22482],q 4 [22482],q 0 [12294,16392,16393],q 14 [16392,16393],q 18 [12294],q 0 [12294,20489,65551],q 0 [12294,16393,1266391],q 1 [16393,1266391],q 4 [16393,1266391],q 3 [12289,16411],q 4 [12289,16411],q 2 [8196,16411],q 0 [16390,20491,692749],q 1 [16390,20491,692749],q 4 [20491,692749],q 0 [12294,16393,21718],q 0 [12294,16394,742865],q 1 [16394,742865],q 4 [16394,742865],q 0 [16388,12361,20489],q 2 [20489],q 3 [12293,20486],q 0 [12293,20486,16395],q 0 [16391,20490,528757],q 6 [16391,528757],q 1 [16391,20490,528757],q 3 [16391,528757],q 0 [20488,12349,16397],q 0 [12294,16394,21969],q 3 [21969],q 0 [16388,12361,20490],q 0 [8196,16395,20493],q 1 [21205,16393],q 0 [12294,21205,16393],q 5 [12294,21205],q 0 [12294,16395,631509],q 1 [16395,631509],q 5 [12294,631509],q 4 [16395,631509],q 2 [16392,13517],q 5 [12289,13517],q 0 [16388,8265,20553],q 0 [12297,20496,151565],q 5 [12297,151565],q 0 [8197,20498,20499],q 0 [16388,20553,20495],q 5 [20553,20495],q 0 [12294,20488,20489],q 0 [8197,16412,20499],q 0 [12294,20489,65552],q 0 [16392,21709,1753095],q 3 [21709],q 15 [1753095],q 0 [8196,20498,20499],q 0 [12294,20490,741749],q 1 [20490,741749],q 4 [20490,741749],q 0 [20486,13497],q 5 [20486,1209],q 0 [20491,17063],q 0 [12294,20491,17063],q 0 [12294,20496,152277],q 1 [20496,152277],q 4 [20496,152277],q 5 [12294,152277],q 0 [12294,20496,16535],q 3 [20496,16535],q 13 [20496,16535],q 0 [16388,20553,20489],q 4 [20553,20489],q 5 [20553,20489],q 0 [16390,16391,20490],q 0 [20485,16392,1257478],q 5 [20485,1257478],q 3 [20485,1257478],q 1 [20485,16392,1257478],q 0 [12294,20497,155663],q 1 [20497],q 14 [20497,155663],q 0 [12294,20498,742881],q 1 [20498,742881],q 4 [20498,742881],q 1 [16390,241672],q 14 [20498,20499],q 0 [12294,20498,20499],q 13 [16389,77839],q 0 [16392,20495,1257877],q 5 [20495,1257877],q 0 [16388,8265],q 2 [16388,8265],q 5 [73729,8265],q 0 [20493,241681,1191944],q 1 [241681,1191944],q 6 [241681,1191944],q 0 [8198,20495,1438101],q 13 [20495,1438101],q 1 [8198,1438101],q 4 [20495,1438101],q 0 [12293,20488,753727],q 1 [20488,753727],q 0 [20484,20485,16394],q 0 [8197,12318,22417],q 1 [8197,22417],q 4 [22417],q 0 [16388,12361,20488],q 2 [16388,20488],q 0 [16389,20495,78231],q 1 [16389,78231],q 2 [8198,16392],q 15 [12289,8198],q 5 [12289,8198],q 5 [73729,20555],q 4 [73729,20555],q 0 [16388,12998],q 4 [12289,17595],q 6 [12289,17595],q 0 [16391,12805,22481],q 1 [16391,22481],q 4 [22481],q 5 [73729,20488],q 0 [16388,20488],q 4 [73729,20488],q 0 [8196,8197,20496],q 1 [16395,241668],q 0 [16388,8265,12361],q 0 [16388,8265,16389],q 4 [8265],q 0 [20493,241670,241671],q 1 [241670,241671],q 0 [12298,20496,151829],q 1 [20496,151829],q 5 [12298,151829],q 0 [16388,8265,12298],q 5 [8265,12298],q 0 [16388,8265,20493],q 0 [16392,16393,20495],q 18 [20495],q 0 [16388,8265,20495],q 0 [20487,16397,323588],q 1 [20487,323588],q 1 [16388,241672],q 0 [8198,16392],q 0 [8198,16392,20495],q 6 [8198,16392],q 5 [20555],q 5 [8267],q 0 [16388,8267,20555],q 0 [12293,20488,61446],q 5 [20488,61446],q 0 [16388,8267,16389],q 0 [16391,12297,20490],q 0 [16388,12361,12297],q 4 [12361,12297],q 5 [12361,12297],q 0 [16391,20493],q 2 [16391,20493],q 1 [16391,241673],q 5 [12361,20493],q 6 [12289,394427],q 0 [20490,16759,2146317],q 13 [2146317],q 0 [16388,12361,21066],q 4 [12361,21066],q 5 [12361,21066],q 0 [20493,241669],q 0 [20493,241669,241683],q 3 [20493,241669],q 13 [20493,241669],q 1 [241669,241683],q 6 [241669],q 0 [20490,4471,14485],q 13 [14485],q 0 [20484,20485,16397],q 0 [16390,12813,20489],q 2 [16390,12813],q 3 [16390,12813],q 4 [12813],q 0 [8197,16397,20498],q 5 [20553,20493],q 5 [20553,307215],q 0 [16388,20554,22957],q 4 [20554,22957],q 5 [20554,22957],q 0 [16388,20555,12298],q 1 [16395,241671],q 0 [20487,16399,1245737],q 2 [12293,17120],q 1 [20488,17120],q 0 [8199,16399,1536553],q 1 [8199,1536553],q 1 [16388,241736],q 6 [16388,241736],q 1 [16391,241668],q 0 [16388,20555,20493],q 3 [16388,20555],q 0 [12298,16663,22861],q 1 [16663,22861],q 13 [22861],q 0 [16388,20490,12661],q 0 [16392],q 0 [16392,20493,241668],q 1 [16392,241668],q 0 [20487,12298,1245461],q 1 [20487,1245461],q 0 [16389,77839,21773],q 1 [16389,21773],q 4 [21773],q 0 [16388,16389,20489],q 0 [16393,1265668,20493],q 0 [16388,16389,20491],q 0 [16388,16389,20495],q 0 [8196,20505,1785871],q 14 [1785871],q 4 [20505,1785871],q 13 [1785871],q 0 [16388,12297,294987],q 5 [12297,294987],q 1 [16388,294987],q 4 [12297,294987],q 2 [20496,20497],q 2 [12297,20490],q 0 [16388,12297,20490],q 0 [8198,8199,20499],q 1 [8198,8199,20499],q 1 [16391,241672],q 5 [12298,74005],q 0 [20493,241668,241682],q 0 [16388,12298,20489],q 2 [12298,20489],q 0 [12297,20499,296347],q 1 [20499,296347],q 2 [20496,16535],q 0 [20487,17603,14645],q 4 [14645],q 0 [16388,20488,12349],q 6 [16388,74101],q 2 [20498,5601],q 0 [20497],q 0 [8197,12318,20497],q 1 [8197,20497],q 5 [8197,12318],q 0 [16388,20491,74405],q 4 [20491,74405],q 5 [20491,74405],q 0 [20484,20485,16392],q 5 [20490,74101],q 2 [20491,12965],q 0 [16388,20491,12965],q 1 [20491],q 0 [16390,16391,20489],q 0 [16388,20493,241737],q 1 [16388,241737],q 0 [16390,12297,295439],q 1 [16390,295439],q 4 [12297,295439],q 1 [16388,241668],q 6 [16388,241668],q 0 [16388,20555,16389],q 0 [16389,12297,20490],q 0 [12298,20498,20499],q 0 [16391,12297,295431],q 0 [16389,12297,78112],q 1 [16389,78112],q 0 [20485,16393,503823],q 1 [16393],q 0 [16389,12297,20770],q 1 [16389,20770],q 0 [16389,12298,20489],q 0 [8196,20496,20497],q 0 [16389,77832],q 0 [16389,77832,20495],q 0 [16389,77835,20493],q 6 [16389,77835],q 0 [16389,77835],q 0 [16389,77835,20495],q 0 [20486,17595,12298],q 2 [20484,16392],q 0 [16389,20488,61446],q 1 [16389,20488,61446],q 0 [16389,20488,16447],q 1 [16389,20488,16447],q 3 [16389,16447],q 0 [20490,16399,565621],q 6 [16399,565621],q 3 [16399,565621],q 0 [20484,16397,20798],q 1 [20484,20798],q 1 [16389,20757],q 0 [16389,12298,20757],q 0 [16389,20488,77887],q 1 [16389,20488,77887],q 3 [16389,77887],q 0 [12294,20497,156375],q 1 [20497,156375],q 14 [20497],q 4 [20497,156375],q 0 [20489],q 0 [16389,20489,77839],q 3 [16389,77839],q 0 [20490,20491,16399],q 15 [20490,20491],q 0 [20487,12297,294916],q 1 [20487,294916],q 0 [16390,20490,20491],q 0 [12294,20488,62165],q 1 [20488,62165],q 4 [20488,62165],q 0 [16389,20490,78199],q 0 [20488,16399,4651],q 2 [16399,4651],q 1 [20488,4651],q 0 [16399,21034,22585],q 1 [21034,22585],q 0 [16390,20491,12965],q 1 [16389,20491],q 0 [16389,20491,12965],q 13 [12965],q 0 [16389,20491,78503],q 0 [16389,77839],q 2 [16389,77839],q 8 [],q 0 [12298,20499,284057],q 1 [20499,284057],q 3 [20499,284057],q 1 [16389,241673],q 1 [16389,241675],q 0 [16390,4623,12361],q 0 [20485,16392,505039],q 5 [20485,505039],q 1 [20485,16392,505039],q 0 [16390,4623,20488],q 0 [12294,17108,23321],q 1 [17108,23321],q 6 [12294,17108],q 0 [16390,4623,20493],q 0 [16390,12813],q 0 [16390,12813,20490],q 13 [16390,12813],q 0 [16390,21005,3149839],q 14 [3149839],q 4 [21005,3149839],q 5 [3149839],q 2 [16390,20490],q 0 [16388,12297,20770],q 1 [16388,20770],q 0 [16390,16391,12297],q 0 [8198,16399,1438249],q 0 [16390,16391,20488],q 0 [20486,12297,296123],q 1 [20486,296123],q 6 [12297,296123],q 4 [12297,296123],q 0 [16390,16391,20491],q 0 [20493,241671,17843],q 1 [241671,17843],q 6 [241671,17843],q 0 [8198,20496,152957],q 4 [20496,152957],q 1 [8198,20496,152957],q 0 [16391,12297,20770],q 1 [16391,20770],q 0 [16390,16391,20495],q 0 [16390,12298,20757],q 1 [16390,20757],q 0 [16390,20488,61965],q 4 [20488,61965],q 0 [20486,13497,16395],q 3 [20486,13497],q 0 [16390,20488,12349],q 6 [16390,65552],q 0 [20493,20497,155663],q 0 [16394,21969,2506767],q 5 [2506767],q 0 [16390,20490,12661],q 0 [20485,16394,505299],q 1 [16390,241673],q 0 [20488,16447,14501],q 13 [14501],q 4 [12289,21005],q 1 [16390,21005],q 2 [16390,21005],q 0 [16391,12805,20489],q 1 [16391,20489],q 0 [12294,16392,21709],q 2 [12294],q 0 [16391,12805],q 0 [16391,12805,20490],q 6 [16391,12805],q 13 [16391,12805],q 0 [16391,12298,20489],q 0 [16391,20488,12349],q 1 [16391,20488],q 0 [12294,20496,20497],q 14 [20496,20497],q 0 [20486,16395,631993],q 6 [16395,631993],q 1 [20486,16395,631993],q 0 [16391,20489,65551],q 0 [16390,12813,23298],q 5 [23298],q 0 [16391,20490,12661],q 0 [16391,20490,20491],q 0 [8196,20498,26081],q 4 [20498,26081],q 5 [8196,26081],q 1 [16391,241674],q 0 [20499,13721],q 0 [8199,20499,13721],q 3 [20499,13721],q 13 [20499,13721],q 1 [8199,20499],q 0 [16391,20495,528789],q 0 [20484,12777,16392],q 1 [20484,16392],q 13 [20484,12777],q 0 [20484,12777,16397],q 4 [12777,16397],q 5 [20484,12777],q 0 [8197,20499,13721],q 1 [8197,20499],q 0 [8196,12313,16397],q 0 [20484,16875,14721],q 14 [14721],q 4 [16875,14721],q 6 [14721],q 1 [20499],q 0 [20498,9699],q 2 [20498],q 0 [20496,151558],q 0 [20495,4503],q 1 [4503],q 1 [241681],q 1 [241680],q 0 [20493,20498],q 1 [241675],q 6 [241672],q 0 [20493,241671],q 1 [241671],q 1 [241670],q 1 [241669],q 0 [16399,20498],q 0 [16399,21035],q 1 [21035],q 1 [21033],q 0 [16399,8747],q 1 [8747],q 0 [16399,4649],q 1 [4649],q 0 [16397,20798],q 1 [20798],q 1 [323588],q 0 [20491],q 0 [20491,16399],q 0 [20491,16397],q 0 [20491,4775],q 0 [20490,20498],q 1 [4651],q 0 [20490,20493],q 0 [20490,16397],q 0 [20489,20497],q 2 [20497],q 0 [20489,16397],q 0 [20488,16397],q 0 [20488,16447],q 0 [16395,20495],q 0 [16388,20489],q 0 [20493,241682],q 1 [241682],q 0 [8199,20495],q 1 [8199],q 0 [12297],q 0 [16388,12297],q 2 [12297],q 0 [20489,16399],q 0 [20484,16392],q 0 [16388,12298],q 0 [12294,20496],q 0 [16399,21034],q 1 [21034],q 0 [12294,20488],q 0 [12294,16392],q 0 [8198],q 0 [8198,16399],q 1 [21205],q 0 [16391,20495],q 0 [20493,20497],q 0 [16392,1257478],q 1 [17111],q 2 [8198],q 0 [12294,8917],q 1 [8917],q 1 [20487],q 0 [20486,16397],q 1 [20486],q 0 [16388,8267],q 0 [12294,16393],q 0 [12293,20499],q 0 [16393,20495],q 0 [12293,20497],q 1 [21218],q 0 [20487,12298],q 0 [12293,20491],q 0 [12294,21207],q 1 [21207],q 0 [8199,20499],q 0 [12297,20770],q 1 [20770],q 0 [12293,16393],q 0 [8199,16397],q 0 [8199,13789],q 0 [8198,20498],q 0 [12294,17108],q 1 [17108],q 2 [20499],q 0 [16389,20558],q 0 [20493,241683],q 1 [241683],q 0 [8196,20497],q 2 [8196],q 0 [16399,8745],q 1 [8745],q 0 [16390,21005],q 4 [21005],q 0 [16395,20493],q 0 [16390,20488],q 0 [20485,12298],q 0 [12293,20498],q 0 [12294,20489],q 0 [8197,20498],q 0 [12293,16395],q 0 [16389,20490],q 0 [8196,16411],q 3 [16411],q 0 [8199,20496],q 0 [8196,20493],q 1 [8196],q 0 [12294,16395],q 0 [8198,20497],q 0 [8199,20493],q 0 [20488,16399],q 13 [17791],q 0 [12298,20489],q 0 [20487],q 0 [20487,16394],q 1 [16394],q 0 [8198,16397],q 0 [12293,20489],q 0 [8198,20499],q 0 [8197,16399],q 0 [8199],q 0 [8199,16399],q 2 [8199],q 0 [12293,20488],q 0 [8196,16397],q 0 [12293,16394],q 0 [16391,20488],q 0 [20486,16399],q 5 [20553],q 0 [20487,16397],q 0 [16388,20491],q 2 [20491],q 1 [16388,20491],q 0 [12297,20490],q 0 [8196,20496],q 0 [8196,20495],q 0 [12294,20486],q 0 [12294,20497],q 6 [13497],q 0 [8197,20495],q 0 [20496,16535],q 0 [12294,16394],q 0 [20488,61446],q 0 [12294,20499],q 0 [8197,20493],q 3 [12313],q 4 [12313],q 0 [20485,20493],q 0 [12293,20496],q 0 [16397,20498],q 0 [8196,20499],q 0 [12297,20499],q 0 [8197,20496],q 0 [8197,20497],q 0 [12294,20498],q 0 [12293,16392],q 0 [8197,20499],q 0 [8199,20497],q 0 [20486,9403],q 0 [8196,20498],q 0 [20484],q 0 [20484,16395],q 0 [8197,20510],q 0 [20485,12297],q 0 [8198,20493],q 2 [16394],q 0 [16392,20493],q 0 [8198,20495],q 0 [20489,20498],q 15 [20489],q 0 [12294,21206],q 1 [21206],q 0 [20485,16394],q 0 [20485,16399],q 15 [20485],q 0 [16388,20495],q 0 [16390,12297],q 0 [20495,16791],q 1 [16791],q 0 [20485,16395],q 0 [16389,12297],q 0 [16389,12298],q 0 [16389,20488],q 0 [16389,20489],q 0 [16389,20491],q 0 [16393,1265679],q 0 [16390,12298],q 0 [20484,12297],q 0 [20485,20490],q 0 [20498],q 0 [20486,20498],q 0 [16390,20489],q 0 [16390,20490],q 0 [16392,20495],q 0 [20484,12298],q 0 [16391,20997],q 5 [20997],q 0 [16391,12297],q 0 [16391,12298],q 0 [16391,20489],q 0 [20498,9697],q 0 [16391,20490],q 0 [16391,20491],q 0 [20485,16397],q 0 [8199,20498],q 0 [20484,16393],q 0 [20485,20497],q 0 [16390,20495],q 0 [20484,16394],q 0 [20484,16397],q 0 [20484,16875],q 4 [16875],q 0 [20484,16399],q 1 [294916],q 0 [20485,16392],q 0 [8197,16397],q 0 [20490,20497],q 0 [20485,20489],q 6 [1209],q 0 [20487,16392],q 0 [12298,20497],q 1 [20486,17593],q 6 [155663],q 0 [12293,20490],q 0 [20486,12297],q 0 [20486,12298],q 0 [12294,8919],q 1 [8919],q 0 [20486,16392],q 0 [20486,16393],q 0 [8198,20496],q 1 [8198,20496],q 0 [20486,16394],q 0 [20486,16395],q 0 [20486,20489],q 1 [16663],q 0 [20486,20493],q 0 [16389,20495],q 0 [20486,20497],q 0 [16390,20491],q 0 [8196,16399],q 0 [8197,12318],q 0 [20487,12297],q 0 [20498,5601],q 1 [20757],q 0 [20487,16395],q 0 [20487,16393],q 0 [20487,16399],q 1 [16672],q 0 [12294,17109],q 1 [17109],q 0 [12297,20496],q 0 [12297,20497],q 0 [12297,20498],q 0 [20485,20498],q 0 [12298,20496],q 0 [12298,20498],q 0 [12298,20499],q 0 [16392,13517],q 5 [13517],q 0 [20486,20490],q 0 [16393,20493],q 0 [16388,20490],q 0 [16393,21718],q 0 [16394,13777],q 0 [16394,20493],q 0 [16394,20495],q 0 [20499]]
def B_23_1 : BT (List (List Nat)) := BT.empty
lemma B_23_1_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 1 xs.toFinset) B_23_1 := .empty
def U_23_2 : List Nat := []
def P_23_2 : BT (Option BoundPool) := buildPoolsSubBT 12 W_23 r_23 S_23 ps_23 U_23_2
def N_23_2 : List NodeSpec := [([14,0,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_2 : checkNodesBT W_23 g_23 F_23 P_23_2 A_23 B_23_1 2 N_23_2 = true := by decide +kernel
def B_23_2 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_2
set_option maxRecDepth 500000 in
lemma B_23_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 2 xs.toFinset) B_23_2 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound S_23_ok) A_23_ok B_23_1_ok C_23_2
def U_23_3 : List Nat := []
def P_23_3 : BT (Option BoundPool) := buildPoolsSubBT 12 W_23 r_23 S_23 ps_23 U_23_3
def N_23_3 : List NodeSpec := [([21,22,0,3],[],[0]),([23,24,0,3],[],[0]),([0,28,29,3],[],[]),([0,12,3,13],[],[0]),([0,11,31,4],[],[]),([0,35,36,3],[],[0]),([40,41,0,3],[],[0]),([42,30,0,3],[],[0]),([39,8,0,44],[],[]),([0,34,2,46],[],[]),([0,50,2,5],[],[]),([51,45,0,3],[],[0]),([0,27,54,3],[],[]),([55,43,0,3],[],[0]),([0,56,53,3],[],[]),([17,20,0,57],[],[]),([0,34,2,58],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_3 : checkNodesBT W_23 g_23 F_23 P_23_3 A_23 B_23_2 3 N_23_3 = true := by decide +kernel
def B_23_3 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_3
set_option maxRecDepth 500000 in
lemma B_23_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 3 xs.toFinset) B_23_3 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound S_23_ok) A_23_ok B_23_2_ok C_23_3
def U_23_4 : List Nat := (r 0 19)
def P_23_4 : BT (Option BoundPool) := buildPoolsSubBT 12 W_23 r_23 S_23 ps_23 U_23_4
def N_23_4 : List NodeSpec := [([0,61,3,63,5],[0],[]),([64,20,0,3,5],[1],[]),([65,17,20,0,3],[2,3,4],[]),([17,22,20,0,3],[2,3,4],[0]),([20,0,2,68,70],[],[]),([0,34,29,2,3],[5,6],[]),([17,20,0,3,71],[2,3,4],[]),([26,0,34,2,3],[5,6,7],[0]),([25,0,28,2,3],[8],[0]),([26,0,27,29,3],[],[0]),([0,34,2,53,3],[],[]),([52,0,34,2,3],[],[]),([25,0,56,2,3],[9],[0]),([32,0,2,3,74],[],[]),([45,0,34,2,3],[10,11,12],[0]),([51,0,34,2,3],[10,11],[0]),([39,43,8,0,3],[13,14,15],[0]),([40,39,8,0,3],[],[0]),([30,0,11,3,4],[16,17,18],[0]),([55,39,8,0,3],[13,14],[0]),([76,0,77,19,70],[],[]),([17,78,0,3,19],[],[]),([17,20,24,0,3],[2,3],[0]),([42,0,11,3,4],[16,17],[0]),([80,0,83,4,5],[],[]),([84,0,86,4,5],[],[]),([0,12,11,3,4],[],[0]),([87,0,2,3,89],[],[]),([91,0,92,4,5],[],[]),([52,0,27,53,3],[],[0]),([20,2,95,96,5],[],[]),([98,0,2,49,5],[],[]),([100,20,0,2,5],[],[]),([101,20,0,2,103],[],[]),([76,20,0,2,70],[],[]),([87,0,2,104,5],[],[]),([105,47,20,0,2],[],[]),([108,101,20,0,2],[],[]),([39,8,41,0,3],[],[0]),([109,20,0,3,16],[],[]),([25,0,27,2,58],[],[0]),([17,20,0,3,49],[2,3,4],[]),([21,17,20,0,3],[2,3],[0]),([48,0,2,49,5],[],[0]),([87,0,2,68,5],[],[]),([66,17,20,0,3],[2,3,4],[]),([0,11,3,4,13],[],[0]),([73,0,2,110,5],[],[]),([0,35,34,2,3],[],[0]),([23,17,20,0,3],[2,3],[0]),([20,0,54,3,5],[],[0]),([0,34,2,36,3],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_4 : checkNodesBT W_23 g_23 F_23 P_23_4 A_23 B_23_3 4 N_23_4 = true := by decide +kernel
def B_23_4 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_4
set_option maxRecDepth 500000 in
lemma B_23_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 4 xs.toFinset) B_23_4 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound S_23_ok) A_23_ok B_23_3_ok C_23_4
def U_23_5 : List Nat := ([2,4,6,7,11,14,15,17]++r 19 83)
def P_23_5 : BT (Option BoundPool) := buildPoolsSubBT 12 W_23 r_23 S_23 ps_23 U_23_5
def N_23_5_0 : List NodeSpec := [([113,0,1,3,111,5],[],[]),([17,0,1,115,3,4],[19,20],[]),([116,117,0,1,3,4],[21,22,23],[]),([39,119,0,1,2,3],[],[]),([39,0,121,1,2,3],[],[]),([124,0,2,126,3,4],[],[]),([124,0,2,128,3,4],[],[]),([17,0,130,1,3,4],[],[]),([131,64,129,0,3,5],[24],[0]),([132,0,1,3,111,5],[],[]),([17,0,1,3,133,4],[19,20],[]),([0,137,1,3,4,5],[],[]),([17,78,0,1,3,4],[19,20],[0]),([64,0,18,3,19,5],[25],[0]),([139,17,0,1,3,4],[19,20],[]),([142,0,18,2,3,140],[],[]),([143,0,2,3,140,5],[26],[]),([65,17,0,18,3,19],[27,28,29],[0]),([145,0,144,3,19,16],[30,31,32],[]),([17,0,18,3,71,19],[27,28,29,33],[0]),([0,144,3,147,19,16],[30,31,32],[]),([148,20,0,2,3,5],[34,35],[]),([20,149,0,2,3,5],[34,35],[]),([151,20,0,2,3,5],[],[]),([152,0,2,3,5,59],[36],[]),([155,124,0,2,3,4],[],[]),([20,0,2,156,5,59],[37,38],[]),([157,20,0,2,3,5],[],[]),([48,20,0,2,3,5],[34,35,39],[0]),([17,20,0,3],[2,4,40],[0]),([20,0,2,3,159,5],[34,35],[]),([69,160,20,0,3,5],[],[]),([20,0,2,3,5,162],[],[]),([161,20,0,3,5,16],[41],[]),([25,20,0,2,3,70],[37,42],[0]),([163,20,0,2,3,5],[38],[]),([25,0,34,2,3],[6,7,42],[0]),([20,0,2,3,95,5],[],[0]),([25,87,0,2,3,5],[41,43],[0]),([20,0,2,68,5,59],[38],[0]),([25,0,27,29,2,3],[44,45],[0]),([26,25,0,27,2,3],[44,45,46],[0]),([26,20,0,29,3,5],[],[0]),([25,160,0,2,3,5],[39,41,47],[]),([52,25,0,27,2,3],[],[0]),([165,20,0,2,3,5],[],[]),([52,20,0,53,3,5],[],[0]),([25,94,0,2,3,5],[37,41,48],[]),([17,0,1,166,3,4],[],[]),([94,0,2,3,5,33],[41],[]),([167,168,17,1,3,4],[],[]),([32,20,0,2,3,70],[],[]),([73,32,0,2,3,5],[49],[0]),([0,34,2,3],[11,42],[0]),([170,20,0,2,3,5],[],[]),([93,66,169,20,0,3],[50,51,52],[0]),([66,20,0,2,156,5],[37,42],[]),([66,158,0,2,3,5],[53],[]),([171,20,0,2,3,5],[],[]),([172,20,0,2,3,5],[34,35],[]),([173,20,0,2,3,5],[34,35],[]),([67,20,0,2,68,5],[35,42],[0]),([105,169,20,0,2,3],[],[]),([20,0,2,3,174,5],[],[]),([20,0,2,3,176,5],[],[]),([20,0,77,3,156,5],[],[]),([102,101,0,2,19,75],[54],[]),([25,20,0,2,3,89],[37,41],[]),([20,177,2,3,5,89],[34,55],[]),([178,8,0,3,4,5],[],[]),([177,2,3,19,70,75],[56],[]),([179,20,0,2,3,5],[],[]),([39,182,0,1,2,3],[],[]),([20,0,2,3,183,5],[38],[]),([47,88,20,0,3,5],[],[]),([0,77,3,19,70,75],[57],[0]),([185,186,0,1,3,4],[22,58,59],[]),([131,65,17,129,0,3],[60,61,62],[0]),([69,20,0,3,5,187],[],[]),([188,17,0,1,3,4],[],[]),([190,20,0,2,3,5],[],[]),([0,2,191,3,19,75],[54],[]),([0,2,191,146,19,5],[63],[]),([20,192,0,2,3,70],[],[]),([0,77,156,146,19,5],[57],[]),([66,20,0,15,3,16],[64,65,66],[0]),([196,0,1,2,3,4],[],[]),([8,0,86,4,5,59],[67],[0]),([81,8,0,83,4,5],[67,68,69],[]),([20,0,197,2,3,5],[],[]),([17,0,1,3,199,4],[19,20],[]),([20,0,77,3,5,70],[],[]),([200,20,0,2,3,5],[34,35],[]),([8,0,92,4,90,5],[67],[0]),([204,0,2,3,4,5],[70],[]),([39,0,1,2,206,3],[71,72],[]),([207,0,3,92,4,5],[69],[]),([211,0,1,2,3,5],[],[]),([20,0,2,3,213,5],[],[]),([214,17,0,1,3,4],[],[]),([0,61,3,19,5,62],[73],[0]),([20,0,60,3,5,62],[74],[0]),([81,8,0,86,4,5],[68,69,75],[]),([93,73,20,0,3,5],[],[]),([215,8,0,3,4,5],[],[]),([216,20,0,2,3,5],[],[]),([76,177,2,19,75,59],[],[]),([218,20,0,2,3,5],[],[]),([8,0,3,219,4,5],[],[]),([91,8,0,3,4,5],[67,68,76],[0]),([131,17,1,3,220,4],[40],[]),([131,17,129,0,3,71],[60,61,62],[0]),([221,0,1,3,4,5],[77],[]),([39,0,1,223,2,3],[],[]),([145,20,0,2,3,5],[34,35],[]),([94,20,177,2,3,5],[],[]),([20,0,2,3,70,75],[37],[0]),([0,18,60,3,63,5],[78],[0]),([80,0,224,3,4,5],[],[]),([0,18,3,225,140,5],[79],[]),([0,11,3,4],[17,80],[0]),([20,2,3,96,5,89],[34,81],[]),([101,20,0,2,3,89],[],[]),([39,0,1,2,227,3],[],[]),([228,124,2,3,96,4],[82,83],[]),([20,0,2,3,70,59],[37,38],[]),([168,17,1,3,96,4],[],[]),([124,230,0,2,3,4],[],[]),([231,232,20,0,3,5],[84],[0]),([20,233,0,2,3,5],[34,35],[]),([88,87,0,2,3,5],[40],[0]),([20,177,2,3,156,5],[],[]),([47,20,0,2,5,59],[38,39],[]),([20,234,2,3,5,70],[35],[]),([80,9,0,3,4,5],[80,85],[0]),([106,20,0,3,156,5],[],[]),([20,0,2,3,235,5],[34,35,86],[]),([101,8,0,237,4,5],[75,80],[]),([93,102,20,0,3,5],[],[]),([39,8,0,3],[14,15,80],[0]),([20,0,2,3,89,75],[37],[]),([20,0,238,2,3,5],[],[]),([20,0,2,3,239,5],[34,35],[]),([207,81,0,3,4,5],[87],[]),([98,20,0,2,3,5],[34,35,41],[0]),([8,0,3,4,240,5],[68,76],[]),([8,0,242,3,4,5],[],[]),([241,84,0,3,4,5],[80,88],[0]),([8,243,0,3,4,5],[],[]),([17,244,0,1,3,4],[19,20],[]),([20,0,2,146,97,5],[41],[]),([94,20,0,3,72,5],[38],[]),([105,20,0,2,3,16],[37],[0]),([20,0,3,72,5,89],[38],[]),([8,0,245,3,4,5],[],[]),([246,8,0,3,4,5],[],[]),([20,0,2,110,72,5],[37],[0]),([153,154,124,2,96,4],[89],[]),([20,0,2,3,5,103],[34,35,39],[0]),([247,20,0,2,3,5],[34,35],[]),([248,20,0,2,3,5],[],[]),([67,87,0,2,3,5],[42,90],[0]),([171,177,2,3,19,5],[],[]),([20,0,2,3,249,5],[],[]),([102,101,20,0,2,5],[39],[0]),([17,0,1,3,250,4],[],[]),([66,175,0,2,3,5],[91],[]),([20,0,2,191,3,5],[34,35,39],[]),([20,0,2,3,5,74],[34,35,92],[0]),([69,20,0,2,68,5],[39],[0]),([20,0,2,251,3,5],[],[]),([101,0,18,2,19,103],[],[0]),([102,0,252,2,19,5],[],[]),([25,0,27,2,53,3],[],[0]),([25,66,0,2,68,5],[38],[]),([20,0,2,3,147,5],[34,35],[]),([20,0,2,3,5,99],[34,35,38,93],[0]),([212,69,20,0,3,5],[],[]),([76,20,0,2,5,253],[35,42],[]),([76,134,0,2,19,5],[],[]),([20,0,254,2,3,5],[37],[]),([20,0,2,3,5,255],[34,35,39],[]),([131,256,17,1,3,4],[40],[]),([69,76,20,0,2,5],[39],[0]),([124,0,258,2,3,4],[82,94],[]),([76,0,1,77,4,70],[],[0]),([76,20,0,2,75,59],[38],[]),([260,20,0,2,3,5],[],[]),([20,0,2,3,5,261],[35,40],[]),([262,20,0,2,3,5],[34,35,39],[]),([175,0,2,3,49,5],[],[]),([84,0,236,3,4,5],[],[]),([93,20,0,3,107,5],[40],[]),([263,20,0,2,3,5],[],[]),([20,0,2,156,146,5],[37],[]),([32,20,0,2,3,89],[95],[]),([76,20,0,2,5,59],[38],[]),([228,124,264,2,3,4],[94],[]),([76,0,217,2,19,5],[],[]),([76,0,18,2,19,70],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_5_0 : checkNodesBT W_23 g_23 F_23 P_23_5 A_23 B_23_4 5 N_23_5_0 = true := by decide +kernel
def N_23_5_1 : List NodeSpec := [([265,0,1,3,71,4],[96],[]),([164,88,20,0,3,5],[],[]),([20,177,2,3,5,70],[34,56],[]),([20,266,0,2,3,5],[34,35],[]),([20,192,0,2,3,89],[],[]),([160,0,2,3,5,33],[41],[]),([69,76,0,77,19,5],[],[0]),([20,267,0,2,3,5],[34,35],[]),([268,20,2,3,5,89],[34,55],[]),([268,20,2,3,5,70],[34,97],[]),([268,94,20,2,3,5],[],[]),([124,0,270,2,3,4],[],[]),([268,20,2,3,156,5],[],[]),([20,271,2,3,5,89],[35],[]),([20,0,3,104,5,16],[41],[]),([20,0,2,3,89,59],[38],[0]),([272,20,0,2,3,5],[34,35,98],[]),([20,0,2,49,97,5],[41],[0]),([20,0,2,104,5,59],[41],[0]),([65,265,0,1,3,4],[99],[]),([17,0,1,273,3,4],[],[]),([93,274,20,2,3,5],[40],[]),([101,20,0,2,107,5],[39],[0]),([275,20,0,2,3,5],[],[]),([20,0,2,3,5,276],[],[]),([129,0,60,3,277,5],[],[]),([32,0,18,2,3,89],[],[]),([108,20,0,2,3,5],[34,35,39],[0]),([8,0,83,4,79,5],[75],[0]),([32,20,0,2,3,187],[100],[]),([94,20,2,3,96,5],[38],[0]),([25,20,0,2,3,187],[39,41],[]),([281,0,1,3,4,5],[101],[]),([20,0,2,3,282,5],[34,35,38],[]),([283,20,0,2,3,5],[],[]),([93,169,20,0,3,49],[50,51,52],[0]),([106,20,0,3,5,70],[],[]),([164,20,0,2,3,59],[38,39],[]),([20,0,2,284,3,5],[34,35,39],[]),([25,20,0,2,58,5],[],[0]),([25,0,2,3,285,5],[42],[]),([158,0,2,3,49,5],[38],[]),([109,20,0,2,3,5],[34,35],[0]),([20,0,15,3,49,16],[41,64,65,66],[0]),([93,20,2,3,286,5],[40],[]),([47,20,0,2,49,5],[39],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_5_1 : checkNodesBT W_23 g_23 F_23 P_23_5 A_23 B_23_4 5 N_23_5_1 = true := by decide +kernel
def N_23_5 := N_23_5_0 ++ N_23_5_1
def B_23_5 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_5
set_option maxRecDepth 500000 in
lemma B_23_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 5 xs.toFinset) B_23_5 := by
  have hP := buildPoolsSubBT_sound (pdepth := 12) (W := W_23) (raw := r_23) (pspecs := ps_23) (used := U_23_5) S_23_ok
  have hm0 := checkNodesBT_mem (by decide) gp_23 W_23_ok hP A_23_ok B_23_4_ok C_23_5_0
  have hm1 := checkNodesBT_mem (by decide) gp_23 W_23_ok hP A_23_ok B_23_4_ok C_23_5_1
  exact buildBucketsBT_of_mem (forall_append (hm0) hm1)
def U_23_6 : List Nat := ([19,20,22,23,27,29]++r 31 5++r 37 6++[45,46,50,52,54,56,57,59,60,62,63,64]++r 66 4++[72,75]++r 79 4++[86,88,93,94,96,97]++r 102 373)
def P_23_6 : BT (Option BoundPool) := buildPoolsSubBT 12 W_23 r_23 S_23 ps_23 U_23_6
def N_23_6_0 : List NodeSpec := [([205,118,39,0,1,2,3],[22,42,102,103,104],[]),([118,0,287,2,3],[42,104,105],[0]),([180,288,39,0,1,2,3],[103,104,106,107,108],[]),([288,289,39,0,1,2,3],[103,104,106,107,108],[]),([292,0,1,2,3,293,5],[109],[]),([205,180,39,0,1,2,3],[22,80,106,107,110],[]),([294,0,1,60,3,111,5],[111],[]),([297,0,298,2,3,4,5],[22,42],[]),([299,297,0,2,3,4,5],[42],[]),([0,202,2,3,4,203,5],[112],[0]),([117,17,0,1,3,4],[20,23,33,59,80,96,113,114],[0]),([186,0,1,3,300],([40,59,80]++r 115 4),[]),([138,114,17,0,1,3,4],[23,80,116,119],[0]),([198,114,17,0,1,3,4],[23,40,59,80,119],[]),([114,186,17,0,1,3,4],[23,33,59,80,116,119],[]),([198,116,17,0,1,3,4],[23,33,40,59,80],[]),([116,0,301,3,4],[23,80,119,120],[0]),([167,116,17,1,3,4],([19,40,80]++r 121 4),[]),([39,69,0,1,120,2,3],[42,104,106,107],[0]),([229,124,303,2,3,4],([42]++r 125 6),[]),([306,0,122,2,3,4,305],[80],[]),([0,308,3,309,123],[80,131,132],[]),([310,124,0,2,3,4],([94]++r 133 6),[]),([180,118,39,0,1,2,3],[42,104,106,107,108],[]),([124,0,307,3,309],[80,135,136,139,140,141],[]),([311,124,0,2,3,4],[80,94,133,135,136,137,142,143],[]),([312,124,0,2,3,4],[94,133,135,137,143,144,145],[]),([69,124,0,269,2,3,4],[22,42,135,143],[0]),([124,0,269,2,3,72,4],[42,80,136,143],[]),([313,0,269,2,3],[42,130,133,146,147],[0]),([69,229,124,0,2,3,4],[42,135,136,143],[0]),([229,124,0,2,3,72,4],[22,42,80,135,136,137,143],[]),([153,229,124,0,2,3,4],[22,42,130,133,143,148],[]),([138,125,124,0,2,3,4],[42,80,136,143],[]),([313,125,124,0,2,3,4],[130,133,135,136,149,150,151],[]),([153,125,124,0,2,3,4],[22,80,130,135,136,152],[]),([138,124,0,2,127,3,4],[42,80,136,143],[]),([124,0,2,127,3,4,79],[22,80,133,136,151],[0]),([314,229,124,0,2,3,4],[130,133,135,136,143,153,154],[]),([129,0,315,2,3,4,5],[155,156],[]),([17,129,0,1,3,71,4],[23,59,80,116,157,158,159],[0]),([313,314,124,0,2,3,4],([130,133,135,136,151]++r 160 4),[]),([316,232,0,1,3,4,5],[],[]),([317,124,0,2,3,4],[42,94,136,137,164],[]),([131,0,1,60,3,111,5],[],[]),([131,64,0,1,3,4,5],[165],[0]),([0,1,60,3,4,277,5],[166],[0]),([131,65,17,0,1,3,4],[22,59,80,167,168,169],[0]),([131,17,0,1,3,71,4],[23,33,59,80,167,168,169],[0]),([131,167,17,1,3,4],[19,22,40,80,124,167,168],[0]),([318,17,0,1,3,4],[20,22,23,33,40,59,96,116,170],[]),([164,131,129,0,2,3,59],[171,172],[0]),([129,0,2,3,277,5,59],[42,172,173],[0]),([180,0,1,319,3],[80,106,107,117,174],[]),([131,47,129,0,2,5,59],[171,172],[0]),([131,17,129,0,3],[23,40,59,60,62],[0]),([0,1,279,3,4,280,5],[80,175],[0]),([232,0,1,3,4,320,5],[80,176],[]),([0,1,2,3,111,278,5],[177,178,179],[]),([0,1,60,3,4,63,5],[166,180],[0]),([164,0,1,2,3,4,278],[178,181],[]),([64,0,1,3,4,19,5],[80,182,183,184],[0]),([132,0,1,3,4,5,62],[185],[0]),([321,0,1,2,3,278,5],[186],[]),e6 [322] [93,178,187,188],([0,1,2,325,4],[80,189,190],[]),([0,1,2,156,4,278,5],[181,191],[]),([142,0,1,2,3,4,140],[],[0]),([47,0,1,2,4,278,5],[178,181],[]),([326,17,0,1,3,4],[19,20,22,23,59,96,130,192,193],[]),([17,0,1,3,71,4,19],([23,40,59,80,119]++r 194 5),[0]),([69,327,1,3,4,140,5],[40],[]),([134,0,1,2,3,4,70],[191],[]),([134,0,1,2,329,4,5],[191],[]),e6 [331] [178],([65,17,0,18,1,3,4],([22,33,80]++r 199 4),[0]),([265,17,0,1,3,4],[19,20,22,23,33,40,96,203],[0]),([333,1,2,3,97,4,5],[204],[]),([0,1,144,3,147,4,16],[205,206,207],[0]),([64,129,0,1,3,4,5],[208],[0]),([335,1,2,144,3,4,5],[22,40,130,209,210],[]),([231,232,0,18,3,19,5],[211],[0]),([0,18,2,3,19,70,59],[57,212],[0]),([0,18,2,3,63,5,59],[213,214],[0]),([336,0,2,3,19,5,59],[215],[0]),([0,18,60,3,19,5,62],[216],[0]),([171,0,18,2,3,19,5],[],[0]),([0,18,2,3,140,5,59],[213,217,218],[]),([145,0,18,2,3,19,5],[219,220,221],[0]),([131,129,234,2,3,5,70],[222],[0]),([145,0,2,144,3,19,5],[221,223,224],[0]),([148,0,18,2,3,19,5],[219,220],[0]),([69,0,18,3,140,5],[40,79,225,226],[0]),([149,0,18,2,3,19,5],[219,220],[0]),([234,18,2,3,19,5,70],[220],[0]),([218,0,18,2,3,19,5],[],[0]),([20,0,259,2,3,5],[37,38,40,227],[0]),([337,0,18,2,3,140,5],[213,217,218,228,229,230],[]),([94,20,0,18,2,3,5],[37,231],[0]),([20,0,18,2,3,97,5],[130,232,233,234],[0]),([158,20,0,18,2,3,5],[34,35,41,130,235],[]),([114,0,338,3,4],[23,80,236],[0]),([20,0,217,2,3,5],[37,40,41,42,237,238],[0]),([20,0,2,3,339,5],[37,39,42,239],[]),([88,32,0,18,2,3,5],[40,240],[0]),([168,17,0,1,3,4],[20,22,23,33,59,96,241],[0]),([20,0,18,2,3,5,89],[40,242],[0]),([260,0,18,2,3,19,5],[],[0]),([20,0,2,150,3,5],[37,39,41,42,243],[0]),([340,20,0,2,3,5],[35,37,38,39,41,42,244,245],[]),([0,2,144,3,147,19,5],[221,223,224],[0]),([231,20,0,2,3,5,59],[37,39,246],[0]),([288,0,120,2,3],[42,104,247],[0]),([118,39,0,1,2,3,72],[42,80,104,106],[]),([20,0,60,2,3,5,59],[37,39,248,249,250],[0]),([67,20,0,2,3,5,59],[42],[0]),([87,20,0,2,3,5,59],[42],[0]),([341,342,0,1,3,4,5],[251],[0]),([20,0,2,3,189,5],[40,41,42,252],[0]),([175,20,0,2,3,5],([35]++r 38 4++[253]),[0]),([93,20,0,2,3,5,59],[37,38,39,41,254],[0]),([93,169,20,0,3],[37,39,40,50,52],[0]),([94,20,0,2,3,5],[35,37,38,39,41,231],[0]),([198,0,1,343,3],[59,80,117,255],[]),([154,124,0,2,3,257,4],[22,136,256,257],[0]),([160,20,0,2,3,5],([34,35]++r 37 5++[86,258]),[0]),([344,17,0,1,3,4],[20,23,33,59,80,96,116,259,260],[]),([20,0,2,3,97,5],[37,42,130,232,233],[0]),([0,1,60,3,111,19,5],[177,261,262],[0]),([64,0,18,1,3,4,5],[22,80,182,183,263,264],[0]),([69,20,0,3,5,16],[37,39,40,41,265,266],[0]),([20,0,2,3,5,70],[34,37,42,267,268],[0]),([161,20,0,2,3,5],[35,37,38,41,42,269,270],[0]),([0,122,2,3,4,305,345],[22,80],[]),([47,0,18,2,19,5,59],[212,213],[0]),([93,20,0,3,72,5],(r 37 5++[271]),[0]),([73,20,0,2,3,5],[35,38,39,41,42,272,273],[0]),([231,131,232,129,0,3,5],[274],[0]),([20,0,346,3,5],[39,42,275],[]),([25,20,0,2,3,5,59],[38,42],[0]),([25,93,20,0,2,3,5],[37,39,41,42],[0]),([25,20,0,2,3,5,16],[37,39,41,42,276,277],[0]),([25,69,20,0,2,3,5],[37,38,39,41,42],[0]),([25,20,0,2,3,72,5],[37,39,42],[0]),([25,20,0,2,3,68,5],[41,42,278],[0]),([101,0,2,77,3,19,75],[54,279],[0]),([131,129,0,60,3,5,62],[280],[0]),([134,0,2,3,19,5,75],[279],[0]),([93,0,77,3,19,5,75],[54,57,279],[]),([0,1,2,191,146,4,5],[281],[0]),([0,2,77,146,19,5,59],[63],[0]),([81,8,0,3,347,4,5],[67,80],[]),([198,167,17,1,3,4],[19,80,119,123,124,282,283],[]),([0,18,2,3,140,141,5],[218,228,229,284,285],[0]),([177,348,2,3,19,5,75],[40,234,286,287],[]),([171,1,177,2,3,4,5],[],[0]),([18,177,2,3,19,5,70],[56,219],[0]),([17,0,18,1,3,71,4],([22,33,80]++r 197 5),[0]),([25,20,177,2,3,5],([34,35,42]++r 288 4),[]),([138,116,17,0,1,3,4],[23,33,59,80,116],[0]),([1,177,2,3,183,4,5],[292],[]),([20,0,2,3,5,253],[37,39,42,293],[0]),([0,1,61,3,4,5,62],[111,294],[0]),([1,177,2,3,4,5,255],[188,295,296],[]),([93,20,0,77,3,5],([37]++r 39 4++[297]),[0]),([1,177,2,3,4,70,75],[22,56],[0]),([0,1,60,3,111,112,5],[111,177,261,262],[0]),([76,177,2,3,19,5,75],[234,298],[0]),([125,229,124,0,2,3,4],[130,133,135,136,143],[]),([177,2,3,19,5,75,253],[42,298],[]),([349,177,2,3,19,5,75],[40],[]),([69,0,77,3,19,5,75],[57],[0]),([0,144,3,19,16],[31,32,40,299],[0]),([1,177,2,191,3,4,5],[188,296,300],[]),([39,0,1,2,222,3,184],[22,42,80,104],[]),([17,0,18,3,19],[23,27,29,40],[0]),([180,39,181,0,1,2,3],[80,103,106],[0]),([93,0,77,3,146,19,5],[57],[0]),([0,18,2,156,19,5,59],[57,212],[0]),([198,181,17,0,1,3,4],[33,40,59,80],[0]),([314,0,127,3,4],[80,135,136,301],[0]),([180,39,0,1,2,3,184],[42,80,104,106],[]),([350,32,20,0,2,3,5],[37,39,41,42],[]),([186,17,0,1,3,184,4],[22,23,80,96,116,119],[0]),([158,20,0,2,3,5],[34,35,37,38,41,130,235],[0]),([8,0,3,83,4,5],[67,68,75,80,88,302,303],[0]),([101,241,8,0,3,4,5],[42,67,80],[]),([20,0,2,3,5,75,59],[41,234,304],[0]),([352,39,0,1,2,3],[42,72,104,106,107,305,306],[]),([153,154,124,0,2,3,4],[22,135,136,137,256,307],[0]),([69,177,2,3,19,5,75],[40,298,308],[0]),([0,2,61,3,19,5,59],[57,309],[0]),([25,66,0,2,3,5],[41,42,278],[0]),([353,20,2,3,5],[35,42,56,310],[]),([87,20,0,2,3,5],[35,37,39,42,311],[0]),([205,39,0,1,2,7,3],[22,80,106,312],[0]),([354,39,0,1,2,3],[22,40,72,104,106,306,313],[]),([355,0,224,3,4],[67,80,314],[0]),([1,177,2,251,3,4,5],[],[]),([356,357,0,1,2,3,4],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_6_0 : checkNodesBT W_23 g_23 F_23 P_23_6 A_23 B_23_5 6 N_23_6_0 = true := by decide +kernel
def N_23_6_1 : List NodeSpec := [([102,0,2,3,19,5,75],[54,279],[0]),([131,129,0,2,156,5,59],[171,315],[0]),([93,20,0,2,3,146,5],[37,38,40,42,316,317],[0]),([0,2,77,3,19,75,59],[54],[0]),([0,1,2,194,3,4,195],[],[0]),([88,20,192,0,2,3,5],([37]++r 39 4),[0]),([359,8,0,3,4,5],[42,67,68,69,88,318],[]),([88,20,0,2,3,5,75],[37,40,41,42],[0]),([8,0,3,86,4,5],[67,68,75,80,88,319,320],[0]),([0,259,2,3,146,19,5],[40,212],[]),([85,81,8,0,3,4,5],[42,75,88],[0]),([101,0,18,1,2,4,103],[22,321],[0]),([360,17,0,1,3,4],[20,23,33,59,80,96,116,322],[]),([274,20,2,3,5],[34,40,42,81,130],[0]),([362,0,7,3,4,361,5],[80,323],[]),([363,0,1,2,193,4,5],[],[]),([364,134,177,2,3,4,5],[],[]),([81,241,8,0,3,4,5],[42,75,88,319],[0]),([20,0,252,2,3,5],[37,39,41,42,324],[]),([20,0,2,77,3,5,59],[37,39,325],[0]),([116,186,17,0,1,3,4],[23,33,59,80,116],[]),([365,0,236,3,5],[40,42,88,117,326,327],[]),([20,134,0,2,3,5,59],[38,41,234,328],[]),([102,101,0,1,2,4,75],[329],[0]),([18,177,2,3,156,19,5],[234],[0]),([80,8,0,3,4,5],[67,68,69,80,88,330,331],[0]),([1,2,308,96,366,4,5],[42,80],[]),([25,20,0,29,2,3,5],[37,39,276,277],[0]),([93,268,20,2,3,5],[34,40,42,316,317,332,333],[0]),([241,8,0,3,4,5,59],[42,67,69,75,80,119],[0]),([135,0,1,136,3,4,5],[],[0]),([181,186,17,0,1,3,4],[23,33,59,80,116],[0]),([0,1,2,209,3,210,5],[],[0]),([241,0,3,367,5],[40,42,117,334,335],[]),([1,2,3,368,4,140,5],[40,336],[]),([20,0,18,2,3,156,5],[37,234,254,337],[0]),([124,2,3,369,4],[80,130],[]),([93,20,0,2,3,5,33],[37,39,41,42,316,317],[0]),([355,365,8,0,3,4,5],[40,67,75,80,88,119],[]),([229,124,2,3,96,4],[130,137,148,153,338,339,340],[]),([0,1,307,3,370,371,5],[42],[]),([76,0,18,2,19,5,253],[42,220],[0]),([373,124,0,2,3,4],[80,94,133,135,137,341],[]),e6 [374] [178,342],([20,0,2,144,3,5],[38,40,41,343],[0]),([353,2,3,19,5,75],[56,286,298,344,345],[]),([76,0,18,2,19,5,59],[212],[0]),([364,177,2,3,4,75,59],[234,346],[]),([39,351,375,0,3],[80,104,106,347,348],[0]),([0,7,3,361,38],[80,349,350],[]),([376,358,8,0,3],[80,88,351],[0]),([228,124,0,2,3,4],[22,82,94,133,135,136,137,143,352],[0]),([377,20,2,3,5],[34,40,42,81],[]),([378,1,2,144,3,4,5],[40,130,188],[]),([268,20,2,3,5,75],[40,42,353,354],[]),([0,7,3,4,361,379,5],[80,323],[]),([0,2,146,19,75,59],[42,279,355],[]),([65,17,129,0,1,3,4],[22,23,80,157,158,159],[0]),([20,0,2,3,110,5],[37,39,41,42,130,356],[0]),([125,0,380,3,4],[80,135,136,357],[0]),([212,0,2,3,146,19,5],[63,212],[]),([1,177,77,3,156,4,5],[],[]),([88,20,2,3,96,5],([34,40,42]++r 358 5),[0]),([76,20,0,2,3,5,75],[234,304],[0]),([212,69,1,177,3,4,5],[],[]),([1,2,3,381,4,140,5],[22,40,363,364],[]),([67,25,20,0,2,3,5],[38,42],[0]),([0,18,2,3,147,19,5],[219,220],[0]),([382,292,0,1,2,3,5],[42],[]),([20,192,0,2,3,59],[41,42,365,366],[]),([20,0,2,3,5,33,16],([37,39,41,42]++r 367 4),[0]),([292,0,1,383,2,3,5],[42],[]),([384,1,2,96,4,90,5],[],[]),([76,1,177,2,4,75,59],[292],[0]),([125,124,0,2,3,4,79],[80,133,136],[0]),([8,0,224,3,4,79,5],[40,80,88,119],[0]),([25,20,2,3,96,5],[38,42,277,278,358,359,362],[]),([81,8,0,3,385,4,5],[42,75,88],[]),([386,39,0,1,2,3],[72,80,103,104,106,107,306,371],[]),([387,0,2,208,3,4,5],[],[]),([67,20,0,2,3,5],[35,37,39,42,372],[0]),([1,177,77,3,4,5,70],[56],[]),([131,17,1,3,96,4],[40,80,169,373],[0]),([65,17,0,1,3,4,19],[22,23,80,194,195,196,202],[0]),([8,0,3,37,38],[67,80,374,375],[0]),([9,8,0,3,4,79,5],[40,67,69,80,88,119],[0]),([0,217,2,3,19,5,75],[40,279],[0]),([93,20,2,3,96,5],[34,40,42,254,316,358,359],[0]),([0,1,388,3,290,293,5],[376],[]),([125,124,2,3,96,4],[80,82,130,149,151,152,338,339,340],[]),([0,1,3,225,4,140,5],[377],[0]),([9,0,3,4,10],[67,80,378,379],[0]),([389,39,0,1,2,3],[72,103,104,107,306,380,381],[]),([116,17,1,3,96,4],[40,80,122,373,382],[]),([25,20,0,2,77,3,5],[37,39,42],[]),([39,0,1,2,7,3,226],[42,80,104,106,108,312],[0]),([8,0,3,237,4,5],[40,67,80,119,383],[0]),([84,8,0,3,4,5],[68,75,80,88,384],[0]),([390,0,328,1,3,4,5],[],[0]),([25,0,27,2,3],[41,42,45,46],[0]),([20,2,3,96,5,75],[40,42],[]),([101,350,20,0,2,3,5],[37,40,41,385],[]),([20,0,2,3,156,5],[37,39,42,254,337],[0]),([177,2,3,19,75,59],([234,298,308]++r 386 4),[0]),([153,124,2,96,4],[22,42,80,130,137],[0]),([376,391,39,0,1,2,3],[390,391],[]),([241,9,8,0,3,4,5],[67,75,80,88,119],[]),([20,0,2,3,5,59,253],[42,392],[0]),([198,17,1,3,96,4],[19,80,119,283,373,382],[]),([69,20,177,2,3,5],[34,40,42,288,289,393],[0]),([20,2,3,286,5],[40,42,97,130],[0]),([355,241,8,0,3,4,5],[67,75,80,88,119],[]),([241,8,0,3,79,5],[40,69,80,88,119,394],[]),([0,18,315,2,3,4,5],[22,80,395,396],[]),([88,20,177,2,3,5],[34,35,40,42,288,289,290,361,397],[0]),([365,9,8,0,3,4,5],[40,67,80,88,119],[]),([364,336,0,2,3,4,5],[398],[]),([164,20,0,2,3,5],[35,39,40,42,399,400],[0]),([8,0,3,92,37,4,5],[67,80,119,401],[0]),([76,20,0,2,3,5],[35,37,39,41,42,402],[0]),([69,20,0,77,3,5],[37,39,42],[0]),([8,0,236,3,4,5,59],[42,80,119],[0]),([392,0,1,307,3,370,5],[42],[]),([39,0,6,7,3],[80,106,107,403,404],[0]),([148,1,177,2,3,4,5],[188,405],[]),([20,0,348,2,3,5,75],[37,40,234,353,354,406],[]),([0,18,2,251,3,19,5],[],[0]),([20,0,2,146,5,59],[41,42,407,408],[]),([20,0,15,3,16],[40,41,64,66],[0]),([101,20,0,2,3,75],[41,42,406],[]),([69,76,0,1,77,4,5],[],[0]),([393,394,0,1,2,3,5],[],[0]),([39,0,1,120,2,3,72],[22,42,80,106,107],[]),([0,1,77,156,146,4,5],[409],[0]),([138,9,8,0,3,4,5],[42,67,75,80],[]),([20,177,2,3,5,59],[42,248,249,288,289,290],[]),([81,8,0,3,37,4,5],[67,80,119,401],[0]),([47,0,1,395,2,4,5],[],[]),([20,0,2,3,107,5],[40,41,42,410],[0]),([47,0,1,2,4,396,5],[],[]),([397,39,0,1,2,3],[72,80,104,107,306,411],[]),([101,106,20,0,2,3,5],[37,38,39,41,42],[0]),([93,20,177,2,3,5],[34,40,42,56,289,290,316,317],[0]),([20,0,2,3,49,5,16],[37,39,41,42,266,367,368,412,413],[0]),([0,259,2,3,19,5,75],[57,279],[]),([138,8,0,224,3,4,5],[42,67,75,80],[]),([154,124,2,3,96,4],[130,256,339,340,414,415],[0]),([8,0,3,4,90,5],[40,67,119,401],[0]),([76,0,2,77,3,19,5],[57],[0]),([17,1,3,220,4],[22,40,80,130],[0]),([268,20,2,3,5,59],[34,42,248,249,332,333,416,417],[]),([0,1,77,3,4,70,75],[409],[0]),([116,17,0,1,3,4,79],[22,33,40,59,80,96],[0]),([398,20,0,3,5],[37,42,418],[]),([268,88,20,2,3,5],[34,40,42,332,333,361,397,417],[0]),([399,400,0,2,3,4,5],[419],[0]),([69,268,20,2,3,5],[34,40,42,332,393,417],[0]),([0,1,2,191,3,4,75],[329],[0]),([32,20,0,2,77,3,5],[37,39,42],[]),([81,9,8,0,3,4,5],[67,80,302],[0]),([102,20,0,2,3,5],[35,37,39,41,42,420],[0]),([212,20,0,2,3,5],[35,37,39,40,42,421],[0]),([0,1,2,3,4,278,70],[181,191],[]),([134,0,2,3,19,5,253],[42,422],[0]),([0,18,77,3,19,5,70],[234],[0]),([118,289,39,0,1,2,3],[42,104,106,107,108],[]),([0,18,77,3,156,19,5],[234],[0]),([93,102,0,18,3,19,5],[],[0]),([134,0,1,2,156,4,5],[191],[]),([0,18,2,3,19,5,255],[213,219,220],[0]),([0,18,2,3,19,5,103],[213,219,220],[0]),([248,0,18,2,3,19,5],[],[0]),([256,17,1,3,4],[19,40,80,130,423],[0]),([102,101,0,18,2,19,5],[213],[0]),([20,0,2,3,5,75,253],[42,304],[0]),([134,0,1,2,3,4,401],[191],[]),([0,2,144,3,146,19,5],[40,212,223,224],[]),([0,18,2,3,213,19,5],[],[0]),([20,0,18,2,3,5,70],[34,37,234,267],[0]),([0,18,2,191,3,19,5],[213,219,220,424],[0]),([207,8,0,3,4,5],[40,67,68,69,75,88,425],[0]),([20,0,2,3,75,59],[41,42,406,426],[0]),([391,39,0,1,2,3],[72,103,104,106,107,306,427,428],[]),([102,0,1,252,2,4,5],[],[0]),([20,0,15,2,3,49,5],[41,42,233,412,413,429,430],[0]),([69,76,0,18,2,19,5],[213],[0]),([25,350,20,0,2,3,5],[37,39,42],[]),([350,20,0,2,3,5,59],[37,40,385],[]),([26,25,20,0,2,3,5],[37,39,276,277,278],[0]),([350,134,0,2,3,19,5],[40],[]),([0,2,146,19,5,75,59],[212,279],[]),([20,134,0,2,3,5],[35,37,39,42,431,432],[]),([8,0,3,402,4,5],[67,75,88,119,433],[]),([76,0,2,146,19,5,75],[212,234],[]),([20,0,2,3,5,187],[37,38,40,41,434],[0]),([364,0,2,146,4,75,59],[234,435,436],[]),([131,129,0,2,3,70,59],[171,315],[0]),([0,18,2,146,97,19,5],[234],[0]),([0,18,2,3,183,19,5],[212],[0]),([0,18,2,156,146,19,5],[234],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_6_1 : checkNodesBT W_23 g_23 F_23 P_23_6 A_23 B_23_5 6 N_23_6_1 = true := by decide +kernel
def N_23_6_2 : List NodeSpec := [([47,20,0,2,3,5],[34,35,37,40,42,266,437],[0]),([20,0,15,2,3,146,5],[38,40,41,42,429,430,438,439],[0]),([0,18,2,3,249,19,5],[],[0]),([134,0,2,146,19,5,59],[212,234],[]),([0,2,77,3,19,5,253],[57],[]),([76,134,0,1,2,4,5],[],[0]),([76,0,18,2,19,75,59],[212,279],[0]),([66,20,0,15,2,3,5],[41,42,233,429,430,440,441],[0]),([69,20,0,2,3,5,75],[37,40,41,304],[0]),([82,81,8,0,3,4,5],[67,80],[0]),([93,20,0,2,3,5,75],[37,39,41,406],[]),([93,66,20,0,2,3,5],[37,39,42,254,316,317],[0]),([349,20,0,2,3,5,75],[37,40],[]),([88,20,0,3,5,16],([37]++r 39 4++[442]),[0]),([0,18,2,3,19,70,75],[234],[0]),([403,8,0,3,4,5],[68,69,80,88,443],[]),([134,0,2,3,19,75,59],[234,279],[]),([76,0,1,217,2,4,5],[],[0]),([76,0,18,1,2,4,70],[22,444,445],[0]),([20,0,2,3,404,5],[37,39,41,42,446],[]),([69,20,192,0,2,3,5],[37,39,40,41,447],[0]),([25,20,0,2,3,5],[35,37,38,39,42,448,449],[]),([114,17,0,1,3,4,79],[23,59,80],[0]),([101,20,0,2,77,3,5],[37,38,39,41,325],[0]),([267,0,18,2,3,19,5],[219,220],[0]),([192,0,18,2,3,19,70],[],[0]),([118,39,69,0,1,2,3],[42,104,107],[0]),([185,17,0,1,3,4],[20,23,59,80,96,116,450,451],[0]),([218,192,0,1,2,3,4],[],[]),([229,0,2,3,405],[42,133,143,151,452],[0]),([20,0,2,3,5,59,62],[37,39,42,248,249,453],[0]),([0,348,77,3,19,5,75],[54],[]),([0,252,2,77,3,19,5],[57],[0]),([88,0,406,3,5],[37,39,42,117,454],[]),([164,0,18,2,3,19,59],[212,213],[0]),([407,8,0,3,4,5],[68,69,75,80,88,455],[]),([20,0,2,3,104,5],[37,41,42,456],[0]),([0,295,2,61,3,4,5],[457,458],[]),([20,0,2,3,5,16,59],[37,38,39,41,248,249],[0]),([198,17,0,1,3,184,4],[23,59,80],[0]),([20,0,2,3,5,89],[34,37,38,39,41,242],[0]),([52,25,20,0,2,3,5],[37,39],[0]),([88,32,20,0,2,3,5],[37,39,41,42],[0]),([25,88,20,0,2,3,5],[37,39,41,42],[0]),([212,69,0,18,3,19,5],[],[0]),([88,20,0,3,72,5],[37,38,39,42,459],[0]),([289,0,1,222,3],[80,106,107,117,460],[]),([39,181,0,1,2,222,3],[80,103,104,106],[0]),([169,20,0,2,3,49,5],[39,41,42,461,462,463],[0]),([218,1,177,2,3,4,5],[464],[]),([88,20,0,2,3,5,59],[37,38,39,41,42],[0]),([69,32,20,0,2,3,5],[37,39,41,42],[0]),([101,88,20,0,2,3,5],[37,39,41,42],[0]),([408,20,0,2,3,5],[35,37,38,39,41,42,465],[]),([106,0,409,3,5],[37,39,42,117,466],[]),([106,32,20,0,2,3,5],[37,39,41,42],[0]),([232,20,0,2,3,5,59],[37,39,467],[0]),([101,8,0,236,3,4,5],[42,67,80],[0]),([69,106,20,0,3,5],[37,39,42],[0]),([134,0,2,3,4,410,5],[],[]),([93,106,20,0,3,5],([37]++r 39 4++[468]),[0]),([66,20,0,2,3,5,16],[37,39,42,266,367,368,440,441],[0]),([106,20,0,2,3,5,59],[37,39,42],[0]),([20,0,2,3,5,411],[37,42,469],[]),([145,0,1,144,3,4,16],[205,206,207],[0]),([25,106,20,0,2,3,5],[37,39,41,42],[0]),([25,0,2,3,49,5],[38,41,42],[0]),([25,268,20,2,3,5],[34,42,276,277,332,333,416,417],[]),([93,20,0,2,3,49,5],[37,39,42,254,316,317],[0]),([105,20,0,2,3,5],[35,37,39,41,42,470,471],[0]),([66,169,20,0,2,3,5],[39,42,461,462,463],[0]),([32,0,2,3,33],[41,42,472],[0]),([32,20,0,2,3,72,5],[37,38,39,41,42],[0]),([25,20,0,2,53,3,5],[37,39],[0]),([412,124,2,3,4],[42,80,300,473],[]),([20,0,2,3,68,5],[37,39,42,474],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_6_2 : checkNodesBT W_23 g_23 F_23 P_23_6 A_23 B_23_5 6 N_23_6_2 = true := by decide +kernel
def N_23_6 := N_23_6_0 ++ N_23_6_1 ++ N_23_6_2
def B_23_6 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_6
set_option maxRecDepth 500000 in
lemma B_23_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 6 xs.toFinset) B_23_6 := by
  have hP := buildPoolsSubBT_sound (pdepth := 12) (W := W_23) (raw := r_23) (pspecs := ps_23) (used := U_23_6) S_23_ok
  have hm0 := checkNodesBT_mem (by decide) gp_23 W_23_ok hP A_23_ok B_23_5_ok C_23_6_0
  have hm1 := checkNodesBT_mem (by decide) gp_23 W_23_ok hP A_23_ok B_23_5_ok C_23_6_1
  have hm2 := checkNodesBT_mem (by decide) gp_23 W_23_ok hP A_23_ok B_23_5_ok C_23_6_2
  exact buildBucketsBT_of_mem (forall_append (forall_append (hm0) hm1) hm2)
def U_23_7 : List Nat := ([19,20,22,23,33,34,35]++r 37 6++[54,56,57,59,63,67,68,69,71,72,75,76,79,80,82,88,93,94,96,103,104,106,107,108,110,111,116,117,119,121,130,132,133,135,136,137,141,143,148,150,151,152,154,156,157,158,161,163,166,167,169,171,172,177,178,181,182,187,188,191,194,195,197,199,201,202,206,207,210,212,213]++r 217 6++[224,226,228,230,233,234,249,254,256,261,263,266,276,278,279,281,282,285,286,292,295,296,298,299,300,306,308,312,315,317,319,323,329,342,345,346,350,353,364,367,369,376,377,383,385,386,388,391,396,397,398,401,405,409,412,424,429,431,435,436,439,441,445,461,462,464]++r 475 957)
def P_23_7 : BT (Option BoundPool) := buildPoolsSubBT 12 W_23 r_23 S_23 ps_23 U_23_7
def N_23_7_0 : List NodeSpec := [([376,205,39,0,1,2,3],([42,108]++r 475 6),[]),([376,288,39,0,1,2,3],([42,108,475]++r 478 6),[]),([39,0,1,2,413,3],[80,108,484],[]),([205,39,0,1,2,3],[22,42,72,80,104,106,107,108,306,485],[0]),([39,0,1,319,2,3],[42,71,80,104,106,108,486],[0]),([180,39,0,1,2,3],[22,40,42,104,106,107,108,110,487],[0]),([39,0,1,120,2,3],[22,104,106,107,108,130,306,488,489],[0]),([288,39,0,1,2,3],[42,72,104,106,107,108,490],[0]),e6 [414,415] [42,80,93,178],e6 [416,417] ([22,191,234]++r 491 6),([292,0,1,2,3,290,5],([42,80]++r 497 5),[0]),([292,0,1,2,3,5],[42,80,498,500],[0]),([0,1,2,3,290,293,5,291],[501,502],[0]),e6 [290,418] [80,503],([294,0,1,2,3,111,5,59],[80,151,501,504,505,506],[0]),([419,420,0,2,3,4,5],([80,93]++r 507 8),[]),([0,1,60,3,290,4,421,5],[191,497,515,516],[]),([39,0,1,422,2,3],[22,80,108,130,475,479,480,517,518],[]),e6 [370] ([93,187,234,497,515]++r 519 4),([0,1,60,3,111,4,5],[80,111,177,261,523,524],[0]),([364,0,423,2,3,4,5],[80,156,398,507,525,526,527],[]),([424,364,0,1,3,4,5],([80,156,178]++r 528 7),[]),([364,0,425,2,3,4,5],([156,525,527,533]++r 535 6),[]),([387,364,0,2,3,4,5,59],[93,234,541,542],[]),([419,0,426,1,2,3,5,59],[80,108,516,543],[]),([327,1,2,3,4,140,5],([22,40,187,364]++r 544 5),[0]),([106,20,0,2,3,5],(r 37 6++[549]),[0]),([20,0,2,406,3,5],[34,39,41,42,550],[0]),([69,0,18,77,3,19,5],[57,213,234,551,552,553],[0]),([0,18,2,3,404,19,5],([57,213,220,279]++r 554 4),[0]),([364,0,18,2,3,404,4,5],[22,234],[]),([138,17,0,1,3,4],[22,23,59,80,96,116,119,558],[0]),u6 [134,75] (r 559 4),([69,192,0,18,2,3,19,5],[40,57,213,279,552,555],[0]),u6 [259,75] [329,409,561,563],([69,76,0,18,1,2,4,5],[22,445,564,565],[0]),([229,124,0,2,3,4],[22,94,130,133,135,136,137,143,148,151,154],[0]),([0,18,1,2,3,4,70,75],[234,566,567,568],[0]),([101,20,0,18,2,3,5],[37,39,41,42,130,569],[0]),u6 [192,217] [40,80,570,571,572],([76,0,18,2,3,19,5,75],[234,279,573,574],[0]),([76,0,18,2,3,19,5],([57,212,213,220,234,279]++r 573 4),[0]),([93,131,169,129,0,3],[40,172,315,577,578,579],[0]),([76,0,18,1,2,4,5,253],[22,42,580,581],[0]),([93,20,0,2,3,5],[37,39,41,42,254,317],[0]),u6 [102,75] [22,80,329,561,582],([349,0,18,2,3,19,5,75],[40,57],[0]),([1,177,2,3,4,5,75,253],[22,42,583,584,585],[0]),([20,0,2,3,5,75],[37,40,41,42,353,559],[0]),([364,0,18,2,3,4,5,253],[22,156,586],[]),u6 [320,59] [166,587,588,589],u6 [18,249] [22,80,590],([93,0,1,77,3,146,4,5],[22,42,409,591,592],[0]),([0,1,2,3,427,4,428],[80,516,593,594,595],[]),u6 [259,146] [22,40,596,597,598],([20,192,0,2,3,5],[37,40,41,42,130,599,600],[0]),u6 [18,183] [567,582,601],u6 [134,253] [42,602,603],([101,350,0,18,2,3,19,5],[40,57,279,604,605],[0]),([39,1,2,3,96],[40,42,71,80,130,306],[]),([350,20,0,2,3,5],[35,37,39,40,42,385,606,607],[0]),([0,6,7,3,37,38],([80]++r 608 4),[0]),u6 [231,278] [166,191,612],e6 [350,404] [22,40,191,606],([124,2,3,96,4],[42,80,82,130,137],[0]),u6 [267,18] [22,80,191,495,571,580,613,614],e6 [430] [80,93,178,187,234,615,616,617],u6 [18,251] [80,191,618,619],([69,1,177,2,3,4,5,75],[22,40,585,620,621],[0]),u6 [18,103] [22,564,613,622,623],([131,129,0,2,3,189,5],([172,222]++r 624 5),[0]),([93,102,0,18,1,3,4,5],[22,191,629,630],[0]),([419,0,1,2,431,3,5,59],[22,80,516,631],[]),([0,18,1,77,3,4,5,70],[191,234,495,632],[0]),([376,8,0,3,4,5],[67,75,80,88,119,633],[0]),([39,0,1,2,222,3],[22,40,42,104,106,108,634,635],[0]),([101,0,18,2,77,3,19,5],[57,212,213,234,279,553,604],[0]),([0,295,2,3,290,4,293,5],[234,516,541,636],[]),([212,0,18,2,3,19,5],[40,57,212,213,220,279,637,638,639],[0]),u6 [76,77] [22,178,409,560,640],([18,1,177,2,3,4,5,70],[22,56,234,613,621,641],[0]),([101,0,1,2,77,3,4,75],[80,329,561],[0]),e6 [432] [80,178,187,191,507,642,643],([192,0,18,2,3,19,59],[42,212,279,525,644],[0]),([231,0,18,2,3,19,5,59],[57,213,645],[0]),([69,0,1,77,3,4,5,75],[80,409,582],[0]),u6 [77,253] [178,409,646],u6 [93,278] [181,191,495,647,648],([8,0,3,4,5,38],[76,80,88,119,649,650],[0]),([0,1,2,77,146,4,5,59],[22,234,281,619],[0]),([376,39,1,2,3,96],[42,80,130,651,652,653],[]),([364,0,433,2,3,4,5,59],[80,234,654],[]),u6 [212,146] [22,42,80,281,598,655,656],u6 [18,213] [22,80,234,657],u6 [144,146] ([22,40,598]++r 658 4),([93,0,18,2,3,146,19,5],[40,42,57,212,234,662,663,664],[0]),([93,0,18,77,3,19,5],[40,57,213,234,279,665,666,667],[0]),([0,18,1,2,146,97,4,5],[22,234,668,669],[0]),([0,122,307,3,309,123],[80,670,671,672],[0]),([1,252,177,2,3,4,5],[130,292,296,464,621,673,674,675],[]),([39,0,287,1,2,3],[42,71,104,106,107,108,676],[0]),([0,18,1,2,156,146,4,5],[22,234,677,678,679],[0]),e6 [434,435] [22,80,680],([18,1,177,2,3,156,4,5],[22,234,621,681,682],[0]),([18,177,2,3,19,5,59],([130,525]++r 683 5),[0]),([129,0,1,2,3,4,70,59],[688,689],[0]),([93,18,177,2,3,19,5],[56,130,219,464,662,666,685,686,687,690],[0]),([69,18,177,2,3,19,5],[40,219,308,464,552,685,686,691,692],[0]),e6 [278] ([93,178,187,191,541]++r 693 4),([1,177,2,3,4,5,75,59],[22,130,234,292],[]),([1,177,348,2,3,4,5,75],[40,234,621,697,698],[0]),e6 [134,60] [42,166,178,191,699,700],([302,229,124,0,2,3,4],([42,130]++r 701 7),[0]),([154,122,2,3,96,4,123],(r 708 9),[0]),([0,18,2,3,19,5,253],[42,57,213,602,603,717,718],[0]),([20,0,2,3,5,59],[37,38,39,41,42,249],[0]),([364,192,0,18,2,3,4,59],[22,80,234,719],[]),([131,69,129,0,3,5,16],[172,226,315,628,720,721,722],[0]),([1,177,2,77,3,4,5,59],[22,234,296,621,723,724],[0]),u6 [252,77] [178,409,725],([353,1,2,3,4,5,75],[56,345,585,697,726],[0]),u6 [390,134] [178,191],([93,1,177,77,3,4,5],[22,56,234,296,516,591,621,727],[0]),([69,1,177,77,3,4,5],[234,296,516,621,724,728,729],[0]),([302,154,304,2,3,96,4],[80,715,730,731,732],[0]),([177,2,3,19,5,75],[40,130,286,298,308,584,733],[0]),u6 [356,193] [80,570],u6 [361,379] [22,80,734],e6 [134,59] [342,570,735,736],([376,39,181,0,1,2,3],[42,80,108,391,516,737,738],[0]),e6 [18,70] ([22,80,191,234,568,641]++r 739 5),e6 [231,387] [151,191,234],([93,131,129,2,3,96,5],([40,171,714]++r 744 7),[0]),e6 [437] ([80,93,178,187,191,234]++r 751 4),([138,8,0,3,4,5],[40,42,69,80],[0]),u6 [350,134] [40,191,606],([8,0,3,37,4,5],[40,67,75,88,119,401,755],[0]),([0,1,2,3,438,4,436],[80,234,754,756],[]),([154,1,2,96,439,4,5],([42,709]++r 757 5),[]),([0,18,252,2,3,19,5],[57,130,213,604,762,763],[0]),([1,417,2,96,4,90,5],([22,42,652]++r 764 6),[]),([20,0,2,3,72,5],[38,40,41,42,770],[0]),([1,2,3,96,4,440,5],([745,746,769]++r 771 4),[]),([39,0,441,1,2,3],[42,108,156,478,479,480,775,776],[]),u6 [357,193] [80,570],([125,124,0,2,3,4],[22,130,133,135,136,137,150,151,152],[0]),([304,442,2,3,96,4,5],([744,759,774]++r 777 5),[]),([1,217,177,2,3,4,5],([40,188,292,296,464,580,620,621,673]++r 782 4),[0]),([443,1,2,3,96,4,5],[342,714,744,769,774,777,781,786,787,788],[]),([154,124,0,2,3,4],[22,94,130,133,135,136,137,141,143,256,789],[0]),([353,1,2,146,4,5],[22,726,790,791],[]),([241,8,0,3,4,5],[40,67,68,69,80,88,119,319,792],[0]),([351,375,0,3,37,38],[80,610,793,794,795],[0]),([192,0,18,1,2,3,4,70],[22,80,234,495,571,796],[0]),([124,0,2,3,444,4],[42,80,130,702,706,797,798],[]),([18,2,3,96,19,5,75],[40,286,573,799,800],[0]),([76,0,18,1,2,4,75,59],[560,561,801,802],[0]),([39,0,1,445,2,3],[42,80,108,478,653,803],[]),([0,18,2,3,19,5,59,62],[57,213,525,683,804,805,806],[0]),([0,18,2,3,19,5,75,253],[42,573,807],[0]),([0,1,60,3,4,19,5,62],([166]++r 808 4),[0]),([1,2,446,3,96,4,5],([342,744,774]++r 812 4),[]),([20,0,2,3,146,5],[34,37,40,41,42,439],[0]),([20,0,2,77,3,5],[37,40,41,42,816],[0]),([447,1,2,3,96,4,5],[342,714,715,769,774,786,817,818,819],[]),([0,18,2,3,189,19,5],[40,279,625,820],[0]),e6 [60,396] [166,178,191,522,525,821,822,823],([448,154,1,2,96,4,5],([80,714,715]++r 824 4),[]),u6 [231,134] [40,166,191],([39,0,1,2,7,3],[22,40,104,106,108,312,828],[0]),u6 [201,203] ([22,80,93,234]++r 829 5),([101,1,177,2,3,4,75],[42,130,234,516,585,620,834,835],[]),([9,8,0,3,4,5],[40,67,80,88,119,130,836],[0]),u6 [60,278] ([42,166,178,191,806]++r 837 4),u6 [18,191] [234,424,495,613,841,842],([1,2,3,96,4,361,5],[40,80,342,734,843,844],[]),([134,0,18,2,3,19,5],[57,213,220,431,525,845,846],[0]),([101,0,18,2,3,19,75],[42,54,130,234,279,573,847],[0]),([17,1,3,96,4],[19,40,80,96,130],[0]),([8,0,224,3,4,5],[40,80,88,119,130,848],[0]),([1,2,3,96,4,449,5],([80,714,774]++r 849 5),[]),([0,1,2,77,3,4,75,59],[80,234,329,854],[0]),e6 [419,208] [156,501,510,516],([93,131,169,1,3,96,4],([40]++r 855 4),[0]),e6 [450] ([156,187,342,570]++r 859 4),([17,0,338,1,3,4],[19,23,40,59,80,119,863],[0]),e6 [321,295] [178,234,424,516,806,864],([451,1,2,3,96,4,5],[342,714,759,774,856,865,866],[]),e6 [452,59] [22,80,342,510,516,867],([0,1,144,3,4,16],[40,206,207,299,561,868,869],[0]),([181,17,0,1,3,4],[22,23,33,40,59,80,96,870],[0]),([88,20,0,18,2,3,5],([35,37]++r 39 4++[397,871]),[0]),e6 [453,90] [40],e6 [454] [40,187,188,496,570,872,873,874],e6 [455,449] [22,80,342],([131,129,0,2,3,5,16,59],[171,172,315,628,875,876],[0]),([1,2,434,3,96,4,5],[80,744,877,878],[]),([1,177,2,144,3,4,5],[22,56,130,187,292,464,661,673,879],[]),e6 [290,432] [80,880],([304,1,2,3,96,4,428],[80,593,652,819,881,882,883],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_7_0 : checkNodesBT W_23 g_23 F_23 P_23_7 A_23 B_23_6 7 N_23_7_0 = true := by decide +kernel
def N_23_7_1 : List NodeSpec := [([8,0,3,4,5,10],[40,76,80,88,119,884,885],[0]),([234,18,1,2,3,4,5,70],[22,300,580,739,886,887,888],[0]),e6 [457] [93,156,178,187,342,570,889,890,891],([0,18,1,77,3,156,4,5],[191,234,629,892],[0]),([0,1,2,156,4,19,5,59],([80,587,810]++r 893 4),[0]),([39,0,1,2,3,458],[42,80,108,475,897],[]),e6 [387,60] [151,156,234,898],([0,295,1,60,459,3,4,5],[191,234,899],[]),([0,18,2,3,19,5,75,59],[130,212,234,573],[0]),u6 [400,201] [93,234,900],e6 [460,90] [130],([1,461,2,3,96,4,5],([342,709,759,819]++r 901 5),[]),([376,358,351,375,0,3],[80,906,907],[0]),([93,0,18,2,3,19,5,75],[54,57,130,213,234],[0]),([8,0,3,4,79,5],[67,69,80,88,119,908],[0]),([1,2,308,3,96,4,5],([22,42,80]++r 909 4),[0]),([20,177,2,3,5],[34,35,40,42,130],[0]),([6,1,2,96,4,90,5],([22,40,652,764,765]++r 913 5),[0]),e6 [462] [40,80,187,497,918,919,920],u6 [277,59] [166,191,504,921,922],([93,1,177,2,3,4,5,75],[130,296,621,835],[]),e6 [463,59] [234,424,528,923],([1,2,464,3,96,4,5],[342,714,759,774,819,850,924,925],[]),e6 [181,466] [80,234],([1,2,96,468,4,5],([42]++r 926 5),[]),u6 [134,136] [178,191,431,501,525,699,700,931],([377,192,1,2,3,4,5],([40,759]++r 932 9),[]),([167,17,1,3,4],[19,20,22,40,80,130],[0]),([303,2,3,469,4,5],[42,80,941,942],[]),([302,124,2,3,96,4],[42,80,130,759,943,944],[0]),([20,18,2,3,96,5],[34,35,40,42,130],[0]),([134,1,177,2,3,4,5,59],[234,292,525,620,684,945],[0]),u6 [18,147] [22,80,613,946],e6 [470,59] [80,108,234,342,528,947],([1,2,3,96,4,140,5],[40,819,933,948,949,950],[0]),u6 [279,278] [42,178,191,648,806,837,838,951],([304,1,307,3,96,309,5],([80,774,786]++r 952 7),[]),([1,2,471,3,96,4,5],([342,759,819]++r 959 5),[]),([376,358,0,6,7,3],[80,907,964,965],[0]),([181,0,1,2,3,472,4,428],[22,80,234],[]),([0,2,77,3,19,5,75],[40,57,279,966,967],[0]),([88,20,0,2,3,5],[35,37,38,39,41,42,397],[0]),([212,69,0,18,1,3,4,5],[80,495,968,969],[0]),([350,0,1,2,146,4,5,59],[22,40,234,970],[]),([8,0,236,3,4,5],[40,67,80,88,119,383,971],[0]),([0,1,2,146,4,5,75,59],[234,561],[0]),([131,1,15,3,96,4,16],[40,959,972,973],[0]),([39,181,0,1,2,3],[42,80,106,108,306,974],[0]),([1,307,2,96,439,4,5],[22,42,758,759,760,813,910,975,976],[]),([102,101,0,18,1,2,4,5],[22,564,977,978],[0]),e6 [473,308] [22,42,80,342],([93,0,1,77,3,4,5,75],[329,409,561],[0]),([1,2,3,96,4,474,5],([342,759,774,819]++r 979 4),[]),([93,0,18,2,3,19,5,59],[57,212,213,279,664],[0]),([0,18,1,2,3,4,70,59],([22,80,409,598,810]++r 983 4),[0]),([18,1,177,2,3,97,4,5],[22,56,130,234,987,988],[0]),e6 [295,475] [234,424,516,806],([8,0,3,4,5,59],[40,42,67,69,80,119,989],[0]),u6 [394,208] [156,516],([81,8,0,3,4,5],[40,42,67,68,69,80,88,119,990],[0]),([358,8,0,3,4,5],[42,67,88,119,991],[0]),([0,18,2,77,3,19,5,59],[57,213,525,553],[0]),([20,2,3,96,5],[34,38,40,42,130],[0]),([101,8,0,3,4,5],[42,67,69,80,992],[0]),u6 [218,18] [80,234,570,993,994],([0,18,15,2,3,146,19,5],([40,42,234,279]++r 995 5),[0]),([0,18,2,3,97,19,5],[57,130,234,999,1000],[0]),([0,18,348,2,3,19,5,75],[40,54,57,279,286,733,1001],[0]),([118,39,0,1,2,3],[22,42,104,106,107,108,130,1002],[0]),([20,0,409,2,3,5],[34,37,39,41,42,1003],[0]),([131,0,1,2,3,476,5,59],[151,831,921,1004,1005],[]),([0,1,60,3,111,5],[80,111,177,261,523,524],[0]),e6 [478] [22,40,178,187,188,191,1006,1007,1008],u6 [18,255] [22,295,564,613],u6 [305,345] [22,80,178],([0,6,434,3,4,5],[80,680,964,1009,1010],[]),([20,0,2,3,49,5],[34,37,38,39,41,42,412],[0]),u6 [370,371] [42,93],([39,351,0,1,2,3],[42,103,104,106,108,1011,1012],[0]),u6 [132,59] [93,166,587,839,1013,1014,1015],e6 [384] [93,178,187,342,516,570,1016,1017,1018],u6 [208,210] [80,156,166,516,806,1019,1020],([1,2,96,4,479,5],[22,652,1021,1022],[]),([0,7,3,4,361,5],[40,323,611,1023],[0]),u6 [208,290] [156,166,499,515,516,806,1024,1025],([0,1,480,2,3,4,428],[80,516,595,1026,1027],[]),([297,0,295,2,3,4,5],[42,80,396,525,806,864,1028,1029],[]),([39,0,6,1,2,3],[71,80,103,104,106,107,108,1030,1031],[0]),([47,129,0,1,2,4,5,59],[80,119,689],[0]),([419,0,1,2,3,111,5],([119,177,501,504,510]++r 1032 5),[]),([124,0,2,3,4,79],[80,130,133,136,137,1037],[0]),([483,1,2,481,4,5],[42,80,1038,1039,1040],[]),([231,131,129,0,2,3,5,59],[172,315,1041],[0]),([355,8,0,3,4,5],[40,67,68,69,80,88,119,1042,1043],[0]),([0,1,2,146,4,75,59],[42,561,1044],[0]),([39,0,1,2,3,184],[42,80,104,306,1045],[0]),u6 [248,18] [22,80,234,424,1046,1047],([8,3,96,4,5],[40,42,69,76,80,130],[]),([101,0,1,2,4,485],([80]++r 1048 4),[]),e6 [450,59] [342,516,570,862],([0,1,2,431,3,486,5],([178]++r 1052 5),[]),([101,1,177,2,77,3,4,5],[22,292,296,620,621,724],[0]),u6 [193,195] ([80,570,832]++r 1057 4),([448,1,2,96,4,309,5],[80,777,824,1061,1062],[]),([487,47,1,2,3,4,19,5],([22,40,300]++r 1063 4),[]),([181,0,2,3,4,449,5],[42,80,1067,1068,1069],[]),([93,0,18,3,72,19,5],[40,57,212,279,1070,1071],[0]),([412,1,2,488,4,5],[42,80,1072,1073],[]),([138,0,1,2,434,3,5],[42,516,1074,1075],[]),u6 [209,208] [156,166,516,806,1019,1020,1024,1076,1077],([131,47,129,0,2,3,5],([40,156,171,222,315,722]++r 1078 4),[0]),u6 [393,208] [156,516],([387,0,2,7,3,4,5,59],[810,1082,1083],[0]),([1,177,2,3,4,75,59],[234,388,516,525,585,620,835,1084,1085],[0]),([154,489,0,1,3,4,5],[156,810,1086,1087],[]),e6 [208] [93,156,187,516,839,899,1088,1089,1090],e6 [181,491] [516,1091,1092],u6 [306,305] [80,178,191],e6 [454,90] [40,766,1093],([351,375,0,3,4,90,5],[40,496,795,1094,1095,1096],[0]),([419,0,426,1,2,3,5],[80,93,501,533,543,1097],[]),e6 [492,290] [80,156,499,515,516,525,1098],([231,232,129,0,1,3,4,5],[1099],[0]),([164,0,1,2,3,4,19,59],([80,166,896]++r 1100 4),[0]),e6 [134,77] [178,409],([0,2,77,3,146,19,5],[42,63,553],[0]),e6 [493,59] [156,515,1104],u6 [145,144] [22,342,660,661,1105,1106],([76,1,177,2,3,4,5,75],[22,234,585],[0]),([17,0,1,3,184,4],[22,23,40,59,80,96,1107],[0]),u6 [148,18] [22,405,580,613],e6 [495] ([80,93,187,516]++r 1108 5),([69,0,18,2,3,19,5,75],[40,57,234,279,552,573],[0]),([17,0,1,343,3,4],[19,23,40,59,80,116,119,1113],[0]),([350,192,0,1,2,3,4,59],[22,40,234,1114],[]),([124,0,2,127,3,4],[22,130,133,136,137,151,1115,1116],[0]),e6 [181,496] [22,80,191],([66,20,0,2,3,5],[34,35,37,38,39,41,42,441],[0]),u6 [140,59] [42,80,806,949,1013,1014,1103,1117,1118],([32,20,0,2,3,5],[37,38,39,41,42,130,1119],[0]),([20,0,2,3,5,33],[34,37,39,41,42,369],[0]),([134,0,1,2,146,4,5,59],[234,342,525,562,1120,1121],[0]),([25,20,0,2,3,5],[35,37,38,39,41,42,276,278],[0]),([20,0,27,2,3,5],[34,37,39,41,42,1122],[0]),([64,0,1,3,4,5],[80,182,263],[0]),([69,20,0,2,3,5],[37,38,41,42,1123],[0]),([364,134,0,18,2,3,4,5],[80,156],[0]),u6 [392,370] [42,93,234],([169,20,0,2,3,5],(r 39 4++[461,462]),[0]),([129,0,1,2,156,4,5,59],[688,689],[0]),([101,20,0,2,3,5],[37,38,39,41,42,130,569],[0]),([268,20,18,2,3,5],[34,35,40,42,130],[0]),([17,0,1,3,4,19],[19,22,59,80,130,194,195],[0]),([32,20,0,18,2,3,5],[37,39,41,42,130,1119],[0]),u6 [395,62] [42,501,806,1124,1125,1126],([124,0,307,2,3,4],[80,130,133,135,136,143,1127,1128],[0]),e6 [497,60] [93,111,117,166,191,516,695,1129,1130],([25,20,0,18,2,3,5],[35,37,38,39,41,42,108,276,1131],[0]),([39,0,1,2,3,72],[42,80,106,306,1132],[0]),([69,20,0,18,2,3,5],[37,40,41,42,1123],[0]),([20,0,18,15,2,3,5],[40,41,42,130,233,429],[0]),([289,39,0,1,2,3],[42,72,80,104,106,107,108,1133],[0]),([0,1,348,77,3,4,5,75],[80,329],[0]),([93,20,0,18,2,3,5],([37]++r 39 4++[254,317,666]),[0]),([20,0,18,2,3,5,59],[37,38,39,41,42,249],[0]),([131,1,2,3,97,332,4,5],[22,80,130,1134,1135,1136],[]),([124,0,2,3,4,309],[42,130,136,1137,1138],[0]),([164,0,18,2,3,19,5],[40,212,220,234,1139,1140,1141],[0]),([0,18,217,2,3,19,5],[40,57,220,279,552,1142,1143,1144],[0]),([131,0,1,2,3,111,5,59],[80,151,504,806,921,1145],[0]),([0,2,144,3,19,5],[57,130,221,224],[0]),([0,18,2,144,3,19,5],[40,57,130,221,224,1146],[0]),([69,498,0,1,3,4,5],[40,1147,1148,1149],[]),e6 [231,396] [119],([0,18,15,3,19,16],[40,279,1150,1151],[0]),e6 [134] [93,156,178,187,191,342,570,1152,1153],([131,0,1,60,3,4,5,62],[166,1154],[0]),([0,18,2,3,19,5,16,59],[57,212,213,279,683,804,806],[0]),([18,1,2,3,97,332,4,5],[22,80,130,1134,1155],[0]),([124,0,499,2,3,4],[80,93,130,151,702,705,706,1156,1157],[]),([350,0,18,2,3,19,5,59],[40,57,525,605],[0]),([47,0,18,2,3,19,5],[40,57,212,219,220,1079,1158,1159],[0]),([0,18,2,3,140,5],[40,79,217,218,228,1160],[0]),([131,0,1,2,156,4,5,59],[1161,1162],[0]),([364,18,177,2,3,4,5,59],[22,234,346,525],[0]),([0,18,259,2,3,19,5],[40,57,212,220,666,1163,1164],[0]),([0,18,2,3,156,19,5],[57,213,234,664,1165,1166],[0]),([0,18,2,146,19,5,59],[42,63,279,525],[0]),([377,18,2,3,19,5],[40,219,759,937,1167],[0]),([17,0,18,1,3,4],[19,22,23,33,40,59,80,199,201],[0]),u6 [396,16] [151,424,499,821,822,1168,1169,1170],([0,18,1,2,156,4,5,59],[22,80,409,598,810,893,894,895],[0]),([0,18,2,3,19,5,59,253],[42,525,1171],[0]),([39,375,0,1,2,3],[80,104,107,108,1172,1173],[0]),e6 [295,315] [80],([0,1,307,3,449,5],[80,1174,1175,1176],[]),([134,0,18,2,3,19,5,59],[212,234,279,525,846],[0]),([0,6,7,3,4,90,5],[40,611,1177,1178,1179],[0]),([0,18,60,2,3,19,5,59],[57,213,525,683,804,1180],[0]),([232,0,18,2,3,19,5,59],[57,213,1181],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_7_1 : checkNodesBT W_23 g_23 F_23 P_23_7 A_23 B_23_6 7 N_23_7_1 = true := by decide +kernel
def N_23_7_2 : List NodeSpec := [([17,0,1,3,4,300],[19,23,59,80,119,1182],[0]),u6 [149,18] [22,80,580,613,1183],([1,2,144,334,3,4,5],[22,40,130,187,210,661,1184,1185,1186],[0]),([268,20,2,3,5],[34,35,40,42,130],[0]),u6 [145,18] [22,570,580,613,1105,1106],([138,124,0,2,3,4],[22,42,80,137],[0]),e6 [498,59] [22,42,342,1013,1014,1148,1187,1188],u6 [134,16] [178,191,431,501,525,699,700,931,1121,1189],([47,0,18,1,2,4,5,59],[22,80,166,564,598,1190,1191],[0]),u6 [260,18] [22,93,191,234,1192,1193],([364,0,423,2,3,4,5,59],[22,80,234,398,526],[]),u6 [171,18] [22,1194],([114,17,0,1,3,4],[22,23,40,59,80,96,119,130,1195],[0]),e6 [232,278] [178,191,810,1196,1197],u6 [93,134] [191,342,495,1121,1198],([39,0,1,2,3,226],[42,80,104,106,108,306,1199],[0]),([231,0,18,295,2,3,4,5],[22,80,396,1200,1201],[0]),e6 [330,60] ([191,495]++r 1202 5),u6 [231,330] ([166,191]++r 1207 4),([17,0,1,3,71,4],[19,23,40,59,80,96,119,197],[0]),u6 [135,134] [178,191,699,700],u6 [134,328] [178,191,562,1121],u6 [134,62] [178,431,501,525,699,700,810,931,1211,1212],([93,169,0,18,3,19],[40,57,213,578,1213],[0]),e6 [232,134] [80,178,1214],([0,18,295,60,2,3,4,5],[22,80,234,522,1215,1216,1217],[0]),([69,0,1,3,4,140,5],[226,377,720,949,1103,1117,1218],[0]),([0,18,2,3,4,410,5,59],[525,806,1219],[0]),([0,1,2,3,111,112,5,59],[80,166,177,501,1032,1034,1220,1221,1222],[0]),([364,0,18,2,3,4,5,62],([22,80,525,527,533]++r 1223 4),[0]),([76,0,18,1,2,4,5,59],[22,560,570,801],[0]),([232,364,0,18,2,3,4,5],[22,80,1227],[]),u6 [61,59] [80,495,1013,1014,1126,1228],([164,131,129,0,2,3,5],[93,156,172,222,1141,1229,1230,1231],[0]),u6 [336,59] [22,42,80,119,166,342,1013,1014,1232],([164,0,18,1,2,3,4,59],[22,80,166,564,598,1100],[0]),([93,1,2,500,96,4,5],[22,42,652,746,1233,1234],[]),e6 [501,59] [22,42,80,234,342,1235],([234,1,2,3,4,19,5,70],[22,300,739,886,887,888,1063],[0]),([364,0,18,2,146,4,5,59],[22,234,436,525,1236],[0]),e6 [364,502] [93,166,234,525,528,1237],([259,1,2,3,96,4,5],[342,596,714,744,769,774,1192,1238],[]),([47,0,1,2,4,19,5,59],[80,166,896,1103,1190,1239,1240],[0]),([364,0,18,2,3,4,75,59],[234,435,525,1241],[0]),e6 [231,497] [42,191,516],u6 [278,16] [178,181,191,424,648,837,838,1242],([1,2,96,4,503,5],[42,80,652,1243,1244,1245],[]),([0,122,2,3,4,305],([80]++r 1246 4),[0]),([304,504,1,2,3,4,428],[80,882,883,1250,1251,1252],[]),e6 [505,59] [234,1253],([0,1,2,3,4,19,70,59],[80,587,810,896,983,984,985],[0]),u6 [337,140] [22,230,342,544,545,949,1103,1117,1254],e6 [138,507] [234,1255,1256],([8,0,3,4,367,5],[42,67,76,80,119,1257,1258],[0]),([101,0,1,2,4,324],[80,1259,1260,1261],[0]),([8,0,3,92,4,5],[40,42,67,69,80,88,119,1262],[0]),e6 [474,59] [42,80,921,981,1263],([321,0,1,2,3,19,5,59],[525,810,1264,1265],[0]),([0,1,2,3,111,19,5,59],[80,166,177,525,1032,1034,1103,1220,1266],[0]),([131,1,2,3,96,476,5],[80,652,714,774,979,1267,1268,1269],[]),([134,1,177,2,3,4,5],[188,292,296,464,580,620,621,673,945,1270],[0]),u6 [278,62] [42,178,424,806,810,837,838,1271],e6 [232,395] [178,191,810,1196],u6 [63,59] [166,191,806,1013,1014,1103,1272,1273],([231,232,0,1,3,4,19,5],[80,166,810,1274,1275,1276],[0]),([259,1,177,2,3,4,5],[22,56,188,292,296,464,580,596,597,620,621,673,1277],[]),u6 [278,280] [42,178,191,806,837,838,1278],u6 [341,278] [178,191,1279],([349,1,177,2,3,4,5,75],[40,621],[0]),u6 [342,278] [178,191,1280],([302,304,2,3,369,4],[80,731,759,1281,1282,1283],[0]),e6 [144] [22,40,187,188,342,1284,1285,1286],([231,131,232,0,1,3,4,5],[810,1287],[0]),u6 [384,90] [191,570,768],e6 [18,97] [22,80,234,669,740,741,987,1288,1289],e6 [93,396] [342,495,1168,1290],e6 [508,59] [156,178,515,1291],([124,0,2,3,4,405],[42,130,133,135,136,1292,1293],[0]),([0,1,2,3,361,38],[80,350,756,1294,1295],[0]),e6 [18,156] [22,80,191,234,679,681,1166,1296,1297],([0,18,1,60,3,4,5,62],[22,80,111,808,809,810,1298,1299],[0]),([93,131,129,0,3,72,5],[171,172,315,628,748,1070,1300,1301],[0]),([131,129,0,2,3,5,70],[222,315,743,1081,1302,1303,1304],[0]),([212,1,177,2,3,4,5],[22,56,234,292,296,464,516,655,673,1305],[0]),([76,0,1,2,146,4,5,75],[80,234,598,1306],[0]),e6 [509] [42,80,396,864,1307,1308,1309],u6 [217,75] [40,80,561,1310],u6 [396,62] [151,424,499,525,821,822,823],u6 [140,141] [22,285,544,831,949,1103,1160,1311],e6 [510,59] [178,522,1312],([131,129,0,15,3,16],[40,628,1151,1313,1314],[0]),e6 [295,502] [93,234,501,806,899,1315],([93,131,129,0,2,3,5,59],[171,172,315,628,748],[0]),([131,129,0,2,3,156,5],[172,222,315,748,1166,1316,1317],[0]),([131,129,0,60,2,3,5,59],[172,315,875,876,1318],[0]),([131,129,0,2,3,5,59,62],[42,172,315,499,806,875,876,1319],[0]),([0,18,2,3,19,5,70],[57,219,234,743,1320,1321],[0]),([131,232,129,0,2,3,5,59],[172,315,1322],[0]),([131,234,1,2,3,4,5,70],[22,80,1323,1324],[0]),u6 [399,201] [93,234,1325],([131,17,0,1,3,4],[22,23,33,40,59,80,167,169],[0]),([131,47,0,1,2,4,5,59],[80,921,1162],[0]),([511,364,0,1,2,3,5],([80,178,528,533]++r 1326 4),[]),e6 [232,396] [178,191,810,1330],([93,18,2,3,96,19,5],[40,664,714,746,1331],[0]),([131,487,47,1,2,3,4,5],[22,40,80,1324,1332,1333],[]),e6 [93,395] [342,495,1334,1335],u6 [316,59] [156,178,1161,1201,1336],([131,0,1,2,3,4,70,59],[1161,1162],[0]),([186,17,0,1,3,4],[20,22,23,40,59,80,96,119,1337],[0]),([17,129,0,1,3,4],[22,23,40,80,157,158],[0]),u6 [395,16] [42,806,1124,1125,1126,1335,1338],([93,129,0,295,2,3,4,5],[396,806,1339],[]),e6 [395,60] [166,178,191,501,839,1124,1125,1340],e6 [231,395] [40],([129,0,295,60,2,3,4,5],[42,806,864,1341,1342],[]),([124,0,2,3,257,4],[42,80,130,136,137,151,1343],[0]),([0,18,2,3,19,75,59],[54,279,386,525,573,1344],[0]),([231,129,0,295,2,3,4,5],[396,806],[0]),([129,0,1,60,3,4,5,62],[111,1345],[0]),([416,1,2,96,4,90,5],[22,42,764,766,768,769,913,1346],[]),([164,129,0,1,2,3,4,59],[689,1347],[0]),([314,124,0,2,3,4],[80,82,94,130,133,135,136,151,161],[0]),([124,0,380,2,3,4],[80,130,133,135,136,151,1348],[0]),([129,234,1,2,3,4,5,70],[22,80,1349,1350],[0]),([153,124,0,2,3,4],[22,42,80,94,130,133,135,136,137,151,1351],[0]),([504,512,1,2,3,4,5],[80,188,1250,1252,1352,1353,1354],[]),([0,1,388,3,290,5],[42,80,376,497,1355,1356],[0]),([313,124,0,2,3,4],[42,82,94,130,133,135,136,151,163],[0]),([124,0,269,2,3,4],[22,130,133,135,136,137,151,1357,1358],[0]),([124,0,2,3,72,4],[42,80,136,137,1359],[0]),u6 [194,193] [40,42,80,570,1057,1058,1060,1360],([69,124,0,2,3,4],[42,94,130,133,135,137,151,1361],[0]),([364,0,513,2,3,4,5],([42,178,1273]++r 1362 5),[]),([372,124,0,2,3,4],[80,82,94,130,133,135,141,1367],[0]),([0,2,308,3,4,123],[80,132,1027,1368,1369],[0]),([0,1,308,3,309,5],[42,671,1370],[0]),([353,18,2,3,19,5],[56,685,1371,1372],[0]),u6 [308,366] [22,42,80,1309,1373,1374],e6 [449,514] [22,80],u6 [362,361] [22,80,342,734],([102,0,18,2,3,19,5],[57,212,213,220,279,553,1375,1376,1377],[0]),([0,295,2,3,515,4,5],[80,396,864,1378,1379,1380],[]),([302,412,304,2,3,4],[42,80,731,1073,1381,1382,1383],[0]),([124,303,2,3,4],[22,42,80,119,130,943,944],[0]),([124,0,2,516,3,4],[80,130,706,1384],[]),e6 [517,59] [93,166,424,899,1385],([124,0,2,3,488,4],[22,42,80,944,1386],[]),([0,2,3,146,19,5,75],[40,42,279,286,573],[0]),([124,0,2,3,4,518],[42,80,130,702,706,1387],[]),([302,153,124,0,2,3,4],[22,42,80,130,707,1388,1389],[]),([302,304,0,307,3,309],[80,1176,1390,1391],[0]),([69,0,18,3,19,5,16],[40,57,212,226,279,1392],[0]),([0,1,307,3,427,309,5],([671,954,1176]++r 1393 5),[]),([20,0,2,3,5,16],[34,37,40,41,42,266,367],[0]),([0,442,2,3,427,4,5],([178,778]++r 1398 4),[]),([39,69,0,1,2,3],[42,104,107,108,306,1402],[0]),([164,131,0,1,2,3,4,59],[921,1162],[0]),([0,1,307,3,370,5],[42,80,1403,1404,1405],[0]),([134,0,1,2,3,4,75,59],[234,525,560,561,562,1344],[0]),u6 [144,147] [22,660,1106,1406],e6 [457,59] [234,342,570,890],e6 [519,434] [22,80,342],([364,0,442,2,3,4,5,59],[22,80,234,398,1407],[]),([101,0,1,2,4,521],[80,1408,1409,1410],[]),e6 [364,370] [80,93,234,525,528],([231,232,0,18,1,3,4,5],[22,80,166,1274,1275,1411],[0]),([154,0,295,1,60,3,4,5],[111,166,424,1412],[]),([116,17,0,1,3,4],[20,22,23,40,59,80,119,121],[0]),([65,17,0,1,3,4],[19,20,22,80,96,202],[0]),([365,8,0,3,4,5],[40,42,67,68,80,88,119,1413],[0]),([17,0,1,301,3,4],[19,23,40,59,80,1414],[0]),([20,0,15,2,3,5],[34,37,42,130,233,429],[0]),([198,17,0,1,3,4],[20,22,23,40,59,80,96,119,282],[0]),([17,0,1,3,4,79],[22,23,59,80,96,119,1415],[0]),e6 [523] [22,119,178,187,188,191,1416,1417],([131,129,0,2,3,97,5],[130,222,315,1081,1289,1418,1419,1420],[0]),u6 [202,201] [22,40,93,234,829,830,832,1421,1422,1423],([1,2,144,3,96,4,5],[40,130,342,714,744,774,819,933,1106,1424],[0]),e6 [295,524] [234,424,516,806],([297,0,2,3,4,5],[42,80,1028,1029],[0]),([0,295,2,3,525,4,5],[42,396,864,1425,1426,1427],[]),u6 [315] [80,156,178,396,516,1428,1429],e6 [527] [80,156,864,1430,1431]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_7_2 : checkNodesBT W_23 g_23 F_23 P_23_7 A_23 B_23_6 7 N_23_7_2 = true := by decide +kernel
def N_23_7 := N_23_7_0 ++ N_23_7_1 ++ N_23_7_2
def B_23_7 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_7
set_option maxRecDepth 500000 in
lemma B_23_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 7 xs.toFinset) B_23_7 := by
  have hP := buildPoolsSubBT_sound (pdepth := 12) (W := W_23) (raw := r_23) (pspecs := ps_23) (used := U_23_7) S_23_ok
  have hm0 := checkNodesBT_mem (by decide) gp_23 W_23_ok hP A_23_ok B_23_6_ok C_23_7_0
  have hm1 := checkNodesBT_mem (by decide) gp_23 W_23_ok hP A_23_ok B_23_6_ok C_23_7_1
  have hm2 := checkNodesBT_mem (by decide) gp_23 W_23_ok hP A_23_ok B_23_6_ok C_23_7_2
  exact buildBucketsBT_of_mem (forall_append (forall_append (hm0) hm1) hm2)
def U_23_8 : List Nat := ([20,22,35,38,40,42,56,57,68,69,72,80,93,94,96,108,111,117,119,130,137,151,156,166,171,172,178,181,187,188,191,204,212,213,219,220,222,226,234,279,281,292,296,300,306,315,329,342,377,396,398,409,424,431,436,457,464,475,492]++r 494 4++[499,501,504,507,508,510,511,514,515,516,522,525,527,528,529,533,534,535,537,541,545]++r 551 5++[557]++r 559 4++[564,567,568,570,571,573,574,576,577,578,580,582,583,585,587,589,592,593,595,597,598,599]++r 602 5++[609,610,611,613,619,620,621,624,625,628,629,639,641,648,651,652,656,658,659,661,663,664,666,669,671,672,673]++r 678 8++[688,689,690,692,695,697,700,707,709,710,711,714,715,719,720,722,724,725,726,731,733,734]++r 738 9++[748,754,756,758,759,760,766,768,769,771,774,776,777,778,781,783,786,787,793,795,799,802,806,807,808,810,812,813,814,817,819,822,823,825,826,829,831,832,838,839,844,847,849,850,852,854,856,857,858,864,865,869,875,877,882,883,887,888,893,896,899,901,902,903,906,907,909,910,915,916,917,921,924]++r 930 4++[936,943,948,949,953,955,958,959,961,962,964,968,970,973,979,980,981,984,986,987,988,996,998,999,1001,1005,1013,1014,1019,1027,1032,1036,1051,1053,1054,1056,1057,1059,1060,1061,1063,1065]++r 1067 4++r 1073 7++[1081,1086,1091,1093,1094,1096,1097,1098,1100,1103,1106,1111,1112,1114,1117,1118,1120,1121,1124,1126,1130,1134,1141,1144,1146,1148,1151,1157]++r 1159 4++[1164,1166,1168,1169,1175,1176,1177,1179,1187,1188,1190,1191,1192,1196,1201,1202,1203]++r 1205 4++[1210,1211,1217,1224,1226,1229,1242,1248,1249,1252,1255,1261,1267,1269,1273,1274,1285,1286,1288,1289,1296,1297,1298,1300,1302,1306,1309,1310,1313,1315,1316,1324,1329,1330,1335,1339,1340,1342,1344,1347,1350,1352,1354,1362,1373,1374,1376,1377,1382,1391,1393,1395,1396,1397,1399,1400,1401,1409,1412,1418,1422]++r 1432 1885)
def P_23_8 : BT (Option BoundPool) := buildPoolsSubBT 12 W_23 r_23 S_23 ps_23 U_23_8
def N_23_8_0 : List NodeSpec := [([376,39,0,1,2,3],[40,80,108,151,475,516,651],[0]),([376,358,0,1,445,2,3],([42,80,516,907]++r 1432 5),[0]),e6 [528] [42,80,93,178,234,1437,1438],e6 [530] [22,80,178,234,1439,1440,1441],([39,0,1,2,3],[72,306],[0]),u6 [414,90] [22,40,42,119,191,496,516,570,1093,1094,1177,1442,1443],u6 [417,90] [22,42,178,492,496,516,766,1093,1126,1177,1444],e6 [532] [42,178,191,234,1445,1446,1447],u6 [423,59] [22,80,119,166,424,499,525,806,810,1013,1014,1448,1449,1450],e6 [290,59] [42,80,151,525,806,1013,1451,1452],e6 [533,59] [80,166,501,525,806,810,1013,1453,1454,1455],([0,1,2,3,290,5,291],[42,80,499,501,1456,1457],[0]),u6 [290,421,59] [80,499,501,515,810,1458,1459],u6 [387,59] ([40,80,151,166,499,501,525,806,810,1013]++r 1460 4),([376,358,0,1,2,3,458],[42,80,516,1436,1464,1465,1466],[0]),([535,534,1,2,3,4,5],([42,80,187]++r 1467 4),[]),u6 [290,293,59] [80,499,501,525,541,1471,1472],([0,1,2,458,4,5,59],[80,342,501,516,1473,1474],[]),e6 [529,59] ([80,166,234,499,525,806,810,1013,1440]++r 1475 4),u6 [231,290] [42,80,117,497,516,541,589,1479,1480,1481],([231,232,0,1,3,4,5],[40,80,166,810,1274,1482],[0]),([0,1,2,3,4,70,59],[80,191,984,986],[0]),u6 [475,59] [40,80,151,156,191,525,806,1013,1201,1483,1484],e6 [536,59] [42,80,93,499,501,525,810,1013,1485,1486],([164,0,1,2,3,4,59],[80,178,342,1100],[0]),([0,1,2,3,111,5,59],[80,119,151,166,501,1032,1036,1487],[0]),u6 [419,62] ([42,80,117,119,504,507,510,1273]++r 1488 5),u6 [60,290] [42,80,111,166,178,497,499,515,516,541,839,1203,1479,1493,1494,1495],([0,1,60,3,4,5,62],[80,166,808,810,1298,1496],[0]),u6 [321,59] [80,151,166,342,424,501,525,806,810,1013,1497,1498,1499],u6 [419,364,59] [42,80,151,499,507,806],u6 [419,364] ([80,93,507,510,527,528,533,1097]++r 1500 4),u6 [364,291] ([80,156,398,533,537,1126]++r 1504 6),u6 [232,364] [40,80,178,528,1196,1330,1510,1511],u6 [364,62] [40,80,151,178,398,504,528,533,1273,1488,1491,1512,1513],u6 [456,290] [42,80,1479,1493,1514,1515],([0,1,2,3,4,537,59],[80,234,525,1516,1517,1518],[]),e6 [295,59] [42,80,166,499,501,525,806,810,1013,1519,1520],([538,0,1,2,3,4,59],[42,80,342,806,1521],[]),e6 [295,290,59] [80,499,501,525,541,695,806,1522,1523],([0,295,2,3,4,5,296],[42,80,525,1524,1525],[0]),([539,0,2,3,4,5,59],[80,499,806,1526,1527,1528],[]),e6 [376,295] ([80,108,342,396,695,806,864,899]++r 1529 9),e6 [541] ([80,234]++r 1538 5),e6 [542,138] ([42,516]++r 1543 6),([376,0,1,2,3,543,5],[80,108,156,516,1549],[]),e6 [544] ([80,234]++r 1550 4),e6 [546] [80,156,188,234,516,1554,1555],e6 [548] [42,178,188,191,1556,1557,1558],e6 [93,441] ([80,156,495,516,666,776,1438]++r 1559 5),e6 [93,529] ([80,156,191,495,666,1561]++r 1564 4),e6 [93,290] ([42,117,497,515,541,666,1479,1563]++r 1568 4),u6 [93,295] [342,396,495,666,679,695,806,899,1529,1532,1535,1561,1563,1572,1573],e6 [93,138,540] [22,42,151,516,666,1563,1570,1574,1575],e6 [93,522] ([80,119,156,191,495,666,1060,1552,1561]++r 1576 6),([93,169,0,1,3,4,79],[119,577,578,832,1582,1583,1584],[0]),([0,1,2,3,524,5,38],[80,516,1585],[]),u6 [231,295] [80,234,396,695,806,1201,1529,1586,1587],u6 [524,59] ([42,80,191,501,525,806,1013]++r 1588 4),([0,1,2,156,4,5,59],[80,342,810,893],[0]),e6 [376,549] ([80,108,178,191,516,1533,1536]++r 1592 5),u6 [479] [22,93,234,516,1267,1597,1598],([487,47,1,2,3,4,5],[22,40,80,187,1065,1599,1600],[0]),u6 [476,59] [42,80,119,166,501,525,806,831,1013,1267,1601,1602,1603],([47,0,1,2,4,5,59],[40,80,119,178,342,1190],[0]),([138,47,0,1,2,4,5],[22,119,156,1078,1242,1547,1604,1605],[]),e6 [376,550] ([80,108,178,191,1160,1533,1537]++r 1606 6),e6 [550,59] [42,80,166,499,501,525,806,810,1013,1160,1477,1610,1612],e6 [551] [42,178,234,1546,1613,1614,1615],e6 [552] [93,108,178,187,191,234,1582,1616,1617],u6 [522,15] ([119,178,191,1146,1552,1576,1578]++r 1618 6),([138,0,1,15,3,4,16],([22,119,1151,1313,1547]++r 1624 4),[0]),([553,0,1,2,3,79,5],([342,516,1582,1623]++r 1628 4),[]),([1,2,3,97,332,4,5],[22,80,130,204,1134,1632],[0]),e6 [555] [42,93,234,516,570,1633,1634,1635],e6 [502] [80,93,166,234,424,1636,1637,1638],e6 [557] [80,93,156,187,234,516,1639,1640,1641],e6 [441,59] [80,151,166,499,501,525,570,776,806,810,1013,1438,1642],e6 [559] [80,93,187,188,234,342,516,1643,1644,1645],e6 [561] [80,93,234,516,1646,1647,1648],e6 [562] [80,234,516,1649,1650],e6 [563] [80,93,187,234,1651,1652],e6 [564] [80,93,234,499,810,1653,1654],e6 [376,565] ([22,42,80,93,108,234,1533]++r 1655 4),e6 [567] [80,93,156,187,188,234,342,1659,1660],e6 [568] ([80,93,234]++r 1661 5),e6 [101,569] ([80,570,1652]++r 1666 6),e6 [569,59] [80,234,499,570,810,1013,1126,1671,1672],e6 [570] [80,234,1673,1674],e6 [571] [42,80,93,234,570,1671,1675,1676,1677],e6 [573] ([80,93,234]++r 1678 4),u6 [370] [42,80,93,166,234,499,1682,1683,1684],u6 [364,309,59] [80,166,528,806,1067,1685,1686],e6 [574] [80,93,156,187,234,1687,1688],u6 [521] [80,93,188,234,1689,1690,1691],e6 [575] [22,42,178,188,1692,1693,1694],([101,0,1,2,3,4,428],([80,191,516,595,1027]++r 1695 4),[]),([0,1,2,3,4,428,59],[80,191,501,516,595,1696,1699,1700],[]),e6 [577] [80,93,187,234,342,516,1701,1702,1703],e6 [578] ([80,93,156,178,188,234]++r 1704 4),([0,1,2,576,4,5,59],[80,501,516,570,810,1708,1709,1710],[]),([0,1,15,3,4,79,16],[119,832,1151,1313,1626,1631,1711],[0]),e6 [101,579] ([80,570,604,1669,1670,1697]++r 1712 4),e6 [580] ([42,80,93,234,516,570]++r 1715 6),e6 [69,547] ([156,191,552,568,582,1557]++r 1721 5),e6 [69,441] ([80,191,516,552,568,582,776,1438,1559]++r 1726 4),e6 [581] [80,93,156,187,234,570,1729,1730,1731],([69,534,0,1,2,4,5],[42,80,178,1724,1732,1733,1734],[]),e6 [69,529] [80,156,191,552,582,1440,1478,1564,1566,1724,1735],e6 [582] [80,93,234,1724,1736,1737,1738],u6 [416,90] [22,42,93,119,494,496,570,766,768,1093,1094,1177],e6 [531,69] ([191,552,568,582,1446,1724,1728,1729]++r 1739 4),([234,1,2,3,4,5,70],[22,80,187,641,739,887,888,1743],[0]),e6 [376,583] ([42,80,108,191,234,516,1533,1536]++r 1744 7),u6 [415,90] [22,42,130,234,496,516,1093,1094,1126,1177,1751,1752],([154,0,1,60,3,4,5,59],[42,80,111,166,522,810,1126,1753,1754],[0]),e6 [583,37] ([42,80,156,234,516,570,1112,1126,1749]++r 1755 4),e6 [584,59] [42,80,342,499,501,525,810,1013,1126,1759,1760],e6 [585] [80,156,234,516,1749,1761,1762,1763],([376,358,0,1,2,3,72],[80,907,1465,1764,1765],[0]),e6 [586] ([80,93,188,234]++r 1766 4),e6 [587] [80,93,234,680,1764,1770,1771],e6 [588] [80,93,178,187,234,1768,1772,1773,1774],([358,0,1,2,3,429,5],([178,516,1764]++r 1775 4),[]),u6 [494,37] ([80,156,516,1111,1112,1755,1773]++r 1779 4),u6 [447] ([22,93,178,187,191,342,495,817]++r 1783 5),([304,0,442,2,3,4,5],[156,178,234,778,1067,1399,1400,1784,1788,1789],[0]),([304,0,1,307,3,309,5],([178,671,1176,1393,1784]++r 1790 4),[0]),([304,0,1,2,3,4,428],[80,191,516,593,595,883,1787,1791,1794,1795],[0]),([0,589,1,2,3,79,5],[516,1060,1631,1789,1796,1797],[]),u6 [295,459,59] [80,525,806,810,899,1798,1799],e6 [154,427] ([22,93,424,516,1395,1396,1397,1477,1785]++r 1800 4),e6 [372,427] ([22,40,93,1396,1397,1401,1477,1800]++r 1804 5),([590,0,1,2,3,4,59],[42,80,342,499,1809],[]),u6 [307,427] [22,516,1027,1395,1396,1401,1477,1800,1810,1811,1812],([302,590,0,1,2,3,4],[80,93,1631,1813,1814,1815],[]),e6 [591] ([42,80,178,191,1813]++r 1816 5),e6 [302,476] ([80,130,234]++r 1821 6),e6 [302,558] ([22,80,93,234,516,582]++r 1827 4),e6 [592] [80,93,234,516,1831],e6 [593] [80,93,178,187,188,570,1813,1832],e6 [594] [42,93,1833,1834,1835],e6 [302,595] ([80,93,151,234,424,516,1825]++r 1836 4),e6 [596] ([80,156,187,342,516,552,570]++r 1840 5),([302,138,304,0,2,3,4],([42,234]++r 1845 7),[0]),([302,304,0,2,3,4,79],([42,1060]++r 1849 4),[0]),([302,304,0,307,2,3,4],[80,1812,1850,1853,1854],[0]),([520,101,0,1,2,4,5],[42,1409,1670,1855],[0]),([302,69,304,0,2,3,4],[80,151,1728,1849,1851,1854,1856],[0]),([302,304,0,2,3,72,4],[80,1850,1851,1857,1858],[0]),([302,304,0,2,3,444,4],[42,234,1849,1850,1854,1859,1860],[0]),([420,0,2,3,4,5,59],[40,80,166,508,511,514,806],[0]),e6 [444,59] [42,80,234,525,570,806,1013,1859,1861,1862],u6 [503] [42,80,156,178,191,516,1861,1863,1864,1865],e6 [93,444] ([80,117,234,570,666,1563,1570,1859]++r 1866 4),([302,304,0,2,3,488,4],[42,80,234,731,1851,1854,1870,1871],[0]),u6 [512,428] ([80,516,595,1352]++r 1872 4),([0,1,2,488,4,5,59],[80,234,342,525,1876,1877],[]),u6 [502,59] [80,166,178,501,525,806,1013,1315,1636,1637],([1,2,3,488,597,4,5],([42,80,187,1470]++r 1878 4),[0]),([302,304,0,2,3,4,309],[42,1067,1850,1882],[0]),([302,304,0,499,2,3,4],[80,151,234,1157,1847,1850,1854,1883],[0]),u6 [433,59] ([80,151,166,234,501,525,570,806,810,1013]++r 1884 4),([302,412,1,2,3,4,5],([42,80,1073]++r 1888 4),[0]),e6 [598] [42,80,191,234,570,1547,1892,1893],([303,1,2,3,444,4,5],([42,80,1866]++r 1894 4),[]),e6 [302,524] ([80,93,234,424,516,1825]++r 1898 4),([303,1,2,3,4,518,5],[42,80,1895,1896,1902,1903,1904],[]),([303,1,2,516,3,4,5],[80,234,1896,1905,1906],[]),([0,441,2,3,4,5,123],[80,234,516,1562,1658,1907],[]),([0,529,2,3,4,5,123],[80,234,1478,1908,1909],[]),u6 [515,59] [42,80,516,806,1013,1910,1911,1912],([448,0,1,2,4,5,59],[80,151,806,1913,1914],[]),([0,295,2,3,4,5,123],[80,93,234,806,1535,1915,1916],[0]),([138,448,0,1,2,4,5],([42,80,156,1846,1914]++r 1917 4),[]),e6 [549,59] [42,166,499,501,525,806,810,1013,1477,1595,1596,1921],e6 [599] [42,80,178,191,570,1846,1922,1923],u6 [305] [80,178,191,1060,1248,1909,1924,1925],e6 [600] [42,80,93,234,1610,1926,1927],([0,549,2,3,4,5,123],[80,234,1928],[]),([0,550,2,3,4,5,123],[40,80,234,1611,1929],[]),e6 [601] [80,93,178,187,188,234,342,1930,1931,1932],u6 [448,154] [22,80,156,178,516,825,1785,1920,1933,1934,1935],u6 [464] [22,80,93,342,424,924,1175,1785,1936],([302,0,1,307,3,309,5],[80,178,671,955,1176,1393,1835,1937,1938],[0]),([0,1,307,3,309,5,123],[80,1175,1176,1939,1940],[0]),([511,0,1,2,3,5,59],[42,80,166,499,1329,1941,1942],[0]),([0,1,2,3,4,123,428],[80,191,234,516,595,1943],[]),([0,1,2,3,476,5,38],[80,119,516,1823,1944],[]),([0,1,307,3,309,5,59],[42,80,166,671,810,1176,1792,1945,1946],[0]),([69,448,0,1,2,4,5],[80,151,178,1728,1914,1919,1933,1947],[]),e6 [602] [80,156,188,516,1175,1857,1948,1949],e6 [603] [42,93,178,188,191,1615,1950],u6 [364,290,59] [42,80,499,501,525,541,806,1951],e6 [604] [42,93,156,178,187,191,234,1631,1818,1952,1953],([302,372,304,0,2,3,4],[80,731,1391,1805,1847,1854],[0]),e6 [605] [42,93,178,191,1807,1954,1955],([0,1,2,3,290,5,38],[80,499,516,1571,1956,1957],[]),e6 [606] [42,93,178,187,234,342,1685,1958,1959,1960],([376,358,0,441,1,2,3],[42,516,776,907,1435,1436,1961,1962],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_8_0 : checkNodesBT W_23 g_23 F_23 P_23_8 A_23 B_23_7 8 N_23_8_0 = true := by decide +kernel
def N_23_8_1 : List NodeSpec := [([0,122,1,307,3,309,5],[42,671,1176,1393,1963,1964,1965],[0]),u6 [308] ([22,178,342,1027,1309,1373,1374,1964]++r 1966 4),e6 [122,595] [80,93,151,234,424,516,1836,1838,1959,1970,1971,1972],u6 [295,290] [42,80,234,499,515,516,541,806,899,1479,1522,1523,1973],([69,0,1,2,3,37,38],[42,568,609,793,1724,1974,1975,1976],[0]),e6 [520,123] ([22,42,80,570,1175,1909,1914]++r 1977 4),u6 [122,429] [80,93,234,516,1764,1778,1959,1981,1982,1983],([154,0,122,2,3,4,123],([22,93,672,710,1249,1785,1803]++r 1984 6),[0]),([0,122,2,3,4,309,123],[42,1067,1986,1990],[0]),e6 [607] [22,40,108,187,191,342,1791,1805,1991,1992],u6 [449] [22,80,849,852,1067,1069,1175,1909],([69,0,122,2,3,4,123],[151,568,570,1249,1728,1984,1986,1987,1988,1993],[0]),([0,122,2,3,72,4,123],[80,1857,1986,1987,1994,1995],[0]),([124,0,2,3,4],[94,137],[0]),e6 [458] [80,93,234,1464,1996,1997],([608,0,1,2,3,79,5],([342,516,1631,1818]++r 1998 5),[]),([608,0,1,2,3,309,5],[42,191,516,570,1685,2002,2003,2004],[]),e6 [69,608] [42,191,516,568,2005,2006],([538,0,1,2,3,37,4],[42,2007,2008],[]),([538,609,1,2,3,4,5],[42,80,187,1470,2009,2010,2011],[]),e6 [610] ([80,516]++r 2012 4),u6 [461] [22,191,234,342,495,903,1412,1959,1969,2016,2017,2018],([547,1,2,3,96,4,5],[188,714,744,759,769,774,819,933,1557,2019],[]),([0,1,15,3,184,4,16],[40,1151,1313,1626,2008,2020,2021],[0]),e6 [611] ([42,80,178,191,570,1785]++r 2021 4),u6 [351,290,59] [80,166,499,501,515,525,806,2025,2026],e6 [184,612] ([42,80,1807]++r 2027 5),e6 [613] [42,178,187,191,1741,2008,2032,2033],u6 [451] [22,187,234,342,495,666,865,1161,1561,2034,2035],e6 [101,433] [80,178,516,570,604,1669,1670,1697,1885,1886,1887,2036,2037],e6 [614] [108,178,187,191,1060,2038,2039],([531,1,2,3,96,4,5],[40,188,652,714,759,769,774,819,1446,2040],[]),([1,2,3,566,615,4,5],[42,80,1469,2041,2042],[]),([0,6,7,3,4,79,5],[80,611,832,964,1582,2043,2044],[0]),e6 [184,428] [42,80,516,595,1696,1872,1873,2045,2046,2047],u6 [497,59] [40,42,80,166,501,516,525,695,806,810,1013,1130,2048,2049,2050],e6 [579,59] [80,151,166,234,342,501,525,570,806,810,1013,1715,2051,2052],([0,1,2,184,576,4,5],([80,191,234,516,1710,2047]++r 2053 4),[]),e6 [616,59] [80,151,156,234,525,806,1013,2057,2058,2059],u6 [146,75] [22,40,42,560,561,567,659,678,697,1306,2060],([531,0,2,3,184,4,5],[234,342,1446,1741,2008,2047,2061,2062,2063],[]),u6 [93,131,59] [80,495,499,810,921,1161,1162,1561,2064,2065],([579,0,2,3,184,4,5],[80,234,342,516,1715,1812,2047,2066,2067,2068],[]),([131,169,1,2,3,96,4,5],[40,80,714,759,769,774,857,959,2069,2070],[0]),e6 [618] ([42,80,191,234,516,570]++r 2071 6),([0,1,307,3,184,309,5],[80,671,1176,1792,2021,2077,2078,2079],[]),e6 [620] [80,188,234,516,2080,2081],([302,304,303,2,3,4],[42,80,119,234,731,1382,1847,2082],[0]),([181,154,0,2,3,4,5,123],[80,119,234,1068,1477,1785,1803,2083,2084],[]),([0,1,621,3,4,5,59],[499,806,810,2085,2086,2087],[]),e6 [69,589] [93,108,191,516,568,1728,1797,2088,2089,2090],([433,1,2,3,96,4,5],[80,342,652,714,715,759,769,774,819,1885,2091,2092,2093],[]),e6 [622] [80,191,424,570,1060,1582,2094,2095],e6 [138,623] ([42,80,191,516,1846]++r 2096 7),([6,1,2,3,96,37,4,5],([40,80,652,744,759,768,915,917]++r 2103 5),[0]),([624,1,2,3,4,5,623],[40,80,130,187,2108,2109],[]),e6 [626] [80,516,2110,2111],([138,0,1,2,3,627,5],[42,80,156,516,2112,2113],[]),e6 [629] ([80,93,156,187,191,342,516]++r 2114 4),u6 [129,70] [22,42,80,191,516,568,641,688,742,743,1302,2118,2119,2120],e6 [558,123] [22,516,582,1175,1830,1977,2083,2121,2122],([0,1,2,439,72,4,5],([42,191,234,1995]++r 2123 5),[]),e6 [630] [22,80,93,156,187,188,234,516,2128,2129,2130],([351,0,1,2,3,37,38],[42,609,610,1974,2131,2132],[0]),e6 [631] [80,234,2133,2134],([554,1,2,3,96,4,5],[42,342,652,744,759,769,819,1634,2135],[]),u6 [351,90] [22,40,234,496,516,768,1093,1094,1126,1177,2132,2136,2137],([304,1,307,2,3,96,4,5],[22,80,652,744,774,781,786,812,813,953,1811,2138,2139],[0]),([376,358,0,1,2,3,184],[151,907,1435,1465,2031],[0]),([0,18,1,2,146,4,5,59],[22,42,281,342,525,561,2140],[0]),([131,69,0,1,3,4,5,16],[40,80,226,568,720,921,1161,2065,2141,2142],[0]),u6 [47,18] [22,40,80,93,178,234,409,580,598,613,1078,1079,1191,2143,2144],([351,0,1,307,3,4,5,59],[80,166,499,806,810,1126,1309,2026,2145,2146,2147],[]),([101,351,375,0,3,4,5],[80,93,178,795,906,1669,1670,2148,2149,2150],[0]),e6 [632] [42,1622,2151,2152,2153],([138,351,375,0,3,4,5],[42,80,93,178,795,906,1547,1846,2148,2150,2154,2155],[0]),u6 [18,59,62] ([22,40,80,119,166,409,499,501,525,806,810,1211,1488]++r 2156 4),u6 [231,19,59] [80,166,587,589,806,810,1103,1207,1208,2160],e6 [633,181] ([191,234,495,738,1477]++r 2161 7),e6 [634] [42,80,191,570,1805,2031,2078,2168,2169],([0,1,2,7,3,37,38],[22,40,793,1059,1976,2170],[0]),e6 [636] ([80,93,156,187,234,516]++r 2171 4),([376,358,375,0,1,2,3],[80,907,1436,2175,2176],[0]),e6 [637] [80,156,178,188,342,516,2177,2178],u6 [18,404] [22,93,409,495,516,554,557,561,564,2179,2180,2181],e6 [638] [22,40,93,108,187,191,342,1533,1536,2182,2183,2184],u6 [93,18,75] [234,329,561,564,567,666,2185],u6 [525,59] [80,156,516,806,1013,2186,2187,2188],([101,18,1,177,2,3,4,5],[130,292,296,516,604,613,620,621,673,1713,2189,2190,2191],[0]),e6 [101,467] ([80,178,234,604,930,1669,1670,1697]++r 2192 4),u6 [350,18,59] [40,80,166,409,525,606,1114,2196,2197],e6 [639] [80,188,516,2198,2199,2200],u6 [396] [151,178,191,499,525,822,823,1168,1169],u6 [468] ([42,80,234,516,570,930]++r 2201 4),e6 [640] [42,80,93,178,187,570,1546,1845,2205,2206,2207],e6 [642] ([80,156,516]++r 2208 5),([0,18,2,3,72,19,5],[40,212,279,1857,2213],[0]),e6 [643] [22,130,156,342,1059,1777,2214,2215],([351,375,0,3,4,79,5],[80,795,832,906,1060,2150,2216],[0]),e6 [644] [40,108,342,1658,2217],e6 [534,7] ([22,80,1059]++r 2218 5),e6 [645] [80,156,516,1669,1670,2223,2224],([302,303,2,3,184,4,5],[80,234,1889,2082,2225,2226],[0]),e6 [101,442] [80,156,178,570,604,1399,1400,1652,1670,1693,2227,2228],e6 [646] [80,156,187,188,234,342,516,2229,2230,2231],([351,375,0,3,37,4,5],[40,795,1096,1741,1773,2150,2232],[0]),u6 [419,7,59] [80,166,499,510,2233,2234],e6 [648,138] [42,516,1544,1547,2235,2236,2237],e6 [649] [42,80,516,1160,2021,2238,2239],u6 [208] [80,156,166,516,806,1019,1076,1077],e6 [650] [42,93,178,187,756,2240],e6 [651] ([80,156,516,1187,1477,2167]++r 2241 4),e6 [7,652] ([22,80,516,1059,2220,2233]++r 2245 6),([653,1,2,3,96,4,5],[80,188,714,744,819,2251],[]),([376,358,0,1,2,413,3],[80,516,907,2252,2253],[0]),e6 [654] [42,80,570,1547,1846,2254,2255],([617,0,1,2,3,5,38],([80,234,516,570]++r 2256 5),[]),e6 [655] [80,570,582,587,1724,1728,2261,2262],u6 [443] [22,93,108,178,187,342,787,1067,1784,2263],e6 [101,625] ([80,570,1669]++r 2264 4),u6 [193] [80,570,832,1057,1059,1060,2268],e6 [656,138] [42,80,516,1846,2269,2270],([375,0,295,2,3,4,5],[80,119,234,806,2271,2272,2273],[]),([358,0,6,7,3,4,5],[42,178,611,964,1777,2274,2275,2276],[0]),e6 [657] [80,93,187,234,1697,1803,2277,2278],e6 [656,79] [80,156,342,495,516,832,1060,2270,2279,2280,2281],u6 [19,16,59] ([80,166,587,810,896,1103,1118]++r 2282 5),e6 [93,515] [80,117,1563,1570,1910,2287,2288,2289],([538,376,0,1,2,3,4],[80,156,1658,2008,2290,2291],[]),([0,18,1,15,3,4,16],[22,40,561,869,1151,1313,1624,1626,2292,2293,2294],[0]),([364,0,18,2,3,4,5,59],[22,80,234,398,436,499,525,527,533,719,806,1126,1224,1226],[0]),e6 [658] [80,156,178,187,234,516,1959,2126,2295,2296,2297],([323,101,0,1,2,4,5],[22,156,1261,1652,1669,2298],[0]),([302,154,304,0,2,3,4],[22,119,130,234,1391,1785,1849,1850,1851,1854,2299,2300],[0]),e6 [101,431] [80,570,1053,1056,1669,1670,1697,2301,2302],u6 [93,138,506] [22,42,516,666,1255,1547,1563,2303,2304,2305],e6 [659] [80,93,234,1652,1670,2306,2307],([0,1,2,431,3,79,5],[80,516,832,1056,1059,1060,2302,2308],[]),e6 [660] [22,178,191,516,1910,2309,2310],([69,18,1,177,2,3,4,5],[22,40,292,516,552,613,620,621,673,692,2311,2312,2313],[0]),([0,1,2,3,444,5,38],[80,234,516,1869,2314,2315],[]),e6 [661] [80,188,516,2316,2317],e6 [662] ([42,80,234,516,570,1885]++r 2318 4),e6 [663] ([42,80,93,178,187,342,570,2259]++r 2322 4),e6 [664] [80,93,178,187,188,2259,2326],e6 [665] [42,516,680,2327],e6 [666] [22,516,2302,2328,2329,2330],e6 [138,635] ([42,80,234,516,1547,2132]++r 2331 5),([372,0,1,2,3,290,5],[80,497,499,516,2336,2337],[]),u6 [154,439] [22,42,234,1803,2124,2125,2338,2339,2340],([69,0,18,2,3,19,5],[57,93,212,220,234,279,552,1728,2341],[0]),([375,0,1,2,3,37,38],[80,609,610,793,1974,2101,2342],[0]),([93,169,0,1,3,4,19],[22,130,577,587,1103,1584,2343,2344],[0]),([484,101,0,1,2,4,5],[22,1051,1669,1670,2222,2345],[0]),([667,1,2,3,4,5,652],([42,80,187,2245]++r 2346 4),[]),([138,0,122,2,3,4,123],([42,570,1615,1846,1984]++r 1986 4++[2350]),[0]),([376,0,6,7,3,4,5],[80,191,611,964,1536,1537,2044,2274,2351,2352],[0]),([0,1,2,3,72,37,38],[80,610,1764,1976,1995,2353],[0]),e6 [668] ([80,156,178,570,738,1309,1477]++r 2354 5),e6 [669] [80,156,187,516,2359,2360,2361],e6 [670] [42,80,178,188,570,2021,2362,2363],u6 [144] [22,156,188,409,561,661,1106,1146,1285,2364,2365],u6 [492,59] [42,80,166,499,501,525,806,810,1013,1098,2366,2367],([93,181,169,0,1,3,4],[22,40,191,577,578,1584,2167,2356,2368,2369,2370],[0]),u6 [101,350,18] [40,80,409,561,604,970,1114,1670,2190,2371],e6 [671] [80,178,187,188,1347,2178,2372],e6 [181,553] [22,93,108,191,234,516,1629,1630,2356,2373],([1,2,3,96,4,5,428],[80,652,714,759,813,819,882,933,1696,2374],[0]),u6 [102,18] [22,93,156,191,234,516,561,564,580,854,1376,1377,2375,2376,2377],e6 [672] [80,93,156,178,187,234,501,2378,2379],u6 [69,18,75] [40,234,552,560,561,567,568,2380],u6 [431,59] [22,80,166,501,806,1013,1056,1059,2302,2381],u6 [93,129,59] [42,80,688,806,1347,1570,2153,2382],([8,0,3,4,5],[68,69],[0]),([0,1,560,2,3,79,5],[516,832,1631,1647,2383,2384],[]),([674,1,2,3,4,5,673],([80,187]++r 2385 4),[]),u6 [18,253] [22,42,80,93,409,564,602,603,2389,2390,2391],([376,351,375,0,3,4,5],[80,93,178,795,906,1536,1658,2148,2150,2392,2393],[0]),u6 [278] [178,181,191,499,648,806,838],u6 [427,309] [22,1061,1067,1395,1401,1477,2394,2395,2396],([93,131,0,1,3,72,4,5],[40,80,921,1070,1161,1162,1300,1995,2064,2065,2397],[0]),([169,0,1,2,3,4,75],[80,234,329,2398,2399,2400],[]),e6 [181,524] [80,191,234,424,516,1477,1588,1590,1591,1898,1900,2166,2167,2401],e6 [675] [80,93,156,178,570,1309,2402,2403],([608,1,2,3,96,4,5],[42,188,652,714,744,759,769,774,819,2001,2404,2405],[]),([18,1,2,3,96,4,5,75],[40,300,560,697,759,2406,2407],[0]),e6 [676] ([22,130,1758]++r 2408 5),u6 [47,19] [22,80,587,896,1063,1078,1079,1103,2413,2414,2415],([0,6,7,3,4,5,59],[40,80,166,611,810,964,2044,2416],[0]),u6 [131,16,59] [80,499,570,831,921,1161,1162,2065,2417,2418],u6 [231,18,59] [22,80,166,525,564,806,810,1126,1207,1208,1210,2419],e6 [101,18] ([80,156,570,604,740,1286,1652,1670,2228]++r 2420 4),([17,0,1,3,4],[20,96],[0]),([93,129,1,2,3,96,4,5],[40,42,80,652,714,746,769,2120,2382,2424,2425,2426],[0]),e6 [677] [22,130,187,191,342,424,2175,2276,2427,2428,2429],([1,2,3,96,4,5,673],[80,652,714,933,2385,2430,2431,2432],[]),([1,560,2,3,96,4,5],[652,714,759,769,774,1647,2433],[]),([1,2,3,481,482,4,5],([42,80]++r 2434 7),[0]),e6 [678] [80,93,234,2384,2441,2442],u6 [18,252] [80,409,561,564,570,604,725,2443,2444,2445]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_8_1 : checkNodesBT W_23 g_23 F_23 P_23_8 A_23 B_23_7 8 N_23_8_1 = true := by decide +kernel
def N_23_8_2 : List NodeSpec := [u6 [231,131,59] [80,499,810,921,1161,1201,2446],u6 [201] [80,93,234,829,831,832,1422,2447],u6 [446] [22,151,156,814,1027,1791,1812,2448,2449,2450],e6 [679] [22,40,187,342,495,516,1741,1773,2451,2452],([154,304,1,2,3,96,4,5],[652,709,715,744,774,786,819,953,958,1802,2453,2454],[0]),([1,2,431,3,96,4,5],[80,130,342,652,714,769,774,2302,2455],[]),e6 [184,556] ([42,80,516,2047]++r 2456 5),e6 [680] ([42,93,178,187,191,342]++r 2461 4),([131,1,2,3,96,4,5,16],[40,80,714,759,769,856,959,979,2142,2465,2466],[0]),([93,0,18,2,3,19,5],[57,93,212,213,220,234,279,663,664,666,1570],[0]),([93,18,1,2,3,96,4,5],[40,80,714,745,746,759,769,774,819,1581,2467,2468,2469],[0]),e6 [681] [80,151,188,234,516,2470,2471],([302,304,0,2,3,4,518],[42,234,1849,1850,1854,2472,2473],[0]),e6 [376,641] ([42,80,108,234,516,1536]++r 2474 5),([129,0,550,2,3,4,5],[42,80,178,234,1160,1347,1610,2479],[]),([101,0,1,2,3,4,436],[80,191,234,604,754,756,2480,2481,2482],[]),e6 [682] ([42,80,156,178,187,570,1812]++r 2483 4),([154,122,1,2,3,96,4,5],([80,652,709,714,715,744,759,774,901,902,909]++r 2487 4),[0]),([1,625,2,3,96,4,5],[80,342,652,714,769,819,2267,2491],[]),e6 [683] [80,156,187,188,234,342,516,2492,2493,2494],([424,0,1,3,4,5,59],[42,80,166,499,529,534,2495],[0]),e6 [684] [42,80,516,1570,2496,2497,2498],u6 [375,90] [22,119,130,496,516,768,1093,1094,1177,2101,2137,2412,2499,2500],([1,2,3,96,4,5,612],[80,714,744,759,819,2027,2501,2502],[]),e6 [685] ([42,80,93,191,570,832,1818,2026]++r 2503 4),e6 [686] ([80,156,191]++r 2507 4),e6 [687] ([22,191,516,570,2267]++r 2511 4),([129,0,1,15,3,4,16],[22,40,1151,1624,1626,2153,2515],[0]),([302,124,0,2,3,4],[42,80,119,130,234,707,943],[0]),([553,1,2,3,96,4,5],[130,188,652,714,744,759,774,819,1629,2516],[]),([101,154,0,6,1,3,4,5],([178,1412,1652,1669,1670,1785,2259]++r 2517 6),[]),e6 [387,290,59] [42,80,151,499,501,525,541,806],u6 [18,16,59] [22,80,166,409,499,501,525,561,564,598,806,810,1160,1187,1242,2157,2158,2282,2283],u6 [434] [22,80,342,516,680,1059,1075,1478,2523,2524],e6 [492] [80,93,156,166,191,516,525,1098,1126,2366,2367,2525,2526],e6 [688,181] [80,108,234,516,2166,2527,2528],e6 [93,181,689] [22,42,234,666,1477,1561,2529,2530],u6 [6,90] [22,234,496,516,756,766,1093,1094,1177,2105,2137,2522,2531],u6 [164,131] [22,40,80,93,156,234,921,1141,1229,1324,2532,2533],([375,0,529,2,3,4,5],[80,156,234,1440,1478,2534],[]),u6 [18,75,253] [42,559,560,807,2535,2536],([0,545,2,3,184,4,5],[178,234,570,1555,2008,2021,2178,2537],[]),([1,2,467,3,96,4,5],[80,188,342,652,714,759,769,774,819,930,2538,2539,2540],[0]),([572,1,2,3,96,4,5],[80,188,714,744,759,2541],[]),e6 [538,154] [22,80,156,178,516,825,1785,1935,2009,2542,2543,2544],([0,1,2,3,4,75,59],[80,234,516,525,560,1344,2545],[]),([358,0,1,2,3,4,436],[42,191,234,754,756,2546,2547],[0]),([0,442,2,3,184,4,5],[80,178,234,1067,1400,1693,2021,2031,2548],[]),e6 [69,515] [80,191,582,1728,1729,1910,2287,2549,2550,2551],([1,2,7,3,96,4,5,38],([40,80,877]++r 2552 4),[0]),([154,1,2,3,96,4,5,123],[80,652,714,715,744,819,850,2083,2556,2557,2558],[0]),e6 [572,184] [42,80,93,234,2559,2560],([1,177,2,3,146,4,5],[22,234,292,296,516,621,658,659],[0]),u6 [111,59] [80,119,151,156,178,501,525,806,1013,1032,1487],([1,2,96,4,90,5],[22,40,130,187,769,916],[0]),e6 [690] [80,156,1478,2561],([691,1,3,96,4,5],[714,744,774,2562,2563],[]),([0,1,2,3,4,652,59],[80,501,516,2564,2565,2566],[]),u6 [76,18,75] [234,560,561,574,802,2567],u6 [134] [93,156,178,187,191,342,431,501,525,562,700,931,1121],([122,2,3,96,4,123],[42,80,711,714,769,1987],[0]),e6 [467,59] [42,80,166,501,516,525,570,806,810,930,1013,2194,2195,2568],([0,1,2,3,4,436,59],[80,234,525,754,2481,2569,2570,2571],[]),([93,169,0,1,3,184,4],[40,577,578,1584,2021,2078,2572],[0]),u6 [93,181,490] [22,234,666,1091,1477,1563,2167,2573,2574,2575],e6 [79,635] [80,234,495,832,1060,1818,2331,2333,2334,2335,2576],u6 [60,19,59] [42,80,166,587,806,810,839,1103,1202,1203,2284,2285,2577],e6 [488] [80,156,188,516,1870,2578,2579],([441,1,2,3,96,4,5],[80,188,652,714,744,759,769,774,819,1438,2580,2581],[]),e6 [692] [42,80,187,234,342,570,688,1728,1729,2582,2583],([154,6,1,3,96,4,5],[714,715,744,774,819,902,2521,2584,2585,2586],[]),([569,1,2,3,96,4,5],[80,342,744,759,769,819,1671,2587],[]),e6 [181,556] [80,234,495,516,738,1477,1803,2166,2167,2456,2457,2459,2460,2588],([302,154,1,2,3,96,4,5],([80,130,652,709,715,744,759,774,1935]++r 2589 4),[0]),([656,1,2,3,96,4,5],[80,342,652,714,744,774,2281,2593],[]),([1,2,3,96,4,5,635],[80,652,744,759,774,2335,2594,2595,2596],[]),u6 [489] [80,93,156,178,187,516,525,810,1086,2597,2598,2599],u6 [181,307,472] [42,80,234,1027,1477,2167,2464,2600],([93,169,0,18,1,3,4],[22,40,409,564,577,578,1584,2344,2368,2370,2601,2602],[0]),([18,1,2,3,96,4,5],[40,80,188,714,740,741,744,759,769,774,819,933,2423],[]),([138,0,1,2,7,3,5,38],[42,80,516,1074,1615,2603,2604,2605],[0]),e6 [693] [42,178,187,191,342,570,1777,2026,2606,2607,2608],u6 [232,129,59] [80,119,166,688,1196,2609],([1,2,3,96,4,5,623],[80,652,714,744,819,933,2100,2108],[]),([93,18,1,177,2,3,4,5],[22,56,292,296,516,613,621,666,673,682,690,2610,2611,2612],[0]),([372,0,1,2,3,515,5],[80,93,516,1909,2551,2613],[]),([20,0,2,3,5],[35,38],[0]),([526,419,0,1,2,3,5],[80,499,2614,2615],[0]),([302,0,2,3,469,4,5],[42,80,93,234,2616],[0]),e6 [694] [80,156,516,2281,2617,2618,2619],e6 [695,181] [108,234,342,495,516,1477,2163,2167,2356,2464,2620,2621,2622],e6 [696] [80,187,191,234,604,2065,2623,2624],e6 [697] [93,234,495,1561,1582,2625,2626],([1,621,3,96,4,5],[714,744,819,2086,2627],[]),([1,2,3,96,4,5,75],[80,560,652,697,759,799,2406,2407],[]),([302,304,0,2,516,3,4],[80,234,1847,1850,2628,2629],[0]),([304,1,2,3,96,4,309,5],[42,744,774,777,781,786,2394,2630,2631,2632],[0]),([192,18,1,2,3,96,4,5],[40,80,130,495,613,714,744,759,932,2180,2407,2467,2633],[0]),([1,2,96,439,4,5],[22,42,758,759,760,769],[0]),e6 [698] [42,80,234,516,1111,2634,2635,2636],u6 [156,19] [22,80,587,1063,1103,1166,1296,1297,1316,2637,2638],u6 [425,59] [80,166,234,499,535,537,806,810,1013,2639],e6 [419,232] [80,119,178,510,1196,1330,1510,2640],([1,307,3,96,309,5],[42,80,774,819,955,1792,2641],[0]),e6 [699] [80,156,187,188,516,2642,2643],u6 [129,189] [40,42,80,178,570,582,625,1347,2153,2644,2645,2646],u6 [232,18,59] [22,40,80,119,166,409,1510,2647,2648],([1,2,3,146,700,4,5],[22,42,187,1470,2649,2650,2651],[0]),([0,6,7,3,4,5,38],[80,680,964,1738,2652,2653],[0]),([18,1,15,2,3,96,4,5],[40,130,714,759,769,961,1619,2407,2654,2655,2656],[0]),([0,1,2,3,515,5,38],[80,156,516,1478,1909,2657],[]),([0,1,15,3,4,19,16],[22,130,1103,1313,1626,2286,2293,2658],[0]),e6 [625,59] [80,119,424,516,806,1013,2267,2659],e6 [701] [80,93,187,234,424,552,570,1161,2660,2661,2662],([377,18,1,2,3,4,5],[40,188,300,613,759,936,2656],[0]),u6 [69,18] [40,80,156,191,552,568,582,740,1286,1724,1725,2422,2423,2663],([617,0,1,2,3,79,5],[80,234,342,516,1818,2072,2259,2664,2665,2666],[]),([18,1,177,2,3,4,5,59],[22,292,296,464,516,525,620,621,684,1013,2157,2158,2196,2667],[0]),([0,1,2,184,97,4,5],[22,191,234,1289,1418,2078,2668],[]),([531,0,2,7,3,4,5],[22,40,191,234,2062,2603,2669,2670],[]),([302,304,2,3,96,4],[42,80,714,731,759,1847],[0]),([1,2,3,96,4,19,5,16],[40,130,819,948,2415,2671,2672],[0]),([504,1,2,3,4,5,428],[80,130,187,882,1252,1354],[0]),u6 [395] [42,178,191,806,1124,1335,2673],e6 [702] [80,187,191,342,570,1537,1658,2674,2675],([93,1,2,3,96,4,19,5],([130,745,746,774,819,896,2469,2637]++r 2676 4),[0]),([1,2,3,96,476,4,5],[80,652,714,759,774,1267,1822,2680],[0]),u6 [131,47] [22,40,80,93,156,234,1078,1079,1161,1162,1191,1324,1599,2142,2466,2681],([442,1,2,3,96,4,5],[80,342,744,759,769,774,933,1693,2682],[0]),([181,0,2,3,4,309,5,123],[42,80,234,1067,1068,2396,2683,2684],[0]),e6 [703] [80,156,187,188,516,2685,2686],([1,2,3,96,515,4,5],[80,652,714,744,774,819,1910,2687],[]),([302,1,2,3,96,4,5],[80,188,652,714,744,759,774,819,933,2579,2688,2689],[]),([1,2,3,96,4,5,556],[80,652,709,714,759,774,2456,2690,2691],[]),u6 [93,18,59] [22,80,409,495,561,564,598,666,810,1570,2468,2692],e6 [705] ([80]++r 2693 6),([1,15,3,96,4,16],[40,130,769,774,1626,2293],[0]),([1,2,500,96,4,5],[22,40,42,652,714,1477,2699],[0]),e6 [93,477] ([40,80,191,495,1563,1570,1581,2015]++r 2700 6),e6 [706] [42,178,1160,1347,2706],([372,304,1,2,3,96,4,5],[40,80,714,744,781,953,958,1806,2453,2502,2707,2708,2709],[]),([0,18,15,2,3,19,5],[57,130,219,234,998,999,1146],[0]),([1,2,3,96,524,4,5],[80,652,714,759,819,1588,1899,2710],[]),([93,169,1,3,96,4],[40,130,774,819,1584,2344],[0]),e6 [707,436] ([80,191,234,516,754]++r 2711 6),e6 [708] [80,93,156,178,187,516,1784,1857,2717,2718],u6 [212,18] [40,80,156,191,234,495,516,564,580,598,639,656,968,2719],([131,1,15,2,3,96,4,5],[40,130,714,759,819,856,959,961,2465,2720,2721],[0]),u6 [7,90] [22,40,496,516,768,1093,2137,2603,2722,2723],([550,1,2,3,96,4,5],[42,80,342,652,714,744,759,774,819,1610,2724],[]),([549,1,2,3,96,4,5],[80,342,652,714,744,759,774,819,1595,2725,2726],[]),e6 [709] ([80,93,234,1829]++r 2727 5),e6 [93,710] ([22,80,191,495,516,666,1563,1581,2166]++r 2732 4),([545,1,2,3,96,4,5],[342,652,714,744,759,769,774,933,1555,2736],[]),e6 [711] [42,80,178,1658,2737,2738],e6 [712] [80,156,191,516,806,810,2739,2740],e6 [351,458] ([80,93,108,234,516,2147,2478]++r 2741 4),e6 [713] [80,156,187,188,516,1669,2745],([529,1,2,3,96,4,5],[80,188,714,744,759,774,819,1440,2746],[]),([376,358,1,2,3,96],[42,80,130,652,744,1434,1961],[0]),([448,1,2,96,4,5],[22,80,187,714,826,1914,2747],[0]),([0,1,2,481,4,5,59],[80,234,525,570,2748,2749,2750],[]),u6 [79,436] [80,191,234,754,1060,1582,1818,2481,2711,2713,2714,2751],u6 [6,290] [40,80,93,234,497,515,1479,1493,2522,2752,2753,2754],u6 [7,290,59] [80,166,499,501,515,806,1059,2755],e6 [714] ([80,156,178,516]++r 2756 5),u6 [350,146] [22,40,80,234,281,598,659,678,970,1114,2761,2762,2763],u6 [97,19] [22,80,130,587,1063,1288,1418,2414,2764,2765,2766],u6 [131,232,59] [80,166,921,1161,1330,2767],([376,441,1,2,3,96,4,5],[42,80,652,714,759,2580,2768],[]),e6 [590,351] [80,93,108,178,234,2026,2477,2769,2770,2771],([131,69,129,0,2,3,5],[156,171,172,222,315,628,1724,1728,2772],[0]),u6 [295,60] [80,166,178,234,396,457,522,695,806,899,1203,2773,2774],e6 [93,540] ([80,119,191,495,516,666,1563,1570,1574,1575]++r 2775 4),([351,375,3,96,4,5],[40,42,80,714,774,2148,2150,2779],[0]),e6 [715] [22,156,234,516,552,1964,2780,2781,2782],([1,2,3,96,4,5,436],[42,80,652,759,819,917,2481,2711,2783,2784,2785],[]),e6 [716] ([80,156,187,191]++r 2786 4),([376,351,0,1,2,3,79,5],[80,2026,2790,2791],[]),e6 [717] [80,188,516,2792,2793,2794],e6 [617,59] [42,80,166,342,516,570,806,810,1013,2072,2795,2796],e6 [718,436] [80,234,754,2711,2713,2797,2798,2799],e6 [15,689] ([40,42,234,516,1146,1618,1622,2529]++r 2800 6),e6 [101,617] [80,570,604,1669,1670,1713,2072,2806,2807],u6 [498] [22,40,156,178,187,188,191,342,1148,1187,1188,2808,2809],([0,1,2,3,4,436,38],[80,191,234,516,754,2810],[]),([18,177,2,3,19,5],[40,130,219,220,234,464,685],[0]),u6 [18,348,75] [40,329,561,567,697,1001,2811,2812],e6 [7,458] [22,80,93,516,1464,2233,2741,2743,2813,2814,2815],([619,1,2,3,96,4,5],[80,188,652,759,774,819,933,2081,2816],[]),([1,2,3,96,4,309,5,123],[42,80,777,1980,2817,2818],[0]),e6 [719] [80,156,188,516,2819,2820,2821],e6 [181,720] [80,234,1477,2167,2464,2822,2823,2824],([579,1,2,3,96,4,5],[80,342,652,714,759,769,774,812,819,1715,2825,2826,2827],[]),([131,0,1,15,3,4,16],[22,40,869,921,973,1151,1313,1624,1626,2065,2828],[0]),([138,0,6,7,3,4,5],[42,80,191,611,964,1546,1547,2044,2274,2829,2830],[0]),([101,0,6,7,3,4,5],[80,178,611,964,1670,2044,2274,2520,2831],[0]),e6 [721] [42,80,93,178,187,191,570,1845,2832,2833],([351,375,0,3,4,5,59],[40,80,166,795,806,906,2150,2834],[0]),u6 [349,18,75] [40,409,2835,2836]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_8_2 : checkNodesBT W_23 g_23 F_23 P_23_8 A_23 B_23_7 8 N_23_8_2 = true := by decide +kernel
def N_23_8_3 : List NodeSpec := [e6 [722] ([80,93,156,178,187,516,604,756]++r 2837 4),u6 [474] [22,151,831,921,980,981,1187,2841,2842],u6 [370,59] [42,80,166,499,525,806,1013,1682,1683,1684],e6 [590,7] [80,108,1059,1814,2218,2222,2769,2843],e6 [723] [42,178,188,191,2008,2844,2845],u6 [361] [22,734,756,844,1112,1758,2522,2846,2847,2848],u6 [18,70] [22,80,191,234,409,516,568,613,641,739,742,743,1302,2849,2850],e6 [138,436] [22,42,80,191,234,516,754,756,2481,2711,2713,2714,2851],([0,1,2,184,4,90,5],[22,234,496,570,1094,2047,2852,2853],[]),([0,1,2,3,184,37,38],[609,610,793,1976,2008,2031,2854],[0]),e6 [154,537] ([22,80,156,234,516,1412,1785]++r 2855 6),([589,1,2,3,96,4,5],[188,652,714,744,769,774,819,1797,2861],[]),e6 [724] [42,80,178,1478,2862,2863],([0,547,2,3,184,4,5],[234,1557,2008,2031,2428,2864],[]),e6 [79,623] [80,130,1060,2096,2099,2100,2101,2865,2866],u6 [376,181,465] [42,234,738,1477,1533,1537,2867],([376,358,0,1,422,2,3],[22,80,130,516,907,1435,1436,1465,1961,2868,2869,2870],[0]),([0,513,2,3,4,5,59],[40,42,80,166,525,1362,2871],[0]),e6 [725] ([80,156,178,187,342,516,2167]++r 2872 4),e6 [93,689] [40,42,80,234,516,570,666,1570,2529,2530,2800,2805,2876,2877],e6 [376,484] [22,80,93,108,516,1658,2222],e6 [726] ([80,188,516]++r 2878 4),([351,375,0,3,4,5,38],[80,680,906,1478,2779,2882],[0]),u6 [93,18] [22,40,80,156,191,495,666,679,740,1561,1581,2421,2422,2423,2883],e6 [537] [80,156,234,516,2884,2885],([181,0,2,3,727,4,5],[42,80,93,119,234,1477,2886,2887],[]),e6 [728] [80,156,516,1728,2888,2889,2890],e6 [729] [80,93,187,191,342,516,2891,2892,2893],([181,0,1,307,3,309,5],[42,80,191,671,1176,1393,1792,2167,2356,2894,2895,2896],[]),([181,47,0,1,2,4,5],[22,40,93,1079,1191,1242,2167,2897],[]),e6 [730] [42,80,570,1685,2166,2167,2898,2899,2900],([617,1,2,3,96,4,5],[80,342,652,714,759,769,774,819,2072,2901,2902,2903],[]),e6 [731] [80,187,234,342,921,2874,2904,2905,2906],e6 [572,181] [42,80,108,234,2907],e6 [732] [42,80,93,187,191,342,570,2166,2356,2908,2909,2910],([376,358,351,0,1,2,3],[40,42,1435,2026],[0]),e6 [146,16] [22,42,234,281,516,2144,2763,2911,2912],([302,154,0,2,3,184,4,5],[80,1785,2913,2914],[]),e6 [733] ([42,187,342,570,1570]++r 2915 4),([0,1,2,97,4,79,5],[22,516,1289,1418,1582,2919],[]),e6 [181,612] [42,80,108,191,234,1807,2027,2028,2030,2166,2920,2921],e6 [93,146] [22,42,234,516,598,659,678,1581,2468,2763,2922],([154,0,6,1,3,4,5,59],[80,166,499,806,810,1412,1785,2259,2517,2521,2522,2923],[0]),e6 [309,537] [22,80,234,1067,1685,2855,2857,2858,2924,2925,2926],e6 [734] ([80,156,178,187,191,342,424,570,738,1412,2167]++r 2927 4),([1,2,96,576,4,5],[22,80,652,819,2931,2932],[]),u6 [77,75] [40,80,234,409,560,561,854,1306,2933],([0,1,2,72,4,90,5],[22,191,496,516,1094,1768,2934,2935],[]),([376,358,0,1,2,7,3],[22,40,1059,1436,1465,2936],[0]),([101,0,1,2,3,4,75],[80,234,329,516,560,561,847,2937,2938],[]),([181,0,1,15,3,4,16],[22,40,570,869,1151,1313,1624,1626,2167,2464,2939],[0]),([358,0,1,2,431,3,5],[130,516,1053,1059,1777,2428,2940],[0]),e6 [181,476] [80,119,234,516,738,831,1267,1477,1602,1821,1823,2166,2167,2941],e6 [735,428] [80,130,191,234,516,595,1872,1873,2942,2943,2944],([376,358,0,6,1,2,3],[80,907,1434,1436,1961,2259,2945],[0]),([18,2,3,96,19,5],[40,130,212,219,714,759],[0]),e6 [736] [93,156,187,342,495,516,570,666,2356,2946,2947,2948],([303,1,2,3,488,4,5],[42,80,234,1881,1889,1895,2949,2950],[0]),e6 [181,560] [22,93,108,178,234,516,1647,2167,2951,2952],([131,129,2,3,96,5],[40,130,171,714,744,1081],[0]),e6 [737] ([22,178,191,738,1112]++r 2953 4),e6 [376,181] [42,108,234,516,1997,2163,2167,2356,2464,2957,2958,2959],([0,1,2,3,4,75,16],[80,191,234,516,2960,2961,2962],[]),([93,131,129,0,2,3,5],[93,156,171,172,222,315,628,748,1561,1570,2963],[0]),([579,0,2,3,4,5,123],([80,234,516,570,1812]++r 2964 4),[]),([181,534,0,1,2,4,5],[42,80,93,1734,2166,2221,2968,2969,2970],[]),e6 [738] [80,93,108,178,187,191,342,1533,2971,2972,2973],([0,425,2,3,4,5,59],[80,499,525,535,2639],[0]),e6 [376,181,738] [42,738,1533,2972],u6 [131,60,59] [80,166,499,522,525,806,810,921,1161,2417,2418,2974],([376,358,181,0,1,2,3],[42,80,108,516,738,907,1465,2166,2975,2976],[0]),e6 [93,323] [22,42,93,191,1561,1581,2611,2637,2977],e6 [739] [80,93,188,234,1697,2978,2979],([1,177,2,77,3,4,5],[22,56,234,292,724,2980,2981,2982],[0]),([0,1,388,3,4,5,59],[42,80,499,810,1126,2983,2984,2985],[0]),e6 [740] ([80,156,178,187,191,516,604,1670,2132]++r 2986 4),e6 [741] [42,187,191,516,1622,2078,2990,2991],([1,177,2,3,4,5,75],[22,40,234,583,585,620,621,697,1306],[0]),([372,0,122,2,3,4,123],[80,672,711,1249,1807,1984,1988,2992],[0]),u6 [485] [80,156,188,516,2993,2994,2995],u6 [18,15,146] [22,40,42,234,561,658,2654,2996,2997],e6 [742] [80,156,191,1652,1669,2998,2999],([351,1,307,3,96,4,5],[714,744,774,812,819,910,2146,3000,3001,3002],[]),([192,1,177,2,3,4,5],[22,40,188,234,296,464,516,580,620,621,673,3003,3004],[]),([353,18,1,2,3,4,5],[22,56,292,726,3005],[0]),([1,2,3,96,444,4,5],[80,652,759,774,819,1861,1894,3006,3007],[0]),e6 [743] [80,156,188,234,3008,3009,3010],([18,1,177,15,2,3,4,5],[22,56,130,296,613,620,621,988,1146,1618,3011,3012,3013],[0]),([0,6,7,3,37,4,5],[40,611,1179,1758,2044,3014],[0]),e6 [76] [80,93,156,187,191,234,516,574,576,2567],u6 [154,295,59] [80,166,499,501,525,806,899,1785,3015],u6 [77,146] [22,42,281,619,659,854,2981,3016],([0,18,2,77,3,19,5],[40,212,234,279,553,3017,3018],[0]),([456,364,0,2,3,4,5],[80,151,398,806,3019,3020],[0]),e6 [744] [22,93,234,1729,1758,3021,3022,3023],([69,0,18,1,77,3,4,5],[234,409,495,516,551,552,564,854,3024,3025],[0]),([93,0,18,1,77,3,4,5],[40,234,409,516,564,592,619,629,666],[0]),u6 [18,77,59] [409,495,525,564,810,854,3018,3026],([101,0,1,307,3,309,5],[80,671,1176,1393,1670,1792,3027,3028],[]),u6 [101,18,77] [234,409,564,598,604,619,854,2520,3029],([304,0,522,2,3,4,5],[156,234,1060,1552,1789,3030,3031],[]),u6 [18,60,59] [22,80,525,564,810,1126,1202,1203,1206,2157,2158,3032],e6 [252] [80,156,191,561,604,725,2443,2444,2445],([101,351,0,1,307,3,4,5],[178,1309,1652,1669,1670,1812,2026,2146,2147,2520,3033,3034,3035],[]),u6 [350,192] [40,191,234,570,571,599,606,970,1114,2180,3036,3037,3038],([554,0,2,3,184,4,5],[234,342,570,1622,1634,2008,2078,3039,3040],[]),([350,0,18,2,3,19,5],[40,57,213,220,234,605,606,3041],[0]),([93,129,0,1,3,72,4,5],[40,80,688,689,1070,1347,1995,2153,2382,3042],[0]),e6 [302,290] [80,130,234,1479,1493,1571,1824,1825],([0,1,2,146,72,4,5],[22,191,234,281,516,3043,3044,3045],[]),u6 [129,59,62] [42,80,119,501,688,1273,3046,3047,3048],u6 [208,59] [80,166,499,501,806,1013,1019,1076,1077],([0,1,2,146,4,5,59],[22,234,281,501,525,570,1120,2140,3049],[]),([302,1,2,3,369,4,5],[42,80,188,759,1891,3050],[0]),e6 [253] [80,93,156,602,603,2389,2390],e6 [745] [22,93,234,516,1588,3051,3052],e6 [746] [80,187,188,234,342,516,3053,3054,3055],u6 [419,296] ([80,507,2188]++r 3056 6),([0,18,2,3,146,19,5],[40,42,57,212,219,234,279,996],[0]),u6 [93,18,146] [22,40,42,234,598,678,2468,2610,2922],e6 [747] [42,80,93,234,516,1595,3062,3063],([0,122,2,3,4,79,123],[1060,1249,1631,1986,1987,1988,3064],[0]),e6 [704,16] ([22,42,831,1187,2142]++r 3065 4),([376,0,1,2,7,3,79,5],[80,108,516,1059,2222,2790,3069],[]),([0,18,2,3,19,5,75],[40,57,234,279,559,573,733],[0]),([0,18,1,2,3,4,75,59],[80,329,516,525,560,561,570,1344,2545,3070],[0]),u6 [134,59] [166,234,342,431,499,501,525,562,570,700,806,810,931,1013,1121],([101,0,18,1,2,3,4,75],[42,80,234,329,516,560,561,2937],[0]),u6 [76,18] [22,80,93,156,234,409,516,560,564,570,574,576,580,802,2567,3071],e6 [75] [80,561,3072,3073,3074],u6 [69,192,18] [22,40,80,234,409,495,552,561,564,571,2180,3075],u6 [154,364,59] [80,166,528,806,1126,1412,3076],e6 [748] [42,178,187,191,570,1615,1846,3077],u6 [15,477] [40,93,1618,1619,1622,2015,2365,2700,2704,3078,3079],e6 [749] [42,80,187,191,570,1546,1846,3080,3081],u6 [330,59] [40,166,501,525,570,810,1013,1014,1205,3082,3083],([129,0,295,2,3,4,5],[80,119,156,234,396,695,806,864,1339,1342,3084],[0]),([192,0,18,1,2,3,4,59],[22,42,80,495,525,561,598,2180,3085,3086],[0]),e6 [750] [80,93,234,516,1838,3087,3088,3089],u6 [18,156] [22,80,191,234,409,516,564,681,1166,1296,1297,1316,2468,3090],u6 [295,307] [42,80,156,396,516,864,899,1309,1812,3091,3092,3093],e6 [751] [22,156,187,342,516,1728,1791,3094,3095],u6 [324] [80,156,188,3096,3097,3098],([20,0,18,2,3,5],[35,38,40,42,234],[0]),([0,18,2,3,19,5,16],[40,57,219,279,1159,1160,3099],[0]),u6 [442,59] [22,80,166,499,525,1013,1014,1067,1400,1693,3100],([169,0,18,2,3,19,5],[40,93,212,213,220,279,2178,3101],[0]),([0,18,2,3,19,5,59],[57,212,213,279,525,683,806],[0]),([101,0,18,2,3,19,5],[57,93,130,212,213,220,234,279,604,1669,3102],[0]),e6 [752] ([22,80,93,156,187,191,234,516]++r 3103 4),e6 [753] ([80,93,156,178,187,342,564,570]++r 3107 4),([1,2,3,96,37,38],[40,80,744,769,1976,3111],[0]),([93,0,18,1,3,72,4,5],[22,40,80,191,409,495,561,598,679,1070,1300,3112,3113],[0]),([358,351,375,0,3,4,5],[42,93,178,795,1777,2148,2150,2428,3114,3115],[0]),u6 [129,60,59] [42,80,501,688,806,839,1347,3046,3047,3116],u6 [18,217] [40,191,409,552,561,783,1144,1310,3117],u6 [526,295] [42,80,1529,3118],([69,0,18,1,3,4,5,16],[40,80,191,226,409,561,568,582,720,2144,3119,3120],[0]),e6 [754] [80,93,234,1764,1777,3121,3122],u6 [396,59] [166,499,525,806,810,822,823,1013,1168,1169],([376,1,2,3,96,4,5],[80,188,652,714,744,759,774,819,1997,3123],[]),u6 [18,144] [40,561,570,613,661,1106,1146,1285,2364],e6 [755] [108,178,191,1797,3124,3125],u6 [18,97] [22,80,191,234,409,516,561,613,987,1288,1289,1418,2654,2766,3126],u6 [18,259] [40,191,409,597,666,1192,3127],([376,1,422,2,3,96,4,5],[80,130,652,759,2768,3128],[]),e6 [484,38] ([22,80,570,582,680,1478,2969]++r 3129 4),e6 [756] [80,564,3133,3134,3135],([0,122,307,2,3,4,123],[80,1027,1249,1986,3136],[0]),u6 [259] [22,156,187,342,409,495,597,666,1164,1192,1563,3137],u6 [18,189] [22,40,80,93,234,561,582,624,625,2644,3138,3139,3140],([131,129,0,2,3,5,16],[40,315,628,722,831,1081,1160,3141],[0]),u6 [18,59,253] [22,42,525,806,3142,3143],u6 [134,18] [80,93,156,409,431,525,562,564,580,700,931],e6 [757] [80,234,570,921,2126,3144,3145,3146],u6 [134,18,59] [80,234,499,525,561,562,598,700,806],([0,18,295,2,3,4,5,59],[22,80,119,396,457,499,525,695,806,864,1217,3147,3148],[0]),([192,0,18,2,3,19,5],[40,57,93,130,212,213,220,234,279,555,599,3149],[0]),([93,0,1,3,72,4,19,5],[80,495,587,896,1070,1103,1300,2286,2637,3112,3150],[0]),([376,358,69,0,1,2,3],[42,80,1436,1465,1724,3151],[0]),e6 [758] [80,187,188,1347,1857,3152],e6 [759] [80,93,1103,1857,3153,3154],u6 [448,309] [22,80,1061,1067,1917,1933,1980,3155,3156],u6 [164,19] [22,80,1063,1103,1141,1229,3157,3158],([69,0,1,3,4,19,5,16],[80,191,226,568,582,587,720,1103,2286,2415,3120,3159],[0]),([0,6,1,2,3,37,38],[80,609,610,756,793,1974,3111,3160],[0]),([101,0,1,621,3,4,5],[156,1652,1669,2086,2087,2520,3161,3162],[]),([129,0,295,2,3,4,5,59],[42,119,806,1339,1342],[0]),([691,0,1,3,4,5,59],[166,499,806,2562,3163,3164],[]),([101,691,0,1,3,4,5],[156,178,1652,1669,1670,2562,3164,3165,3166],[]),e6 [69,444] [42,80,234,516,1859,1861,1866,1868,3167],([122,1,307,2,3,96,4,5],[22,42,80,652,714,744,759,813,901,910,2125,2138,3168],[0]),([554,0,2,3,4,19,5],[42,234,570,587,3040,3169,3170],[]),([553,0,1,2,3,19,5],[22,130,234,516,587,1630,3171,3172,3173],[]),e6 [760] [42,80,178,187,234,570,3174,3175,3176],([590,0,122,1,2,3,4],[80,93,108,1814,2771,3177,3178],[]),u6 [19,70] [22,80,191,568,587,641,739,742,743,1302,2414,3179,3180],e6 [761] [22,108,130,187,188,191,342,587,1622,3181,3182,3183],e6 [762] ([42,80,178,570]++r 3184 4),e6 [323,16] [22,42,93,178,831,2415,2912,3188,3189,3190]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_8_3 : checkNodesBT W_23 g_23 F_23 P_23_8 A_23 B_23_7 8 N_23_8_3 = true := by decide +kernel
def N_23_8_4 : List NodeSpec := [([93,138,169,0,1,3,4],[22,119,191,577,578,1546,1547,1584,2368,3191,3192],[0]),u6 [140] [22,188,191,377,545,831,949,1103,1117,1160],([304,0,494,2,3,4,5],[178,234,1111,1784,1857,3193,3194],[]),([93,131,169,0,1,3,4],[22,40,577,578,858,921,1161,1584,2370,3195],[0]),e6 [763] [22,156,516,1146,2356,3196,3197,3198],u6 [440] [22,495,587,771,1561,1570,3199],e6 [540,15] [119,151,178,191,1146,1542,1574,1618,1622,2365,2777,3200,3201,3202],e6 [217] [80,156,409,552,570,582,783,1144,1310,1729,3117],u6 [93,19,59] [80,495,587,806,810,896,1103,1570,2286,2637,2692],e6 [652] [80,93,188,234,516,3203,3204],u6 [131,189] [40,80,93,234,570,582,624,625,921,2065,2070,2644,3205],u6 [189,19] [80,582,624,625,1063,1103,2286,3138,3206,3207,3208],e6 [764] [80,1103,2178,3209],u6 [278,59] [166,181,499,648,806,810,838,1013],u6 [18,75,59] [525,559,560,561,2545],([765,323,1,2,3,4,5],[22,42,187,1470,3210,3211,3212],[]),e6 [766] [22,42,93,187,234,1724,2276,3213,3214,3215],u6 [19,59,62] [42,80,166,587,806,810,1103,1273,1488,2156,2284,2285,3216],u6 [232,19,59] [80,166,587,806,1103,1196,1510,2647,3217],e6 [146] [22,42,188,2423,3218],e6 [767] [80,156,178,187,342,1812,3219,3220,3221],u6 [18,15] [22,40,669,740,741,1146,1286,1618,1619,1622,2423,3222],e6 [768] [80,234,516,3223,3224,3225],u6 [18,59] [22,80,166,499,525,740,806,810,1013,1014,1286,2421,2422,2423,3226],e6 [93,704] [22,42,234,1561,2064,3068,3227,3228,3229],e6 [770] ([80,93,187,191,234]++r 3230 4),([93,131,1,2,3,96,4,5],[40,80,714,744,745,746,759,769,856,857,959,2064,2466,3234],[0]),u6 [164,18] [22,40,80,93,178,234,580,598,1141,1229,3235,3236],([131,129,0,2,3,72,5],[171,172,628,1764,1857,3237],[0]),e6 [771] [42,80,187,188,570,1547,3238],([131,129,0,15,2,3,5],[130,171,222,315,628,1081,1622,1623,3239],[0]),e6 [772] ([80,156,516,570,1835,2126]++r 3240 4),([131,169,129,0,2,3,5],[40,171,172,628,2178,2384,3244],[0]),u6 [426,59] [40,80,108,166,501,570,806,810,1013,1126,3245,3246,3247],e6 [773] [22,40,1112,2132,3248,3249,3250],([131,129,0,2,3,5,59],[171,172,315,499,628,806,875],[0]),u6 [164,129] [22,40,42,80,93,516,1141,1347,1350,3251,3252],([131,101,129,0,2,3,5],[156,171,172,222,315,628,1652,1669,3253],[0]),u6 [131,70] [22,80,191,234,568,641,742,743,1161,1302,2466,3254,3255],u6 [471] [22,108,234,342,962,1146,1161,3256,3257],e6 [154,488] [22,80,156,234,516,1412,1870,2543,2590,2949,3258,3259],u6 [131,97] [22,80,191,234,669,987,1161,1289,1418,2065,2466,2720,2766,3260],([131,0,1,2,3,476,5],[80,178,516,831,921,1005,1267,1269,1602,1826,3261],[0]),([534,0,1,2,4,5,59],[42,80,342,499,3262],[]),e6 [774] [80,93,187,234,3263,3264],u6 [131,156] [22,80,93,191,234,681,921,1161,1166,1297,1316,2064,3265],e6 [775] [80,1805,1909,3266],u6 [131,59,62] [80,504,525,806,921,1161,2417,2418,3267],e6 [776] [93,108,234,1629,3268,3269],([1,2,3,96,4,5,769],[80,744,759,959,3270,3271,3272],[]),e6 [500,16] [22,40,1160,1477,2699,3273,3274],u6 [181,428] [22,80,191,234,516,595,738,1027,1477,1696,1872,1873,2943,3275,3276],u6 [93,500] ([22,42,191,495,516,689,1570,2382]++r 3277 4),([69,129,0,1,3,4,5,16],[40,80,226,568,688,1347,2153,3274,3281],[0]),u6 [129,97] [22,80,130,191,516,669,688,987,1289,1418,2120,2766,3282,3283],([181,0,1,2,3,37,38],[42,609,610,1974,1976,2464,3284,3285],[0]),u6 [129,16,59] [42,80,119,570,688,806,1160,2153,3046,3047],e6 [777] [22,130,187,342,424,570,1835,3286,3287,3288],u6 [47,129] [22,40,42,80,93,688,1079,1350,2120,3274,3289],e6 [778] [80,156,187,188,234,342,3290,3291],u6 [129,156] [22,42,80,191,516,681,688,1166,1297,1316,1347,2382,3292],([93,169,129,0,1,3,4],[22,40,578,688,1347,1584,2368,3293],[0]),e6 [779] [80,93,156,178,187,570,1533,2522,3294,3295,3296],u6 [395,59] [166,499,501,525,806,810,1013,1124,1335,1340,2673],u6 [231,129,59] [42,80,589,688,806,1347,3297],u6 [513,59] [42,80,93,166,499,501,525,1013,1362,2871],e6 [375,486] ([22,42,1054,2101]++r 3298 5),e6 [780] [80,187,188,1669,2153,3303],u6 [307,439] [22,42,234,1027,1309,2338,2340,3304,3305,3306],([0,1,2,439,4,79,5],[42,234,516,1631,1818,2124,3307,3308,3309],[]),u6 [7,486] [22,42,2603,3298,3300,3310,3311],([0,1,2,481,4,79,5],[42,80,191,516,1582,3312],[]),([6,7,3,96,4,5],[40,42,80,774,819,2044,2274,2653],[0]),e6 [781] ([42,178,191,2001]++r 3313 4)]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_8_4 : checkNodesBT W_23 g_23 F_23 P_23_8 A_23 B_23_7 8 N_23_8_4 = true := by decide +kernel
def N_23_8 := N_23_8_0 ++ N_23_8_1 ++ N_23_8_2 ++ N_23_8_3 ++ N_23_8_4
def B_23_8 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_8
set_option maxRecDepth 500000 in
lemma B_23_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 8 xs.toFinset) B_23_8 := by
  have hP := buildPoolsSubBT_sound (pdepth := 12) (W := W_23) (raw := r_23) (pspecs := ps_23) (used := U_23_8) S_23_ok
  have hm0 := checkNodesBT_mem (by decide) gp_23 W_23_ok hP A_23_ok B_23_7_ok C_23_8_0
  have hm1 := checkNodesBT_mem (by decide) gp_23 W_23_ok hP A_23_ok B_23_7_ok C_23_8_1
  have hm2 := checkNodesBT_mem (by decide) gp_23 W_23_ok hP A_23_ok B_23_7_ok C_23_8_2
  have hm3 := checkNodesBT_mem (by decide) gp_23 W_23_ok hP A_23_ok B_23_7_ok C_23_8_3
  have hm4 := checkNodesBT_mem (by decide) gp_23 W_23_ok hP A_23_ok B_23_7_ok C_23_8_4
  exact buildBucketsBT_of_mem (forall_append (forall_append (forall_append (forall_append (hm0) hm1) hm2) hm3) hm4)
def U_23_9 : List Nat := ([22,40,42,80,93,108,117,119,130,151,156,166,171,178,187,188,191,212,220,222,234,292,342,409,424,464,495,499,501,516,525,552,559,560,561,564,568,570,580,582,587,598,599,604,606,613,641,652,659,666,669,673,679,680,681,688,689,714,738,740,744,756,759,768,769,774,776,806,810,819,825,831,832,854,896,921,930,933,934,987,1013,1014,1027,1053,1059,1060,1061,1063,1067,1093,1103,1112,1114,1126,1146,1160,1161,1162,1175,1187,1203,1206,1208,1210,1211,1242,1267,1306,1309,1347,1393,1399,1412,1438,1440,1446,1465,1467,1470,1477,1478,1479,1488,1491,1502,1503,1504,1510,1514,1529,1531,1532,1533,1535,1536,1537,1544,1546,1547,1555,1557,1559]++r 1561 4++[1567,1570,1571,1576,1581,1582,1584,1588,1592,1595,1596,1599,1606,1610,1611,1615,1618,1619,1622,1623,1624,1626,1629,1631,1634,1647,1652,1655,1658,1666,1669,1670,1671,1693,1696,1697,1713,1715,1721,1724,1725,1728,1729,1738,1741,1742,1744,1747,1755,1758,1764,1768,1773,1777,1779,1781,1784,1785,1787,1789,1791,1792,1793,1797,1800,1802,1803,1805,1807,1808,1811,1812,1813,1818,1821,1823,1824,1825,1827,1830,1835,1836,1841,1845,1846,1847,1851,1857,1859,1861,1866,1869,1870,1872,1873,1885,1887,1889,1891,1898,1900,1902,1905,1909,1910,1914,1931,1935,1938,1940,1946,1959,1961,1964,1965,1969,1974,1976,1977,1980,1981,1984,1987,1995,2000,2001,2008,2009,2021,2026,2027,2028,2031,2036,2044,2046,2047,2052,2055,2064,2065,2070,2072,2078,2079,2081,2082,2086,2088,2096,2098,2100,2101,2102,2105,2120,2125,2126,2132,2137,2138,2142,2144,2146,2147,2148,2150,2153,2157,2163,2166,2167,2175,2178,2180,2192,2195,2218,2220,2222,2225,2228,2233,2245,2259,2264,2267,2274,2276,2279,2281,2282,2284,2286,2287,2289,2302,2303,2312,2331,2333,2335,2338,2340,2356,2365,2368,2382,2384,2396,2412,2414,2415,2417,2423,2428,2430,2434,2453,2456,2457,2460,2464,2466,2468,2474,2476,2477,2478,2481,2487,2488,2500,2508,2517,2520,2521,2522,2543,2556,2559,2562,2573,2579,2603,2604,2611,2630,2637,2641,2644,2654,2683,2688,2700,2702,2711,2713,2714,2720,2741,2747,2753,2763,2775,2777,2796,2800,2805,2814,2816,2817,2855,2858,2866,2874,2890,2896,2912,2949,2951,2969,2980,3012,3028,3033,3036,3037,3046,3056,3068,3091,3129,3140,3156,3161,3165,3186,3188,3210,3227,3271,3274,3276,3277,3283,3298]++r 3317 271)
def P_23_9 : BT (Option BoundPool) := buildPoolsSubBT 12 W_23 r_23 S_23 ps_23 U_23_9
def N_23_9_0 : List NodeSpec := [u6 [486] [22,42,93,156,178,191,234,570,3298,3317],u6 [547] [93,119,156,178,187,188,191,234,342,570,1557,1721],u6 [376,458] [80,108,342,516,1531,2741],u6 [458] [80,93,108,156,178,191,234,516,1531,2741],u6 [376,445] [40,80,108,178,516,1658,3318,3319],u6 [441] [93,119,156,178,187,191,234,342,516,570,776,1438,1559,1562],u6 [529] [93,119,156,178,187,191,234,342,1440,1564,1567],([0,1,2,3,37,38],[156,570,1974,1976],[0]),u6 [90] [22,93,178,191,234,516,570,768,1093,2137],u6 [531] [93,119,178,187,191,234,342,516,570,1446,1742,3320],e6 [782] [42,80,93,119,156,178,187,188,191,234,516,570,3321,3322],u6 [59,291] [42,80,499,516,806,1014,1504,3323],u6 [290,59] [40,80,151,166,499,501,516,806,1479,1571,3324],u6 [376,59] [80,156,342,499,501,516,570,806,1013,1531,1658,3325],u6 [232,59] [40,80,119,166,191,806,1013,1510,3326],u6 [60,59] [80,178,424,499,806,810,1014,1126,1203,1206,3327],u6 [364,59] [80,151,166,234,499,570,806,810,1013,1126,1502,3328,3329],u6 [456,59] [42,80,93,234,499,525,806,1013,1014,1514,3330],u6 [59,296] [80,151,234,499,806,3056,3331],u6 [295,59] [42,80,119,166,234,499,525,806,1013,1529,1532,1535],([376,138,0,1,2,3,5],[40,80,156,516,570,1531,1615,3332],[]),u6 [138,783] [42,156,516,1546,1547,1615,3333,3334],e6 [138,652] [42,80,516,570,1546,1547,1615,2102,2245,3335],e6 [138,784] [40,42,178,516,2102,3336,3337],u6 [138,506] [22,40,42,234,516,1546,1547,1615,1846,2102,3338,3339],u6 [590] [80,93,108,156,178,187,191,234,342,3340,3341],u6 [522] [93,119,156,178,187,188,191,234,570,1576,3342],u6 [138,169] [22,42,119,156,178,516,1547,1846,1931,2178,2384,3140,3343,3344],u6 [169,79] [42,119,156,191,832,1060,1631,2178,2279,2384,3140,3345],u6 [545] [42,93,156,178,187,188,234,342,516,570,1555,3346],u6 [93,376] [80,156,178,191,516,570,1536,1537,1561,1563,1570,1658,3347],u6 [540] [93,119,178,187,191,234,516,570,2775,2777,3348],u6 [93,59] [80,166,178,499,570,679,806,810,1013,1561,1570,3349],u6 [93,79] [42,80,679,832,1060,1561,1570,1582,1631,2279,3350],([93,169,0,1,3,4],[178,191,1584,2368],[0]),u6 [524] [93,151,178,191,234,516,1588,1898,1900],u6 [476] [93,151,178,191,234,516,1267,1821,1823],u6 [16,38] [42,80,119,178,191,570,831,1160,1478,2912,3351,3352],u6 [231,59] [80,178,424,499,806,810,1013,1126,1208,1210],u6 [47] [22,80,93,156,178,187,188,191,234,342,516,1242,1599],u6 [16,59] [40,80,119,166,191,499,570,806,831,1014,1160,1242,2282],u6 [79,16] [42,80,119,831,832,1060,1160,1242,1582,1631,2866,3353],u6 [15,79] [42,178,669,1060,1582,1622,1623,1631,2866,3354],u6 [553] [93,151,156,178,187,191,234,342,516,570,1629,3355],u6 [97] [22,80,93,156,188,191,234,516,570,669,987],u6 [101,154] [119,156,178,516,1652,1669,1670,1697,1785,1803,1935,2520,3028,3356],u6 [189] [80,93,156,178,234,516,570,582,2644,3140],u6 [18,16] [40,80,93,156,178,191,234,409,516,561,570,613,831,1160,1187,1242,2144,2912,3188,3357],u6 [18,15] [22,191,234,409,516,561,613,669,1146,1618,1619,1622,1623,2365,2654,3012],u6 [526,59] [80,151,156,499,501,516,806,1013,3358,3359],u6 [101,375] [80,93,178,191,1652,1669,2101,2175,3360,3361],u6 [18] [40,93,156,178,187,188,191,234,342,570,740,2423],u6 [652] [42,80,93,178,188,191,234,516,1615,2245,3335],u6 [18,72] [40,80,93,178,191,234,561,598,1764,1857,1995,2126,3362,3363,3364],u6 [138,16] [40,42,80,119,178,516,570,1160,1242,1546,1615,1846,2102,3188,3365],u6 [122,307] [22,80,93,156,234,516,1027,1309,1812,1959,1964,1969,2000,2125,3091,3366],u6 [192,18] [22,40,93,156,234,409,495,561,564,580,598,599,934,2180,3036],u6 [69,18] [80,93,156,178,191,234,409,516,552,561,568,580,598,1724,1725,1728,1729,3367],u6 [18,77] [40,191,234,495,561,854,2980],u6 [556] [80,93,178,234,495,516,1803,2456,2457,2460],u6 [59,62] [40,80,119,166,191,499,806,1014,1211,1488,1491],u6 [181,37] [22,93,156,234,516,570,738,768,1112,1741,1755,1758,1773,2166,2167,2356,3368],u6 [569] [156,187,191,234,342,570,1666,1671],u6 [526] [40,80,93,178,187,191,234,516,1615,3369,3370],u6 [181,169] [22,40,93,178,234,2166,2167,2178,2384,2874,3140],([0,18,2,3,19,5],[93,212,220,234],[0]),u6 [181,15] [22,93,178,191,234,570,669,1146,1618,1622,1623,2166,2356,2464,3276,3371],u6 [181,307] [80,93,156,191,234,516,738,1027,1309,1477,1812,2055,2166,2167,2356,2464,3091,3372],([181,0,2,3,4,5,123],[80,93,234,570,1477,1914,2464,2683],[0]),u6 [138,351] [40,42,178,516,1547,1615,2132,2477,3373,3374],e6 [181,537] [22,42,80,119,234,570,1477,2356,2464,2855,3375],u6 [101,129] [93,156,516,688,689,1347,1652,1669,1670,1697,2153,2520,3376],u6 [59,38] [42,80,499,516,570,806,1014,1478,2969,3377],u6 [579] [93,178,187,191,234,342,516,570,1715,2052,3378],u6 [689] [40,178,191,234,516,570,2800,2805,3379],([1,2,3,96,4,5,16],[40,80,714,744,769,774,819,933,1242,2912],[0]),([351,1,2,3,96,4,5],[40,42,188,714,744,759,769,774,819,2477,3380],[0]),u6 [181,465] [22,42,191,234,1477,2166,2167,2464,3381,3382],([304,1,2,3,96,4,5],[188,714,744,769,774,819,2453,3383],[0]),u6 [641] [22,42,156,178,234,516,570,2474,2476,2477],u6 [302,79] [42,80,156,234,570,832,1060,1582,1631,1835,1841,2279,2866,3384,3385],u6 [350,18] [40,80,93,156,178,234,409,564,580,606,1114,1470,3037,3386],([122,1,2,3,96,4,5],[42,188,714,744,759,769,774,819,2125,2488],[0]),u6 [181,309] [42,93,234,1061,1067,2166,2167,2396,2464,3156,3387],u6 [93,181] [80,191,234,570,666,679,1477,1561,1570,2166,2167,2356,2464,2573],u6 [358,184] [1777,2008,2021,2031,2078,2276,2428,2559,3317,3388],u6 [101,309] [42,178,1061,1067,1652,1669,1670,2396,3156,3389],u6 [184,38] [80,151,570,680,1478,2008,2021,2031,2046,2078,2969,3390],u6 [538] [42,80,93,156,178,187,188,191,516,2008,2009,3391],u6 [69,304] [93,151,178,568,1724,1728,1789,1791,3383,3392],u6 [477] [40,93,178,188,191,516,570,2700,2702],u6 [169,184] [40,93,151,2008,2021,2031,2178,2384,2559,3140,3393],u6 [181,472] [42,93,119,234,495,1477,2167,2356,2464,3394,3395],u6 [358,375] [22,93,130,178,191,2101,2175,2276,2428,3317,3361,3396],u6 [164] [22,80,93,156,178,187,234,516,3397,3398],u6 [550] [42,93,156,178,187,191,234,342,516,1606,1610,1611],u6 [184,309] [42,1067,2008,2021,3156,3399],u6 [375,79] [80,156,832,1060,1582,1631,2101,2175,2279,3361,3400],u6 [623] [80,93,130,156,188,191,516,2096,2098,2100,2101],([351,0,1,307,3,4,5],[93,156,178,191,1309,1812,2026,2146,2147,3033],[0]),u6 [625] [93,191,342,516,570,2264,2267],u6 [628] [22,80,93,156,191,516,570,3361,3401],u6 [376,351] [40,80,93,108,178,234,516,1533,1536,1658,2026,2132,2477,2478,3373,3402],u6 [710] [22,40,178,187,188,191,234,516,570,3403,3404],([358,1,2,3,96,4,5],[42,130,188,714,744,769,774,819,3317,3405],[0]),u6 [653] [80,93,156,178,187,191,342,2508,3406],u6 [419,59] [42,80,166,424,499,516,570,806,810,1013,1503,3407,3408],([351,375,0,3,4,5],[93,178,2148,2150],[0]),u6 [6,38] [80,93,156,178,234,570,680,1478,1738,2259,3129,3352,3409,3410],u6 [431] [93,178,342,516,570,1053,2302],u6 [138,647] [42,191,516,1547,1615,3411,3412],u6 [769] [80,156,178,191,234,3271,3413,3414],([93,1,2,3,96,4,5],[80,188,679,714,744,769,774,819,1581],[0]),u6 [154,59] [80,119,166,191,499,501,570,806,810,1013,1785,1803,1935,1946,3415],u6 [131,15] [22,93,178,191,234,669,1146,1161,1618,1622,1623,2065,2466,2720,3416],u6 [69,123] [80,151,1175,1724,1728,1909,1914,1977,2890,3417],u6 [376,184] [80,108,342,516,570,1531,1536,1658,2008,2021,2031,2047,2078,2559,3418],u6 [181,16] [40,80,119,234,570,831,1160,1187,1242,2166,2167,2356,2464,3188,3276,3419],u6 [295] [42,93,119,156,178,187,191,234,516,1529,1532,1535],u6 [376,7] [40,80,108,516,1059,1536,1658,2218,2222,2603,2814,3420],u6 [154,184] [93,156,191,516,1785,1803,1935,2008,2021,2031,2047,2078,2079,2559,3421],u6 [93,19] [80,156,178,587,896,1063,1103,1561,1570,1581,2286,2637,3422],([18,1,177,2,3,4,5],[40,187,234,292,464,580,613,673,1470],[0]),([0,6,7,3,4,5],[178,191,2044,2274],[0]),([376,358,0,1,2,3],[156,516,1465,1961],[0]),u6 [617] [93,178,187,191,234,342,516,570,2072,2796,3423,3424],u6 [375,37] [22,80,130,156,178,516,768,1741,1755,1758,1773,2101,2175,2412,2500,3361,3425],u6 [6,59] [80,93,166,234,499,525,570,806,810,1013,1014,2259,3426,3427],u6 [181,154] [119,156,178,234,516,738,825,1412,1477,1785,1803,1935,2166,2167,2356,2464,2896,3428],u6 [448] [22,80,93,156,178,187,191,234,342,516,1914,2747],u6 [290] [40,93,151,178,191,234,516,1479,1571,3324],u6 [351,38] [40,42,80,156,191,570,680,1738,2132,3129,3380,3429],([1,2,7,3,96,4,5],[40,130,342,714,744,769,774,2220,2222],[0]),([1,2,3,96,4,309,5],[42,714,744,769,774,2630,3156],[0]),u6 [375,59] [80,151,166,499,806,810,1013,2175,3361,3430],([1,15,2,3,96,4,5],[130,669,714,744,769,819,933,1619],[0]),u6 [302] [42,80,93,119,156,178,187,188,191,234,342,516,570,2579,2688],([6,1,2,3,96,4,5],[42,80,342,714,744,759,769,774,819,933,3410,3427],[0]),u6 [138,15] [22,42,156,178,191,516,570,669,1546,1618,1622,1623,1846,2102,2365,3431],u6 [467] [93,178,191,234,342,516,570,930,2192,2195,3432],([69,0,1,3,4,5,16],[80,178,191,568,570,1242,3433],[0]),u6 [372,304] [22,93,1789,1791,1793,1805,1807,2453,3383,3434,3435,3436],u6 [351,79] [156,191,234,832,1060,1582,1631,1818,2026,2132,2279,2477,3437],([0,1,621,3,4,5],[93,156,191,2086,3161],[0]),u6 [184,16] [40,80,151,831,1160,1242,2008,2021,2031,2046,2078,3438],u6 [358,351] [42,93,178,191,234,1777,2026,2132,3439],u6 [138,7] [40,42,156,516,1059,1547,1615,1846,2218,2222,2233,2603,3440],u6 [500] [22,42,93,178,191,516,570,689,1477,3277],u6 [138,375] [42,80,93,191,516,1546,1615,1846,2101,2175,2412,3361,3441,3442],([375,1,2,3,96,4,5],[80,130,188,714,744,769,774,819,3361,3443],[0]),([1,2,3,96,37,4,5],[40,130,188,714,744,768,769,774,819,1755,1779],[0]),u6 [15,184] [93,151,669,1622,1623,2008,2031,2046,2078,3444],u6 [6,79] [80,156,178,234,756,832,1060,1582,1631,1818,2259,2279,2866,3427,3445],u6 [619] [80,178,187,188,191,234,342,516,2081,2816],u6 [372,184] [80,93,1805,1807,2008,2031,2046,2078,2079,2559,3436,3446],u6 [129,15] [22,130,156,178,191,516,669,688,689,1618,1622,1623,2120,2153,2365,3283,3447],u6 [302,138] [42,80,234,516,570,1544,1546,1547,1615,1825,1835,1841,1845,1846,2102,3385,3448],u6 [18,75] [40,80,234,409,559,560,561,1306,3449],u6 [612] [80,93,108,156,191,234,1807,2027,2028],([1,2,3,96,4,19,5],[130,714,744,769,774,819,896,933,2414],[0]),u6 [589] [40,93,156,178,187,191,342,516,570,1797,2088],u6 [304,79] [156,832,1060,1582,1631,1784,1789,1791,2279,3383,3450],u6 [156] [22,80,93,156,178,191,234,516,679,681],u6 [169,18] [22,40,93,178,234,561,564,580,598,2178,2384,2874,3140,3451,3452,3453],([93,0,1,3,72,4,5],[80,178,191,342,679,1995,3454],[0]),u6 [6,37] [22,80,156,516,756,768,1112,1741,1755,1758,1773,1779,2105,2259,2522,3455],([129,1,2,3,96,4,5],[40,130,188,652,689,714,744,769,774,819,2120],[0]),u6 [101,6] [80,93,234,570,604,756,1652,1669,1670,2228,2259,2520,2753,3427,3456],u6 [436] [80,156,191,234,516,756,2481,2711,2713,2714],([302,181,0,2,3,4,5],[42,80,93,119,234,570,2464,3385,3457],[]),u6 [181,38] [42,80,156,234,570,680,1738,2167,2356,2464,2969,3129,3186,3276,3458],([154,1,2,3,96,4,5],[188,652,714,744,769,774,819,1935,2543,2641],[0]),u6 [488] [42,80,156,178,188,191,234,516,1870,2949,3385,3459],u6 [101,7] [40,570,1059,1652,1669,1670,2218,2222,2603,3460],([1,2,3,96,4,5,38],[42,80,714,744,769,774,819,933,2969,3129,3352],[0]),([154,0,6,1,3,4,5],[93,156,178,191,1412,1785,2259,2517,2521,2522],[0]),u6 [376] [40,80,93,151,156,178,187,191,234,342,516,570,3461],([302,304,0,2,3,4],[93,234,1847,1851],[0]),u6 [372,181] [42,80,156,234,1807,2163,2166,2356,2464,2896,3276,3436,3462],u6 [439] [22,42,156,178,191,234,516,570,2125,2338,2340],u6 [554] [42,156,187,191,234,342,516,570,1634,3463],u6 [358,181] [42,93,156,234,1777,2166,2167,2276,2356,2464,3317,3464],u6 [7,59] [40,80,166,499,570,806,1059,2222,2603,3465],u6 [481] [22,42,80,156,188,191,234,516,570,2434,3427,3466,3467],u6 [123,59] [80,151,234,499,570,806,1909,1914,3468],u6 [184,37] [151,768,1741,1758,1773,2008,2021,2031,2047,2078,3469],([376,0,1,2,3,79,5],[80,108,156,342,516,570,1531,3470],[0]),u6 [302,444] [40,42,80,130,156,234,1813,1824,1835,1861,1866],([1,2,3,96,4,5,123],[80,714,744,769,774,819,1914,2556],[0]),u6 [358,6] [42,93,156,178,234,756,2259,2276,2753,3405,3471],u6 [302,516] [80,130,191,234,1835,1905],u6 [376,441] [80,93,108,151,234,516,1438,1536,1537,1559,1658],u6 [635] [80,156,178,234,495,516,2132,2331,2333,2335],u6 [358,72] [42,119,178,191,1764,1777,1857,1995,2428,3317,3362,3472],u6 [7,37] [22,40,156,178,191,516,570,768,1741,2222,2603,3473],u6 [7,38] [40,80,570,680,1059,1478,2220,2222,2603,2969,3474],u6 [376,181] [80,108,234,516,738,1477,1531,1533,1536,1658,2166,2167,2356,2464,3475],u6 [307,184] [80,178,516,1027,1812,2008,2021,2031,2047,2055,2078,3476],([18,1,2,3,96,4,5],[40,342,598,613,714,744,759,769,774,819,933],[0]),u6 [358,7] [22,130,156,1059,1777,2218,2222,2428,2603,3317,3477]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_9_0 : checkNodesBT W_23 g_23 F_23 P_23_9 A_23 B_23_8 9 N_23_9_0 = true := by decide +kernel
def N_23_9_1 : List NodeSpec := [u6 [375,38] [80,156,680,1478,1738,2175,3129,3443,3478],u6 [302,499] [80,119,130,178,234,424,1470,1813,1835,3479],([0,1,15,3,4,16],[178,570,1624,1626],[0]),u6 [376,6] [80,93,156,191,234,516,756,1533,1536,1537,1658,2259,2522,2753,3319,3480],u6 [154,122] [22,93,119,156,178,234,516,1803,1935,1959,1964,1965,1969,2000,2125,2487,3481,3482],u6 [656] [80,93,156,178,187,342,495,516,2281,3483],u6 [72,123] [40,80,1175,1764,1857,1914,1995,3484],u6 [351,59] [40,42,80,166,499,525,570,806,810,1013,2026,2132,2477,3485],u6 [181,689] [22,40,42,119,156,234,738,1477,2166,2167,2356,2800,3379],([372,1,2,3,96,4,5],[42,80,188,714,744,769,819,933,2641,3436,3486],[0]),u6 [307,59] [80,156,166,178,499,501,516,570,806,810,1027,1812,2055,3487],u6 [101,351] [40,93,178,234,604,1652,1669,1670,2026,2132,2477,2520,3488],u6 [323] [22,42,93,156,178,187,188,191,342,570,896,3210],u6 [376,16] [80,119,156,178,191,516,570,831,1160,1658,3188,3319,3489,3490],u6 [456] [42,80,119,156,178,187,188,191,234,516,2464,3491,3492],([302,0,2,3,184,4,5],[42,80,93,234,342,570,2008,2225,3385],[0]),u6 [372,123] [80,93,1805,1909,1940,1977,2556,2890,3493],([302,1,2,3,96,4,5],[42,80,342,714,744,759,769,774,819,933,1891,3385],[0]),u6 [704] [22,42,156,178,191,234,570,1162,3068,3227],u6 [433] [93,178,187,191,234,342,516,570,1885,1887,2036],u6 [18,59] [80,93,166,234,409,499,501,525,561,564,570,598,806,810,1013,1014,2157],u6 [138,123] [42,80,516,570,1175,1546,1547,1615,1846,1909,1914,1977,2890,3494,3495],u6 [101,18] [93,156,234,409,516,561,564,570,580,598,604,1652,1669,1670,1697,2228,2520,3496],u6 [131,72] [40,80,93,234,921,1162,1764,1857,1995,2065,2126,3362,3497],e6 [785] [40,80,93,178,191,234,516,570,3498,3499],u6 [154,123] [80,93,119,191,570,1175,1785,1803,1909,1914,1935,1940,1977,2890,3495,3500],u6 [72,19] [80,191,896,1103,1764,1857,1995,2286,3364,3501],u6 [69,19] [80,178,191,568,587,896,1063,1103,1724,1725,1728,2286,3502],u6 [75] [80,178,191,234,516,559,560,1306,3449],([691,0,1,3,4,5],[93,156,178,2562,3165],[0]),([131,1,2,3,96,4,5],[188,714,744,759,769,774,819,1162,2466],[0]),u6 [15,19] [22,93,130,178,587,669,896,1619,1623,2286,2414,3503],u6 [19,16] [80,191,587,831,1103,1160,1242,2286,2414,2415,2912,3504],u6 [169,19] [22,93,130,156,191,896,1063,1103,2178,2286,2384,3140,3452,3505],u6 [146] [22,42,178,188,191,234,516,570,598,659,2763],u6 [302,488] [42,80,234,342,1891,2949,3385],u6 [520] [22,42,93,156,178,187,234,342,570,3156,3506],u6 [19,59] [80,166,499,587,806,810,896,1014,1103,2284,2286],u6 [131,69] [80,93,156,234,552,568,1161,1162,1724,1728,2065,3507],u6 [122,72] [40,80,93,178,191,234,1764,1857,1959,1995,2000,2125,2126,3362,3508],u6 [93,123] [80,151,178,570,1561,1570,1909,1977,2890,3509],e6 [302,376] [80,93,156,234,516,570,1533,1658,3319,3510,3511],([131,129,0,2,3,5],[93,156,171,222],[0]),u6 [131,16] [40,80,570,831,921,1160,1161,1187,1242,2065,2142,2466,3188,3512],u6 [93,131] [80,93,156,234,570,666,679,921,1161,1162,1561,1570,2064,2065,3513],u6 [101,307] [80,191,1027,1652,1669,1670,1697,1812,2055,3091,3514],u6 [69,122] [80,93,178,234,552,568,570,1724,1728,1964,2000,2125,3481,3515],u6 [673] [80,93,178,188,191,516,2430,3516,3517],([169,1,2,3,96,4,5],[40,130,188,714,744,769,774,3140,3452],[0]),u6 [129,72] [40,80,178,689,1347,1857,1995,2153,3362,3518],u6 [69,129] [80,93,156,516,568,688,689,1724,1728,1729,2153,3519],u6 [129,16] [40,80,178,570,688,1160,1242,1347,2120,2153,3188,3274,3520],u6 [376,413] [80,108,191,516,3521],u6 [93,129] [80,93,156,516,570,679,688,689,1347,1561,1563,1570,2153,2382,3522],u6 [169,129] [22,40,156,178,516,689,1347,2153,2178,3140,3523],u6 [79,123] [42,80,832,1060,1175,1582,1631,1909,1914,2890,3524],u6 [129,59] [80,166,499,501,570,688,689,806,810,1013,1347,2153,3046],([0,122,2,3,4,123],[93,570,1984,1987],[0]),u6 [376,375] [80,93,156,516,1658,2101,2175,3525],u6 [122,309] [42,93,156,178,191,234,570,1061,1067,1959,2396,3526],u6 [123,38] [80,570,1478,1909,2556,3527],u6 [444] [40,93,178,191,234,516,1859,1861,1866,1869],u6 [131,101] [93,156,234,604,921,1161,1162,1652,1669,1670,2065,2520,3528],u6 [372,122] [42,93,178,234,1807,1964,1965,2000,2488,3481,3529],u6 [122,79] [42,93,156,234,832,1582,1631,1959,1964,2125,2279,3530],u6 [608] [40,93,156,178,187,191,234,342,516,570,2001,3531,3532],u6 [138,122] [42,156,516,570,1546,1547,1615,1959,1964,2125,3481,3533],u6 [494] [42,80,156,178,187,188,234,516,570,1781,3534],u6 [307,123] [80,93,156,178,191,516,570,1175,1812,1909,3535],u6 [560] [93,151,178,234,516,570,1647,2951],u6 [7,79] [832,1059,1060,1631,2222,2603,3536],u6 [309,123] [42,80,1067,1175,1909,1980,2396,2817],u6 [93,38] [42,80,156,178,570,1478,1561,1570,1581,1738,3129,3537],u6 [123,16] [40,80,151,178,191,570,831,1160,1909,2556,3538],u6 [515] [40,93,178,191,516,1910,2287,2289],([376,1,2,3,96,4,5],[40,80,342,652,714,744,769,774,819,1531,3319],[0]),([302,303,1,2,3,4,5],[42,80,119,187,234,1470,1825,1889,1891,2082,3539],[0]),u6 [304,307] [22,156,178,516,1027,1784,1787,1789,1791,1811,1812,2055,3091,3383,3540],u6 [69,38] [42,80,1478,1724,1725,1728,1738,2969,3129,3541],u6 [302,518] [42,80,130,234,516,1813,1835,1902,3542],u6 [534] [42,80,93,156,178,187,188,191,234,342,516,1467,2969,3543],u6 [93,184] [80,151,191,342,679,1561,1570,2008,2021,2031,2078,2559,3544],u6 [302,72] [40,80,178,234,1764,1835,1857,1995,2126,3362,3364,3385,3545],u6 [131,59] [80,166,499,525,570,806,810,921,1013,1161,1162,2065,2417],u6 [302,69] [80,93,191,234,552,568,1724,1725,1728,1813,1841,2312,3385,3546],e6 [181,786] [22,80,119,178,191,234,424,1477,2166,2167,2356,3547,3548],u6 [302,307] [80,93,156,191,234,516,1027,1309,1812,1813,1835,2138,3091,3549],u6 [302,309] [42,80,178,234,1061,1067,1835,2396,2630,3550],([138,0,1,2,3,5,38],[42,80,156,516,570,1615,2604,2969],[0]),u6 [351,37] [22,40,93,156,234,516,768,1112,1741,1755,1758,1773,2132,3551,3552],u6 [302,372] [80,93,156,234,1805,1807,1808,1813,1825,1891,1938,3486,3553],u6 [302,154] [80,119,130,156,178,234,516,825,1785,1803,1813,1824,1835,1841,1935,1938,2543,3385,3554],u6 [302,16] [40,80,93,178,191,234,570,831,1160,1187,1813,1891,2912,3188,3555],u6 [595] [93,151,191,234,516,570,1836,3556],u6 [302,59] [80,93,234,342,499,525,570,806,1013,1014,1813,3385,3557],u6 [101,19] [156,587,896,1063,1103,1652,1669,1670,2228,2286,2520,3558],u6 [302,38] [80,93,156,234,570,1813,1891,3129,3352,3559],u6 [131,169] [22,40,93,178,234,921,1162,2065,2070,2178,2384,2874,3140,3560],u6 [427] [22,93,156,178,191,516,570,1477,1800,3383],u6 [428] [80,93,188,191,234,516,1027,1696,1872,1873],u6 [138,6] [42,80,156,191,516,756,1546,1615,2102,2753,3427,3561],u6 [484] [22,93,156,178,187,342,516,570,582,2222,3562],u6 [304,72] [40,151,178,191,1764,1784,1789,1857,1995,3362,3383,3563],u6 [376,422] [80,108,234,516,1531,1536,1537,1655,1658,3564],u6 [70] [22,80,93,156,188,191,234,516,568,641,3565],([1,307,2,3,96,4,5],[80,652,714,744,769,774,819,2055,2138],[0]),u6 [154,304] [22,156,178,191,516,1784,1785,1787,1789,1791,1793,1802,1803,1935,3383,3566],u6 [304,309] [22,156,178,1061,1067,1784,1789,2396,3156,3383,3567],u6 [442] [156,178,187,188,234,342,570,1399,1693],u6 [138,304] [42,93,156,516,570,1546,1547,1615,1784,1787,1789,1791,1846,3383,3434,3568],u6 [93,138] [42,80,191,516,570,679,1546,1547,1561,1563,1570,1615,1846,2303],u6 [429] [80,93,151,178,234,516,570,1981,3569],u6 [181,490] [22,119,234,516,1477,2166,2167,2356,3276,3570,3571],u6 [72,37] [80,119,156,191,516,768,1741,1764,1768,1773,1857,1995,3572],u6 [72,38] [80,119,680,1764,1857,2969,3364,3573],u6 [376,72] [80,119,178,516,1531,1536,1764,1768,1857,1995,3362,3574],u6 [583] [42,156,187,191,234,516,570,1744,1747],u6 [376,123] [80,156,234,516,570,1658,1977,3575],u6 [69,37] [80,156,178,516,568,768,1724,1728,1729,1741,1755,1758,3576],u6 [376,69] [80,156,191,516,568,1531,1537,1658,1724,1728,1729,3577],u6 [537] [22,80,156,178,191,234,516,2464,2855,2858,3375],u6 [358,69] [42,156,178,568,1724,1728,2276,2428,3317,3578],u6 [576] [22,80,93,191,234,516,570,2055,3579,3580],([0,1,307,3,309,5],[117,178,191,1393,1792],[0]),u6 [138,540] [22,40,42,93,151,234,516,1546,1547,1846,2775,3348],u6 [302,93] [80,93,178,191,234,570,666,1561,1570,1581,1813,1835,1841,2611,3581],u6 [309,59] [42,80,166,499,806,1067,2396,3156,3582],u6 [93,18] [80,93,156,178,191,234,409,516,561,564,570,580,598,666,679,1561,1563,1570,1581,2468,3583],u6 [572] [80,93,108,156,178,187,234,342,3584],u6 [549] [42,93,156,178,187,191,234,342,516,1592,1595,1596],u6 [566] [22,42,80,93,156,188,191,234,570,3436,3585],u6 [372,59] [42,80,499,806,810,1013,1014,1805,1946,3436,3586],u6 [372,101] [80,156,1652,1669,1713,1805,1807,2228,2520,3028,3436,3587],u6 [18,146] [22,40,42,234,409,561,598,613,659],u6 [558] [22,93,178,234,516,570,582,1827,1830,1935]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_9_1 : checkNodesBT W_23 g_23 F_23 P_23_9 A_23 B_23_8 9 N_23_9_1 = true := by decide +kernel
def N_23_9 := N_23_9_0 ++ N_23_9_1
def B_23_9 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_9
set_option maxRecDepth 500000 in
lemma B_23_9_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 9 xs.toFinset) B_23_9 := by
  have hP := buildPoolsSubBT_sound (pdepth := 12) (W := W_23) (raw := r_23) (pspecs := ps_23) (used := U_23_9) S_23_ok
  have hm0 := checkNodesBT_mem (by decide) gp_23 W_23_ok hP A_23_ok B_23_8_ok C_23_9_0
  have hm1 := checkNodesBT_mem (by decide) gp_23 W_23_ok hP A_23_ok B_23_8_ok C_23_9_1
  exact buildBucketsBT_of_mem (forall_append (hm0) hm1)
def U_23_10 : List Nat := [93,117,156,178,187,188,191,234,342,516,570,580,598,669,679,689,768,825,896,1013,1061,1063,1162,1242,1324,1350,1531,1544,1618,1713,1755,1808,1825,1914,1935,1977,2055,2125,2163,2218,2222,2279,2312,2477,2559,2611,2753,2969,3091,3129,3140,3156,3188,3317,3343,3361,3362,3373,3383,3385,3427,3434,3436,3441,3481,3510,3588]
def P_23_10 : BT (Option BoundPool) := buildPoolsSubBT 12 W_23 r_23 S_23 ps_23 U_23_10
def N_23_10 : List NodeSpec := [u6 [376] [93,156,178,187,191,342,516,570,1531,3510],u6 [37] [93,156,178,191,516,570,768,1755],u6 [123] [93,156,178,191,570,1914,1977],u6 [18] [93,156,178,187,188,191,234,342,516,570,580,598],u6 [19] [93,156,178,188,191,570,896,1063],u6 [38] [93,156,178,188,191,570,2969,3129],u6 [122] [93,156,178,187,191,234,342,570,2125,3481],u6 [375] [93,156,178,187,191,342,570,3361,3441],u6 [131] [93,156,178,187,191,234,342,570,1162,1324],u6 [302] [93,156,178,187,188,191,234,342,570,1825,3385],u6 [372] [93,117,156,187,188,191,342,570,1808,3436],u6 [184] [93,156,178,191,342,570,2559],u6 [351] [93,156,178,187,191,234,342,570,2477,3373],u6 [181] [93,156,178,187,191,234,342,570,2163],u6 [6] [93,156,178,187,188,191,234,342,570,2753,3427],([1,2,3,96,4,5],[188,342],[0]),u6 [304] [93,156,178,187,191,342,570,3383,3434],u6 [72] [93,156,178,342,570,3362],u6 [309] [93,156,178,570,1061,3156],u6 [154] [93,117,156,178,187,191,342,516,570,825,1935],u6 [15] [93,156,188,191,570,669,1618],u6 [7] [93,156,178,342,570,2218,2222],u6 [16] [93,156,178,188,191,570,1242,3188],u6 [79] [93,156,178,191,342,570,2279],u6 [93] [93,156,178,187,191,342,570,679,2611],u6 [169] [93,156,178,187,342,570,3140,3343],u6 [358] [93,156,178,187,191,342,570,3317,3588],u6 [138] [93,156,178,187,191,342,516,570,1544],u6 [69] [93,156,187,191,342,570,2312],u6 [129] [93,156,178,187,191,342,516,570,689,1350],u6 [307] [93,156,178,191,516,570,2055,3091],u6 [59] [93,156,178,191,342,570,1013],u6 [101] [93,156,178,187,191,342,570,1713]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_10 : checkNodesBT W_23 g_23 F_23 P_23_10 A_23 B_23_9 10 N_23_10 = true := by decide +kernel
def B_23_10 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_10
set_option maxRecDepth 500000 in
lemma B_23_10_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 10 xs.toFinset) B_23_10 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound S_23_ok) A_23_ok B_23_9_ok C_23_10
def U_23_11 : List Nat := [187,342]
def P_23_11 : BT (Option BoundPool) := buildPoolsSubBT 12 W_23 r_23 S_23 ps_23 U_23_11
def N_23_11 : List NodeSpec := [u6 [] [187,342]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_11 : checkNodesBT W_23 g_23 F_23 P_23_11 A_23 B_23_10 11 N_23_11 = true := by decide +kernel
def B_23_11 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_11
set_option maxRecDepth 500000 in
lemma B_23_11_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 11 xs.toFinset) B_23_11 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound S_23_ok) A_23_ok B_23_10_ok C_23_11
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_23_ok : forestRootCheck r_23 g_23 [(VAR 0,20,21),(VAR 1,12,14),(VAR 2,10,14),(VAR 3,6,14),(VAR 4,5,21),(VAR 5,3,35)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_23_in : bucketContainsBT B_23_11 r_23 = true := by decide +kernel
lemma low_23 : Lower r_23 g_23 12 := lower_of_forestBT root_23_ok B_23_11_ok root_23_in

def g_orig := (d 0xfeeaeac8fee8ea80)
set_option maxHeartbeats 0 in
lemma low_orig : Lower (varsOf 63) g_orig 12 := carry_of (swaps := [(0,5),(1,4)]) (by decide +kernel) low_23
def targetFn (x : Fin 6 → Bool) : Bool := Nat.testBit (4276808392 * 2 ^ 32 + 4276677248) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def temoin : List Gate := [⟨.or,[2,1]⟩,⟨.and,[1,2]⟩,⟨.or,[1,4]⟩,⟨.and,[7,0]⟩,⟨.and,[4,6]⟩,⟨.or,[0,7]⟩,⟨.or,[9,3]⟩,⟨.and,[5,8]⟩,⟨.or,[11,12]⟩,⟨.or,[12,13]⟩,⟨.and,[10,14]⟩,⟨.and,[15,11]⟩,⟨.or,[16,17]⟩]
lemma temoin_ok : PEqualNP.MetaComplexity.Monotone2 ⟨temoin, 18⟩ := by
  intro g hg; simp [temoin] at hg; rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxHeartbeats 0 in
lemma tgt_eq_G : ∀ r : Row, targetFn (evalInput6 r) = g_orig.testBit r.val := by decide +kernel
set_option maxHeartbeats 0 in
lemma temoin_eval : ∀ r : Row, Circuit.eval ⟨temoin, 18⟩ (List.ofFn (evalInput6 r)) = g_orig.testBit r.val := by decide +kernel

end PEqualNP.Outside.L_meta_45560

open PEqualNP.Outside.L_meta_45560 in
theorem PEqualNP.Outside.L_meta_45560 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808392 * 2 ^ 32 + 4276677248) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808392 * 2 ^ 32 + 4276677248) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  exact replace_of_lower6 g_orig (by decide) (by decide) (by decide) 12 low_orig temoin 18 (by decide) temoin_ok targetFn tgt_eq_G temoin_eval
