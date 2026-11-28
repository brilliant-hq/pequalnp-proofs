import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_45476
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
def g_1 := (d 0xe880e880e880e880)
def r_1 : List Nat := varsOf 15
def p_1 : List Nat := [7,7,7,11,11,11,13,13,13,14,14,14]
def q_1 : List Nat := [6,5,3,10,9,3,12,9,5,12,10,6]
def F_1 : Nat := fullMask 12
set_option maxHeartbeats 0 in
lemma gp_1 : goodPairs g_1 p_1 q_1 := goodPairs_of (by decide +kernel)
def W_1 : BT Decor := buildWiresBT 4 (mkBase p_1 q_1 r_1) [(0,0,1),(0,0,2),(0,1,2),(0,6,3),(3,7,0),(0,2,3),(3,9,0),(0,4,2)]
lemma W_1_ok : btAll (fun x => faithful p_1 q_1 x ∧ x.1 < 2^256) W_1 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_1 : List (List (Nat × Nat)) := [[],[(2,3)],[(1,2)],[(1,2),(2,3)],[(0,1)],[(0,1),(2,3)],[(0,2),(1,2)],[(0,2),(1,2),(2,3)],[(0,2),(1,3)],[(0,1),(1,2),(2,3)],[(0,2),(1,3),(2,3)]]
def A_1 : BT (List (Nat × Nat)) := btOfList 4 al_1
set_option maxHeartbeats 0 in
lemma A_1_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_1 = g_1) A_1 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_1_0 : Slice r_1 g_1 (subcubeFast 0 1) 4 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_1_1 : Slice r_1 g_1 (subcubeFast 0 2) 4 := by
  have hc : Lower (varsOf 13) (d 0xfaa0faa0faa0faa0) 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_1_2 : Slice r_1 g_1 (subcubeFast 0 4) 4 := by
  have hc : Lower (varsOf 11) (d 0xee88ee88ee88ee88) 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_1_3 : Slice r_1 g_1 (subcubeFast 0 8) 4 := by
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) low_0
def S_1 : BT (Option (Nat × Nat)) := btOfList 2 [some (subcubeFast 0 1,4),some (subcubeFast 0 2,4),some (subcubeFast 0 4,4),some (subcubeFast 0 8,4)]
lemma S_1_ok : btAll (fun o => ∀ p, o = some p → Slice r_1 g_1 p.1 p.2) S_1 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_1_0) (forall_cons (fun _ h => by cases h; exact sl_1_1) (forall_cons (fun _ h => by cases h; exact sl_1_2) (forall_cons (fun _ h => by cases h; exact sl_1_3) (fun _ h => (List.not_mem_nil h).elim)))))
def ps_1 : BT (Option PoolSpec) := btOfList 2 [q 1 [],q 0 [],q 2 [],q 3 []]
def B_1_2 : BT (List (List Nat)) := BT.empty
lemma B_1_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_1 2 xs.toFinset) B_1_2 := .empty
def U_1_3 : List Nat := [0,1]
def P_1_3 : BT (Option BoundPool) := buildPoolsSubBT 2 W_1 r_1 S_1 ps_1 U_1_3
def N_1_3 : List NodeSpec := [([4,5,6,3],[0,1],[]),([8,1,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_1_3 : checkNodesBT W_1 g_1 F_1 P_1_3 A_1 B_1_2 3 N_1_3 = true := by decide +kernel
def B_1_3 : BT (List (List Nat)) := buildBucketsBT W_1 N_1_3
set_option maxRecDepth 500000 in
lemma B_1_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_1 3 xs.toFinset) B_1_3 :=
  buildBucketsBT_sound (by decide) gp_1 W_1_ok (buildPoolsSubBT_sound S_1_ok) A_1_ok B_1_2_ok C_1_3
def U_1_4 : List Nat := [0,2,3]
def P_1_4 : BT (Option BoundPool) := buildPoolsSubBT 2 W_1 r_1 S_1 ps_1 U_1_4
def N_1_4 : List NodeSpec := [([4,5,1,2,3],[0,2],[0]),([10,0,1,2,3],[],[]),([11,0,1,2,3],[3],[9])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_1_4 : checkNodesBT W_1 g_1 F_1 P_1_4 A_1 B_1_3 4 N_1_4 = true := by decide +kernel
def B_1_4 : BT (List (List Nat)) := buildBucketsBT W_1 N_1_4
set_option maxRecDepth 500000 in
lemma B_1_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_1 4 xs.toFinset) B_1_4 :=
  buildBucketsBT_sound (by decide) gp_1 W_1_ok (buildPoolsSubBT_sound S_1_ok) A_1_ok B_1_3_ok C_1_4
def U_1_5 : List Nat := (r 0 4)
def P_1_5 : BT (Option BoundPool) := buildPoolsSubBT 2 W_1 r_1 S_1 ps_1 U_1_5
def N_1_5 : List NodeSpec := [([4,0,1,2,3],(r 0 4),[0,1,4,5,8,10])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_1_5 : checkNodesBT W_1 g_1 F_1 P_1_5 A_1 B_1_4 5 N_1_5 = true := by decide +kernel
def B_1_5 : BT (List (List Nat)) := buildBucketsBT W_1 N_1_5
set_option maxRecDepth 500000 in
lemma B_1_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_1 5 xs.toFinset) B_1_5 :=
  buildBucketsBT_sound (by decide) gp_1 W_1_ok (buildPoolsSubBT_sound S_1_ok) A_1_ok B_1_4_ok C_1_5
def U_1_6 : List Nat := (r 0 4)
def P_1_6 : BT (Option BoundPool) := buildPoolsSubBT 2 W_1 r_1 S_1 ps_1 U_1_6
def N_1_6 : List NodeSpec := [([0,1,2,3],(r 0 4),[0,2,3,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_1_6 : checkNodesBT W_1 g_1 F_1 P_1_6 A_1 B_1_5 6 N_1_6 = true := by decide +kernel
def B_1_6 : BT (List (List Nat)) := buildBucketsBT W_1 N_1_6
set_option maxRecDepth 500000 in
lemma B_1_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_1 6 xs.toFinset) B_1_6 :=
  buildBucketsBT_sound (by decide) gp_1 W_1_ok (buildPoolsSubBT_sound S_1_ok) A_1_ok B_1_5_ok C_1_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_1_ok : forestRootCheck r_1 g_1 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_1_in : bucketContainsBT B_1_6 r_1 = true := by decide +kernel
lemma low_1 : Lower r_1 g_1 7 := lower_of_forestBT root_1_ok B_1_6_ok root_1_in
def g_2 := (d 0xfe80fe80fe80fe80)
def r_2 : List Nat := varsOf 15
def p_2 : List Nat := [7,7,7,9,9,10,10,11,12,12,13,14]
def q_2 : List Nat := [6,5,3,8,1,8,2,3,8,4,5,6]
def F_2 : Nat := fullMask 12
set_option maxHeartbeats 0 in
lemma gp_2 : goodPairs g_2 p_2 q_2 := goodPairs_of (by decide +kernel)
def W_2 : BT Decor := buildWiresBT 5 (mkBase p_2 q_2 r_2) [(0,2,3),(1,2,3),(3,4,5),(0,1,2),(1,1,2),(3,7,8),(2,0,3),(3,0,3),(1,0,3),(3,2,12),(1,1,3),(0,0,14),(0,0,3),(1,16,2),(3,4,0),(2,0,2),(3,0,2),(2,2,1),(3,21,0),(2,0,1),(1,23,2),(0,0,1),(1,0,1),(3,2,3)]
lemma W_2_ok : btAll (fun x => faithful p_2 q_2 x ∧ x.1 < 2^256) W_2 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_2 : List (List (Nat × Nat)) := [[],[(1,2)],[(0,1)],[(0,2),(1,2)],[(0,1),(1,2)],[(0,2)]]
def A_2 : BT (List (Nat × Nat)) := btOfList 3 al_2
set_option maxHeartbeats 0 in
lemma A_2_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_2 = g_2) A_2 := btAll_ofList (autos_of (by decide +kernel))
def S_2 : BT (Option (Nat × Nat)) := btOfList 1 []
lemma S_2_ok : btAll (fun o => ∀ p, o = some p → Slice r_2 g_2 p.1 p.2) S_2 := btAll_ofList (fun _ h => (List.not_mem_nil h).elim)
def ps_2 : BT (Option PoolSpec) := btOfList 1 []
def B_2_1 : BT (List (List Nat)) := BT.empty
lemma B_2_1_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 1 xs.toFinset) B_2_1 := .empty
def U_2_2 : List Nat := []
def P_2_2 : BT (Option BoundPool) := buildPoolsSubBT 1 W_2 r_2 S_2 ps_2 U_2_2
def N_2_2 : List NodeSpec := [([6,0,1],[],[]),([9,0,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_2_2 : checkNodesBT W_2 g_2 F_2 P_2_2 A_2 B_2_1 2 N_2_2 = true := by decide +kernel
def B_2_2 : BT (List (List Nat)) := buildBucketsBT W_2 N_2_2
set_option maxRecDepth 500000 in
lemma B_2_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 2 xs.toFinset) B_2_2 :=
  buildBucketsBT_sound (by decide) gp_2 W_2_ok (buildPoolsSubBT_sound S_2_ok) A_2_ok B_2_1_ok C_2_2
def U_2_3 : List Nat := []
def P_2_3 : BT (Option BoundPool) := buildPoolsSubBT 1 W_2 r_2 S_2 ps_2 U_2_3
def N_2_3 : List NodeSpec := [([10,11,1,2],[],[3]),([13,0,1,3],[],[]),([15,1,2,3],[],[]),([16,1,2,12],[],[3]),([0,1,17,3],[],[]),([18,1,2,3],[],[]),([19,20,1,3],[],[2]),([22,1,2,3],[],[]),([0,1,24,3],[],[]),([25,26,2,3],[],[4])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_2_3 : checkNodesBT W_2 g_2 F_2 P_2_3 A_2 B_2_2 3 N_2_3 = true := by decide +kernel
def B_2_3 : BT (List (List Nat)) := buildBucketsBT W_2 N_2_3
set_option maxRecDepth 500000 in
lemma B_2_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 3 xs.toFinset) B_2_3 :=
  buildBucketsBT_sound (by decide) gp_2 W_2_ok (buildPoolsSubBT_sound S_2_ok) A_2_ok B_2_2_ok C_2_3
def U_2_4 : List Nat := []
def P_2_4 : BT (Option BoundPool) := buildPoolsSubBT 1 W_2 r_2 S_2 ps_2 U_2_4
def N_2_4 : List NodeSpec := [([27,0,1,2,3],[],[4]),([10,0,1,2,3],[],[0]),([0,1,2,3,12],[],[0,1,2,4]),([16,0,1,2,3],[],[0,1,3,5]),([19,0,1,2,3],[],[0,1,3]),([0,1,26,2,3],[],[0]),([25,0,1,2,3],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_2_4 : checkNodesBT W_2 g_2 F_2 P_2_4 A_2 B_2_3 4 N_2_4 = true := by decide +kernel
def B_2_4 : BT (List (List Nat)) := buildBucketsBT W_2 N_2_4
set_option maxRecDepth 500000 in
lemma B_2_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 4 xs.toFinset) B_2_4 :=
  buildBucketsBT_sound (by decide) gp_2 W_2_ok (buildPoolsSubBT_sound S_2_ok) A_2_ok B_2_3_ok C_2_4
def U_2_5 : List Nat := []
def P_2_5 : BT (Option BoundPool) := buildPoolsSubBT 1 W_2 r_2 S_2 ps_2 U_2_5
def N_2_5 : List NodeSpec := [([0,1,2,3],[],[0,1,2,3,4,5])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_2_5 : checkNodesBT W_2 g_2 F_2 P_2_5 A_2 B_2_4 5 N_2_5 = true := by decide +kernel
def B_2_5 : BT (List (List Nat)) := buildBucketsBT W_2 N_2_5
set_option maxRecDepth 500000 in
lemma B_2_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 5 xs.toFinset) B_2_5 :=
  buildBucketsBT_sound (by decide) gp_2 W_2_ok (buildPoolsSubBT_sound S_2_ok) A_2_ok B_2_4_ok C_2_5
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_2_ok : forestRootCheck r_2 g_2 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,1,9)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_2_in : bucketContainsBT B_2_5 r_2 = true := by decide +kernel
lemma low_2 : Lower r_2 g_2 6 := lower_of_forestBT root_2_ok B_2_5_ok root_2_in
def g_3 := (d 0xffe8ffe8ffe8ffe8)
def r_3 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_3 : Lower r_3 g_3 5 := by
  exact lift_of_f (z := 8) (o := 0) (other := r_0) (G := g_0) (essPairs := [(VAR 3,0,8)]) (by decide +kernel) low_0
def g_4 := (d 0xfffee880fffee880)
def r_4 : List Nat := varsOf 31
def p_4 : List Nat := [7,7,7,11,11,11,13,13,13,14,14,14,17,17,18,18,19,20,20,21,22,24,24,25,26,28]
def q_4 : List Nat := [6,5,3,10,9,3,12,9,5,12,10,6,16,1,16,2,3,16,4,5,6,16,8,9,10,12]
def F_4 : Nat := fullMask 26
set_option maxHeartbeats 0 in
lemma gp_4 : goodPairs g_4 p_4 q_4 := goodPairs_of (by decide +kernel)
def W_4 : BT Decor := buildWiresBT 3 (mkBase p_4 q_4 r_4) [(1,0,1),(1,2,3),(0,5,6)]
lemma W_4_ok : btAll (fun x => faithful p_4 q_4 x ∧ x.1 < 2^256) W_4 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_4 : List (List (Nat × Nat)) := [[],[(1,2)],[(1,2),(2,3)],[(0,2),(1,2)],[(0,2),(1,2),(2,3)],[(0,2),(1,3)]]
def A_4 : BT (List (Nat × Nat)) := btOfList 3 al_4
set_option maxHeartbeats 0 in
lemma A_4_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_4 = g_4) A_4 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_4_0 : Slice r_4 g_4 (subcubeFast 16 0) 7 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_1
set_option maxHeartbeats 0 in
lemma sl_4_1 : Slice r_4 g_4 (subcubeFast 2 0) 6 := by
  have hc : Lower (varsOf 29) (d 0xfffaa000fffaa000) 6 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_4_2 : Slice r_4 g_4 (subcubeFast 4 0) 6 := by
  have hc : Lower (varsOf 27) (d 0xffee8800ffee8800) 6 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_4_3 : Slice r_4 g_4 (subcubeFast 8 0) 6 := by
  have hc : Lower (varsOf 23) (d 0xfefe8080fefe8080) 6 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_4_4 : Slice r_4 g_4 (subcubeFast 1 0) 6 := by
  have hc : Lower (varsOf 30) (d 0xfffcc000fffcc000) 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_4_5 : Slice r_4 g_4 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) (d 0xfffffcc0fffffcc0) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_4_6 : Slice r_4 g_4 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffffaa0fffffaa0) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_4_7 : Slice r_4 g_4 (subcubeFast 0 4) 5 := by
  have hc : Lower (varsOf 27) (d 0xffffee88ffffee88) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_4_8 : Slice r_4 g_4 (subcubeFast 0 8) 5 := by
  have hc : Lower (varsOf 23) (d 0xffffe8e8ffffe8e8) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
def S_4 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 16 0,7),some (subcubeFast 2 0,6),some (subcubeFast 4 0,6),some (subcubeFast 8 0,6),some (subcubeFast 1 0,6),some (subcubeFast 0 1,5),some (subcubeFast 0 2,5),some (subcubeFast 0 4,5),some (subcubeFast 0 8,5)]
lemma S_4_ok : btAll (fun o => ∀ p, o = some p → Slice r_4 g_4 p.1 p.2) S_4 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_4_0) (forall_cons (fun _ h => by cases h; exact sl_4_1) (forall_cons (fun _ h => by cases h; exact sl_4_2) (forall_cons (fun _ h => by cases h; exact sl_4_3) (forall_cons (fun _ h => by cases h; exact sl_4_4) (forall_cons (fun _ h => by cases h; exact sl_4_5) (forall_cons (fun _ h => by cases h; exact sl_4_6) (forall_cons (fun _ h => by cases h; exact sl_4_7) (forall_cons (fun _ h => by cases h; exact sl_4_8) (fun _ h => (List.not_mem_nil h).elim))))))))))
def ps_4 : BT (Option PoolSpec) := btOfList 4 [q 1 [12297],q 4 [],q 5 [],q 6 [],q 2 [],q 7 [],q 3 [],q 8 [],q 2 [4097],q 1 [],q 0 [4097],q 3 [4097],q 0 []]
def B_4_4 : BT (List (List Nat)) := BT.empty
lemma B_4_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_4 4 xs.toFinset) B_4_4 := .empty
def U_4_5 : List Nat := []
def P_4_5 : BT (Option BoundPool) := buildPoolsSubBT 4 W_4 r_4 S_4 ps_4 U_4_5
def N_4_5 : List NodeSpec := [e5 [7] []]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_4_5 : checkNodesBT W_4 g_4 F_4 P_4_5 A_4 B_4_4 5 N_4_5 = true := by decide +kernel
def B_4_5 : BT (List (List Nat)) := buildBucketsBT W_4 N_4_5
set_option maxRecDepth 500000 in
lemma B_4_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_4 5 xs.toFinset) B_4_5 :=
  buildBucketsBT_sound (by decide) gp_4 W_4_ok (buildPoolsSubBT_sound S_4_ok) A_4_ok B_4_4_ok C_4_5
def U_4_6 : List Nat := (r 0 9)
def P_4_6 : BT (Option BoundPool) := buildPoolsSubBT 4 W_4 r_4 S_4 ps_4 U_4_6
def N_4_6 : List NodeSpec := [u5 [5,6] (r 0 9)]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_4_6 : checkNodesBT W_4 g_4 F_4 P_4_6 A_4 B_4_5 6 N_4_6 = true := by decide +kernel
def B_4_6 : BT (List (List Nat)) := buildBucketsBT W_4 N_4_6
set_option maxRecDepth 500000 in
lemma B_4_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_4 6 xs.toFinset) B_4_6 :=
  buildBucketsBT_sound (by decide) gp_4 W_4_ok (buildPoolsSubBT_sound S_4_ok) A_4_ok B_4_5_ok C_4_6
def U_4_7 : List Nat := ([1,2]++r 4 8)
def P_4_7 : BT (Option BoundPool) := buildPoolsSubBT 4 W_4 r_4 S_4 ps_4 U_4_7
def N_4_7 : List NodeSpec := [u5 [5] ([1,2]++r 4 8)]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_4_7 : checkNodesBT W_4 g_4 F_4 P_4_7 A_4 B_4_6 7 N_4_7 = true := by decide +kernel
def B_4_7 : BT (List (List Nat)) := buildBucketsBT W_4 N_4_7
set_option maxRecDepth 500000 in
lemma B_4_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_4 7 xs.toFinset) B_4_7 :=
  buildBucketsBT_sound (by decide) gp_4 W_4_ok (buildPoolsSubBT_sound S_4_ok) A_4_ok B_4_6_ok C_4_7
def U_4_8 : List Nat := [1,4,6,9,12]
def P_4_8 : BT (Option BoundPool) := buildPoolsSubBT 4 W_4 r_4 S_4 ps_4 U_4_8
def N_4_8 : List NodeSpec := [a5 [] [1,4,6,9,12] [0,1,2,3,4,5]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_4_8 : checkNodesBT W_4 g_4 F_4 P_4_8 A_4 B_4_7 8 N_4_8 = true := by decide +kernel
def B_4_8 : BT (List (List Nat)) := buildBucketsBT W_4 N_4_8
set_option maxRecDepth 500000 in
lemma B_4_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_4 8 xs.toFinset) B_4_8 :=
  buildBucketsBT_sound (by decide) gp_4 W_4_ok (buildPoolsSubBT_sound S_4_ok) A_4_ok B_4_7_ok C_4_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_4_ok : forestRootCheck r_4 g_4 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11),(VAR 4,1,17)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_4_in : bucketContainsBT B_4_8 r_4 = true := by decide +kernel
lemma low_4 : Lower r_4 g_4 9 := lower_of_forestBT root_4_ok B_4_8_ok root_4_in
def g_5 := (d 0xe800e800e800e800)
def r_5 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_5 : Lower r_5 g_5 5 := by
  exact lift_of_f (z := 0) (o := 8) (other := r_0) (G := g_0) (essPairs := [(VAR 3,3,11)]) (by decide +kernel) low_0
def g_6 := (d 0xf880f880f880f880)
def r_6 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_6 : Lower r_6 g_6 5 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,6,7)]) (by decide +kernel) hc
def g_7 := (d 0xffe88000ffe88000)
def r_7 : List Nat := varsOf 31
def p_7 : List Nat := [15,15,15,15,19,19,19,21,21,21,22,22,22,23,24,24,25,25,26,26,27,28,28,29,30]
def q_7 : List Nat := [14,13,11,7,18,17,3,20,17,5,20,18,6,7,16,8,17,9,18,10,11,20,12,13,14]
def F_7 : Nat := fullMask 25
set_option maxHeartbeats 0 in
lemma gp_7 : goodPairs g_7 p_7 q_7 := goodPairs_of (by decide +kernel)
def W_7 : BT Decor := buildWiresBT 8 (mkBase p_7 q_7 r_7) [(0,0,1),(0,0,2),(0,1,2),(0,7,4),(1,8,3),(1,3,4),(0,0,10),(1,7,3),(0,12,4),(0,6,4),(3,14,0),(2,0,3),(3,16,2),(2,3,4),(3,18,7),(3,19,0),(0,3,4),(3,21,10),(1,5,21),(0,0,4),(1,7,24),(3,8,4),(2,1,3),(1,27,24),(1,5,3),(3,18,29),(0,5,4),(1,31,2),(1,31,3),(1,7,4),(3,8,34),(2,7,3),(3,36,0),(0,29,4),(2,0,13),(2,0,4),(0,5,2),(3,41,0),(3,42,4),(0,7,3),(3,44,12),(3,40,1),(0,2,3),(3,47,0),(3,5,2),(0,41,4),(3,50,0),(3,41,1),(3,3,4),(3,14,2),(2,5,3),(3,7,3),(1,14,1),(1,14,3),(3,14,4),(3,8,3),(1,8,0),(1,27,6),(3,18,2),(3,63,0),(0,2,10),(3,65,0),(0,5,10),(2,2,21),(3,68,0),(2,0,21),(3,70,1),(1,5,4),(0,3,72),(3,18,0),(0,2,72),(3,6,3),(3,41,4),(3,17,4),(3,16,4),(2,5,47),(3,56,0),(3,5,3),(2,2,3),(3,83,0),(0,84,4),(0,83,4),(3,86,0),(3,49,4),(1,41,3),(0,2,4),(2,5,90),(1,42,3),(0,1,4),(1,93,3),(0,0,94),(3,55,2),(3,12,4),(0,5,3),(0,0,3),(0,0,12),(3,26,0),(3,83,5),(2,5,21),(2,2,4),(3,104,0),(2,5,4),(3,31,4),(1,26,3),(3,16,1),(3,27,2),(3,104,5),(0,16,4),(3,106,0),(1,7,99),(3,27,4),(1,83,5),(1,104,5),(3,55,0),(1,16,21),(3,7,10),(1,18,5),(3,36,4),(3,18,5),(0,1,3),(3,124,2),(3,125,0),(3,110,0),(2,0,115),(3,3,72),(3,93,2),(3,130,0),(1,15,3),(0,42,4),(2,1,4),(3,134,2),(3,135,0),(1,24,3),(3,83,4)]
lemma W_7_ok : btAll (fun x => faithful p_7 q_7 x ∧ x.1 < 2^256) W_7 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_7 : List (List (Nat × Nat)) := [[],[(1,2)],[(0,1)],[(0,2),(1,2)],[(0,1),(1,2)],[(0,2)]]
def A_7 : BT (List (Nat × Nat)) := btOfList 3 al_7
set_option maxHeartbeats 0 in
lemma A_7_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_7 = g_7) A_7 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_7_0 : Slice r_7 g_7 (subcubeFast 0 1) 6 := by
  have hc : Lower (varsOf 30) (d 0xfffcc000fffcc000) 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_1 : Slice r_7 g_7 (subcubeFast 0 2) 6 := by
  have hc : Lower (varsOf 29) (d 0xfffaa000fffaa000) 6 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_2 : Slice r_7 g_7 (subcubeFast 0 4) 6 := by
  have hc : Lower (varsOf 27) (d 0xffee8800ffee8800) 6 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_3 : Slice r_7 g_7 (subcubeFast 8 0) 5 := by
  have hc : Lower (varsOf 23) (d 0xe8e80000e8e80000) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_4 : Slice r_7 g_7 (subcubeFast 0 16) 5 := by
  exact slice_fast_direct_f (z := 0) (o := 16) (by decide +kernel) low_3
set_option maxHeartbeats 0 in
lemma sl_7_5 : Slice r_7 g_7 (subcubeFast 8 16) 4 := by
  exact slice_fast_direct_f (z := 8) (o := 16) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_7_6 : Slice r_7 g_7 (identDom 0 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xeaea8080eaea8080) 5 := carry_of (swaps := [(0,2),(1,2),(3,4)]) (by decide +kernel) low_6
  exact slice_ident (u := 0) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_7 : Slice r_7 g_7 (identDom 1 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xecec8080ecec8080) 5 := carry_of (swaps := [(1,2),(3,4)]) (by decide +kernel) low_6
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_8 : Slice r_7 g_7 (identDom 2 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xf8f88080f8f88080) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_6
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
def S_7 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 0 1,6),some (subcubeFast 0 2,6),some (subcubeFast 0 4,6),some (subcubeFast 8 0,5),some (subcubeFast 0 16,5),some (subcubeFast 8 16,4),some (identDom 0 3,5),some (identDom 1 3,5),some (identDom 2 3,5)]
lemma S_7_ok : btAll (fun o => ∀ p, o = some p → Slice r_7 g_7 p.1 p.2) S_7 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_7_0) (forall_cons (fun _ h => by cases h; exact sl_7_1) (forall_cons (fun _ h => by cases h; exact sl_7_2) (forall_cons (fun _ h => by cases h; exact sl_7_3) (forall_cons (fun _ h => by cases h; exact sl_7_4) (forall_cons (fun _ h => by cases h; exact sl_7_5) (forall_cons (fun _ h => by cases h; exact sl_7_6) (forall_cons (fun _ h => by cases h; exact sl_7_7) (forall_cons (fun _ h => by cases h; exact sl_7_8) (fun _ h => (List.not_mem_nil h).elim))))))))))
def ps_7 : BT (Option PoolSpec) := btOfList 7 [q 0 [16396,16397,41047],q 1 [],q 1 [16412,16413,139299],q 1 [12316,12317,49331],q 2 [],q 0 [],q 0 [16397,40968],q 6 [],q 3 [40960],q 1 [16397,40960],q 5 [],q 1 [16396,16397,41047],q 2 [16396,16397,41047],q 0 [16396,86026],q 1 [16396,86018],q 0 [16405,294924],q 3 [],q 0 [16405,294920],q 0 [16396,86037],q 4 [12386],q 0 [16404,16405],q 1 [16412,12323],q 1 [16412,35],q 1 [12319,227],q 0 [12310,12311],q 4 [],q 0 [16398,16399],q 0 [16392,368662],q 0 [16388,12661],q 0 [12310,8415],q 0 [16404,12413],q 7 [],q 0 [12308,12309],q 0 [12298,20815],q 3 [16388],q 0 [16396,86038],q 4 [12290],q 0 [16406,16407],q 1 [8192],q 0 [12294,8303],q 1 [16404,12413],q 1 [16392,363],q 3 [40968],q 0 [12298,20813],q 1 [16384,98333],q 0 [16396,16397],q 0 [16397,40980],q 1 [16397,40991],q 0 [16405,294927],q 3 [16451],q 1 [8564,35],q 1 [16384,12413],q 0 [4192,12413],q 0 [16388,8567],q 0 [16398],q 0 [16396],q 2 [16396,86018],q 0 [16397],q 2 [16397,40960],q 4 [12385],q 2 [16384],q 1 [16384],q 0 [4192],q 0 [12385],q 1 [16384,12385],q 2 [16384,12385],q 8 [],q 0 [16399],q 0 [16388],q 1 [12290],q 0 [12294],q 0 [16448],q 2 [4096],q 0 [12310],q 1 [16396,16397],q 2 [16396,16397],q 0 [16404],q 0 [16392],q 2 [363],q 0 [12309],q 1 [12309],q 1 [12310],q 0 [12308],q 0 [8196],q 1 [31],q 0 [8212],q 2 [31],q 0 [16405],q 1 [12319],q 0 [16406],q 1 [16398,16399],q 2 [16398,16399],q 1 [16386],q 1 [8212],q 1 [16415],q 2 [16415],q 2 [16719],q 3 [16719],q 3 [16384],q 2 [335],q 0 [12298],q 1 [12298,335],q 0 [12296],q 2 [419],q 0 [16394],q 1 [16404],q 2 [191],q 1 [16399],q 2 [16399],q 1 [16398],q 2 [16398],q 2 [16386],q 2 [12290],q 1 [12288],q 2 [12288],q 1 [16397],q 2 [16397],q 1 [16396],q 2 [16396]]
def B_7_2 : BT (List (List Nat)) := BT.empty
lemma B_7_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_7 2 xs.toFinset) B_7_2 := .empty
def U_7_3 : List Nat := []
def P_7_3 : BT (Option BoundPool) := buildPoolsSubBT 7 W_7 r_7 S_7 ps_7 U_7_3
def N_7_3 : List NodeSpec := [([5,6,9,4],[],[]),([11,1,2,13],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_7_3 : checkNodesBT W_7 g_7 F_7 P_7_3 A_7 B_7_2 3 N_7_3 = true := by decide +kernel
def B_7_3 : BT (List (List Nat)) := buildBucketsBT W_7 N_7_3
set_option maxRecDepth 500000 in
lemma B_7_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_7 3 xs.toFinset) B_7_3 :=
  buildBucketsBT_sound (by decide) gp_7 W_7_ok (buildPoolsSubBT_sound S_7_ok) A_7_ok B_7_2_ok C_7_3
def U_7_4 : List Nat := (r 0 6)
def P_7_4 : BT (Option BoundPool) := buildPoolsSubBT 7 W_7 r_7 S_7 ps_7 U_7_4
def N_7_4 : List NodeSpec := [([15,1,17,3,4],[],[]),([20,1,2,3,4],[],[]),([22,5,0,1,2],[0],[]),([16,1,2,23,4],[],[]),([5,25,2,3,4],[1],[]),([26,5,6,3,4],[],[]),([5,28,2,3,4],[],[]),([0,1,2,30,4],[],[]),([11,1,2,12,4],[],[0]),([0,1,32,33,4],[],[]),([35,0,1,2,3],[2],[]),([16,5,2,12,4],[],[]),([37,1,2,21,4],[],[]),([0,1,2,38,10],[],[4]),([39,1,2,3,4],[],[]),([40,1,43,2,3],[],[]),([45,0,1,2,4],[3],[]),([42,46,2,3,4],[],[]),([48,49,1,3,4],[],[]),([51,1,2,3,4],[],[]),([42,52,2,3,4],[],[]),([53,37,1,2,4],[],[]),([15,54,1,3,4],[],[]),([5,6,3,12,4],[],[]),([55,6,7,3,4],[4],[]),([56,37,1,2,4],[],[]),([15,57,2,3,4],[],[]),([15,1,2,58,4],[],[]),([15,59,1,2,3],[],[]),([60,1,61,2,4],[],[]),([51,1,2,9,4],[],[]),([51,60,1,2,4],[],[]),([31,6,7,3,4],[4],[4]),([5,62,2,3,4],[5],[]),([5,0,2,9,4],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_7_4 : checkNodesBT W_7 g_7 F_7 P_7_4 A_7 B_7_3 4 N_7_4 = true := by decide +kernel
def B_7_4 : BT (List (List Nat)) := buildBucketsBT W_7 N_7_4
set_option maxRecDepth 500000 in
lemma B_7_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_7 4 xs.toFinset) B_7_4 :=
  buildBucketsBT_sound (by decide) gp_7 W_7_ok (buildPoolsSubBT_sound S_7_ok) A_7_ok B_7_3_ok C_7_4
def U_7_5 : List Nat := ([0,1]++r 4 50)
def P_7_5 : BT (Option BoundPool) := buildPoolsSubBT 7 W_7 r_7 S_7 ps_7 U_7_5
def N_7_5 : List NodeSpec := [e5 [64] [],([66,0,1,65,3,4],[6],[]),([67,11,1,2,3,4],[7,8,9],[]),([22,0,1,2],[0,10,11,12],[0,1,3]),e5 [69] [13],([70,71,1,2,3,4],[14],[]),e5 [66] [6],([5,0,1,2,73,4],[15],[]),([5,74,1,2,3,4],[1,16],[]),([5,0,1,75,3,4],[17],[]),([16,76,6,1,2,4],[],[]),e5 [77] [],a5 [23] [16,18] [0,2],e5 [78] [],([24,0,1,2,3,79],[7,19],[]),([31,0,1,2,3,72],[20],[4]),([60,0,7,1,2,4],[21],[]),([16,5,7,2,3,4],[],[0,1,2]),([16,0,1,2,12,4],[5],[0,1]),([51,7,1,2,3,4],[22],[]),([51,8,1,2,3,4],[5],[0]),e5 [80] [4,7],([81,7,1,2,3,4],[23],[]),([55,82,0,1,2,4],[24],[4]),e5 [85] [16],a5 [50] [7,16] [0,2,4],e5 [87] [],([84,24,1,2,3,4],[25],[5]),([55,6,1,2,3,4],[4],[0]),([31,0,1,2,33,4],[16],[0,1,3,4]),([40,42,1,2,3,4],[],[0,1]),([42,5,1,2,3,4],[5],[1]),([16,41,1,2,3,4],[16],[]),([18,53,5,0,1,2],[26],[0]),e5 [37] [],a5 [88] [] [4],e5 [89] [],e5 [91] [27],([53,84,0,1,2,4],[],[]),e5 [92] [7],e5 [95] [28],([16,5,1,2,21,4],[],[0]),([5,0,1,96,3,4],[7,29],[4]),([42,41,1,2,3,4],[5],[0,1]),([16,52,1,2,3,4],[],[]),([42,0,93,2,3,4],[],[]),([5,0,1,2,33,4],[30],[]),([41,24,1,2,3,4],[25],[]),([0,1,2,29,4,10],[7,31],[0,4]),e5 [97] [],([98,0,1,2,29,4],[32],[4]),a5 [38] [1,4,5,7] [0,4],a5 [31] [4,7,16] [4],([16,53,5,1,2,4],[10],[]),([51,1,2,3,4],[],[]),([5,0,2,3,12,4],[5],[0]),([31,6,1,2,3,4],[4],[0,4]),([99,0,1,2,12,4],[5],[]),([26,0,8,1,2,3],[5],[2,4]),e5 [26] [],([5,24,1,2,3,72],[],[]),([42,5,7,2,3,4],[1,5],[]),([15,6,1,90,3,4],[5],[]),e5 [100] [],([60,0,8,1,2,4],[31],[0]),([15,14,1,2,3,4],[5],[0]),([55,0,1,2,21,4],[],[0,4]),([18,0,1,2,29,4],[],[0]),e5 [101] [],e5 [102] [4,33],([16,5,1,2,29,4],[16],[]),([31,0,1,32,3,4],[],[0,1,3,4]),([5,0,2,3,94,4],[28,34],[]),e5 [103] [35],([42,99,1,2,3,4],[7],[3,5]),e5 [29] [],([16,5,93,2,3,4],[1,5,34,36],[2]),([5,105,1,2,3,4],[1],[4]),([106,107,0,1,2,3],[37],[4]),e5 [108] [1,4,5,7],([26,5,0,2,3,4],[5],[0]),([5,6,7,3,4],[1,4,5,38],[0,1,2,3,4]),([26,0,7,93,2,3],[25],[]),([5,6,93,2,3,4],[],[2,3]),([16,5,109,2,3,4],[1],[]),([5,0,110,2,3,4],[5,39],[]),a5 [111] [7,16] [4],([55,53,0,1,2,4],[25],[4]),([15,6,1,2,3,4],[5],[0]),([112,5,1,2,3,4],[1],[]),([0,1,2,33,4],[30,40],[4,5]),([48,5,1,2,3,4],[1,16],[0]),e5 [51] [],([16,27,5,2,3,4],[1,5,16],[]),([5,113,1,2,3,4],[5,25],[]),([15,0,7,1,3,4],[1,41],[]),([5,24,93,2,3,4],[1,5,25],[]),u5 [28] [],e5 [114] [],([5,0,1,65,3,4],[6,42],[4]),([48,6,1,2,3,4],[5,16],[]),([5,0,2,3,115,4],[5],[]),a5 [116] [1,5,16,43] [1,3],a5 [25] [4,25,44] [0,1],e5 [117] [],([70,5,1,2,3,4],[1],[]),([70,7,1,2,3,4],[14],[]),([5,118,1,2,3,4],[5,7],[]),([5,0,1,2,21,10],[45],[0]),e5 [67] [7,46],([16,0,1,2,119,4],[16],[]),e5 [120] [1,47],([37,1,2,3,4],[],[0]),([5,11,1,2,3,4],[1,7,8],[]),([84,0,1,2,21,4],[],[]),e5 [121] [],e5 [33] [],e5 [122] [],a5 [123] [4,16] [4],e5 [126] [],e5 [127] [39],e5 [128] [],([129,5,0,1,2,4],[48],[]),([16,53,0,1,2,79],[25,49],[]),([51,93,1,2,3,4],[50],[]),([16,15,1,2,3,4],[16],[0]),([15,24,1,2,3,4],[5],[0]),([24,0,1,2,33,4],[51,52],[3]),([26,0,93,1,2,3],[1,5],[4]),e5 [131] [53],e5 [132] [],e5 [133] [],e5 [136] [],([103,70,1,2,3,4],[14],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_7_5 : checkNodesBT W_7 g_7 F_7 P_7_5 A_7 B_7_4 5 N_7_5 = true := by decide +kernel
def B_7_5 : BT (List (List Nat)) := buildBucketsBT W_7 N_7_5
set_option maxRecDepth 500000 in
lemma B_7_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_7 5 xs.toFinset) B_7_5 :=
  buildBucketsBT_sound (by decide) gp_7 W_7_ok (buildPoolsSubBT_sound S_7_ok) A_7_ok B_7_4_ok C_7_5
def U_7_6 : List Nat := ([1,4,5]++r 7 4++[14,16,25,26,31,36,38,41,45,49]++r 54 53)
def P_7_6 : BT (Option BoundPool) := buildPoolsSubBT 7 W_7 r_7 S_7 ps_7 U_7_6
def N_7_6 : List NodeSpec := [a5 [74] [1,4,5,16,25,54] [0,1,3,5],a5 [70] [1,4,10,14,16,55,56] [0,1,3,5],a5 [11] [1,4,5,9,10,25,57,58] [0,1,3,5],u5 [112,24] [7,10,16],e5 [24,137] [7,10,59],a5 [31,24] [1,10,60,61,62] [0,1,3,4],a5 [137] ([7,10,31]++r 63 4) [2,4],([16,53,0,1,2,4],[5,10,16,25,67],[0,1,3,5]),a5 [16,93] [1,5,7,68,69] [0,1,2,3],u5 [16,27] [1,7,31,69,70],u5 [16,79] [5,7,10,16,25,49],([70,1,2,3,4],[10,14,16,56],[0,1]),a5 [112] [1,4,7,10,71] [0,1,3,5],a5 [55,5] [7,16,72,73] [0,2],([0,1,2,21,10],[16,25,45,74,75],[0,1,3]),a5 [31,5] [25,72,76] [0,1,3,4],u5 [15,90] [5,25,77,78],a5 [29] [4,7,25,66,79,80] [0,4,5],([11,1,2,3,4],[8,9,10,58],[0,1,3,5]),a5 [55] [4,7,25,73,81] [0,2,4],a5 [98,5] [7,16,82] [0,1,3],a5 [42,7] [1,4,5,83,84] [0,1],a5 [41,5] [4,72,85] [0,2,4],([5,6,1,2,3,4],[1,4,5,38,72],[0,1,2,4]),a5 [42] [7,16,25,83,84,86] [0,1,2,3,4],u5 [16,109] [1,5,7,16],a5 [5,72] [1,25,72,87] [0,2,4],a5 [56,7] [1,4,16,83,88] [0,2,3,4],a5 [106,5] [25,89] [0,2],([18,53,0,1,2],[10,16,26,90,91],[0,1,3]),a5 [5,90] [1,4,72,77] [0,1,3,4],a5 [40,7] [1,4,5,25,83,92] [0,3,5],a5 [15] [1,7,16,41,77,78] [0,3],a5 [41] [7,16,25,72,85,93] [0,2,4],a5 [24,93] [1,61,68] [0,1,3],([16,0,1,2,21,4],[10,16,25,36,55],[0,1,3,5]),a5 [26] [4,5,16,94,95] [0,1,3],a5 [5,21] [1,16,55,72] [0,2,4],([16,5,1,2,3,4],[1,5,16,36,69],[0,1,2]),a5 [138] [1,5,10,16,66,96,97] [0,1,2,3],([5,24,1,2,3,4],[1,5,25,61,98],[0,1,2,3,4,5]),a5 [84] [1,7,25,99,100,101] [0,3,5],a5 [5,47] [1,4,16,72,102] [0,2,4],a5 [5,29] [1,7,16,79] [0,2],a5 [16,7] [1,4,5,7,16,69,83] [0,1,2,3,4],a5 [5,10] [1,16,25,57,72] [0,2,4],a5 [105] [1,10,16,25,103,104] [0,3],a5 [53,5] [1,5,7,10,67] [0,2,4],a5 [31] [4,7,16,76,105] [0,1,2,3,4],a5 [18,5] [1,5,16,54] [0,2],a5 [26,7] [1,4,25,94] [0,1,3],a5 [48] [1,10,16,102,106] [0,3]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_7_6 : checkNodesBT W_7 g_7 F_7 P_7_6 A_7 B_7_5 6 N_7_6 = true := by decide +kernel
def B_7_6 : BT (List (List Nat)) := buildBucketsBT W_7 N_7_6
set_option maxRecDepth 500000 in
lemma B_7_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_7 6 xs.toFinset) B_7_6 :=
  buildBucketsBT_sound (by decide) gp_7 W_7_ok (buildPoolsSubBT_sound S_7_ok) A_7_ok B_7_5_ok C_7_6
def U_7_7 : List Nat := ([1,4,5,7,10,16,25,54,55,57,60,61,67,69,72,92]++r 107 12)
def P_7_7 : BT (Option BoundPool) := buildPoolsSubBT 7 W_7 r_7 S_7 ps_7 U_7_7
def N_7_7 : List NodeSpec := [a5 [53] [1,4,5,10,67,107,108] [0,1,2,3,4],a5 [18] [1,4,5,16,25,54,109,110] [0,1,2,3,4],a5 [40] [1,4,5,10,25,92,111] [0,3,5],a5 [24] [1,4,5,10,16,25,60,61] [0,1,2,3,4,5],a5 [16] [1,4,5,7,10,16,25,69,112] [0,1,3,5],a5 [99] [1,4,5,10,16,25,113,114] [3,5],a5 [10] [1,4,5,10,16,57,115,116] [0,1,2,3,4],a5 [21] [1,4,5,10,16,55,117,118] [0,1,2,3,4],a5 [5] [1,4,5,16,25,72] [0,2,4]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_7_7 : checkNodesBT W_7 g_7 F_7 P_7_7 A_7 B_7_6 7 N_7_7 = true := by decide +kernel
def B_7_7 : BT (List (List Nat)) := buildBucketsBT W_7 N_7_7
set_option maxRecDepth 500000 in
lemma B_7_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_7 7 xs.toFinset) B_7_7 :=
  buildBucketsBT_sound (by decide) gp_7 W_7_ok (buildPoolsSubBT_sound S_7_ok) A_7_ok B_7_6_ok C_7_7
def U_7_8 : List Nat := [1,4,5]
def P_7_8 : BT (Option BoundPool) := buildPoolsSubBT 7 W_7 r_7 S_7 ps_7 U_7_8
def N_7_8 : List NodeSpec := [a5 [] [1,4,5] [0,1,2,3,4]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_7_8 : checkNodesBT W_7 g_7 F_7 P_7_8 A_7 B_7_7 8 N_7_8 = true := by decide +kernel
def B_7_8 : BT (List (List Nat)) := buildBucketsBT W_7 N_7_8
set_option maxRecDepth 500000 in
lemma B_7_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_7 8 xs.toFinset) B_7_8 :=
  buildBucketsBT_sound (by decide) gp_7 W_7_ok (buildPoolsSubBT_sound S_7_ok) A_7_ok B_7_7_ok C_7_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_7_ok : forestRootCheck r_7 g_7 [(VAR 0,14,15),(VAR 1,13,15),(VAR 2,11,15),(VAR 3,7,15),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_7_in : bucketContainsBT B_7_8 r_7 = true := by decide +kernel
lemma low_7 : Lower r_7 g_7 9 := lower_of_forestBT root_7_ok B_7_8_ok root_7_in
def g_8 := (d 0xfec0fec0fec0fec0)
def r_8 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_8 : Lower r_8 g_8 5 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,8,9)]) (by decide +kernel) hc
def g_9 := (d 0xfee0fee0fee0fee0)
def r_9 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_9 : Lower r_9 g_9 5 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,4,5)]) (by decide +kernel) hc
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
def g_12 := (d 0xfea8c000fea8c000)
def r_12 : List Nat := varsOf 31
def p_12 : List Nat := [14,14,14,15,15,15,19,19,19,21,21,21,23,23,25,25,25,26,26,26,27,28,28,28,29,30]
def q_12 : List Nat := [12,10,6,13,11,7,18,17,3,20,17,5,22,7,24,17,9,24,18,10,11,24,20,12,13,22]
def F_12 : Nat := fullMask 26
set_option maxHeartbeats 0 in
lemma gp_12 : goodPairs g_12 p_12 q_12 := goodPairs_of (by decide +kernel)
def W_12 : BT Decor := buildWiresBT 8 (mkBase p_12 q_12 r_12) [(0,0,4),(1,1,2),(0,6,3),(1,5,7),(0,3,4),(0,2,4),(1,1,10),(2,11,3),(3,2,3),(0,11,3),(2,6,3),(0,1,2),(3,16,3),(0,0,3),(3,18,6),(1,2,4),(3,10,20),(1,0,7),(0,22,4),(2,0,3),(1,24,1),(0,1,4),(1,26,2),(2,6,9),(0,7,4),(0,27,3),(2,0,30),(1,5,2),(0,6,4),(1,5,1),(1,34,2),(0,35,3),(3,0,4),(1,37,7),(1,24,16),(3,6,3),(3,40,4),(2,0,7),(3,33,3),(1,3,4),(3,9,44),(0,3,20),(2,0,46),(1,1,4),(0,3,48),(0,0,49),(1,1,3),(3,2,51),(1,2,3),(3,1,53),(3,54,4),(0,1,3),(1,13,1),(0,2,3),(1,58,1),(3,6,4),(3,60,3),(1,13,10),(0,57,4),(3,7,4),(3,3,4),(3,65,6),(3,1,3),(3,58,6),(3,10,51),(0,0,6),(2,2,1),(1,71,13),(3,67,4),(2,34,2),(3,24,6),(0,25,4),(2,0,2),(1,77,26),(3,2,48),(0,1,20),(3,18,48),(2,1,2),(1,82,18),(1,18,26),(3,10,1),(1,77,1),(0,86,4),(1,18,1),(0,88,4),(2,1,4),(1,24,82),(1,18,2),(1,90,18),(1,18,16),(1,24,26),(3,24,48),(0,53,4),(1,90,24),(3,1,4),(0,0,11),(3,5,6),(1,13,26),(1,1,9),(3,2,9),(2,3,4),(3,105,0),(3,2,44),(0,0,44),(1,65,1),(3,2,4),(2,2,4),(3,111,0),(3,13,4),(3,111,3),(2,2,3),(1,115,1),(0,51,4),(2,0,1),(3,118,4),(0,1,44),(3,18,4),(2,0,58),(3,24,4),(3,13,1),(0,0,2),(1,125,1),(2,1,3),(1,127,2),(3,3,48),(3,115,1),(3,10,3),(0,0,48),(3,71,3),(0,0,1),(2,0,4)]
lemma W_12_ok : btAll (fun x => faithful p_12 q_12 x ∧ x.1 < 2^256) W_12 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_12 : List (List (Nat × Nat)) := [[],[(1,2)]]
def A_12 : BT (List (Nat × Nat)) := btOfList 1 al_12
set_option maxHeartbeats 0 in
lemma A_12_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_12 = g_12) A_12 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_12_0 : Slice r_12 g_12 (subcubeFast 0 1) 6 := by
  have hc : Lower (varsOf 30) (d 0xfffcc000fffcc000) 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_1 : Slice r_12 g_12 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xfaa00000faa00000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_2 : Slice r_12 g_12 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xfc00c000fc00c000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_3 : Slice r_12 g_12 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) (d 0xee880000ee880000) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_4 : Slice r_12 g_12 (subcubeFast 0 8) 5 := by
  have hc : Lower (varsOf 23) (d 0xfefec0c0fefec0c0) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_5 : Slice r_12 g_12 (subcubeFast 0 16) 5 := by
  have hc : Lower (varsOf 15) (d 0xfea8fea8fea8fea8) 5 := carry_of (swaps := [(0,2),(1,2)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 0) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_6 : Slice r_12 g_12 (subcubeFast 4 16) 4 := by
  have hc : Lower (varsOf 11) (d 0xee88ee88ee88ee88) 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_7 : Slice r_12 g_12 (subcubeFast 2 16) 4 := by
  have hc : Lower (varsOf 13) (d 0xfaa0faa0faa0faa0) 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 2) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_8 : Slice r_12 g_12 (subcubeFast 1 8) 4 := by
  have hc : Lower (varsOf 22) (d 0xfcfcc0c0fcfcc0c0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_9 : Slice r_12 g_12 (identDom 1 2) 5 := by
  have hc : Lower (varsOf 27) (d 0xee88cc00ee88cc00) 5 := carry_of (swaps := [(1,2),(2,4)]) (by decide +kernel) low_6
  exact slice_ident (u := 1) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_10 : Slice r_12 g_12 (identDom 1 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xececc0c0ececc0c0) 5 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_10
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_11 : Slice r_12 g_12 (identDom 2 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xf8f8c0c0f8f8c0c0) 5 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_10
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_12 : Slice r_12 g_12 (subcubeFast 0 4) 4 := by
  have hc : Lower (varsOf 27) (d 0xffaacc00ffaacc00) 4 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_11
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_13 : Slice r_12 g_12 (subcubeFast 0 2) 4 := by
  have hc : Lower (varsOf 29) (d 0xffaaf000ffaaf000) 4 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_11
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
def S_12 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 0 1,6),some (subcubeFast 2 0,5),some (subcubeFast 1 0,5),some (subcubeFast 4 0,5),some (subcubeFast 0 8,5),some (subcubeFast 0 16,5),some (subcubeFast 4 16,4),some (subcubeFast 2 16,4),some (subcubeFast 1 8,4),some (identDom 1 2,5),some (identDom 1 3,5),some (identDom 2 3,5),some (subcubeFast 0 4,4),some (subcubeFast 0 2,4)]
lemma S_12_ok : btAll (fun o => ∀ p, o = some p → Slice r_12 g_12 p.1 p.2) S_12 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_12_0) (forall_cons (fun _ h => by cases h; exact sl_12_1) (forall_cons (fun _ h => by cases h; exact sl_12_2) (forall_cons (fun _ h => by cases h; exact sl_12_3) (forall_cons (fun _ h => by cases h; exact sl_12_4) (forall_cons (fun _ h => by cases h; exact sl_12_5) (forall_cons (fun _ h => by cases h; exact sl_12_6) (forall_cons (fun _ h => by cases h; exact sl_12_7) (forall_cons (fun _ h => by cases h; exact sl_12_8) (forall_cons (fun _ h => by cases h; exact sl_12_9) (forall_cons (fun _ h => by cases h; exact sl_12_10) (forall_cons (fun _ h => by cases h; exact sl_12_11) (forall_cons (fun _ h => by cases h; exact sl_12_12) (forall_cons (fun _ h => by cases h; exact sl_12_13) (fun _ h => (List.not_mem_nil h).elim)))))))))))))))
def ps_12 : BT (Option PoolSpec) := btOfList 7 [q 0 [16392,16393,81963],q 0 [],q 1 [16384,16408],q 9 [12312,28674],q 8 [],q 7 [],q 6 [],q 0 [16393,81932],q 10 [],q 1 [196620],q 0 [16389,196620],q 2 [],q 3 [],q 1 [16392],q 5 [],q 13 [],q 1 [],q 0 [12299,4149],q 0 [16388,8297],q 3 [16388],q 12 [],q 4 [],q 11 [],q 9 [],q 9 [12314],q 0 [8196,8197],q 9 [12312],q 9 [24576],q 1 [16408],q 5 [4105],q 5 [8197],q 9 [12290],q 0 [16388,16389],q 0 [16388,106805],q 0 [16389,196619],q 3 [81924],q 0 [16393,81924],q 0 [16389,196683],q 0 [8198,74057],q 0 [16388,106569],q 0 [16392,4139],q 9 [12288],q 0 [16389,196707],q 0 [16390,16391],q 0 [16392,4137],q 1 [16384],q 4 [16384],q 1 [16387],q 4 [16387],q 0 [16396,36869],q 1 [16395],q 3 [16439],q 2 [12299],q 0 [16389],q 0 [12299],q 0 [16396],q 3 [16384],q 1 [16859],q 0 [16859],q 0 [8196],q 2 [16396],q 0 [16390],q 0 [16388],q 0 [8197],q 0 [16459],q 0 [16483],q 0 [12296],q 0 [12292],q 0 [16391],q 0 [8198],q 0 [4169],q 0 [4117],q 0 [16395],q 0 [16399],q 3 [16387],q 0 [12293],q 0 [4597],q 2 [12295],q 1 [196619],q 1 [196623],q 0 [16389,196623],q 2 [12292],q 0 [16392,12331],q 0 [4193],q 1 [196608],q 0 [4106,12575],q 0 [4405]]
def B_12_2 : BT (List (List Nat)) := BT.empty
lemma B_12_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 2 xs.toFinset) B_12_2 := .empty
def U_12_3 : List Nat := []
def P_12_3 : BT (Option BoundPool) := buildPoolsSubBT 7 W_12 r_12 S_12 ps_12 U_12_3
def N_12_3 : List NodeSpec := [([1,2,8,9],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_3 : checkNodesBT W_12 g_12 F_12 P_12_3 A_12 B_12_2 3 N_12_3 = true := by decide +kernel
def B_12_3 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_3
set_option maxRecDepth 500000 in
lemma B_12_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 3 xs.toFinset) B_12_3 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_2_ok C_12_3
def U_12_4 : List Nat := (r 0 4)
def P_12_4 : BT (Option BoundPool) := buildPoolsSubBT 7 W_12 r_12 S_12 ps_12 U_12_4
def N_12_4 : List NodeSpec := [([12,13,0,11,4],[],[]),([13,0,14,11,4],[],[]),([15,17,0,6,4],[],[]),([19,0,16,3,4],[],[]),([21,18,0,1,3],[0],[]),([1,2,7,23,3],[],[]),([0,25,27,3,4],[],[]),([28,5,1,2,3],[],[]),([5,1,2,29,3],[1],[]),([31,1,27,3,4],[],[]),([17,0,7,6,4],[],[]),([5,1,32,33,3],[2],[]),([24,21,0,1,3],[0],[]),([5,1,2,36,4],[],[]),([1,2,38,3,4],[],[]),([0,39,6,3,4],[],[]),([13,5,1,33,3],[2],[]),([1,2,8,3,4],[1],[0]),([5,1,2,7,9],[],[0]),([5,1,2,41,3],[],[]),([42,16,6,3,4],[3],[]),([43,5,1,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_4 : checkNodesBT W_12 g_12 F_12 P_12_4 A_12 B_12_3 4 N_12_4 = true := by decide +kernel
def B_12_4 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_4
set_option maxRecDepth 500000 in
lemma B_12_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 4 xs.toFinset) B_12_4 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_3_ok C_12_4
def U_12_5 : List Nat := ([0,1,2]++r 4 45)
def P_12_5 : BT (Option BoundPool) := buildPoolsSubBT 7 W_12 r_12 S_12 ps_12 U_12_5
def N_12_5 : List NodeSpec := [([45,0,1,2],[4,5,6],[]),([47,0,1,2,46,4],[7],[]),([50,0,1,2,49,4],[8,9,10],[]),e5 [14] [1,8,11,12],([13,0,11,3,4],[5,6,12,13],[0]),([52,0,1,10,3,4],[14,15],[]),e5 [55] [16],([0,56,57,2,3,4],[16,17],[]),([0,56,2,59,3,4],[16],[]),([0,1,30,27,3,4],[16,18,19,20],[0,1]),e5 [61] [1,11],([0,1,2,33,9,3],[5,6,15,20,21],[]),u5 [43] [],u5 [41] [],e5 [7] [1,11],([13,0,1,3,62,4],[12],[]),e5 [63] [16],([42,1,2,6,3,4],[],[0]),([0,1,2,7,9,4],[8,14,22],[0]),e5 [64] [1,11],([42,1,2,7,3,4],[1],[]),([1,2,7,22,3,4],[11],[0]),e5 [66] [1,11],([13,67,0,6,3,4],[12,16,21],[]),([0,56,58,6,3,4],[16,21],[]),([68,0,1,6,3,4],[12,16],[]),e5 [69] [16],([15,0,16,6,3,4],[16,20,23,24],[0]),([0,16,7,6,3,4],[16,20,23,25,26],[0]),([70,0,16,6,3,4],[25,27],[]),([13,0,1,33,3,4],[6,12,28,29],[0]),([17,0,6,3,4],[6,16,23,30],[0]),([12,0,2,11,3,4],[5,12,15],[0]),([13,72,0,1,3,4],[12],[]),([24,0,16,6,3,4],[16,25,31],[0]),([0,1,73,2,9,3],[8,21],[]),([74,5,1,2,3,4],[],[]),e5 [75] [11],e5 [76] [],u5 [39] [],([40,5,1,2,3,4],[14],[0]),([24,0,1,2,7,4],[1],[]),([18,0,26,2,3,48],[32],[1]),([65,0,1,2,7,4],[],[]),e5 [78] [33],([18,0,1,2,49,4],[1,8,9],[]),([0,26,25,2,3,4],[],[0]),([24,0,1,2,49,4],[1],[]),([79,18,0,1,3,4],[34],[]),([18,0,80,2,3,4],[20,35,36],[]),e5 [81] [1,37],e5 [83] [38],([82,0,25,2,3,4],[],[]),e5 [84] [39],([85,18,0,2,3,4],[40],[]),([5,0,1,2,33,3],[1,6,15,20],[]),([0,26,86,2,3,4],[20],[]),e5 [87] [16],e5 [89] [11,12,15,20],([18,0,1,2,7,4],[1],[]),([90,0,88,2,3,4],[11],[]),e5 [91] [],([18,0,16,6,3,4],[20,25,41],[0]),([45,0,1,2,9],[4,5,6,21],[]),([24,79,0,1,3,4],[34],[]),([21,0,1,3],[0,5,6],[0]),([0,16,1,92,3,4],[20],[]),([5,1,2,33,6,3],[2,6],[]),([52,37,1,2,3,4],[],[]),([13,0,1,11,3,4],[13,21],[]),([18,0,1,27,3,4],[18],[]),e5 [93] [1],e5 [94] [],u5 [19] [],([24,0,80,2,3,4],[36],[]),e5 [95] [],e5 [96] [42],([24,0,1,27,3,4],[16,18],[0]),([0,26,1,2,3,97],[6,15,20],[]),([37,1,2,7,3,4],[1],[0]),([24,0,26,2,3,48],[32],[1]),u5 [29] [1,11,12,16],([13,0,56,6,3,4],[16,21],[]),e5 [98] [1],([90,24,99,0,2,3],[43],[1]),([100,0,2,11,3,4],[44],[]),([5,1,32,6,3,4],[11,45],[0]),([5,1,2,7,3,4],[11,14],[0]),([5,1,2,35,3,4],[1,14,46],[0]),([5,1,2,33,3],[1,5,6],[0,1]),([101,5,1,2,3,4],[1,14],[]),([13,5,1,6,3,4],[45,46],[0]),([0,26,57,2,3,4],[20],[]),u5 [28] [],([90,99,18,0,2,3],[43],[1]),([5,1,2,6,9,3],[5,6,46],[0]),e5 [102] [16],([5,1,57,2,3,4],[],[]),([5,1,2,9,3,103],[5],[]),([37,1,57,2,3,4],[],[]),([104,5,1,2,9,3],[6],[]),([24,85,0,2,3,4],[40],[]),e5 [101] [11],([13,37,1,6,3,4],[47,48],[]),([40,37,1,2,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_5 : checkNodesBT W_12 g_12 F_12 P_12_5 A_12 B_12_4 5 N_12_5 = true := by decide +kernel
def B_12_5 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_5
set_option maxRecDepth 500000 in
lemma B_12_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 5 xs.toFinset) B_12_5 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_4_ok C_12_5
def U_12_6 : List Nat := ([1,4,5,6]++r 8 11++r 20 4++[25,28,29,31,32,34,35,36,40,41]++r 43 44)
def P_12_6 : BT (Option BoundPool) := buildPoolsSubBT 7 W_12 r_12 S_12 ps_12 U_12_6
def N_12_6 : List NodeSpec := [([106,1,2,3,4],[1,5,6,11],[]),([107,0,1,3,4],[5,6,21],[]),([108,1,2,3,4],[1,6,11,21],[]),a5 [104,9] [6,12,22] [0,1],e5 [109] [4,5,12,15,20],e5 [103] [5,11,12,15,20,49],([90,99,0,2,3],[5,6,16,43],[0,1]),u5 [49] [1,5,6,10,11,14,16],([0,1,2,49,4],[5,6,9,10],[0,1]),([85,0,2,3,4],[6,12,16,40],[0]),u5 [11] [5,11,12,15,21,44],a5 [13,9] [4,6,22] [1],([13,110,0,1,3,4],[6,12,14,20,21,50],[]),([112,1,2,3,4],[1,5,11,12],[]),u5 [13,67] [8,12,16,21,22],e5 [13,113] [12,14,20,21,22,51],e5 [104] [1,6,11,15,16,22],e5 [13,57] [12,16,20,22],u5 [57] ([8,11,12]++r 14 4++[20]),([0,1,2,9,44],[4,5,6],[0]),u5 [9,103] [5,8],e5 [114] [1,5,11,12,14],e5 [116] [4,6],a5 [117] [1,4,5,11,12,20] [1],([13,0,1,10,3,4],[6,12,13,14,21,52],[0]),e5 [110,51] [5,6,20,21],a5 [24,48] [11,14,21,53] [0,1],u5 [13,56] [4,8,12,16,22,54],([5,1,2,9,3,4],[1,4,5,6,11,45,55,56],[]),e5 [119] [1,4,5,11,12,20,57,58],u5 [24,16] [1,11,16,59],e5 [13,99] [5,6,8,12,15,20],([5,1,2,9,3],[4,5,6,60],[0,1]),u5 [90,18] [1,11,16,61],([0,120,2,3,4],[6,16,21],[]),([105,5,1,2,3],[4,6,14],[]),([13,5,1,2,3,4],[4,6,11,45,56],[0]),a5 [52] [1,4,11,12,14,15,16,20] [0,1],u5 [77,26] [6,11,12,16,20,62],([37,1,2,6,3,4],[5,6,47,48,63],[0,1]),([5,1,2,3,4],[1,4,5,6,11],[]),e5 [121] [1,4,11,12,15,16,20,21,64],([0,56,2,51,4],[4,5,8,16],[]),([122,1,2,3,4],[4,6,11],[]),e5 [123] [11,12,15,16,20,21,65],u5 [24,6] [1,11,12,15,16,20,21,63],a5 [56,58] [4,12,16,66,67] [0,1],([0,1,27,3,4],[5,6,16,18,20],[0,1]),e5 [77,99] [5,6,11,15,68],u5 [13,26] [6,12,16,20,22],u5 [82,18] [11,12,16,20,41,69],a5 [88] [4,11,12,14,15,20,70] [0,1],([5,1,34,2,3,4],[4,5,11,45,56,71],[0,1]),a5 [24,26] [1,11,16,62] [0,1],u5 [90,24] [1,11,16,61],a5 [110,18] [6,11,20,72] [1],e5 [13,124] [12,15,16,20,21,22],a5 [24,110] [1,6,11,20,72] [1],([105,65,0,1,2],[5,6,14,21],[0]),([65,37,1,2,3,4],[1,5,6,47,48,73,74],[]),u5 [18,6] [1,11,20,21,63],a5 [18,26] [11,16,62] [0,1],([37,1,2,3,51,4],[1,5,48,74,75],[0]),a5 [18,16] [11,12,16,59] [0,1],u5 [17] [1,6,11,12,16],u5 [59] [1,6,8,11,16],a5 [18,48] [11,15,16,21,53] [0,1],([5,1,2,6,3,4],[5,6,11,46,63],[0,1]),e5 [9] [1,4,5,6,11,12,14,16],a5 [26,53] [6,12,16,20] [0,1],u5 [24,82] [1,11,16,31,69],e5 [126] [4,6,11,12,76],([0,1,128,3,4],[4,5,16],[]),([82,67,0,2,3,4],[5,12,15,16,21,77],[1]),e5 [34] [4,5,11,12,15,20,71],u5 [5,6] [1,6,11,12,15,16,20,63],([79,0,1,3,4],[5,6,34,78],[0]),([13,37,1,2,3,4],[1,6,47,48,54,74],[0]),([129,0,1,2,4],[5,6,21,79,80],[]),([0,80,2,3,4],[6,16,35,36],[0]),([37,1,2,9,3,4],[1,4,5,6,47,55,74],[]),u5 [33,6] [5,6,16,20,28],([0,130,2,3,4],[6,12,16,21],[]),([0,16,6,3,4],[6,16,20,23,25],[0]),u5 [70,6] [1,11,63],u5 [7] [1,11,12,14,15,16,20],u5 [73] [1,5,8,11,12,20],([0,56,2,6,3,4],[5,12,15,16,21,81],[0,1]),e5 [131] [1,6,11,12,15,16,82],u5 [60] [1,5,6,8,11,15,20,21],u5 [25] [11,12,14,15,20,21,83],([13,0,1,6,3,4],[6,12,16,20,21,29,52],[0]),u5 [7,6] [12,15,16,20,21,63],u5 [15,6] [12,15,16,20],([132,1,2,3,4],[1,5,6,11,84],[]),a5 [33] [1,5,6,11,20,21,28] [0,1],u5 [40] [1,8,11,14,15,20],u5 [6,9] [5,6,15,16,20,21],u5 [65,6] [5,6,12,15,16,20,21],u5 [6] [1,6,11,15,16,20,21],([0,26,2,3,48],[6,16,32],[0,1]),e5 [133] [1,6,11,15,16,85],u5 [86] [4,11,14,15,16,20,86],e5 [13] [1,4,6,11,12,15,16,20,21]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_6 : checkNodesBT W_12 g_12 F_12 P_12_6 A_12 B_12_5 6 N_12_6 = true := by decide +kernel
def B_12_6 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_6
set_option maxRecDepth 500000 in
lemma B_12_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 6 xs.toFinset) B_12_6 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_5_ok C_12_6
def U_12_7 : List Nat := ([1,4,5,6,8,11,12,14,15,16]++r 20 4++[53,54,55,59,61,62,63,67,69,72,73,75])
def P_12_7 : BT (Option BoundPool) := buildPoolsSubBT 7 W_12 r_12 S_12 ps_12 U_12_7
def N_12_7 : List NodeSpec := [a5 [65] [1,4,5,6,11,12,16,21,73] [0,1],a5 [44] [1,5,6,11,21] [0,1],a5 [110] [1,5,6,11,16,21,72] [0,1],a5 [9] [4,5,6,55] [0,1],a5 [90] [1,6,11,16,21,61] [0,1],a5 [26] [1,5,6,11,16,21,62] [0,1],a5 [127] [1,4,5,8,11,12,14,16,21] [0,1],a5 [134] [1,4,5,12,14,16,21] [1],([5,1,2,3,4],[1,4,5,6,11],[0,1]),u5 [105] [1,4,5,6,11,14],a5 [77] [1,4,6,11,12,14,16,20,21] [0,1],a5 [18] [1,4,11,12,14,16] [0,1],a5 [24] [1,11,12,14,16,21] [0,1],u5 [135] [1,4,5,6,11,21],a5 [48] [1,5,6,11,16,21,53] [0,1],a5 [13] [1,4,6,11,12,14,16,20,22,54] [0,1],a5 [82] [1,5,11,12,14,16,20,21,23,69] [0,1],([37,1,2,3,4],[1,5,6],[0,1]),a5 [51] [4,5,12,15,16,75] [0,1],a5 [5] [1,4,5,6,11,12,16,21] [0,1],u5 [16] [1,6,11,12,16,21,59],a5 [6] [5,6,11,12,15,16,20,21,63] [0,1],a5 [56] [1,4,5,11,12,16,67] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_7 : checkNodesBT W_12 g_12 F_12 P_12_7 A_12 B_12_6 7 N_12_7 = true := by decide +kernel
def B_12_7 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_7
set_option maxRecDepth 500000 in
lemma B_12_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 7 xs.toFinset) B_12_7 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_6_ok C_12_7
def U_12_8 : List Nat := [1]
def P_12_8 : BT (Option BoundPool) := buildPoolsSubBT 7 W_12 r_12 S_12 ps_12 U_12_8
def N_12_8 : List NodeSpec := [a5 [] [1] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_8 : checkNodesBT W_12 g_12 F_12 P_12_8 A_12 B_12_7 8 N_12_8 = true := by decide +kernel
def B_12_8 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_8
set_option maxRecDepth 500000 in
lemma B_12_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 8 xs.toFinset) B_12_8 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_7_ok C_12_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_12_ok : forestRootCheck r_12 g_12 [(VAR 0,18,19),(VAR 1,12,14),(VAR 2,10,14),(VAR 3,6,14),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_12_in : bucketContainsBT B_12_8 r_12 = true := by decide +kernel
lemma low_12 : Lower r_12 g_12 9 := lower_of_forestBT root_12_ok B_12_8_ok root_12_in
def g_13 := (d 0xfee8fee8fee8fee8)
def r_13 : List Nat := varsOf 15
def p_13 : List Nat := [3,3,5,5,6,6,9,9,10,10,12,12]
def q_13 : List Nat := [2,1,4,1,4,2,8,1,8,2,8,4]
def F_13 : Nat := fullMask 12
set_option maxHeartbeats 0 in
lemma gp_13 : goodPairs g_13 p_13 q_13 := goodPairs_of (by decide +kernel)
def W_13 : BT Decor := buildWiresBT 4 (mkBase p_13 q_13 r_13) [(1,0,1),(1,4,2),(2,5,3),(1,1,2),(1,3,1),(1,3,2),(2,4,3),(1,3,0)]
lemma W_13_ok : btAll (fun x => faithful p_13 q_13 x ∧ x.1 < 2^256) W_13 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_13 : List (List (Nat × Nat)) := [[],[(2,3)],[(1,2)],[(1,3),(2,3)],[(1,2),(2,3)],[(1,3)],[(0,2),(1,2)],[(0,3),(1,3),(2,3)],[(0,2),(1,2),(2,3)],[(0,3),(1,3)],[(0,1),(1,2)],[(0,2),(1,3)]]
def A_13 : BT (List (Nat × Nat)) := btOfList 4 al_13
set_option maxHeartbeats 0 in
lemma A_13_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_13 = g_13) A_13 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_13_0 : Slice r_13 g_13 (subcubeFast 1 0) 4 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_1 : Slice r_13 g_13 (subcubeFast 2 0) 4 := by
  have hc : Lower (varsOf 13) (d 0xfaa0faa0faa0faa0) 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_2 : Slice r_13 g_13 (subcubeFast 4 0) 4 := by
  have hc : Lower (varsOf 11) (d 0xee88ee88ee88ee88) 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_3 : Slice r_13 g_13 (subcubeFast 8 0) 4 := by
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) low_0
def S_13 : BT (Option (Nat × Nat)) := btOfList 2 [some (subcubeFast 1 0,4),some (subcubeFast 2 0,4),some (subcubeFast 4 0,4),some (subcubeFast 8 0,4)]
lemma S_13_ok : btAll (fun o => ∀ p, o = some p → Slice r_13 g_13 p.1 p.2) S_13 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_13_0) (forall_cons (fun _ h => by cases h; exact sl_13_1) (forall_cons (fun _ h => by cases h; exact sl_13_2) (forall_cons (fun _ h => by cases h; exact sl_13_3) (fun _ h => (List.not_mem_nil h).elim)))))
def ps_13 : BT (Option PoolSpec) := btOfList 2 [q 2 [],q 1 [],q 3 [],q 0 []]
def B_13_2 : BT (List (List Nat)) := BT.empty
lemma B_13_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_13 2 xs.toFinset) B_13_2 := .empty
def U_13_3 : List Nat := [0,1]
def P_13_3 : BT (Option BoundPool) := buildPoolsSubBT 2 W_13 r_13 S_13 ps_13 U_13_3
def N_13_3 : List NodeSpec := [([6,0,1,2],[],[]),([0,7,8,9],[0,1],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_13_3 : checkNodesBT W_13 g_13 F_13 P_13_3 A_13 B_13_2 3 N_13_3 = true := by decide +kernel
def B_13_3 : BT (List (List Nat)) := buildBucketsBT W_13 N_13_3
set_option maxRecDepth 500000 in
lemma B_13_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_13 3 xs.toFinset) B_13_3 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok (buildPoolsSubBT_sound S_13_ok) A_13_ok B_13_2_ok C_13_3
def U_13_4 : List Nat := [1,2,3]
def P_13_4 : BT (Option BoundPool) := buildPoolsSubBT 2 W_13 r_13 S_13 ps_13 U_13_4
def N_13_4 : List NodeSpec := [([0,1,2,5,3],[2],[0]),([10,0,1,2,3],[],[]),([0,1,2,11,8],[1,3],[10])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_13_4 : checkNodesBT W_13 g_13 F_13 P_13_4 A_13 B_13_3 4 N_13_4 = true := by decide +kernel
def B_13_4 : BT (List (List Nat)) := buildBucketsBT W_13 N_13_4
set_option maxRecDepth 500000 in
lemma B_13_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_13 4 xs.toFinset) B_13_4 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok (buildPoolsSubBT_sound S_13_ok) A_13_ok B_13_3_ok C_13_4
def U_13_5 : List Nat := (r 0 4)
def P_13_5 : BT (Option BoundPool) := buildPoolsSubBT 2 W_13 r_13 S_13 ps_13 U_13_5
def N_13_5 : List NodeSpec := [([0,1,4,2,3],(r 0 4),[0,1,3,5,7,9])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_13_5 : checkNodesBT W_13 g_13 F_13 P_13_5 A_13 B_13_4 5 N_13_5 = true := by decide +kernel
def B_13_5 : BT (List (List Nat)) := buildBucketsBT W_13 N_13_5
set_option maxRecDepth 500000 in
lemma B_13_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_13 5 xs.toFinset) B_13_5 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok (buildPoolsSubBT_sound S_13_ok) A_13_ok B_13_4_ok C_13_5
def U_13_6 : List Nat := (r 0 4)
def P_13_6 : BT (Option BoundPool) := buildPoolsSubBT 2 W_13 r_13 S_13 ps_13 U_13_6
def N_13_6 : List NodeSpec := [([0,1,2,3],(r 0 4),[0,2,4,6,8,11])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_13_6 : checkNodesBT W_13 g_13 F_13 P_13_6 A_13 B_13_5 6 N_13_6 = true := by decide +kernel
def B_13_6 : BT (List (List Nat)) := buildBucketsBT W_13 N_13_6
set_option maxRecDepth 500000 in
lemma B_13_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_13 6 xs.toFinset) B_13_6 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok (buildPoolsSubBT_sound S_13_ok) A_13_ok B_13_5_ok C_13_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_13_ok : forestRootCheck r_13 g_13 [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,1,9)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_13_in : bucketContainsBT B_13_6 r_13 = true := by decide +kernel
lemma low_13 : Lower r_13 g_13 7 := lower_of_forestBT root_13_ok B_13_6_ok root_13_in
def g_14 := (d 0xfff8e880fff8e880)
def r_14 : List Nat := varsOf 31
def p_14 : List Nat := [7,7,7,11,11,11,13,13,13,14,14,14,19,19,19,20,20,21,21,22,22,24,24,25,25,26,26,28]
def q_14 : List Nat := [6,5,3,10,9,3,12,9,5,12,10,6,18,17,3,16,4,17,5,18,6,16,8,17,9,18,10,12]
def F_14 : Nat := fullMask 28
set_option maxHeartbeats 0 in
lemma gp_14 : goodPairs g_14 p_14 q_14 := goodPairs_of (by decide +kernel)
def W_14 : BT Decor := buildWiresBT 8 (mkBase p_14 q_14 r_14) [(1,2,3),(0,0,1),(1,6,4),(0,5,7),(0,2,3),(1,9,4),(0,6,2),(1,11,4),(0,3,12),(1,3,12),(3,13,14),(1,6,9),(2,16,4),(0,0,5),(2,0,4),(0,0,3),(0,1,2),(1,20,21),(2,22,4),(1,21,4),(1,20,24),(0,0,2),(1,26,4),(0,1,3),(1,28,4),(1,6,2),(1,30,4),(3,6,31),(0,6,3),(1,33,4),(0,2,34),(1,2,34),(3,3,36),(3,6,10),(1,9,7),(1,3,4),(1,2,4),(0,0,41),(1,20,4),(1,37,33),(0,1,41),(0,3,24),(1,3,24),(3,46,47),(1,28,2),(1,49,4),(0,0,50),(0,2,29),(0,3,41),(0,3,7),(1,54,2),(1,3,7),(0,6,5),(1,57,4),(2,6,4),(1,59,9),(3,54,56),(2,2,34),(3,2,34),(0,2,7),(0,3,31),(3,45,3),(2,5,4),(2,2,7),(3,2,7),(0,2,56),(3,54,2),(1,5,4),(1,30,3),(3,6,73),(2,2,3),(1,75,4),(2,5,7),(3,3,7),(3,6,3),(2,30,4),(3,6,2),(1,6,3),(3,28,41),(2,2,4),(3,79,41),(3,33,41),(3,79,40),(3,28,2),(1,88,4),(3,3,31),(0,0,10),(2,1,4),(3,92,0),(3,3,27),(0,1,5),(2,73,4),(1,75,7),(3,21,3),(3,59,5),(2,0,46),(1,79,2),(1,59,75),(1,74,4),(1,37,6),(1,79,4),(3,3,30),(3,79,5),(0,2,43),(2,3,2),(3,109,7),(1,81,4),(1,75,6),(2,112,4),(0,6,40),(3,114,2),(2,3,4),(1,116,2),(3,3,12),(2,0,29),(3,6,72),(1,64,3),(3,26,3),(3,6,117),(3,28,0),(1,26,3),(3,9,7),(1,20,2),(2,127,4),(3,122,40),(3,28,27),(3,20,0),(1,131,4),(1,2,43),(2,2,29),(3,2,29),(1,19,2),(3,28,136),(0,28,41),(3,138,0),(0,0,40),(0,2,40),(3,2,14),(1,142,26),(2,0,10),(2,9,4),(3,145,5),(3,95,0),(3,75,41),(2,0,53),(0,1,40),(3,150,0),(3,84,3),(3,109,40),(3,150,2),(1,84,6),(1,92,3),(1,122,4),(2,1,2),(3,158,0),(1,18,4),(3,33,2),(3,19,3),(0,0,24),(0,26,40),(1,116,26),(1,158,4),(2,1,3),(3,167,2),(1,168,4),(1,125,4),(3,167,0),(1,11,3),(0,26,3),(1,173,4),(0,6,41),(0,21,3),(3,176,0),(0,0,72),(1,167,4),(1,75,20),(3,142,0),(1,92,2),(3,158,40),(3,116,2),(3,116,0),(2,75,4),(3,109,0),(2,26,3),(2,26,4),(2,6,3),(3,92,2),(2,0,9),(2,131,2),(1,131,2),(2,131,4)]
lemma W_14_ok : btAll (fun x => faithful p_14 q_14 x ∧ x.1 < 2^256) W_14 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_14 : List (List (Nat × Nat)) := [[],[(2,3)],[(0,1)],[(0,1),(2,3)]]
def A_14 : BT (List (Nat × Nat)) := btOfList 2 al_14
set_option maxHeartbeats 0 in
lemma A_14_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_14 = g_14) A_14 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_14_0 : Slice r_14 g_14 (subcubeFast 0 1) 7 := by
  have hc : Lower (varsOf 30) (d 0xfffcfcc0fffcfcc0) 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_13
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_14_1 : Slice r_14 g_14 (subcubeFast 0 2) 7 := by
  have hc : Lower (varsOf 29) (d 0xfffafaa0fffafaa0) 7 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_13
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_14_2 : Slice r_14 g_14 (subcubeFast 16 0) 7 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_1
set_option maxHeartbeats 0 in
lemma sl_14_3 : Slice r_14 g_14 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xfff0a000fff0a000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_14_4 : Slice r_14 g_14 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) (d 0xff888800ff888800) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_14_5 : Slice r_14 g_14 (subcubeFast 0 4) 5 := by
  have hc : Lower (varsOf 27) (d 0xffffee88ffffee88) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_14_6 : Slice r_14 g_14 (subcubeFast 8 0) 5 := by
  have hc : Lower (varsOf 23) (d 0xf8f88080f8f88080) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_14_7 : Slice r_14 g_14 (subcubeFast 0 8) 5 := by
  have hc : Lower (varsOf 23) (d 0xffffe8e8ffffe8e8) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_14_8 : Slice r_14 g_14 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xfff0c000fff0c000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_14_9 : Slice r_14 g_14 (subcubeFast 16 8) 4 := by
  exact slice_fast_direct_f (z := 16) (o := 8) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_14_10 : Slice r_14 g_14 (subcubeFast 16 4) 4 := by
  have hc : Lower (varsOf 11) (d 0xee88ee88ee88ee88) 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_14_11 : Slice r_14 g_14 (subcubeFast 16 2) 4 := by
  have hc : Lower (varsOf 13) (d 0xfaa0faa0faa0faa0) 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_14_12 : Slice r_14 g_14 (subcubeFast 8 2) 4 := by
  have hc : Lower (varsOf 21) (d 0xfafaa0a0fafaa0a0) 4 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 8) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_14_13 : Slice r_14 g_14 (subcubeFast 4 2) 4 := by
  have hc : Lower (varsOf 25) (d 0xffaaaa00ffaaaa00) 4 := carry_of (swaps := [(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_14_14 : Slice r_14 g_14 (subcubeFast 16 1) 4 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_14_15 : Slice r_14 g_14 (subcubeFast 8 1) 4 := by
  have hc : Lower (varsOf 22) (d 0xfcfcc0c0fcfcc0c0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 8) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_14_16 : Slice r_14 g_14 (subcubeFast 4 1) 4 := by
  have hc : Lower (varsOf 26) (d 0xffcccc00ffcccc00) 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_14_17 : Slice r_14 g_14 (subcubeFast 2 1) 4 := by
  have hc : Lower (varsOf 28) (d 0xfff0f000fff0f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 2) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_14_18 : Slice r_14 g_14 (subcubeFast 1 2) 4 := by
  have hc : Lower (varsOf 28) (d 0xfff0f000fff0f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_14_19 : Slice r_14 g_14 (identDom 2 3) 6 := by
  have hc : Lower (varsOf 23) (d 0xf8f8e0e0f8f8e0e0) 6 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_2
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
def S_14 : BT (Option (Nat × Nat)) := btOfList 5 [some (subcubeFast 0 1,7),some (subcubeFast 0 2,7),some (subcubeFast 16 0,7),some (subcubeFast 2 0,5),some (subcubeFast 4 0,5),some (subcubeFast 0 4,5),some (subcubeFast 8 0,5),some (subcubeFast 0 8,5),some (subcubeFast 1 0,5),some (subcubeFast 16 8,4),some (subcubeFast 16 4,4),some (subcubeFast 16 2,4),some (subcubeFast 8 2,4),some (subcubeFast 4 2,4),some (subcubeFast 16 1,4),some (subcubeFast 8 1,4),some (subcubeFast 4 1,4),some (subcubeFast 2 1,4),some (subcubeFast 1 2,4),some (identDom 2 3,6)]
lemma S_14_ok : btAll (fun o => ∀ p, o = some p → Slice r_14 g_14 p.1 p.2) S_14 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_14_0) (forall_cons (fun _ h => by cases h; exact sl_14_1) (forall_cons (fun _ h => by cases h; exact sl_14_2) (forall_cons (fun _ h => by cases h; exact sl_14_3) (forall_cons (fun _ h => by cases h; exact sl_14_4) (forall_cons (fun _ h => by cases h; exact sl_14_5) (forall_cons (fun _ h => by cases h; exact sl_14_6) (forall_cons (fun _ h => by cases h; exact sl_14_7) (forall_cons (fun _ h => by cases h; exact sl_14_8) (forall_cons (fun _ h => by cases h; exact sl_14_9) (forall_cons (fun _ h => by cases h; exact sl_14_10) (forall_cons (fun _ h => by cases h; exact sl_14_11) (forall_cons (fun _ h => by cases h; exact sl_14_12) (forall_cons (fun _ h => by cases h; exact sl_14_13) (forall_cons (fun _ h => by cases h; exact sl_14_14) (forall_cons (fun _ h => by cases h; exact sl_14_15) (forall_cons (fun _ h => by cases h; exact sl_14_16) (forall_cons (fun _ h => by cases h; exact sl_14_17) (forall_cons (fun _ h => by cases h; exact sl_14_18) (forall_cons (fun _ h => by cases h; exact sl_14_19) (fun _ h => (List.not_mem_nil h).elim)))))))))))))))))))))
set_option maxRecDepth 500000 in
def ps_14 : BT (Option PoolSpec) := btOfList 9 [q 1 [12296,36889,12297],q 1 [],q 0 [],q 4 [4],q 6 [4],q 19 [],q 19 [4096,20504,16613],q 5 [],q 7 [],q 4 [],q 19 [4096,16410],q 1 [12296,36889],q 8 [],q 3 [],q 1 [16409,16393,167936],q 19 [4096,20507],q 2 [12296,12297],q 0 [12296,16421,12297],q 1 [12296,16421,12297],q 1 [12296,12297],q 19 [4096,20480],q 6 [],q 0 [12313,16409,16397],q 2 [4096,12313],q 0 [8217,12313,12297],q 12 [],q 9 [],q 5 [16386],q 2 [4096,12312,168071],q 19 [4096,16386],q 2 [],q 19 [4096,16409],q 19 [16390,371],q 1 [12297],q 0 [12297],q 0 [8216,16429],q 1 [8216,16429],q 0 [8217,12409,16678],q 2 [12288],q 2 [4096,163864,8651],q 0 [8217,16505,126991],q 15 [],q 3 [12288],q 0 [12296,36889,12297],q 0 [12297,16405,294939],q 19 [4096,20504],q 0 [12312,16517],q 1 [12312,16517],q 2 [4096,12312],q 10 [],q 0 [8196,16469],q 1 [16393],q 0 [16393],q 0 [12393,16489,16397],q 2 [8192,12393],q 2 [12292,168048,555],q 0 [16397,163848],q 2 [8192,163840,163848],q 0 [16489,16397,163848],q 2 [12296,12297,21063],q 19 [20484,383],q 0 [16393,167948],q 2 [167948,217090],q 0 [16393,167951],q 2 [167936],q 2 [167936,167948],q 0 [16393,167940],q 0 [16397,163844],q 2 [163844,603],q 2 [12298,12627],q 0 [12298,16393],q 2 [8206,164279],q 13 [],q 2 [8205,163848],q 0 [12296,12297],q 19 [20480],q 19 [16421],q 1 [16397],q 2 [163844,8795],q 0 [12296,16421],q 0 [12297,20484],q 2 [12296,8231,12589],q 0 [12296,8231,12589],q 0 [12297,16406],q 2 [12297],q 19 [16386],q 17 [],q 1 [371],q 2 [371],q 0 [12296,36889],q 0 [16394,24913],q 1 [12297,20480],q 1 [12296],q 4 [4096],q 3 [16386],q 2 [12296],q 1 [16386],q 1 [12288],q 1 [16394],q 2 [4096,12288],q 2 [167951],q 2 [4096,28687],q 0 [16409,28687],q 0 [12298,24877],q 0 [16398,8657],q 3 [8192],q 1 [8192],q 2 [4096,8192],q 1 [12657],q 0 [16390,12657],q 2 [4096],q 1 [16409],q 0 [16409],q 0 [16409,16393],q 1 [16409,16393],q 14 [],q 1 [12298],q 19 [4096],q 0 [16465],q 1 [12288,16465],q 0 [12298,8495,16421],q 1 [12298,8495,16421],q 2 [4096,12315],q 1 [16393,168051],q 2 [12292,168051],q 0 [8217,12409],q 2 [8192,12395],q 0 [12395,16873],q 2 [8198,635],q 7 [16386],q 0 [8196,86097],q 1 [12288,86097],q 16 [],q 0 [12297,16457],q 1 [12297,20480,16457],q 0 [12315,8509],q 0 [12312,8327],q 1 [12312,8327],q 2 [4096,12312,8327],q 1 [12290,16386,12367],q 2 [12290,12367],q 0 [8217,12298],q 1 [12296,16421],q 2 [4096,8216],q 2 [12292,8307],q 1 [8307,16393],q 8 [12292],q 0 [12292],q 6 [4096],q 2 [8192,163944],q 0 [8219,12297],q 1 [8219,12297],q 2 [4096,8219],q 2 [12288,167951],q 0 [8219,16393],q 0 [12297,20507],q 0 [16398,106961],q 0 [8198,17017],q 0 [8219],q 1 [8219],q 0 [8217,12313],q 0 [8216],q 1 [8216],q 0 [8217,16409],q 2 [12290,167948],q 0 [8219,16709],q 1 [8863,17057],q 7 [17057],q 2 [12294,8863],q 1 [8217,8192],q 0 [12313,16397],q 0 [12313,8205],q 8 [8196],q 0 [8196],q 2 [4,8196],q 1 [16469],q 2 [4096,8217],q 0 [8217,16506],q 0 [8217,16394],q 0 [16489],q 1 [8192,16489],q 7 [16393],q 1 [8219,16393],q 0 [8217,12410],q 1 [8219,16709],q 2 [12294,671],q 0 [8216,12333],q 1 [8216,12333],q 2 [4096,8216,12333],q 0 [16410],q 1 [16410],q 5 [16397],q 2 [8205],q 0 [8205,16397],q 0 [8217,16505],q 7 [16394],q 0 [12297,16394],q 1 [12298,24877],q 0 [12297,16405],q 2 [12292],q 0 [12298,12589],q 0 [12392,17077],q 2 [8196],q 2 [12298],q 2 [4096,167960],q 0 [12292,16497],q 0 [16393,167963],q 2 [4096,167963],q 1 [16393,167963],q 1 [16393,167936],q 2 [4096,167936],q 1 [8307,16737],q 1 [115],q 2 [12292,115],q 1 [8217,12298],q 0 [12298,16685],q 1 [12372,707],q 2 [8196,12372,707],q 2 [8192,12392],q 1 [8192,12392,17077],q 0 [12393,16885],q 0 [8273,16465],q 0 [12393,16397],q 0 [8273,16394],q 2 [12297,294912],q 2 [12288,8273],q 0 [8273,16894],q 2 [8192],q 11 [],q 0 [16489,16397],q 2 [8192,110607],q 0 [16489,110607],q 1 [17053],q 2 [12294],q 0 [12294,17053],q 0 [8207,82221],q 0 [16397,163851],q 2 [163851,571],q 2 [8192,163840],q 0 [16397],q 2 [8192,163848],q 0 [16390,8561],q 2 [8198,164475],q 0 [16398,8659],q 1 [16398,8657],q 0 [16398],q 18 [],q 1 [16393,167951],q 1 [12298,16393],q 1 [12298,16685],q 0 [8206],q 2 [8206,439],q 1 [8206,439],q 1 [12297,16406],q 1 [12297,16405],q 2 [12297,20480],q 1 [8205,16397],q 2 [12290],q 2 [12298,8495],q 0 [12298,8495],q 1 [8307],q 0 [8269],q 1 [16386,8269],q 2 [8269],q 0 [8273],q 1 [12288,8273],q 0 [12294],q 0 [12393],q 1 [8192,12393],q 0 [16394],q 0 [12394],q 0 [12298],q 0 [8217],q 1 [8217],q 0 [16490],q 0 [12314],q 0 [8198],q 1 [635],q 1 [16397,163848],q 2 [163848],q 0 [12296],q 1 [8563],q 2 [8563],q 0 [12392],q 1 [8192,12392],q 0 [8207],q 2 [8198],q 1 [12296,36866],q 2 [12296,36866],q 1 [8863],q 0 [12294,8863],q 0 [8718],q 0 [16909],q 1 [12290,16909],q 1 [12290],q 1 [12298,12589],q 2 [12298,12589],q 0 [16390],q 0 [8717],q 0 [16910],q 2 [12296,8231],q 0 [12296,8231],q 1 [12297,16394]]
def B_14_2 : BT (List (List Nat)) := BT.empty
lemma B_14_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_14 2 xs.toFinset) B_14_2 := .empty
def U_14_3 : List Nat := []
def P_14_3 : BT (Option BoundPool) := buildPoolsSubBT 9 W_14 r_14 S_14 ps_14 U_14_3
def N_14_3 : List NodeSpec := [([0,1,8,10],[],[]),([15,0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_14_3 : checkNodesBT W_14 g_14 F_14 P_14_3 A_14 B_14_2 3 N_14_3 = true := by decide +kernel
def B_14_3 : BT (List (List Nat)) := buildBucketsBT W_14 N_14_3
set_option maxRecDepth 500000 in
lemma B_14_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_14 3 xs.toFinset) B_14_3 :=
  buildBucketsBT_sound (by decide) gp_14 W_14_ok (buildPoolsSubBT_sound S_14_ok) A_14_ok B_14_2_ok C_14_3
def U_14_4 : List Nat := (r 0 7)
def P_14_4 : BT (Option BoundPool) := buildPoolsSubBT 9 W_14 r_14 S_14 ps_14 U_14_4
def N_14_4 : List NodeSpec := [([17,0,1,5,4],[],[]),([18,1,16,5,4],[0],[]),([19,1,16,5,4],[0],[]),([23,6,2,3,4],[],[]),([6,2,3,4,25],[1,2],[]),([6,2,3,27,29],[3,4],[]),([32,0,2,3,29],[],[]),([0,1,35,3,36],[],[1]),([37,0,1,2,34],[],[]),([38,0,1,5,4],[],[]),([0,1,5,4,39],[5],[]),([0,1,2,8,40],[],[]),([37,42,1,2,43],[],[]),([44,0,1,2,4],[],[]),([42,45,2,3,7],[],[]),([48,0,1,2,4],[],[]),([51,1,52,3,4],[],[]),([42,1,2,53,43],[],[]),([0,1,9,8,4],[5],[0]),([0,1,55,4,56],[5],[]),([0,1,9,5,58],[6],[]),([0,1,55,7,40],[],[]),([0,1,60,5,4],[],[]),([61,0,1,2,4],[],[]),([62,63,0,1,3],[],[1]),([0,1,5,7,10],[],[0]),([0,1,64,65,4],[5],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_14_4 : checkNodesBT W_14 g_14 F_14 P_14_4 A_14 B_14_3 4 N_14_4 = true := by decide +kernel
def B_14_4 : BT (List (List Nat)) := buildBucketsBT W_14 N_14_4
set_option maxRecDepth 500000 in
lemma B_14_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_14 4 xs.toFinset) B_14_4 :=
  buildBucketsBT_sound (by decide) gp_14 W_14_ok (buildPoolsSubBT_sound S_14_ok) A_14_ok B_14_3_ok C_14_4
def U_14_5 : List Nat := (r 0 6++r 7 54)
def P_14_5 : BT (Option BoundPool) := buildPoolsSubBT 9 W_14 r_14 S_14 ps_14 U_14_5
def N_14_5 : List NodeSpec := [([37,66,0,1,2,4],[],[]),([59,67,0,1,2,3],[7,8],[]),([59,0,1,9,5,4],[9,10],[0]),([19,1,2,16,3,4],[2,11],[0]),([68,69,0,1,3,4],[],[1]),([0,1,70,3,4,7],[8],[1]),([71,0,1,3,4,7],[],[]),([0,1,2,3,7,72],[12,13],[]),([37,0,1,2,3,7],[],[]),([42,1,2,3,7,41],[14],[0]),([0,1,64,3,4,31],[],[0,1]),([74,0,1,9,5,4],[5,9,15],[]),([0,1,2,3,76,7],[8],[]),e5 [77] [],([78,79,0,1,2,4],[],[]),([80,0,1,2,3,7],[2,7],[]),u5 [60] [],([6,0,1,5,4,10],[16,17,18],[0]),([6,18,1,9,5,4],[7,19,20],[0]),([0,1,2,3,27,29],[9,12,13,21],[0]),([62,0,1,2,3,34],[],[0]),([81,0,1,5,4,40],[9],[]),([0,1,2,5,7,40],[],[0]),([42,1,2,3,43,41],[],[0]),([0,1,2,82,7,40],[12,13,22,23],[]),([83,6,0,2,3,4],[2],[]),([32,0,1,3,5,4],[21],[]),([0,1,30,82,5,4],[12,13,24,25],[]),([19,67,6,1,2,3],[26,27],[]),([84,79,0,1,5,4],[9],[]),([37,33,0,1,2,4],[7],[0]),e5 [85] [13],e5 [86] [28],([19,6,1,9,5,4],[16,19,29],[0]),([87,0,1,2,4,40],[21,30],[]),([0,1,2,3,89,29],[9,13,21],[]),u5 [23] [],([90,0,1,2,4,7],[],[]),([91,0,1,5,4,10],[17],[]),e5 [74] [],([0,1,9,5,4,7],[7,9,31],[0]),([93,0,1,9,5,4],[32],[]),([94,0,1,2,27,40],[21],[]),([81,79,0,1,5,4],[9],[]),([6,18,95,2,3,4],[7,8,33,34],[]),([0,1,2,3,12,14],[9,12,13,35,36],[1]),([96,6,0,1,2,3],[37],[]),([75,0,1,3,7,41],[],[]),e5 [97] [7],([37,98,0,1,2,4],[],[]),e5 [32] [],e5 [99] [],([100,1,2,3,4,24],[],[]),([81,0,1,3,4,72],[12,13],[1]),([0,1,64,3,7,41],[],[1]),e5 [83] [],a5 [8] [1,2,7,9,13] [0,1],([81,0,1,101,3,4],[],[]),u5 [25] [1,2,8,13],e5 [102] [],e5 [103] [1,2],([81,0,1,3,7,41],[12,13,30],[]),e5 [104] [7],([0,1,2,5,4,105],[9],[]),([106,79,0,1,2,4],[],[]),([107,0,1,2,5,4],[9,21],[]),([0,1,108,3,43,41],[38],[]),([67,81,0,1,3,4],[],[]),([37,81,0,1,3,4],[],[]),e5 [110] [9],([0,1,2,3,5,58],[],[0]),u5 [39] [1,2,7,9],([0,1,2,3,111,7],[9,12,13],[]),([81,0,1,82,5,4],[9,12,13],[]),e5 [113] [],([115,0,1,3,4,40],[39],[]),([81,0,1,117,3,4],[],[]),([6,26,2,3,4,29],[3],[0,1]),([118,0,1,2,3,12],[],[1]),([90,6,0,1,2,4],[40],[]),([119,6,2,3,4,29],[41],[]),([6,22,2,3,4],[1,2,42],[0]),([32,20,1,2,3,4],[8],[2]),([37,6,20,1,2,4],[8],[]),([19,112,1,2,3,4],[],[]),([0,1,16,5,4],[0,5,43],[0,2]),u5 [17] [],([6,0,1,16,5,4],[0,9,43],[]),e5 [120] [2,44],([37,20,42,1,2,4],[2,7],[0]),([57,0,1,9,5,4],[5,9,16,45],[0]),([0,1,2,121,4,7],[9],[1]),([74,0,1,2,4,40],[30],[]),([0,1,2,3,7,10],[9,12,13,21],[0]),([94,122,0,1,2,4],[],[]),([84,74,0,1,3,4],[],[]),([112,0,1,3,4,41],[],[]),([0,1,35,2,3,34],[12,13,21,46,47,48],[0]),([75,32,0,1,3,4],[],[]),([6,0,2,3,24,40],[3,4,49,50],[1]),([6,42,45,2,3,4],[7,51,52],[0]),e5 [123] [],([37,124,0,1,2,4],[],[]),([0,1,2,125,27,40],[9,12,53,54],[]),e5 [126] [],([51,1,2,3,4,29],[7],[0]),u5 [38] [],([128,0,1,2,3,43],[2,7],[]),([129,0,1,2,4,40],[21,30],[]),([78,0,1,2,7,40],[21],[]),([88,0,1,3,29,41],[13,21,30],[]),e5 [130] [],([0,1,2,3,132,24],[8],[]),([37,0,1,2,43,41],[21],[0]),([0,1,108,3,4,133],[],[2,3]),([134,135,0,1,3,4],[],[1]),e5 [137] [],([139,1,2,3,4,41],[55],[]),([26,140,1,141,3,4],[8,56,57],[1]),([26,0,143,1,3,4],[7],[]),([67,93,0,1,2,3],[],[]),([144,0,1,5,4,10],[41],[]),([0,1,141,3,27,40],[58],[1]),([0,1,146,4],[25,41,59],[]),([84,0,1,2,3,34],[7,13],[]),([147,0,1,9,5,4],[60],[]),([0,1,2,3,12,40],[9,12,13,21,35,36],[1]),([42,0,1,3,148,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_14_5 : checkNodesBT W_14 g_14 F_14 P_14_5 A_14 B_14_4 5 N_14_5 = true := by decide +kernel
def B_14_5 : BT (List (List Nat)) := buildBucketsBT W_14 N_14_5
set_option maxRecDepth 500000 in
lemma B_14_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_14 5 xs.toFinset) B_14_5 :=
  buildBucketsBT_sound (by decide) gp_14 W_14_ok (buildPoolsSubBT_sound S_14_ok) A_14_ok B_14_4_ok C_14_5
def U_14_6 : List Nat := (r 1 5++r 7 7++r 16 4++[21,23,25,26,27]++r 29 5++[35,36,38,41,42]++r 48 5++[54,56]++r 61 182)
def P_14_6 : BT (Option BoundPool) := buildPoolsSubBT 9 W_14 r_14 S_14 ps_14 U_14_6
def N_14_6 : List NodeSpec := [e5 [149,41] [2,8,12,61,62],a5 [37,42] [8,12,21,63] [0,2],a5 [42,53] [7,8,12,21,26,61,64,65] [1],u5 [42,45] [1,12,13,51,66],e5 [151,40] [1,2,12,67,68],([75,0,1,152,4],[9,21,25,69],[0]),([75,42,0,1,3,4,41],[70],[0]),([0,1,2,153,4,40],[8,21,71],[1,3]),([0,1,141,5,4],[8,72,73],[]),([18,0,1,9,5,4],[7,16,19,26,41,74,75],[0,2]),([0,1,9,5,4,10],[9,16,17,18,25,26,41,76],[]),a5 [154,40] [8,9,77,78] [1],u5 [144,10] [12,41],u5 [91,10] [12,79],u5 [147,5] [1,2,12,80],([0,1,9,5,4],[5,7,25,26,81,82],[]),([19,67,0,1,2,3],[2,7,8,26,27,83,84],[0,2]),([19,0,1,9,5,4],[9,16,19,26,41,85],[0,2]),e5 [75,93] [9,12,32,86,87],u5 [93,5] [7,12,86,88],u5 [6,16] [9,11,89],e5 [6,155] [1,2,9,90],([6,18,1,2,3,5,4],[2,7,8,33,91],[0]),([19,6,1,9,2,3,4],(r 92 5),[0]),([84,6,20,1,2,3,4],[26,42,93,97,98,99],[]),u5 [59,9] [9,13],a5 [37,6] [1,2,7,8,12,13,63,100] [0,2],u5 [78,6] [8,12,13,101,102],e5 [6,112] [1,2,9,103],u5 [6,117] [1,7,12,13,21,26,104],([6,26,1,2,3,4,40],[25,49,77,93,105,106,107],[1,2,3]),a5 [26,156] [8,9,13,25,108,109] [3],a5 [78,7] [8,13,21,110] [0,1],a5 [81,82] [8,9,12,13,25] [0,1],u5 [68,7] [7,9],a5 [7,31] [7,9,111,112] [0,1],([0,1,2,3,7,41],[9,12,13,110,113,114],[0,1,2]),u5 [9,7] [7,8,9,21,110],([19,75,6,1,2,3,4],[12,29,49,94,96,115,116],[0]),([6,0,1,9,5,4],[7,9,16,19,25,74,117],[0,2]),a5 [108,43] [7,9,12,21,38,118,119] [0,3],e5 [10] [9,12,13,26,120,121],a5 [84,79] [9,21,49,122] [0,1],u5 [83] [2,7,12,13,123,124],u5 [6,73] [1,110,125],a5 [26,157] [7,8,9,12,126,127] [3],e5 [159,40] [7,8,12,72,86,128],([19,6,1,2,3,5,4],[12,27,33,84,94,96,115,129],[0]),u5 [22] [25,30,130,131,132],e5 [160] [7,8,12,13,133,134],u5 [6,101] [1,7,12,13,135],([161,0,1,3,4],[9,21,136,137,138],[]),([145,0,1,5,4],[9,25,26],[0]),([131,1,2,162,4],[12,21,25,129,139,140],[]),([75,6,0,1,30,3,4],[9,12,13,141],[]),e5 [163,24] [12,50],u5 [6,10] [12,13,79,95,142],a5 [12] [8,9,21,35,36,143] [0,1],([88,0,1,3,4,41],[7,9,21,30,132,144,145],[3]),([6,26,28,2,3,4],[1,2,93,105,106,146,147,148],[0,1,3]),a5 [164,40] [21,30,77,149] [3],([81,0,1,3,5,4],[9,21,150,151],[0,1]),a5 [81,7] [7,9,110,152] [0,1],e5 [153] [1,2,8,12,13,21],([37,20,0,1,2,4],[2,7,8,63,153],[0,1,2]),([81,6,0,1,3,4,41],[7,12,13,110,152,154],[0]),a5 [74] [1,7,9,13,30,155] [0,1],e5 [26,165] [21,156],e5 [131,166] [8,49,72,157],a5 [81,40] [8,9,12,13,21,152,158,159] [0,1],([37,20,0,1,2,4,41],[7,21,52,63,153],[0]),u5 [30,82] [7,8,12,13,25,72,160],u5 [18,95] [1,12,13,33,80],a5 [11,40] [8,9,12,13,21,30,143,161,162] [0,1],a5 [30,7] [7,12,13,72,110,163] [0,1],([131,0,1,2,53,4,41],[7,8,164],[]),u5 [6,111] [1,7,12,13,152,165],u5 [74,5] [7,9,13,21],e5 [74,6] [1,2,7,155],e5 [169] [2,7,9,12,166,167,168],([0,1,5,4,10],[9,17,18,26],[0,2]),([26,1,30,3,4],[7,12,49,169],[]),([6,0,1,2,82,4,40],[12,13,21,23,170],[0]),([6,0,1,2,82,5,4],[12,13,21,72,171],[0]),([19,6,21,2,3,4],[1,3,25,41,49,94,96,115,172,173,174],[]),a5 [64,7] [7,9,12,13,110,111,112] [0,1],([6,0,2,3,4,24],[3,4,13,49,50,174,175],[0,1]),u5 [80,6] [1,2,9,12,13,176,177],([84,6,0,1,30,3,4],[9,12,13,178],[]),a5 [27,170] [8,12,21,49,179,180] [1,3],([81,0,1,3,4,41],[9,30,152,154,181,182],[0,1]),u5 [106,6] [8,12,13,72,183],u5 [84,33] [9,13,48,49],u5 [57,5] [7,9,21,84],a5 [5,7] [7,8,9,21,110] [0,1],a5 [111] [8,9,21,165,184] [1],e5 [84,171] [9,49,185],a5 [75,7] [7,8,9,12,13,21,31,110,111,112] [0,1],([0,1,2,172,4],[8,9,186,187,188],[]),u5 [59,75] [7,9,10,12,13,189,190],u5 [119,29] [12,41],([6,0,1,2,5,4,40],[8,72,110,191,192,193],[0,1]),a5 [16] [11,13,25,30,72,89,93,148] [0,2],u5 [6,31] [1,25,194],([84,6,0,1,3,5,4],[9,25,49,195,196],[0]),a5 [112] [1,7,9,13,30,72,93,103,197] [0,2],a5 [6,72] [1,7,8,12,13,84,198] [0,1],a5 [88,29] [7,9,144,199] [0,3],u5 [6,5] [1,7,8,9,12,13,21,25,200],([0,1,2,3,174],[9,12,21,25,201],[]),u5 [131,24] [8,12,41,50,202],([81,6,0,1,3,5,4],[7,12,13,25,150],[0]),([75,6,0,1,3,4,41],[7,9,70,203],[0]),u5 [59,5] [7,8,9,13,21,110],a5 [175,41] [9,26,30,204] [0,1],([0,1,2,3,12],[9,35,36],[0,1]),a5 [26,29] [7,9,12,199,205] [0,1,3],a5 [32] [1,8,13,21,206,207,208] [0,2],e5 [83,28] [1,7,13,123],e5 [32,6] [1,2,7,206],([6,42,1,2,3,4,41],[2,7,51,209,210],[0]),e5 [32,41] [9,13,207],e5 [89] [7,21,132,211],u5 [124,41] [7,12,13,41,212,213],([75,0,1,30,3,4],[7,21,49,72,141,214],[]),u5 [6,76] [1,9,12,13,26,49,215],e5 [84,124] [9,12,49,147,213],([177,1,2,3,4],[9,12,21,216,217],[]),e5 [174] [9,12,25,201,218,219],a5 [26,170] [7,86,106,220] [3],a5 [127,43] [7,38,132,221] [0,1],([26,0,1,2,125,4,40],[9,12,21,54,222],[0]),([84,20,0,1,127,3,4],[9,21,223],[]),([178,1,2,3,4],[7,8,12,224],[]),u5 [128,20] [9,225,226],a5 [67,6] [1,2,7,12,13,26,83] [0,1,2],a5 [94,27] [8,9,21,227] [0,3],a5 [88,40] [9,21,77,191,228] [1],([88,0,28,1,3,4,41],[7,13,21,144,145,199],[0]),([0,1,2,3,27,40],[9,12,21,49,180,229],[0,1,2]),u5 [134,29] [7,9],([26,0,1,2,3,27,40],[9,12,41,49,229],[0,3]),u5 [94,26] [8,9,230,231],a5 [26,179] [9,13,25,26,232,233,234] [2],e5 [180] [25,26,30,235],e5 [181,40] [8,9,12,21,30,41,236,237],a5 [37,26] [8,9,63,115] [2],([6,0,1,2,3,7,41],[12,13,30,72,113],[0,1]),([26,140,1,2,3,4,40],[2,8,49,238],[0,1]),e5 [83,41] [9,13,124],a5 [81,79] [7,9,21] [0,1],([26,0,1,141,3,4,40],[7,8,56,239,240],[0]),e5 [131,182] [7,8,12,41,241],e5 [183,40] [13,242],u5 [93,9] [9,12,86]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_14_6 : checkNodesBT W_14 g_14 F_14 P_14_6 A_14 B_14_5 6 N_14_6 = true := by decide +kernel
def B_14_6 : BT (List (List Nat)) := buildBucketsBT W_14 N_14_6
set_option maxRecDepth 500000 in
lemma B_14_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_14 6 xs.toFinset) B_14_6 :=
  buildBucketsBT_sound (by decide) gp_14 W_14_ok (buildPoolsSubBT_sound S_14_ok) A_14_ok B_14_5_ok C_14_6
def U_14_7 : List Nat := ([1,2,5,7,8,9,12,13,16,19,21,25,26,27,30,33,34,38,41,49,51,52,54,56,63,64,70,72,74,77,79]++r 83 6++[91,92,93]++r 95 4++[100]++r 104 4++[110,111,112,115,116,117,128,132,142,143,144,147,152,158,159,161,168,176,179,180,189,193,196,198,199,200,202,203,209,212,213,215,218,225,227,233,239]++r 243 60)
def P_14_7 : BT (Option BoundPool) := buildPoolsSubBT 9 W_14 r_14 S_14 ps_14 U_14_7
def N_14_7 : List NodeSpec := [a5 [184] [2,12,21,26,30,72,243] [1],u5 [117] [7,12,13,21,26,104,244],e5 [185] [1,2,7,9,12,13,21,26,245,246],a5 [37,41] [7,9,21,26,30,51,52,63,247] [0,1,2,3],a5 [37] [1,2,7,8,9,12,13,30,63,100,247] [0,2],([84,0,1,2,3,41],[7,9,30,72,132],[]),e5 [42] [1,2,7,8,12,13,21,52,64,132,246],([84,75,0,1,3,4],[9,21,26,72,203],[0]),([75,0,1,3,4,41],[7,9,26,70,248],[0,1,2]),e5 [186] [1,2,8,9,12,13,72,203],u5 [76] [9,12,13,26,49,215,249],e5 [187] [1,2,7,12,13,41,132,246,250,251,252],a5 [67] [1,2,7,12,13,26,30,49,83,253] [0,2],a5 [72] [1,2,7,8,12,13,84,198,254] [0,2],([75,0,1,2,5,4],[2,5,9,26,34,72],[0]),u5 [18] [1,2,7,8,12,13,30,34,41,91,132,246,255],([0,1,2,5,4,40],[8,30,49,193,256],[0]),e5 [9,41] [7,9,26,51,52,72,95,132],e5 [9,5] [5,9,25,26,33,34,41],a5 [131,21] [8,13,25,41,132,202,246,257] [0,2],a5 [26,41] [7,9,26,41,51,52,72,115] [0,3],([0,1,9,2,5,4],[5,7,16,49,72,74],[]),a5 [26,28] [41,72,147,199,227] [0,1,3],([19,131,1,2,3,4],[2,12,21,26,49,246,257],[0]),([6,26,1,2,3,4],[2,7,12,25,72,93,105,106,107],[0,1,2]),u5 [9] [2,9,12,25,41,258,259],a5 [27] [8,9,13,21,49,179,180,227] [0,1,2,3],u5 [88] [1,2,7,9,12,21,30,132,144,260],a5 [84,20] [8,9,21,26,38,49,86,97,98,132] [0,1,2],a5 [136] [1,7,8,13,21,261,262,263] [2,3],a5 [88,28] [7,41,72,144,147,199] [0,3],e5 [127] [7,9,13,21,25,49,225,264,265],([131,20,1,2,3,4],[2,8,25,26],[]),a5 [19,167] [8,12,13,25,26,49,72,115,132,233,246,266] [2],a5 [19,5] [7,8,9,12,21,26,27,33,34,49,84,86,96,115] [0,2],a5 [26,125] [9,41,54,72,267,268] [0,1],a5 [84,6] [1,2,9,13,25,26,49,72,110,269] [0,1,2],e5 [75] [1,2,5,7,9,12,13,26,72],e5 [188] [1,8,9,13,26,270],a5 [81] [1,8,9,13,21,30,152,158,159] [0,1],a5 [75,41] [7,9,21,51,52,72,132,203] [1],a5 [75,6] [1,2,8,9,12,13,21,25,41,72,110,117,203,271] [0,2],a5 [11] [8,9,13,21,30,143,161] [0,1],a5 [30] [1,7,8,21,49,272,273] [0,2],a5 [19,21] [1,12,13,25,26,41,115,132,202,246] [0,2],e5 [189] [1,8,9,12,13,21,72,227,274],a5 [26,27] [9,41,49,72,179,180,227] [0,1,3],e5 [190] [7,8,9,13,26,275],a5 [159] [1,2,8,12,13,21,72,86,128,276,277] [0,1],a5 [141,40] [8,49,56,77,239,278,279] [0,1,2,3],a5 [7] [7,8,9,13,21,110,111,112] [0,1],a5 [81,6] [2,7,12,13,25,72,110,152,158] [0,1],a5 [6,7] [12,13,25,72,110,111,112] [0,1],([19,6,1,2,3,4],[12,25,26,30,49,72,96,110],[0,1]),a5 [6,9] [7,9,13,25,72,92,93,95,110,280] [0,2],e5 [26,5] [9,21,33,34,41,49,72],a5 [6,30] [12,13,25,72,176,272,273] [0,1],a5 [59] [7,8,9,13,21,110,189] [0,1],a5 [191] [1,8,21,30,132,281,282] [3],a5 [6,5] [7,8,9,12,13,21,25,33,34,41,72,84,110,132] [0,1,2],a5 [42,41] [7,26,51,52,64,209] [0,1,3],a5 [173] [1,9,12,13,21,25,30,218,283,284] [0,2],u5 [75,20] [2,7,8,21,25,26,97,285],u5 [124] [2,7,9,12,13,41,147,212,213],([0,1,9,5,4],[5,7,9,16,19,25,26,41,74],[0,2]),a5 [26,40] [8,9,12,21,41,49,77,86,106,227,239] [0,1,3],a5 [18,5] [7,9,26,33,34,84,91] [0,2],u5 [9,10] [9,25,26,41,49,79,142],a5 [6,41] [7,9,12,13,25,26,51,52,72,110,132] [0,1,2,3],a5 [131,158] [7,8,13,25,41,72,86,132,246,257,276,286] [0,3],e5 [192] [1,2,9,12,13,41,72,132,246,280,287,288],u5 [168] [2,9,12,25,132,168,289,290],e5 [193] [1,7,8,13,26,291],a5 [19,75] [7,9,12,26,41,49,85,86,96,115,116,271] [0,2],u5 [141] [2,7,8,12,30,72,132,279],a5 [132] [7,9,13,26,292,293] [2,3],a5 [131,41] [7,9,26,41,51,52,86,132,294] [0,3],u5 [5] [7,8,9,12,13,21,26,200,295,296],a5 [84,131] [8,9,26,49,86,98,132,269,294] [2],a5 [93] [2,7,8,9,12,13,21,87,88,297] [0,1],e5 [194] [1,13,41,49,298],a5 [19,9] [7,9,12,26,41,49,86,92,95,96,115] [0,2],e5 [195] [1,7,8,9,13,246,257,299],([75,0,1,9,3,4],[2,5,9,21,25,26,300,301],[0]),a5 [10] [9,12,13,21,26,49,79,95,142] [0,2],([84,0,1,3,5,4],[9,21,26,49,196,302],[0]),u5 [145] [1,2,9,12,13,21,25,95]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_14_7 : checkNodesBT W_14 g_14 F_14 P_14_7 A_14 B_14_6 7 N_14_7 = true := by decide +kernel
def B_14_7 : BT (List (List Nat)) := buildBucketsBT W_14 N_14_7
set_option maxRecDepth 500000 in
lemma B_14_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_14 7 xs.toFinset) B_14_7 :=
  buildBucketsBT_sound (by decide) gp_14 W_14_ok (buildPoolsSubBT_sound S_14_ok) A_14_ok B_14_6_ok C_14_7
def U_14_8 : List Nat := [1,2,5,7,8,9,12,13,25,26,30,33,34,41,49,51,52,72,84,92,95,96,98,106,110,115,116,132,227,257,269,271,280,294]
def P_14_8 : BT (Option BoundPool) := buildPoolsSubBT 9 W_14 r_14 S_14 ps_14 U_14_8
def N_14_8 : List NodeSpec := [a5 [84] [1,2,9,30,49,98,269] [0,1,2,3],a5 [41] [7,30,51,52] [0,1,2,3],a5 [5] [7,8,26,33,34,49,84] [0,1,2,3],a5 [75] [1,2,5,8,9,26,30,72,116,132,271] [0,1,2,3],a5 [19] [1,2,12,30,96,115] [0,1,2,3],a5 [131] [1,2,8,30,41,257,294] [0,2,3],a5 [26] [1,2,9,30,72,106,227] [0,1,2,3],a5 [9] [9,25,41,72,92,95,132,280] [0,1,2],a5 [6] [1,2,13,30,110] [0,1,2,3]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_14_8 : checkNodesBT W_14 g_14 F_14 P_14_8 A_14 B_14_7 8 N_14_8 = true := by decide +kernel
def B_14_8 : BT (List (List Nat)) := buildBucketsBT W_14 N_14_8
set_option maxRecDepth 500000 in
lemma B_14_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_14 8 xs.toFinset) B_14_8 :=
  buildBucketsBT_sound (by decide) gp_14 W_14_ok (buildPoolsSubBT_sound S_14_ok) A_14_ok B_14_7_ok C_14_8
def U_14_9 : List Nat := [1,2,30]
def P_14_9 : BT (Option BoundPool) := buildPoolsSubBT 9 W_14 r_14 S_14 ps_14 U_14_9
def N_14_9 : List NodeSpec := [a5 [] [1,2,30] [0,1,2,3]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_14_9 : checkNodesBT W_14 g_14 F_14 P_14_9 A_14 B_14_8 9 N_14_9 = true := by decide +kernel
def B_14_9 : BT (List (List Nat)) := buildBucketsBT W_14 N_14_9
set_option maxRecDepth 500000 in
lemma B_14_9_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_14 9 xs.toFinset) B_14_9 :=
  buildBucketsBT_sound (by decide) gp_14 W_14_ok (buildPoolsSubBT_sound S_14_ok) A_14_ok B_14_8_ok C_14_9
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_14_ok : forestRootCheck r_14 g_14 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_14_in : bucketContainsBT B_14_9 r_14 = true := by decide +kernel
lemma low_14 : Lower r_14 g_14 10 := lower_of_forestBT root_14_ok B_14_9_ok root_14_in
def g_15 := (d 0xfcc08000fcc08000)
def r_15 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_15 : Lower r_15 g_15 8 := by
  have hc : Lower (varsOf 30) (d 0xfcc0c000fcc0c000) 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,14,15)]) (by decide +kernel) hc
def g_16 := (d 0xfffefc80fffefc80)
def r_16 : List Nat := varsOf 31
def p_16 : List Nat := [7,7,7,10,10,11,11,12,12,13,13,14,17,17,18,18,19,20,20,21,22,24,24,25]
def q_16 : List Nat := [6,5,3,8,2,9,3,8,4,9,5,6,16,1,16,2,3,16,4,5,6,16,8,9]
def F_16 : Nat := fullMask 24
set_option maxHeartbeats 0 in
lemma gp_16 : goodPairs g_16 p_16 q_16 := goodPairs_of (by decide +kernel)
def W_16 : BT Decor := buildWiresBT 4 (mkBase p_16 q_16 r_16) [(1,1,2),(1,5,4),(3,3,6),(1,1,4),(3,2,8),(2,5,4),(1,2,4)]
lemma W_16_ok : btAll (fun x => faithful p_16 q_16 x ∧ x.1 < 2^256) W_16 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_16 : List (List (Nat × Nat)) := [[],[(1,2)]]
def A_16 : BT (List (Nat × Nat)) := btOfList 1 al_16
set_option maxHeartbeats 0 in
lemma A_16_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_16 = g_16) A_16 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_16_0 : Slice r_16 g_16 (identDom 0 2) 7 := by
  have hc : Lower (varsOf 27) (d 0xffeeee88ffeeee88) 7 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_13
  exact slice_ident (u := 0) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_1 : Slice r_16 g_16 (identDom 0 1) 7 := by
  have hc : Lower (varsOf 29) (d 0xfffafaa0fffafaa0) 7 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_13
  exact slice_ident (u := 0) (v := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_2 : Slice r_16 g_16 (subcubeFast 8 0) 6 := by
  have hc : Lower (varsOf 23) (d 0xfefe8080fefe8080) 6 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_3 : Slice r_16 g_16 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) (d 0xfffffcc0fffffcc0) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_4 : Slice r_16 g_16 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffaf000fffaf000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_5 : Slice r_16 g_16 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) (d 0xffeecc00ffeecc00) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_6 : Slice r_16 g_16 (subcubeFast 16 0) 5 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_10
set_option maxHeartbeats 0 in
lemma sl_16_7 : Slice r_16 g_16 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xfffcfc00fffcfc00) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_8 : Slice r_16 g_16 (subcubeFast 16 1) 4 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 1) (by decide +kernel) hc
def S_16 : BT (Option (Nat × Nat)) := btOfList 4 [some (identDom 0 2,7),some (identDom 0 1,7),some (subcubeFast 8 0,6),some (subcubeFast 0 1,5),some (subcubeFast 2 0,5),some (subcubeFast 4 0,5),some (subcubeFast 16 0,5),some (subcubeFast 1 0,5),some (subcubeFast 16 1,4)]
lemma S_16_ok : btAll (fun o => ∀ p, o = some p → Slice r_16 g_16 p.1 p.2) S_16 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_16_0) (forall_cons (fun _ h => by cases h; exact sl_16_1) (forall_cons (fun _ h => by cases h; exact sl_16_2) (forall_cons (fun _ h => by cases h; exact sl_16_3) (forall_cons (fun _ h => by cases h; exact sl_16_4) (forall_cons (fun _ h => by cases h; exact sl_16_5) (forall_cons (fun _ h => by cases h; exact sl_16_6) (forall_cons (fun _ h => by cases h; exact sl_16_7) (forall_cons (fun _ h => by cases h; exact sl_16_8) (fun _ h => (List.not_mem_nil h).elim))))))))))
def ps_16 : BT (Option PoolSpec) := btOfList 4 [q 0 [],q 3 [],q 2 [],q 0 [4105],q 4 [],q 6 [],q 1 [16389],q 2 [16389],q 8 [],q 5 [],q 1 [8197],q 0 [8197],q 2 [8197],q 1 [],q 7 []]
def B_16_3 : BT (List (List Nat)) := BT.empty
lemma B_16_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 3 xs.toFinset) B_16_3 := .empty
def U_16_4 : List Nat := []
def P_16_4 : BT (Option BoundPool) := buildPoolsSubBT 4 W_16 r_16 S_16 ps_16 U_16_4
def N_16_4 : List NodeSpec := [([7,0,1,2,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_16_4 : checkNodesBT W_16 g_16 F_16 P_16_4 A_16 B_16_3 4 N_16_4 = true := by decide +kernel
def B_16_4 : BT (List (List Nat)) := buildBucketsBT W_16 N_16_4
set_option maxRecDepth 500000 in
lemma B_16_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 4 xs.toFinset) B_16_4 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok (buildPoolsSubBT_sound S_16_ok) A_16_ok B_16_3_ok C_16_4
def U_16_5 : List Nat := (r 0 6)
def P_16_5 : BT (Option BoundPool) := buildPoolsSubBT 4 W_16 r_16 S_16 ps_16 U_16_5
def N_16_5 : List NodeSpec := [e5 [9] [],e5 [10] [],u5 [6] [0,1,2],([0,1,5,3,4,11],[3,4,5],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_16_5 : checkNodesBT W_16 g_16 F_16 P_16_5 A_16 B_16_4 5 N_16_5 = true := by decide +kernel
def B_16_5 : BT (List (List Nat)) := buildBucketsBT W_16 N_16_5
set_option maxRecDepth 500000 in
lemma B_16_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 5 xs.toFinset) B_16_5 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok (buildPoolsSubBT_sound S_16_ok) A_16_ok B_16_4_ok C_16_5
def U_16_6 : List Nat := ([1]++r 4 9)
def P_16_6 : BT (Option BoundPool) := buildPoolsSubBT 4 W_16 r_16 S_16 ps_16 U_16_6
def N_16_6 : List NodeSpec := [a5 [8] ([1,4]++r 6 4) [0,1],a5 [5] ([1,4,5]++r 9 4) [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_16_6 : checkNodesBT W_16 g_16 F_16 P_16_6 A_16 B_16_5 6 N_16_6 = true := by decide +kernel
def B_16_6 : BT (List (List Nat)) := buildBucketsBT W_16 N_16_6
set_option maxRecDepth 500000 in
lemma B_16_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 6 xs.toFinset) B_16_6 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok (buildPoolsSubBT_sound S_16_ok) A_16_ok B_16_5_ok C_16_6
def U_16_7 : List Nat := [0,1,2,4,5,9,13,14]
def P_16_7 : BT (Option BoundPool) := buildPoolsSubBT 4 W_16 r_16 S_16 ps_16 U_16_7
def N_16_7 : List NodeSpec := [a5 [] [0,1,2,4,5,9,13,14] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_16_7 : checkNodesBT W_16 g_16 F_16 P_16_7 A_16 B_16_6 7 N_16_7 = true := by decide +kernel
def B_16_7 : BT (List (List Nat)) := buildBucketsBT W_16 N_16_7
set_option maxRecDepth 500000 in
lemma B_16_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 7 xs.toFinset) B_16_7 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok (buildPoolsSubBT_sound S_16_ok) A_16_ok B_16_6_ok C_16_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_16_ok : forestRootCheck r_16 g_16 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,2,10),(VAR 4,1,17)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_16_in : bucketContainsBT B_16_7 r_16 = true := by decide +kernel
lemma low_16 : Lower r_16 g_16 8 := lower_of_forestBT root_16_ok B_16_7_ok root_16_in
def g_17 := (d 0xffc8e080ffc8e080)
def r_17 : List Nat := varsOf 31
def p_17 : List Nat := [7,7,7,13,13,13,14,14,14,15,19,19,19,22,22,22,23,24,24,25,25,26,26,27,28,28,29]
def q_17 : List Nat := [6,5,3,12,9,5,12,10,6,11,18,17,3,20,18,6,21,16,8,17,9,18,10,11,20,12,21]
def F_17 : Nat := fullMask 27
set_option maxHeartbeats 0 in
lemma gp_17 : goodPairs g_17 p_17 q_17 := goodPairs_of (by decide +kernel)
def W_17 : BT Decor := buildWiresBT 4 (mkBase p_17 q_17 r_17) [(1,3,4),(3,0,5),(1,0,3),(2,7,4),(1,7,4),(1,0,4),(0,1,2)]
lemma W_17_ok : btAll (fun x => faithful p_17 q_17 x ∧ x.1 < 2^256) W_17 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_17 : List (List (Nat × Nat)) := [[],[(1,2),(3,4)]]
def A_17 : BT (List (Nat × Nat)) := btOfList 1 al_17
set_option maxHeartbeats 0 in
lemma A_17_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_17 = g_17) A_17 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_17_0 : Slice r_17 g_17 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffaf0a0fffaf0a0) 5 := carry_of (swaps := [(1,4),(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_1 : Slice r_17 g_17 (subcubeFast 0 4) 5 := by
  have hc : Lower (varsOf 27) (d 0xffccee88ffccee88) 5 := carry_of (swaps := [(1,2),(2,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_2 : Slice r_17 g_17 (subcubeFast 8 0) 5 := by
  have hc : Lower (varsOf 23) (d 0xc8c88080c8c88080) 5 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_3 : Slice r_17 g_17 (subcubeFast 16 0) 5 := by
  have hc : Lower (varsOf 15) (d 0xe080e080e080e080) 5 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_4 : Slice r_17 g_17 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xffc0c000ffc0c000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_5 : Slice r_17 g_17 (subcubeFast 8 2) 4 := by
  have hc : Lower (varsOf 21) (d 0xfafaa0a0fafaa0a0) 4 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 8) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_6 : Slice r_17 g_17 (subcubeFast 1 2) 4 := by
  have hc : Lower (varsOf 28) (d 0xfff0f000fff0f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_7 : Slice r_17 g_17 (subcubeFast 1 4) 4 := by
  have hc : Lower (varsOf 26) (d 0xffcccc00ffcccc00) 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_8 : Slice r_17 g_17 (subcubeFast 16 4) 4 := by
  have hc : Lower (varsOf 11) (d 0xee88ee88ee88ee88) 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_9 : Slice r_17 g_17 (identDom 1 4) 6 := by
  have hc : Lower (varsOf 15) (d 0xecc8ecc8ecc8ecc8) 6 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_2
  exact slice_ident (u := 1) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_10 : Slice r_17 g_17 (identDom 2 3) 6 := by
  have hc : Lower (varsOf 23) (d 0xf8f8e0e0f8f8e0e0) 6 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_2
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
def S_17 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 0 2,5),some (subcubeFast 0 4,5),some (subcubeFast 8 0,5),some (subcubeFast 16 0,5),some (subcubeFast 1 0,5),some (subcubeFast 8 2,4),some (subcubeFast 1 2,4),some (subcubeFast 1 4,4),some (subcubeFast 16 4,4),some (identDom 1 4,6),some (identDom 2 3,6)]
lemma S_17_ok : btAll (fun o => ∀ p, o = some p → Slice r_17 g_17 p.1 p.2) S_17 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_17_0) (forall_cons (fun _ h => by cases h; exact sl_17_1) (forall_cons (fun _ h => by cases h; exact sl_17_2) (forall_cons (fun _ h => by cases h; exact sl_17_3) (forall_cons (fun _ h => by cases h; exact sl_17_4) (forall_cons (fun _ h => by cases h; exact sl_17_5) (forall_cons (fun _ h => by cases h; exact sl_17_6) (forall_cons (fun _ h => by cases h; exact sl_17_7) (forall_cons (fun _ h => by cases h; exact sl_17_8) (forall_cons (fun _ h => by cases h; exact sl_17_9) (forall_cons (fun _ h => by cases h; exact sl_17_10) (fun _ h => (List.not_mem_nil h).elim))))))))))))
def ps_17 : BT (Option PoolSpec) := btOfList 4 [q 9 [],q 0 [],q 10 [],q 1 [],q 2 [],q 3 [],q 4 [],q 5 [],q 8 [],q 6 [],q 0 [12289],q 7 []]
def B_17_4 : BT (List (List Nat)) := BT.empty
lemma B_17_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 4 xs.toFinset) B_17_4 := .empty
def U_17_5 : List Nat := (r 0 6)
def P_17_5 : BT (Option BoundPool) := buildPoolsSubBT 4 W_17 r_17 S_17 ps_17 U_17_5
def N_17_5 : List NodeSpec := [e5 [6] [],e5 [8] [],e5 [9] (r 0 4),([1,2,3,7,4,10],[4,5],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_5 : checkNodesBT W_17 g_17 F_17 P_17_5 A_17 B_17_4 5 N_17_5 = true := by decide +kernel
def B_17_5 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_5
set_option maxRecDepth 500000 in
lemma B_17_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 5 xs.toFinset) B_17_5 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_4_ok C_17_5
def U_17_6 : List Nat := (r 3 9)
def P_17_6 : BT (Option BoundPool) := buildPoolsSubBT 4 W_17 r_17 S_17 ps_17 U_17_6
def N_17_6 : List NodeSpec := [u5 [5] [6,7,8],e5 [11] (r 3 7),u5 [7] (r 4 4++[10,11])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_6 : checkNodesBT W_17 g_17 F_17 P_17_6 A_17 B_17_5 6 N_17_6 = true := by decide +kernel
def B_17_6 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_6
set_option maxRecDepth 500000 in
lemma B_17_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 6 xs.toFinset) B_17_6 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_5_ok C_17_6
def U_17_7 : List Nat := (r 0 10++[11])
def P_17_7 : BT (Option BoundPool) := buildPoolsSubBT 4 W_17 r_17 S_17 ps_17 U_17_7
def N_17_7 : List NodeSpec := [a5 [] (r 0 10++[11]) [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_7 : checkNodesBT W_17 g_17 F_17 P_17_7 A_17 B_17_6 7 N_17_7 = true := by decide +kernel
def B_17_7 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_7
set_option maxRecDepth 500000 in
lemma B_17_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 7 xs.toFinset) B_17_7 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_6_ok C_17_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_17_ok : forestRootCheck r_17 g_17 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,5,13),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_17_in : bucketContainsBT B_17_7 r_17 = true := by decide +kernel
lemma low_17 : Lower r_17 g_17 8 := lower_of_forestBT root_17_ok B_17_7_ok root_17_in
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
  have hc : Lower (varsOf 30) (d 0xfffcc000fffcc000) 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_1 : Slice r_18 g_18 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xffc0c000ffc0c000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_2 : Slice r_18 g_18 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffaf000fffaf000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_3 : Slice r_18 g_18 (subcubeFast 0 4) 5 := by
  have hc : Lower (varsOf 27) (d 0xffeecc00ffeecc00) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_4 : Slice r_18 g_18 (subcubeFast 8 0) 5 := by
  have hc : Lower (varsOf 23) (d 0xe8e80000e8e80000) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_5
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
def g_19 := (d 0xfef8f800fef8f800)
def r_19 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_19 : Lower r_19 g_19 8 := by
  have hc : Lower (varsOf 27) (d 0xee888800ee888800) 7 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_1
  exact lift_of_f (z := 4) (o := 0) (essPairs := [(VAR 2,8,12)]) (by decide +kernel) hc
def g_20 := (d 0xffa8c000ffa8c000)
def r_20 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_20 : Lower r_20 g_20 7 := by
  have hc : Lower (varsOf 30) (d 0xfffcc000fffcc000) 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,18,19)]) (by decide +kernel) hc
def g_21 := (d 0xfefefc80fefefc80)
def r_21 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_21 : Lower r_21 g_21 7 := by
  have hc : Lower (varsOf 23) (d 0xfefe8080fefe8080) 6 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_2
  exact lift_of_f (z := 8) (o := 0) (essPairs := [(VAR 3,2,10)]) (by decide +kernel) hc
def g_22 := (d 0xfff8e800fff8e800)
def r_22 : List Nat := varsOf 31
def p_22 : List Nat := [11,11,11,13,13,13,14,14,14,15,19,19,19,20,20,21,21,22,22,23,24,24,25,25,26,26,28]
def q_22 : List Nat := [10,9,3,12,9,5,12,10,6,7,18,17,3,16,4,17,5,18,6,7,16,8,17,9,18,10,12]
def F_22 : Nat := fullMask 27
set_option maxHeartbeats 0 in
lemma gp_22 : goodPairs g_22 p_22 q_22 := goodPairs_of (by decide +kernel)
def W_22 : BT Decor := buildWiresBT 3 (mkBase p_22 q_22 r_22) [(1,2,4)]
lemma W_22_ok : btAll (fun x => faithful p_22 q_22 x ∧ x.1 < 2^256) W_22 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_22 : List (List (Nat × Nat)) := [[]]
def A_22 : BT (List (Nat × Nat)) := btOfList 1 al_22
set_option maxHeartbeats 0 in
lemma A_22_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_22 = g_22) A_22 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_22_0 : Slice r_22 g_22 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) (d 0xfffcfc00fffcfc00) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_1 : Slice r_22 g_22 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xfff0a000fff0a000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_2 : Slice r_22 g_22 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffafa00fffafa00) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_3 : Slice r_22 g_22 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) (d 0xff888800ff888800) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_4 : Slice r_22 g_22 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xfff0c000fff0c000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_5 : Slice r_22 g_22 (subcubeFast 0 8) 5 := by
  have hc : Lower (varsOf 23) (d 0xffffe8e8ffffe8e8) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_6 : Slice r_22 g_22 (subcubeFast 16 0) 5 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_5
set_option maxHeartbeats 0 in
lemma sl_22_7 : Slice r_22 g_22 (subcubeFast 16 8) 4 := by
  exact slice_fast_direct_f (z := 16) (o := 8) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_22_8 : Slice r_22 g_22 (identDom 2 3) 6 := by
  have hc : Lower (varsOf 23) (d 0xf8f8e0e0f8f8e0e0) 6 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_2
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
def S_22 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 0 1,5),some (subcubeFast 2 0,5),some (subcubeFast 0 2,5),some (subcubeFast 4 0,5),some (subcubeFast 1 0,5),some (subcubeFast 0 8,5),some (subcubeFast 16 0,5),some (subcubeFast 16 8,4),some (identDom 2 3,6)]
lemma S_22_ok : btAll (fun o => ∀ p, o = some p → Slice r_22 g_22 p.1 p.2) S_22 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_22_0) (forall_cons (fun _ h => by cases h; exact sl_22_1) (forall_cons (fun _ h => by cases h; exact sl_22_2) (forall_cons (fun _ h => by cases h; exact sl_22_3) (forall_cons (fun _ h => by cases h; exact sl_22_4) (forall_cons (fun _ h => by cases h; exact sl_22_5) (forall_cons (fun _ h => by cases h; exact sl_22_6) (forall_cons (fun _ h => by cases h; exact sl_22_7) (forall_cons (fun _ h => by cases h; exact sl_22_8) (fun _ h => (List.not_mem_nil h).elim))))))))))
def ps_22 : BT (Option PoolSpec) := btOfList 4 [q 4 [],q 0 [],q 1 [],q 2 [],q 5 [16393],q 3 [],q 6 [],q 7 [],q 5 [],q 8 []]
def B_22_5 : BT (List (List Nat)) := BT.empty
lemma B_22_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 5 xs.toFinset) B_22_5 := .empty
def U_22_6 : List Nat := (r 0 8)
def P_22_6 : BT (Option BoundPool) := buildPoolsSubBT 4 W_22 r_22 S_22 ps_22 U_22_6
def N_22_6 : List NodeSpec := [e5 [5] (r 0 8)]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_6 : checkNodesBT W_22 g_22 F_22 P_22_6 A_22 B_22_5 6 N_22_6 = true := by decide +kernel
def B_22_6 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_6
set_option maxRecDepth 500000 in
lemma B_22_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 6 xs.toFinset) B_22_6 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_5_ok C_22_6
def U_22_7 : List Nat := (r 0 4++r 5 5)
def P_22_7 : BT (Option BoundPool) := buildPoolsSubBT 4 W_22 r_22 S_22 ps_22 U_22_7
def N_22_7 : List NodeSpec := [u5 [] (r 0 4++r 5 5)]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_7 : checkNodesBT W_22 g_22 F_22 P_22_7 A_22 B_22_6 7 N_22_7 = true := by decide +kernel
def B_22_7 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_7
set_option maxRecDepth 500000 in
lemma B_22_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 7 xs.toFinset) B_22_7 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_6_ok C_22_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_22_ok : forestRootCheck r_22 g_22 [(VAR 0,10,11),(VAR 1,9,11),(VAR 2,9,13),(VAR 3,3,11),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_22_in : bucketContainsBT B_22_7 r_22 = true := by decide +kernel
lemma low_22 : Lower r_22 g_22 8 := lower_of_forestBT root_22_ok B_22_7_ok root_22_in
def g_23 := (d 0xfffafcc0fffafcc0)
def r_23 : List Nat := varsOf 31
def p_23 : List Nat := [6,6,7,7,10,10,11,11,12,12,13,13,17,17,19,19,20,20,21,22,24,24,25,26]
def q_23 : List Nat := [4,2,5,3,8,2,9,3,8,4,9,5,16,1,18,3,16,4,5,18,16,8,9,18]
def F_23 : Nat := fullMask 24
set_option maxHeartbeats 0 in
lemma gp_23 : goodPairs g_23 p_23 q_23 := goodPairs_of (by decide +kernel)
def W_23 : BT Decor := buildWiresBT 3 (mkBase p_23 q_23 r_23) [(1,2,3),(3,1,5)]
lemma W_23_ok : btAll (fun x => faithful p_23 q_23 x ∧ x.1 < 2^256) W_23 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_23 : List (List (Nat × Nat)) := [[]]
def A_23 : BT (List (Nat × Nat)) := btOfList 1 al_23
set_option maxHeartbeats 0 in
lemma A_23_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_23 = g_23) A_23 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_23_0 : Slice r_23 g_23 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) (d 0xfffffcc0fffffcc0) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_1 : Slice r_23 g_23 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffaf000fffaf000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_2 : Slice r_23 g_23 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xfff0fcc0fff0fcc0) 5 := carry_of (swaps := [(0,4),(1,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_3 : Slice r_23 g_23 (subcubeFast 17 0) 4 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 17) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_4 : Slice r_23 g_23 (subcubeFast 8 0) 4 := by
  have hc : Lower (varsOf 23) (d 0xfafac0c0fafac0c0) 4 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_11
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_5 : Slice r_23 g_23 (subcubeFast 4 0) 4 := by
  have hc : Lower (varsOf 27) (d 0xffaacc00ffaacc00) 4 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_11
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
def S_23 : BT (Option (Nat × Nat)) := btOfList 3 [some (subcubeFast 0 1,5),some (subcubeFast 2 0,5),some (subcubeFast 1 0,5),some (subcubeFast 17 0,4),some (subcubeFast 8 0,4),some (subcubeFast 4 0,4)]
lemma S_23_ok : btAll (fun o => ∀ p, o = some p → Slice r_23 g_23 p.1 p.2) S_23 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_23_0) (forall_cons (fun _ h => by cases h; exact sl_23_1) (forall_cons (fun _ h => by cases h; exact sl_23_2) (forall_cons (fun _ h => by cases h; exact sl_23_3) (forall_cons (fun _ h => by cases h; exact sl_23_4) (forall_cons (fun _ h => by cases h; exact sl_23_5) (fun _ h => (List.not_mem_nil h).elim)))))))
def ps_23 : BT (Option PoolSpec) := btOfList 3 [q 0 [],q 2 [],q 1 [],q 4 [],q 3 [],q 5 []]
def B_23_3 : BT (List (List Nat)) := BT.empty
lemma B_23_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 3 xs.toFinset) B_23_3 := .empty
def U_23_4 : List Nat := []
def P_23_4 : BT (Option BoundPool) := buildPoolsSubBT 3 W_23 r_23 S_23 ps_23 U_23_4
def N_23_4 : List NodeSpec := [([6,0,2,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_4 : checkNodesBT W_23 g_23 F_23 P_23_4 A_23 B_23_3 4 N_23_4 = true := by decide +kernel
def B_23_4 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_4
set_option maxRecDepth 500000 in
lemma B_23_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 4 xs.toFinset) B_23_4 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound S_23_ok) A_23_ok B_23_3_ok C_23_4
def U_23_5 : List Nat := (r 0 4)
def P_23_5 : BT (Option BoundPool) := buildPoolsSubBT 3 W_23 r_23 S_23 ps_23 U_23_5
def N_23_5 : List NodeSpec := [u5 [5] (r 0 4)]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_5 : checkNodesBT W_23 g_23 F_23 P_23_5 A_23 B_23_4 5 N_23_5 = true := by decide +kernel
def B_23_5 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_5
set_option maxRecDepth 500000 in
lemma B_23_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 5 xs.toFinset) B_23_5 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound S_23_ok) A_23_ok B_23_4_ok C_23_5
def U_23_6 : List Nat := (r 0 6)
def P_23_6 : BT (Option BoundPool) := buildPoolsSubBT 3 W_23 r_23 S_23 ps_23 U_23_6
def N_23_6 : List NodeSpec := [u5 [] (r 0 6)]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_6 : checkNodesBT W_23 g_23 F_23 P_23_6 A_23 B_23_5 6 N_23_6 = true := by decide +kernel
def B_23_6 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_6
set_option maxRecDepth 500000 in
lemma B_23_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 6 xs.toFinset) B_23_6 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound S_23_ok) A_23_ok B_23_5_ok C_23_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_23_ok : forestRootCheck r_23 g_23 [(VAR 0,16,17),(VAR 1,4,6),(VAR 2,2,6),(VAR 3,2,10),(VAR 4,1,17)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_23_in : bucketContainsBT B_23_6 r_23 = true := by decide +kernel
lemma low_23 : Lower r_23 g_23 7 := lower_of_forestBT root_23_ok B_23_6_ok root_23_in
def g_24 := (d 0xffecf800ffecf800)
def r_24 : List Nat := varsOf 31
def p_24 : List Nat := [11,11,11,12,12,13,13,14,14,15,18,18,19,19,21,21,21,22,22,23,24,24,25,25,26,28]
def q_24 : List Nat := [10,9,3,8,4,9,5,10,6,7,16,2,17,3,20,17,5,20,6,7,16,8,17,9,10,20]
def F_24 : Nat := fullMask 26
set_option maxHeartbeats 0 in
lemma gp_24 : goodPairs g_24 p_24 q_24 := goodPairs_of (by decide +kernel)
def W_24 : BT Decor := buildWiresBT 6 (mkBase p_24 q_24 r_24) [(0,3,4),(1,3,4),(3,5,6),(2,7,2),(0,7,1),(2,7,0),(1,2,3),(0,0,11),(1,2,4),(0,3,13),(1,0,5),(1,2,5),(1,13,3),(3,2,17),(1,1,5),(3,0,6),(0,7,0),(2,1,5),(0,0,6),(2,0,5),(0,1,6),(0,2,6),(2,3,4),(3,1,4),(1,28,3),(3,2,29),(1,1,2),(1,31,3),(2,32,4),(0,0,31),(2,31,4),(1,1,3),(1,36,4),(3,2,37),(3,2,3),(0,0,4),(1,40,3),(3,2,41),(3,5,4),(2,2,5),(3,1,37),(3,2,36),(3,13,3),(1,1,4),(3,2,48),(2,11,4),(2,0,4),(3,51,3),(1,43,1),(3,40,3),(1,51,3),(2,36,4),(0,0,3)]
lemma W_24_ok : btAll (fun x => faithful p_24 q_24 x ∧ x.1 < 2^256) W_24 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_24 : List (List (Nat × Nat)) := [[],[(1,2),(3,4)]]
def A_24 : BT (List (Nat × Nat)) := btOfList 1 al_24
set_option maxHeartbeats 0 in
lemma A_24_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_24 = g_24) A_24 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_24_0 : Slice r_24 g_24 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) (d 0xfffcfc00fffcfc00) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_1 : Slice r_24 g_24 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xffa0f000ffa0f000) 5 := carry_of (swaps := [(1,4),(2,4)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_2 : Slice r_24 g_24 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) (d 0xffcc8800ffcc8800) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_3 : Slice r_24 g_24 (subcubeFast 4 1) 4 := by
  have hc : Lower (varsOf 26) (d 0xffcccc00ffcccc00) 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_4 : Slice r_24 g_24 (subcubeFast 2 1) 4 := by
  have hc : Lower (varsOf 28) (d 0xfff0f000fff0f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 2) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_5 : Slice r_24 g_24 (identDom 1 3) 6 := by
  have hc : Lower (varsOf 23) (d 0xececc8c8ececc8c8) 6 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_2
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_6 : Slice r_24 g_24 (identDom 2 4) 6 := by
  have hc : Lower (varsOf 15) (d 0xf8e0f8e0f8e0f8e0) 6 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_2
  exact slice_ident (u := 2) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_7 : Slice r_24 g_24 (identDom 0 1) 5 := by
  have hc : Lower (varsOf 29) (d 0xffaafa00ffaafa00) 5 := carry_of (swaps := [(0,1),(1,4),(2,4)]) (by decide +kernel) low_8
  exact slice_ident (u := 0) (v := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_8 : Slice r_24 g_24 (identDom 0 4) 5 := by
  have hc : Lower (varsOf 15) (d 0xfaa8faa8faa8faa8) 5 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_8
  exact slice_ident (u := 0) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_9 : Slice r_24 g_24 (identDom 0 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xeeeea8a8eeeea8a8) 5 := carry_of (swaps := [(0,3),(2,3),(3,4)]) (by decide +kernel) low_8
  exact slice_ident (u := 0) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_10 : Slice r_24 g_24 (subcubeFast 1 0) 4 := by
  have hc : Lower (varsOf 30) (d 0xffccf000ffccf000) 4 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_11
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
def S_24 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 0 1,5),some (subcubeFast 2 0,5),some (subcubeFast 4 0,5),some (subcubeFast 4 1,4),some (subcubeFast 2 1,4),some (identDom 1 3,6),some (identDom 2 4,6),some (identDom 0 1,5),some (identDom 0 4,5),some (identDom 0 3,5),some (subcubeFast 1 0,4)]
lemma S_24_ok : btAll (fun o => ∀ p, o = some p → Slice r_24 g_24 p.1 p.2) S_24 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_24_0) (forall_cons (fun _ h => by cases h; exact sl_24_1) (forall_cons (fun _ h => by cases h; exact sl_24_2) (forall_cons (fun _ h => by cases h; exact sl_24_3) (forall_cons (fun _ h => by cases h; exact sl_24_4) (forall_cons (fun _ h => by cases h; exact sl_24_5) (forall_cons (fun _ h => by cases h; exact sl_24_6) (forall_cons (fun _ h => by cases h; exact sl_24_7) (forall_cons (fun _ h => by cases h; exact sl_24_8) (forall_cons (fun _ h => by cases h; exact sl_24_9) (forall_cons (fun _ h => by cases h; exact sl_24_10) (fun _ h => (List.not_mem_nil h).elim))))))))))))
def ps_24 : BT (Option PoolSpec) := btOfList 5 [q 2 [],q 8 [],q 4 [],q 3 [],q 0 [],q 10 [],q 5 [],q 1 [],q 6 [],q 6 [16397],q 1 [126976],q 7 [],q 2 [126976],q 0 [8197],q 9 [],q 2 [45056],q 5 [16391,12401],q 5 [16398],q 5 [16397],q 6 [12299]]
def B_24_2 : BT (List (List Nat)) := BT.empty
lemma B_24_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_24 2 xs.toFinset) B_24_2 := .empty
def U_24_3 : List Nat := []
def P_24_3 : BT (Option BoundPool) := buildPoolsSubBT 5 W_24 r_24 S_24 ps_24 U_24_3
def N_24_3 : List NodeSpec := [([8,7,0,1],[],[]),([9,7,0,2],[],[]),([10,7,1,2],[],[]),([12,1,14,4],[],[]),([1,15,16,6],[],[]),([7,0,1,16],[],[]),([7,18,0,1],[],[]),([0,19,16,6],[],[]),([7,20,1,2],[],[]),([21,7,1,2],[],[]),([22,7,0,2],[],[]),([7,23,1,2],[],[]),([7,1,2,15],[],[]),([7,0,1,2],[],[]),([24,7,1,2],[],[]),([0,25,26,5],[],[]),([7,0,25,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_24_3 : checkNodesBT W_24 g_24 F_24 P_24_3 A_24 B_24_2 3 N_24_3 = true := by decide +kernel
def B_24_3 : BT (List (List Nat)) := buildBucketsBT W_24 N_24_3
set_option maxRecDepth 500000 in
lemma B_24_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_24 3 xs.toFinset) B_24_3 :=
  buildBucketsBT_sound (by decide) gp_24 W_24_ok (buildPoolsSubBT_sound S_24_ok) A_24_ok B_24_2_ok C_24_3
def U_24_4 : List Nat := []
def P_24_4 : BT (Option BoundPool) := buildPoolsSubBT 5 W_24 r_24 S_24 ps_24 U_24_4
def N_24_4 : List NodeSpec := [([27,7,0,1,2],[],[]),([18,0,25,3,4],[],[]),([0,25,26,3,4],[],[0]),([7,0,1,2,3],[],[]),([1,3,15,16,4],[],[0]),([18,0,1,5,6],[],[0]),([18,0,1,3,4],[],[]),([0,1,14,11,4],[],[0]),([0,25,2,5,6],[],[0]),([30,0,1,3,4],[],[]),([7,0,1,2,6],[],[0,1]),([27,0,2,19,4],[],[]),([33,0,1,2,3],[],[]),([34,1,3,4,13],[],[]),([7,0,1,2],[],[0,1]),([35,28,0,2,3],[],[]),([23,25,2,3,4],[],[]),([0,1,2,14,6],[],[]),([38,0,1,3,4],[],[]),([39,34,1,3,4],[],[]),([7,0,1,2,5],[],[0,1]),([39,12,1,3,4],[],[]),([42,0,1,3,4],[],[]),([24,1,2,5,6],[],[0]),([18,20,1,3,4],[],[]),([27,43,0,1,2],[],[0]),([12,1,3,4,13],[],[0]),([1,2,5,15,6],[],[0,1]),([24,1,3,16,4],[],[]),([18,23,1,3,4],[],[]),([24,22,2,3,4],[],[]),([0,3,19,16,4],[],[0]),([22,0,3,16,4],[],[]),([0,1,5,16,6],[],[0]),([22,44,0,3,4],[],[]),([22,0,2,5,6],[],[0]),([0,1,2,5,6],[],[0]),([23,1,2,5,6],[],[0]),([18,45,0,3,4],[],[]),([20,1,2,5,6],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_24_4 : checkNodesBT W_24 g_24 F_24 P_24_4 A_24 B_24_3 4 N_24_4 = true := by decide +kernel
def B_24_4 : BT (List (List Nat)) := buildBucketsBT W_24 N_24_4
set_option maxRecDepth 500000 in
lemma B_24_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_24 4 xs.toFinset) B_24_4 :=
  buildBucketsBT_sound (by decide) gp_24 W_24_ok (buildPoolsSubBT_sound S_24_ok) A_24_ok B_24_3_ok C_24_4
def U_24_5 : List Nat := (r 0 17)
def P_24_5 : BT (Option BoundPool) := buildPoolsSubBT 5 W_24 r_24 S_24 ps_24 U_24_5
def N_24_5 : List NodeSpec := [([27,43,0,1,2],[],[0,1]),([18,0,1,3,4,6],[0],[0]),e5 [18] [],([20,1,2,3,4,6],[1,2,3],[0,1]),([23,1,2,3,4],[],[]),u5 [27] [],([27,0,1,2,5,4],[4],[0]),([18,0,1,3,4],[],[]),([23,1,2,3,4,6],[4],[0,1]),e5 [46] [],u5 [14] (r 4 5),u5 [35] [0],a5 [6] [0,1,4,7] [0,1],e5 [47] [],e5 [49] [],e5 [50] [],([39,0,1,31,3,4],[7],[0,1]),([27,43,0,1,2,3],[],[0]),([0,1,2,5,3,6],[9],[0]),([34,1,2,31,3,4],[4,10],[]),e5 [52] [5,6,7],e5 [53] [4,11],e5 [54] [],([0,25,2,3,4,6],[2],[0,1]),e5 [55] [],u5 [32] [4,8,11],([0,1,31,3,4,13],[7,8],[0]),([34,1,2,3,4],[10,12,13],[0,1]),([1,2,5,3,15,4],[2,3,5],[0,1]),u5 [41] [0,14],([12,1,2,3,11,4],[4,15],[0]),([12,1,2,3,4],[15],[0]),([39,0,1,3,11,4],[0],[0]),([22,0,2,5,3,4],[2,6],[0]),([27,0,1,2,36,4],[7],[]),([0,1,3,11,4,13],[8],[0]),a5 [37] [0,4,11] [0,1],e5 [56] [],a5 [29] [0,4,14,16] [0,1],([27,0,1,2,3,6],[4],[0]),([0,1,2,3,13,6],[0],[0]),([24,1,2,5,3,4],[4],[0,1]),([24,1,2,3,4],[],[]),u5 [5] ([0]++r 4 5),([0,1,2,5,6],[],[0,1]),([0,1,5,3,16,4],[0],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_24_5 : checkNodesBT W_24 g_24 F_24 P_24_5 A_24 B_24_4 5 N_24_5 = true := by decide +kernel
def B_24_5 : BT (List (List Nat)) := buildBucketsBT W_24 N_24_5
set_option maxRecDepth 500000 in
lemma B_24_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_24 5 xs.toFinset) B_24_5 :=
  buildBucketsBT_sound (by decide) gp_24 W_24_ok (buildPoolsSubBT_sound S_24_ok) A_24_ok B_24_4_ok C_24_5
def U_24_6 : List Nat := (r 0 10++[13,14,17,18,19])
def P_24_6 : BT (Option BoundPool) := buildPoolsSubBT 5 W_24 r_24 S_24 ps_24 U_24_6
def N_24_6 : List NodeSpec := [a5 [27] ([0,1]++r 4 4++[17]) [0,1],a5 [6] [0,4,5,7,9,18] [0,1],a5 [5] ([0]++r 4 5) [0,1],a5 [39] [3,6,7,8,19] [0,1],a5 [11] [3,7,8] [0,1],a5 [36] [0,2,6,7] [0,1],a5 [31] [3,6,7,8,13] [0,1],u5 [51] (r 1 5),a5 [57] [0,2,3,5,7,14] [1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_24_6 : checkNodesBT W_24 g_24 F_24 P_24_6 A_24 B_24_5 6 N_24_6 = true := by decide +kernel
def B_24_6 : BT (List (List Nat)) := buildBucketsBT W_24 N_24_6
set_option maxRecDepth 500000 in
lemma B_24_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_24 6 xs.toFinset) B_24_6 :=
  buildBucketsBT_sound (by decide) gp_24 W_24_ok (buildPoolsSubBT_sound S_24_ok) A_24_ok B_24_5_ok C_24_6
def U_24_7 : List Nat := [0,2,3,4,6,7,8]
def P_24_7 : BT (Option BoundPool) := buildPoolsSubBT 5 W_24 r_24 S_24 ps_24 U_24_7
def N_24_7 : List NodeSpec := [a5 [] [0,2,3,4,6,7,8] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_24_7 : checkNodesBT W_24 g_24 F_24 P_24_7 A_24 B_24_6 7 N_24_7 = true := by decide +kernel
def B_24_7 : BT (List (List Nat)) := buildBucketsBT W_24 N_24_7
set_option maxRecDepth 500000 in
lemma B_24_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_24 7 xs.toFinset) B_24_7 :=
  buildBucketsBT_sound (by decide) gp_24 W_24_ok (buildPoolsSubBT_sound S_24_ok) A_24_ok B_24_6_ok C_24_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_24_ok : forestRootCheck r_24 g_24 [(VAR 0,10,11),(VAR 1,9,11),(VAR 2,8,12),(VAR 3,3,11),(VAR 4,2,18)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_24_in : bucketContainsBT B_24_7 r_24 = true := by decide +kernel
lemma low_24 : Lower r_24 g_24 8 := lower_of_forestBT root_24_ok B_24_7_ok root_24_in
def g_25 := (d 0xfffffae8fc80c000)
def r_25 : List Nat := varsOf 63
def p_25 : List Nat := [14,14,14,15,15,15,23,23,23,23,26,26,26,27,27,27,28,28,28,29,29,29,30,35,35,35,37,37,37,38,38,38,39,41,41,41,43,43,44,44,44,45,46,48,48,49,49,50,50,51,52,52,53,54,56,56,57,58]
def q_25 : List Nat := [12,10,6,13,11,7,22,21,19,7,24,18,10,25,19,11,24,20,12,25,21,13,22,34,33,3,36,33,5,36,34,6,7,40,33,9,42,11,40,36,12,13,42,32,16,33,17,34,18,19,36,20,21,22,40,24,25,42]
def F_25 : Nat := fullMask 58
set_option maxHeartbeats 0 in
lemma gp_25 : goodPairs g_25 p_25 q_25 := goodPairs_of (by decide +kernel)
def W_25 : BT Decor := buildWiresBT 10 (mkBase p_25 q_25 r_25) [(0,1,5),(1,1,5),(3,6,7),(0,8,2),(1,8,2),(3,9,10),(1,9,3),(1,2,3),(1,8,4),(0,13,14),(1,1,3),(1,2,4),(0,16,17),(0,18,5),(1,18,5),(3,19,20),(0,1,2),(1,1,2),(1,4,5),(0,23,24),(1,25,3),(3,22,26),(2,1,4),(0,2,5),(1,2,5),(3,29,30),(2,31,3),(1,28,32),(1,31,4),(0,16,34),(1,6,3),(0,2,36),(2,0,37),(1,37,4),(3,1,39),(2,31,4),(3,41,16),(1,31,3),(3,28,43),(0,13,24),(0,1,45),(1,1,45),(3,46,47),(2,8,2),(2,8,3),(3,50,2),(0,16,24),(0,2,52),(1,2,52),(3,53,54),(3,50,17),(2,2,4),(1,57,50),(3,31,1),(2,0,59),(2,1,45),(3,1,45),(0,2,7),(1,63,4),(3,57,7),(0,17,7),(2,2,3),(3,67,8),(2,8,4),(0,2,14),(2,16,4),(2,71,5),(3,2,16),(1,72,73),(0,0,24),(3,57,30),(2,16,76),(1,31,1),(1,3,4),(3,4,20),(2,31,1),(3,57,8),(1,3,5),(0,17,83),(3,1,84),(2,2,19),(1,19,4),(0,2,16),(0,16,5),(1,57,89),(3,89,17),(2,0,2),(3,92,7),(3,28,7),(2,88,4),(1,71,2),(3,95,96),(2,2,52),(3,2,52),(3,57,16),(2,1,5),(3,101,16),(2,18,5),(3,18,5),(1,89,4),(0,8,13),(0,31,1),(0,8,17),(2,25,3),(3,1,5),(1,110,4),(3,2,111),(3,3,111),(3,113,2),(3,3,66),(3,88,24),(3,49,7),(0,31,16),(1,16,5),(0,17,119),(3,4,120),(1,88,4),(3,71,2),(2,10,3),(3,3,14),(1,9,4),(3,0,24),(3,2,24),(3,128,16),(2,1,3),(3,130,31),(2,2,5),(1,8,3),(0,2,133),(1,1,4),(3,3,5),(1,136,4),(3,2,137),(3,1,137),(3,139,2),(3,28,31),(0,0,7),(3,8,2),(2,0,143),(1,79,5),(0,2,145),(3,1,145),(0,2,24),(0,1,145),(0,0,145),(1,2,24),(3,148,151),(0,1,151),(3,3,24),(1,148,3),(3,1,24),(1,128,3),(2,1,24),(1,158,148),(1,135,5),(3,3,160),(3,148,160),(0,1,24),(1,1,148),(0,2,160),(3,163,160),(1,163,3),(3,2,145),(3,1,151),(3,2,160),(2,17,5),(0,2,137),(0,1,137),(3,173,2),(3,4,83),(0,1,83),(0,2,83),(1,1,177),(3,2,5),(1,132,4),(1,132,3),(3,132,1),(0,0,30),(1,1,84),(0,0,84),(0,0,83),(3,67,24),(1,67,1),(0,188,24),(1,132,1),(3,163,13),(3,4,5),(2,13,4),(1,193,5),(3,1,13),(3,195,24),(3,67,111),(0,13,111),(1,57,3),(3,101,199),(3,4,7),(2,67,4),(3,202,7),(0,13,7),(2,204,4),(1,204,4),(1,71,5),(1,3,66),(1,57,73),(3,71,30),(0,36,17),(3,92,24),(2,1,2),(3,213,137),(0,1,122),(3,132,16),(2,216,4),(1,6,4),(3,171,16),(1,29,4),(3,3,220),(3,1,220),(0,0,5),(1,223,3),(0,224,17),(2,57,5),(2,16,5),(2,135,5),(2,0,3),(3,229,2),(3,1,2),(3,231,137),(1,92,4),(0,233,7),(0,0,16),(3,231,24),(0,79,5),(1,231,237),(0,2,111),(2,231,3),(3,240,24),(0,16,30),(1,16,4),(3,101,243),(3,158,0),(1,88,5),(2,0,4),(3,247,2),(0,0,2),(1,249,3),(0,250,7),(0,23,137),(0,67,24),(1,73,4),(3,22,24),(0,199,7),(1,92,3),(2,71,2),(3,28,2),(3,0,7),(0,23,83),(1,247,3),(0,262,7),(0,23,262),(3,226,16),(0,250,24),(1,28,3),(0,267,30),(3,1,17),(0,262,30),(0,0,1),(1,271,3),(0,272,30),(3,229,24),(3,128,145),(2,0,84),(2,224,4),(2,23,4),(1,278,5),(1,179,4),(3,249,7),(1,231,163),(0,23,145),(0,272,17),(0,23,224),(3,247,7),(3,57,5),(2,16,287),(0,272,24),(1,22,4),(3,223,16),(0,2,79),(1,6,292),(2,23,237),(1,223,22),(1,57,223),(1,22,3),(0,297,24),(1,231,4),(0,299,83),(3,22,137),(1,28,177),(1,177,4),(3,249,24),(1,261,4),(2,261,4),(3,73,24),(0,71,30),(1,242,4),(1,57,5),(0,16,310),(1,67,4),(0,312,7),(0,243,30),(3,158,2),(3,4,30),(3,3,151),(1,132,71),(0,0,96),(0,16,220),(1,86,4),(1,249,4),(0,322,7),(3,88,17),(3,16,24),(3,130,220),(0,135,5),(1,3,327),(0,2,328),(3,2,328),(1,192,3),(0,23,331),(0,231,24),(3,57,36),(2,36,4),(3,335,2),(1,216,4),(3,2,7),(1,57,1),(0,339,83),(0,57,7),(3,226,0),(1,28,5),(3,163,2),(2,0,24),(3,345,2),(2,79,5),(1,136,1),(2,348,4),(3,2,83),(1,350,4),(1,292,5),(0,1,79),(3,353,2),(3,179,79),(1,179,1),(2,356,4),(2,181,4),(1,182,3),(2,190,4),(3,1,30),(1,361,4),(3,29,79),(1,29,3),(2,364,4),(1,57,136),(3,57,83),(1,1,287),(3,57,1),(1,369,5),(2,339,3),(0,1,220),(3,136,2),(3,132,17),(1,269,5),(1,67,5),(3,4,376),(1,202,5),(2,188,4),(3,192,13),(2,13,5),(1,381,4),(2,193,5),(1,195,5),(1,195,4),(3,110,79),(3,110,17),(3,110,13),(1,110,3),(3,110,2),(1,390,4),(3,1,83),(1,369,3),(3,101,17),(3,101,13),(3,176,2),(1,101,4),(1,101,3),(2,398,4),(1,392,4),(3,101,2),(0,79,7),(1,101,57),(2,199,5),(3,3,7),(1,213,4),(1,406,5),(1,271,4),(1,213,3),(1,73,5),(3,136,23),(2,0,5),(2,278,5),(1,136,22),(1,227,4),(3,28,30),(3,22,83),(3,3,30),(3,223,17),(3,223,79),(3,223,135),(3,136,17),(1,213,223),(3,271,2),(1,230,4),(1,223,4),(1,22,5),(1,28,29),(1,231,5),(3,4,429),(1,1,237),(3,192,23),(1,130,4),(2,433,5),(1,249,5),(3,4,435),(3,6,2),(1,213,5),(3,4,438),(2,406,5),(3,223,2),(3,213,79),(1,441,4),(0,0,151),(1,259,5),(1,28,223),(3,192,16),(3,1,199),(2,297,5),(2,272,4),(3,213,83),(3,249,135),(1,28,249),(2,23,3),(1,229,5),(1,1,29),(1,271,5),(3,271,79),(3,1,79),(3,271,83),(3,231,79),(3,4,427),(2,272,5),(1,92,5),(3,4,464),(1,290,5),(3,271,30),(0,23,79),(3,223,23),(1,230,5),(1,132,271),(1,192,22),(2,2,237),(1,424,5),(2,262,5),(3,4,457),(3,6,79),(1,229,4),(3,223,13),(3,130,2),(2,312,5),(1,408,5),(2,290,5),(1,480,4),(3,271,24),(3,4,455),(3,271,17),(2,408,5),(3,249,16),(3,271,13),(0,135,30),(0,0,427),(1,101,249),(3,231,83),(1,247,5),(3,101,79),(3,249,79),(3,29,135),(2,250,4),(3,249,83),(2,297,4),(1,373,4),(1,459,5),(2,478,5),(2,23,5),(0,2,135),(2,233,5),(1,505,4),(3,6,13),(1,57,271),(3,213,24),(2,1,237),(1,192,213),(1,231,3),(1,240,4),(1,240,5),(3,3,17),(1,299,5),(2,299,5),(2,231,4),(1,520,5),(1,506,5),(3,231,5),(1,523,4),(2,243,5),(1,136,231),(3,101,135),(1,424,4),(1,437,4),(1,57,6),(2,456,4),(1,192,231),(1,248,5),(2,88,5),(3,3,299),(2,250,5),(1,130,5),(2,339,5),(3,29,16),(1,136,213),(1,132,28),(2,322,5),(0,79,30),(3,136,135),(1,322,5),(1,57,110),(0,135,83),(3,179,16),(3,132,79),(1,128,1),(2,188,5),(2,231,5),(1,552,4),(0,2,119),(3,4,119),(3,192,2),(1,480,5),(3,4,537),(3,179,135),(3,132,135),(3,3,135),(0,13,135),(0,57,83),(3,0,427),(1,179,3),(2,2,327),(3,2,36),(2,67,5),(1,568,4),(3,28,13),(1,3,287),(1,28,179),(3,28,83),(3,22,79),(1,401,4),(1,28,136),(1,231,223),(1,338,4),(3,6,17),(2,267,5),(1,192,1),(3,2,79),(0,0,79),(0,0,135),(3,2,135)]
lemma W_25_ok : btAll (fun x => faithful p_25 q_25 x ∧ x.1 < 2^256) W_25 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_25 : List (List (Nat × Nat)) := [[]]
def A_25 : BT (List (Nat × Nat)) := btOfList 1 al_25
set_option maxHeartbeats 0 in
lemma A_25_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_25 = g_25) A_25 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_25_0 : Slice r_25 g_25 (subcubeFast 0 1) 9 := by
  have hc : Lower (varsOf 62) (d 0xfffffffcfcc0c000) 9 := carry_of (swaps := [(0,5),(1,5),(2,5),(3,5),(4,5)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_25_1 : Slice r_25 g_25 (subcubeFast 8 0) 9 := by
  have hc : Lower (varsOf 55) (d 0xffffe8e880800000) 9 := carry_of (swaps := [(3,5),(4,5)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_25_2 : Slice r_25 g_25 (subcubeFast 16 0) 9 := by
  have hc : Lower (varsOf 47) (d 0xfae8fae8c000c000) 9 := carry_of (swaps := [(2,3),(4,5)]) (by decide +kernel) low_12
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_25_3 : Slice r_25 g_25 (identDom 0 1) 10 := by
  have hc : Lower (varsOf 61) (d 0xfffffaaafaa0a000) 10 := carry_of (swaps := [(0,2),(1,5),(3,5),(4,5)]) (by decide +kernel) low_14
  exact slice_ident (u := 0) (v := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_25_4 : Slice r_25 g_25 (subcubeFast 32 0) 8 := by
  have hc : Lower (varsOf 31) (d 0xfc80c000fc80c000) 8 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_15
  exact slice_fast_direct_f (z := 32) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_25_5 : Slice r_25 g_25 (subcubeFast 32 1) 7 := by
  have hc : Lower (varsOf 30) (d 0xfcc0c000fcc0c000) 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 32) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_25_6 : Slice r_25 g_25 (subcubeFast 0 4) 8 := by
  have hc : Lower (varsOf 59) (d 0xffffffeeff88cc00) 8 := carry_of (swaps := [(2,5),(4,5)]) (by decide +kernel) low_16
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_25_7 : Slice r_25 g_25 (subcubeFast 1 0) 8 := by
  have hc : Lower (varsOf 62) (d 0xfffff0c0fc00c000) 8 := carry_of (swaps := [(0,5),(1,5),(2,5),(3,5),(4,5)]) (by decide +kernel) low_17
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_25_8 : Slice r_25 g_25 (subcubeFast 2 0) 8 := by
  have hc : Lower (varsOf 61) (d 0xfffffaa0f0000000) 8 := carry_of (swaps := [(1,5),(2,5),(3,5),(4,5)]) (by decide +kernel) low_18
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_25_9 : Slice r_25 g_25 (identDom 0 2) 8 := by
  have hc : Lower (varsOf 59) (d 0xffffaaaaee888800) 8 := carry_of (swaps := [(0,3),(1,3),(2,5)]) (by decide +kernel) low_19
  exact slice_ident (u := 0) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_25_10 : Slice r_25 g_25 (subcubeFast 4 0) 7 := by
  have hc : Lower (varsOf 59) (d 0xffffaa88cc000000) 7 := carry_of (swaps := [(2,5),(3,5),(4,5)]) (by decide +kernel) low_20
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_25_11 : Slice r_25 g_25 (subcubeFast 0 2) 7 := by
  have hc : Lower (varsOf 61) (d 0xfffffafaffa0f000) 7 := carry_of (swaps := [(1,5),(2,5),(4,5)]) (by decide +kernel) low_21
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_25_12 : Slice r_25 g_25 (identDom 0 3) 8 := by
  have hc : Lower (varsOf 55) (d 0xffffeaeaa8a88080) 8 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,5),(4,5)]) (by decide +kernel) low_22
  exact slice_ident (u := 0) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_25_13 : Slice r_25 g_25 (subcubeFast 0 8) 7 := by
  have hc : Lower (varsOf 55) (d 0xfffffafafcfcc0c0) 7 := carry_of (swaps := [(3,5),(4,5)]) (by decide +kernel) low_23
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_25_14 : Slice r_25 g_25 (subcubeFast 2 1) 6 := by
  have hc : Lower (varsOf 60) (d 0xfffffff0f0000000) 6 := carry_of (swaps := [(0,4),(1,5),(2,4),(3,5)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 2) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_25_15 : Slice r_25 g_25 (subcubeFast 8 4) 6 := by
  have hc : Lower (varsOf 51) (d 0xffffeeee88880000) 6 := carry_of (swaps := [(2,4),(3,5)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 8) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_25_16 : Slice r_25 g_25 (subcubeFast 8 2) 6 := by
  have hc : Lower (varsOf 53) (d 0xfffffafaa0a00000) 6 := carry_of (swaps := [(1,4),(2,4),(3,5)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 8) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_25_17 : Slice r_25 g_25 (subcubeFast 16 1) 6 := by
  have hc : Lower (varsOf 46) (d 0xfffcfffcc000c000) 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4),(4,5)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 16) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_25_18 : Slice r_25 g_25 (subcubeFast 8 1) 6 := by
  have hc : Lower (varsOf 54) (d 0xfffffcfcc0c00000) 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,5)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 8) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_25_19 : Slice r_25 g_25 (subcubeFast 4 1) 6 := by
  have hc : Lower (varsOf 58) (d 0xffffffcccc000000) 6 := carry_of (swaps := [(0,4),(1,4),(2,5),(3,4),(4,5)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 4) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_25_20 : Slice r_25 g_25 (identDom 1 2) 8 := by
  have hc : Lower (varsOf 59) (d 0xffffeecccc88cc00) 8 := carry_of (swaps := [(1,4),(2,5),(3,4),(4,5)]) (by decide +kernel) low_24
  exact slice_ident (u := 1) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_25_21 : Slice r_25 g_25 (subcubeFast 3 4) 4 := by
  have hc : Lower (varsOf 56) (d 0xffffff00ff000000) 4 := carry_of (swaps := [(0,3),(1,4),(2,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 3) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_25_22 : Slice r_25 g_25 (subcubeFast 3 8) 4 := by
  have hc : Lower (varsOf 52) (d 0xfffff0f0f0f00000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 3) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_25_23 : Slice r_25 g_25 (subcubeFast 32 3) 4 := by
  have hc : Lower (varsOf 28) (d 0xfff0f000fff0f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 32) (o := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_25_24 : Slice r_25 g_25 (subcubeFast 17 4) 4 := by
  have hc : Lower (varsOf 42) (d 0xffccffcccc00cc00) 4 := carry_of (swaps := [(0,3),(1,3),(2,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 17) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_25_25 : Slice r_25 g_25 (subcubeFast 32 5) 4 := by
  have hc : Lower (varsOf 26) (d 0xffcccc00ffcccc00) 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 32) (o := 5) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_25_26 : Slice r_25 g_25 (subcubeFast 33 8) 4 := by
  have hc : Lower (varsOf 22) (d 0xfcfcc0c0fcfcc0c0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 33) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_25_27 : Slice r_25 g_25 (subcubeFast 32 9) 4 := by
  have hc : Lower (varsOf 22) (d 0xfcfcc0c0fcfcc0c0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 32) (o := 9) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_25_28 : Slice r_25 g_25 (subcubeFast 32 17) 4 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 32) (o := 17) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_25_29 : Slice r_25 g_25 (subcubeFast 18 32) 4 := by
  have hc : Lower (varsOf 13) (d 0xfaa0faa0faa0faa0) 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 18) (o := 32) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_25_30 : Slice r_25 g_25 (subcubeFast 24 32) 4 := by
  exact slice_fast_direct_f (z := 24) (o := 32) (by decide +kernel) low_0
def S_25 : BT (Option (Nat × Nat)) := btOfList 5 [some (subcubeFast 0 1,9),some (subcubeFast 8 0,9),some (subcubeFast 16 0,9),some (identDom 0 1,10),some (subcubeFast 32 0,8),some (subcubeFast 32 1,7),some (subcubeFast 0 4,8),some (subcubeFast 1 0,8),some (subcubeFast 2 0,8),some (identDom 0 2,8),some (subcubeFast 4 0,7),some (subcubeFast 0 2,7),some (identDom 0 3,8),some (subcubeFast 0 8,7),some (subcubeFast 2 1,6),some (subcubeFast 8 4,6),some (subcubeFast 8 2,6),some (subcubeFast 16 1,6),some (subcubeFast 8 1,6),some (subcubeFast 4 1,6),some (identDom 1 2,8),some (subcubeFast 3 4,4),some (subcubeFast 3 8,4),some (subcubeFast 32 3,4),some (subcubeFast 17 4,4),some (subcubeFast 32 5,4),some (subcubeFast 33 8,4),some (subcubeFast 32 9,4),some (subcubeFast 32 17,4),some (subcubeFast 18 32,4),some (subcubeFast 24 32,4)]
lemma S_25_ok : btAll (fun o => ∀ p, o = some p → Slice r_25 g_25 p.1 p.2) S_25 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_25_0) (forall_cons (fun _ h => by cases h; exact sl_25_1) (forall_cons (fun _ h => by cases h; exact sl_25_2) (forall_cons (fun _ h => by cases h; exact sl_25_3) (forall_cons (fun _ h => by cases h; exact sl_25_4) (forall_cons (fun _ h => by cases h; exact sl_25_5) (forall_cons (fun _ h => by cases h; exact sl_25_6) (forall_cons (fun _ h => by cases h; exact sl_25_7) (forall_cons (fun _ h => by cases h; exact sl_25_8) (forall_cons (fun _ h => by cases h; exact sl_25_9) (forall_cons (fun _ h => by cases h; exact sl_25_10) (forall_cons (fun _ h => by cases h; exact sl_25_11) (forall_cons (fun _ h => by cases h; exact sl_25_12) (forall_cons (fun _ h => by cases h; exact sl_25_13) (forall_cons (fun _ h => by cases h; exact sl_25_14) (forall_cons (fun _ h => by cases h; exact sl_25_15) (forall_cons (fun _ h => by cases h; exact sl_25_16) (forall_cons (fun _ h => by cases h; exact sl_25_17) (forall_cons (fun _ h => by cases h; exact sl_25_18) (forall_cons (fun _ h => by cases h; exact sl_25_19) (forall_cons (fun _ h => by cases h; exact sl_25_20) (forall_cons (fun _ h => by cases h; exact sl_25_21) (forall_cons (fun _ h => by cases h; exact sl_25_22) (forall_cons (fun _ h => by cases h; exact sl_25_23) (forall_cons (fun _ h => by cases h; exact sl_25_24) (forall_cons (fun _ h => by cases h; exact sl_25_25) (forall_cons (fun _ h => by cases h; exact sl_25_26) (forall_cons (fun _ h => by cases h; exact sl_25_27) (forall_cons (fun _ h => by cases h; exact sl_25_28) (forall_cons (fun _ h => by cases h; exact sl_25_29) (forall_cons (fun _ h => by cases h; exact sl_25_30) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))))))))))))))
set_option maxRecDepth 500000 in
def ps_25 : BT (Option PoolSpec) := btOfList 12 [q 1 [20484,20485,28699],q 1 [20484,20485,28699,8224,8225],q 5 [8224,8225,40999],q 1 [20484,20485,28699,8224,8225,40999],q 10 [20484,20485,28699],q 29 [],q 1 [20497,98356,184324,184325,192699],q 1 [20484,20485,28699,8226,8395],q 1 [20497,98368,213000,213001,221399],q 0 [20484,20485,28699],q 7 [20484,20485,28699],q 1 [20488,20489,122999,16510],q 2 [20488,20489,122999],q 13 [20488,20489,122999],q 28 [],q 2 [20488,20489,122999,12414],q 5 [4223],q 3 [20488,20489,122999,4223,241666],q 8 [20488,20489,122999],q 1 [20488,20489,122999,4223,241666],q 25 [],q 24 [],q 1 [20497,98356,184326,184327],q 2 [20484,20485,28699,28680],q 4 [16394,28903],q 5 [16394,28903],q 2 [20484,20485,28699,28903],q 6 [20484,20485,28699],q 13 [20484,20485,28699],q 4 [16393,28740],q 5 [16393,28740],q 2 [20484,20485,28699,28740],q 5 [12298,33039],q 2 [20484,20485,28699],q 1 [20484,20485,28699,33039],q 15 [20484,20485,28699],q 2 [20484,20485,28699,12298],q 1 [20484,20485,28699,16418],q 1 [20484,20485,28699,16417],q 2 [20484,20485,28699,12297],q 23 [],q 1 [20484,20485,28699,16394],q 2 [20484,20485,28699,12322],q 2 [20484,20485,28699,57352],q 1 [20488,20489,122999],q 30 [],q 11 [20488,20489,122999],q 2 [12293,20488,20489,122999],q 1 [20488,20489,122999,16509],q 1 [20484,20485,28699,8226],q 2 [20488,20489,122999,4222],q 5 [16394,32999],q 2 [20484,20485,28699,32999],q 8 [],q 2 [12293,20493,340036,344071],q 1 [20484,20485,28699,8224],q 1 [65544,16394,20544,364773],q 1 [16450,8476,8477,393599],q 11 [8476,8477,393599],q 0 [8196,8197,20497,98396],q 8 [20497,98396],q 1 [8196,8197,20497,98396],q 1 [20497,98368,213002,213003],q 1 [16393,69696,20544,16741],q 5 [12297,53280],q 1 [20484,20485,28699,53280],q 1 [20488,20489,122999,4222],q 5 [4220,4221],q 20 [],q 1 [20488,20489,122999,4220,4221],q 5 [16393,69664],q 2 [20484,20485,28699,69664],q 1 [],q 2 [12293,20485,28740,270351],q 13 [20486],q 5 [12293,65660],q 1 [20488,20489,122999,65660],q 2 [12293,20486,65943],q 1 [65544,16737,20497,98368],q 5 [8225,12330],q 2 [20484,20485,28699,8225,12330],q 1 [65544,16393,20544,16741],q 4 [12293,65544],q 2 [20484,20485,28699,57359],q 5 [16417,57359],q 22 [],q 2 [20484,20485,28699,8224],q 1 [20488,20489,122999,4220],q 1 [20497,98356,184324,184325],q 10 [],q 1 [16390,20488,20489,122999],q 1 [20497,98368,213000,213001],q 5 [12294,127499],q 1 [20488,20489,122999,127499],q 4 [12293,65660],q 1 [20484,20485,28699,544776],q 5 [12322,8395],q 1 [20484,20485,28699,8395],q 1 [20484,20485,28699,16393],q 1 [16389,20488,20489,122999],q 2 [20488,20489,122999,12413],q 5 [16390,127091],q 2 [20488,20489,122999,127091],q 16 [16394],q 5 [8224,8225],q 5 [8227],q 6 [20484,20485,28699,585730],q 1 [20484,20485,28699,8227,585730],q 2 [20484,20485,28699,8227,585730],q 8 [147464,151554],q 5 [147464,16533,159751],q 13 [16533,159751],q 3 [20488,20489,122999,4222,4223],q 0 [20488,20489,122999,4222,4223],q 5 [4222,4223],q 1 [20488,20489,122999,4222,4223],q 6 [20484,20485,28672,28699],q 5 [8224],q 1 [20484,20485,28672,28699],q 16 [8224],q 2 [20484,20485,28672,28699],q 4 [8226,32967],q 5 [8226,32967],q 5 [8226,8227],q 1 [20484,20485,28699,8226,8227],q 6 [20497,98317],q 0 [20497,98317,593928],q 7 [20497,98317,593928],q 16 [20497,593928],q 8 [20497,98317,593928],q 1 [20497,593928],q 1 [20497,98315,593928],q 2 [98315,98317,593928],q 4 [98317,593928],q 8 [20497,98315],q 10 [20497],q 6 [20497,98317,593927],q 11 [],q 0 [20497,98317,593927],q 1 [20497,593927],q 2 [98315,98317,593927],q 4 [98317,593927],q 1 [20497,98315,593927],q 1 [20497,98312,593927],q 7 [20497,98317,593924],q 0 [20497,98317,593924],q 8 [20497,98312],q 1 [20497,593924],q 1 [20497,98312,593924],q 7 [],q 0 [20497,98317],q 8 [20497,98317,593920],q 16 [20497,593920],q 1 [20497,98312,593920],q 2 [98312,98313,619091],q 1 [20497,98312],q 6 [20497],q 0 [20497,98312,98313,619091],q 19 [20497],q 10 [20497,618500],q 0 [20497,98312,98313,618500],q 19 [20497,618500],q 1 [20497,98312,98313,618500],q 13 [],q 15 [],q 8 [20497],q 1 [20497,98311,98315],q 1 [20497,98311,98312],q 2 [98310,98312,606841],q 6 [20497,98309,655375],q 1 [20497,98309],q 16 [20497,98315],q 0 [20497,98309,655375],q 7 [20497,98309,655375],q 8 [20497,655375],q 2 [98309,98315,655375],q 4 [98309,655375],q 8 [20497,98315,655375],q 16 [20497,98312],q 8 [20497,98312,655375],q 2 [98309,98312,655955],q 11 [20497],q 16 [20497],q 2 [98308,98312,606213],q 0 [],q 6 [20497,98308],q 2 [98308,98312,606861],q 4 [98308,98312,606861],q 8 [20497,655368],q 10 [20497,98308],q 0 [20497,98308,98309,655368],q 19 [20497,98308],q 1 [20497,98308,98309,655368],q 1 [20497,98308,98309,656015],q 2 [98308,98309,656015],q 1 [20497,98308,98312],q 0 [20497,98317,593931],q 6 [20497,98307],q 1 [20497,98307,593931],q 2 [98307,98317,593931],q 4 [98307,98317,593931],q 5 [98317,593931],q 0 [20497,98313,618503],q 1 [20497,98307,98313,618503],q 16 [20497,98307],q 2 [98307,98313,618503],q 5 [98313,618503],q 8 [20497,98307,655375],q 11 [20497,98307],q 13 [20497,98307],q 2 [98307,98309,655375],q 4 [98307,98309,655375],q 5 [98309,655375],q 0 [20497,98309,655371],q 1 [20497,98307,98309,655371],q 8 [20497,98307,655371],q 2 [98307,98309,655371],q 5 [98309,655371],q 6 [20497,98304],q 7 [20497,98317,593931],q 21 [],q 1 [20497,98304,593931],q 2 [98304,98317,593931],q 3 [20497,98304,98317,593927],q 2 [98304,98317,593927],q 4 [98304,98317,593927],q 26 [],q 2 [98304,98313,618519],q 1 [20497,98304,98313,618519],q 16 [20497,98304],q 13 [20497,98304],q 8 [20497,98304,655375],q 2 [98304,98309,655375],q 4 [98304,98309,655375],q 11 [20497,98304],q 8 [20497,98304,655368],q 1 [20497,98304],q 1 [20497,98304,98309,655368],q 7 [20497,98309,655368],q 6 [],q 6 [20495,16929],q 10 [20497,98311],q 2 [20493],q 10 [20493,339987],q 8 [20493,339987],q 1 [20497,98312,339987],q 2 [20493,98304],q 4 [98304,339987],q 8 [20493,339976],q 2 [20490,20491,733713],q 5 [16510],q 10 [16510],q 8 [20490,20491,733713],q 1 [20490,20491,733713],q 2 [98304,98317,593928],q 5 [12414],q 10 [12414],q 4 [4222],q 5 [4222],q 1 [20490,20491,733713,4222],q 10 [4222],q 5 [16913],q 1 [20490,16913,20491,733713],q 5 [12817],q 2 [20490,12817,20491,733713],q 5 [4627],q 1 [20490,4627,20491,733713],q 7 [20493,339976],q 10 [122880],q 1 [20489,122880,339976],q 2 [20489,122880,20493,339976],q 4 [122880,339976],q 5 [16397],q 5 [16509],q 5 [12413],q 1 [20488,20489,122999,4223],q 3 [20488,20489,122999],q 3 [20488,20489,122999,4222],q 0 [20488,20489,122999],q 0 [20488,20489,122999,4222],q 5 [4220],q 2 [20488,20489,122999,4220],q 4 [16393,340036],q 1 [16393,340036],q 0 [16393,20493,340036],q 2 [20493,340036,344064],q 2 [20493,339968,340036],q 1 [16393,339968,340036],q 6 [20497,98311],q 15 [20497],q 10 [20497,98319],q 8 [20497,98319],q 10 [20497,98307],q 15 [20497,98307],q 8 [20497,98307],q 1 [20497,98307,98311],q 10 [20497,98304],q 15 [20497,98304],q 8 [20497,98304],q 1 [20497,98304,98311],q 0 [12298,20497,98575],q 1 [20497,98575,98307],q 2 [98307],q 2 [12298,98575,98307],q 4 [98307],q 14 [12298],q 2 [12298,4365,98308],q 5 [4625],q 1 [20490,4625,20491,733713],q 11 [20490,20491,733713],q 1 [20497,98356,184326],q 3 [12297,20497,98356],q 0 [12297,20497,98356],q 1 [20497,98356,184325],q 13 [20497],q 1 [20497,98356,184324],q 1 [20497,98308,98356],q 2 [12297,98308,98356],q 14 [12297],q 2 [12297,98308,53903],q 1 [20497,98307,98356],q 2 [12297,98307,98356],q 4 [12297,98307,98356],q 1 [20497,98307,593927],q 2 [98307,98317,593927],q 1 [20497,98304,98312],q 4 [12297,16438],q 1 [16438,21253,20499],q 0 [12297,53255],q 2 [12297,53255,98304],q 1 [20487,16825,454667],q 1 [20486,16394,815511],q 2 [20486,12517,815511],q 2 [20485],q 10 [20485,28691],q 8 [20497,98312,28691],q 1 [20485,28691],q 1 [20485,20497,98312,28691],q 2 [20485,28680],q 7 [20485,28680],q 4 [28680,98304],q 2 [98304],q 2 [20485,28680,98304],q 1 [20485,28680,20497,98304],q 2 [20485,28740,270351],q 1 [20485,16393,28740],q 1 [20485,16654,29483],q 2 [20485,12298,29483],q 4 [],q 4 [12298,16654,29483],q 2 [],q 1 [20485,28724,17202],q 2 [20485,12297,28724],q 1 [20485,28724,17201],q 11 [12297],q 6 [20485],q 13 [20485],q 1 [65544,16738],q 0 [12293,20486],q 7 [12293,20486],q 6 [12293,20544],q 2 [12293],q 1 [16393,20544,364554],q 2 [12293,65547,20765],q 10 [12293],q 3 [20497,98304,98313,618503],q 1 [20497,98304,98313,618503],q 2 [98304,98313,618503],q 1 [65544,20544,16741],q 2 [12293,20544],q 6 [12293],q 2 [20493,339976,98304],q 4 [98304],q 4 [339976,98304],q 2 [20485,28740,270349],q 11 [16393],q 5 [8196,8197],q 20 [20495,16929],q 8 [20495,16929],q 1 [8196,8197,16929],q 2 [12293,65547,299237],q 1 [65547,16394,299237],q 6 [12293,16450],q 2 [12293,65547,8479],q 7 [12293,65547],q 11 [8479],q 1 [65547,16450,8479],q 4 [12293,65547],q 13 [8479],q 2 [12293,20486,65547],q 2 [12293,20765],q 0 [8197,20497,98396],q 1 [20497,98307],q 0 [12293,65544],q 7 [12293,65544],q 2 [12293,20766],q 19 [12293],q 2 [12293,98312,66131],q 2 [12293,65544,8479],q 1 [65544,16450,8479],q 1 [20497,98312,66131],q 2 [12293,20485,28740],q 6 [12293,20485],q 1 [20489,16450,123167],q 5 [16393,69776],q 7 [20484,12313],q 2 [20484,12313],q 2 [20484,12313,69776],q 5 [16417],q 0 [20497,98308],q 2 [12293,65544,98659],q 2 [12293,65544,98315],q 2 [8194,20485,29043],q 0 [20485,28691],q 1 [65544,20497,98659],q 3 [20497,98304],q 14 [20497],q 1 [65544,16737],q 1 [65544,16737,499716],q 13 [16737,499716],q 0 [20497],q 2 [8197,98304,98396],q 1 [65544,16737,20497],q 4 [12293],q 8 [16393,28740],q 2 [20486,20885,28740],q 6 [20486,20885],q 1 [16394,65767],q 11 [16409],q 4 [12297,53255],q 0 [20484,16409,12297,53255],q 5 [12297,53255],q 6 [20484,16409],q 1 [20484,16409,53255],q 1 [16393,69696],q 6 [12293,20486],q 1 [16393,20550,66223],q 2 [12293,65544,8477],q 1 [65544,16450,8477],q 1 [20488,16501,901127],q 8 [20488,16501],q 1 [65547,16394],q 0 [13181,16393,70528],q 7 [16393,70528],q 13 [16393],q 1 [20480,16393,70528],q 2 [20480,13181,70528],q 2 [98304,98314,9099],q 1 [65544,16450],q 2 [12293,20486,65544],q 2 [12293,65544],q 0 [9111],q 1 [16389,21022],q 7 [16389,21022],q 2 [12293,20486,8479],q 1 [16450,8479],q 1 [20497,98312,98313,619091],q 7 [20485,29604],q 0 [16753,20485,29604],q 5 [16753,29604],q 19 [],q 6 [12293,65536],q 1 [8199,20497,99231],q 7 [12293,20486,65943],q 16 [16929],q 1 [20486],q 4 [16397],q 1 [8199,20796,971677],q 16 [20796],q 1 [20487,16825,454664],q 6 [20487,16825],q 1 [65544,20497,98368],q 2 [12293,98368],q 4 [98304,98317,593928],q 1 [8199,20497,99267],q 2 [8199,13214,99267],q 4 [8199,13214,99267],q 1 [16393,20544,16741],q 6 [12293,20544,16741],q 4 [12293,122944],q 1 [16394,20489,122944],q 8 [16394,20489,122944],q 0 [12298,4365],q 2 [12298,4365,98304],q 2 [12293,20486,995735],q 4 [12293,16449,995735],q 1 [8197,20497,98396],q 1 [16393,20544,69991],q 0 [20497,98310],q 7 [20497,98312],q 1 [20497,98310,635],q 1 [20497,98310,635,98312],q 1 [65544,16393],q 2 [12293,8476],q 1 [16450,8476,16765],q 5 [16418],q 5 [16393],q 16 [16393],q 1 [16386,9183,339987],q 0 [13285,20485,29672],q 6 [13285,20485,29672],q 7 [20485,29672],q 1 [8192,20485,29672],q 5 [13285,29672],q 16 [8192],q 16 [8226],q 5 [8226],q 2 [20484,20485,28699,8226],q 5 [8197,561244],q 1 [8197,16929,561244],q 0 [13285],q 0 [20497,98311],q 7 [20497,98309,655371],q 8 [20497,98304,655371],q 1 [20497,98304,98309,655371],q 2 [98304,98309,655371],q 6 [12293,20546],q 18 [],q 0 [8196,20497,98395],q 1 [16393],q 8 [16393],q 1 [20486,65943],q 2 [12293,20546],q 1 [20497,98315,98368],q 1 [20485,16394,29468],q 10 [20485,29468],q 2 [20485,12517,29468],q 15 [20485,28691],q 2 [12293,8478],q 1 [16450,8478,17417],q 5 [12297,454708],q 1 [20487,16825,454708],q 1 [16390,8307,339987],q 0 [20485,16393,28740],q 2 [20485,28675,28740],q 4 [28675,16393,28740],q 6 [20485,28675],q 5 [28691],q 1 [20484,20485,28699,28691],q 16 [],q 6 [16397,20493],q 1 [8197,340060],q 4 [8197,340060],q 0 [13277,20485,29720],q 1 [16386,20485,29720],q 5 [13277,29720],q 2 [13277,20485,29720],q 0 [13277,8197,1073244],q 6 [16386,13277],q 2 [13277,8197,1073244],q 1 [16394,20710,66443],q 8 [16394,20710,66443],q 0 [13285,20497,99304],q 6 [13285,20497,99304],q 2 [8192,13285,99304],q 4 [8192,13285,99304],q 1 [8192,20497,99304],q 10 [20497,99304],q 5 [13285,99304],q 1 [16390,20489,123948],q 8 [20489,123948],q 2 [12401,20489,123948],q 3 [20484,12313,16393,69639],q 0 [20484,12313,16393,69639],q 5 [16393,69639],q 2 [20484,12313,69639],q 6 [20484,12313],q 1 [20484,16393,69639],q 11 [12313],q 0 [13277,20489,123928],q 5 [13277,123928],q 1 [16386,20489,123928],q 2 [13277,20489,123928],q 2 [12293,65544,98304],q 0 [12293,20497,98368],q 1 [20497,98307,98368],q 8 [20497,98307,98368],q 5 [12293,98368],q 1 [20484,20485,28699,8227],q 0 [13373,20489,123968],q 7 [20489,123968],q 1 [4096,20489,123968],q 8 [20489,123968],q 5 [13373,123968],q 6 [4096,13373],q 7 [20497,98308],q 7 [20497,99304],q 1 [20497,98315,594435],q 1 [16394,65767,20544],q 11 [16394],q 6 [12293,65767],q 8 [16394,65767],q 13 [16394],q 2 [20493,340036,344066],q 7 [12293,20546],q 2 [20495],q 1 [65544,16394],q 2 [12293,20486],q 7 [20485,28691],q 0 [13181,17282],q 3 [20480,13181,17282],q 20 [20480,13181,17282],q 5 [12293,65544],q 1 [65544,20833,20544],q 0 [16390,20485,28787],q 8 [8192],q 4 [8197,16478],q 1 [8197,16478,21593,20499],q 11 [21593,20499],q 8 [16478,21593,20499],q 2 [12293,8479,20546],q 1 [65547,16677],q 5 [12293],q 10 [17101],q 1 [65544,20491,17101],q 7 [20497,98311],q 0 [20497,99223],q 7 [20497],q 0 [20497,98312],q 1 [16394,20489,123111],q 1 [8192],q 2 [20484,20485,28740],q 1 [20484,20485],q 13 [20484,20485],q 1 [20484,20485,16393,28740],q 7 [16390,20485],q 0 [16390,20485],q 1 [65544,20497,98304],q 14 [],q 2 [8199,98308,668573],q 6 [16397,20797],q 16 [20797],q 2 [8197,20797,594012],q 0 [13373,16393,70720],q 7 [16393,70720],q 1 [4096,16393,70720],q 2 [4096,13373,70720],q 6 [20485,28672],q 2 [20485,28672,28680],q 10 [20485,28672],q 1 [20485,28672],q 13 [20485,28672],q 5 [4221],q 1 [20488,20489,122999,4221],q 2 [20488,20489,122999,4221],q 1 [65544,16737,16450],q 0 [8199,20497,99231],q 8 [20497,99231,98307],q 2 [8199,99231,98307],q 4 [28672],q 2 [20490],q 1 [20490,16913,16450],q 0 [20485],q 2 [20485,28672,28740],q 0 [20487,16825],q 7 [20487,16825],q 1 [20487,16825],q 0 [20485,16394,28903],q 2 [20485,28675,28903],q 8 [28675],q 1 [20485,28675],q 13 [20485,28675],q 0 [13181,8197,917596],q 6 [20480,13181],q 1 [20480,8197,917596],q 1 [20497,98575,98304],q 2 [12298,98575,98304],q 4 [12298,98575,98304],q 7 [20485],q 0 [20485,29663],q 0 [20485,28680],q 2 [12293,20711,1175618],q 0 [13373,20497,99392],q 2 [4096,13373,99392],q 4 [4096,13373,99392],q 1 [4096,20497,99392],q 8 [20497,99392],q 5 [13373,99392],q 1 [16390,20485,28724],q 6 [16390,20485],q 8 [12297,28724],q 4 [12297,28724],q 7 [8196,16473],q 6 [16473,20497,98304],q 1 [8196,16473,20497,98304],q 4 [8196,16473,98304],q 1 [16450,8478,8479],q 11 [8478,8479],q 2 [20480,12293,66431],q 5 [16397,323592],q 8 [16397,323592],q 2 [20484,323592,1196057],q 1 [20484,323592,1196057],q 1 [8197,20796,970846],q 7 [8196,8197],q 0 [8196,91005,8197],q 6 [20480,91005],q 1 [20480,8196,91005,8197],q 2 [20480,8196,91005,8197],q 4 [8196,8197],q 1 [20480,16394,913637],q 1 [8196,20497,99492],q 8 [20497,99492],q 10 [20497,99492],q 2 [8196,12377,99492],q 4 [8196,12377,99492],q 2 [8199,20493,341164],q 10 [20493,341164],q 1 [8199,17309,341164],q 2 [8192,20485,29671],q 0 [20485,29671],q 2 [8196,8197,98396],q 3 [16390,20485,28787],q 8 [8194],q 1 [16450,8476,8477],q 11 [8476,8477],q 5 [8196,561243],q 1 [8196,16929,561243],q 1 [16390,339976,725105],q 2 [20493,339976,725105],q 2 [20493,339976],q 5 [8198,562007],q 1 [8198,16929,562007],q 8 [20493,340060],q 2 [8196,8197,20493,340060],q 1 [20497,98308],q 2 [98308,98309,655368],q 2 [20485,28672],q 1 [20485,28672,28691],q 11 [20493],q 20 [20497,98307,98319],q 6 [20497,98309],q 0 [20497,98309,655368],q 2 [12293,98315,66051],q 4 [147464,151554],q 6 [20484,12313,151554],q 10 [20484,12313],q 2 [20484,12313,147464,151554],q 13 [151554],q 1 [20497,98356,184327],q 1 [65547,20497,98599],q 1 [65547,20497,98312],q 5 [12321],q 2 [20484,20485,28699,12321],q 1 [20497,98304,98356],q 2 [12297,98304,98356],q 4 [12297,98304,98356],q 1 [16393,20490,66067],q 2 [12293,20490,66067],q 4 [12293,66067],q 6 [12293,20493],q 1 [20497,98304,593924],q 2 [98304,98317,593924],q 0 [12293,16393,69696],q 2 [12293,69696],q 0 [12293,65547],q 7 [20497,98313,618500],q 1 [20497,98304,98313,618500],q 2 [98304,98313,618500],q 1 [20489,16450,123164],q 1 [16393,69696,20544],q 8 [16393,69696],q 1 [20489,122944,17353],q 2 [12293,20489,122944],q 1 [16393,20544,20550],q 1 [16394,20709,1269824],q 2 [20485,12298,29920],q 10 [20485,29920],q 1 [20485,16653,29920],q 20 [20497,98304],q 1 [8196,8197,20497,98304],q 2 [8196,8197,98304],q 1 [16394,20490,66067],q 1 [16394],q 8 [16394],q 1 [20497,98368,213002],q 6 [12293,16449],q 11 [20489],q 2 [12293,20489,123852],q 1 [20489,16449,123852],q 1 [20497,98311],q 1 [20497,98310,8827,98311],q 2 [20489],q 1 [20489,16450,122899],q 7 [12293,16450],q 1 [20489,122880,16450],q 2 [20489,122880],q 11 [20489,122880],q 4 [122880],q 4 [12293,16450],q 8 [16450,20765,20499],q 11 [20765,20499],q 1 [16450,20765,20499],q 5 [12297],q 1 [20489,16450,122944],q 0 [20497,98313,618511],q 2 [98307,98313,618511],q 4 [98307,98313,618511],q 5 [98313,618511],q 2 [12293,20490,291345],q 1 [20490,16450,291345],q 1 [16450,8477,393216],q 2 [12293,8477,393216],q 11 [8477,393216],q 5 [12293,901184],q 1 [20488,16501,901184],q 11 [20488,16501],q 2 [12293,20488,901184],q 1 [16450,8476,65919],q 1 [16450,20766,65827],q 8 [16450,20766,65827],q 11 [20766],q 5 [28680],q 1 [20484,20485,28699,28680],q 2 [12293,20766,65827],q 1 [20544,364554,16729],q 1 [20497,98304,98368],q 8 [20497,98304,98368],q 2 [12293,98304,98368],q 7 [20485,29960],q 0 [17381,20485,29960],q 5 [17381,29960],q 1 [20497,98307,98315],q 1 [65544,16393,20544],q 8 [65544,16393],q 1 [65544,16393,69987],q 8 [20497,98368],q 1 [20497,98312,98368],q 2 [12293,98312,98368],q 8 [20497,98371],q 1 [20497,98312,98371],q 1 [20497,98315,98371],q 1 [20497,98368],q 1 [20497,98368,213000],q 4 [12293,98368],q 7 [20497,98313,618511],q 2 [98304,98313,618511],q 2 [20488],q 1 [20497,98368,213001],q 1 [20484,16393,69776],q 1 [65547,20497,98368],q 1 [20497,98368,213003],q 2 [12294,20485,28740],q 6 [12294,20485],q 5 [12294],q 2 [12294,20488,20489,122999],q 1 [20497,98311,98356],q 5 [16389],q 0 [16389,21020,1339405],q 11 [1339405],q 2 [21020,1339405],q 6 [16389,21020,1339405],q 1 [16389,21020],q 2 [21020,1339405,1343499],q 13 [16389],q 1 [16390,20485,28787],q 2 [20485,28787,28680],q 1 [16390,20485,28787,28680],q 13 [20489],q 0 [20484,12313],q 0 [20484,12313,147464],q 7 [20484,12313,147464],q 5 [8197,1355868],q 6 [20499,13057],q 2 [8197,13057,1355868],q 5 [147464,16533],q 8 [147464],q 2 [20484,12313,147464],q 13 [16533],q 2 [8199,99228,98304],q 5 [16394,147687],q 1 [20484],q 2 [20484,12313,147687],q 6 [12293,20545],q 2 [12293,20545,487492],q 1 [16393,20545,487492],q 5 [16530,9535],q 8 [16530,9535],q 2 [20484,12313,9535],q 13 [9535],q 7 [20484,20485],q 2 [20484,20485,28672],q 1 [20484,20485,28672],q 1 [16394,20544,364773],q 5 [8225],q 1 [20484,20485,28699,8225],q 1 [20490,66067,17249],q 5 [12322],q 1 [20489,122944,17354],q 2 [12293,8478,66571],q 1 [16450,8478,66571],q 11 [8478],q 2 [12297,53255,98308],q 5 [16390],q 4 [28683],q 5 [28683],q 2 [20484,20485,28699,28683],q 2 [20484,20485,28903],q 10 [20484,20485],q 2 [4325,20493,341324],q 2 [20484,20485,28680],q 11 [16637],q 1 [65544,16394,20544],q 8 [65544,16394],q 8 [28672],q 2 [20485,28672,28900],q 1 [20497,593931],q 2 [98317,593931],q 2 [98317,593928],q 2 [98317,593924],q 1 [20497,98315],q 6 [20497,98319],q 7 [20497,98315],q 0 [20497,98315],q 0 [20497,98319],q 7 [20497,98319],q 1 [20497,98314,21385],q 6 [20497,907],q 1 [20497,98314,907],q 2 [98314,907],q 2 [98313,618511],q 27 [],q 6 [20497,12881],q 6 [20497,606213],q 2 [98312,606213],q 3 [20497],q 1 [20497],q 1 [20497,98312,606213],q 3 [20497,98312],q 1 [20497,98310,98311],q 2 [98310,98311],q 1 [20497,98310,21113],q 8 [20497,655371],q 3 [20497,98309,655371],q 1 [20497,98309,655371],q 2 [98309,655371],q 2 [98309,655368],q 3 [20497,98309,655368],q 1 [20497,98309,655368],q 2 [98308,98312],q 4 [98312],q 1 [20497,98308,98309],q 2 [98308,98309],q 2 [98308,8847],q 1 [20497,98308,8847],q 2 [98307,98315],q 0 [20497,98313],q 9 [],q 1 [20497,98307,98313],q 2 [98307,98311],q 0 [20497,9575],q 1 [20497,98306,9575],q 1 [20497,98306,1383],q 2 [98306,1383],q 2 [98304,98311],q 1 [20497,98304,98314],q 1 [20497,593943],q 2 [98304,98312],q 3 [],q 3 [20497,98310],q 2 [98304,98310],q 7 [20497,98309],q 1 [20497,98304,98309],q 7 [20497,98310],q 5 [17778],q 2 [20495,4641],q 5 [98312],q 8 [20493],q 10 [20493],q 2 [98312],q 7 [20493],q 0 [20493],q 0 [20493,339979,17785],q 13 [17785],q 1 [339979,17785],q 6 [20493],q 2 [20493,339979],q 6 [20493,17093],q 13 [17093],q 1 [339976,17093],q 5 [339976],q 1 [339976,20497],q 0 [20493,339976],q 3 [20493,339972,339976],q 7 [20493,339972],q 0 [20493,339972],q 4 [339976],q 10 [20493,339972],q 3 [20493,339976],q 8 [20493,339968],q 16 [339968],q 19 [20493],q 2 [20493,339968],q 2 [20493,339968,339976],q 1 [323592,21649],q 7 [16397],q 0 [16397],q 8 [16397],q 1 [323588,9607],q 2 [323588,9607],q 10 [16397],q 6 [16397],q 19 [16397],q 13 [9607],q 2 [20491,324303],q 5 [17810],q 2 [20491,4813],q 6 [17810],q 1 [20491,4813,17810],q 2 [20490,98304],q 7 [20490],q 8 [20490,20491],q 1 [20490,20491],q 5 [],q 4 [12817],q 2 [20490,12817,20491],q 0 [20490,12817,17110],q 6 [12817,17110],q 10 [17110],q 10 [13017],q 0 [20490,4627,13017],q 19 [13017],q 8 [20490],q 1 [20490,4627],q 4 [4625],q 0 [20490,4625,20491],q 3 [20490,4625,20491],q 3 [20490,20491],q 11 [20490,20491],q 1 [20490,4625,20491],q 2 [20490,20491],q 2 [20490,4625],q 8 [20490,17146],q 6 [4625,17146],q 10 [17146],q 5 [122899],q 1 [20489,20497,122899],q 1 [20489,339976],q 2 [20489,20493,339976],q 8 [20489,17829],q 0 [20489,122887,17829],q 3 [20489,122887,17829],q 6 [17829],q 1 [20489,122887,17829],q 2 [20489,122887],q 6 [16397,323703],q 2 [20488,323703],q 5 [901135],q 2 [20488,901135],q 1 [20488,16501],q 5 [17842],q 6 [12405,17842],q 10 [17842],q 6 [16913],q 1 [20488,8311,16913],q 5 [16394],q 8 [20495],q 1 [4641],q 6 [20495,4641],q 1 [16394,4641],q 1 [16394,557285],q 6 [20493,339987],q 1 [16394,339987],q 1 [16394,339968],q 2 [20493,340199],q 1 [16394,340199],q 0 [16394,20493,340199],q 4 [16394,123111],q 8 [16394,20711],q 10 [1175557],q 2 [20711,1175557],q 0 [20497,98312,98313],q 2 [98312,98313],q 10 [21957],q 0 [16394,4327,21957],q 19 [21957],q 1 [16394,4327,21957],q 2 [4327,21957],q 2 [4325,20493],q 1 [16394,4325],q 8 [16394,13646],q 10 [13646],q 0 [16394,4325,13646],q 19 [13646],q 2 [4325,13646],q 4 [16394],q 5 [901124],q 2 [20488,901124],q 1 [20488,16501,901124],q 1 [16393,8739],q 2 [20495,8739],q 6 [20495],q 3 [16393],q 0 [16393],q 1 [16393,4641],q 0 [16393,20493],q 7 [16393],q 1 [16393,339968],q 6 [20493,339968],q 1 [16393,20490,70163],q 8 [16393,21557],q 0 [16393,69639,21557],q 3 [16393,69639,21557],q 6 [21557],q 1 [16393,69639,21557],q 2 [69639,21557],q 4 [16393,69639],q 8 [12298],q 11 [12298],q 2 [12298,98311],q 2 [12298,98308],q 0 [12298,20497],q 2 [12298,98307],q 5 [12298],q 7 [12298],q 2 [12298,98304],q 0 [12298],q 2 [12298,20749],q 10 [1540115],q 6 [20749,1540115],q 1 [16654,21289],q 2 [12298,21289],q 4 [12298,16654],q 3 [20495,16929],q 0 [20495,16929],q 2 [20495,561159],q 5 [561159],q 2 [12298,4365],q 6 [20499],q 1 [20499,54019],q 2 [12297,54019],q 8 [20497,655383],q 1 [20497,98309,655383],q 1 [20497,98356],q 2 [12297,98356],q 4 [12297,98356],q 2 [12298,98319],q 8 [12297],q 2 [12297,98311],q 2 [12297,98308],q 0 [12297,20497],q 7 [12297],q 2 [12297,98307],q 0 [12297],q 0 [12297,20534,17909],q 6 [17909],q 1 [20534,17909],q 2 [12297,20534],q 5 [12297,16438],q 1 [16438,20499],q 6 [21254],q 1 [16438,21254],q 1 [53255,20497],q 2 [12297,53255],q 8 [12297,21261],q 0 [12297,53255,21261],q 3 [12297,53255,21261],q 6 [21261],q 1 [53255,21261],q 2 [12297,53255,21261],q 8 [12297,17165],q 0 [12297,53255,17165],q 3 [12297,53255,17165],q 6 [17165],q 1 [53255,17165],q 8 [16397,324027],q 11 [16397],q 2 [20487,324027],q 6 [20487],q 1 [20487,16393,70075],q 2 [20487,70075],q 8 [16393,70075],q 1 [20487,53691],q 2 [20487,12297,53691],q 8 [12297,53691],q 5 [454671],q 2 [20487],q 11 [454671],q 2 [20487,454671],q 5 [454667],q 8 [16825,454667],q 2 [20487,454667],q 8 [16825],q 2 [20487,12298],q 2 [12297],q 2 [20487,12297],q 8 [12729],q 2 [20487,12729],q 1 [20487],q 1 [20487,16394],q 6 [20487,12729],q 1 [20487,16393],q 1 [20487,8635],q 2 [20487,8635],q 8 [8635],q 6 [16501,16397],q 5 [17945],q 8 [8635,17945],q 6 [20487,17945],q 11 [17945],q 1 [20487,8635,17945],q 5 [561156],q 1 [16929,561156],q 2 [20495,561156],q 2 [20486],q 10 [20486],q 1 [20486,20497,98311],q 2 [20486,98311],q 5 [339975],q 2 [20486,20493,339975],q 10 [13765],q 0 [16394,4327,13765],q 19 [13765],q 1 [16394,4327],q 2 [4327,13765],q 7 [20486],q 6 [20486],q 1 [20489,122880],q 1 [20486,20489,122880],q 8 [16394,12517],q 1 [20486,16394],q 2 [20486,12517],q 1 [20486,16393,70039],q 0 [20486,16393,70039],q 2 [20486,70039],q 7 [12298,16653],q 0 [12298,16653],q 4 [12298,16653],q 8 [12298,16653],q 6 [16653],q 1 [20486,16653],q 2 [20486,12298],q 15 [20486],q 16 [16653],q 1 [20486,53655],q 4 [12298],q 1 [20486,20487],q 6 [20486,20487],q 2 [20486,20487],q 2 [20486,20487,12298],q 15 [20486,20487],q 10 [20486,20487],q 1 [339972,8899],q 4 [12297],q 3 [16397,20797,593927],q 0 [16397,20797,593927],q 1 [20797,593927],q 2 [20797,593927],q 4 [16397,593927],q 3 [20488,16501],q 0 [20488,16501],q 2 [20488,901127],q 2 [20486,20885],q 1 [20486,20885],q 5 [16789],q 1 [20486,16789,20497],q 8 [28691],q 1 [20486,20885,28691],q 7 [20486,16789],q 0 [20486,16789],q 6 [20486,16789],q 1 [20486,16789],q 0 [20486,12693,17978],q 1 [20486,17978],q 8 [17978],q 8 [20493,17953],q 0 [20493,339975,17953],q 3 [20493,339975,17953],q 2 [20493,339975],q 4 [339975,17953],q 7 [20486,12693],q 0 [20486,12693],q 2 [20486,12693],q 6 [20486,12693],q 4 [12693],q 0 [16394],q 7 [20486,8599],q 0 [20486,8599],q 1 [20486,8599],q 2 [20486,8599],q 4 [8599],q 5 [8599],q 1 [20486,8599,20489],q 8 [20489],q 8 [20497,28691],q 1 [20485,20497,28691],q 2 [20485,98304],q 1 [20485,20497,98304],q 16 [339976],q 1 [20485,339976],q 10 [20485],q 8 [16397,28988],q 0 [20485,16397,28988],q 3 [20485,16397,28988],q 1 [20485,28988],q 2 [20485,28988],q 4 [16397,28988],q 6 [20485,16637],q 0 [20486,16394,233877],q 2 [20486,233877],q 1 [20486,16394,233877],q 8 [28680],q 1 [20485,28680,20497],q 1 [20485,28680],q 1 [16394,21278],q 4 [16394,12517],q 7 [16394],q 19 [21278],q 2 [12517,21278],q 1 [20485,20489,28680],q 8 [20489,28680],q 1 [20485,20489,122880],q 2 [20485,20489,122880],q 6 [20485,28691],q 1 [20485,16394,28691],q 8 [16394,28691],q 7 [20485,28687],q 0 [20485,28687],q 2 [20485,28687],q 6 [20485,28687],q 4 [28687],q 2 [20485,28903],q 8 [16394,28903],q 3 [20485,16394,28903],q 6 [20485,28903],q 1 [20485,16394,28903],q 1 [20485,16394],q 0 [16394,12517],q 2 [20485,12517],q 1 [20485,16393],q 4 [16393],q 8 [28687],q 7 [20493,339987],q 2 [12298],q 2 [20485,12298],q 0 [20485,16393],q 3 [20485,16393],q 2 [20485,28675],q 19 [20485],q 3 [20485,28680],q 7 [20493,339979],q 0 [20493,339979],q 8 [20493,339979],q 16 [339979],q 1 [339979,339987],q 8 [28672,28680],q 1 [20485,28672,28680],q 0 [20485,16394],q 8 [20489,122880],q 4 [16390],q 1 [20797,593928],q 2 [20797,593928],q 4 [16397,593928],q 7 [16389],q 18 [16389],q 10 [12290],q 11 [12290],q 11 [20490],q 18 [20490],q 0 [16389,20490],q 2 [12290,20490],q 1 [65544,20544],q 8 [65544],q 8 [22105],q 6 [22105],q 1 [8198,17237,22105],q 0 [8198,17237,22105],q 0 [17469,12298],q 1 [4096,17469],q 6 [4096,17469],q 2 [4096],q 2 [4096,12298],q 19 [17469],q 2 [20485,12297],q 1 [8197],q 2 [8197,98319],q 7 [8197],q 0 [8197],q 13 [8197],q 1 [8197,20497],q 3 [20497,98319],q 4 [98319],q 16 [16637],q 0 [8198,13141],q 1 [8198,20497],q 2 [8198,13141],q 2 [8197,98396],q 4 [8197,98396],q 1 [20484,16409],q 2 [20484],q 15 [20484,16409],q 2 [8197,20493,340060],q 3 [16397,20493],q 0 [16397,20493],q 2 [8197,20493],q 4 [8197],q 3 [20493,339972],q 2 [20493,339972],q 0 [8199,20493,339972],q 0 [12293,65547,20773],q 1 [65547,20773],q 11 [20773],q 5 [8197],q 11 [20495],q 1 [8197,94755],q 2 [8197,20495,94755],q 8 [20495,94755],q 5 [8197,16478],q 2 [8197],q 11 [20499],q 1 [8197,16478,20499],q 8 [16478,20499],q 6 [16913,20497],q 1 [20490,16913,20497],q 0 [16393,20550],q 2 [20482,20550],q 7 [16393,20550],q 1 [20482,16393,20550],q 6 [21594],q 1 [8197,16478,21594],q 11 [21594],q 8 [16478,21594],q 7 [8196],q 2 [8196,98304],q 12 [],q 5 [8196],q 6 [20495,90657],q 10 [20495],q 1 [8196,90657],q 2 [8196,20495,90657],q 3 [16394,12517],q 6 [12517],q 1 [16929],q 2 [8197,20495],q 8 [16478,21593],q 0 [8197,16478,21593],q 3 [8197,16478,21593],q 6 [21593],q 1 [8197,16478,21593],q 11 [21593],q 8 [20546,17293],q 0 [12293,20546,17293],q 3 [12293,20546,17293],q 1 [20546,17293],q 6 [16390],q 1 [16390,20489,122995],q 0 [16390,20489,122995],q 2 [20489,122995],q 2 [8196,20493,340059],q 6 [20493,340059],q 3 [20497,98317,593927],q 2 [98317,593927],q 0 [8196,8197],q 8 [20499],q 1 [8196,8197],q 2 [8196,8197],q 20 [20499],q 0 [16389],q 1 [16389],q 1 [16389,20489],q 4 [16389],q 6 [16389],q 2 [20489,122895],q 15 [16389],q 3 [20489,122895],q 0 [20489,122895],q 8 [20489,122895],q 16 [20489],q 4 [122895],q 2 [8196,8197,20493],q 0 [8196,8197,20493],q 20 [20493],q 20 [16397],q 6 [20485,29671],q 5 [29671],q 1 [8192,20485,29671],q 11 [8192],q 0 [8196,16473,20497],q 6 [16473,20497],q 1 [8196,16473,20497],q 0 [8196,12377],q 1 [8196,20497],q 6 [12377],q 2 [8196,12377],q 3 [16390,20485],q 4 [16390,28672],q 0 [16393,70527],q 2 [20480,70527],q 1 [20480,16393,70527],q 0 [16397,324479],q 1 [20480,324479],q 2 [20480,324479],q 2 [20480,20550],q 1 [20480,16393,20550],q 1 [16394,20546],q 0 [16389,553855],q 2 [20480,553855],q 1 [20480,16389,553855],q 4 [4627],q 0 [20490,20491],q 1 [20490,4627,20491],q 1 [16393,70179],q 2 [20495,70179],q 3 [12293,65544],q 1 [65536,65544],q 2 [12293,65536],q 0 [8198,914261],q 7 [8198],q 8 [20480],q 6 [20480],q 1 [20480,8198,914261],q 4 [8198],q 3 [8196,8197],q 20 [20480],q 0 [9279,20489],q 6 [4096],q 1 [4096,9279,20489],q 5 [9279],q 0 [8196,91005],q 10 [20480],q 1 [20480,8196,91005],q 2 [20480,8196,91005],q 4 [8196],q 1 [16393,20544],q 8 [20544],q 0 [9111,17305],q 1 [9111,17305],q 2 [12290,9111],q 0 [17277,8199],q 3 [20480,17277],q 7 [8199],q 6 [20480,17277],q 8 [20480,17277],q 1 [20480,17277],q 19 [17277],q 20 [20480,17277],q 1 [8199],q 1 [8196,20569],q 7 [8196,20569],q 3 [8196,20569],q 6 [20569],q 0 [8196,20569],q 0 [20497,98313,618519],q 1 [20497,98313,618519],q 8 [20488],q 10 [16390],q 6 [16390,118897],q 1 [16390,20488,118897],q 0 [8199,21405,1757203],q 11 [1757203],q 10 [1757203],q 1 [8199,21405,1757203],q 2 [8199,21405],q 1 [20480,17282],q 1 [20796,970757],q 2 [20796,970757],q 13 [970757],q 1 [8197,20499,94979],q 8 [20499,94979],q 2 [8197,94979],q 0 [12294,16905,22214],q 2 [12294,22214],q 8 [22214],q 1 [16905,22214],q 0 [13181,16394],q 8 [20480,13181],q 16 [20480],q 2 [20480,13181],q 1 [20480],q 1 [20480,16394],q 0 [21477,1781779],q 2 [8192,21477],q 10 [1781779],q 6 [21477,1781779],q 0 [13181,16389],q 11 [20480,13181],q 1 [20480,16389],q 10 [16389],q 19 [13181],q 7 [12293],q 0 [12293],q 2 [12293,98312],q 1 [20484,8219],q 2 [20484,8219],q 0 [8198,21333,1794067],q 8 [1794067],q 4 [8198,1794067],q 6 [1794067],q 1 [8198,21333,1794067],q 2 [8198,21333],q 2 [21020,554271],q 1 [16389,21020,554271],q 1 [8198,17237,22106],q 8 [22106],q 1 [339976,339987],q 0 [20493,339987],q 0 [13181,8197],q 0 [9087,16393],q 1 [20480,9087,16393],q 2 [20480,9087],q 0 [9087,12297],q 1 [20480,9087],q 0 [9087,18149],q 1 [20480,9087,18149],q 4 [18149],q 7 [12297,53255],q 1 [4096,53255],q 2 [4096,12297,53255],q 8 [20497,99231],q 20 [20497],q 2 [8199,99231],q 0 [17277,16393],q 1 [20480,17277,16393],q 1 [20497,98313,618496],q 2 [98313,618496],q 7 [20490,4625],q 3 [20490,4625],q 17 [],q 11 [16386],q 6 [4625],q 16 [16386],q 10 [16386],q 6 [16386],q 0 [13285,20497],q 6 [13285,20497],q 2 [8192,13285],q 4 [8192,13285],q 8 [8192,13285],q 1 [8192,20497],q 5 [13285],q 2 [98309,655375],q 0 [20485,28683],q 2 [20485,28675,28683],q 17 [20485],q 8 [21517],q 1 [16390,8307,21517],q 0 [16390,8307,21517],q 2 [8307,21517],q 4 [12294],q 1 [16394,20711],q 2 [98310,635],q 0 [16390,913521],q 7 [16390],q 2 [20480,913521],q 1 [20480,16390,913521],q 2 [98307,98319],q 0 [12293,65544,16737],q 3 [12293,65544,16737],q 8 [65544,16737],q 11 [16737],q 6 [12293,16737],q 13 [16737],q 6 [16397,20798],q 1 [8197,20798],q 0 [16397,20798],q 8 [20499,66307],q 1 [20499,66307],q 2 [12293,66307],q 7 [8198,21333],q 3 [8198,21333],q 5 [8198],q 2 [8199,98311],q 1 [8199,20497,98311],q 1 [65544,20833],q 6 [12293,20833],q 18 [20497],q 18 [8199],q 0 [8199,20497],q 20 [12290,20497],q 2 [12290,8199],q 0 [13277,20489],q 8 [16386,13277],q 2 [13277,20489],q 5 [13277],q 1 [16386,20489],q 7 [20489],q 4 [28680],q 0 [13277,20485],q 3 [16386,13277],q 1 [16386,20485],q 2 [13277,20485],q 19 [13277],q 5 [561163],q 1 [16929,561163],q 0 [13277,8199],q 1 [16386],q 13 [8199],q 1 [16386,8199],q 2 [13277],q 2 [13277,8199],q 4 [16386,13277],q 20 [16386,13277],q 4 [8199],q 1 [16394,815111],q 10 [815111],q 0 [16394,12517,815111],q 19 [815111],q 2 [12517,815111],q 8 [28680,16637],q 0 [20485,28680,16637],q 3 [20485,28680,16637],q 1 [20485,28680,16637],q 1 [20544,364554],q 11 [364554],q 2 [12293,20544,364554],q 0 [8196,12377,21670],q 1 [8196,21670],q 10 [21670],q 2 [8196,12377,21670],q 6 [12377,21670],q 8 [21670],q 4 [28675],q 4 [28675,28691],q 0 [13373,17474],q 1 [4096,17474],q 8 [17474],q 0 [12293,16394,65767],q 3 [12293,16394,65767],q 6 [12290],q 2 [12290,98312],q 3 [20497,98311],q 8 [12290],q 2 [12290,98311],q 0 [9111,16389],q 1 [9111,16389],q 8 [12290,9111],q 16 [9111],q 4 [12290,9111],q 1 [20497,99223],q 2 [12290,99223],q 0 [9087,16397],q 3 [16393,20493,340036],q 2 [20493,340036],q 1 [20490,16913],q 7 [20490,16913],q 3 [20490,16913],q 8 [20490,16913],q 2 [8199,98307],q 5 [8199],q 1 [8199,20497,98307],q 7 [16393,20490],q 2 [12290],q 3 [16393,20490],q 8 [16393,20490],q 6 [16390,20593],q 7 [16390,20593],q 3 [16390,20593],q 0 [16390,20593],q 2 [8192,20593],q 2 [8198,20493,340823],q 3 [8197,20497,98396],q 0 [16389,553959],q 2 [8192,553959],q 6 [16389,553959],q 1 [8192,16389,553959],q 5 [16389,553959],q 0 [16390,1020017],q 2 [8192,1020017],q 3 [8192,16390,1020017],q 6 [16390,1020017],q 1 [8192,16390,1020017],q 0 [9183,20493],q 5 [9183],q 2 [9183,20493],q 2 [8196],q 4 [98307,98315],q 0 [17381,20497],q 6 [17381,20497],q 1 [8192,17381,20497],q 2 [8194,20593],q 5 [454664],q 8 [16825,454664],q 11 [454664],q 7 [16389,20486],q 2 [8192],q 2 [8192,20486],q 0 [17381,20485],q 3 [8192,17381],q 2 [8192,20485],q 8 [8192,17381],q 1 [20485],q 1 [8192,17381],q 0 [9087,8197],q 1 [20480,9087,8197],q 11 [20480,9087],q 8 [20480,9087],q 1 [20497,98314,9099],q 2 [98314,9099],q 0 [12293,65544,16393],q 3 [12293,65544,16393],q 2 [8197,12382],q 0 [8197,12382],q 1 [16390,20489,122880],q 13 [8192],q 3 [20485,28691],q 0 [20497,98309],q 3 [20497,98315],q 0 [21397,8197],q 6 [12290,21397],q 1 [21397],q 1 [21397,8197],q 0 [20493,339975],q 1 [339975],q 6 [20493,339975],q 0 [9087,16389],q 7 [12293,20493],q 0 [12293,20493],q 2 [20488,118789],q 0 [21565,16393],q 2 [4096,21565],q 6 [4096,21565],q 1 [4096,21565],q 0 [17381,20486],q 4 [8192,17381],q 6 [17381],q 0 [16397,324671],q 2 [4096,324671],q 7 [20497,98317],q 8 [20497,98317],q 3 [20484,16397,323591],q 0 [20484,16397,323591],q 5 [16397,323591],q 2 [20484,323591],q 1 [20484,323591],q 0 [20493,341055],q 2 [4096,20493,341055],q 2 [8192,21022],q 0 [12657,20485],q 3 [8194,12657],q 1 [8194,20485],q 16 [8194],q 15 [20485],q 2 [8194,12657],q 7 [20497,98313],q 1 [20497,98304,98313],q 2 [98304,98313],q 8 [16397,324511],q 0 [8199,16397,324511],q 3 [8199,16397,324511],q 1 [8199,324511],q 2 [8199,324511],q 3 [16394],q 0 [17277,16397],q 2 [12293,20486,20493],q 0 [13181,8199],q 3 [20480,13181],q 1 [20480,8199],q 20 [20480,13181],q 2 [8199],q 11 [20480],q 3 [12293,16394],q 0 [12293,16394],q 2 [20480,12293],q 3 [20497,98308],q 11 [8194],q 2 [8194,98308],q 0 [13285,16389],q 6 [13285,16389],q 3 [12298,16653],q 7 [20493,339975],q 1 [4096,339975],q 2 [4096,20493,339975],q 0 [12657,20497],q 8 [8194,12657],q 1 [8194],q 1 [8194,20497],q 5 [12657],q 0 [13373,20497],q 2 [4096,13373],q 4 [4096,13373],q 1 [4096,20497],q 19 [13373],q 5 [13373],q 1 [20796],q 1 [8197,20796],q 2 [8196,20569],q 6 [20569,1749011],q 8 [1749011],q 1 [8196,20569,1749011],q 10 [1749011],q 6 [20497,99303],q 0 [20497,99303],q 2 [8192,99303],q 1 [8192,20497,99303],q 1 [8196,8197,20497],q 0 [8196,8197,20497],q 0 [13373,21570],q 7 [21570],q 1 [4096,21570],q 2 [4096,13373,21570],q 0 [20849,1900563],q 2 [8194,20849],q 1 [8194,20849,1900563],q 8 [21641],q 10 [21641],q 0 [8196,16473,21641],q 6 [16473,21641],q 1 [8196,16473,21641],q 2 [8194],q 1 [8194,16450],q 3 [12293,16450],q 8 [16450],q 2 [8194,12293],q 8 [21405],q 6 [21405],q 1 [8196,8283,21405],q 0 [8196,8283,21405],q 2 [8196,8283,21405],q 1 [8196,16929],q 3 [20489,123967],q 0 [20489,123967],q 1 [4096,20489,123967],q 8 [16397,323676],q 0 [8197,16397,323676],q 3 [8197,16397,323676],q 1 [8197,323676],q 0 [16753,12293],q 1 [8194,16753],q 8 [8194,16753],q 6 [20493,724997],q 13 [724997],q 0 [8197,95103],q 1 [20480,8197,95103],q 0 [13373,20490],q 1 [4096],q 1 [4096,20490],q 13 [20490],q 1 [20497,98572],q 2 [12298,98572],q 1 [8199,16929],q 2 [8199,20495],q 0 [8199],q 11 [20833],q 4 [16394,340199],q 0 [9111,21401],q 7 [21401],q 1 [9111,21401],q 2 [12290,9111,21401],q 5 [9111],q 0 [20490,1110545],q 4 [4096,1110545],q 1 [4096,20490,1110545],q 6 [4096,1110545],q 10 [4096],q 1 [20486,16393],q 0 [9111,20497],q 1 [9111,20497],q 1 [8196,20499,90881],q 6 [20499,90881],q 10 [20499],q 0 [9279,20497],q 2 [4096,9279],q 1 [4096,9279],q 1 [20796,970762],q 2 [20796,970762],q 13 [970762],q 0 [9279,22177],q 7 [22177],q 8 [22177],q 1 [4096,9279,22177],q 6 [4096,22177],q 0 [8197,20497],q 1 [8197,20497,98307],q 2 [8197,98307],q 0 [13277,21530],q 7 [21530],q 1 [16386,21530],q 20 [20482],q 1 [20482,8196,8197],q 8 [20482],q 6 [20482],q 0 [21565,1871891],q 5 [1871891],q 8 [1871891],q 5 [12293,16450],q 1 [16450,20499],q 8 [16450,20499],q 6 [16389,20485],q 0 [16389,20485],q 1 [16389,20485],q 1 [16393,20550],q 2 [12290,20550],q 3 [16393,20550],q 8 [16393,20550],q 2 [20484,323611],q 2 [98311],q 2 [8192,98311],q 0 [17301,20490],q 8 [12290,17301],q 16 [17301],q 4 [12290,17301],q 1 [17301,20490],q 0 [12297,54143],q 1 [20480,54143],q 0 [16753,20485],q 2 [8194,20485],q 5 [16753],q 8 [21021,655375],q 0 [16389,21021,655375],q 3 [16389,21021,655375],q 2 [21021,655375],q 4 [16389,655375],q 6 [20569,20495],q 1 [16389,20488,20489],q 11 [20488,20489],q 8 [20488,20489],q 2 [20488,20489],q 0 [12294,8715],q 1 [8715,20497],q 2 [12294,8715],q 0 [12298,16653,21730],q 2 [12298,21730],q 10 [21730],q 6 [16653,21730],q 1 [16653,21730],q 1 [20489,122887],q 1 [20486,20489,122887],q 2 [20486,20489,122887],q 4 [122887],q 2 [12293,98315],q 1 [16390,20485],q 2 [12290,20485],q 4 [12290],q 6 [12294,16905],q 0 [12294,16905],q 3 [12294,16905],q 1 [8194,16905],q 2 [12294],q 2 [8194,12294],q 0 [17469,22113],q 3 [17469,22113],q 8 [22113],q 1 [4096,17469,22113],q 5 [17469],q 1 [16450],q 1 [20486,16450],q 1 [20484,8219,16393],q 6 [20484],q 0 [12293,16450],q 1 [16450,20546],q 3 [8196,20493,339975],q 0 [8196,20493,339975],q 10 [20493,339975],q 1 [8196,339975],q 2 [8196,20493,339975],q 7 [12293,20485],q 0 [12293,20485],q 2 [12293,20485],q 0 [17381],q 0 [17381,12293],q 2 [8192,12293],q 2 [8196,21642],q 6 [16473,21642],q 8 [21642],q 1 [8196,16473,21642],q 10 [21642],q 8 [18305],q 1 [8715,18305],q 8 [17309],q 6 [17309],q 1 [8196,8283,17309],q 0 [8196,8283,17309],q 2 [8196,8283],q 1 [20497,98310,8827],q 2 [98310,8827],q 0 [16389,20486],q 6 [16389,20486],q 1 [20484,16393],q 0 [20484,12313,16393],q 3 [20497,99391],q 0 [20497,99391],q 2 [4096,99391],q 1 [4096,20497,99391],q 0 [21397,1863699],q 2 [12290,21397],q 0 [13373,16394],q 1 [4096,16394],q 0 [9279,16397],q 4 [4096,9279],q 1 [20484,20485,28680],q 2 [20484,20485],q 6 [20484,20485],q 0 [9279,20493],q 1 [65544],q 1 [20484,20485,16394],q 3 [20486,16789],q 2 [8194,20486],q 18 [8196],q 0 [8196,20497],q 0 [16393,70719],q 1 [4096,16393,70719],q 2 [4096,70719],q 0 [16753,20493],q 16 [339987],q 3 [20493,339987],q 2 [12290,20486],q 0 [17469,22114],q 2 [4096,22114],q 1 [4096,17469,22114],q 5 [339987],q 1 [20497,339987],q 0 [12293,66535],q 1 [8192,66535],q 6 [12293,66535],q 2 [8192,12293,66535],q 0 [17277,12293],q 11 [20480,17277],q 2 [20480],q 1 [65544,20546],q 0 [12297,54335],q 1 [4096,54335],q 2 [4096,12297,54335],q 2 [20484,12297],q 0 [16753,20486],q 4 [8194,16753],q 19 [20486],q 8 [20489,123420],q 0 [16389,20489,123420],q 3 [16389,20489,123420],q 1 [16389,20489,123420],q 2 [20489,123420],q 0 [21397,8199],q 8 [12290,21397],q 1 [21397,8199],q 16 [21397],q 20 [12290,21397],q 0 [13181,16393],q 1 [20480,16393],q 0 [17469,20497],q 1 [4096,17469,20497],q 7 [12294],q 0 [17277],q 0 [17277,12294],q 1 [4096,16653],q 15 [4096],q 2 [8197,98304],q 1 [8197,20497,98304],q 1 [8196,16473],q 3 [8196,16473],q 6 [16473],q 2 [12290,8196],q 7 [8199,17309],q 0 [8199,17309],q 2 [8199,20493],q 1 [8199,17309],q 4 [8199,17309],q 18 [20485],q 18 [16394],q 0 [17301,8196],q 6 [12290,17301],q 1 [17301,8196],q 3 [8192],q 4 [98311],q 5 [98311],q 1 [16394,20710],q 2 [12293,20710],q 3 [16394,20710],q 0 [16394,20710],q 0 [8196,16473,16397],q 6 [16473,16397],q 0 [20486,1020309],q 5 [1020309],q 3 [8192,20486,1020309],q 6 [20486,1020309],q 1 [8192,20486,1020309],q 2 [98304,98315],q 1 [20497,98304,98315],q 4 [98304,98315],q 0 [8199,20493,340895],q 8 [20493,340895],q 1 [8199,340895],q 2 [8199,20493,340895],q 0 [12293,20497],q 0 [12293,66431],q 1 [20480,66431],q 1 [20489,122880,20497],q 0 [21469,8199],q 6 [16386,21469],q 8 [16386,21469],q 1 [16386,21469],q 19 [21469],q 20 [16386,21469],q 2 [21469,8199],q 1 [20484,20485,16393],q 1 [20497,98314,98315],q 2 [98314,98315],q 2 [20486,323991],q 4 [16397,323991],q 0 [16397,324583],q 1 [8192,324583],q 20 [16397,20796],q 6 [12294],q 1 [8197,16478],q 1 [16393,20490],q 1 [339968,339987],q 2 [20488,553079],q 6 [16389,553079],q 1 [16389,20488,553079],q 0 [13285,17386],q 6 [13285,17386],q 10 [17386],q 2 [12293,20489],q 1 [20489,122899],q 1 [20544,65895],q 2 [12293,20544,65895],q 2 [98315,98317],q 4 [98317],q 1 [20497,98371],q 2 [12293,98371],q 6 [12517,21278],q 10 [21278],q 0 [17381,20493],q 2 [8192,20493],q 5 [17381],q 1 [8197,339987],q 3 [20484,12297,53255],q 0 [20484,12297,53255],q 1 [20484,53255],q 2 [20484,12297,53255],q 1 [16390,20593],q 2 [12290,20593],q 8 [20497,98306],q 3 [20499,13057],q 0 [20499,13057],q 8 [20499,13057],q 1 [20499],q 1 [8199,20499],q 2 [13057],q 2 [8199,13057],q 20 [20499,13057],q 0 [20493,340967],q 3 [20497,98309],q 3 [20497,98307],q 1 [20497,98307,98309],q 1 [65544,20497],q 3 [16397,20797],q 0 [16397,20797],q 2 [20797],q 2 [8197,20797],q 2 [98304,98308],q 0 [17381,12294],q 2 [8192,12294],q 10 [12294],q 1 [8192,339987],q 4 [8192,99303],q 0 [21469,8197],q 0 [8196,12377,17574],q 1 [8196,17574],q 10 [17574],q 6 [12377,17574],q 8 [21020,1339405],q 2 [98308],q 2 [8192,98308],q 5 [561160],q 1 [16929,561160],q 0 [16753,12294],q 19 [12294],q 5 [17877],q 1 [8739,17877],q 2 [8199,98308],q 1 [8199,20497,98308],q 6 [16389,21021],q 0 [16389,21021],q 3 [16389,21021],q 8 [21021],q 2 [8194,21021],q 3 [8194],q 3 [20491,17101],q 0 [20491,17101],q 1 [20491,17101],q 8 [20491,17101],q 2 [20491],q 2 [12293,20491],q 1 [20798],q 8 [16397,22317],q 0 [16397,323591,22317],q 3 [16397,323591,22317],q 2 [323591,22317],q 4 [16397,323591],q 0 [21565,16394],q 4 [4096],q 19 [21565],q 8 [1748992],q 6 [20569,1748992],q 10 [1748992],q 1 [8196,20569,1748992],q 2 [20485,28683],q 7 [20485,28683],q 1 [20485,28683],q 0 [17301,22394],q 1 [17301,22394],q 5 [17301],q 6 [16389,21022],q 13 [8194],q 2 [8194,21022],q 0 [17301,20486],q 19 [17301],q 1 [17301,20486],q 18 [20486],q 1 [20486,20487,16393],q 4 [8194],q 0 [20497,98675],q 1 [8194,20497,98675],q 2 [8194,98675],q 1 [20490,66067],q 6 [12293,66067],q 2 [8194,98311],q 0 [8197,20493,340060],q 3 [8197,20493,340060],q 8 [16386],q 20 [16386],q 0 [13277,8197],q 2 [13277,8197],q 8 [20489,122899],q 0 [13277,20490],q 1 [16386,20490],q 2 [13277,20490],q 0 [9111,20485],q 1 [9111,20485],q 2 [20485,28900],q 7 [8197,20574],q 4 [16386],q 13 [16386],q 2 [8197,20574],q 4 [16389,552968],q 2 [552968,20491],q 5 [16389,552968],q 1 [16389,552968,20491],q 11 [20491],q 8 [552968,20491],q 4 [28672,28691],q 1 [8194,339987],q 2 [8194,20493],q 1 [20487,8635,16393],q 8 [8635,16393],q 1 [8198,21333],q 0 [17301,20485],q 3 [12290,17301],q 1 [17301,20485],q 0 [21397,16393],q 1 [21397,16393],q 0 [17277,8196],q 20 [20497,98319],q 2 [8199,98319],q 0 [16753,21414],q 1 [8194,16753,21414],q 8 [20574,18405],q 0 [8197,20574,18405],q 3 [8197,20574,18405],q 6 [18405],q 1 [8197,20574,18405],q 19 [16389],q 20 [12290],q 3 [20497,98313,618503],q 2 [98313,618503],q 2 [12293,20711],q 3 [20490,12817],q 0 [20490,12817],q 2 [20490,12817],q 8 [20490,12817],q 16 [20490],q 6 [12817],q 1 [20490],q 0 [21397,16394],q 1 [21397,16394],q 1 [20484,53275],q 1 [8197,20574],q 8 [20490,66067],q 0 [12293,20490,66067],q 3 [12293,20490,66067],q 0 [16394,1110245],q 2 [4096,1110245],q 1 [4096,16394,1110245],q 6 [4096,1110245],q 2 [12290,21022],q 11 [16738],q 13 [16738],q 1 [8198,339976],q 1 [8198,16929],q 2 [8198,20495],q 6 [20497,98395],q 1 [8196,20497,98395],q 0 [8198,20497,99159],q 1 [8198,20497,99159],q 2 [8198,98304],q 2 [8198,98312],q 1 [8198,20497,98312],q 0 [8198,20497,98312],q 1 [20796,970758],q 2 [20796,970758],q 13 [970758],q 1 [8198,20499,873217],q 2 [8198,873217],q 1 [20486,20490,4625],q 6 [20486,4625],q 0 [8199,13213],q 1 [8199,20497],q 2 [8199,13213],q 3 [8199,20493,340895],q 1 [16394,20544],q 8 [13214,17345],q 0 [8199,13214,17345],q 3 [8199,13214,17345],q 1 [8199,17345],q 2 [8199,13214],q 20 [20495],q 8 [13214,21441],q 0 [8199,13214,21441],q 3 [8199,13214,21441],q 1 [8199,21441],q 2 [8199,13214,21441],q 1 [16393,339975],q 2 [20485,69647],q 3 [16393,69647],q 0 [16393,69647],q 8 [17309,21677],q 0 [8199,17309,21677],q 3 [8199,17309,21677],q 10 [21677],q 6 [17309,21677],q 1 [8199,17309,21677],q 2 [8199,21677],q 2 [8199,21678],q 1 [8199,17309,21678],q 10 [21678],q 20 [21678],q 8 [17310,22561],q 0 [8199,17310,22561],q 3 [8199,17310,22561],q 1 [8199,17310,22561],q 2 [8199,22561],q 4 [8199,17310],q 5 [8199,17310],q 8 [552968,22505],q 0 [16389,552968,22505],q 3 [16389,552968,22505],q 1 [16389,552968,22505],q 5 [16530],q 1 [20484,16530],q 8 [16530],q 3 [8199,21407,18477],q 0 [8199,21407,18477],q 6 [21407,18477],q 8 [21407,18477],q 1 [8199,21407,18477],q 16 [18477],q 20 [18477],q 2 [98319],q 1 [16438,21253],q 3 [8196,20497,98311],q 0 [8196,20497,98311],q 1 [8196,20497,98311],q 2 [8196,98311],q 4 [8196,98311],q 5 [8196,98311],q 1 [20484,16409,16393],q 0 [12293,16449,21454],q 2 [12293,21454],q 1 [16449,21454],q 8 [16397,20493],q 8 [16397,20797],q 1 [20797],q 1 [8199,20797],q 2 [8199,20797],q 0 [17277,12298],q 7 [12293,20545],q 0 [12293,20545],q 8 [20545],q 2 [12293,20545],q 1 [20545],q 1 [16394,20545],q 4 [16390,8307],q 0 [16390,8307],q 5 [16390,8307],q 1 [16390,8307],q 2 [8307,20495],q 0 [20485,12297,28724],q 3 [20485,12297,28724],q 1 [20485,28724],q 16 [20798],q 1 [20497,98307,98312],q 2 [98307,98312],q 2 [20489,122880,20493],q 6 [20495,946721],q 8 [20495,946721],q 1 [8199,946721],q 2 [8199,20495,946721],q 0 [13285,20485],q 6 [13285,20485],q 1 [8192,20485],q 2 [8199,99228],q 1 [8199,20497,99228],q 3 [8199,20497,99231],q 4 [8199,99231],q 0 [12293,16450,8477],q 1 [16450,8477],q 2 [12293,8477],q 1 [20485,16438],q 16 [16438],q 1 [8196,8283],q 3 [8199,20497,98304],q 1 [8199,20497,98304],q 2 [8199,98304],q 4 [16397,323592],q 1 [20491,323592],q 2 [20491,323592],q 1 [65536,16394],q 1 [65536],q 1 [65536,16450],q 4 [12293,65536],q 1 [16389,20486,553367],q 2 [20486,553367],q 1 [20497,98313,618500],q 0 [20497,98313,618500],q 2 [98313,618500],q 3 [12293,20497,98368],q 0 [9279,18081],q 8 [18081],q 1 [4096,9279,18081],q 6 [4096,18081],q 1 [16386,339987],q 2 [12293,20485,20493],q 5 [18133],q 8 [18133],q 1 [20484,8219,18133],q 6 [20484,18133],q 0 [12293,20485,16450],q 1 [20485,16450],q 4 [12293,65943],q 1 [20486,20487,16394],q 2 [20484,24805],q 1 [20484,16394,24805],q 8 [65547],q 1 [65547],q 1 [20486,65547],q 1 [20488,20489],q 8 [16449],q 4 [12293,16449],q 5 [18210],q 10 [18210],q 6 [118789,18210],q 1 [20488,118789,18210],q 0 [12293,20486,16450],q 0 [13373,20489],q 1 [4096,20489],q 8 [65544,20833],q 0 [12293,65544,20833],q 3 [12293,65544,20833],q 2 [12293,65544,20833],q 0 [17301,8199],q 1 [17301],q 1 [17301,8199],q 20 [12290,17301],q 1 [65544,20491],q 2 [12293,65544,20491],q 8 [65544,20491],q 0 [16389,20488,12405],q 11 [20488,12405],q 2 [20488,12405],q 8 [20488,12405],q 1 [16389,20488],q 6 [12405],q 6 [20499,946945],q 8 [20499,946945],q 1 [8199,20499,946945],q 2 [8199,946945],q 1 [65544,20499],q 2 [20486,98304],q 0 [9183,21473],q 7 [21473],q 1 [16386,9183,21473],q 2 [9183,21473],q 2 [98304,98317],q 4 [98304,98317],q 1 [20497,98575],q 2 [12298,98575],q 1 [65544,20834],q 11 [20834],q 0 [9183,12293],q 3 [16386,9183],q 1 [16386,9183],q 8 [16386,9183],q 2 [9183,12293],q 0 [16394,913637],q 0 [16389,552968],q 8 [552968],q 1 [16389,552968],q 2 [552968,20495],q 4 [16913],q 1 [20490,16913,20491],q 1 [16390,4641],q 0 [12293,65547,16677],q 11 [16677],q 13 [16677],q 2 [12293,65547],q 3 [20497,98304,98311],q 2 [8199,1224719],q 0 [12293,65547,16394],q 7 [16389,21021],q 2 [8192,21021],q 1 [65547,16450],q 1 [65547,20546],q 2 [12294,98312],q 0 [12294],q 0 [13285,21482],q 7 [21482],q 1 [65547,20497],q 3 [12293,16393,69696],q 1 [20485,16654],q 16 [16654],q 0 [12298,16654],q 1 [16393,20545],q 1 [16393,20546],q 7 [12294,21001],q 0 [12294,21001],q 2 [12294,21001],q 1 [21001],q 1 [21001,16394],q 6 [12294,21001],q 2 [4325,21838],q 1 [16394,4325,21838],q 6 [4325,21838],q 10 [21838],q 1 [20488,65655],q 6 [12293,65655],q 2 [12293,20488,65655],q 1 [8198,872993],q 2 [8198,20495,872993],q 2 [12293,65767],q 3 [16394,20709],q 0 [16394,20709],q 1 [16394,20709],q 8 [16394,20709],q 6 [20709],q 8 [12297,16438],q 1 [20486,16438],q 0 [16390,20490,115217],q 2 [20490,115217],q 4 [16390,115217],q 1 [16390,20490,115217],q 0 [17381,21770],q 1 [8192,17381,21770],q 2 [12293,20709],q 1 [20489,20497,98304],q 2 [20489,98304],q 1 [4365,20497],q 6 [4365],q 0 [8196,20569,20493],q 6 [20569,20493],q 2 [8196,20569,20493],q 0 [8199,17309,21678],q 11 [21678],q 0 [16394,20489],q 1 [16394,20489],q 8 [16394,20489],q 2 [12293,20490],q 3 [16394,20490],q 0 [16394,20490],q 1 [16394,20490],q 8 [16394,20490],q 8 [16394,21838],q 19 [21838],q 0 [20489,16397,123196],q 1 [20489,123196],q 2 [20489,123196],q 1 [20488,8311],q 8 [20495,553507],q 1 [16389,553507],q 2 [20495,553507],q 0 [12293,20488,16501],q 6 [16501],q 2 [12293,20488],q 0 [17381,21769],q 7 [21769],q 10 [21769],q 6 [17381,21769],q 1 [8192,17381,21769],q 2 [8192,21769],q 2 [20593],q 2 [20593,12297],q 2 [12293,20488,20489],q 8 [16394,450789],q 2 [20487,450789],q 1 [20487,16394,450789],q 3 [20485,16393,28740],q 2 [20485,28740],q 2 [20484,20485,12298],q 15 [20484,20485],q 3 [16397,323591,20493],q 0 [16397,323591,20493],q 2 [323591,20493],q 3 [20489],q 0 [20489],q 0 [12293,16449],q 1 [20489,16449],q 1 [20489,16450],q 8 [20489,122944],q 0 [12293,20489,122944],q 3 [12293,20489,122944],q 1 [20489,122944],q 6 [16389,16501],q 7 [12294,16905],q 1 [8192,16905],q 7 [12293,16449],q 1 [16449],q 1 [20490,16449],q 3 [20490],q 1 [20490,16450],q 8 [20493,340508],q 0 [16389,20493,340508],q 3 [16389,20493,340508],q 2 [20493,340508],q 1 [20491,66255],q 2 [12293,20491,66255],q 8 [20491,66255],q 0 [12293,20493,16450],q 2 [12293,8479],q 8 [16450,20765],q 0 [12293,16450,20765],q 3 [12293,16450,20765],q 11 [20765],q 1 [16450,20765],q 8 [16450,20766],q 1 [16450,20766],q 1 [20490,324115],q 2 [20490,324115],q 1 [16450,8476],q 11 [8476],q 1 [20497,98315,4609],q 1 [16394,20710,21385],q 2 [12298,4365,21234],q 6 [4365,21234],q 10 [21234],q 8 [21406,18593],q 0 [8199,21406,18593],q 3 [8199,21406,18593],q 1 [8199,21406,18593],q 2 [8199,21406],q 11 [8477],q 10 [20482],q 11 [20482],q 1 [20482,16394],q 2 [20482,12293],q 1 [16450,8478],q 2 [12293,20493],q 8 [16450,8479],q 1 [20544,16741],q 8 [20544,16741],q 11 [16741],q 8 [20545,487432],q 0 [12293,20545,487432],q 3 [12293,20545,487432],q 1 [20545,487432],q 2 [12293,20545,487432],q 0 [12293,20545,487443],q 1 [20545,487443],q 2 [12293,98304],q 1 [20499,8963],q 8 [20499,8963],q 2 [12293,8963],q 8 [22401],q 1 [8715,22401],q 2 [12294,8715,22401],q 0 [12294,8715,22401],q 4 [12294,8715],q 5 [12294,8715],q 1 [8715,20499],q 8 [2199571],q 2 [20491,553679],q 1 [16389,20491,553679],q 8 [20491,553679],q 2 [12294,20485],q 7 [12294,20485],q 0 [12294,20485],q 2 [8197,13057],q 2 [12294,20488],q 2 [98312,12881],q 2 [12294,20491],q 0 [12657,16389],q 4 [8194,12657],q 8 [20490,553491],q 0 [16389,20490,553491],q 3 [16389,20490,553491],q 6 [16389,553491],q 1 [16389,20490,553491],q 2 [20490,553491],q 2 [12294,98304],q 2 [20486,12297],q 1 [16389,20486],q 8 [552975],q 2 [20486,552975],q 4 [16389,552975],q 8 [12297,553012],q 0 [16389,12297,553012],q 3 [16389,12297,553012],q 1 [16389,553012],q 2 [12297,553012],q 1 [20489,20497,98312],q 0 [9087,12293],q 2 [20485,29663],q 5 [29663],q 2 [12297,21022],q 1 [16394,340196],q 2 [20493,340196],q 2 [12298,21022],q 1 [16389,20489,122880],q 0 [9183,20485],q 2 [9183,20485],q 1 [16389,20490,20491],q 0 [16389,20490,20491],q 2 [20485,98312],q 1 [8196,20569,1748995],q 6 [20569,1748995],q 10 [1748995],q 1 [16389,20491],q 11 [20491,13005],q 2 [20491,13005],q 8 [20491,13005],q 2 [21020,1339402],q 11 [1339402],q 1 [16389,21020,1339402],q 16 [1339402],q 1 [8192,16450],q 0 [20490,16913],q 8 [21021,655368],q 0 [16389,21021,655368],q 3 [16389,21021,655368],q 1 [16389,21021,655368],q 2 [21021,655368],q 4 [16389,655368],q 5 [16389,655368],q 5 [147467],q 2 [20484,12313,147467],q 8 [147467],q 0 [13373,16393],q 1 [4096,16393],q 7 [16390,8307],q 2 [8307,20493],q 0 [16390,12401,20485],q 2 [12401,20485],q 4 [16390,12401],q 6 [16390,12401],q 0 [16390,12401],q 1 [16390,20489],q 2 [12401,20489],q 7 [16390,12401],q 1 [16390],q 1 [16390,20490],q 10 [16390,12401],q 2 [12401],q 2 [12401,20490],q 1 [20750,18657],q 2 [12298,20750],q 2 [20593,12298],q 2 [20485,28787],q 4 [16390,28675],q 8 [28683],q 1 [16390,53363],q 2 [12297,53363],q 1 [16390,53255],q 10 [1175565],q 2 [20711,1175565],q 1 [16390,20488,20489],q 2 [12290,98308],q 2 [20491,733297],q 1 [16390,20491,733297],q 8 [20491],q 2 [20493,340083],q 0 [17277,16389],q 1 [20480,17277,16389],q 7 [16393,69639],q 2 [4096,69639],q 0 [16393,69639],q 1 [339976],q 0 [16390],q 19 [16390],q 1 [16390,339976],q 2 [8196,323675],q 6 [16397,323675],q 1 [16390,339987],q 8 [17989],q 1 [20486,8599,17989],q 0 [20486,8599,17989],q 2 [20495,557169],q 8 [20495,8739],q 1 [16390,8739],q 5 [147464],q 1 [16389,8739],q 16 [8739],q 2 [12297,98304],q 0 [20485,29043],q 5 [29043],q 1 [20484,16394],q 3 [20484,20485],q 0 [20484,20485],q 0 [8199,914333],q 6 [20480,914333],q 8 [20480,914333],q 1 [20480,8199,914333],q 1 [20486,339976],q 3 [16397,323592],q 0 [16397,323592],q 16 [323592],q 10 [20487],q 2 [20487,323592],q 0 [20487],q 11 [17737],q 16 [17737],q 2 [20484,20485,28683],q 1 [20484,20485,28691],q 2 [20484,69659],q 1 [20484,16393,69659],q 1 [20497,593920],q 2 [98317,593920],q 3 [20484,16393,69639],q 0 [20484,16393,69639],q 2 [20484,69639],q 1 [16390,21550],q 8 [21550],q 2 [12401,21550],q 10 [20484],q 1 [323592],q 2 [20484,323592],q 2 [4865],q 2 [98317],q 2 [98314],q 2 [98309],q 4 [98308],q 5 [98308],q 1 [8739],q 1 [339987],q 1 [339979],q 3 [20493,339975],q 4 [339975],q 1 [339972],q 2 [20798],q 1 [323595],q 2 [323592],q 3 [16397],q 3 [16397,323591],q 0 [16397,323591],q 2 [323591],q 0 [20490,4625],q 1 [20490,4625],q 1 [20497,98313],q 2 [98313],q 2 [323584],q 1 [20489],q 0 [20489,16397],q 3 [20489,122887],q 0 [20489,122887],q 1 [20488],q 2 [20711],q 1 [323588],q 2 [20709],q 2 [12517],q 0 [16394,4325],q 3 [16394,4325],q 6 [4325],q 2 [4325],q 2 [20550],q 2 [69647],q 3 [16393,69639],q 2 [69639],q 1 [16393,69639],q 1 [20750],q 0 [12298,20749],q 3 [12298,4365],q 1 [4365],q 3 [8199,17309],q 8 [13213],q 3 [8199,13213],q 6 [13213],q 0 [8198],q 1 [8198],q 2 [8198],q 3 [12297],q 0 [8196],q 1 [16905],q 0 [8198,21333],q 0 [16393,20490],q 0 [8196,16473],q 0 [20486],q 3 [8196,8283],q 0 [8196,8283],q 2 [20482],q 2 [8963],q 0 [16389,20489],q 3 [16389,20489],q 1 [20482],q 3 [12293],q 3 [8197],q 0 [8196,16397],q 1 [8196],q 11 [20488],q 0 [17301],q 3 [16389],q 3 [20480],q 1 [8198,17237],q 0 [8198,17237],q 1 [16653],q 3 [8197,20497],q 3 [12293,20493],q 3 [8199],q 3 [20480,8199],q 3 [20485],q 1 [20491],q 0 [13181],q 0 [9087],q 3 [8199,17310],q 0 [8199,17310],q 1 [8199,17310],q 3 [16386],q 3 [16386,8199],q 1 [323591],q 0 [20490,4627],q 3 [16390],q 0 [16389,20493],q 3 [16389,20493],q 0 [16390,12298],q 15 [16390],q 1 [8196,20499],q 3 [20486],q 3 [12293,20497],q 1 [16386,8197],q 0 [20849],q 1 [8194,20849],q 8 [16478],q 0 [12294,16394],q 1 [16654],q 0 [21477],q 6 [21477],q 1 [8192,21477],q 1 [20491,4813],q 2 [21022],q 3 [8199,16397],q 0 [8199,16397],q 3 [8198],q 0 [8199,21405],q 3 [8199,21405],q 1 [8199,21405],q 3 [16393,20493],q 0 [20490],q 3 [20493],q 1 [339968],q 3 [20482],q 3 [20482,8199],q 1 [20482,8199],q 6 [13285],q 3 [12297,53255],q 1 [53255],q 0 [16394,4327],q 2 [4327],q 0 [16753],q 0 [8198,20497],q 0 [9279],q 3 [20487,16397],q 0 [20487,16397],q 2 [98315],q 4 [98315],q 1 [20482,16389],q 0 [16389,12297],q 3 [16389,12297],q 4 [8192],q 1 [20482,16393],q 0 [9183],q 2 [9183],q 8 [21020],q 2 [21020],q 0 [21397],q 6 [118789],q 1 [20488,118789],q 0 [13373],q 0 [8196,20493],q 2 [8196,20493],q 0 [21469],q 2 [21469],q 0 [20485,12297],q 3 [20485,12297],q 3 [12298],q 0 [16389,552975],q 2 [552975],q 3 [12290],q 3 [12290,8199],q 2 [8307],q 0 [17469],q 3 [8199,20493],q 0 [8199,20493],q 1 [8194,16389],q 3 [20499],q 3 [8199,20499],q 0 [20499],q 0 [8199,20499],q 16 [20499],q 1 [20534],q 3 [12297,20534],q 3 [8199,20497],q 2 [552960],q 1 [16389,552960],q 0 [20490,16397],q 3 [20490,16397],q 2 [20710],q 1 [9111],q 0 [13277],q 0 [20486,12298],q 2 [8196,20495],q 0 [12657],q 3 [8199,21406],q 1 [8199,21406],q 0 [8199,21406],q 3 [8199,21407],q 0 [8199,21407],q 6 [21407],q 1 [8715],q 3 [16389,552968],q 2 [552968],q 0 [20485,16397],q 3 [20485,16397],q 1 [16389,21021],q 2 [21021],q 0 [16394,20493],q 3 [16394,20493],q 0 [16390,20489],q 0 [12293,16393],q 3 [12293,16393],q 0 [12293,20489],q 3 [12293,20489],q 3 [12293,16449],q 1 [20544],q 0 [16390,20490],q 3 [12293,20545],q 8 [12382],q 3 [8197,12382],q 3 [20487,12297],q 0 [20487,12297],q 0 [21565],q 1 [20546],q 15 [20487],q 0 [12293,20546],q 15 [20499],q 2 [98310],q 0 [12294,20490],q 0 [12294,20497],q 0 [8197,20493],q 3 [8197,20493],q 2 [20482,12294],q 0 [16389,12298],q 2 [552971],q 1 [8192,16389],q 1 [16389,20490],q 1 [16390,20488],q 0 [20485,12298],q 3 [8199,13214],q 0 [8199,13214],q 0 [20491],q 2 [20484,12298],q 15 [20484],q 0 [20486,16393],q 0 [20495],q 0 [8197,16397],q 3 [8197,16397],q 0 [12293,20490],q 0 [20486,12297],q 2 [20796],q 0 [20486,16394],q 3 [20487,16393],q 0 [20487,16393],q 1 [16438],q 3 [20487]]
def B_25_3 : BT (List (List Nat)) := BT.empty
lemma B_25_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_25 3 xs.toFinset) B_25_3 := .empty
def U_25_4 : List Nat := []
def P_25_4 : BT (Option BoundPool) := buildPoolsSubBT 12 W_25 r_25 S_25 ps_25 U_25_4
def N_25_4 : List NodeSpec := [([0,11,3,12,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_25_4 : checkNodesBT W_25 g_25 F_25 P_25_4 A_25 B_25_3 4 N_25_4 = true := by decide +kernel
def B_25_4 : BT (List (List Nat)) := buildBucketsBT W_25 N_25_4
set_option maxRecDepth 500000 in
lemma B_25_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_25 4 xs.toFinset) B_25_4 :=
  buildBucketsBT_sound (by decide) gp_25 W_25_ok (buildPoolsSubBT_sound S_25_ok) A_25_ok B_25_3_ok C_25_4
def U_25_5 : List Nat := (r 0 11)
def P_25_5 : BT (Option BoundPool) := buildPoolsSubBT 12 W_25 r_25 S_25 ps_25 U_25_5
def N_25_5 : List NodeSpec := [([8,0,2,3,15,4],[0],[]),([21,0,1,2,3,4],[],[]),([27,0,25,3,4,5],[],[]),([33,31,0,1,3,4],[],[]),([31,0,1,3,35,4],[],[]),([38,40,2,36,4,5],[],[]),([31,0,1,3,42,4],[],[]),([31,0,1,3,44,4],[],[]),([9,0,10,3,12,4],[1],[0]),([9,0,11,3,4],(r 2 4),[0]),([48,0,2,3,4,5],[6],[]),([49,8,0,51,3,4],[7],[]),([55,0,1,3,4,5],[8],[]),([8,0,2,3,56,4],[9,10],[]),([58,8,0,2,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_25_5 : checkNodesBT W_25 g_25 F_25 P_25_5 A_25 B_25_4 5 N_25_5 = true := by decide +kernel
def B_25_5 : BT (List (List Nat)) := buildBucketsBT W_25 N_25_5
set_option maxRecDepth 500000 in
lemma B_25_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_25 5 xs.toFinset) B_25_5 :=
  buildBucketsBT_sound (by decide) gp_25 W_25_ok (buildPoolsSubBT_sound S_25_ok) A_25_ok B_25_4_ok C_25_5
def U_25_6 : List Nat := ([0,1,4,5]++r 9 116)
def P_25_6 : BT (Option BoundPool) := buildPoolsSubBT 12 W_25 r_25 S_25 ps_25 U_25_6
def N_25_6 : List NodeSpec := [([41,32,31,0,1,3,4],(r 11 5),[]),([31,60,1,3,4],(r 16 6),[]),([61,62,0,2,3,4,5],[22],[0]),([8,0,63,2,3,4,64],[4,23],[]),([8,0,2,3,4,65],([0,4]++r 24 5),[]),([8,0,2,3,4,66],([0]++r 27 5),[]),([68,8,0,2,3,4],[0,4,14,27,32,33,34],[]),([69,67,8,0,2,3,4],[4,14,33,35,36,37],[]),([67,8,0,2,3,4,14],[4,28,35,36,38],[]),([8,0,2,3,13,4,14],[28,38,39,40],[0]),([57,50,8,0,2,3,4],[0,4,28,41,42],[0]),([8,0,70,2,3,4],[0,27,28,40,43],[]),([74,75,1,2,3,4,5],[],[]),([77,57,0,1,3,4,5],[],[]),([31,0,1,78,3,4,79],[5,13,14,44,45],[]),([80,0,1,2,3,18,5],[],[]),([41,31,0,1,3,16,4],[11,14,46,47],[0]),([31,0,1,3,16,4,34],[13,18,20,46,47,48],[0]),([50,49,8,0,2,3,4],[4,27,28,40,49],[0]),([41,81,31,0,1,3,4],[14,18,20,46,50],[]),([82,8,0,2,3,4],[0,4,27,28,33,51,52],[]),([85,0,2,16,4,84,5],[53,54],[]),([9,8,0,2,3,12,4],[4,55],[0]),([50,9,8,0,2,3,4],[4,27,28,40,55],[]),([86,0,1,3,18,4,5],[],[]),([0,1,2,3,18,87,5],[],[]),([0,1,88,3,90,4,5],[56],[]),([91,0,1,88,3,4,5],[],[]),([0,2,93,3,4,94,5],[],[]),([0,1,97,3,16,4,5],[57,58],[]),([0,22,25,3,26,4,5],[21,59,60,61],[0]),([98,99,0,1,3,4,5],[62],[0]),([0,2,3,100,102,4,5],[],[]),([103,104,0,1,2,3,4],[],[0]),([0,1,2,3,18,105,5],[63],[]),([106,8,0,2,3,4],[0,14,27,33,64,65],[]),e6 [74] [],([32,81,31,0,1,3,4],[13,18,20,46,66],[]),([107,0,78,3,4],[5,18,40,67,68,69],[]),([108,8,0,2,3,4],[0,27,28,33,70,71],[]),([109,0,22,25,3,4,5],[61],[]),([112,0,1,114,3,4,5],[],[]),([115,0,2,16,4,66,5],[72,73],[]),([81,31,0,1,3,4,79],[5,13,45,46],[]),([0,88,3,102,4,17,5],[74],[]),([116,75,1,2,3,4,5],[],[]),([8,0,2,117,3,4],[0,14,27,28,33,40],[]),([118,31,0,1,3,4],[12,14,18,46,75,76],[]),([0,2,3,18,102,4,5],[53],[]),([121,0,1,2,3,120,5],[5],[]),([57,0,88,3,102,4,5],[77],[]),([0,1,2,3,52,122,5],[78],[]),([101,73,0,123,3,4,5],[],[]),([9,8,0,2,3,4,79],[4,5,14,33,45],[]),([124,8,0,2,4],[27,28,35,40,79,80],[]),([0,1,88,3,17,105,5],[81,82],[]),([0,1,2,3,19,4,20],[],[0]),([125,8,0,2,4],[28,38,40,83,84,85],[]),([9,8,0,2,3,4,126],[4,5,86],[]),([32,107,31,0,1,3,4],[13,18,20,40,46,87],[]),([49,8,0,2,3,4,79],[5,27,28,45],[]),([127,1,129,2,3,4,5],[],[]),([0,46,2,3,47,4,5],[88],[0]),([0,1,123,3,18,4,5],[89],[]),e6 [116] [],([28,32,31,0,1,3,4],[13,15,18,44,90],[0]),([0,1,53,3,54,4,5],[91],[0]),([131,31,0,1,3,4],[12,14,18,44,92,93],[]),([132,118,31,0,1,3,4],[89,94],[]),([8,0,134,2,3,4],[5,14,27,33,40,95],[]),([8,0,51,2,3,4],[0,4,9,10,14,27,33,96,97],[0]),([50,8,0,2,3,4,17],[27,28,42,98],[0]),([31,0,1,3,43,4,135],[5,14,18,46,99,100],[]),([138,0,140,1,3,4,5],[],[]),([32,31,0,1,3,4,135],[5,13,15,46,99],[]),([141,31,0,1,3,4],[12,13,18,44,101,102],[]),([57,8,142,2,3,4],[5,10,14,40,103],[]),([9,0,10,3,4],[1,4,5,27,68,104],[0]),([28,31,0,1,3,43,4],[13,18,40,90,100],[0]),([144,8,2,3,4],([4,10,40,85]++r 105 4),[]),([38,1,2,36,4,39,5],[109],[0]),([40,0,37,2,36,4,5],[110,111],[0]),([81,0,59,3,4],([5,18,40,68]++r 112 4),[]),([9,8,142,2,3,4],([10,14,40]++r 116 5),[]),([69,8,0,2,3,13,4],[5,14,27,37,39],[]),([9,8,0,2,3,4],[0,4,14,27,28,33,121,122],[]),([49,0,143,3,4],[5,27,40,68,123,124],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_25_6 : checkNodesBT W_25 g_25 F_25 P_25_6 A_25 B_25_5 6 N_25_6 = true := by decide +kernel
def B_25_6 : BT (List (List Nat)) := buildBucketsBT W_25 N_25_6
set_option maxRecDepth 500000 in
lemma B_25_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_25 6 xs.toFinset) B_25_6 :=
  buildBucketsBT_sound (by decide) gp_25 W_25_ok (buildPoolsSubBT_sound S_25_ok) A_25_ok B_25_5_ok C_25_6
def U_25_7 : List Nat := ([0,4,5,9]++r 11 6++[18,20,21,23,25,27,29,30,33]++r 36 7++r 44 7++[53,55,59,60,61,66,72,74,77,82,85,86,87,89,90,98,99,100,103,105,109]++r 117 4++r 125 781)
def P_25_7 : BT (Option BoundPool) := buildPoolsSubBT 12 W_25 r_25 S_25 ps_25 U_25_7
def N_25_7_0 : List NodeSpec := [([128,0,1,146,3,4,5],(r 125 11),[]),([128,147,0,2,3,4,5],([5,85]++r 136 7),[]),([147,0,148,2,3,4,5],[5,85,137,138,139,143],[]),([0,149,148,2,3,4,5],([14,53]++r 144 5),[]),([150,1,148,2,3,4,5],([5]++r 149 5),[]),([152,0,1,148,3,4,5],([5,45,135,146]++r 154 5),[]),([0,153,148,3,4,5],([21,45,146]++r 159 4),[]),([154,0,1,148,2,155,4,5],[89,155],[]),e6 [156,157] ([137]++r 163 4),e6 [156,155] [5,137,163,167],e6 [148,159] [14,168],([161,128,0,1,2,4,5],([14,163]++r 169 9),[]),([161,0,1,148,2,4,5],[14,163,170,172,173,174,178,179],[]),e6 [162,148] [14,146,156,180],([0,163,148,2,164,3,4,5],[89,146],[]),([0,163,2,164,3,4,5],[40,89,146,181,182,183],[]),e6 [25] ([72,146,149,163]++r 184 4),([0,163,165,3,4,5],([14,45]++r 188 5),[]),([166,0,2,3,4,5],[5,14,45,193,194],[]),e6 [148,167] [53,89,156,164,182,195],([168,127,1,3,4,5],(r 196 6),[]),([169,127,2,3,4,5],([197]++r 202 5),[]),([161,127,1,2,4,5],([172,204]++r 207 6),[]),([170,127,1,3,4,5],([197,208]++r 213 5),[]),([168,75,1,3,4,5],(r 218 5),[]),([147,75,2,3,4,5],([85]++r 223 4),[]),([171,75,1,2,3,4],[14,20,220,227,228],[]),([161,75,1,2,4,5],([85,173,226]++r 229 5),[]),([75,1,165,2,3,4,5],([14,45,218,230]++r 234 4),[]),([75,1,165,3,4,5],[14,45,234,235,237,238],[]),u6 [138,139] [85,89,137,239],e6 [139,172] [85,89,137,239,240],([156,0,148,2,164,3,4,5],[89,165,241],[]),e6 [174,137] [89,220,239],([175,0,1,148,2,3,5],([5,14]++r 242 4),[]),([175,75,1,2,3,5],[14,85,246,247],[]),([0,176,177,2,178,3,4,5],[89,248],[]),([132,41,31,0,1,3,4],([20,40,226]++r 249 5),[]),([75,1,146,2,3,4,5],[85,218,226,254],[]),([132,32,31,0,1,3,4],[14,20,40,249,252,253,255,256],[]),([132,81,31,0,1,3,4],([14,20,40,226,249,252]++r 257 4),[]),([31,0,1,3,4,180],[5,20,261,262],[]),([31,0,1,3,181,4],[5,14,20,40,252,253,263,264],[]),([31,0,182,1,3,4],[5,14,20,40,226,249,252,253,265,266],[]),([183,1,177,3,4,5],([85]++r 267 5),[]),([31,0,1,3,4,79],[5,12,20,44,45,226,272],[0]),([41,31,0,1,3,4],[5,11,12,14,18,20,40,44,226,250],[0]),([31,0,1,3,4,34],[5,12,20,40,48,226,273],[0]),([31,0,1,3,43,4],[14,18,20,40,44,100,274],[0]),([31,0,59,1,3,4],[5,12,14,16,18,20,40,44,226,275],[0]),([81,31,0,1,3,4],([12,14,18,20,40,44,50,66,226,258]++r 276 4),[0]),([32,31,0,1,3,4],(r 12 4++[18,20,40,44,226,255]),[0]),([107,31,0,1,3,4],[5,12,14,18,20,40,44,87,226,280,281],[0]),e6 [84,184] [5,14,137],e6 [185,84] ([149,184]++r 282 4),e6 [186,84] [149,239,284,286,287],([67,154,156,0,1,2,4,5],(r 288 4),[]),([67,156,127,1,2,3,4,5],([208]++r 292 4),[]),([67,156,75,1,2,3,4,5],([234]++r 296 4),[]),e6 [156,187] [53,137,165,226],([127,1,2,3,187,4,5],([184,197,208,294]++r 300 5),[]),e6 [189,24] [40,85],([0,163,188,2,3,4,5,24],[85,137,181,220,305,306],[]),([31,0,1,190,3,4],[5,14,20,89,226,249,252,307,308,309],[]),u6 [61,45] [53,137,310],u6 [45,47] ([45,53,137,156]++r 311 4),u6 [46,45] [53,137,315],e6 [163,45] [53,137,181,185,316,317],e6 [191,24] [137,185,220,239,318,319],([127,1,2,3,45,4,5],[184,197,208,294,312,320,321,322],[]),([156,75,1,2,3,13,4,5],[5,218,234,299],[]),([147,127,2,3,4,5],[40,138,208,323,324],[]),([75,1,148,2,3,155,4,5],[296,325],[]),([192,0,1,2,3,194],[21,326,327],[]),([195,75,1,2,3,4,5,24],[220,234,328,329],[]),e6 [196,24] [40,220],u6 [113,112] [89,163,239,330],e6 [197,111] [89],e6 [198,111] [239],e6 [57,200] [53,331,332],([201,0,1,148,2,3,5],([14,137]++r 333 5),[]),([201,0,1,63,2,3,64,5],[89,338],[]),([75,1,63,2,3,4,5],([149,218,230,234,236]++r 339 5),[]),u6 [115,66] [72,163,344,345],e6 [203] ([53,89,149,184,239]++r 346 4),e6 [205,204] [14,350,351,352],e6 [204,206] ([14]++r 352 5),([101,95,0,2,3,16,4,5],[357,358,359],[]),([86,0,1,3,16,4,17,5],[89,360,361,362],[0]),e6 [73,207] [14,40,239,363,364],([169,75,2,3,4,5],[14,220,365,366,367],[]),([156,127,1,2,3,13,4,5],[5,197,208,295],[]),u6 [88,105] [14,21,89,368,369,370],([75,1,177,2,3,4,5],[85,149,234,236,267,296,298,371,372,373],[]),e6 [66,208] [14,163,345,355,374,375],([0,22,23,3,4,137,5],([240]++r 376 4),[]),([57,209,0,1,3,16,4,5],[364,370,380,381],[]),([75,1,148,2,164,3,4,5],[218,296,298],[]),([73,0,1,123,3,4,5],([137,364]++r 382 7),[0]),([101,71,73,0,2,3,4,5],[14,389],[0]),e6 [88,207] [14,40,89,370,390],([127,1,2,25,3,4,5],[5,184,197,209,391,392],[]),e6 [72,88] [14,89,164,393,394,395],u6 [74,24] [21,40,137,239,396,397],([71,0,1,88,123,3,4,5],[14,137,382,398,399],[]),e6 [74,16] [89,400],e6 [74] [5,53,89,149,184,239,397,400],([0,2,3,16,4,66,5],[5,29,72,345,375,401,402],[0]),e6 [210] [14,137,149,184,350,403],([0,1,2,211,36,4,5],([220]++r 404 4),[]),([8,0,2,3,4,14],[0,27,33,38,40,85,408],[0]),e6 [163,212] [53,137,181,185,409],u6 [116,24] [89,158,348,350,410],([128,0,1,88,3,4,5,24],[14,89,158,220,411],[]),e6 [201,93] [14,239,412,413],e6 [116] [137,149,184,239,348,350,410,414],([75,1,2,164,3,4,5],[5,230,234,236,415,416],[]),e6 [214,137] [239],([0,215,2,3,16,4,122,5],[14,137,417,418,419],[]),([75,1,2,25,3,4,5],[5,218,230,236,415,420,421],[]),([0,1,2,3,16,122,5,24],[14,364,422,423],[0]),e6 [66] [30,72,163,375,424,425,426],([101,0,2,3,100,16,4,5],[427],[0]),e6 [217,16] [5,53,72],([195,0,2,3,4,218,5],(r 428 6),[]),([101,0,2,3,18,16,4,5],[40,53,434,435],[0]),e6 [219,16] [5,53,436],([71,0,1,88,96,3,4,5],[14,85,89,239,437,438],[]),e6 [221,222] [53,137,163,439,440],([101,57,73,0,3,16,4,5],[137,441],[]),e6 [225] ([53,137,348,350]++r 442 5),([75,1,148,2,3,4,5],[218,230,234,236,296,298,420,447],[]),([101,71,0,88,2,3,4,5],[14,435,448,449],[]),e6 [227,122] [5,14,40,450],e6 [228,230] [89,149,220,451,452,453],([101,0,123,2,3,16,4,5],[40,454,455],[0]),([152,0,1,3,4,5],[5,21,45,154,157,456],[]),e6 [232,137] [89],e6 [234,7] (r 457 4),e6 [235,122] [40,149,461],e6 [154,236] [89,163,462],([0,88,2,3,102,4,5],[40,77,85,463],[0]),([231,0,173,2,3,4,137,5],[220,464],[]),([101,0,2,3,16,4,122,5],[14,40,53,74,417,465],[]),e6 [79,238] [220,466,467,468],e6 [113,239] [89,163,239,469,470],u6 [88,52] [89,164,471,472],e6 [241,24] [158,226],([75,1,146,3,4,5],[85,127,226,254,473],[]),e6 [241] [53,72,89,137,149,184,239,474,475,476],([0,1,2,3,16,17,105,5],[364,423,477,478],[0]),([57,0,1,3,242,4,5],[5,21,370,479,480,481],[]),([75,1,188,2,3,4,5,24],[85,220,234,482,483],[]),([0,2,3,4,244,5],[40,85,484,485],[]),e6 [154,25] [5,163,239,486],u6 [91,16] [5,53,72,137,163,360,487],([245,1,148,2,3,4,5],([14,53,85,146,149]++r 488 4),[]),e6 [173,172] [40,53,89,240],([101,0,88,3,16,4,17,5],[40,74,492],[0]),([71,0,1,2,3,16,122,5],[137,163,364,493,494],[]),([69,8,0,2,3,4],[5,14,27,33,37,495],[0]),([57,8,0,2,3,4],[0,4,5,14,27,33,40,41,85],[0]),([227,0,1,88,2,3,4,246],[89,423],[]),u6 [25,26] [5,21,60,163,181,391,486],([8,0,2,3,4,17,7],[0,5,220,496,497],[0]),([175,0,1,248,2,3,5],[14,244,498],[]),e6 [251] ([14,53,85,89,350,356]++r 499 6),([49,8,0,2,3,4,7],[5,14,27,33,40,220,505,506,507],[0]),e6 [252] [53,72,89,240,508,509],e6 [201,250] [5,14,149,163,510],e6 [253,156] [5,89,137],e6 [156,212] [53,137,165,288,511],e6 [227,254] [21,40,89],([170,75,1,3,4,5],([14,218,220,234]++r 512 4),[]),([227,0,1,88,3,4,17,5],[5,40,516],[]),e6 [229,255] [149,517,518],([0,2,3,102,16,4,17,5],[40,74,77,85,519,520,521],[0]),([227,57,0,1,88,3,4,5],[5,40,89,239,522],[]),e6 [128,52] [40,89,135,239,523],e6 [256] [53,149,184,348,524,525,526],e6 [201,257] [163,164,333,527],([71,0,1,2,3,16,254,5],[370,528,529],[]),e6 [198] [137,350,470,530,531],([175,0,1,259,2,3,5],[14,242,244,532],[]),([260,1,2,3,4,66,5],([30,375,497]++r 533 4),[]),([201,8,0,2,3,4],[5,14,27,33,537,538,539],[]),e6 [228,257] [163,164],([0,1,2,261,4,79,5],[72,85,350,540,541,542],[]),e6 [263] ([53,89,239]++r 543 4),e6 [264] [5,72,85,348,547,548,549],e6 [265,16] [89,550,551],e6 [266] ([53,137]++r 552 7),e6 [268] [149,184,226,559,560,561],([269,0,2,36,4,5],(r 562 7),[]),e6 [270] ([53,137,548]++r 569 4),([75,1,88,2,3,4,5,24],[14,220,296,341,393,573],[0]),e6 [116,16] [137,164,239,414],([127,1,2,3,52,4,5],([184,197,292,302]++r 574 4),[]),([8,0,143,2,3,4],[0,4,5,14,27,33,40,85,105,578],[0]),e6 [273] ([21]++r 579 6)]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_25_7_0 : checkNodesBT W_25 g_25 F_25 P_25_7 A_25 B_25_6 7 N_25_7_0 = true := by decide +kernel
def N_25_7_1 : List NodeSpec := [e6 [163,274] [53,137,181,409,585],e6 [266,24] [163,552,554,555,586],e6 [275] [5,149,184,587],e6 [100,89] ([5,21,348,364]++r 588 5),u6 [85,84] [5,53,137],e6 [276,84] [149,184,284,593],e6 [265] [5,89,149,184,239,550,551],([231,156,75,2,3,4,5],[14,40,218,234,298,299],[]),e6 [227,95] [5,21,40,89,594],u6 [140,137] [20,53,85,89,595],([101,57,0,88,3,16,4,5],[137,596,597],[0]),e6 [201,230] [89,149,220,333,334,336,451,598],e6 [277,231] [89,220,599,600,601],([0,1,2,3,89,4,246],[5,89,137,226,602,603],[]),([249,0,2,3,4,94,5,7],[20,604,605],[]),([192,0,1,2,3,279],([21]++r 606 4),[]),e6 [227,123] [40,350,610],e6 [252,137] [239],([101,0,2,3,16,4,254,5],[14,611],[]),([132,31,0,1,3,16,4],[5,20,40,89,252,253,309,364,612],[0]),([0,1,88,3,4,280,5],[137,602,613,614],[]),e6 [156,274] [53,137,165,511,615],e6 [148,274] [89,156,239,489,616,617,618],([57,0,1,3,16,4,76,5],[21,89,370,619],[0]),e6 [228,250] [5,40,149,163,510,620],([0,6,2,3,4,66,7],([30,220,375]++r 621 4),[0]),([28,281,0,2,3,4,5,7],[20,625,626],[]),([75,1,88,2,3,4,5],[149,218,226,234,341,372,394,573,627],[]),([231,0,2,282,3,4,5,24],[165,189,220,628,629],[]),e6 [283] [5,85,149,184,630,631,632],e6 [284] ([5,53,348,584]++r 633 4),([142,1,2,3,4,64,5],([14,40]++r 637 5),[]),([31,0,1,78,3,4],[12,14,18,20,40,44,226,642,643,644],[0]),([71,0,1,88,2,3,122,5],[89,137,163,450,645],[]),([127,1,236,2,3,4,5],[184,197,209,294,302,304,392,646,647,648],[]),([8,142,2,3,4],[5,9,40,118,120,220,539,649],[0]),([71,0,1,2,3,16,180,5],[137,163,364,650,651],[]),([142,1,2,3,4,66,5],[5,220,375,497,637,652,653],[]),u6 [114,111] [20,89,654,655,656],([260,1,2,3,4,65,5],([25,536]++r 657 5),[]),e6 [285] [21,85,348,350,662,663,664],([227,57,73,0,1,3,4,5],[5,40,89,239],[]),([75,1,2,3,187,4,5],[149,218,234,298,341,372,420,665,666,667],[]),e6 [63,286] [89,239,339,355,668,669,670],e6 [288,57] [21,40,89,671],e6 [289] ([89,239]++r 672 6),([28,0,2,3,204,4,5],([352]++r 678 4),[]),([75,1,2,3,290,5],([14,85,296,298]++r 682 4),[]),([258,0,1,123,3,16,4,5],[686,687],[0]),([71,73,0,1,123,3,4,5],[14,89,239,383],[]),e6 [57,291] [21,85,89,688],e6 [293] ([53,72,89]++r 689 4),e6 [294,79] [5,72,163,466,693],([0,295,23,3,4,5],([85,220]++r 694 6),[]),e6 [296,16] [14,21,137,700],e6 [298] ([149,184,314]++r 701 5),e6 [300] [72,137,149,184,348,350,706,707,708],e6 [201,281] [14,149,413,668,709,710],([0,22,25,3,4,5],[5,21,59,60,61,711],[0]),([92,0,2,3,4,94,5,7],[604,712,713],[0]),([95,0,1,96,3,16,4,5],[21,714,715],[0]),e6 [301] [72,89,239,378,716,717],e6 [301,137] [53,348,595],e6 [302] [5,72,89,149,184,248,348,718,719],([175,0,1,177,2,3,303,5],[89,720],[]),e6 [214] [53,72,240,378,721,722],e6 [156,304] [53,137,165,511,615],([0,22,261,3,4,5],[5,85,723,724],[]),([0,163,165,2,3,4,5],([14,45]++r 188 4++[725,726]),[]),([57,201,142,1,2,3,5],[14,40,137,637,727,728],[]),e6 [261,305] [5,14,729],([154,231,127,1,2,3,4,5],[45,209,292,730],[]),e6 [306,261] [5,14,350],([128,0,1,165,3,4,5],[45,137,188,238,731,732],[]),u6 [129,24] [40,89,220,350,733],([154,127,1,2,23,3,4,5],[5,45,197,209],[]),([38,1,2,36,4,5],([109,405]++r 734 5),[]),e6 [163,187] [40,53],u6 [62,45] [53,137,739],u6 [307,16] [53,89,137,740],([73,0,1,148,3,16,4,5],[89,137,741],[]),([8,0,2,3,133,4],[0,5,27,40,742,743],[0]),([75,1,2,3,45,4,5],[218,234,298,420,744,745,746],[]),([0,1,3,216,16,4,17,5],[89,361,747],[]),([57,0,1,3,216,4,5],[20,364,748,749],[]),([0,1,2,16,4,84,5],[5,53,282,283,444,750],[0]),([75,149,2,3,4,5],[144,220,298,751,752],[]),u6 [19,18] [5,220,348,434,753,754],u6 [72,73] [89,239,364,384,755],u6 [18,20] [5,220,348,375,444,753],([75,153,2,3,4,5],[85,218,220,298,756,757,758],[]),u6 [103,18] [5,348],e6 [308,16] [21,759],([28,0,2,93,3,4,5,7],[625,626],[0]),u6 [104,18] [5,348],u6 [109,25] [72,163,486],u6 [18,89] [5,348,370,375,444,754,760,761],e6 [227,18] [5,348,423,516],e6 [16,309] [14,137,163,370,762,763],([171,0,1,2,3,89,16,4],[5,137,163,764],[]),e6 [311,16] [21,765],e6 [313] [53,149,184,348,766,767,768],([57,0,1,3,242,16,4,5],[239,480,481],[]),([75,22,23,3,4,5],[85,218,298,694,769,770,771],[]),([57,0,1,3,216,16,4,5],[89,772],[]),([57,0,2,3,102,16,4,5],[77,137,773,774],[0]),u6 [98,52] [89,239,775],([31,0,1,3,16,4],[14,18,20,40,44,46,47,612],[0]),e6 [314] ([40,137,149,184,239]++r 776 4),([156,0,315,2,3,4,5],[5,780,781],[]),e6 [57,256] [89,524,526],e6 [16,210] [137,361,403],([71,316,0,1,2,3,16,5],[137,370,782,783],[]),([71,183,1,2,3,4,5],([149,226,382]++r 784 5),[]),([192,0,1,2,3,207],([14]++r 789 4),[]),e6 [71,216] [14,89,748],([0,1,88,2,3,89,4,246],[82,89,603],[]),([8,0,2,3,13,4],[0,14,27,39,40,793],[0]),e6 [71,242] [14,239,763,794],([9,8,0,2,3,4,7],[0,5,14,27,33,40,86,117,119,220],[0]),([317,127,1,2,4,5],([197,209,293]++r 795 4),[]),e6 [318,16] [89,799,800],([71,319,1,2,3,4,5],[20,149,226,382,784,801,802,803],[]),e6 [320] ([53,89]++r 804 4),e6 [304,163] [53,137,181,409,585],e6 [71,100] [21,361,364,382,808],e6 [52] [40,89,149,184,239,809,810,811],([8,0,63,2,3,4],[4,5,14,23,27,40,539,812,813],[0]),e6 [71,52] [5,40,814],e6 [16,321] [5,20,53,89,137,163,815],([75,1,148,2,3,16,4,5],[218,234,296,298,325],[0]),([75,1,2,3,52,4,5],[218,226,296,415,420,816,817,818],[]),e6 [323,7] [20,53,348,819,820,821],([128,127,1,2,3,16,4,5],[158,197,208,822],[0]),([0,1,88,3,89,4,17,5],[5,82,89,137,163,360,375,444,450,823,824],[0]),([324,0,1,88,3,16,4,5],[370,825],[]),e6 [148,52] [89,156,181,239,826,827,828],e6 [325,148] [21,89,137,829,830],u6 [325,128] [89,135,239,831],u6 [53,52] [89,239,472,826,832,833,834],([317,75,1,2,4,5],[220,230,297,835,836],[]),e6 [227,100] [5,21,40,89],([8,0,2,3,4,17],[5,27,33,85,98,496],[0]),e6 [320,220] [137,348,837],u6 [52,54] [89,181,226,239,574,826,838],e6 [211] [149,220,404,407,839],e6 [73,52] [5,89,239,364,840],u6 [99,52] [89,239,841],([130,0,2,3,4,66,5],[5,29,345,424,842,843],[]),e6 [326,220] [53,348,837],([130,31,0,1,3,4],[5,12,14,18,20,44,844,845],[0]),e6 [156,45] [53,137,165,288,846],([31,0,1,3,4,135],[5,12,18,40,46,99,847],[0]),([139,0,22,2,3,4,137,5],[14,53],[]),([0,1,329,2,4,135,328,5],[5,14,85,848,849,850],[]),([330,0,1,2,4,135,328,5],([5]++r 851 4),[]),([0,63,2,3,4,94,5],[5,53,137,855,856,857],[]),e6 [242,309] [14,370,762,763,777,858],([38,1,37,2,36,4,5],([109]++r 734 5++[859,860,861]),[0]),e6 [332] [72,85,862,863,864],([0,1,37,2,36,4,39,5],([736]++r 865 4),[0]),([333,75,1,2,3,4,5],[230,234,236,296,372,415,420,869],[]),([0,1,2,334,36,4,5],[53,406,566,736,870,871,872],[]),u6 [120] [5,137,149,184,239,873,874,875],([0,1,336,2,36,4,5],([53,406,566,736]++r 876 4),[]),([57,142,6,2,3,4,7],[103,220,880,881,882],[0]),([9,8,0,2,3,4],[0,4,5,14,27,33,40,55,85,86,117],[0]),u6 [16,90] [14,21,883],([8,0,2,10,3,4],[0,5,14,27,33,40,85,884,885],[0]),e6 [16,337] [14,748,886],([49,8,0,2,3,4],[0,5,9,14,27,33,40,49,85,506,507],[0]),([50,8,0,2,3,4],[0,5,14,27,33,40,42,85,887],[0]),([67,8,0,2,3,4],[0,4,14,27,33,36,40,85],[0]),([8,0,2,3,4,79],[0,5,45,85,272],[0]),e6 [308,242] [14,350,763,888],u6 [71,18] [370,889,890,891],([57,8,0,2,3,4,7],[4,5,14,27,33,40,103],[0]),([195,0,163,2,3,4,5,24],[181,220,318,892],[]),([28,31,0,1,3,4],[12,18,20,44,90,226,893],[0]),([338,8,0,2,3,4],[5,9,14,27,33,40,539,894,895,896],[0]),([0,6,2,3,4,65,7],[25,589,622,623,897,898],[0]),e6 [57,340] [89,220,899],([0,6,63,2,3,4,64,7],[898,900,901],[0]),([57,0,1,88,3,89,4,5],[5,89,164,369,589,592,902,903],[0]),([341,142,1,2,3,4,5],[14,149,639,640,641,649,652,904,905],[]),([142,1,63,2,3,4,64,5],[638,639],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_25_7_1 : checkNodesBT W_25 g_25 F_25 P_25_7 A_25 B_25_6 7 N_25_7_1 = true := by decide +kernel
def N_25_7 := N_25_7_0 ++ N_25_7_1
def B_25_7 : BT (List (List Nat)) := buildBucketsBT W_25 N_25_7
set_option maxRecDepth 500000 in
lemma B_25_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_25 7 xs.toFinset) B_25_7 := by
  have hP := buildPoolsSubBT_sound (pdepth := 12) (W := W_25) (raw := r_25) (pspecs := ps_25) (used := U_25_7) S_25_ok
  have hm0 := checkNodesBT_mem (by decide) gp_25 W_25_ok hP A_25_ok B_25_6_ok C_25_7_0
  have hm1 := checkNodesBT_mem (by decide) gp_25 W_25_ok hP A_25_ok B_25_6_ok C_25_7_1
  exact buildBucketsBT_of_mem (forall_append (hm0) hm1)
def U_25_8 : List Nat := ([0,5,12,14,20,21,24,29,33,40,44,45,53,60,68,72,74,77,82,85,89,103,125,126,130,134,135,137,138,139,145,146,147,149,150,155,156,158]++r 163 5++[170,172,174,181,182,184,185,188,189,195,196,197,202,208,209,213,218,220,226,230,234,236]++r 239 6++[246,248,249,253,261,263,265,267,272,282,283,284]++r 288 4++[294,295,296,298,299,300,302,305,307,312,314,318,325,326,330,333,334,336,338,339,341,345,348,350,352]++r 354 8++[364,369,370,372]++r 375 4++[382,384,385,387,388]++r 390 7++[402,406,409,412,413,415,417,420,423,424,426,427,429,431,432,434,435,439,440,441,444,448,450,452,453,455,460,461,462,464,465,466,468,469,470,472,479,482,486,488,489,490,492,493,496,497,504,511]++r 516 5++[522,527,528,533,536,537]++r 539 4++[548,564,566,574,584,585]++r 589 4++r 594 6++[602,604,605,606,611,612]++r 615 6++[622,625,626,628,630]++r 637 4++[646,649,650,652,656,657,659,660,663,668,669,670]++r 679 4++[688,689,690,694,696,699,700,709,710,713,720,723,725,727,729,731,732,736,748,749,750,753,754,755,761,763,769,773,774,776,777,780,782,784]++r 786 4++[793,795,806,811,812,822,824,826,832,837,843,844,847,849,850,854,855,858,863,866,867,871,873,880,881,891,893,894,895,898,900,901,903,904]++r 906 2017)
def P_25_8 : BT (Option BoundPool) := buildPoolsSubBT 12 W_25 r_25 S_25 ps_25 U_25_8
def N_25_8_0 : List NodeSpec := [([168,0,1,3,4,5,24],[5,14,21,156,196,220,906,907],[0]),u6 [146,24] [5,14,126,130,135,158,163,165,181,239,420,617,908],([0,1,146,3,4,5,24],[5,14,126,130,135,163,226,460,908],[0]),([0,149,2,3,4,5,24],[14,145,147,163,165,220,226,628,909],[0]),u6 [154,128] ([5,45,89,134,163,182,291]++r 910 6),([0,1,2,3,4,310,24],[5,14,21,89,350,916],[]),([342,1,2,3,4,5,24],[5,14,135,184,220,226,420,617,917,918,919],[]),([317,0,1,2,4,5,24],[5,14,21,156,220,289,314,795,920],[0]),u6 [154,148] [5,45,146,155,156,163,182,239,290,291,489,618,914,915],u6 [155,24] [45,85,155,165,181,226,420,460,617,921,922],u6 [148,164,24] [5,135,156,165,460,923,924],u6 [164,24] ([5,40,182,314,420]++r 923 5),u6 [154,156] [5,45,53,137,165,182,288,291,511,615,780],u6 [156,148] [5,14,89,137,155,156,167,241,615,618,928],([158,156,0,2,3,4,5],[5,14,45,165,780,929,930],[0]),([0,1,2,3,4,343,24],[14,45,165,350,931],[]),([170,0,1,3,4,5,24],([14,21,45,156,181,213]++r 932 4),[0]),u6 [165,24] [14,45,135,137,156,158,181,188,314,420,617,732,926,936],([0,1,165,3,4,5,24],[14,45,135,137,158,181,188,460,732,936,937,938],[0]),u6 [163,148] [5,85,89,146,155,156,189,195,409,489,585,618,939,940],([0,163,2,3,4,5,160],[14,45,165,725,941,942],[0]),e6 [344,24] [5,21,85,135,165,220,314,348,350,420,617,628,926,943,944],([128,127,1,2,3,4,5,24],[5,21,40,45,158,197,220,294,392,420,460,822,913,921,945],[]),([127,1,2,3,4,5,151],[5,197,392,628,921,946,947,948],[0]),([156,127,1,2,3,4,5],[5,40,184,197,295,392,460,511,921,949],[0]),e6 [346,24] [5,14,21,85,135,149,165,181,220,617,950,951],([75,1,2,3,4,5,24],[5,21,184,226,420,617,952,953],[0]),e6 [75,148] [14,21,40,85,89,146,156,158,236,298,489,618,928],e6 [156,75] [5,14,40,85,149,158,165,218,236,288,511,615,954],([226,75,1,2,3,4,5],[5,14,85,218,236,296,947,955],[0]),([347,0,1,2,3,4,24],[5,14,163,226,350,956],[]),([75,1,148,2,3,4,5,24],[5,14,45,218,226,236,298,325,420,617,618,957],[]),([75,1,148,2,3,4,5],[5,14,85,218,296,298,325,489,957],[0]),([158,75,1,2,3,4,5],[14,85,218,220,298,415,958,959,960],[]),([75,1,2,3,4,5,160],[5,14,45,218,234,236,298,628,961,962],[0]),u6 [158,148] [45,68,89,146,156,488,489,618,963],e6 [349] [85,89,239,350,964,965],u6 [148,83] ([5,155,156,164,729]++r 966 4),e6 [351,83] ([5,14,220,729,967]++r 970 7),u6 [177,303,83] [720,968,977,978,979],e6 [303,83] [5,14,720,729,967,970,971,977,978,979],u6 [177,24] [5,21,135,163,926,975,980,981],u6 [176,177] ([5,85,89,163,164,248,267,539]++r 982 6),e6 [186,177] ([14,85,89,248,267,921,975,982]++r 988 6),e6 [352] [5,72,149,460,994],([75,1,2,3,4,5,83],[85,218,246,372,970],[0]),e6 [354,79] ([5,45,72,89,220,239,350,466,539]++r 995 9),e6 [355] [53,137,226,272,1001,1004],e6 [357] ([72,163,350,539]++r 1005 4),([132,75,1,2,3,4,5],[5,85,218,236,296,298,341,372,1009,1010],[]),([132,179,0,1,3,4,79],[40,45,272,466,1011,1012],[0]),([132,31,0,1,3,4],[5,20,45,89,249,253,348,1013],[0]),([132,179,0,1,3,181,4],[5,14,20,40,89,263,1011,1012,1014,1015],[0]),e6 [358] [14,72,85,89,137,149,184,1016,1017,1018],e6 [132,359] ([14,20,163,226,650]++r 1019 5),([132,179,0,1,190,3,4],([5,14,40,89,226,307,1011,1012]++r 1024 7),[0]),e6 [360] ([14,72,89,137,149,163,239]++r 1031 4),([316,0,1,2,3,5,24],[5,14,156,1035,1036],[]),([0,1,177,3,4,5,30],[5,89,975,980,1037,1038],[0]),e6 [362] ([14,149,220,348,539]++r 1039 6),e6 [363] [53,72,89,137,226,239,272,1000,1045,1046],u6 [221,220] [14,40,72,85,89,226,440,1047,1048,1049],e6 [365] [14,53,72,85,89,137,1050,1051,1052],e6 [180] [5,163,261,1053,1054],e6 [57,348] ([21,85,89,137,589,965]++r 1055 5),e6 [366] [21,53,72,137,1055,1060],([57,175,0,1,2,3,5],[14,163,239,242,243,244,1061,1062],[]),e6 [57,186,83] [14,21,921,970,991,992,1063],e6 [57,367,83] [14,163,592,968,975,1064,1065],e6 [347] [5,53,72,85,89,137,226,239,272],e6 [367,83] [5,21,592,729,967,968,970,971,1065,1066],([57,0,1,3,4,76,5],[5,21,89,239,619,1067],[0]),e6 [57,368] [21,103,137,220,589,1055,1068,1069,1070],([0,1,148,3,4,5,151],[5,21,45,135,155,156,1071,1072],[0]),e6 [57,370] ([14,20,21,85,592,774]++r 1073 5),u6 [57,339,83] [14,21,589,592,774,967,968,1078,1079],e6 [57,371] ([21,53,103,163,592,774]++r 1079 7),e6 [372,220] [14,40,85,89,137,226,440,837,1049,1086,1087,1088],([0,1,373,3,4,17,5],[89,496,1089,1090,1091],[]),e6 [348,17] [85,137,496,965,1056,1058,1092,1093,1094],u6 [186,17,83] ([921,970,975,992,1093]++r 1095 4),([132,0,1,3,4,374,5],[5,20,89,239,1099],[]),e6 [375] ([149,220,539,564]++r 1100 7),u6 [67,156,24] [14,45,135,165,181,289,780,1107,1108,1109],u6 [67,163,24] [14,45,85,135,165,289,305,725,1108,1110],([67,127,1,2,3,4,5,24],([14,40,45,158,197,294,302,305,392,420,460,921]++r 1111 4),[0]),([67,75,1,2,3,4,5,24],[14,45,220,226,236,296,298,617,1115,1116],[0]),([67,75,1,2,3,4,5],[85,149,226,236,296,298,1114,1115],[]),e6 [377] [53,89,137,149,226,348,1117,1118,1119],e6 [378] [53,137,226,460,1120,1121,1122],u6 [139,137] ([14,53,240,348,378,464]++r 1123 4),e6 [379] [14,85,89,149,239,1127],e6 [380] [20,53,137,793,1128,1129,1130],([228,0,1,2,3,4,24],[14,40,45,137,350,1131,1132],[]),u6 [45] [21,45,53,137,156,312,1133,1134,1135],([67,154,0,1,2,4,5,24],[14,45,85,156,226,290,291,314,911,921,926,1136],[0]),u6 [156,13,24] [5,45,156,181,288,354,1137,1138],u6 [163,13,24] [45,156,165,220,318,354,1139],([127,1,2,3,13,4,5,24],[21,40,45,197,294,318,420,1140,1141,1142],[0]),([75,1,2,3,13,4,5,24],[21,45,218,220,298,617,1140,1143],[0]),e6 [382] ([20,21,53,137]++r 1144 4),([193,192,0,1,2,3,5],[14,239,326,1128,1148,1149],[0]),e6 [383] [14,21,53,137,149,184,1150,1151],u6 [195,24] [14,40,156,220,348,350,420,925,926,1152,1153],e6 [384] ([40,137,220]++r 1154 6),e6 [385] ([14,149,220,348,1153]++r 1160 5),e6 [386] [53,72,89,137,226,239,272,1165,1166,1167],e6 [387] ([20,72,137,163,239,375,496]++r 1168 4),e6 [388] [14,20,137,239,350,354,793,1168,1172,1173,1174],u6 [113,111] ([14,72,137,226,470,656]++r 1175 4),u6 [112,111] [14,89,137,226,330,470,656,1176,1179,1180,1181],u6 [67,111] [14,89,137,164,226,470,656,1108,1113,1176,1182,1183],u6 [13,111] [14,137,354,470,656,793,1176,1182,1184,1185],e6 [57,389] ([89,103,137,539,592,1055]++r 1186 5),e6 [389,17] [137,163,375,496,519,539,1186,1187,1188,1190,1191],e6 [390,79] [20,72,89,163,226,272,350,1000,1001,1166,1192,1193,1194],([0,1,2,3,220,79,5],[14,40,89,272,1000,1049,1195],[]),e6 [391] ([20,89,163,1193]++r 1196 5),u6 [173,137] [14,137,220,240,378,464,595,1201,1202,1203],e6 [101,148] [45,68,146,350,966,969,1204,1205],([101,156,0,2,3,4,5],[40,74,137,165,539,1206,1207],[]),([101,392,0,2,3,4,5],[5,40,85,137,967,1208,1209],[]),e6 [57,393] ([5,21,163,592,774,1085]++r 1210 5),([101,183,1,2,3,4,5],([5,85,149,788]++r 1215 4),[]),u6 [101,57,199] [14,21,89,1205,1219,1220,1221],e6 [394] [40,220,520,1216,1222,1223,1224],e6 [101,312] ([14,40,89,164,1215]++r 1225 9),e6 [395] [40,149,220,1137,1216,1234],([101,67,110,0,2,3,4],([14,53,1107,1113]++r 1235 7),[0]),e6 [396,83] [5,14,72,89,164,220,242,539,967,968,970,971,991,1242],([101,110,0,2,3,13,4],[14,793,1137,1236,1237,1238,1243],[0]),([147,0,2,3,4,5],([5,85,137]++r 1244 5),[]),u6 [222,220] [14,40,53,89,226,439,440,837,1049,1249,1250,1251],u6 [17,7] [375,426,496,497,520,1092,1252,1253],([0,1,2,3,397,5,24],[14,45,165,1254,1255],[]),e6 [201] [14,72,89,163,239,350,537,539,1252,1256,1257],e6 [13,397] ([5,14,45,53,1137,1141,1143,1204]++r 1258 4),e6 [399] [14,72,85,89,149,184,239,1262,1263,1264],e6 [400] ([14,85,89,137,239]++r 1265 5),e6 [57,398] ([5,21,53,89,465,592,774,1220]++r 1270 6),e6 [401,79] ([5,72,85,89,163,220,350,466,539,995,996,997,1000,1001]++r 1276 5),([0,1,401,3,4,5,30],[5,89,220,1216,1281,1282,1283],[]),([201,0,1,2,3,5,24],[14,45,137,181,333,537,1284,1285],[0]),([75,1,2,3,4,5,7],[5,218,226,234,298,372,628,668,1286,1287],[0]),e6 [177,7] [5,163,220,975,980,988,1288,1289,1290],e6 [402] ([45,85,89,239,348,356,539,1166]++r 1291 6),u6 [63,64,7] [338,460,901,1290,1297],e6 [403] [40,72,149,163,184,220,350,774,1205,1298,1299,1300],u6 [63,24] [5,21,45,135,137,314,355,812,926,1301,1302],e6 [63,83] [5,72,137,164,355,729,812,968,975,1301,1303],e6 [404,57] ([21,348,589,774,1275]++r 1304 5),e6 [63,79] [14,45,72,339,350,466,670,995,996,1000,1001,1166,1301,1303],([0,1,63,3,4,5,30],[5,14,89,355,777,812,1309,1310],[]),([183,1,2,3,4,5,7],[5,226,355,628,668,788,1311,1312],[]),([57,201,0,1,2,3,5],[14,137,239,333,334,336,589,1313,1314,1315],[]),e6 [57,405] ([5,89,103,163,539,592]++r 1316 5),u6 [65,7] [5,21,24,103,589,652,657,668,1290,1321],e6 [65] ([5,21,24,163,589,657,1290]++r 1322 4),u6 [57,199,7] [14,21,103,592,1290,1326,1327,1328],e6 [405,17] ([5,163,350,375,519,520,539,1093,1096]++r 1316 5++[1329,1330,1331]),([57,175,0,1,2,3,5,83],[5,14,163,242,243,244,592,975,1061,1062,1332],[]),e6 [201,67] [5,14,45,89,164,334,336,527,598,1107,1108,1114,1116,1235,1313,1333,1334],([260,1,2,3,4,17,5,7],[375,496,497,536,1092,1335,1336,1337],[0]),e6 [201,142] [14,40,149,333,350,413,537,539,598,637,640,649,727,1313,1338],e6 [142,63] [14,40,89,239,339,355,539,637,638,670,727,1339],e6 [57,142,7] [14,21,40,668,727,1055,1338],e6 [175,350] ([5,14,85,89,976,1061,1332]++r 1340 5),([338,142,1,2,3,4,5],[5,21,149,539,637,649,652,904],[]),([142,1,63,2,3,4,5],([5,40,149,339,539]++r 637 4++[652,727,904,1339,1345,1346]),[0]),([57,142,1,2,3,4,5,7],[5,21,40,103,637,639,640,668,727,904,1275,1347],[0]),([142,1,2,3,4,17,5,7],[5,220,375,497,637,640,668,727,1093,1335],[0]),([183,1,2,3,4,79,5],[85,226,786,788,995,1001,1217,1348],[]),([28,67,0,2,3,4,5,7],[5,53,356,539,625,626,679,1107,1235,1334,1349],[]),([0,1,146,3,4,5],[5,460,1350,1351,1352],[]),e6 [132,229,135] ([20,847,1010]++r 1353 8),u6 [88,89] [14,89,137,163,164,360,369,450,602,1361,1362],e6 [407] ([14,21,149,163,184]++r 1363 4),e6 [67,408] ([21,40,53,89,164,226,1107]++r 1367 6),e6 [201,13] [5,14,45,72,336,354,598,1137,1141,1143,1184,1243,1313,1373],u6 [154,23,24] [5,45,85,156,314,911,1374,1375],e6 [154,23] ([45,53,85,137,163,911,914]++r 1375 7),u6 [64,7] [14,338,652,668,901,1297,1382],e6 [409,24] [85,156,164,165,226,289,350,420,617,921,1383,1384,1385],u6 [25,24] [5,21,156,314,391,420,486,617,926,1386,1387],e6 [231,75,24] [14,40,158,220,617,769,925],e6 [67,218] [5,14,53,85,89,164,432,1107,1113,1388,1389,1390],e6 [261,83] [5,14,72,85,242,541,542,970,971,975,1391],([0,1,2,23,4,79,5,83],([5,85,242,466,540]++r 1392 4),[0]),([231,0,176,2,3,4,5,83],[5,220,539,967,975,987,1396,1397,1398],[]),e6 [16,410] [5,20,40,220,370,1399,1400,1401],e6 [411] ([14,40,89,1091]++r 1402 5),([278,192,0,1,2,3,5],([14,21,239,606,1128]++r 1407 5),[0]),([0,1,2,3,180,5,24],[5,14,89,135,261,1412,1413],[]),([412,171,0,1,2,3,4],([20,220,239,496]++r 1414 4),[]),e6 [413] ([14,21,53,72,89,149,163,184]++r 1418 4),([75,22,1,2,3,4,5],[5,85,149,218,220,298,1422,1423],[0]),([127,1,2,3,4,5,145],[5,150,197,460,628,921,1424],[0]),e6 [414] ([14,85,89,239,350]++r 1425 5),u6 [199,7] [85,89,103,226,348,652,668,773,1327,1328,1430,1431],u6 [23,137] [14,163,240,378,464,595,1123,1124,1402,1432,1433]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_25_8_0 : checkNodesBT W_25 g_25 F_25 P_25_8 A_25 B_25_7 8 N_25_8_0 = true := by decide +kernel
def N_25_8_1 : List NodeSpec := [u6 [279] ([14,21]++r 1434 6),e6 [415] ([40,89,239,522]++r 1440 4),e6 [416] ([5,163,220,1283]++r 1444 4),e6 [417] [5,14,72,85,89,149,239,350,968,1448,1449],([147,0,2,3,4,5,24],[5,40,138,139,226,1450,1451],[0]),([192,0,22,23,3,4,5],([85,239,376,699,1128]++r 1452 5),[]),e6 [418,135] ([5,53,85,137,163,164,350,854,1353]++r 1457 12),([0,22,23,3,4,5,83],[5,85,967,975,1454,1469,1470,1471],[0]),([0,22,23,3,4,79,5],[5,85,694,699,997,1001,1454,1455,1472],[]),e6 [281] ([14,20,72,85,149,163,184,350,668,709,710]++r 1473 4),([0,1,2,3,290,5,24],[14,85,89,135,165,348,1477,1478,1479],[0]),u6 [297,24] ([5,85,89,165,226,350,420,617,921]++r 1480 4),([28,142,2,3,4,5,7],[5,220,539,625,626,649,727,904,1484,1485],[]),e6 [419] [53,72,163,220,350,1330,1486,1487,1488],e6 [420] [53,85,89,239,466,1489,1490,1491],([171,223,0,1,2,3,4],[20,184,220,1416,1492,1493],[]),u6 [227,57,16] [5,40,364,589,1085,1494],e6 [421] [40,72,85,89,163,220,239,348,1460,1495,1496,1497],([132,179,0,182,1,3,4],[5,14,89,226,265,1011,1012,1030,1498,1499,1500],[0]),e6 [422] [20,53,137,496,1091,1501,1502],u6 [235,88] [40,89,220,239,370,393,394,396,461,1503,1504,1505],e6 [423] ([21,53,72,163,220,239]++r 1506 6),([223,0,22,23,3,4,5],[21,85,699,1452,1508,1509,1512,1513],[0]),([424,0,1,3,4,5,30],([21,89,149,220]++r 1514 4),[]),u6 [295] ([14,72,85,89,163,220,239,350,696,1422,1508]++r 1518 5),u6 [89,16,17] [5,137,163,360,369,370,375,423,444,520,1523,1524],e6 [425] [14,89,220,348,1525,1526,1527],e6 [231,426] ([40,85,137,220]++r 1528 9),e6 [229,427] ([45,53,89,517,1425]++r 1537 5),([171,0,1,2,3,4,24],[5,14,21,156,350,1542,1543],[0]),e6 [428] ([14,72,89,163,893]++r 1544 4),e6 [430] ([40,72,89,137,149,163,184,220]++r 1548 5),u6 [277] [14,21,53,72,85,89,137,239,599,1553],([0,2,3,4,79,431,5],[45,272,539,1554,1555,1556],[]),e6 [432] [40,89,163,1128,1402,1409,1557,1558,1559],u6 [52,24] [5,135,156,226,420,472,574,617,832],e6 [434] ([14,53,89,149,184,226,239]++r 1560 4),e6 [57,224] ([21,89,149,163,348,589,592,774,1085,1306]++r 1564 6),e6 [436] ([53,89,137,226,348]++r 1570 4),e6 [224,135] ([5,53,137,663,854,1460,1461,1565,1567]++r 1574 5),u6 [148,16] [5,45,53,137,146,155,156,364,423,618,928,940,1579,1580,1581],e6 [437,79] [72,85,89,163,220,272,350,997,1000,1582,1583],e6 [439] ([20,21,53,72,149,163,184,348]++r 1584 6),e6 [228] [40,72,89,163,239,350,539,847,1590,1591],e6 [440] [14,21,53,72,149,163,350,1592,1593],u6 [175,177] [5,14,85,239,243,248,267,720,975,982,1061,1288,1332,1594,1595],u6 [23,224] [21,85,348,663,1395,1567,1596],e6 [401,83] [5,14,40,85,89,163,164,242,967,975,1216,1278,1279,1281],([441,0,1,3,4,17,5],[85,89,220,350,1330,1509,1597,1598,1599],[]),([441,0,1,3,13,4,5],[21,72,89,220,348,1509,1600,1601],[]),e6 [442] [5,72,85,149,348,997,1001],e6 [443] [89,163,220,1599,1602,1603,1604],([195,271,0,2,3,4,5],[40,137,239,1515,1605,1606,1607],[]),e6 [231,236,24] [14,135,156,158,165,181,220,1608,1609,1610],([0,1,2,3,426,17,5],[21,85,89,220,1096,1330,1531,1611,1612],[]),([444,1,2,3,4,5,24],[5,14,156,184,220,226,420,617,1613,1614],[]),e6 [247,190] ([89,307,1022,1031]++r 1615 8),u6 [250,24] ([14,135,149,165,181,314,504,617]++r 1623 7),([161,0,1,2,4,5,24],[14,172,174,182,226,314,1630],[0]),([338,260,1,2,3,4,5],[14,184,536,539,659,895,1337,1631,1632],[]),u6 [247,63,7] [339,355,668,670,812,1290,1339,1618,1622,1633],e6 [445] ([5,89,149,163,220,460]++r 1634 4),e6 [57,130,287] [5,21,89,103,1068,1638,1639],([245,1,2,3,4,5,24],[14,21,165,184,226,420,490,617,1640],[0]),e6 [446] ([72,89,163,220,350,1349]++r 1641 4),([154,127,1,2,3,4,5],[5,40,184,197,209,294,392,460,914,921,1645],[0]),u6 [16,122] ([5,14,137,163,364,370,417,423,450,1579]++r 1646 6),u6 [84,83] [5,282,283,284,444,729,967,970,971,975],e6 [347,23] [5,53,137,226,1376,1377,1652,1653,1654],e6 [447] [40,89,239,612,1409,1655,1656,1657],e6 [247,438] [20,53,85,239,1589,1617,1622,1658,1659,1660],([231,156,0,2,3,4,5,24],[5,14,40,156,165,181,182,241,288,780,1661,1662],[0]),u6 [16,246] [5,40,164,226,1579,1663,1664],e6 [229,231,24] ([220,617,925,1355,1356,1530]++r 1665 5),u6 [262,30] ([149,163,548,777,858,1283,1620]++r 1670 6),u6 [201,63] [5,14,239,334,338,339,355,413,539,598,670,1303,1313,1676],u6 [262,7] ([53,137,163,355,356,548,668,1290,1620,1671,1673]++r 1677 5),u6 [138,137] [14,89,220,240,378,464,595,1682,1683],e6 [231,262] ([5,89,163,220,548,1530,1620,1671,1678]++r 1684 9),e6 [57,448] ([5,21,53,85,137,774,1085,1219]++r 1693 5),e6 [64] ([14,89,163,338,460,901]++r 1698 4),u6 [86,16] [14,20,53,72,89,137,361,364,612,1702,1703,1704],e6 [449] ([14,72,85,89,149,184,226,350]++r 1705 6),([201,260,1,2,3,4,5],[14,184,413,460,536,539,1337,1711,1712],[]),e6 [450] [14,53,89,239,1713,1714,1715],e6 [100] [5,21,149,348,364,427,589,590,591,1716,1717],u6 [229,148,24] [14,135,156,489,617,618,1665,1718,1719],u6 [229,156,24] [14,165,511,615,617,925,1665,1720,1721,1722],([57,201,0,1,2,3,5,7],[14,103,137,333,334,336,355,589,1313],[0]),u6 [230,135] ([53,137,220,1353,1458,1527,1577]++r 1723 5),u6 [274,24] [14,21,135,156,165,181,616,617,1728,1729],e6 [441,79] [72,85,89,163,220,350,466,997,1000,1166,1599,1601,1730],u6 [84] [5,137,149,282,283,284,975,1731,1732],e6 [229,180] ([20,89,517,1053,1356,1360,1721]++r 1733 4),([231,127,1,2,3,4,5,24],[5,14,40,158,197,294,302,392,420,460,628,921,1530,1667,1737,1738,1739],[0]),([132,229,0,1,3,4,17,5],([460,496,1360,1718]++r 1740 4),[]),e6 [249,343] ([14,20,53,85,89,893]++r 1744 5),u6 [236,24] [5,89,135,220,314,420,462,617,646,926,1610],e6 [451] [5,14,72,85,149,350,967,975,1749],u6 [25] [5,21,60,72,89,149,156,163,181,391,486,1386,1387,1750],e6 [452] ([20,72,85,149,163,239,348,1353]++r 1751 5),e6 [453] ([20,72,163,220,239,350,958]++r 1756 5),u6 [248,83] [85,89,220,242,348,729,967,1761,1762,1763],u6 [45,24] [21,45,156,165,181,312,420,617,1134,1135],([247,0,1,2,3,290,5],[14,53,85,89,184,682,1764],[]),([128,127,1,2,3,4,5],[5,40,184,197,294,392,822,913,921,945,1765],[0]),([0,1,2,3,322,5,24],[14,20,21,135,149,226,348,617,1766,1767,1768],[]),e6 [92,343] [14,53,85,460,893,1744,1746,1747,1769],u6 [239,111] [14,137,226,239,469,470,656,1176,1770,1771,1772],([101,249,0,2,3,4,135,5],[20,40,85,605,1773,1774,1775],[]),u6 [322,7] ([20,21,53,137,226,668]++r 1776 6),([441,0,1,23,3,4,5],([21,53,85,89,348,1509]++r 1782 4),[]),u6 [148,24] [5,14,45,156,158,165,181,314,420,617,926,1786,1787],([0,1,88,3,4,17,5],[5,82,89,137,370,375,394,450,460,492,824,1788,1789],[]),e6 [454,24] [85,135,137,156,226,289,314,348,350,420,617,921,926,1379,1790,1791],([154,75,1,2,3,4,5],[45,85,218,230,236,298,420,914],[]),([28,183,1,2,3,4,5],[5,85,149,786,1217,1444,1642,1792],[]),u6 [201,249] [14,20,89,149,336,598,620,1256,1774,1778,1793,1794],u6 [128,160] [5,45,68,134,137,165,731,910,913,961,1795,1796],u6 [167,24] [5,85,135,156,165,220,226,420,617,628,725,921],e6 [23,455] ([5,226,1376]++r 1797 4),e6 [57,392] [5,21,85,89,137,589,1801,1802,1803],e6 [441,135] [53,85,89,137,220,350,854,1458,1460,1577,1599,1601,1804],([0,1,2,16,4,17,5,83],[5,444,519,520,729,750,967,1330,1805,1806],[0]),([132,130,179,0,1,3,4],[5,20,89,844,1011,1012,1638],[0]),([28,0,2,456,3,4,5],[89,137,539,893,1544,1807],[]),e6 [17,457] ([40,53,85,226,444,496,519,520,1096]++r 1808 4),e6 [101,322] [20,40,85,89,1775,1779,1812,1813,1814],e6 [458] [40,72,85,89,239,348,997,1815,1816],u6 [148,145] [5,14,150,155,156,164,182,289,489,618,1817,1818],([459,0,6,2,3,4,5],([137,163]++r 1819 5),[0]),e6 [460] [5,40,85,89,239,350,967,1824,1825],u6 [228,249] [20,40,89,149,452,453,620,1793,1826],u6 [257,7] ([53,85,137,333,355,668]++r 1827 6),([75,1,2,3,4,5,151],[14,85,220,236,460,1833,1834,1835],[0]),e6 [461] ([5,149,220,348,350]++r 1836 5),([57,260,1,2,3,4,5,7],[14,103,137,460,536,652,659,660,1055,1337,1338,1347,1711,1841],[0]),([0,1,2,3,426,79,5],[21,72,85,466,995,1842],[]),([101,0,2,16,4,5,83],[5,74,612,967,1843],[]),u6 [231,224] ([89,163,220,663,1530]++r 1565 4++[1686]++r 1844 5),u6 [57,223,16] ([21,364,370,423,592,773,774,1275,1519,1569,1579,1580]++r 1849 4),u6 [92,163,24] [14,156,158,165,185,409,585,1853,1854,1855],u6 [250,135] [5,53,85,89,137,504,620,854,1353,1460,1625,1626,1627,1856,1857],u6 [312,7] [14,89,652,668,1226,1229,1233,1334,1858],([392,271,0,2,3,4,5],[5,40,137,1859,1860,1861],[]),e6 [257,24] ([149,156,163,164,165,181,289,314,348,350,617,1830,1832]++r 1862 5),u6 [272,24] ([5,135,149,156,165,314,584,617]++r 1867 6),u6 [23,237,79] [5,45,85,466,1166,1873,1874],e6 [462] ([14,53,72,89,149,163,348]++r 1875 5),e6 [304] ([20,53,72,137,163,184,226]++r 1880 4),e6 [303] [14,53,137,460,720,979],([0,22,23,3,4,5,24],[5,21,85,156,165,1452,1455,1609,1884,1885],[0]),e6 [463] ([5,14,40,89,239,350,1013,1872]++r 1886 4),e6 [465] [20,53,72,137,163,226,1890,1891,1892],e6 [466] ([14,72,89,149,163,184]++r 1893 5),e6 [71,92] ([14,149,239,382,460,1864]++r 1898 5),e6 [429] ([40,220,460,539]++r 1903 5),u6 [22,137] [14,89,137,240,378,464,595,1425,1908],e6 [467] [21,40,72,163,184,220,239,350,1515,1909,1910,1911],e6 [468] ([45,72,85,89,149,348,1001,1166]++r 1912 4),e6 [16,233] [21,137,226,370,460,1898,1902,1916,1917,1918],u6 [177,178,83] [967,968,975,1288,1919,1920],e6 [469] [21,72,89,163,220,239,348,350,1395,1509,1849,1921,1922],e6 [132,272] ([5,20,53,89,149,1010,1022,1868,1869,1872]++r 1923 4),u6 [253,24] [45,85,135,158,164,165,181,226,289,348,420,460,617,1927,1928],u6 [231,137] [14,89,220,240,377,378,464,595,1123,1124,1432,1692,1929,1930,1931],u6 [88,16,246] [82,85,364,370,393,423,1663,1664,1932],e6 [367] [5,21,53,137,1065,1933],e6 [470] ([21,89,220]++r 1934 5),e6 [471] ([14,40,72,163,226,348,350,1022]++r 1939 5),e6 [398,17] ([5,45,89,239,444,520,1093,1096]++r 1270 4++[1944]),e6 [230,24] [21,89,135,165,181,220,348,350,617,926,1527,1725,1726,1938,1945,1946],e6 [472] [5,72,149,163,184,1425,1947,1948,1949],e6 [424,24] [21,85,89,135,156,165,220,314,348,350,617,926,1517,1950,1951,1952],e6 [473,79] [20,45,72,89,239,272,350,997,1000,1001,1166,1953,1954,1955],e6 [474] ([21,89,163,1517]++r 1956 5),([127,1,2,23,3,4,5,24],[5,21,197,392,420,921,1376,1961,1962,1963],[0]),e6 [475] [5,53,72,85,89,137,149,226,239,1964,1965,1966],([412,0,22,23,3,4,5],([85,376,694,699,1452]++r 1967 4),[]),e6 [476] [53,89,226,239,1809,1971,1972,1973],([71,192,0,1,2,3,5],[14,137,163,361,789,1409,1974,1975,1976],[0]),([249,0,2,3,4,135,5,7],[20,333,504,847,1460,1778,1977,1978,1979],[]),e6 [171,229] ([20,149,517,1356,1416,1721,1741]++r 1980 4),e6 [477] [53,72,85,89,239,272,997,1984],u6 [156,249,24] [14,20,511,605,615,617,925,1985,1986],e6 [132,478] ([21,89,1358,1360,1741]++r 1987 5),u6 [148,16,24] [5,135,155,156,165,181,370,396,1581],e6 [479] [21,53,72,220,350,1992,1993],u6 [233,7] [14,21,53,137,226,355,668,1780,1917,1918,1994,1995,1996],([161,0,1,2,4,5],([5,85,137,163]++r 1997 5),[]),([136,0,1,2,3,4,427],[45,53,89,1056,1425,1522,1537,2002],[]),([28,249,0,2,3,4,5,7],[20,85,605,625,626,893,1484,1778],[0]),([0,1,29,3,4,135,30],([40,226,847,1461]++r 2003 4),[0]),e6 [480,24] [5,89,163,220,420,617,926,2007,2008,2009],e6 [247,427] [5,53,85,89,1425,1538,1539,1540,1617,1875],e6 [481] ([14,53,137,149,184,226]++r 2010 5),([101,361,0,2,3,4,5],([74,137,220,239,539,1044,1283]++r 2015 4),[]),u6 [128,16,24] [5,156,181,220,364,910,2019],([28,229,0,2,3,4,5,7],[220,539,625,679,893,1721,2020,2021,2022],[]),e6 [92,433] ([14,53,460]++r 2023 6)]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_25_8_1 : checkNodesBT W_25 g_25 F_25 P_25_8 A_25 B_25_7 8 N_25_8_1 = true := by decide +kernel
def N_25_8_2 : List NodeSpec := [e6 [482] ([21,40,89,226,958]++r 2029 5),([101,71,0,2,3,16,4,5],[40,137,358,359,423,435,597,1901,2034,2035],[0]),([437,0,1,3,4,17,5],[89,350,496,520,1583,2036,2037],[]),u6 [227,71] [5,40,137,348,382,423,516,522,784,789,2038,2039],([392,0,22,2,3,4,5],([5,85,137,239,967,1803,1859]++r 2040 5),[]),([0,2,3,16,4,17,5,7],[5,356,375,402,423,519,520,1330,1780,2045,2046,2047],[0]),e6 [16,322] [14,21,89,137,226,364,1579,1777,1779,1781,1814,2048,2049,2050],e6 [52,16,24] [5,14,40,226,826,832],e6 [483] ([14,72,149,163]++r 2051 5),e6 [484] [14,89,149,220,348,460,2009,2056,2057],e6 [299] ([14,149,220,348,460,539]++r 2058 5),u6 [315,24] [14,85,89,165,220,314,420,617,628,926,2063,2064],([101,67,0,2,3,4,135,5],[5,53,539,1107,1204,1231,1235,1333,1460,1773,2065,2066],[]),u6 [36,17] [163,406,444,496,520,539,566,2067,2068],e6 [485] ([21,40,72,89,163,165,184,226,239]++r 2069 4),e6 [486] [5,53,89,137,226,239,2073,2074],e6 [57,272] [5,21,53,89,592,774,1085,1868,1869,1871,1924,2075,2076],e6 [424,79] [21,72,85,89,163,220,226,350,995,1000,1001,1951,1952,2077,2078],([0,6,63,2,3,4,7],[14,137,539,622,812,898,900,1676,2079,2080,2081],[0]),e6 [424,83] [5,14,40,72,85,89,163,220,242,968,970,975,1517,1951,1952,2082],([101,0,88,2,3,16,4,5],[40,53,85,137,358,359,423,435,597,1362,2083],[0]),([57,0,6,2,3,4,7],[14,85,103,137,589,622,898,1055,2080,2081,2084],[0]),e6 [92,397] [40,53,85,460,1259,1260,2085,2086],u6 [229,22,24] [14,21,539,617,1355,1422,1665,1721,1741,2087,2088],e6 [487] [40,72,163,220,239,348,350,1515,2089,2090,2091],e6 [233,83] [14,21,85,975,1898,1917,2092],e6 [175,231] [5,14,85,89,220,243,1595,1931,2093,2094],e6 [229,397] [40,53,220,517,1258,1260,1261,2085,2095],e6 [488] [21,40,72,89,163,239,1013,2033,2096,2097,2098],([175,0,1,2,3,5,24],[5,14,163,2099,2100],[0]),([101,92,0,2,3,4,135,5],[40,85,713,1898,2066,2086],[]),e6 [489] ([20,85,149,239,350,1579]++r 2101 4),e6 [16,426] ([14,21,85,220,364,423]++r 1531 4++[1579,1852,2105,2106,2107]),u6 [227,88] [5,40,82,89,239,370,393,394,450,522,2108],e6 [490] [40,72,220,239,350,1515,2109,2110,2111],u6 [13,218] [5,14,53,432,793,1137,1388,1389,2112],e6 [101,233] [40,85,460,1216,1917,1996,2086,2113,2114,2115],e6 [491] ([5,163,220,777,1461]++r 2116 5),([132,28,179,0,1,3,4],[5,20,89,226,893,1011,1012,1030,1349],[0]),e6 [231,455] ([5,220,1666,1798,1799,1848,2074]++r 2121 5),u6 [224,17] [375,444,520,663,1330,1565,1566,1567,2126,2127],([0,1,2,3,408,5,24],[14,21,149,165,226,617,2033,2128,2129],[]),e6 [492,427] [5,53,85,89,184,1425,1522,1538,1539,1541],u6 [201,249,7] [20,413,537,598,668,1256,1476,1778,1794],e6 [130,426] ([14,21,149,220,539]++r 1531 4++[1638,2107,2130,2131,2132]),e6 [271,312] [40,53,89,164,226,1225,1229,1371,1858,2133,2134],([75,1,2,23,3,4,5],[5,85,218,220,236,298,341,372,1376,2135,2136],[0]),e6 [229,290] ([14,53,89,517,682]++r 2137 4),u6 [299,83] ([5,14,72,242,729,968,970,971,2058,2059]++r 2141 5),e6 [57,229,7] [14,21,589,668,1055,1347,1355,1356,2021,2146,2147],e6 [22,478] [21,45,517,1988,1989,1990,2087,2140,2148,2149,2150],e6 [156,249] [20,89,241,288,504,511,620,780,958,1476,1720,1774,1793,1985,1986,2151,2152,2153],u6 [226,16] ([5,53,137,364,1579,1580]++r 2154 4),([0,1,2,3,290,79,5],[14,85,997,1000,2137,2158,2159],[]),e6 [493] ([40,72,85,163,220,239,348,958]++r 2160 5),([128,75,1,2,3,4,5],[5,85,149,218,220,236,372,420,2165,2166,2167],[]),e6 [494,83] ([5,14,72,220,242,729,967,968,970,971,975,1686]++r 2168 4),([75,1,2,3,16,4,5,24],[5,218,220,226,234,236,298,415,1580,2172],[0]),u6 [291] [14,85,89,220,239,348,350,423,688,2173,2174],([183,1,2,3,4,5,24],[5,156,226,617,786,788,1348,1617,2175],[]),e6 [231,495] ([220,1536,1686]++r 2176 7),([0,6,2,3,4,17,7],[85,220,375,496,497,622,1330,2080,2183],[0]),([226,128,0,1,3,4,5],[5,14,134,156,910,2184,2185],[0]),e6 [496] [40,85,89,239,997,2186,2187],e6 [497] [20,53,85,348,2188,2189],([75,1,2,23,3,4,5,24],[5,21,85,218,226,236,415,1377,1961,2136],[0]),u6 [231,237,79] [5,45,163,466,468,997,1000,1686,1848,2190],([130,183,1,2,3,4,5],[5,149,1217,1348,2130,2191],[]),u6 [201,229] [14,149,336,517,598,1256,1313,1355,1718,1794,2021],e6 [278,83] [5,14,21,72,163,242,348,968,970,971,975,1394,2192],([132,0,1,3,16,4,17,5],[5,20,89,370,1742,2193],[0]),e6 [175,186] ([14,85,149,163,242,244,350,921]++r 989 4++[1061,1098,1332,1595,2094,2194]),e6 [498] [40,72,89,163,239,350,847,1577,2195,2196,2197],e6 [499] [14,53,72,85,89,137,2198,2199,2200],u6 [316,16] [5,14,21,53,72,137,361,370,423,1579,1580,2201,2202],e6 [227] [5,14,40,72,89,239,350,612,2203,2204],u6 [128,145] [5,14,125,150,182,220,910,913,1817,1818,2205,2206],([31,0,1,3,4],[12,44,1013],[0]),u6 [325,24] [5,40,85,135,156,181,348,420,925,2207,2208],e6 [404] [85,137,149,184,226,1304,1308,2209,2210],e6 [322,83] [20,21,72,85,968,1781,1814,2211,2212,2213],e6 [350,392] [5,85,89,137,239,1803],e6 [175,23] [5,14,53,85,137,1061,1374,1376,1377,2094,2214],([195,0,6,2,3,4,5],([137,163,239,431,2037]++r 2215 4),[0]),e6 [229,343] [14,53,220,517,893,1744,1745,1746,2219,2220],u6 [345,148] [21,40,45,146,158,489,928,947,2221],e6 [231,331] ([89,137,220,348,863,1686,1692,1931]++r 2222 8),e6 [500] [20,53,85,350,2230],([127,1,2,3,4,5,160],[40,45,197,208,294,392,460,958,1795,2231,2232,2233],[0]),u6 [88,24] [5,14,82,135,156,158,181,350,370,420,450,617,926,1362,2234],u6 [23,145] ([5,53,85,89,137,466,630,1376,1377,1378]++r 2235 4),([75,163,1,2,3,4,5],[5,85,220,298,372,415,585,2239],[]),e6 [130,322] [20,21,89,226,539,1779,1781,1814,2240,2241,2242],e6 [175,249] [14,20,89,149,244,605,620,1332,1476,2094,2212,2243],e6 [249,397] [20,40,53,85,89,1258,1259,1260,1775,2085],u6 [304,24] ([14,135,149,165,181,226,314,348,350,420,617,926]++r 1880 4++[2244]),e6 [23,495] [5,85,226,1374,2177,2179,2245],e6 [501] ([14,72,85,89,149,184,226,348]++r 2246 4),([0,1,2,4,135,328,5],[5,847,849,850,854,2250],[0]),u6 [72,71,16] [5,40,85,395,423,2038],u6 [249,163,24] [14,20,409,585,617,1476,2251,2252],u6 [172,137] [14,239,240,378,464,2253,2254],e6 [130,233] [14,226,539,1898,1917,1918,2191,2255,2256],e6 [502] [20,53,89,137,1090,2257,2258],u6 [71,88] [5,14,40,82,85,89,137,163,239,370,382,393,394,448,450,784,2038],([231,0,163,2,3,4,5,24],[5,85,137,156,165,189,220,628,725,2259,2260],[0]),e6 [92,160] ([85,460,847,1830,1864]++r 2261 6),u6 [16,280] ([14,21,40,137,370,612]++r 2267 6),e6 [347,23,79] [5,45,226,1001,1378,1395,2273],e6 [503] ([40,85,137]++r 2274 5),e6 [57,457] [21,40,53,85,89,592,773,774,1055,1809,1810,1811,2279,2280,2281],([492,1,2,3,4,5,427],([5,85,184,1538,1541]++r 2282 4),[]),e6 [201,338] [5,14,89,539,598,894,1313,1631,2286,2287,2288],e6 [504] [21,53,137,2289,2290,2291],u6 [228,92] [40,239,452,453,460,1864,1898,2292,2293,2294],e6 [101,478] ([40,517,1205,1216,1988,1990,2095,2149,2291]++r 2295 4),([101,110,0,2,3,4,17],[85,496,520,1237,1238,1330,2299],[0]),u6 [201,92,7] [14,355,598,1313,1338,1794,1995,2300],e6 [57,7] [14,21,53,89,103,426,774,1055,1252,1253],u6 [212,24] [14,156,165,181,226,314,617,926,2301,2302,2303],u6 [216,16] [40,361,364,748,1579,1580,2304,2305],e6 [92,156] [165,288,460,511,958,1720,1830,1854,2153,2266,2306],u6 [261] [5,14,72,85,89,149,350,541,542,723,729,975,1391,2307,2308],([247,0,22,23,3,4,5],[5,85,694,699,1455,1512,1622,2309,2310],[]),u6 [23,262] [5,45,85,548,1395,1688,1690,2311,2312],([28,316,0,1,2,3,5],[14,137,1444,2202,2313],[]),u6 [92,156,24] [14,156,158,165,288,511,615,713,925,1720,2306],([128,75,1,2,3,4,5,24],[5,21,45,218,226,236,420,617,913,2166],[0]),e6 [132,262] [20,89,548,1022,1357,1620,1671,1673,1688,1690,1926,2314,2315,2316],u6 [230,7] [53,137,220,333,668,1290,1527,1726,1780,2317,2318],u6 [341,7] [14,21,53,103,348,356,589,652,668,1290,1338,1780,2319],e6 [505,247] ([40,45,149,1617,1622,1685]++r 2320 4),([179,0,1,506,3,4,5],([89,137]++r 2324 6),[]),([201,142,1,2,3,4,5],[5,14,40,413,539,598,637,640,649,652,727,2330],[0]),e6 [175,92] [14,239,242,244,460,713,1061,1854,2094,2331,2332],([0,390,1,3,4,17,5],[89,350,375,496,1168,1193,2333,2334],[]),e6 [229,438] [20,21,53,239,517,1658,1659,1660,1718,1721,2335],e6 [478,7] [14,21,53,137,355,668,1290,1988,1989,2021,2149,2291,2296,2336,2337,2338],([101,229,0,2,3,4,135,5],[220,539,847,1721,1741,1773,2066,2095],[]),e6 [17,455] [226,375,496,517,520,1096,1798,2074,2122,2124,2339,2340],e6 [22,426] [14,21,85,149,1422,1522,1531,1532,1534,2107,2131,2341],u6 [154,231,24] [45,85,135,182,314,1536,2342,2343],([28,142,0,2,3,4,5,7],[220,539,625,626,649,679,727,904],[]),u6 [132,71,16] [5,40,137,361,364],e6 [507] [21,53,72,137,163,226,1996,2344,2345],e6 [508] ([40,163,2323]++r 2346 5),e6 [177,135] [5,14,53,137,248,720,1288,1353,1457,1577,2351],([28,92,0,2,3,4,5,7],[85,679,713,893,1484,1995,2300],[0]),([229,0,22,23,3,4,5],[5,21,694,699,1452,1454,1512,1718,1721,2352],[]),([169,0,2,3,4,5,24],[14,40,45,156,182,202,220,2353,2354],[0]),u6 [57,16,287] [5,21,40,89,364,589,592,774,1639,2355],e6 [181,135] ([5,53,85,89,137,854,1353,1457]++r 2356 7),e6 [57,455] [21,89,589,774,1055,1798,2022,2074,2122,2124,2147,2363,2364],e6 [509] [14,53,72,220,350,793,1137,2365],u6 [281,7] [14,333,356,504,652,668,709,710,1290,1473,1474,1476,1780],e6 [505,229] [21,40,149,517,1718,1741,2022,2320,2366],u6 [216] [14,20,149,350,364,1357,2304,2305,2367,2368,2369],e6 [510] ([40,72,163,350,774,1943]++r 2370 4),([92,0,2,3,4,135,5,7],[847,1830,1977,1978,1995],[]),u6 [228,229] [40,149,452,453,517,1355,1718,1741,2292,2374],u6 [95,16] [5,14,21,53,72,357,364,396,423,450,1579,1580,2375,2376],([213,0,1,177,3,4,5],[5,89,248,267,720,975,2377],[]),u6 [213,137] [14,240,377,378,1660,2378,2379],u6 [255] [5,72,89,135,149,163,184,239,518,2380,2381],e6 [511] [5,21,72,149,156,163,165,184,2382,2383],([213,75,1,2,3,4,5],[5,85,218,298,769,1507,2384],[]),([213,0,1,148,3,4,5],[5,89,146,155,156,460,2385,2386,2387],[]),([512,0,2,3,4,79,5],[45,272,997,2388,2389,2390],[]),e6 [513] [20,53,72,163,239,1128,1453,1660,2391,2392],([101,0,190,2,3,4,5],[14,74,89,137,307,539,1022,1205,2393,2394],[]),e6 [514,24] [89,137,182,220,226,350,420,539,617,921,2395,2396,2397],e6 [494] ([5,14,149,220,350]++r 2168 4++[2398]),u6 [57,89,16] [5,14,20,137,364,369,370,423,589,592,774,2399],e6 [515] ([14,40,89,137,149,460]++r 2400 5),([136,0,22,23,3,4,5],[239,376,699,1056,1091,1452,1454,1455,2405],[0]),e6 [516] ([14,40,89,137,460]++r 2406 5),u6 [240,24] [14,40,85,135,181,226,420,925,2396,2404],u6 [157,24] [45,85,156,165,181,226,420,617,910,921],e6 [392,17] [5,85,239,375,1092,1093,1268,1330,1801,1803,2411],e6 [517,7] [53,85,137,333,348,355,356,497,652,668,1329,1780,1831,2412,2413,2414],e6 [518] ([14,149,163,184,220,239]++r 2415 7),e6 [519,231] ([89,137,220,348,1530,1536,1686,1931,2145]++r 2422 4),e6 [521] ([89,149,460,539]++r 2426 7),e6 [522] ([5,45,89,149,460]++r 2433 4),e6 [335] [14,53,89,239,406,2437,2438,2439],e6 [231,524] ([220,1738]++r 2440 7),e6 [154,231] [5,89,137,163,220,291,911,914,1380,1381,1686,1931,2342,2343,2396,2447],([57,0,1,88,3,16,4,5],[5,82,137,239,361,364,394,396,450,589,592,596,903],[0]),u6 [128,156] [5,89,137,166,239,288,511,615,780,910,913,1796],u6 [194] [14,21,239,326,2448],([132,179,0,1,3,16,4],[5,14,20,40,89,364,423,612,1011,1012,1028],[0]),([156,0,22,2,3,4,5],([5,137,165,239,241,288,539]++r 2449 6),[]),([0,1,2,3,218,17,5],[14,89,432,496,520,2455],[]),e6 [525] [5,40,72,85,89,137,149,184,239,350,2456,2457,2458],([231,0,1,2,4,79,5,83],[5,242,466,540,1392,1393,1686,1692,2143,2459],[]),e6 [231,145] ([5,89,137,220,466,630,1931,2235,2236,2237]++r 2460 4),e6 [67,426] [14,21,85,149,164,1114,1235,1532,1533,2107,2131,2464],e6 [57,119] ([5,14,21,89,137,423,873,1275]++r 2465 6),e6 [136,259] ([89,220,1056]++r 2471 5),u6 [204] [14,45,149,220,348,350,352,355,539,680,681,2476,2477,2478]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_25_8_2 : checkNodesBT W_25 g_25 F_25 P_25_8 A_25 B_25_7 8 N_25_8_2 = true := by decide +kernel
def N_25_8_3 : List NodeSpec := [e6 [347,231] [5,89,220,226,1654,1931,2479],e6 [347,231,79] [5,45,226,1000,1686,1692,2479],([127,1,148,2,3,4,5,24],[5,14,40,45,158,197,294,392,420,618,921,2480,2481],[0]),([183,1,2,3,4,5,83],[5,85,788,970,975,1217,2482],[0]),e6 [57,65,7] [14,21,137,589,1290,1321,1338],e6 [526] ([40,53,72,220,239,350,1738]++r 2483 4),u6 [250,7] [14,53,85,89,137,333,356,504,668,1625,1629,2487,2488,2489],u6 [333,24] [5,135,158,181,182,220,314,348,420,925,926,2490,2491],e6 [236] [5,72,149,163,220,348,462,646,1608,1610,2492,2493],u6 [71,96] [14,89,137,220,361,382,2494,2495,2496],e6 [193,7] [14,21,53,137,333,348,355,652,668,2497,2498],e6 [231,24] [5,14,40,156,182,220,314,348,420,925,926,2062,2499],u6 [201,92] [14,239,336,460,598,1256,1313,1794,1864,1995,2293],([231,75,1,2,3,4,5],[5,85,218,220,236,298,341,372,415,769,1530,2500,2501,2502],[]),u6 [18,16] [5,220,375,423,434,444,753,754,1579,1580],([179,0,1,292,3,4,5],[89,689,2503,2504,2505],[]),e6 [57,235,16] [21,40,396,1505,1579,2506],([231,75,1,2,3,4,5,24],[5,14,85,218,220,226,236,296,298,341,415,1667,1931,2501,2502],[0]),e6 [71,235] [40,137,149,350,361,396,461,784,1505,2038,2507,2508,2509],([0,2,3,4,527,135,5],[5,40,53,539,2510,2511],[]),u6 [72,16] [5,40,226,364,370,1579,1580],([0,153,2,3,4,5,24],[14,21,85,156,165,628,2512,2513,2514],[0]),u6 [52] [5,45,89,181,226,239,472,574,826,832,2515],([335,0,1,2,36,4,5],[14,53,163,406,566,2437,2439],[0]),([57,0,2,3,16,4,5,7],[5,402,423,589,774,1085,1326,1780,2045,2046,2047],[]),e6 [528] ([14,89,163,220,1951]++r 2516 4),([247,175,0,1,2,3,5],[14,85,244,1332,1595,2099,2520],[0]),([0,2,16,4,5,7,83],[5,72,612,729,2521],[]),e6 [529] ([89,163,220,1583]++r 2522 4),([71,0,2,3,4,5,7],[14,137,226,2526,2527],[]),([0,2,3,102,16,4,5],[40,53,72,77,85,2528],[0]),([101,57,110,0,2,3,4],[14,53,85,774,1055,1085,1236,1237,1238,1241,2529],[0]),e6 [530] [21,53,72,163,350,774,1055,2530,2531],([101,73,0,2,3,16,4,5],[40,137,358,359,435,465,597,2532,2533,2534],[0]),([101,0,2,3,16,4,17,5],[5,40,74,359,375,435,519,520,597,1330,1944],[0]),([0,1,29,3,4,79,30],[40,226,272,1001,2005,2006,2535],[0]),([101,57,0,2,3,16,4,5],[5,53,358,359,423,435,465,589,597,773,774,1085,1220],[0]),([101,0,2,3,4,243,5],[40,85,137,597,2536,2537],[0]),e6 [531] ([72,89,163,239,350,539,1807]++r 2538 4),([101,71,0,2,3,4,5],[14,85,137,597,1901,2035,2542],[]),e6 [122] ([14,89,137,149,417,450,460]++r 1646 4),u6 [272,30] [21,584,858,1283,1675,1872,2543,2544],e6 [246] ([5,89,149,460,1663]++r 2545 4),e6 [231,478] ([21,89,220,1530,1666,1669,1692,1741,1988,1989,2149,2337]++r 2549 4),([179,0,1,88,3,4,5],[82,89,137,602,2328,2553,2554,2555],[0]),e6 [364,135] ([5,53,137,163,847,854,1577]++r 2556 6),e6 [532] ([53,72,163,220,239,350,1738]++r 2562 4),e6 [192,88] [5,82,137,393,450,602,1362,1409,1949,2566],([101,75,1,2,3,4,5],[85,218,220,298,341,372,415,1215,2567],[]),e6 [533] ([89,149,163,220,1762]++r 2568 4),([0,6,2,3,13,4,7],[14,539,793,1243,2080,2081],[0]),u6 [88,16,122] [137,163,364,370,417,450,1649,1650],([75,1,2,3,4,5,145],[85,218,226,517,1817,2572,2573],[0]),u6 [187,24] [45,135,165,181,226,300,420,617,2574,2575],e6 [534,16] [5,20,53,364,396,1579,1580,2576,2577],e6 [248,16] ([53,89,137,220,226,1579]++r 2578 5),u6 [296] [21,53,72,137,163,220,700,1085,1306,2583],e6 [71,16,207] [5,14,40,390],e6 [136,506] ([45,137,1091,1403,1427,2324,2326]++r 2584 4),([132,179,0,1,3,4,180],[5,20,89,261,1030,2588,2589],[0]),([0,1,88,3,16,4,17,5],[5,82,137,163,220,361,370,375,394,444,450,492,1788],[0]),([28,0,348,2,3,4,5],[137,350,893,965,1056,2590],[]),u6 [88,16,24] [5,85,156,181,361,364,370,393,450,2234],u6 [16,254] ([5,14,137,220,370,423,611]++r 2591 4),([156,75,1,2,3,4,5],[5,14,85,218,234,236,299,415,615,2595],[0]),e6 [535,299] [14,72,89,137,220,1848,2141,2142,2144,2145,2596],([57,73,0,1,3,16,4,5],[5,20,137,220,364,370,384,387,441,589,592,2594,2597],[0]),e6 [249,160] ([20,85,89,504,620,847]++r 2261 4++[2598,2599]),u6 [71,73] [5,14,40,85,89,137,163,382,384,387,755,784,2533,2594,2600],u6 [227,73] [5,40,89,239,516,522,2533,2594,2601],e6 [130,148] [5,53,146,155,156,489,539,618,2130,2242,2602,2603],e6 [536] [5,14,20,53,85,137,350,2604,2605],u6 [73,16,24] [5,135,156,181,220,370,755,2594,2606],u6 [18] [5,149,220,348,370,375,434,753,754,761,2607],u6 [202,7] [53,137,226,652,668,1290,1334,2608,2609,2610],u6 [17,119] [5,14,89,375,873,1092,1093,2465,2466,2468,2469,2611],e6 [227,17] [5,40,89,239,516,594,1093,1096,1330,2612],e6 [57,537] ([5,21,53,89,774,1275,1638]++r 2613 6),e6 [538] ([40,72,89,149,163,239,350]++r 2619 4),e6 [539] [14,40,72,89,239,350,364,612,2623,2624,2625],e6 [540] [14,53,85,239,350,1056,1091,1660,2626,2627],u6 [227,16,17] [5,40,163,370,375,516,1330,2612],u6 [100,16] [5,21,361,364,423,427,589,591,592,1579,1580,1716,2628],e6 [57,100,16] [137,364,427,589,2628],u6 [16,310] ([5,14,89,137,364,423,1579,1580]++r 2629 5),([28,0,2,3,13,4,5,7],[5,53,539,625,626,679,1137,1243,1349,1373,2020],[0]),e6 [101,193] [14,21,40,53,1216,2634,2635],e6 [541] ([20,72,149,163,184,220,348,1022]++r 2636 4),e6 [542] [21,53,72,137,163,226,2213,2640,2641],e6 [57,16,310] [14,21,89,364,423,2631,2642],([75,1,2,3,4,5,30],[85,218,220,372,460,1675,2643,2644],[]),u6 [188,24] [14,40,85,135,156,350,420,482,925,1127,2645,2646],([0,1,2,3,4,427,83],[5,85,89,967,968,1537,2647,2648,2649],[]),e6 [519] [14,72,89,137,149,163,184,220,2422,2423,2424,2650,2651],([57,0,1,3,16,4,5,30],[5,21,89,370,423,2652,2653,2654],[0]),([132,57,0,1,3,16,4,5],([5,89,361,364,370,423]++r 2655 5),[0]),e6 [538,57] [21,40,53,89,589,592,773,1275,1306,2619,2622,2660,2661],e6 [227,57] [5,21,40,89,516,594,1275,1494],e6 [543] [5,21,45,53,137,1001,2662,2663,2664],e6 [132,16] [5,20,40,53,72,89,137,364,612,2665],e6 [544] [40,89,239,847,1403,2666,2667,2668],u6 [16,220] [14,40,89,364,440,612,806,1049,1249,1250,2669,2670,2671],e6 [545] ([20,53,137,226,239,2213]++r 2672 6),e6 [13,343] [5,14,53,1137,1141,1143,1349,1744,1745,1747,2219,2678,2679],([0,1,29,3,16,4,30],[14,40,370,612,2004,2005,2006,2535,2680],[0]),e6 [546] [21,53,72,137,163,350,589,1055,2681,2682,2683],u6 [66] [5,29,163,220,345,355,375,424,533,2684,2685],([67,0,6,2,3,4,7],[14,539,622,898,1113,2080,2081,2686,2687],[0]),([459,0,1,2,4,5,83],[40,72,85,163,348,729,2278,2688,2689,2690],[]),u6 [243,30] ([40,85,776,777,2201]++r 2691 4),u6 [71,16,30] [40,85,361,370,382,782,2038,2695],([183,1,2,3,16,4,5],[226,370,786,787,1217,1348,1579],[0]),u6 [242] ([5,14,45,149,220,370,479,777]++r 2696 4),([130,0,1,29,3,4,30],[14,239,844,2005,2006,2191,2535],[0]),([0,1,2,3,135,220,5],[14,53,89,226,440,806,837,847,1577,2700],[]),e6 [132,216,16] [40,137,364,749,1357,2304],e6 [249,433] [20,53,89,226,504,539,2023,2024,2025,2241,2701,2702],e6 [132,243] ([5,20,40,89,137,361,776,1357,2536,2537,2655,2693]++r 2703 4),([28,0,63,2,3,4,5,7],[5,53,333,338,539,625,626,679,1301,1349,1676],[0]),e6 [392,177] [5,85,89,137,163,164,967,982,988,1268,1288],e6 [132,71] [14,20,89,137,361,382,1901,2034,2655,2707],e6 [547] ([5,85,89,239,348,539,729]++r 2708 4),e6 [548] [14,40,72,370,612,2328,2712,2713,2714],([71,0,1,2,4,5,83],[14,72,85,163,729,2034,2715],[]),e6 [71,123] [14,137,239,382,455,2716],u6 [207] ([14,89,137,226,239,390]++r 2717 5),e6 [72] [14,53,72,89,149,184,226,239,811,2722,2723],e6 [549] [20,53,137,2724,2725],u6 [95,71,16] [85,364,370,493,2038,2726,2727],e6 [550,24] [5,40,156,182,220,314,420,925,926,2728],e6 [310] [5,89,163,1055,2729],e6 [551] [40,85,89,149,239,2730,2731,2732],e6 [553] ([14,89,149,460,539]++r 2733 5),u6 [71,96,16] [85,364,370,382,2038,2495,2496,2738],e6 [412,57,16] ([21,612,1055,1306,1579,1851]++r 2739 4),u6 [258,71,16] [364,370,528,891,1901,2034,2743],([57,0,1,2,16,4,5,83],[5,423,592,729,750,774,967,1085,1805,1806,2744],[]),u6 [123,16] [5,14,137,361,385,388,396,423,455,1579,1580,2716,2745],u6 [16,105] [14,20,137,364,369,370,612,2746,2747,2748],([0,1,554,3,4,5],([5,89,137,460]++r 2749 5),[]),([555,0,1,2,3,5],[5,14,85,137,2754,2755],[]),e6 [67,397] ([5,40,45,53,85,89,164,1107,1204,1231]++r 1258 4),([75,1,2,3,16,4,5],[218,226,234,236,298,1579,2756],[0]),([127,1,2,3,16,4,5,24],[5,40,158,197,208,226,294,392,396,420,612,1579,2172],[0]),([101,110,0,2,3,4,79],[45,85,272,466,997,1236,1237,1238],[0]),u6 [52,16] [5,14,40,364,370,472,826,832,1579,1580],e6 [556,16] [20,40,53,89,137,364,612,2757,2758,2759],e6 [557] ([5,89,460]++r 2760 4),e6 [192,480] [89,220,1453,2007,2009,2764,2765,2766],e6 [17,537] [5,226,497,1093,1096,2613,2614,2615,2618],u6 [71,30] [14,348,361,382,777,782,1675,1901,2692,2695],e6 [558] [53,89,149,226,239,348,2615,2767],e6 [559] [40,163,350,847,1461,2328,2768,2769,2770],u6 [16,207] [5,14,40,364,370,390,2721],([130,0,2,3,4,17,5,7],[5,497,520,843,1329,1330,2771,2772,2773],[0]),u6 [23,331] [85,863,1402,2222,2223,2227,2774],([57,130,0,2,3,4,5,7],[5,53,774,843,1326,1638,1780,2771,2772,2773],[]),u6 [130,220] [14,89,440,539,837,844,1049,2242,2670,2775],u6 [148,155,24] [45,135,155,460,922,2776],e6 [130,280] [14,21,539,844,2191,2269,2270,2777],u6 [257,135] [53,85,137,164,1460,1461,1463,1830,1832,1863,2778,2779],e6 [560] ([20,163,1357,1577]++r 2780 6),([130,75,1,2,3,4,5],[149,218,220,226,236,298,2130,2786],[]),([101,0,2,3,13,4,135,5],[5,40,53,539,1137,1184,1204,1243,1773,2066,2787],[]),([101,561,0,2,3,4,5],([74,85,137,226,348]++r 2788 4),[]),u6 [148,160] [5,14,45,89,137,146,155,156,165,170,220,618,928,961,1795],u6 [242,16] [40,220,361,370,763,777,1579,1580,2697,2699],e6 [562] ([5,149,220,348,350,354,1461]++r 2792 5),([0,1,148,3,4,5,30],[5,89,156,966,2797],[]),e6 [441,16] [14,53,72,85,89,137,220,364,423,1599,1601,2798],e6 [555] [14,85,89,137,149,184,239,2468,2754,2755],u6 [286,7] [220,355,668,669,1290,1618,1620,2799,2800],e6 [228,13] [5,40,72,354,452,453,1141,1143,1243,2292,2801],e6 [563,83] [5,21,348,592,729,967,968,970,971,991,2802,2803],e6 [228,67] [5,40,89,164,452,453,1108,1114,1116,1235,2292,2804],([183,1,2,3,4,135,5],[5,85,786,787,1348,1353,1461,2805],[]),e6 [248,7] [53,89,137,220,226,668,1290,1762,1780,2579,2580,2581,2806,2807],([132,179,0,1,3,4,135],[5,40,847,1030,1460,2808,2809],[0]),u6 [148,7] [5,45,156,220,928,966,1290,2810],([564,1,2,3,4,5,427],[5,149,921,1425,1541,2811,2812,2813],[]),e6 [565,135] ([53,163,164,847,854,1461,1463]++r 2814 4),e6 [566,135] ([20,53,89,137,350,847,854,1458,1577]++r 2818 4),e6 [71,249] [14,20,89,149,361,620,784,1774,1900,1901,2050,2822],u6 [16,180] [5,14,53,89,137,361,364,1053,1579,1580,1733,1735,1736,2823],([0,1,165,3,4,5],([89,539]++r 2824 7),[]),([567,0,1,2,36,4,5],[14,53,163,406,566,871,2831,2832,2833],[]),u6 [272,17] [5,89,444,520,539,584,1096,1330,1868,1869,2834,2835],u6 [259,83] [5,72,89,220,242,348,967,970,971,975,2472,2474,2836,2837],([0,2,3,267,4,5,7],[85,226,356,539,2838,2839,2840],[]),u6 [66,7] [5,29,220,355,375,497,533,652,668,2685],([0,6,2,3,4,79,7],[45,85,272,466,539,2080,2081],[0]),u6 [267,30] ([85,226,1283,1675,2692]++r 2841 4),e6 [132,267] ([20,53,89,163,226,1010,1022,1926,2840,2841,2842]++r 2845 6),e6 [569] [14,85,137,460,2851,2852],e6 [67,343] [5,14,53,85,89,164,1107,1349,1744,1745,1747,2219,2678,2853],u6 [171,16] [5,20,53,137,220,361,370,423,1579,1580,1980,1982],([0,2,3,4,94,5,7],[5,53,539,604,855,2854],[0]),([28,260,2,3,4,5,7],[539,626,659,893,1337,1711,2855],[]),([28,338,0,2,3,4,5,7],[5,220,539,625,626,679,894,1349,2286,2856],[]),e6 [570] [5,149,220,348,1137,1444,2857,2858]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_25_8_3 : checkNodesBT W_25 g_25 F_25 P_25_8 A_25 B_25_7 8 N_25_8_3 = true := by decide +kernel
def N_25_8_4 : List NodeSpec := [([28,195,0,2,3,4,5],[137,220,239,350,429,1137,1153,1605,2859],[]),e6 [57,571] [40,85,164,589,592,774,1055,1639,2860,2861],u6 [71,123,16] [137,364,370,385,455,2716],([28,0,1,29,3,4,30],[226,239,893,1444,2005,2006,2535,2862],[0]),u6 [229,163,24] [14,165,409,585,617,1356,1665,1853,2863],e6 [572] [72,163,220,350,893,1444,2864,2865],([28,0,356,2,3,4,5],[137,239,350,539,893,1006,2866],[]),e6 [573] [5,85,89,239,967,2867],([0,1,2,3,426,135,5],[21,40,53,85,1353,1460,1532,2106,2868,2869],[]),([269,271,0,2,3,4,5],[137,239,539,564,1106,1515,2870,2871,2872],[]),u6 [28,177] ([5,53,137,163,248,267,720,975,982,1545,1642]++r 2873 4),e6 [574] [5,72,85,89,149,239,348,1000,2877,2878],([28,175,0,1,2,3,5],[14,137,163,244,1332,2879],[0]),e6 [575] [14,89,163,220,460,1279,2880,2881,2882],e6 [576] [85,89,239,350,893,2883],e6 [28,373] [20,53,89,893,1090,2884,2885],([0,1,37,2,36,4,5],[14,53,163,406,566,736,866,867,2886],[0]),e6 [373,135] [20,53,89,137,847,1090,1458,1577,2884,2887,2888],([0,1,2,36,4,17,5],[163,406,496,520,566],[0]),([75,1,2,3,13,4,5],[218,220,226,236,298,341,372,1141,2889],[]),e6 [401,24] [5,40,85,89,220,314,926,1278,1281],([57,0,1,2,36,4,5],[14,53,163,406,566,736,774,1055],[0]),u6 [93,7] [14,333,348,355,412,668,1830,1854,2890,2891],e6 [57,36] [21,53,89,163,406,566,592,774,871,1055,2892],([142,6,2,3,4,7],[40,220,539,649,880,881,2893,2894],[0]),e6 [577] ([40,53,72,85,163,220,239,350,1530]++r 2895 4),([8,0,2,3,4],[0,33,1013],[0]),e6 [101,177] [5,68,72,248,465,980,1205,2873,2899],([8,0,2,3,4,7],[0,5,33,40,539,1013],[0]),e6 [110,292] ([5,45,689,2503]++r 2900 6),e6 [578,7] [14,21,355,652,668,2286,2906,2907],([338,0,6,2,3,4,7],[14,539,895,2080,2081,2908],[0]),([201,0,6,2,3,4,7],[5,14,537,539,2081,2909],[0]),e6 [579] [53,72,163,220,350,496,520,2910,2911],([150,1,2,3,4,5,24],[5,184,220,420,617,2912,2913],[0]),([269,0,6,2,3,4,5],[137,239,539,564,2914,2915,2916],[0]),e6 [580] [72,85,89,149,184,226,239,2917,2918,2919],u6 [6,292] [45,163,689,690,2503,2901,2920,2921,2922]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_25_8_4 : checkNodesBT W_25 g_25 F_25 P_25_8 A_25 B_25_7 8 N_25_8_4 = true := by decide +kernel
def N_25_8 := N_25_8_0 ++ N_25_8_1 ++ N_25_8_2 ++ N_25_8_3 ++ N_25_8_4
def B_25_8 : BT (List (List Nat)) := buildBucketsBT W_25 N_25_8
set_option maxRecDepth 500000 in
lemma B_25_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_25 8 xs.toFinset) B_25_8 := by
  have hP := buildPoolsSubBT_sound (pdepth := 12) (W := W_25) (raw := r_25) (pspecs := ps_25) (used := U_25_8) S_25_ok
  have hm0 := checkNodesBT_mem (by decide) gp_25 W_25_ok hP A_25_ok B_25_7_ok C_25_8_0
  have hm1 := checkNodesBT_mem (by decide) gp_25 W_25_ok hP A_25_ok B_25_7_ok C_25_8_1
  have hm2 := checkNodesBT_mem (by decide) gp_25 W_25_ok hP A_25_ok B_25_7_ok C_25_8_2
  have hm3 := checkNodesBT_mem (by decide) gp_25 W_25_ok hP A_25_ok B_25_7_ok C_25_8_3
  have hm4 := checkNodesBT_mem (by decide) gp_25 W_25_ok hP A_25_ok B_25_7_ok C_25_8_4
  exact buildBucketsBT_of_mem (forall_append (forall_append (forall_append (forall_append (hm0) hm1) hm2) hm3) hm4)
def U_25_9 : List Nat := ([5,14,20,21,40,45,53,68,72,85,89,103,135,137,149,150,155,156,158,163,164,165,170,181,182,184,220,226,236,239,242,272,289,302,304,307,314,328,333,336,338,341,348,350,355,356,358,361,364,369,370,372,375,392,393,396,406,409,420,423,450,451,452,460,465,466,482,496,497,510,511,517,519,520,522,539,589,595,597,605,612,617,618,620,622,626,628,649,650,652,656,659,668,670,713,720,725,727,729,755,773,774,777,780,782,786,788,793,812,837,844,847,852,858,871,893,894,904,910,913,914,921,925,926,928,940,946,958,965]++r 967 5++[975,976,982,986,991,992,995,996,997,1000,1001,1002,1010,1012,1013,1014,1022,1023,1024,1030,1031,1044,1049,1053,1055,1056,1057,1079,1085]++r 1090 4++[1095,1096,1107,1108,1111,1113,1114,1116,1117,1127,1128,1137,1140,1141,1143,1153,1168,1176,1182,1183,1184]++r 1186 4++r 1191 4++[1204,1205,1213,1215,1216,1217,1220,1226,1229,1232,1235,1236,1238,1243,1252,1253,1259,1261,1268,1271,1272,1274,1275]++r 1277 4++[1283,1290,1301,1303,1306,1317,1318,1320,1326,1327,1329,1330]++r 1333 7++[1341,1347,1349,1353,1355,1357,1359,1360,1362,1368,1370,1371,1373,1374,1376,1377,1379,1381,1383,1384,1385,1388,1389]++r 1393 4++[1402,1408,1422,1425,1427,1431,1432,1444]++r 1452 12++[1465,1468,1471,1472,1476]++r 1480 5++[1503,1505,1507,1508,1509,1511,1513,1515,1517,1519,1522,1524,1527,1530,1533,1536,1537,1540,1541,1544,1545,1552,1567,1568,1569,1571,1576,1577,1579,1580,1582,1583,1589,1595,1599,1601,1609]++r 1616 4++[1622,1625,1628,1629,1631,1638,1639,1642,1654,1660,1667,1669]++r 1673 4++[1679,1685,1687,1688,1692,1718,1720,1721,1733,1735,1738,1741,1742,1747,1762,1764,1774,1775,1778,1780,1781,1790,1791,1795,1799,1801,1802,1806,1809,1811,1814,1829,1831,1832,1841,1846,1848,1849,1851,1852,1854,1858,1864,1865,1866,1868,1870,1872,1875,1891,1898,1900,1901,1903,1904,1917,1924,1930,1931,1938,1944,1949,1951,1952,1961,1967,1969,1970,1978,1979,1980,1982,1985,1995,1996,2006,2007,2009,2015,2020,2021,2022,2024,2027,2033,2034,2037,2038,2046,2047,2048,2050,2058,2059,2062,2065,2076,2080,2083,2088,2094,2107,2115,2127,2130,2131,2134,2137,2139,2140,2142,2144,2152,2153,2154,2172,2179,2191,2192,2193,2202,2212,2219,2225,2226,2227,2231,2236,2237,2241,2242,2251,2256,2262,2263,2264,2269,2271,2273,2286,2291,2300,2309,2310,2315,2321,2335,2351,2352,2357,2358,2361,2362,2366,2395,2397,2404,2405,2414,2447]++r 2466 4++[2472,2474,2489,2499,2507,2533,2535,2536,2544,2550,2558,2561,2580,2584,2585,2586,2594,2603,2614,2615,2630,2631,2646,2652,2653,2658,2665,2670,2678,2691,2692,2693,2704,2706,2737]++r 2739 4++[2744,2757,2771,2773,2787,2788,2816,2823,2835,2842,2843,2846,2847,2849,2852,2866]++r 2872 4++[2892,2901,2903,2920,2921]++r 2923 245)
def P_25_9 : BT (Option BoundPool) := buildPoolsSubBT 12 W_25 r_25 S_25 ps_25 U_25_9
def N_25_9_0 : List NodeSpec := [u6 [331] [53,85,89,137,163,239,1013,2225,2227],e6 [581] [89,137,239,539,958,1013,2923],u6 [154,24] [5,45,72,85,156,163,165,226,314,420,617,914,926,2447],u6 [24,145] [5,14,150,156,163,226,420,926,2924],u6 [226,24] [5,14,45,135,156,239,420,460,617,2925],u6 [148,24] [5,14,45,135,155,156,158,460,617,618,928,940,969],u6 [156,24] [5,14,40,53,137,156,420,511,780,925,926,1720,1985],u6 [156] [5,72,89,137,163,184,239,348,511,539,780,958,1720,1985,2152,2153],u6 [24,160] [5,14,45,137,156,165,170,181,420,925,926,1795,2231,2926],u6 [163,24] [5,85,137,156,165,220,409,420,617,628,725,2251,2927,2928],([127,1,2,3,4,5,24],[5,45,149,302,304,392,420,460,628],[0]),u6 [75,24] [5,14,21,156,165,184,220,226,236,341,420,617,925],([75,1,2,3,4,5],[149,236,341,372],[0]),u6 [373] [53,89,137,1013,1090,2929],u6 [348] [89,137,239,350,965,1013,1056,1057],u6 [175,83] [5,72,85,163,348,350,539,970,971,975,1595,2930],u6 [175] [5,14,53,72,89,137,149,163,184,239,242,350,2094,2930],u6 [83,24] [5,156,163,350,926,975,1013],u6 [350,83] [5,85,89,163,220,242,348,539,967,970,971,975,976,1341,2931],u6 [392] [5,85,89,137,184,239,348,350,958,1268,1801,1802,2932,2933],u6 [176,83] [5,72,85,137,163,220,348,967,970,971,975,1396,2934],u6 [177] [53,137,460,720,986,2873],u6 [347] [5,53,72,89,137,149,163,184,226,239,350,1654,2273,2935],u6 [145] [5,53,85,89,137,149,163,184,239,466,2236,2237],e6 [582,79] [45,85,89,163,350,539,995,996,997,1001,2936],u6 [292] [45,53,137,348,460,2921,2937],e6 [459,79] ([45,53,85,163,539,996,1001]++r 2938 4),e6 [132,83] [5,20,72,89,163,239,242,539,967,968,1013],([132,179,0,1,3,4],[89,348,1012,1013,1030],[0]),u6 [132,180] [5,20,89,350,460,650,1733,2823],u6 [280] [14,21,53,137,163,239,1013,2269,2271],u6 [180] [5,20,53,89,137,149,163,650,1053,1733,1735,2823],u6 [181] [45,53,85,89,137,149,163,1014,2357,2358,2361,2362],u6 [132,190] [5,20,89,460,1022,1357,2362,2942],u6 [190] [5,89,137,239,307,539,958,1022,1024,1031,1616,1619,2942,2943],u6 [24,151] [5,14,21,45,89,156,420,926,946,2944,2945],u6 [316] [5,14,21,53,72,89,137,149,163,184,239,348,350,782,2202],u6 [30,24] [5,45,89,156,350,926,1013],e6 [583,79] [45,85,184,921,995,996,997,1001,2938,2946],u6 [30,83] [5,163,975,1013,2947],u6 [79,30] [5,21,45,163,539,782,858,995,996,997,1001,1283,2947,2948],u6 [361] [5,72,137,163,184,220,239,348,350,539,958,1044,2015,2949,2950],([0,1,29,3,4,30],[239,1013,2006,2535],[0]),u6 [220] [14,53,89,137,163,837,1013,1049,2670],u6 [364] [53,85,89,137,163,1013,2558,2561,2951],u6 [132] [5,45,53,72,89,137,163,239,350,1013,2665],u6 [57,136] [14,21,89,239,348,539,595,773,774,1055,1056,1085,1091,1427],([57,0,1,3,4,5,30],[5,21,89,239,348,460,782,1085,2652,2653],[0]),u6 [57,287] [21,40,89,239,774,1055,1639,2952],u6 [353,79] [45,72,85,137,163,350,995,996,997,1001,2953],u6 [57,310] [5,14,21,89,348,460,774,2630,2631,2954],u6 [57,199] [14,21,72,89,460,773,774,1327,2955],u6 [199] [53,85,89,137,149,163,226,348,1327,1431,2955],u6 [339] ([40,89,137,348,539,774,958,1079]++r 2956 4),u6 [171] [5,20,53,72,137,149,163,184,239,348,1980,1982,2960],u6 [136,17] [163,239,496,519,520,539,595,1056,1091,1093,1330],u6 [517] [53,85,137,149,163,164,184,226,519,2414,2961],u6 [269] [72,137,163,184,220,239,348,350,539,958,2872,2962,2963,2964],u6 [568] [5,53,89,137,149,164,184,350,460,2852,2965],u6 [376] [5,53,89,137,149,164,184,226,1117,2966],u6 [188] [40,85,89,137,348,482,958,1107,1127,2646,2967,2968],u6 [299] [14,89,137,149,163,220,348,1848,2058,2059,2142,2144,2969],u6 [514] [89,137,149,163,220,226,539,1536,2395,2397,2970,2971,2972],u6 [271,24] [5,14,21,156,226,460,617,925,926,1013,1370,1870],u6 [136,213] [14,348,595,1056,1091,1511,1660,2405,2973,2974,2975],e6 [247,13] [220,226,239,1137,1141,1143,1184,1617,1622,1685,2309,2976],([75,1,2,3,4,5,24],[5,14,45,184,236,341,372,420,617],[0]),u6 [22,24] [5,85,89,135,156,165,239,420,617,1422,1425,1481,1522,1764,2088,2977],u6 [345,24] [5,45,156,165,220,617,925,1013,1617],u6 [433] [5,14,53,89,149,239,348,539,2024,2027,2978],u6 [438] [20,45,53,149,163,239,1511,1589,1660,2335,2979],([0,2,3,4,135,5,7],[5,53,333,348,539,847,1460,1978,1979],[0]),u6 [201] [5,14,53,72,89,137,149,163,184,239,333,336,348,350],([132,0,1,3,4,17,5],[5,20,89,239,348,350,460,650,1742,2193,2980],[0]),u6 [290] [5,14,53,89,149,163,348,1764,2137,2139,2981],u6 [101,92] [85,239,460,713,1013,1204,1216,1898,2982],u6 [231] [40,53,72,89,163,184,239,348,350,460,539,958,2062,2499,2983,2984],e6 [412,79] [85,272,460,466,995,996,1970,2938,2985],u6 [556] [5,53,89,137,163,1013,2757,2986],([183,1,2,3,4,5],[149,239,786,788,1217],[0]),u6 [135,30] [5,137,220,777,782,1283,1353,1457,1459,1461,2987,2988],e6 [412,67] [14,85,149,1013,1113,1114,1116,1969,1970,2739,2985,2989],u6 [92,16] [53,85,226,361,370,460,1580,1864,1898,2990],e6 [412,13] [21,220,793,1141,1143,1243,1969,1970,2976,2985,2989],u6 [137] [14,53,89,137,239,595,1013,1432],u6 [201,7] [5,14,333,348,355,539,652,668,1780],u6 [412,23] [21,85,460,1376,1377,1395,1402,1969,1970,2740,2985,2989,2991],u6 [132,271] [5,85,149,184,239,460,1010,1013,1022,1924,2362],u6 [22,79] [5,45,85,163,466,539,995,996,997,1000,1001,1422,1522,1764,2992,2993],u6 [29,16] [14,40,53,89,137,163,239,361,364,370,612,837,1544,2951,2994],e6 [412,28] [85,149,460,893,1013,1642,1969,1970,2874,2985],u6 [412,22] [14,85,149,460,1013,1422,1425,1522,1969,1970,2977,2985],u6 [478] [21,53,89,137,239,517,1741,2291,2550,2995],u6 [92,24] [14,156,165,226,420,460,617,713,925,926,1013,1865,1898],u6 [101,30] [45,1013,1216,1283],u6 [223,13] [21,72,149,163,220,239,1137,1143,1243,1508,1509,1568,2976],u6 [223,135] [40,53,85,220,460,1353,1457,1458,1460,1461,1576,2107,2996],u6 [223,16] [14,53,72,85,163,220,361,370,423,460,1509,1568,1580,1852,2990,2997],u6 [67,24] [5,45,89,135,156,163,164,165,226,289,348,350,420,539,617,926,1107,1111,1116,1333],u6 [406] [5,14,21,53,149,163,239,348,2975,2998,2999],u6 [130,223] [14,53,149,184,220,348,460,539,1508,1509,1568,1638,2027,2107,2130,2191,2603],u6 [312] [14,53,89,137,149,164,348,1226,1229,1333,1858,3000],u6 [23,24] [5,21,156,165,181,348,350,925,1377,1379,1395,1408,1961,3001],([0,1,2,16,4,5,83],[5,53,72,85,163,348,423,729,967,1806,2744,3002],[0]),u6 [231,223] [85,184,220,239,460,958,1509,1513,1536,1692,1846,1848,2997,3003,3004],u6 [418] [45,53,85,137,149,163,164,184,1462,1465,1468,2947],u6 [426] [14,21,53,89,137,149,163,239,348,1533,2107,2131],u6 [229,7] [53,220,333,355,460,517,539,668,1013,1780,2021,3005],u6 [223,23] [21,53,85,239,460,1374,1377,1395,1508,1509,1568,1849,2991,2997],u6 [565] [53,85,137,163,164,239,1013,2816,3006],u6 [249,16] [53,85,89,226,239,361,364,370,620,1579,1580,2050,2990],u6 [192,23] [40,53,137,226,239,1128,1374,1377,1395,1402,1408,1453,2225],u6 [224] [53,85,89,137,163,239,348,1567,1568,3007],u6 [441] [53,72,89,137,163,220,348,350,1599,1601,3008],u6 [409] [53,85,149,163,164,184,226,239,1383,1385,2974],u6 [520] [72,89,137,163,184,348,460,539,958,1848,3009,3010,3011],u6 [343] [5,14,53,89,149,163,239,893,1349,1747,2219,2678],u6 [247,30] [85,220,239,782,1013,1283,1617,1622,1674,1675,2691,2947],u6 [310] [5,14,21,53,89,137,149,163,348,1085,2630,2631,2954],u6 [247,16] [53,85,226,361,370,460,1579,1580,1617,1622,1685,2990],u6 [67,223] [14,85,89,149,164,184,348,1114,1116,1235,1333,1508,1509,1519,1568,2107],u6 [412,16] [14,85,220,423,460,612,1579,1580,1969,1970,2740,2742,2989,2990],([0,6,2,3,4,7],[137,348,539,622,1013,2080],[0]),u6 [247,231] [53,85,220,460,958,1530,1536,1617,1622,1687,1692,1848,2310,3003,3012,3013],u6 [459] [40,45,85,89,137,184,239,348,350,958,2939,2940,2941,3014],u6 [132,182] [5,20,85,89,137,460,1022,1023,3015],u6 [132,247] [85,149,226,460,650,1010,1013,1022,1617,1685,2309,2315,2362,2706],u6 [28,223] [85,149,184,220,348,460,1349,1444,1508,1509,2107,2874,3016],u6 [135,83] [5,72,85,163,242,539,729,967,1353,1461,3017,3018],u6 [28,67] [5,53,89,163,164,220,1107,1114,1116,1235,1333,1349,1444,1545,1642,2846,2874,3019,3020],u6 [6,13] [14,72,163,239,793,871,1137,1143,1184,1243,1389,2037],u6 [192,22] [40,85,89,226,239,1128,1425,1453,1522,1764,1949,2225,2977,2993,3021],u6 [101,249] [85,89,149,184,239,605,1013,1204,1205,1215,1216,1774,1775,3022],u6 [16,24] [5,45,137,156,165,181,226,348,361,370,925,926,1580,2172,3023],e6 [247,130] [53,149,220,226,539,1685,2027,2130,2191,2603],u6 [247,23] [53,85,239,460,1374,1376,1377,1395,1408,1617,1618,1622,1685,2309,2321,2991,3024],u6 [464] [5,53,137,163,226,239,460,1891,3025,3026],u6 [271,13] [21,53,72,149,184,226,1137,1141,1515,1924,2976],u6 [88] [72,89,137,149,348,350,393,450,460,1362,1503,2083],u6 [57,110] [14,21,53,89,137,226,239,348,589,774,1055,1085,1168,1176,1188,1189,2903],u6 [213,79] [5,45,85,163,466,995,996,997,1001,1472,1511,2974,2975],e6 [292,79] [45,85,163,539,996,1000,1001,2901,2921],e6 [101,247] [85,149,220,460,1013,1204,1215,1216,1617,1622,2309],u6 [278] [14,21,72,89,137,149,163,184,239,348,350,1408,2192,3027],u6 [57,130] [5,21,53,89,220,539,773,774,1085,1638,2027,2130,2191,2242,2256,2603,3028],u6 [130,249] [53,89,149,226,239,539,605,620,1774,2027,2130,2191,2241,2242,2603],u6 [412,57] [40,85,149,220,460,1013,1055,1306,1969,2739,2741,2985,2989],u6 [401] ([53,89,149,163,184,348,350,460]++r 1277 4),u6 [213,83] [5,72,163,967,970,971,975,1471,1507,2973,2974],u6 [202] [53,85,89,137,149,184,226,348,460,1333,3029],e6 [92,79] [85,163,226,460,996,997,1001,1864,1898,2938],u6 [29,79] [40,45,89,163,226,239,272,539,837,997,1000,1001,1544,2951],u6 [435] [5,53,89,137,149,163,226,1571,3030,3031,3032],u6 [356] [137,239,350,539,1013,3033],u6 [228] [5,40,72,89,137,149,163,184,239,348,452,3034],u6 [231,79] [45,85,163,466,539,996,997,1000,1001,1472,1530,1692,1848,2938,3035,3036],u6 [213,223] [21,85,149,184,348,1508,1509,1511,1513,2973,3037],u6 [229,135] [5,53,220,460,517,539,847,1353,1457,1458,1460,1461,1718,1741,2996],u6 [429] [45,89,137,149,163,220,350,1903,1904,3038,3039,3040],u6 [17,83] [5,163,242,519,520,539,970,975,1095,1096,1330,3041],u6 [101,132] [45,53,89,239,1013,1022,3042],u6 [186,83] [85,184,220,921,967,970,971,975,992,3043,3044],e6 [412,231] [85,220,460,958,1013,1530,1738,1967,1969,1970,2989,3003,3045,3046,3047],u6 [229,24] [14,21,156,165,460,517,539,617,925,926,1013,1721,1741],u6 [250] [53,85,89,137,149,163,510,620,1625,1629,3048],u6 [195] [40,72,137,184,220,239,328,348,350,958,1153,3049,3050],u6 [57,369] [5,14,21,85,89,137,460,774,1085,1213,3051,3052],u6 [233] [53,137,149,163,239,460,1898,1917,1996,3053],u6 [213,24] [5,21,85,156,165,420,617,926,1384,1609,2973,2975,3054],u6 [424] [53,72,89,149,163,239,348,350,1515,1517,1951,1952,3055],u6 [110,79] [53,72,163,226,466,539,996,1001,1168,1176,2938,3056,3057],u6 [249,24] [14,135,156,165,226,420,605,617,925,926,1013,1628,1774],u6 [128,24] [5,21,45,89,156,165,220,348,420,617,910,913,926,3058,3059],u6 [132,24] [5,45,89,135,165,239,350,650,1013],u6 [7,30] [5,45,53,137,355,1013,2691],u6 [179,135] [40,53,137,226,847,1457,1458,1460,1461,2271,3006],u6 [271,83] [5,53,72,163,184,460,970,975,1515,1924,3043],u6 [249,79] [85,89,163,226,620,995,996,997,1001,1774,2938],u6 [223,17] [85,220,239,519,520,1092,1093,1096,1330,1509,2107,2127],e6 [412,135] [40,85,220,460,847,1353,1457,1460,1969,2740,2985,2996,3060],u6 [57,223] [40,85,149,184,220,239,348,460,773,774,1085,1306,1508,1568,1569,1841,2107],u6 [13,135] [5,53,220,539,1137,1184,1243,1353,1458,1460,1461,2976,3061,3062],u6 [28,249] [5,85,89,149,239,605,893,1349,1444,1545,1642,1774,2874,3063],u6 [36] [53,89,163,239,406,871,1013],u6 [57,271] [5,21,85,149,460,773,774,1055,1085,1306,1370,1924,2076],u6 [412,17] [85,220,496,1092,1093,1096,1330,1970,2985,3064],u6 [248] [53,89,137,163,220,1762,2580,3065,3066],u6 [271,17] [5,85,496,519,520,1092,1093,1096,1330,1370,1515,2835],u6 [130,92] [53,226,239,539,713,1864,1898,2027,2191,2603],u6 [229,23] [21,53,163,239,517,539,1374,1376,1377,1395,1718,1721,2022,2991],u6 [327,135] [5,53,137,539,847,852,1461,3067,3068],u6 [13,24] [21,45,156,165,539,617,926,1137,1140,1143,1184,1243],u6 [455] [5,53,89,137,149,239,350,517,1799,2022,3069],u6 [101,79] [45,85,163,465,466,539,995,996,997,1001,1204],u6 [63,7] [5,53,239,338,355,460,539,668,670,812,1290,1301,1303,1338,1339,1676],u6 [67,271] [53,89,149,164,226,460,1107,1114,1370,1371,1515,1924,2134],u6 [249,83] [72,85,89,163,239,242,620,967,968,970,971,975,1013,2212,3043],u6 [28,92] [5,85,149,239,460,713,1349,1444,1898,2300,2874],u6 [229,17] [163,220,239,496,517,519,520,539,1092,1093,1096,1330,1718,1721,1741],u6 [322] [20,21,53,89,137,163,348,1774,1781,1814,2048]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_25_9_0 : checkNodesBT W_25 g_25 F_25 P_25_9 A_25 B_25_8 9 N_25_9_0 = true := by decide +kernel
def N_25_9_1 : List NodeSpec := [u6 [92,7] [53,226,333,355,460,652,668,713,1013,1780,1829,1854,1995,3005],u6 [456] [89,137,350,539,1013,3070,3071],u6 [272] [53,89,149,163,239,1868,1872,1924,3072],u6 [22,83] [5,85,89,163,239,348,539,967,968,970,971,975,2993,3073,3074],u6 [223,22] [14,85,89,239,460,1508,1522,1764,2107,2977],u6 [495] [5,53,89,137,149,163,226,239,1013,2179,3075,3076],u6 [505] [5,40,45,72,137,149,163,184,239,348,350,2366],u6 [13,7] [5,45,220,355,539,668,1137,1143,1243,1373,1780,2976,3077,3078],u6 [92,83] [85,163,242,460,967,971,975,1013,1864,1898,3043],u6 [130,17] [5,220,239,519,520,539,1093,1096,1330,1638,2027,2130,2191,2603],e6 [247,67] [85,89,149,164,226,1107,1114,1116,1333,1685,3079],u6 [247,7] [53,220,226,333,355,460,668,1013,1617,1618,1622,1679,1780,2309,3005],u6 [63] [53,89,137,149,163,338,348,350,460,670,1301,1303,1339,1676],u6 [561] [5,85,89,149,163,184,226,239,539,1458,3080,3081],u6 [247,83] [85,163,242,460,967,970,975,1013,1617,1622,1685,3043],u6 [229,231] [89,220,239,517,539,958,1530,1669,1692,1721,1738,1848,1931,2352,3003,3082,3083],u6 [259] [53,89,149,163,184,348,460,2472,2474,3084],u6 [408] [5,21,40,53,89,163,239,1368,1370,2033,3085],u6 [392,83] [5,53,72,85,163,348,539,971,975,1268,1801,2932,3043],u6 [229,22] [5,89,149,239,517,539,1355,1422,1425,1522,1718,1721,1741,1764,2022,2140,2977,2993],u6 [231,83] [5,53,85,163,242,348,539,967,968,971,975,1471,1530,1692,1848,3043,3086,3087],u6 [57,339] [14,21,89,460,589,773,774,1079,1085,2956,2959],u6 [229,213] [5,21,53,149,239,517,1507,1511,1718,1721,2022,2352,2973,2974,3037],u6 [347,79] [45,72,85,163,226,348,350,539,995,996,1654,2273],u6 [92,135] [5,40,53,85,460,713,847,1353,1457,1458,1460,1461,1854,1898,2300,2996,3088],u6 [192,231] ([89,137,220,226,348,1128,1453,1456,1536,1692,1738,1848,1931,1949,2225,2226]++r 3089 5),u6 [148] [53,137,155,163,460,940,969],u6 [381] [5,20,53,137,149,184,226,239,348,350,3094,3095],u6 [28,229] [5,149,220,460,517,1349,1444,1642,1718,1721,1741,2022,2846,2874],u6 [231,24] [5,53,89,137,156,158,165,182,220,348,350,420,925,926,1609,1667,1692,1848,1931,3096],u6 [136,23] [14,53,137,163,239,539,595,1056,1091,1374,1377,1395,1402,1408],u6 [249,7] [53,226,333,355,605,652,668,1013,1290,1476,1774,1778,1780,2489,3005],e6 [584,135] [5,40,184,539,1353,1461,2996,3097,3098],([0,1,2,4,79,5,83],[5,72,85,163,242,348,466,1393],[0]),u6 [101,229] [149,220,460,465,517,1013,1204,1215,1216,1718,1721,1741],u6 [177,83] [5,85,163,539,720,968,971,975,982,2873],e6 [229,30] [21,239,517,539,1013,1283,1675,1718,1721,2691,2947],u6 [132,79] [5,45,89,163,350,466,539,650,995,996,997,1000,1001,1002,1010,2362,3099,3100],u6 [226] [5,53,72,89,137,149,163,184,460,1085,2154,3101],u6 [230] [53,72,89,137,149,220,451,1527,1938,3102],u6 [132,229] [149,220,460,517,539,650,1010,1013,1022,1360,1721,1741,2362,2706],u6 [179,79] [40,72,163,226,272,466,539,996,997,1001,2271,2866],u6 [262] [53,85,89,137,163,239,1673,1685,1688,3103],u6 [28,83] [5,72,85,163,242,967,970,971,975,1444,2846],u6 [101,67] [5,45,53,85,89,164,348,465,539,1107,1114,1116,1204,1205,1215,1216,1232,1235,1333,2982,3104],u6 [247,22] [5,85,89,149,239,460,1422,1522,1617,1764,2309,2321,2977],u6 [247,213] [5,53,85,149,239,1507,1511,1617,1622,2310,2321,2975,3037],u6 [136,22] [14,89,239,539,595,1056,1091,1425,1427,1522,1764,2977,2993,3105],u6 [427] [5,45,53,89,149,163,184,1425,1522,1537,1540,1541,1875],u6 [231,299] [68,220,460,539,1692,1848,2059,2142,2969],u6 [257] [53,85,137,163,164,239,1832,1864,1866,3106],u6 [552] [5,72,89,137,163,184,350,460,539,958,2737,3107,3108,3109],u6 [132,181] [20,45,72,89,460,1022,2357,2362],u6 [231,523] [68,89,220,539,1738,1848,3110,3111,3112],u6 [480] [53,89,149,184,348,460,2007,2009,3113],u6 [136,231] [14,89,239,348,539,595,1056,1091,1427,1692,1738,1848,1930,1931,2405],e6 [506,135] [5,239,539,1353,1577,2351,2584,2585,2586,3114,3115],u6 [235,16] [40,184,220,370,1505,1579,2507,2990],u6 [338,7] [5,53,89,220,333,348,355,539,652,668,894,1631,2286],([0,2,3,16,4,5,7],[45,53,137,226,348,1780,2046,2047],[0]),u6 [79,7] [45,53,85,163,333,355,356,466,539,668,996,997,1001,2938,3116,3117],u6 [57,7] [5,21,53,89,103,137,333,348,355,589,652,668,774,1085,1275,1290,1326,1338,1347,1780,1841],u6 [223,79] [72,85,149,163,460,466,996,997,1001,1509,2107,2938],([101,0,2,3,16,4,5],[45,53,72,85,137,358,423,465,597],[0]),u6 [192,13] [40,239,539,793,1128,1137,1143,1184,1243,1453,2225],([142,1,2,3,4,5,7],[5,40,137,184,539,649,652,668,727,904,3005],[0]),u6 [160] [5,72,89,184,239,539,847,958,1460,2262,2263,2264,3118,3119],u6 [57,83] [5,21,89,163,242,348,539,773,774,967,968,970,971,975,991,1085,3120,3121],u6 [88,16] [40,72,85,137,163,239,361,364,370,393,396,423,450,1362,1503,1579,2083],u6 [142,7] [40,184,220,355,539,652,668,727,1013,3005],u6 [73,16] [20,40,53,72,85,89,137,163,220,361,370,423,755,1579,1580,2533,2594],u6 [28,30] [5,85,220,239,782,1283,1444,1675,2692,2843,2874,2947,3122],u6 [16,17] [53,137,163,220,361,370,375,423,519,520,1092,1330,1579,3123,3124],u6 [57,16] [21,53,72,89,137,239,361,364,370,396,423,589,773,774,1085,1579,1580,1851],u6 [16,30] [5,45,137,220,361,370,423,777,1283,1579,1580,2691,2947,3125,3126],e6 [412,213] [21,85,149,239,1507,1660,1967,1969,1970,2973],u6 [179,16] [14,40,53,72,137,163,361,370,423,612,1580,2271,3006],u6 [192,213] [85,226,348,1128,1453,1456,1511,1660,2225,2973,2974,2975],u6 [71] [14,89,137,149,184,239,348,350,361,1901,2034],u6 [243] [40,85,89,137,163,239,348,361,958,2536,2693,2704,3127],u6 [71,16] [14,40,72,85,137,163,350,361,370,423,1579,1580,1900,1901,2034,2038],u6 [89,16] [14,20,53,137,163,369,370,612,1524,3128],u6 [132,28] [5,20,53,85,89,220,650,1010,1022,1349,1545,1642,2362,2846,2847,2874,2875,3129],u6 [119] ([5,85,89,137,184,239,350,423,958]++r 2466 4++[3130]),u6 [454] [85,137,149,163,164,184,226,1374,1790,1791,3131,3132],u6 [110,13] [14,53,239,539,793,1143,1168,1176,1184,1243,2976,3133,3134],u6 [457] [40,53,89,149,163,226,239,1013,1809,1811,3135],u6 [227] [5,40,89,137,149,184,226,239,348,350,3136],u6 [67,110] [14,53,89,137,164,348,539,1107,1108,1113,1168,1176,1183,1188,1235,2903,3137],u6 [227,16] [40,53,85,137,163,348,361,370,522,1579,1580,3136,3138],e6 [192,67] [40,89,164,348,539,1107,1113,1116,1128,1235,1333,1453,1949,2225,3139],u6 [537] [5,53,89,149,184,226,239,539,2614,2615],([130,0,2,3,4,5,7],[5,53,226,539,1780,2771,2773],[0]),u6 [271,79] [85,163,226,460,995,1001,1370,1515,1924,2938],u6 [130,29] [5,14,53,89,239,539,837,844,1544,2191,2242,2951],u6 [130,30] [5,163,239,539,1283,1675,2130,2191,2603,2692,2947],u6 [158,24] [14,45,137,156,165,220,420,617,628,3140],u6 [192,16] [40,53,72,137,163,361,370,423,612,1128,1580,2225],u6 [132,130] [5,20,53,89,539,1010,1022,1638,2027,2130,2191,2242,2256,2362,2603,3141],u6 [130,179] [14,53,348,539,844,1638,2027,2191,2271,2866,3006],u6 [130,24] [5,156,163,165,226,420,539,617,926,2027,2191,2603,3142],u6 [506] [5,89,137,149,163,348,350,460,2584,2585,2586,3114,3115],u6 [23,83] [5,85,163,348,539,967,975,1374,1376,1394,1395,3043,3143,3144],u6 [192,130] [5,53,348,539,844,1128,1638,2027,2191,2225,2603],e6 [412,130] [14,149,220,460,844,1013,1969,1970,2130,2603,2985,2989,3145],([28,0,2,3,4,5,7],[5,53,333,348,539,626,893,1349,1484,2020],[0]),([101,0,2,3,4,135,5],[5,40,53,137,348,350,1204,2065,2788],[0]),u6 [67,135] [5,53,85,89,137,164,350,539,1235,1333,1353,1457,1458,1460,1461,1463,1577,3079,3146],e6 [585,135] [5,53,89,350,539,1353,1457,1461,3147],u6 [29,135] [5,40,53,89,137,226,239,837,847,1458,1461,1544,1577,2951,2994],u6 [249,135] [5,40,53,85,605,620,847,1353,1457,1458,1460,1461,1476,1577,1774,2996,3063,3148],([0,22,23,3,4,5],[53,68,239,1452,1454,1455],[0]),u6 [132,135] [5,53,89,137,650,1022,1353,1357,1359,1457,1458,1460,1461,1577,2351,2706,3149],u6 [101,24] [45,137,156,165,350,1013,1216],u6 [136,135] [53,137,163,539,595,847,1091,1457,1458,1460,1461],e6 [132,7] [20,45,53,89,137,239,1013,1022,1290,1780,2706],e6 [228,135] [5,40,137,348,452,539,1353,3034],u6 [28,13] [5,220,239,1137,1141,1143,1184,1243,1349,1444,1642,2846,2874],([132,57,0,1,3,4,5],[5,89,239,348,460,650,1085,2658],[0]),u6 [267] [53,85,89,149,163,226,239,348,2842,2846,2849],u6 [28,29] [5,85,89,226,239,837,893,1444,1544,1545,2846,2951,3150],u6 [271,30] [21,85,1013,1283,1515,1675,2544,2691,2947],u6 [67,7] [5,45,53,85,89,137,163,164,333,348,355,539,652,668,1116,1235,1290,1334,1780,1831,3079,3151],u6 [240] [40,89,137,184,348,350,460,958,1536,2404,3152,3153],u6 [389] [89,137,163,239,539,1013,1186,1187,1188],u6 [28,179] [85,226,239,348,893,1349,1444,2271,2846,2866,3006,3154],u6 [67,6] [14,53,89,163,164,871,1107,1113,1389,2037,2920,3155,3156],u6 [437] [53,72,89,163,350,1013,1582,1583],u6 [7,83] [5,53,72,163,355,539,975,1013,3043],u6 [297] [53,85,89,149,163,226,348,1480,1482,1483,2993],([0,1,2,36,4,5],[53,163,406,1013],[0]),u6 [218] [5,14,53,89,163,239,1013,1388,1389],u6 [101,17] [5,85,220,239,519,520,1093,1096,1204,1216,1330,1944,3157],u6 [6,17] [85,239,496,519,520,871,1093,1330,1389,2037],u6 [7,24] [5,45,53,137,156,350,355,925,1013],u6 [57,229] [21,149,220,460,517,539,773,774,1055,1085,1306,1721,1741,1841],u6 [28,136] [348,595,893,1056,1091,1349,1444,2846,3158],u6 [57,6] [14,21,53,85,89,239,773,774,871,1055,1389,2037,2892,2920],u6 [6,79] [72,85,163,272,466,996,997,1001,1389,2037],([260,1,2,3,4,5,7],[137,460,539,652,659,958,1013,1337,3005],[0]),u6 [23,79] [45,85,163,466,539,997,1001,1374,1376,1395,1408,2938,3159,3160],u6 [17,7] [5,137,220,333,355,375,497,520,668,1092,1093,1329,1330,1335,1336],e6 [231,429] [40,68,220,348,460,539,1552,1904,3038,3039],u6 [405] [45,85,89,149,163,184,239,539,1317,1318,1320,1780],u6 [390] [72,89,137,163,239,350,1013,1192,1193,1194],u6 [398] [45,53,85,89,149,163,239,465,1271,1272,1274],u6 [397] [5,40,53,89,137,149,163,239,1204,1259,1261],u6 [7] [53,89,137,239,539,958,1013,1252,1253],([101,110,0,2,3,4],[53,348,1013,1236,1238],[0]),u6 [154] [45,53,85,89,137,149,163,184,239,914,926,1381,2447],u6 [132,16] [5,20,40,45,53,72,89,137,226,361,364,370,396,423,1022,1357,1579,1580,2362,2706,3161],u6 [101,13] [5,45,220,239,465,539,1137,1141,1143,1184,1215,1216,1243,2787,2982,3162],u6 [237,79] [45,72,85,163,272,539,1001,3163],u6 [101,57] [5,21,53,85,89,220,348,465,773,774,1085,1204,1205,1215,1216,1220,1275,2115,2982,3164],u6 [101,83] [5,72,163,465,967,975,1013,1216],u6 [111] [14,89,137,163,239,656,1013,1176,1182],u6 [110,17] [53,137,226,239,375,496,519,520,1092,1093,1168,1176,1191,1330,3165,3166],u6 [193] [14,21,53,137,149,184,239,348,350,1184,3167]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_25_9_1 : checkNodesBT W_25 g_25 F_25 P_25_9 A_25 B_25_8 9 N_25_9_1 = true := by decide +kernel
def N_25_9 := N_25_9_0 ++ N_25_9_1
def B_25_9 : BT (List (List Nat)) := buildBucketsBT W_25 N_25_9
set_option maxRecDepth 500000 in
lemma B_25_9_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_25 9 xs.toFinset) B_25_9 := by
  have hP := buildPoolsSubBT_sound (pdepth := 12) (W := W_25) (raw := r_25) (pspecs := ps_25) (used := U_25_9) S_25_ok
  have hm0 := checkNodesBT_mem (by decide) gp_25 W_25_ok hP A_25_ok B_25_8_ok C_25_9_0
  have hm1 := checkNodesBT_mem (by decide) gp_25 W_25_ok hP A_25_ok B_25_8_ok C_25_9_1
  exact buildBucketsBT_of_mem (forall_append (hm0) hm1)
def U_25_10 : List Nat := ([53,68,72,89,137,149,163,164,184,239,242,333,348,350,361,420,460,465,519,539,595,620,650,652,773,782,837,871,925,926,958,971,996,1013,1092,1093,1116,1143,1176,1184,1188,1204,1275,1333,1370,1374,1377,1389,1408,1457,1458,1568,1580,1685,1741,1764,1774,1780,1841,1848,1864,1898,1924,1931,2027,2107,2225,2271,2362,2603,2691,2692,2706,2846,2874,2905,2938,2947,2951]++r 2973 5++[2982,2985,2989,2990,2991,2993,2996,3003,3005,3006,3042,3043,3079,3168])
def P_25_10 : BT (Option BoundPool) := buildPoolsSubBT 12 W_25 r_25 S_25 ps_25 U_25_10
def N_25_10 : List NodeSpec := [u6 [136] [53,72,184,239,348,350,595,1013],u6 [16] [53,72,137,239,348,361,958,1580,2990],u6 [213] [53,68,72,149,184,239,348,350,2973,2974,2975],u6 [92] [53,72,149,184,239,348,350,958,1013,1864,1898],u6 [412] [149,184,348,958,1013,2985,2989],u6 [231] [53,68,72,184,239,348,350,460,539,958,1848,1931,3003],u6 [24] [53,149,184,239,348,350,420,925,926,1013],u6 [6] [53,72,184,239,348,350,871,1013,1389],u6 [247] [53,72,149,184,239,348,350,958,1013,1685],u6 [130] [53,72,149,184,239,348,350,2027,2603],u6 [22] [53,89,149,184,239,348,1764,2977,2993],u6 [192] [53,72,184,239,348,350,1013,2225],u6 [229] [53,72,149,184,239,348,350,958,1013,1741],u6 [249] [53,72,89,149,184,239,348,350,620,958,1013,1774],u6 [135] [53,137,239,348,350,539,958,1457,1458,2996],u6 [83] [53,72,149,163,239,242,348,971,1013,3043],u6 [67] [53,72,89,149,164,184,239,348,350,1116,1333,3079],u6 [223] [53,72,149,184,239,348,350,958,1568,2107],u6 [28] [53,72,149,184,239,348,350,2846,2874],u6 [271] [53,72,149,184,239,348,350,958,1013,1370,1924],u6 [23] [53,137,239,348,958,1374,1377,1408,2991],u6 [30] [53,149,184,239,348,782,1013,2691,2692,2947],u6 [7] [53,137,184,239,333,348,539,652,958,1013,1780,3005],u6 [101] [53,72,149,184,239,348,350,465,1013,1204,2982],u6 [57] [53,72,89,149,184,239,348,350,460,773,1275,1841],u6 [110] [53,72,137,184,239,348,350,958,1013,1176,1188,2905,3168],u6 [13] [53,72,149,239,348,1143,1184,2976],u6 [17] [53,149,239,348,350,519,1092,1093],u6 [29] [53,89,239,837,1013,2951],u6 [132] [53,72,89,149,184,239,348,350,460,650,1013,2362,2706,3042],u6 [79] [53,72,149,163,239,348,350,996,2938],u6 [179] [53,72,184,239,348,350,1013,2271,3006]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_25_10 : checkNodesBT W_25 g_25 F_25 P_25_10 A_25 B_25_9 10 N_25_10 = true := by decide +kernel
def B_25_10 : BT (List (List Nat)) := buildBucketsBT W_25 N_25_10
set_option maxRecDepth 500000 in
lemma B_25_10_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_25 10 xs.toFinset) B_25_10 :=
  buildBucketsBT_sound (by decide) gp_25 W_25_ok (buildPoolsSubBT_sound S_25_ok) A_25_ok B_25_9_ok C_25_10
def U_25_11 : List Nat := [72,184,350,958]
def P_25_11 : BT (Option BoundPool) := buildPoolsSubBT 12 W_25 r_25 S_25 ps_25 U_25_11
def N_25_11 : List NodeSpec := [u6 [] [72,184,350,958]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_25_11 : checkNodesBT W_25 g_25 F_25 P_25_11 A_25 B_25_10 11 N_25_11 = true := by decide +kernel
def B_25_11 : BT (List (List Nat)) := buildBucketsBT W_25 N_25_11
set_option maxRecDepth 500000 in
lemma B_25_11_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_25 11 xs.toFinset) B_25_11 :=
  buildBucketsBT_sound (by decide) gp_25 W_25_ok (buildPoolsSubBT_sound S_25_ok) A_25_ok B_25_10_ok C_25_11
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_25_ok : forestRootCheck r_25 g_25 [(VAR 0,22,23),(VAR 1,12,14),(VAR 2,10,14),(VAR 3,6,14),(VAR 4,7,23),(VAR 5,3,35)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_25_in : bucketContainsBT B_25_11 r_25 = true := by decide +kernel
lemma low_25 : Lower r_25 g_25 12 := lower_of_forestBT root_25_ok B_25_11_ok root_25_in

def g_orig := (d 0xfeeaeaa8eee0e8a0)
set_option maxHeartbeats 0 in
lemma low_orig : Lower (varsOf 63) g_orig 12 := carry_of (swaps := [(0,5),(1,3),(2,4),(3,4)]) (by decide +kernel) low_25
def targetFn (x : Fin 6 → Bool) : Bool := Nat.testBit (4276808360 * 2 ^ 32 + 4007717024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def temoin : List Gate := [⟨.and,[0,1]⟩,⟨.or,[6,4]⟩,⟨.or,[3,7]⟩,⟨.and,[7,3]⟩,⟨.and,[8,5]⟩,⟨.and,[9,2]⟩,⟨.or,[9,2]⟩,⟨.and,[1,8]⟩,⟨.or,[0,13]⟩,⟨.or,[11,0]⟩,⟨.and,[12,14]⟩,⟨.and,[15,10]⟩,⟨.or,[17,16]⟩]
lemma temoin_ok : PEqualNP.MetaComplexity.Monotone2 ⟨temoin, 18⟩ := by
  intro g hg; simp [temoin] at hg; rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxHeartbeats 0 in
lemma tgt_eq_G : ∀ r : Row, targetFn (evalInput6 r) = g_orig.testBit r.val := by decide +kernel
set_option maxHeartbeats 0 in
lemma temoin_eval : ∀ r : Row, Circuit.eval ⟨temoin, 18⟩ (List.ofFn (evalInput6 r)) = g_orig.testBit r.val := by decide +kernel

end PEqualNP.Outside.L_meta_45476

open PEqualNP.Outside.L_meta_45476 in
theorem PEqualNP.Outside.L_meta_45476 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808360 * 2 ^ 32 + 4007717024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808360 * 2 ^ 32 + 4007717024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  exact replace_of_lower6 g_orig (by decide) (by decide) (by decide) 12 low_orig temoin 18 (by decide) temoin_ok targetFn tgt_eq_G temoin_eval
