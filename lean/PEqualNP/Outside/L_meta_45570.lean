import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_45570
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
def g_3 := (d 0xfec0fec0fec0fec0)
def r_3 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_3 : Lower r_3 g_3 5 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,8,9)]) (by decide +kernel) hc
def g_4 := (d 0xffe8ffe8ffe8ffe8)
def r_4 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_4 : Lower r_4 g_4 5 := by
  exact lift_of_f (z := 8) (o := 0) (other := r_0) (G := g_0) (essPairs := [(VAR 3,0,8)]) (by decide +kernel) low_0
def g_5 := (d 0xf880f880f880f880)
def r_5 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_5 : Lower r_5 g_5 5 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,6,7)]) (by decide +kernel) hc
def g_6 := (d 0xfffef880fffef880)
def r_6 : List Nat := varsOf 31
def p_6 : List Nat := [7,7,7,11,11,11,12,12,13,13,14,14,17,17,18,18,19,20,20,21,22,24,24,25,26]
def q_6 : List Nat := [6,5,3,10,9,3,8,4,9,5,10,6,16,1,16,2,3,16,4,5,6,16,8,9,10]
def F_6 : Nat := fullMask 25
set_option maxHeartbeats 0 in
lemma gp_6 : goodPairs g_6 p_6 q_6 := goodPairs_of (by decide +kernel)
def W_6 : BT Decor := buildWiresBT 7 (mkBase p_6 q_6 r_6) [(1,0,2),(3,3,5),(1,1,3),(3,2,7),(0,0,1),(1,2,3),(2,10,4),(1,2,4),(3,3,12),(1,10,4),(3,1,14),(3,0,14),(0,10,4),(3,17,14),(0,1,10),(1,1,10),(3,19,20),(0,0,14),(0,1,4),(1,1,4),(3,23,24),(2,0,3),(1,26,2),(1,3,4),(3,2,28),(1,9,2),(1,30,4),(3,3,31),(3,2,4),(3,33,28),(3,10,4),(1,35,3),(1,26,4),(0,0,4),(1,38,3),(1,2,39),(2,0,2),(1,41,3),(1,41,4),(3,3,43),(2,27,4),(1,27,4),(1,0,4),(3,3,47),(1,48,2),(0,5,7),(1,38,2),(3,3,51),(2,1,2),(3,53,28),(3,23,0),(3,9,12),(2,0,10),(3,0,10),(2,30,4),(1,9,3),(1,30,3),(1,9,4),(3,3,62),(3,2,47),(3,0,4),(3,65,10),(2,1,3),(1,67,2),(0,0,10),(1,0,10),(3,23,10),(3,1,47),(3,9,10),(3,10,47),(2,30,3),(2,0,4),(3,1,4),(1,77,3),(0,10,47),(1,77,2),(1,80,3),(2,80,3),(2,0,17),(1,58,1),(1,1,17),(2,1,10),(3,86,0),(1,35,2),(3,3,4),(0,0,12),(2,0,28),(1,1,2),(1,0,1),(3,1,10)]
lemma W_6_ok : btAll (fun x => faithful p_6 q_6 x ∧ x.1 < 2^256) W_6 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_6 : List (List (Nat × Nat)) := [[],[(2,3)],[(0,1)],[(0,1),(2,3)]]
def A_6 : BT (List (Nat × Nat)) := btOfList 2 al_6
set_option maxHeartbeats 0 in
lemma A_6_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_6 = g_6) A_6 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_6_0 : Slice r_6 g_6 (identDom 0 1) 7 := by
  have hc : Lower (varsOf 29) (d 0xfffafaa0fffafaa0) 7 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_ident (u := 0) (v := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_6_1 : Slice r_6 g_6 (subcubeFast 4 0) 6 := by
  have hc : Lower (varsOf 27) (d 0xffee8800ffee8800) 6 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_6_2 : Slice r_6 g_6 (subcubeFast 8 0) 6 := by
  have hc : Lower (varsOf 23) (d 0xfefe8080fefe8080) 6 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_6_3 : Slice r_6 g_6 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xfffcf000fffcf000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_6_4 : Slice r_6 g_6 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) (d 0xfffffcc0fffffcc0) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_6_5 : Slice r_6 g_6 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffaf000fffaf000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_6_6 : Slice r_6 g_6 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffffaa0fffffaa0) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_6_7 : Slice r_6 g_6 (subcubeFast 16 0) 5 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_5
set_option maxHeartbeats 0 in
lemma sl_6_8 : Slice r_6 g_6 (subcubeFast 3 0) 4 := by
  have hc : Lower (varsOf 28) (d 0xfff0f000fff0f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 3) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_6_9 : Slice r_6 g_6 (subcubeFast 16 1) 4 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_6_10 : Slice r_6 g_6 (subcubeFast 16 2) 4 := by
  have hc : Lower (varsOf 13) (d 0xfaa0faa0faa0faa0) 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 2) (by decide +kernel) hc
def S_6 : BT (Option (Nat × Nat)) := btOfList 4 [some (identDom 0 1,7),some (subcubeFast 4 0,6),some (subcubeFast 8 0,6),some (subcubeFast 1 0,5),some (subcubeFast 0 1,5),some (subcubeFast 2 0,5),some (subcubeFast 0 2,5),some (subcubeFast 16 0,5),some (subcubeFast 3 0,4),some (subcubeFast 16 1,4),some (subcubeFast 16 2,4)]
lemma S_6_ok : btAll (fun o => ∀ p, o = some p → Slice r_6 g_6 p.1 p.2) S_6 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_6_0) (forall_cons (fun _ h => by cases h; exact sl_6_1) (forall_cons (fun _ h => by cases h; exact sl_6_2) (forall_cons (fun _ h => by cases h; exact sl_6_3) (forall_cons (fun _ h => by cases h; exact sl_6_4) (forall_cons (fun _ h => by cases h; exact sl_6_5) (forall_cons (fun _ h => by cases h; exact sl_6_6) (forall_cons (fun _ h => by cases h; exact sl_6_7) (forall_cons (fun _ h => by cases h; exact sl_6_8) (forall_cons (fun _ h => by cases h; exact sl_6_9) (forall_cons (fun _ h => by cases h; exact sl_6_10) (fun _ h => (List.not_mem_nil h).elim))))))))))))
def ps_6 : BT (Option PoolSpec) := btOfList 7 [q 1 [16424,16425,57415],q 1 [40964,40965,81999],q 1 [16388,16389,98399],q 1 [],q 1 [49165,57344],q 2 [16393,57344],q 2 [],q 7 [],q 3 [],q 4 [],q 5 [],q 6 [],q 1 [16425,57351],q 1 [16425,57344],q 0 [],q 4 [12441],q 1 [16384,12441],q 1 [16426,16427],q 1 [16385,192527],q 2 [16384,8345],q 1 [16388,95],q 0 [12297,40963],q 0 [12297,40962],q 1 [40962,40963],q 8 [],q 9 [],q 10 [],q 2 [16388,16389,98399],q 0 [12294,8461],q 1 [40960,40961],q 1 [16388,41055],q 1 [16385,192519],q 0 [12297,40999],q 1 [16385,192555],q 1 [16386,16387],q 1 [16385,192552],q 1 [16384,12493],q 1 [16424,69634],q 0 [16421,16393],q 1 [40963,4329],q 4 [16397,16393],q 6 [16397,16393],q 2 [16393],q 1 [16424,69637],q 1 [40966,347],q 1 [16384,16385],q 1 [16424,16425],q 2 [8549],q 1 [49167],q 1 [16397],q 1 [16426],q 2 [16426],q 1 [16427],q 1 [16425],q 2 [16425],q 1 [16424],q 4 [16397],q 6 [16397],q 2 [16489],q 1 [12310],q 2 [8193],q 1 [12293],q 0 [8193],q 0 [12293],q 0 [12297],q 1 [16384],q 1 [4096],q 1 [16391],q 0 [16385,192519],q 2 [16385,192519],q 5 [8193],q 0 [12290],q 0 [16393],q 0 [8197],q 3 [8197],q 1 [4],q 0 [16421],q 1 [40961],q 1 [49165],q 1 [4097],q 0 [16385],q 2 [16385],q 0 [16384,12441],q 1 [16399],q 0 [12290,8297],q 1 [12290],q 2 [8297],q 2 [16388,95],q 0 [16384,8345],q 1 [16385],q 1 [16386],q 2 [16384,16385],q 1 [40962],q 2 [16386,16387],q 1 [40960],q 1 [40967],q 0 [16391],q 2 [16391],q 2 [16386],q 0 [16384],q 2 [16384],q 2 [4097],q 2 [4096]]
def B_6_2 : BT (List (List Nat)) := BT.empty
lemma B_6_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_6 2 xs.toFinset) B_6_2 := .empty
def U_6_3 : List Nat := []
def P_6_3 : BT (Option BoundPool) := buildPoolsSubBT 7 W_6 r_6 S_6 ps_6 U_6_3
def N_6_3 : List NodeSpec := [([6,8,9,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_6_3 : checkNodesBT W_6 g_6 F_6 P_6_3 A_6 B_6_2 3 N_6_3 = true := by decide +kernel
def B_6_3 : BT (List (List Nat)) := buildBucketsBT W_6 N_6_3
set_option maxRecDepth 500000 in
lemma B_6_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_6 3 xs.toFinset) B_6_3 :=
  buildBucketsBT_sound (by decide) gp_6 W_6_ok (buildPoolsSubBT_sound S_6_ok) A_6_ok B_6_2_ok C_6_3
def U_6_4 : List Nat := [0,1,2]
def P_6_4 : BT (Option BoundPool) := buildPoolsSubBT 7 W_6 r_6 S_6 ps_6 U_6_4
def N_6_4 : List NodeSpec := [([11,13,0,1,2],[],[]),([15,16,2,3,4],[],[]),([18,0,1,2,3],[0],[]),([21,0,2,3,4],[1],[]),([15,22,2,3,4],[],[]),([25,0,2,3,10],[2],[]),([13,0,1,27,4],[],[]),([6,8,0,1,4],[],[0]),([13,29,0,1,4],[],[]),([6,9,2,7,4],[],[0]),([13,22,1,2,4],[],[]),([32,0,1,2,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_6_4 : checkNodesBT W_6 g_6 F_6 P_6_4 A_6 B_6_3 4 N_6_4 = true := by decide +kernel
def B_6_4 : BT (List (List Nat)) := buildBucketsBT W_6 N_6_4
set_option maxRecDepth 500000 in
lemma B_6_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_6 4 xs.toFinset) B_6_4 :=
  buildBucketsBT_sound (by decide) gp_6 W_6_ok (buildPoolsSubBT_sound S_6_ok) A_6_ok B_6_3_ok C_6_4
def U_6_5 : List Nat := (r 2 45)
def P_6_5 : BT (Option BoundPool) := buildPoolsSubBT 7 W_6 r_6 S_6 ps_6 U_6_5
def N_6_5 : List NodeSpec := [([11,0,1,2,3,12],[3],[0]),([22,1,2,3,4,12],[4,5],[0]),([0,1,2,34,3,28],[6,7],[]),([13,0,1,2,4,28],[6],[0]),([13,0,1,2,12,28],[6,7],[]),([0,1,2,36,10,4],[3,7],[]),([0,1,2,3,37,28],[6,8],[]),e5 [14] (r 8 4),([13,0,1,2,10,4],[3],[0]),([15,0,2,3,10,4],[12],[]),([22,1,2,3,10,4],[13],[]),([11,0,1,2,3,14],[14],[0,1]),([6,9,1,2,3,4],[11],[0]),([0,1,2,39,40,4],[8,15,16],[]),([0,2,30,3,7,4],[6],[]),([0,1,2,42,10,4],[3,8],[]),e5 [44] [],([11,35,0,1,2,3],[17],[0]),e5 [45] [],e5 [46] [9],([26,13,0,1,2,4],[9],[0]),([0,1,2,42,4,28],[7],[1]),e5 [49] [18],e5 [50] [],([13,0,1,10,4,12],[3,6],[]),([6,0,1,2,7,4],[9,10],[0]),([0,1,2,39,10,4],[3,8,15],[]),([52,0,1,51,3,4],[19],[]),e5 [54] [3],([13,0,1,2,4,14],[14],[0,2]),([55,1,2,3,10,4],[20],[]),e5 [56] [],u5 [31] [6,14],([9,2,5,3,7,4],[9],[0,3]),([57,58,1,2,3,4],[21,22,23],[2]),e5 [59] [],([0,1,2,60,10,4],[3],[]),e5 [61] [],e5 [63] [],([26,64,1,2,3,4],[],[]),([25,0,2,3],([2]++r 24 4),[0]),e5 [66] [],([0,2,68,3,4,24],[28],[]),([69,1,2,3,70,4],[29],[2]),e5 [71] [3,30],([72,0,2,3,10,4],[31],[]),e5 [73] [14,32],([15,0,2,3,4,14],[10],[0]),e5 [74] [33],([22,1,2,3,4,14],[9,24],[0,1]),e5 [75] [],([76,65,1,2,3,10],[34],[2]),([0,1,2,60,4,28],[7,8,10],[]),([0,1,2,78,10,4],[3,11],[]),e5 [79] [9,35],e5 [81] [8,9,11],([0,1,2,17,10,28],[6],[]),e5 [82] [],e5 [40] [8,36],([83,1,2,3,10,4],[37],[]),([6,0,1,2,10,4],[3,9],[]),([0,1,2,3,62,12],[3,8,10,25,26,38],[]),([0,1,10,4,12,28],[3,7],[]),([0,84,2,3,10,4],[39],[]),([0,1,10,12,28],[3,6,7,40,41,42],[]),e5 [52] [19],([11,0,1,2,10,28],[6,7],[]),([0,2,3,10,85,4],[43],[]),([87,1,2,3,10,4],[44],[]),e5 [11] [],([38,1,2,3,10,47],[45],[2]),([0,1,2,3,17,14],[46],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_6_5 : checkNodesBT W_6 g_6 F_6 P_6_5 A_6 B_6_4 5 N_6_5 = true := by decide +kernel
def B_6_5 : BT (List (List Nat)) := buildBucketsBT W_6 N_6_5
set_option maxRecDepth 500000 in
lemma B_6_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_6 5 xs.toFinset) B_6_5 :=
  buildBucketsBT_sound (by decide) gp_6 W_6_ok (buildPoolsSubBT_sound S_6_ok) A_6_ok B_6_4_ok C_6_5
def U_6_6 : List Nat := ([3]++r 6 6++[16,18,19,20,24,25,26,31,34,42,45]++r 47 49)
def P_6_6 : BT (Option BoundPool) := buildPoolsSubBT 7 W_6 r_6 S_6 ps_6 U_6_6
def N_6_6 : List NodeSpec := [e5 [88] [25,26,47],a5 [13] ([3]++r 8 4++[42,48]) [0,2],a5 [12,28] [6,7,49] [0,1],([0,1,2,3,12,28],[25,26,42,49],[0,1]),e5 [90,12] [3,7,8,9,25],a5 [11,10] [3,6,7,50] [0,1],u5 [11] ([3,6]++r 8 4++[50,51]),a5 [35,10] [7,52] [0,1],a5 [14] (r 8 4++[53,54]) [0,1,2],a5 [17,10] [6,7,55] [0,1,2],u5 [91,28] [8,25],([0,1,2,10,4,28],[6,7,49,56,57],[0,1]),a5 [37] [3,8,10,11,25,58] [0,1],u5 [6] [6,7,9,10,11,25,59,60],a5 [5,7] ([9,11]++r 60 4) [0,3],a5 [38,10] [3,6,8,9,64,65] [0,1,2],a5 [9,10] ([3,6]++r 8 4++[64,66]) [0,1],a5 [80] [6,11,25,67] [0,1],([72,0,2,3,4],[9,11,25,31,68,69],[0]),([26,1,2,5,3,4],[3,6,8,9,25,70,71],[]),a5 [9,12] [3,7,8,10,25,26,72] [0,1],([9,0,2,92,3,4],[3,11,26,73,74,75],[1,2]),a5 [26,12] [3,6,8,25] [0,1,3],a5 [62] [3,6,8,10,25,26,76] [0,1],a5 [10,70] [8,9,77] [0,1],a5 [12,14] [25,26,42,78] [0,1,2],e5 [93,10] (r 8 4++[24,64,79]),([26,1,2,3,4,47],[7,8,9,71,80,81],[0,2]),([0,1,2,39,4],[7,8,16,24,82],[0,1]),([89,0,1,2,3,12],[3,7,25,26,42,83],[1]),a5 [27] [7,8,24,84,85,86] [0,1,2],a5 [30] [6,7,8,10,66] [0,1,2],([55,1,2,3,4],[7,8,10,20,87],[0]),a5 [51] [7,8,19,24,65,88] [0,1],u5 [13,12] [3,6,7,42,48],u5 [10,47] [8,9,64,89],u5 [76,10] [8,25,90],([38,1,2,3,47],[8,9,24,45,91],[0,2]),a5 [57,10] [8,9,64,92] [0,1,2],a5 [48] ([3,6]++r 8 4++[18,25,81]) [0,1],([76,65,1,2,3],[8,9,24,34,93],[0,2]),a5 [77,10] [3,6,10,11,67] [0,1,2],u5 [69,10] [8,9,94],a5 [10,14] [7,53] [0,1,2],a5 [94,10] [10,11,64,95] [2]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_6_6 : checkNodesBT W_6 g_6 F_6 P_6_6 A_6 B_6_5 6 N_6_6 = true := by decide +kernel
def B_6_6 : BT (List (List Nat)) := buildBucketsBT W_6 N_6_6
set_option maxRecDepth 500000 in
lemma B_6_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_6 6 xs.toFinset) B_6_6 :=
  buildBucketsBT_sound (by decide) gp_6 W_6_ok (buildPoolsSubBT_sound S_6_ok) A_6_ok B_6_5_ok C_6_6
def U_6_7 : List Nat := ([3]++r 6 6++[14,24,25,26,42,60]++r 64 4++[71,72,79,80,81,83,85,89,90]++r 96 7)
def P_6_7 : BT (Option BoundPool) := buildPoolsSubBT 7 W_6 r_6 S_6 ps_6 U_6_7
def N_6_7 : List NodeSpec := [u5 [89] ([3]++r 6 6++[25,26,83]),a5 [12] [3,8,10,25,26,42,72] [0,1,2,3],a5 [10] ([3]++r 6 6++[64]) [0,1,2],a5 [77] [3,6,9,10,11,14,25,67,96,97] [0,1,2],u5 [76] [8,10,14,24,25,90,98],a5 [38] ([3]++r 6 5++[14,24,65,99,100]) [0,1,2],u5 [26] [3,6,7,8,10,14,24,25,71,85],a5 [5] [3,8,9,11,14,24,25,60] [0,2],a5 [47] [7,8,9,14,24,25,26,80,81,89] [0,1],u5 [93] [9,11,14,24,25,79,101],a5 [9] [3,6,7,8,10,14,25,26,66,102] [0,1,2,3]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_6_7 : checkNodesBT W_6 g_6 F_6 P_6_7 A_6 B_6_6 7 N_6_7 = true := by decide +kernel
def B_6_7 : BT (List (List Nat)) := buildBucketsBT W_6 N_6_7
set_option maxRecDepth 500000 in
lemma B_6_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_6 7 xs.toFinset) B_6_7 :=
  buildBucketsBT_sound (by decide) gp_6 W_6_ok (buildPoolsSubBT_sound S_6_ok) A_6_ok B_6_6_ok C_6_7
def U_6_8 : List Nat := [3,6,14]
def P_6_8 : BT (Option BoundPool) := buildPoolsSubBT 7 W_6 r_6 S_6 ps_6 U_6_8
def N_6_8 : List NodeSpec := [a5 [] [3,6,14] [0,1,2,3]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_6_8 : checkNodesBT W_6 g_6 F_6 P_6_8 A_6 B_6_7 8 N_6_8 = true := by decide +kernel
def B_6_8 : BT (List (List Nat)) := buildBucketsBT W_6 N_6_8
set_option maxRecDepth 500000 in
lemma B_6_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_6 8 xs.toFinset) B_6_8 :=
  buildBucketsBT_sound (by decide) gp_6 W_6_ok (buildPoolsSubBT_sound S_6_ok) A_6_ok B_6_7_ok C_6_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_6_ok : forestRootCheck r_6 g_6 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11),(VAR 4,1,17)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_6_in : bucketContainsBT B_6_8 r_6 = true := by decide +kernel
lemma low_6 : Lower r_6 g_6 9 := lower_of_forestBT root_6_ok B_6_8_ok root_6_in
def g_7 := (d 0xe800e800e800e800)
def r_7 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_7 : Lower r_7 g_7 5 := by
  exact lift_of_f (z := 0) (o := 8) (other := r_0) (G := g_0) (essPairs := [(VAR 3,3,11)]) (by decide +kernel) low_0
def g_8 := (d 0xffe88000ffe88000)
def r_8 : List Nat := varsOf 31
def p_8 : List Nat := [15,15,15,15,19,19,19,21,21,21,22,22,22,23,24,24,25,25,26,26,27,28,28,29,30]
def q_8 : List Nat := [14,13,11,7,18,17,3,20,17,5,20,18,6,7,16,8,17,9,18,10,11,20,12,13,14]
def F_8 : Nat := fullMask 25
set_option maxHeartbeats 0 in
lemma gp_8 : goodPairs g_8 p_8 q_8 := goodPairs_of (by decide +kernel)
def W_8 : BT Decor := buildWiresBT 8 (mkBase p_8 q_8 r_8) [(0,0,1),(0,0,2),(0,1,2),(0,7,4),(1,8,3),(1,3,4),(0,0,10),(1,7,3),(0,12,4),(0,6,4),(3,14,0),(2,0,3),(3,16,2),(2,3,4),(3,18,7),(3,19,0),(0,3,4),(3,21,10),(1,5,21),(0,0,4),(1,7,24),(3,8,4),(2,1,3),(1,27,24),(1,5,3),(3,18,29),(0,5,4),(1,31,2),(1,31,3),(1,7,4),(3,8,34),(2,7,3),(3,36,0),(0,29,4),(2,0,13),(2,0,4),(0,5,2),(3,41,0),(3,42,4),(0,7,3),(3,44,12),(3,40,1),(0,2,3),(3,47,0),(3,5,2),(0,41,4),(3,50,0),(3,41,1),(3,3,4),(3,14,2),(2,5,3),(3,7,3),(1,14,1),(1,14,3),(3,14,4),(3,8,3),(1,8,0),(1,27,6),(3,18,2),(3,63,0),(0,2,10),(3,65,0),(0,5,10),(2,2,21),(3,68,0),(2,0,21),(3,70,1),(1,5,4),(0,3,72),(3,18,0),(0,2,72),(3,6,3),(3,41,4),(3,17,4),(3,16,4),(2,5,47),(3,56,0),(3,5,3),(2,2,3),(3,83,0),(0,84,4),(0,83,4),(3,86,0),(3,49,4),(1,41,3),(0,2,4),(2,5,90),(1,42,3),(0,1,4),(1,93,3),(0,0,94),(3,55,2),(3,12,4),(0,5,3),(0,0,3),(0,0,12),(3,26,0),(3,83,5),(2,5,21),(2,2,4),(3,104,0),(2,5,4),(3,31,4),(1,26,3),(3,16,1),(3,27,2),(3,104,5),(0,16,4),(3,106,0),(1,7,99),(3,27,4),(1,83,5),(1,104,5),(3,55,0),(1,16,21),(3,7,10),(1,18,5),(3,36,4),(3,18,5),(0,1,3),(3,124,2),(3,125,0),(3,110,0),(2,0,115),(3,3,72),(3,93,2),(3,130,0),(1,15,3),(0,42,4),(2,1,4),(3,134,2),(3,135,0),(1,24,3),(3,83,4)]
lemma W_8_ok : btAll (fun x => faithful p_8 q_8 x ∧ x.1 < 2^256) W_8 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_8 : List (List (Nat × Nat)) := [[],[(1,2)],[(0,1)],[(0,2),(1,2)],[(0,1),(1,2)],[(0,2)]]
def A_8 : BT (List (Nat × Nat)) := btOfList 3 al_8
set_option maxHeartbeats 0 in
lemma A_8_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_8 = g_8) A_8 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_8_0 : Slice r_8 g_8 (subcubeFast 0 1) 6 := by
  have hc : Lower (varsOf 30) (d 0xfffcc000fffcc000) 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_8_1 : Slice r_8 g_8 (subcubeFast 0 2) 6 := by
  have hc : Lower (varsOf 29) (d 0xfffaa000fffaa000) 6 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_8_2 : Slice r_8 g_8 (subcubeFast 0 4) 6 := by
  have hc : Lower (varsOf 27) (d 0xffee8800ffee8800) 6 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_8_3 : Slice r_8 g_8 (subcubeFast 8 0) 5 := by
  have hc : Lower (varsOf 23) (d 0xe8e80000e8e80000) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_8_4 : Slice r_8 g_8 (subcubeFast 0 16) 5 := by
  exact slice_fast_direct_f (z := 0) (o := 16) (by decide +kernel) low_4
set_option maxHeartbeats 0 in
lemma sl_8_5 : Slice r_8 g_8 (subcubeFast 8 16) 4 := by
  exact slice_fast_direct_f (z := 8) (o := 16) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_8_6 : Slice r_8 g_8 (identDom 0 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xeaea8080eaea8080) 5 := carry_of (swaps := [(0,2),(1,2),(3,4)]) (by decide +kernel) low_5
  exact slice_ident (u := 0) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_8_7 : Slice r_8 g_8 (identDom 1 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xecec8080ecec8080) 5 := carry_of (swaps := [(1,2),(3,4)]) (by decide +kernel) low_5
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_8_8 : Slice r_8 g_8 (identDom 2 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xf8f88080f8f88080) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_5
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
def S_8 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 0 1,6),some (subcubeFast 0 2,6),some (subcubeFast 0 4,6),some (subcubeFast 8 0,5),some (subcubeFast 0 16,5),some (subcubeFast 8 16,4),some (identDom 0 3,5),some (identDom 1 3,5),some (identDom 2 3,5)]
lemma S_8_ok : btAll (fun o => ∀ p, o = some p → Slice r_8 g_8 p.1 p.2) S_8 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_8_0) (forall_cons (fun _ h => by cases h; exact sl_8_1) (forall_cons (fun _ h => by cases h; exact sl_8_2) (forall_cons (fun _ h => by cases h; exact sl_8_3) (forall_cons (fun _ h => by cases h; exact sl_8_4) (forall_cons (fun _ h => by cases h; exact sl_8_5) (forall_cons (fun _ h => by cases h; exact sl_8_6) (forall_cons (fun _ h => by cases h; exact sl_8_7) (forall_cons (fun _ h => by cases h; exact sl_8_8) (fun _ h => (List.not_mem_nil h).elim))))))))))
def ps_8 : BT (Option PoolSpec) := btOfList 7 [q 0 [16396,16397,41047],q 1 [],q 1 [16412,16413,139299],q 1 [12316,12317,49331],q 2 [],q 0 [],q 0 [16397,40968],q 6 [],q 3 [40960],q 1 [16397,40960],q 5 [],q 1 [16396,16397,41047],q 2 [16396,16397,41047],q 0 [16396,86026],q 1 [16396,86018],q 0 [16405,294924],q 3 [],q 0 [16405,294920],q 0 [16396,86037],q 4 [12386],q 0 [16404,16405],q 1 [16412,12323],q 1 [16412,35],q 1 [12319,227],q 0 [12310,12311],q 4 [],q 0 [16398,16399],q 0 [16392,368662],q 0 [16388,12661],q 0 [12310,8415],q 0 [16404,12413],q 7 [],q 0 [12308,12309],q 0 [12298,20815],q 3 [16388],q 0 [16396,86038],q 4 [12290],q 0 [16406,16407],q 1 [8192],q 0 [12294,8303],q 1 [16404,12413],q 1 [16392,363],q 3 [40968],q 0 [12298,20813],q 1 [16384,98333],q 0 [16396,16397],q 0 [16397,40980],q 1 [16397,40991],q 0 [16405,294927],q 3 [16451],q 1 [8564,35],q 1 [16384,12413],q 0 [4192,12413],q 0 [16388,8567],q 0 [16398],q 0 [16396],q 2 [16396,86018],q 0 [16397],q 2 [16397,40960],q 4 [12385],q 2 [16384],q 1 [16384],q 0 [4192],q 0 [12385],q 1 [16384,12385],q 2 [16384,12385],q 8 [],q 0 [16399],q 0 [16388],q 1 [12290],q 0 [12294],q 0 [16448],q 2 [4096],q 0 [12310],q 1 [16396,16397],q 2 [16396,16397],q 0 [16404],q 0 [16392],q 2 [363],q 0 [12309],q 1 [12309],q 1 [12310],q 0 [12308],q 0 [8196],q 1 [31],q 0 [8212],q 2 [31],q 0 [16405],q 1 [12319],q 0 [16406],q 1 [16398,16399],q 2 [16398,16399],q 1 [16386],q 1 [8212],q 1 [16415],q 2 [16415],q 2 [16719],q 3 [16719],q 3 [16384],q 2 [335],q 0 [12298],q 1 [12298,335],q 0 [12296],q 2 [419],q 0 [16394],q 1 [16404],q 2 [191],q 1 [16399],q 2 [16399],q 1 [16398],q 2 [16398],q 2 [16386],q 2 [12290],q 1 [12288],q 2 [12288],q 1 [16397],q 2 [16397],q 1 [16396],q 2 [16396]]
def B_8_2 : BT (List (List Nat)) := BT.empty
lemma B_8_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_8 2 xs.toFinset) B_8_2 := .empty
def U_8_3 : List Nat := []
def P_8_3 : BT (Option BoundPool) := buildPoolsSubBT 7 W_8 r_8 S_8 ps_8 U_8_3
def N_8_3 : List NodeSpec := [([5,6,9,4],[],[]),([11,1,2,13],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_8_3 : checkNodesBT W_8 g_8 F_8 P_8_3 A_8 B_8_2 3 N_8_3 = true := by decide +kernel
def B_8_3 : BT (List (List Nat)) := buildBucketsBT W_8 N_8_3
set_option maxRecDepth 500000 in
lemma B_8_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_8 3 xs.toFinset) B_8_3 :=
  buildBucketsBT_sound (by decide) gp_8 W_8_ok (buildPoolsSubBT_sound S_8_ok) A_8_ok B_8_2_ok C_8_3
def U_8_4 : List Nat := (r 0 6)
def P_8_4 : BT (Option BoundPool) := buildPoolsSubBT 7 W_8 r_8 S_8 ps_8 U_8_4
def N_8_4 : List NodeSpec := [([15,1,17,3,4],[],[]),([20,1,2,3,4],[],[]),([22,5,0,1,2],[0],[]),([16,1,2,23,4],[],[]),([5,25,2,3,4],[1],[]),([26,5,6,3,4],[],[]),([5,28,2,3,4],[],[]),([0,1,2,30,4],[],[]),([11,1,2,12,4],[],[0]),([0,1,32,33,4],[],[]),([35,0,1,2,3],[2],[]),([16,5,2,12,4],[],[]),([37,1,2,21,4],[],[]),([0,1,2,38,10],[],[4]),([39,1,2,3,4],[],[]),([40,1,43,2,3],[],[]),([45,0,1,2,4],[3],[]),([42,46,2,3,4],[],[]),([48,49,1,3,4],[],[]),([51,1,2,3,4],[],[]),([42,52,2,3,4],[],[]),([53,37,1,2,4],[],[]),([15,54,1,3,4],[],[]),([5,6,3,12,4],[],[]),([55,6,7,3,4],[4],[]),([56,37,1,2,4],[],[]),([15,57,2,3,4],[],[]),([15,1,2,58,4],[],[]),([15,59,1,2,3],[],[]),([60,1,61,2,4],[],[]),([51,1,2,9,4],[],[]),([51,60,1,2,4],[],[]),([31,6,7,3,4],[4],[4]),([5,62,2,3,4],[5],[]),([5,0,2,9,4],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_8_4 : checkNodesBT W_8 g_8 F_8 P_8_4 A_8 B_8_3 4 N_8_4 = true := by decide +kernel
def B_8_4 : BT (List (List Nat)) := buildBucketsBT W_8 N_8_4
set_option maxRecDepth 500000 in
lemma B_8_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_8 4 xs.toFinset) B_8_4 :=
  buildBucketsBT_sound (by decide) gp_8 W_8_ok (buildPoolsSubBT_sound S_8_ok) A_8_ok B_8_3_ok C_8_4
def U_8_5 : List Nat := ([0,1]++r 4 50)
def P_8_5 : BT (Option BoundPool) := buildPoolsSubBT 7 W_8 r_8 S_8 ps_8 U_8_5
def N_8_5 : List NodeSpec := [e5 [64] [],([66,0,1,65,3,4],[6],[]),([67,11,1,2,3,4],[7,8,9],[]),([22,0,1,2],[0,10,11,12],[0,1,3]),e5 [69] [13],([70,71,1,2,3,4],[14],[]),e5 [66] [6],([5,0,1,2,73,4],[15],[]),([5,74,1,2,3,4],[1,16],[]),([5,0,1,75,3,4],[17],[]),([16,76,6,1,2,4],[],[]),e5 [77] [],a5 [23] [16,18] [0,2],e5 [78] [],([24,0,1,2,3,79],[7,19],[]),([31,0,1,2,3,72],[20],[4]),([60,0,7,1,2,4],[21],[]),([16,5,7,2,3,4],[],[0,1,2]),([16,0,1,2,12,4],[5],[0,1]),([51,7,1,2,3,4],[22],[]),([51,8,1,2,3,4],[5],[0]),e5 [80] [4,7],([81,7,1,2,3,4],[23],[]),([55,82,0,1,2,4],[24],[4]),e5 [85] [16],a5 [50] [7,16] [0,2,4],e5 [87] [],([84,24,1,2,3,4],[25],[5]),([55,6,1,2,3,4],[4],[0]),([31,0,1,2,33,4],[16],[0,1,3,4]),([40,42,1,2,3,4],[],[0,1]),([42,5,1,2,3,4],[5],[1]),([16,41,1,2,3,4],[16],[]),([18,53,5,0,1,2],[26],[0]),e5 [37] [],a5 [88] [] [4],e5 [89] [],e5 [91] [27],([53,84,0,1,2,4],[],[]),e5 [92] [7],e5 [95] [28],([16,5,1,2,21,4],[],[0]),([5,0,1,96,3,4],[7,29],[4]),([42,41,1,2,3,4],[5],[0,1]),([16,52,1,2,3,4],[],[]),([42,0,93,2,3,4],[],[]),([5,0,1,2,33,4],[30],[]),([41,24,1,2,3,4],[25],[]),([0,1,2,29,4,10],[7,31],[0,4]),e5 [97] [],([98,0,1,2,29,4],[32],[4]),a5 [38] [1,4,5,7] [0,4],a5 [31] [4,7,16] [4],([16,53,5,1,2,4],[10],[]),([51,1,2,3,4],[],[]),([5,0,2,3,12,4],[5],[0]),([31,6,1,2,3,4],[4],[0,4]),([99,0,1,2,12,4],[5],[]),([26,0,8,1,2,3],[5],[2,4]),e5 [26] [],([5,24,1,2,3,72],[],[]),([42,5,7,2,3,4],[1,5],[]),([15,6,1,90,3,4],[5],[]),e5 [100] [],([60,0,8,1,2,4],[31],[0]),([15,14,1,2,3,4],[5],[0]),([55,0,1,2,21,4],[],[0,4]),([18,0,1,2,29,4],[],[0]),e5 [101] [],e5 [102] [4,33],([16,5,1,2,29,4],[16],[]),([31,0,1,32,3,4],[],[0,1,3,4]),([5,0,2,3,94,4],[28,34],[]),e5 [103] [35],([42,99,1,2,3,4],[7],[3,5]),e5 [29] [],([16,5,93,2,3,4],[1,5,34,36],[2]),([5,105,1,2,3,4],[1],[4]),([106,107,0,1,2,3],[37],[4]),e5 [108] [1,4,5,7],([26,5,0,2,3,4],[5],[0]),([5,6,7,3,4],[1,4,5,38],[0,1,2,3,4]),([26,0,7,93,2,3],[25],[]),([5,6,93,2,3,4],[],[2,3]),([16,5,109,2,3,4],[1],[]),([5,0,110,2,3,4],[5,39],[]),a5 [111] [7,16] [4],([55,53,0,1,2,4],[25],[4]),([15,6,1,2,3,4],[5],[0]),([112,5,1,2,3,4],[1],[]),([0,1,2,33,4],[30,40],[4,5]),([48,5,1,2,3,4],[1,16],[0]),e5 [51] [],([16,27,5,2,3,4],[1,5,16],[]),([5,113,1,2,3,4],[5,25],[]),([15,0,7,1,3,4],[1,41],[]),([5,24,93,2,3,4],[1,5,25],[]),u5 [28] [],e5 [114] [],([5,0,1,65,3,4],[6,42],[4]),([48,6,1,2,3,4],[5,16],[]),([5,0,2,3,115,4],[5],[]),a5 [116] [1,5,16,43] [1,3],a5 [25] [4,25,44] [0,1],e5 [117] [],([70,5,1,2,3,4],[1],[]),([70,7,1,2,3,4],[14],[]),([5,118,1,2,3,4],[5,7],[]),([5,0,1,2,21,10],[45],[0]),e5 [67] [7,46],([16,0,1,2,119,4],[16],[]),e5 [120] [1,47],([37,1,2,3,4],[],[0]),([5,11,1,2,3,4],[1,7,8],[]),([84,0,1,2,21,4],[],[]),e5 [121] [],e5 [33] [],e5 [122] [],a5 [123] [4,16] [4],e5 [126] [],e5 [127] [39],e5 [128] [],([129,5,0,1,2,4],[48],[]),([16,53,0,1,2,79],[25,49],[]),([51,93,1,2,3,4],[50],[]),([16,15,1,2,3,4],[16],[0]),([15,24,1,2,3,4],[5],[0]),([24,0,1,2,33,4],[51,52],[3]),([26,0,93,1,2,3],[1,5],[4]),e5 [131] [53],e5 [132] [],e5 [133] [],e5 [136] [],([103,70,1,2,3,4],[14],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_8_5 : checkNodesBT W_8 g_8 F_8 P_8_5 A_8 B_8_4 5 N_8_5 = true := by decide +kernel
def B_8_5 : BT (List (List Nat)) := buildBucketsBT W_8 N_8_5
set_option maxRecDepth 500000 in
lemma B_8_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_8 5 xs.toFinset) B_8_5 :=
  buildBucketsBT_sound (by decide) gp_8 W_8_ok (buildPoolsSubBT_sound S_8_ok) A_8_ok B_8_4_ok C_8_5
def U_8_6 : List Nat := ([1,4,5]++r 7 4++[14,16,25,26,31,36,38,41,45,49]++r 54 53)
def P_8_6 : BT (Option BoundPool) := buildPoolsSubBT 7 W_8 r_8 S_8 ps_8 U_8_6
def N_8_6 : List NodeSpec := [a5 [74] [1,4,5,16,25,54] [0,1,3,5],a5 [70] [1,4,10,14,16,55,56] [0,1,3,5],a5 [11] [1,4,5,9,10,25,57,58] [0,1,3,5],u5 [112,24] [7,10,16],e5 [24,137] [7,10,59],a5 [31,24] [1,10,60,61,62] [0,1,3,4],a5 [137] ([7,10,31]++r 63 4) [2,4],([16,53,0,1,2,4],[5,10,16,25,67],[0,1,3,5]),a5 [16,93] [1,5,7,68,69] [0,1,2,3],u5 [16,27] [1,7,31,69,70],u5 [16,79] [5,7,10,16,25,49],([70,1,2,3,4],[10,14,16,56],[0,1]),a5 [112] [1,4,7,10,71] [0,1,3,5],a5 [55,5] [7,16,72,73] [0,2],([0,1,2,21,10],[16,25,45,74,75],[0,1,3]),a5 [31,5] [25,72,76] [0,1,3,4],u5 [15,90] [5,25,77,78],a5 [29] [4,7,25,66,79,80] [0,4,5],([11,1,2,3,4],[8,9,10,58],[0,1,3,5]),a5 [55] [4,7,25,73,81] [0,2,4],a5 [98,5] [7,16,82] [0,1,3],a5 [42,7] [1,4,5,83,84] [0,1],a5 [41,5] [4,72,85] [0,2,4],([5,6,1,2,3,4],[1,4,5,38,72],[0,1,2,4]),a5 [42] [7,16,25,83,84,86] [0,1,2,3,4],u5 [16,109] [1,5,7,16],a5 [5,72] [1,25,72,87] [0,2,4],a5 [56,7] [1,4,16,83,88] [0,2,3,4],a5 [106,5] [25,89] [0,2],([18,53,0,1,2],[10,16,26,90,91],[0,1,3]),a5 [5,90] [1,4,72,77] [0,1,3,4],a5 [40,7] [1,4,5,25,83,92] [0,3,5],a5 [15] [1,7,16,41,77,78] [0,3],a5 [41] [7,16,25,72,85,93] [0,2,4],a5 [24,93] [1,61,68] [0,1,3],([16,0,1,2,21,4],[10,16,25,36,55],[0,1,3,5]),a5 [26] [4,5,16,94,95] [0,1,3],a5 [5,21] [1,16,55,72] [0,2,4],([16,5,1,2,3,4],[1,5,16,36,69],[0,1,2]),a5 [138] [1,5,10,16,66,96,97] [0,1,2,3],([5,24,1,2,3,4],[1,5,25,61,98],[0,1,2,3,4,5]),a5 [84] [1,7,25,99,100,101] [0,3,5],a5 [5,47] [1,4,16,72,102] [0,2,4],a5 [5,29] [1,7,16,79] [0,2],a5 [16,7] [1,4,5,7,16,69,83] [0,1,2,3,4],a5 [5,10] [1,16,25,57,72] [0,2,4],a5 [105] [1,10,16,25,103,104] [0,3],a5 [53,5] [1,5,7,10,67] [0,2,4],a5 [31] [4,7,16,76,105] [0,1,2,3,4],a5 [18,5] [1,5,16,54] [0,2],a5 [26,7] [1,4,25,94] [0,1,3],a5 [48] [1,10,16,102,106] [0,3]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_8_6 : checkNodesBT W_8 g_8 F_8 P_8_6 A_8 B_8_5 6 N_8_6 = true := by decide +kernel
def B_8_6 : BT (List (List Nat)) := buildBucketsBT W_8 N_8_6
set_option maxRecDepth 500000 in
lemma B_8_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_8 6 xs.toFinset) B_8_6 :=
  buildBucketsBT_sound (by decide) gp_8 W_8_ok (buildPoolsSubBT_sound S_8_ok) A_8_ok B_8_5_ok C_8_6
def U_8_7 : List Nat := ([1,4,5,7,10,16,25,54,55,57,60,61,67,69,72,92]++r 107 12)
def P_8_7 : BT (Option BoundPool) := buildPoolsSubBT 7 W_8 r_8 S_8 ps_8 U_8_7
def N_8_7 : List NodeSpec := [a5 [53] [1,4,5,10,67,107,108] [0,1,2,3,4],a5 [18] [1,4,5,16,25,54,109,110] [0,1,2,3,4],a5 [40] [1,4,5,10,25,92,111] [0,3,5],a5 [24] [1,4,5,10,16,25,60,61] [0,1,2,3,4,5],a5 [16] [1,4,5,7,10,16,25,69,112] [0,1,3,5],a5 [99] [1,4,5,10,16,25,113,114] [3,5],a5 [10] [1,4,5,10,16,57,115,116] [0,1,2,3,4],a5 [21] [1,4,5,10,16,55,117,118] [0,1,2,3,4],a5 [5] [1,4,5,16,25,72] [0,2,4]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_8_7 : checkNodesBT W_8 g_8 F_8 P_8_7 A_8 B_8_6 7 N_8_7 = true := by decide +kernel
def B_8_7 : BT (List (List Nat)) := buildBucketsBT W_8 N_8_7
set_option maxRecDepth 500000 in
lemma B_8_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_8 7 xs.toFinset) B_8_7 :=
  buildBucketsBT_sound (by decide) gp_8 W_8_ok (buildPoolsSubBT_sound S_8_ok) A_8_ok B_8_6_ok C_8_7
def U_8_8 : List Nat := [1,4,5]
def P_8_8 : BT (Option BoundPool) := buildPoolsSubBT 7 W_8 r_8 S_8 ps_8 U_8_8
def N_8_8 : List NodeSpec := [a5 [] [1,4,5] [0,1,2,3,4]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_8_8 : checkNodesBT W_8 g_8 F_8 P_8_8 A_8 B_8_7 8 N_8_8 = true := by decide +kernel
def B_8_8 : BT (List (List Nat)) := buildBucketsBT W_8 N_8_8
set_option maxRecDepth 500000 in
lemma B_8_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_8 8 xs.toFinset) B_8_8 :=
  buildBucketsBT_sound (by decide) gp_8 W_8_ok (buildPoolsSubBT_sound S_8_ok) A_8_ok B_8_7_ok C_8_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_8_ok : forestRootCheck r_8 g_8 [(VAR 0,14,15),(VAR 1,13,15),(VAR 2,11,15),(VAR 3,7,15),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_8_in : bucketContainsBT B_8_8 r_8 = true := by decide +kernel
lemma low_8 : Lower r_8 g_8 9 := lower_of_forestBT root_8_ok B_8_8_ok root_8_in
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
  have hc : Lower (varsOf 29) (d 0xfaa00000faa00000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_2 : Slice r_12 g_12 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xfc00c000fc00c000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_3 : Slice r_12 g_12 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) (d 0xee880000ee880000) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_4 : Slice r_12 g_12 (subcubeFast 0 8) 5 := by
  have hc : Lower (varsOf 23) (d 0xfefec0c0fefec0c0) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_3
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
  have hc : Lower (varsOf 27) (d 0xee88cc00ee88cc00) 5 := carry_of (swaps := [(1,2),(2,4)]) (by decide +kernel) low_5
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
def g_13 := (d 0xffe8c000ffe8c000)
def r_13 : List Nat := varsOf 31
def p_13 : List Nat := [14,14,14,15,15,15,19,19,19,21,21,21,22,22,22,23,24,24,25,25,26,26,27,28,28,29]
def q_13 : List Nat := [12,10,6,13,11,7,18,17,3,20,17,5,20,18,6,7,16,8,17,9,18,10,11,20,12,13]
def F_13 : Nat := fullMask 26
set_option maxHeartbeats 0 in
lemma gp_13 : goodPairs g_13 p_13 q_13 := goodPairs_of (by decide +kernel)
def W_13 : BT Decor := buildWiresBT 5 (mkBase p_13 q_13 r_13) [(0,2,4),(3,5,1),(2,2,3),(3,7,1),(0,1,2),(0,1,4),(2,1,3),(0,9,4),(3,9,4),(1,9,3),(0,0,4),(2,0,3)]
lemma W_13_ok : btAll (fun x => faithful p_13 q_13 x ∧ x.1 < 2^256) W_13 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_13 : List (List (Nat × Nat)) := [[],[(1,2)]]
def A_13 : BT (List (Nat × Nat)) := btOfList 1 al_13
set_option maxHeartbeats 0 in
lemma A_13_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_13 = g_13) A_13 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_13_0 : Slice r_13 g_13 (subcubeFast 0 1) 6 := by
  have hc : Lower (varsOf 30) (d 0xfffcc000fffcc000) 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_1 : Slice r_13 g_13 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xffc0c000ffc0c000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_2 : Slice r_13 g_13 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffaf000fffaf000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_3 : Slice r_13 g_13 (subcubeFast 0 4) 5 := by
  have hc : Lower (varsOf 27) (d 0xffeecc00ffeecc00) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_4 : Slice r_13 g_13 (subcubeFast 8 0) 5 := by
  have hc : Lower (varsOf 23) (d 0xe8e80000e8e80000) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_5 : Slice r_13 g_13 (subcubeFast 0 16) 5 := by
  exact slice_fast_direct_f (z := 0) (o := 16) (by decide +kernel) low_4
set_option maxHeartbeats 0 in
lemma sl_13_6 : Slice r_13 g_13 (subcubeFast 8 16) 4 := by
  exact slice_fast_direct_f (z := 8) (o := 16) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_13_7 : Slice r_13 g_13 (subcubeFast 1 4) 4 := by
  have hc : Lower (varsOf 26) (d 0xffcccc00ffcccc00) 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_8 : Slice r_13 g_13 (identDom 2 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xf8f8c0c0f8f8c0c0) 5 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_10
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
def S_13 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 0 1,6),some (subcubeFast 1 0,5),some (subcubeFast 0 2,5),some (subcubeFast 0 4,5),some (subcubeFast 8 0,5),some (subcubeFast 0 16,5),some (subcubeFast 8 16,4),some (subcubeFast 1 4,4),some (identDom 2 3,5)]
lemma S_13_ok : btAll (fun o => ∀ p, o = some p → Slice r_13 g_13 p.1 p.2) S_13 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_13_0) (forall_cons (fun _ h => by cases h; exact sl_13_1) (forall_cons (fun _ h => by cases h; exact sl_13_2) (forall_cons (fun _ h => by cases h; exact sl_13_3) (forall_cons (fun _ h => by cases h; exact sl_13_4) (forall_cons (fun _ h => by cases h; exact sl_13_5) (forall_cons (fun _ h => by cases h; exact sl_13_6) (forall_cons (fun _ h => by cases h; exact sl_13_7) (forall_cons (fun _ h => by cases h; exact sl_13_8) (fun _ h => (List.not_mem_nil h).elim))))))))))
def ps_13 : BT (Option PoolSpec) := btOfList 4 [q 3 [],q 5 [],q 4 [],q 0 [],q 1 [],q 8 [],q 0 [16388],q 6 [],q 2 [],q 0 [12294],q 0 [8196],q 7 []]
def B_13_4 : BT (List (List Nat)) := BT.empty
lemma B_13_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_13 4 xs.toFinset) B_13_4 := .empty
def U_13_5 : List Nat := (r 0 6)
def P_13_5 : BT (Option BoundPool) := buildPoolsSubBT 4 W_13 r_13 S_13 ps_13 U_13_5
def N_13_5 : List NodeSpec := [e5 [6] [],e5 [8] [],([0,9,10,2,3,4],[0,1],[]),([11,0,9,2,3,4],[0,2],[]),e5 [12] (r 2 4),e5 [13] [3,4],e5 [14] [3,4]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_13_5 : checkNodesBT W_13 g_13 F_13 P_13_5 A_13 B_13_4 5 N_13_5 = true := by decide +kernel
def B_13_5 : BT (List (List Nat)) := buildBucketsBT W_13 N_13_5
set_option maxRecDepth 500000 in
lemma B_13_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_13 5 xs.toFinset) B_13_5 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok (buildPoolsSubBT_sound S_13_ok) A_13_ok B_13_4_ok C_13_5
def U_13_6 : List Nat := (r 0 12)
def P_13_6 : BT (Option BoundPool) := buildPoolsSubBT 4 W_13 r_13 S_13 ps_13 U_13_6
def N_13_6 : List NodeSpec := [a5 [10] [0,6,7,8] [0,1],a5 [11] [0,2,5,7,8,9] [0,1],a5 [9] [1,2,4,5,8,10,11] [0,1],([15,1,2,3,4],[4,7,11],[]),([16,1,2,3,4],[3,4,7,11],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_13_6 : checkNodesBT W_13 g_13 F_13 P_13_6 A_13 B_13_5 6 N_13_6 = true := by decide +kernel
def B_13_6 : BT (List (List Nat)) := buildBucketsBT W_13 N_13_6
set_option maxRecDepth 500000 in
lemma B_13_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_13 6 xs.toFinset) B_13_6 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok (buildPoolsSubBT_sound S_13_ok) A_13_ok B_13_5_ok C_13_6
def U_13_7 : List Nat := (r 0 4++[7,8])
def P_13_7 : BT (Option BoundPool) := buildPoolsSubBT 4 W_13 r_13 S_13 ps_13 U_13_7
def N_13_7 : List NodeSpec := [a5 [] (r 0 4++[7,8]) [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_13_7 : checkNodesBT W_13 g_13 F_13 P_13_7 A_13 B_13_6 7 N_13_7 = true := by decide +kernel
def B_13_7 : BT (List (List Nat)) := buildBucketsBT W_13 N_13_7
set_option maxRecDepth 500000 in
lemma B_13_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_13 7 xs.toFinset) B_13_7 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok (buildPoolsSubBT_sound S_13_ok) A_13_ok B_13_6_ok C_13_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_13_ok : forestRootCheck r_13 g_13 [(VAR 0,18,19),(VAR 1,12,14),(VAR 2,10,14),(VAR 3,6,14),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_13_in : bucketContainsBT B_13_7 r_13 = true := by decide +kernel
lemma low_13 : Lower r_13 g_13 8 := lower_of_forestBT root_13_ok B_13_7_ok root_13_in
def g_14 := (d 0xffc8e000ffc8e000)
def r_14 : List Nat := varsOf 31
def p_14 : List Nat := [13,13,13,14,14,14,15,15,19,19,19,22,22,22,23,23,24,24,25,25,26,26,27,28,28,29]
def q_14 : List Nat := [12,9,5,12,10,6,11,7,18,17,3,20,18,6,21,7,16,8,17,9,18,10,11,20,12,21]
def F_14 : Nat := fullMask 26
set_option maxHeartbeats 0 in
lemma gp_14 : goodPairs g_14 p_14 q_14 := goodPairs_of (by decide +kernel)
def W_14 : BT Decor := buildWiresBT 7 (mkBase p_14 q_14 r_14) [(0,3,4),(1,3,4),(3,5,6),(2,7,2),(0,7,1),(2,7,0),(0,2,4),(1,0,11),(0,2,3),(1,13,4),(0,0,6),(0,1,6),(1,1,5),(1,2,5),(3,0,6),(3,2,6),(0,7,0),(0,1,3),(0,22,4),(3,23,1),(1,0,5),(2,0,5),(0,2,6),(2,3,4),(0,1,4),(1,29,3),(0,11,3),(3,31,1),(2,2,4),(0,1,2),(0,34,4),(3,35,3),(3,34,4),(1,0,34),(2,1,3),(3,39,4),(2,2,40),(2,2,5),(1,0,22),(1,0,3),(0,44,4),(2,2,45),(3,5,4),(3,1,6),(3,47,1),(3,33,3),(3,13,4),(3,34,3),(0,34,3),(3,0,4),(3,54,3),(2,44,4),(1,54,3),(3,11,1),(3,11,3),(0,33,3),(3,13,1),(1,0,4),(0,62,3),(3,0,3)]
lemma W_14_ok : btAll (fun x => faithful p_14 q_14 x ∧ x.1 < 2^256) W_14 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_14 : List (List (Nat × Nat)) := [[],[(1,2),(3,4)]]
def A_14 : BT (List (Nat × Nat)) := btOfList 1 al_14
set_option maxHeartbeats 0 in
lemma A_14_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_14 = g_14) A_14 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_14_0 : Slice r_14 g_14 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffaf000fffaf000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_14_1 : Slice r_14 g_14 (subcubeFast 0 4) 5 := by
  have hc : Lower (varsOf 27) (d 0xffccee00ffccee00) 5 := carry_of (swaps := [(2,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_14_2 : Slice r_14 g_14 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xffc0c000ffc0c000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_14_3 : Slice r_14 g_14 (subcubeFast 1 4) 4 := by
  have hc : Lower (varsOf 26) (d 0xffcccc00ffcccc00) 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_14_4 : Slice r_14 g_14 (subcubeFast 1 2) 4 := by
  have hc : Lower (varsOf 28) (d 0xfff0f000fff0f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_14_5 : Slice r_14 g_14 (identDom 1 4) 6 := by
  have hc : Lower (varsOf 15) (d 0xecc8ecc8ecc8ecc8) 6 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_2
  exact slice_ident (u := 1) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_14_6 : Slice r_14 g_14 (identDom 2 3) 6 := by
  have hc : Lower (varsOf 23) (d 0xf8f8e0e0f8f8e0e0) 6 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_2
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_14_7 : Slice r_14 g_14 (identDom 0 4) 5 := by
  have hc : Lower (varsOf 15) (d 0xea88ea88ea88ea88) 5 := carry_of (swaps := [(0,3),(2,3)]) (by decide +kernel) low_10
  exact slice_ident (u := 0) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_14_8 : Slice r_14 g_14 (identDom 0 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xeaeaa0a0eaeaa0a0) 5 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4)]) (by decide +kernel) low_10
  exact slice_ident (u := 0) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_14_9 : Slice r_14 g_14 (identDom 0 1) 5 := by
  have hc : Lower (varsOf 29) (d 0xffaaa000ffaaa000) 5 := carry_of (swaps := [(0,1),(1,4),(2,4),(3,4)]) (by decide +kernel) low_10
  exact slice_ident (u := 0) (v := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_14_10 : Slice r_14 g_14 (subcubeFast 0 1) 4 := by
  have hc : Lower (varsOf 30) (d 0xffccf000ffccf000) 4 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_11
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
def S_14 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 0 2,5),some (subcubeFast 0 4,5),some (subcubeFast 1 0,5),some (subcubeFast 1 4,4),some (subcubeFast 1 2,4),some (identDom 1 4,6),some (identDom 2 3,6),some (identDom 0 4,5),some (identDom 0 3,5),some (identDom 0 1,5),some (subcubeFast 0 1,4)]
lemma S_14_ok : btAll (fun o => ∀ p, o = some p → Slice r_14 g_14 p.1 p.2) S_14 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_14_0) (forall_cons (fun _ h => by cases h; exact sl_14_1) (forall_cons (fun _ h => by cases h; exact sl_14_2) (forall_cons (fun _ h => by cases h; exact sl_14_3) (forall_cons (fun _ h => by cases h; exact sl_14_4) (forall_cons (fun _ h => by cases h; exact sl_14_5) (forall_cons (fun _ h => by cases h; exact sl_14_6) (forall_cons (fun _ h => by cases h; exact sl_14_7) (forall_cons (fun _ h => by cases h; exact sl_14_8) (forall_cons (fun _ h => by cases h; exact sl_14_9) (forall_cons (fun _ h => by cases h; exact sl_14_10) (fun _ h => (List.not_mem_nil h).elim))))))))))))
def ps_14 : BT (Option PoolSpec) := btOfList 5 [q 2 [],q 10 [],q 5 [],q 0 [],q 6 [],q 1 [],q 9 [],q 3 [],q 8 [],q 6 [16394,12423],q 0 [90113],q 5 [16396],q 0 [139265],q 1 [139265],q 7 [],q 4 [],q 5 [16398],q 6 [16396],q 6 [16394],q 0 [12289]]
def B_14_2 : BT (List (List Nat)) := BT.empty
lemma B_14_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_14 2 xs.toFinset) B_14_2 := .empty
def U_14_3 : List Nat := []
def P_14_3 : BT (Option BoundPool) := buildPoolsSubBT 5 W_14 r_14 S_14 ps_14 U_14_3
def N_14_3 : List NodeSpec := [([8,7,0,1],[],[]),([9,7,0,2],[],[]),([10,7,1,2],[],[]),([1,12,3,14],[],[]),([15,16,2,5],[],[]),([0,17,18,6],[],[]),([7,19,1,2],[],[]),([7,0,1,18],[],[]),([7,20,0,1],[],[]),([21,7,1,2],[],[]),([24,7,0,2],[],[]),([7,15,1,2],[],[]),([7,1,2,25],[],[]),([7,0,1,2],[],[]),([26,7,1,2],[],[]),([0,16,27,5],[],[]),([7,0,16,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_14_3 : checkNodesBT W_14 g_14 F_14 P_14_3 A_14 B_14_2 3 N_14_3 = true := by decide +kernel
def B_14_3 : BT (List (List Nat)) := buildBucketsBT W_14 N_14_3
set_option maxRecDepth 500000 in
lemma B_14_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_14 3 xs.toFinset) B_14_3 :=
  buildBucketsBT_sound (by decide) gp_14 W_14_ok (buildPoolsSubBT_sound S_14_ok) A_14_ok B_14_2_ok C_14_3
def U_14_4 : List Nat := []
def P_14_4 : BT (Option BoundPool) := buildPoolsSubBT 5 W_14 r_14 S_14 ps_14 U_14_4
def N_14_4 : List NodeSpec := [([28,0,16,2,3],[],[]),([28,7,0,1,2],[],[]),([20,0,16,3,4],[],[]),([0,16,27,3,4],[],[0]),([19,16,2,3,4],[],[]),([7,0,1,2,6],[],[0,1]),([7,0,1,2,5],[],[0,1]),([0,1,2,5,30],[],[]),([32,0,2,3,4],[],[]),([7,0,1,2,3],[],[]),([33,1,12,3,4],[],[]),([1,3,25,18,4],[],[]),([20,0,1,5,6],[],[0]),([15,16,2,3,4],[],[0]),([36,0,1,2,4],[],[]),([24,0,2,3,4],[],[]),([0,3,17,18,4],[],[0]),([33,37,0,1,3],[],[]),([29,38,2,3,4],[],[]),([0,22,2,30,4],[],[1]),([41,0,1,3,4],[],[]),([33,1,38,3,4],[],[]),([24,42,0,3,4],[],[]),([24,0,2,5,6],[],[0]),([29,43,2,3,4],[],[1]),([46,0,1,3,4],[],[]),([0,1,5,18,6],[],[0]),([24,2,3,25,4],[],[]),([20,19,1,3,4],[],[]),([28,47,0,1,2],[],[0]),([1,2,5,25,6],[],[0]),([26,24,2,3,4],[],[]),([26,1,2,5,6],[],[0]),([24,0,3,18,4],[],[]),([0,1,2,5,6],[],[0]),([15,1,2,5,6],[],[0,1]),([20,48,0,3,4],[],[]),([19,1,2,5,6],[],[0]),([0,16,2,5,6],[],[0]),([7,0,1,2],[],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_14_4 : checkNodesBT W_14 g_14 F_14 P_14_4 A_14 B_14_3 4 N_14_4 = true := by decide +kernel
def B_14_4 : BT (List (List Nat)) := buildBucketsBT W_14 N_14_4
set_option maxRecDepth 500000 in
lemma B_14_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_14 4 xs.toFinset) B_14_4 :=
  buildBucketsBT_sound (by decide) gp_14 W_14_ok (buildPoolsSubBT_sound S_14_ok) A_14_ok B_14_3_ok C_14_4
def U_14_5 : List Nat := (r 0 17)
def P_14_5 : BT (Option BoundPool) := buildPoolsSubBT 5 W_14 r_14 S_14 ps_14 U_14_5
def N_14_5 : List NodeSpec := [([28,47,0,1,2],[],[0,1]),u5 [6] (r 0 6),e5 [49] [0,6],([20,0,1,3,4,6],[4,7],[0]),([19,1,2,3,4,6],[0],[0,1]),([19,1,2,3,4],[],[]),u5 [28] [],([28,0,1,2,5,4],[3],[0]),([24,0,2,5,3,4],[3],[0]),([33,0,1,11,3,4],[3,5],[0]),a5 [50] [0,3,8,9] [1],([0,34,29,2,3,4],[2,5],[0]),e5 [51] [],([28,0,29,1,2,3],[3],[]),([1,43,2,3,4],[10],[0,1]),([28,47,0,1,2,3],[],[0]),([0,1,2,5,3,6],[11],[0]),([33,0,34,1,3,4],[3],[0]),([0,16,2,3,4,6],[3],[0]),a5 [52] [5] [1],([22,1,43,2,3,4],[0,10],[1]),u5 [30] [0,1,2,4,5],a5 [53] [0,2,8] [1],e5 [55] [],e5 [56] [],e5 [57] [1,4,5],([34,1,38,2,3,4],[0,12],[]),([1,38,2,3,4],[12,13],[0,1]),a5 [23] [0,5,14] [0,1],e5 [58] [],([15,1,2,3,4,6],[1,7,15],[0,1]),([24,0,2,3,4],[],[]),e5 [59] [],([0,22,29,2,3,4],[2],[0]),e5 [60] [],e5 [24] [],e5 [61] [],([28,0,1,2,3,6],[3,16],[0]),([26,1,2,5,3,4],[7,14,15],[0,1]),([0,29,1,2,5,3],[3],[0]),([1,2,3,25,4],[],[]),([1,2,5,3,25,4],[0],[0,1]),a5 [5] [0,3,5,14] [0,1],([0,1,2,5,6],[],[0,1]),a5 [63] [3,8,14] [1],([0,1,5,3,18,4],[7],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_14_5 : checkNodesBT W_14 g_14 F_14 P_14_5 A_14 B_14_4 5 N_14_5 = true := by decide +kernel
def B_14_5 : BT (List (List Nat)) := buildBucketsBT W_14 N_14_5
set_option maxRecDepth 500000 in
lemma B_14_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_14 5 xs.toFinset) B_14_5 :=
  buildBucketsBT_sound (by decide) gp_14 W_14_ok (buildPoolsSubBT_sound S_14_ok) A_14_ok B_14_4_ok C_14_5
def U_14_6 : List Nat := (r 0 6++[7,8,11]++r 15 5)
def P_14_6 : BT (Option BoundPool) := buildPoolsSubBT 5 W_14 r_14 S_14 ps_14 U_14_6
def N_14_6 : List NodeSpec := [a5 [28] (r 0 4++[5,16]) [0,1],a5 [6] (r 0 6) [0,1],a5 [5] [0,1,3,5,11,17] [0,1],u5 [33] [0,2,3,4,7,18],a5 [22] [0,2,5,15] [0,1],a5 [34] [0,2,3,4,7] [0,1],a5 [29] [0,2,5,15] [0,1],a5 [64] [0,1,3,5,7,8,15] [1],a5 [44] [0,1,7,8,15,19] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_14_6 : checkNodesBT W_14 g_14 F_14 P_14_6 A_14 B_14_5 6 N_14_6 = true := by decide +kernel
def B_14_6 : BT (List (List Nat)) := buildBucketsBT W_14 N_14_6
set_option maxRecDepth 500000 in
lemma B_14_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_14 6 xs.toFinset) B_14_6 :=
  buildBucketsBT_sound (by decide) gp_14 W_14_ok (buildPoolsSubBT_sound S_14_ok) A_14_ok B_14_5_ok C_14_6
def U_14_7 : List Nat := ([0]++r 2 4++[7,15])
def P_14_7 : BT (Option BoundPool) := buildPoolsSubBT 5 W_14 r_14 S_14 ps_14 U_14_7
def N_14_7 : List NodeSpec := [a5 [] ([0]++r 2 4++[7,15]) [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_14_7 : checkNodesBT W_14 g_14 F_14 P_14_7 A_14 B_14_6 7 N_14_7 = true := by decide +kernel
def B_14_7 : BT (List (List Nat)) := buildBucketsBT W_14 N_14_7
set_option maxRecDepth 500000 in
lemma B_14_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_14 7 xs.toFinset) B_14_7 :=
  buildBucketsBT_sound (by decide) gp_14 W_14_ok (buildPoolsSubBT_sound S_14_ok) A_14_ok B_14_6_ok C_14_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_14_ok : forestRootCheck r_14 g_14 [(VAR 0,12,13),(VAR 1,12,14),(VAR 2,9,13),(VAR 3,5,13),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_14_in : bucketContainsBT B_14_7 r_14 = true := by decide +kernel
lemma low_14 : Lower r_14 g_14 8 := lower_of_forestBT root_14_ok B_14_7_ok root_14_in
def g_15 := (d 0xffecf880ffecf880)
def r_15 : List Nat := varsOf 31
def p_15 : List Nat := [7,7,7,11,11,11,12,12,13,13,14,14,18,18,19,19,21,21,21,22,22,24,24,25,25,26,28]
def q_15 : List Nat := [6,5,3,10,9,3,8,4,9,5,10,6,16,2,17,3,20,17,5,20,6,16,8,17,9,10,20]
def F_15 : Nat := fullMask 27
set_option maxHeartbeats 0 in
lemma gp_15 : goodPairs g_15 p_15 q_15 := goodPairs_of (by decide +kernel)
def W_15 : BT Decor := buildWiresBT 7 (mkBase p_15 q_15 r_15) [(0,1,4),(0,2,3),(1,5,6),(1,2,3),(1,1,4),(0,8,9),(3,6,8),(3,5,9),(0,0,9),(1,13,6),(2,1,4),(3,1,4),(2,11,5),(1,5,3),(0,2,18),(1,2,18),(3,19,20),(2,0,6),(2,2,3),(3,2,3),(0,0,8),(3,13,8),(1,25,4),(0,1,27),(1,16,6),(1,25,5),(3,6,9),(2,0,19),(1,6,4),(0,0,20),(1,13,3),(3,2,35),(3,4,20),(0,1,33),(1,1,33),(2,1,33),(3,1,33),(0,3,4),(1,3,4),(3,42,43),(3,16,8),(3,13,3),(1,25,1),(1,24,16),(3,25,1),(1,24,5),(2,2,4),(2,1,3),(1,52,4),(0,1,2),(3,54,43),(1,54,3),(2,56,4),(1,51,52),(1,56,4),(1,54,4),(3,2,18),(2,3,4),(3,3,4),(2,1,43),(2,0,42),(1,16,3),(3,6,1),(1,2,42),(2,1,42),(1,51,3),(0,1,3),(1,1,3),(0,2,4),(1,73,3),(1,1,2),(0,0,75),(1,5,2),(3,1,3),(3,78,0),(3,6,4),(0,1,43),(2,2,1),(1,82,3),(3,2,4),(2,1,2)]
lemma W_15_ok : btAll (fun x => faithful p_15 q_15 x ∧ x.1 < 2^256) W_15 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_15 : List (List (Nat × Nat)) := [[],[(1,2),(3,4)]]
def A_15 : BT (List (Nat × Nat)) := btOfList 1 al_15
set_option maxHeartbeats 0 in
lemma A_15_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_15 = g_15) A_15 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_15_0 : Slice r_15 g_15 (subcubeFast 0 1) 7 := by
  have hc : Lower (varsOf 30) (d 0xfffcfcc0fffcfcc0) 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_15_1 : Slice r_15 g_15 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xffa0f000ffa0f000) 5 := carry_of (swaps := [(1,4),(2,4)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_15_2 : Slice r_15 g_15 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffffaa0fffffaa0) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_15_3 : Slice r_15 g_15 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) (d 0xffcc8800ffcc8800) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_15_4 : Slice r_15 g_15 (subcubeFast 0 4) 5 := by
  have hc : Lower (varsOf 27) (d 0xffeeff88ffeeff88) 5 := carry_of (swaps := [(2,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_15_5 : Slice r_15 g_15 (subcubeFast 8 0) 5 := by
  have hc : Lower (varsOf 23) (d 0xecec8080ecec8080) 5 := carry_of (swaps := [(1,2),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_15_6 : Slice r_15 g_15 (subcubeFast 16 0) 5 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_5
set_option maxHeartbeats 0 in
lemma sl_15_7 : Slice r_15 g_15 (subcubeFast 4 1) 4 := by
  have hc : Lower (varsOf 26) (d 0xffcccc00ffcccc00) 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_15_8 : Slice r_15 g_15 (subcubeFast 8 4) 4 := by
  have hc : Lower (varsOf 19) (d 0xeeee8888eeee8888) 4 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 8) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_15_9 : Slice r_15 g_15 (subcubeFast 16 2) 4 := by
  have hc : Lower (varsOf 13) (d 0xfaa0faa0faa0faa0) 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_15_10 : Slice r_15 g_15 (identDom 1 3) 6 := by
  have hc : Lower (varsOf 23) (d 0xececc8c8ececc8c8) 6 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_2
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_15_11 : Slice r_15 g_15 (identDom 2 4) 6 := by
  have hc : Lower (varsOf 15) (d 0xf8e0f8e0f8e0f8e0) 6 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_2
  exact slice_ident (u := 2) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_15_12 : Slice r_15 g_15 (identDom 0 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xeeeea8a8eeeea8a8) 5 := carry_of (swaps := [(0,3),(2,3),(3,4)]) (by decide +kernel) low_3
  exact slice_ident (u := 0) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_15_13 : Slice r_15 g_15 (identDom 1 2) 5 := by
  have hc : Lower (varsOf 27) (d 0xffcccc88ffcccc88) 5 := carry_of (swaps := [(1,3),(2,4)]) (by decide +kernel) low_3
  exact slice_ident (u := 1) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_15_14 : Slice r_15 g_15 (subcubeFast 1 0) 4 := by
  have hc : Lower (varsOf 30) (d 0xffccf000ffccf000) 4 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_11
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
def S_15 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 0 1,7),some (subcubeFast 2 0,5),some (subcubeFast 0 2,5),some (subcubeFast 4 0,5),some (subcubeFast 0 4,5),some (subcubeFast 8 0,5),some (subcubeFast 16 0,5),some (subcubeFast 4 1,4),some (subcubeFast 8 4,4),some (subcubeFast 16 2,4),some (identDom 1 3,6),some (identDom 2 4,6),some (identDom 0 3,5),some (identDom 1 2,5),some (subcubeFast 1 0,4)]
lemma S_15_ok : btAll (fun o => ∀ p, o = some p → Slice r_15 g_15 p.1 p.2) S_15 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_15_0) (forall_cons (fun _ h => by cases h; exact sl_15_1) (forall_cons (fun _ h => by cases h; exact sl_15_2) (forall_cons (fun _ h => by cases h; exact sl_15_3) (forall_cons (fun _ h => by cases h; exact sl_15_4) (forall_cons (fun _ h => by cases h; exact sl_15_5) (forall_cons (fun _ h => by cases h; exact sl_15_6) (forall_cons (fun _ h => by cases h; exact sl_15_7) (forall_cons (fun _ h => by cases h; exact sl_15_8) (forall_cons (fun _ h => by cases h; exact sl_15_9) (forall_cons (fun _ h => by cases h; exact sl_15_10) (forall_cons (fun _ h => by cases h; exact sl_15_11) (forall_cons (fun _ h => by cases h; exact sl_15_12) (forall_cons (fun _ h => by cases h; exact sl_15_13) (forall_cons (fun _ h => by cases h; exact sl_15_14) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))
def ps_15 : BT (Option PoolSpec) := btOfList 7 [q 9 [],q 8 [],q 0 [12296,12297,32795],q 0 [16396,16397,176299],q 2 [],q 0 [16390,16391],q 0 [16389],q 14 [],q 0 [12296,16409],q 4 [16409],q 3 [],q 5 [],q 1 [],q 0 [12296,12297],q 4 [],q 3 [32768],q 5 [32768],q 1 [36864],q 12 [],q 0 [],q 7 [],q 4 [24578],q 0 [16388,16389],q 6 [],q 0 [16398,16399],q 0 [16398,16633],q 0 [16396,16397],q 0 [16391,12353],q 0 [16394,12297],q 2 [16394],q 0 [12297],q 0 [12296,4123],q 0 [12297,16418],q 0 [12304,172041],q 4 [16397],q 0 [16396,172038],q 0 [16394,12493],q 0 [12292,12293],q 10 [],q 0 [16392,12581],q 0 [8196,8197],q 13 [],q 0 [8197],q 1 [307200],q 0 [8196,12505],q 0 [16388,8213],q 0 [16388,12309],q 0 [12295],q 0 [12296,16411],q 2 [16397],q 0 [12296],q 0 [16388],q 0 [4106,12617],q 0 [12299],q 0 [16390],q 0 [16398],q 0 [12292],q 0 [8196],q 0 [12293],q 0 [16395],q 11 [],q 0 [8198],q 0 [16396],q 0 [16394],q 0 [16397]]
def B_15_1 : BT (List (List Nat)) := BT.empty
lemma B_15_1_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_15 1 xs.toFinset) B_15_1 := .empty
def U_15_2 : List Nat := []
def P_15_2 : BT (Option BoundPool) := buildPoolsSubBT 7 W_15 r_15 S_15 ps_15 U_15_2
def N_15_2 : List NodeSpec := [([0,7,10],[],[]),([11,12,0],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_15_2 : checkNodesBT W_15 g_15 F_15 P_15_2 A_15 B_15_1 2 N_15_2 = true := by decide +kernel
def B_15_2 : BT (List (List Nat)) := buildBucketsBT W_15 N_15_2
set_option maxRecDepth 500000 in
lemma B_15_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_15 2 xs.toFinset) B_15_2 :=
  buildBucketsBT_sound (by decide) gp_15 W_15_ok (buildPoolsSubBT_sound S_15_ok) A_15_ok B_15_1_ok C_15_2
def U_15_3 : List Nat := []
def P_15_3 : BT (Option BoundPool) := buildPoolsSubBT 7 W_15 r_15 S_15 ps_15 U_15_3
def N_15_3 : List NodeSpec := [([1,14,8,4],[],[]),([0,5,6,10],[],[0]),([15,11,16,0],[],[0]),([11,0,5,9],[],[0]),([17,0,1,4],[],[]),([0,7,8,9],[],[0]),([11,13,1,4],[],[]),([21,0,1,4],[],[]),([22,12,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_15_3 : checkNodesBT W_15 g_15 F_15 P_15_3 A_15 B_15_2 3 N_15_3 = true := by decide +kernel
def B_15_3 : BT (List (List Nat)) := buildBucketsBT W_15 N_15_3
set_option maxRecDepth 500000 in
lemma B_15_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_15 3 xs.toFinset) B_15_3 :=
  buildBucketsBT_sound (by decide) gp_15 W_15_ok (buildPoolsSubBT_sound S_15_ok) A_15_ok B_15_2_ok C_15_3
def U_15_4 : List Nat := [0,1,2]
def P_15_4 : BT (Option BoundPool) := buildPoolsSubBT 7 W_15 r_15 S_15 ps_15 U_15_4
def N_15_4 : List NodeSpec := [([15,23,24,16,0],[],[0,1]),([15,16,25,2,3],[],[1]),([26,1,2,3,4],[],[]),([25,28,2,3,4],[],[]),([15,0,2,29,3],[0],[]),([15,16,0,6,8],[],[0,1]),([0,5,2,3,10],[],[0]),([1,30,2,3,4],[],[1]),([0,1,7,8,4],[],[0]),([22,1,2,18,4],[],[]),([22,5,2,3,9],[],[0]),([31,0,5,2,3],[],[1]),([15,22,16,2,3],[],[0]),([25,5,2,3,9],[],[1]),([0,5,6,8,9],[],[0,1]),([32,1,2,18,4],[],[]),([0,1,2,18,33],[],[]),([34,1,2,18,4],[],[]),([36,13,1,3,4],[],[]),([25,1,2,18,4],[],[]),([37,0,1,2,18],[],[]),([24,12,0,2,3],[],[1]),([11,0,5,1,4],[1,2],[0,1]),([0,38,2,3,39],[],[1]),([40,41,0,2,3],[],[1]),([11,0,1,4,9],[2],[0]),([15,11,0,1,4],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_15_4 : checkNodesBT W_15 g_15 F_15 P_15_4 A_15 B_15_3 4 N_15_4 = true := by decide +kernel
def B_15_4 : BT (List (List Nat)) := buildBucketsBT W_15 N_15_4
set_option maxRecDepth 500000 in
lemma B_15_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_15 4 xs.toFinset) B_15_4 :=
  buildBucketsBT_sound (by decide) gp_15 W_15_ok (buildPoolsSubBT_sound S_15_ok) A_15_ok B_15_3_ok C_15_4
def U_15_5 : List Nat := (r 0 23)
def P_15_5 : BT (Option BoundPool) := buildPoolsSubBT 7 W_15 r_15 S_15 ps_15 U_15_5
def N_15_5 : List NodeSpec := [([44,0,1,2],[0,1,3],[]),e5 [45] [],([15,37,0,1,2,3],[4],[]),([15,16,0,2,3,8],[5],[0,1]),([15,25,1,2,3,4],[],[0]),([46,13,1,2,3,4],[4,6,7],[]),([25,1,47,2,3,4],[7],[]),([22,16,1,2,3,4],[],[0]),e5 [48] [],([49,25,1,2,3,4],[7],[]),([0,38,1,2,3,33],(r 8 4),[0,1]),a5 [50] [12] [1],([40,0,1,2,3,33],[],[0]),([0,5,1,6,8,4],[10,13,14],[0,1]),([15,24,16,0,2,3],[],[0]),([51,25,1,3,4],[14,15,16],[]),([24,13,1,2,3,4],[4,17],[1]),([0,1,2,3,33,39],[8,9,10],[0,1]),([15,0,1,6,8,4],[],[0]),([25,1,2,3,4,27],[7],[0,1]),([15,22,1,2,3,4],[],[0]),([15,23,24,0,1,4],[],[0]),([0,1,2,3,53,43],[11,12],[]),e5 [55] [],e5 [57] [],e5 [58] [],([44,0,1,2,43],[0,1,3],[]),e5 [59] [4,12,18,19],([25,1,2,3,4,9],[7],[0,1]),([22,1,2,3,4,9],[7,20],[0]),([0,1,2,3,60,43],[10,11,12],[]),a5 [10] [7,19] [0,1],([22,5,1,2,3,4],[7,11,20,21],[0]),([25,5,1,2,3,4],[7,14,15,16],[0]),([61,0,1,2,18,4],[],[1]),([24,0,1,2,18,4],[10],[]),([0,5,1,2,3,33],([4]++r 8 4),[0,1]),([0,1,2,3,9,33],(r 8 5),[1]),([11,0,1,4],[1,2],[0,1]),([15,0,1,2,3,33],[4],[]),([0,5,2,3,8,9],[4,22],[0,1]),([24,0,5,2,3,9],[],[0,1]),a5 [7] [4,7,10,12,19] [0,1],([37,0,5,1,2,3],[4,14],[0]),u5 [31] [7,10,12,19],([15,16,0,6,2,3],[0,5,12],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_15_5 : checkNodesBT W_15 g_15 F_15 P_15_5 A_15 B_15_4 5 N_15_5 = true := by decide +kernel
def B_15_5 : BT (List (List Nat)) := buildBucketsBT W_15 N_15_5
set_option maxRecDepth 500000 in
lemma B_15_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_15 5 xs.toFinset) B_15_5 :=
  buildBucketsBT_sound (by decide) gp_15 W_15_ok (buildPoolsSubBT_sound S_15_ok) A_15_ok B_15_4_ok C_15_5
def U_15_6 : List Nat := ([0,1]++r 4 5++[10,11,12,14,15,16,20]++r 22 33)
def P_15_6 : BT (Option BoundPool) := buildPoolsSubBT 7 W_15 r_15 S_15 ps_15 U_15_6
def N_15_6 : List NodeSpec := [([62,63,0,1,2],[1,11,23,24],[0]),e5 [43] [0,1,25],u5 [64,43] [0,12],([0,1,2,42,43],[0,1,11,26],[0]),([65,1,2,3,4],[0,1],[]),e5 [66] [4,10,14,23,27],u5 [15,24] [0,12],([51,0,1,3,8,4],[10,11,14,23,28,29],[0]),([25,1,2,3,4],[1,7,14,15,16,30],[0,1]),u5 [51,52] [1,4,10,12,14],([67,0,2,3,4],[10,11,12,31],[]),([0,1,2,3,33],[8,10,11],[0,1]),u5 [37] [1,4,10,11,12,14,32],([0,1,3,68,4],[11,14,23,33],[]),a5 [15,23] [1,10,12] [0,1],a5 [51,43] [10,11,14,23,34] [1],([69,0,2,3,4],[11,12,23,35],[]),a5 [70] [1,4,10,12,36] [1],([0,71,2,72,4],[0,12,37,38],[]),a5 [54,43] [1,4,10,11,12,23] [0,1],e5 [74] [0,1,10,39],([22,1,2,3,4],[11,20],[0]),([0,54,75,3,4],[1,4,12,40,41],[]),a5 [24,16] [4,14] [0,1],([76,1,2,3,4],[0,1,4,42,43],[]),a5 [56] [1,10,12,23,44] [0,1],([0,1,77,3,4],[12,14,23,45],[]),a5 [18] [10,12,14,23,46] [0,1],([79,1,2,3,4],[0,1,4,47],[]),a5 [8,9] [4,6,14,30] [0,1],([80,0,1,2,3],[10,11,23,48],[]),e5 [81,43] [0,12,23,49],a5 [5,6] [4,10,11,12,14,23,50,51] [0,1],e5 [83] [0,1,4,10,23,52],([0,5,2,3,9],[4,12,22],[0,1]),a5 [5,8] [4,10,11,12,14,23,30,51] [0,1],a5 [24,9] [4,10,12,14,53] [0,1],a5 [24,5] [10,11,12,14,53] [0,1],u5 [15,6] [0,12,54],u5 [15,8] [0,12,14,54],([15,16,0,2,3],[4,5,12],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_15_6 : checkNodesBT W_15 g_15 F_15 P_15_6 A_15 B_15_5 6 N_15_6 = true := by decide +kernel
def B_15_6 : BT (List (List Nat)) := buildBucketsBT W_15 N_15_6
set_option maxRecDepth 500000 in
lemma B_15_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_15 6 xs.toFinset) B_15_6 :=
  buildBucketsBT_sound (by decide) gp_15 W_15_ok (buildPoolsSubBT_sound S_15_ok) A_15_ok B_15_5_ok C_15_6
def U_15_7 : List Nat := ([0,1,4,10,11,12,14,23,30,41,42,51]++r 53 12)
def P_15_7 : BT (Option BoundPool) := buildPoolsSubBT 7 W_15 r_15 S_15 ps_15 U_15_7
def N_15_7 : List NodeSpec := [u5 [62] [0,1,4,10,11,12,14,55],a5 [71] [1,4,10,11,12,14,23,56] [0,1],a5 [54] [0,1,4,10,11,12,23,57] [0,1],u5 [75] [0,1,4,10,42],u5 [72] [0,1,4,10,12,58],a5 [84] [1,4,10,12,14,23,59,60] [1],a5 [85] [1,4,12,23,41,61] [1],a5 [24] [4,10,11,12,14,23,53] [0,1],a5 [5] [4,10,11,12,14,23,51] [0,1],a5 [8] [1,4,11,12,14,23,30] [0,1],u5 [15] [0,10,12,14,54],a5 [42] [1,4,11,12,23,62] [0,1],u5 [51] [0,1,4,10,11,12,14,60,63],a5 [43] [0,1,10,12,64] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_15_7 : checkNodesBT W_15 g_15 F_15 P_15_7 A_15 B_15_6 7 N_15_7 = true := by decide +kernel
def B_15_7 : BT (List (List Nat)) := buildBucketsBT W_15 N_15_7
set_option maxRecDepth 500000 in
lemma B_15_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_15 7 xs.toFinset) B_15_7 :=
  buildBucketsBT_sound (by decide) gp_15 W_15_ok (buildPoolsSubBT_sound S_15_ok) A_15_ok B_15_6_ok C_15_7
def U_15_8 : List Nat := [19]
def P_15_8 : BT (Option BoundPool) := buildPoolsSubBT 7 W_15 r_15 S_15 ps_15 U_15_8
def N_15_8 : List NodeSpec := [a5 [] [19] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_15_8 : checkNodesBT W_15 g_15 F_15 P_15_8 A_15 B_15_7 8 N_15_8 = true := by decide +kernel
def B_15_8 : BT (List (List Nat)) := buildBucketsBT W_15 N_15_8
set_option maxRecDepth 500000 in
lemma B_15_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_15 8 xs.toFinset) B_15_8 :=
  buildBucketsBT_sound (by decide) gp_15 W_15_ok (buildPoolsSubBT_sound S_15_ok) A_15_ok B_15_7_ok C_15_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_15_ok : forestRootCheck r_15 g_15 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11),(VAR 4,2,18)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_15_in : bucketContainsBT B_15_8 r_15 = true := by decide +kernel
lemma low_15 : Lower r_15 g_15 9 := lower_of_forestBT root_15_ok B_15_8_ok root_15_in
def g_16 := (d 0xe880e880e880e880)
def r_16 : List Nat := varsOf 15
def p_16 : List Nat := [7,7,7,11,11,11,13,13,13,14,14,14]
def q_16 : List Nat := [6,5,3,10,9,3,12,9,5,12,10,6]
def F_16 : Nat := fullMask 12
set_option maxHeartbeats 0 in
lemma gp_16 : goodPairs g_16 p_16 q_16 := goodPairs_of (by decide +kernel)
def W_16 : BT Decor := buildWiresBT 4 (mkBase p_16 q_16 r_16) [(0,0,1),(0,0,2),(0,1,2),(0,6,3),(3,7,0),(0,2,3),(3,9,0),(0,4,2)]
lemma W_16_ok : btAll (fun x => faithful p_16 q_16 x ∧ x.1 < 2^256) W_16 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_16 : List (List (Nat × Nat)) := [[],[(2,3)],[(1,2)],[(1,2),(2,3)],[(0,1)],[(0,1),(2,3)],[(0,2),(1,2)],[(0,2),(1,2),(2,3)],[(0,2),(1,3)],[(0,1),(1,2),(2,3)],[(0,2),(1,3),(2,3)]]
def A_16 : BT (List (Nat × Nat)) := btOfList 4 al_16
set_option maxHeartbeats 0 in
lemma A_16_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_16 = g_16) A_16 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_16_0 : Slice r_16 g_16 (subcubeFast 0 1) 4 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_1 : Slice r_16 g_16 (subcubeFast 0 2) 4 := by
  have hc : Lower (varsOf 13) (d 0xfaa0faa0faa0faa0) 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_2 : Slice r_16 g_16 (subcubeFast 0 4) 4 := by
  have hc : Lower (varsOf 11) (d 0xee88ee88ee88ee88) 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_3 : Slice r_16 g_16 (subcubeFast 0 8) 4 := by
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) low_0
def S_16 : BT (Option (Nat × Nat)) := btOfList 2 [some (subcubeFast 0 1,4),some (subcubeFast 0 2,4),some (subcubeFast 0 4,4),some (subcubeFast 0 8,4)]
lemma S_16_ok : btAll (fun o => ∀ p, o = some p → Slice r_16 g_16 p.1 p.2) S_16 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_16_0) (forall_cons (fun _ h => by cases h; exact sl_16_1) (forall_cons (fun _ h => by cases h; exact sl_16_2) (forall_cons (fun _ h => by cases h; exact sl_16_3) (fun _ h => (List.not_mem_nil h).elim)))))
def ps_16 : BT (Option PoolSpec) := btOfList 2 [q 1 [],q 0 [],q 2 [],q 3 []]
def B_16_2 : BT (List (List Nat)) := BT.empty
lemma B_16_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 2 xs.toFinset) B_16_2 := .empty
def U_16_3 : List Nat := [0,1]
def P_16_3 : BT (Option BoundPool) := buildPoolsSubBT 2 W_16 r_16 S_16 ps_16 U_16_3
def N_16_3 : List NodeSpec := [([4,5,6,3],[0,1],[]),([8,1,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_16_3 : checkNodesBT W_16 g_16 F_16 P_16_3 A_16 B_16_2 3 N_16_3 = true := by decide +kernel
def B_16_3 : BT (List (List Nat)) := buildBucketsBT W_16 N_16_3
set_option maxRecDepth 500000 in
lemma B_16_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 3 xs.toFinset) B_16_3 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok (buildPoolsSubBT_sound S_16_ok) A_16_ok B_16_2_ok C_16_3
def U_16_4 : List Nat := [0,2,3]
def P_16_4 : BT (Option BoundPool) := buildPoolsSubBT 2 W_16 r_16 S_16 ps_16 U_16_4
def N_16_4 : List NodeSpec := [([4,5,1,2,3],[0,2],[0]),([10,0,1,2,3],[],[]),([11,0,1,2,3],[3],[9])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_16_4 : checkNodesBT W_16 g_16 F_16 P_16_4 A_16 B_16_3 4 N_16_4 = true := by decide +kernel
def B_16_4 : BT (List (List Nat)) := buildBucketsBT W_16 N_16_4
set_option maxRecDepth 500000 in
lemma B_16_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 4 xs.toFinset) B_16_4 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok (buildPoolsSubBT_sound S_16_ok) A_16_ok B_16_3_ok C_16_4
def U_16_5 : List Nat := (r 0 4)
def P_16_5 : BT (Option BoundPool) := buildPoolsSubBT 2 W_16 r_16 S_16 ps_16 U_16_5
def N_16_5 : List NodeSpec := [([4,0,1,2,3],(r 0 4),[0,1,4,5,8,10])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_16_5 : checkNodesBT W_16 g_16 F_16 P_16_5 A_16 B_16_4 5 N_16_5 = true := by decide +kernel
def B_16_5 : BT (List (List Nat)) := buildBucketsBT W_16 N_16_5
set_option maxRecDepth 500000 in
lemma B_16_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 5 xs.toFinset) B_16_5 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok (buildPoolsSubBT_sound S_16_ok) A_16_ok B_16_4_ok C_16_5
def U_16_6 : List Nat := (r 0 4)
def P_16_6 : BT (Option BoundPool) := buildPoolsSubBT 2 W_16 r_16 S_16 ps_16 U_16_6
def N_16_6 : List NodeSpec := [([0,1,2,3],(r 0 4),[0,2,3,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_16_6 : checkNodesBT W_16 g_16 F_16 P_16_6 A_16 B_16_5 6 N_16_6 = true := by decide +kernel
def B_16_6 : BT (List (List Nat)) := buildBucketsBT W_16 N_16_6
set_option maxRecDepth 500000 in
lemma B_16_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 6 xs.toFinset) B_16_6 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok (buildPoolsSubBT_sound S_16_ok) A_16_ok B_16_5_ok C_16_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_16_ok : forestRootCheck r_16 g_16 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_16_in : bucketContainsBT B_16_6 r_16 = true := by decide +kernel
lemma low_16 : Lower r_16 g_16 7 := lower_of_forestBT root_16_ok B_16_6_ok root_16_in
def g_17 := (d 0xfef8f800fef8f800)
def r_17 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_17 : Lower r_17 g_17 8 := by
  have hc : Lower (varsOf 27) (d 0xee888800ee888800) 7 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_16
  exact lift_of_f (z := 4) (o := 0) (essPairs := [(VAR 2,8,12)]) (by decide +kernel) hc
def g_18 := (d 0xfefce800fefce800)
def r_18 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_18 : Lower r_18 g_18 8 := by
  have hc : Lower (varsOf 23) (d 0xfefee8e8fefee8e8) 7 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_1
  exact lift_of_f (z := 0) (o := 8) (essPairs := [(VAR 3,3,11)]) (by decide +kernel) hc
def g_19 := (d 0xfefefc80fefefc80)
def r_19 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_19 : Lower r_19 g_19 7 := by
  have hc : Lower (varsOf 23) (d 0xfefe8080fefe8080) 6 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_2
  exact lift_of_f (z := 8) (o := 0) (essPairs := [(VAR 3,2,10)]) (by decide +kernel) hc
def g_20 := (d 0xfac08000fac08000)
def r_20 : List Nat := varsOf 31
def p_20 : List Nat := [15,15,15,15,22,22,22,23,23,23,25,25,25,27,27,27,28,28,28,29,29,30,30]
def q_20 : List Nat := [14,13,11,7,20,18,6,21,19,7,24,17,9,26,19,11,24,20,12,21,13,26,14]
def F_20 : Nat := fullMask 23
set_option maxHeartbeats 0 in
lemma gp_20 : goodPairs g_20 p_20 q_20 := goodPairs_of (by decide +kernel)
def W_20 : BT Decor := buildWiresBT 3 (mkBase p_20 q_20 r_20) []
lemma W_20_ok : btAll (fun x => faithful p_20 q_20 x ∧ x.1 < 2^256) W_20 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_20 : List (List (Nat × Nat)) := [[]]
def A_20 : BT (List (Nat × Nat)) := btOfList 1 al_20
set_option maxHeartbeats 0 in
lemma A_20_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_20 = g_20) A_20 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_20_0 : Slice r_20 g_20 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) (d 0xffc0c000ffc0c000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_20_1 : Slice r_20 g_20 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) (d 0xfaf0a000faf0a000) 5 := carry_of (swaps := [(1,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_20_2 : Slice r_20 g_20 (subcubeFast 0 4) 5 := by
  have hc : Lower (varsOf 27) (d 0xffcc8800ffcc8800) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_20_3 : Slice r_20 g_20 (subcubeFast 0 8) 5 := by
  have hc : Lower (varsOf 23) (d 0xfafa8080fafa8080) 5 := carry_of (swaps := [(0,1),(3,4)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
def S_20 : BT (Option (Nat × Nat)) := btOfList 2 [some (subcubeFast 0 1,5),some (subcubeFast 0 2,5),some (subcubeFast 0 4,5),some (subcubeFast 0 8,5)]
lemma S_20_ok : btAll (fun o => ∀ p, o = some p → Slice r_20 g_20 p.1 p.2) S_20 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_20_0) (forall_cons (fun _ h => by cases h; exact sl_20_1) (forall_cons (fun _ h => by cases h; exact sl_20_2) (forall_cons (fun _ h => by cases h; exact sl_20_3) (fun _ h => (List.not_mem_nil h).elim)))))
def ps_20 : BT (Option PoolSpec) := btOfList 2 [q 0 [],q 3 [],q 2 [],q 1 []]
def B_20_5 : BT (List (List Nat)) := BT.empty
lemma B_20_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_20 5 xs.toFinset) B_20_5 := .empty
def U_20_6 : List Nat := (r 0 4)
def P_20_6 : BT (Option BoundPool) := buildPoolsSubBT 2 W_20 r_20 S_20 ps_20 U_20_6
def N_20_6 : List NodeSpec := [e5 [] (r 0 4)]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_20_6 : checkNodesBT W_20 g_20 F_20 P_20_6 A_20 B_20_5 6 N_20_6 = true := by decide +kernel
def B_20_6 : BT (List (List Nat)) := buildBucketsBT W_20 N_20_6
set_option maxRecDepth 500000 in
lemma B_20_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_20 6 xs.toFinset) B_20_6 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok (buildPoolsSubBT_sound S_20_ok) A_20_ok B_20_5_ok C_20_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_20_ok : forestRootCheck r_20 g_20 [(VAR 0,14,15),(VAR 1,13,15),(VAR 2,11,15),(VAR 3,7,15),(VAR 4,6,22)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_20_in : bucketContainsBT B_20_6 r_20 = true := by decide +kernel
lemma low_20 : Lower r_20 g_20 7 := lower_of_forestBT root_20_ok B_20_6_ok root_20_in
def g_21 := (d 0xfff8e800fff8e800)
def r_21 : List Nat := varsOf 31
def p_21 : List Nat := [11,11,11,13,13,13,14,14,14,15,19,19,19,20,20,21,21,22,22,23,24,24,25,25,26,26,28]
def q_21 : List Nat := [10,9,3,12,9,5,12,10,6,7,18,17,3,16,4,17,5,18,6,7,16,8,17,9,18,10,12]
def F_21 : Nat := fullMask 27
set_option maxHeartbeats 0 in
lemma gp_21 : goodPairs g_21 p_21 q_21 := goodPairs_of (by decide +kernel)
def W_21 : BT Decor := buildWiresBT 3 (mkBase p_21 q_21 r_21) [(1,2,4)]
lemma W_21_ok : btAll (fun x => faithful p_21 q_21 x ∧ x.1 < 2^256) W_21 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_21 : List (List (Nat × Nat)) := [[]]
def A_21 : BT (List (Nat × Nat)) := btOfList 1 al_21
set_option maxHeartbeats 0 in
lemma A_21_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_21 = g_21) A_21 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_21_0 : Slice r_21 g_21 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) (d 0xfffcfc00fffcfc00) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_1 : Slice r_21 g_21 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xfff0a000fff0a000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_2 : Slice r_21 g_21 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffafa00fffafa00) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_3 : Slice r_21 g_21 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) (d 0xff888800ff888800) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_4 : Slice r_21 g_21 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xfff0c000fff0c000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_5 : Slice r_21 g_21 (subcubeFast 0 8) 5 := by
  have hc : Lower (varsOf 23) (d 0xffffe8e8ffffe8e8) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_6 : Slice r_21 g_21 (subcubeFast 16 0) 5 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_7
set_option maxHeartbeats 0 in
lemma sl_21_7 : Slice r_21 g_21 (subcubeFast 16 8) 4 := by
  exact slice_fast_direct_f (z := 16) (o := 8) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_21_8 : Slice r_21 g_21 (identDom 2 3) 6 := by
  have hc : Lower (varsOf 23) (d 0xf8f8e0e0f8f8e0e0) 6 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_2
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
def S_21 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 0 1,5),some (subcubeFast 2 0,5),some (subcubeFast 0 2,5),some (subcubeFast 4 0,5),some (subcubeFast 1 0,5),some (subcubeFast 0 8,5),some (subcubeFast 16 0,5),some (subcubeFast 16 8,4),some (identDom 2 3,6)]
lemma S_21_ok : btAll (fun o => ∀ p, o = some p → Slice r_21 g_21 p.1 p.2) S_21 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_21_0) (forall_cons (fun _ h => by cases h; exact sl_21_1) (forall_cons (fun _ h => by cases h; exact sl_21_2) (forall_cons (fun _ h => by cases h; exact sl_21_3) (forall_cons (fun _ h => by cases h; exact sl_21_4) (forall_cons (fun _ h => by cases h; exact sl_21_5) (forall_cons (fun _ h => by cases h; exact sl_21_6) (forall_cons (fun _ h => by cases h; exact sl_21_7) (forall_cons (fun _ h => by cases h; exact sl_21_8) (fun _ h => (List.not_mem_nil h).elim))))))))))
def ps_21 : BT (Option PoolSpec) := btOfList 4 [q 4 [],q 0 [],q 1 [],q 2 [],q 5 [16393],q 3 [],q 6 [],q 7 [],q 5 [],q 8 []]
def B_21_5 : BT (List (List Nat)) := BT.empty
lemma B_21_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_21 5 xs.toFinset) B_21_5 := .empty
def U_21_6 : List Nat := (r 0 8)
def P_21_6 : BT (Option BoundPool) := buildPoolsSubBT 4 W_21 r_21 S_21 ps_21 U_21_6
def N_21_6 : List NodeSpec := [e5 [5] (r 0 8)]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_21_6 : checkNodesBT W_21 g_21 F_21 P_21_6 A_21 B_21_5 6 N_21_6 = true := by decide +kernel
def B_21_6 : BT (List (List Nat)) := buildBucketsBT W_21 N_21_6
set_option maxRecDepth 500000 in
lemma B_21_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_21 6 xs.toFinset) B_21_6 :=
  buildBucketsBT_sound (by decide) gp_21 W_21_ok (buildPoolsSubBT_sound S_21_ok) A_21_ok B_21_5_ok C_21_6
def U_21_7 : List Nat := (r 0 4++r 5 5)
def P_21_7 : BT (Option BoundPool) := buildPoolsSubBT 4 W_21 r_21 S_21 ps_21 U_21_7
def N_21_7 : List NodeSpec := [u5 [] (r 0 4++r 5 5)]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_21_7 : checkNodesBT W_21 g_21 F_21 P_21_7 A_21 B_21_6 7 N_21_7 = true := by decide +kernel
def B_21_7 : BT (List (List Nat)) := buildBucketsBT W_21 N_21_7
set_option maxRecDepth 500000 in
lemma B_21_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_21 7 xs.toFinset) B_21_7 :=
  buildBucketsBT_sound (by decide) gp_21 W_21_ok (buildPoolsSubBT_sound S_21_ok) A_21_ok B_21_6_ok C_21_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_21_ok : forestRootCheck r_21 g_21 [(VAR 0,10,11),(VAR 1,9,11),(VAR 2,9,13),(VAR 3,3,11),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_21_in : bucketContainsBT B_21_7 r_21 = true := by decide +kernel
lemma low_21 : Lower r_21 g_21 8 := lower_of_forestBT root_21_ok B_21_7_ok root_21_in
def g_22 := (d 0xffffeee8fa80c000)
def r_22 : List Nat := varsOf 63
def p_22 : List Nat := [14,14,14,15,15,15,23,23,23,23,25,25,25,27,27,27,28,28,28,29,29,30,30,35,35,35,37,37,37,38,38,38,39,41,41,41,42,42,42,43,45,45,46,48,48,49,49,50,50,51,52,52,53,54,56,56,58,60]
def q_22 : List Nat := [12,10,6,13,11,7,22,21,19,7,24,17,9,26,19,11,24,20,12,21,13,26,22,34,33,3,36,33,5,36,34,6,7,40,33,9,40,34,10,11,44,13,44,32,16,33,17,34,18,19,36,20,21,22,40,24,26,44]
def F_22 : Nat := fullMask 58
set_option maxHeartbeats 0 in
lemma gp_22 : goodPairs g_22 p_22 q_22 := goodPairs_of (by decide +kernel)
def W_22 : BT Decor := buildWiresBT 10 (mkBase p_22 q_22 r_22) [(1,4,5),(0,0,6),(0,2,5),(1,8,3),(1,7,9),(0,1,10),(1,2,5),(0,0,9),(0,13,6),(3,14,10),(3,14,12),(3,14,1),(1,2,3),(1,7,18),(0,1,19),(1,7,3),(0,2,21),(0,7,2),(1,7,2),(3,23,24),(2,25,3),(1,25,3),(3,2,21),(0,1,2),(1,29,4),(2,7,9),(2,0,3),(2,32,8),(3,33,6),(3,22,19),(3,7,9),(0,2,6),(0,32,6),(1,38,2),(1,37,21),(3,28,6),(3,3,6),(2,0,2),(0,43,6),(1,44,3),(2,24,3),(3,37,24),(2,1,4),(3,8,12),(3,48,49),(1,29,3),(2,51,5),(0,0,51),(3,53,5),(2,0,4),(2,49,3),(2,13,4),(3,57,0),(1,48,3),(0,0,59),(3,60,12),(2,1,3),(1,62,4),(0,0,63),(3,64,12),(1,62,2),(3,7,66),(2,1,2),(1,68,7),(2,69,3),(0,55,5),(3,71,51),(0,7,1),(3,73,12),(3,62,49),(1,68,3),(3,29,21),(1,32,2),(0,66,6),(3,43,6),(1,80,3),(2,2,21),(3,48,12),(1,43,3),(2,0,29),(1,85,3),(0,86,6),(3,84,6),(0,1,18),(1,89,4),(3,7,18),(2,18,4),(2,92,5),(3,93,0),(0,78,6),(1,68,4),(0,0,96),(1,3,5),(3,97,98),(1,73,2),(3,0,6),(1,7,29),(2,102,3),(0,1,12),(1,104,4),(0,0,105),(2,43,5),(3,107,0),(3,32,49),(0,0,1),(3,110,6),(3,111,18),(0,18,6),(1,110,4),(0,1,24),(1,115,4),(0,46,6),(3,2,6),(3,55,18),(1,110,3),(0,120,6),(3,4,12),(1,55,104),(3,55,12),(0,49,0),(1,3,4),(0,1,5),(1,127,2),(3,7,128),(1,38,8),(1,110,2),(0,131,6),(3,55,49),(3,55,5),(2,51,134),(1,7,51),(3,127,21),(0,0,18),(3,7,51),(1,62,7),(1,48,5),(0,0,141),(3,142,18),(3,13,6),(2,0,104),(3,7,1),(3,7,98),(1,127,3),(1,7,148),(0,0,5),(0,32,5),(1,151,3),(1,29,152),(3,150,153),(1,127,4),(0,0,155),(3,156,98),(2,2,5),(1,158,7),(3,73,18),(1,73,3),(3,7,2),(3,162,18),(3,8,21),(3,2,5),(1,165,4),(0,0,166),(0,1,9),(3,168,12),(0,150,51),(1,170,4),(2,1,9),(3,172,12),(3,73,98),(0,9,12),(1,49,4),(3,3,176),(1,111,3),(3,49,0),(3,179,1),(3,56,0),(1,37,3),(3,68,6),(1,183,3),(0,0,98),(2,49,4),(0,108,105),(1,162,3),(0,1,21),(1,189,4),(1,2,4),(1,191,5),(0,1,192),(1,126,5),(0,1,194),(3,101,194),(3,3,192),(3,2,194),(0,2,194),(0,1,6),(2,2,6),(1,201,7),(3,7,192),(0,18,5),(1,204,4),(3,62,6),(3,3,5),(1,207,4),(3,43,208),(2,2,4),(1,210,185),(3,4,98),(0,0,194),(3,62,0),(3,32,166),(0,24,6),(1,185,29),(2,2,3),(0,2,152),(1,150,2),(3,210,0),(3,7,12),(0,51,6),(1,51,5),(3,4,224),(2,51,4),(3,226,5),(0,51,5),(0,55,18),(2,0,5),(1,210,3),(3,230,231),(2,191,5),(3,3,96),(3,230,51),(1,221,5),(2,220,3),(1,150,4),(0,0,191),(1,239,5),(3,48,0),(3,210,12),(1,241,5),(3,32,6),(1,48,150),(1,120,5),(3,4,246),(0,18,155),(1,150,29),(2,249,3),(1,218,150),(0,96,98),(2,148,4),(3,253,0),(3,150,231),(1,218,5),(2,43,3),(3,257,6),(2,55,104),(2,32,4),(3,260,0),(1,261,29),(3,92,0),(0,1,98),(3,55,98),(0,0,2),(3,266,6),(0,49,1),(1,138,5),(1,266,3),(0,270,6),(0,126,5),(1,43,272),(3,165,6),(3,1,12),(3,29,208),(3,32,155),(2,55,5),(0,2,98),(1,185,2),(2,1,5),(2,1,6),(1,282,7),(0,7,18),(1,281,3),(2,285,4),(0,226,5),(1,30,5),(3,3,288),(3,4,5),(3,107,1),(3,230,2),(3,226,0),(1,62,150),(3,278,18),(1,55,3),(0,296,12),(0,120,12),(2,0,264),(1,282,101),(1,18,5),(3,279,301),(3,29,152),(1,261,127),(1,110,5),(0,18,305),(2,9,4),(1,261,5),(2,18,5),(3,55,51),(2,0,37),(1,311,3),(3,110,12),(3,214,6),(3,260,12),(3,18,6),(1,29,272),(3,110,5),(1,318,4),(1,32,4),(3,52,0),(3,29,5),(1,322,4),(3,8,6),(3,29,6),(3,68,5),(1,326,4),(0,0,224),(3,185,301),(3,3,191),(1,218,7),(1,92,5),(3,272,194),(0,32,166),(0,2,126),(1,18,4),(3,335,336),(3,2,98),(2,2,98),(3,339,0),(0,114,12),(0,63,12),(1,264,4),(0,0,343),(3,151,32),(1,345,3),(1,270,5),(3,4,347),(0,55,51),(3,185,12),(1,55,5),(1,230,134),(1,167,3),(1,29,134),(0,0,301),(1,185,4),(2,0,83),(0,241,12),(0,59,12),(3,1,194),(3,0,194),(0,0,148),(1,89,5),(3,218,155),(1,281,4),(2,0,89),(2,126,5),(0,0,90),(3,68,0),(3,89,6),(2,231,5),(0,0,231),(2,1,113),(3,158,336),(1,290,3),(3,37,192),(0,55,12),(2,0,113),(1,23,3),(3,3,166),(3,380,0),(3,55,9),(0,191,5),(1,3,383),(0,0,384),(0,21,5),(0,231,5),(2,0,387),(3,371,0),(3,150,18),(1,13,4),(1,13,5),(1,9,4),(0,0,393),(3,2,393),(0,1,113),(3,55,148),(3,49,1),(1,49,3),(1,71,29),(3,230,18),(1,213,2),(1,261,8),(0,230,2),(1,230,2),(3,404,405),(3,272,98),(3,3,12),(3,3,155),(3,165,0),(3,165,1),(1,53,4),(3,7,194),(1,228,4),(3,43,98),(2,185,2),(0,1,301),(3,4,301),(0,0,208),(0,2,208),(2,0,228),(2,0,420),(3,32,5),(1,29,423),(2,1,21),(0,0,375),(1,290,2),(0,1,427),(1,210,5),(3,201,0),(0,0,192),(1,68,5),(3,4,432),(2,96,5),(3,218,0),(1,435,5),(3,395,0),(1,32,5),(3,4,438),(3,118,0),(1,266,5),(1,230,48),(0,55,98),(3,29,98),(1,29,5),(1,165,3),(1,446,4),(0,0,445),(3,281,32),(3,122,0),(1,51,4),(1,395,5),(0,32,191),(1,85,5),(1,85,4),(1,326,3),(1,230,8),(3,230,191),(0,230,18),(3,290,0),(1,460,3),(3,266,5),(1,462,3),(2,230,48),(2,230,210),(2,131,4),(2,230,29),(1,230,4),(3,3,468),(2,1,152),(2,346,4),(1,369,4),(1,230,165),(0,59,5),(0,230,1),(3,475,0),(1,369,5),(3,150,126),(1,43,5),(1,55,2),(3,3,429),(3,150,12),(1,210,150),(1,158,290),(1,281,150),(2,32,29),(2,152,4),(1,152,4),(3,3,479),(2,220,4),(1,207,2),(2,66,5),(2,480,5),(2,405,4),(3,3,441),(1,158,3),(3,165,98),(2,0,127),(3,210,5),(2,0,499),(1,410,3),(1,59,5),(3,3,445),(1,158,110),(1,3,134),(1,71,3),(1,278,3),(1,281,2),(0,0,508),(1,221,3),(1,345,4),(3,126,5),(3,512,0),(1,257,5),(1,8,4),(1,84,4),(3,4,305),(2,270,4),(0,0,515),(1,266,4),(3,266,98),(2,0,272),(1,281,266),(1,158,4),(3,3,30),(3,150,191),(1,122,3),(3,29,126),(3,4,441),(0,1,441),(0,0,432),(1,270,4),(3,367,0),(1,43,4),(3,158,18),(1,218,4),(2,491,4),(3,207,12),(3,260,5),(1,207,110),(3,158,0),(3,3,238),(3,322,0),(1,292,3),(3,281,191),(1,260,5),(1,165,110),(3,110,126),(3,110,18),(0,230,126),(1,230,29),(0,126,12),(1,290,29),(1,3,499),(2,114,5),(2,32,165),(1,230,127),(2,30,5),(1,62,5),(0,0,559),(1,158,150),(3,4,559),(3,230,126),(1,423,4),(3,266,126),(3,281,126),(2,131,5),(1,120,4),(1,520,5),(3,151,0),(3,4,445),(1,541,3),(3,158,32),(1,207,266),(3,43,5),(1,575,4),(2,120,5),(0,0,30),(3,48,32),(2,2,126),(1,290,266),(1,346,4),(3,290,32),(1,476,4),(1,114,5),(1,48,266),(1,110,8),(2,1,126),(3,588,0),(3,3,520),(2,0,8),(1,591,4),(1,257,4),(3,158,126),(3,3,524),(1,534,5),(2,534,5),(3,3,351),(2,43,4),(1,599,5),(2,270,5),(0,32,12),(3,212,0),(3,3,432),(1,210,110),(1,318,3),(1,84,5),(1,207,29),(1,48,43),(1,43,127),(2,78,5),(2,128,4),(1,290,110),(3,126,12),(1,338,4),(1,575,3),(1,290,43),(0,32,2),(1,618,5),(2,1,98),(3,620,0),(2,2,152),(2,320,5),(1,2,272),(3,257,5),(3,3,305),(0,32,1),(2,2,272),(1,207,43),(3,210,32),(3,618,5),(3,3,534),(2,120,4),(3,43,126),(2,520,5),(1,462,4),(3,2,208),(3,127,126),(0,191,98),(3,4,479),(1,214,5),(2,66,4),(3,62,5),(2,0,643),(2,78,4),(1,643,4),(3,3,515),(3,150,1),(3,110,98),(2,0,335),(3,191,5),(3,651,0),(1,281,210),(1,241,3),(1,48,2),(0,0,655),(2,655,5),(3,42,0),(2,59,5),(3,3,141),(3,48,5),(2,0,661),(1,231,5),(1,151,4),(2,32,127),(1,3,661),(3,48,18),(1,48,8),(1,158,48),(0,0,429),(3,627,5),(2,63,5),(3,48,98),(1,48,207),(1,498,3),(1,498,4),(0,0,128),(0,0,336),(1,148,4),(1,108,4),(2,296,5),(0,2,155),(1,233,3),(3,2,155),(1,309,4),(3,127,191),(1,210,127),(3,127,6),(3,3,114),(1,476,3),(2,508,4),(0,0,285),(1,285,4),(0,0,365),(3,3,365),(3,281,18),(3,207,6),(3,282,0),(1,138,4),(2,336,5),(3,8,126),(2,0,204),(1,322,3),(3,338,0),(3,309,0),(0,230,191),(3,18,5),(3,707,0),(1,707,4),(1,281,290),(3,290,18),(1,435,4),(3,218,5),(1,713,4),(0,0,536),(2,536,5),(0,0,256),(2,0,713),(1,239,3),(3,127,18),(3,158,191),(1,108,3),(2,330,5),(1,627,5),(3,110,191),(3,207,191),(2,0,383),(3,233,0),(1,214,4),(2,0,279),(3,210,98),(1,210,207),(1,591,3),(3,4,256),(0,1,152),(3,290,12),(1,541,4),(3,150,2),(0,0,496),(1,496,4),(2,496,4),(0,0,524),(3,261,2),(1,281,43),(1,410,4),(1,369,3),(3,165,126),(1,261,2),(0,43,5),(1,749,4),(0,0,66),(1,266,127),(3,580,0),(0,0,491),(3,185,2),(2,0,326),(1,230,210),(1,48,165),(3,290,98),(0,0,427),(1,570,4),(1,107,4),(3,290,1),(3,207,1),(0,1,126),(3,43,1),(3,290,2),(0,1,191),(3,207,2),(3,230,1)]
lemma W_22_ok : btAll (fun x => faithful p_22 q_22 x ∧ x.1 < 2^256) W_22 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_22 : List (List (Nat × Nat)) := [[]]
def A_22 : BT (List (Nat × Nat)) := btOfList 1 al_22
set_option maxHeartbeats 0 in
lemma A_22_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_22 = g_22) A_22 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_22_0 : Slice r_22 g_22 (subcubeFast 0 2) 9 := by
  have hc : Lower (varsOf 61) (d 0xfffffffafaa0f000) 9 := carry_of (swaps := [(1,5),(4,5)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_1 : Slice r_22 g_22 (subcubeFast 0 1) 9 := by
  have hc : Lower (varsOf 62) (d 0xfffffffcffc0c000) 9 := carry_of (swaps := [(0,5),(1,5),(2,5),(3,5),(4,5)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_2 : Slice r_22 g_22 (subcubeFast 8 0) 9 := by
  have hc : Lower (varsOf 55) (d 0xffffe8e880800000) 9 := carry_of (swaps := [(3,5),(4,5)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_3 : Slice r_22 g_22 (subcubeFast 16 0) 9 := by
  have hc : Lower (varsOf 47) (d 0xeee8eee8c000c000) 9 := carry_of (swaps := [(1,3),(2,3),(4,5)]) (by decide +kernel) low_12
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_4 : Slice r_22 g_22 (subcubeFast 4 0) 8 := by
  have hc : Lower (varsOf 59) (d 0xffffee88aa000000) 8 := carry_of (swaps := [(0,1),(2,5),(3,5),(4,5)]) (by decide +kernel) low_13
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_5 : Slice r_22 g_22 (subcubeFast 2 0) 8 := by
  have hc : Lower (varsOf 61) (d 0xffffaaa0fa000000) 8 := carry_of (swaps := [(0,1),(1,5),(2,5),(3,5),(4,5)]) (by decide +kernel) low_14
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_6 : Slice r_22 g_22 (identDom 1 2) 9 := by
  have hc : Lower (varsOf 59) (d 0xffffeeccee88cc00) 9 := carry_of (swaps := [(1,4),(2,5),(3,4),(4,5)]) (by decide +kernel) low_15
  exact slice_ident (u := 1) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_7 : Slice r_22 g_22 (identDom 0 1) 8 := by
  have hc : Lower (varsOf 61) (d 0xffffaaaafaa0a000) 8 := carry_of (swaps := [(0,3),(1,5),(2,3),(3,5)]) (by decide +kernel) low_17
  exact slice_ident (u := 0) (v := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_8 : Slice r_22 g_22 (identDom 0 4) 8 := by
  have hc : Lower (varsOf 47) (d 0xeeeaeeeaea80ea80) 8 := carry_of (swaps := [(0,4),(1,3),(2,4),(4,5)]) (by decide +kernel) low_18
  exact slice_ident (u := 0) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_9 : Slice r_22 g_22 (subcubeFast 0 4) 7 := by
  have hc : Lower (varsOf 59) (d 0xffffeeeeff88cc00) 7 := carry_of (swaps := [(2,5),(4,5)]) (by decide +kernel) low_19
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_10 : Slice r_22 g_22 (subcubeFast 32 0) 7 := by
  have hc : Lower (varsOf 31) (d 0xfa80c000fa80c000) 7 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_20
  exact slice_fast_direct_f (z := 32) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_11 : Slice r_22 g_22 (identDom 0 2) 8 := by
  have hc : Lower (varsOf 59) (d 0xffffeeaaaa888800) 8 := carry_of (swaps := [(0,3),(1,3),(2,5),(4,5)]) (by decide +kernel) low_21
  exact slice_ident (u := 0) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_12 : Slice r_22 g_22 (subcubeFast 8 4) 6 := by
  have hc : Lower (varsOf 51) (d 0xffffeeee88880000) 6 := carry_of (swaps := [(2,4),(3,5)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 8) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_13 : Slice r_22 g_22 (subcubeFast 8 2) 6 := by
  have hc : Lower (varsOf 53) (d 0xfffffafaa0a00000) 6 := carry_of (swaps := [(1,4),(2,4),(3,5)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 8) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_14 : Slice r_22 g_22 (subcubeFast 4 2) 6 := by
  have hc : Lower (varsOf 57) (d 0xffffffaaaa000000) 6 := carry_of (swaps := [(1,4),(2,5),(3,4),(4,5)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 4) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_15 : Slice r_22 g_22 (subcubeFast 16 1) 6 := by
  have hc : Lower (varsOf 46) (d 0xfffcfffcc000c000) 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4),(4,5)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 16) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_16 : Slice r_22 g_22 (subcubeFast 8 1) 6 := by
  have hc : Lower (varsOf 54) (d 0xfffffcfcc0c00000) 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,5)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 8) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_17 : Slice r_22 g_22 (subcubeFast 6 1) 4 := by
  have hc : Lower (varsOf 56) (d 0xffffff00ff000000) 4 := carry_of (swaps := [(0,3),(1,4),(2,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 6) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_18 : Slice r_22 g_22 (subcubeFast 17 2) 4 := by
  have hc : Lower (varsOf 44) (d 0xfff0fff0f000f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 17) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_19 : Slice r_22 g_22 (subcubeFast 32 3) 4 := by
  have hc : Lower (varsOf 28) (d 0xfff0f000fff0f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 32) (o := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_20 : Slice r_22 g_22 (subcubeFast 32 5) 4 := by
  have hc : Lower (varsOf 26) (d 0xffcccc00ffcccc00) 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 32) (o := 5) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_21 : Slice r_22 g_22 (subcubeFast 6 8) 4 := by
  have hc : Lower (varsOf 49) (d 0xffffaaaaaaaa0000) 4 := carry_of (swaps := [(1,3),(2,4),(3,5),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 6) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_22 : Slice r_22 g_22 (subcubeFast 32 18) 4 := by
  have hc : Lower (varsOf 13) (d 0xfaa0faa0faa0faa0) 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 32) (o := 18) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_23 : Slice r_22 g_22 (subcubeFast 20 32) 4 := by
  have hc : Lower (varsOf 11) (d 0xee88ee88ee88ee88) 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 20) (o := 32) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_24 : Slice r_22 g_22 (subcubeFast 24 32) 4 := by
  exact slice_fast_direct_f (z := 24) (o := 32) (by decide +kernel) low_0
def S_22 : BT (Option (Nat × Nat)) := btOfList 5 [some (subcubeFast 0 2,9),some (subcubeFast 0 1,9),some (subcubeFast 8 0,9),some (subcubeFast 16 0,9),some (subcubeFast 4 0,8),some (subcubeFast 2 0,8),some (identDom 1 2,9),some (identDom 0 1,8),some (identDom 0 4,8),some (subcubeFast 0 4,7),some (subcubeFast 32 0,7),some (identDom 0 2,8),some (subcubeFast 8 4,6),some (subcubeFast 8 2,6),some (subcubeFast 4 2,6),some (subcubeFast 16 1,6),some (subcubeFast 8 1,6),some (subcubeFast 6 1,4),some (subcubeFast 17 2,4),some (subcubeFast 32 3,4),some (subcubeFast 32 5,4),some (subcubeFast 6 8,4),some (subcubeFast 32 18,4),some (subcubeFast 20 32,4),some (subcubeFast 24 32,4)]
lemma S_22_ok : btAll (fun o => ∀ p, o = some p → Slice r_22 g_22 p.1 p.2) S_22 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_22_0) (forall_cons (fun _ h => by cases h; exact sl_22_1) (forall_cons (fun _ h => by cases h; exact sl_22_2) (forall_cons (fun _ h => by cases h; exact sl_22_3) (forall_cons (fun _ h => by cases h; exact sl_22_4) (forall_cons (fun _ h => by cases h; exact sl_22_5) (forall_cons (fun _ h => by cases h; exact sl_22_6) (forall_cons (fun _ h => by cases h; exact sl_22_7) (forall_cons (fun _ h => by cases h; exact sl_22_8) (forall_cons (fun _ h => by cases h; exact sl_22_9) (forall_cons (fun _ h => by cases h; exact sl_22_10) (forall_cons (fun _ h => by cases h; exact sl_22_11) (forall_cons (fun _ h => by cases h; exact sl_22_12) (forall_cons (fun _ h => by cases h; exact sl_22_13) (forall_cons (fun _ h => by cases h; exact sl_22_14) (forall_cons (fun _ h => by cases h; exact sl_22_15) (forall_cons (fun _ h => by cases h; exact sl_22_16) (forall_cons (fun _ h => by cases h; exact sl_22_17) (forall_cons (fun _ h => by cases h; exact sl_22_18) (forall_cons (fun _ h => by cases h; exact sl_22_19) (forall_cons (fun _ h => by cases h; exact sl_22_20) (forall_cons (fun _ h => by cases h; exact sl_22_21) (forall_cons (fun _ h => by cases h; exact sl_22_22) (forall_cons (fun _ h => by cases h; exact sl_22_23) (forall_cons (fun _ h => by cases h; exact sl_22_24) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))))))))
set_option maxRecDepth 500000 in
def ps_22 : BT (Option PoolSpec) := btOfList 12 [q 2 [20497,24576,86024,86025,77828],q 2 [20497,24576,8220,8221,98399],q 8 [20488,12321,20489],q 3 [20488,12321,20489,24576],q 0 [20488,12321,20489],q 2 [20488,20489],q 16 [20488,20489],q 0 [20488,12321,20489,20497,24576],q 2 [20497,24576,86024,86025,77915],q 5 [20497,24576],q 0 [20497,24576],q 2 [20497,24576,24584,86165],q 9 [20497,24576],q 4 [20497,24576],q 5 [20488,20489,49187],q 17 [],q 2 [20488,20489,49187],q 21 [],q 0 [20488,20489,49187,200899],q 3 [20488,20489,49187],q 3 [20488,20489,49187,200899],q 8 [20488,20489,49187],q 15 [20488,20489,49187],q 2 [16386,20488,20489,49187],q 1 [20488,20489,49187,12486],q 1 [20488,12321,20489,20497],q 0 [20488,12321],q 8 [20488,12321],q 1 [20488,12321],q 3 [24576],q 20 [],q 13 [20488,20489,49187],q 1 [20488,20489,49187],q 22 [],q 16 [],q 2 [20497,24576,86026,86027],q 0 [20488,20489,49347,49187],q 12 [16390],q 8 [],q 2 [73732,16741,20497,24576],q 2 [20497,24576],q 5 [20497,24579],q 3 [20489,49152,49156,430080],q 9 [],q 2 [20497,24576,86025,77828],q 16 [20488,20489,49187],q 0 [20488,20489,49187],q 1 [],q 18 [],q 2 [4096,16825,20497,24648],q 10 [12297,24648],q 4 [12294,200955],q 4 [16386,49375],q 3 [20488,20489,49375,49187],q 12 [16386],q 24 [],q 1 [20488,20489,49187,16397],q 2 [20488,20489,49187,196],q 2 [73732,16741,20497,24648],q 3 [20488,20489,49156,49187],q 2 [20488,20489,49156,49187],q 23 [],q 0 [20488,12321,20497,24576],q 19 [],q 2 [20488,20489,49187,20497,24576],q 1 [20488,20489,49187,200927],q 3 [20488,20489,49187,200927],q 2 [20488,20497,24576],q 3 [20488,12321,24576],q 10 [24576],q 15 [],q 2 [16386,73728,73732,16741],q 0 [],q 8 [12297,73759],q 15 [20489,49156],q 0 [20493,20497,24576,401439],q 0 [20490,20497,24576,29305],q 2 [20497,24576,86024,86025],q 3 [24576,4124,12581],q 3 [12297,20850,375],q 2 [20497,24576,24648],q 3 [12297,24576,8221,24648],q 3 [20488,12321,20489],q 3 [24576,8220,8221,98399],q 12 [20497,24576],q 2 [20488],q 16 [20488],q 3 [20490,20491,676473,679936],q 1 [20490,20491,676473,17045],q 8 [20490,20491,676473],q 0 [20490,20491,676473],q 2 [20490,20491,676473],q 12 [679936],q 0 [20490,20491,676473,17045,679936],q 4 [36868,49827],q 5 [20488,12321,20489],q 4 [],q 11 [20497,24576,98399],q 2 [8196,16501,20497,24576],q 0 [16501,20497,24576],q 1 [20497],q 16 [20497],q 0 [12297,20497,24576,73759],q 4 [49156,16801],q 0 [20488,20489,16801,49187],q 12 [16801],q 1 [20488,12321,20489,49156],q 3 [20488,12321,20489,49156],q 3 [20488,12321,20489,49156,49188],q 3 [20488,20489,49187,720911],q 2 [20488,20489,49187,16581],q 5 [20488,12321],q 1 [20488,20489,49187,4815],q 0 [20488,20489,49187,199],q 2 [20488,20489,49187,199,4815],q 2 [20497,24576,24584],q 0 [20497,24579],q 4 [20497,24579],q 12 [],q 3 [20488,20489,49187,20493,401408],q 3 [20489,49152,49156],q 3 [12290,20488,20489,49187],q 1 [20488,20489,49187,16582],q 4 [49156],q 2 [20497,24576,8223,86027],q 2 [20497,24576,86020,17141],q 5 [20497,24584],q 4 [20497,786436],q 2 [20497,24584,24585,786436],q 1 [20497,24584,24585,786436],q 3 [24584,24585,786436],q 1 [20497,24589,794628],q 2 [20497,24579,794628],q 3 [24579,24589,794628],q 1 [20497,24589],q 2 [20497,24579,795031],q 1 [20497,24585,786447],q 4 [20497,24579,786447],q 9 [20497,24579],q 1 [20497,24585,786436],q 4 [20497,24579,786436],q 2 [20497,24579,24585,786436],q 3 [24579,24585,786436],q 2 [20497,794635],q 1 [20497,24589,794635],q 2 [20497,24576,794635],q 2 [20497,794632],q 1 [20497,24589,794632],q 2 [20497,24576,794632],q 2 [20497,24585],q 0 [20497,24585,786447],q 4 [20497,24576,786447],q 2 [20497,24585,786436],q 4 [20497,24576,786436],q 2 [20497,24576,24585,786436],q 1 [20497,8221,24584],q 1 [20497,8221,24580],q 14 [],q 5 [],q 3 [24576,24586,29477],q 2 [20497,24576,24586,29477],q 3 [24576,24585,786463],q 0 [20497,24576,24585,786463],q 2 [20497,24576,24585,786463],q 1 [8196,12405,209499],q 3 [12297,20552],q 0 [12297,20552,17201],q 13 [20497,24576],q 0 [20497,24576,24587],q 1 [12294,20497,28921],q 2 [20497,24576,28921],q 3 [12294,24576,28921],q 5 [20497,24587],q 4 [20497],q 3 [12294,20488,20489,49187],q 1 [20497,12317,24591],q 1 [20497,12317,24587],q 2 [20497,24576,24587],q 0 [20497,24576,24584],q 1 [16394,20493,758601],q 4 [20493,401408],q 2 [16394,401408,758601],q 3 [],q 3 [20493,401408,758601],q 3 [20489,49375,49156],q 1 [20489,49156],q 1 [20489,49375,49156],q 0 [20489],q 1 [16397,20985,794643],q 3 [20985,794624],q 4 [16397,20985,794643],q 2 [20985,794624,794643],q 9 [20497],q 3 [12294,8441,24584],q 13 [],q 3 [12297,24576,24648],q 1 [8198,20497,28945],q 14 [20497,24576],q 3 [8198,24576,28945],q 2 [],q 1 [8198,16657],q 2 [8198,16657,393216],q 1 [12297,20497,73757],q 3 [12297,24576,73757],q 0 [20489,20497,24576],q 2 [20497,24576,8221],q 1 [20497,8221,12386],q 0 [20493,401408,119525],q 1 [8196,20493,119525],q 2 [8196,401408,119525],q 3 [8196,20493,401408,119525],q 0 [12298],q 8 [12298],q 3 [12298,24576],q 2 [4096,20497,24576],q 10 [],q 3 [20493],q 2 [16394,843,401427],q 4 [20493,401427],q 3 [20489,24576,49183],q 0 [12405,20497,24780],q 3 [8196,12405,24780],q 2 [8196,20497,24780],q 4 [20497,24780],q 1 [20488,12321,20489],q 10 [401408],q 3 [20490,20491],q 3 [20490,20491,20493,401408],q 2 [8196,20497,24576],q 0 [12405,20497,24576],q 3 [8196,12405,24576],q 4 [20685,917523],q 2 [8196,20685,917523],q 3 [12297,24576],q 0 [12297,20497,24576],q 2 [73732,20497,24576],q 0 [20497,24591],q 3 [24576,24591],q 2 [8196],q 3 [8196,12405,21387],q 8 [20489,49156],q 2 [20489,49156],q 1 [20489,49156,20497],q 3 [20489,49156],q 4 [49156,20497,24576],q 2 [20489,49156,20497,24576],q 1 [8196,12405,16590],q 3 [8196,12405],q 1 [8196,12405,20684],q 2 [8196,208896],q 4 [208896],q 2 [20497,24576,8222,8223],q 2 [20497,24576,8222],q 0 [16386,12297,73948],q 3 [12297,73948],q 4 [20497,24648],q 1 [12297,20497,24648],q 3 [20489,49156,430080],q 1 [20489,49156,16801],q 1 [8198,20497,24851],q 4 [20497,24851,24579],q 0 [20497,24851,24579],q 2 [20497,24579],q 14 [20497,24579],q 3 [8198,24851,24579],q 11 [4096],q 3 [4096,20490,24576],q 2 [20497,24579,794632],q 3 [24579,24589,794632],q 2 [8198,20497,24576],q 0 [20497,24576,12317],q 1 [8198,16657,393231],q 10 [16394,843],q 0 [20480,16394,843,21365],q 3 [20480],q 3 [20480,8793,13170],q 10 [16393,782336],q 0 [20480,16393,782336,21437],q 5 [12297],q 9 [16390,195],q 0 [16394,20489,49995],q 5 [16394,20489,49995],q 4 [4096],q 0 [20480,195,21445],q 10 [16390,195],q 1 [20497,24584],q 2 [20480,16390,614593],q 1 [12729,20961,1007635],q 0 [12729,20961,1007635],q 3 [20484],q 0 [12405],q 2 [20480,8196,119385],q 1 [8196,119385,13286],q 1 [12294,8441],q 3 [12294,8441,24576],q 0 [20497,24827,24576],q 3 [12294,24827,24576],q 0 [20480,119385,13286],q 3 [20480,12298,615273],q 1 [20488,20489,49375],q 3 [20488,20489,49375],q 5 [20488,20489],q 0 [20488,20489],q 9 [16386],q 8 [20488,20489],q 2 [4096,16825],q 4 [16657,20493,401792],q 0 [16657,20493,401792],q 5 [20493,401792],q 3 [8198,20493,401792],q 2 [8198,16657,401792],q 2 [20484],q 1 [20484,12797,16978],q 1 [16394,13129,946779],q 2 [20480,16394,946779],q 3 [20480,13129,946779],q 3 [20480,8198,12561],q 14 [20480,16985],q 13 [20497,24579],q 0 [20497,24579,24587],q 3 [20480,20489,49156],q 1 [16985,20489,49156],q 10 [49156],q 5 [20480,16985],q 9 [20480,16985],q 3 [12294,8441,24840],q 0 [12797,16978],q 5 [16978],q 1 [16397,20985,794632,794643],q 1 [12889,8196,12405],q 5 [20480],q 4 [20480],q 1 [12889,8196,119385],q 0 [20480,12889,119385],q 2 [20480],q 12 [16390,195],q 3 [20480,8793,195],q 1 [12462,20497,25607],q 2 [8194,20497,25607],q 1 [20489,49156,49171],q 2 [20489,49156,49171],q 0 [12297],q 8 [12297],q 0 [16386,20489,426206],q 3 [20489,49156,426206],q 0 [16893,12297,634952],q 2 [20484,16893,634952],q 9 [20484,16893],q 5 [12297,634952],q 3 [20484,12297,634952],q 10 [12297,634952],q 1 [8196,16397,119829],q 2 [8196,516096,119829],q 0 [16397,516096,119829],q 4 [16397,516096],q 3 [8196,516096,119829],q 7 [],q 3 [12297,73732,371],q 1 [12297,16458],q 0 [12297,16458,371],q 12 [20480,16985],q 3 [20480,8793,12298],q 1 [16390,12481],q 3 [20488,20489,49156],q 2 [20488,20489,49156],q 0 [16386,20493,401631],q 2 [20488,20489,49187,20497],q 1 [12294],q 0 [8192,20497,25643],q 10 [36864],q 2 [20488,36864,20489],q 0 [20488,12321,36864,20489],q 12 [4292],q 3 [20488,20489,49187,4292],q 10 [12297,73728],q 0 [20480,12297,73728,21033],q 1 [8321,20497,24584],q 3 [12290,8321,24584],q 2 [20488,36868,20489],q 1 [13353,20497,25656],q 2 [8192,20497,25656],q 4 [20497,25656],q 1 [8633],q 3 [4096,8633,24576],q 0 [16386,12297,73951],q 3 [12297,73951],q 1 [16397,20984,1114285],q 2 [8194,20984,1114285],q 12 [20984],q 0 [20497],q 2 [8198,20497,24851],q 3 [8198,24851,13021],q 1 [20497,4124,8485],q 3 [24576,4124,8485],q 1 [20491,20497,25239],q 9 [12321],q 3 [20488,12321,20489,49159],q 2 [20488,20489,49159],q 0 [20495,17213,852087],q 4 [20495,17213],q 2 [8196,17213,852087],q 3 [8196,20495,852087],q 3 [20489],q 8 [20489,49171],q 0 [20497,25019],q 0 [20497,25019,24576],q 3 [4096,25019,24576],q 0 [12729,20497,24576],q 0 [20488,20489,49187,196],q 3 [20488,20489,49187,196],q 1 [8196,16501,20497],q 5 [12290],q 4 [12290],q 10 [12290],q 2 [20497,24576,794628],q 0 [16893],q 5 [16386,20702,1115],q 4 [16386,20702,1115],q 1 [20493,8933,401416],q 2 [4096,20488,20489,49187],q 9 [4096],q 12 [4096],q 3 [4096,20488,20489,49187],q 1 [8196,119385],q 0 [20480,119385,13285],q 4 [20486],q 2 [20486,20488,20489,49187],q 3 [20486,20488,20489,49187],q 0 [20497,24576,118813],q 3 [8196,24576,118813],q 8 [20489],q 3 [20489,24576],q 3 [4096,24576],q 0 [20497,24576,29801],q 1 [12729,20497,25056],q 0 [12729,20497,25056],q 3 [4096,12729,25056],q 2 [4096,20497,25056],q 1 [16397,20985,794628],q 3 [20985,794624,794628],q 2 [4096,16825,20497],q 10 [12298],q 2 [20497,24576,73756],q 1 [20486,13413,17526],q 1 [20497,24707],q 2 [20497,24707],q 3 [8196,20601,1179663],q 3 [8196,118786,12629],q 0 [12729,20493,401408],q 1 [9114,4527,9115],q 4 [20482,4527],q 2 [20482,9114,4527,9115],q 5 [20482,9115],q 8 [20497],q 2 [8194],q 1 [12461,20497,24591],q 12 [20497],q 3 [8194,12461,24591],q 0 [20480,12405,209499],q 2 [20480,8196,209499],q 5 [20480,209499],q 8 [8196,16501],q 0 [16501,16397,516096],q 1 [8196,16501,16397],q 2 [8196,16501,516096],q 2 [8194,20497,24751],q 1 [20497,24591],q 0 [8441,20497,24576],q 2 [8441,20497,24576],q 1 [13353,20493],q 2 [8192,401408],q 1 [12729],q 5 [20497,24576,24584],q 3 [8198,24576,24584],q 1 [12461],q 2 [8194,20497,24576],q 3 [8194,12461,24576],q 2 [20491,20497,24576],q 0 [20497,24584],q 3 [24576,24584],q 0 [12298,20497,25019],q 2 [4096,20497,25019],q 1 [20702,12297,74843],q 2 [16386,20702,74843],q 4 [16386,20702,74843],q 3 [8198,12561],q 0 [20497,24579,24591],q 5 [20497,24579,24591],q 1 [12294,20497,24591],q 4 [20497,24579,24591],q 3 [12294,24579,24591],q 1 [12509,20489,50336],q 2 [16386,20489,50336],q 3 [12509,20489,50336],q 1 [12729,20489,49632],q 0 [12729,20489,49632],q 5 [20489,49632],q 2 [4096,20489,49632],q 0 [20493,1081346,401427],q 8 [20493,401427],q 4 [20480,12889,73728],q 9 [20480,12889],q 1 [12889,12297],q 2 [20480,73728],q 1 [20497,24580],q 0 [12290,20497,24707],q 0 [20497,24576,12581],q 2 [20497,24576,4124],q 1 [8196,20497,118813],q 2 [16394],q 0 [12297,20497,25019],q 5 [20497],q 5 [241664],q 2 [16390,241664],q 0 [20488,20489,49347],q 9 [16390],q 3 [20488,20489,49347],q 0 [20497,24579,414825],q 2 [20497,24579,24582,414825],q 3 [24579,24582,414825],q 5 [16397,20985,794624],q 1 [16985],q 3 [20480,8196,12405],q 0 [20480,16985,12405],q 3 [20493,401416,401417,1234015],q 1 [20493,401416,401417,1234015],q 2 [401416,401417,1234015],q 2 [16386,20702,1115],q 2 [20480,8196,622711],q 1 [12889,8196,622711],q 1 [20484,16397,521237],q 2 [20484,516096,521237],q 3 [20484,516096,521237],q 10 [16397,516096],q 0 [16397,516096,521237],q 5 [16397,516096],q 1 [20921,12297,1249352],q 0 [20921,12297,1249352],q 5 [12297,1249352],q 2 [4096,20921,1249352],q 4 [20482],q 0 [20482,20488,20489,49187],q 2 [20482,20488,20489,49187],q 3 [20482,20488,20489,49187],q 0 [20497,25019,12733],q 3 [4096,25019,12733],q 2 [20497,24576,73759],q 3 [12297,24576,73759],q 1 [12297,20497,73759],q 1 [16397,20985,794635],q 4 [16397,20985],q 12 [20985,794624],q 3 [20985,794624,794635],q 1 [20497,24584,12437],q 2 [20497,24579,24584],q 1 [20488,12321,16422],q 3 [20488,12321],q 3 [20488,12321,36864],q 0 [20480,16397,516096,21525],q 0 [8633,20497,24576],q 3 [4096],q 10 [12297],q 1 [20497,24584,13533],q 0 [16394,20489],q 5 [16394,20489],q 3 [20490,24576,4124],q 0 [20490,20497,24576],q 0 [16386,20489,49375],q 1 [12294,20497,25435],q 1 [16514,20489,50195],q 2 [16514,20489,50195],q 3 [12290,20489,50195],q 12 [16514],q 5 [16386,20703,20482],q 10 [12294],q 4 [16386,20703,20482],q 1 [20497,24751,12609],q 3 [8194,24751,12609],q 0 [20482,20488,12321,20489],q 2 [20482,20488,20489],q 3 [20482,20488,12321,20489],q 2 [20497,24576,24651],q 3 [12297,24576,24651],q 0 [16397,20984,1114229],q 3 [8196,20984,1114229],q 5 [16397,20984],q 4 [16397,20984],q 2 [8196,20984,1114229],q 2 [8321,20497,24576],q 2 [8198],q 14 [20497,24591],q 3 [8198,12561,24591],q 1 [20493,20497,401427],q 2 [20497,24576,401427],q 1 [12298],q 2 [4096,20923,17657],q 1 [16513,20489,49156],q 5 [12290,16513],q 2 [16513,20489,49156],q 3 [12290,20489,49156],q 16 [20489,49156],q 1 [20488,12321,20497],q 1 [8196,12405,20686],q 0 [20493],q 3 [4096,20493,24576],q 0 [20489,425986],q 1 [8196,20599,17673],q 1 [20488,20497,24611],q 1 [8196,20497,24695],q 0 [20497,24587],q 3 [24576,24587],q 1 [8198,20755,17689],q 0 [12405,20685,917504],q 4 [20685,917504],q 2 [8196,20685,917504],q 3 [8196,12405,20685,917504],q 1 [20493,401417,1233639],q 1 [12294,20497,24827],q 2 [20497,24827,24579],q 0 [20497,24827,24579],q 3 [12294,24827,24579],q 1 [8321],q 3 [12290,8321,24576],q 1 [16985,16393,782351],q 0 [20480,16985],q 2 [20480,16985,16393],q 3 [20480,782351],q 2 [20497,24576,29545],q 3 [12298,24576,29545],q 3 [12297,20849],q 1 [20497,24751],q 4 [20497,24751],q 1 [8198,12561],q 3 [8198,12561,24576],q 2 [73728,16458,371],q 3 [12290,20488,12321],q 2 [20984,20985,795715],q 4 [20497,24591],q 0 [16386,20489,426205],q 3 [20489,49156,426205],q 1 [20497,12317],q 2 [20488,20489,49187,199],q 1 [12294,16633],q 5 [258048],q 3 [516104,516105,1377599],q 1 [20493,401418,401419],q 12 [1359],q 4 [20493],q 5 [20493,401419],q 3 [20493,401419],q 3 [20493,401418,1359,401419],q 5 [20489,49608],q 0 [16825,20489,49608],q 1 [16825,20497],q 13 [20497],q 5 [20497,24591],q 0 [16633,20489,49404],q 3 [12294,20489,49404],q 2 [16633,20489,49404],q 2 [20488,20489,49159,49187],q 3 [20488,20489,49159,49187],q 2 [4096],q 4 [20497,24576,24648],q 2 [16390,195,401427],q 1 [16390,20493,401427],q 3 [4096,20489,49595],q 5 [20489],q 0 [20489,49595],q 0 [20489,49171],q 12 [20985,794628],q 1 [16397,20985,794628,794635],q 3 [20985,794628,794635],q 3 [20493,401412,1404928],q 1 [20493,401412,17441],q 2 [401412,17441,1404928],q 2 [20497,24584],q 2 [20491],q 2 [20497,24587],q 1 [20700],q 1 [20702,12317],q 1 [13353,21561,1421331],q 2 [20489,401408,49895],q 1 [20493],q 0 [20493,17441],q 0 [20493,401408,17441],q 5 [20493,401408],q 2 [16386,20703,20482,549785],q 4 [17045],q 2 [20491,17045,679936],q 3 [20703,8196,548981],q 1 [20703,8196,548981],q 10 [8196],q 0 [16386,20703,548981],q 2 [8192,20497,24576],q 3 [20985,794624,794632],q 9 [20493],q 5 [20493,401416],q 1 [20493,401416,401417],q 4 [20493,1232896],q 2 [401416,401417,1232896],q 3 [20493,401416],q 3 [20493,401416,401417,1232896],q 2 [20490,20491,20497,24576],q 3 [12297,73732],q 15 [12297],q 8 [12297,73728],q 5 [12297,73728],q 2 [16386,73728,73732],q 1 [20493,17125,401427],q 3 [20493,401408],q 1 [12297],q 1 [12297,73732,16741],q 2 [16386,73732,16741],q 0 [20497,25019,24584],q 1 [20703],q 9 [12405],q 1 [8633,20497,25100],q 3 [4096,8633,25100],q 2 [16390,195],q 1 [16390,20489,49347],q 5 [20489,339970],q 0 [195,20489,50116],q 2 [20488,20489,49187,49171],q 1 [20488,20489,49187,49171],q 4 [20497,24589,794628],q 12 [20497,794628],q 0 [12481,20489,49388],q 2 [16390,20489,49388],q 3 [12481,20489,49388],q 1 [16397,20985,794632],q 1 [16390,20673],q 2 [16390,20673,577536],q 3 [20484,634880,20493],q 1 [20484,16893,20493],q 2 [20484,16893,634880],q 0 [16397,20985,794627],q 1 [16397,20985,794631],q 2 [20985,794627,794631],q 3 [20985,794627,794631],q 1 [12297,73732],q 0 [12297,16458,20850],q 3 [12297,20850],q 3 [20484,12797],q 2 [16394,20489,49995],q 3 [20489,49995,49156],q 1 [20484,12797,20497],q 0 [12297,20837,20552],q 5 [12297,20552],q 2 [73732,20837,20552],q 1 [20497,24587],q 0 [17509,20497,24576],q 0 [12297,73728,16741],q 2 [73728,73732,16741],q 0 [12297,364546,16458],q 2 [20985,794643,794647],q 3 [20985,794647],q 3 [12297,73732,368640],q 2 [73732,16741,368640],q 3 [20493,24576],q 0 [12297,20497,24935],q 2 [73732,20497,24935],q 0 [12297,20497,24648],q 3 [12297,24648],q 2 [73732,20497,24648],q 1 [16394,13129,21406],q 0 [20497,25019,24591],q 2 [20497,24648,462854],q 2 [20490,16457,1376891],q 3 [12297,20490,1376891],q 4 [17045,679936],q 9 [679936],q 8 [20490,20491],q 5 [20490,20491],q 0 [20490,20491],q 2 [20490,20491],q 0 [20490,20491,17045,679936],q 1 [20490,20491,17045],q 3 [12297,20493,401416],q 1 [12297,20493,20552],q 3 [12297,20493,20552],q 3 [12297,20493,401408,20552],q 2 [20497,24580,24648],q 3 [12297,24580,24648],q 0 [20497,24576,24591],q 3 [12297,20493,401480],q 1 [12297,20493,401480],q 2 [401480],q 3 [12297,20493,401408,401480],q 10 [12297,16458],q 1 [12297,16458,20849,20499],q 9 [20850,375],q 3 [12297,20850,74103],q 5 [16397,20985,794632],q 1 [16397,20985,794628,794632],q 2 [20985,794628,794632],q 3 [20985,794628,794632],q 2 [20497,24576,4127],q 2 [20497,24584,24585,786583],q 1 [20497,24584,24585,786583],q 3 [24584,24585,786583],q 1 [12297,20497,8221],q 3 [12297,24576,8221],q 2 [20497,24576,24580],q 1 [20489,49156,20493],q 3 [20489,49156,20493,401408],q 2 [20497,24579,24648],q 4 [20497,24579,24648],q 3 [20489,49375,49159],q 1 [20489,49159],q 1 [20489,49375,49159],q 2 [20489,49159],q 2 [20497,24648],q 2 [20497,24648,462848],q 2 [20488,20497],q 1 [20489,49372,49156],q 3 [20489,49372,49156],q 2 [20497,24648,462850],q 0 [16397,20985,794624],q 2 [20985,794624,794631],q 6 [20497,24576],q 2 [20497,24576,8220],q 0 [12298,20497,24576],q 2 [20484,20497,24576],q 0 [12797,20497,24576],q 3 [20484,12797,24576],q 2 [20491,17045],q 1 [20491,17045,679951],q 0 [20497,24851,24576],q 3 [8198,24851,24576],q 3 [21244,1568781],q 3 [21244,1568781,1572864],q 1 [16393,21244,1568781],q 2 [16393,21244],q 10 [1572864],q 1 [16394,13129,20489],q 2 [20497,24576,86026],q 0 [20497,24827],q 2 [20497,24576,20564],q 2 [16458,20850,375],q 1 [16394,13129,21404],q 2 [16394,946176],q 4 [946176],q 5 [20490,20491,676473],q 1 [20490,20491,676473],q 3 [20488,20489,49152,49187],q 0 [20488,20489,49152,49187],q 0 [20480,12297,74331],q 1 [16394,20489,49995,49156],q 2 [16394,20489,49995,49156],q 1 [20488,12321,16437],q 0 [20489,49152],q 2 [20489,49152,49156],q 12 [425986],q 15 [20488,12321],q 1 [20488,12321,16438],q 2 [20488,36864],q 1 [20488,12321,20533],q 3 [20488,12321,36866],q 2 [20488,36870,20489],q 4 [16422,1231],q 0 [20488,12321,20489,49188],q 3 [20488,12321,20489,49188],q 3 [24576,8221,24584],q 1 [8196,20493,401419],q 9 [118786],q 2 [8196,118786,401419],q 0 [118786,20493,401419],q 3 [8196,118786,20493,401419],q 4 [49191],q 3 [20488,12321,20489,49191],q 2 [20488,20489,49191],q 1 [20497,24585,786463],q 4 [16421,1609728],q 1 [20488,12321,16421],q 1 [16390],q 5 [20489,49152],q 0 [195,20489,49152],q 2 [4096,20497,24648],q 1 [8196,12629],q 2 [8196,118786],q 3 [20488,12321,516096],q 0 [20489,16801],q 3 [20489,24576,4124],q 2 [20497,24648,462852],q 0 [20497,24579,24589,794635],q 2 [20497,24579,794635],q 3 [24579,24589,794635],q 2 [73732,16741,20497],q 3 [20488,20489,49187,12486],q 2 [20488,20489,49187,4295],q 2 [8198,20497,24579],q 12 [20497,24579],q 3 [8198,12561,24579],q 0 [12297,16741,20554],q 3 [20488,20489,49187,12485],q 0 [20488,20489,49187,12485],q 0 [20488,20489,49187,16581],q 3 [8196],q 3 [20490,24576,29305],q 1 [12461,20497,24915],q 3 [8194,12461,24915],q 2 [20488,20489,49187,16582],q 1 [20700,8196,119069],q 3 [20700,8196,119069],q 0 [16386,20700,119069],q 4 [16386,20700],q 4 [12486],q 0 [20488,20489,49187,12486],q 1 [12297,74651],q 10 [12297,74651],q 3 [20488,20489,49187,20493],q 3 [20488,20489],q 2 [20488,20489,401408],q 12 [401408],q 3 [20488,20489,20493,401408],q 2 [20488,20489,20497,24576],q 4 [16397,20985,794624],q 1 [16397,20985],q 2 [20985,794624,9045],q 1 [20488,20489],q 1 [20488,20489,20497],q 3 [20488,20489,24576],q 1 [20488,16397,33813],q 3 [20488,516096,33813],q 2 [20488,516096,33813],q 1 [8321,20497,24888],q 3 [12290,8321,24888],q 0 [20489,49152,16801],q 1 [9112,9113,1660499],q 2 [20482,9112,9113,1660499],q 0 [20489,16801,430080],q 2 [20497,24576,8223],q 5 [20489,49171],q 0 [20489,425986,49171],q 3 [20489,49156,425986],q 2 [20489],q 3 [20489,49167],q 3 [20489,20493,401408,49167],q 1 [20489,20493,49167],q 4 [20497,24576,49171],q 2 [20489,20497,24576,49171],q 1 [20484,16893,634895],q 2 [20484,16893],q 5 [20497,24576,24591],q 2 [20497,24576,86027],q 3 [24576,12317,86027],q 1 [20489,20497,49171],q 2 [20489,49171],q 3 [20490,20491,676473],q 2 [20490,20491,676473,4759],q 3 [20490,20491,676473,4759],q 2 [20490,20491,676473,17045],q 8 [20493],q 3 [20493,24576,4124],q 0 [20493,20497,24576],q 3 [8196,12405,208896],q 3 [20493,20984],q 3 [20493,401408,20984],q 1 [16397,20493,20984],q 2 [20497,24576,794655],q 3 [24576,24589,794655],q 3 [24576,8221,12386],q 0 [12729],q 2 [16458,20850,74103],q 4 [16458,20850,74103],q 9 [20850],q 2 [20497,24576,73757],q 5 [16397,20985,794627],q 2 [20985,794627,794628],q 3 [20985,794627,794628],q 0 [20497,25019,24587],q 1 [8196,12405],q 3 [20985,794632,794639],q 4 [16397,20985,794627],q 0 [16397,20985,794627,794632],q 2 [20985,794627,794632],q 3 [20985,794627,794632],q 2 [16394,20489],q 3 [12294,13129,20489],q 5 [16394,13129,20489],q 12 [20985,794627],q 0 [16397,20985,794627,794635],q 2 [20985,794627,794635],q 3 [20985,794627,794635],q 1 [12889,8196,622709],q 3 [20985,794628,794639],q 1 [20497,8222,12465],q 3 [24576,8222,12465],q 2 [20497,24576,86025],q 0 [16397,20985,794635],q 12 [20985,794631],q 1 [16397,20985,794631,794635],q 3 [20985,794631,794635],q 4 [20497,24576,24591],q 3 [12294,24576,24591],q 0 [12405,20684,17297],q 3 [8196,12405,20684],q 2 [20985,794643],q 2 [20985,794647],q 2 [401408,8934,403075],q 3 [20493,401417,1232900],q 1 [20488,12321,37087],q 3 [20493,401417],q 1 [20493,401417,1232915],q 5 [20493,401417,1232915],q 3 [20493,794628],q 1 [20493,401425,794628],q 3 [20493,401408,794628],q 2 [401425,794628],q 3 [20493,794632],q 1 [20493,401425,794632],q 3 [20493,401408,794632],q 2 [401425,794632],q 5 [20497,24576,24587],q 3 [8198,24576,24587],q 3 [20493,794635],q 1 [20493,401425,794635],q 3 [20493,401408,794635],q 4 [20493,1232900],q 2 [401416,401417,1232900],q 3 [20493,401416,401417,1232900],q 1 [20493,401416,401417,1232900],q 3 [20493,24576,401439],q 2 [20497,24576,401439],q 2 [20497,24576,86020],q 3 [24576,12317],q 1 [20495,17213,851976],q 12 [17213],q 2 [20497,24576,8220,8221],q 1 [20611,8196,1732725],q 0 [12290,20611,1732725],q 5 [12290,20611],q 4 [12290,20611],q 2 [20611,8196,1732725],q 2 [20497,24576,86024],q 8 [20486,17509],q 15 [20486],q 2 [16386,20486,17509],q 2 [20497,24576,8345],q 1 [20497,4124,12581],q 3 [24576,8221,24587],q 1 [20497,12317,86027],q 3 [24576,12317,24591],q 1 [20497,12318,8345],q 3 [24576,12318,8345],q 1 [20499,13449],q 2 [20499],q 2 [20499,1536000],q 10 [1536000],q 3 [13449,1536000],q 10 [1748996],q 1 [20499,9353,1748996],q 5 [20499],q 2 [20499,9353,1748996],q 3 [9353,1748996],q 2 [20497,794647],q 0 [20497,24589,794635],q 3 [24589,794635],q 3 [24589,794632],q 2 [20497,794624],q 3 [24589,794624],q 2 [20497,24586,21285],q 1 [20497,24586,21285],q 2 [20497],q 1 [20497,24586],q 3 [24586,807],q 2 [20497,24585,786455],q 4 [20497,786447],q 3 [24585,786447],q 1 [20497,24585],q 2 [20497,24585,786432],q 4 [20497,786432],q 3 [24585,786432],q 2 [20497,24584,24585],q 1 [20497,24584,24585],q 3 [24584,24585],q 0 [20497,24584,12437],q 3 [24584,12437],q 2 [20497,24584,151554],q 0 [20497,21609],q 2 [20497,24582,21609],q 1 [20497,20499],q 10 [24579],q 3 [24579],q 2 [20497,24579,20499],q 11 [],q 2 [20497,24579,24585],q 0 [20497,24579,24585],q 1 [20497,24582],q 3 [24578,1115],q 4 [20497,20499],q 2 [20497,20499],q 4 [20497,24589],q 5 [20497,24586],q 0 [20497,24586],q 3 [24584],q 4 [20497,24580],q 2 [20497,24580],q 1 [20497,8221],q 2 [20497,24576,20499],q 1 [20497,12318],q 3 [12290,24707],q 0 [20753,1769491],q 3 [8198,20753],q 3 [8198,20866],q 4 [16657,20866],q 1 [8198,16657,20866],q 9 [20866],q 2 [8198,16657,20866],q 3 [20486,20488,12321],q 1 [12298,22221],q 4 [22221],q 2 [875,22221],q 3 [12298,875,22221],q 0 [12298,875,22221],q 0 [275,20497],q 14 [20497],q 2 [8198,275],q 2 [516107,1583],q 1 [20609,1794067],q 2 [20609,1794067],q 10 [16421],q 2 [8196,20497,24587],q 1 [8196,20497,24587],q 3 [8196,24587],q 1 [21545,16390],q 3 [8192,21545],q 4 [16390],q 2 [8192,21545],q 5 [8192,21545],q 2 [16390],q 8 [8196],q 1 [8196,20497],q 1 [16390,197529],q 3 [20482,197529],q 0 [20482,197529],q 5 [20482],q 2 [20497,24580,24587],q 3 [8196,24576],q 1 [20493,401628],q 5 [20493],q 2 [16386,401628],q 3 [20493,401628],q 15 [20493],q 1 [20495,17213],q 1 [8196],q 0 [20495,17213],q 2 [8196,17213],q 3 [20495],q 4 [21244,1568781],q 9 [1568781],q 3 [8196,20493,401527],q 1 [8196,20493,401527],q 1 [8196,16397],q 2 [8196,516096],q 1 [20700,12298],q 5 [12298],q 2 [16386,20700],q 3 [20700,12298],q 0 [16386,20700],q 5 [16386,20700],q 3 [20480,12297],q 0 [20480,16985,12297],q 2 [20480,16985],q 0 [20597,20493],q 2 [8196,20597],q 3 [8196,20597,20493],q 1 [8196,20597,20493],q 1 [9113,8196],q 0 [20482,9113],q 5 [20482,9113],q 2 [20482,9113,8196],q 2 [20489,20497,24576],q 3 [20491,12949],q 10 [18169],q 1 [20491,12949,18169],q 0 [20597,1822720],q 1 [8196,20597],q 2 [8196,20597,1822720],q 5 [1822720],q 2 [20486,132199],q 4 [1822720],q 0 [12405,20686],q 2 [8196,20686],q 1 [20489,49171],q 2 [20489,49171,491],q 9 [491],q 4 [49171,491],q 0 [12405,20684],q 2 [8196,20684],q 0 [12405,16589],q 4 [16589],q 2 [8196,16589],q 2 [516107,22061],q 3 [516107,22061],q 0 [118786,20493],q 4 [16397],q 0 [118786,16397],q 3 [8196,118786],q 10 [16397],q 0 [118786,20821],q 1 [8196,20821],q 5 [20821],q 2 [8196,118786,20821],q 4 [20821],q 0 [118786,16725],q 1 [8196,16725],q 2 [8196,118786,16725],q 4 [16725],q 0 [118786,12629],q 5 [12629],q 4 [12629],q 2 [20497,24586,24587],q 1 [20497,24586,24587],q 3 [24586,24587],q 1 [12461,20497],q 5 [8194,12461],q 0 [8194,12461],q 4 [12461],q 2 [8194,20497],q 3 [8194,12461],q 2 [20497,24651],q 3 [12297,24651],q 0 [12297,20497,24651],q 0 [20482,20488,20489],q 0 [20755,13593],q 4 [20755,13593],q 1 [8198,20755,13593],q 9 [13593],q 2 [8198,20755],q 3 [8198,20755,13593],q 1 [20488,33689],q 2 [20482,20488,33689],q 3 [20482,20488,33689],q 1 [16393,783259],q 3 [20482,783259],q 2 [20482,16393,783259],q 9 [20482],q 4 [20482,783259],q 1 [16513,20489],q 12 [16513],q 0 [12290,16513],q 3 [12290,20489],q 8 [20482],q 4 [16458],q 2 [16458],q 2 [20482,16458],q 3 [12297],q 3 [20482,12297],q 2 [20482,74651],q 3 [20482,12297,74651],q 4 [20482,74651],q 1 [20499,14129],q 2 [20499,1163],q 3 [1163,14129],q 1 [21547,14137],q 4 [14137],q 2 [8192,21547],q 1 [12297,21033],q 2 [73728,21033],q 1 [16390,197530],q 0 [20488,12321,36864],q 4 [36864],q 1 [16394,861082],q 2 [20482,16394,861082],q 5 [16393],q 13 [16393],q 9 [12294],q 13 [20482],q 1 [12294,16393],q 1 [16394,13129],q 2 [20480,16394],q 0 [20482,12561],q 2 [20482,8198],q 3 [20482],q 14 [20482],q 12 [20482],q 2 [20482,8196,118786],q 1 [8633,16910],q 0 [8633,16910],q 3 [4096,8633],q 5 [16910],q 2 [4096,8633,16910],q 2 [20482,8196,119706],q 1 [17305,1916943],q 2 [20482,17305],q 0 [16657,393216],q 3 [8198,393216],q 9 [393216],q 4 [16657,393216],q 1 [17305,12294],q 4 [20482,17305],q 0 [20482,17305],q 3 [20482,12294],q 5 [20482,17305],q 2 [20482,1383],q 1 [13210],q 3 [20484,24576],q 13 [20480],q 1 [12889,622598],q 1 [13209,17770],q 0 [20482,13209,17770],q 2 [20482,17770],q 15 [13209],q 1 [9114,9115],q 2 [20482,9114,9115],q 0 [275,17861],q 1 [8198,17861],q 2 [8198,275,17861],q 9 [17861],q 4 [275,17861],q 3 [8198,275],q 1 [20491,676761],q 2 [20482,20491,676761],q 3 [20482,20491,676761],q 4 [20482,431],q 0 [20482],q 1 [9114],q 2 [20482,9114,431],q 1 [9112,22097],q 2 [20482,9112,22097],q 3 [4096,24584],q 4 [16390,12481],q 0 [20482,1903],q 1 [20490,20491],q 16 [20490,20491],q 0 [275,21957],q 1 [8198,21957],q 2 [8198,275,21957],q 9 [21957],q 4 [275,21957],q 1 [16397,516699],q 2 [20480,516699],q 1 [9114,20909],q 2 [20482,9114,20909],q 4 [20482,20909],q 1 [9112,9113],q 0 [16386,20753],q 4 [20753],q 2 [8198,20753],q 1 [8198,20753],q 10 [8198],q 14 [16386],q 1 [16825,20490],q 0 [16825,20490],q 4 [4096,16825],q 3 [4096,20490],q 1 [8196,20493],q 2 [8196,401408],q 1 [8413,20486],q 5 [16386,8413],q 4 [16386],q 9 [20486],q 12 [20486],q 3 [8413,20486],q 0 [16386,8413],q 3 [21321,1757199],q 2 [16394,21321],q 1 [16397,20493],q 1 [20489,49755],q 3 [20480,20489,49755],q 4 [20484,16893],q 1 [20484,16893],q 1 [16394,615241],q 0 [20480,16394,615241],q 3 [20480,615241],q 2 [20480,16394,615241],q 0 [12297,16458],q 5 [12297,16458],q 2 [73732],q 2 [73732,16458],q 3 [20490,1188473],q 2 [20490,20499,1188473],q 0 [20490,20499,1188473],q 1 [12297,74331],q 2 [20480,74331],q 3 [20480,12297,74331],q 4 [12294],q 0 [20480,615525],q 1 [20486,615525],q 3 [20480,20486,615525],q 2 [8322],q 4 [12290,13317],q 0 [12290,8322,13317],q 9 [12290],q 3 [12290,8322,13317],q 9 [20480],q 1 [16390,12297],q 0 [20480,12297],q 2 [20480,16390],q 2 [16394,843],q 3 [843,20495],q 4 [20495],q 5 [20495],q 0 [20495],q 0 [16394,843,20495],q 13 [20489],q 0 [20480,20489],q 1 [12294,614649],q 2 [20480,614649],q 0 [20597],q 0 [20480,20597],q 1 [20611,8196],q 0 [12290,20611],q 2 [20611,8196],q 2 [8196,118914],q 0 [13413,20493],q 3 [20486,13413,20493],q 5 [16393,21244],q 1 [16393,21244],q 4 [21244],q 3 [12294,21244],q 1 [20497,8222],q 3 [20480,20489],q 1 [16985,20489],q 0 [20480,16985,20489],q 1 [16985,16393],q 0 [20480,16985,16393],q 1 [16985,12298],q 4 [20480,16985],q 0 [20480,16985,12298],q 1 [16985,8196],q 3 [20480,8196],q 0 [20497,24695],q 2 [8196,20497,24695],q 5 [16397],q 14 [16397],q 9 [16397],q 1 [8198,16397],q 4 [20482,49156],q 2 [20482,20489,49156],q 1 [12889,16994],q 5 [20480,12889],q 0 [20480,12889],q 4 [20480,12889],q 12 [20480],q 2 [20480,16994],q 10 [16994],q 3 [20480,12889],q 0 [12297,73728],q 2 [73728,73732],q 0 [20480,12405],q 2 [20480,8196],q 1 [16985,8198],q 3 [20480,8198],q 1 [12889,16993],q 8 [12294],q 1 [20700,12294],q 3 [20700,12294],q 3 [24576,8223],q 2 [20480,8793],q 4 [20480,13170],q 1 [8793,13170],q 0 [20480],q 10 [13170],q 0 [20480,8793,13170],q 1 [20703,12294],q 2 [16386,20703],q 4 [16386,20703],q 0 [16386,20703],q 3 [20703],q 3 [20703,12294],q 1 [20653,1961999],q 0 [8194,20653,1961999],q 9 [1961999],q 3 [8194,20653,1961999],q 2 [8194,20653],q 3 [20493,401631],q 1 [20493,401631],q 2 [16386,401631],q 1 [8793,17266],q 3 [20480,8793],q 5 [20480,603],q 4 [20480,603],q 1 [20493,401417,1232900],q 2 [401417,1232900],q 3 [20495,9021],q 5 [20495,9021],q 0 [20495,9021],q 2 [9021],q 2 [16386,9021],q 1 [20495,9021],q 5 [16386],q 0 [16386],q 1 [16985,20490],q 3 [20480,20490],q 0 [20480,16985,20490],q 5 [20490],q 2 [20490],q 2 [8441,20746],q 0 [20493,401419],q 15 [20493,401419],q 2 [401419],q 2 [16386,401419],q 1 [20493,401419],q 10 [401419],q 0 [12405,20499],q 2 [8196,20499],q 1 [20499],q 3 [8196,118786,20495],q 1 [8413,22402],q 3 [8413,22402],q 1 [9113,18006],q 3 [20482,9113],q 1 [21545,1806351],q 3 [8192,21545,1806351],q 5 [20491,12949],q 0 [20491,12949],q 4 [12949],q 2 [16386,20491],q 1 [20491,12949],q 1 [8793,20497],q 0 [20480,8793,20497],q 5 [20480,8793],q 0 [12405,16590],q 2 [8196,16590],q 3 [20490,12921],q 5 [20490,12921],q 0 [20490,12921],q 2 [16386,20490],q 3 [20493,20495],q 5 [20489,49167],q 0 [20489,49167],q 15 [20489,49167],q 1 [20489,49167],q 10 [49167],q 2 [16386],q 1 [20484,12797],q 2 [20484,606208],q 3 [20484,12797,606208],q 4 [20493,402071],q 2 [20491,402071],q 1 [20493,401427],q 0 [12405,208896],q 4 [20484,520194],q 2 [20484,520194],q 1 [20489],q 15 [20489],q 2 [17213,851976],q 5 [12298,20489],q 1 [12298,20489],q 2 [16390,20489],q 0 [12298,20489],q 0 [16386,20489],q 2 [16386,20488],q 0 [16386,20493,401427],q 2 [16386,401427],q 3 [12298,20489],q 2 [16386,20489],q 5 [16393,21246],q 3 [12294,21246],q 2 [16393,21246],q 4 [21246],q 0 [16394,21323,2043906],q 4 [2043906],q 2 [16394,21323,2043906],q 1 [20493,8934],q 2 [401408,8934],q 3 [12298,21353],q 5 [12298,21353],q 0 [12298,21353],q 2 [21353],q 2 [16386,21353],q 1 [12298,21353],q 3 [12297,20493],q 5 [12297,20493],q 0 [12297,20493],q 3 [12297,73728],q 2 [16386,73728],q 0 [16386,12297,73728],q 2 [20480,20489,49156],q 4 [20480,49156],q 1 [5016,22381],q 2 [20482,5016,22381],q 1 [20491,13929],q 4 [663,13929],q 0 [20491,663,13929],q 9 [13929],q 2 [20491,663],q 0 [12481,20717],q 2 [16390,20717],q 1 [12297,20552],q 0 [12297,20552],q 2 [73732,20552],q 4 [73732],q 3 [8196,20597,1822735],q 1 [8196,20597,1822735],q 3 [20486],q 0 [16386,17509],q 0 [16386,16501],q 2 [16386,8196,16501],q 15 [8196],q 1 [8196,16501],q 1 [13353,21561],q 2 [8192,21561],q 3 [8192,13353,21561],q 0 [8192,13353,21561],q 15 [12294],q 13 [16386],q 1 [12294,20489],q 0 [12405,20685],q 4 [20685],q 2 [8196,20685],q 3 [8196,12405,20685],q 1 [8196,12405,20685],q 1 [12298,615273],q 0 [20480,12298,615273],q 2 [20480,615273],q 0 [20490,451193],q 1 [20490,451193],q 2 [4096,20490,451193],q 3 [12294,8441],q 0 [16386,8441],q 15 [12294,8441],q 2 [8441],q 2 [16386,8441],q 14 [20493],q 8 [8198],q 15 [8198],q 1 [8198,20493],q 0 [16386,20493],q 2 [16386,8198],q 3 [8196,20597],q 0 [16386,20597],q 0 [20493,401408],q 3 [20493,401412],q 1 [20493,401412],q 2 [401412],q 3 [20493,401408,401412],q 0 [275,16397],q 1 [16397],q 3 [20482,1115],q 3 [12294],q 5 [16386,20482],q 4 [16386,20482],q 16 [8198],q 14 [12290],q 1 [8198,20497],q 0 [20480,12889,16994],q 4 [16590],q 3 [8198,24584],q 2 [8198,20497,24584],q 1 [20703,548877],q 3 [20703,548877],q 1 [20700,12573],q 3 [20700,12573],q 1 [20703,12298],q 5 [16386,20703],q 3 [20703,12298],q 5 [16386,20702],q 1 [20702,8198],q 3 [20702,8198],q 0 [16386,20702],q 2 [16386,20702],q 1 [20702,13401],q 3 [20702,13401],q 0 [9317,2080768],q 2 [20486,9317,2080768],q 3 [20486,9317,2080768],q 1 [20702],q 5 [16393,20490],q 1 [16393,20490],q 3 [12294,20490],q 4 [16386,49156],q 2 [16386,20489,49156],q 1 [20701,8198],q 4 [16386,20701],q 0 [16386,20701],q 2 [16386,20701],q 5 [16386,20701],q 3 [20701,8198],q 1 [20493,20497],q 2 [401408,20497],q 1 [16394,13173],q 4 [13173],q 3 [843,13173],q 1 [20610,17765],q 2 [20610,17765],q 1 [8793,16985],q 0 [20480,8793,16985],q 2 [20608,131679],q 16 [20484],q 1 [20484,20497],q 1 [20702,12297],q 3 [20702],q 3 [20702,12297],q 1 [20701,12297],q 3 [20701],q 3 [20701,12297],q 3 [12290],q 5 [20497,20499],q 0 [20497,20499],q 0 [16893,634880],q 1 [16397,20987],q 2 [20987,2051],q 3 [12290,195],q 1 [12462,21509],q 4 [12462,21509],q 0 [8194,12462,21509],q 2 [8194,21509],q 3 [8194,12462,21509],q 2 [20488,16417,20489],q 3 [12297,20553],q 4 [20553,1232915],q 1 [12297,20553,1232915],q 2 [20553,1232915],q 3 [8196,20599,20493],q 1 [8196,20599,20493],q 2 [20552,17201],q 1 [8633,20497],q 0 [8633,20497],q 5 [20495,17213],q 2 [8192,17213],q 5 [8192],q 0 [8192],q 1 [20489,20493],q 2 [20489,401408],q 3 [20489,20493,401408],q 4 [49171],q 3 [4096,20489],q 1 [12461,20499],q 2 [8194,20499],q 0 [20499],q 1 [12461,16721],q 4 [12461,16721],q 0 [8194,12461,16721],q 9 [16721],q 2 [8194,16721],q 1 [12889,16397],q 2 [16514,1043],q 1 [20921,1249299],q 0 [20921,1249299],q 2 [4096,20921,1249299],q 1 [13353,17466],q 0 [8192,13353,17466],q 2 [8192,17466],q 2 [20985,794624],q 3 [20493,401417,1232896],q 2 [401417,1232896],q 0 [20488,16417,2109440],q 3 [20488,2109440],q 2 [20488,16417,2109440],q 1 [20488,16417],q 4 [2109440],q 1 [17449,12294],q 2 [8192,17449],q 0 [8192,17449],q 3 [8192],q 3 [8192,12294],q 5 [8192,17449],q 1 [20493,402475],q 2 [8192,402475],q 1 [17305],q 2 [16386,20482,17305],q 0 [16397],q 2 [20984,1114114],q 3 [20984,1114114],q 1 [16397,20984],q 1 [16825,12298],q 0 [16825,12298],q 3 [4096,12298],q 2 [20610],q 2 [20489,49152],q 3 [20489,49152,20493],q 4 [49152],q 1 [20486,1090661],q 0 [8192,1090661],q 2 [8192,20486,1090661],q 5 [12297,20553],q 0 [12297,20553],q 4 [20553],q 2 [20553],q 2 [16386,20553],q 1 [12297,20553],q 0 [20490,17017],q 1 [20490,17017],q 2 [20490,17017],q 0 [20480,20493],q 16 [401412],q 2 [20480,401412],q 2 [8196,16501],q 2 [401408,17126],q 1 [16393,782939],q 2 [20480,16393,782939],q 0 [20480,16393,782939],q 3 [20489,12777],q 1 [20489,49171,12777],q 0 [8192,16893],q 1 [9114,4527],q 13 [8192],q 4 [20499],q 13 [20499],q 1 [12294,20499],q 0 [8192,20499],q 1 [8196,16397,516215],q 3 [8196,516215],q 0 [16397,516215],q 1 [20609,8198],q 4 [12290,20609],q 0 [12290,20609],q 2 [20609],q 2 [20609,8198],q 3 [12290,20609],q 0 [20493,401427],q 5 [20493,401427],q 2 [16390,401427],q 4 [16397,20493],q 5 [16397,20493],q 0 [16397,20493],q 3 [8194,20493],q 1 [21545,1806355],q 4 [1806355],q 2 [8192,21545,1806355],q 1 [21545,1806340],q 4 [1806340],q 2 [4096,16458],q 3 [4096,12297],q 1 [17449,20497],q 2 [8192,17449,20497],q 2 [8198,20753,1769472],q 1 [13353,17465],q 4 [17465],q 2 [8192,17465],q 3 [8192,13353],q 2 [20986,1471],q 1 [16397,20986],q 5 [8192,13353],q 0 [8192,13353],q 1 [16557,20493],q 5 [8194,16557],q 0 [8194,16557],q 4 [16557],q 2 [8194,16557],q 2 [20490,74363],q 3 [12297,20490,74363],q 3 [8198,24591],q 3 [8192,13353,20493],q 0 [20480,119385],q 3 [20480,8196,119385],q 2 [16393,20489,21244],q 3 [20489,21244],q 0 [12298,17257],q 1 [12298,17257],q 2 [17257],q 2 [4096,17257],q 3 [12298],q 5 [12298,17257],q 2 [4096,21353],q 1 [20489,49595],q 4 [4096,49595],q 2 [4096,20489,49595],q 3 [12297,20490],q 5 [12297,20490],q 0 [12297,20490],q 2 [401408,401427],q 3 [20484,8701],q 0 [16386,8701],q 4 [20484],q 15 [20484,8701],q 2 [20484,8701],q 1 [20484,8701],q 2 [8198,16657],q 3 [8198,393231],q 2 [20480,21353],q 8 [20499],q 3 [24591],q 3 [4096,24591],q 0 [16397,20985],q 3 [20985,794631],q 8 [20486],q 1 [20486,12297],q 0 [16386,12297],q 2 [16386,20486],q 0 [8441,20497],q 2 [8441,20497],q 1 [16825,20489],q 0 [16825,20489],q 10 [18350],q 1 [20495,9021,18350],q 2 [9021,18350],q 4 [20495,49983],q 9 [20495],q 2 [20489,49983],q 3 [20489,20495,49983],q 0 [16393,21244],q 3 [21244],q 3 [12290,21244],q 2 [20497,24576,24585],q 2 [8192,401419],q 3 [8192,20493,401419],q 0 [8192,20493,401419],q 0 [12297,20497],q 2 [73732,20497],q 2 [16514,21523],q 16 [21523],q 3 [20985,794632],q 0 [20495,451389],q 1 [20495,451389],q 2 [4096,451389],q 3 [20493,24591],q 10 [24591],q 1 [20493,20497,24591],q 0 [16386,20488,12321],q 5 [8194],q 4 [16390,195],q 0 [8194,195],q 2 [8194,16390,195],q 1 [20484,12797,16393],q 0 [12797,16393],q 2 [20484,16393],q 1 [9112],q 0 [20482,9112,1619],q 0 [12290,20488,20489],q 3 [12290,20488,20489],q 2 [4096,401408],q 1 [12509,20489],q 0 [16386,12509],q 3 [12509],q 3 [12509,20489],q 5 [634880],q 1 [16985,974863],q 10 [974863],q 3 [20489,49152],q 1 [20493,401418],q 5 [20493,401418],q 0 [20493,401418],q 0 [20599,1291],q 4 [1291],q 2 [8196,20599,1291],q 2 [20482,9115],q 3 [20482,9115,13457],q 1 [9115,13457],q 2 [16386,20703,20482],q 3 [20703,20482],q 0 [16393,783463],q 4 [20486,783463],q 1 [20486,16393,783463],q 2 [20486,16393,783463],q 3 [20486,783463],q 0 [20480,8793],q 1 [8793,12294],q 1 [20488,20497],q 3 [12290,20488],q 2 [20490,635],q 5 [20490,635],q 0 [12290,20490,635],q 3 [20490,635],q 3 [12290,20490,635],q 16 [20490],q 0 [12297,16458,20849],q 2 [16458,20849],q 5 [16397,20986],q 2 [4096,20986],q 12 [20986],q 4 [16397,20986],q 2 [8322,1031],q 4 [12290,1031],q 5 [16394,13129],q 3 [12294,13129],q 0 [16394,13129],q 0 [195,20493],q 1 [16390,20493],q 3 [195,20493],q 1 [16514,21521],q 0 [12290,16514,21521],q 3 [12290,21521],q 0 [16825,20497],q 0 [20491,451221],q 1 [20491,451221],q 4 [4096,451221],q 2 [4096,20491,451221],q 5 [20491],q 0 [16397,516539],q 1 [16397,516539],q 2 [4096,516539],q 3 [4096,516539],q 4 [49156,20497],q 2 [20489,49156,20497],q 0 [12297,74171],q 1 [12297,74171],q 2 [4096,74171],q 4 [4096,74171],q 3 [4096,12297,74171],q 2 [20482,517016],q 1 [8196,119705],q 0 [20482,119705],q 2 [20482,8196,119705],q 3 [20490,21113],q 5 [20490,21113],q 0 [20490,21113],q 2 [20490,21113],q 1 [20490,21113],q 0 [20493,20497],q 4 [20493,401583],q 1 [20493,401583],q 0 [8194,20493,401583],q 2 [8194,401583],q 3 [8194,20493,401583],q 1 [20488,20489,49156],q 1 [8793,12298],q 0 [20480,8793,12298],q 3 [8198,24587],q 2 [8198,20497,24587],q 0 [20489,16397,49656],q 1 [20489,16397,49656],q 2 [20489,49656],q 3 [20489,49656],q 0 [17509,20497],q 2 [20486,17509,20497],q 0 [20499,119945],q 2 [8196,20499,119945],q 1 [8196,20499,119945],q 4 [2043917],q 2 [16394,21323],q 3 [21323,2043917],q 8 [12290],q 16 [20489,49171],q 2 [20480,603,16985],q 1 [16825],q 1 [16825,12297],q 0 [12297,20489],q 1 [12297,20489],q 2 [4096,20489],q 5 [12297,20489],q 3 [12297,20489],q 1 [16825,20938],q 0 [16825,20938],q 2 [4096,16825,20938],q 0 [12405,20493],q 3 [8196,12405,20493],q 1 [8196,12405,20493],q 0 [20482,12797],q 4 [20484,12797],q 12 [20484],q 2 [20482,20484],q 0 [20482,521113],q 1 [20484,521113],q 2 [20482,20484,521113],q 3 [20482,20484,521113],q 4 [12294,16633],q 0 [16633],q 0 [8192,16633],q 2 [8192,16633],q 1 [12889,16985],q 0 [20480,12889,16985],q 3 [12290,24587],q 0 [12290,20753],q 1 [20703,8196],q 3 [20703,8196],q 3 [20493,401417,1232919],q 3 [8196,20602],q 4 [20602],q 2 [8196,16501,20602],q 1 [8196,16501,20602],q 1 [20921,12297],q 0 [20921,12297],q 2 [4096,20921],q 4 [4096,20921],q 3 [4096,20921],q 0 [118786,20497],q 4 [20493,20495],q 3 [20493,20495,9021],q 1 [20484,20493],q 2 [17213,851968],q 10 [851968],q 1 [12294,20729],q 2 [8196,20984],q 3 [8196,20984],q 1 [20490,615033],q 3 [20480,20490,615033],q 0 [20480,20490,615033],q 2 [20480,20490,615033],q 1 [21545,12294],q 0 [8192,21545],q 1 [12729,20497],q 0 [12729,20497],q 3 [4096,12729],q 4 [4096,12729],q 2 [4096,20497],q 0 [20499,9353],q 1 [20499,9353],q 5 [20499,9353],q 3 [4096,9353],q 2 [20729,2289683],q 1 [20491,17045],q 3 [20491],q 3 [20491,679936],q 8 [20491],q 3 [20486,24576],q 0 [20488,20515,663],q 2 [20488,20515,663],q 3 [20488,20515,663],q 1 [20488,20515],q 2 [20486,20490,20491],q 1 [16397,517019],q 3 [20482,517019],q 2 [20482,517019],q 0 [20482,20488,12321],q 2 [20482,20488],q 3 [20482,20488,12321],q 1 [20611,18077],q 2 [20611,18077],q 0 [16633,20489],q 2 [16633,20489],q 3 [12294,20489],q 12 [16633],q 0 [20923,17657],q 1 [20923,17657],q 1 [16397,517163],q 2 [8192,517163],q 3 [8192,517163],q 0 [16397,517223],q 3 [20486,517223],q 2 [20486,517223],q 1 [8633,21006],q 0 [8633,21006],q 4 [4096,21006],q 5 [21006],q 2 [4096,8633,21006],q 3 [4096,8633,21006],q 1 [8793,16394],q 10 [16394],q 0 [20480,8793,16394],q 0 [16501,20497],q 2 [8196,16501,20497],q 2 [20484,21353],q 0 [12729,16865],q 1 [12729,16865],q 2 [4096,16865],q 1 [13353,20497],q 2 [8192],q 2 [8192,20497],q 0 [12290,20488,12321],q 4 [20493,20552],q 2 [20552],q 1 [17449,22561],q 2 [8192,17449,22561],q 0 [8192,17449,22561],q 0 [20673,12297],q 2 [16390,20673],q 0 [195,21445],q 1 [16390,21445],q 3 [195,21445],q 5 [21445],q 2 [16390,195,21445],q 1 [12729,20489],q 0 [12729,20489],q 3 [20987,14337],q 1 [16397,20987,14337],q 3 [12297,20489,20493],q 0 [12297,20489,20493],q 12 [401427],q 2 [4096,401427],q 3 [4096,20493],q 2 [16394,9021],q 1 [16394,20495,9021],q 5 [12297,20554],q 2 [4096,20554],q 3 [12297,20554],q 0 [12297,20554],q 4 [49156,20493],q 3 [20489,49156,20493],q 0 [16393,20489],q 1 [16393,20489],q 2 [16393,20489],q 5 [16393,20489],q 1 [8633,20490],q 0 [8633,20490],q 3 [4096,8633,20490],q 0 [12298,20497],q 2 [16458,20554],q 2 [20553,1232896],q 0 [12729,20493],q 1 [12729,20493],q 3 [4096,12729,20493],q 3 [20495,831],q 8 [20495,831],q 0 [16386,20495,831],q 15 [20495],q 2 [16386,831],q 1 [20495],q 10 [16386],q 4 [1822739],q 2 [8196,20597,1822739],q 1 [8196,20597,1822739],q 5 [8192,21547],q 1 [21547],q 1 [21547,12294],q 0 [8192,21547],q 1 [8196,20597,20495],q 0 [20597,20495],q 0 [12561],q 0 [20480,12561],q 14 [20480],q 1 [20701,12294],q 3 [20701,12294],q 2 [20497,794628],q 3 [24589,794628],q 1 [16825,20493],q 0 [16825,20493],q 2 [4096,73728],q 3 [20491,663],q 8 [20491,663],q 0 [16386,20491,663],q 15 [20491],q 1 [20491],q 2 [16386,20491,663],q 4 [16386,663],q 1 [20490,14453],q 4 [14453],q 3 [20490,635,14453],q 3 [4096,25019],q 1 [20493,401416],q 0 [8194,20493,401416],q 2 [4096,17213],q 3 [4096,20495],q 2 [20490,131707],q 1 [20495,1090365],q 2 [8192,1090365],q 0 [12405,20497],q 2 [8196,20497],q 8 [16397],q 1 [20655,18685],q 2 [8194,20655,18685],q 9 [18685],q 4 [20655,18685],q 3 [24579,24584],q 1 [12729,20962],q 0 [12729,20962],q 2 [4096,20962],q 5 [20962],q 3 [4096,12729,20962],q 0 [16501,122880],q 3 [8196,122880],q 4 [122880],q 2 [8196,16501,122880],q 2 [16390,131267],q 3 [516106,14609],q 2 [20986,20987],q 1 [20499,1090697],q 3 [8192,1090697],q 2 [8192,20499,1090697],q 0 [8192,20499,1090697],q 3 [20489,49159],q 4 [49159],q 10 [49159],q 15 [20489,49159],q 0 [12290,20610],q 1 [20610],q 10 [8194],q 1 [13209,17769],q 2 [20482,17769],q 3 [20482,13209],q 1 [20610,13669],q 0 [275,20493],q 1 [12729,16393],q 0 [12729,16393],q 10 [16393],q 1 [13209,20493],q 3 [20482,13209,20493],q 3 [20489,49375],q 1 [20489,49375],q 1 [12297,73951],q 2 [16386,73951],q 1 [16513,20490],q 4 [12290,16513],q 2 [16513,20490],q 3 [12290,20490],q 0 [20490],q 1 [16985,16397],q 1 [8793,16390],q 10 [16390],q 1 [9113,20490],q 2 [20482,9113,20490],q 0 [20482,9113,20490],q 3 [20482,9113,20490],q 3 [20484,520194],q 8 [20484,520194],q 15 [20484],q 2 [16386,20484,520194],q 2 [8198,516096],q 2 [20497,24579,24587],q 1 [16394,20489],q 1 [8321,20497],q 5 [12290,8321],q 0 [12290,8321],q 2 [8321,20497],q 3 [12290,8321],q 2 [20480,20489],q 0 [16393,20490],q 2 [16393,20490],q 2 [20497,24704],q 0 [16394,21321],q 1 [16394,21321],q 3 [4096,21321],q 2 [20499,132235],q 0 [1127,18289],q 1 [20486,18289],q 3 [20486,1127],q 2 [20486,1127,18289],q 4 [782351],q 3 [20490,782351],q 0 [16825,20937],q 1 [16825,20937],q 2 [4096,16825,20937],q 1 [16390,1089729],q 3 [8192,1089729],q 0 [8192,1089729],q 2 [8192,16390,1089729],q 0 [20490,21113,49152],q 2 [20490,21113,49152],q 3 [20490,21113,49152],q 1 [12294,20497],q 3 [4096,21246],q 0 [20488,33209],q 1 [20488,33209],q 5 [20488],q 2 [4096,20488,33209],q 1 [16397,516102],q 2 [516102,2355],q 3 [516102,2355],q 0 [16397,2355],q 2 [4096,20488,20489],q 3 [4096,20488,20489],q 1 [17449,2129935],q 9 [364546],q 0 [12297,364546],q 2 [73732,364546],q 3 [12297,73732,364546],q 1 [20488,18749],q 4 [18749],q 2 [20488,32770,18749],q 0 [20488,32770,18749],q 3 [20488,32770],q 10 [36866],q 2 [20608],q 0 [12290,20608,12893],q 1 [12462,17413],q 4 [12462,17413],q 0 [8194,12462,17413],q 2 [8194,17413],q 3 [8194,12462],q 1 [12462,20497],q 1 [20702,12294],q 3 [20702,12294],q 4 [16386,20702],q 2 [20490,516731],q 3 [20490,516731],q 4 [20499,13449],q 5 [20499,13449],q 0 [20499,13449],q 12 [20499],q 3 [8194,13449],q 0 [16386,12797],q 15 [20484,12797],q 3 [20490,2146319],q 1 [20495,20497],q 8 [20495],q 0 [16386,20489,49171],q 2 [16386,20489,49171],q 4 [16386,49171],q 1 [16557,22617],q 2 [8194,16557,22617],q 3 [8194,22617],q 1 [16557,22618],q 0 [8194,16557,22618],q 9 [22618],q 2 [8194,16557,22618],q 1 [20701,1437711],q 3 [20701,1437711],q 1 [16558,22877],q 4 [16558,22877],q 0 [8194,16558,22877],q 2 [8194,16558,22877],q 3 [8194,22877],q 4 [20486,13413],q 0 [8194,13413],q 1 [20486,13413],q 2 [20486],q 2 [8194,20486],q 3 [8194],q 4 [20497,49171],q 2 [20489,20497,49171],q 0 [16501,20601],q 4 [20601],q 2 [8196,16501,20601],q 1 [8196,16501,20601],q 2 [20480,622600],q 10 [622600],q 1 [12889,622600],q 1 [20484,8701,20497],q 9 [16801],q 1 [16390,614593],q 0 [20480,614593],q 0 [8194,20655,18685],q 12 [18685],q 3 [20985,794628],q 3 [8194,24591],q 1 [12889,16393],q 0 [20480,12889,16393],q 0 [16386,12561],q 4 [12561],q 15 [8198,12561],q 1 [13353,21562],q 2 [8192,21562],q 3 [8192,13353,21562],q 0 [8192,13353,21562],q 0 [20491,17045],q 5 [20491,17045],q 5 [16394,21321],q 3 [21321],q 3 [12290,21321],q 2 [401427,851],q 0 [20753,1769487],q 2 [20480,516096],q 0 [8194,16633],q 2 [16633],q 2 [8194,16633],q 3 [8194,12294],q 13 [8194],q 4 [12294,20729],q 0 [8194,20729],q 2 [20729],q 2 [8194,20729],q 3 [12294,20729],q 12 [20729],q 2 [20489,16458],q 0 [16394,451401],q 1 [16394,451401],q 3 [4096,451401],q 2 [4096,16394,451401],q 1 [20493,401425],q 2 [401425],q 0 [20923,13561],q 1 [20923,13561],q 2 [4096,20923],q 1 [12461,20817],q 4 [12461,20817],q 0 [8194,12461,20817],q 9 [20817],q 2 [8194,20817],q 3 [8194,12461,20817],q 0 [8194,20499],q 3 [8196,20495,119613],q 1 [8196,20495,119613],q 2 [8196,119613],q 0 [20495,119613],q 1 [12297,20497],q 2 [20482,16633],q 0 [16397,14641],q 12 [516096],q 1 [20491,16397],q 0 [16397,516096],q 0 [20491],q 1 [16390,176321],q 0 [8194,176321],q 4 [16390,176321],q 2 [8194,16390,176321],q 3 [8194,176321],q 0 [8194,520365],q 1 [20484,520365],q 4 [20484,520365],q 2 [8194,20484,520365],q 0 [8194,12797],q 2 [8194,20484],q 0 [251,20489],q 12 [251],q 2 [20488,20489,49171],q 1 [20488,20489,49171],q 16 [8196],q 1 [8321,20794],q 2 [8321,20794],q 4 [20486,17509],q 0 [8194,17509],q 1 [20486,17509],q 2 [20486,17509],q 0 [20489,20493],q 1 [16393,20493],q 2 [16393,401408],q 0 [20499,451721],q 1 [20499,451721],q 3 [4096,451721],q 2 [4096,20499,451721],q 0 [8194],q 1 [9113,16390],q 0 [8194,520194],q 1 [20484],q 2 [8194,20484,520194],q 5 [20488,16417],q 0 [20488,16417],q 3 [20488],q 2 [20488,16417],q 2 [20608,607],q 4 [16457],q 2 [20490,16457],q 3 [12297,20493,20554],q 0 [12297,20493,20554],q 2 [16386,20554],q 1 [20484,12797,20489],q 0 [12797,20489],q 2 [20484,20489],q 3 [20489,49659],q 0 [12561,20499],q 2 [8198,20499],q 1 [12889,8196],q 0 [8194,20497,24751],q 3 [8194,24751],q 3 [12290,20491],q 16 [20488,16417],q 3 [12294,20488,12321],q 3 [24587],q 3 [4096,24587],q 3 [20480,20493],q 1 [16985,20493],q 0 [20480,16985,20493],q 3 [12294,24587],q 0 [16393,21245],q 1 [16393,21245],q 4 [21245],q 2 [16393,21245],q 3 [21245],q 3 [4096,21245],q 5 [16393,21245],q 0 [20490,635],q 1 [20490],q 3 [4096,20490,635],q 2 [17213],q 2 [8194,17213],q 3 [8194,20495],q 4 [20497,25239],q 2 [20491,20497,25239],q 3 [21244,783871],q 1 [20497,24748],q 3 [8194,24748],q 1 [20655,14589],q 4 [20655,14589],q 0 [8194,20655,14589],q 9 [14589],q 2 [8194,20655],q 0 [12290,20597],q 5 [16397,20985],q 2 [20985],q 2 [8194,20985],q 3 [20985],q 3 [8194,20985],q 16 [20491],q 1 [20491,20497],q 1 [20497,25019],q 2 [16386,73732],q 1 [20499,177289],q 2 [8194,20499,177289],q 3 [8194,177289],q 2 [73728,20497],q 0 [20482,16893],q 2 [20482],q 2 [8320,22953],q 0 [12290,8320,22953],q 3 [12290,8320,22953],q 16 [22953],q 2 [8322,21509],q 4 [12290,21509],q 16 [21509],q 1 [20493,401414],q 2 [401414,2483],q 0 [20493,2483],q 3 [20493,401414,2483],q 1 [12889,622602],q 1 [16513,8198],q 2 [16513],q 2 [16513,8198],q 3 [12290,8198],q 1 [12509,20491],q 5 [16386,12509],q 4 [16386,12509],q 1 [16513,21762],q 2 [16513,21762],q 0 [16386,20488,20489],q 15 [20488,20489],q 2 [16386,20488,20489],q 1 [16514,20489],q 2 [16514,20489],q 2 [16514,21521],q 16 [21521],q 1 [17305,20497],q 2 [20482,17305,20497],q 0 [20729],q 0 [20480,20729],q 2 [20480,20729],q 2 [20610,1383],q 0 [12290,118786],q 3 [12290,8196,118786],q 0 [16397,20984,1114121],q 2 [20984,1114121],q 3 [20984,1114121],q 1 [16397,20984,1114121],q 2 [8322,21511],q 4 [12290,21511],q 4 [4096,20923],q 1 [20923],q 1 [20923,12298],q 0 [20923],q 0 [20923,12298],q 3 [4096,20923],q 4 [49156,16397],q 1 [20489,49156,16397],q 2 [8196,20599],q 0 [12290,20599],q 1 [8196,20599],q 3 [8196,20599],q 1 [20489,49372],q 3 [20489,49372],q 0 [20488,20489,49152],q 2 [20488,20489,49152],q 3 [20488,20489,49152],q 16 [20499],q 1 [8196,20499],q 2 [8320],q 0 [12290,16657],q 4 [16657],q 3 [8198],q 16 [8198,16657],q 0 [12290,20755],q 4 [20755],q 1 [8198,20755],q 3 [8198,20755],q 4 [12290,20755],q 3 [12297,20493,401419],q 0 [12297,20493,401419],q 2 [8196,401419],q 3 [8196,20493,401419],q 1 [20921,1249295],q 0 [20921,1249295],q 3 [4096,20921,1249295],q 2 [4224],q 0 [12290,14797],q 3 [20984,1114122],q 1 [20495,176957],q 2 [8194,176957],q 3 [20490],q 2 [16394,131915],q 2 [8320,22955],q 0 [12290,8320,22955],q 3 [12290,8320,22955],q 16 [22955],q 1 [16557,2187279],q 0 [8194,16557,2187279],q 9 [2187279],q 1 [12729,16866],q 0 [12729,16866],q 2 [20488,32898],q 1 [16397,516271],q 4 [16397,516271],q 0 [8194,16397,516271],q 2 [8194,516271],q 3 [8194,516271],q 3 [20482,8198],q 1 [8198],q 2 [16386,20482],q 1 [17449,22562],q 4 [12290,49156],q 1 [21547,18233],q 2 [8192,21547,18233],q 4 [18233],q 3 [20495,851979],q 3 [13129,946176],q 3 [12290,20489,49167],q 8 [20484],q 9 [20484],q 1 [20484,16397],q 2 [20484,516096],q 1 [12297,20493],q 0 [16397,516607],q 3 [20484,516607],q 1 [20484,16397,516607],q 5 [20490,17017],q 1 [16513,8196],q 2 [16513,8196],q 3 [12290,8196],q 0 [16393,20493,402172],q 1 [16393,20493,402172],q 2 [16393,402172],q 3 [20493,402172],q 3 [12294,24591],q 2 [8198,20986],q 3 [13129,20493],q 1 [16394,13129,20493],q 0 [20489,20497],q 3 [516105,1376271],q 1 [20653,1962003],q 0 [8194,20653,1962003],q 9 [1962003],q 2 [8194,20653,1962003],q 3 [8194,20653],q 2 [8198,401408],q 0 [16386,20729],q 2 [16386,20729],q 2 [8198,401427],q 3 [8198,20493],q 3 [8198,24851],q 3 [8198,24576],q 1 [20700,8196],q 3 [20700,8196],q 2 [401425,794624],q 3 [20493,794624],q 3 [8198,24579],q 2 [20488,32770],q 1 [20488,16397],q 0 [251,21337],q 1 [12294,21337],q 5 [21337],q 2 [251,21337],q 3 [12294,251,21337],q 3 [12294,251],q 13 [20491],q 0 [251,20497],q 8 [8221],q 2 [251,20499],q 9 [20499],q 2 [8441,16650],q 3 [20985,794627],q 0 [16633,258048],q 2 [16633,258048],q 2 [16633,20490],q 13 [20490],q 3 [20495,851968],q 3 [20985,794635],q 0 [20731,2633730],q 2 [20731,2633730],q 1 [8321,16698],q 0 [20731,18957],q 2 [20731,18957],q 3 [12294,20731],q 5 [16393,782336],q 4 [782336],q 2 [16393,782336],q 3 [20488,2109455],q 10 [2109455],q 1 [20488,16417,2109455],q 0 [16393,21244,1568781],q 3 [12294,21321],q 3 [12290,24584],q 1 [20488,20489,49159],q 3 [20488,20489,49159],q 1 [4699,8793],q 2 [20480,4699],q 5 [16394,21323],q 1 [16394,21323],q 0 [16394,21323],q 3 [12294,21323],q 0 [20493,401851],q 1 [20493,401851],q 2 [4096,401851],q 2 [20480,16390,195],q 0 [16393,21245,786447],q 3 [21245,786447],q 10 [49152],q 5 [20491,663],q 4 [663],q 3 [12294,20491],q 2 [516104,1372162],q 3 [516104,1372162],q 12 [1372162],q 1 [16397,516104],q 3 [12294,24827],q 3 [12294,24576],q 3 [12294,24579],q 1 [12297,73948],q 2 [16386,73948],q 1 [8793,12889],q 0 [20480,8793,12889],q 0 [12298,20499],q 2 [4096,20499],q 3 [12294,24584],q 1 [16393,21247],q 2 [20486,16394,861285],q 3 [20486,861285],q 0 [195,13253],q 1 [16390,13253],q 3 [195,13253],q 0 [195,12297],q 3 [195,12297],q 0 [195,20489],q 3 [195,20489],q 3 [195,20491],q 3 [195,20495],q 0 [8385,2682880],q 2 [16390,8385,2682880],q 3 [8385,2682880],q 1 [16394,21365],q 3 [843,21365],q 4 [21365],q 2 [16394,843,21365],q 3 [8385,23102],q 2 [20497,171],q 0 [12481,20491],q 3 [12481,20491],q 1 [16390,12481,20718],q 0 [12481,20718],q 2 [16390,20718],q 1 [16390,20673,577551],q 0 [20673,577551],q 3 [20673,577551],q 8 [20488,32770],q 0 [20488,32770],q 0 [16386,20488,32770],q 15 [20488],q 1 [20488],q 2 [16386,20488,32770],q 0 [20675,2707458],q 3 [13129,21405],q 1 [16394,13129,21405],q 1 [20608,16989],q 2 [20608,16989],q 4 [16390,20675],q 1 [16390,20675],q 2 [16390,20675],q 3 [20675,12298],q 2 [20484,520322],q 0 [20675,2707469],q 1 [16390,20675,2707469],q 3 [20675,2707469],q 0 [12297,73923],q 4 [16390,73923],q 1 [16390,12297,73923],q 2 [16390,73923],q 2 [16390,20554],q 2 [16390,21353],q 0 [12297,16741],q 9 [16741],q 2 [73732,16741],q 0 [20488,32961],q 2 [16390,20488,32961],q 0 [20489,49347],q 4 [16390,49347],q 2 [16390,20489,49347],q 3 [20489,49347],q 3 [516106,516107],q 1 [16390,20489],q 2 [16390,20490,197241],q 4 [1757184],q 2 [16394,21321,1757184],q 2 [16394,21406],q 2 [4224,22991],q 0 [12290,22991],q 16 [22991],q 8 [12317],q 0 [16386,12405],q 2 [16386,8196],q 1 [20497,24704],q 2 [16633,20734],q 0 [20493,401603],q 2 [16390,401603],q 1 [16985,12294],q 3 [20480,12294],q 2 [16390,848065],q 0 [520194,14281],q 1 [20484,14281],q 3 [20484,520194,14281],q 0 [520194,18377],q 1 [20484,18377],q 2 [20484,520194,18377],q 0 [8701,524288],q 2 [20484,8701,524288],q 3 [20484,8701,524288],q 0 [8701,16394],q 1 [20484,8701,16394],q 10 [606208],q 0 [12797,12297],q 1 [20484,12797,12297],q 9 [20484,12797],q 1 [12297,16457],q 0 [12797,16397],q 1 [20484,12797,16397],q 0 [12797,16977],q 10 [16977],q 1 [20484,12797,16977],q 2 [20484,16978],q 1 [20489,16817],q 2 [20489,49152,16817],q 9 [16817],q 4 [49152,16817],q 4 [20495,831],q 2 [8196,831],q 1 [20484,16893,12297],q 0 [16893,12297],q 3 [20484,12297],q 1 [20497,4127],q 1 [20497,4124],q 3 [24576,4124],q 0 [16893,16393],q 1 [20484,16893,16393],q 2 [20484,16893,16393],q 0 [16893,20493],q 1 [12509,21666],q 0 [16386,12509,21666],q 4 [16458,20849],q 1 [12297,16458,20849],q 9 [20849],q 0 [16893,634888],q 3 [21246,13221],q 0 [16893,634891],q 5 [634891],q 3 [20484,634891],q 2 [20484,16893,634891],q 1 [20484,16893,20489],q 0 [16893,20489],q 3 [12290,20484,520194],q 0 [16893,16397],q 3 [20484,634895],q 10 [634895],q 0 [16893,634895],q 4 [20552,17201],q 9 [17201],q 2 [20554,17621],q 0 [16393,782847],q 2 [20484,16393,782847],q 0 [16394,521033],q 3 [20484,521033],q 0 [20497,25087],q 2 [20484,20497,25087],q 1 [16825,466959],q 0 [16825,466959],q 0 [1127,14193],q 1 [20486,14193],q 5 [14193],q 2 [20486,1127],q 0 [12481,20489],q 3 [12481,20489],q 0 [1127,20493],q 1 [20486,20493],q 4 [20486,1127],q 3 [20486,9317],q 4 [4759],q 2 [20486,1167360],q 0 [13413,17525],q 2 [20486,17525],q 3 [20486,13413],q 2 [20486,17526],q 0 [17509,1495040],q 3 [20486,1495055],q 0 [12297,74855],q 4 [20486,74855],q 1 [20486,12297,74855],q 2 [20486,74855],q 4 [73728],q 2 [20486,73728],q 2 [401408],q 2 [20486,401408],q 1 [20486],q 2 [20497,25407],q 0 [20497,1131],q 1 [12297,16937],q 4 [73728,16937],q 0 [12297,73728,16937],q 9 [16937],q 2 [73728,16937],q 1 [20609,16390],q 12 [20609],q 2 [20609,16390],q 5 [12290,20609],q 1 [20491,20493],q 2 [73728],q 2 [73728,16458],q 2 [73732,20554],q 0 [8194,16893],q 2 [20489,20552],q 3 [12297,20489,20552],q 3 [12297,20490,20493],q 0 [12297,20490,20493],q 2 [20490,16458],q 2 [20488,20489,20497],q 1 [12297,20493,401416],q 1 [12889,20497],q 0 [20480,12889,20497],q 2 [20480,20497],q 2 [20488,516107],q 3 [20488,516107],q 2 [4096,20490,20491],q 2 [16457,21826],q 3 [12297,21826],q 2 [16458,371],q 4 [16458,371],q 9 [371],q 3 [12297,371],q 4 [16458,20850],q 1 [12297,16458,20850],q 2 [16458,20850],q 2 [16458,20499],q 1 [12298,20497],q 2 [875,20497],q 3 [12298,875],q 3 [20488,20489,20493],q 1 [20493,20499],q 2 [401408,20499],q 2 [20552,835586],q 15 [24591],q 2 [20552,74547],q 3 [12297,20552,74547],q 0 [12297,20552,74547],q 12 [516102],q 4 [16397,516102],q 0 [20599,13577],q 4 [13577],q 3 [8196,20599,13577],q 1 [8196,20599,13577],q 2 [401419,1355],q 2 [20554,1239],q 1 [12297,20554],q 4 [20554,1239],q 9 [1239],q 3 [20486,1127,12297],q 0 [1127,12297],q 1 [12297,20555],q 2 [20555,2831],q 4 [20555,19213],q 2 [20555,19213],q 3 [12297,20555],q 2 [20486,20499,1188965],q 0 [12297,20497,24579],q 3 [12297,13449],q 2 [20499,74891],q 3 [12297,74891],q 1 [12298,18125],q 4 [18125],q 2 [875,18125],q 0 [12298,875],q 2 [875,20499],q 4 [19237],q 2 [21355,19237],q 3 [12298,21355],q 3 [24582,1131],q 0 [12298,17257,2195456],q 3 [12298,2195456],q 2 [17257,2195456],q 3 [12298,22626],q 4 [22626],q 2 [17257,22626],q 0 [12298,21353,1048576],q 3 [12298,21353,1048576],q 0 [12298,21355,2920450],q 4 [2920450],q 2 [21355,2920450],q 3 [12298,21355,2920450],q 3 [12298,24591],q 1 [16393,13245],q 4 [782336,13245],q 0 [16393,782336,13245],q 9 [13245],q 3 [782336,13245],q 0 [12297,74239],q 2 [20484,74239],q 1 [16393,21437],q 3 [782336,21437],q 2 [16393,782336,21437],q 0 [16393,782336,21437],q 2 [16393,20490,782971],q 0 [16393,20490,782971],q 3 [20490,782971],q 1 [20489,12721],q 4 [49152,12721],q 0 [20489,49152,12721],q 9 [12721],q 3 [20489,49152,12721],q 0 [12290,17509],q 3 [12290,20486],q 3 [782351,21802],q 2 [20482,16394],q 2 [4224,22989],q 0 [12290,22989],q 16 [22989],q 0 [16393,782779],q 1 [16393,782779],q 3 [4096,782779],q 4 [4096,782779],q 2 [4096,16393,782779],q 3 [12297,24580],q 2 [16393,783167],q 3 [20495,783167],q 3 [8192,25643],q 2 [8192,20497,25643],q 2 [16393,21244,1568770],q 9 [1568770],q 4 [21244,1568770],q 1 [16393,21246],q 2 [16393,21246,935],q 9 [935],q 4 [21246,935],q 3 [20986,21949],q 1 [16397,20986,21949],q 1 [16394,20493],q 3 [843,20493],q 0 [16394,843,20493],q 0 [251,17241],q 1 [12294,17241],q 2 [251,17241],q 0 [16394,13129,20489],q 3 [13129,20489],q 0 [20599,17673],q 4 [17673],q 2 [8196,20599,17673],q 1 [16397,21525],q 3 [516096,21525],q 2 [516096,21525],q 0 [16394,13129,21406],q 1 [16394,20489,49995],q 3 [20489,49995],q 2 [401416,1142786],q 12 [1142786],q 0 [20493,401416,1142786],q 1 [16394,20489,49156],q 1 [12889,20489],q 0 [20480,12889,20489],q 3 [20493,402251],q 1 [16394,20493,402251],q 3 [20490,20491,12949],q 2 [16394,401408],q 0 [12290,16893],q 16 [20484,16893],q 2 [16394,401427],q 0 [9317,20490],q 2 [20486,9317,20490],q 1 [20486,9317,20490],q 3 [20486,9317,20490],q 3 [20495,848713],q 2 [16394,848713],q 1 [16394,20495,848713],q 2 [16394,831],q 1 [20488,14653],q 4 [14653],q 3 [20488,32770,14653],q 3 [20488,12321,36868],q 4 [16422],q 2 [20488,16422],q 1 [20488,12321,16397],q 2 [401412,17441],q 2 [20488,20515,17045],q 3 [20488,20515],q 1 [16397,516105],q 2 [516105],q 1 [20493,17125],q 2 [401408,17125],q 4 [1048595],q 2 [21353,1048595],q 2 [8198,17213],q 3 [8198,20495],q 0 [12729,20961],q 1 [12729,20961],q 5 [20961],q 2 [4096,20961],q 3 [4096,12729,20961],q 8 [20488],q 0 [20488],q 0 [12297,20837],q 2 [73732,20837],q 3 [12297,73732,20837],q 1 [20488,20493],q 3 [20488,20493,401408],q 3 [12290,21246],q 0 [16393,21246],q 3 [20488,24576],q 3 [20488,12321,36870],q 3 [20488,24611],q 2 [20488,20497,24611],q 2 [401412,1081346],q 0 [20493,1081346],q 0 [16393,782351],q 1 [16393,782351],q 2 [20489,49152,49159],q 3 [20489,49152,49159],q 2 [20489,49156,20499],q 2 [4096,16866],q 2 [20489,20491,17045],q 3 [20489,20491],q 2 [20480,622596],q 10 [622596],q 1 [12889,622596],q 3 [20489,20493,49167],q 4 [20499,50315],q 2 [20489,20499,50315],q 1 [20490,18549],q 2 [20490,635,18549],q 4 [18549],q 1 [8795,16985],q 3 [20480,8795],q 0 [20480,8795,16985],q 5 [20480,8795],q 2 [20480,8795],q 1 [20490,16397],q 10 [635],q 1 [8793,20486],q 0 [20482,20490,20491],q 2 [20482,20490,20491],q 3 [20482,20490,20491],q 1 [20490,20493],q 3 [20490,635,20493],q 3 [20490,12921,20493],q 0 [20490,12921,20493],q 2 [20490,18369],q 4 [18370],q 2 [20490,18370],q 0 [20490,17017,2146304],q 3 [20490,2146304],q 2 [20490,17017,2146304],q 1 [16397,9239],q 2 [516096,9239],q 0 [16397,516096,9239],q 1 [20486,177253],q 0 [8194,177253],q 4 [20486,177253],q 2 [8194,20486,177253],q 0 [20490,20491,663],q 2 [20490,20491,663],q 3 [20490,20491,663],q 5 [20499,1163],q 4 [20499,1163],q 2 [20490,20491,17045],q 10 [16393,782351],q 3 [782351,20495],q 2 [20490,20491,20497],q 1 [20490,20491,20497],q 3 [20486,1127,20489],q 3 [20490,20493,401408],q 3 [20490,24576],q 3 [21323],q 3 [12290,21323],q 3 [20490,24587],q 1 [20491,18025],q 4 [663,18025],q 0 [20491,663,18025],q 9 [18025],q 2 [20491,663,18025],q 0 [275,13765],q 1 [8198,13765],q 9 [13765],q 3 [8198,275,13765],q 4 [275,13765],q 1 [20491,12949,16397],q 1 [20654,20909],q 4 [20654,20909],q 0 [8194,20654,20909],q 2 [8194,20654,20909],q 3 [8194,20654,20909],q 10 [679936],q 3 [20985,794639],q 3 [20491,679951],q 10 [679951],q 4 [17045,679951],q 0 [20491,16397,516759],q 1 [20491,16397,516759],q 2 [20491,516759],q 1 [20609,20484],q 2 [20609,20484],q 1 [20489,20497],q 8 [20490],q 2 [20490,20497,24576],q 2 [20491,20497],q 3 [20486,12297],q 0 [17509,12297],q 8 [9237],q 1 [16397,9237],q 1 [20652,19381],q 4 [20652,19381],q 0 [8194,20652,19381],q 2 [8194,20652,19381],q 3 [8194,20652],q 1 [16397,516106],q 0 [16397,516106],q 5 [16397,516106],q 0 [8441,270336],q 2 [8441,270336],q 3 [12294,8441,270336],q 3 [516104,516105],q 0 [8192,521257],q 1 [20484,521257],q 2 [8192,20484,521257],q 2 [516105,1376256],q 4 [16397,1376256],q 4 [16397,1376275],q 1 [16397,516105,1376275],q 2 [516105,1376275],q 2 [516106,2323],q 3 [516106,2323],q 3 [516107,20493],q 0 [12290,16501],q 1 [16397,20984,517187],q 2 [20984,517187],q 3 [20984,20985],q 1 [16397,20984,20985],q 3 [24585,786436],q 0 [20755,17689],q 4 [20755,17689],q 9 [17689],q 2 [8198,20755,17689],q 2 [9021,2011136],q 2 [20985,794635],q 12 [20985],q 4 [16657,20493],q 0 [16657,20493],q 1 [20493,8933],q 2 [401408,8933],q 1 [20493,8935],q 2 [401408,8935],q 0 [20755,1335298],q 4 [20755,1335298],q 9 [1335298],q 2 [8198,20755,1335298],q 1 [16394,861081],q 0 [20482,16394,861081],q 3 [20482,861081],q 2 [20482,16394,861081],q 2 [16458,368],q 2 [401408,401414],q 1 [20493,20495],q 5 [20493,20495],q 0 [20493,20495],q 2 [16390,20491,676033],q 1 [20493,401417],q 3 [20490,20491,20493],q 1 [20490,20491,20493],q 3 [20493,401416,401417],q 2 [401416,401417],q 2 [401417,1232915],q 2 [401418,1359],q 3 [20493,401418,1359],q 3 [20493,401418,401419],q 2 [20497,401427],q 2 [20499,402571],q 3 [24576,8221],q 0 [20497,24576,8221],q 1 [20495,18665],q 2 [831,18665],q 10 [18665],q 1 [20654,16813],q 4 [20654,16813],q 0 [8194,20654,16813],q 2 [8194,20654,16813],q 3 [8194,20654],q 0 [20497,24576,8222],q 0 [20482,12405],q 2 [20482,8196],q 0 [12290,20490,20491],q 3 [12290,20490,20491],q 1 [20497,8223],q 0 [16501,16397],q 3 [13449],q 2 [20499,9353],q 3 [9353],q 1 [20499,5259],q 3 [5259],q 0 [20499,1163],q 3 [1163],q 3 [24589],q 3 [24586],q 3 [24580],q 1 [20495,4927],q 2 [4927],q 0 [20495,831],q 2 [831],q 2 [401427],q 2 [401417],q 2 [20987],q 3 [20987],q 2 [20986],q 2 [20984],q 3 [20984],q 3 [516107],q 2 [516107],q 0 [16397,516107],q 2 [516102],q 2 [516100],q 2 [516098],q 2 [516096],q 3 [516096],q 0 [20491,663],q 2 [20490,20499],q 0 [20490,20499],q 0 [20490,20497],q 1 [20490,20497],q 3 [24585],q 2 [20489,20499],q 0 [20489,20499],q 0 [20489,16397],q 1 [20489,16397],q 1 [20491,4759],q 1 [16394],q 2 [516106],q 3 [13129],q 3 [843],q 0 [16394,843],q 3 [21247],q 3 [20489,20493],q 0 [16393],q 3 [21246],q 2 [16393],q 3 [516105],q 3 [782351],q 2 [20480,20486],q 1 [8795],q 0 [20480,8795],q 1 [8793],q 0 [16386,12298],q 15 [12298],q 3 [20700],q 1 [16393],q 2 [4096,16393],q 2 [20480,603],q 1 [8413],q 2 [16386,8413],q 3 [8413],q 1 [4699],q 0 [12290],q 2 [20554],q 4 [20653],q 0 [8194,20653],q 1 [20653],q 2 [20482,9113],q 1 [9113],q 0 [20753],q 0 [12290,20488],q 1 [5016],q 1 [20701],q 0 [16386,20488],q 1 [20608],q 0 [12290,20608],q 3 [516104],q 1 [12509],q 0 [12290,20491],q 0 [8441],q 4 [4271],q 1 [4271],q 2 [8194,4271],q 1 [20486,16393],q 2 [20486,16393],q 6 [],q 1 [20655],q 4 [20655],q 0 [8194,20655],q 3 [8194,20655],q 0 [16397,20984],q 5 [16394],q 0 [16394],q 0 [8194,20497],q 2 [20480,16393],q 0 [20480,16393],q 1 [20486,20489],q 1 [8322],q 1 [13353],q 1 [16514],q 1 [20499,9355],q 0 [20499,9355],q 2 [20499,9355],q 3 [9355],q 0 [20482,20490],q 2 [20482,20490],q 2 [401410],q 4 [782340],q 1 [16393,782340],q 2 [16393,782340],q 3 [782340],q 1 [12889],q 0 [20675],q 3 [20675],q 0 [16825],q 2 [401416],q 16 [20489],q 0 [12290,20489],q 0 [20921],q 1 [20921],q 1 [17449],q 3 [8192,21547],q 2 [8198,20497],q 0 [12797],q 2 [401418],q 3 [8192,20495],q 0 [8192,20495],q 1 [17306],q 2 [20489,20497],q 0 [1127],q 1 [21545],q 2 [20482,16393],q 0 [20482,16393],q 3 [20986],q 2 [8321],q 3 [20484,20489],q 0 [8192,20497],q 0 [20673],q 3 [20673],q 0 [12481],q 3 [12481],q 0 [16386,20490],q 15 [20490],q 1 [12462],q 0 [8194,12462],q 1 [16513],q 1 [16557],q 0 [8385],q 1 [16390,8385],q 2 [16390,8385],q 3 [8385],q 2 [20486,20497],q 1 [20486,20497],q 16 [16393],q 1 [20611],q 2 [20611],q 3 [12290,20611],q 2 [20555],q 1 [20652],q 0 [8194,20652],q 1 [20495,9023],q 0 [20495,9023],q 2 [9023],q 3 [24578],q 2 [16386,20484],q 2 [8194,16390],q 2 [4096,20491],q 0 [8194,16397],q 0 [20731],q 2 [20731],q 0 [12290,20490],q 1 [20654],q 0 [8194,20654],q 1 [13209],q 0 [20482,13209],q 0 [8194,20493],q 3 [8196,20493],q 1 [16558],q 0 [8194,16558],q 0 [8194,20495],q 2 [16514],q 0 [12290,16514],q 3 [20482,9115],q 1 [9115],q 3 [20482,20493],q 1 [20609],q 2 [20482,16390],q 0 [20482,12297],q 0 [9317],q 1 [20486,9317],q 2 [20486,9317],q 0 [118786],q 0 [16501],q 0 [275],q 0 [20482,20488],q 0 [20599],q 3 [8196,20495],q 1 [8196,20495],q 0 [20755],q 0 [195],q 3 [195],q 3 [24582],q 1 [12294,20491],q 3 [20484,20493],q 1 [5019],q 2 [20482,5019],q 1 [16390,20491],q 2 [16390,20491],q 3 [20482,20484],q 3 [20484,12298],q 2 [401414],q 0 [8633],q 2 [4096,8633],q 0 [8701],q 2 [20480,20490],q 0 [20480,20490],q 2 [20484,20497],q 0 [13413],q 0 [17509],q 3 [20488,20493],q 0 [16393,20493],q 1 [20490,12921],q 0 [12297,16457],q 2 [16457],q 4 [20552],q 2 [8192,20499],q 0 [20480,12298],q 2 [21355],q 0 [16657],q 1 [12298,20499],q 2 [20482,20489],q 3 [782336]]
def B_22_3 : BT (List (List Nat)) := BT.empty
lemma B_22_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 3 xs.toFinset) B_22_3 := .empty
def U_22_4 : List Nat := []
def P_22_4 : BT (Option BoundPool) := buildPoolsSubBT 12 W_22 r_22 S_22 ps_22 U_22_4
def N_22_4 : List NodeSpec := [([7,11,9,4,12],[],[]),([14,1,10,4,12],[],[]),([15,1,2,4,5],[],[]),([16,7,1,9,4],[],[]),([17,7,9,4,12],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_4 : checkNodesBT W_22 g_22 F_22 P_22_4 A_22 B_22_3 4 N_22_4 = true := by decide +kernel
def B_22_4 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_4
set_option maxRecDepth 500000 in
lemma B_22_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 4 xs.toFinset) B_22_4 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_3_ok C_22_4
def U_22_5 : List Nat := (r 0 9)
def P_22_5 : BT (Option BoundPool) := buildPoolsSubBT 12 W_22 r_22 S_22 ps_22 U_22_5
def N_22_5 : List NodeSpec := [([7,20,22,3,4,5],[0],[]),([26,25,1,3,4,5],[1],[]),([25,1,3,27,4,5],[1],[]),([28,7,1,3,30,5],[],[]),([13,7,1,9,4,12],[2,3],[]),([31,7,1,9,4,12],[],[]),([14,0,1,9,4,12],[2,4],[]),([0,1,9,34,4,12],[],[]),([33,7,1,9,4,12],[5,6],[]),([14,7,1,9,4,12],[2,3,7],[0]),([14,1,2,10,4,5],[],[0]),([35,7,1,3,4,5],[8],[]),([7,1,9,10,4,12],[7],[0]),([7,11,2,9,4,5],[],[0]),([17,7,2,9,4,5],[],[0]),([36,7,1,9,4,12],[],[]),([31,36,1,2,4,5],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_5 : checkNodesBT W_22 g_22 F_22 P_22_5 A_22 B_22_4 5 N_22_5 = true := by decide +kernel
def B_22_5 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_5
set_option maxRecDepth 500000 in
lemma B_22_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 5 xs.toFinset) B_22_5 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_4_ok C_22_5
def U_22_6 : List Nat := (r 1 4++[6]++r 9 117)
def P_22_6 : BT (Option BoundPool) := buildPoolsSubBT 12 W_22 r_22 S_22 ps_22 U_22_6
def N_22_6 : List NodeSpec := [([7,1,37,39,3,4,5],[],[]),([7,1,2,3,40,4,5],[9,10,11],[]),([7,1,2,41,3,4,5],[],[]),([42,7,1,2,45,4,5],[10],[]),([46,42,7,1,2,4,5],[12],[]),([47,7,1,24,3,4,5],[13],[]),([50,49,0,1,3,4],(r 14 7),[]),([52,54,0,1,2,3,4],[],[]),([55,56,49,0,1,3,4],([16,17]++r 21 4),[]),([33,0,1,9,4,12,6],[6,25],[0]),([13,58,1,2,9,4,5],[26,27,28],[]),e6 [61] [],e6 [65] [],([7,1,37,66,3,4,5],[],[]),([67,7,1,2,3,4,5],[],[]),([70,7,1,2,3,4,5],[],[]),e6 [72] [],([74,7,1,2,3,4,5],[10,29,30],[]),([75,49,0,1,3,4],[14,15,19,31,32,33],[]),([42,7,1,2,76,4,5],[9],[]),([77,7,1,2,3,4,5],[],[]),([7,1,37,78,3,4,5],[],[]),([7,1,2,79,3,4,5],[],[]),([7,1,2,3,81,4,5],[13,34],[]),([82,28,7,1,3,4,5],[35],[0]),([49,0,1,3,4,83],[14,15,16,36,37],[]),([42,7,1,2,84,4,5],[38],[]),e6 [87] [],([88,7,1,2,3,4,5],[],[]),([7,1,2,3,18,90,5],[39],[]),([91,7,1,2,3,4,5],[],[]),([91,94,1,2,3,4,5],[],[]),([7,1,2,95,3,4,5],[],[]),([91,1,2,3,21,4,5],[12,40],[]),e6 [99] [],([7,1,37,100,3,4,5],[],[]),([42,101,1,2,76,4,5],[41],[]),([103,7,1,2,3,4,5],[],[]),([106,108,104,2,3,4,5],[42,43],[]),([7,20,2,3,21,4,5],[12,44],[0]),([109,49,0,1,3,4],[14,19,30,33,45,46],[]),e6 [112] [47],([0,1,2,3,113,114,5],[48,49,50],[]),([7,1,2,24,3,116,5],[48],[]),([117,7,1,2,3,4,5],[],[]),([118,7,69,1,3,4,5],[],[]),([75,49,0,1,3,4,5],[14,51],[]),([0,1,2,3,119,90,5],[],[]),([7,1,2,3,121,4,5],[],[]),([122,0,104,123,2,3,5],[],[]),([49,0,1,3,4,124],[14,16,21,32,46,52,53,54],[]),([125,49,0,1,3,4,126],[21,30,55,56,57],[]),([129,7,1,2,3,4,5],[],[]),([7,1,2,130,3,4,5],[40],[]),([7,1,2,132,3,4,5],[],[]),([0,1,2,3,113,90,5],[58],[]),([55,49,0,104,3,4],[14,15,30,54,59,60],[]),([28,7,29,1,3,4,5],[10],[0]),([7,1,9,4,12],[3,33,61],[0]),([7,1,2,9,10,4,5],[13,30,62],[0]),([49,7,0,1,3,4],[15,16,17,21,30,46,55,63,64],[]),([133,49,0,1,3,4],[14,16,17,19,21,46,65,66],[]),e6 [135] [],([7,1,2,3,136,4,5],[9,10],[]),([137,7,1,2,3,4,5],[],[]),([14,7,1,2,9,4,5],[13,27,62,67,68,69],[0]),([55,138,1,2,3,90,5],[70,71],[]),([139,7,1,2,3,4,5],[],[]),([91,110,1,2,3,4,5],[72,73],[]),([7,1,2,21,51,4,5],[9,13,48],[]),([42,7,140,1,2,4,5],[],[]),e6 [143] [],([1,102,2,3,21,4,5],[9,13,40],[]),([144,0,1,2,9,4,5],[28],[]),([122,145,0,2,3,105,5],[74],[]),([62,46,7,1,2,4,5],[10],[]),([146,147,1,2,3,4,5],[75],[]),([7,1,2,3,76,4,5],[],[]),([7,1,2,3,149,4,5],[9,12,13],[]),e6 [154] [],e6 [157] [],e6 [139] [38],([146,159,1,2,3,4,5],[76],[]),([7,1,2,21,148,4,5],[9,48],[]),([7,1,22,3,19,4,5],[77],[0]),([160,7,1,2,3,4,5],[],[]),([7,1,2,3,10,4,5],[9,10,13],[]),([42,7,1,2,161,4,5],[10],[]),([7,1,2,161,4,5,98],[9,69,78],[]),([7,163,1,3,18,4,5],[13],[]),([164,7,1,2,3,4,5],[40],[]),([94,89,1,2,3,4,5],[33,79],[]),([7,1,24,3,113,4,5],[12,80,81],[]),([13,0,1,9,4,12,6],[25,33,82],[0]),([13,7,1,2,9,4,5],[17,27,67,68,69],[0]),([25,1,24,3,4,5],[1,12,30,48,83,84],[]),([33,7,1,2,9,4,5],[85,86],[0]),([0,1,2,9,34,4,5],[28],[0]),([49,167,0,1,3,4],([15,30]++r 87 7),[]),([28,7,1,37,3,4,5],[],[]),([91,73,1,2,3,4,5],[10,73],[]),([169,0,1,9,4,5,12],[4,94,95],[]),([0,1,2,3,51,171,5],[],[]),([0,1,9,173,4,5,12],[4,95,96],[]),([7,0,1,9,4,12],[2,3,4,6,15,25,30,63],[0]),([25,1,3,4,5],[1,48,61,97],[0]),([46,7,1,2,3,4,5],[],[]),([31,7,1,2,9,4,5],[],[0]),([36,7,1,2,9,4,5],[],[0]),([7,1,2,3,21,30,5],[9,13,98,99],[0]),([174,7,1,2,3,4,5],[29,33],[]),([7,1,2,21,9,4,5],[13,30,48,55],[]),([38,7,1,2,9,4,5],[55,100,101],[]),([146,91,1,2,3,4,5],[102],[]),([49,0,104,3,4,105],[14,15,30,33,46,59,103,104,105],[]),([0,104,175,9,4,5],[4,17,30,106,107,108],[]),([177,49,0,1,4],[17,30,109,110],[]),([14,0,1,2,9,4,5],[26,27,85,96,111],[0]),([7,1,2,3,178,4,5],[10,29,33,34],[]),([49,180,0,3,4],[14,17,30,112,113,114],[]),([49,181,0,1,3,4],[16,17,19,30,32,33],[]),([7,1,24,3,182,4,5],[84,115],[]),([101,1,2,3,184,4,5],[116,117],[]),([49,185,0,1,3,4],[17,19,30,33,118,119],[]),([49,7,1,3,4],[33,55,61,64],[]),([145,108,2,3,4,105,5],[74,120],[]),([186,32,49,0,1,3,4],[17,19,21,33,45,121,122],[]),([187,0,104,2,3,4,5],[43,123],[]),([122,106,0,104,2,3,5],[43],[]),([7,1,2,3,184,4,5],[10,13],[]),([32,7,1,2,9,4,5],[34,55,85,100],[]),([73,159,1,2,3,4,5],[],[]),([7,1,2,161,18,4,5],[9,13,48],[]),([147,73,1,2,3,4,5],[10],[]),([46,7,1,2,21,4,5],[12,40],[]),([7,1,2,188,21,4,5],[13,40],[]),([28,162,7,1,3,4,5],[124],[]),([7,1,2,3,21,190,5],[125],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_6 : checkNodesBT W_22 g_22 F_22 P_22_6 A_22 B_22_5 6 N_22_6 = true := by decide +kernel
def B_22_6 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_6
set_option maxRecDepth 500000 in
lemma B_22_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 6 xs.toFinset) B_22_6 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_5_ok C_22_6
def U_22_7 : List Nat := ([4,5,6,9,10]++r 12 6++[19,23]++r 26 5++[32,33,34,37,38,40,41,43]++r 45 4++[52]++r 54 4++r 59 5++r 67 4++[72,74,78,79,80,82,84,85,86,90,91,92,95,96]++r 98 4++[105,106,107,110,111,113]++r 115 4++r 120 4++r 126 919)
def P_22_7 : BT (Option BoundPool) := buildPoolsSubBT 12 W_22 r_22 S_22 ps_22 U_22_7
def N_22_7_0 : List NodeSpec := [([0,193,37,3,4,5],([15,17]++r 126 5),[]),([101,195,2,3,4,5],[15,41,131,132,133],[]),([196,1,2,3,4,5],[33,61,134,135],[]),([197,101,1,2,4,5],[33,136,137,138],[]),([101,193,2,3,4,5],([30,41]++r 138 5),[]),([198,7,0,1,3,4,5],[30,33,43,143,144,145],[]),([7,0,1,199,3,4,5],[13,33,96,146,147,148],[]),([197,7,0,1,2,4,5],[12,17,33,43,55,136,149,150,151],[]),([7,0,193,2,3,4,5],[12,17,33,43,55,127,139,152,153,154],[]),([7,0,1,37,24,3,4,5],[13,43,48,96,155],[]),e6 [200,24] [48,156,157,158],([198,7,1,3,4,5],[12,33,61,145],[]),([7,1,199,3,4,5],[13,33,148],[]),([7,202,1,2,3,4,5],[13,33,55,159,160],[]),([203,7,1,2,3,4,5],[9,10,12,13,15,40,55,100,161,162],[]),([203,1,2,3,4,5],[15,33,161,163],[]),([7,1,2,3,182,4,5],[9,13,48,61,101,115],[0]),e6 [154,150] [17,47,48,164],e6 [89,205] [33,48,158,165,166],([62,118,7,1,2,3,4,5],[9,12,13,167,168],[]),([7,140,1,2,3,4,5,6],[9,100,169,170,171],[0]),([7,1,2,3,45,4,5],[48,61,69,84],[]),e6 [118,206] [43,96,172,173],([62,49,0,1,3,4],[14,15,16,19,30,33,46,174],[0]),([42,7,0,1,2,21,4,5],[40,48,175],[]),e6 [209,208] [43],e6 [118,21] [43,61,176,177],([62,7,1,37,2,3,4,5],[9,13,167,178],[0]),e6 [211] ([61,72,158]++r 179 5),([0,104,2,3,4,124,5],([30,54,158]++r 184 4),[]),([212,213,0,1,2,3,5],([17,33]++r 188 4),[]),([0,1,37,66,3,4,5,6],[15,43,192,193],[0]),e6 [214,166] [15,48,194],e6 [215,166] [48],([7,1,2,216,24,3,4,5],[12,13],[]),([7,1,2,3,113,4,5],[9,48,61,80,100,195],[0]),([7,69,1,2,3,4,5,6],[9,100,196,197,198],[0]),u6 [97,98] [17,33,48,199,200,201],([7,1,2,3,19,4,5,6],[9,10,12,33,100,202,203],[]),([146,7,1,2,3,4,5,12],[9,12,33,48,204],[]),e6 [46,7] [17,48,96,100,205,206],e6 [217] ([48,61,180]++r 207 4),([218,110,7,1,2,3,4,5],([13,84]++r 211 4),[]),([0,1,219,220,3,152,4,5],[17,43,215],[]),([212,221,0,1,2,3,5],[33,216,217,218],[]),([222,7,1,2,3,4,5],[9,10,12,13,40,55,100,219],[]),e6 [223] ([47,48,61]++r 220 4),([32,0,1,9,4,5,12],[4,5,6,17,33,55,61,82,95,96,118,224],[]),([158,165,185,0,1,3,4],[17,33,180,225,226,227],[0]),([7,1,2,3,51,4,5],[13,48,61,228,229,230],[0]),([225,0,1,2,3,5],[33,231,232],[]),([7,89,1,2,3,18,4,5],[9,10,233,234,235],[0]),([42,110,7,1,2,3,4,5],[9,33,63,236,237],[]),([68,7,0,1,37,3,4,5],[126,157],[]),([162,7,0,1,3,18,4,5],[43,48],[]),e6 [51,227] [17,61,182,215,238,239],([7,0,104,2,3,4,5],([9,12,17,43,55,123,158,185]++r 240 6),[]),e6 [226,53] [33,48,182,246,247],e6 [53,228] [17,48,61,215,248,249,250],([44,162,1,3,4,5],[13,48,61,251],[0]),([42,44,7,1,2,3,4,5],[61,252],[0]),e6 [85,208] [15,48],e6 [229,89] [33,158,253,254],e6 [7,113] [48,80,192,195,255,256],e6 [106,12] [15,33,43,48,63,96,257,258],([101,1,2,183,3,4,5],([41,47,116]++r 259 6),[0]),([158,110,7,1,2,3,4,5],[9,13,63,265,266],[]),([101,1,199,3,4,5],[15,117,147,267,268],[]),([68,7,1,2,3,21,4,5],[9,12,197,269,270],[]),e6 [232,231] [48],e6 [233,214] [15,194],e6 [230,234] [48,63,271],e6 [235,51] [48],([7,1,2,3,76,4,5],[84,197],[]),([32,49,0,1,3,4],[16,17,19,30,32,33,121],[0]),([150,1,2,3,4,236],[15,48,272,273],[]),e6 [237,238] [33,48,274,275],([150,1,2,3,4,240],[30,48,276,277],[]),([241,150,1,2,3,18,4,5],[15,17,48,278,279],[]),([7,69,1,2,3,4,5],[9,12,13,40,61,100,197,198],[0]),([110,0,1,3,4,242,5,12],[63,280,281,282],[]),([150,1,2,3,4,243],[15,48,283,284],[]),e6 [37,244] [43,48,96,192,285],e6 [245,18] [33,43,48,286],([247,0,1,2,3,5],[17,63,287,288],[]),e6 [248,155] [43,158,289],u6 [170,51] [96,158,238,247,290],e6 [250,150] [17,96,291,292],([7,1,2,66,3,4,5,6],[12,33,293,294],[0]),([7,1,2,3,206,4,5],[9,12,13,33,40,100,295,296],[]),e6 [250,249] [17,199,291,297],e6 [251,238] [33,298],([0,1,8,3,4,124,12],([5,52,54]++r 299 6),[0]),([62,7,1,2,24,3,4,5],[9,12,48,167],[0]),([0,1,3,18,4,114,5,12],[33,305],[]),e6 [252] ([43,47,48,199,215]++r 306 5),e6 [254,148] [15,48,182,311,312],e6 [255] [17,72,96,158,313,314,315],e6 [76,238] [118,316,317],([62,118,101,1,2,3,4,5],[41,117,138,318,319],[]),e6 [114,256] [48,63,118],([0,104,2,3,4,238,5],([17,33,123,241]++r 320 5),[]),u6 [79,6] [15,43,325],e6 [253,43] [15,38,43,312,326,327],([212,0,1,199,3,5],[17,33,190,328],[]),([150,0,1,2,152,51,4,5],[48,215,238,329,330,331],[]),e6 [249,152] ([17,30]++r 330 5),([241,1,2,220,3,4,5],[15,279,335,336],[]),e6 [258] [30,43,48,96,199,337,338],([62,49,0,1,3,4,5],[14,15,16,30,33,46,61],[0]),([55,122,0,104,2,3,5],[33,43,185,243,339,340],[0]),([110,7,1,2,3,18,4,5],[9,12,48,63,214,233,341,342],[0]),([259,0,104,2,3,4,5,12],[15,33,43,187,343,344],[]),e6 [248] ([47,48,96,158,215]++r 345 6),e6 [262] ([61,215]++r 351 5),e6 [263,89] ([33,48,158,182,341]++r 356 4),([218,0,1,220,3,4,238,5],[331,360,361],[]),e6 [165,60] [15,43,48,61,362],([55,0,104,8,3,4,12],[15,54,301,363,364],[0]),([162,7,1,3,18,4,5],[12,13,40,48,61],[0]),e6 [264,265] [158,365],([49,0,1,3,4,6],[30,32,33,55,61,366],[0]),e6 [38,118] [43,61],e6 [62,267] [158,194,367,368],([13,0,1,9,4,5,12],[4,5,17,30,33,82,224,369,370,371],[0]),([268,49,0,1,3,4,12],[14,15,19,32,33,46,372,373],[]),([150,1,2,3,4,269],[30,48,374,375],[]),([261,1,2,152,4,5],[17,48],[]),([0,1,37,78,3,4,5,6],[17,43,192,376,377],[0]),([0,168,1,9,4,5,12],[4,5,15,33,95,224,378],[0]),e6 [271] [30,72,158,379,380,381],([7,1,2,131,3,4,5,6],[12,33,382,383],[0]),u6 [89,119] [158,384,385],e6 [126,273] [15,386,387,388],u6 [184,6] [17,173,389,390,391],([7,1,2,100,3,4,5,6],[12,13,392,393],[0]),e6 [32,274] [34,48,394],([275,0,9,4,5,12],[4,33,63,395,396,397],[]),e6 [276] ([17,47,48,215]++r 398 4),e6 [122,214] [15,38,194,402,403],([111,7,1,2,3,4,5],[9,10,12,13,40,63,404,405,406],[0]),([7,1,2,3,120,4,5],[9,12,13,48,63,407],[]),([125,49,0,1,3,4],(r 14 4++[19,30,32,33,46,57,408,409]),[0]),([32,0,1,2,3,30,5,6],([48]++r 410 4),[]),([7,195,2,3,4,5],[9,61,414],[]),e6 [277,155] [48,158,289,415],([62,7,1,2,3,4,5],[30,33,48,416,417],[]),([185,0,1,279,280,3,4,5],[43,48,96,180,418],[]),([7,1,2,3,84,4,5],[48,61,69,84],[]),([49,110,0,1,3,4,12],([14,33,46,63]++r 419 4),[]),e6 [249,153] [17,30,48,291,330,423,424],([281,49,0,1,3,4],[14,15,17,30,32,33,46,63,96,425,426,427],[]),([7,1,102,2,3,4,5],[13,40,48,61,100,428,429],[0]),([110,7,1,2,3,4,5,12],[9,12,13,33,61,63,69,187,430,431,432],[]),([7,283,1,2,3,4,5],[10,48,55,61,433],[]),e6 [121] ([43,63,96,199]++r 434 4),([213,0,195,2,3,4,5],[17,33,438,439],[]),([55,53,1,2,3,51,4,5],[17,47,247],[]),([218,0,1,2,3,114,5,6],[212,440,441],[]),([284,7,1,2,3,18,4,5],[12,13,40,233,342,442],[0]),e6 [286,43] [15,38,43,443],e6 [287,51] [61,96,238],e6 [223,51] [33,223],([7,1,2,3,244,4,5],[12,13,40,48,55,444,445],[]),([289,0,1,2,4,5],[17,33,446],[]),e6 [290,86] [15,61,215,447],([7,1,2,100,3,4,5],[12,30,48,84],[]),([185,1,2,120,4,5],[48,63,448],[]),([0,291,292,3,4,5],([48,63]++r 449 4),[]),([42,0,1,2,84,4,5,6],([17]++r 453 5),[0]),e6 [154] [17,33,96,164,182,458,459,460],([261,0,1,2,3,30,5],([15,33,96]++r 461 4),[]),e6 [42,80] [17,43,465,466],([7,1,2,66,3,4,5],[12,30,48,69,294,467,468],[0]),u6 [121,6] [63,434],e6 [293,51] [15,48,182,238,246],([185,1,2,270,4,5],[30,48,180,469,470],[]),([7,1,2,3,120,4,5,6],[33,63,471],[0]),([68,7,1,37,3,4,5],[30,197,472,473],[]),([7,1,2,3,84,4,5,6],[33,84,474,475,476],[0]),e6 [42,183] [17,158,390],([38,165,7,1,2,3,4,5],[12,55,61,477],[]),e6 [294,220] [43,331],([110,7,1,37,2,3,4,5],[9,13,33,63,478,479],[]),([49,0,104,1,3,4],[15,30,33,46,59,60,118],[]),e6 [218,111] [96,118,480,481],e6 [295] [30,72,158,482,483,484],([230,55,1,2,3,76,4,5],[30,485],[]),([62,42,101,1,2,4,5],([33,116]++r 486 5),[]),e6 [297] [43,72,96,158,215,491,492,493],e6 [298] ([17,33,43,63,96,182,421]++r 494 4),e6 [212,299] [70,72,216,498,499],([138,1,2,152,4,5],([48]++r 500 4),[]),e6 [200,244] [158,504,505],([7,1,2,3,161,4,5],[9,12,13,48,61,69,506,507],[0]),e6 [102] [13,17,48,61,199,428,508],e6 [255,231] [96,215,509],u6 [111,18] [43,48,63,481,510,511],u6 [60,12] [15,17,43,48,96,362,512,513],([0,1,8,3,4,83,12],[5,15,37,301,514,515,516],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_7_0 : checkNodesBT W_22 g_22 F_22 P_22_7 A_22 B_22_6 7 N_22_7_0 = true := by decide +kernel
def N_22_7_1 : List NodeSpec := [([32,7,1,8,2,3,4,5],[13,48,55,85,101],[0]),([300,1,2,3,4,5],[15,33,517,518,519],[]),([213,195,2,3,4,5],[17,33,439,520],[]),e6 [51,238] [33,48,521,522,523],([302,0,1,3,4,5],[17,61,524,525,526],[]),([68,7,1,2,3,4,5],[30,48,416,527],[0]),e6 [303,150] [96,528,529],e6 [304] ([43,48,96]++r 530 6),e6 [306] ([30,33,96,182]++r 536 4),([230,49,0,1,3,4],(r 14 4++[19,30,32,33,46,63,96,215]++r 540 4),[]),u6 [178,6] [17,33,100,182,481,544,545],([91,7,1,2,3,4,5],[9,10,12,13,61,100,546,547,548],[0]),([198,213,0,1,3,4,5],([17,33]++r 549 4),[]),([101,1,2,3,182,4,5],[41,47,61,116,117,553,554],[]),([307,13,0,1,2,9,4,5],[33,555,556,557],[0]),([150,1,2,3,4,308],[48,61,533,558],[]),([7,1,2,131,3,4,5],[10,12,40,48,63,84,559],[]),([49,0,104,3,4],[14,15,30,46,59,60,61,118,123],[0]),e6 [309,114] [33,48,61,560,561],e6 [310,51] [38],([7,1,2,3,18,4,5],[30,48,61,416],[0]),e6 [312,6] [48,118,562],([210,313,0,1,3,4,5,12],[63,96,563,564],[]),([158,73,7,1,2,3,4,5],[13,29,30,33,565,566],[0]),e6 [104,124] [158,567],([49,0,104,1,3,4,5],[14,15,32,33,46,118,123],[]),e6 [314,6] [48,100,194,568],e6 [315] ([17,43,72,96,158,430]++r 569 4),([33,0,1,9,4,5,12],[17,30,33,61,82,224],[0]),([230,62,1,2,3,4,134],[30,48,573,574,575],[]),u6 [81,6] [17,100,173,465,576,577],([230,0,1,9,4,12],[4,5,15,30,33,63,215,578,579,580],[]),([49,110,0,1,3,4],[14,17,30,33,46,63,419,422],[]),([316,7,1,2,3,4,5],[9,12,48,61,69,100,581,582],[]),e6 [317] ([17,47,48,199]++r 583 5),([7,1,2,78,3,4,5],[12,30,48,69,588],[]),([42,0,1,2,76,4,5,6],[456,511,589,590,591],[0]),([212,7,0,1,2,3,5],[33,61,216,218,499,592,593],[]),e6 [218,319] [17,96,118,594,595],([0,104,2,3,4,320,5],([33,43,123,158,240,322]++r 596 5),[]),u6 [7,9] [17,34,48,55,67,85,601],e6 [321,51] [15,48,215,238,602],([110,7,1,2,3,4,5,98],[9,33,34,61,63,69,603,604],[]),([122,145,0,104,2,3,4,5],[15,33,61,74,187,339,605],[0]),e6 [258,6] [30,48,100,337],e6 [32,323] [34,48,606],e6 [32,324] [34,48,607],u6 [278,76] [17,38,118,589],e6 [32,325] [34,48,608],([118,110,7,1,2,3,4,5],[9,33,63,609,610],[]),e6 [32,327] [34,48,611],([73,7,1,2,3,18,4,5],[9,12,13,40,48,233,234,342,507],[0]),([328,1,2,3,4,5],([48]++r 612 4),[]),([62,0,1,9,4,5,12],[4,15,33,61,95,118,224],[]),e6 [329,185] [17,180,616],([101,1,2,3,206,4,5],([41,47,116,117,138]++r 617 4),[]),([7,1,2,78,3,4,5,6],[12,33,621,622],[0]),([330,0,1,2,3,238,5],([30,48,215,274,324]++r 623 4),[]),([7,331,1,2,3,4,5],[9,10,13,61,84,100,627,628],[]),e6 [89,332] [30,33,158,341,629],([7,1,24,3,18,4,5],[12,13,30,40,48],[]),([7,1,2,80,3,4,5],[13,30,40,48,630,631],[0]),([7,1,2,3,76,4,5,6],[84,197,269,632,633],[0]),([92,138,263,1,2,3,4,5],[30,358,634],[]),([32,0,1,2,9,4,5,6],[17,55,86,100,635],[0]),([333,0,1,2,3,4],[17,33,636],[]),([42,43,7,1,2,3,4,5],[12,55,637],[0]),([32,49,0,1,3,4,5],[14,16,17,19,30,33,45,46,55,61],[]),([0,104,123,2,3,4,5,12],[15,43,187,638,639],[0]),e6 [7,182] [34,48,96,100,115,456],([7,127,1,2,3,21,4,5],[9,40,48,640],[0]),e6 [334,166] [34],([49,179,0,1,3,4],(r 14 4++[19,30,32,33,46,61,113,641]),[0]),u6 [64,12] [15,33,43,48,96,642,643],([337,0,1,3,4,5],[17,33,644],[]),([338,340,0,1,3,4,5],([17,30]++r 645 6),[]),e6 [341,12] [43,63,96,651,652],([62,162,7,1,2,3,4,5],[9,13,48,167],[]),([0,1,2,3,18,114,5,6],[33,48,342,440,511,561,653],[0]),([62,42,118,0,1,2,4,5],[609,637,654,655],[]),e6 [342] [43,47,48,96,215,656,657,658],([55,49,0,1,3,4,12],[14,16,19,30,33,46,54],[0]),([49,275,0,3,4,5],[30,33,46,63,118,659,660],[]),e6 [233,120] [17,30,61,661],([218,0,1,3,4,114,5,12],[96,118],[]),([7,1,2,3,113,18,4,5],[33,80,195,662],[]),([212,241,0,1,2,3,5],[17,33,218,663,664],[]),e6 [122,313] ([33,158]++r 665 4),([198,0,195,3,4,5],[17,33,669,670,671],[]),e6 [344,98] [17,33,48,63,199,672,673,674],([32,7,1,37,2,3,4,5],[13,48,101,675],[0]),([32,165,7,1,2,3,4,5],[12,48,55,101,676],[]),e6 [154,51] [96,215,238],([32,118,7,1,2,3,4,5],[12,13,48,101,677],[]),u6 [71,51] [17,38,48,238,678],([7,1,2,3,21,4,5],[30,48,61,417,527,679],[]),([185,1,2,346,4,5],[48,63],[]),([348,0,1,2,3,5],[17,30,680],[]),e6 [349,51] [70],e6 [350,185] [180,681,682],e6 [76,351] [118,157],e6 [185,343] ([48,70,158]++r 682 4),([230,1,2,3,4,352],[30,48,63,686],[]),e6 [7,183] [9,48,158,259],([55,49,0,1,3,4],[16,17,23,30,32,33],[0]),e6 [353,166] [17,43,687,688],e6 [354] ([17,199]++r 689 4),([7,1,2,3,30,5],[13,33,48,98,99],[0]),([7,1,2,3,270,4,5],[13,30,48,693],[]),([49,275,0,3,4],[30,33,46,118,659,660],[]),([213,1,199,3,4,5],[17,33,694],[]),([355,0,1,279,3,4,5],([17,30,61]++r 695 7),[]),([158,165,7,1,3,4],[13,33,55,69,702],[0]),([55,138,89,1,2,3,4,5],(r 703 5),[0]),([212,185,0,1,2,3,356,5],[48,708,709],[]),([55,0,1,2,3,18,90,5],[33,710,711,712],[0]),e6 [111,37] [43,96,126,192,713],u6 [51,134] [17,48,61,215,238,247,714,715],u6 [132,6] [43,716,717],([241,0,1,3,18,4,5,12],[15,43,63,718],[]),e6 [357,12] [15,43,48,96,158,187,719,720],e6 [358,12] [15,721],([122,49,0,1,3,4],[19,32,33,61,118,722,723],[]),([7,0,195,2,3,4,5],[33,61,131,414,724,725],[]),e6 [359] [43,47,48,96,726,727,728],([213,0,1,199,3,4,5],[17,33,694,729],[]),u6 [142,18] [43,48,730,731],([48,49,0,1,3,4],[14,15,17,19,30,46],[0]),([48,49,0,1,3,4,12],[14,15,30,37,46,61],[0]),([7,193,2,3,4,5],[9,12,55,153,154],[]),u6 [156,98] [17,33,48,199,216,732,733,734],([360,361,2,3,4,5],([63]++r 735 4),[]),([7,1,2,128,3,4,5],[12,40,48,61,84],[0]),u6 [93,89] [33,158,739,740,741],e6 [253,362] [33,48,182,312,742],([0,104,1,3,4,242,5],[280,281,743,744],[]),e6 [7,148] [17,34,48,311,745],([53,150,1,2,3,51,4,5],[17,47,61],[]),([0,1,2,3,204,4,363],[17,30,746,747,748],[]),([218,7,0,1,24,3,4,5],[13,84,118],[]),e6 [118,244] [43,48,96,173,749],e6 [364,155] [96,158,289,415],([91,7,1,2,3,18,4,5],[12,48,546],[]),([7,1,2,3,365,5],[48,55,61,750],[]),u6 [138,90] [33,70,703,705,706,710,751,752],e6 [92,366] [48,70,72,739,753],([367,212,0,1,2,3],[17,33,754,755],[]),e6 [368,18] [63,756,757],e6 [212,369] [15,38,157,216,499],([212,7,1,2,3,5],[33,61,593,758],[]),([7,29,1,2,3,21,4,5],[9,13,40,48],[0]),e6 [370,18] [43,72,759,760],u6 [89,113] [158,761,762,763],e6 [371,372] [33,48,61,215,764],e6 [42,111] [17,158,481,765],e6 [373,113] [72,158,761,766],([0,1,3,4,374,5],[30,767,768],[]),([158,165,167,0,1,3,4],([92]++r 769 8),[0]),([185,0,1,279,18,4,5],[17,61,777],[]),([185,0,1,2,204,4,98],[17,33,225,778,779,780],[]),e6 [200,113] [158,761,781,782],([42,68,7,1,2,3,4,5],[9,40,197,783],[0]),([185,0,1,2,9,4,5],([17,33,225]++r 784 4),[]),([290,0,1,2,3,332],[30,33,788,789],[]),([92,0,1,2,375,5],[17,30],[]),e6 [58,9] [15,48,85,182,555],([118,146,7,1,2,3,4,5],[9,12,13,100,168,197],[]),([94,1,2,3,18,4,5],[48,61,790],[0]),([38,7,1,37,2,3,4,5],[12,13,115],[0]),e6 [92,113] [30,61,791],([0,195,199,3,4,5],([15]++r 792 4),[]),([146,7,1,2,3,18,4,5],[9,12,48,234,796],[0]),([376,0,1,3,4,5],[33,55,61,797,798,799],[]),([7,1,24,3,18,4,5,6],[12,40,48,800,801],[0]),([91,7,1,2,3,4,5,6],[12,33,100,547,548],[]),([7,200,1,2,3,18,4,5],[9,12,33,802],[]),e6 [91,6] [43,47,453,546,547,548],u6 [91] [30,38,72,96,158,546,547,548],([185,0,104,2,3,4,5],[17,30,33,241,243,803,804],[]),([101,1,2,3,113,4,5],[30,41,47,116,256,805,806],[]),([275,0,2,3,4,124,5],([30,54,567]++r 807 4),[]),e6 [284,113] [30,47,48,255,811,812],([13,0,1,2,9,4,5,6],[33,556,557,601,813],[0]),([377,0,104,2,3,4,5],[30,43,54,123,158,187,240,322,814,815],[]),e6 [378,113] [47,48,256,816],([360,213,2,3,4,5],[17,48,817,818],[]),([146,7,1,37,2,3,4,5],[9,13,100,178,472,819],[]),u6 [52,53] [48,61,215,602],([355,1,279,3,4,5],[17,30,61,701],[]),([7,1,2,3,379,4,5],[13,48,61,820],[]),([218,73,7,1,2,3,4,5],[13,84,212,213,507,821],[]),([7,1,2,3,148,4,5],[13,30,48,101,822,823,824],[0]),e6 [381,166] [48,63,825,826],([218,146,7,1,2,3,4,5],[13,84,796,821],[]),e6 [382,9] [38,85,96],e6 [7,331] [13,38,96],([7,1,2,183,3,4,5],[9,13,30,40,100,197,827,828],[0]),([385,0,1,2,4,384,5],([17,215]++r 829 5),[]),([372,0,1,3,231,4,5,12],[834],[]),([82,7,1,2,3,21,4,5],[13,84,835],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_7_1 : checkNodesBT W_22 g_22 F_22 P_22_7 A_22 B_22_6 7 N_22_7_1 = true := by decide +kernel
def N_22_7_2 : List NodeSpec := [e6 [7,206] [9,48,511,617,836],([7,1,2,3,386,21,4,5],[61,640,837],[]),([92,94,1,2,3,18,4,5],[79,790,838],[]),e6 [372,387] [17,48,61,215,839,840,841],([212,0,1,2,231,5],[17,33,218],[]),e6 [388,231] [47,48,839],([7,140,1,2,3,4,5],[9,12,13,61,100,167,170,171],[]),([268,165,49,0,1,3,4],[15,33,90,372,842,843],[]),([49,108,0,1,3,4],[14,15,16,19,30,32,33,46,118,844,845],[]),e6 [389,231] [15,48,215,509,764],e6 [48,390] [48,158,846],([0,104,3,4,242,5],[15,61,118,281,744,847,848],[]),([13,0,1,2,9,4,391,5],[27,557,849],[]),([145,108,104,2,3,4,5],[15,30,43,120,185,187,605,850,851,852],[0]),([7,1,2,24,3,4,5],[30,48,61,417,527],[0]),([57,13,0,1,2,9,4,5],[27,556,557,853,854],[0]),([13,0,1,2,9,4,5,392],[215,855,856],[]),([33,0,1,2,9,4,5,6],[17,86,601,857],[0]),([158,165,7,0,1,3,4],([13,17,55,63,69,702]++r 771 4),[0]),([172,0,1,9,4,5,12],[4,15,33,61,95,224,858],[0]),([58,0,1,2,9,4,5],[26,27,28,33,86,96,111,215,555,556,859],[0]),([0,104,1,9,4,5,12],[4,15,17,33,95,224],[]),u6 [7,51] [17,48,100,238],([0,1,175,9,4,5,12],[4,5,17,30,33,61,82,95,860,861],[0]),([0,1,37,24,3,4,5],[13,30,126,155,192,456,862],[]),([338,85,0,1,3,4,5],([30,647,648,649]++r 863 5),[]),([56,0,1,9,4,5,12],[4,5,17,30,33,61,82,95,868,869,870],[]),e6 [203,7] [13,33,871],([0,1,9,4,12,6],[5,30,33,61,63,82],[0]),([394,0,1,2,9,4,5],[17,26,27,28,33,96,111,215,556,872,873],[]),([241,108,1,2,3,4,5,12],[15,43,666,874,875,876],[]),([395,0,1,9,4,5],[17,30,395],[]),([268,49,0,1,3,4,5],[14,15,17,32,33,46],[]),u6 [110,113] [48,63,158,761,762,877],([7,1,2,9,4,5],[13,33],[0]),u6 [86,6] [17,33,48,878,879],([7,0,1,2,9,4,5],[13,17,26,27,28,63,68,86,96,111,556,601],[0]),([261,0,1,2,9,4,5],[15,26,27,33,96,111,215,354,880],[]),([108,0,104,2,3,4,105,5],[74,120,258,881],[0]),([13,0,1,3,9,4,5,12],[17,96,224,370],[]),([118,7,1,2,3,21,4,5],[12,61,177],[]),([73,7,1,2,3,4,5,12],[9,12,13,33,69,204,430,431,882],[0]),e6 [396,113] [30,72,158,761,762,883],e6 [307,13] [33,48,182,555,557],([198,101,1,3,4,5],[30,138,144,884,885,886],[]),e6 [397,148] [38,158,311],([0,1,2,3,18,90,5,6],[33,278,561,887],[0]),([218,7,1,24,3,4,5],[13,61,84],[]),([7,1,2,3,9,4,5],[13,33,48,55,62,67,101],[0]),e6 [37,206] [43,96,126,192],([268,49,0,1,3,4],[14,15,17,19,32,33,46,373],[]),([56,49,0,1,3,4],[16,17,19,30,32,33,61,888],[0]),([49,0,398,1,3,4],[15,17,19,30,33,46,889],[]),([101,1,2,3,76,4,5,6],[263,890,891,892],[0]),e6 [309,90] [30,33,703,893],([49,0,1,3,399,4],[14,16,17,30,33,46,894,895],[]),([7,1,37,2,3,21,4,5],[13,84,115],[0]),([49,0,1,3,4,176],[16,17,19,30,33,110,896],[0]),([7,0,1,2,3,30,5],[13,15,17,48,96,98,99,410,461,897],[]),([7,159,1,2,3,4,5],[9,10,13,55,898],[0]),u6 [88,6] [118,899,900],([186,49,0,1,3,4],[19,32,33,61,122,901],[0]),e6 [400] ([17,199,691]++r 902 4),([49,0,1,3,4,126],[16,17,55,56,61],[0]),([49,0,104,3,4,5],[30,33,59,60,61,118,123],[]),([56,49,0,1,3,4,5],[14,16,17,19,30,33,46,61,96,906,907],[]),e6 [367,369] [15,157],([55,1,2,3,401,4,5],[63,70,908,909],[]),([38,7,1,8,2,3,4,5],[13,48,55,67],[0]),([38,118,7,1,2,3,4,5],[12,13,177],[]),([49,0,1,3,4,98],[16,17,30,33,96,910],[0]),e6 [7,76] [84,100,118,157,197],e6 [309,241] [15,48],([185,0,1,8,3,4,12],([17,33]++r 911 4),[0]),([226,290,0,1,2,3,51,5],[17,61,182],[]),([7,1,8,3,4,12],[33,55,915],[0]),([213,1,2,402,3,4,5],[48,61,551,916,917,918],[]),([7,0,1,8,3,4,12],[5,13,15,17,55,63,301,302,304,915,919,920,921],[0]),e6 [403] [33,72,96,158,354,533,922,923,924],u6 [95,6] [43,925,926],([7,1,8,2,3,21,4,5],[13,30,55,67],[0]),e6 [108,105] [48,70,120,258,881,927],([197,7,1,2,4,5],[12,33,55,151],[]),([7,104,2,3,4,5],[9,12,55,244,245],[]),([0,1,406,3,4,5],[30,48,928,929],[]),e6 [222,7] [13,100,219],([106,0,104,2,3,4,5,12],[15,43,63,123,257,258,930],[0]),e6 [7,188] [17,48,100,931],([122,0,104,2,3,105,5],[33,105,243,932],[0]),e6 [122,145] [70,72,339,403,933,934],([407,0,1,2,4,98],[17,30,55,63],[]),([408,185,0,1,2,4,5],([17,30,913]++r 935 4),[]),([122,7,1,2,3,5],[12,33,55,431,939,940],[]),e6 [409,156] [17,48,199,941,942],([42,146,7,1,2,3,4,5],[9,40,48,100,167,783,943],[]),([28,7,1,2,3,4,5],[9,10,12,13,30,944,945],[0]),([122,7,0,1,2,3,5],[12,33,43,55,402,403,939,940,946,947],[]),([49,410,0,1,3,4],[30,33,90,91,118,842,843,948],[]),([49,0,411,1,3,4],[15,30,33,90,118,949,950],[]),([49,0,1,3,4,166],[30,33,118,948,951],[0]),e6 [380,167] [17,48,199,825,826],([165,7,1,2,3,21,4,5],[12,55,61,477],[]),([73,7,1,2,3,4,5,98],[9,33,40,69,507,758,952,953,954],[0]),e6 [51,412] [33,955],([185,0,1,2,4,272,98],[17,225,956,957,958],[]),([413,7,1,2,3,4,5],[9,10,12,13,33,61,100,101,959,960],[]),([42,68,101,1,2,3,4,5],[41,262,263,486],[0]),([198,213,1,3,4,5],[17,33,551,552],[]),([46,7,1,2,3,4,5,6],[13,84,206,961],[0]),e6 [122,120] [33,61,63,158,962],e6 [113] [30,47,48,158,963,964,965],([212,213,1,2,3,5],[17,33,188,189,191],[]),([7,1,2,3,19,4,5],[9,10,12,30,100,203,966],[0]),([361,195,2,3,4,5],[15,438,967,968,969],[]),e6 [118,111] [43,96,172,173,970],u6 [54,51] [17,215,971],([42,0,1,199,4,5],[17,33,972],[]),([361,1,199,3,4,5],([15,729]++r 973 4),[]),([62,0,1,231,4,5,12],[33,96,118,977,978,979],[]),([198,361,1,3,4,5],([30,549]++r 980 4),[]),([62,42,7,0,1,2,4,5],[10,654,655],[]),u6 [150,153] [47,48,330,984],([42,0,195,2,4,5],[17,33,985],[]),([212,0,195,2,3,5],[17,33],[]),([7,1,2,3,45,4,5,6],[252,986,987],[0]),([73,7,1,37,2,3,4,5],[9,13,33,479],[0]),([7,1,2,3,21,19,4,5],[12,13,270,988],[0]),([198,360,0,3,4,5],([17,33]++r 989 4),[]),([62,42,7,1,2,4,5],[10,33,783,943,993,994],[0]),e6 [51,414] [33,995,996],([212,42,0,1,2,5],[17,33,997],[]),([28,7,1,2,3,21,4,5],[12,13,944],[0]),([367,42,0,1,2,4],[17,33,998],[]),([146,7,1,2,3,4,5,98],[9,33,48,796,954],[0]),e6 [185,415] [15,180,682,695,999],([185,0,417,2,3,4,5],[17,61,1000],[]),([0,1,2,382,9,4,5],[26,33,85,96,111,1001],[]),([418,185,0,1,2,3,5],[17,33,61,1002,1003,1004],[]),([185,0,195,2,3,4,5],([17,61]++r 1005 4),[]),e6 [91,7] [38,43,100],([0,104,8,3,4,105,12],[15,105,301,363],[0]),([185,0,1,199,3,4,5],([17,61]++r 1009 4),[]),([68,118,7,1,3,4,5],[10,30,168,177,1013,1014],[0]),([198,185,0,1,3,4,5],[17,30,43,913,1015,1016,1017],[]),([0,417,279,3,4,5],([15,61,696]++r 1018 4),[]),([147,7,1,2,3,4,5],[9,10,12,13,40,61,100,1022,1023],[0]),([7,189,1,2,3,21,4,5],[9,10,270,1024,1025],[0]),e6 [419,420] [43,48,96,1026,1027],e6 [421,51] [47,48,248],e6 [422,208] [43,47,48,1026],([23,1,24,3,4,5],[12,13,30,48,61,84,1028],[0]),([7,1,2,24,3,21,4,5],[12,13,40,48],[0]),([7,115,1,2,24,3,4,5],[9,48],[0]),([145,0,2,3,4,105,5,12],[15,185,243,258,605,881,934],[0]),([46,7,1,2,3,4,5],[9,10,12,13,29,30,40,61,69,84,205,961],[0]),e6 [424] ([33,182,199]++r 1029 5),([7,1,2,3,188,4,5],[9,10,12,13,61,931],[0]),([162,7,1,2,3,21,4,5],[12,13,40,48,931],[0]),([425,7,1,2,3,21,4,5],[9,48,167],[]),([7,1,22,2,3,21,4,5],[12,13,1034],[0]),([55,0,1,2,3,18,365,5],[48,710,1035,1036,1037],[]),([7,1,2,39,3,4,5],[12,30,48,69,1038],[]),e6 [24,21] [13,17,40,43,48],([7,1,2,3,161,4,5,6],[63,78,507,1039],[0]),([118,73,7,1,2,3,4,5],[9,12,13,30,168,610],[]),([42,73,7,1,2,3,4,5],[33,63,237,507],[0]),([158,146,7,1,2,3,4,5],[9,13,33,48,566],[0]),([7,200,1,2,24,3,4,5],[9,12,48,197],[]),([7,1,37,24,3,4,5],[12,13,61,115,472,862],[0]),([118,7,1,24,3,4,5],[12,13,30,84,1013,1040],[]),([42,7,1,2,24,3,4,5],[12,13,55,61],[0]),([7,200,1,2,3,21,4,5],[9,33,802],[]),([28,7,1,2,3,4,5,6],[12,944,945,1041],[0]),([0,104,9,4,5,12],[15,17,30,33,61,95,106,107,123,364],[0]),([42,7,1,2,21,4,5],[40,61,943,993,1042],[]),([7,1,2,39,3,4,5,6],[12,13,1043,1044],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_7_2 : checkNodesBT W_22 g_22 F_22 P_22_7 A_22 B_22_6 7 N_22_7_2 = true := by decide +kernel
def N_22_7 := N_22_7_0 ++ N_22_7_1 ++ N_22_7_2
def B_22_7 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_7
set_option maxRecDepth 500000 in
lemma B_22_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 7 xs.toFinset) B_22_7 := by
  have hP := buildPoolsSubBT_sound (pdepth := 12) (W := W_22) (raw := r_22) (pspecs := ps_22) (used := U_22_7) S_22_ok
  have hm0 := checkNodesBT_mem (by decide) gp_22 W_22_ok hP A_22_ok B_22_6_ok C_22_7_0
  have hm1 := checkNodesBT_mem (by decide) gp_22 W_22_ok hP A_22_ok B_22_6_ok C_22_7_1
  have hm2 := checkNodesBT_mem (by decide) gp_22 W_22_ok hP A_22_ok B_22_6_ok C_22_7_2
  exact buildBucketsBT_of_mem (forall_append (forall_append (hm0) hm1) hm2)
def U_22_8 : List Nat := ([4,5,6,9,10,12,13,15,16,17,19]++r 26 5++[32,33,34,37,38,40,41,43,46,47,48,54,55,61,63,67,69,70,72,74,82,84,85,86,90,92,96,100,101,105,111]++r 115 4++[120,123,126,127,131,134,136,138,139,143,144,146,147,149,152,157,158,165,166,168,172,173,177,178,180,182,185,187,189,192,194,199,200,201,204,205]++r 211 6++[218,225,226,228,233,234,236,238]++r 240 4++r 246 5++r 252 5++[258,259,262,269,270,271,274,275,276,278,280,282,285,286,289,290,291,293,298]++r 301 5++[311,312,316,319,320,322,323,330,331,334,339,341,342,347,354,356,358,359]++r 361 5++[367,368,369,374,384,385,388,389,390,397,399,402,403,404]++r 410 4++[415,420,421,423,425,430,431,432,438,440,441,443,444,445,447,450,453,454,456,461,465,466,469,470,475,477,479,481,485,486,488,499]++r 501 5++[507,509,511,513,515,521,527,533,535,540,549,550]++r 553 5++[560,561,563,564,566,567,572,574,586,589,594,595,597]++r 599 5++r 605 5++[611,617,624,625,626]++r 629 4++[635,637,640,642]++r 645 5++[653,654,655,661]++r 665 4++[673,675,676,677,682,683,685,687,688,691,695,696,697,700]++r 703 4++[709,710,711,718,719,729,730,731,733,734,736]++r 739 5++[745,747,749,758,761,762,764,769,770,772,773,774,777,779,783,784,788,796,802,803,808,810,811,813,820,821,822,825,826,829,832,834,839,840,841,843,846]++r 850 4++[855,857,863,873,874,875,878,879,881,890,897,905,908,911,913,917,919,931,932,934,935,936,938,941,942,946,947,948,952,954,955,956,958,965,971,977,989,1000,1002,1003,1005,1006,1008,1009,1010,1012,1015,1016,1018,1025,1026,1027,1032,1035,1036,1037]++r 1045 2299)
def P_22_8 : BT (Option BoundPool) := buildPoolsSubBT 12 W_22 r_22 S_22 ps_22 U_22_8
def N_22_8_0 : List NodeSpec := [e6 [290,426] ([30,48,199]++r 1045 4),e6 [426,375] [17,47,61,215,1045,1046,1047,1049],e6 [426] [30,43,48,96,199,215,1045,1047,1048],([290,0,428,2,3,4,5],([17,30]++r 1050 5),[]),([367,0,1,2,3,4,6],[33,61,182,1055],[0]),([198,0,1,3,4,5,6],[17,30,33,143,144,192,1056,1057],[0]),([0,1,199,3,4,5,6],[33,146,147,173,1058],[0]),e6 [213,6] [17,33,48,61,100,134,173,192,389,453,511,1059],([213,1,2,3,4,5,6],[17,47,48,61,134,1059,1060],[]),u6 [42,118] [55,61,96,172,456,466,609,637,677,749],([0,1,2,3,4,429,6],[33,55,173,182,1061,1062],[]),e6 [430,6] [48,55,173,389,511,1063,1064],([430,1,2,3,4,5,6],[15,38,48,55,173,1064,1065],[]),([233,0,1,2,3,4,6],[30,33,43,55,182,1066],[]),([197,0,1,2,4,5,6],[33,55,136,192,1067,1068],[0]),e6 [431,6] [30,33,48,55,100,192,389,453,511,1063,1069,1070],([431,1,2,3,4,5,6],([30,33,38,48,55,100,192]++r 1069 4),[]),([0,1,37,3,4,5,192],[33,55,173,675,1073,1074,1075],[0]),u6 [182,6] [15,17,48,61,100,511,553,675,1076,1077],u6 [311,6] [17,30,48,70,173,215,285,389,511,1063,1078],([0,1,2,3,4,141,6],[33,48,61,158,182,1079,1080],[]),([290,101,1,2,3,5,6],([30,33]++r 1081 4),[]),([42,101,1,2,3,4,5],[30,41,47,55,61,116,117,466,486],[0]),([101,1,2,3,4,5,192],[30,33,55,116,262,1069,1085,1086,1087],[0]),([282,101,1,2,3,4,5],[15,41,55,1088],[0]),([7,1,2,3,4,5,6],[33,47,48,55,61,100,1089],[]),([290,7,0,1,2,3,5,6],[29,30,33,55,69,1081,1090,1091],[]),u6 [42,7] [9,13,17,30,40,48,55,61,199,236,456,466,637,655,783,1063],u6 [7,194] [10,33,34,40,61,101,134,456,1092],u6 [118,7] [9,12,13,30,48,61,96,168,172,173,177,609,677,749],e6 [201,7] [9,10,13,30,33,38,55,100,1085,1093,1094],u6 [7,192] [10,12,13,15,30,33,38,40,43,55,149,173,1069],u6 [7,37] [9,13,17,33,43,48,61,115,126,285,479,675,1095],u6 [7,200] [9,10,13,17,30,33,47,48,158,504,1096,1097],u6 [7,21,6] [40,48,640],u6 [21,6] [17,40,48,55,173,192,270,389,511,640,1025],u6 [7,24,6] [13,30,48,173,1098],([290,7,1,2,3,5,6],[29,33,55,61,69,1081,1099],[]),([42,7,1,2,3,4,5],[9,10,13,40,55,61,100,466,783],[0]),([7,1,2,3,4,5,194],[10,33,34,40,61],[0]),([118,7,1,2,3,4,5],[9,12,40,48,61,100,168,177],[0]),([201,7,1,2,3,4,5],[9,10,13,33,55,1085],[0]),([7,1,37,2,3,4,5],[9,13,33,48,61,100,115,178,285,479],[0]),([282,7,1,2,3,4,5],[9,55,61,356],[0]),([7,200,1,2,3,4,5],[9,10,33,48,61,100,504,802],[0]),([38,7,1,2,3,4,5,6],[9,10,13,29,40,48,55,69,1100],[0]),u6 [244,6] [48,55,100,173,192,389,444,445,505,511,1101],e6 [433] [17,30,38,72,199,1102,1103],e6 [434] ([17,33,47,48,55,199]++r 1104 5),([281,0,1,2,9,4,5],[15,17,26,28,63,111,1109],[]),e6 [436] ([15,61]++r 1110 5),e6 [369,6] [17,30,48,100,511,1063,1115,1116,1117],e6 [437] [30,43,48,158,1118],e6 [439] [33,43,96,158,1119,1120],e6 [393] [17,33,38,47,96,556,873,1121],e6 [440] [43,48,70,96,118,158],([207,7,1,2,3,4,5],[9,30,33,40,48,55,61,69,100],[]),([118,0,29,1,3,4,5],[30,43,61,72,118,173,609,1122,1123,1124],[]),e6 [48,441] ([17,48,96]++r 1125 6),([146,7,1,2,3,4,5],[9,10,33,48,796],[0]),u6 [7,29] [13,17,40,48,61,96,238,1131,1132],e6 [442] ([15,17,30,43,48,96,182,199]++r 1133 4),e6 [118,200] [17,33,48,96,158,172,173,504,609,1096,1097,1137],([7,29,1,2,3,4,5],[10,13,48,61,228,1132,1138],[0]),e6 [443,98] ([33,61,70,215,603,647,695,952]++r 1139 5),u6 [29,208] ([33,43,48,399]++r 1144 5),([0,1,2,4,384,5],[17,63,215,829,1149,1150],[0]),e6 [444] [17,33,47,48,61,199,1151,1152],u6 [261,29] [33,43,48,55,61,72,96,158,354,535,691,1131,1153,1154],e6 [71,218] ([96,118,211,212,441,905]++r 1155 6),e6 [18,238] [30,33,48,278,323,521,1161,1162,1163],([0,1,2,3,4,445,98],([61,158,647]++r 1164 4),[]),([0,29,1,405,3,4,5],([43,63,118,540]++r 1168 4),[]),([7,1,2,3,4,5,12],[9,10,12,13,29,55,69,204,1172],[0]),e6 [447] [17,33,38,43,47,1173,1174,1175],e6 [448,445] ([17,47,55,61,1165]++r 1176 4),e6 [449] [15,43,48,63,72,96,215,1180],e6 [448] [17,47,48,61,63,199,1177,1178,1181],u6 [52,51] [17,61,215,290,602,971,1182,1183],e6 [450] ([15,17,38,43,48,61,158,182,199]++r 1184 4),u6 [228,51] [17,33,61,238,248,971,1188,1189],e6 [451] [17,33,38,47,247,1190,1191,1192],e6 [452] [30,43,72,158,1193,1194],e6 [453] [48,61,118,158],u6 [85,98] [15,33,48,61,199,216,647,879,1195],e6 [85,126] ([15,17,48,61,63,182,199,879]++r 1196 4),e6 [454] ([17,61]++r 1200 5),e6 [455] ([15,33,48,1198]++r 1205 4),u6 [86] [15,33,61,96,182,447,878,879,1209,1210,1211],([201,118,0,1,3,4,5],[33,55,61,172,173,677,1212,1213,1214],[0]),u6 [84,6] ([17,30,61,118,182,192,215,389,454,456,511,1063]++r 1215 6),u6 [316,6] [17,30,48,61,100,192,215,511,1221,1222,1223],([230,0,1,8,3,4,12],[5,15,17,30,33,55,63,215,301,302,911,919,1224],[0]),e6 [282,7] [9,13,30,48,55,61,63,100,356],e6 [456] ([17,33,48,215]++r 1225 6),e6 [457] [15,17,33,63,158,182,199,540,1231,1232,1233],e6 [458] ([17,63]++r 1234 5),u6 [320,12] ([33,48,187,597,666]++r 1239 4),e6 [230,92] ([33,38,43,48,63,358]++r 1243 6),u6 [401] [33,63,96,908,1237,1249,1250,1251],e6 [459] [30,48,96,199],e6 [461] [43,63,96,1252,1253,1254],e6 [463] [17,33,158,182,1255,1256,1257],u6 [269] [43,61,72,158,1258,1259],e6 [464] [15,17,43,48,61,96,199,1260],([13,0,1,2,9,4,5],[17,26,28,33,85,369,556,557,855,1261,1262],[0]),e6 [465] [15,17,48,61,199,540,1263,1264],e6 [230,62,191] ([48,63,1136,1237]++r 1265 5),u6 [150,231] [17,33,96,118,331,1270,1271],u6 [113,18,6] [30,33,61,255,811],u6 [230,76] ([30,118,157,485,589,632]++r 1272 5),([230,85,1,2,3,4,5],[17,48,61,158,215,540,1145,1277],[]),e6 [466] ([15,33,118,158,182,199,215]++r 1278 5),u6 [145,12] [15,43,48,402,430,605,666,852,935],e6 [467] [15,17,48,61,158,199,540,1283],e6 [469] [30,34,43,48,63,96,158,182,1284,1285],u6 [97] ([17,30,38,43,48,61,182,199,200,201,215]++r 1286 4),e6 [62,468] ([30,48,63,158,194,1274,1285]++r 1290 5),([230,185,1,2,3,4,5],[17,30,48,63,1295,1296],[0]),([7,127,1,2,3,4,5],[9,10,30,48,61,100,822,1297],[0]),e6 [470,150,152] [48,330,1298,1299],e6 [471] ([17,30,33,43,70,72,158,199]++r 1300 4),([107,0,1,292,3,4,5],[15,48,63,540,1304,1305],[0]),e6 [472] ([15,30,48]++r 1306 6),e6 [473] [15,17,33,158,182,199,215,1312,1313,1314],([101,1,2,3,4,5,194],[30,33,116,117,134,262],[0]),([230,108,1,2,3,4,5],([30,43,48,72,1237]++r 1315 4),[]),([230,0,1,2,3,4,441],[30,47,48,96,540,1319,1320],[]),u6 [110,37,6] [33,63,126,173,285,420,511,1095,1321],e6 [474,59] [17,33,37,48,61,1322],([230,476,1,2,3,4,5],[15,30,47,48,63,158,1136,1323],[]),([158,32,165,0,1,3,4,5],[17,33,55,61,96,226,412,413,772,773,774,1324,1325],[0]),e6 [477] ([17,61]++r 1326 5),e6 [478] [33,43,96,158,199,1331,1332],([230,0,1,2,3,4,479],[15,43,47,48,1237,1333,1334,1335],[]),([404,0,1,405,3,4,5],[48,63,540,1170,1336],[0]),([43,7,1,2,3,4,5],[12,30,40,48,61,69,96,100,475],[0]),e6 [55,432] ([17,30,43,157,1103]++r 1337 6),e6 [158,114] ([17,48,63]++r 1343 4),u6 [185,29] [48,61,180,1347,1348],e6 [281,480] ([30,43,63]++r 1349 7),e6 [481] [17,33,47,48,1356,1357],([185,0,1,2,4,126,5,98],[17,61,199,216,709,1358],[0]),e6 [482] [15,30,33,158,1359,1360],e6 [21] [17,40,61,640,1025],([221,150,1,2,3,4,5],[33,48,331],[0]),e6 [158,155] [15,17,30,215,1361,1362],e6 [483] ([15,17,33,72,158,199,331]++r 1363 4),u6 [92,89] ([17,30,33,43,61,158,182,703,739,1247]++r 1367 4),e6 [484] [17,30,48,55,72,158,182,199,1371,1372,1373],u6 [390] [30,33,72,158,182,199,846,1374,1375,1376],([158,62,165,0,1,3,4,5],[15,33,61,96,574,772,773,774,1324,1377],[0]),e6 [485] [15,17,30,33,43,47,63,72,96,199,215,1378,1379,1380],([32,0,1,2,84,4,5],([15,34,48,118]++r 1381 5),[]),u6 [48,150,18] ([17,48,278,330,341,515,561,710,874,1127,1130]++r 1386 4),e6 [207,221] ([15,30,48,215]++r 1390 6),e6 [62,150,12] [15,330,666,1298,1386,1396,1397],u6 [150,294] [15,48,158,330,574,1386,1398,1399],e6 [150,445] [15,17,33,55,61,331,334,691,1165,1177,1400,1401],([207,0,104,2,3,4,5],[30,55,158,185,187,241,322],[]),u6 [29,423] [33,43,691,1032,1402,1403,1404],e6 [230,48,18] [30,48,61,63,278,515,1136,1387],e6 [486] [48,61,215,412,1405],([0,1,2,285,4,5,98],[17,33,63,199,695,1140,1406,1407],[]),e6 [62,383] ([17,43,63,118,194,1377]++r 1408 4),([44,7,1,2,3,4,5,6],[9,10,13,40,48,61,252,1412],[0]),u6 [238,12] [17,30,33,55,61,215,323,624,666,935,1163,1413,1414,1415],([0,1,2,3,238,191,5],[30,33,38,96,274,625,1416,1417],[0]),e6 [218,238] [33,48,61,118,212,274,323,624,1156,1163,1418,1419,1420],u6 [29,238] [33,48,624,1163,1419,1421,1422],u6 [325] [17,47,48,61,199,608,1423,1424],e6 [230,68,126] ([48,63,1136,1275]++r 1425 4),([230,0,104,2,3,4,5],[17,30,43,61,63,123,185,241,243,322,1136,1429,1430],[]),e6 [487,152] ([17,182,215,334]++r 1431 8),u6 [138,89] [30,43,47,48,158,703,706,710,739,1439,1440],u6 [150,51] [17,33,48,61,215,238,330,331,971,1441,1442],u6 [68,238] [33,43,48,157,274,323,589,624,1163,1419,1443,1444],u6 [7,18] [9,30,40,43,48,96,100,199,233,234,278,341,342],e6 [488] [17,33,38,1438,1445],e6 [71,62] [30,158,194,574,905,1157,1160,1267,1377,1446,1447,1448],([162,7,1,2,3,4,5],[9,10,13,40,48,61,931,1449],[0]),u6 [237,150] ([17,33,96,274,275,330,1386,1435]++r 1450 6),u6 [62,134] ([17,30,158,194,574,1267,1377]++r 1456 6),e6 [489] ([15,30,33,43,72,158,182]++r 1462 5),u6 [265,98] [38,61,199,365,603,682,952,1140,1467,1468,1469],e6 [490] [33,118,158,1470,1471],([230,62,150,1,2,3,4,5],[30,48,367,574,1472,1473],[]),([0,417,2,3,4,5,98],[43,61,695,1000,1018,1140,1474,1475],[0]),e6 [55,491] ([30,38,43,70,215,303,1392]++r 1476 8),e6 [158,238] ([17,30,33,215,323,624,1419]++r 1484 5),e6 [492] [15,30,1489],e6 [55,338] ([30,38,43,61,70,303,647,648,649,1482,1483]++r 1490 6),u6 [290,51] [17,33,48,61,215,238,247,971,1496,1497,1498],u6 [207,85] [15,33,48,63,215,879,1148,1392,1393,1499],e6 [493] [30,72,118,158,182,199,1500,1501],e6 [494] [33,118,158,1502,1503],e6 [495] [17,33,61,158,182,1128,1504,1505],e6 [55,446] ([33,38,43,54,70,118,215,676,1173]++r 1506 5),e6 [220,6] [33,192,215,331,456,511,1471,1511,1512,1513],u6 [226,51] [17,33,61,96,182,246,247,971,1514,1515]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_8_0 : checkNodesBT W_22 g_22 F_22 P_22_8 A_22 B_22_7 8 N_22_8_0 = true := by decide +kernel
def N_22_8_1 : List NodeSpec := [([431,1,2,3,4,5],[30,33,43,48,118],[]),e6 [55,496] ([30,38,48,70,96,1351,1482,1488]++r 1516 4),([0,1,2,4,208,5,98],[30,33,61,63,1520],[]),e6 [55,408] ([17,38,54,61,70,936,1482,1483]++r 1521 6),u6 [362,148] [17,33,311,742,1527,1528,1529],e6 [497] [48,61,63,96,158,695,1530,1531],([55,212,0,1,2,3,5,98],[17,33,61,216,682,1532],[]),u6 [53,51] [17,47,61,247,249,955,971,1533],e6 [498,6] [17,30,48,63,173,192,511,1063,1534,1535],([55,122,0,1,2,3,5,12],[30,33,43,54,402,947,1184,1536,1537],[0]),u6 [420,208] [33,43,399,1026,1144,1538],([48,218,0,1,3,4,5,12],([15,61,96,1127]++r 1539 4),[]),u6 [55,104,12] [33,43,185,187,243,430,666,1482,1537],([55,0,104,2,3,4,5,12],[30,43,54,74,123,185,240,241,243,322,666,1483,1543],[0]),u6 [55,9] [17,26,27,28,33,38,70,85,96,111,556,853,1351,1544],([55,212,0,1,2,3,5],[17,33,216,499,1143,1532,1545,1546],[]),([55,218,0,1,3,4,5,12],[61,96,441,935,1351,1539,1540,1542,1547,1548],[]),u6 [233,62] ([30,33,48,158,194,367,1267]++r 1549 4),e6 [500] [15,48,63,72,158,199,215,1553,1554,1555],u6 [416,185,98] [17,647,695,1556,1557],e6 [55,256] ([38,61,70,96,441,1351,1482,1483]++r 1558 6),([55,0,1,2,18,4,5,98],[30,33,61,647,695,1351,1564,1565,1566],[]),([55,138,1,2,3,18,4,5],[30,43,303,704,706,710,1247,1567,1568,1569],[0]),([150,0,104,2,3,4,5],[17,33,123,158,185,187,241,243,320,322,330,1386,1397,1570,1571],[0]),([230,0,1,2,3,4,305],[15,30,47,48,63,158,1572,1573],[]),e6 [501] ([33,63,158,182]++r 1574 5),([55,138,1,2,3,4,5],[30,43,48,61,704,705,706,710,1567,1568,1569],[]),e6 [502] [17,48,61,1579,1580],u6 [89,204] ([17,30,33,43,165,703,747]++r 1581 4),e6 [503] [17,33,47,48,55,1165,1585,1586],([55,0,1,2,3,365,5],[15,47,63,158,1035,1036,1037,1587,1588],[0]),([55,0,1,2,3,30,5],([17,33,96,461,897,1351]++r 1589 4),[]),u6 [347] ([17,30,33,43,72,158,182]++r 1593 4),e6 [55,62,12] [15,33,303,666,1267,1396,1446,1482,1543,1597,1598,1599],u6 [224] ([47,48,61,158,182]++r 1600 5),u6 [150,251] [15,33,96,298,331,441,1435,1605,1606,1607],e6 [504] [15,17,47,63,72,96,199,282,1608,1609,1610],([122,0,104,2,3,4,5],[33,61,118,185,187,241,243,339,932],[0]),e6 [55,66] ([30,38,43,70,293,303,1377]++r 1611 5),e6 [55,68,98] ([33,303,1140,1342,1482]++r 1616 6),u6 [142] [15,17,33,43,48,96,199,730,731],e6 [55,445] [17,33,55,61,70,96,691,1165,1177,1351,1482,1526,1622,1623],u6 [185,264] ([17,33,48,61]++r 1624 5),u6 [369,126] [15,17,61,63,157,182,199,1117,1199,1311,1425,1426,1428,1629,1630],([230,7,1,2,3,4,5],[38,47,48,55,61,1631],[]),([230,55,62,1,2,3,4,5],[30,33,48,367,574,1293,1632,1633,1634],[0]),e6 [32,68,6] [48,411,511,1116,1384,1635,1636,1637],e6 [487] [17,33,43,72,158,199,1431,1638],e6 [226] [33,38,47,96,199,1515,1639],([68,0,1,37,3,4,5,6],[15,17,33,43,126,173,675,1116,1640,1641],[0]),e6 [505] [17,182,1457,1642,1643],e6 [506] [17,1157,1644,1645],e6 [218,134] [61,118,211,441,1156,1457,1458,1459,1646,1647,1648],u6 [278,68] ([17,30,43,157,158,589,1617,1618]++r 1649 5),e6 [507] [17,1653,1654,1655],e6 [509] [15,38,43,63,118,182,199,1656,1657,1658],([7,1,2,3,4,5],[33,48,61,527,1659],[0]),([158,62,0,1,3,4,191,5],[15,33,96,118,1377,1632,1660,1661,1662],[]),u6 [122,104] [33,61,118,185,187,243,932,1184],([55,0,104,2,3,4,5],[17,30,43,61,74,123,158,185,240,241,243,303,322,1482,1663,1664],[]),u6 [68,351] ([17,30,70,157,589,1618]++r 1665 6),([145,0,104,2,3,4,5,12],[15,30,43,185,187,241,243,605,666,852,934],[0]),e6 [185,6] [48,70,173,180,192,225,913,1671,1672],e6 [510] [15,61,158,215,1390,1673,1674,1675],e6 [511] [17,33,43,48,1676,1677],u6 [220,238] [30,33,48,215,323,331,1163,1471,1513,1678,1679],u6 [32,200,6] [33,48,101,389,411,504,511],e6 [345] [30,34,43,48,96,158,413,1680],e6 [32,127,6] [48,101,511,1681,1682],u6 [278,18] [30,43,96,278,341,342,1649,1652,1653,1683,1684,1685],([32,7,1,2,3,4,5,6],[9,10,13,40,47,48,55,61,69,453],[0]),e6 [18,351] ([30,33,70,278,341,342]++r 1666 4++[1686,1687,1688]),([290,32,0,1,2,3,5,6],[30,55,215,413,1090,1091,1689,1690,1691],[]),u6 [156] [15,17,30,38,43,48,96,182,199,215,734,1362,1692],e6 [513] [38,43,48,96,158,215,1693,1694],([32,241,1,2,3,4,5],[15,17,33,48,158,411,718,1695],[]),e6 [514] ([30,33,43,48,158]++r 1696 5),([0,1,3,4,515,5,12],[33,55,63,911,1701],[]),e6 [418] ([33,38,43,47]++r 1702 4),([322,0,1,2,3,4,98],[17,33,199,215,1706,1707],[]),u6 [18,205] [30,33,165,166,278,1708],u6 [131,6] [15,33,63,182,192,456,511,1063,1280,1709,1710],e6 [266,208] ([30,399,1144,1146]++r 1711 4),u6 [185,12] [15,17,30,33,43,48,61,187,402,935,1536,1715,1716,1717],u6 [122,110] [17,33,43,63,158,560,661,932,947,1184,1718,1719],e6 [290,84] [15,30,43,118,215,454,1052,1216,1217,1218,1220,1720,1721,1722],e6 [516] ([15,33,158,215,1220]++r 1723 5),([0,1,2,152,4,126,5],[17,182,199,215,334,1438,1728],[0]),([32,261,1,2,3,4,5],[17,34,48,1729],[]),([62,0,1,8,3,4,12],[15,33,43,118,301,302,911,919],[0]),e6 [517] [17,33,43,61,96,199,1730,1731,1732],e6 [518] [17,30,33,72,158,199,215,1733,1734,1735],([213,1,2,3,4,126,5],[17,33,48,917,1736],[]),([355,1,2,3,4,5,98],[17,30,43,48,61,1737,1738],[0]),e6 [519] ([15,17,38,48,61,72,158,182,199,215]++r 1739 5),e6 [62,520] ([33,48,96,158,194,1377]++r 1744 6),([138,150,1,2,3,4,5],[30,43,48,374,503],[0]),e6 [521] [17,30,72,158,1750,1751],([230,55,1,2,3,468,5],[30,48,1274,1752,1753],[]),e6 [522,126] ([30,33,47,48,55,182,199,1196,1199,1425,1427,1630]++r 1754 4),u6 [218,114] [48,61,63,118,305,441,1156,1345,1758,1759,1760],([32,0,1,2,346,4,5],[34,48,63,1761],[]),e6 [108,98] [30,34,48,61,96,199,216,603,647,682,695,875,952,1140,1762,1763,1764],e6 [523] [15,17,63,199,425,1765,1766,1767],e6 [55,301] ([30,33,38,43,48,70,561,1482,1702]++r 1768 6),u6 [13,9] [17,28,33,85,556,557,855],e6 [110,524] [17,30,63,96,282,1346,1774,1775,1776],e6 [150,264,98] [330,1140,1626,1777,1778,1779],e6 [525] [17,47,48,61,1780],([43,7,1,2,3,4,5,6],[40,48,61,100,173,475],[0]),e6 [443,185,98] [61,216,952,1143,1781],e6 [526] [17,30,33,72,158,182,199,1782,1783,1784],e6 [527] [17,33,47,48,61,947,1785,1786],e6 [266,155] [17,30,415,1361,1362,1787],([230,0,291,2,3,4,5],[30,43,48,450,1788],[0]),e6 [290,62,266] ([55,574,1052,1377,1713,1748]++r 1789 5),e6 [528] [17,33,47,48,61,199,215,1794,1795,1796],e6 [68,438] ([61,157,158]++r 1797 6),([48,212,0,1,2,3,5],[17,33,218,1803,1804,1805],[0]),([43,0,1,2,4,126,5,98],([17,30,61,118,216,1358]++r 1806 4),[]),e6 [529] [17,33,158,199,1810,1811,1812],e6 [530,441] [17,61,72,1129,1813,1814],e6 [92,110] [33,43,63,158,358,560,661,1244,1247,1368,1815,1816],e6 [372] [48,61,96,199,215,840,841,1270],([0,1,2,3,520,5,6],[33,38,173,215,1817,1818],[]),e6 [531] [17,30,48,157,199,1340,1819],e6 [532] ([30,72,158]++r 1820 4),e6 [533] [33,43,48,96,1824,1825],([49,0,1,3,4,5,12],[30,33,46,61,96,118],[0]),e6 [518,270] [17,30,96,182,1733,1735,1823,1826,1827],e6 [534,98] ([30,33,48,61,199,216,603,695,1140,1809]++r 1828 5),([0,1,3,535,18,4,5],[17,30,96,1833,1834],[]),u6 [42,68,6] [17,33,456,511,589,655,1063,1116,1835],([0,1,2,270,4,5,98],[17,30,33,96,215,469,1836],[0]),u6 [249] [17,33,61,199,291,330,331,423,1837,1838],([0,1,3,4,383,12],[63,118,215,1839,1840],[]),e6 [110,536] ([33,63,96,118,158,282,421,1760]++r 1841 6),u6 [110,256] ([33,61,63,96,282,421,441,560]++r 1558 4++[1563,1847]),e6 [313] [17,33,43,47,63,72,96,182,199,420,665,666,667,1848,1849,1850],([158,55,0,1,3,18,4,5],[30,96,1351,1488,1519,1526,1851,1852,1853],[]),u6 [212,185] [17,33,48,61,182,216,685,709,1532,1803,1804,1854],e6 [55,128] ([30,38,43,54,70,215,303,1482]++r 1855 6),u6 [234] [17,33,47,48,61,215,271,1861,1862],e6 [150,256] [15,61,331,441,1453,1559,1560,1563,1863],u6 [290,85] [15,17,38,48,63,879,1046,1790,1864],u6 [42,110,6] [33,63,466,511,655,661,1865,1866],([360,0,2,3,4,5,194],[17,33,48,157,158,736,1867,1868],[0]),u6 [281,55,18] ([48,63,278,303,342,704,1036,1352,1482]++r 1869 4),u6 [66,6] [15,30,33,48,100,1377,1611,1873,1874],u6 [114,12] [17,43,48,63,96,158,305,666,935,1345,1719,1875,1876],([110,7,1,2,3,4,5,6],[9,10,13,29,33,40,47,100,214,432],[0]),e6 [537] [17,30,38,47,96,215,1476,1877,1878,1879],e6 [538] ([17,30,33,48,63,158]++r 1880 4),e6 [32,383] [17,34,43,48,118,215,411,412,413,832,1408,1409,1410,1884,1885,1886],([7,1,2,3,4,5,192],[10,12,13,33,40,55,61,1887],[0]),([338,266,0,1,3,4,5],[17,30,43,47,647,648,649,1888,1889,1890],[]),u6 [89,18,6] [43,61,278,389,511,703,739,1247,1891,1892],e6 [32,539] [48,412,1384,1893,1894],([0,1,199,3,4,5,194],[17,33,43,157,729,1895],[0]),e6 [540] [17,43,47,63,72,96,182,199,1896,1897,1898],([42,0,1,2,4,5,98],[17,61,1063,1899,1900,1901],[0]),([55,0,1,2,9,4,5],[17,26,27,28,33,96,111,556,853,1351,1902],[0]),([43,241,1,2,3,4,5],([15,17,48,96,874]++r 1903 4),[]),e6 [148,191] [17,30,48,61,311,742,1907,1908,1909],([230,541,1,2,3,4,5],[15,30,47,48,540,1910,1911],[]),([32,0,1,8,3,4,12],[5,6,15,17,33,43,118,301,302,412,911,919,1912,1913],[0]),([110,185,1,2,3,4,5],[17,48,61,63,180,685,709,1624,1914],[0]),u6 [296,12] ([17,54,61,187,215,666,1526]++r 1915 4),u6 [156,155] [15,17,30,33,48,289,734,942,1361,1362,1919],e6 [542] [17,43,48,96,158,182,215,1163,1920,1921],e6 [108,126] [17,30,48,55,182,199,1425,1427,1630,1754,1762,1764,1922],e6 [339,185] [17,30,61,180,685,1085,1624,1923,1924,1925],([110,7,1,2,3,4,5],[9,10,13,29,38,40,48,61,63,69,214],[0]),e6 [543] [48,63,96,199,215,1926,1927,1928],e6 [230,544] [61,63,96,540,1929,1930,1931],([230,1,2,3,4,134],[30,48,61,63,215,1932,1933],[0]),e6 [545] ([17,63,1352]++r 1934 5),u6 [62,150,220] [215,331,574,1298,1377,1386,1513,1939,1940],u6 [32,8,6] [17,48,55,86,101,173,1941,1942],([32,541,1,2,3,4,5],([15,48,61,96,412]++r 1943 6),[]),u6 [18,332] [30,33,61,278,629,1949,1950],e6 [367,110] ([33,63,158,282,420,1825]++r 1951 4),([110,0,1,2,9,4,5],[17,26,28,63,96,111,282],[]),([32,138,1,2,3,4,5],[34,43,48,1384,1955,1956],[]),([62,0,1,2,231,4,5],[15,17,61,72,96,1377,1957,1958,1959],[0]),u6 [241,98] [15,17,33,48,61,199,215,647,682,695,718,1140,1960,1961,1962],e6 [546] [17,33,43,199,1963,1964,1965],([0,1,2,3,114,5,6],[33,38,215,440,653,1966],[0]),e6 [547] ([17,33,43,47,63,72,96,182,199,420]++r 1967 5),e6 [548] ([43,47,63,72,96,182]++r 1972 4),([0,104,2,3,4,5,6],[43,55,123,185,192,242,243,511,1976,1977],[0]),e6 [549] ([17,47,63,72,96,182]++r 1978 5),e6 [550] [43,48,61,96,1983],u6 [55,264,98] [17,33,603,952,1140,1143,1482,1625,1626],e6 [551] [17,33,61,63,182,199,540,1984,1985,1986],u6 [122,110,12] [33,43,63,420,666,668,932,1718,1719],e6 [55,12] ([30,33,38,54,70,96,215,1351,1482,1483]++r 1987 5),u6 [110,98,6] [17,33,48,61,63,215,511,661,1140,1992],([92,0,1,2,4,5,98],[33,61,199],[]),([218,7,1,2,3,4,5],[9,13,40,48,61,213,821],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_8_1 : checkNodesBT W_22 g_22 F_22 P_22_8 A_22 B_22_7 8 N_22_8_1 = true := by decide +kernel
def N_22_8_2 : List NodeSpec := [u6 [43,272,126] [17,55,61,388,1199,1427],e6 [415,98] ([15,17,33,61,199,216,603,682,695,1140]++r 1993 5),([0,104,8,3,4,5,12],[15,30,33,61,118,123,301,363,364,1998],[0]),([218,150,0,1,220,3,4,5],[15,215,331,361,441,1435,1939,1999,2000],[0]),([68,118,0,1,3,4,5,6],[30,33,96,172,389,456,609,677,2001,2002],[0]),e6 [552] ([17,43,48,55,1427]++r 2003 4),e6 [338,185] [17,48,61,96,180,647,649,685,913,1494],([0,1,2,3,365,5,6],[33,61,63,158,182,2007,2008],[0]),u6 [158,110,6] [30,48,63,173,282,511,1346,1487],e6 [553] [47,48,55,61,158,2009,2010,2011],e6 [554] [17,48,63,215,2012,2013,2014],e6 [122,32] [33,34,38,48,55,61,411,412,932,947,1184,1242,1384,2015,2016],([230,1,2,3,4,238,5],[30,33,48,61,274,521,2017],[]),u6 [18,114] [17,33,48,61,158,305,561,1816,2018,2019],([110,0,1,3,18,4,5,12],([30,33,43,63,420,935]++r 2020 5),[0]),e6 [555] [43,48,61,63,96,2025,2026,2027],e6 [556] [34,48,96,118,158],([0,1,2,51,4,5,98],[17,61,158,215,647,2028,2029,2030],[]),e6 [230,148] ([30,33,63,215,742,1274]++r 2031 4),e6 [557] ([15,17,30,33,43,47,63,72,96,182,199,1136]++r 2035 4),e6 [266,63] ([30,33,55,61,194,642,1748,1789]++r 2039 4),e6 [152,238] [30,33,48,215,323,334,1419,1432,1434,1438,2043,2044],u6 [32,118,6] [33,48,55,101,173,192,412,749,1384,2045],e6 [32,432] [30,33,43,157,1103,1338,1339,1340,1636,2046],u6 [29,134] [17,43,61,238,691,1457,1459,2047,2048],([309,0,1,2,3,4,98],[17,30,43,61,199,2049],[]),e6 [558] ([17,33,47,48,55,199]++r 2050 4),e6 [110,12] [33,43,63,96,282,421,560,1988,1989,1991],u6 [18,305] ([30,33,61,278]++r 2054 5),u6 [85,6] [15,17,48,61,173,879,1063,1132,2059],u6 [218,150,238] [33,61,212,215,274,1163,1419,1435],([0,1,2,491,4,5,98],[17,30,63,695,2060,2061],[]),e6 [498,98] [17,30,33,48,63,194,199,216,647,695,952,1140,1535,2062],e6 [419] [30,38,43,48,96,158,182,215,1144,2063,2064],e6 [560] [15,43,48,61,96,194,2065],u6 [29,272] [17,43,63,586,1757,2066,2067],e6 [561] ([15,17,30,33,72,158,199,215,331]++r 2068 4),e6 [62,441] [55,96,158,194,1126,1128,1377,2072,2073],u6 [120,6] ([33,63,173,192,421,511]++r 2074 5),e6 [110,427] ([43,63,420,421,1790]++r 2079 4),e6 [562] [33,38,43,47,61,96,2083],u6 [165,167] ([48,63,92,182,770]++r 2084 4),([281,7,1,2,3,4,5],[9,10,13,29,33,48,55,61,2088],[0]),e6 [410] ([15,38,43,48,72,118,158,182,199]++r 2089 4),([281,158,165,0,1,3,4],[15,17,63,215,425,772,773,1324,2093],[0]),e6 [563] [43,63,96,2094,2095,2096],([230,0,1,2,9,4,5],[15,17,26,33,63,85,111,215,540,556,2097,2098,2099],[0]),e6 [564] [33,43,96,2100,2101],u6 [63,12] ([33,43,48,96,158,430,642,666,1536,2039]++r 2102 4),u6 [319] [17,30,33,96,595,2106,2107],e6 [565] [30,72,158,182,2108,2109,2110],e6 [566] [43,63,96,2111,2112,2113],e6 [567] ([15,63,96,118,158,182,199]++r 2114 6),e6 [230,9] [17,26,33,55,63,85,96,111,215,540,556,2098],([210,0,1,220,3,4,5],[15,43,118,215,331,1471,1939,2120,2121,2122],[]),([0,1,2,3,30,5,6],[17,33,158,173,215,410,2123,2124],[0]),e6 [127,256] [15,61,157,1559,1563,2125],([266,7,1,2,3,4,5],[13,29,38,40,43,48,61],[0]),([165,49,0,1,3,4],[30,33,43,63,90,96,118,843,948],[0]),e6 [568] [43,63,96,2076,2126,2127,2128],u6 [270,6] [30,61,389,511,1826,1827,2129,2130,2131],([32,0,1,2,9,4,5],[15,17,26,28,33,47,61,85,86,111,412,413,556,635,2132],[0]),([0,1,2,204,4,98],[17,33,63,118,215,695,779,2133,2134],[0]),e6 [569] [17,30,33,38,2135,2136,2137],u6 [18,141] [17,33,48,61,710,730,2138,2139],u6 [243] ([15,17,33,61,158]++r 2140 5),u6 [120,12] [17,33,43,63,96,402,421,666,2022,2076,2145,2146],([0,1,2,375,4,126,5],[17,33,215,1199,2147,2148],[]),([0,1,18,4,5,12,98],[17,30,33,61,199,215,2149,2150],[]),e6 [212,110] [33,63,158,218,282,420,661,1532,1804,2151,2152,2153],([210,0,1,491,3,4,5],[17,30,43,215,1392,1476,2121,2154,2155],[]),u6 [309,110] ([30,33,63,158,560]++r 2156 4),([0,104,2,3,4,5,98],[43,61,123,241,695,803,1140,2160,2161],[0]),([110,0,1,3,4,191,5,12],([30,63,402,421,1719]++r 2162 4),[]),([158,0,1,131,3,4,5],[15,43,63,118,282,2166,2167,2168],[]),u6 [218,110,6] [17,61,173,282,421,456,594,1156,1760,1845,2078,2169],e6 [309,92] [30,43,61,215,561,1367,1368,2156,2158,2159,2170],e6 [355] [43,48,158,1773,2171],([0,1,2,120,4,5,98],[17,33,63,158,215,2172,2173,2174],[0]),([55,570,1,2,3,4,5],([30,48,215]++r 2175 7),[]),e6 [571] [17,33,38,47,55,199,2182,2183,2184],e6 [62,462] ([33,158,194,574,1257,1377]++r 2185 4),([207,0,1,2,3,4,445],[17,55,63,96,691,1392,2189,2190],[]),u6 [150,76] [17,30,118,158,316,485,589,632,1435,2191,2192,2193],e6 [62,351] [30,33,158,194,1267,1377,1666,1667,1668,1687,2194,2195],([0,195,2,3,4,5,6],[61,131,511,2196,2197],[0]),e6 [114,98] [17,48,63,305,560,2153,2198,2199],([110,138,1,2,3,4,5],[30,43,48,706,1439,2200],[]),([55,410,1,2,3,4,5],([33,43,48,215,303]++r 2201 7),[]),e6 [572] [15,33,55,118,158,182,1943,2208,2209,2210],e6 [122,108] [30,48,61,118,182,402,668,875,932,1184,1762,1922],u6 [111,6] [33,63,100,158,173,192,404,481,511,1063,2211],([43,0,1,279,3,4,5,98],[15,61,118,647,682,696,700,2212,2213],[]),e6 [110,208] [63,158,282,399,420,1027,1144,1146,1148,1711,2214,2215],e6 [573] [43,48,215,412,2216],e6 [574] [17,30,72,158,182,199,2217,2218],u6 [51,6] [17,48,61,100,238,247,971,2219,2220],e6 [213,126] [17,33,48,917,1196,1425,1427,1630,1736,1754,2221],e6 [576] ([17,33]++r 2222 4),([101,1,37,2,3,4,5],[15,41,61,116,117,262,285,554,1082,2226],[0]),e6 [577] ([33,43,61,63,96,182,199]++r 2227 5),e6 [578] ([17,38,48,61,96,199]++r 2232 4),e6 [579] [15,17,43,48,61,96,215,2236],([0,1,2,231,4,126,5],[17,33,96,2237],[]),([367,512,0,1,2,3,4],[17,33,2238],[0]),e6 [581] ([17,30,55,72,158,199]++r 2239 4),([55,275,0,2,3,4,5,12],([30,33,43,48,54,187,808,810,1482,1543]++r 2243 4),[0]),([355,1,2,3,4,5],[17,30,43,48,61,2171],[]),([345,185,1,2,3,4,5],[17,34,48,72,2247,2248],[0]),e6 [367,43,126] [17,33,55,61,1427,1953,2249],e6 [582] [43,63,96,2250,2251,2252],u6 [110,18,6] [33,48,61,63,192,278,420,511,710,1247,1816,1891,2078],([345,0,1,2,346,4,5],[34,48,63,72,2253],[0]),u6 [369,98] [17,30,48,157,199,216,682,952,1117,1140,1616,2254],u6 [120,191] [17,43,61,63,96,421,661,2076,2255,2256,2257],([0,1,2,346,4,5,98],[17,33,63,199,2258,2259],[0]),u6 [419,208] [30,33,47,399,1027,1144,2063],u6 [124,12] [30,38,54,187,430,567,666,1536,2260,2261],u6 [119,18] [30,38,278,303,341,342,384,385,2262,2263],e6 [158,320] ([33,34,48,597,1240,1241,1487]++r 2264 5),([218,110,0,1,3,4,5,12],[61,96,118,282,421,441,1539,1542,1547,2022],[0]),([0,1,2,3,238,126,5],[30,33,38,274,1163,2269],[]),u6 [48,220] [37,43,48,331,515,1127,1513,1939,2270,2271],e6 [281,108] [30,43,48,63,96,356,425,875,1764],([158,0,1,405,3,4,5],([15,33,43,63,118,540,1170]++r 2272 4),[]),([55,498,1,2,3,4,5],([15,17,30,33,48,158,1482]++r 2276 4),[]),e6 [68,261] [33,43,48,55,61,157,158,535,2280],([118,101,1,2,3,4,5],[30,41,47,61,116,138,319,749,2281],[0]),([210,32,0,1,3,4,5,12],[61,96,118,412,413,563,564,977,1242,2121,2282],[]),u6 [78,6] ([17,30,33,182,192,215,389,412,511]++r 2283 5),([218,150,0,1,3,4,5,12],[15,61,96,331,441,1435,1539,1540,1542,2288],[]),([158,110,0,1,3,4,191,5],[17,30,63,96,282,560,1346,2289,2290],[]),e6 [38] [17,43,48,96,182,215,2291],e6 [110,429] [17,33,63,96,282,1357,2292,2293,2294],([239,150,1,2,3,4,5],[30,38,43,48,276],[0]),e6 [583] [30,34,43,48,96,182,413,2295],e6 [584] ([15,33,48]++r 2296 4),([0,1,2,152,18,4,5],[17,30,33,96,502],[0]),([158,330,0,1,3,4,5],[17,30,43,118,215,2290,2300,2301],[]),e6 [585] [17,61,2302,2303,2304],e6 [586] ([15,30,48,182,199,1127]++r 2305 4),e6 [108] [15,38,43,48,72,118,158,182,199,1991,2309,2310,2311],u6 [62,266,6] [17,33,48,173,511,654,1377,1632,1713,1789,2312],u6 [233,110] [17,30,63,158,661,1549,1551,2313],e6 [52] [47,48,61,1182,1183],e6 [587] ([15,17,63,96,199,282]++r 2314 4),e6 [589,126] ([15,17,33,48,72,1196,1199,1425,1427,1630]++r 2318 4),([110,0,1,8,3,4,12],[5,17,33,63,96,282,301,302,420,919,2322,2323],[0]),e6 [590] [48,61,96,158,182,1745,2324],u6 [366,18] ([15,30,43,48,278,341,342,561,1247]++r 2325 4),e6 [592] ([15,48,63]++r 2329 5),([33,0,1,2,9,4,5],[17,28,33,61,556,857,2334],[0]),([32,0,1,2,152,4,5],[17,34,48,2335,2336],[]),e6 [593] ([30,33,43,48,158]++r 2337 5),u6 [257,6] [30,33,48,192,389,511,1219,2341,2342],e6 [92,18,332] [30,33,61,629],u6 [278,62] [17,30,33,158,194,1267,1377,1446,1597,1649,1652,2343,2344,2345],e6 [594] [30,72,96,158,2346,2347],([55,0,1,3,18,4,5,12],[30,33,303,561,935,1548,2020,2021,2023,2024],[]),e6 [43,375] ([15,17,30,43,1045,1046,1721]++r 2348 5),u6 [55,148] [17,30,33,38,70,311,742,1351,1527,2032,2033,2353,2354],e6 [595] [17,30,47,48,118,182,1776,2355],e6 [207,7] [9,30,40,48,63,69,1393,1394,2356,2357],([55,122,0,1,2,3,5],[33,43,303,402,403,947,1184,1537,2358,2359,2360],[]),e6 [596] [15,17,33,96,2361,2362,2363],e6 [597] ([15,17,33,43,48,72,158,199]++r 2364 4),e6 [598] [17,158,1668,2368,2369],e6 [600] ([30,43,118,158]++r 2370 5),u6 [43,285] ([15,43,63,1353]++r 2375 6),([122,0,1,2,3,5,6],[33,43,55,182,192,946,2381,2382],[0]),u6 [288] ([38,47,55,158,199]++r 2383 4),u6 [150,219,152] [30,48,215,1386,1434,2387,2388,2389],u6 [128,6] [30,33,48,456,511,1857,2390],([0,104,2,3,4,105,5,12],[61,105,185,243,258,666,881,2391],[0]),u6 [245] [15,17,33,43,48,96,199,286,330,2392,2393],([0,104,8,3,4,12],[15,118,123,301,302,363,364,1998],[0]),e6 [43,576] [15,48,454,2222,2224,2225,2249,2394,2395],([0,195,2,3,4,126,5],[17,55,1425,2396],[]),e6 [42,43] [15,17,43,61,456,466,1063,1900,2397],e6 [152,191] [17,30,61,96,501,1265,1432,1434,1435,1438,2398,2399],u6 [55,76] [17,30,38,43,54,118,485,589,632,1342,1526,2400,2401,2402],e6 [601] ([17,30,33,72,158,182,199]++r 2403 4),e6 [110,166] [17,43,63,420,560,661,687,825,2084,2407,2408],e6 [32,429] [17,33,34,48,61,96,412,1357,2121,2292,2293,2409,2410,2411],e6 [602] [48,96,118,158,215],([48,0,1,3,18,4,5,12],[33,43,61,515,561,1127,1541,2020,2021,2023,2024],[0]),e6 [603] [33,34,38,43,48,61,96,158,182,1532,2412],e6 [604] [30,33,48,1339,2413],([261,150,1,2,3,4,5],[33,38,48,533,2414],[0]),e6 [43,63] ([15,43,61,158,642,1632,1903,2039,2105,2249]++r 2415 5),e6 [43,559] ([15,48,61,2065]++r 2419 7),([92,0,1,3,4,5,12],[33,43,2426],[]),e6 [605] ([15,47,63,72,182,199,282]++r 2427 4),u6 [185,194] [17,61,70,216,709,1143,1624,2431,2432],e6 [606] [17,30,33,96,182,2433,2434,2435],e6 [607] ([15,61]++r 2436 6),([198,0,1,3,4,5,98],[17,30,118,695,1015,1016],[0]),e6 [290,62,43] [15,1052,1267,1446,1791,1792,1903,2418,2419,2442],([213,1,2,3,4,5],[17,48,61,917,1736],[0]),e6 [608] ([17,33,47,48,63]++r 2443 4)]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_8_2 : checkNodesBT W_22 g_22 F_22 P_22_8 A_22 B_22_7 8 N_22_8_2 = true := by decide +kernel
def N_22_8_3 : List NodeSpec := [u6 [7,18,6] [30,33,40,48,100,173,192,342,710,2447],e6 [230,63] [33,48,63,194,540,642,1237,1268,2039,2105,2448],([0,1,2,59,4,126,5],[17,33,48,158,199,1425,2449],[]),e6 [165,261] ([43,55,61,535,1630,1971]++r 2450 4),e6 [408,150] [15,17,33,55,274,1435,1453,1521,1522,1524,1525,2288],e6 [609] ([15,17,61,96,182,199,215]++r 2454 5),e6 [610] ([15,17,30,96,199]++r 2459 4),u6 [43,148] [15,17,43,158,311,1527,1903,2032,2033,2380,2463,2464],u6 [214,12] [15,43,48,96,215,402,430,666,1396,1536,2465,2466],([122,0,1,8,3,4,12],[33,61,118,919,2467,2468],[0]),u6 [32,29,6] [48,55,101,118,173,411,412,1132,2469],e6 [611] [17,30,72,158,182,199,2470,2471],([7,1,2,3,4,5,98],[9,29,40,61,954,1671],[0]),e6 [43,365] ([15,17,48,63,454]++r 2472 4),([150,0,1,2,3,4,12,98],[30,61,215,331,334,647,935,1715,2476],[]),e6 [185,191] [43,48,61,96,2477,2478],e6 [522] [43,48,96,158,215,1755],e6 [612] [15,38,96,118,215,1855],e6 [613] ([17,30,43,47,61,63,72,96,199]++r 2479 4),e6 [367,43] [15,33,43,61,1825,1951,1953,2483],e6 [48,405] [15,37,43,48,158,515,540,1130,1170,1503,2484],([43,498,1,2,3,4,5],[15,30,48,96,1534,1903,2485,2486,2487],[]),e6 [62,515] ([15,33,194,1742]++r 2488 4),([32,570,1,2,3,4,5],[30,34,48,413,2492],[]),([158,0,1,3,4,336,5],[30,43,1851,2493,2494],[0]),([309,0,1,2,18,4,98],[17,30,61,199,215,2495,2496],[]),e6 [309,55] [30,38,48,70,1482,1526,2156,2158,2159,2497],e6 [415] ([15,33,61,158,182,695]++r 1993 5),e6 [148,12] [17,30,33,158,402,742,2498,2499,2500],e6 [614] [17,33,38,47,96,215,2501],e6 [290,76] [30,118,157,485,2191,2502,2503],u6 [150,29,152] [30,215,330,691,1433,1434,1442,2504],u6 [80,6] [15,43,61,100,192,389,465,511,630,631,1063,2505,2506],u6 [32,166] [33,34,43,48,55,61,118,411,413,687,825,1384,2084,2085,2407,2408,2507],([210,275,0,3,4,5,12],[30,118,563,2243,2244,2245],[]),e6 [32,515] ([17,33,34,48,55,61,96,412,413,1742,1942]++r 2488 4++[2508]),([62,0,1,2,9,4,5],[15,26,28,33,61,85,111,556,2509],[0]),([122,275,0,2,3,4,5],[33,48,72,118,668,808,2243],[]),u6 [118,110,6] [33,63,172,282,511,749,2510,2511],e6 [238,98] [30,33,61,199,215,323,647,1140,1163,2512,2513,2514],u6 [62,118,6] [33,172,173,192,511,654,677,1377,2515],e6 [110,192] ([17,30,43,48,63,421,661]++r 2516 7),e6 [615] [17,30,33,38,43,47,649],e6 [212,43] [15,17,33,38,61,1532,1803,1804,2151,2483],([110,541,1,2,3,4,5],[15,17,48,61,96,282,1944,1946,2523,2524,2525],[]),u6 [43,208] [15,30,33,43,399,1027,1144,1146,1148,1711,2483,2526,2527,2528],u6 [274] [17,33,48,63,192,2529,2530],e6 [233] [30,48,118,158,199,2531],e6 [44,6] [15,48,61,192,215,389,456,511,2532,2533],e6 [616] ([15,17,33,182]++r 2534 5),u6 [42,43,6] [17,55,192,454,456,466,2397],e6 [53] [48,61,96,199,215,249,250,971],e6 [32,445] [17,33,34,48,55,61,96,412,1165,1177,1622,2539],e6 [43,194] ([15,43,48,61,550,917,1199,1867]++r 2540 5),u6 [32,165,6] [17,48,55,101,192,2507,2545,2546],u6 [111] [17,43,47,63,96,199,404,481,2211,2547],u6 [55,89,18] [43,278,341,342,704,739,1482,1483,1871,2548],u6 [9,6] [17,28,33,48,55,173,556,601,813],e6 [617] [15,30,158,199,2549,2550,2551],e6 [138,6] [30,48,100,182,192,389,511,1567,2447,2552],([158,62,165,0,1,3,4],[15,33,96,118,226,772,773,1324,1377],[0]),e6 [230,155] [30,33,48,55,63,215,1136,1361,2553,2554],e6 [32,619] ([15,48,412]++r 2555 4),e6 [32,514] [43,48,1384,2559,2560,2561],e6 [621,98] ([17,33,61,194,216,647,682,695,1140]++r 2562 4),e6 [622,150,152] [30,331,1435,2566],e6 [68,320] ([33,43,157,158,1241,1689,2265]++r 2567 4),e6 [165,296] [17,54,61,70,215,1916,1971,2204,2453,2571,2572,2573],e6 [623] [33,34,43,48,96,158,2574,2575],([55,0,1,8,3,4,12],([5,17,33,43,54,96]++r 301 4++[911,919,1351,2576,2577,2578]),[0]),u6 [260,12] [17,33,43,96,187,430,572,666,1242,2579,2580],e6 [32,546] [48,412,1384,2581,2582],([0,1,2,3,468,5,6],[30,33,38,182,2583,2584],[]),e6 [150,559] [15,33,574,1386,2065,2420,2425,2585,2586,2587],([32,185,1,2,3,4,5],[17,34,48,2588],[]),([32,85,1,2,3,4,5],[48,61,96,412,879,1145,1198,2469,2589,2590],[]),([0,1,3,4,126,624,5],([17,33,55,118]++r 2591 4),[]),e6 [32,625] [34,43,48,413,1384,2595,2596],u6 [218,318] ([33,96,118,441,1845,2435]++r 2597 6),([0,104,2,3,4,126,5],[17,55,241,243,1425,1427,2603,2604],[]),u6 [32,322] ([33,34,48,96,215,412,413]++r 2605 4),u6 [377,12] [30,33,43,54,70,96,187,215,430,666,2609,2610],([108,0,1,8,3,4,12],[5,15,30,33,43,118,301,302,911,919,1764,2611,2612,2613],[0]),u6 [76,6] [17,30,100,456,485,632,1116],e6 [290,32,29] [48,55,411,412,413,1131,2469,2614,2615],([32,0,1,2,270,4,5],[30,34,48,412,2616],[]),e6 [32,96] ([33,34,43,48,55,61,200,413,1636,1861]++r 2617 4),u6 [32,326] ([17,33,34,43,48,215,413,1229,1384]++r 2621 5),([32,7,1,2,3,4,5],[9,13,38,40,48,55,61,69,2015],[0]),([338,0,1,18,4,5,98],[17,30,96,199,647,695,2626,2627],[]),([338,0,29,1,3,4,5],[43,61,72,647,863,1490,2628,2629],[0]),e6 [626] [17,33,61,96,182,2056,2630,2631,2632],([32,0,1,2,120,4,5],[15,34,48,63,158,411,2633,2634],[]),([48,0,1,2,9,4,5],[15,17,26,28,33,111],[]),([628,0,1,3,4,126,5],[17,55,1196,2635],[]),e6 [629] [15,30,158,182,199,2636,2637],e6 [110,515] [17,63,96,282,661,1742,2488,2489,2491],([158,32,0,1,3,4,191,5],[30,96,118,412,1660,1661,1689,2257,2267,2289,2638],[]),e6 [213] [17,38,43,48,61,96,158,917,1736],e6 [630] [48,61,215,412,2639],e6 [32,631] ([15,34,43,48,118,215,412,413,1384]++r 2640 4),e6 [632] [15,43,48,61,72,158,199,215,1832,2644,2645,2646],e6 [633] [17,33,43,96,199,2647,2648],e6 [33] [34,43,48,412,2649],e6 [634] ([15,61,158,215,1427]++r 2650 5),([230,55,68,1,2,3,4,5],[30,48,1341,1633,2619,2655,2656,2657],[0]),([32,0,1,8,3,4,5,12],[5,6,17,33,55,61,96,118,301,302,412,413,911,919],[0]),e6 [635] [30,48,96,158,182,2658],([73,7,1,2,3,4,5],[9,10,13,29,33,38,40,48,69,507],[0]),([32,0,104,2,3,4,5],[17,43,55,61,123,158,185,241,243,322,411,599,600,1384,2659],[0]),e6 [636] [17,33,2660,2661,2662],e6 [637,208] [30,33,96,399,1027,1144,1146,1711,2663],u6 [372,231] [17,33,47,61,509,840,1270,2664],([32,408,0,1,2,4,5],[17,43,55,61,935,936,1384,1524,2665],[]),u6 [261,127] ([33,48,158,354,535,1857,2450]++r 2666 4),([185,0,1,2,18,4,5,98],[17,61,1564,2670],[0]),e6 [638] [17,33,47,48,199,1199,2671,2672,2673],e6 [32,524] [30,34,48,96,411,412,1774,1775,1776,2267,2638,2674],e6 [29,320] [33,34,48,1241,2265,2675,2676,2677],([210,110,0,1,3,4,5,12],[17,33,43,63,96,282,563,1719],[0]),e6 [639] ([17,48,61,215,695]++r 2678 4),([62,42,0,1,2,4,5],[17,33,55,61,236,488,637,655,2682],[]),u6 [367,68] [33,43,48,157,158,589,1825,1951,2656,2683],([0,1,2,231,4,5,98],[17,33,61,215,2684,2685],[0]),u6 [110,12,6] [33,61,63,173,192,215,282,420,511,560,666,2686],([330,0,1,2,4,126,5],[17,33,118,199,2687],[]),e6 [640] ([15,17,30,43,72,158,199]++r 2688 5),e6 [68,185] [30,48,157,158,682,685,2693],e6 [55,559] [33,70,194,303,574,1351,1598,2065,2420,2424,2425,2694,2695],e6 [108,6] [30,48,55,61,100,192,389,511,1063,1762],e6 [281,7] [9,17,29,48,63,100,182,356,425,1352,1587,2378],u6 [212,68] [33,43,48,157,158,216,1532,1804,2656,2696,2697],u6 [183,6] [33,48,100,158,259,390,1063,1116,2698],u6 [7,98] [9,34,40,48,61,101,199,216,603,647,682,695,758,952,954,1140,1671],u6 [68,7] [9,17,30,40,48,100,157,158,589],([68,7,1,2,3,4,5,6],[9,12,13,33,40,48,269,1637,2656,2699],[0]),u6 [71,29] [17,72,238,691,905,1131,1157,1159,2700,2701],u6 [68,7,6] [9,30,33,48,100,511,1116,1637,2656],u6 [213,98] [17,61,603,647,682,695,952,1140,2431,2702,2703],([68,101,1,2,3,4,5,6],[15,30,33,41,100,116,117,262,890,1637,2704],[0]),e6 [591,126] [15,17,33,48,182,199,215,1196,1425,1630,1754,2333,2705,2706],e6 [641] ([15,61]++r 2707 5),u6 [214,191] [15,43,63,96,1265,1266,2466,2712],u6 [165,214] [15,43,194,215,2085,2087,2466,2712,2713],u6 [214,6] [15,48,61,63,100,173,182,192,194,215,511,654,2312,2466,2712,2714],u6 [7,24] [13,30,48,205,1098,2715],e6 [290,214] [15,38,63,194,1052,1790,1864,2466,2712,2716,2717],e6 [642] [15,33,38,1611,2718],u6 [213,194] [17,33,48,189,917],([361,1,2,3,4,5,194],[17,33,38,917,2719],[0]),([101,200,1,2,3,4,5],[15,33,41,116,504],[]),u6 [64] [15,33,38,43,48,61,96,215,642,2720,2721],e6 [158,63] [15,30,33,194,642,1662,2039,2105,2722,2723],e6 [207,419] [30,48,63,182,1144,1148,2063,2064,2357,2724],([198,0,1,3,4,126,5],[17,55,118,549,1427,2725],[]),e6 [644] [15,43,48,96,215,2726,2727],e6 [645] [17,33,158,2287,2728],e6 [646] [30,33,38,96,2729,2730,2731],e6 [62,239] [30,43,48,55,61,158,194,574,1269,2732,2733,2734],e6 [647] [17,47,48,61,182,215,2491,2735,2736,2737],([0,1,2,4,191,384,5],[17,30,61,829,2738],[]),e6 [62,429] [15,33,194,1357,2292,2293,2409,2739],u6 [32,37,6] [17,33,48,55,101,173,285,1384,2740],([275,0,8,3,4,5,12],[33,43,63,118,302,397,2244,2741,2742],[0]),e6 [648,220] [15,17,30,43,48,331,1513,2743,2744],e6 [62,499] ([15,194,574,2013]++r 2745 4),u6 [387,231] [17,33,61,509,839,1270],e6 [649] [17,43,47,63,72,96,2749,2750,2751],([210,62,0,1,3,4,5,12],[15,33,96,118,564,574,977,1377,2104,2282],[0]),([49,0,1,3,4,12],[16,19,30,32,46,61,96,118],[0]),([241,150,1,2,3,4,5],[15,17,33,48,330,2752],[0]),([62,0,1,8,3,4,5,12],[15,33,61,118,301,302,919],[0]),u6 [150,249] [48,61,291,331,423,691,1837],([197,0,1,2,4,5],[17,30,118,2753,2754],[]),e6 [62,108] [43,48,61,158,194,875,1536,1599,1762,1764,2755],e6 [62,524] [15,30,33,194,1662,1774,1775,1776,2674],e6 [62,410] [43,48,63,158,194,2756,2757],u6 [62,166] [17,33,43,48,194,367,687,2084,2407,2408,2758],e6 [650,126] ([43,47,48,55,61,182,199,1196,1199,1425,1754]++r 2759 4),([266,185,1,2,3,4,5],[43,48,61,180,470],[0]),u6 [206,6] [33,48,100,158,173,192,617,654,2763],([62,7,1,2,3,4,5],[9,10,13,33,40,48,55,61,69,2312,2764],[0]),e6 [62,7] [9,13,30,40,48,61,100,158,194,1267,1377,2312],([62,7,1,2,3,4,5,6],[9,13,33,40,48,367,2312,2764],[0]),u6 [62,7,6] [9,33,40,48,100,367,511,654,2312],([230,55,1,2,3,18,4,5],[30,48,70,561,704,1247,1248,1633,2657],[0]),([62,101,1,2,3,4,5,6],[15,30,33,41,100,116,117,262,1083,2312,2765],[0]),u6 [229,18] [30,70,96,199,253,254,278,303,341,342,2766,2767],u6 [220,152] [17,30,33,215,331,1432,1438,1450,1471,1513,2768,2769],e6 [290,218,110] [61,282,421,441,1156,1760,2351,2770,2771],u6 [62,37,6] [15,17,33,126,173,511,654,675,1267,2772],e6 [652] [38,48,118,158,2773],([7,1,2,3,18,4,5,6],[9,12,40,48,61,233,234,710,2447],[0]),([290,62,0,1,2,3,5,6],[30,33,63,574,1081,1090,1632,1690],[]),e6 [653] [15,63,2774,2775],e6 [654] [15,61,96,215,718,2776,2777,2778],([68,7,1,2,3,4,5],[9,10,12,30,40,48,61,69,269,1637,2699],[0]),u6 [241,18] [15,17,43,48,61,63,96,199,278,561,718,2779,2780],u6 [241,12] [15,17,33,43,48,61,96,215,666,718,935,2781,2782],e6 [165,241] [15,17,43,48,63,676,718,2783]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_8_3 : checkNodesBT W_22 g_22 F_22 P_22_8 A_22 B_22_7 8 N_22_8_3 = true := by decide +kernel
def N_22_8_4 : List NodeSpec := [e6 [207,241] [15,17,48,63,215,718,2784],e6 [656] [15,30,43,118,182,199,215,2785,2786,2787],u6 [236] ([15,17,33,61,96]++r 2788 4),e6 [657] [15,118,2792],e6 [658] [17,43,48,55,70,96,199,466,2793],u6 [60] [15,43,48,61,96,215,362,513],([367,0,1,2,3,4,194],[17,33,72],[0]),u6 [165,59] [17,37,48,61,215,362,2205,2794,2795],e6 [659] [17,43,47,48,61,96,199,2796,2797],([158,55,165,0,1,3,4],[17,33,96,774,1324,1351],[0]),e6 [659,59] [17,33,37,48,215,1322,2798],e6 [660] [17,47,48,96,2139,2799,2800,2801],([55,591,1,2,3,4,5],([15,33,48,96,215,1351,2333]++r 2802 6),[]),e6 [662] [15,30,43,48,63,96,215,2808],e6 [663] [17,33,43,48,61,2809,2810],e6 [664] [30,48,96,182,2811,2812],e6 [218,661] ([15,118,441]++r 2813 4),e6 [665] [30,34,43,48,72,96,413,2817],e6 [666] [17,30,48,96,2815,2818,2819,2820],e6 [667] ([17,48,278,515]++r 2821 4),u6 [309,48] [30,48,61,158,874,2156,2159,2825],e6 [48,256] [15,48,61,1559,1560,1563,2826],u6 [18,90] [17,33,61,278,342,561,703,711,2827,2828,2829],e6 [668] [15,17,48,1127,2830,2831],u6 [122,62] [33,43,48,158,194,367,932,947,1184,1718,2104],([48,0,1,8,3,4,12],[15,17,43,301,302,911,919],[0]),e6 [83] [17,48,515,666,719,2832,2833,2834],u6 [83,12] [33,37,48,96,515,666,719,1536,2832,2833,2835],([580,395,0,1,3,4,5],[17,30,33,118,1196,2836],[0]),u6 [48,108,12] [15,30,48,187,666,850,874,875,2837],e6 [669] [15,30,48,182,2838],e6 [670] [17,33,47,48,199,2293,2839,2840],([38,7,1,2,3,4,5],[9,13,29,40,48,55,69],[0]),u6 [371,231] [17,61,215,764,1270,1957,1959,2841],e6 [32,671] [15,48,1384,2842,2843,2844],u6 [7,21] [13,17,30,40,48,61,640,2845],u6 [55,51] [17,38,48,61,70,96,238,247,971,1351,2181,2846,2847],u6 [38,6] [17,34,48,55,101,173,182,192,215,2291,2848],([158,48,165,0,1,3,4],[15,17,33,96,773,1127,1324],[0]),e6 [672] [33,43,47,48,61,96,2849],e6 [673] [17,43,48,96,1140,2850,2851],e6 [62,238] [30,33,48,158,194,274,624,1163,1267,1377,1419,2852,2853],e6 [43,200,6] [15,33,48,504,511],e6 [674] [17,43,48,96,158,199,2271,2854],e6 [675] [15,33,63,96,182,1535,2855,2856,2857],e6 [676] [15,48,63,2276,2858,2859,2860],e6 [498,126] [15,17,33,48,182,199,215,1196,1425,1427,1535,1630,1754,2276,2668],e6 [13] [28,48,96,199,215,855,1262],e6 [677] [15,38,43,48,96,118,182,199,215,1860,2861,2862,2863],([210,0,1,128,3,4,5],[15,43,118,215,1855,1857,1860,2121,2864,2865],[]),e6 [362] [30,43,48,96,199,215,1527,1528,2866],([210,0,104,1,3,4,5,12],[15,118,123,243,322,563,564,2282],[0]),([0,1,2,148,18,4,5],[17,30,33,96,158,2032,2867,2868,2869],[]),e6 [678] [30,38,48,158,2870],([0,1,2,148,4,126,5],[17,33,158,742,1199,1527,2871,2872],[]),e6 [679] [17,33,38,47,158,742,2873,2874,2875],e6 [62,43,6] [15,17,48,511,654,1267,1903,2312,2419],u6 [253] [17,33,38,43,47,96,312,2876],u6 [148,6] [17,30,33,48,173,311,742,745,1527,2032],e6 [680] ([30,48,1922]++r 2877 4),e6 [570,29] [48,63,72,96,158,691,2881,2882],u6 [18,155] [30,33,48,158,415,942,1362,2883,2884,2885],([146,7,1,2,3,4,5,6],[9,10,33,48,796,2886],[0]),u6 [218,155] [15,33,61,118,289,942,1361,1362],([73,7,1,2,3,4,5,6],[9,10,13,29,33,40,507,2887,2888],[0]),([0,1,2,3,155,191,5],[17,30,33,96,158,347,1361,2889,2890,2891],[]),u6 [230,96] [30,43,48,200,1275,2554,2618],u6 [155,98] [17,30,33,48,289,647,733,942,952,1140,1361,2892],e6 [681] [17,43,61,72,158,199,2893,2894],u6 [332] [33,43,48,1950,2895,2896,2897],e6 [682,155] [15,17,30,33,43,158,289,1361,1362,2898],e6 [683] [30,72,158,1551,2899],e6 [684,155] ([17,30,33,48,158,942,1362]++r 2900 4),e6 [155,12] [17,30,33,61,158,215,289,935,942,2904,2905],([32,498,1,2,3,4,5],[15,30,48,158,411,1535,2906],[]),([0,1,3,4,624,5],[43,63,215,2592,2593],[]),([0,1,2,3,155,126,5],[17,33,158,199,1362,2907],[]),e6 [118,110] [30,63,158,172,420,421,560,749,2511],e6 [409] [17,47,48,55,182,215,941,942,2908,2909],([367,0,1,2,4,126,98],[17,33,199,215],[]),u6 [409,155] [17,30,33,48,289,941,942,1361,1362,2910],([213,1,2,3,4,5,194],[17,33,47,189,917],[0]),e6 [205] [33,38,63,165,1708,2911,2912],([218,0,127,1,3,4,5,12],[15,61,96,157,1539,1540,1857,2033,2500],[]),e6 [685] [30,72,158,2158,2913],e6 [686] [17,30,48,199,2914,2915],e6 [80] [15,17,30,61,158,192,199,465,630,631,2505,2506],e6 [687] [15,17,2916,2917],e6 [185,127] [48,180,685,913,1624,1857,2062,2667],u6 [7,127] [9,17,30,40,48,311,1682,1857,2666,2667],e6 [688] [17,30,43,48,61,96,199,511,2918,2919],e6 [689] [17,43,48,61,63,96,215,305,2920,2921],e6 [690] ([15,33,96,182,194]++r 2922 4),([62,42,0,1,2,4,5,6],[17,33,199,236,389,488,637,655,1063,2682],[0]),u6 [59,12] [17,37,48,61,215,362,1130,1536,2926,2927],e6 [476,98] [30,33,34,199,216,647,695,1140,2925,2928,2929,2930],e6 [691] [15,38,48,96,118,2931],([158,165,0,411,1,3,4],[15,43,63,118,772,773,1324,2932],[0]),e6 [692] [43,48,63,96,2377,2933],e6 [693] [43,63,96,2934,2935,2936],u6 [286] [17,33,38,43,47,96,443,2937],e6 [694] [15,38,43,48,61,63,96,2938],([0,1,9,4,5,12],[4,5,30,33,63,82,96,215],[0]),e6 [695] [17,47,48,63,182,194,2475,2939],e6 [696] ([17,48,63,278,1352]++r 2940 4),e6 [281,138] [30,43,48,63,158,706,710,2944,2945],([281,0,1,8,3,4,12],[15,61,63,301,919],[0]),e6 [281,185] [48,180,199,356,425,685,913,1352,2378,2929,2946,2947,2948],e6 [697] [30,33,48,63,96,2949],e6 [698,6] [15,47,48,55,61,173,192,511,1063,1088,2950],e6 [699] ([30,48,158,1567]++r 2951 5),e6 [48,438] ([48,515,1127,1798,1799,1802]++r 2956 4),u6 [165,185] [48,61,63,225,685,913,1971,2453,2960],u6 [92,138] [17,30,43,48,182,358,706,1247,1367,1368,1567,2961,2962],u6 [309,89] [30,61,703,1369,2156,2158,2159,2963],e6 [43,155] [15,17,48,158,454,942,1361,1362,1903,2249,2964],([0,1,3,204,4,12],[33,43,63,215,2965,2966],[]),u6 [108,104] [30,33,43,47,48,118,120,158,185,241,243,850,875,1536],([158,0,1,18,4,5,98],[17,30,33,215,647,2967,2968],[]),([158,92,0,1,3,4,5],[33,43,1244,1851,2969],[]),([158,92,0,1,3,18,4,5],[17,30,43,1244,1245,1851,1852,1853],[]),([0,1,8,3,4,12,6],[55,63,173,301,919,2970],[0]),([0,1,279,18,4,5,98],[17,61,777,2971],[0]),([0,1,2,4,336,5,98],[17,30,215,1564],[]),e6 [152,6] [17,30,33,173,334,511,1432,1434,1438,2972,2973,2974],([395,0,1,8,3,4,5],[30,43,1196,2975,2976],[0]),([92,0,1,2,18,4,5,98],[17,30,33,61,1244,1564,1565,1566],[]),([158,165,110,0,1,3,4],[17,63,282,772,773,774,2977],[0]),([0,1,2,204,18,4,98],[17,30,33,779],[]),e6 [700] [17,30,48,158,199,2978,2979],e6 [263] [38,43,48,61,158,182,215,358,2980,2981,2982],([0,1,3,9,4,5,12],[5,17,33,55,63,82,215],[0]),e6 [92,263] [33,38,43,47,358,2980,2983],e6 [93] [33,38,47,96,199,965,2984,2985,2986],([92,290,0,1,2,3,5],[30,33,43,788,2987],[0]),u6 [263,18] [30,43,48,278,341,342,358,359,561,1247,2980,2982,2983],u6 [92,263,18] [43,342,358,710,2980,2982,2983],([201,101,1,2,3,4,5],[41,55,116,117,1064],[0]),e6 [435,6] [15,48,61,100,118,173,182,215,389,511,2988,2989,2990],([0,1,8,3,4,12,98],[5,17,33,61,63,118,2991],[0]),u6 [93,18] [30,61,278,341,342,710,740,2986],u6 [93,92,18] [30,61,358,561,741],e6 [701] [17,33,43,47,48,199],e6 [290,185] [48,180,225,913,1790,2717,2992,2993],([0,195,2,3,4,5,194],[17,33,72,438,2396,2540],[0]),e6 [702] [43,48,96,158,215,2994],e6 [42,150] [17,33,61,70,330,331,456,466,637,1386,1453,2974,2995],e6 [122] [33,38,47,118,1987],e6 [309] [17,30,33,48,158,199,2996,2997,2998],e6 [588,261] [33,48,354,356,535,2318,2450,2999,3000],([418,0,1,2,3,5],[17,33,43,61,1704,1705],[]),e6 [703] ([17,33,47,48,215,2605]++r 3001 4),e6 [704] [34,43,48,96,158,3005],e6 [705] ([43,47,48,96]++r 3006 4),e6 [476,18] [15,30,33,43,48,96,199,278,342,1247,2925,3010,3011],([0,104,1,8,3,4,12],[15,33,118,301,302,911,919],[0]),e6 [706] [30,48,96,182],e6 [708] [43,48,158,3012,3013],e6 [709] [33,38,43,63,3014,3015,3016],e6 [710] [17,30,43,48,61,96,182,199,1052,3017],([7,1,2,3,18,4,5],[9,12,13,30,40,48,55,61,69,233,234,2447],[0]),([101,1,2,3,18,4,5,6],[15,30,41,61,100,116,262,2447,3018],[0]),u6 [113] [30,48,55,61,158,192,255,256,761,762,811],([0,1,2,375,18,4,5],[17,30,96,3019],[0]),e6 [711] [30,72,158,3020,3021],e6 [712] [15,48,158,215,2990,3022,3023,3024],e6 [290,435] [15,30,38,118,1052,1722,1790,1864,2990,3025,3026],e6 [714] [33,38,63,3027,3028,3029],([698,1,2,3,4,5,6],[47,48,55,61,1088,2950,3030],[]),e6 [715] [15,38,48,61,72,158,182,215,3031,3032,3033],e6 [716] [33,47,48,3034,3035,3036],e6 [717] [15,38,48,72,118,158,182,1563,3037,3038],e6 [718] ([15,38,48,72,158,182,199,215]++r 3039 4),u6 [218,7] [9,13,40,48,61,96,100,118,211,213,821,1156,2988],([218,42,0,1,2,4,5],[17,43,61,637,3043],[]),e6 [719] ([30,158,2734]++r 3044 5),u6 [113,6] [30,43,48,61,100,192,256,511,761,762,811],e6 [720] [30,33,48,199,3049,3050],u6 [240] ([30,38,55,158]++r 3051 4),([0,1,3,4,721,191,5],[30,33,96,118,3055,3056,3057],[]),e6 [722] ([30,33,48,158,1762]++r 3058 5),e6 [32,365] [17,34,63,2472,2475,3063,3064],e6 [723] [17,30,47,48,118,3065],u6 [230,231] [15,17,33,48,61,63,96,509,540,1270,1957,3066],e6 [32,724] [15,48,1384,3067,3068,3069],e6 [725] ([17,47,63,72,96,199,215]++r 3070 5),u6 [200,18,6] [15,17,33,192,341,511,1097,1891,3075],e6 [726] [30,72,158,3076,3077],u6 [267] [17,30,47,72,158,199,368,3078,3079],e6 [727] [43,48,63,96,158,215,3080,3081,3082],e6 [384] [17,48,63,215,829,832,1149,1150],e6 [431] [38,48,118,158,2517],e6 [728] ([17,30,43,47,48,96,199]++r 3083 4),e6 [194] [17,33,38,43,47,72,96,158,1199,3087,3088],u6 [221,98] [15,48,61,199,215,603,647,682,1140,1390,3089,3090,3091],e6 [729] [15,48,96,215,2712,3092,3093,3094],([0,1,3,231,4,5,12],[17,33,61,118,834,977,3095,3096],[0]),u6 [323] [17,33,38,47,606,2608,3097,3098,3099],u6 [308] [33,38,61,158,3100,3101,3102],e6 [371] [17,47,48,61,158,2841,3103]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_8_4 : checkNodesBT W_22 g_22 F_22 P_22_8 A_22 B_22_7 8 N_22_8_4 = true := by decide +kernel
def N_22_8_5 : List NodeSpec := [([0,1,3,4,242,5,12],[61,96,118,280,743,3104,3105],[0]),e6 [730,98] [15,33,34,43,48,61,199,216,603,647,1140,2212,3106,3107,3108],([210,0,104,3,4,5,12],[15,30,118,123,243,322,563,564,3109],[0]),e6 [152,12] [17,30,33,334,402,666,1433,1435,1438,3110,3111],e6 [731] [17,33,47,48,61,3112,3113],([158,0,1,3,446,4,5],[33,43,63,118,774,1508,3114],[]),u6 [210,185] [43,48,61,96,180,682,3115],u6 [313,12] [33,43,63,96,187,402,420,421,665,666,667,935,1536,1848],u6 [32,155] [30,33,34,48,61,289,411,412,942,1361,3116,3117],([210,212,0,1,2,3,5],[33,43,218,3118],[0]),u6 [113,18] [30,33,61,255,278,341,761,762,811],([158,0,1,508,3,4,5],([15,43,63,118,425]++r 3119 4),[]),e6 [732] [17,30,47,48,2121,3123,3124,3125],e6 [210,570] [30,48,63,96,2881,3126],e6 [733] [15,33,63,158,182,2705,3127,3128,3129],e6 [591,6] [17,48,63,173,389,511,1063,2705],([0,168,1,2,9,4,5],[15,17,26,28,33,85,111,556,3130],[0]),([0,1,2,9,4,393,5],[17,28,33,96,556,873,1121],[0]),([307,0,1,2,9,4,5],[17,28,33,85,96,555,556,3131],[0]),([0,1,2,9,4,5,6],[17,28,33,63,85,173,556],[0]),e6 [307] [33,38,47,96,199,556,3131,3132],u6 [307,9] [17,28,33,85,96,182,555,556,3132],([0,1,2,9,4,126,5],[17,28,33,96,556,1199,3133],[0]),u6 [343,98] [17,33,673,682,683,952,1140,1625,3134],([210,108,0,1,3,4,5,12],[30,118,402,563,564,1764,1922,2282,2755],[]),e6 [166] [33,38,63,118,687,3135,3136],e6 [261,336] [15,17,55,3137,3138],e6 [356] [33,43,48,96,709,3139,3140],([275,0,8,3,4,12],[33,43,118,302,397,2244,2741,2742],[0]),e6 [734] [33,38,47,3141,3142],e6 [68,208] [30,33,157,1144,1711,3143,3144],([49,0,1,3,4],[16,19,32,46],[0]),([0,1,8,3,4,126,12],[17,55,911],[0]),([0,104,1,8,3,4,5,12],[15,33,118,301,302,919],[0]),([49,0,1,3,4,5],[16,19,30,32,33,46,63,96,215],[0]),u6 [246] ([17,33,43,63,96,182]++r 3145 5),u6 [261,8] [55,96,354,535,1630,2316,2452,2706,3150,3151],u6 [18,363] [30,61,278,3152,3153,3154],u6 [185,8] [17,33,48,61,118,225,913,2490,2946,3155,3156],([7,1,8,2,3,4,5],[13,33,40,48,67,100],[0]),e6 [233,32] [30,34,48,411,1549,1551,3157,3158],u6 [7,8] [13,17,40,48,63,67,85,1941,2316,2490,3150,3151,3159],([172,0,1,2,9,4,5],[15,17,26,28,33,61,111,556,3160],[0]),u6 [324] [17,33,47,48,173,199,607,3161,3162],u6 [299,98] [17,33,34,48,216,603,647,695,1140,1626,3163,3164],u6 [330,150] [17,30,215,330,334,626,1435,1453,3165,3166],([108,0,104,2,3,4,5],[30,43,118,120,185,187,241,243,850,851,875],[0]),([275,108,0,2,3,4,5],[43,48,72,118,808,810,850,2243,3167,3168],[]),([290,0,104,2,3,4,5],[17,30,158,185,187,241,243,322,1052,3169],[]),e6 [633,120] [17,63,182,421,2076,2077,2647,2648,3170],u6 [105,12] [33,105,243,258,430,666,881,1536,2391],([0,1,3,4,166,5,12],[33,63,118,3171,3172],[]),e6 [150,735,152] [334,1432,1433,3173,3174,3175],e6 [43,80,6] [15,33,48,192,630,631],([408,0,1,2,4,5,98],[17,61,118,938,3176],[0]),e6 [736] [30,55,63,182,2717,3177,3178],e6 [737] [15,33,48,1946,3179,3180,3181],e6 [738,238] ([30,33,48,323,624,1419]++r 3182 5),e6 [541,126] [15,17,48,61,182,199,1196,1425,1754,1943,1946,3187,3188],e6 [281,220] [15,33,43,63,331,1353,1513,1587,1939,3189],e6 [541,6] [48,55,70,173,389,511,1063,2524],u6 [185,279] [17,43,48,61,118,700,913,2212],([230,158,165,0,1,3,4],[15,17,33,63,215,226,540,773,774,1324,3190,3191,3192],[0]),e6 [541,98] [15,17,30,33,34,48,61,118,199,216,603,647,695,1140,1943,3193,3194],e6 [739] [30,48,96,199],([0,1,2,496,4,5,98],[17,30,33,96,199,3195,3196],[]),e6 [740] [30,72,158,1516,3197],e6 [741] [33,38,47,96,199,3198,3199],e6 [742] [15,30,38,48,72,158,182,199,3200,3201,3202],e6 [743,261] [15,43,48,55,354,535,2450,2452,3203,3204,3205],e6 [744] ([15,17,33,96,182,199]++r 3206 4),([0,1,2,3,524,5,6],[30,33,96,182],[]),([158,165,410,0,1,3,4],[15,33,43,63,118,226,772,773,774,1324,2757,3210,3211,3212],[0]),e6 [62,460] [30,48,63,158,194,3213,3214],([158,165,0,1,3,4,166],[33,43,63,118,226,687,3215],[0]),([158,165,0,1,3,4,126],[17,55,118,226,1196],[0]),([330,207,0,1,2,4,5],[30,43,118,3216,3217],[]),([158,0,1,3,4,166,5],[33,43,55,63,226,687,3215],[]),([158,165,0,1,3,4,6],[33,55,173,215,1324,3218,3219],[0]),e6 [476,12] [15,17,30,33,43,63,96,666,935,2925,3220],u6 [158,185] [17,30,33,180,199,1085,1488,2638,2946,3221],e6 [48,12] [15,33,37,48,1988,1989,1991],([158,338,0,1,3,4,5],[17,30,43,647],[]),([158,7,1,2,3,4,5],[9,10,13,29,55,566,3222],[0]),e6 [32,499] [34,48,96,215,411,412,413,2013,2745,2746,2747,3223,3224],([158,118,0,1,3,4,5],[30,43,118,172,173,677,3225],[]),e6 [745] ([48,63]++r 3226 5),([213,1,2,3,4,5,98],[17,33,61,2431,2702,2703],[0]),e6 [746] ([15,30,33,43,157,1117]++r 3231 5),e6 [410,126] [17,33,48,63,182,199,1425,1427,1578,1630,1754,2201,2757],([0,1,2,446,4,126,5],[17,33,43,1173,1199,3236],[]),e6 [479] ([15,30,43,118]++r 3237 5),e6 [167] [17,38,43,48,61,158,182,199,215,688,769,770,2084,3242],u6 [167,166] [33,43,47,688,769,825,2084,2085,2086],([42,0,1,2,4,126,5],[17,33,199,2541,3243],[0]),e6 [380] [17,47,48,61,118,182,215,825,826,3244,3245],u6 [380,166] [33,43,199,825,826,2084,2085,2407,2408,3244,3246],e6 [747] [17,33,47,48,1427,3247,3248,3249],([165,7,1,2,3,4,5],[9,33,48,61,69,100,477],[0]),u6 [165,7] [9,17,30,48,61,63,69,477,676,1971,2453,2546],e6 [127,438] [48,61,1798,2957,2959,3250,3251],u6 [7,12] [9,12,13,15,17,43,48,55,69,96,187,204,402,430,431,666,935,1172,1536,3252],u6 [158,7] [13,17,29,30,48,55,100,182,566,1085,1487,1488,2268,2638,3253,3254],e6 [42,165] [17,55,61,466,1900,2205,3255],u6 [18,365] [17,33,43,48,61,96,342,710,2474,2475,3256,3257],e6 [261,748] [48,55,354,3258,3259],([0,1,2,3,208,126,5],[17,33,199,215],[]),e6 [750] ([43,48,118,158,215]++r 3260 5),e6 [580,261] [55,354,535,1085,1630,2452,3265,3266,3267],e6 [751] [15,30,38,43,182,199,3268,3269,3270],([0,1,335,3,4,336,5],[17,33,3271],[0]),e6 [752] [15,17,30,199,1713,1857,3272,3273,3274],e6 [678,126] [33,1199,1425,1427,1630,1754,2221,3137,3275,3276],([92,0,1,2,3,126,5],[33,43,199,1427,3277,3278,3279],[]),e6 [753,126] [33,38,1196,1199,1425,1630,1754,2221,3265,3280,3281],([395,0,1,2,4,5,98],[17,30,199,215,695,3282],[]),u6 [32,30] [17,33,34,55,61,96,412,413,897,1592,1780,2677,3283],([212,0,1,2,126,5,98],[17,33,182,216],[]),([0,1,2,4,272,98],[17,30,63,215,956],[0]),([0,1,2,4,272,126,98],[17,33,55,956,958,1199],[]),e6 [367] [17,33,43,47,48,61,96,199,3284,3285],([0,1,2,3,4,272,194],[17,33,1199,3286,3287],[0]),([0,193,2,3,4,5,6],[43,55,127,139,152,192,511,3288],[0]),u6 [327] ([17,33,38,611,2624]++r 3289 4),e6 [754] [43,48,96,158,215,3293],([198,0,1,3,4,5],[17,30,43,989,2725,3294],[]),([198,0,1,3,4,5,194],[17,33,96,549,2725,3295],[0]),([42,0,1,2,4,5,194],[17,33,72,3243],[0]),([212,0,1,2,3,5,194],[17,33,72],[0]),u6 [96,98] [17,30,33,48,199,200,682,695,952,1861,2697,3296,3297],u6 [185,356,98] [48,709,952,3139,3140],([0,1,199,3,4,126,5],[17,55,1895],[]),([212,0,1,2,3,126,5],[17,33,55,199],[0]),e6 [185,280] [30,48,180,3298,3299],e6 [755,185] [43,48,180,685,913,1624,3300,3301],u6 [185,280,98] [17,695,913,3298],e6 [756] ([43,48,63,96,199,215]++r 3302 4),([0,1,2,9,4,5,98],[17,33,63,215,647,784],[0]),e6 [356,98] [33,61,709,3139,3140],e6 [757] ([15,17,63,72,158,199,540]++r 3306 4),e6 [229,92,18] [30,342,704,710,3310],e6 [620,185] [61,63,180,356,685,913,1624,2562,3311],u6 [185,301] [15,17,48,61,682,1002],([207,185,0,1,2,4,5,98],[30,61,63,225,2946,3312,3313,3314],[]),e6 [758] [17,48,96,199,515,1971,3315],u6 [355,98] [17,30,48,61,96,216,603,647,682,695,952,1140,1737,1738,3316],u6 [212,264] [33,61,1532,1626,1804],e6 [591,98] [17,33,48,63,118,199,216,603,647,952,1140,2705,3155],([158,165,0,1,3,4,98],[17,33,215,647,3317,3318],[0]),([0,1,279,3,4,5,301],[17,61,697,700,3319,3320],[0]),([418,0,1,2,3,5,98],[17,33,61,1003,3321],[0]),u6 [340,98] [17,33,61,118,216,603,646,647,682,1140,1923,3322,3323],([339,338,0,1,3,4,5],[17,61,118,645,647,648,649,3324],[0]),([212,0,1,2,3,5,6],[33,61,182,3325],[0]),e6 [759] [30,48,61,63,158,182,3326],([0,195,2,3,4,5,98],[17,33,61,1005,1006,1008,1140],[0]),u6 [24,6] [61,192,389,456,511,1063,1098,3327,3328],([0,1,199,3,4,5,98],[17,33,61,1009,1010,1012],[0]),([367,0,1,2,3,4,98],[17,61,199],[0]),e6 [760] [43,48,96,118,158,215,2080],e6 [761] [43,48,63,96,3329,3330,3331],([23,7,1,2,3,4,5],[13,29,38,40,48,61,69,820],[0]),e6 [762] ([33,43,48,118,158]++r 3332 5),([7,1,2,24,3,4,5],[9,12,13,30,48,61,84,100,205,1098,3327],[0]),([44,7,1,2,3,4,5],[9,10,12,13,29,30,40,48,61,69,252,3337],[0]),u6 [230,51] [17,61,63,290,971,3338,3339],([158,32,165,0,1,3,4],[15,17,33,96,118,226,412,772,773,1324,1325,3340,3341],[0]),([7,1,2,3,21,4,5],[9,13,40,48,55,100,640,1025],[0]),u6 [162,7] [13,17,40,43,48,61,100,931,3342],([0,1,2,3,30,126,5],[33,1196,1780,3343],[0]),([7,1,2,24,3,4,5,6],[9,40,48,61,100,205,1098,3327],[0]),u6 [253,148] [17,33,182,312,742,1527,2032,2033,2876],([7,1,2,3,21,4,5,6],[9,13,40,48,55,640,1025],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_8_5 : checkNodesBT W_22 g_22 F_22 P_22_8 A_22 B_22_7 8 N_22_8_5 = true := by decide +kernel
def N_22_8 := N_22_8_0 ++ N_22_8_1 ++ N_22_8_2 ++ N_22_8_3 ++ N_22_8_4 ++ N_22_8_5
def B_22_8 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_8
set_option maxRecDepth 500000 in
lemma B_22_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 8 xs.toFinset) B_22_8 := by
  have hP := buildPoolsSubBT_sound (pdepth := 12) (W := W_22) (raw := r_22) (pspecs := ps_22) (used := U_22_8) S_22_ok
  have hm0 := checkNodesBT_mem (by decide) gp_22 W_22_ok hP A_22_ok B_22_7_ok C_22_8_0
  have hm1 := checkNodesBT_mem (by decide) gp_22 W_22_ok hP A_22_ok B_22_7_ok C_22_8_1
  have hm2 := checkNodesBT_mem (by decide) gp_22 W_22_ok hP A_22_ok B_22_7_ok C_22_8_2
  have hm3 := checkNodesBT_mem (by decide) gp_22 W_22_ok hP A_22_ok B_22_7_ok C_22_8_3
  have hm4 := checkNodesBT_mem (by decide) gp_22 W_22_ok hP A_22_ok B_22_7_ok C_22_8_4
  have hm5 := checkNodesBT_mem (by decide) gp_22 W_22_ok hP A_22_ok B_22_7_ok C_22_8_5
  exact buildBucketsBT_of_mem (forall_append (forall_append (forall_append (forall_append (forall_append (hm0) hm1) hm2) hm3) hm4) hm5)
def U_22_9 : List Nat := ([5,10,15,17,26,28,29,30,33,34,38,40,43,47,48,54,55,61,63,70,72,85,86,96,100,101,116,118,123,134,149,157,158,165,173,182,185,187,192,194,199,200,211,212,215,216,226,236,238,241,243,247,262,274,278,282,285,289,290,293,302,303,305,311,330,331,334,341,342,358,362,367,382,389,402,411,412,413,415,420,425,430,441,454,456,466,471,474,478,485,504,509,511,515,521,540,556,560,563,574,589,594,603,609,621,624,632,642,647,649,661,666]++r 675 4++[682,687,691,695,700,703,704,709,710,714,718,730,739,742,749,773,774,808,810,813,825,832,850,874,879,897,911,917,919,935,936,942,947,952,962,971,977,1002,1045,1046,1052,1063,1064,1069,1083,1088,1091,1095,1097,1103,1117,1126,1127,1128,1130,1131,1132,1136,1140]++r 1143 4++[1148,1153,1156,1157,1159,1161,1163,1165,1169,1173,1177,1184,1196,1198,1199,1217,1218,1220,1229]++r 1241 5++[1247,1248,1253,1257,1265,1269,1270,1273,1274,1280,1285,1292,1296,1311,1316,1317,1324,1338,1339,1340,1346,1347,1351,1352,1355,1357,1358,1362,1367,1369,1377,1384]++r 1386 5++[1392,1393,1394,1397,1400,1403,1410,1413,1425,1427,1428,1433,1438,1439,1442,1444,1446,1450,1453,1457,1459,1460,1466,1471,1476,1478,1479,1481,1482,1483,1485,1487,1488,1490,1492,1494,1497,1498,1503,1507,1509,1510,1516,1518,1519,1520,1522,1524,1526,1527,1532,1535,1536,1537]++r 1540 4++[1547,1548,1551,1558,1560,1561,1563,1564,1566,1567,1578,1582,1584,1587,1591,1592,1597,1599,1611,1614]++r 1617 6++r 1624 4++[1630,1632,1637,1652,1653,1659,1661,1662,1667,1668,1671,1681,1684,1687,1689,1702,1713,1714,1715,1719,1721,1722,1742]++r 1745 4++[1752,1754,1757,1760,1761,1762,1764,1769,1771]++r 1773 5++[1780,1790,1792,1793,1799,1800,1808,1816,1823,1825,1827,1830,1831,1832,1841,1842,1843,1845,1851,1853,1855,1857,1859,1860,1861,1865,1867,1870,1871,1872,1881,1884,1885,1891,1903,1910,1916,1917,1922,1923,1929,1939,1942,1943,1946,1948,1959,1961,1971,1987]++r 1989 4++[2013,2018,2020,2021,2022,2024,2034,2040,2056,2065,2073,2076,2078,2079,2080,2084,2085,2087,2104,2130,2131,2134,2139,2153,2158,2159,2162,2163,2164,2169,2180,2186,2188,2191,2205,2212,2220,2243,2244,2248,2252,2267,2268,2278,2282,2285]++r 2287 4++[2292,2293,2298,2312,2316,2318,2335,2341,2350,2357]++r 2377 4++[2401,2407,2410,2416,2418,2422,2431,2432,2435,2442,2447,2452,2453,2464]++r 2474 4++[2483,2486,2489,2490,2491,2500,2507,2510,2512]++r 2516 5++[2524,2526,2528,2538,2541,2543,2545,2554,2562,2568,2585,2598,2600,2602,2605,2607,2608,2614,2615,2616,2618,2619,2622,2623,2624,2633,2638,2656,2666,2668,2670,2686,2692,2705,2706,2712,2717,2731,2733,2734,2744,2757,2758,2770,2771,2803,2805,2806,2814,2815,2837,2847,2853,2870,2925,2931,2936,2944,2946,2948,2961,2974,2988,2990,3016,3025,3029,3066,3136,3137,3150,3151,3165,3166,3172,3183,3186,3223,3252,3253,3255,3256,3264,3265,3316,3336]++r 3344 236)
def P_22_9 : BT (Option BoundPool) := buildPoolsSubBT 12 W_22 r_22 S_22 ps_22 U_22_9
def N_22_9_0 : List NodeSpec := [u6 [290,375] [61,63,199,215,1045,1046,1052,3344],u6 [375] [17,43,61,96,158,215,1045,1046,2350,3344],u6 [290,427] [30,55,61,96,215,1052,1722,2079,2080,3345,3346],e6 [290,763] [61,63,72,215,3347,3348],e6 [290,460] [30,38,47,61,63,215,1498,3349,3350],u6 [42,6] [17,55,61,100,173,199,236,389,466,511,1063,1865],u6 [6,194] [33,61,100,134,389,1063,3351],u6 [118] [30,43,47,61,72,96,118,158,609,749,2510],u6 [201,6] [33,43,55,100,173,389,511,1064,3352],u6 [200,6] [15,17,33,61,72,100,389,504,511,1097,3353],u6 [7,6] [29,33,38,40,47,48,55,61,100,173,511,1063],([7,1,2,3,4,5],[10,29,40,100],[0]),u6 [207,6] [30,33,55,63,100,215,1063,1392,2180],u6 [207,208] [17,30,55,63,182,215,1144,2526],u6 [208] [33,38,43,55,96,158,215,1144,1146,1148,2526],u6 [491] [17,30,43,55,96,158,215,1476,1478,1479,1481],e6 [207,764] [17,33,63,72,215,3354,3355],e6 [207,570] [30,47,55,63,215,2180,3356,3357],u6 [212,98] [17,33,61,182,199,215,216,603,682,1140,1532,3358],u6 [207,491] [17,30,55,96,215,1478,1479,1481],u6 [98,194] [17,33,61,216,603,682,2431,2432],u6 [290,98] [61,63,215,216,682,1046,1052],([207,0,1,2,4,5,98],[17,30,33,63,199,215,1520],[0]),u6 [338,98] [17,61,96,118,199,215,649,682,1494],u6 [98,301] [17,43,61,96,216,603,682,1002,3316,3359],u6 [264,98] [17,61,603,682,1140,1625,1626,1627],u6 [185,98] [17,61,118,216,603,682,709,1624,2946],u6 [185] [38,43,48,72,96,158,182,682,709,2946],u6 [512,126] [17,55,215,1630,3360],u6 [512] [17,30,38,43,47,63,72,96,158,215,3360,3361],u6 [367,126] [17,33,55,182,199,215,1630,1825,3362],u6 [126,194] [17,55,215,1630,1754,2543],u6 [272] [30,43,47,63,72,96,158,215,3363,3364],u6 [395,126] [17,55,96,118,1630,3365],u6 [395] [17,30,43,47,72,158,182,215,3365,3366,3367],u6 [588,126] [17,33,118,194,1196,1425,1630,1754,2318,3368],e6 [765,126] [17,33,55,72,1425,1630,1754,3369],e6 [260,126] [17,33,34,38,70,1630,3370],u6 [261] [38,43,47,48,55,72,96,158,215,1630,3371,3372],u6 [194] [17,33,38,43,47,61,72,96,158,917,1867,2541,2543],u6 [165,6] [33,61,63,100,215,2205,3255],u6 [165,98] [61,63,215,676,682,1971],u6 [165,166] [43,61,63,118,182,825,1971,2084],u6 [165,410] [43,47,61,63,118,2205,3373],u6 [410] [38,43,47,48,61,63,72,96,158,182,199,215,1578,2205,2757],u6 [158,290] [17,30,55,215,1487,1488,1498,1790,2268,2638,3374,3375],u6 [118,6] [43,61,96,100,192,389,511,609,677,749,1063,2510],u6 [158,6] [43,55,100,173,182,389,511,1487,2524,2638,3376,3377],([158,165,0,1,3,4,5],[33,63,96,215,226,773,774,1324],[0]),u6 [12] [30,61,72,96,118,158,215,1987,1989,1990,1991],u6 [166] [33,38,43,61,158,215,687,825,2084,2085,2407],u6 [524] [30,33,38,43,61,96,158,1774,1775,1776,2638],u6 [122,12] [33,43,61,118,187,402,666,935,1184,1536],u6 [6,192] [33,43,55,61,100,149,173,192,389,1063,1069,3378],u6 [122] [33,38,43,47,61,72,96,158,182,199,402,947,1184],u6 [290,12] [30,55,61,187,215,402,666,1052,1536,1722,3379,3380],u6 [126,12] [17,43,55,96,118,402,666,935,1427,1754,3381,3382],u6 [104,12] [30,43,61,118,123,185,187,241,243,666,1536],u6 [207,12] [30,55,187,215,666,935,1393,1394,1536],([0,104,2,3,4,5,12],[30,43,61,72,118,123,185,187,241,243,666],[0]),u6 [165,411] [33,43,63,72,118,3383],([0,104,2,3,4,5],[43,123,158,185,241,243],[0]),([0,1,8,3,4,5,12],[5,30,33,63,96,118,215,302,911,919],[0]),([0,1,8,3,4,12],[5,43,96,118,302,911,919],[0]),u6 [165] [33,43,47,63,72,96,118,158,182,3136],u6 [9] [17,26,28,85,96,158,215,556],u6 [591] [15,38,43,47,48,72,96,158,182,199,215,2705,2803,2806],u6 [210,98] [17,61,216,509,603,647,682,1140,3384],u6 [580,126] [33,118,1196,1425,1630,1754,3265,3385],([210,0,1,3,4,5,12],[33,61,96,118,215,402,563,977,2282],[0]),u6 [429] [33,61,96,158,1357,2292,2293,2410],u6 [231] [17,96,158,215,509,1270,1959,3386],u6 [221] [15,47,48,72,96,158,199,215,1390,3384,3387,3388],u6 [212] [33,38,43,47,61,72,96,158,199,216,1532,3358],u6 [651] [38,43,47,63,72,118,158,215,3389],u6 [261,126] [17,38,47,55,118,1630,1754,2452,3371],u6 [12,98] [17,43,61,96,603,666,695,935,1715,2476,3390],e6 [233,191] [30,33,118,215,1265,3391,3392,3393],u6 [233] [30,33,43,47,61,72,96,158,199,1551,3392],u6 [192] ([30,33,43,47,72,118,158,199]++r 2516 5),u6 [383,191] [30,33,96,118,832,1265,1884,1885],u6 [207,191] [30,43,96,215,1148,1265,1393,1394,3391,3393],u6 [126,336] [17,33,43,96,3137,3394],u6 [330] [17,47,61,72,118,158,199,215,3165,3166,3395],u6 [150,18] [30,33,43,47,96,215,278,330,334,341,710,1161,1247,1388,1453],u6 [281,150] [15,17,30,33,47,63,215,330,425,1453,2378,2948,3396],u6 [158,110] [17,47,61,63,96,215,282,560,1346,1487,2268,2524,2638],u6 [738,150] [15,17,30,33,43,47,215,330,331,1453,3183,3186,3397,3398],u6 [220] [43,118,158,215,331,1450,1471,1939,3399],u6 [150,238] [30,33,48,182,215,274,331,521,624,1163],([290,0,1,2,3,5,6],[30,33,55,61,63,182,215,1091],[0]),u6 [55,12] [30,33,38,43,54,61,70,96,187,215,303,402,430,666,935,1351,1482,1483,1536,1537,1543,1548],u6 [230,6] [47,48,55,61,100,173,182,215,389,511,1136,1274],u6 [55,218] [15,33,38,61,70,96,118,211,212,594,1156,1351,1482,1526,1845,3400,3401],u6 [150,12] [30,33,96,187,215,330,402,666,935,1397,1413,1453,1536,2288],u6 [55,62] [15,33,38,70,118,158,194,367,1351,1377,1446,1482,1526,1597,1632],([275,0,2,3,4,5,12],[30,43,61,118,158,187,808,810,2243,2244],[0]),([230,55,1,2,3,4,5],[33,47,48,55,61,70,215,1243,1274],[0]),u6 [134] [30,43,96,158,215,714,1457,1459,1460],u6 [158,48] [15,17,33,61,96,215,874,1127,1487,2638],u6 [71] [30,38,43,72,96,158,199,215,678,1157,1159,3402],u6 [107,230] [43,48,55,63,96,540,1316,1317],u6 [110,191] [17,30,43,61,63,96,282,560,661,1265,3391,3393,3403,3404],([230,150,1,2,3,4,5],[30,33,47,48,61,63,72,215,274,3405],[0]),u6 [480] [30,43,118,158,215,1351,1355,3406,3407,3408],u6 [648,150] [15,17,30,48,72,215,330,1453,2744,3409],u6 [32,68] [17,30,34,43,48,157,158,411,412,589,1384,2619,2656,3410],u6 [7] [10,29,38,40,43,47,48,72,96,100,158,182,199],u6 [309] [30,43,47,61,72,96,158,182,2159,3411],u6 [536] [33,61,96,118,158,215,1841,1842,1843,1845],e6 [43,479] [15,30,43,118,215,1466,2692,3412,3413,3414],u6 [42] [17,43,47,55,72,96,158,236,466,1063,1865],u6 [281,18] [17,30,33,43,55,96,278,341,710,1247,1870,2378,2948,3256],u6 [230,405] [43,61,63,540,3415,3416],u6 [432] [30,43,55,157,1103,1338,1339,1340,3417],u6 [32,8] [15,17,33,34,48,61,85,86,96,118,412,413,1942,2316,2490,2806,3151,3418],u6 [48,98] [17,33,48,61,118,215,216,603,647,682,1130,1140,1961],e6 [281,218] [15,61,96,118,211,425,594,1156,2378],u6 [55,29] [17,33,38,61,70,96,238,897,1131,1145,1351,1482,1483,1591,2847],u6 [110,12] [17,43,61,63,96,187,215,282,402,420,666,935,1536,1719,2022],([0,1,2,4,126,5,98],[17,33,55,199,215,216,1358,1808],[0]),u6 [8,6] [17,33,63,100,173,813,1063,2490,2806],u6 [281,32] [17,33,34,48,55,61,118,158,411,412,425,1587,2378,2948,3410],u6 [98,6] [61,216,511,682,1063,1140,1671,1992],u6 [345,32] [17,34,48,118,215,412,1761],u6 [48,32] [17,33,34,48,72,158,411,874,3410],u6 [475,230] [15,30,48,63,72,1136,1316,3419],u6 [110,8] [17,63,96,282,560,661,2316,2806,3151],u6 [150,29] [17,33,48,61,96,215,238,330,331,691,1145,1442,1453],u6 [351] [33,38,43,61,70,96,158,1667,1668,1687,3420],u6 [92,18] [17,30,33,43,182,199,278,341,358,710,1245,1247,1367],u6 [404,230] [30,43,48,540,1910],u6 [55,8] [17,33,38,70,85,96,215,1351,1526,2316,2490,2805,2806,3150,3151,3421],e6 [230,218] [48,61,63,96,118,211,540,594,1136,1156,2554],u6 [55,68] [17,30,33,38,43,70,157,158,303,589,1351,1482,1483,1617,1618,1621,2619,2656],u6 [151] [17,30,43,72,96,158,182,215,2335,3422,3423],u6 [515] [33,38,61,96,158,215,1742,2489,2490,2491],u6 [55,207] [33,38,70,118,215,1351,1392,1526,2180,2357],u6 [335,126] [17,43,55,96,1630,3424],u6 [281,55] [15,17,33,38,70,158,425,1482,1483,1872,2378,2948],u6 [165,126] [17,33,96,118,199,1425,1630,1754,2085,2205],u6 [296] [17,38,43,70,72,96,158,215,1526,1916,1917,3425],u6 [32,165] [17,33,34,43,48,61,118,413,1971,2085,2205,2453,2507,2545,3426],u6 [43,127] [15,17,30,43,47,72,158,311,454,1857,1903,2380,2464,2483,2486],u6 [66] [30,43,215,293,1377,1611,1614,3427],u6 [210,62] [15,33,61,96,158,194,367,509,1377,1632],u6 [62,266] [30,61,96,158,194,367,1377,1713,1714,1747,1748,2130],e6 [43,766] [15,48,72,118,158,1903,2483,3428,3429,3430],u6 [345] [17,34,38,43,48,61,72,96,158,182,1761,2248],u6 [155] [33,38,43,96,158,215,289,415,942,1362],u6 [281,191] [17,33,43,61,425,1265,1352,1587,3391,3403,3431,3432],u6 [570] [30,38,43,47,48,55,63,72,96,158,182,215,2180,3357],u6 [68,150] [17,30,33,157,158,274,330,334,589,1444,1453,2619,2656],u6 [281,8] [15,17,33,63,2316,2378,2806,3151,3433],u6 [281,266] [17,47,61,72,96,425,1713,1714,2948],u6 [575] ([15,33,43,158,182,215,2538]++r 3434 4),u6 [272,126] [17,33,55,118,215,1757,3363,3364,3438],u6 [281,210] [15,17,33,96,425,1587,3384,3439,3440],u6 [43,6] [15,30,43,48,61,100,173,182,192,215,389,456,511,1063,2380,3441],u6 [150,126] [30,33,118,182,215,331,334,1196,1630],u6 [150,191] [30,33,43,47,96,215,274,1265,3391,3393,3403,3442,3443],u6 [158,127] [15,17,30,215,1857,2268,2486,2638,3433],u6 [150,98] [30,33,34,61,118,215,216,330,331,334,603,647,682,1140,1777,2512],u6 [281,12] [43,55,96,187,215,425,666,1352,1536,3444],u6 [257,32] [34,48,96,118,411,412,3410,3445],u6 [270] [17,30,72,96,158,182,215,1823,1827,2130,3446],u6 [290,110] [17,30,63,158,215,282,560,661,1052,1722,2771],u6 [207,68] [30,33,157,158,589,1148,1393,1394,2619],u6 [62,150] [15,30,33,47,118,158,194,215,274,330,331,334,367,1377,1453,1632,2853],u6 [108,12] [30,43,47,118,187,402,666,850,935,1922],u6 [260,32] [17,34,48,70,118,182,412,1689,3447],u6 [499] [47,63,72,96,158,215,2013,3223],u6 [230,62] [15,30,48,55,61,63,118,158,194,367,540,1136,1316,1377,1632,2554],u6 [150,6] [30,33,61,70,100,173,182,215,274,331,389,511,1063,2974],u6 [290,18] [30,43,96,215,278,341,1046,1052,1247,1722],u6 [68,126] [17,30,33,55,157,589,1425,1428,1630,1754,2619,2656],([218,0,1,3,4,5,12],[61,96,118,935,1540,1542,1547],[0]),u6 [32,6] [34,38,48,55,61,100,101,118,173,182,215,389,411,412,511,1063,1689],e6 [290,767] ([15,17,30,43,55,215,1790]++r 3448 4),u6 [110,98] [17,61,63,118,215,216,603,647,661,682,1140,2153],u6 [230,158] [15,17,30,43,48,61,63,215,540,1487,1488,2268,2524,2638,3452,3453],u6 [281,43] [15,17,33,43,61,158,454,1587,1903,2378,2379,2380,2483,2948],u6 [460] [30,38,43,47,48,61,63,72,96,158,182,199,215,1253,1498,3350],u6 [158,98] [17,43,61,603,647,682,1140,1488,2524],u6 [290,32] [30,34,38,48,61,63,118,215,411,412,413,1046,1052,1689,2614],u6 [290,68] [17,30,157,158,589,1046,1052,1722,2619],u6 [405] [43,61,63,118,158,540,1169,1503,3415,3416],u6 [345,98] [17,34,61,682,3454],u6 [541] [15,30,38,43,47,48,72,96,158,182,199,1943,1946,2524],e6 [768,191] ([33,43,61,72,118,1265,3403]++r 3455 4),u6 [152] [17,43,96,158,215,334,1433,1438,3459],u6 [661] [30,43,48,96,158,215,2814,2815,3460,3461],u6 [62,43] [15,30,47,118,158,194,367,1903,2380,2418,2483],u6 [266,98] [61,603,647,682,1140,1713,1714,2130],u6 [218,110] [47,61,63,96,118,211,282,560,594,661,1156,1760,1845],u6 [32,29] [17,34,48,61,96,238,412,897,1145,3410],u6 [114] [43,48,63,96,158,215,305,560,2018,3462],u6 [279,98] [17,43,61,96,199,682,700,2212,3463],u6 [32,12] [17,34,43,55,61,96,118,187,215,402,666,935,1242,1536,3410,3464,3465],u6 [305] [43,55,61,96,158,182,2056,3466,3467]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_9_0 : checkNodesBT W_22 g_22 F_22 P_22_9 A_22 B_22_8 9 N_22_9_0 = true := by decide +kernel
def N_22_9_1 : List NodeSpec := [u6 [338] [17,30,43,47,61,72,96,158,182,649,1490,1492,1494],e6 [281,207] [17,33,63,194,1393,1394,2180,2378],u6 [150,152] [17,30,33,48,215,330,331,334,1433,1438,3459],u6 [520] [30,33,48,61,96,158,215,1745,1746,1747,3468],u6 [32,127] [17,30,33,34,48,158,289,311,411,1681,1857,3410],u6 [110,6] [17,33,61,63,100,173,215,282,389,511,560,1063,2078],u6 [210,207] [17,33,96,215,509,1148,1392,2180,3384],u6 [462] [33,72,96,158,182,199,215,1257,2186,2188,3469],u6 [68,6] [17,30,43,61,100,157,192,215,389,511,1063,1637,2619,2656,3470],u6 [210,150] [17,33,47,96,215,274,331,334,509,3384],u6 [48,266] [17,33,47,48,96,874,1127,1713,1714],u6 [383] [43,47,63,72,158,199,215,832,1410,1885],u6 [148] [17,43,96,215,311,742,1527,3471],u6 [339,98] [17,61,118,603,647,682,1140,1923,3472],u6 [408] [17,47,55,72,96,118,158,182,199,936,1522,1524],u6 [238] [33,43,48,96,158,215,274,521,624,1163],u6 [207,266] [17,30,96,215,1392,1713,1714,1747,2130,2180,3473,3474],u6 [427] [30,43,61,72,118,158,215,1790,2079,2080,3345,3346],u6 [278,230] [30,38,48,55,61,70,182,540,1274,3475],u6 [318] [30,33,43,47,72,96,182,199,215,2435,2598,2600,2602],u6 [12,6] [43,55,96,173,192,215,389,402,511,666,1536,2686,3252,3476],u6 [108] [30,38,43,47,48,72,96,158,182,199,1536,1762,1764,1922],u6 [476] [15,33,38,43,47,48,96,158,182,199,2298,2925,2948,3477],u6 [110,18] [17,30,43,63,96,278,282,341,560,661,710,1247,1816],u6 [479] [15,43,55,158,182,1466,3412,3413,3414],u6 [266,126] [17,30,33,55,61,1196,1425,1630,1747,1754,2130],([101,1,2,3,4,5,6],[33,55,61,100,116,262,1083],[0]),u6 [266,127] [17,30,1713,1714,1747,1857,2486],u6 [8,126] [17,33,96,199,1199,1630,2490,2706,2806],u6 [441] [30,55,61,96,158,1126,1128,2073,3478],u6 [210,110] [17,33,47,61,63,96,282,560,3384,3439],u6 [230,191] [30,43,61,1265,1274,3391,3393,3403,3479,3480],u6 [618,32] [34,43,48,118,411,412,2616,3410],e6 [230,207] [30,33,34,55,63,118,215,1148,1392,1393,2554],u6 [367] [33,43,47,61,72,96,158,182,199,1825,3362,3481],u6 [78] [17,30,43,158,215,412,621,2285,2287,3482],u6 [29,126] [17,33,55,61,238,897,1145,1153,1196,1630,1754],u6 [127,12] [17,30,33,157,187,215,402,666,935,1536,2500,3483],u6 [266,6] [17,61,100,173,389,511,1063,1713,1747,2131,3484],u6 [141] [33,43,48,61,96,158,730,2139,3485,3486],u6 [281,290] [61,63,215,1052,1498,1587],u6 [59] [17,43,48,96,158,215,362,1130,3487,3488],u6 [158,55] [15,17,33,38,61,70,96,215,1351,1482,1483,1487,1488,1519,1526,2268,2524,2638,3253,3489,3490],u6 [48,150] [15,17,33,47,48,72,158,215,330,874,1127,1130,1389,1453],u6 [84] [15,43,118,158,215,454,474,1217,1218,1220],u6 [257] [17,30,43,48,72,158,182,215,454,2341,3491,3492],u6 [320] [33,34,43,96,158,215,1241,1689,2568,3493],u6 [230,29] [17,61,72,96,158,238,1145,1316,2554],u6 [534] [15,33,43,48,158,215,1830,1831,1832,2380,3494],u6 [55,98] [33,38,61,70,118,215,216,603,647,682,952,1140,1143,1351,1482,1526,1620],u6 [655] ([43,48,118,158,215,1127]++r 3495 4),u6 [281,6] [33,55,61,72,100,182,389,511,1587,2948,3499,3500],e6 [43,534] [15,43,48,118,182,1830,1831,1832,2380,3494],u6 [32,191] [17,30,34,43,48,61,96,118,182,411,412,1265,1384,1689,3391,3393,3403,3501],u6 [423] [30,33,43,96,158,215,1403,3502,3503,3504],u6 [707] [33,43,47,63,72,158,182,215,3016,3505],u6 [749] [43,48,72,118,158,182,215,3264,3506,3507],([7,1,2,3,4,5,6],[10,29,33,40,55,61,100],[0]),e6 [207,769] [15,30,43,55,215,3508,3509,3510],u6 [29,6] [17,33,61,100,158,173,389,897,1132,1145,2220],u6 [278,6] [33,38,55,61,70,100,3511],u6 [63] [33,43,96,194,215,642,1632,2040,2416],u6 [150,220] [30,33,48,215,330,331,1386,1450,1471,1939,3399],u6 [55,18] [30,33,38,43,70,96,199,278,341,342,704,710,1247,1351,1482,1526,1871],([0,1,2,9,4,5],[26,28,85,96,215,556],[0]),u6 [127,126] [17,33,72,199,289,1199,1425,1630,1754,2486,2668],u6 [627,32] [15,17,34,48,72,118,194,411,412,2633,3410],u6 [48,8] [15,17,33,96,1130,2316,2806,3151],u6 [55,127] [15,17,30,33,38,70,158,289,311,1351,1482,1483,1526,1857,2278,2486,2666,3512],u6 [43,575] ([15,30,43,118,2380]++r 3434 4),u6 [48,43] [15,17,43,47,48,72,158,874,1903,2483,3513],u6 [165,110] [17,43,63,158,420,560,661,1971,2453,3514],u6 [43,126] [17,30,33,55,118,1196,1425,1427,1630,1754,1903,2380,3515],u6 [643] [30,33,43,47,96,215,2731,3516,3517],u6 [158,32] [15,17,34,48,55,61,96,118,215,411,412,1487,1488,1948,2267,2268,2524,2638,3518],u6 [107] [30,43,48,61,72,118,158,182,3336,3519,3520],u6 [346] [17,30,43,55,72,96,158,182,2252,2554,3521,3522],u6 [43,98] [17,30,61,96,118,215,216,603,647,682,695,1140,1903,2380,3523],u6 [89,18] [17,30,43,278,341,703,710,739,1369,1584],u6 [120] [17,43,63,96,158,215,471,661,962,2076],u6 [29,98] [61,158,238,603,647,682,1347,3524],u6 [599] [30,33,38,43,72,118,158,215,2380,3525,3526],u6 [207,43] [17,30,33,43,215,454,1148,1393,1394,1881,1903,2180,2380,2483,2528,3527],u6 [138] [30,38,43,47,48,72,158,182,215,710,2944,2961],u6 [278] [33,38,43,61,70,72,96,158,199,1652,1653,1659,1684],u6 [158,126] [17,55,118,1196,1425,1488,1630,1754,2638],u6 [290,43] [30,38,43,215,454,1046,1052,1498,1721,1722,1903,2380,2442,2483,2717],u6 [260] [17,33,38,43,72,96,158,215,1689,3447,3528,3529],([0,1,3,18,4,5,12],[30,43,55,96,215,935,2020,2021,2024],[0]),u6 [230,292] [17,43,61,63,96,540,1929,3530,3531],u6 [345,230] [30,34,48,61,199,540,1296,2554],u6 [37,6] [15,17,33,43,61,173,285,478,511,675,1095],u6 [468] [30,38,43,61,96,158,1274,1285,1292,1752],u6 [230,468] [30,38,48,63,215,1274,1285,1752],u6 [230,98] [30,47,61,63,118,215,216,603,647,682,1136,1140,2554,3532],([165,0,1,3,4,5,12],[33,43,63,96,118,3172],[0]),u6 [438] [34,43,61,96,158,182,1799,1800,3533],u6 [18,6] [30,43,55,61,173,192,215,278,511,710,1063,1247,1891,2447],u6 [230,48] [15,17,48,61,63,72,158,874,1127,1130,1136,1316,3534],u6 [230,281] [15,47,61,63,158,215,425,1136,1316,2948],u6 [51] [17,47,96,158,215,238,247,290,971],u6 [230,18] [30,43,199,278,341,710,1136,1247,1248,1316,2554,3535],u6 [230,210] [15,17,30,33,48,61,63,96,182,509,540,1136,1274,2554,3066,3384,3439],u6 [508] [33,43,63,118,425,2931,3536,3537,3538],u6 [230,165] [43,61,63,96,676,2205],u6 [230,126] [30,33,38,48,55,61,118,182,1136,1196,1425,1630,2554],u6 [290,29] [17,61,72,96,158,215,238,691,897,1145,1497,1722,2615],e6 [230,290] [30,48,61,63,70,215,1046,1052,1274,1722,1790],u6 [55,165] [33,38,43,70,96,303,676,1351,1509,1526,2087,2205],u6 [281,98] [61,72,118,603,647,682,1140,2378,2948],u6 [230,68] [17,30,43,48,63,157,158,589,1136,1273,1316,2554,2619,2656],u6 [85] [15,38,48,96,158,182,199,215,879,1145,1198,3539],([158,0,1,3,4,191,5],[30,33,43,61,96,118,182,215,1661,2289,2290,2638],[0]),u6 [30] [33,38,61,96,215,897,1592,1780,3540],u6 [369] [30,47,157,158,182,199,215,1117,1311,2656,3541],u6 [230,8] [15,17,33,61,63,85,215,540,2316,2490,2554,3151,3542],u6 [322] [33,47,72,96,182,199,215,2605,2607,2608,3543],u6 [445] [55,61,96,158,1165,1177,1400,1622],u6 [207,29] [17,33,55,63,96,215,238,897,1145,1394,2180,3544,3545],u6 [207,110] [17,63,158,215,560,661,1393,1394],u6 [127,18] [30,33,43,72,96,278,289,311,341,710,1247],u6 [48,218] [15,33,61,96,118,211,594,1127,1130,1156,1845],u6 [281,126] [17,33,55,1425,1630,1754,2378],u6 [326] [33,43,215,1229,2622,2623,2624,3546],u6 [68,98] [17,30,43,61,157,215,216,589,603,682,1140,1619,2619],u6 [138,18] [17,30,43,278,341,710,1247,1439,1567,2961],u6 [62,191] [30,33,43,61,96,118,194,367,1265,1269,1632,3391,3403],u6 [214] [15,43,96,158,182,194,215,367,2712],u6 [76] [43,118,157,485,589,632,2191,2401],u6 [241] [15,43,47,48,96,158,199,215,718,874,3547,3548],u6 [110,126] [17,33,55,63,118,560,661,1196,1425,1630,1754],u6 [230,346] [30,55,63,2252,2554,3521],u6 [62,8] [15,33,61,85,118,194,1632,2316,2490,2806,3151],u6 [62,12] [43,55,61,96,118,187,194,215,402,666,1377,1536,1599,2104],([0,1,2,18,4,5,98],[17,30,61,96,199,215,695,1564,1566,2670],[0]),u6 [282,6] [55,61,72,100,389,511,1088,3549],u6 [158,62] [15,55,61,96,118,158,194,215,367,1377,1488,1632,1662,2268,2638],u6 [62,165] [33,61,63,118,158,194,367,1377,1632,1971,2085,2205,2453,2758,3550],u6 [62,6] [33,55,61,100,118,173,194,215,367,389,511,1063,1377,1632,2312],u6 [127,98] [17,30,33,194,311,603,682,1140,3551],u6 [290,62] [30,55,61,63,118,158,194,215,367,574,1046,1052,1377,1632,1792],u6 [281,165] [61,63,157,1971,2205,2453],u6 [48,18] [17,30,33,43,48,96,278,341,710,874,1130,1247,1387],u6 [48,12] [17,33,43,48,61,96,187,215,402,515,666,935,1536,1541,2837],e6 [158,207] [30,55,118,215,1392,1487,1488,2180,2268],([0,1,3,4,191,5,12],[30,33,96,118,215,402,2162,2163,2164],[0]),e6 [230,770] [30,48,63,72,158,1136,1316,3552,3553],u6 [48,165] [17,33,43,48,72,96,158,515,676,874,1130,1971,2205,2453,3554,3555],u6 [230,127] [17,30,33,63,215,289,311,1274,1316,1857,2034,2554,3556],u6 [218,127] [15,33,61,118,211,289,311,1845,1857,2486,3557],u6 [498] [15,30,38,43,47,48,72,96,158,182,199,215,1535,2486],u6 [620,98] [61,118,194,603,647,682,1140,2562,3558],u6 [131] [43,63,118,158,182,215,382,1280,3559,3560],u6 [92] [33,38,43,47,72,158,182,215,358,1244,1245,1247],u6 [446] [17,43,61,118,158,215,676,1173,1507,1510],u6 [128] [30,43,118,158,215,1855,1857,1859,1860,3561],u6 [127,191] [17,30,43,72,96,289,311,1265,3391,3393,3403],u6 [158,150] [15,17,30,33,47,215,330,331,1453,1485,1487,1488,2268,2524,2638,3562,3563],u6 [210,32] [17,33,34,48,61,96,411,412,509,1689,3384,3439,3440],u6 [48,207] [17,33,48,158,215,874,1130,1393,1394,2180],u6 [210,127] [15,17,33,158,289,1857,2486,3440],u6 [127,6] [17,30,33,61,100,173,289,389,511,1857,2486,3564],u6 [285] [17,33,43,55,63,96,158,2377,2378,2936,3565],u6 [151,32] [30,34,48,118,412,413,2335],u6 [365] [38,43,61,63,96,158,1587,2474,2475,3566],u6 [8,98] [17,33,61,63,85,118,647,682,3567],u6 [191,98] [17,61,118,216,695,1265,2477,3393,3568],u6 [281,158] [15,17,61,158,425,1487,2268,2524],u6 [496] [17,30,43,55,96,158,1488,1516,1518,3569],([158,0,1,3,18,4,5],[17,30,43,55,96,199,215,1488,1851,1853],[0]),u6 [336] [17,30,43,158,215,1247,2870,3570,3571],u6 [204] [33,43,47,63,72,96,158,165,215,2134,3572],u6 [204,18] [17,30,33,43,96,165,278,341,1582,2134],u6 [290,266] [17,30,96,215,1498,1713,1714,1747,1790,1793,2130,3573],u6 [301] [17,30,43,47,61,72,158,182,1702,1769,1771,1773],u6 [309,18] [17,30,43,96,215,278,341,1247,2158,2159,3411],u6 [256] [61,96,118,158,1558,1560,1561,1563],u6 [218,150] [15,33,47,61,96,118,211,215,274,330,331,334,441,594,1156,1453,3574],u6 [713] [33,47,63,72,96,158,215,3029,3575],u6 [96] [33,43,157,200,215,1861,2618,2619,3576],u6 [218,6] [61,100,118,173,389,511,594,1063,1156,1845,2169,2988],u6 [559] [43,61,96,158,182,194,2065,2422,2585],u6 [435] [15,72,96,118,158,182,215,594,2990,3025],u6 [290,218] [61,96,118,211,594,1046,1052,1156,1498,1722,1790,1845,2770,3577],([158,165,0,1,3,4],[43,96,118,226,773,1324],[0]),u6 [230,12] [30,43,55,61,63,96,187,215,540,666,935,1136,1316,1536,3578],u6 [239] [30,38,43,47,48,61,72,158,182,199,215,2733,2734,3403,3579],e6 [239,191] [30,43,48,61,118,1265,3391,3393,3403,3579]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_9_1 : checkNodesBT W_22 g_22 F_22 P_22_9 A_22 B_22_8 9 N_22_9_1 = true := by decide +kernel
def N_22_9 := N_22_9_0 ++ N_22_9_1
def B_22_9 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_9
set_option maxRecDepth 500000 in
lemma B_22_9_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 9 xs.toFinset) B_22_9 := by
  have hP := buildPoolsSubBT_sound (pdepth := 12) (W := W_22) (raw := r_22) (pspecs := ps_22) (used := U_22_9) S_22_ok
  have hm0 := checkNodesBT_mem (by decide) gp_22 W_22_ok hP A_22_ok B_22_8_ok C_22_9_0
  have hm1 := checkNodesBT_mem (by decide) gp_22 W_22_ok hP A_22_ok B_22_8_ok C_22_9_1
  exact buildBucketsBT_of_mem (forall_append (hm0) hm1)
def U_22_10 : List Nat := [34,38,43,47,70,72,85,96,100,118,158,182,187,199,211,215,216,238,274,289,311,334,341,367,389,402,509,560,589,594,603,661,682,710,874,897,935,1046,1063,1130,1145,1148,1247,1274,1316,1394,1453,1483,1488,1498,1526,1536,1587,1630,1632,1689,1714,1722,1747,1754,1845,2085,2130,2180,2205,2268,2378,2380,2453,2483,2486,2490,2524,2554,2619,2638,2656,2806,2948,3151,3384,3391,3393,3403,3410,3440]
def P_22_10 : BT (Option BoundPool) := buildPoolsSubBT 12 W_22 r_22 S_22 ps_22 U_22_10
def N_22_10 : List NodeSpec := [u6 [126] [96,158,182,199,1630,1754],u6 [165] [43,47,72,96,118,158,182,199,215,2085,2205,2453],u6 [8] [85,96,158,199,215,2490,2806,3151],u6 [191] [43,96,118,158,182,3391,3393,3403],u6 [18] [43,96,158,199,341,710,1247],u6 [12] [43,72,96,118,158,187,402,935,1536],u6 [110] [47,72,96,158,182,199,560,661],u6 [218] [47,72,96,158,182,199,211,594,1845],u6 [266] [47,72,96,158,182,199,1714,1747,2130],u6 [29] [47,72,96,158,238,897,1145],u6 [98] [96,158,199,216,603,682],u6 [55] [38,47,70,72,96,158,182,199,1483,1526],u6 [62] [47,72,96,158,182,199,367,1632],u6 [32] [34,47,72,96,158,182,199,1689,3410],u6 [48] [47,72,96,158,182,199,874,1130],u6 [290] [47,72,96,158,182,199,215,1046,1498,1722],u6 [207] [47,72,96,158,182,199,215,1148,1394,2180],u6 [150] [47,72,96,158,182,199,215,274,334,1453],u6 [230] [47,72,96,158,182,199,1274,1316,2554],u6 [6] [47,96,100,158,182,389,1063],u6 [158] [47,72,96,158,182,199,1488,2268,2524,2638],u6 [43] [43,47,72,96,118,158,182,199,2380,2483],u6 [68] [43,47,72,96,158,182,199,589,2619,2656],u6 [127] [47,72,96,158,215,289,311,2486],u6 [210] [47,72,96,158,182,199,509,3384,3440],u6 [281] [47,72,96,158,182,199,1587,2378,2948]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_10 : checkNodesBT W_22 g_22 F_22 P_22_10 A_22 B_22_9 10 N_22_10 = true := by decide +kernel
def B_22_10 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_10
set_option maxRecDepth 500000 in
lemma B_22_10_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 10 xs.toFinset) B_22_10 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_9_ok C_22_10
def U_22_11 : List Nat := [47,72,182,199]
def P_22_11 : BT (Option BoundPool) := buildPoolsSubBT 12 W_22 r_22 S_22 ps_22 U_22_11
def N_22_11 : List NodeSpec := [u6 [] [47,72,182,199]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_11 : checkNodesBT W_22 g_22 F_22 P_22_11 A_22 B_22_10 11 N_22_11 = true := by decide +kernel
def B_22_11 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_11
set_option maxRecDepth 500000 in
lemma B_22_11_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 11 xs.toFinset) B_22_11 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_10_ok C_22_11
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_22_ok : forestRootCheck r_22 g_22 [(VAR 0,22,23),(VAR 1,12,14),(VAR 2,10,14),(VAR 3,6,14),(VAR 4,7,23),(VAR 5,3,35)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_22_in : bucketContainsBT B_22_11 r_22 = true := by decide +kernel
lemma low_22 : Lower r_22 g_22 12 := lower_of_forestBT root_22_ok B_22_11_ok root_22_in

def g_orig := (d 0xfeeaeae8eea8e0a0)
set_option maxHeartbeats 0 in
lemma low_orig : Lower (varsOf 63) g_orig 12 := carry_of (swaps := [(0,5),(1,3),(2,4),(3,4)]) (by decide +kernel) low_22
def targetFn (x : Fin 6 → Bool) : Bool := Nat.testBit (4276808424 * 2 ^ 32 + 4004044960) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def temoin : List Gate := [⟨.or,[3,0]⟩,⟨.or,[0,2]⟩,⟨.or,[3,2]⟩,⟨.and,[6,2]⟩,⟨.and,[5,7]⟩,⟨.and,[8,0]⟩,⟨.or,[1,11]⟩,⟨.and,[6,4]⟩,⟨.or,[9,10]⟩,⟨.and,[12,14]⟩,⟨.or,[10,12]⟩,⟨.and,[16,13]⟩,⟨.or,[15,17]⟩]
lemma temoin_ok : PEqualNP.MetaComplexity.Monotone2 ⟨temoin, 18⟩ := by
  intro g hg; simp [temoin] at hg; rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxHeartbeats 0 in
lemma tgt_eq_G : ∀ r : Row, targetFn (evalInput6 r) = g_orig.testBit r.val := by decide +kernel
set_option maxHeartbeats 0 in
lemma temoin_eval : ∀ r : Row, Circuit.eval ⟨temoin, 18⟩ (List.ofFn (evalInput6 r)) = g_orig.testBit r.val := by decide +kernel

end PEqualNP.Outside.L_meta_45570

open PEqualNP.Outside.L_meta_45570 in
theorem PEqualNP.Outside.L_meta_45570 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808424 * 2 ^ 32 + 4004044960) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808424 * 2 ^ 32 + 4004044960) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  exact replace_of_lower6 g_orig (by decide) (by decide) (by decide) 12 low_orig temoin 18 (by decide) temoin_ok targetFn tgt_eq_G temoin_eval
