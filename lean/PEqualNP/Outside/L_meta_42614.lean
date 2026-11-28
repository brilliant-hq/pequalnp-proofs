import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_42614.Core

def unpack (packed width index : Nat) : Nat :=
  (packed >>> (width * index)) &&& ((1 <<< width) - 1)

def decodeNode (parentWidth width packed index : Nat) : Nat × Nat :=
  let entry := unpack packed width index
  (entry &&& ((1 <<< parentWidth) - 1), entry >>> parentWidth)

def treeBlock (start count : Nat) (check : Nat → Bool) : Bool :=
  (Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ next i => check i && next (i + 1)) count) start

theorem treeBlock_at {start count i : Nat} {check : Nat → Bool}
    (h : treeBlock start count check = true) (lo : start ≤ i) (hi : i < start + count) :
    check i = true := by
  induction count generalizing start with
  | zero => omega
  | succ count ih =>
    change (check start && treeBlock (start + 1) count check) = true at h
    rcases Bool.and_eq_true_iff.mp h with ⟨here, rest⟩
    by_cases eq : i = start
    · simpa [eq] using here
    · exact ih rest (by omega) (by omega)

theorem treeBlock_merge {start left right : Nat} {check : Nat → Bool}
    (a : treeBlock start left check = true)
    (b : treeBlock (start + left) right check = true) :
    treeBlock start (left + right) check = true := by
  induction left generalizing start with
  | zero => simpa using b
  | succ left ih =>
    rw [Nat.succ_add]
    change (check start && treeBlock (start + 1) (left + right) check) = true
    change (check start && treeBlock (start + 1) left check) = true at a
    rcases Bool.and_eq_true_iff.mp a with ⟨here, rest⟩
    exact Bool.and_eq_true_iff.mpr ⟨here, ih rest (by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using b)⟩

def rootWords (base : List Nat) (token : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun word _ next bits =>
      let tail := next (bits >>> 1)
      if bits &&& 1 == 0 then tail else word :: tail) base token

def rootState (base : List Nat) (fuel token : Nat) : (Nat × List Nat × List (Nat × Nat × Nat)) :=
  (fuel, rootWords base token, [])

def insertWord (w : Nat) (ws : List Nat) : List Nat :=
  List.rec [w] (fun a tail next => if w ≤ a then w :: a :: tail else a :: next) ws

def childState (mask token : Nat) (state : (Nat × List Nat × List (Nat × Nat × Nat))) : Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  let (fuel, ws, history) := state
  let keep := token % 4
  let op := (token / 4) % 3
  let a := token / (4 * 3 * 64)
  let b := (token / (4 * 3)) % 64
  if fuel == 0 || b ≥ ws.length || (if op == 2 then a != b || keep ≥ 2 else a ≥ b) then none
  else
    let x := ws.getD a 0
    let y := ws.getD b 0
    let w := if op == 0 then x &&& y else if op == 1 then x ||| y else mask ^^^ x
    if w == 0 || w == mask || ws.contains w then none
    else
      let rest := if keep.testBit 0 then ws else ws.erase x
      let rest := if op == 2 || keep.testBit 1 then rest else rest.erase y
      some (fuel - 1, insertWord w rest, (w, x, y) :: history)

def gateToken (a b op keep : Nat) : Nat := ((a * 64 + b) * 3 + op) * 4 + keep

def stockWord (mask : Nat) (stock : List Nat) (needed : List Nat) (word : Nat) : List Nat :=
  let v := word &&& mask
  if v == 0 || v == mask || stock.contains v || needed.contains v then needed
  else v :: needed

def recipeStart (mask : Nat) (stock words : List Nat) : List Nat :=
  (List.rec (motive := fun _ => List Nat → List Nat) id
    (fun word _ next seen => next (stockWord mask stock seen word)) words) []

def recipeClosure (mask : Nat) (stock : List Nat) (history : List (Nat × Nat × Nat))
    (start : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) id
    (fun (out, a, b) _ next seen =>
      next (if seen.contains (out &&& mask) then stockWord mask stock (stockWord mask stock seen a) b else seen))
    history start

def recipeNeeded (mask : Nat) (stock words : List Nat) (history : List (Nat × Nat × Nat)) :
    List Nat :=
  recipeClosure mask stock history (recipeStart mask stock words)

def maskFlat (mask word : Nat) : Bool :=
  let v := word &&& mask
  v == 0 || v == mask

def flatCount (mask : Nat) (words : List Nat) : Nat :=
  List.rec 0 (fun word _ count => if maskFlat mask word then count + 1 else count) words

def availableB (mask : Nat) (bank : List Nat) (w : Nat) : Bool :=
  w == 0 || w == mask || bank.contains w

def recipeGate (mask : Nat) (bank : List Nat) (w a b : Nat) : Bool :=
  availableB mask bank a &&
    ((w == mask ^^^ a) || (availableB mask bank b && (w == a &&& b || w == a ||| b)))

def replayRecipes (mask : Nat) (needed : List Nat) (recipes : List (Nat × Nat × Nat))
    (bank : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun _ => [])
    (fun (w, a, b) _ next bank =>
      let v := w &&& mask
      if needed.contains v && !availableB mask bank v &&
          recipeGate mask bank v (a &&& mask) (b &&& mask) then
        v :: next (v :: bank)
      else next bank) recipes bank

def boundCloses (target : Nat) (state : (Nat × List Nat × List (Nat × Nat × Nat))) (bound : (Nat × List Nat × Nat × Nat)) : Bool :=
  let (mask, stock, lower, goal) := bound
  let (fuel, ws, history) := state
  (target &&& mask) == goal && goal != 0 && goal != mask &&
    (let remaining := fuel - flatCount mask ws
     if remaining < lower then
       let start := recipeStart mask stock ws
       if start.length + remaining < lower then
         let needed := recipeClosure mask stock history start
         if needed.length + remaining < lower then
           let replay := replayRecipes mask needed history.reverse stock
           (replay.length + remaining < lower) &&
             ws.all (fun w => availableB mask (replay ++ stock) (w &&& mask))
         else false
       else false
     else false)

def knownCloses (target : Nat) (bounds : List (Nat × List Nat × Nat × Nat)) (state : (Nat × List Nat × List (Nat × Nat × Nat))) : Bool :=
  List.rec false (fun bound _ later => boundCloses target state bound || later) bounds

def AvailableWord (mask : Nat) (bank : List Nat) (word : Nat) : Prop :=
  word = 0 ∨ word = mask ∨ word ∈ bank

def GateWord (mask : Nat) (bank : List Nat) (out : Nat) : Prop :=
  (∃ a, AvailableWord mask bank a ∧ out = mask ^^^ a) ∨
  (∃ a b, AvailableWord mask bank a ∧ AvailableWord mask bank b ∧
    (out = a &&& b ∨ out = a ||| b))

def WordBuilds (mask : Nat) (roots : List Nat) : List Nat → Prop
  | [] => True
  | w :: ws => GateWord mask roots w ∧ WordBuilds mask (w :: roots) ws

def Lower (mask : Nat) (roots : List Nat) (target : Nat) (minimum : Nat) : Prop :=
  ∀ values, WordBuilds mask roots values →
    AvailableWord mask (values ++ roots) target → minimum ≤ values.length

def Known (bounds : List (Nat × List Nat × Nat × Nat)) : Prop :=
  ∀ bound ∈ bounds, Lower bound.1 bound.2.1 bound.2.2.2 bound.2.2.1

theorem restrictWord (mask : Nat) (word : Nat) : word &&& mask &&& mask = word &&& mask := by
  simp

theorem projectGate {mask cut : Nat} (submask : mask &&& cut = cut)
    {roots : List Nat} {out : Nat} (gate : GateWord mask roots out) :
    GateWord cut (roots.map (· &&& cut)) (out &&& cut) := by
  have av {word : Nat} (ha : AvailableWord mask roots word) :
      AvailableWord cut (roots.map (· &&& cut)) (word &&& cut) := by
    rcases ha with rfl | rfl | hm
    · exact Or.inl (by simp)
    · exact Or.inr (Or.inl submask)
    · exact Or.inr (Or.inr (List.mem_map_of_mem hm))
  rcases gate with ⟨a, ha, rfl⟩ | ⟨a, b, ha, hb, eq | eq⟩
  · refine Or.inl ⟨a &&& cut, av ha, ?_⟩
    apply Nat.eq_of_testBit_eq
    intro i
    have cutAt := congrArg (fun n : Nat => n.testBit i) submask
    simp only [Nat.testBit_and, Nat.testBit_xor] at cutAt ⊢
    cases h : cut.testBit i
    · simp
    · simp [h] at cutAt
      simp [cutAt]
  · subst out
    refine Or.inr ⟨a &&& cut, b &&& cut, av ha, av hb, Or.inl ?_⟩
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and]
    cases cut.testBit i <;> simp
  · subst out
    refine Or.inr ⟨a &&& cut, b &&& cut, av ha, av hb, Or.inr ?_⟩
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and, Nat.testBit_or]
    cases cut.testBit i <;> simp

theorem projectBuilds {mask cut : Nat} (submask : mask &&& cut = cut)
    {roots values : List Nat} (builds : WordBuilds mask roots values) :
    WordBuilds cut (roots.map (· &&& cut)) (values.map (· &&& cut)) := by
  induction values generalizing roots with
  | nil => trivial
  | cons w ws ih =>
    exact ⟨projectGate submask builds.1, ih builds.2⟩

theorem availableWeaken {mask : Nat} {small big : List Nat} {w : Nat}
    (sub : ∀ x ∈ small, AvailableWord mask big x)
    (av : AvailableWord mask small w) : AvailableWord mask big w := by
  rcases av with rfl | rfl | h
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact sub w h

theorem gateWeaken {mask : Nat} {small big : List Nat} {out : Nat}
    (sub : ∀ x ∈ small, AvailableWord mask big x)
    (gate : GateWord mask small out) : GateWord mask big out := by
  rcases gate with ⟨a, ha, rfl⟩ | ⟨a, b, ha, hb, eq⟩
  · exact Or.inl ⟨a, availableWeaken sub ha, rfl⟩
  · exact Or.inr ⟨a, b, availableWeaken sub ha, availableWeaken sub hb, eq⟩

theorem extendKnown {bound : (Nat × List Nat × Nat × Nat)} {bounds : List (Nat × List Nat × Nat × Nat)}
    (old : Known bounds)
    (new : Lower bound.1 bound.2.1 bound.2.2.2 bound.2.2.1) :
    Known (bound :: bounds) := by
  intro x h
  rcases List.mem_cons.mp h with rfl | h
  · exact new
  · exact old _ h

def AgreesAt (i j : Nat) (word : Nat) : Prop :=
  word.testBit i = word.testBit j

theorem agreesAvailable {i j mask : Nat} {bank : List Nat} {word : Nat}
    (m : AgreesAt i j mask) (all : ∀ w ∈ bank, AgreesAt i j w)
    (av : AvailableWord mask bank word) : AgreesAt i j word := by
  rcases av with rfl | rfl | h
  · simp [AgreesAt]
  · exact m
  · exact all _ h

theorem agreesGate {i j mask : Nat} {bank : List Nat} {word : Nat}
    (m : AgreesAt i j mask) (all : ∀ w ∈ bank, AgreesAt i j w)
    (gate : GateWord mask bank word) : AgreesAt i j word := by
  rcases gate with ⟨a, ha, rfl⟩ | ⟨a, b, ha, hb, eq | eq⟩
  · simp only [AgreesAt, Nat.testBit_xor] at m ⊢
    rw [m, show a.testBit i = a.testBit j from agreesAvailable m all ha]
  · subst word
    simp only [AgreesAt, Nat.testBit_and]
    rw [show a.testBit i = a.testBit j from agreesAvailable m all ha,
      show b.testBit i = b.testBit j from agreesAvailable m all hb]
  · subst word
    simp only [AgreesAt, Nat.testBit_or]
    rw [show a.testBit i = a.testBit j from agreesAvailable m all ha,
      show b.testBit i = b.testBit j from agreesAvailable m all hb]

theorem agreesBuilds {i j mask : Nat} {roots values : List Nat} {word : Nat}
    (m : AgreesAt i j mask) (all : ∀ w ∈ roots, AgreesAt i j w)
    (builds : WordBuilds mask roots values)
    (av : AvailableWord mask (values ++ roots) word) : AgreesAt i j word := by
  induction values generalizing roots with
  | nil => exact agreesAvailable m all av
  | cons v vs ih =>
    have vg := agreesGate m all builds.1
    have hc : ∀ w ∈ v :: roots, AgreesAt i j w := by
      intro w h
      rcases List.mem_cons.mp h with rfl | mem
      · exact vg
      · exact all _ mem
    apply ih hc builds.2
    rcases av with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (by
        simpa [List.mem_append, List.mem_cons, or_assoc, or_left_comm] using h))

theorem buildsMap {m n : Nat} (f : Nat → Nat)
    (zero : f 0 = 0) (ones : f m = n)
    (invert : ∀ a, f (m ^^^ a) = n ^^^ f a)
    (meet : ∀ a b, f (a &&& b) = f a &&& f b)
    (join : ∀ a b, f (a ||| b) = f a ||| f b)
    {roots : List Nat} {bank : List Nat}
    (supply : ∀ v ∈ roots, AvailableWord n bank (f v))
    {values : List Nat} (h : WordBuilds m roots values) :
    WordBuilds n bank (values.map f) := by
  have av {bank roots : List Nat} {v : Nat}
      (src : ∀ v ∈ roots, AvailableWord n bank (f v))
      (h : AvailableWord m roots v) : AvailableWord n bank (f v) := by
    rcases h with rfl | rfl | hv
    · exact Or.inl zero
    · exact Or.inr (Or.inl ones)
    · exact src _ hv
  induction values generalizing roots bank with
  | nil => trivial
  | cons v vs ih =>
    refine ⟨?_, ih ?_ h.2⟩
    · rcases h.1 with ⟨a, ha, eq⟩ | ⟨a, b, ha, hb, eq | eq⟩
      · exact Or.inl ⟨f a, av supply ha, eq ▸ invert a⟩
      · exact Or.inr ⟨f a, f b, av supply ha, av supply hb, Or.inl (eq ▸ meet a b)⟩
      · exact Or.inr ⟨f a, f b, av supply ha, av supply hb, Or.inr (eq ▸ join a b)⟩
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact Or.inr (Or.inr List.mem_cons_self)
      · exact availableWeaken (fun x hx => Or.inr (Or.inr (List.mem_cons_of_mem _ hx))) (supply _ hw)

theorem lowerMap {m n : Nat} (f : Nat → Nat)
    (zero : f 0 = 0) (ones : f m = n)
    (invert : ∀ a, f (m ^^^ a) = n ^^^ f a)
    (meet : ∀ a b, f (a &&& b) = f a &&& f b)
    (join : ∀ a b, f (a ||| b) = f a ||| f b)
    {roots bank : List Nat} {goal : Nat} {minimum : Nat}
    (supply : ∀ v ∈ roots, AvailableWord n bank (f v))
    (bound : Lower n bank (f goal) minimum) :
    Lower m roots goal minimum := by
  intro values build hit
  suffices AvailableWord n (values.map f ++ bank) (f goal) by
    simpa using bound (values.map f) (buildsMap f zero ones invert meet join supply build) this
  rcases hit with rfl | rfl | mem
  · exact Or.inl zero
  · exact Or.inr (Or.inl ones)
  · rcases List.mem_append.mp mem with hv | hr
    · exact Or.inr (Or.inr (List.mem_append_left _ (List.mem_map_of_mem hv)))
    · exact availableWeaken (fun w hw => Or.inr (Or.inr (List.mem_append_right _ hw))) (supply _ hr)

theorem buildsWeaken {mask : Nat} {small big values : List Nat}
    (supply : ∀ w ∈ small, AvailableWord mask big w) (build : WordBuilds mask small values) :
    WordBuilds mask big values := by
  induction values generalizing small big with
  | nil => trivial
  | cons v vs ih =>
    refine ⟨gateWeaken supply build.1, ih ?_ build.2⟩
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact Or.inr (Or.inr List.mem_cons_self)
    · exact availableWeaken (fun x hx => Or.inr (Or.inr (List.mem_cons_of_mem _ hx))) (supply _ hw)

theorem gateBuildsIndex {mask : Nat} (bank values : List Nat)
    (legal : ∀ i, i < values.length →
      GateWord mask (bank ++ values.take i) (values.getD i 0)) :
    WordBuilds mask bank values := by
  induction values generalizing bank with
  | nil => trivial
  | cons v vs ih =>
    have first := legal 0 (by simp)
    have tail : ∀ i, i < vs.length →
        GateWord mask ((bank ++ [v]) ++ vs.take i) (vs.getD i 0) := by
      intro i hi
      simpa [List.take_succ_cons, List.append_assoc] using
        legal (i + 1) (by simpa using hi)
    refine ⟨by simpa using first, buildsWeaken ?_ (ih (bank ++ [v]) tail)⟩
    intro w mem
    exact Or.inr (Or.inr (by simpa [or_comm] using mem))

theorem lowerWeaken {mask goal minimum : Nat} {old new : List Nat}
    (lower : Lower mask old goal minimum) (supply : ∀ w ∈ new, AvailableWord mask old w) :
    Lower mask new goal minimum := by
  apply lowerMap id rfl rfl (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) supply
  exact lower

def properWord (mask word : Nat) : Prop := word ≠ 0 ∧ word ≠ mask

def binWord (isOr : Bool) (a b : Nat) : Nat :=
  if isOr then a ||| b else a &&& b

theorem binWord_comm (d : Bool) (a b : Nat) : binWord d a b = binWord d b a := by
  cases d <;> simp [binWord, Nat.land_comm, Nat.lor_comm]

variable {mask : Nat} {target : Nat}

def LiveWord (mask : Nat) (target : Nat) : Nat → Nat → Finset (Nat) → Prop
  | 0,t,S => t=0 ∧ S={target} ∧ properWord mask target
  | k+1,t,S =>
    (∃ (u : Nat) (U : Finset (Nat)) (a : Nat), t=u+1 ∧ S=insert a U ∧ properWord mask a ∧
      (mask ^^^ a) ∉ insert a U ∧ LiveWord mask target k u (insert ((mask ^^^ a)) U)) ∨
    (∃ (U : Finset (Nat)) (a b : Nat) (d : Bool), S=insert a (insert b U) ∧ properWord mask a ∧ properWord mask b ∧ a ≠ b ∧
      binWord d a b ∉ insert a (insert b U) ∧ LiveWord mask target k t (insert (binWord d a b) U))
theorem LiveWord.stop {target : Nat} (hp : properWord mask target) : LiveWord mask target 0 0 {target} := ⟨rfl,rfl,hp⟩
theorem LiveWord.unary {target : Nat} {k t : Nat} {U : Finset (Nat)} {a : Nat} (ha : properWord mask a)
    (hfresh : (mask ^^^ a) ∉ insert a U) (tail : LiveWord mask target k t (insert ((mask ^^^ a)) U)) :
    LiveWord mask target (k+1) (t+1) (insert a U) :=
  Or.inl ⟨t,U,a,rfl,rfl,ha,hfresh,tail⟩
theorem LiveWord.binary {target : Nat} {k t : Nat} {U : Finset (Nat)} {a b : Nat} {d : Bool}
    (ha : properWord mask a) (hb : properWord mask b) (hab : a ≠ b)
    (hfresh : binWord d a b ∉ insert a (insert b U)) (tail : LiveWord mask target k t (insert (binWord d a b) U)) :
    LiveWord mask target (k+1) t (insert a (insert b U)) :=
  Or.inr ⟨U,a,b,d,rfl,ha,hb,hab,hfresh,tail⟩
theorem LiveWord.ind {target : Nat} {motive : ∀ (k t : Nat) (S : Finset (Nat)), LiveWord mask target k t S → Prop}
    (stop : ∀ (hp : properWord mask target), motive 0 0 {target} (LiveWord.stop hp))
    (unary : ∀ {k t : Nat} {U : Finset (Nat)} {a : Nat} (ha : properWord mask a)
      (hfresh : (mask ^^^ a) ∉ insert a U) (tail : LiveWord mask target k t (insert ((mask ^^^ a)) U)),
      motive k t (insert ((mask ^^^ a)) U) tail → motive (k+1) (t+1) (insert a U) (LiveWord.unary ha hfresh tail))
    (binary : ∀ {k t : Nat} {U : Finset (Nat)} {a b : Nat} {d : Bool}
      (ha : properWord mask a) (hb : properWord mask b) (hab : a ≠ b)
      (hfresh : binWord d a b ∉ insert a (insert b U)) (tail : LiveWord mask target k t (insert (binWord d a b) U)),
      motive k t (insert (binWord d a b) U) tail →
      motive (k+1) t (insert a (insert b U)) (LiveWord.binary ha hb hab hfresh tail))
    {k t : Nat} {S : Finset (Nat)} (h : LiveWord mask target k t S) : motive k t S h := by
  induction k generalizing t S with
  | zero =>
    obtain ⟨rfl,rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    rcases h with ⟨u,U,a,rfl,rfl,ha,hf,tail⟩ | ⟨U,a,b,d,rfl,ha,hb,hab,hf,tail⟩
    · exact unary ha hf tail (ih tail)
    · exact binary ha hb hab hf tail (ih tail)

theorem liveWordProper {k t S} (h : LiveWord mask target k t S) : ∀ a ∈ S, properWord mask a := by
  induction h using LiveWord.ind with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

theorem liveWordSize {k t S} (h : LiveWord mask target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h using LiveWord.ind with
  | stop hp => simp
  | @unary k t U a ha hf _ ih =>
    have hu : (mask ^^^ a) ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : binWord d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩

def wordRep (mask : Nat) (ws : List Nat) (w : Nat) : Prop :=
  w ∈ ws ∨ ¬properWord mask w

def wordWitness (mask : Nat) (ws : List Nat) (w : Nat) : Prop :=
  (∃ a ∈ ws, properWord mask a ∧ w = mask ^^^ a) ∨
  ∃ d a b, a ∈ ws ∧ b ∈ ws ∧ properWord mask a ∧ properWord mask b ∧
    a ≠ b ∧ w = binWord d a b

theorem pullWord {w : List (Nat)} {z : Nat} {k t S} (h : LiveWord mask target k t S)
    (hz : wordRep mask w z ∨ wordWitness mask w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ LiveWord mask target k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := liveWordProper h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase ((mask ^^^ a))
        have ht : LiveWord mask target k t (insert ((mask ^^^ a)) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : (mask ^^^ a) ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,LiveWord.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (binWord d a b)
        have ht : LiveWord mask target k t (insert (binWord d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : binWord d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,LiveWord.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

def Masked (mask word : Nat) : Prop := word &&& mask = word

theorem maskedAvailable {bank : List Nat} {word : Nat}
    (all : ∀ w ∈ bank, Masked mask w) (aw : AvailableWord mask bank word) :
    Masked mask word := by
  rcases aw with rfl | rfl | hw
  · simp [Masked]
  · simp [Masked]
  · exact all _ hw

theorem maskedGate {bank : List Nat} {out : Nat}
    (all : ∀ w ∈ bank, Masked mask w) (g : GateWord mask bank out) :
    Masked mask out := by
  rcases g with ⟨a, ha, rfl⟩ | ⟨a, b, ha, hb, ea | ea⟩
  · have h := projectGate (mask := mask) (cut := mask) (by simp)
      (roots := bank) (out := mask ^^^ a) (Or.inl ⟨a, ha, rfl⟩)
    have ma := maskedAvailable all ha
    unfold Masked at ma ⊢
    apply Nat.eq_of_testBit_eq
    intro i
    have bit := congrArg (fun n : Nat => n.testBit i) ma
    simp only [Nat.testBit_and, Nat.testBit_xor] at bit ⊢
    cases hm : mask.testBit i <;> simp_all
  · subst out
    have ma := maskedAvailable all ha
    have mb := maskedAvailable all hb
    simp only [Masked] at ma mb ⊢
    rw [Nat.land_assoc, mb]
  · subst out
    have ma := maskedAvailable all ha
    have mb := maskedAvailable all hb
    unfold Masked at ma mb ⊢
    apply Nat.eq_of_testBit_eq
    intro i
    have bitA := congrArg (fun n : Nat => n.testBit i) ma
    have bitB := congrArg (fun n : Nat => n.testBit i) mb
    simp only [Nat.testBit_and, Nat.testBit_or] at bitA bitB ⊢
    cases hm : mask.testBit i <;> simp_all

def binaryWitness (mask : Nat) (bank : List Nat) (out : Nat) : Prop :=
  ∃ d a b, a ∈ bank ∧ b ∈ bank ∧ properWord mask a ∧ properWord mask b ∧
    a ≠ b ∧ out = binWord d a b

theorem classifyBinary {bank : List Nat}
    (all : ∀ w ∈ bank, Masked mask w) (d : Bool) {a b : Nat}
    (ha : AvailableWord mask bank a) (hb : AvailableWord mask bank b) :
    wordRep mask bank (binWord d a b) ∨ binaryWitness mask bank (binWord d a b) := by
  have c0 : wordRep mask bank 0 := Or.inr fun h => h.1 rfl
  have cm : wordRep mask bank mask := Or.inr fun h => h.2 rfl
  have classify {w : Nat} (hw : AvailableWord mask bank w) :
      w = 0 ∨ w = mask ∨ w ∈ bank ∧ properWord mask w := by
    by_cases zh : w = 0
    · exact Or.inl zh
    by_cases mh : w = mask
    · exact Or.inr (Or.inl mh)
    exact Or.inr (Or.inr ⟨(hw.resolve_left zh).resolve_left mh, zh, mh⟩)
  have ma : a &&& mask = a := maskedAvailable all ha
  have mb : b &&& mask = b := maskedAvailable all hb
  have absorbA : a ||| mask = mask := by
    apply Nat.eq_of_testBit_eq
    intro i
    have h := congrArg (fun n : Nat => n.testBit i) ma
    simp only [Nat.testBit_and, Nat.testBit_or] at h ⊢
    cases hm : mask.testBit i <;> simp_all
  have absorbB : b ||| mask = mask := by
    apply Nat.eq_of_testBit_eq
    intro i
    have h := congrArg (fun n : Nat => n.testBit i) mb
    simp only [Nat.testBit_and, Nat.testBit_or] at h ⊢
    cases hm : mask.testBit i <;> simp_all
  rcases classify ha with rfl | hma | ⟨ha', pa⟩
  · rw [binWord_comm]
    cases d
    · exact Or.inl (by simpa [binWord] using c0)
    · rcases hb with hz | hm | hv
      · exact Or.inl (by simpa [binWord, hz] using c0)
      · exact Or.inl (by simpa [binWord, hm] using cm)
      · exact Or.inl (by simpa [binWord, wordRep] using
          (Or.inl hv : wordRep mask bank b))
  · rw [hma, binWord_comm]
    cases d
    · rcases hb with hz | hm | hv
      · exact Or.inl (by simpa [binWord, hz] using c0)
      · exact Or.inl (by simpa [binWord, hm] using cm)
      · exact Or.inl (by simpa [binWord, mb, wordRep] using
          (Or.inl hv : wordRep mask bank b))
    · exact Or.inl (by simpa [binWord, absorbB] using cm)
  rcases classify hb with rfl | hmb | ⟨hb', pb⟩
  · cases d
    · exact Or.inl (by simpa [binWord] using c0)
    · exact Or.inl (by simpa [binWord, wordRep] using
        (Or.inl ha' : wordRep mask bank a))
  · rw [hmb]
    cases d
    · exact Or.inl (by simpa [binWord, ma, wordRep] using
        (Or.inl ha' : wordRep mask bank a))
    · exact Or.inl (by simpa [binWord, absorbA] using cm)
  by_cases eq : a = b
  · subst b
    cases d <;> exact Or.inl (by simpa [binWord, wordRep] using
      (Or.inl ha' : wordRep mask bank a))
  exact Or.inr ⟨d, a, b, ha', hb', pa, pb, eq, rfl⟩

theorem classifyWord {bank : List Nat} {out : Nat}
    (all : ∀ w ∈ bank, Masked mask w) (gate : GateWord mask bank out) :
    wordRep mask bank out ∨ wordWitness mask bank out := by
  have c0 : wordRep mask bank 0 := Or.inr fun h => h.1 rfl
  have cm : wordRep mask bank mask := Or.inr fun h => h.2 rfl
  have classify {w : Nat} (hw : AvailableWord mask bank w) :
      w = 0 ∨ w = mask ∨ w ∈ bank ∧ properWord mask w := by
    by_cases zh : w = 0
    · exact Or.inl zh
    by_cases mh : w = mask
    · exact Or.inr (Or.inl mh)
    exact Or.inr (Or.inr ⟨(hw.resolve_left zh).resolve_left mh, zh, mh⟩)
  rcases gate with ⟨a, ha, rfl⟩ | ⟨a, b, ha, hb, h | h⟩
  · rcases classify ha with rfl | hma | ⟨hm, hp⟩
    · exact Or.inl (by simpa using cm)
    · exact Or.inl (by simpa [hma] using c0)
    · exact Or.inr (Or.inl ⟨a, hm, hp, rfl⟩)
  · subst out; exact (classifyBinary all false ha hb).imp id Or.inr
  · subst out; exact (classifyBinary all true ha hb).imp id Or.inr

theorem extractWordLive {roots values : List Nat}
    (all : ∀ w ∈ roots, Masked mask w) (builds : WordBuilds mask roots values)
    (hit : AvailableWord mask (values ++ roots) target) (p : properWord mask target) :
    ∃ k t S, k ≤ values.length ∧ LiveWord mask target k t S ∧ ∀ w ∈ S, w ∈ roots := by
  have hm := (hit.resolve_left p.1).resolve_left p.2
  induction values generalizing roots with
  | nil =>
    exact ⟨0, 0, {target}, Nat.zero_le _, LiveWord.stop p, by simpa using hm⟩
  | cons w ws ih =>
    have next : ∀ v ∈ w :: roots, Masked mask v := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact maskedGate all builds.1
      · exact all _ hv
    have ht : AvailableWord mask (ws ++ w :: roots) target := by
      exact Or.inr (Or.inr (by simpa [List.mem_append, List.mem_cons, or_assoc, or_left_comm] using hm))
    obtain ⟨k, t, S, hk, live, sub⟩ :=
      ih next builds.2 ht ((ht.resolve_left p.1).resolve_left p.2)
    have available : ∀ v ∈ S, v ∈ roots ++ [w] := by
      intro v h
      simpa [or_comm] using sub v h
    obtain ⟨k', t', S', hk', hl, hsub⟩ := pullWord live (classifyWord all builds.1) available
    exact ⟨k', t', S', by simp only [List.length_cons]; omega, hl, hsub⟩

theorem insertWordMem {x w : Nat} {ws : List Nat} :
    x ∈ insertWord w ws ↔ x = w ∨ x ∈ ws := by
  induction ws with
  | nil => simp [insertWord]
  | cons a tail ih =>
    change x ∈ (if w ≤ a then w :: a :: tail else a :: insertWord w tail) ↔ _
    split <;> simp [ih, or_assoc, or_left_comm]

theorem insertWordNodup {w : Nat} {ws : List Nat} (nd : ws.Nodup) (fresh : w ∉ ws) :
    (insertWord w ws).Nodup := by
  induction ws with
  | nil => simp [insertWord]
  | cons a tail ih =>
    change (if w ≤ a then w :: a :: tail else a :: insertWord w tail).Nodup
    split
    · exact List.nodup_cons.mpr ⟨fresh, nd⟩
    have hn := List.nodup_cons.mp nd
    have hnot : w ≠ a ∧ w ∉ tail := by simpa using fresh
    exact List.nodup_cons.mpr ⟨by simp [insertWordMem, hnot.1.symm, hn.1], ih hn.2 hnot.2⟩

theorem insertWordSet (w : Nat) (ws : List Nat) :
    (insertWord w ws).toFinset = insert w ws.toFinset := by
  ext x
  simp [insertWordMem]

theorem eraseWordSet {ws : List Nat} (nd : ws.Nodup) (w : Nat) :
    (ws.erase w).toFinset = ws.toFinset.erase w := by
  ext x
  simp [nd.mem_erase_iff, and_comm]

theorem gateTokenFields {a b op keep : Nat} (hb : b < 64) (ho : op < 3) (hk : keep < 4) :
    gateToken a b op keep % 4 = keep ∧
    gateToken a b op keep / 4 % 3 = op ∧
    gateToken a b op keep / (4 * 3 * 64) = a ∧
    gateToken a b op keep / (4 * 3) % 64 = b := by
  unfold gateToken
  omega

def keepWord (save : Bool) (w : Nat) (ws : List Nat) : List Nat :=
  if save then ws else ws.erase w

theorem keepNodup {ws : List Nat} (nd : ws.Nodup) (save : Bool) (w : Nat) :
    (keepWord save w ws).Nodup := by
  cases save
  · exact nd.erase _
  · exact nd

theorem keepSubset (save : Bool) (w : Nat) (ws : List Nat) :
    ∀ v ∈ keepWord save w ws, v ∈ ws := by
  cases save
  · exact fun _ h => List.mem_of_mem_erase h
  · exact fun _ h => h

theorem keepSet {ws : List Nat} (nd : ws.Nodup) {w : Nat} {U : Finset Nat}
    (eq : ws.toFinset = insert w U) :
    (keepWord (decide (w ∈ U)) w ws).toFinset = U := by
  by_cases hw : w ∈ U
  · simp [keepWord, hw, eq, Finset.insert_eq_of_mem hw]
  · simp [keepWord, hw, eraseWordSet nd, eq]

theorem keepPairSet {ws : List Nat} (nd : ws.Nodup) {a b : Nat} {U : Finset Nat}
    (ab : a ≠ b) (eq : ws.toFinset = insert a (insert b U)) :
    (keepWord (decide (b ∈ U)) b (keepWord (decide (a ∈ U)) a ws)).toFinset = U := by
  have x : decide (a ∈ insert b U) = decide (a ∈ U) := by simp [ab]
  have h := keepSet nd eq
  rw [x] at h
  exact keepSet (keepNodup nd _ _) h

theorem getWord {ws : List Nat} {x : Nat} (h : x ∈ ws) :
    ws.getD (ws.idxOf x) 0 = x := by
  have inb := List.idxOf_lt_length_iff.mpr h
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inb] using
    List.getElem_idxOf inb

theorem unaryChild {mask fuel a : Nat} {ws : List Nat}
    {history : List (Nat × Nat × Nat)} {x : Nat} {keep : Nat}
    (ha : a < ws.length) (ha64 : a < 64) (hf : fuel ≠ 0) (hk : keep < 2)
    (hx : ws.getD a 0 = x) (p : properWord mask (mask ^^^ x)) (fresh : mask ^^^ x ∉ ws) :
    childState mask (gateToken a a 2 keep) (fuel, ws, history) =
      some (fuel - 1, insertWord (mask ^^^ x) (keepWord (keep.testBit 0) x ws),
        (mask ^^^ x, x, x) :: history) := by
  obtain ⟨ke, op, aa, bb⟩ := gateTokenFields (a := a) ha64 (by decide : 2 < 3) (by omega : keep < 4)
  simp only [childState, ke, op, aa, bb, hx]
  simp [hf, Nat.not_le_of_lt ha, Nat.not_le_of_lt hk, p.1, p.2, fresh, keepWord]

theorem binaryChild {mask fuel a b : Nat} {ws : List Nat}
    {history : List (Nat × Nat × Nat)} {x y : Nat} {keep : Nat}
    (d : Bool) (hab : a < b) (hb : b < ws.length) (hb64 : b < 64)
    (hf : fuel ≠ 0) (hk : keep < 4)
    (hx : ws.getD a 0 = x) (hy : ws.getD b 0 = y)
    (p : properWord mask (binWord d x y)) (fresh : binWord d x y ∉ ws) :
    childState mask (gateToken a b (if d then 1 else 0) keep) (fuel, ws, history) =
      some (fuel - 1, insertWord (binWord d x y)
        (keepWord (keep.testBit 1) y (keepWord (keep.testBit 0) x ws)),
        (binWord d x y, x, y) :: history) := by
  have oh : (if d then 1 else 0) < 3 := by cases d <;> decide
  obtain ⟨ke, op, aa, bb⟩ := gateTokenFields (a := a) hb64 oh hk
  simp only [childState, ke, op, aa, bb, hx, hy]
  cases d <;>
    simp_all [Nat.not_le_of_lt hab, Nat.not_le_of_lt hb, keepWord, binWord, properWord]

def WordViable (mask : Nat) (target : Nat) (state : (Nat × List Nat × List (Nat × Nat × Nat))) : Prop :=
  state.2.1.Nodup ∧ ∃ k t, k ≤ state.1 ∧ LiveWord mask target k t state.2.1.toFinset

def HasChild (mask : Nat) (state child : (Nat × List Nat × List (Nat × Nat × Nat))) : Prop :=
  ∃ a b op keep, a < state.2.1.length ∧
    ((a = b ∧ op = 2 ∧ keep < 2) ∨
      (a < b ∧ b < state.2.1.length ∧ op < 2 ∧ keep < 4)) ∧
    childState mask (gateToken a b op keep) state = some child

theorem unaryProgress {mask fuel k t : Nat} {x target : Nat} {U : Finset Nat} {ws : List Nat}
    {history : List (Nat × Nat × Nat)}
    (nd : ws.Nodup) (wide : ws.length ≤ 64) (hk : k + 1 ≤ fuel)
    (he : ws.toFinset = insert x U) (fresh : mask ^^^ x ∉ insert x U)
    (tail : LiveWord mask target k t (insert (mask ^^^ x) U)) :
    ∃ child, HasChild mask (fuel, ws, history) child ∧ WordViable mask target child := by
  let a := ws.idxOf x
  have xm : x ∈ ws := by
    rw [← List.mem_toFinset, he]
    simp
  have ha : a < ws.length := List.idxOf_lt_length_iff.mpr xm
  have hx : ws.getD a 0 = x := getWord xm
  have p := liveWordProper tail (mask ^^^ x) (Finset.mem_insert_self _ _)
  let save := decide (x ∈ U)
  let keep := if save then 1 else 0
  have keepLt : keep < 2 := by dsimp [keep]; split <;> decide
  have keepBit : keep.testBit 0 = save := by
    unfold keep
    cases save <;> decide
  have fn : mask ^^^ x ∉ ws := by simpa [← List.mem_toFinset, he] using fresh
  let rest := keepWord save x ws
  let child : (Nat × List Nat × List (Nat × Nat × Nat)) := (fuel - 1, insertWord (mask ^^^ x) rest, (mask ^^^ x, x, x) :: history)
  refine ⟨child, ⟨a, a, 2, keep, ha, Or.inl ⟨rfl, rfl, keepLt⟩, ?_⟩, ?_⟩
  · have eq := unaryChild (fuel := fuel) (history := history) ha (by omega) (by omega) keepLt hx p fn
    rw [keepBit] at eq
    exact eq
  · refine ⟨insertWordNodup (keepNodup nd save x) (fun h => fn (keepSubset save x ws _ h)),
      k, t, by change k ≤ fuel - 1; omega, ?_⟩
    change LiveWord mask target k t (insertWord (mask ^^^ x) rest).toFinset
    rw [insertWordSet, keepSet nd he]
    exact tail

theorem binaryProgress {mask fuel k t : Nat} {x y target : Nat} {d : Bool} {U : Finset Nat}
    {ws : List Nat} {history : List (Nat × Nat × Nat)}
    (nd : ws.Nodup) (wide : ws.length ≤ 64) (hk : k + 1 ≤ fuel)
    (he : ws.toFinset = insert x (insert y U)) (xy : x ≠ y)
    (ordered : ws.idxOf x < ws.idxOf y) (fresh : binWord d x y ∉ insert x (insert y U))
    (tail : LiveWord mask target k t (insert (binWord d x y) U)) :
    ∃ child, HasChild mask (fuel, ws, history) child ∧ WordViable mask target child := by
  let a := ws.idxOf x
  let b := ws.idxOf y
  have xm : x ∈ ws := by rw [← List.mem_toFinset, he]; simp
  have ym : y ∈ ws := by rw [← List.mem_toFinset, he]; simp
  have ha : a < ws.length := List.idxOf_lt_length_iff.mpr xm
  have hb : b < ws.length := List.idxOf_lt_length_iff.mpr ym
  have hab : a < b := ordered
  have hx : ws.getD a 0 = x := getWord xm
  have hy : ws.getD b 0 = y := getWord ym
  let v := binWord d x y
  have p := liveWordProper tail v (Finset.mem_insert_self _ _)
  let saveX := decide (x ∈ U)
  let saveY := decide (y ∈ U)
  let keep := (if saveX then 1 else 0) + (if saveY then 2 else 0)
  have fields : keep < 4 ∧ keep.testBit 0 = saveX ∧ keep.testBit 1 = saveY := by
    unfold keep
    cases saveX <;> cases saveY <;> decide
  obtain ⟨keepLt, bx, by'⟩ := fields
  have fn : v ∉ ws := by simpa [← List.mem_toFinset, he] using fresh
  let rest := keepWord saveY y (keepWord saveX x ws)
  let child : (Nat × List Nat × List (Nat × Nat × Nat)) := (fuel - 1, insertWord v rest, (v, x, y) :: history)
  refine ⟨child, ⟨a, b, if d then 1 else 0, keep, ha, Or.inr ⟨hab, hb, ?_, keepLt⟩, ?_⟩, ?_⟩
  · cases d <;> decide
  · have eq := binaryChild (fuel := fuel) (history := history) d hab hb (by omega) (by omega) keepLt hx hy p fn
    rw [bx, by'] at eq
    exact eq
  · refine ⟨insertWordNodup (keepNodup (keepNodup nd saveX x) saveY y)
      (fun h => fn (keepSubset saveX x ws _ (keepSubset saveY y _ _ h))), k, t, by change k ≤ fuel - 1; omega, ?_⟩
    change LiveWord mask target k t (insertWord v rest).toFinset
    rw [insertWordSet, keepPairSet nd xy he]
    exact tail

theorem wordProgress {mask : Nat} {target : Nat} {state : (Nat × List Nat × List (Nat × Nat × Nat))}
    (width : state.2.1.length ≤ 64) (h : WordViable mask target state) :
    target ∈ state.2.1 ∨ ∃ child, HasChild mask state child ∧ WordViable mask target child := by
  obtain ⟨fuel, ws, history⟩ := state
  obtain ⟨nd, k, t, cap, live⟩ := h
  cases k with
  | zero =>
    obtain ⟨_, eq, _⟩ := live
    left
    change ws.toFinset = {target} at eq
    rw [← List.mem_toFinset, eq]
    simp
  | succ k =>
    right
    rcases live with ⟨u,U,x,_,eq,px,fresh,tail⟩ | ⟨U,x,y,d,eq,px,py,xy,fresh,tail⟩
    · exact unaryProgress nd width cap eq fresh tail
    have xm : x ∈ ws := by rw [← List.mem_toFinset, eq]; simp
    have ym : y ∈ ws := by rw [← List.mem_toFinset, eq]; simp
    have diff : ws.idxOf x ≠ ws.idxOf y := by
      intro same
      apply xy
      rw [← getWord xm, same, getWord ym]
    by_cases h : ws.idxOf x < ws.idxOf y
    · exact binaryProgress nd width cap eq xy h fresh tail
    · have eq' : ws.toFinset = insert y (insert x U) := by rw [eq, Finset.insert_comm]
      have fresh' : binWord d y x ∉ insert y (insert x U) := by
        rw [binWord_comm d y x, Finset.insert_comm]; exact fresh
      have tail' : LiveWord mask target k t (insert (binWord d y x) U) := by
        rw [binWord_comm d y x]; exact tail
      exact binaryProgress nd width cap eq' xy.symm (by omega) fresh' tail'

theorem rootWordSublist (base : List Nat) (token : Nat) : (rootWords base token).Sublist base := by
  induction base generalizing token with
  | nil => exact List.Sublist.slnil
  | cons w ws ih =>
    change (if token &&& 1 == 0 then rootWords ws (token >>> 1)
      else w :: rootWords ws (token >>> 1)).Sublist (w :: ws)
    split
    · exact (ih _).cons _
    · exact (ih _).cons₂ _

theorem rootToken (base : List Nat) (S : Finset Nat) :
    ∃ token < 2 ^ base.length, (rootWords base token).toFinset = base.toFinset ∩ S := by
  induction base with
  | nil => exact ⟨0, by simp, by simp [rootWords]⟩
  | cons w ws ih =>
    obtain ⟨token, htoken, ih⟩ := ih
    let bit : Nat := if w ∈ S then 1 else 0
    have hbit : bit < 2 := by dsimp [bit]; split <;> decide
    let code := 2 * token + bit
    have low : code &&& 1 = bit := by
      rw [show (1 : Nat) = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
      dsimp [code]
      omega
    have high : code >>> 1 = token := by
      rw [Nat.shiftRight_eq_div_pow]
      change code / 2 = token
      dsimp [code]
      omega
    refine ⟨code, ?_, ?_⟩
    · simp only [List.length_cons, pow_succ]
      dsimp [code]
      omega
    · change (if code &&& 1 == 0 then rootWords ws (code >>> 1)
        else w :: rootWords ws (code >>> 1)).toFinset = _
      rw [low, high]
      by_cases hw : w ∈ S
      · simp [bit, hw, ih]
      · simp [bit, hw, ih]

theorem liveAgrees {i j k t : Nat} {S : Finset Nat}
    (h : LiveWord mask target k t S) (m : AgreesAt i j mask)
    (all : ∀ w ∈ S, AgreesAt i j w) : AgreesAt i j target := by
  induction h using LiveWord.ind with
  | stop => exact all _ (Finset.mem_singleton_self _)
  | @unary k t U a pa fresh tail ih =>
    apply ih
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · simp only [AgreesAt, Nat.testBit_xor]
      rw [show mask.testBit i = mask.testBit j from m,
        show a.testBit i = a.testBit j from all a (Finset.mem_insert_self _ _)]
    · exact all _ (Finset.mem_insert_of_mem hw)
  | @binary k t U a b d pa pb ab fresh tail ih =>
    apply ih
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · have aa : a.testBit i = a.testBit j := all a (Finset.mem_insert_self _ _)
      have bb : b.testBit i = b.testBit j := all b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      cases d <;> simp [AgreesAt, binWord, Nat.testBit_and, Nat.testBit_or, aa, bb]
    · exact all _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw))

theorem positiveInMask {i : Nat} (mt : Masked mask target) (ht : target.testBit i = true) :
    mask.testBit i = true := by
  have h := congrArg (fun n : Nat => n.testBit i) mt
  simpa [Nat.testBit_and, ht] using h

variable {rows : Nat}

def fullMask (rows : Nat) : Nat := 2 ^ rows - 1

theorem toNatMasked (v : BitVec rows) : Masked (fullMask rows) v.toNat := by
  unfold Masked fullMask
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt v.isLt]

theorem notNat (v : BitVec rows) : (~~~v).toNat = fullMask rows ^^^ v.toNat := by
  rw [← BitVec.xor_allOnes, BitVec.toNat_xor, Nat.xor_comm, BitVec.toNat_allOnes]
  rfl

theorem gateOfAvailable {bank : List Nat} {w : Nat}
    (av : AvailableWord mask bank w) : GateWord mask bank w :=
  Or.inr ⟨w, 0, av, Or.inl rfl, Or.inr (by simp)⟩

theorem toNatAvailable (bank : List (BitVec rows)) (i : Nat) :
    AvailableWord (fullMask rows) (bank.map BitVec.toNat) (bank.getD i 0).toNat := by
  rw [List.getD_eq_getElem?_getD]
  cases h : bank[i]? with
  | none => exact Or.inl rfl
  | some a => exact Or.inr (Or.inr (List.mem_map_of_mem (List.mem_of_getElem? h)))

def buildable (m g : Nat) : Nat → Finset (Nat) → Prop
  | 0, s => g ∈ s
  | n+1, s => buildable m g n s ∨
    (∃ a ∈ s, buildable m g n (insert (m ^^^ a) s)) ∨
    (∃ a ∈ s, ∃ b ∈ s, ∃ d, buildable m g n (insert (binWord d a b) s))

theorem supplyPool {m g : Nat} {n s q} (sub : s ⊆ q) (h : buildable m g n s) : buildable m g n q := by
  induction n generalizing s q with
  | zero => exact sub h
  | succ n ih =>
    rcases h with h | ⟨a,ha,h⟩ | ⟨a,ha,b,hb,d,h⟩
    · exact Or.inl (ih sub h)
    · exact Or.inr (Or.inl ⟨a,sub ha,ih (Finset.insert_subset_insert _ sub) h⟩)
    · exact Or.inr (Or.inr ⟨a,sub ha,b,sub hb,d,ih (Finset.insert_subset_insert _ sub) h⟩)

theorem supplyMore {m g : Nat} {n l s} (le : n ≤ l) (h : buildable m g n s) : buildable m g l s := by
  induction le with
  | refl => exact h
  | step _ ih => exact Or.inl ih

abbrev maskedFlat (m a : Nat) : Prop := a &&& m = 0 ∨ a &&& m = m

def flatSet (m : Nat) (s : Finset (Nat)) := s.filter (maskedFlat m)
def visibleWords (m : Nat) (s : Finset (Nat)) := s.image fun w => w &&& m

theorem flIns {m a : Nat} {s : Finset (Nat)} (ha : a ∉ s) :
    (flatSet m (insert a s)).card = (flatSet m s).card + (if maskedFlat m a then 1 else 0) := by
  by_cases f : maskedFlat m a <;> simp [flatSet,Finset.filter_insert,f,ha]

theorem flLe (m a : Nat) (s : Finset (Nat)) :
    (flatSet m (insert a s)).card ≤ (flatSet m s).card + (if maskedFlat m a then 1 else 0) := by
  by_cases old : a ∈ s
  · rw [Finset.insert_eq_of_mem old]
    omega
  · rw [flIns old]

theorem prIns (m a : Nat) (s : Finset (Nat)) :
    visibleWords m (insert a s) = insert (a &&& m) (visibleWords m s) := Finset.image_insert ..

theorem cofNot {mask m : Nat} (sub : mask &&& m = m) (a : Nat) :
    (mask ^^^ a) &&& m = m ^^^ (a &&& m) := by
  apply Nat.eq_of_testBit_eq
  intro i
  have h := congrArg (fun w : Nat => w.testBit i) sub
  simp only [Nat.testBit_and, Nat.testBit_xor] at h ⊢
  cases he : m.testBit i
  · simp
  · have hm : mask.testBit i = true := by simpa [he] using h
    simp [hm]

theorem cofBinary (m a b : Nat) (d : Bool) :
    binWord d a b &&& m = binWord d (a &&& m) (b &&& m) := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases d <;> simp only [binWord, Bool.false_eq_true, ite_false, ite_true, Nat.testBit_and, Nat.testBit_or] <;>
    cases m.testBit i <;> simp

theorem flNot {mask m : Nat} (sub : mask &&& m = m) (a : Nat) :
    maskedFlat m (mask ^^^ a) ↔ maskedFlat m a := by
  unfold maskedFlat
  rw [cofNot sub]
  constructor <;> intro h
  · rcases h with h | h
    · right
      have hh := congrArg (fun v => m ^^^ v) h
      simpa [← Nat.xor_assoc] using hh
    · left
      have hh := congrArg (fun v => m ^^^ v) h
      simpa [← Nat.xor_assoc] using hh
  · rcases h with h | h <;> simp [h]

theorem flBoth {m a b : Nat} {d : Bool} (ha : maskedFlat m a) (hb : maskedFlat m b) :
    maskedFlat m (binWord d a b) := by
  unfold maskedFlat at *
  rw [cofBinary]
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> cases d <;>
    simp [binWord, ha, hb]

theorem simpleBin {m a b : Nat} {d : Bool} (h : maskedFlat m a ∨ maskedFlat m b) :
    binWord d a b &&& m = 0 ∨ binWord d a b &&& m = m ∨
      binWord d a b &&& m = a &&& m ∨ binWord d a b &&& m = b &&& m := by
  rw [cofBinary]
  have top1 (x : Nat) : m &&& (x &&& m) = x &&& m := by
    rw [Nat.land_comm x m, ← Nat.land_assoc]
    simp
  have top2 (x : Nat) : m ||| (x &&& m) = m := by
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_or, Nat.testBit_and]
    cases x.testBit i <;> cases m.testBit i <;> rfl
  have right1 (x : Nat) : (x &&& m) &&& m = x &&& m := restrictWord m x
  have right2 (x : Nat) : (x &&& m) ||| m = m := by rw [Nat.lor_comm, top2]
  rcases h with (ha|ha)|(hb|hb) <;> cases d <;>
    simp [binWord, *, top1, top2, right1, right2]

def projectedStock (m : Nat) (s : Finset (Nat)) := insert 0 (insert m (visibleWords m s))

theorem maskedBuild {goal : Nat} {k t s} (run : LiveWord mask goal k t s) (m : Nat) (submask : mask &&& m = m) (properGoal : ¬ maskedFlat m goal) :
    ∃ n, n+(flatSet m s).card ≤ k ∧ buildable m (goal &&& m) n (projectedStock m s) := by
  induction run using LiveWord.ind with
  | stop =>
    refine ⟨0,?_,?_⟩
    · simp only [flatSet, Finset.filter_singleton, properGoal, ite_false, Finset.card_empty,
        Nat.add_zero, Nat.le_refl]
    · change goal &&& m ∈ projectedStock m {goal}
      simp [projectedStock,visibleWords]
  | @unary k t u a pa fresh tail ih =>
    obtain ⟨n,cap,built⟩ := ih
    have nn : (mask ^^^ a) ∉ u := fun h => fresh (Finset.mem_insert_of_mem h)
    rw [flIns nn] at cap
    have card := flLe m a u
    have old : a &&& m ∈ projectedStock m (insert a u) := by simp [projectedStock,prIns]
    have sub : projectedStock m u ⊆ projectedStock m (insert a u) := by
      exact Finset.insert_subset_insert _ (Finset.insert_subset_insert _ (Finset.image_subset_image (Finset.subset_insert ..)))
    by_cases f : maskedFlat m a
    · have ff := (flNot submask a).mpr f
      simp only [f,ff,ite_true] at cap card
      refine ⟨n,by omega,supplyPool ?_ built⟩
      intro w hw
      simp only [projectedStock,prIns,Finset.mem_insert] at hw ⊢
      rcases hw with rfl|rfl|rfl|h
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · rcases ff with e|e
        · exact Or.inl e
        · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr (Or.inr h))
    · have nf := mt (flNot submask a).mp f
      simp only [f,nf,ite_false] at cap card
      refine ⟨n+1,by omega,Or.inr (Or.inl ⟨_,old,supplyPool ?_ built⟩)⟩
      intro w hw
      simp only [projectedStock,prIns,Finset.mem_insert] at hw ⊢
      rw [cofNot submask] at hw
      tauto
  | @binary k t u a b d pa pb ab fresh tail ih =>
    let v := binWord d a b
    obtain ⟨n,cap,built⟩ := ih
    have nn : v ∉ u := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    change n+(flatSet m (insert v u)).card ≤ k at cap
    rw [flIns nn] at cap
    have ca := flLe m a (insert b u)
    have cb := flLe m b u
    by_cases simple : maskedFlat m a ∨ maskedFlat m b
    · have budget : n + (flatSet m (insert a (insert b u))).card ≤ k+1 := by
        by_cases fa : maskedFlat m a <;> by_cases fb : maskedFlat m b <;>
          simp only [fa,fb,ite_true,ite_false] at ca cb simple
        all_goals first | have vf : maskedFlat m v := flBoth fa fb; simp only [vf,ite_true] at cap; omega | omega | tauto
      refine ⟨n,budget,supplyPool ?_ built⟩
      intro w hw
      simp only [projectedStock,prIns,Finset.mem_insert] at hw ⊢
      rcases hw with e|e|e|e
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
      · subst w
        have cases := simpleBin (d := d) simple
        tauto
      · tauto
    · have fa : ¬maskedFlat m a := fun h => simple (Or.inl h)
      have fb : ¬maskedFlat m b := fun h => simple (Or.inr h)
      simp only [fa,fb,ite_false] at ca cb
      refine ⟨n+1,by omega,Or.inr (Or.inr ⟨a &&& m,?_,b &&& m,?_,d,supplyPool ?_ built⟩)⟩
      · simp [projectedStock,prIns]
      · simp [projectedStock,prIns]
      · intro w hw
        simp only [projectedStock,prIns,Finset.mem_insert] at hw ⊢
        rw [cofBinary] at hw
        tauto

theorem availableB_spec {mask : Nat} {bank : List Nat} {v : Nat} :
    availableB mask bank v = true ↔ AvailableWord mask bank v := by
  simp [availableB, AvailableWord, or_assoc]

theorem recipeGate_spec {mask : Nat} {bank : List Nat} {v a b : Nat}
    (h : recipeGate mask bank v a b = true) : GateWord mask bank v := by
  simp only [recipeGate, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, availableB_spec] at h
  rcases h with ⟨ha, first | ⟨hb, second⟩⟩
  · exact Or.inl ⟨a, ha, first⟩
  · exact Or.inr ⟨a, b, ha, hb, second⟩

theorem replayRecipesBuilds (mask : Nat) (needed : List Nat) (recipes : List (Nat × Nat × Nat))
    (bank : List Nat) : WordBuilds mask bank (replayRecipes mask needed recipes bank) := by
  induction recipes generalizing bank with
  | nil => trivial
  | cons recipe recipes ih =>
    obtain ⟨w, a, b⟩ := recipe
    change WordBuilds mask bank
      (if needed.contains (w &&& mask) && !availableB mask bank (w &&& mask) &&
          recipeGate mask bank (w &&& mask) (a &&& mask) (b &&& mask) then
        (w &&& mask) :: replayRecipes mask needed recipes ((w &&& mask) :: bank)
      else replayRecipes mask needed recipes bank)
    split
    · rename_i yes
      exact ⟨recipeGate_spec (Bool.and_eq_true_iff.mp yes).2, ih _⟩
    · exact ih _

theorem flatCountCard (mask : Nat) {words : List Nat} (nodup : words.Nodup) :
    flatCount mask words = (flatSet mask words.toFinset).card := by
  induction words with
  | nil => rfl
  | cons w ws ih =>
    have nd := List.nodup_cons.mp nodup
    have fresh : w ∉ ws.toFinset := by simpa using nd.1
    have bool : maskFlat mask w = true ↔ maskedFlat mask w := by
      simp [maskFlat, maskedFlat]
    change (if maskFlat mask w then flatCount mask ws + 1 else flatCount mask ws) = _
    rw [List.toFinset_cons, flIns fresh, ih nd.2]
    by_cases h : maskedFlat mask w
    · simp [h, bool.mpr h]
    · have no : maskFlat mask w = false := Bool.eq_false_iff.mpr (fun ht => h (bool.mp ht))
      simp [h, no]

theorem buildsAppend {mask : Nat} {roots first second : List Nat}
    (left : WordBuilds mask roots first)
    (right : WordBuilds mask (first ++ roots) second) :
    WordBuilds mask roots (first ++ second) := by
  induction first generalizing roots with
  | nil => exact right
  | cons w ws ih =>
    refine ⟨left.1, ih left.2 ?_⟩
    have same (bank other vals : List Nat) (perm : bank.Perm other)
        (h : WordBuilds mask bank vals) : WordBuilds mask other vals := by
      induction vals generalizing bank other with
      | nil => trivial
      | cons v vs ih =>
        exact ⟨gateWeaken (fun x hx => Or.inr (Or.inr (perm.mem_iff.mp hx))) h.1,
          ih _ _ (perm.cons v) h.2⟩
    exact same _ _ _ (List.perm_middle (a := w) (l₁ := ws) (l₂ := roots)).symm right

theorem buildableWords {mask goal n : Nat} {pool : Finset Nat} {bank : List Nat}
    (h : buildable mask goal n pool) (supply : ∀ w ∈ pool, AvailableWord mask bank w) :
    ∃ values, values.length ≤ n ∧ WordBuilds mask bank values ∧
      AvailableWord mask (values ++ bank) goal := by
  induction n generalizing pool bank with
  | zero => exact ⟨[], Nat.le_refl _, trivial, supply _ h⟩
  | succ n ih =>
    have add {w : Nat} (g : GateWord mask bank w)
        (tail : buildable mask goal n (insert w pool)) :
        ∃ values, values.length ≤ n+1 ∧ WordBuilds mask bank values ∧
          AvailableWord mask (values ++ bank) goal := by
      have growing : ∀ v ∈ insert w pool, AvailableWord mask (w :: bank) v := by
        intro v hv
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact Or.inr (Or.inr List.mem_cons_self)
        · exact availableWeaken (fun _ hh => Or.inr (Or.inr (List.mem_cons_of_mem _ hh))) (supply _ hv)
      obtain ⟨values, budget, build, hit⟩ := ih tail growing
      refine ⟨w :: values, by simp only [List.length_cons]; omega, ⟨g, build⟩, ?_⟩
      rcases hit with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (by simp only [List.mem_append, List.mem_cons] at *; tauto))
    rcases h with h | ⟨a, ha, h⟩ | ⟨a, ha, b, hb, d, h⟩
    · obtain ⟨values, cap, build, hit⟩ := ih h supply
      exact ⟨values, by omega, build, hit⟩
    · exact add (Or.inl ⟨a, supply a ha, rfl⟩) h
    · apply add (w := binWord d a b) ?_ h
      exact Or.inr ⟨a, b, supply a ha, supply b hb, by cases d <;> simp [binWord]⟩

theorem boundClosesSound {state : (Nat × List Nat × List (Nat × Nat × Nat))} {bound : (Nat × List Nat × Nat × Nat)}
    (known : Lower bound.1 bound.2.1 bound.2.2.2 bound.2.2.1)
    (submask : mask &&& bound.1 = bound.1)
    (viable : WordViable mask target state) :
    boundCloses target state bound = false := by
  obtain ⟨fuel, ws, history⟩ := state
  obtain ⟨cut, stock, minimum, goal⟩ := bound
  obtain ⟨nd, k, t, steps, live⟩ := viable
  change k ≤ fuel at steps
  change LiveWord mask target k t ws.toFinset at live
  apply Bool.eq_false_iff.mpr
  intro hc
  let replay := replayRecipes cut (recipeNeeded cut stock ws history) history.reverse stock
  change ((target &&& cut) == goal && goal != 0 && goal != cut &&
    (if fuel - flatCount cut ws < minimum then
      if (recipeStart cut stock ws).length + (fuel - flatCount cut ws) < minimum then
        if (recipeNeeded cut stock ws history).length + (fuel - flatCount cut ws) < minimum then
          (replay.length + (fuel - flatCount cut ws) < minimum) &&
            ws.all (fun w => availableB cut (replay ++ stock) (w &&& cut))
        else false
      else false
    else false)) = true at hc
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hc
  obtain ⟨⟨⟨goalEq, nonzero⟩, nonflat⟩, scan⟩ := hc
  split at scan <;> try contradiction
  split at scan <;> try contradiction
  split at scan <;> try contradiction
  rcases Bool.and_eq_true_iff.mp scan with ⟨length, sources⟩
  simp only [decide_eq_true_eq] at length
  have pn : ¬maskedFlat cut target := by simpa [maskedFlat, goalEq] using And.intro nonzero nonflat
  obtain ⟨n, hn, build⟩ := maskedBuild live cut submask pn
  rw [← flatCountCard cut nd] at hn
  change n + flatCount cut ws ≤ k at hn
  have supply : ∀ w ∈ projectedStock cut ws.toFinset, AvailableWord cut (replay ++ stock) w := by
    intro w hw
    simp only [projectedStock, visibleWords, Finset.mem_insert, Finset.mem_image,
      List.mem_toFinset] at hw
    rcases hw with rfl | rfl | ⟨v, hv, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact availableB_spec.mp (List.all_eq_true.mp sources v hv)
  obtain ⟨ys, hy, built, avail⟩ := buildableWords build supply
  have both := buildsAppend (replayRecipesBuilds cut _ history.reverse stock) built
  have hit : AvailableWord cut ((replay ++ ys) ++ stock) goal := by
    rw [← goalEq]
    exact availableWeaken (fun v hv => Or.inr (Or.inr (by
      simpa [List.mem_append, or_assoc, or_left_comm, or_comm] using hv))) avail
  have enough := known (replay ++ ys) both hit
  simp only [List.length_append] at enough
  omega

theorem knownClosesSound {bounds : List (Nat × List Nat × Nat × Nat)} {state : (Nat × List Nat × List (Nat × Nat × Nat))}
    (known : Known bounds) (submask : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (viable : WordViable mask target state) :
    knownCloses target bounds state = false := by
  induction bounds with
  | nil => rfl
  | cons bound bounds ih =>
    change (boundCloses target state bound || knownCloses target bounds state) = false
    rw [boundClosesSound (known _ List.mem_cons_self) (submask _ List.mem_cons_self) viable]
    exact ih (fun b hb => known b (List.mem_cons_of_mem _ hb))
      (fun b hb => submask b (List.mem_cons_of_mem _ hb))

def encodePoint (f : (Fin rows → Bool)) : BitVec rows :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn

theorem encodeBit (f : (Fin rows → Bool)) (i : Fin rows) :
    (encodePoint f).getLsbD i.val = f i := by
  simp only [encodePoint, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [i.isLt]

theorem encodeNot (f : (Fin rows → Bool)) : encodePoint (fun j => !f j) = ~~~encodePoint f := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_not, encodeBit f ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩]
  simp [hi]

theorem encodeAnd (a b : (Fin rows → Bool)) :
    encodePoint (fun i => a i && b i) = encodePoint a &&& encodePoint b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, encodeBit a ⟨i, hi⟩, encodeBit b ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩]

theorem encodeOr (a b : (Fin rows → Bool)) :
    encodePoint (fun i => a i || b i) = encodePoint a ||| encodePoint b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_or, encodeBit a ⟨i, hi⟩, encodeBit b ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩]

def pointWord (f : (Fin rows → Bool)) : Nat := (encodePoint f).toNat

def relabel (sourceIndex : Fin rows → Fin rows) (word : Nat) : Nat :=
  pointWord fun i => word.testBit (sourceIndex i).val

theorem maskBit {i : Nat} (hi : i < rows) : (fullMask rows).testBit i = true := by
  simp [fullMask, Nat.testBit_two_pow_sub_one, hi]

theorem pointZero : pointWord (fun _ : Fin rows => false) = 0 := by
  have eq : encodePoint (fun _ : Fin rows => false) = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [encodeBit _ ⟨i, hi⟩]
    simp
  simp [pointWord, eq]

theorem relabelZero (sourceIndex : Fin rows → Fin rows) : relabel sourceIndex 0 = 0 := by
  simpa [relabel] using (pointZero (rows := rows))

theorem relabelMask (sourceIndex : Fin rows → Fin rows) : relabel sourceIndex (fullMask rows) = fullMask rows := by
  have all : (fun i => (fullMask rows).testBit (sourceIndex i).val) = fun _ => true := by
    funext i
    exact maskBit (sourceIndex i).isLt
  have bits : encodePoint (fun _ : Fin rows => true) = BitVec.allOnes rows := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [encodeBit _ ⟨i, hi⟩]
    simp [hi]
  simp [relabel, all, pointWord, bits, fullMask]

theorem relabelNot (sourceIndex : Fin rows → Fin rows) (a : Nat) :
    relabel sourceIndex (fullMask rows ^^^ a) = fullMask rows ^^^ relabel sourceIndex a := by
  have eq : (fun i => (fullMask rows ^^^ a).testBit (sourceIndex i).val) =
      fun i => !a.testBit (sourceIndex i).val := by
    funext i
    simp [Nat.testBit_xor, maskBit (sourceIndex i).isLt]
  simp only [relabel, eq, pointWord, encodeNot, notNat]

theorem relabelAnd (sourceIndex : Fin rows → Fin rows) (a b : Nat) :
    relabel sourceIndex (a &&& b) = relabel sourceIndex a &&& relabel sourceIndex b := by
  simp only [relabel, Nat.testBit_and, pointWord, encodeAnd, BitVec.toNat_and]

theorem relabelOr (sourceIndex : Fin rows → Fin rows) (a b : Nat) :
    relabel sourceIndex (a ||| b) = relabel sourceIndex a ||| relabel sourceIndex b := by
  simp only [relabel, Nat.testBit_or, pointWord, encodeOr, BitVec.toNat_or]

theorem lowerRelabel (sourceIndex : Fin rows → Fin rows) {bank roots : List Nat}
    {src dst : Nat} {minimum : Nat}
    (old : Lower (fullMask rows) bank src minimum)
    (goal : relabel sourceIndex dst = src)
    (supply : ∀ w ∈ roots, AvailableWord (fullMask rows) bank (relabel sourceIndex w)) :
    Lower (fullMask rows) roots dst minimum := by
  apply lowerMap (relabel sourceIndex) (relabelZero sourceIndex) (relabelMask sourceIndex)
    (relabelNot sourceIndex) (relabelAnd sourceIndex) (relabelOr sourceIndex) supply
  rw [goal]
  exact old

theorem relabelXor (sourceIndex : Fin rows → Fin rows) (a b : Nat) :
    relabel sourceIndex (a ^^^ b) = relabel sourceIndex a ^^^ relabel sourceIndex b := by
  have eq : encodePoint (fun i => (a ^^^ b).testBit (sourceIndex i).val) =
      encodePoint (fun i => a.testBit (sourceIndex i).val) ^^^
      encodePoint (fun i => b.testBit (sourceIndex i).val) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_xor, encodeBit _ ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩]
    exact Nat.testBit_xor ..
  simpa only [relabel, pointWord, BitVec.toNat_xor] using congrArg BitVec.toNat eq

theorem lowerRelabelMasked (sourceIndex : Fin rows → Fin rows)
    {oldMask newMask : Nat} {bank roots : List Nat} {src dst : Nat} {minimum : Nat}
    (old : Lower oldMask bank src minimum)
    (masks : relabel sourceIndex newMask = oldMask)
    (goal : relabel sourceIndex dst = src)
    (supply : ∀ w ∈ roots, AvailableWord oldMask bank (relabel sourceIndex w)) :
    Lower newMask roots dst minimum := by
  apply lowerMap (relabel sourceIndex) (relabelZero sourceIndex) masks
    (fun w => by rw [relabelXor, masks]) (relabelAnd sourceIndex) (relabelOr sourceIndex) supply
  rwa [goal]

theorem extendKnownRelabel (sourceIndex : Fin rows → Fin rows) {bounds : List (Nat × List Nat × Nat × Nat)}
    {source destination : (Nat × List Nat × Nat × Nat)} (old : Known bounds) (mem : source ∈ bounds)
    (budget : destination.2.2.1 = source.2.2.1)
    (masks : relabel sourceIndex destination.1 = source.1)
    (goal : relabel sourceIndex destination.2.2.2 = source.2.2.2)
    (supply : ∀ w ∈ destination.2.1,
      AvailableWord source.1 source.2.1 (relabel sourceIndex w)) :
    Known (destination :: bounds) := by
  apply extendKnown old
  rw [budget]
  exact lowerRelabelMasked sourceIndex (old _ mem) masks goal supply

theorem relabelToNatBound (sourceIndex : Fin rows → Fin rows) (word : Nat) :
    Masked (fullMask rows) (relabel sourceIndex word) := toNatMasked _

theorem relabelBit (sourceIndex : Fin rows → Fin rows) (word : Nat) (i : Fin rows) :
    (relabel sourceIndex word).testBit i.val = word.testBit (sourceIndex i).val :=
  encodeBit _ i

theorem relabelOutside (sourceIndex : Fin rows → Fin rows) (word i : Nat) (h : rows ≤ i) :
    (relabel sourceIndex word).testBit i = false := by
  apply Nat.testBit_lt_two_pow
  exact Nat.lt_of_lt_of_le (show (encodePoint _).toNat < 2 ^ rows from BitVec.isLt _)
    (Nat.pow_le_pow_right (by decide) h)

theorem relabelInj (sourceIndex : Fin rows → Fin rows) (onto : Function.Surjective sourceIndex)
    {a b : Nat} (ba : Masked (fullMask rows) a) (bb : Masked (fullMask rows) b)
    (eq : relabel sourceIndex a = relabel sourceIndex b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases inside : i < rows
  · obtain ⟨j, h⟩ := onto ⟨i, inside⟩
    have bit := congrArg (fun w : Nat => w.testBit j.val) eq
    simpa only [relabelBit, h] using bit
  · have ea := congrArg (fun w : Nat => w.testBit i) ba
    have eb := congrArg (fun w : Nat => w.testBit i) bb
    simp only [Nat.testBit_and, fullMask, Nat.testBit_two_pow_sub_one, inside, decide_false,
      Bool.and_false] at ea eb
    rw [← ea, ← eb]

theorem kw_step (goal : Nat) (D D' : Finset Nat) (u v w : ℕ) (c : ℕ → ℕ → Bool) (f : ℕ → ℕ → ℕ)
    (hu : u ∈ D) (hv : v ∈ D) (huv : u ≠ v) (huD : u ∉ D') (hvD : v ∉ D')
    (hsub : ∀ x ∈ D', x ≠ w → x ∈ D)
    (hf : ∀ e i, goal.testBit e = true → goal.testBit i = false →
      f e i ∈ D' ∧ (f e i).testBit e = true ∧ (f e i).testBit i = false)
    (hr : ∀ e i e' i', goal.testBit e = true → goal.testBit e' = true → goal.testBit i = false → goal.testBit i' = false → f e i = f e' i' → f e i' = f e i)
    (hcu : ∀ e i, w.testBit e = true → w.testBit i = false → c e i = true →
      u.testBit e = true ∧ u.testBit i = false)
    (hcv : ∀ e i, w.testBit e = true → w.testBit i = false → c e i = false →
      v.testBit e = true ∧ v.testBit i = false)
    (hc : ∀ e i e' i', c e i = c e' i' → c e i' = c e i) :
    ∃ g : ℕ → ℕ → ℕ,
      (∀ e i, goal.testBit e = true → goal.testBit i = false →
        g e i ∈ D ∧ (g e i).testBit e = true ∧ (g e i).testBit i = false) ∧
      (∀ e i e' i', goal.testBit e = true → goal.testBit e' = true → goal.testBit i = false → goal.testBit i' = false → g e i = g e' i' → g e i' = g e i) := by
  have hg : ∀ e i, goal.testBit e = true → goal.testBit i = false → f e i = w →
      ((if f e i = w then (cond (c e i) u v) else f e i) = u ∧ c e i = true) ∨
      ((if f e i = w then (cond (c e i) u v) else f e i) = v ∧ c e i = false) := by
    intro e i _ _ h
    rw [ite_eq_left (h)]
    cases c e i
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
  refine ⟨fun e i => if f e i = w then (cond (c e i) u v) else f e i, ?_, ?_⟩
  · intro e i he hi
    obtain ⟨h1, h2, h3⟩ := hf e i he hi
    show (if f e i = w then (cond (c e i) u v) else f e i) ∈ D ∧
      (if f e i = w then (cond (c e i) u v) else f e i).testBit e = true ∧
      (if f e i = w then (cond (c e i) u v) else f e i).testBit i = false
    by_cases hw : f e i = w
    · rw [hw] at h2 h3
      rcases hg e i he hi hw with ⟨hx, hcc⟩ | ⟨hx, hcc⟩
      · rw [hx]; exact ⟨hu, hcu e i h2 h3 hcc⟩
      · rw [hx]; exact ⟨hv, hcv e i h2 h3 hcc⟩
    · rw [ite_eq_right (hw)]; exact ⟨hsub _ h1 hw, h2, h3⟩
  · intro e i e' i' he he' hi hi' heq
    show (if f e i' = w then (cond (c e i') u v) else f e i') =
      (if f e i = w then (cond (c e i) u v) else f e i)
    have heq' : (if f e i = w then (cond (c e i) u v) else f e i) =
      (if f e' i' = w then (cond (c e' i') u v) else f e' i') := heq
    by_cases h1 : f e i = w
    · by_cases h2 : f e' i' = w
      · have h3 : f e i' = w := (hr e i e' i' he he' hi hi' (h1.trans h2.symm)).trans h1
        have hcc : c e i = c e' i' := by
          rcases hg e i he hi h1 with ⟨hx, hx'⟩ | ⟨hx, hx'⟩ <;>
            rcases hg e' i' he' hi' h2 with ⟨hy, hy'⟩ | ⟨hy, hy'⟩
          · rw [hx', hy']
          · exact absurd (hx.symm.trans (heq'.trans hy)) huv
          · exact absurd (hy.symm.trans (heq'.symm.trans hx)) huv
          · rw [hx', hy']
        rw [ite_eq_left (h3), ite_eq_left (h1), hc e i e' i' hcc]
      · exfalso
        rw [ite_eq_right (h2)] at heq'
        have hm := (hf e' i' he' hi').1
        rcases hg e i he hi h1 with ⟨hx, _⟩ | ⟨hx, _⟩
        · exact huD (by rw [← hx, heq']; exact hm)
        · exact hvD (by rw [← hx, heq']; exact hm)
    · by_cases h2 : f e' i' = w
      · exfalso
        rw [ite_eq_right (h1)] at heq'
        have hm := (hf e i he hi).1
        rcases hg e' i' he' hi' h2 with ⟨hx, _⟩ | ⟨hx, _⟩
        · exact huD (by rw [← hx, ← heq']; exact hm)
        · exact hvD (by rw [← hx, ← heq']; exact hm)
      · have h1n : (if f e i = w then (cond (c e i) u v) else f e i) = f e i := ite_eq_right h1
        have h2n : (if f e' i' = w then (cond (c e' i') u v) else f e' i') = f e' i' := ite_eq_right h2
        rw [h1n, h2n] at heq'
        have h3 := hr e i e' i' he he' hi hi' heq'
        have h3n : ¬ f e i' = w := by rw [h3]; exact h1
        rw [h1n, ite_eq_right (h3n)]
        exact h3

theorem and_cu (u v e i : ℕ) (h1 : (u &&& v).testBit e = true) (_h2 : (u &&& v).testBit i = false)
    (h3 : (!(u.testBit i)) = true) : u.testBit e = true ∧ u.testBit i = false := by
  rw [Nat.testBit_and] at h1
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all

theorem and_cv (u v e i : ℕ) (h1 : (u &&& v).testBit e = true) (h2 : (u &&& v).testBit i = false)
    (h3 : (!(u.testBit i)) = false) : v.testBit e = true ∧ v.testBit i = false := by
  rw [Nat.testBit_and] at h1 h2
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all

theorem or_cu (u v e i : ℕ) (_h1 : (u ||| v).testBit e = true) (h2 : (u ||| v).testBit i = false)
    (h3 : u.testBit e = true) : u.testBit e = true ∧ u.testBit i = false := by
  rw [Nat.testBit_or] at h2
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all

theorem or_cv (u v e i : ℕ) (h1 : (u ||| v).testBit e = true) (h2 : (u ||| v).testBit i = false)
    (h3 : u.testBit e = false) : v.testBit e = true ∧ v.testBit i = false := by
  rw [Nat.testBit_or] at h1 h2
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all

def KWPartition (goal : Nat) (ws : Finset Nat) : Prop :=
  ∃ f : Nat → Nat → Nat,
    (∀ e i, goal.testBit e = true → goal.testBit i = false →
      f e i ∈ ws ∧ (f e i).testBit e = true ∧ (f e i).testBit i = false) ∧
    (∀ e i e' i', goal.testBit e = true → goal.testBit e' = true →
      goal.testBit i = false → goal.testBit i' = false → f e i = f e' i' → f e i' = f e i)

theorem kwFromLive {mask goal : Nat} {k : Nat} {S : Finset Nat}
    (live : LiveWord mask goal k 0 S) (tight : S.card = k + 1) : KWPartition goal S := by
  induction k generalizing S with
  | zero =>
    obtain ⟨_, eq, _⟩ := live
    subst S
    exact ⟨fun _ _ => goal, fun _ _ hp hn => ⟨by simp, hp, hn⟩, fun _ _ _ _ _ _ _ _ _ => rfl⟩
  | succ k ih =>
    rcases live with ⟨u, U, a, eq, _⟩ | ⟨U, a, b, op, rfl, pa, pb, ab, fresh, tail⟩
    · omega
    let w := binWord op a b
    have wU : w ∉ U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have wA : w ≠ a := fun eq => fresh (Finset.mem_insert.mpr (Or.inl eq))
    have wB : w ≠ b := fun eq => fresh (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl eq)))
    have tailSize := (liveWordSize tail).2
    change (insert w U).card + 0 ≤ k + 1 at tailSize
    rw [Finset.card_insert_of_notMem wU] at tailSize
    have paCard := Finset.card_insert_le a (insert b U)
    have pbCard := Finset.card_insert_le b U
    have aU : a ∉ U := by
      intro h
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem h)] at tight
      omega
    have bU : b ∉ U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight
      have := Finset.card_insert_le a U
      omega
    obtain ⟨f, hf, hr⟩ := ih tail (by
      change (insert w U).card = k + 1
      rw [Finset.card_insert_of_notMem wU]
      omega)
    have keepA : a ∉ insert w U := by simp [wA.symm, aU]
    have keepB : b ∉ insert w U := by simp [wB.symm, bU]
    have other : ∀ x ∈ insert w U, x ≠ w → x ∈ insert a (insert b U) := by
      intro x hx hn
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ((Finset.mem_insert.mp hx).resolve_left hn))
    have ha : a ∈ insert a (insert b U) := Finset.mem_insert_self ..
    have hb : b ∈ insert a (insert b U) := Finset.mem_insert_of_mem (Finset.mem_insert_self ..)
    cases op
    · exact kw_step goal _ _ a b w (fun _ i => !(a.testBit i)) f ha hb ab keepA keepB other hf hr
        (fun e i h1 h2 h3 => and_cu a b e i h1 h2 h3) (fun e i h1 h2 h3 => and_cv a b e i h1 h2 h3)
        (fun _ _ _ _ h => h.symm)
    · exact kw_step goal _ _ a b w (fun e _ => a.testBit e) f ha hb ab keepA keepB other hf hr
        (fun e i h1 h2 h3 => or_cu a b e i h1 h2 h3) (fun e i h1 h2 h3 => or_cv a b e i h1 h2 h3)
        (fun _ _ _ _ _ => rfl)

theorem liveDirected {mask goal : Nat} {k : Nat} {S : Finset Nat}
    (live : LiveWord mask goal k 0 S) {p n : Nat}
    (hp : goal.testBit p = true) (hn : goal.testBit n = false) :
    ∃ w ∈ S, w.testBit p = true ∧ w.testBit n = false := by
  induction k generalizing S with
  | zero =>
    obtain ⟨_,rfl,_⟩ := live
    exact ⟨goal, by simp, hp, hn⟩
  | succ k ih =>
    rcases live with ⟨u, U, a, ueq, _⟩ | ⟨U,a,b,op,rfl,pa,pb,ab,fresh,tail⟩
    · omega
    obtain ⟨w, hw, wp, wn⟩ := ih tail
    rcases Finset.mem_insert.mp hw with eq | hU
    · subst w
      cases op
      · by_cases ha : a.testBit n = false
        · exact ⟨a, Finset.mem_insert_self .., and_cu a b p n wp wn (by simp [ha])⟩
        · exact ⟨b, Finset.mem_insert_of_mem (Finset.mem_insert_self ..),
            and_cv a b p n wp wn (by cases h : a.testBit n <;> simp_all)⟩
      · by_cases ha : a.testBit p = true
        · exact ⟨a, Finset.mem_insert_self .., or_cu a b p n wp wn ha⟩
        · exact ⟨b, Finset.mem_insert_of_mem (Finset.mem_insert_self ..),
            or_cv a b p n wp wn (by cases h : a.testBit p <;> simp_all)⟩
    · exact ⟨w, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU),wp,wn⟩

namespace PackedRect

theorem tb4095 (i : ℕ) : (4095 : ℕ).testBit i = decide (i < 12) := by
  have e : (4095 : ℕ) = 2 ^ 12 - 1 := by norm_num
  rw [e, Nat.testBit_two_pow_sub_one]

def tb (w e : ℕ) : Bool := !(Nat.beq (Nat.land (Nat.shiftRight w e) 1) 0)

theorem tb_eq (w e : ℕ) : tb w e = w.testBit e := by
  have h : Nat.land (Nat.shiftRight w e) 1 = 1 &&& (w >>> e) := Nat.and_comm _ _
  unfold tb Nat.testBit
  rw [h]
  generalize (1 &&& w >>> e) = X
  cases X <;> rfl

def rect (x J : ℕ) : ℕ → ℕ
  | 0 => 0
  | e + 1 => Nat.lor (cond (tb x e) (Nat.shiftLeft J (Nat.mul 12 e)) 0) (rect x J e)

def rectW (x : ℕ) : ℕ := rect x (Nat.xor (Nat.shiftRight x 12) 4095) 12

theorem rect_tb (x J i : ℕ) (hJ : J.testBit i = true) : ∀ n e : ℕ, e < n → x.testBit e = true →
    (rect x J n).testBit (12 * e + i) = true := by
  intro n
  induction n with
  | zero => intro e he; omega
  | succ n ih =>
    intro e he hx
    show ((cond (tb x n) (J <<< (12 * n)) 0) ||| rect x J n).testBit (12 * e + i) = true
    rw [Nat.testBit_or]
    by_cases hen : e = n
    · subst hen
      rw [tb_eq, hx]
      simp [Nat.testBit_shiftLeft, hJ]
    · rw [ih e (by omega) hx]
      simp

theorem rectW_tb (x e i : ℕ) (he : e < 12) (hi : i < 12) (h1 : x.testBit e = true)
    (h2 : x.testBit (12 + i) = false) : (rectW x).testBit (12 * e + i) = true := by
  apply rect_tb _ _ _ _ 12 e he h1
  show ((x >>> 12) ^^^ 4095).testBit i = true
  rw [Nat.testBit_xor, Nat.testBit_shiftRight, h2, tb4095]
  simp [hi]

def full : ℕ := 22300745198530623141535718272648361505980415

theorem full_eq : full = 2 ^ 144 - 1 := by norm_num [full]

theorem tb_land (a b q : ℕ) : (Nat.land a b).testBit q = (a.testBit q && b.testBit q) :=
  Nat.testBit_and a b q

theorem tb_lor (a b q : ℕ) : (Nat.lor a b).testBit q = (a.testBit q || b.testBit q) :=
  Nat.testBit_or a b q

theorem tb_xor (a b q : ℕ) : (Nat.xor a b).testBit q = Bool.xor (a.testBit q) (b.testBit q) :=
  Nat.testBit_xor a b q

theorem full_tb (q : ℕ) : full.testBit q = decide (q < 144) := by
  rw [full_eq, Nat.testBit_two_pow_sub_one]

theorem land_sub (h a : ℕ) (H : ∀ q, h.testBit q = true → a.testBit q = true) :
    Nat.land h a = h := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [tb_land]
  cases hh : h.testBit q
  · rfl
  · rw [H q hh]; rfl

theorem land_disj (a h : ℕ) (H : ∀ q, a.testBit q = true → h.testBit q = true → False) :
    Nat.land a h = 0 := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [tb_land, Nat.zero_testBit]
  cases ha : a.testBit q
  · rfl
  · cases hh : h.testBit q
    · rfl
    · exact (H q ha hh).elim

def orS (x s : ℕ) : ℕ := Nat.lor x (Nat.shiftRight x s)

def orSL (x s : ℕ) : ℕ := Nat.lor x (Nat.shiftLeft x s)

theorem orS_tb (x s q : ℕ) : (orS x s).testBit q = (x.testBit q || x.testBit (s + q)) := by
  show (x ||| x >>> s).testBit q = _
  rw [Nat.testBit_or, Nat.testBit_shiftRight]

theorem orSL_tb (x s q : ℕ) :
    (orSL x s).testBit q = (x.testBit q || (decide (s ≤ q) && x.testBit (q - s))) := by
  show (x ||| x <<< s).testBit q = _
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft, ge_iff_le]

theorem orS_ex (k p x n s : ℕ)
    (hx : ∀ q, x.testBit q = true → ∃ j, j < n ∧ p.testBit (k * j + q) = true) (q : ℕ)
    (h : (orS x (k * s)).testBit q = true) : ∃ j, j < n + s ∧ p.testBit (k * j + q) = true := by
  rw [orS_tb, Bool.or_eq_true] at h
  rcases h with h | h
  · obtain ⟨j, hj, hp⟩ := hx q h
    exact ⟨j, by omega, hp⟩
  · obtain ⟨j, hj, hp⟩ := hx _ h
    refine ⟨j + s, by omega, ?_⟩
    rw [Nat.mul_add, Nat.add_assoc]; exact hp

theorem orSL_ex (k p x n s : ℕ)
    (hx : ∀ q, x.testBit q = true → ∃ j, j < n ∧ k * j ≤ q ∧ p.testBit (q - k * j) = true)
    (q : ℕ) (h : (orSL x (k * s)).testBit q = true) :
    ∃ j, j < n + s ∧ k * j ≤ q ∧ p.testBit (q - k * j) = true := by
  rw [orSL_tb, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with h | ⟨hs, h⟩
  · obtain ⟨j, hj, hq, hp⟩ := hx q h
    exact ⟨j, by omega, hq, hp⟩
  · obtain ⟨j, hj, hq, hp⟩ := hx _ h
    have e : q - k * (j + s) = q - k * s - k * j := by rw [Nat.mul_add]; omega
    refine ⟨j + s, by omega, ?_, ?_⟩
    · rw [Nat.mul_add]; omega
    · rw [e]; exact hp

def rowM : ℕ := 5445847423328601499764522166702896582657

theorem rowM_tb (q : ℕ) (h : rowM.testBit q = true) : q < 144 ∧ q % 12 = 0 := by
  have hlt : q < 144 := by
    by_contra hq
    have h0 : rowM.testBit q = false := by
      apply Nat.testBit_lt_two_pow
      have h1 : rowM < 2 ^ 144 := by norm_num [rowM]
      have h2 : (2 : ℕ) ^ 144 ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [h0] at h
    exact Bool.noConfusion h
  have hall : ∀ q : ℕ, q < 144 → rowM.testBit q = true → q % 12 = 0 := by decide +kernel
  exact ⟨hlt, hall q hlt h⟩

def rowsOf (p : ℕ) : ℕ := Nat.land (orS (orS (orS (orS p 6) 3) 1) 1) rowM

def colsOf (p : ℕ) : ℕ := Nat.land (orS (orS (orS (orS p 96) 48) 24) 12) 4095

def hullC (p : ℕ) : ℕ :=
  Nat.land (orSL (orSL (orSL (orSL (rowsOf p) 6) 3) 1) 1)
    (orSL (orSL (orSL (orSL (colsOf p) 96) 48) 24) 12)

def hull (p : ℕ) : ℕ := hullC (Nat.land p full)

theorem rowsOf_tb (p q : ℕ) (h : (rowsOf p).testBit q = true) :
    (q < 144 ∧ q % 12 = 0) ∧ ∃ j, j < 12 ∧ p.testBit (j + q) = true := by
  unfold rowsOf at h
  rw [tb_land, Bool.and_eq_true] at h
  refine ⟨rowM_tb q h.2, ?_⟩
  have h0 : ∀ q, p.testBit q = true → ∃ j, j < 1 ∧ p.testBit (1 * j + q) = true :=
    fun q hq => ⟨0, by norm_num, by simpa using hq⟩
  have h1 := orS_ex 1 p _ 1 6 h0
  have h2 := orS_ex 1 p _ _ 3 h1
  have h3 := orS_ex 1 p _ _ 1 h2
  have h4 := orS_ex 1 p _ _ 1 h3
  obtain ⟨j, hj, hp⟩ := h4 q h.1
  exact ⟨j, by omega, by simpa using hp⟩

theorem colsOf_tb (p q : ℕ) (h : (colsOf p).testBit q = true) :
    q < 12 ∧ ∃ j, j < 16 ∧ p.testBit (12 * j + q) = true := by
  unfold colsOf at h
  rw [tb_land, Bool.and_eq_true, tb4095, decide_eq_true_eq] at h
  refine ⟨h.2, ?_⟩
  have h0 : ∀ q, p.testBit q = true → ∃ j, j < 1 ∧ p.testBit (12 * j + q) = true :=
    fun q hq => ⟨0, by norm_num, by simpa using hq⟩
  have h1 := orS_ex 12 p _ 1 8 h0
  have h2 := orS_ex 12 p _ _ 4 h1
  have h3 := orS_ex 12 p _ _ 2 h2
  have h4 := orS_ex 12 p _ _ 1 h3
  obtain ⟨j, hj, hp⟩ := h4 q h.1
  exact ⟨j, by omega, hp⟩

theorem hullC_spec (p : ℕ) (hp : ∀ q, p.testBit q = true → q < 144) (q : ℕ)
    (h : (hullC p).testBit q = true) :
    q < 144 ∧ ∃ i e', i < 12 ∧ e' < 12 ∧ p.testBit (12 * (q / 12) + i) = true ∧
      p.testBit (12 * e' + q % 12) = true := by
  unfold hullC at h
  rw [tb_land, Bool.and_eq_true] at h
  obtain ⟨hR, hC⟩ := h
  have r0 : ∀ q, (rowsOf p).testBit q = true →
      ∃ j, j < 1 ∧ 1 * j ≤ q ∧ (rowsOf p).testBit (q - 1 * j) = true :=
    fun q hq => ⟨0, by norm_num, by omega, by simpa using hq⟩
  have r1 := orSL_ex 1 (rowsOf p) _ 1 6 r0
  have r2 := orSL_ex 1 (rowsOf p) _ _ 3 r1
  have r3 := orSL_ex 1 (rowsOf p) _ _ 1 r2
  have r4 := orSL_ex 1 (rowsOf p) _ _ 1 r3
  obtain ⟨j, hj, hjq, hr⟩ := r4 q hR
  obtain ⟨⟨hb, hm⟩, i, hi, hpi⟩ := rowsOf_tb p _ hr
  have c0 : ∀ q, (colsOf p).testBit q = true →
      ∃ j, j < 1 ∧ 12 * j ≤ q ∧ (colsOf p).testBit (q - 12 * j) = true :=
    fun q hq => ⟨0, by norm_num, by omega, by simpa using hq⟩
  have c1 := orSL_ex 12 (colsOf p) _ 1 8 c0
  have c2 := orSL_ex 12 (colsOf p) _ _ 4 c1
  have c3 := orSL_ex 12 (colsOf p) _ _ 2 c2
  have c4 := orSL_ex 12 (colsOf p) _ _ 1 c3
  obtain ⟨j', hj', hjq', hc⟩ := c4 q hC
  obtain ⟨hlt, e', he', hpe⟩ := colsOf_tb p _ hc
  have e1 : i + (q - 1 * j) = 12 * (q / 12) + i := by omega
  have e2 : q - 12 * j' = q % 12 := by omega
  rw [e1] at hpi
  rw [e2] at hpe
  have hb' := hp _ hpe
  exact ⟨by omega, i, e', hi, by omega, hpi, hpe⟩

theorem hull_spec (p q : ℕ) (h : (hull p).testBit q = true) :
    q < 144 ∧ ∃ i e', i < 12 ∧ e' < 12 ∧ p.testBit (12 * (q / 12) + i) = true ∧
      p.testBit (12 * e' + q % 12) = true := by
  have hp : ∀ q, (Nat.land p full).testBit q = true → q < 144 := by
    intro q hq
    rw [tb_land, full_tb, Bool.and_eq_true, decide_eq_true_eq] at hq
    exact hq.2
  obtain ⟨h1, i, e', hi, he, ha, hb⟩ := hullC_spec _ hp q h
  rw [tb_land, Bool.and_eq_true] at ha hb
  exact ⟨h1, i, e', hi, he, ha.1, hb.1⟩

def tw : List ℕ → ℕ → ℕ → ℕ
  | [], _, t => t
  | a :: l, o, t => tw l (Nat.lor o a) (Nat.lor t (Nat.land o a))

def priv (t a : ℕ) : ℕ := hull (Nat.land a (Nat.xor t full))

def hullsOK (t : ℕ) : List ℕ → ℕ → Bool
  | [], _ => true
  | a :: l, acc => Nat.beq (Nat.land (priv t a) a) (priv t a) &&
      (Nat.beq (Nat.land acc (priv t a)) 0 && hullsOK t l (Nat.lor acc (priv t a)))

def avOK1 (as : List ℕ) : Bool := hullsOK (tw as 0 0) as 0

def orL : List ℕ → ℕ
  | [] => 0
  | a :: l => Nat.lor a (orL l)

def rectOK1 (l : List ℕ) : Bool := avOK1 (l.map rectW)

def IsRect (R : ℕ → Prop) : Prop :=
  ∀ e i e' i' : ℕ, e < 12 → i < 12 → e' < 12 → i' < 12 →
    R (12 * e + i) → R (12 * e' + i') → R (12 * e + i')

def Part (zs : List ((ℕ → Prop) × ℕ)) : Prop :=
  (∀ z ∈ zs, IsRect z.1) ∧
  (∀ z ∈ zs, ∀ q, z.1 q → q < 144) ∧
  (zs.Pairwise (fun z z' => ∀ q, z.1 q → z'.1 q → False)) ∧
  (∀ q, q < 144 → ∃ z ∈ zs, z.1 q) ∧
  (∀ z ∈ zs, ∀ q, z.1 q → z.2.testBit q = true)

theorem Part.rect {zs : List ((ℕ → Prop) × ℕ)} (h : Part zs) :
    ∀ z ∈ zs, IsRect z.1 := h.1

theorem Part.bnd {zs : List ((ℕ → Prop) × ℕ)} (h : Part zs) :
    ∀ z ∈ zs, ∀ q, z.1 q → q < 144 := h.2.1

theorem Part.disj {zs : List ((ℕ → Prop) × ℕ)} (h : Part zs) :
    zs.Pairwise (fun z z' => ∀ q, z.1 q → z'.1 q → False) := h.2.2.1

theorem Part.cov {zs : List ((ℕ → Prop) × ℕ)} (h : Part zs) :
    ∀ q, q < 144 → ∃ z ∈ zs, z.1 q := h.2.2.2.1

theorem Part.sub {zs : List ((ℕ → Prop) × ℕ)} (h : Part zs) :
    ∀ z ∈ zs, ∀ q, z.1 q → z.2.testBit q = true := h.2.2.2.2

theorem pw_forall {α : Type} {R : α → α → Prop} (hs : ∀ a b, R a b → R b a) :
    ∀ l : List α, l.Pairwise R → ∀ a ∈ l, ∀ b ∈ l, a ≠ b → R a b := by
  intro l
  induction l with
  | nil => intro _ a ha; simp at ha
  | cons x l ih =>
    intro h a ha b hb hab
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.mp ha with ha' | ha'
    · rcases List.mem_cons.mp hb with hb' | hb'
      · exact absurd (ha'.trans hb'.symm) hab
      · rw [ha']; exact h.1 b hb'
    · rcases List.mem_cons.mp hb with hb' | hb'
      · rw [hb']; exact hs _ _ (h.1 a ha')
      · exact ih h.2 a ha' b hb' hab

theorem tw_spec (q : ℕ) : ∀ (as : List ℕ) (o t : ℕ), (tw as o t).testBit q = false →
    t.testBit q = false ∧ (o.testBit q = true → ∀ a ∈ as, a.testBit q = false) ∧
    as.Pairwise (fun a b => ¬ (a.testBit q = true ∧ b.testBit q = true)) := by
  intro as
  induction as with
  | nil => intro o t h; exact ⟨h, fun _ a ha => by simp at ha, List.Pairwise.nil⟩
  | cons a l ih =>
    intro o t h
    obtain ⟨h1, h2, h3⟩ := ih (Nat.lor o a) (Nat.lor t (Nat.land o a)) h
    rw [tb_lor, Bool.or_eq_false_iff, tb_land] at h1
    refine ⟨h1.1, ?_, ?_⟩
    · intro ho b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · have h4 := h1.2
        rw [ho] at h4
        simpa using h4
      · exact h2 (by rw [tb_lor, ho]; rfl) b hb
    · refine List.pairwise_cons.mpr ⟨?_, h3⟩
      intro b hb hab
      have h4 := h2 (by rw [tb_lor, hab.1]; simp) b hb
      rw [h4] at hab
      exact Bool.noConfusion hab.2

theorem priv_in {zs : List ((ℕ → Prop) × ℕ)} (hP : Part zs) : ∀ z ∈ zs, ∀ q,
    (priv (tw (zs.map Prod.snd) 0 0) z.2).testBit q = true → z.1 q := by
  intro z hz q hq
  obtain ⟨hq144, i, e', hi, he', ha, hb⟩ := hull_spec _ q hq
  have key : ∀ x, x < 144 →
      (Nat.land z.2 (Nat.xor (tw (zs.map Prod.snd) 0 0) full)).testBit x = true → z.1 x := by
    intro x hx hbit
    rw [tb_land, tb_xor, full_tb, Bool.and_eq_true] at hbit
    obtain ⟨hzx, ht⟩ := hbit
    have ht' : (tw (zs.map Prod.snd) 0 0).testBit x = false := by simpa [hx] using ht
    obtain ⟨_, _, hpw⟩ := tw_spec x _ 0 0 ht'
    rw [List.pairwise_map] at hpw
    obtain ⟨z', hz', hzq⟩ := hP.cov x hx
    by_cases hzz : z' = z
    · rw [← hzz]; exact hzq
    · exfalso
      exact pw_forall (fun a b h h' => h ⟨h'.2, h'.1⟩) zs hpw z' hz' z hz hzz
        ⟨hP.sub z' hz' x hzq, hzx⟩
  have h1 := key _ (by omega) ha
  have h2 := key _ (by omega) hb
  have h3 := hP.rect z hz (q / 12) i e' (q % 12) (by omega) hi he' (Nat.mod_lt _ (by norm_num))
    h1 h2
  rwa [Nat.div_add_mod] at h3

theorem hullsOK_sound (t : ℕ) : ∀ (zs : List ((ℕ → Prop) × ℕ)) (acc : ℕ),
    (∀ z ∈ zs, ∀ q, (priv t z.2).testBit q = true → z.1 q) →
    (∀ z ∈ zs, ∀ q, z.1 q → z.2.testBit q = true) →
    zs.Pairwise (fun z z' => ∀ q, z.1 q → z'.1 q → False) →
    (∀ q, acc.testBit q = true → ∀ z ∈ zs, ¬ z.1 q) →
    hullsOK t (zs.map Prod.snd) acc = true := by
  intro zs
  induction zs with
  | nil => intros; rfl
  | cons z zs ih =>
    intro acc hh hs hd ha
    rw [List.pairwise_cons] at hd
    have hz := hh z List.mem_cons_self
    have e1 := land_sub _ _ (fun q hq => hs z List.mem_cons_self q (hz q hq))
    have e2 := land_disj acc (priv t z.2) (fun q h1 h2 => ha q h1 z List.mem_cons_self (hz q h2))
    have e3 := ih (Nat.lor acc (priv t z.2)) (fun z' hz' => hh z' (List.mem_cons_of_mem _ hz'))
      (fun z' hz' => hs z' (List.mem_cons_of_mem _ hz')) hd.2 (fun q hq z' hz' hz'q => by
        rw [tb_lor, Bool.or_eq_true] at hq
        rcases hq with hq | hq
        · exact ha q hq z' (List.mem_cons_of_mem _ hz') hz'q
        · exact hd.1 z' hz' q (hz q hq) hz'q)
    show (Nat.beq (Nat.land (priv t z.2) z.2) (priv t z.2) &&
      (Nat.beq (Nat.land acc (priv t z.2)) 0 &&
        hullsOK t (zs.map Prod.snd) (Nat.lor acc (priv t z.2)))) = true
    rw [e1, e2, e3, Nat.beq_refl]
    rfl

theorem avOK1_sound {zs : List ((ℕ → Prop) × ℕ)} (hP : Part zs) :
    avOK1 (zs.map Prod.snd) = true :=
  hullsOK_sound _ zs 0 (priv_in hP) hP.sub hP.disj (fun q hq => by simp at hq)

end PackedRect

def witnessWord (w : (Nat × Nat × Nat)) : Nat := w.1

def essentialB (mask target : Nat) (stock : List Nat) (entry : (Nat × Nat × Nat)) : Bool :=
  let (w,p,n) := entry
  mask.testBit p && mask.testBit n && target.testBit p && !target.testBit n &&
    (w.testBit p != w.testBit n) &&
    stock.all (fun x => x == w || x.testBit p == x.testBit n)

theorem essentialRequired {stock : List Nat} {entry : (Nat × Nat × Nat)} {S : Finset Nat} {k t : Nat}
    (ok : essentialB mask target stock entry = true)
    (sub : ∀ w ∈ S, w ∈ stock) (live : LiveWord mask target k t S) :
    witnessWord entry ∈ S := by
  obtain ⟨w,p,n⟩ := entry
  simp only [essentialB, Bool.and_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨mp,mn⟩,tp⟩,tn⟩,unequal⟩,rest⟩ := ok
  by_contra no
  have all : ∀ x ∈ S, AgreesAt p n x := by
    intro x hx
    have h := List.all_eq_true.mp rest x (sub x hx)
    have hw : x ≠ w := fun e => no (by simpa [witnessWord, e] using hx)
    simpa [hw, AgreesAt] using h
  have agree := liveAgrees live (mp.trans mn.symm) all
  have falseBit : target.testBit n = false := by simpa using tn
  simp [AgreesAt, tp, falseBit] at agree

theorem essentialWordsIn {stock : List Nat} {witnesses : List (Nat × Nat × Nat)} {S : Finset Nat} {k t : Nat}
    (ok : witnesses.all (essentialB mask target stock) = true)
    (sub : ∀ w ∈ S, w ∈ stock) (live : LiveWord mask target k t S) :
    (witnesses.map witnessWord).toFinset ⊆ S := by
  intro w hw
  obtain ⟨entry, mem, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hw)
  exact essentialRequired (List.all_eq_true.mp ok entry mem) sub live

theorem essentialLower {stock : List Nat} {witnesses : List (Nat × Nat × Nat)} {minimum : Nat}
    (proper : properWord mask target)
    (masked : ∀ w ∈ stock, Masked mask w)
    (ok : witnesses.all (essentialB mask target stock) = true)
    (bound : minimum ≤ (witnesses.map witnessWord).toFinset.card - 1) :
    Lower mask stock target minimum := by
  intro values build hit
  obtain ⟨k,t,S,hk,live,sub⟩ := extractWordLive masked build hit proper
  have card := Finset.card_le_card (essentialWordsIn ok sub live)
  have size := (liveWordSize live).2
  omega

theorem essentialLift {stock cutStock : List Nat} {witnesses : List (Nat × Nat × Nat)} {minimum cut prior : Nat}
    (proper : properWord mask target)
    (masked : ∀ w ∈ stock, Masked mask w)
    (ok : witnesses.all (essentialB mask target stock) = true)
    (submask : mask &&& cut = cut)
    (cutProper : properWord cut (target &&& cut))
    (supplies : ∀ w ∈ stock, AvailableWord cut cutStock (w &&& cut))
    (known : Lower cut cutStock (target &&& cut) prior)
    (bound : minimum ≤ prior + (flatSet cut (witnesses.map witnessWord).toFinset).card) :
    Lower mask stock target minimum := by
  intro values build hit
  obtain ⟨k,t,S,hk,live,sub⟩ := extractWordLive masked build hit proper
  have subW := essentialWordsIn ok sub live
  have subFlat : flatSet cut (witnesses.map witnessWord).toFinset ⊆ flatSet cut S :=
    Finset.filter_subset_filter _ subW
  have card := Finset.card_le_card subFlat
  have pf : ¬maskedFlat cut target := by simpa [maskedFlat, properWord] using cutProper
  obtain ⟨n, budget, built⟩ := maskedBuild live cut submask pf
  have starts : ∀ w ∈ projectedStock cut S, AvailableWord cut cutStock w := by
    intro w hw
    simp only [projectedStock, visibleWords, Finset.mem_insert, Finset.mem_image] at hw
    rcases hw with rfl | rfl | ⟨x,hx,rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact supplies _ (sub _ hx)
  obtain ⟨ys,len,built',out⟩ := buildableWords built starts
  have lower := known ys built' out
  omega

def unpackWitnesses (stock : List Nat) (codes : List Nat) : List (Nat × Nat × Nat) :=
  List.rec [] (fun code _ rest =>
    (stock.getD (code >>> 18) 0, (code >>> 9) &&& 511, code &&& 511) :: rest) codes

def DagAuto (mask goal : Nat) (select : Fin rows → Fin rows) : Prop :=
  Function.Surjective select ∧ relabel select mask = mask ∧ relabel select goal = goal

def mixStep (m : (List (Nat × Nat) × List (Nat × Nat))) (w : Nat) : Nat :=
  let left := List.rec 0 (fun (part,n) _ acc => ((w &&& part) <<< n) ||| acc) m.1
  let right := List.rec 0 (fun (part,n) _ acc => ((w &&& part) >>> n) ||| acc) m.2
  left ||| right

def BitLinear (f : Nat → Nat) : Prop :=
  ∀ w i, (f w).testBit i = true ↔ ∃ j, w.testBit j = true ∧ (f (2 ^ j)).testBit i = true

theorem bitLinearZero : BitLinear (fun _ => 0) := by
  simp [BitLinear]

theorem bitLinearOr {f g : Nat → Nat} (hf : BitLinear f) (hg : BitLinear g) :
    BitLinear (fun w => f w ||| g w) := by
  intro w i
  change ((f w ||| g w).testBit i = true) ↔ _
  simp only [Nat.testBit_or, Bool.or_eq_true]
  rw [hf w i, hg w i]
  constructor
  · rintro (⟨j,hw,hj⟩ | ⟨j,hw,hj⟩)
    · exact ⟨j,hw,Or.inl hj⟩
    · exact ⟨j,hw,Or.inr hj⟩
  · rintro ⟨j,hw,hj | hj⟩
    · exact Or.inl ⟨j,hw,hj⟩
    · exact Or.inr ⟨j,hw,hj⟩

theorem bitLinearLeft (mask n : Nat) : BitLinear (fun w => (w &&& mask) <<< n) := by
  intro w i
  simp only [Nat.testBit_shiftLeft, Nat.testBit_and, Nat.testBit_two_pow,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h, hw, hm⟩
    exact ⟨i-n,hw,h,rfl,hm⟩
  · rintro ⟨j,hw,h,rfl,hm⟩
    exact ⟨h,hw,hm⟩

theorem bitLinearRight (mask n : Nat) : BitLinear (fun w => (w &&& mask) >>> n) := by
  intro w i
  simp only [Nat.testBit_shiftRight, Nat.testBit_and, Nat.testBit_two_pow,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hw,hm⟩
    exact ⟨n+i,hw,rfl,hm⟩
  · rintro ⟨j,hw,rfl,hm⟩
    exact ⟨hw,hm⟩

theorem mixStepLinear (move : (List (Nat × Nat) × List (Nat × Nat))) : BitLinear (mixStep move) := by
  obtain ⟨left, right⟩ := move
  unfold mixStep
  apply bitLinearOr
  · induction left with
    | nil => exact bitLinearZero
    | cons entry rest ih =>
      obtain ⟨part, count⟩ := entry
      exact bitLinearOr (bitLinearLeft part count) ih
  · induction right with
    | nil => exact bitLinearZero
    | cons entry rest ih =>
      obtain ⟨part, count⟩ := entry
      exact bitLinearOr (bitLinearRight part count) ih

def mixMove (move : (List (List (Nat × Nat) × List (Nat × Nat)))) (w : Nat) : Nat :=
  (List.rec (motive := fun _ => Nat → Nat) id
    (fun step _ next w => next (mixStep step w)) move) w

theorem bitLinearId : BitLinear id := by
  intro w i
  change w.testBit i = true ↔ ∃ j, w.testBit j = true ∧ (2 ^ j).testBit i = true
  simp [Nat.testBit_two_pow]

theorem bitLinearComp {f g : Nat → Nat} (hf : BitLinear f) (hg : BitLinear g) :
    BitLinear (fun w => f (g w)) := by
  intro w i
  change (f (g w)).testBit i = true ↔ ∃ j, w.testBit j = true ∧ (f (g (2 ^ j))).testBit i = true
  rw [hf]
  constructor
  · rintro ⟨j,gj,fj⟩
    obtain ⟨k,wk,gk⟩ := (hg w j).mp gj
    exact ⟨k,wk,(hf (g (2^k)) i).mpr ⟨j,gk,fj⟩⟩
  · rintro ⟨j,wj,h⟩
    obtain ⟨k,gk,fk⟩ := (hf (g (2^j)) i).mp h
    exact ⟨k,(hg w k).mpr ⟨j,wj,gk⟩,fk⟩

theorem mixMoveLinear (move : (List (List (Nat × Nat) × List (Nat × Nat)))) : BitLinear (mixMove move) := by
  induction move with
  | nil => exact bitLinearId
  | cons op ops ih =>
    change BitLinear (fun w => mixMove ops (mixStep op w))
    exact bitLinearComp ih (mixStepLinear op)

def permuteAxes (axes : List Nat) (offset row : Nat) : Nat :=
  offset ^^^ (List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun j _ next i => (if row.testBit i then 1 <<< j else 0) ||| next (i + 1)) axes) 0

theorem relabelLinear (select : Fin rows → Fin rows) : BitLinear (relabel select) := by
  intro w i
  by_cases inside : i < rows
  · let ii : Fin rows := ⟨i,inside⟩
    change (relabel select w).testBit ii.val = true ↔ _
    rw [relabelBit]
    constructor
    · intro h
      refine ⟨(select ii).val,h,?_⟩
      change (relabel select (2 ^ (select ii).val)).testBit ii.val = true
      rw [relabelBit, Nat.testBit_two_pow]
      simp
    · rintro ⟨j,h,bit⟩
      change (relabel select (2^j)).testBit ii.val = true at bit
      rw [relabelBit, Nat.testBit_two_pow, decide_eq_true_eq] at bit
      exact bit ▸ h
  · rw [relabelOutside _ _ _ (Nat.le_of_not_gt inside)]
    simp [relabelOutside _ _ _ (Nat.le_of_not_gt inside)]

theorem wordMoveAgreement {select : Fin rows → Fin rows} {mask : Nat} {move : (List (List (Nat × Nat) × List (Nat × Nat)))}
    (bounded : Masked (fullMask rows) mask)
    (basis : ∀ i : Fin rows, mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = relabel select (2 ^ i.val))
    {w : Nat} (masked : Masked mask w) : mixMove move w = relabel select w := by
  apply Nat.eq_of_testBit_eq
  intro i
  apply Bool.eq_iff_iff.mpr
  rw [mixMoveLinear, relabelLinear]
  have source {j : Nat} (bit : w.testBit j = true) :
      mixMove move (2^j) = relabel select (2^j) := by
    have m : mask.testBit j = true := by
      have eq := congrArg (fun x : Nat => x.testBit j) masked
      simpa [Nat.testBit_and, bit] using eq
    have within : j < rows := by
      have eq := congrArg (fun x : Nat => x.testBit j) bounded
      simpa [Nat.testBit_and, fullMask, Nat.testBit_two_pow_sub_one, m] using eq
    exact basis ⟨j,within⟩ m
  constructor <;> rintro ⟨j,hj,hi⟩
  · exact ⟨j,hj,by rwa [← source hj]⟩
  · exact ⟨j,hj,by rwa [source hj]⟩

theorem relabelBasis {select inverse : Fin rows → Fin rows}
    (left : ∀ i, inverse (select i) = i) :
    ∀ j : Fin rows, select (inverse j) = j →
      relabel select (2 ^ j.val) = 2 ^ (inverse j).val := by
  intro j right
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases inside : i < rows
  · let pos : Fin rows := ⟨i,inside⟩
    change (relabel select (2 ^ j.val)).testBit pos.val = _
    rw [relabelBit, Nat.testBit_two_pow, Nat.testBit_two_pow]
    apply (Bool.eq_iff_iff).mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro eq
      have e : j = select pos := Fin.ext eq
      rw [e,left]
    · intro eq
      have hp : inverse j = pos := Fin.ext eq
      rw [← hp, right]
  · rw [relabelOutside _ _ _ (Nat.le_of_not_gt inside), Nat.testBit_two_pow]
    have ne : (inverse j).val ≠ i := by have := (inverse j).isLt; omega
    simp [ne]

theorem dagAutoFromMove {select inverse : Fin rows → Fin rows} {mask goal : Nat} {move : (List (List (Nat × Nat) × List (Nat × Nat)))}
    (left : ∀ i, inverse (select i) = i)
    (right : ∀ i, select (inverse i) = i)
    (bm : Masked (fullMask rows) mask)
    (gm : Masked mask goal)
    (basis : ∀ i : Fin rows, mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = 2 ^ (inverse i).val)
    (sameMask : mixMove move mask = mask) (sameGoal : mixMove move goal = goal) :
    DagAuto mask goal select ∧ ∀ w, Masked mask w → mixMove move w = relabel select w := by
  have agree {w : Nat} (hw : Masked mask w) : mixMove move w = relabel select w :=
    wordMoveAgreement bm (fun i h => (basis i h).trans (relabelBasis left i (right i)).symm) hw
  exact ⟨⟨fun i => ⟨inverse i,right i⟩,(agree (by simp [Masked])).symm.trans sameMask,
    (agree gm).symm.trans sameGoal⟩,fun _ h => agree h⟩

theorem maskedBelow {mask w : Nat} (bm : Masked (fullMask rows) mask)
    (bw : Masked mask w) : Masked (fullMask rows) w := by
  unfold Masked at *
  rw [← bw, Nat.land_assoc, bm, bw]

theorem maskedTransfer {mask w : Nat} {select : Fin rows → Fin rows}
    (same : relabel select mask = mask) (hw : Masked mask w) :
    Masked mask (relabel select w) := by
  unfold Masked at *
  rw [← same, ← relabelAnd, hw]

theorem liveMaskedImage {mask goal : Nat} {select : Fin rows → Fin rows}
    (auto : DagAuto mask goal select) (maskBounds : Masked (fullMask rows) mask)
    {k t : Nat} {S : Finset Nat} (live : LiveWord mask goal k t S)
    (masked : ∀ w ∈ S, Masked mask w) :
    LiveWord mask goal k t (S.image (relabel select)) := by
  let f := relabel select
  have hmask : f mask = mask := auto.2.1
  have inj {a b : Nat} (ma : Masked mask a) (mb : Masked mask b) :
      f a = f b → a = b :=
    relabelInj select auto.1 (maskedBelow maskBounds ma) (maskedBelow maskBounds mb)
  have proper {a : Nat} (ma : Masked mask a) (ha : properWord mask a) :
      properWord mask (f a) := by
    exact ⟨fun eq => ha.1 (inj ma (by simp [Masked]) (eq.trans (relabelZero select).symm)),
      fun eq => ha.2 (inj ma (by simp [Masked]) (eq.trans hmask.symm))⟩
  have freshImage {S : Finset Nat} {v : Nat} (hv : v ∉ S) (mv : Masked mask v)
      (ms : ∀ w ∈ S, Masked mask w) : f v ∉ S.image f := by
    intro hw
    obtain ⟨w,hs,eq⟩ := Finset.mem_image.mp hw
    exact hv (inj (ms w hs) mv eq ▸ hs)
  induction live using LiveWord.ind with
  | stop hp =>
    rw [Finset.image_singleton, auto.2.2]
    exact LiveWord.stop hp
  | @unary k t U a ha fresh tail ih =>
    let v := mask ^^^ a
    have ma := masked a (Finset.mem_insert_self ..)
    have mv : Masked mask v := by
      apply maskedGate (bank := [a]) (by simpa using ma)
      exact Or.inl ⟨a, Or.inr (Or.inr (by simp)), rfl⟩
    have hnew : ∀ w ∈ insert v U, Masked mask w := by
      intro w h
      rcases Finset.mem_insert.mp h with rfl | hU
      · exact mv
      · exact masked _ (Finset.mem_insert_of_mem hU)
    have fve : f v = mask ^^^ f a := by
      change relabel select (mask ^^^ a) = _
      rw [relabelXor, auto.2.1]
    have ht := ih hnew
    have hf := freshImage fresh mv masked
    change LiveWord mask goal (k+1) (t+1) ((insert a U).image f)
    rw [Finset.image_insert] at ht hf
    change LiveWord mask goal k t (insert (f v) (U.image f)) at ht
    rw [fve] at ht hf
    rw [Finset.image_insert]
    exact LiveWord.unary (proper ma ha) hf ht
  | @binary k t U a b op pa pb ab fresh tail ih =>
    let v := binWord op a b
    have ma := masked a (Finset.mem_insert_self ..)
    have mb := masked b (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    have mv : Masked mask v := by
      apply maskedGate (bank := [a,b]) (by simpa using And.intro ma mb)
      exact Or.inr ⟨a,b,Or.inr (Or.inr (by simp)),Or.inr (Or.inr (by simp)),by
        cases op <;> simp [v, binWord]⟩
    have hnew : ∀ w ∈ insert v U, Masked mask w := by
      intro w h
      rcases Finset.mem_insert.mp h with rfl | hU
      · exact mv
      · exact masked _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU))
    have fve : f v = binWord op (f a) (f b) := by
      cases op
      · exact relabelAnd ..
      · exact relabelOr ..
    have ht := ih hnew
    have hf := freshImage fresh mv masked
    change LiveWord mask goal (k+1) t ((insert a (insert b U)).image f)
    rw [Finset.image_insert] at ht
    change LiveWord mask goal k t (insert (f v) (U.image f)) at ht
    rw [fve] at ht
    rw [Finset.image_insert, Finset.image_insert, fve] at hf
    rw [Finset.image_insert, Finset.image_insert]
    exact LiveWord.binary (proper ma pa) (proper mb pb) (fun h => ab (inj ma mb h)) hf ht

def dagMoveWords (m : (List (List (Nat × Nat) × List (Nat × Nat)))) (ws : List Nat) : List Nat :=
  List.rec [] (fun w _ next => insertWord (mixMove m w) next) ws

theorem dagMoveSet {m : (List (List (Nat × Nat) × List (Nat × Nat)))} {ws : List Nat} {select : Fin rows → Fin rows}
    (agree : ∀ w ∈ ws, mixMove m w = relabel select w) :
    (dagMoveWords m ws).toFinset = ws.toFinset.image (relabel select) := by
  induction ws with
  | nil => simp [dagMoveWords]
  | cons w ws ih =>
    change (insertWord (mixMove m w) (dagMoveWords m ws)).toFinset = _
    rw [insertWordSet, ih (fun w hw => agree _ (List.mem_cons_of_mem _ hw)),
      agree _ List.mem_cons_self, List.toFinset_cons, Finset.image_insert]

def chartRow (chart : ({ rows : List Nat // rows.length = 24 })) (i : Nat) : Nat :=
  chart.val.getD i 0

def chartBits (w : Nat) (rows : List Nat) : Nat :=
  List.rec 0 (fun r _ packed => ((w >>> r) &&& 1) ||| (packed <<< 1)) rows

theorem chartBitsBit (w : Nat) (rows : List Nat) (i : Nat) (hi : i < rows.length) :
    (chartBits w rows).testBit i = w.testBit (rows.getD i 0) := by
  induction rows generalizing i with
  | nil => simp at hi
  | cons row rows ih =>
    change (((w >>> row) &&& 1) ||| (chartBits w rows <<< 1)).testBit i = _
    rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_shiftLeft]
    cases i with
    | zero => simp
    | succ i =>
      have lt : i < rows.length := by simpa using hi
      simp [ih i lt, Nat.testBit_succ]

def chartWord (chart : ({ rows : List Nat // rows.length = 24 })) (w : Nat) : Nat := chartBits w chart.val

def ChartOK (goal : Nat) (chart : ({ rows : List Nat // rows.length = 24 })) : Prop :=
  (∀ i : Fin 12, goal.testBit (chartRow chart i.val) = true) ∧
  (∀ i : Fin 12, goal.testBit (chartRow chart (12+i.val)) = false)

def chartCheck (goal : Nat) (chart : Option ({ rows : List Nat // rows.length = 24 })) : Bool :=
  chart.all fun c => @decide (ChartOK goal c) (by unfold ChartOK; infer_instance)

theorem chartOfCheck {goal : Nat} {chart : Option ({ rows : List Nat // rows.length = 24 })}
    (ok : chartCheck goal chart = true) (c : ({ rows : List Nat // rows.length = 24 })) (eq : chart = some c) :
    ChartOK goal c := by
  subst chart
  unfold ChartOK
  exact of_decide_eq_true ok

theorem chartWordBit (chart : ({ rows : List Nat // rows.length = 24 })) (w : Nat) {i : Nat} (hi : i < 24) :
    (chartWord chart w).testBit i = w.testBit (chartRow chart i) := by
  exact chartBitsBit w chart.val i (by rw [chart.property]; exact hi)

theorem chartPos {goal : Nat} {chart : ({ rows : List Nat // rows.length = 24 })} (ok : ChartOK goal chart) {i : Nat} (hi : i < 12) :
    goal.testBit (chartRow chart i) = true := ok.1 ⟨i,hi⟩

theorem chartNeg {goal : Nat} {chart : ({ rows : List Nat // rows.length = 24 })} (ok : ChartOK goal chart) {i : Nat} (hi : i < 12) :
    goal.testBit (chartRow chart (12+i)) = false := ok.2 ⟨i,hi⟩

theorem chartRectangles {goal : Nat} {chart : ({ rows : List Nat // rows.length = 24 })} {ws : List Nat}
    (ok : ChartOK goal chart) (nd : ws.Nodup) (kw : KWPartition goal ws.toFinset) :
    PackedRect.rectOK1 (ws.map (chartWord chart)) = true := by
  obtain ⟨f, good, rectangle⟩ := kw
  let label := fun p n => f (chartRow chart p) (chartRow chart (12+n))
  let part := fun w => ((fun q : Nat => q < 144 ∧ label (q/12) (q % 12) = w),
    PackedRect.rectW (chartWord chart w))
  have partition : PackedRect.Part (ws.map part) := by
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro z hz
      obtain ⟨w,_,rfl⟩ := List.mem_map.mp hz
      intro p n p' n' hp hn hp' hn' h h'
      have divmod (a b : Nat) (lt : b < 12) :
          (12*a+b)/12 = a ∧ (12*a+b)%12 = b := by omega
      have h1 := h.2
      have h2 := h'.2
      rw [(divmod p n hn).1, (divmod p n hn).2] at h1
      rw [(divmod p' n' hn').1, (divmod p' n' hn').2] at h2
      refine ⟨by omega,?_⟩
      rw [(divmod p n' hn').1, (divmod p n' hn').2]
      exact (rectangle _ _ _ _ (chartPos ok hp) (chartPos ok hp') (chartNeg ok hn)
        (chartNeg ok hn') (h1.trans h2.symm)).trans h1
    · intro z hz q hq
      obtain ⟨w,_,rfl⟩ := List.mem_map.mp hz
      exact hq.1
    · rw [List.pairwise_map]
      exact List.Pairwise.imp (fun hne q h1 h2 => hne (h1.2.symm.trans h2.2)) nd
    · intro q hq
      have member := (good _ _ (chartPos ok (show q/12 < 12 by omega))
        (chartNeg ok (Nat.mod_lt q (by decide : 0 < 12)))).1
      exact ⟨_, List.mem_map.mpr ⟨_,List.mem_toFinset.mp member,rfl⟩,hq,rfl⟩
    · intro z hz q hq
      obtain ⟨w,_,rfl⟩ := List.mem_map.mp hz
      obtain ⟨bound, same⟩ := hq
      have hp : q/12 < 12 := by omega
      have hn : q % 12 < 12 := Nat.mod_lt _ (by decide)
      have h := (good _ _ (chartPos ok hp) (chartNeg ok hn)).2
      change (label (q/12) (q % 12)).testBit (chartRow chart (q/12)) = true ∧
        (label (q/12) (q % 12)).testBit (chartRow chart (12+q % 12)) = false at h
      rw [same] at h
      have bit := PackedRect.rectW_tb (chartWord chart w) (q/12) (q % 12) hp hn
        ((chartWordBit chart w (by omega)).trans h.1)
        ((chartWordBit chart w (by omega)).trans h.2)
      rwa [Nat.div_add_mod] at bit
  have hw := PackedRect.avOK1_sound partition
  simpa only [PackedRect.rectOK1, List.map_map, Function.comp_def, part] using hw

theorem tightChart {goal mask : Nat} {chart : ({ rows : List Nat // rows.length = 24 })} {ws : List Nat} {fuel : Nat}
    (ok : ChartOK goal chart) (tight : ws.length = fuel + 1)
    (viable : WordViable mask goal (fuel,ws,[])) : PackedRect.rectOK1 (ws.map (chartWord chart)) = true := by
  obtain ⟨nd,k,t,cap,live⟩ := viable
  change k ≤ fuel at cap
  have card := (liveWordSize live).2
  rw [List.toFinset_card_of_nodup nd] at card
  change (ws : List Nat).length + t ≤ k + 1 at card
  have ht : t = 0 := by omega
  have hk : ws.toFinset.card = k + 1 := by
    have q : ws.toFinset.card = ws.length := List.toFinset_card_of_nodup nd
    omega
  subst t
  exact chartRectangles ok nd (kwFromLive live hk)

def dagForceWord {α : Type} (word : Nat) (cont : Nat → α) : α :=
  Nat.rec (cont 0) (fun k _ => cont (k + 1)) word

theorem dagForceWordEq {α : Type} (word : Nat) (cont : Nat → α) :
    dagForceWord word cont = cont word := by cases word <;> rfl

def dagForceWords (words : List Nat) (cont : List Nat → Bool) : Bool :=
  (List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k [])
    (fun w _ next k => dagForceWord w (fun v => next (fun rest => k (v :: rest)))) words) cont

theorem dagForceWordsEq (words : List Nat) (cont : List Nat → Bool) :
    dagForceWords words cont = cont words := by
  induction words generalizing cont with
  | nil => rfl
  | cons w ws ih =>
    change dagForceWord w (fun v => dagForceWords ws (fun rest => cont (v :: rest))) = _
    rw [dagForceWordEq, ih]

def dagBoundCloses (target : Nat) (state : (Nat × List Nat × List (Nat × Nat × Nat))) (bound : (Nat × List Nat × Nat × Nat)) : Bool :=
  let (mask, stock, lower, goal) := bound
  let (fuel, ws, history) := state
  (target &&& mask) == goal && goal != 0 && goal != mask &&
    dagForceWord (fuel - flatCount mask ws) (fun remaining =>
      if Nat.blt remaining lower then
        dagForceWords (recipeStart mask stock ws) (fun start =>
          if Nat.blt (start.length + remaining) lower then
            dagForceWords (recipeClosure mask stock history start) (fun needed =>
              if Nat.blt (needed.length + remaining) lower then
                dagForceWords (replayRecipes mask needed history.reverse stock) (fun replay =>
                  decide (replay.length + remaining < lower) &&
                    ws.all (fun w => availableB mask (replay ++ stock) (w &&& mask)))
              else false)
          else false)
      else false)

theorem dagBoundClosesEq (target : Nat) (state : (Nat × List Nat × List (Nat × Nat × Nat))) (bound : (Nat × List Nat × Nat × Nat)) :
    dagBoundCloses target state bound = boundCloses target state bound := by
  obtain ⟨fuel, ws, history⟩ := state
  obtain ⟨mask, stock, lower, goal⟩ := bound
  simp [dagBoundCloses, boundCloses, dagForceWordsEq, dagForceWordEq, Nat.blt_eq]

def dagKnownCloses (target : Nat) (bounds : List (Nat × List Nat × Nat × Nat)) (state : (Nat × List Nat × List (Nat × Nat × Nat))) : Bool :=
  List.rec false (fun bound _ later => dagBoundCloses target state bound || later) bounds

theorem dagKnownClosesEq (target : Nat) (bounds : List (Nat × List Nat × Nat × Nat)) (state : (Nat × List Nat × List (Nat × Nat × Nat))) :
    dagKnownCloses target bounds state = knownCloses target bounds state := by
  induction bounds with
  | nil => rfl
  | cons bound bounds ih =>
    change (dagBoundCloses target state bound || dagKnownCloses target bounds state) =
      (boundCloses target state bound || knownCloses target bounds state)
    rw [dagBoundClosesEq, ih]

def dagAllowedRoot (witnesses : List (Nat × Nat × Nat)) (ws : List Nat) : Bool :=
  witnesses.all (fun entry => ws.contains (witnessWord entry))

def dagTrace (mask : Nat) (stock : List Nat) (fuel : Nat) (forest : (Nat → Nat × Nat))
    (i : Nat) : Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
    (fun _ previous j =>
      let (parent, token) := forest j
      if parent == 0 then
        if token < 2 ^ stock.length then some (rootState stock fuel token) else none
      else (previous (parent - 1)).bind (childState mask token)) (fuel + 1)) i

def dagRef (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (moves : Array (List (List (Nat × Nat) × List (Nat × Nat)))) (links : (Nat → Nat → Option (Nat × Nat))) (parent token : Nat) (state : (Nat × List Nat × List (Nat × Nat × Nat))) : Bool :=
  match links parent token with
  | none => false
  | some (destination, auto) =>
    Nat.blt destination count &&
      match states destination with
      | none => false
      | some saved =>
        saved.1 == state.1 &&
          if auto == 0 then saved.2.1 == state.2.1
          else match moves[auto-1]? with
               | none => false
               | some m => saved.2.1 == dagMoveWords m state.2.1

def dagPartition (directed : Bool) (ws : List Nat) : Nat → Nat → Bool :=
  List.rec
    (fun p n => Nat.beq p 0 || Nat.beq n 0)
    (fun w _ rest p n =>
      Nat.beq p 0 || Nat.beq n 0 ||
      dagForceWord (p &&& w) (fun up =>
        dagForceWord (n &&& w) (fun down =>
          rest up down &&
            dagForceWord (p ^^^ up) (fun offP =>
              dagForceWord (if directed then n else n ^^^ down) (rest offP))))) ws

theorem dagOffBits {v w : Nat} {i : Nat} (bit : (v ^^^ (v &&& w)).testBit i = true) :
    v.testBit i = true ∧ w.testBit i = false := by
  rw [Nat.testBit_xor, Nat.testBit_and] at bit
  cases hv : v.testBit i <;> cases hw : w.testBit i <;> simp [hv, hw] at bit ⊢

theorem dagPartitionSound {directed : Bool} {ws : List Nat} {positive negative : Nat}
    (fail : dagPartition directed ws positive negative = false) :
    ∃ p n, positive.testBit p = true ∧ negative.testBit n = true ∧
      ∀ w ∈ ws, if directed then w.testBit p = true → w.testBit n = true
                  else w.testBit p = w.testBit n := by
  have nonempty {w : Nat} (hn : w ≠ 0) : ∃ j, w.testBit j = true := by
    by_contra! all
    apply hn
    apply Nat.eq_of_testBit_eq
    intro i
    simp [all i]
  induction ws generalizing positive negative with
  | nil =>
    change (Nat.beq positive 0 || Nat.beq negative 0) = false at fail
    simp only [Bool.or_eq_false_iff] at fail
    obtain ⟨p,hp⟩ := nonempty (w := positive) (fun eq => by simp [eq] at fail)
    obtain ⟨n,hn⟩ := nonempty (w := negative) (fun eq => by simp [eq] at fail)
    exact ⟨p,n,hp,hn,by simp⟩
  | cons w ws ih =>
    change (Nat.beq positive 0 || Nat.beq negative 0 ||
      dagForceWord (positive &&& w) (fun up =>
        dagForceWord (negative &&& w) (fun down =>
          dagPartition directed ws up down &&
            dagForceWord (positive ^^^ up) (fun offP =>
              dagForceWord (if directed then negative else negative ^^^ down)
                (dagPartition directed ws offP))))) = false at fail
    simp only [dagForceWordEq, Bool.or_eq_false_iff, Bool.and_eq_false_iff] at fail
    rcases fail.2 with on | off
    · obtain ⟨p,n,hp,hn,agree⟩ := ih on
      rw [Nat.testBit_and, Bool.and_eq_true] at hp hn
      refine ⟨p,n,hp.1,hn.1,?_⟩
      intro a ha
      rcases List.mem_cons.mp ha with rfl | tail
      · simp [hp.2, hn.2]
      · exact agree _ tail
    · obtain ⟨p,n,hp,hn,agree⟩ := ih off
      have hp' := dagOffBits hp
      cases mode : directed
      · have hn' : negative.testBit n = true ∧ w.testBit n = false := by
          apply dagOffBits
          simpa [mode] using hn
        refine ⟨p,n,hp'.1,hn'.1,?_⟩
        intro a ha
        rcases List.mem_cons.mp ha with rfl | tail
        · simp [hp'.2, hn'.2]
        · simpa [mode] using agree _ tail
      · have hn' : negative.testBit n = true := by simpa [mode] using hn
        refine ⟨p,n,hp'.1,hn',?_⟩
        intro a ha
        rcases List.mem_cons.mp ha with rfl | tail
        · simp [hp'.2]
        · simpa [mode] using agree _ tail

theorem dagPartitionLive {mask goal : Nat} {ws : List Nat} {k t : Nat} {directed : Bool}
    (goalMask : Masked mask goal) (live : LiveWord mask goal k t ws.toFinset)
    (noNot : directed = true → t = 0) :
    dagPartition directed ws goal (mask ^^^ goal) = true := by
  by_contra fail
  have openPair : dagPartition directed ws goal (mask ^^^ goal) = false := by
    cases h : dagPartition directed ws goal (mask ^^^ goal) <;> simp_all
  obtain ⟨p,n,hp,hn,agree⟩ := dagPartitionSound openPair
  have pm := positiveInMask goalMask hp
  have nm : mask.testBit n = true ∧ goal.testBit n = false := by
    rw [Nat.testBit_xor] at hn
    have implied := fun ht : goal.testBit n = true => positiveInMask goalMask ht
    cases hm : mask.testBit n <;> cases ht : goal.testBit n <;> simp_all
  cases mode : directed with
  | false =>
    have same := liveAgrees live (pm.trans nm.1.symm) (fun w hw => by
      simpa [mode,AgreesAt] using agree w (List.mem_toFinset.mp hw))
    simp [AgreesAt, hp, nm.2] at same
  | true =>
    have ht := noNot mode
    subst t
    obtain ⟨w,hw,a,b⟩ := liveDirected live hp nm.2
    have same := agree w (List.mem_toFinset.mp hw)
    simp [mode, a, b] at same

def dagForceCache (tags : List (Nat × Nat)) (use : List (Nat × Nat) → Bool) : Bool :=
  (List.rec (motive := fun _ => (List (Nat × Nat) → Bool) → Bool) (fun k => k [])
    (fun tag _ next k =>
      dagForceWord tag.1 (fun up => dagForceWord tag.2 (fun down =>
        next (fun tail => k ((up,down)::tail))))) tags) use

theorem dagForceCacheEq (tags : List (Nat × Nat)) (use : List (Nat × Nat) → Bool) :
    dagForceCache tags use = use tags := by
  induction tags generalizing use with
  | nil => rfl
  | cons tag rest ih =>
    obtain ⟨a,b⟩ := tag
    change dagForceWord a (fun up => dagForceWord b (fun down =>
      dagForceCache rest (fun tail => use ((up,down)::tail)))) = _
    simp only [dagForceWordEq, ih]

def dagSignalContrast (directed : Bool) (full : Nat) (tag : (Nat × Nat)) : Nat :=
  if directed then tag.1 &&& (tag.2 ^^^ full) else tag.1 ^^^ tag.2

def dagCountStep (acc : (Nat × Nat × Nat)) (column : Nat) : (Nat × Nat × Nat) :=
  (acc.1 ||| column, acc.2.1 ||| (acc.1 &&& column), acc.2.2 ||| (acc.2.1 &&& column))

def dagCountSigns (directed : Bool) (full : Nat) (tags : List (Nat × Nat))
    (use : (Nat × Nat × Nat) → Bool) : Bool :=
  (List.rec (motive := fun _ => ((Nat × Nat × Nat) → Bool) → Bool) (fun k => k (0,0,0))
    (fun tag _ more k =>
      dagForceWord (dagSignalContrast directed full tag) (fun column =>
        more (fun acc =>
          dagForceWord (acc.1 ||| column) (fun once =>
            dagForceWord (acc.2.1 ||| (acc.1 &&& column)) (fun twice =>
              dagForceWord (acc.2.2 ||| (acc.2.1 &&& column)) (fun thrice => k (once,twice,thrice)))))))
    tags) use

theorem dagCountSignsEq (directed : Bool) (full : Nat) (tags : List (Nat × Nat))
    (use : (Nat × Nat × Nat) → Bool) : dagCountSigns directed full tags use =
    use (tags.foldr (fun tag acc => dagCountStep acc (dagSignalContrast directed full tag)) (0,0,0)) := by
  induction tags generalizing use with
  | nil => rfl
  | cons tag tags ih =>
    change dagForceWord (dagSignalContrast directed full tag) (fun column =>
      dagCountSigns directed full tags (fun acc =>
        dagForceWord (acc.1 ||| column) (fun once =>
          dagForceWord (acc.2.1 ||| (acc.1 &&& column)) (fun twice =>
            dagForceWord (acc.2.2 ||| (acc.2.1 &&& column)) (fun thrice => use (once,twice,thrice)))))) = _
    simp only [dagForceWordEq, ih]
    rfl

def dagHighest (value : Nat) : Nat :=
  (Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ offset => offset)
    (fun i next w offset =>
      let shift := 1 <<< i
      dagForceWord (w >>> shift) (fun upper =>
        if Nat.beq upper 0 then next w offset else next upper (offset+shift))) 8) value 0

def dagSampleMiss (sample : (Nat × Nat)) (full : Nat) (normal tight : (Nat × Nat × Nat))
    (x y out : (Nat × Nat)) (directed : Bool) (op keep : Nat) : List Nat :=
  let counts := if directed then tight else normal
  let dx := if keep.testBit 0 then 0 else dagSignalContrast directed full x
  let dy := if op == 2 || keep.testBit 1 then 0 else dagSignalContrast directed full y
  let rest := counts.2.2 ||| (counts.2.1 ^^^ (counts.2.1 &&& dx &&& dy)) |||
    (counts.1 ^^^ (counts.1 &&& (dx ||| dy)))
  dagForceWord ((rest ||| dagSignalContrast directed full out) ^^^ full) (fun missing =>
    if Nat.beq missing 0 then [] else [unpack sample.1 18 (dagHighest missing)])

def dagPairReject (mask goal : Nat) (directed : Bool) (ws : List Nat) (pairs : List Nat) : Bool :=
  pairs.any fun code =>
    let p := code &&& 511
    let n := code >>> 9
    goal.testBit p && mask.testBit n && !goal.testBit n &&
      ws.all (fun w => if directed then !(w.testBit p) || w.testBit n
                       else w.testBit p == w.testBit n)

theorem dagPairsOpen {mask goal : Nat} {ws : List Nat} {pairs : List Nat} {k t : Nat} {directed : Bool}
    (masked : Masked mask goal) (live : LiveWord mask goal k t ws.toFinset)
    (noNot : directed = true → t = 0) : dagPairReject mask goal directed ws pairs = false := by
  apply Bool.eq_false_iff.mpr
  intro close
  obtain ⟨code,_,check⟩ := List.any_eq_true.mp close
  simp only [Bool.and_eq_true, Bool.not_eq_true, List.all_eq_true] at check
  obtain ⟨⟨⟨hp, mn⟩, hn⟩, bank⟩ := check
  have neg : goal.testBit (code >>> 9) = false := by simpa using hn
  cases mode : directed
  · have h := liveAgrees live ((positiveInMask masked hp).trans mn.symm) (fun w hw => by
      have pair := bank _ (List.mem_toFinset.mp hw)
      simpa [mode, AgreesAt] using pair)
    simp [AgreesAt, hp, neg] at h
  · have ht := noNot mode
    subst t
    obtain ⟨word,mem,on,off⟩ := liveDirected live hp neg
    have pair := bank _ (List.mem_toFinset.mp mem)
    simp [mode,on,off] at pair

def dagLocal (mask goal : Nat) (chart : Option ({ rows : List Nat // rows.length = 24 }))
    (cut : ((Nat × List Nat × List (Nat × Nat × Nat)) → Bool)) (state : (Nat × List Nat × List (Nat × Nat × Nat))) : Bool :=
  let (fuel,ws,_) := state
  ws.length > fuel + 1 ||
    (!ws.contains goal &&
      (fuel == 0 ||
        (if ws.length == fuel + 1 then
           chart.any (fun c => !PackedRect.rectOK1 (ws.map (chartWord c)))
         else false) ||
        cut state ||
        (if ws.length == fuel + 1 then !dagPartition true ws goal (mask ^^^ goal)
         else !dagPartition false ws goal (mask ^^^ goal))))

def dagSizeFloor (n op keep : Nat) : Nat :=
  (n - (if keep.testBit 0 then 0 else 1) -
    (if op == 2 || keep.testBit 1 then 0 else 1)) + 1

def dagTooWide (n fuel token : Nat) : Bool :=
  dagSizeFloor n (token / 4 % 3) (token % 4) > (fuel-1) + 1

def dagKept (ws : List Nat) (op keep x y : Nat) : List Nat :=
  keepWord (op == 2 || keep.testBit 1) y (keepWord (keep.testBit 0) x ws)

def dagGateWord (mask op x y : Nat) : Nat :=
  if Nat.beq op 0 then x &&& y else if Nat.beq op 1 then x ||| y else mask ^^^ x

def dagDirectChild (mask : Nat) (state : (Nat × List Nat × List (Nat × Nat × Nat))) (a b op keep x y out : Nat) : Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  let (fuel, ws, history) := state
  if fuel == 0 || b ≥ ws.length || (if op == 2 then a != b || keep ≥ 2 else a ≥ b) then none
  else if out == 0 || out == mask || ws.contains out then none
  else
    some (fuel-1, insertWord out (dagKept ws op keep x y), (out,x,y) :: history)

theorem dagDirectChildEq {mask a b op keep : Nat} {state : (Nat × List Nat × List (Nat × Nat × Nat))}
    (hb : b < 64) (hop : op < 3) (hk : keep < 4) :
    let x := state.2.1.getD a 0
    let y := state.2.1.getD b 0
    dagDirectChild mask state a b op keep x y (dagGateWord mask op x y) =
      childState mask (gateToken a b op keep) state := by
  obtain ⟨fuel,ws,history⟩ := state
  obtain ⟨keepEq,opEq,aEq,bEq⟩ := gateTokenFields (a := a) hb hop hk
  simp only [childState, keepEq, opEq, aEq, bEq]
  rfl

def dagTagBases (stock : List Nat) (positive negative width : Nat) : List (Nat × (Nat × Nat)) :=
  (List.rec (motive := fun _ => Nat → List (Nat × (Nat × Nat))) (fun _ => [])
    (fun w _ next i => (w, unpack positive width i, unpack negative width i) :: next (i+1)) stock) 0

def dagTagRoot (bank : List (Nat × (Nat × Nat))) (token : Nat) : List (Nat × (Nat × Nat)) :=
  (List.rec (motive := fun _ => Nat → List (Nat × (Nat × Nat))) (fun _ => [])
    (fun tag _ next k =>
      if Nat.beq (k &&& 1) 0 then next (k >>> 1) else tag :: next (k >>> 1)) bank) token

def dagTagKeep (keep : Bool) (w : Nat) (bank : List (Nat × (Nat × Nat))) : List (Nat × (Nat × Nat)) :=
  if keep then bank
  else List.rec [] (fun tag tail next => if Nat.beq tag.1 w then tail else tag :: next) bank

def dagTagInsert (tag : (Nat × (Nat × Nat))) (bank : List (Nat × (Nat × Nat))) : List (Nat × (Nat × Nat)) :=
  List.rec [tag] (fun old tail next => if Nat.ble tag.1 old.1 then tag :: old :: tail else old :: next) bank

def dagTagStep (mask full token : Nat) (bank : List (Nat × (Nat × Nat))) : List (Nat × (Nat × Nat)) :=
  let keep := token % 4
  let op := token / 4 % 3
  let x := bank.getD (token / (4*3*64)) (0,0,0)
  let y := bank.getD (token / (4*3) % 64) (0,0,0)
  let tag := (dagGateWord mask op x.1 y.1, dagGateWord full op x.2.1 y.2.1, dagGateWord full op x.2.2 y.2.2)
  dagTagInsert tag (dagTagKeep (op == 2 || keep.testBit 1) y.1 (dagTagKeep (keep.testBit 0) x.1 bank))

def dagTraceTags (mask width : Nat) (root : List (Nat × (Nat × Nat))) (fuel : Nat) (forest : (Nat → Nat × Nat))
    (i : Nat) : List (Nat × Nat) :=
  let tags := (Nat.rec (motive := fun _ => Nat → List (Nat × (Nat × Nat))) (fun _ => [])
    (fun _ previous j =>
      let (parent, token) := forest j
      if Nat.beq parent 0 then dagTagRoot root token
      else dagTagStep mask (fullMask width) token (previous (parent-1))) (fuel+1)) i
  List.rec [] (fun tag _ rest => tag.2 :: rest) tags

def dagPackWords (ws : List Nat) : Nat :=
  List.rec 0 (fun w _ tail => (w &&& fullMask 512) ||| (tail <<< 512)) ws

def dagLaneMarks (n : Nat) : Nat :=
  Nat.rec 0 (fun _ more => 1 ||| (more <<< 512)) n

def dagOmitted (a b : Nat) (left right : Bool) : Nat :=
  (if left then 0 else 1 <<< (512*a)) ||| (if right then 0 else 1 <<< (512*b))

def dagPackedPair (mask goal packed marks erased out : Nat) (directed : Bool) (pairs : List Nat) : Bool :=
  pairs.any fun code =>
    dagForceWord code (fun code =>
      dagForceWord (code &&& 511) (fun p =>
        dagForceWord (code >>> 9) (fun n =>
          let up := (packed >>> p) &&& marks
          let down := (packed >>> n) &&& marks
          let contrast := if directed then up &&& (down ^^^ marks) else up ^^^ down
          let gateOK := if directed then !out.testBit p || out.testBit n else out.testBit p == out.testBit n
          goal.testBit p && mask.testBit n && !goal.testBit n && Nat.blt p 512 && Nat.blt n 512 &&
            gateOK && Nat.beq (contrast &&& (marks ^^^ erased)) 0)))

theorem dagPackBits {ws : List Nat} {i row : Nat} (inside : i < ws.length) (width : row < 512) :
    (dagPackWords ws).testBit (512*i+row) = (ws.getD i 0).testBit row := by
  induction ws generalizing i with
  | nil => simp at inside
  | cons w ws ih =>
    change ((w &&& fullMask 512) ||| (dagPackWords ws <<< 512)).testBit (512*i+row) = _
    rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft]
    cases i with
    | zero => simp [fullMask, Nat.testBit_two_pow_sub_one, width, Nat.not_le.mpr width]
    | succ i =>
      have hi : i < ws.length := by simpa using inside
      have crossed : 512 ≤ 512*i.succ+row := by omega
      have offset : 512*i.succ+row-512 = 512*i+row := by omega
      have past : ¬ 512*i.succ+row < 512 := by omega
      simp [crossed, offset, fullMask, Nat.testBit_two_pow_sub_one, past, ih hi]

theorem dagMarkBits {length i : Nat} (inside : i < length) :
    (dagLaneMarks length).testBit (512*i) = true := by
  induction length generalizing i with
  | zero => omega
  | succ length ih =>
    change (1 ||| (dagLaneMarks length <<< 512)).testBit (512*i) = true
    rw [Nat.testBit_or, Nat.testBit_shiftLeft]
    cases i with
    | zero => simp
    | succ i =>
      have hi : i < length := by omega
      have crossed : 512 ≤ 512*i.succ := by omega
      have offset : 512*i.succ-512 = 512*i := by omega
      simp [crossed, offset, ih hi]

def dagCheckChildren (mask goal : Nat) (chart : Option ({ rows : List Nat // rows.length = 24 })) (cut : ((Nat × List Nat × List (Nat × Nat × Nat)) → Bool))
    (reference : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool) (state : (Nat × List Nat × List (Nat × Nat × Nat))) (sample : (Nat × Nat)) (tags : List (Nat × Nat)) : Bool :=
  let n := state.2.1.length
  (n ≤ 64) && !state.2.1.contains goal &&
  dagForceWord (dagPackWords state.2.1) (fun packed =>
    dagForceWord (dagLaneMarks n) (fun marks =>
      dagForceCache tags (fun tags =>
    dagForceWord (fullMask sample.2) (fun full =>
      dagCountSigns false full tags (fun normal =>
        dagCountSigns true full tags (fun tight =>
          let visit := fun a b op retains =>
            dagForceWord (state.2.1.getD a 0) (fun x =>
              dagForceWord (state.2.1.getD b 0) (fun y =>
                dagForceWord (dagGateWord mask op x y) (fun out =>
                  let xs := tags.getD a (0,0)
                  let ys := tags.getD b (0,0)
                  dagForceWord (dagGateWord full op xs.1 ys.1) (fun up =>
                    dagForceWord (dagGateWord full op xs.2 ys.2) (fun down =>
                      treeBlock 0 retains (fun keep =>
                        let token := gateToken a b op keep
                        if dagTooWide n state.1 token then true else
                          let directed := dagSizeFloor n op keep == (state.1-1)+1
                          let pairs := dagSampleMiss sample full normal tight xs ys (up,down) directed op keep
                          let erased := dagOmitted a b (keep.testBit 0) (op == 2 || keep.testBit 1)
                          if dagPackedPair mask goal packed marks erased out directed pairs then true
                          else match dagDirectChild mask state a b op keep x y out with
                          | none => true
                          | some (fuel, ws, history) => dagForceWords ws (fun forced =>
                            let child := (fuel, forced, history)
                            reference token child || dagLocal mask goal chart cut child)))))))
          treeBlock 0 n (fun a =>
            visit a a 2 2 && treeBlock (a+1) (n-(a+1)) (fun b =>
              treeBlock 0 2 (fun op => visit a b op 4)))))))))

def dagStateOK (mask : Nat) (ws : List Nat) : Bool :=
  (ws.dedup.length == ws.length) && ws.all (fun w => w &&& mask == w)

theorem dagStateOKSpec {mask : Nat} {ws : List Nat} (ok : dagStateOK mask ws = true) :
    ws.Nodup ∧ ∀ w ∈ ws, Masked mask w := by
  simp only [dagStateOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at ok
  exact ⟨List.nodup_iff_length_dedup_eq.mpr ok.1, ok.2⟩

def dagCheckNode (mask goal : Nat) (chart : Option ({ rows : List Nat // rows.length = 24 })) (cut : ((Nat × List Nat × List (Nat × Nat × Nat)) → Bool))
    (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (moves : Array (List (List (Nat × Nat) × List (Nat × Nat)))) (links : (Nat → Nat → Option (Nat × Nat)))
    (sample : (Nat × Nat)) (tags : Nat → List (Nat × Nat)) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some (fuel, ws, history) => dagForceWords ws (fun forced =>
      dagStateOK mask forced && dagCheckChildren mask goal chart cut
        (dagRef count states moves links (i+1)) (fuel, forced, history) sample (tags i))

def dagCheckRoots (mask goal : Nat) (chart : Option ({ rows : List Nat // rows.length = 24 })) (cut : ((Nat × List Nat × List (Nat × Nat × Nat)) → Bool))
    (witnesses : List (Nat × Nat × Nat)) (reference : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool) (stock : List Nat)
    (fuel : Nat) : Bool :=
  treeBlock 0 (2^stock.length) fun token =>
    let state := rootState stock fuel token
    !dagAllowedRoot witnesses state.2.1 || dagLocal mask goal chart cut state || reference token state

theorem dagLocalOpen {mask goal : Nat} {chart : Option ({ rows : List Nat // rows.length = 24 })}
    {cut : ((Nat × List Nat × List (Nat × Nat × Nat)) → Bool)} {state : (Nat × List Nat × List (Nat × Nat × Nat))}
    (masked : Masked mask goal) (chartOK : ∀ c, chart = some c → ChartOK goal c)
    (viable : WordViable mask goal state) (noCut : cut state = false) :
    dagLocal mask goal chart cut state = false := by
  obtain ⟨fuel,ws,history⟩ := state
  have ⟨nd,k,t,cap,live⟩ := viable
  change k ≤ fuel at cap
  have card := (liveWordSize live).2
  rw [List.toFinset_card_of_nodup nd] at card
  change ws.length + t ≤ k + 1 at card
  have fit : ¬ ws.length > fuel + 1 := by omega
  by_cases hz : fuel = 0
  · have kz : k = 0 := by omega
    subst k
    obtain ⟨_,eq,_⟩ := live
    have hm : goal ∈ ws := List.mem_toFinset.mp (by rw [eq]; simp)
    simp [dagLocal, fit, hm]
  by_cases tight : ws.length = fuel + 1
  · have ht : t = 0 := by omega
    subst t
    have dir := dagPartitionLive (directed := true) masked live (fun _ => rfl)
    have noChart : chart.any (fun c => !PackedRect.rectOK1 (ws.map (chartWord c))) = false := by
      cases opt : chart with
      | none => rfl
      | some c =>
        have vt : WordViable mask goal (fuel,ws,[]) := viable
        have ok := tightChart (chartOK c opt) tight vt
        simp [ok]
    simp [dagLocal, fit, hz, tight, dir, noCut, noChart]
  · have sep := dagPartitionLive (directed := false) masked live (by simp)
    simp [dagLocal, fit, hz, tight, sep, noCut]

theorem dagInsertLength (w : Nat) (ws : List Nat) :
    (insertWord w ws).length = ws.length + 1 := by
  induction ws with
  | nil => rfl
  | cons a ws ih =>
    change (if w ≤ a then w :: a :: ws else a :: insertWord w ws).length = _
    split <;> simp [ih]

theorem dagKeepLength (keep : Bool) (w : Nat) (ws : List Nat) :
    ws.length - (if keep then 0 else 1) ≤ (keepWord keep w ws).length := by
  cases keep
  · exact List.le_length_erase
  · simp [keepWord]

theorem dagWideChild {mask token : Nat} {state child : (Nat × List Nat × List (Nat × Nat × Nat))}
    (eval : childState mask token state = some child)
    (wide : dagTooWide state.2.1.length state.1 token = true) :
    child.2.1.length > child.1 + 1 := by
  obtain ⟨fuel,ws,history⟩ := state
  let keep := token % 4
  let op := token / 4 % 3
  let i := token / (4 * 3 * 64)
  let j := token / (4 * 3) % 64
  let x := ws.getD i 0
  let y := ws.getD j 0
  let z := if op == 0 then x &&& y else if op == 1 then x ||| y else mask ^^^ x
  let a := keep.testBit 0
  let b := op == 2 || keep.testBit 1
  let rest := keepWord b y (keepWord a x ws)
  let bad : Bool := fuel == 0 || j ≥ ws.length || (if op == 2 then i != j || keep ≥ 2 else i ≥ j)
  let stale : Bool := z == 0 || z == mask || ws.contains z
  change (if bad then none else if stale then none else
    some (fuel - 1, insertWord z rest, (z,x,y) :: history)) = some child at eval
  by_cases hb : bad = true
  · simp [hb] at eval
  by_cases hs : stale = true
  · simp [hb,hs] at eval
  have eq : (fuel-1, insertWord z rest, (z,x,y) :: history) = child := by simpa [hb,hs] using eval
  rw [← eq]
  change (insertWord z rest).length > fuel - 1 + 1
  rw [dagInsertLength]
  have h1 := dagKeepLength a x ws
  have h2 := dagKeepLength b y (keepWord a x ws)
  have h : ws.length - (if a then 0 else 1) - (if b then 0 else 1) + 1 > fuel - 1 + 1 :=
    of_decide_eq_true wide
  dsimp only [rest]
  omega

theorem dagKeepMem {ws : List Nat} {x w : Nat} {keep : Bool}
    (nd : ws.Nodup) (h : w ∈ keepWord keep x ws) : w ∈ ws ∧ (keep = true ∨ w ≠ x) := by
  cases keep
  · simpa [keepWord, nd.mem_erase_iff, and_comm] using h
  · simpa [keepWord] using h

theorem dagKeepNodup {ws : List Nat} (nd : ws.Nodup) (keep : Bool) (x : Nat) :
    (keepWord keep x ws).Nodup := by
  cases keep
  · exact nd.erase x
  · exact nd

theorem dagPackedPairSound {mask goal out : Nat} {ws : List Nat} {directed : Bool}
    {pairs : List Nat} {a b : Nat} {left right : Bool}
    (nd : ws.Nodup)
    (checked : dagPackedPair mask goal (dagPackWords ws) (dagLaneMarks ws.length)
      (dagOmitted a b left right) out directed pairs = true) :
    dagPairReject mask goal directed
      (out :: keepWord right (ws.getD b 0) (keepWord left (ws.getD a 0) ws)) pairs = true := by
  obtain ⟨code,mem,verdict⟩ := List.any_eq_true.mp checked
  apply List.any_eq_true.mpr
  refine ⟨code,mem,?_⟩
  simp only [dagForceWordEq, Bool.and_eq_true, Nat.blt_eq] at verdict
  obtain ⟨⟨⟨⟨⟨⟨hp, hn⟩, neg⟩, wp⟩, wn⟩, output⟩, closure⟩ := verdict
  refine Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨
    Bool.and_eq_true_iff.mpr ⟨hp,hn⟩,neg⟩,List.all_eq_true.mpr ?_⟩
  intro w hw
  rcases List.mem_cons.mp hw with rfl | later
  · exact output
  have rightMem := dagKeepMem (dagKeepNodup nd left (ws.getD a 0)) later
  have leftMem := dagKeepMem nd rightMem.1
  obtain ⟨i,inside,eq⟩ := List.mem_iff_getElem.mp leftMem.1
  have atIndex : ws.getD i 0 = w := by
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside] using eq
  have omitted : (dagOmitted a b left right).testBit (512*i) = false := by
    have cleared (j : Nat) (keep : Bool) (h : keep = true ∨ w ≠ ws.getD j 0) :
        (if keep then 0 else 1 <<< (512*j)).testBit (512*i) = false := by
      rcases h with yes | diff
      · simp [yes]
      · have ne : i ≠ j := fun same => diff (same ▸ atIndex).symm
        cases keep <;> simp [Nat.shiftLeft_eq, Nat.testBit_two_pow, show 512*j ≠ 512*i by omega]
    simp [dagOmitted, Nat.testBit_or, cleared a left leftMem.2, cleared b right rightMem.2]
  let p := code &&& 511
  let n := code >>> 9
  let marks := dagLaneMarks ws.length
  let signal := dagPackWords ws
  have mark : marks.testBit (512*i) = true := dagMarkBits inside
  have test {j : Nat} (within : j < 512) :
      ((signal >>> j) &&& marks).testBit (512*i) = w.testBit j := by
    rw [Nat.testBit_and, Nat.testBit_shiftRight, mark, Bool.and_true,
      Nat.add_comm j, dagPackBits inside within, atIndex]
  have h := congrArg (fun word => Nat.testBit word (512*i)) (Nat.beq_eq.mp closure)
  simp only [Nat.zero_testBit] at h
  change (((if directed then (signal >>> p &&& marks) &&& ((signal >>> n &&& marks) ^^^ marks)
      else (signal >>> p &&& marks) ^^^ (signal >>> n &&& marks)) &&&
    (marks ^^^ dagOmitted a b left right)).testBit (512*i)) = false at h
  have pt := test (j := p) wp
  have nt := test (j := n) wn
  cases directed <;> cases px : w.testBit p <;> cases nx : w.testBit n <;>
    simp [px,nx,pt,nt,Nat.testBit_and,Nat.testBit_xor,mark,omitted,p,n] at h ⊢

theorem dagEarlyOpen {mask goal a b op keep out : Nat} {state child : (Nat × List Nat × List (Nat × Nat × Nat))}
    (masked : Masked mask goal) (viable : WordViable mask goal child)
    (parent : state.2.1.Nodup) (eval : dagDirectChild mask state a b op keep
      (state.2.1.getD a 0) (state.2.1.getD b 0) out = some child) (pairs : List Nat) :
    dagPackedPair mask goal (dagPackWords state.2.1) (dagLaneMarks state.2.1.length)
      (dagOmitted a b (keep.testBit 0) (op == 2 || keep.testBit 1)) out
      (dagSizeFloor state.2.1.length op keep == (state.1-1)+1) pairs = false := by
  obtain ⟨fuel,ws,history⟩ := state
  let x := ws.getD a 0
  let y := ws.getD b 0
  apply Bool.eq_false_iff.mpr
  intro closed
  have closed := dagPackedPairSound parent closed
  let bad : Bool := fuel == 0 || b ≥ ws.length || (if op == 2 then a != b || keep ≥ 2 else a ≥ b)
  let stale : Bool := out == 0 || out == mask || ws.contains out
  let bank := dagKept ws op keep x y
  change (if bad then none else if stale then none else
    some (fuel-1, insertWord out bank, (out,x,y)::history)) = some child at eval
  by_cases h : bad = true
  · simp [h] at eval
  by_cases h' : stale = true
  · simp [h,h'] at eval
  have eq : (fuel-1,insertWord out bank,(out,x,y)::history) = child := by simpa [h,h'] using eval
  subst child
  obtain ⟨nd,k,t,cap,live⟩ := viable
  change k ≤ fuel-1 at cap
  have size := (liveWordSize live).2
  change (insertWord out bank : List Nat).toFinset.card + t ≤ k+1 at size
  rw [List.toFinset_card_of_nodup nd, dagInsertLength] at size
  have same : (out::bank).toFinset = (insertWord out bank).toFinset := by
    ext w
    simp only [List.mem_toFinset, List.mem_cons, insertWordMem]
  have openBank := dagPairsOpen (pairs := pairs)
    (directed := dagSizeFloor ws.length op keep == (fuel-1)+1) masked (show LiveWord mask goal k t (out::bank).toFinset by rwa [same])
  have available : (dagSizeFloor ws.length op keep == (fuel-1)+1) = true → t = 0 := by
    intro directed
    have exactBudget := beq_iff_eq.mp directed
    have first := dagKeepLength (keep.testBit 0) x ws
    have second := dagKeepLength (op == 2 || keep.testBit 1) y (keepWord (keep.testBit 0) x ws)
    change dagSizeFloor ws.length op keep = (fuel-1)+1 at exactBudget
    unfold dagSizeFloor at exactBudget
    dsimp only [bank, dagKept] at size
    omega
  have refuses := openBank available
  exact Bool.noConfusion (closed.symm.trans refuses)

theorem dagChildAt {mask goal : Nat} {chart : Option ({ rows : List Nat // rows.length = 24 })}
    {cut : ((Nat × List Nat × List (Nat × Nat × Nat)) → Bool)} {ref : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool} {state child : (Nat × List Nat × List (Nat × Nat × Nat))} {sample : (Nat × Nat)} {tags : List (Nat × Nat)} {a b op keep : Nat}
    (checked : dagCheckChildren mask goal chart cut ref state sample tags = true)
    (ha : a < state.2.1.length)
    (legal : (a = b ∧ op = 2 ∧ keep < 2) ∨ (a < b ∧ b < state.2.1.length ∧ op < 2 ∧ keep < 4))
    (eval : childState mask (gateToken a b op keep) state = some child)
    (masked : Masked mask goal) (viable : WordViable mask goal child) (nd : state.2.1.Nodup)
    (openChild : dagLocal mask goal chart cut child = false) :
    ref (gateToken a b op keep) child = true := by
  have narrow : dagTooWide state.2.1.length state.1 (gateToken a b op keep) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have tooMany := dagWideChild eval h
    obtain ⟨f,w,path⟩ := child
    simp [dagLocal, tooMany] at openChild
  simp only [dagCheckChildren, dagForceCacheEq, dagForceWordEq, dagCountSignsEq,
    Bool.and_eq_true, decide_eq_true_eq] at checked
  have width := checked.1.1
  have atA := treeBlock_at checked.2 (i := a) (Nat.zero_le _) (by simpa using ha)
  rcases Bool.and_eq_true_iff.mp atA with ⟨unary,binary⟩
  rcases legal with ⟨rfl,rfl,hk⟩ | ⟨ab,hb,hop,hk⟩
  · have atKeep := treeBlock_at unary (i := keep) (Nat.zero_le _) (by simpa using hk)
    have fields := dagDirectChildEq (mask := mask) (state := state) (a := a) (b := a) (op := 2)
      (keep := keep) (by omega) (by decide) (by omega)
    have direct := fields.trans eval
    have early := dagEarlyOpen masked viable nd direct
    rcases child with ⟨fuel,ws,history⟩
    simpa only [narrow,Bool.false_eq_true,ite_false,fields,eval,dagForceWordsEq,early,openChild,Bool.or_false] using atKeep
  · have atB := treeBlock_at binary (i := b) (by omega) (by omega)
    have atOp := treeBlock_at atB (i := op) (Nat.zero_le _) (by simpa using hop)
    have atKeep := treeBlock_at atOp (i := keep) (Nat.zero_le _) (by simpa using hk)
    have fields := dagDirectChildEq (mask := mask) (state := state) (a := a) (b := b) (op := op)
      (keep := keep) (by omega) (by omega) hk
    have direct := fields.trans eval
    have early := dagEarlyOpen masked viable nd direct
    rcases child with ⟨fuel,ws,history⟩
    simpa only [narrow,Bool.false_eq_true,ite_false,fields,eval,dagForceWordsEq,early,openChild,Bool.or_false] using atKeep

theorem readWordMasked {mask : Nat} {ws : List Nat}
    (all : ∀ w ∈ ws, Masked mask w) (i : Nat) : Masked mask (ws.getD i 0) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : ws[i]? with
  | none => simp [Masked]
  | some w => exact all w (List.mem_of_getElem? h)

theorem childStateData {mask token : Nat} {state child : (Nat × List Nat × List (Nat × Nat × Nat))}
    (eval : childState mask token state = some child)
    (masked : ∀ w ∈ state.2.1, Masked mask w) :
    child.1 < state.1 ∧ ∀ w ∈ child.2.1, Masked mask w := by
  obtain ⟨fuel,ws,history⟩ := state
  let keep := token % 4
  let op := token / 4 % 3
  let a := token / (4 * 3 * 64)
  let b := token / (4 * 3) % 64
  let x := ws.getD a 0
  let y := ws.getD b 0
  let z := if op == 0 then x &&& y else if op == 1 then x ||| y else mask ^^^ x
  let rest := keepWord (op == 2 || keep.testBit 1) y (keepWord (keep.testBit 0) x ws)
  let bad : Bool := fuel == 0 || b ≥ ws.length || (if op == 2 then a != b || keep ≥ 2 else a ≥ b)
  let stale : Bool := z == 0 || z == mask || ws.contains z
  change (if bad then none else if stale then none else
    some (fuel - 1, insertWord z rest, (z,x,y) :: history)) = some child at eval
  by_cases hb : bad = true
  · simp [hb] at eval
  by_cases hs : stale = true
  · simp [hb,hs] at eval
  have eq : (fuel-1, insertWord z rest, (z,x,y) :: history) = child := by simpa [hb,hs] using eval
  subst child
  have pos : 0 < fuel := by
    by_contra! h
    have he : fuel = 0 := by omega
    simp [bad, he] at hb
  refine ⟨by dsimp; omega,?_⟩
  have read (i : Nat) : AvailableWord mask ws (ws.getD i 0) := by
    simp only [List.getD_eq_getElem?_getD]
    cases h : ws[i]? with
    | none => exact Or.inl rfl
    | some a => exact Or.inr (Or.inr (List.mem_of_getElem? h))
  have hm : Masked mask z := by
    apply maskedGate masked
    unfold z
    split
    · exact Or.inr ⟨x,y,read _,read _,Or.inl rfl⟩
    split
    · exact Or.inr ⟨x,y,read _,read _,Or.inr rfl⟩
    · exact Or.inl ⟨x,read _,rfl⟩
  intro w hw
  rcases insertWordMem.mp hw with rfl | other
  · exact hm
  · apply masked w
    apply keepSubset (keep.testBit 0) x ws w
    exact keepSubset (op == 2 || keep.testBit 1) y _ w other

def DagMovesOK (mask goal : Nat) (width : Nat) (moves : Array (List (List (Nat × Nat) × List (Nat × Nat)))) : Prop :=
  ∀ (i : Nat) (m : (List (List (Nat × Nat) × List (Nat × Nat)))), moves[i]? = some m →
    ∃ select : Fin width → Fin width, DagAuto mask goal select ∧
      ∀ w, Masked mask w → mixMove m w = relabel select w

def dagMoves (cert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin width → Fin width) × (Fin width → Fin width)))) : Array (List (List (Nat × Nat) × List (Nat × Nat))) := (cert.map Prod.fst).toArray

def dagMoveRecordProps {width : Nat} (mask goal : Nat) (entry : ((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin width → Fin width) × (Fin width → Fin width))) : Prop :=
  let (move, select, inverse) := entry
  (∀ i, inverse (select i) = i) ∧ (∀ i, select (inverse i) = i) ∧
    (mask &&& fullMask width = mask) ∧ (goal &&& mask = goal) ∧
    (∀ i : Fin width, mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = 2 ^ (inverse i).val) ∧
    mixMove move mask = mask ∧ mixMove move goal = goal

def dagMoveRecordOK {width : Nat} (mask goal : Nat) (entry : ((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin width → Fin width) × (Fin width → Fin width))) : Bool :=
  let (move, select, inverse) := entry
  decide ((∀ i, inverse (select i) = i) ∧ (∀ i, select (inverse i) = i) ∧
    (mask &&& fullMask width = mask) ∧ (goal &&& mask = goal) ∧
    (∀ i : Fin width, mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = 2 ^ (inverse i).val) ∧
    mixMove move mask = mask ∧ mixMove move goal = goal)

theorem dagMoveRecordSpec {width : Nat} {mask goal : Nat} {entry : ((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin width → Fin width) × (Fin width → Fin width))}
    (ok : dagMoveRecordOK mask goal entry = true) : dagMoveRecordProps mask goal entry := by
  rcases entry with ⟨move,select,inverse⟩
  unfold dagMoveRecordProps
  exact of_decide_eq_true ok

theorem dagMovesOfCheck {width : Nat} {mask goal : Nat} {cert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin width → Fin width) × (Fin width → Fin width)))}
    (ok : cert.all (dagMoveRecordOK mask goal) = true) :
    DagMovesOK mask goal width (dagMoves cert) := by
  intro i m get
  simp only [dagMoves, List.getElem?_toArray, List.getElem?_map] at get
  cases e : cert[i]? with
  | none => simp [e] at get
  | some entry =>
    have eq : entry.1 = m := by simpa [e] using get
    rcases entry with ⟨move,select,inverse⟩
    obtain ⟨left,right,bm,gm,basis,mm,mg⟩ :=
      dagMoveRecordSpec (List.all_eq_true.mp ok _ (List.mem_of_getElem? e))
    subst m
    exact ⟨select, dagAutoFromMove left right bm gm basis mm mg⟩

theorem dagLinked {mask goal : Nat} {width count : Nat} {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {moves : Array (List (List (Nat × Nat) × List (Nat × Nat)))} {links : (Nat → Nat → Option (Nat × Nat))} {parent token : Nat} {state : (Nat × List Nat × List (Nat × Nat × Nat))}
    (bounds : Masked (fullMask width) mask)
    (valid : DagMovesOK mask goal width moves)
    (masked : ∀ w ∈ state.2.1, Masked mask w)
    (ok : dagRef count states moves links parent token state = true)
    {k t : Nat} (live : LiveWord mask goal k t state.2.1.toFinset) :
    ∃ i saved, i < count ∧ states i = some saved ∧ saved.1 = state.1 ∧
      LiveWord mask goal k t saved.2.1.toFinset := by
  unfold dagRef at ok
  split at ok
  · contradiction
  next destination auto h =>
    have hd := Nat.blt_eq.mp (Bool.and_eq_true_iff.mp ok).1
    have finish := (Bool.and_eq_true_iff.mp ok).2
    cases eq : states destination with
    | none => simp [eq] at finish
    | some saved =>
      simp only [eq, Bool.and_eq_true, beq_iff_eq] at finish
      refine ⟨destination,saved,hd,eq,finish.1,?_⟩
      have last := finish.2
      split at last
      · have same : saved.2.1 = state.2.1 := beq_iff_eq.mp last
        rwa [same]
      · split at last
        · contradiction
        next m hm =>
          obtain ⟨select,auto,agree⟩ := valid _ _ hm
          have same : saved.2.1 = dagMoveWords m state.2.1 := beq_iff_eq.mp last
          rw [same, dagMoveSet (fun w hw => agree w (masked w hw))]
          exact liveMaskedImage auto bounds live (fun w hw => masked _ (List.mem_toFinset.mp hw))

theorem dagAllNodes {mask goal : Nat} {width fuel count : Nat}
    {stock : List Nat} {chart : Option ({ rows : List Nat // rows.length = 24 })}
    {cut : ((Nat × List Nat × List (Nat × Nat × Nat)) → Bool)} {forest : (Nat → Nat × Nat)} {moves : Array (List (List (Nat × Nat) × List (Nat × Nat)))} {links : (Nat → Nat → Option (Nat × Nat))} {sample : (Nat × Nat)}
    {tags : Nat → List (Nat × Nat)}
    (maskBounds : Masked (fullMask width) mask)
    (goalMask : Masked mask goal)
    (chartOK : ∀ c, chart = some c → ChartOK goal c)
    (cutSound : ∀ s, WordViable mask goal s → cut s = false)
    (autos : DagMovesOK mask goal width moves)
    (verified : treeBlock 0 count (dagCheckNode mask goal chart cut count
      (dagTrace mask stock fuel forest) moves links sample tags) = true):
    ∀ cap i saved, i < count → dagTrace mask stock fuel forest i = some saved →
      saved.1 = cap → ∀ k t, k ≤ cap → ¬LiveWord mask goal k t saved.2.1.toFinset := by
  intro cap
  induction cap using Nat.strong_induction_on with
  | ind cap ih =>
    intro i s iBound stateEq sFuel k t kBound live
    rcases s with ⟨remaining, words, history⟩
    let s : (Nat × List Nat × List (Nat × Nat × Nat)) := (remaining, words, history)
    let states := dagTrace mask stock fuel forest
    change states i = some s at stateEq
    have checked := treeBlock_at verified (Nat.zero_le i) (by simpa using iBound)
    change dagCheckNode mask goal chart cut count states moves links sample tags i = true at checked
    simp only [dagCheckNode, stateEq, dagForceWordsEq, Bool.and_eq_true] at checked
    obtain ⟨nd,masked⟩ := dagStateOKSpec checked.1
    have ok := checked.2
    have viable : WordViable mask goal s := ⟨nd,k,t,sFuel ▸ kBound,live⟩
    have scanned := ok
    simp only [dagCheckChildren, Bool.and_eq_true, decide_eq_true_eq] at scanned
    have wide := scanned.1.1
    have absent := scanned.1.2
    rcases wordProgress wide viable with hit | ⟨child, possible, cv⟩
    · simpa [hit] using absent
    obtain ⟨a,b,op,keep,ha,legal,eval⟩ := possible
    have r := dagChildAt ok ha legal eval goalMask cv nd (dagLocalOpen goalMask chartOK cv (cutSound _ cv))
    have ⟨less,cm⟩ := childStateData eval masked
    have below : child.1 < cap := sFuel ▸ less
    obtain ⟨_,k',t',fits,clive⟩ := cv
    obtain ⟨j,dest,bound,restore,fuelEq,tail⟩ :=
      dagLinked maskBounds autos cm r clive
    exact ih child.1 below j dest bound restore fuelEq k' t' fits tail

theorem lowerDag {mask goal : Nat} {width fuel count : Nat}
    {stock : List Nat} {chart : Option ({ rows : List Nat // rows.length = 24 })}
    {forest : (Nat → Nat × Nat)} {moves : Array (List (List (Nat × Nat) × List (Nat × Nat)))} {links : (Nat → Nat → Option (Nat × Nat))} {sample : (Nat × Nat)}
    {tags : Nat → List (Nat × Nat)}
    {bounds : List (Nat × List Nat × Nat × Nat)} {witnesses : List (Nat × Nat × Nat)}
    (maskBounds : Masked (fullMask width) mask)
    (goalMask : Masked mask goal) (proper : properWord mask goal)
    (chartOK : ∀ c, chart = some c → ChartOK goal c)
    (autos : DagMovesOK mask goal width moves)
    (stockMasked : ∀ w ∈ stock, Masked mask w) (stockNd : stock.Nodup)
    (essential : witnesses.all (essentialB mask goal stock) = true)
    (known : Known bounds) (submasks : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (rootCheck : dagCheckRoots mask goal chart (dagKnownCloses goal bounds) witnesses
      (dagRef count (dagTrace mask stock fuel forest) moves links 0)
      stock fuel = true)
    (nodeCheck : treeBlock 0 count (dagCheckNode mask goal chart (dagKnownCloses goal bounds)
      count (dagTrace mask stock fuel forest) moves links sample tags) = true) :
    Lower mask stock goal (fuel+1) := by
  intro values build hit
  by_contra! small
  obtain ⟨k,t,S,hk,live,sub⟩ := extractWordLive stockMasked build hit proper
  have included : S ⊆ stock.toFinset := fun w hw => List.mem_toFinset.mpr (sub w hw)
  obtain ⟨token,tokenBound,eq⟩ := rootToken stock S
  rw [Finset.inter_eq_right.mpr included] at eq
  let state := rootState stock fuel token
  have eq' : state.2.1.toFinset = S := eq
  have v : WordViable mask goal state := by
    refine ⟨(rootWordSublist stock token).nodup stockNd,k,t,?_,?_⟩
    · change k ≤ fuel
      omega
    · rwa [eq']
  have cutOpen (s : (Nat × List Nat × List (Nat × Nat × Nat))) (h : WordViable mask goal s) : dagKnownCloses goal bounds s = false := by
    rw [dagKnownClosesEq]
    exact knownClosesSound known submasks h
  have openRoot := dagLocalOpen goalMask chartOK v (cutOpen _ v)
  have allowed : dagAllowedRoot witnesses state.2.1 = true := by
    apply List.all_eq_true.mpr
    intro entry mem
    apply List.contains_iff_mem.mpr
    rw [← List.mem_toFinset, eq']
    exact essentialRequired (List.all_eq_true.mp essential entry mem) sub live
  have checked := treeBlock_at rootCheck (Nat.zero_le token) (by simpa using tokenBound)
  change (!dagAllowedRoot witnesses state.2.1 || dagLocal mask goal chart (dagKnownCloses goal bounds) state ||
    dagRef count (dagTrace mask stock fuel forest) moves links 0 token state) = true at checked
  simp only [allowed,openRoot,Bool.not_true,Bool.false_or] at checked
  have finish := dagAllNodes maskBounds goalMask chartOK cutOpen autos nodeCheck
  have fits : k ≤ fuel := by omega
  have still : LiveWord mask goal k t state.2.1.toFinset := by rwa [eq']
  have stateMask : ∀ w ∈ state.2.1, Masked mask w := by
    intro w hw
    exact stockMasked _ ((rootWordSublist stock token).subset hw)
  obtain ⟨i,s,hi,restore,cap,plan⟩ := dagLinked maskBounds autos stateMask checked still
  exact finish fuel i s hi restore cap k t fits plan

def dagLookupLinks (index data indexWidth sizeBits tokenBits destinationBits autoBits trials : Nat) :
    (Nat → Nat → Option (Nat × Nat)) := fun parent token =>
  let entry := unpack index indexWidth parent
  let size := entry &&& ((1 <<< sizeBits) - 1)
  let offset := entry >>> sizeBits
  let width := tokenBits + destinationBits + autoBits
  (Nat.rec (motive := fun _ => Nat → Nat → Option (Nat × Nat)) (fun _ _ => none)
    (fun _ next lo hi =>
      if Nat.blt lo hi then
        let mid := (lo+hi)/2
        let code := unpack data width mid
        let key := code &&& ((1 <<< tokenBits) - 1)
        if Nat.beq token key then
          some ((code >>> tokenBits) &&& ((1 <<< destinationBits) - 1),
            code >>> (tokenBits + destinationBits))
        else if Nat.blt token key then next lo mid else next (mid+1) hi
      else none) trials) offset (offset+size)

def projectDAGStock (mask : Nat) (source : List Nat) (indices : List Nat) : List Nat :=
  List.rec [] (fun i _ rest => (mask &&& source.getD i 0) :: rest) indices

theorem stockMaskedOfCheck {mask : Nat} {stock : List Nat}
    (h : stock.all (fun w => w &&& mask == w) = true) :
    ∀ w ∈ stock, Masked mask w := by
  intro w hw
  exact beq_iff_eq.mp (List.all_eq_true.mp h w hw)

theorem suppliesOfCheck {oldMask : Nat} {old new : List Nat} {rename : Nat → Nat}
    (h : new.all (fun w => availableB oldMask old (rename w)) = true) :
    ∀ w ∈ new, AvailableWord oldMask old (rename w) := by
  intro w hw
  exact availableB_spec.mp (List.all_eq_true.mp h w hw)

def dagShift (mask : Nat) (move : (List (List (Nat × Nat) × List (Nat × Nat)))) (word : Nat) : Nat :=
  mixMove move (word &&& mask)

def dagShiftUnique (mask : Nat) (move : (List (List (Nat × Nat) × List (Nat × Nat)))) : Nat → Nat → Bool :=
  Nat.rec (fun _ => true) (fun i next occupied =>
    if mask.testBit i then
      dagForceWord (mixMove move (2^i)) (fun col =>
        Nat.beq (col &&& occupied) 0 && dagForceWord (occupied ||| col) next)
    else next occupied)

theorem dagShiftLinear (mask : Nat) (move : (List (List (Nat × Nat) × List (Nat × Nat)))) : BitLinear (dagShift mask move) := by
  apply bitLinearComp (mixMoveLinear move)
  simpa using bitLinearRight mask 0

theorem dagShiftBasis (mask : Nat) (move : (List (List (Nat × Nat) × List (Nat × Nat)))) (i : Nat) :
    dagShift mask move (2 ^ i) = if mask.testBit i then mixMove move (2^i) else 0 := by
  have select : 2 ^ i &&& mask = if mask.testBit i then 2^i else 0 := by
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases same : i = j
    · subst j
      simp only [Nat.testBit_and, Nat.testBit_two_pow, decide_true, Bool.true_and]
      cases mask.testBit i <;> simp
    · cases h : mask.testBit i <;> simp [Nat.testBit_and, Nat.testBit_two_pow, same, h]
  rw [dagShift, select]
  split
  · rfl
  · apply Nat.eq_of_testBit_eq
    intro j
    apply Bool.eq_iff_iff.mpr
    rw [mixMoveLinear]
    simp

theorem dagShiftUniqueSpec {mask : Nat} {move : (List (List (Nat × Nat) × List (Nat × Nat)))} {n : Nat} {occupied : Nat}
    (ok : dagShiftUnique mask move n occupied = true) :
    (∀ j < n, ∀ b, (dagShift mask move (2^j)).testBit b = true → occupied.testBit b = false) ∧
    (∀ j < n, ∀ k < n, ∀ b, (dagShift mask move (2^j)).testBit b = true →
      (dagShift mask move (2^k)).testBit b = true → j = k) := by
  induction n generalizing occupied with
  | zero => simp
  | succ n ih =>
    let col := mixMove move (2^n)
    change (if mask.testBit n then dagForceWord col (fun w =>
      Nat.beq (w &&& occupied) 0 && dagForceWord (occupied ||| w) (dagShiftUnique mask move n))
      else dagShiftUnique mask move n occupied) = true at ok
    cases active : mask.testBit n
    · simp [active,dagForceWordEq] at ok
      obtain ⟨existing,unique⟩ := ih ok
      have dead : dagShift mask move (2^n) = 0 := by simp [dagShiftBasis,active]
      refine ⟨?_,?_⟩
      · intro j hj b h
        by_cases same : j = n
        · simp [same,dead] at h
        · exact existing j (by omega) b h
      · intro j hj k hk b a c
        by_cases e : j = n
        · simp [e,dead] at a
        by_cases e' : k = n
        · simp [e',dead] at c
        exact unique j (by omega) k (by omega) b a c
    · simp only [active,ite_true,dagForceWordEq,Bool.and_eq_true] at ok
      have disjoint := Nat.beq_eq.mp ok.1
      obtain ⟨existing,unique⟩ := ih ok.2
      have colEq : dagShift mask move (2^n) = col := by simp [dagShiftBasis,active,col]
      have old {j b : Nat} (hj : j < n) (h : (dagShift mask move (2^j)).testBit b = true) :
          occupied.testBit b = false ∧ col.testBit b = false := by
        simpa [Nat.testBit_or, Bool.or_eq_false_iff] using existing j hj b h
      refine ⟨?_,?_⟩
      · intro j hj b h
        by_cases same : j = n
        · rw [same,colEq] at h
          have bit := congrArg (fun w => Nat.testBit w b) disjoint
          simpa [Nat.testBit_and,h] using bit
        · exact (old (by omega) h).1
      · intro j hj k hk b a c
        by_cases e : j = n
        · by_cases e' : k = n
          · exact e.trans e'.symm
          · rw [e,colEq,(old (by omega) c).2] at a
            contradiction
        by_cases e' : k = n
        · rw [e',colEq,(old (by omega) a).2] at c
          contradiction
        exact unique j (by omega) k (by omega) b a c

theorem dagShiftGates {mask : Nat} {move : (List (List (Nat × Nat) × List (Nat × Nat)))} {width : Nat}
    (bounded : Masked (fullMask width) mask) (checked : dagShiftUnique mask move width 0 = true) :
    (∀ a b, dagShift mask move (a &&& b) = dagShift mask move a &&& dagShift mask move b) ∧
    (∀ a b, dagShift mask move (a ||| b) = dagShift mask move a ||| dagShift mask move b) ∧
    (∀ a b, dagShift mask move (a ^^^ b) = dagShift mask move a ^^^ dagShift mask move b) := by
  let f := dagShift mask move
  have lin := dagShiftLinear mask move
  have uniq {j k i : Nat} (hj : (f (2^j)).testBit i = true) (hk : (f (2^k)).testBit i = true) : j = k := by
    have within {m : Nat} (a : (f (2^m)).testBit i = true) : m < width := by
      by_contra! big
      have eq := congrArg (fun w => Nat.testBit w m) bounded
      have zero : mask.testBit m = false := by
        simpa [Masked,fullMask,Nat.testBit_and,Nat.testBit_two_pow_sub_one,show ¬m < width by omega] using eq.symm
      simp [f,dagShiftBasis,zero] at a
    exact (dagShiftUniqueSpec checked).2 j (within hj) k (within hk) i hj hk
  refine ⟨?_,?_,?_⟩
  · intro a b
    apply Nat.eq_of_testBit_eq; intro i
    apply Bool.eq_iff_iff.mpr
    rw [Nat.testBit_and, Bool.and_eq_true, lin, lin, lin]
    constructor
    · rintro ⟨j,hj,h⟩
      rw [Nat.testBit_and, Bool.and_eq_true] at hj
      exact ⟨⟨j,hj.1,h⟩,⟨j,hj.2,h⟩⟩
    · rintro ⟨⟨j,hj,q⟩,⟨k,hk,r⟩⟩
      have same := uniq q r
      subst k
      exact ⟨j,by simp [Nat.testBit_and,hj,hk],q⟩
  · intro a b
    apply Nat.eq_of_testBit_eq; intro i
    apply Bool.eq_iff_iff.mpr
    rw [lin (a ||| b) i, Nat.testBit_or, Bool.or_eq_true, lin a i, lin b i]
    simp only [Nat.testBit_or, Bool.or_eq_true]
    constructor
    · rintro ⟨j,(left | right),same⟩
      · exact Or.inl ⟨j,left,same⟩
      · exact Or.inr ⟨j,right,same⟩
    · rintro (⟨j,left,same⟩ | ⟨j,right,same⟩)
      · exact ⟨j,Or.inl left,same⟩
      · exact ⟨j,Or.inr right,same⟩
  · intro a b
    apply Nat.eq_of_testBit_eq; intro i
    have l := lin a i
    have r := lin b i
    have v := lin (a ^^^ b) i
    cases pa : (f a).testBit i <;> cases pb : (f b).testBit i
    · rw [Nat.testBit_xor,pa,pb]
      apply Bool.eq_false_iff.mpr
      intro yes
      obtain ⟨j,hj,h⟩ := v.mp yes
      have disj : a.testBit j = true ∨ b.testBit j = true := by
        rw [Nat.testBit_xor] at hj
        cases aj : a.testBit j <;> cases bj : b.testBit j <;> simp [aj,bj] at hj ⊢
      rcases disj with da | db
      · have := l.mpr ⟨j,da,h⟩
        change (f a).testBit i = true at this
        simp [pa] at this
      · have := r.mpr ⟨j,db,h⟩
        change (f b).testBit i = true at this
        simp [pb] at this
    · rw [Nat.testBit_xor,pa,pb]
      apply v.mpr
      obtain ⟨j,hj,h⟩ := r.mp pb
      have notA : a.testBit j = false := Bool.eq_false_iff.mpr (fun yes => by
        have := l.mpr ⟨j,yes,h⟩
        change (f a).testBit i = true at this
        simp [pa] at this)
      exact ⟨j,by simp [Nat.testBit_xor,notA,hj],h⟩
    · rw [Nat.testBit_xor,pa,pb]
      apply v.mpr
      obtain ⟨j,hj,h⟩ := l.mp pa
      have notB : b.testBit j = false := Bool.eq_false_iff.mpr (fun yes => by
        have := r.mpr ⟨j,yes,h⟩
        change (f b).testBit i = true at this
        simp [pb] at this)
      exact ⟨j,by simp [Nat.testBit_xor,hj,notB],h⟩
    · rw [Nat.testBit_xor,pa,pb]
      apply Bool.eq_false_iff.mpr
      intro yes
      obtain ⟨j,hj,h⟩ := v.mp yes
      obtain ⟨a',ha,q⟩ := l.mp pa
      obtain ⟨b',hb,r⟩ := r.mp pb
      have ea := uniq h q
      have eb := uniq h r
      rw [← ea] at ha
      rw [← eb] at hb
      simp [Nat.testBit_xor,ha,hb] at hj

def dagShiftCheck (width mask goal oldMask oldGoal : Nat) (stock old : List Nat) (move : (List (List (Nat × Nat) × List (Nat × Nat)))) : Bool :=
  Nat.beq (mask &&& fullMask width) mask && dagShiftUnique mask move width 0 &&
    Nat.beq (dagShift mask move mask) oldMask && Nat.beq (dagShift mask move goal) oldGoal &&
    stock.all (fun w => availableB oldMask old (dagShift mask move w))

theorem dagShiftLower {width mask goal oldMask oldGoal : Nat} {stock old : List Nat} {min : Nat}
    (move : (List (List (Nat × Nat) × List (Nat × Nat)))) (origin : Lower oldMask old oldGoal min)
    (ok : dagShiftCheck width mask goal oldMask oldGoal stock old move = true) :
    Lower mask stock goal min := by
  simp only [dagShiftCheck,Bool.and_eq_true,Nat.beq_eq] at ok
  obtain ⟨⟨⟨⟨bounded,unique⟩,masks⟩,goals⟩,supply⟩ := ok
  obtain ⟨andG,orG,xorG⟩ := dagShiftGates bounded unique
  have zero : dagShift mask move 0 = 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    apply Bool.eq_iff_iff.mpr
    rw [dagShiftLinear]
    simp
  apply lowerMap (dagShift mask move) zero masks (fun w => by rw [xorG,masks]) andG orG (suppliesOfCheck supply)
  rwa [goals]

def moveSchedule (stages : Array (List (Nat × Nat) × List (Nat × Nat))) (indices : List Nat) : (List (List (Nat × Nat) × List (Nat × Nat))) :=
  List.rec [] (fun i _ rest => stages[i]?.getD ([],[]) :: rest) indices

def hcsGateVal {rows : Nat} (bank : List (BitVec rows)) (g : PEqualNP.CircuitLowerBounds.Gate) :
    BitVec rows :=
  let args := g.inputs.map fun i => bank.getD i 0
  match g.op with
  | PEqualNP.CircuitLowerBounds.GateOp.and => args.foldr (· &&& ·) (BitVec.allOnes rows)
  | PEqualNP.CircuitLowerBounds.GateOp.or => args.foldr (· ||| ·) 0
  | PEqualNP.CircuitLowerBounds.GateOp.not => ~~~(args.headD 0)
  | _ => 0

def hcsStep {rows : Nat} (bank : List (BitVec rows)) (g : PEqualNP.CircuitLowerBounds.Gate) :
    List (BitVec rows) :=
  bank ++ [hcsGateVal bank g]

theorem hcsGetDBit {rows : Nat} (bank : List (BitVec rows)) (i : Nat) (k : Nat) :
    (bank.getD k 0).getLsbD i = (bank.map fun w => w.getLsbD i).getD k false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases bank[k]? <;> simp

theorem hcsAndBit {rows : Nat} (xs : List (BitVec rows)) (i : Fin rows) :
    (xs.foldr (· &&& ·) (BitVec.allOnes rows)).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).all id := by
  induction xs with
  | nil => simp [i.isLt]
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_and, List.map_cons, List.all_cons, id_eq, ih]

theorem hcsOrBit {rows : Nat} (xs : List (BitVec rows)) (i : Fin rows) :
    (xs.foldr (· ||| ·) 0).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).any id := by
  induction xs with
  | nil => simp
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_or, List.map_cons, List.any_cons, id_eq, ih]

theorem hcsGateBit {rows : Nat} (bank : List (BitVec rows)) (i : Fin rows)
    (g : PEqualNP.CircuitLowerBounds.Gate)
    (hop : g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp)) :
    (hcsGateVal bank g).getLsbD i.val =
      g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false) := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, hcsAndBit, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hcsGetDBit bank i.val k
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, hcsOrBit, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hcsGetDBit bank i.val k
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, BitVec.getLsbD_not, i.isLt,
      decide_true, Bool.true_and]
    cases ins with
    | nil => simp
    | cons k _ => simp only [List.map_cons, List.headD_cons, hcsGetDBit]

theorem hcsFoldBits {rows : Nat} (bank : List (BitVec rows)) (i : Fin rows)
    (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (hfan : ∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      g.inputs.length ≤ 2) :
    (gs.foldl hcsStep bank).map (fun w => w.getLsbD i.val) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
        (bank.map fun w => w.getLsbD i.val) := by
  induction gs generalizing bank with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hstep : (hcsStep bank g).map (fun w => w.getLsbD i.val) =
        (bank.map fun w => w.getLsbD i.val) ++
          [g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false)] := by
      simp only [hcsStep, List.map_append, List.map_cons, List.map_nil,
        hcsGateBit bank i g (hfan g List.mem_cons_self).1]
    rw [ih (hcsStep bank g) (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg')), hstep]

theorem hcsGateWord {rows : Nat} (bank : List (BitVec rows))
    (g : PEqualNP.CircuitLowerBounds.Gate)
    (hop : g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp))
    (hlen : g.inputs.length ≤ 2) :
    GateWord (fullMask rows) (bank.map BitVec.toNat) (hcsGateVal bank g).toNat := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  have zeroAv : AvailableWord (fullMask rows) (bank.map BitVec.toNat) 0 := Or.inl rfl
  have maskAv : AvailableWord (fullMask rows) (bank.map BitVec.toNat) (fullMask rows) :=
    Or.inr (Or.inl rfl)
  rcases hop with rfl | rfl | rfl
  · cases ins with
    | nil => exact gateOfAvailable (by simpa [hcsGateVal, fullMask] using maskAv)
    | cons a t =>
      cases t with
      | nil => exact gateOfAvailable (by simpa [hcsGateVal] using toNatAvailable bank a)
      | cons b t =>
        cases t with
        | nil =>
          exact Or.inr ⟨_, _, toNatAvailable bank a, toNatAvailable bank b,
            Or.inl (by simp [hcsGateVal, BitVec.toNat_and])⟩
        | cons c t => simp at hlen
  · cases ins with
    | nil => exact gateOfAvailable (by simpa [hcsGateVal] using zeroAv)
    | cons a t =>
      cases t with
      | nil => exact gateOfAvailable (by simpa [hcsGateVal] using toNatAvailable bank a)
      | cons b t =>
        cases t with
        | nil =>
          exact Or.inr ⟨_, _, toNatAvailable bank a, toNatAvailable bank b,
            Or.inr (by simp [hcsGateVal, BitVec.toNat_or])⟩
        | cons c t => simp at hlen
  · cases ins with
    | nil => exact Or.inl ⟨0, zeroAv, by simpa [hcsGateVal] using notNat (0 : BitVec rows)⟩
    | cons a _ => exact Or.inl ⟨_, toNatAvailable bank a, by simpa [hcsGateVal] using notNat (bank.getD a 0)⟩

theorem hcsBuilds {rows : Nat} (bank : List (BitVec rows))
    (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (hfan : ∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      g.inputs.length ≤ 2) :
    ∃ vs, vs.length = gs.length ∧ WordBuilds (fullMask rows) (bank.map BitVec.toNat) vs ∧
      ∀ v ∈ gs.foldl hcsStep bank, v.toNat ∈ vs ++ bank.map BitVec.toNat := by
  induction gs generalizing bank with
  | nil => exact ⟨[], rfl, trivial, fun _ h => List.mem_map_of_mem h⟩
  | cons g gs ih =>
    let v := hcsGateVal bank g
    have hg := hfan g List.mem_cons_self
    obtain ⟨xs, len, build, sub⟩ := ih (hcsStep bank g) (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))
    have eq : (hcsStep bank g).map BitVec.toNat = bank.map BitVec.toNat ++ [v.toNat] := by
      simp [hcsStep, v]
    rw [eq] at build
    refine ⟨v.toNat :: xs, by simp [len], ⟨hcsGateWord bank g hg.1 hg.2, buildsWeaken ?_ build⟩, ?_⟩
    · intro u hu; exact Or.inr (Or.inr (by simpa [or_comm] using hu))
    · intro u hu; have m := sub u hu; rw [eq] at m
      simpa [List.mem_append, or_assoc, or_left_comm, or_comm] using m

def hcsCheckPow (p : Nat → Bool) : Nat → Nat → Bool
  | 0, s => p s
  | k + 1, s => hcsCheckPow p k s && hcsCheckPow p k (s + 2 ^ k)

theorem hcsCheckPow_spec {p : Nat → Bool} {k s i : Nat}
    (h : hcsCheckPow p k s = true) (lo : s ≤ i) (hi : i < s + 2 ^ k) : p i = true := by
  induction k generalizing s with
  | zero =>
    have e : i = s := by omega
    simpa [hcsCheckPow, e] using h
  | succ k ih =>
    simp only [hcsCheckPow, Bool.and_eq_true] at h
    by_cases hlt : i < s + 2 ^ k
    · exact ih h.1 lo hlt
    · exact ih h.2 (by omega) (by rw [Nat.pow_succ] at hi; omega)

theorem hcsLowerEq {m1 m2 g1 g2 min : Nat} {b1 b2 : List Nat}
    (hm : m1 = m2) (hb : b1 = b2) (hg : g1 = g2)
    (h : Lower m1 b1 g1 min) : Lower m2 b2 g2 min := by
  subst hm; subst hb; subst hg; exact h

theorem hcsEvalWord {n : Nat} (raw : List (BitVec (2 ^ n))) (goal : BitVec (2 ^ n))
    (f : (Fin n → Bool) → Bool)
    (hRaw : hcsCheckPow (fun r => (raw.map fun v => v.getLsbD r) == List.ofFn fun j : Fin n => r.testBit j.val) n 0 = true)
    (hGoal : hcsCheckPow (fun r => goal.getLsbD r == f (fun j : Fin n => r.testBit j.val)) n 0 = true)
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hev : ∀ x, C.eval (List.ofFn x) = f x) :
    (C.gates.foldl hcsStep raw).getD C.output 0 = goal := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let y : Fin n → Bool := fun k => j.testBit k.val
  have hbank : raw.map (fun v => v.getLsbD j) = List.ofFn y :=
    beq_iff_eq.mp (hcsCheckPow_spec hRaw (Nat.zero_le j) (Nat.zero_add _ ▸ hj))
  have hfg : goal.getLsbD j = f y :=
    beq_iff_eq.mp (hcsCheckPow_spec hGoal (Nat.zero_le j) (Nat.zero_add _ ▸ hj))
  have hbits := hcsFoldBits raw ⟨j, hj⟩ C.gates hfan
  have hevj : (C.wires (List.ofFn y)).getD C.output false = f y := hev y
  change (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
    (List.ofFn y)).getD C.output false = f y at hevj
  rw [← hbank, ← hbits] at hevj
  rw [hfg, ← hevj, ← hcsGetDBit]

theorem hcsLower {n : Nat} (raw : List (BitVec (2 ^ n))) (goal : BitVec (2 ^ n)) (min : Nat)
    (f : (Fin n → Bool) → Bool)
    (hRaw : hcsCheckPow (fun r => (raw.map fun v => v.getLsbD r) == List.ofFn fun j : Fin n => r.testBit j.val) n 0 = true)
    (hGoal : hcsCheckPow (fun r => goal.getLsbD r == f (fun j : Fin n => r.testBit j.val)) n 0 = true)
    (claim : Lower (fullMask (2 ^ n)) (raw.map BitVec.toNat) goal.toNat min)
    (t : Nat) (h : PEqualNP.MetaComplexity.HasCircuitSize n f t) : min ≤ t := by
  obtain ⟨C, hfan, hsz, hev⟩ := h
  obtain ⟨vs, len, built, sub⟩ := hcsBuilds raw C.gates hfan
  let eb := C.gates.foldl hcsStep raw
  have same : eb.getD C.output 0 = goal := hcsEvalWord raw goal f hRaw hGoal C hfan hev
  have av : AvailableWord (fullMask (2 ^ n)) (vs ++ raw.map BitVec.toNat) goal.toNat := by
    rw [← same, List.getD_eq_getElem?_getD]
    cases h : eb[C.output]? with
    | none => exact Or.inl rfl
    | some v => exact Or.inr (Or.inr (sub v (List.mem_of_getElem? h)))
  have lb := claim vs built av
  have hs : C.gates.length ≤ t := hsz
  omega

end PEqualNP.Outside.L_meta_42614.Core

open PEqualNP.Outside.L_meta_42614.Core
namespace PEqualNP.Outside.L_meta_42614.TableHashCert

abbrev State := Nat × List Nat × List (Nat × Nat × Nat)
abbrev Fact := Nat × List Nat × Nat × Nat

structure Code where
  count : Nat
  seed : Nat
  bucketCount : Nat
  displacementBits : Nat
  parentBits : Nat
  tokenBits : Nat
  groupBits : Nat
  displacements : Array Nat
  records : Array Nat
  groups : Array Nat

def chunk (a : Array Nat) (width i : Nat) : Nat :=
  unpack (a[i / 32]?.getD 0) width (i % 32)

def hash64 (x : Nat) : Nat :=
  let a := ((x ^^^ (x >>> 30)) * 0xbf58476d1ce4e5b9) &&& 0xffffffffffffffff
  let b := ((a ^^^ (a >>> 27)) * 0x94d049bb133111eb) &&& 0xffffffffffffffff
  b ^^^ (b >>> 31)

def bankHash (seed fuel : Nat) (ws : List Nat) : Nat :=
  hash64 (ws.foldl (fun a w =>
      ((a * 0x9e3779b97f4a7c15) ^^^ ((w ^^^ (w >>> 31)) * 0xbf58476d1ce4e5b9)) &&& 0xffffffffffffffff)
    (seed + fuel * 0x94d049bb133111eb))

def Code.record (c : Code) (i : Nat) : Nat :=
  chunk c.records (c.parentBits + c.tokenBits + 8 + c.groupBits) i

def Code.forest (c : Code) (i : Nat) : Nat × Nat :=
  let row := c.record i
  (row &&& fullMask c.parentBits, (row >>> c.parentBits) &&& fullMask c.tokenBits)

def Code.group (c : Code) (i : Nat) : Nat :=
  c.groups[(c.record i) >>> (c.parentBits + c.tokenBits + 8)]?.getD 0

def Code.probe (c : Code) (s : State) : Option Nat :=
  if c.count == 0 then none else
  let h := bankHash c.seed s.1 s.2.1
  let displacement := chunk c.displacements c.displacementBits (h % c.bucketCount)
  let i := if displacement.testBit 0 then displacement >>> 1 else
    ((h >>> 20) + (displacement >>> 1) * (1 + (h >>> 40) % (c.count - 1))) % c.count
  if ((c.record i) >>> (c.parentBits + c.tokenBits)) &&& 255 == (h >>> 8) &&& 255 then some i else none

def reference (count : Nat) (states : Nat → Option State) (probe : State → Option Nat)
    (_token : Nat) (s : State) : Bool :=
  match probe s with
  | none => false
  | some i => Nat.blt i count &&
    match states i with
    | none => false
    | some saved => saved.1 == s.1 && saved.2.1 == s.2.1

theorem linked {count : Nat} {states : Nat → Option State} {probe : State → Option Nat}
    {token : Nat} {s : State} (ok : reference count states probe token s = true)
    {mask goal k t : Nat} (live : LiveWord mask goal k t s.2.1.toFinset) :
    ∃ i saved, i < count ∧ states i = some saved ∧ saved.1 = s.1 ∧ LiveWord mask goal k t saved.2.1.toFinset := by
  unfold reference at ok
  split at ok
  · contradiction
  next i _ =>
    have ⟨hi,rest⟩ := Bool.and_eq_true_iff.mp ok
    cases eq : states i with
    | none => simp [eq] at rest
    | some saved =>
      simp only [eq,Bool.and_eq_true,beq_iff_eq] at rest
      exact ⟨i,saved,Nat.blt_eq.mp hi,eq,rest.1,by rwa [rest.2]⟩

def selectFacts (bits : Nat) (xs : List Fact) : List Fact :=
  (List.rec (motive := fun _ => Nat → List Fact) (fun _ => [])
    (fun x _ next m => if m.testBit 0 then x :: next (m >>> 1) else next (m >>> 1)) xs) bits

theorem selectedMem {bits : Nat} {xs : List Fact} {x : Fact} (h : x ∈ selectFacts bits xs) : x ∈ xs := by
  induction xs generalizing bits with
  | nil => simp [selectFacts] at h
  | cons y ys ih =>
    change x ∈ (if bits.testBit 0 then y :: selectFacts (bits >>> 1) ys else selectFacts (bits >>> 1) ys) at h
    split at h
    · rcases List.mem_cons.mp h with rfl | ht
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih ht)
    · exact List.mem_cons_of_mem _ (ih h)

structure Problem where
  mask : Nat
  goal : Nat
  bank : List Nat
  fuel : Nat
  chart : Option ({ rows : List Nat // rows.length = 24 })
  witnesses : List (Nat × Nat × Nat)
  sample : Nat × Nat
  positiveTags : Nat
  negativeTags : Nat
  code : Code

def Problem.states (p : Problem) := dagTrace p.mask p.bank p.fuel p.code.forest
def Problem.ref (p : Problem) := reference p.code.count p.states p.code.probe
def Problem.tags (p : Problem) := dagTraceTags p.mask p.sample.2
    (dagTagBases p.bank p.positiveTags p.negativeTags p.sample.2) p.fuel p.code.forest

def Problem.check (p : Problem) (facts : List Fact) (i : Nat) : Bool :=
  match p.states i with
  | none => false
  | some (remaining, ws, history) => dagForceWords ws (fun forced =>
      dagStateOK p.mask forced && dagCheckChildren p.mask p.goal p.chart
       (dagKnownCloses p.goal (selectFacts (p.code.group i) facts)) p.ref
       (remaining,forced,history) p.sample (p.tags i))

def Problem.roots (p : Problem) (facts : List Fact) : Bool :=
  dagCheckRoots p.mask p.goal p.chart (dagKnownCloses p.goal facts) p.witnesses p.ref p.bank p.fuel

theorem SoundCuts {mask goal : Nat} {facts : List Fact} (known : Known facts)
    (sub : ∀ b ∈ facts, mask &&& b.1 = b.1) (s : State) (v : WordViable mask goal s) :
    dagKnownCloses goal facts s = false := by
  rw [dagKnownClosesEq]
  exact knownClosesSound known sub v

theorem allStates (p : Problem) (facts : List Fact) (known : Known facts)
    (sub : ∀ b ∈ facts, p.mask &&& b.1 = b.1) (masked : Masked p.mask p.goal)
    (chartOK : ∀ c, p.chart = some c → ChartOK p.goal c)
    (verified : treeBlock 0 p.code.count (p.check facts) = true) :
    ∀ cap i saved, i < p.code.count → p.states i = some saved → saved.1 = cap →
      ∀ k t, k ≤ cap → ¬LiveWord p.mask p.goal k t saved.2.1.toFinset := by
  intro cap
  induction cap using Nat.strong_induction_on with
  | ind cap ih =>
    intro i s hi es hs k t hk live
    rcases s with ⟨remaining,ws,hist⟩
    let s : State := (remaining,ws,hist)
    change p.states i = some s at es
    have step := treeBlock_at verified (Nat.zero_le i) (by simpa using hi)
    simp only [Problem.check, es, dagForceWordsEq, Bool.and_eq_true] at step
    obtain ⟨nd,maskWs⟩ := dagStateOKSpec step.1
    have ok := step.2
    have scanned := ok
    simp only [dagCheckChildren,Bool.and_eq_true,decide_eq_true_eq] at scanned
    have viable : WordViable p.mask p.goal s := ⟨nd,k,t,hs ▸ hk,live⟩
    rcases wordProgress scanned.1.1 viable with hit | ⟨child,possible,cv⟩
    · simpa [hit] using scanned.1.2
    obtain ⟨a,b,op,keep,ha,legal,eval⟩ := possible
    have knows : Known (selectFacts (p.code.group i) facts) := fun b h => known b (selectedMem h)
    have sub' : ∀ b ∈ selectFacts (p.code.group i) facts, p.mask &&& b.1 = b.1 :=
      fun b h => sub b (selectedMem h)
    have r := dagChildAt ok ha legal eval masked cv nd (dagLocalOpen masked chartOK cv (SoundCuts knows sub' _ cv))
    have ⟨less,_⟩ := childStateData eval maskWs
    have below : child.1 < cap := hs ▸ less
    obtain ⟨_,k',t',fits,run⟩ := cv
    obtain ⟨j,dest,bound,restore,fe,tail⟩ := linked r run
    exact ih child.1 below j dest bound restore fe k' t' fits tail

theorem lower (p : Problem) (facts : List Fact) (known : Known facts)
    (sub : facts.all (fun b => p.mask &&& b.1 == b.1) = true)
    (masked : Masked p.mask p.goal) (proper : properWord p.mask p.goal)
    (chartOK : chartCheck p.goal p.chart = true)
    (stockMasked : p.bank.all (fun w => w &&& p.mask == w) = true)
    (nd : p.bank.Nodup) (ess : p.witnesses.all (essentialB p.mask p.goal p.bank) = true)
    (root : p.roots facts = true) (nodes : treeBlock 0 p.code.count (p.check facts) = true) :
    Lower p.mask p.bank p.goal (p.fuel+1) := by
  have subm : ∀ b ∈ facts, p.mask &&& b.1 = b.1 := fun b hb => beq_iff_eq.mp (List.all_eq_true.mp sub b hb)
  have chart := chartOfCheck chartOK
  have sm := stockMaskedOfCheck stockMasked
  intro values build hit
  by_contra! small
  obtain ⟨k,t,S,hk,live,incl⟩ := extractWordLive sm build hit proper
  have included : S ⊆ p.bank.toFinset := fun w hw => List.mem_toFinset.mpr (incl w hw)
  obtain ⟨token,tbound,eq⟩ := rootToken p.bank S
  rw [Finset.inter_eq_right.mpr included] at eq
  let state := rootState p.bank p.fuel token
  have eq' : state.2.1.toFinset = S := eq
  have v : WordViable p.mask p.goal state := by
    refine ⟨(rootWordSublist p.bank token).nodup nd,k,t,?_,?_⟩
    · change k ≤ p.fuel
      omega
    · rwa [eq']
  have openRoot := dagLocalOpen masked chart v (SoundCuts known subm _ v)
  have allowed : dagAllowedRoot p.witnesses state.2.1 = true := by
    apply List.all_eq_true.mpr
    intro entry mem
    apply List.contains_iff_mem.mpr
    rw [← List.mem_toFinset,eq']
    exact essentialRequired (List.all_eq_true.mp ess entry mem) incl live
  have checked := treeBlock_at root (Nat.zero_le token) (by simpa using tbound)
  change (!dagAllowedRoot p.witnesses state.2.1 ||
    dagLocal p.mask p.goal p.chart (dagKnownCloses p.goal facts) state || p.ref token state) = true at checked
  simp only [allowed,openRoot,Bool.not_true,Bool.false_or] at checked
  have still : LiveWord p.mask p.goal k t state.2.1.toFinset := by rwa [eq']
  obtain ⟨i,s,hi,restore,cap,plan⟩ := linked checked still
  exact allStates p facts known subm masked chart nodes p.fuel i s hi restore cap k t (by omega) plan

end PEqualNP.Outside.L_meta_42614.TableHashCert

open PEqualNP.Outside.L_meta_42614.TableHashCert
namespace PEqualNP.Outside.L_meta_42614.Proof
def p48 : Problem := ⟨0x22002200220022, 0x22002000200000, [0x20002000200020, 0x22000000220000, 0x22002200000000], 3,
  some ⟨[21, 37, 49, 21, 21, 21, 21, 21, 21, 21, 21, 21, 5, 17, 33, 5, 5, 5, 5, 5, 5, 5, 5, 5], rfl⟩, [(0x20002000200020, 21, 17), (0x22000000220000, 21, 5), (0x22002200000000, 37, 5)],
  (0x8d40a31088944215108d42235028d40231008940215108c42231108940a25088540a15, 16), 0xefbcdf73becf, 0x182824124205,
  ⟨1, 1, 2, 1, 1, 3, 1,
  #[0x2],
  #[0x38e],
  #[0x0]⟩⟩
def p48Fact : Fact := (p48.mask, p48.bank, p48.fuel+1, p48.goal)
def p48Cuts : List Fact := []
theorem p48Known : Known p48Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p48Block0 : treeBlock 0 1 (p48.check p48Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p48All : treeBlock 0 1 (p48.check p48Cuts) = true := p48Block0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p48Lower : Lower p48.mask p48.bank p48.goal (p48.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p48 p48Cuts p48Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p48All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def p49 : Problem := ⟨0x30303030, 0x30202000, [0x20202020, 0x30003000, 0x30300000], 3,
  some ⟨[13, 21, 28, 13, 13, 13, 13, 13, 13, 13, 13, 13, 5, 12, 20, 5, 5, 5, 5, 5, 5, 5, 5, 5], rfl⟩, [(0x20202020, 13, 12), (0x30003000, 13, 5), (0x30300000, 21, 5)],
  (0x20740a1c06054280d0a074181d02874081c02054080d0a070181c0a0540a15060340a0d, 16), 0xefbcdf73becf, 0x182824124205,
  ⟨1, 1, 2, 1, 1, 3, 1,
  #[0x2],
  #[0xcee],
  #[0x0]⟩⟩
def p49Fact : Fact := (p49.mask, p49.bank, p49.fuel+1, p49.goal)
def p49Cuts : List Fact := []
theorem p49Known : Known p49Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p49Block0 : treeBlock 0 1 (p49.check p49Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p49All : treeBlock 0 1 (p49.check p49Cuts) = true := p49Block0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p49Lower : Lower p49.mask p49.bank p49.goal (p49.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p49 p49Cuts p49Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p49All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def p50 : Problem := ⟨0x44004400440044, 0x44004000400000, [0x40004000400040, 0x44000000440000, 0x44004400000000], 3,
  some ⟨[22, 38, 50, 22, 22, 22, 22, 22, 22, 22, 22, 22, 6, 18, 34, 6, 6, 6, 6, 6, 6, 6, 6, 6], rfl⟩, [(0x40004000400040, 22, 18), (0x44000000440000, 22, 6), (0x44004400000000, 38, 6)],
  (0x10d80c32090984416110d82436030d80432010980416110c82432110980c26090580c16, 16), 0xefbcdf73becf, 0x182824124205,
  ⟨1, 1, 2, 1, 1, 3, 1,
  #[0x2],
  #[0x64e],
  #[0x0]⟩⟩
def p50Fact : Fact := (p50.mask, p50.bank, p50.fuel+1, p50.goal)
def p50Cuts : List Fact := []
theorem p50Known : Known p50Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p50Block0 : treeBlock 0 1 (p50.check p50Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p50All : treeBlock 0 1 (p50.check p50Cuts) = true := p50Block0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p50Lower : Lower p50.mask p50.bank p50.goal (p50.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p50 p50Cuts p50Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p50All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def p51 : Problem := ⟨0x444400004444, 0x444000004000, [0x404000004040, 0x440000004400, 0x444400000000], 3,
  some ⟨[14, 38, 42, 14, 14, 14, 14, 14, 14, 14, 14, 14, 6, 10, 34, 6, 6, 6, 6, 6, 6, 6, 6, 6], rfl⟩, [(0x404000004040, 14, 10), (0x440000004400, 14, 6), (0x444400000000, 38, 6)],
  (0x10b80c2a05098440e110b8142e030b8042a01098040e110a8142a110980c26050380c0e, 16), 0xefbcdf73becf, 0x182824124205,
  ⟨1, 1, 2, 1, 1, 3, 1,
  #[0x2],
  #[0xf1e],
  #[0x0]⟩⟩
def p51Fact : Fact := (p51.mask, p51.bank, p51.fuel+1, p51.goal)
def p51Cuts : List Fact := []
theorem p51Known : Known p51Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p51Block0 : treeBlock 0 1 (p51.check p51Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p51All : treeBlock 0 1 (p51.check p51Cuts) = true := p51Block0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p51Lower : Lower p51.mask p51.bank p51.goal (p51.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p51 p51Cuts p51Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p51All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def p52 : Problem := ⟨0x50505050, 0x50404000, [0x40404040, 0x50005000, 0x50500000], 3,
  some ⟨[14, 22, 28, 14, 14, 14, 14, 14, 14, 14, 14, 14, 6, 12, 20, 6, 6, 6, 6, 6, 6, 6, 6, 6], rfl⟩, [(0x40404040, 14, 12), (0x50005000, 14, 6), (0x50500000, 22, 6)],
  (0x20780c1c06058280e0a078181e03078081c02058080e0a070181c0a0580c16060380c0e, 16), 0xefbcdf73becf, 0x182824124205,
  ⟨1, 1, 2, 1, 1, 3, 1,
  #[0x1],
  #[0x93e],
  #[0x0]⟩⟩
def p52Fact : Fact := (p52.mask, p52.bank, p52.fuel+1, p52.goal)
def p52Cuts : List Fact := []
theorem p52Known : Known p52Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p52Block0 : treeBlock 0 1 (p52.check p52Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p52All : treeBlock 0 1 (p52.check p52Cuts) = true := p52Block0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p52Lower : Lower p52.mask p52.bank p52.goal (p52.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p52 p52Cuts p52Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p52All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def p53 : Problem := ⟨0x33330000, 0x32200000, [0x22220000, 0x30300000, 0x33000000], 3,
  some ⟨[21, 25, 28, 21, 21, 21, 21, 21, 21, 21, 21, 21, 17, 20, 24, 17, 17, 17, 17, 17, 17, 17, 17, 17], rfl⟩, [(0x22220000, 21, 20), (0x30300000, 21, 17), (0x33000000, 25, 17)],
  (0x8074221c0a06430150c074281d08874201c0806420150c070281c0c06422190a0542215, 16), 0xefbcdf73becf, 0x182824124205,
  ⟨1, 1, 2, 1, 1, 3, 1,
  #[0x2],
  #[0x82e],
  #[0x0]⟩⟩
def p53Fact : Fact := (p53.mask, p53.bank, p53.fuel+1, p53.goal)
def p53Cuts : List Fact := []
theorem p53Known : Known p53Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p53Block0 : treeBlock 0 1 (p53.check p53Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p53All : treeBlock 0 1 (p53.check p53Cuts) = true := p53Block0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p53Lower : Lower p53.mask p53.bank p53.goal (p53.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p53 p53Cuts p53Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p53All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def p54 : Problem := ⟨0xcccc, 0xc880, [0x8888, 0xc0c0, 0xcc00], 3,
  some ⟨[7, 11, 14, 7, 7, 7, 7, 7, 7, 7, 7, 7, 3, 6, 10, 3, 3, 3, 3, 3, 3, 3, 3, 3], rfl⟩, [(0x8888, 7, 6), (0xc0c0, 7, 3), (0xcc00, 11, 3)],
  (0x103c060e0302c14070503c0c0f0183c040e0102c0407050380c0e0502c060b0301c0607, 16), 0xefbcdf73becf, 0x182824124205,
  ⟨1, 1, 2, 1, 1, 3, 1,
  #[0x2],
  #[0x8ee],
  #[0x0]⟩⟩
def p54Fact : Fact := (p54.mask, p54.bank, p54.fuel+1, p54.goal)
def p54Cuts : List Fact := []
theorem p54Known : Known p54Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p54Block0 : treeBlock 0 1 (p54.check p54Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p54All : treeBlock 0 1 (p54.check p54Cuts) = true := p54Block0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p54Lower : Lower p54.mask p54.bank p54.goal (p54.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p54 p54Cuts p54Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p54All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def p55 : Problem := ⟨0xf000f0, 0xe00080, [0xa000a0, 0xc000c0, 0xf00000], 3,
  some ⟨[7, 21, 22, 7, 7, 7, 7, 7, 7, 7, 7, 7, 5, 6, 20, 5, 5, 5, 5, 5, 5, 5, 5, 5], rfl⟩, [(0xa000a0, 7, 6), (0xc000c0, 7, 5), (0xf00000, 21, 5)],
  (0x205c0a160305428070a05c0c170285c08160205408070a0580c160a0540a150301c0a07, 16), 0xefbcdf73becf, 0x182824124205,
  ⟨1, 1, 2, 1, 1, 3, 1,
  #[0x1],
  #[0xbde],
  #[0x0]⟩⟩
def p55Fact : Fact := (p55.mask, p55.bank, p55.fuel+1, p55.goal)
def p55Cuts : List Fact := []
theorem p55Known : Known p55Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p55Block0 : treeBlock 0 1 (p55.check p55Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p55All : treeBlock 0 1 (p55.check p55Cuts) = true := p55Block0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p55Lower : Lower p55.mask p55.bank p55.goal (p55.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p55 p55Cuts p55Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p55All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def p56 : Problem := ⟨0xf0000000f0, 0xe000000080, [0xa0000000a0, 0xc0000000c0, 0xf000000000], 3,
  some ⟨[7, 37, 38, 7, 7, 7, 7, 7, 7, 7, 7, 7, 5, 6, 36, 5, 5, 5, 5, 5, 5, 5, 5, 5], rfl⟩, [(0xa0000000a0, 7, 6), (0xc0000000c0, 7, 5), (0xf000000000, 37, 5)],
  (0x209c0a260309448071209c0c270289c0826020940807120980c26120940a250301c0a07, 16), 0xefbcdf73becf, 0x182824124205,
  ⟨1, 1, 2, 1, 1, 3, 1,
  #[0x2],
  #[0x50e],
  #[0x0]⟩⟩
def p56Fact : Fact := (p56.mask, p56.bank, p56.fuel+1, p56.goal)
def p56Cuts : List Fact := []
theorem p56Known : Known p56Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p56Block0 : treeBlock 0 1 (p56.check p56Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p56All : treeBlock 0 1 (p56.check p56Cuts) = true := p56Block0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p56Lower : Lower p56.mask p56.bank p56.goal (p56.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p56 p56Cuts p56Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p56All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def p57 : Problem := ⟨0xf0f0, 0xe080, [0xa0a0, 0xc0c0, 0xf000], 3,
  some ⟨[7, 13, 14, 7, 7, 7, 7, 7, 7, 7, 7, 7, 5, 6, 12, 5, 5, 5, 5, 5, 5, 5, 5, 5], rfl⟩, [(0xa0a0, 7, 6), (0xc0c0, 7, 5), (0xf000, 13, 5)],
  (0x203c0a0e0303418070603c0c0f0283c080e020340807060380c0e060340a0d0301c0a07, 16), 0xefbcdf73becf, 0x182824124205,
  ⟨1, 1, 2, 1, 1, 3, 1,
  #[0x1],
  #[0x73e],
  #[0x0]⟩⟩
def p57Fact : Fact := (p57.mask, p57.bank, p57.fuel+1, p57.goal)
def p57Cuts : List Fact := []
theorem p57Known : Known p57Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p57Block0 : treeBlock 0 1 (p57.check p57Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p57All : treeBlock 0 1 (p57.check p57Cuts) = true := p57Block0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p57Lower : Lower p57.mask p57.bank p57.goal (p57.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p57 p57Cuts p57Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p57All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def p27 : Problem := ⟨0x2222222222222222, 0x2222222022202200, [0x2020202020202020, 0x2200220022002200, 0x2222000022220000, 0x2222222200000000], 4,
  some ⟨[9, 21, 37, 49, 9, 9, 9, 9, 9, 9, 9, 9, 5, 17, 33, 5, 5, 5, 5, 5, 5, 5, 5, 5], rfl⟩, [(0x2020202020202020, 21, 17), (0x2200220022002200, 9, 1), (0x2222000022220000, 21, 5), (0x2222222200000000, 37, 5)],
  (0x108e42239108d42235028d40231108b40a2d008a40225088740a1d008640215008344209088240a09108c42231108a44225028942219088540a15028340209, 28), 0xffc03e0fc3c31cc3bbc933b7606e, 0xa2012c0502091800000000910426,
  ⟨0, 0, 1, 1, 1, 1, 1,
  #[],
  #[],
  #[]⟩⟩
def p27Fact : Fact := (p27.mask, p27.bank, p27.fuel+1, p27.goal)
def p27Cuts : List Fact := [p48Fact]
theorem p27Known : Known p27Cuts := (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) p48Lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p27All : treeBlock 0 0 (p27.check p27Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p27Lower : Lower p27.mask p27.bank p27.goal (p27.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p27 p27Cuts p27Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p27All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def p28 : Problem := ⟨0xffff, 0xea80, [0xaaaa, 0xcccc, 0xf0f0, 0xff00], 4,
  some ⟨[7, 9, 14, 7, 7, 7, 7, 7, 7, 7, 7, 7, 3, 5, 6, 10, 12, 3, 3, 3, 3, 3, 3, 3], rfl⟩, [(0xaaaa, 7, 6), (0xcccc, 7, 5), (0xf0f0, 7, 3), (0xff00, 9, 1)],
  (0x2038040e04034080d00834100b0102c020b0002408070101c020706024140902824060906038140e03038180d02834140b0182c1009008240c070281c0607, 28), 0xff8fff8f870f87c770e673fff1ff, 0x240cd50904ab86422566509130ab,
  ⟨0, 0, 1, 1, 1, 1, 1,
  #[],
  #[],
  #[]⟩⟩
def p28Fact : Fact := (p28.mask, p28.bank, p28.fuel+1, p28.goal)
def p28Cuts : List Fact := [p54Fact, p57Fact]
theorem p28Known : Known p28Cuts := (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) p57Lower) p54Lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p28All : treeBlock 0 0 (p28.check p28Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p28Lower : Lower p28.mask p28.bank p28.goal (p28.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p28 p28Cuts p28Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p28All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def p29 : Problem := ⟨0x3030303030303030, 0x3020202030202000, [0x2020202020202020, 0x3000300030003000, 0x3030000030300000, 0x3030303000000000], 4,
  some ⟨[13, 21, 28, 37, 13, 13, 13, 13, 13, 13, 13, 13, 5, 44, 52, 5, 5, 5, 5, 5, 5, 5, 5, 5], rfl⟩, [(0x2020202020202020, 13, 12), (0x3000300030003000, 13, 5), (0x3030000030300000, 21, 5), (0x3030303000000000, 37, 5)],
  (0x120b4182d028b408250a074181d02874081c02054080d1a09458251a070581c1a054580d1a0f0583c1a0d4582d120940a250a070181c0a0540a15060340a0d, 28), 0xf030fc00f8ee3cef4dd33fef33cf, 0x803ff80082aa2844155122200045,
  ⟨0, 0, 1, 1, 1, 1, 1,
  #[],
  #[],
  #[]⟩⟩
def p29Fact : Fact := (p29.mask, p29.bank, p29.fuel+1, p29.goal)
def p29Cuts : List Fact := [p49Fact]
theorem p29Known : Known p29Cuts := (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) p49Lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p29All : treeBlock 0 0 (p29.check p29Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p29Lower : Lower p29.mask p29.bank p29.goal (p29.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p29 p29Cuts p29Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p29All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def p30 : Problem := ⟨0x33003300330033, 0x22002000200000, [0x22002200220022, 0x30003000300030, 0x33000000330000, 0x33003300000000], 4,
  some ⟨[21, 37, 49, 21, 21, 21, 21, 21, 21, 21, 21, 21, 5, 17, 33, 52, 5, 5, 5, 5, 5, 5, 5, 5], rfl⟩, [(0x22002200220022, 21, 20), (0x30003000300030, 21, 17), (0x33000000330000, 21, 5), (0x33003300000000, 37, 5)],
  (0x180d44835108d42835088d40a35100c42031008c440250209402250805408150085468311a09468151a0d46031108c42231120944225028942815088540a15, 28), 0xfff1bf8ff8f7c7fc7ee3ffffffff, 0xe241fb09909f465425e2d2c920db,
  ⟨0, 0, 1, 1, 1, 1, 1,
  #[],
  #[],
  #[]⟩⟩
def p30Fact : Fact := (p30.mask, p30.bank, p30.fuel+1, p30.goal)
def p30Cuts : List Fact := [p48Fact]
theorem p30Known : Known p30Cuts := (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) p48Lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p30All : treeBlock 0 0 (p30.check p30Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p30Lower : Lower p30.mask p30.bank p30.goal (p30.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p30 p30Cuts p30Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p30All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def p31 : Problem := ⟨0x5050505050505050, 0x5040404050404000, [0x4040404040404040, 0x5000500050005000, 0x5050000050500000, 0x5050505000000000], 4,
  some ⟨[14, 22, 28, 38, 14, 14, 14, 14, 14, 14, 14, 14, 6, 44, 52, 6, 6, 6, 6, 6, 6, 6, 6, 6], rfl⟩, [(0x4040404040404040, 14, 12), (0x5000500050005000, 14, 6), (0x5050000050500000, 22, 6), (0x5050505000000000, 38, 6)],
  (0x120b8182e030b808260a078181e03078081c02058080e1a09858261a070581c1a058580e1a0f0583c1a0d8582e120980c260a070181c0a0580c16060380c0e, 28), 0xf030fc00f8ee3cef4dd33fef33cf, 0x803ff80082aa2844155122200045,
  ⟨0, 0, 1, 1, 1, 1, 1,
  #[],
  #[],
  #[]⟩⟩
def p31Fact : Fact := (p31.mask, p31.bank, p31.fuel+1, p31.goal)
def p31Cuts : List Fact := [p52Fact]
theorem p31Known : Known p31Cuts := (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) p52Lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p31All : treeBlock 0 0 (p31.check p31Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p31Lower : Lower p31.mask p31.bank p31.goal (p31.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p31 p31Cuts p31Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p31All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def p32 : Problem := ⟨0x55005500550055, 0x44004000400000, [0x44004400440044, 0x50005000500050, 0x55000000550000, 0x55005500000000], 4,
  some ⟨[22, 38, 50, 22, 22, 22, 22, 22, 22, 22, 22, 22, 6, 18, 34, 52, 6, 6, 6, 6, 6, 6, 6, 6], rfl⟩, [(0x44004400440044, 22, 20), (0x50005000500050, 22, 18), (0x55000000550000, 22, 6), (0x55005500000000, 38, 6)],
  (0x180d84836110d82836090d80c36100c82032010c840260209804260805808160105868321a09868161a0d86032110c82432120984426030982816090580c16, 28), 0xfff1bf8ff8f7c7fc7ee3ffffffff, 0xe241fb09909f465425e2d2c920db,
  ⟨0, 0, 1, 1, 1, 1, 1,
  #[],
  #[],
  #[]⟩⟩
def p32Fact : Fact := (p32.mask, p32.bank, p32.fuel+1, p32.goal)
def p32Cuts : List Fact := [p50Fact]
theorem p32Known : Known p32Cuts := (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) p50Lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p32All : treeBlock 0 0 (p32.check p32Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p32Lower : Lower p32.mask p32.bank p32.goal (p32.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p32 p32Cuts p32Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p32All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def p33 : Problem := ⟨0x3333000033330000, 0x3222000032200000, [0x2222000022220000, 0x3030000030300000, 0x3300000033000000, 0x3333000000000000], 4,
  some ⟨[21, 25, 28, 49, 21, 21, 21, 21, 21, 21, 21, 21, 17, 52, 56, 17, 17, 17, 17, 17, 17, 17, 17, 17], rfl⟩, [(0x2222000022220000, 21, 20), (0x3030000030300000, 21, 17), (0x3300000033000000, 25, 17), (0x3333000000000000, 49, 17)],
  (0x180d42835088d420310c074281d08874201c0806420151c0c468311c070681c1c06468151c0f0683c1c0e46835180c422310c070281c0c06422190a0542215, 28), 0xf030fc00f8ee3cef4dd33fef33cf, 0x803ff80082aa2844155122200045,
  ⟨0, 0, 1, 1, 1, 1, 1,
  #[],
  #[],
  #[]⟩⟩
def p33Fact : Fact := (p33.mask, p33.bank, p33.fuel+1, p33.goal)
def p33Cuts : List Fact := [p53Fact]
theorem p33Known : Known p33Cuts := (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) p53Lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p33All : treeBlock 0 0 (p33.check p33Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p33Lower : Lower p33.mask p33.bank p33.goal (p33.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p33 p33Cuts p33Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p33All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def p34 : Problem := ⟨0xf0f0f0f0, 0xf0e0e080, [0xa0a0a0a0, 0xc0c0c0c0, 0xf000f000, 0xf0f00000], 4,
  some ⟨[7, 13, 14, 21, 22, 28, 7, 7, 7, 7, 7, 7, 5, 6, 12, 20, 5, 5, 5, 5, 5, 5, 5, 5], rfl⟩, [(0xa0a0a0a0, 7, 6), (0xc0c0c0c0, 7, 5), (0xf000f000, 13, 5), (0xf0f00000, 21, 5)],
  (0x3078281d060740a1d0207028170305c0a170205808150603c0c0f0283c080e0203408070a070181c0a0580c160a0540a15060380c0e060340a0d0301c0a07, 28), 0xffc0fc0f83ec3c87bd333777b0cf, 0x4400a80202042882101121108045,
  ⟨0, 0, 1, 1, 1, 1, 1,
  #[],
  #[],
  #[]⟩⟩
def p34Fact : Fact := (p34.mask, p34.bank, p34.fuel+1, p34.goal)
def p34Cuts : List Fact := [p49Fact, p52Fact, p55Fact, p57Fact]
theorem p34Known : Known p34Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) p57Lower) p55Lower) p52Lower) p49Lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p34All : treeBlock 0 0 (p34.check p34Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p34Lower : Lower p34.mask p34.bank p34.goal (p34.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p34 p34Cuts p34Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p34All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def p35 : Problem := ⟨0xf000f000f000f0, 0xe000e000e00080, [0xa000a000a000a0, 0xc000c000c000c0, 0xf0000000f00000, 0xf000f000000000], 4,
  some ⟨[7, 21, 22, 37, 38, 7, 7, 7, 7, 7, 7, 7, 5, 6, 52, 5, 5, 5, 5, 5, 5, 5, 5, 5], rfl⟩, [(0xa000a000a000a0, 7, 6), (0xc000c000c000c0, 7, 5), (0xf0000000f00000, 21, 5), (0xf000f000000000, 37, 5)],
  (0x28d448270309c0a270209808250a05c0c170285c08160205408071a09868251a05868151a0d86835120980c26120940a250a0580c160a0540a150301c0a07, 28), 0xfc0cfc083e3c3c7bdab33f7b54cf, 0x400fe80020fc2821001129080045,
  ⟨0, 0, 1, 1, 1, 1, 1,
  #[],
  #[],
  #[]⟩⟩
def p35Fact : Fact := (p35.mask, p35.bank, p35.fuel+1, p35.goal)
def p35Cuts : List Fact := [p55Fact, p56Fact]
theorem p35Known : Known p35Cuts := (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) p56Lower) p55Lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p35All : treeBlock 0 0 (p35.check p35Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p35Lower : Lower p35.mask p35.bank p35.goal (p35.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p35 p35Cuts p35Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p35All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def p36 : Problem := ⟨0xff000000ff, 0xe000000080, [0xaa000000aa, 0xcc000000cc, 0xf0000000f0, 0xff00000000], 4,
  some ⟨[7, 37, 38, 7, 7, 7, 7, 7, 7, 7, 7, 7, 5, 6, 35, 36, 5, 5, 5, 5, 5, 5, 5, 5], rfl⟩, [(0xaa000000aa, 7, 6), (0xcc000000cc, 7, 5), (0xf0000000f0, 7, 3), (0xff00000000, 37, 5)],
  (0x1209c44271089c0c270289c06271009808260109840250209402250201c04070081c46261189446071189c4826110980c26120944225028940c070281c0607, 28), 0xfff1bf8fffffffff8f7c7fc7ee3f, 0xe241fb0992816e5485ec52c13e1b,
  ⟨0, 0, 1, 1, 1, 1, 1,
  #[],
  #[],
  #[]⟩⟩
def p36Fact : Fact := (p36.mask, p36.bank, p36.fuel+1, p36.goal)
def p36Cuts : List Fact := [p56Fact]
theorem p36Known : Known p36Cuts := (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) p56Lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p36All : treeBlock 0 0 (p36.check p36Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p36Lower : Lower p36.mask p36.bank p36.goal (p36.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p36 p36Cuts p36Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p36All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def p37 : Problem := ⟨0xff00ff, 0xe00080, [0xaa00aa, 0xcc00cc, 0xf000f0, 0xff0000], 4,
  some ⟨[7, 21, 22, 7, 7, 7, 7, 7, 7, 7, 7, 7, 5, 6, 19, 20, 5, 5, 5, 5, 5, 5, 5, 5], rfl⟩, [(0xaa00aa, 7, 6), (0xcc00cc, 7, 5), (0xf000f0, 7, 3), (0xff0000, 21, 5)],
  (0xa05c24170885c0c170285c06170805808160105820150205402150201c04070081c26160985426070985c2816090580c160a0542215028540c070281c0607, 28), 0xfff1bf8fffffffff8f7c7fc7ee3f, 0xe241fb0992816e5485ec52c13e1b,
  ⟨0, 0, 1, 1, 1, 1, 1,
  #[],
  #[],
  #[]⟩⟩
def p37Fact : Fact := (p37.mask, p37.bank, p37.fuel+1, p37.goal)
def p37Cuts : List Fact := [p55Fact]
theorem p37Known : Known p37Cuts := (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) p55Lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p37All : treeBlock 0 0 (p37.check p37Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p37Lower : Lower p37.mask p37.bank p37.goal (p37.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p37 p37Cuts p37Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p37All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def p38 : Problem := ⟨0x33333333, 0x32202200, [0x22222222, 0x30303030, 0x33003300, 0x33330000], 4,
  some ⟨[9, 21, 28, 9, 9, 9, 9, 9, 9, 9, 9, 9, 5, 12, 17, 20, 24, 5, 5, 5, 5, 5, 5, 5], rfl⟩, [(0x22222222, 9, 8), (0x30303030, 21, 17), (0x33003300, 9, 1), (0x33330000, 21, 5)],
  (0x4070081c08064101900864201502054021504034080d0083400090c0242209060240a090c070281c060703019088642815088540a15060340a0d040240209, 28), 0xff00ff0f8fff8fc7e0e7c3fff1ff, 0x240cde0908ab0a424365c09250b5,
  ⟨0, 0, 1, 1, 1, 1, 1,
  #[],
  #[],
  #[]⟩⟩
def p38Fact : Fact := (p38.mask, p38.bank, p38.fuel+1, p38.goal)
def p38Cuts : List Fact := [p49Fact, p53Fact]
theorem p38Known : Known p38Cuts := (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) p53Lower) p49Lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p38All : treeBlock 0 0 (p38.check p38Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p38Lower : Lower p38.mask p38.bank p38.goal (p38.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p38 p38Cuts p38Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p38All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def p39 : Problem := ⟨0x55555555, 0x50404000, [0x44444444, 0x50505050, 0x55005500, 0x55550000], 4,
  some ⟨[14, 22, 28, 14, 14, 14, 14, 14, 14, 14, 14, 14, 6, 12, 20, 26, 6, 6, 6, 6, 6, 6, 6, 6], rfl⟩, [(0x44444444, 14, 12), (0x50505050, 14, 10), (0x55005500, 14, 6), (0x55550000, 22, 6)],
  (0xc078281e09078181e050780c1e08070101c02070201602058041604038080e01038341c0d058340e0d078301c0a070181c0a058241603058180e050380c0e, 28), 0xfff1bf8ff8f7c7ffffffffc7ee3f, 0xe241fb09909f4654a40ed2c13e1b,
  ⟨0, 0, 1, 1, 1, 1, 1,
  #[],
  #[],
  #[]⟩⟩
def p39Fact : Fact := (p39.mask, p39.bank, p39.fuel+1, p39.goal)
def p39Cuts : List Fact := [p52Fact]
theorem p39Known : Known p39Cuts := (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) p52Lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p39All : treeBlock 0 0 (p39.check p39Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p39Lower : Lower p39.mask p39.bank p39.goal (p39.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p39 p39Cuts p39Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p39All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def p40 : Problem := ⟨0x555500005555, 0x444000004000, [0x444400004444, 0x505000005050, 0x550000005500, 0x555500000000], 4,
  some ⟨[14, 38, 42, 14, 14, 14, 14, 14, 14, 14, 14, 14, 6, 10, 34, 44, 6, 6, 6, 6, 6, 6, 6, 6], rfl⟩, [(0x444400004444, 14, 12), (0x505000005050, 14, 10), (0x550000005500, 14, 6), (0x555500000000, 38, 6)],
  (0x140b8482e110b8182e050b80c2e100a8102a010a8402602098042604038080e01038582a16098580e160b8502a110a8142a12098442603098180e050380c0e, 28), 0xfff1bf8ff8f7c7fc7ee3ffffffff, 0xe241fb09909f465425e2d2c920db,
  ⟨0, 0, 1, 1, 1, 1, 1,
  #[],
  #[],
  #[]⟩⟩
def p40Fact : Fact := (p40.mask, p40.bank, p40.fuel+1, p40.goal)
def p40Cuts : List Fact := [p51Fact]
theorem p40Known : Known p40Cuts := (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) p51Lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p40All : treeBlock 0 0 (p40.check p40Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p40Lower : Lower p40.mask p40.bank p40.goal (p40.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p40 p40Cuts p40Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p40All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def p41 : Problem := ⟨0x4444444444444444, 0x4444444040404000, [0x4040404040404040, 0x4400440044004400, 0x4444000044440000, 0x4444444400000000], 4,
  some ⟨[14, 22, 38, 42, 50, 14, 14, 14, 14, 14, 14, 14, 6, 26, 34, 6, 6, 6, 6, 6, 6, 6, 6, 6], rfl⟩, [(0x4040404040404040, 14, 10), (0x4400440044004400, 14, 6), (0x4444000044440000, 22, 6), (0x4444444400000000, 38, 6)],
  (0x30d80432110b8142e030b8042a01098241e050780c1e01058040e0d0c8342a0d058340e0d0e84432090c8442a050a8442603098341e090580c16050380c0e, 28), 0xfe0cfe0c1eae1c3dd5993bbf307f, 0x2000540010fa18108f8928840025,
  ⟨0, 0, 1, 1, 1, 1, 1,
  #[],
  #[],
  #[]⟩⟩
def p41Fact : Fact := (p41.mask, p41.bank, p41.fuel+1, p41.goal)
def p41Cuts : List Fact := [p50Fact, p51Fact]
theorem p41Known : Known p41Cuts := (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) p51Lower) p50Lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p41All : treeBlock 0 0 (p41.check p41Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p41Lower : Lower p41.mask p41.bank p41.goal (p41.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p41 p41Cuts p41Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p41All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def p42 : Problem := ⟨0xf0f00000f0f0, 0xe0e00000e080, [0xa0a00000a0a0, 0xc0c00000c0c0, 0xf0000000f000, 0xf0f000000000], 4,
  some ⟨[7, 13, 14, 37, 38, 7, 7, 7, 7, 7, 7, 7, 5, 6, 44, 5, 5, 5, 5, 5, 5, 5, 5, 5], rfl⟩, [(0xa0a00000a0a0, 7, 6), (0xc0c00000c0c0, 7, 5), (0xf0000000f000, 13, 5), (0xf0f000000000, 37, 5)],
  (0x28b448270309c0a270209808250603c0c0f0283c080e02034080716098582516038580d160b8582d120980c26120940a25060380c0e060340a0d0301c0a07, 28), 0xfc0cfc083e3c3c7bdab33f7b54cf, 0x400fe80020fc2821001129080045,
  ⟨0, 0, 1, 1, 1, 1, 1,
  #[],
  #[],
  #[]⟩⟩
def p42Fact : Fact := (p42.mask, p42.bank, p42.fuel+1, p42.goal)
def p42Cuts : List Fact := [p56Fact, p57Fact]
theorem p42Known : Known p42Cuts := (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) p57Lower) p56Lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p42All : treeBlock 0 0 (p42.check p42Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p42Lower : Lower p42.mask p42.bank p42.goal (p42.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p42 p42Cuts p42Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p42All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def p43 : Problem := ⟨0xcccc0000cccc, 0xccc00000c880, [0x888800008888, 0xc0c00000c0c0, 0xcc000000cc00, 0xcccc00000000], 4,
  some ⟨[7, 11, 14, 38, 42, 7, 7, 7, 7, 7, 7, 7, 6, 10, 35, 6, 6, 6, 6, 6, 6, 6, 6, 6], rfl⟩, [(0x888800008888, 7, 6), (0xc0c00000c0c0, 7, 3), (0xcc000000cc00, 11, 3), (0xcccc00000000, 38, 6)],
  (0x18ac042a1109c0c270189c04260503c0c0f0183c040e0102c0407118a846261182c4607118ac442a050a84627110980c26050380c0e0502c060b0301c0607, 28), 0xfc0cfc0c3eae3c3fd51f3bbb390f, 0x200fd8002002281100052888f905,
  ⟨0, 0, 1, 1, 1, 1, 1,
  #[],
  #[],
  #[]⟩⟩
def p43Fact : Fact := (p43.mask, p43.bank, p43.fuel+1, p43.goal)
def p43Cuts : List Fact := [p51Fact, p54Fact]
theorem p43Known : Known p43Cuts := (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) p54Lower) p51Lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p43All : treeBlock 0 0 (p43.check p43Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p43Lower : Lower p43.mask p43.bank p43.goal (p43.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p43 p43Cuts p43Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p43All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def p44 : Problem := ⟨0xffff0000, 0xfae00000, [0xaaaa0000, 0xcccc0000, 0xf0f00000, 0xff000000], 4,
  some ⟨[21, 22, 25, 28, 21, 21, 21, 21, 21, 21, 21, 21, 19, 20, 26, 19, 19, 19, 19, 19, 19, 19, 19, 19], rfl⟩, [(0xaaaa0000, 21, 20), (0xcccc0000, 22, 20), (0xf0f00000, 21, 17), (0xff000000, 25, 17)],
  (0x8070301b0906c221b0806428170905c22170805820150d07034190986434160985826150d078301c0a070341b0986c30190886426170a05824160a0542215, 28), 0xf838fe087e7e1f778699c7f591f3, 0x4034d40040020a223f994110b0b1,
  ⟨0, 0, 1, 1, 1, 1, 1,
  #[],
  #[],
  #[]⟩⟩
def p44Fact : Fact := (p44.mask, p44.bank, p44.fuel+1, p44.goal)
def p44Cuts : List Fact := [p53Fact]
theorem p44Known : Known p44Cuts := (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) p53Lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p44All : treeBlock 0 0 (p44.check p44Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p44Lower : Lower p44.mask p44.bank p44.goal (p44.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p44 p44Cuts p44Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p44All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def p45 : Problem := ⟨0xcccccccc, 0xc8c0c880, [0x88888888, 0xc0c0c0c0, 0xcc00cc00, 0xcccc0000], 4,
  some ⟨[7, 11, 14, 22, 7, 7, 7, 7, 7, 7, 7, 7, 6, 19, 26, 6, 6, 6, 6, 6, 6, 6, 6, 6], rfl⟩, [(0x88888888, 7, 6), (0xc0c0c0c0, 7, 3), (0xcc00cc00, 11, 3), (0xcccc0000, 22, 6)],
  (0x905c0c170185c04160503c0c0f0183c040e0102c04070d05826160d038340b0982c26070d078341b0986c2617090580c16050380c0e0502c060b0301c0607, 28), 0xf030fc00f8ee3cff799f3eec770f, 0x803ff80082cc2844000522213305,
  ⟨0, 0, 1, 1, 1, 1, 1,
  #[],
  #[],
  #[]⟩⟩
def p45Fact : Fact := (p45.mask, p45.bank, p45.fuel+1, p45.goal)
def p45Cuts : List Fact := [p54Fact]
theorem p45Known : Known p45Cuts := (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) p54Lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p45All : treeBlock 0 0 (p45.check p45Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p45Lower : Lower p45.mask p45.bank p45.goal (p45.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p45 p45Cuts p45Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p45All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def p46 : Problem := ⟨0xaa00aa00aa00aa, 0xaa00a000a00080, [0x88008800880088, 0xa000a000a000a0, 0xaa000000aa0000, 0xaa00aa00000000], 4,
  some ⟨[7, 21, 37, 49, 7, 7, 7, 7, 7, 7, 7, 7, 5, 19, 35, 5, 5, 5, 5, 5, 5, 5, 5, 5], rfl⟩, [(0x88008800880088, 7, 5), (0xa000a000a000a0, 7, 3), (0xaa000000aa0000, 21, 5), (0xaa00aa00000000, 37, 5)],
  (0x8c442270289c06270089422170285c0617008540207118c426311189426151181c2607118cc2633108c422311189c4225028942617088540a150281c0607, 28), 0xf838fe087b4f1c7fcf0ff7743c93, 0x402aac004155182200026113fc91,
  ⟨0, 0, 1, 1, 1, 1, 1,
  #[],
  #[],
  #[]⟩⟩
def p46Fact : Fact := (p46.mask, p46.bank, p46.fuel+1, p46.goal)
def p46Cuts : List Fact := [p48Fact]
theorem p46Known : Known p46Cuts := (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) p48Lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p46All : treeBlock 0 0 (p46.check p46Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p46Lower : Lower p46.mask p46.bank p46.goal (p46.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p46 p46Cuts p46Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p46All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def p47 : Problem := ⟨0xcc00cc00cc00cc, 0xcc00c000c00080, [0x88008800880088, 0xc000c000c000c0, 0xcc000000cc0000, 0xcc00cc00000000], 4,
  some ⟨[7, 22, 38, 50, 7, 7, 7, 7, 7, 7, 7, 7, 6, 19, 35, 6, 6, 6, 6, 6, 6, 6, 6, 6], rfl⟩, [(0x88008800880088, 7, 6), (0xc000c000c000c0, 7, 3), (0xcc000000cc0000, 22, 6), (0xcc00cc00000000, 38, 6)],
  (0x10c844270309c06270109824170305c0617010580407118c826321189826161181c2607118cc2633110c824321189c4426030982617090580c160301c0607, 28), 0xf838fe087b4f1c7fcf0ff7743c93, 0x402aac004155182200026113fc91,
  ⟨0, 0, 1, 1, 1, 1, 1,
  #[],
  #[],
  #[]⟩⟩
def p47Fact : Fact := (p47.mask, p47.bank, p47.fuel+1, p47.goal)
def p47Cuts : List Fact := [p50Fact]
theorem p47Known : Known p47Cuts := (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) p50Lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p47All : treeBlock 0 0 (p47.check p47Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p47Lower : Lower p47.mask p47.bank p47.goal (p47.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p47 p47Cuts p47Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p47All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def p17 : Problem := ⟨0x3333333300000000, 0x3222222000000000, [0x2222222200000000, 0x3030303000000000, 0x3300330000000000, 0x3333000000000000], 5,
  some ⟨[37, 41, 49, 60, 37, 37, 37, 37, 37, 37, 37, 37, 33, 44, 52, 56, 33, 33, 33, 33, 33, 33, 33, 33], rfl⟩, [(0x2222222200000000, 37, 36), (0x3030303000000000, 37, 33), (0x3300330000000000, 41, 33), (0x3333000000000000, 49, 33)],
  (0x108e46035120d44235100c4502d120b4422d100a440251c0c468311c0a458291a09458251c0f0683c160f070391a0d46031108c4582d140a44229120944225, 28), 0xf830fe0878cf1c7743e93ffff1ff, 0x403adc0042db1822176929100025,
  ⟨5, 1, 2, 3, 3, 12, 1,
  #[0x14],
  #[0xfc9620631022318a2768078488042],
  #[0x0]⟩⟩
def p17Fact : Fact := (p17.mask, p17.bank, p17.fuel+1, p17.goal)
def p17Cuts : List Fact := []
theorem p17Known : Known p17Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p17Block0 : treeBlock 0 5 (p17.check p17Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p17All : treeBlock 0 5 (p17.check p17Cuts) = true := p17Block0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p17Lower : Lower p17.mask p17.bank p17.goal (p17.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p17 p17Cuts p17Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p17All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def p19 : Problem := ⟨0x5555555500000000, 0x5444444000000000, [0x4444444400000000, 0x5050505000000000, 0x5500550000000000, 0x5555000000000000], 5,
  some ⟨[38, 42, 50, 60, 38, 38, 38, 38, 38, 38, 38, 38, 34, 44, 52, 56, 34, 34, 34, 34, 34, 34, 34, 34], rfl⟩, [(0x4444444400000000, 38, 36), (0x5050505000000000, 38, 34), (0x5500550000000000, 42, 34), (0x5555000000000000, 50, 34)],
  (0x110e86036120d84436100c8502e120b8442e100a840261c0c868321c0a8582a1a09858261c0f0683c160f0703a1a0d86032110c8582e140a8442a120984426, 28), 0xf830fe0878cf1c7743e93ffff1ff, 0x403adc0042db1822176929100025,
  ⟨5, 1, 2, 3, 3, 12, 1,
  #[0x14],
  #[0x7c00426db1025218a253007840c962],
  #[0x0]⟩⟩
def p19Fact : Fact := (p19.mask, p19.bank, p19.fuel+1, p19.goal)
def p19Cuts : List Fact := []
theorem p19Known : Known p19Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p19Block0 : treeBlock 0 5 (p19.check p19Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p19All : treeBlock 0 5 (p19.check p19Cuts) = true := p19Block0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p19Lower : Lower p19.mask p19.bank p19.goal (p19.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p19 p19Cuts p19Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p19All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def p18 : Problem := ⟨0xffff0000ffff0000, 0xfeee0000fae00000, [0xaaaa0000aaaa0000, 0xcccc0000cccc0000, 0xf0f00000f0f00000, 0xff000000ff000000, 0xffff000000000000], 5,
  some ⟨[21, 22, 25, 28, 49, 50, 21, 21, 21, 21, 21, 21, 19, 26, 52, 56, 19, 19, 19, 19, 19, 19, 19, 19], rfl⟩, [(0xaaaa0000aaaa0000, 21, 20), (0xcccc0000cccc0000, 22, 20), (0xf0f00000f0f00000, 21, 17), (0xff000000ff000000, 25, 17), (0xffff000000000000, 49, 17)],
  (0xd05826161a05426151c0f0683c1c0e8343a1c0e468361a0d42633180c82432180c422310d078301c0a070341b0986c30190886426170a05824160a0542215, 28), 0xfff0000f80fe0fc60e1fc35c99c30b31f3, 0x2eea0008b80d40246020ad11499450110b1,
  ⟨0, 0, 1, 1, 1, 1, 1,
  #[],
  #[],
  #[]⟩⟩
def p18Fact : Fact := (p18.mask, p18.bank, p18.fuel+1, p18.goal)
def p18Cuts : List Fact := [p33Fact, p44Fact, p53Fact]
theorem p18Known : Known p18Cuts := (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) p53Lower) p44Lower) p33Lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p18All : treeBlock 0 0 (p18.check p18Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p18Lower : Lower p18.mask p18.bank p18.goal (p18.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p18 p18Cuts p18Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p18All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def p20 : Problem := ⟨0xf0f0f0f0f0f0f0f0, 0xf0e0e0e0f0e0e080, [0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000], 5,
  some ⟨[7, 13, 14, 21, 22, 28, 37, 38, 7, 7, 7, 7, 5, 6, 44, 52, 5, 5, 5, 5, 5, 5, 5, 5], rfl⟩, [(0xa0a0a0a0a0a0a0a0, 7, 6), (0xc0c0c0c0c0c0c0c0, 7, 5), (0xf000f000f000f000, 13, 5), (0xf0f00000f0f00000, 21, 5), (0xf0f0f0f000000000, 37, 5)],
  (0x1a070581c1a058681516038580d1a0f0583c1a0d86835160b8582d120980c26120940a250a070181c0a0580c160a0540a15060380c0e060340a0d0301c0a07, 28), 0x3ff000f3c0fc0cf30c3c28ac33314530cf, 0xfffa000b2c0a804d3042800041120001045,
  ⟨0, 0, 1, 1, 1, 1, 1,
  #[],
  #[],
  #[]⟩⟩
def p20Fact : Fact := (p20.mask, p20.bank, p20.fuel+1, p20.goal)
def p20Cuts : List Fact := [p29Fact, p31Fact, p34Fact, p35Fact, p42Fact, p49Fact, p52Fact, p55Fact, p56Fact, p57Fact]
theorem p20Known : Known p20Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) p57Lower) p56Lower) p55Lower) p52Lower) p49Lower) p42Lower) p35Lower) p34Lower) p31Lower) p29Lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p20All : treeBlock 0 0 (p20.check p20Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p20Lower : Lower p20.mask p20.bank p20.goal (p20.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p20 p20Cuts p20Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p20All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def p21 : Problem := ⟨0xcccccccccccccccc, 0xccccccc0c8c0c880, [0x8888888888888888, 0xc0c0c0c0c0c0c0c0, 0xcc00cc00cc00cc00, 0xcccc0000cccc0000, 0xcccccccc00000000], 5,
  some ⟨[7, 11, 14, 22, 38, 42, 50, 7, 7, 7, 7, 7, 6, 19, 26, 35, 6, 6, 6, 6, 6, 6, 6, 6], rfl⟩, [(0x8888888888888888, 7, 6), (0xc0c0c0c0c0c0c0c0, 7, 3), (0xcc00cc00cc00cc00, 11, 3), (0xcccc0000cccc0000, 22, 6), (0xcccccccc00000000, 38, 6)],
  (0x1182c340b0982c46070981c343a118cc2633110c82432118ac442a050a84627110980c260d078341b0986c2617090580c16050380c0e0502c060b0301c0607, 28), 0x7ff00007c0fc0e438e3c18079f3fb2470f, 0x92b60006d40f804408c280001052bb24305,
  ⟨0, 0, 1, 1, 1, 1, 1,
  #[],
  #[],
  #[]⟩⟩
def p21Fact : Fact := (p21.mask, p21.bank, p21.fuel+1, p21.goal)
def p21Cuts : List Fact := [p41Fact, p43Fact, p45Fact, p47Fact, p50Fact, p51Fact, p54Fact]
theorem p21Known : Known p21Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) p54Lower) p51Lower) p50Lower) p47Lower) p45Lower) p43Lower) p41Lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p21All : treeBlock 0 0 (p21.check p21Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p21Lower : Lower p21.mask p21.bank p21.goal (p21.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p21 p21Cuts p21Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p21All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def p22 : Problem := ⟨0xaaaaaaaaaaaaaaaa, 0xaaaaaaa0aaa0aa80, [0x8888888888888888, 0xa0a0a0a0a0a0a0a0, 0xaa00aa00aa00aa00, 0xaaaa0000aaaa0000, 0xaaaaaaaa00000000], 5,
  some ⟨[7, 9, 21, 37, 49, 7, 7, 7, 7, 7, 7, 7, 5, 19, 35, 5, 5, 5, 5, 5, 5, 5, 5, 5], rfl⟩, [(0x8888888888888888, 7, 5), (0xa0a0a0a0a0a0a0a0, 7, 3), (0xaa00aa00aa00aa00, 9, 1), (0xaaaa0000aaaa0000, 21, 5), (0xaaaaaaaa00000000, 37, 5)],
  (0x9854460b0982c4209088240a090182446070981c4633098cc4231088c4462b108a44627108940a250986c22190985c2215028540a0d0182c02090281c0607, 28), 0x7fc0080783e07e0631c8181cf361e528b, 0x5157800a8a83c000000000400432e3e5289,
  ⟨0, 0, 1, 1, 1, 1, 1,
  #[],
  #[],
  #[]⟩⟩
def p22Fact : Fact := (p22.mask, p22.bank, p22.fuel+1, p22.goal)
def p22Cuts : List Fact := [p27Fact, p46Fact, p48Fact]
theorem p22Known : Known p22Cuts := (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) p48Lower) p46Lower) p27Lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p22All : treeBlock 0 0 (p22.check p22Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p22Lower : Lower p22.mask p22.bank p22.goal (p22.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p22 p22Cuts p22Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p22All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def p26 : Problem := ⟨0xf0f0f0f00f0f0f0f, 0xf0e0e0e00a000a00, [0xa0a0a0a00a0a0a0a, 0xc0c0c0c00c0c0c0c, 0xf000f0000f000f00, 0xf0f000000f0f0000, 0xf0f0f0f000000000], 5,
  some ⟨[9, 37, 38, 60, 9, 9, 9, 9, 9, 9, 9, 9, 19, 26, 44, 52, 19, 19, 19, 19, 19, 19, 19, 19], rfl⟩, [(0xa0a0a0a00a0a0a0a, 9, 8), (0xc0c0c0c00c0c0c0c, 38, 36), (0xf000f0000f000f00, 9, 1), (0xf0f000000f0f0000, 60, 44), (0xf0f0f0f000000000, 37, 1)],
  (0x1a09858261a09458250d06426190d02c260b0c02422090502406091a0f0583c1a0d86835160b8582d1209848250d06c261b0c06422190502c060b040240209, 28), 0xf00ff000c0f0f00ffccffc302acc3ff15ff, 0xf00ff00afcb0f05aa4caa0f300cc0550055,
  ⟨1, 1, 2, 1, 1, 5, 1,
  #[0x1],
  #[0x333e],
  #[0x0]⟩⟩
def p26Fact : Fact := (p26.mask, p26.bank, p26.fuel+1, p26.goal)
def p26Cuts : List Fact := []
theorem p26Known : Known p26Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p26Block0 : treeBlock 0 1 (p26.check p26Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p26All : treeBlock 0 1 (p26.check p26Cuts) = true := p26Block0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p26Lower : Lower p26.mask p26.bank p26.goal (p26.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p26 p26Cuts p26Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p26All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def p13 : Problem := ⟨0xffffffff00000000, 0xfeeeeee000000000, [0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf0f0f0f000000000, 0xff00ff0000000000, 0xffff000000000000], 6,
  some ⟨[37, 38, 41, 42, 49, 50, 60, 37, 37, 37, 37, 37, 35, 44, 52, 56, 35, 35, 35, 35, 35, 35, 35, 35], rfl⟩, [(0xaaaaaaaa00000000, 37, 36), (0xcccccccc00000000, 38, 36), (0xf0f0f0f000000000, 37, 33), (0xff00ff0000000000, 41, 33), (0xffff000000000000, 49, 33)],
  (0x1189868251609446251c0f0683c160f0703a1c0e468361a0d44633180c84432180c44231160b8582d118ac502a110a85029108a44627120984426120944225, 28), 0xfff0000f80fe0fe60c1f815cb9c70b3673, 0x4dea0002b80d406660c0a90142949011231,
  ⟨0, 0, 1, 1, 1, 1, 1,
  #[],
  #[],
  #[]⟩⟩
def p13Fact : Fact := (p13.mask, p13.bank, p13.fuel+1, p13.goal)
def p13Cuts : List Fact := [p17Fact, p19Fact]
theorem p13Known : Known p13Cuts := (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) p19Lower) p17Lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p13All : treeBlock 0 0 (p13.check p13Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p13Lower : Lower p13.mask p13.bank p13.goal (p13.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p13 p13Cuts p13Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p13All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def p14 : Problem := ⟨0x9999999999999999, 0x9888888098808880, [0x8888888888888888, 0x9090909090909090, 0x9900990099009900, 0x9999000099990000, 0x9999999900000000], 6,
  some ⟨[7, 11, 28, 51, 7, 7, 7, 7, 7, 7, 7, 7, 19, 35, 44, 52, 56, 19, 19, 19, 19, 19, 19, 19], rfl⟩, [(0x8888888888888888, 7, 4), (0x9090909090909090, 7, 3), (0x9900990099009900, 11, 3), (0x9999000099990000, 28, 12), (0x9999999900000000, 51, 19)],
  (0x186c28170185c180f0183c100b0201c701c1a070581c1182c260b1181c26071c0f0683c160f04633098cc462b1189c301c0a070181c0986c26170182c0607, 28), 0x3f80e1c3e7c9df397a7bcf8f5fe3c78f, 0x1ebd80419726c154285052c1830a83c78f,
  ⟨13, 1, 5, 5, 4, 12, 1,
  #[0x359c7],
  #[0xff33513698a09ef0e45212622c603114bc9868424c09560102fd62012ec960abf0e057cc6a24401f0],
  #[0x0]⟩⟩
def p14Fact : Fact := (p14.mask, p14.bank, p14.fuel+1, p14.goal)
def p14Cuts : List Fact := []
theorem p14Known : Known p14Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p14Block0 : treeBlock 0 13 (p14.check p14Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p14All : treeBlock 0 13 (p14.check p14Cuts) = true := p14Block0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p14Lower : Lower p14.mask p14.bank p14.goal (p14.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p14 p14Cuts p14Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p14All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def p15 : Problem := ⟨0xa5a5a5a5a5a5a5a5, 0xa4a4a4a0a0a0a080, [0x8484848484848484, 0xa0a0a0a0a0a0a0a0, 0xa500a500a500a500, 0xa5a50000a5a50000, 0xa5a5a5a500000000], 6,
  some ⟨[7, 13, 21, 37, 42, 50, 7, 7, 7, 7, 7, 7, 5, 26, 34, 56, 5, 5, 5, 5, 5, 5, 5, 5], rfl⟩, [(0x8484848484848484, 7, 5), (0xa0a0a0a0a0a0a0a0, 7, 2), (0xa500a500a500a500, 13, 5), (0xa5a50000a5a50000, 21, 5), (0xa5a5a5a500000000, 37, 5)],
  (0x289c40250d07c301d0287424170285c20150503c0a0f0403404071c0c834321c0a8342a1c0e8343a180c84432090c8502a110a8142a028940a15028340a07, 28), 0xc00fff83f0cf8438e3c72fff000fa6dfff1, 0x400ab60350fe8030afc508a4000f24955b0,
  ⟨13, 7, 5, 5, 4, 12, 1,
  #[0x173200],
  #[0x3162ab26e1c5a0407c06125963c629b12c9620b8c52c50c502cf62041d3145b8d882d18c50e29008b],
  #[0x0]⟩⟩
def p15Fact : Fact := (p15.mask, p15.bank, p15.fuel+1, p15.goal)
def p15Cuts : List Fact := []
theorem p15Known : Known p15Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p15Block0 : treeBlock 0 13 (p15.check p15Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p15All : treeBlock 0 13 (p15.check p15Cuts) = true := p15Block0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p15Lower : Lower p15.mask p15.bank p15.goal (p15.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p15 p15Cuts p15Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p15All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def p16 : Problem := ⟨0xf0f00f0ff0f00f0f, 0xf0e00e00f0e00a00, [0xa0a00a0aa0a00a0a, 0xc0c00c0cc0c00c0c, 0xf0000f00f0000f00, 0xf0f00000f0f00000, 0xf0f00f0f00000000], 6,
  some ⟨[9, 21, 22, 28, 42, 9, 9, 9, 9, 9, 9, 9, 10, 35, 40, 52, 10, 10, 10, 10, 10, 10, 10, 10], rfl⟩, [(0xa0a00a0aa0a00a0a, 9, 8), (0xc0c00c0cc0c00c0c, 22, 20), (0xf0000f00f0000f00, 9, 1), (0xf0f00000f0f00000, 21, 1), (0xf0f00f0f00000000, 42, 10)],
  (0x82c0009118a846291a07068161a054460b1402442090502406091a0f068361a0d4462b140a8442a050a85029108a4281c0a05828150502c060b040240209, 28), 0x300ff800e0e070f9f9fcfa505e2cd3f319f, 0x3fcfd800e0e07000a0b0a313160cb151085,
  ⟨16, 9, 6, 5, 5, 12, 1,
  #[0x3a011416],
  #[0x1a00f8016068c3e80440f602096f008c0de66057be1c41a066305fb18c09406b035e1cc1db26b05d0082c48c4106e18a40e72590],
  #[0x0]⟩⟩
def p16Fact : Fact := (p16.mask, p16.bank, p16.fuel+1, p16.goal)
def p16Cuts : List Fact := []
theorem p16Known : Known p16Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p16Block0 : treeBlock 0 16 (p16.check p16Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p16All : treeBlock 0 16 (p16.check p16Cuts) = true := p16Block0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p16Lower : Lower p16.mask p16.bank p16.goal (p16.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p16 p16Cuts p16Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p16All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def p1 : Problem := ⟨0x5555555555555555, 0x5444444050404000, [0x4444444444444444, 0x5050505050505050, 0x5500550055005500, 0x5555000055550000, 0x5555555500000000], 7,
  some ⟨[14, 22, 28, 38, 42, 50, 14, 14, 14, 14, 14, 14, 6, 26, 34, 44, 52, 56, 6, 6, 6, 6, 6, 6], rfl⟩, [(0x4444444444444444, 14, 12), (0x5050505050505050, 14, 10), (0x5500550055005500, 14, 6), (0x5555000055550000, 22, 6), (0x5555555500000000, 38, 6)],
  (0x16038340e1c0f0683c160f0703a0d0e86836180c84432090c8582e140a8442a050a84826110980c260d078301c0a070181c0a058241603058180e050380c0e, 28), 0x3fffc003fe03f8fe1e3c7f911fffc7ffe3f, 0xbddd80077a03b0ee1a34699114ed4266e1b,
  ⟨12, 8, 4, 4, 4, 12, 1,
  #[0xa800],
  #[0x4249649624b196801107631486a80f8029882572c4101803180f496424cc5291c01f0d062b8],
  #[0x1ff]⟩⟩
def p1Fact : Fact := (p1.mask, p1.bank, p1.fuel+1, p1.goal)
def p1Cuts : List Fact := [p19Fact, p31Fact, p32Fact, p39Fact, p40Fact, p41Fact, p50Fact, p51Fact, p52Fact]
theorem p1Known : Known p1Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) p52Lower) p51Lower) p50Lower) p41Lower) p40Lower) p39Lower) p32Lower) p31Lower) p19Lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p1Block0 : treeBlock 0 12 (p1.check p1Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p1All : treeBlock 0 12 (p1.check p1Cuts) = true := p1Block0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p1Lower : Lower p1.mask p1.bank p1.goal (p1.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p1 p1Cuts p1Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p1All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def p2 : Problem := ⟨0x3333333333333333, 0x3222222032202200, [0x2222222222222222, 0x3030303030303030, 0x3300330033003300, 0x3333000033330000, 0x3333333300000000], 7,
  some ⟨[9, 21, 28, 37, 49, 9, 9, 9, 9, 9, 9, 9, 5, 17, 33, 44, 52, 56, 5, 5, 5, 5, 5, 5], rfl⟩, [(0x2222222222222222, 9, 8), (0x3030303030303030, 21, 17), (0x3300330033003300, 9, 1), (0x3333000033330000, 21, 5), (0x3333333300000000, 37, 5)],
  (0x60240a091c0f0683c160f070391a0d46031108c42231160b45029108a44825108940a250c070281c060703019088642815088540a15060340a0d040240209, 28), 0x3fff0003fc0ff0fc38f8f3a27e7cc7ff1ff, 0x3fbe0003740de0ac30b0ada2565c40cb0b5,
  ⟨14, 8, 5, 5, 4, 12, 1,
  #[0x1780947],
  #[0x10003e0be92c758004730409f91464fcb5314e4b18a605588392925982e92ce73c964b4003f8d8063cc46209],
  #[0x1ff]⟩⟩
def p2Fact : Fact := (p2.mask, p2.bank, p2.fuel+1, p2.goal)
def p2Cuts : List Fact := [p17Fact, p27Fact, p29Fact, p30Fact, p33Fact, p38Fact, p48Fact, p49Fact, p53Fact]
theorem p2Known : Known p2Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) p53Lower) p49Lower) p48Lower) p38Lower) p33Lower) p30Lower) p29Lower) p27Lower) p17Lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p2Block0 : treeBlock 0 14 (p2.check p2Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p2All : treeBlock 0 14 (p2.check p2Cuts) = true := p2Block0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p2Lower : Lower p2.mask p2.bank p2.goal (p2.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p2 p2Cuts p2Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p2All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def p3 : Problem := ⟨0xff00ff00ff00ff, 0xee00e000e00080, [0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xf000f000f000f0, 0xff000000ff0000, 0xff00ff00000000], 7,
  some ⟨[7, 21, 22, 37, 38, 49, 50, 7, 7, 7, 7, 7, 5, 6, 19, 35, 52, 5, 5, 5, 5, 5, 5, 5], rfl⟩, [(0xaa00aa00aa00aa, 7, 6), (0xcc00cc00cc00cc, 7, 5), (0xf000f000f000f0, 7, 3), (0xff000000ff0000, 21, 5), (0xff00ff00000000, 37, 5)],
  (0x981c68361a0d44633098cc6032110c82432180c44231088c44627120984426030984825108940a250985c2816090580c160a0542215028540c070281c0607, 28), 0x7fffc007fe03f8e01ffffdf1e3c7b8f1e3f, 0x76dd800eda03b0600b56e9b162c59870e1b,
  ⟨14, 10, 5, 5, 4, 12, 1,
  #[0x140aa44],
  #[0x1d725962ec38271b105a8002143ac402d2c38174496087988157d26ea0801f00b61c2ab70e2db7258a263145],
  #[0x7ff]⟩⟩
def p3Fact : Fact := (p3.mask, p3.bank, p3.fuel+1, p3.goal)
def p3Cuts : List Fact := [p30Fact, p32Fact, p35Fact, p36Fact, p37Fact, p46Fact, p47Fact, p48Fact, p50Fact, p55Fact, p56Fact]
theorem p3Known : Known p3Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) p56Lower) p55Lower) p50Lower) p48Lower) p47Lower) p46Lower) p37Lower) p36Lower) p35Lower) p32Lower) p30Lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p3Block0 : treeBlock 0 14 (p3.check p3Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p3All : treeBlock 0 14 (p3.check p3Cuts) = true := p3Block0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p3Lower : Lower p3.mask p3.bank p3.goal (p3.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p3 p3Cuts p3Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p3All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def p4 : Problem := ⟨0xffff0000ffff, 0xeee00000ea80, [0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000], 7,
  some ⟨[7, 9, 14, 37, 38, 42, 7, 7, 7, 7, 7, 7, 5, 6, 10, 35, 44, 5, 5, 5, 5, 5, 5, 5], rfl⟩, [(0xaaaa0000aaaa, 7, 6), (0xcccc0000cccc, 7, 5), (0xf0f00000f0f0, 7, 3), (0xff000000ff00, 9, 1), (0xffff00000000, 37, 5)],
  (0x1181c582e160b4462b140a8442a050a85029108a44627120984426030984825108940a2506038140e03038180d02834140b0182c1009008240c070281c0607, 28), 0x7fff0007f80ff8e07ff87de78e67b1c71ff, 0xfdf60006b00d50602db86965866590c30ab,
  ⟨17, 4, 6, 4, 5, 12, 1,
  #[0x46efab],
  #[0x7526a255c9b9d8862871b61c319d2587258041da5258f67b103d12056741c96308003e03fe1c358063677d3101d7cc40c5401b9cf58707],
  #[0x1ff]⟩⟩
def p4Fact : Fact := (p4.mask, p4.bank, p4.fuel+1, p4.goal)
def p4Cuts : List Fact := [p28Fact, p36Fact, p40Fact, p42Fact, p43Fact, p51Fact, p54Fact, p56Fact, p57Fact]
theorem p4Known : Known p4Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) p57Lower) p56Lower) p54Lower) p51Lower) p43Lower) p42Lower) p40Lower) p36Lower) p28Lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p4Block0 : treeBlock 0 17 (p4.check p4Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p4All : treeBlock 0 17 (p4.check p4Cuts) = true := p4Block0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p4Lower : Lower p4.mask p4.bank p4.goal (p4.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p4 p4Cuts p4Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p4All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def p5 : Problem := ⟨0xffffffff, 0xfae0ea80, [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000], 7,
  some ⟨[7, 9, 14, 21, 22, 28, 7, 7, 7, 7, 7, 7, 5, 6, 12, 19, 20, 26, 5, 5, 5, 5, 5, 5], rfl⟩, [(0xaaaaaaaa, 7, 6), (0xcccccccc, 7, 5), (0xf0f0f0f0, 7, 3), (0xff00ff00, 9, 1), (0xffff0000, 21, 5)],
  (0x981c341e0c070281c06070341b0986c30190886426170a0582416030582815088540a1506038140e03038180d02834140b0182c1009008240c070281c0607, 28), 0x7fff0007f80ff8f87ff87c678e6787c71ff, 0xf7f60006d00d50182db86c65866582c30ab,
  ⟨15, 6, 5, 3, 4, 12, 1,
  #[0x6d00],
  #[0x38007c072629eb6c38871496405f0e3cb8c60889631f0000478c24b3c6862908a92ce1818d786f0e1c44c41e9c02bf],
  #[0x1fff]⟩⟩
def p5Fact : Fact := (p5.mask, p5.bank, p5.fuel+1, p5.goal)
def p5Cuts : List Fact := [p28Fact, p34Fact, p37Fact, p38Fact, p39Fact, p44Fact, p45Fact, p49Fact, p52Fact, p53Fact, p54Fact, p55Fact, p57Fact]
theorem p5Known : Known p5Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) p57Lower) p55Lower) p54Lower) p53Lower) p52Lower) p49Lower) p45Lower) p44Lower) p39Lower) p38Lower) p37Lower) p34Lower) p28Lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p5Block0 : treeBlock 0 15 (p5.check p5Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p5All : treeBlock 0 15 (p5.check p5Cuts) = true := p5Block0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p5Lower : Lower p5.mask p5.bank p5.goal (p5.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p5 p5Cuts p5Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p5All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def p7 : Problem := ⟨0xaaaaaaaa55555555, 0xaaaaaaa050404000, [0x8888888844444444, 0xa0a0a0a050505050, 0xaa00aa0055005500, 0xaaaa000055550000, 0xaaaaaaaa00000000], 7,
  some ⟨[14, 22, 28, 37, 41, 49, 14, 14, 14, 14, 14, 14, 6, 12, 20, 26, 35, 6, 6, 6, 6, 6, 6, 6], rfl⟩, [(0x8888888844444444, 14, 12), (0xa0a0a0a050505050, 14, 10), (0xaa00aa0055005500, 14, 6), (0xaaaa000055550000, 22, 6), (0xaaaaaaaa00000000, 37, 4)],
  (0x8058081601058100e02038040e118c4462911894341c0d058340e118cc4231118ac42291189c42250d078301c0a070181c0a058241603058180e050380c0e, 28), 0x38fc00e26c3f81d533c7fcf0ffffc3aa3f, 0x38fc0080703b0107034648000ed27faa1b,
  ⟨46, 12, 16, 7, 6, 12, 1,
  #[0x95343161d0c0006ed410e208c008],
  #[0x6781a040bc38a93605710ad882c45310321800989d6039413cc5220a807c4e762088a6c4048b1882a3e496444762b88c001d504a4b190661c58b692d899f26f131cc52c7ac96129e637895d871105403a22261c2ef231b89a606d53a24b1729310c43f934a0ac03711f009e2, 0x6125953f80a017181b4478008248801111dcc52a2fb13c4550304d2a650d3ac07e21401bc48032789f203e011b0e14],
  #[0x3]⟩⟩
def p7Fact : Fact := (p7.mask, p7.bank, p7.fuel+1, p7.goal)
def p7Cuts : List Fact := [p39Fact, p52Fact]
theorem p7Known : Known p7Cuts := (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) p52Lower) p39Lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p7Block0 : treeBlock 0 32 (p7.check p7Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p7Block32 : treeBlock 32 14 (p7.check p7Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p7All : treeBlock 0 46 (p7.check p7Cuts) = true := (@treeBlock_merge 0 32 14 (p7.check p7Cuts) p7Block0 p7Block32)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p7Lower : Lower p7.mask p7.bank p7.goal (p7.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p7 p7Cuts p7Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p7All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def p8 : Problem := ⟨0xc3c3c3c3c3c3c3c3, 0xc2c2c2c0c2c0c280, [0x8282828282828282, 0xc0c0c0c0c0c0c0c0, 0xc300c300c300c300, 0xc3c30000c3c30000, 0xc3c3c3c300000000], 7,
  some ⟨[7, 9, 14, 22, 38, 49, 7, 7, 7, 7, 7, 7, 6, 17, 33, 56, 6, 6, 6, 6, 6, 6, 6, 6], rfl⟩, [(0x8282828282828282, 7, 6), (0xc0c0c0c0c0c0c0c0, 7, 1), (0xc300c300c300c300, 9, 1), (0xc3c30000c3c30000, 22, 6), (0xc3c3c3c300000000, 38, 6)],
  (0x885c0c17080580c0f0403800090081c70311c0a470191402442090c02422091c0e46031108c42231140a44229030983019088640c16030381009008240c07, 28), 0x183f80e143c701cfe36efa00099d7fff67, 0x1f3b00a1cf46009ea24450000998214d22,
  ⟨103, 2, 35, 8, 7, 12, 1,
  #[0x1a527a2c60120216b90c109036b30c0e7b0077000675005616001e00004b006e, 0x5440bb],
  #[0xa80f8b4618a635d4968b3f9998b7e8081d220158b0e61c427c61e0c2a9938b44e1c631f320256e98a0b52815102b49628400150d39b1a3f0861c0b0f6202e59812c212c960b029958b6e00f8030194181fe1c286d4a002413185e5200e026db1aa844818336861c0d5e80d8b4a00818, 0x770198b5c3149576314312cb143207b1406754a0336bb1a24028048b70b1a415fb1a22538046328496420d99a216db108b2b49e4577820020c31a0651008210ec998b3231a19509a0217531a282801a580e49a021eb148b26c9b8b39b1a4d20b158b37b142e3f3138b2818f8b2198d8b, 0x7501e33253125e108098b36b198b54018c27031a8b4cb10632c19a1d058078b69e1c155bc9a335d4962b57b1b283261c5b2d1a0180f31b8b55b101532c9615558205828314e33631a5d74b1ae316814582e49663693102b6d320230c31e5e6c99b8b23b1a956d0138b7f3100b1401a02, 0x7d18a8b44b202277e1c8b5981b8b770040b04c965b251941d],
  #[0x0]⟩⟩
def p8Fact : Fact := (p8.mask, p8.bank, p8.fuel+1, p8.goal)
def p8Cuts : List Fact := []
theorem p8Known : Known p8Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p8Block0 : treeBlock 0 32 (p8.check p8Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p8Block32 : treeBlock 32 32 (p8.check p8Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p8Block64 : treeBlock 64 32 (p8.check p8Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p8Block96 : treeBlock 96 7 (p8.check p8Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p8All : treeBlock 0 103 (p8.check p8Cuts) = true := (@treeBlock_merge 0 64 39 (p8.check p8Cuts) (@treeBlock_merge 0 32 32 (p8.check p8Cuts) p8Block0 p8Block32) (@treeBlock_merge 64 32 7 (p8.check p8Cuts) p8Block64 p8Block96))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p8Lower : Lower p8.mask p8.bank p8.goal (p8.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p8 p8Cuts p8Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p8All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def p10 : Problem := ⟨0xcccccccc33333333, 0xccccccc032202200, [0x8888888822222222, 0xc0c0c0c030303030, 0xcc00cc0033003300, 0xcccc000033330000, 0xcccccccc00000000], 7,
  some ⟨[9, 21, 28, 38, 42, 50, 9, 9, 9, 9, 9, 9, 5, 12, 17, 20, 24, 35, 5, 5, 5, 5, 5, 5], rfl⟩, [(0x8888888822222222, 9, 8), (0xc0c0c0c030303030, 21, 17), (0xcc00cc0033003300, 9, 1), (0xcccc000033330000, 21, 5), (0xcccccccc00000000, 38, 4)],
  (0x2034020d000244632118a846260c0242209060240a09118cc4432118ac442a1189c44260c070281c060703019088642815088540a15060340a0d040240209, 28), 0x1c3f0001030ff0ebccf8fc403e7ce3ea1ff, 0x1c3f0000300de00280b0a80c065c5d6a0b5,
  ⟨31, 2, 11, 6, 5, 12, 1,
  #[0x36e80f54080d6f023],
  #[0x1ba64ee2f807b80e080d2431bb958c40405c96387987085a99494de629338310b89d25880e013b8aa010e7698db9e125843e01bb80587136e80f803c036e7680fb90f87053c3104c74628512310392406d321b13b86c06ce2a98a3927870e62c964c52012e],
  #[0x7]⟩⟩
def p10Fact : Fact := (p10.mask, p10.bank, p10.fuel+1, p10.goal)
def p10Cuts : List Fact := [p38Fact, p49Fact, p53Fact]
theorem p10Known : Known p10Cuts := (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) p53Lower) p49Lower) p38Lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10Block0 : treeBlock 0 31 (p10.check p10Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10All : treeBlock 0 31 (p10.check p10Cuts) = true := p10Block0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10Lower : Lower p10.mask p10.bank p10.goal (p10.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p10 p10Cuts p10Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p10All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def p0 : Problem := ⟨0xffff00000000ffff, 0xfeee00000000ea80, [0xaaaa00000000aaaa, 0xcccc00000000cccc, 0xf0f000000000f0f0, 0xff0000000000ff00, 0xffff000000000000], 8,
  some ⟨[7, 9, 14, 49, 50, 60, 7, 7, 7, 7, 7, 7, 3, 5, 6, 10, 12, 52, 56, 3, 3, 3, 3, 3], rfl⟩, [(0xaaaa00000000aaaa, 7, 6), (0xcccc00000000cccc, 7, 5), (0xf0f000000000f0f0, 7, 3), (0xff0000000000ff00, 9, 1), (0xffff000000000000, 49, 1)],
  (0x1c0c868321c0c468310602414090282406091c0f0683c1c0e870391a0d86835180c8603106038140e03038180d02834140b0182c1009008240c070281c0607, 28), 0xf0ff0000ff0ff800ccf87c02ae673f151ff, 0xf0ff000acb0d505a4cb86050066503000ab,
  ⟨363, 66, 121, 10, 9, 12, 1,
  #[0x27481170000487315c060084900000000040002a040431481c10802010081041a0fc200080226812, 0x3380441410070281801e168a605806000000388c18800060163bc301781a3140a058740000801000, 0x1c1f979c1c049b51381022000078000117e0080e5fd650002a230000104c51c023d8040000c0b834, 0x2bd4f164629820001a0d00273a8d1f0489dc0697e2f0b016052292591c8154a],
  #[0x57c9b3c13667afd6f80fbc9c60261b4e00786db3258d16b31031c12061155449635db0662df79b1203cdd8825854e1c510340800e1901b5109265161184962d08e026ac56019311a0c62df3861f5454ac4eac74015ab0e38715701995ab060c4b570a4961849d870841f0201d5e38705f23310bc98c62960, 0x3301bab034035444ab1e1fcd802551091944d462684b43401b1f173870a955c963f4d06513b03498359e6684e23f82055850062f302c995ad49e88455b61c86d0f261385b4960d8ba03eac6380eaa5fc0535724499255dec40ac4f9a15101c06e1b2981386d72650bb11819ae5ec0794c18c963c8c1258c7, 0x99eb4dcb2590403e1cab146c6ef240c99ab175e89444831935d9d266d73e499b45b206ca223015c106a678ad114961b51ac61100a009bc81b264b453008d85ecc60df4280fc11c1258e20cb1eb20e0022b46bb104505c0502c0d812dadd1258c3053120acda06ed13d0084addb258c86001494425258d9, 0x461c584fa66eac6b99b2a4bac40455300db443e035510f00e01d90c40a97d807545c7870df1461c0886a052a96018a1154863ac40a99a251632584f28e1c3890ec40d93f3130ed08038a91d61c34dd387114110074246e06c847461c311280661b16b18570900855122c9643cf6010ac1cc9655dfc05149, 0x6ec96c10f52584556993511b0c78ad50998bcdb066aa97b007ab0006293628b1e91400c7ad3388215106e64cd76899f511c0039492b7a23105c06d4914192b596d259690049a915fb8701b2a80418d96027040b7a25457e0847c07b10ab016c66d10a01a284eb2613a6598ab441b8704538018be812c84f0, 0x35c9826caf8704f4219b2d07cc4c841900e201e3262a97d193ab131870d12981eb4c6b26ef27631037cd3258f37818db4543258631061c3c14a024a23a01a19d932647c4019b5848f884df3400434478056f26798f510b804ed10f19e56956c6eac7161c5aca6c40c40e0135450be887c0ab10b448404cc4, 0x56496450dc056d16ec960457ac62fa2e31032012c406d0631335da6c78c83800ebc08c026d13e00fb4549886b44498a30dc326ed16031b21d0003e000801586d0e0107c75fa234c3a03a877e62114414024843ce1c21c5727afd4f99bb4566c60fa717a22a50127a450f807b445e050a9458213108a084a9, 0x640135108d870f26281ada580c6ed10be1c524fec66ac45995b45a606cc412820284178707c5c01496076678a732c9bc1026c56d11018a3445f25aac22313b45b4c6ce20cc9bab060020fc4bc962b1c12610520b101f1ef25af2493180204d870b412019424bcc40fa29c99289566354461993b4556c40f0, 0x7680c5a14a010c4718200b150c41571598dab1a867a453681416534c40f244019510e66812b5cfa237d3726c4f3e98a2b178012ac2619425182628b45318a37d42669611eb180e8dec48be518084a818c64df6d4993593b872d14f496581a0c41446c0084ed84632d645b10344d6683492bc960a4ec04968, 0x1dc9851cef88551028081e5f4066ac4a4964d8d4666ac6c1949f1b1258fa2d1955105f871040f99e3f5286654410e1c28979258930449637d5f870ac6961e23816c404f4d00f86dba022e25618a55c26664b4564962a4a6628e24f61c3b0f868135147a22d13c04eac40c9651071258c43461c0a5d2036ac, 0x100085857462aac77807ae47407afd5399b51020082a9584a13c1e3870d74698e251f0080a9210191f16be88e209c96210bd870d64361c4642925ad15400d86dbec6484126213c0d463935504a137d646482d05315ab1cc066d106315bc956628d61cc9eb21252587c1a804b4578c60f9497a23c1c263eac, 0x13463ed12db13bc88006949200042a5a86693b45c96465ea061530bc9a8ecdc0121b7c81eb2120666d1],
  #[0x7]⟩⟩
def p0Fact : Fact := (p0.mask, p0.bank, p0.fuel+1, p0.goal)
def p0Cuts : List Fact := [p28Fact, p54Fact, p57Fact]
theorem p0Known : Known p0Cuts := (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) p57Lower) p54Lower) p28Lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p0Block0 : treeBlock 0 32 (p0.check p0Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p0Block32 : treeBlock 32 32 (p0.check p0Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p0Block64 : treeBlock 64 32 (p0.check p0Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p0Block96 : treeBlock 96 32 (p0.check p0Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p0Block128 : treeBlock 128 32 (p0.check p0Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p0Block160 : treeBlock 160 32 (p0.check p0Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p0Block192 : treeBlock 192 32 (p0.check p0Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p0Block224 : treeBlock 224 32 (p0.check p0Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p0Block256 : treeBlock 256 32 (p0.check p0Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p0Block288 : treeBlock 288 32 (p0.check p0Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p0Block320 : treeBlock 320 32 (p0.check p0Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p0Block352 : treeBlock 352 11 (p0.check p0Cuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p0All : treeBlock 0 363 (p0.check p0Cuts) = true := (@treeBlock_merge 0 192 171 (p0.check p0Cuts) (@treeBlock_merge 0 96 96 (p0.check p0Cuts) (@treeBlock_merge 0 32 64 (p0.check p0Cuts) p0Block0 (@treeBlock_merge 32 32 32 (p0.check p0Cuts) p0Block32 p0Block64)) (@treeBlock_merge 96 32 64 (p0.check p0Cuts) p0Block96 (@treeBlock_merge 128 32 32 (p0.check p0Cuts) p0Block128 p0Block160))) (@treeBlock_merge 192 96 75 (p0.check p0Cuts) (@treeBlock_merge 192 32 64 (p0.check p0Cuts) p0Block192 (@treeBlock_merge 224 32 32 (p0.check p0Cuts) p0Block224 p0Block256)) (@treeBlock_merge 288 32 43 (p0.check p0Cuts) p0Block288 (@treeBlock_merge 320 32 11 (p0.check p0Cuts) p0Block320 p0Block352))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p0Lower : Lower p0.mask p0.bank p0.goal (p0.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower p0 p0Cuts p0Known (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) p0All
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def root : Problem := ⟨0xffffffffffffffff, 0xfeeeeee0fae0ea80, [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], 11,
  some ⟨[7, 9, 14, 21, 22, 28, 37, 38, 42, 49, 50, 7, 5, 6, 19, 26, 35, 44, 52, 56, 5, 5, 5, 5], rfl⟩, [(0xaaaaaaaaaaaaaaaa, 7, 6), (0xcccccccccccccccc, 7, 5), (0xf0f0f0f0f0f0f0f0, 7, 3), (0xff00ff00ff00ff00, 9, 1), (0xffff0000ffff0000, 21, 5), (0xffffffff00000000, 37, 5)],
  (0x289c06271009808260109840250209402250d07c261f0c078281e09078181e050780c1e0c074281d08874181d02874201c04070081c0c06c241b0886c141b0186c20190406402190a05c24170885c0c170285c06170805808160105820150205402150603c140f0303c0a0f0183c100e02038040e04034080d00834100b0102c020b0002408070101c02071c0c86832118c83432098c870311a0c44631098c4702a160a8462a0d0a87029160a446291a09858261189868251609446251c070681c16070341c1c06434190986468160d05826161a054261516038340e16034460b0d02c260b1402442090c02422090602414090282406091181c26071c0f0683c160f0703a0d0e870391a0d86835118cc2633180c84432090c86031108c42231160b8582d118ac502a110a8142a140a442291189c4826110980c2612094422502894341e0c070281c06070341b0986c30190886426170a0582416030582815088540a1506038140e03038180d02834140b0182c1009008240c070281c0607, 170), 0xff00000000000003fffff0000000fffffffe000000003ffffffffc0000ff8003ffc0003fffc0007fff00000ffffff000fffe001fc0fe0fffcfc00ff01fe03fe3fffffc03fffff870000ffc7f800f8c0303ff87ff87f8ff00f8ff8ff1dfe1e3801cdc031af8bcf119e399f1f03e3fff1fe3ff07871c38cfffc171d8e387c71ff, 0x24000000000000039ddffe92b302f7b6fbec000000003e393938900000decc937fd33077db400077f600000a69292000c490251b92bc8eab0bc00d601b4035424855640264ac9044222d984a80a18c03016982db8648cb005854869088e664916d5c1708d82cb119619970500a0a4b046091299124094553c030c86182c30ab,
  ⟨9282, 17, 3094, 15, 14, 13, 8,
  #[0x40000000f00020004000002a0000001801400100016001000080030002002000500030018000000200010004000000f8000000c00ac01000040005, 0xde018c023000e00380018004800000000010021000c00300038003000c000800080000002005000180150012000400000000004000400000000002, 0x68000000c002a000804dc089801c021e00000260103001000f800000e50040000001200e1004c00000100000000c029c00d005e014200780040012, 0x100db8000000000a00d381a1005800180080185003c00e000b002000940000000002a00280000001015d004800a80180004001405340090008, 0x40008008022100000010007000000280008000000c03f6000000000460080000000100180060003000000140058006805401f10074079c0000056, 0x5c00181568002000c0a6400b001000340040003000a00940008014000200000000004000c007c0060004028b00000010005024b003c00480030000, 0xc000802303570000004800400140010003800400000000000000000020000005817d8002004400a80080008005000e00000010000000100090000, 0x940168001000c00b0003025e8467001000102268000000010c40000004005c00c81e183a5000000081c9801a000800001b2800400340008010035d, 0xb2a003000f007a000c00b800600380b26001001500420074000800000000004001000300020010157400e0012007c14b400000020a3e00000150012, 0x14002039a8024000800a800006ef000000e0017000c0014002000c00040daa00003678000004400300410004004c1afc00b05ed01ac00782ea80a8, 0x400018006000000e4203c039007800281fbc0010000002000f8000007c000800000000042001c000800c00080074011000c00020f9e00083e58004, 0x1c0030000200140000000001c00b401300000026004822fc00b000600000010003087f0014206c003000a000403f000e000400a800680020010, 0x400000020054011c27d400009e7000000700080002001400104f1801e002c266c0020002004000e00090006000400000010012002400000010002, 0x6000f00000016000400000040000007000600280a510008006000000020018012802d003c00b40018000001e003428ec0030002000002c851a8022, 0x10012854f8022000c2a6c000001a000000480020012000801080040000004829dc535800000040008001002a004400280400004003400080080a57, 0x28002000000042e04000000c000c0000003000c16e20010009000216420060023001600042c2c583801200002bcc001002a005800300030000, 0x2400506958d1b00d0000866f8000002400680010c5f0024001000000260054001800b003800c00050613800c178e00505e2800200000018001001e, 0xa80188783803a00103bbc73e807e00100120720801a00f400180000e3b00300000004000a001038040070012001400406e98004000000180020002, 0x543e0400300000000000000200060008002001e0f7b1eb200180000000005c00f0002000000603d0c0170004002000b8005001200383cb40370000, 0xc4000002b0012000000000410004001800c80030002000400180000008001040a400b0fc3003000180010008001c0038001000400bc01100110038, 0x1c0008005004000000070019002c215600080030054001800a000200502112008800100000008419400a001a00f000300000046000440cc0120080, 0xc00080030052005800480000000002400780070038000000288e6800e22f2004000000040088009089780040080437400000080004000085e800a, 0x400080030000005400080040008000000188fc80160058000800400340004002000d002e001c478c8ec805a000c00a80030002004000280000016, 0x2400000090008000400809da936f00180018009000c2692000001f1339006c4be494d800a00180008000000024ea009893480960000001000100a6, 0x260005004e28020048001000000004fcc9f78000000000780030000000c0008000004e00c400409e4802c008c000800e008a000800080160026, 0xc0000a5f801000080000a518002010002680011473000051b400a000e000c0000a30806c001c00e80110024000000000051419005400000140004, 0x5c00780010036000400c800000020014000003a00100008008801d000200080000a6b802a299600480010004001800000010028002400600000000, 0x100010b33800c002000f0b09800c0044000001800b200040000b06804000285774004003600000088000158f2a960018000000e00240018a7f94d9, 0x94002800d000400085d7cb99803c00000240b7a800e001800200170002001c00c80710060000800c800b00000008007000300002daa0008022169b, 0x7c5fbc043003e001800380140004002c018002c00002fba0000000000600000158bd780002f1e000004e000400100008bb2801a000400180000044, 0x30a6003007500b80018608c000001200340088020007000000018064001e006c00b800017ff001003480050018000c0078bfd80580058000000d000a, 0x580000000000032de0020051003e000400d0000000000100058cad80303282645c014000800680040c698000000000180060000000462340070004, 0x40088cf380080004008000a001200100038014000000bc00080210002009800000000000003400180000182330a65fc01c0004004400b8024003e, 0x3469ac003000000040270d33801034ba00780001a5301c4692c02d00420000031000e1a43000c0018065000000100118010000033fe0008001000c, 0x36560030006001c000001d0001000e00000050d87800600000020d85806c00606ab4003001a001400600230016001001600080000000000400140018, 0x400180080016007400f0000000037060000000001200000080dbf800e00586d7400c003600700020001000a000800300100004000000e80090014, 0xc001800600080010026802b001c00600020e07800200186ff400a000600000010001000200046e2c0000040003400a801000100004007802d0004, 0xd0003803600003be202200040068000002500141dd5002801980081d15009800180021d0939e600a8e4f80000020713c0081c1b002400180040002, 0x1300018022005600287b34027000000b000f80091e9d00640018f4b803a0008000000e00043c860000f04802a000000a00030030003c01b004a0000, 0x7e940450006005000080040018000401f8f9e802e0020002006e000800380020f7a800200407b64015003200a8000000800360000000802f0000, 0x409200000030032005c8104007000200e00000003004400c00010000000000dc00a10128020001c002804300080000024002c00060090805401d000c, 0x439604b800321ad0014866c0210008427a0011095a121000400e000020f70098000000c007001440150002000241c6002000120d1007481c50318008, 0x46120000005008c0074023800d0004004c00680090026003401c9177a2eb451a0070000000000048a1513880100054001112e8076003001111218000, 0x2c8e34048003200c4000801f000600040000017007246620080001000c01440078002000c46360020000231700e400080030000000403b80080024, 0xa892c4000000449420018001005a0000927c000000400a09104000000600940218056001800340001204803c0004000800923ed00000058004000c, 0x28000135ea67b4c9a004801700004c92977401600a2000c02a92e4a59f005400000000030019c96552b280500018000802e000000740009267a4c1, 0x12000c0016271d002000180040142004800480000012007800f800100184de20298007000e00b00020027007400c80078019010200009b241380000, 0x4c00e80100008000000380000028003000393cb808c00989e1d3b88026000800000030026001800c0001002602209dbc0000056002c00080030034, 0x1300050004287f00f4000000200060024a16d424800850660068007282f000804100540030017c9f6402d000a00f8012800001e80004000001627b5, 0x4003000628c10030000000d010001d0000002d00000000006800c28bb0118003800b002e005401680180050512600994408018003802a8014003c, 0x4a3d4030000000000001476800e51d200a800f000200100058025000c0060029000128df00000268000005e000000380170034001404b80070000, 0x7400880420046527e00a14938098524a024803400860004008800000c2000c008000a0052001c010948a801800640080003003200ec00a80080010, 0x540e00214ea804c008404e80000006000006b0000001a00600680008001c000000394cd804a006c02b0002298f005c00180030194000001880190000, 0x550e00080050000003c002152280a6001ca8e4002000e012800000022a310008003000c003600000200059000001b40039515802a543603b80110022, 0x3080372b3900080000007018c00a800700520268566a000000900040018002158c807400240060013002455ce00100000034000800015448004, 0xc000001f003256f6002003d005e56b601b801700f6008400080020000000c00b00000098007800000100116004802000190004001800c959e8014, 0x9001200000050583eafbc0030024003403300210006000000015e5801e01240040019002c0098adf40830026001402a0007008800d0000000000ae, 0x5a3eb3ec0040038002c000000700380000000001701cc59aeb35402b0006595200080060012592200200020090021c01d8012001800a400100002c6d, 0x7280000084000800b800000040010000802c001802f801200082dc3004c000000e008c0100003801100005b220068038001a00a8000001b2d85, 0x5c4e000000000020070000970dadf55bde009802a000800000018009001c003c008803a00be00880068021000000000048000001a5bce000800f2ddd, 0x5a8028801e00040028005800100040058006800c006c5e42020977f8054007c0099779800a0004006000700485d8600080912e7f000c00a97198008, 0x24000400010002017800100130046002400100000062002800000040038009cbd540362f470010011006800005e6200180000002000801980000002, 0x1dcbed4015001a0004021800b00c6000000000000080028c00a80392fa500240590048004e5f0600a00272f7f01cc059000100000000bd8c0070054, 0x4c01f8000017261da06c005c00120000000000a000e6162c28401500000034021001900180004c21c005012a000c0328000000660e601e8098305b, 0x800038042001a629a05d004c026600040400000000c00ec0038001002200000008009001000100278062001600000190008003e01cc002800130f5, 0x64fec9d590d801e0190c85c1c831eb0008c7358e580100000c70400400dc03380668067005a009800a000f001a0080038004200ac009c070000f0022, 0x180058004000600a00088004000a000c0298054008e00000770059000000840000007004e00080001957800000000271953b2a502400018020329f, 0x1407b00450000002cce940bc004200340000004000666de02d0001009600000030000007466d601f8010000001e00138003001200440060064331b, 0x2b0007003c68d201b8040001e0104031800200080078013801e002000a803a00100000005c0028017345f00100458012344b000c00b003733eb, 0xa801d801e024069c20040050019e00c00030002000c00840000009003e696e016800400d2002c02e9a4b8000009000d8000346f00e80030010003e, 0xf40001abc800400cc000801335730088012805e354f00200099aa4812801480060000001200d80000041002069f600c1a76800000e0002000a000e, 0x6b4201c800b019800600001acf801c01f00028000000802ac0328045000400d804d9aca800400000000014358f0064007801400be012000580060078, 0x180000000364b0000088800935e70004018002e00e4006400a000a0000010001c00220000006400b9add80180000035007700a6007800000150000, 0x11c07f002000aa008c0148027000000000b88012009401140001b62805000a80181b5780046cf200a80170040005802f800c00000274000003e007a, 0x200050024000a6e760c78001004200540038028003400ac0319b968040005401d1b94b71b005c0071b67b6cd000c00b0051003a001c0978006002a, 0xc0681bbe8004004c0000000008a000800000030014001802d9bbd80106eca005003d00486ea200180000000007c00c00000186015801b001a00a0, 0xdfac0030010000c00500c800a801280051bf281d0013c03f1bdb80960b20001801b01546f2600b004a000802a400381bd01e200c80050000377f, 0x2c8e31404b00b60020000000000e8713a02a0003383b002800100f7001002700ba002c01b4005400800da02ba009400000060012000000200443815, 0x40000004000002500050001031c002000780a4000e000c0070007003000000000023004200a004e801600300004e514000393f05a8e405c738000, 0xa800a001039e70000001802700020580034800000040234000000000080030e6ec007031a0020000001201e000b4000000001b072ca00700c30074, 0x776a0219dca8008018801e1db9bb41000002180030000007401b004f00b20244090000000cc00bc017002e3b0d752ee95400c002000000018058000a, 0x68f0cc0003c19000402200700050003800800a704f802340011df48002031006a80203be777b606a814900100040023000e3bd70724000001501a6, 0x6000a9e8d80100038004801e008400000090013004079caf24c08701020120f21c06a002a0018f1d5e2b81e800880071e24804e028c03a00170054, 0x5802780470000013002e007000567b96041003800127b7e0010023000401c40578072000400240291ede800c0008000816d00547b5af55c0110030, 0x2401380060060046403200243e717c4602d805606280004001800b001a080c0010010012400c8010801e3df5005000180a23ddb0598054001a000e, 0xc0ca80000184005805f00ae00360000055800e000001f8fabc04104c0002c007000400047d56036800b0000000002780233ea3015800580010044, 0x978043003700087e0202400f8023c0000fbdc25702900000017000000327dc6003800001ae004800000130004000c000009a3ed50038019000000aa, 0xd0004003016200f8fe0c0b4064403740ac8005000e0394002823a0026034801300200022003c01380a5000801580331fad800001e0000001a3f1d, 0x81520300119013c004501b40040078010800000c940210084060800000000018000002f00740010003800700000004160802400000058005a00c802c, 0x84560010009000e83a2000a0bec14101d804680030056010801a0009005a000408a808500d8000002100004133000c0042090c11b000502ec0f90006, 0x12400000000a1a03250d5e185800000a400c8026003e85f20000010006685ca00d800800420038008a146c26f000108d4050000002bc006000d06fa, 0x1f40270000000002dc000001d0000000801a0027007c00310f6c00801ec00ac006a1e980d6004800000dd0000001816c800800360e640120001437f, 0x58c02a814400ae000004c001000fc002400aa296801c00080002287869e8a1604400d5000e01c5134c1af44a388e604e804700ac880200300000170, 0x21000080ca45b9000d15fc117000a8a9a06d80670000000000d8000003000dc016229d80048a6a063000700060034230800100240018007001103da, 0x4801a001600a8000c00200f1001e0000000809a002e0160005800200ea8ca6018801d02e200041eba3158a5c8bda05f0001018c024800c00000038, 0xac00d801100000000093800000248f7201c000c000201f11dcc00600c68ec204523ad81a2000d1c840c100740060090005500b601351bf63778032, 0x2422c83b001001400010554004005c01e547f1000003d002e0ac08fbe001001c00aa0008008800d0032],
  #[0x7cf54963a2401546207450f560c602f58c3ea5254c40062313a78668a66435dfc01f807ee820046a4b02169f0d00729f80160c3f3735d5d0010a960e90a50602930ec009454d081a029849c561469e01fc50d01383362c8861e39ec00943424d8a175467e620155a81391108951310261201163290ec800c4c40513ca908ccc1e100ec4a6b64304d863306c400a4c82e6cb4068c6ca459ab0621894c014c93230a0021068053eb9fb009d541, 0x31211a59ee4496c933129801240108d0c59c0c7d781446501bbea0eaae00c20edf3f8c4c87e806ca508539655100f3d25046a31e509c029803e623805b8070a7300864960baec3da64b5738032de88aa29a5c8c54a0f4ec262031f2ea3002756726bf469060b3a9d807868907cf4aa22052490637540c00dc06b09e80139881628850d313af08ffea34b7f09fcf8682c598fa2803cf250f4631a244c3f4200811a1add00108c6005b3151683, 0x4b4998a069218327421001fc0841060ee118fd5032c13315bf84042403f2a0c02592582c780538cd8816564200e8051128832b10b41c50696e751226807c0c477f14a1a8e648e033706cde87c63ae67805ba4b0e898ec7193c5401cd092c3cfc017c084463c829a509f5000be3149d8ca7d863166a8289862ac6535c700fc89c00db18eba9b2450f44540c00f0c7a7993f59813180558ac31484d44f823144c7cb1ac05035e35dc80215c6, 0x9f327246d08fe03f540e17ec6800e6b814813097000e11a4480a013af548605e491e92ce1b59a80203de00f118a31bf37f601b7aec02a401e281804db0f4764981301aad5828f863c117c568869eb7bb05e8ca04a700da928030c54440433335275863e44a92c40cfdef0385049e1e3ca65e3143999cdd8c6c98ba5f02508c4e00d7320222e4c6a93f24f1f640026a83003218802386179019be3714b634c3c980350084656003c8cd1ada, 0x69b81ac39cc00406206248000006469745570ca5877738b00eb6fa90aa64f47a9928409858b1de7807c1b31739195b512018c6206e95689401e620000d1880c4b02f13133de6a68c0087681590587028780710cdd3c3186c18a041ed74200870e80264c401ce001280d8ec69ae9026395825cc328368002d187020e9daf0d01a2c68e901f9fba1930620243202e403e216a0888c503de005f02480d600020080135ff28c56bc235a7002151a, 0x25b849aa232624e31c149c023466f0480013a52088500a318a254600940183ee6010d29c0ae0ef61885503008d32080d239f234f0d240260c40bfb00318d21db61f3c0143686029c3353aed4f49870308001c81612d87e3e324ab6ef9f603147a9fb1466efe148c680a5c8b531918abde0a6ecc3866a846dc6381b880ba812d18f00bf31014d23e300373c949768684baf0ffe80219c1019631314fd2e9401d3b24037c09ccb0801030f4b0b, 0x342310417e01aa63d431dd4f4c930741403b12c72e006b32020a6008862071a9617003f153000b8d31067645b021b75458986201e68036927a689804ba4f49b142c4013194e96ec03d71543370c62d06b2798d0622101f118e9d7600c831425250b8c6a90b9007b0c518a702ea49eb85c35743373f100889292b760c6718813ce00921a19c78923c02879bc027cc4cd06001db121d4043553263205311001367d1eee8c40cfa006fa50d976, 0x1ef43208172bcf0c4a1a2c014527ea489d540150dd598c161c0c8c0c1e0290be81e20c4e323807499513be449d01aab2ec28a6213019767803cf890028a4f60cf00727a23cca026003f2f08908c069048c2f398cc2ad773e193a8e66abe626241418d0096e1c83190c506fc617861c38c600c093f33ac0115258563803f8124186004449e8ac485840341d7e016c6a88a8802d98f5fae4b3d194875a015cf4402980bc526a734921500adeca, 0x1fdd0043dce272e92d1e3cb99808034480c8812d64a3d76007ab38f83834e7228019c07ab17805a0c503b9828131ba8e6009c32a66f4023c03c8d200711882242703c18fbda0fc7a03404e403c1258b47806c8c50db206da3202e1d0d4c31446740348026c144dea98d58f47c8619b06ee19bc02929e40de869892e16b78c51df172d24999946e96a01172280009258bcb16bc8c501bd008d1944498a73c008640801ed87ac2faec04950dac, 0x7fd03258366d27434f8ded09c4ca89dc000c98811a565589282a3400780372cb4024cc4064c98b21884f7289e600eb638004e3147c2401e926834c804698c1b7200b600ec6b7348432b14c87fb00125eb005118a60095a1c18d855a40bef54343a05212980ae35af8c506cd9a7b7a2085a0188008378cd78406c6910498b1201249af30138820014263c333801e1e8842312df80f4e51020f1a199c4108604b001001e06507bfbf1600f1585, 0x8a8d1aa30cc1f2ec48866802f0c40c9f3d358ca94544bd7496133800d29373e9400e46290d43dff313c46851781a1988000c43588c3a7c512926d60044007904c000231036bc7582f543d2a298d26e5eb002698a0edc1f8819383632872333047802840363c10404a4d163435081933e848e3831f3a400bec638092007e0c5213600a861f839000d803d202400b1264a7ac26ea4b499c4263024300a01c262981395394628216871d0c7d00c, 0xa3320a3fc4b2c635251002d403e49f81ec98d0371637318a97ac015402a329812392580d8a349803c0239fdb194a31f00ea04d541803b0c50943003ba4ca2af490f195a108013403102994ff8c60815443780d55c61a3400413ecf3ca02b2570ffec07ef04000ba4f20695d5b310875a0c640357dea535001ec81001ca4b16d404617aa2d4331ec64132a094b1870ae7001018a421b8fd41a6858855206299024144069e482a2ac1880654, 0xf7a18a91e83f820087f08002c06231aa08c00fd3bd282f19a881efe886275418186001edcb005b0cd22fc02a70040b8928f034836a88d64628cd4bec198c58d98c261a71a3920406302fbc14a0c9e4a220cb25212ae4bf8499a8e600c4c541d0622bc6286eababa8c742e87d0831a8272017e32a7c980358060f8a49ca24c876d002d6261cdcc42863f76a8c50128679fca640c6cf255eb418cbef80026c3c20d061b12867483e090c9c17a, 0x75320062c4c01d602659540c5404eeeec2cf24ccbd600933182b7001fcc381cbd4a2de88bc096ef8c5002800b96243ad2012a0360a040018c40155cc7e18800fc087e025a84e27726211e3debe0c62aa98216bd1078f00af0189f6c032431b5bdc01b9265114002d8cccdcd9c933268172614c02b403003e46660278032bd11e89080931ea0f2010e02a419525e066e0f0810b8c79a3d5f0849f9e7e4a2092c57381188096806097c00d9566, 0x8661c0c26baf664c624140ecc9ea7e2e87312232a0035193a74ea2183296e252eb5258e3180640071ce700c83159b9a9a5a0124be97e7cc411e7285f80fce4013b400f8f1eeba2011284092d00681abc9193d10ce411fb31035e2dbecf44201266a8010afa1893a4b411f9ac002735d402ee33431f80060c8086c003f8cda1e21342315948a2fa495424b60c7cc9c92d824d012debb00db92821fedd8c3378c0577fd2645b1807080a8e7c, 0x8a4400414f2a61862429f80191278d8880700d05cd900e549616e0d69c058079590acc662f33a9480a4a1086c892834ff0200941718c03b0c68c8b806e988061321ec4a59508f2b0040403c009469853e800700220e77d7818d823e6a5863579a904a1872aa9806b81088aa00ff00e94fa01566208c74014c010ebb3f28b0e1d128aa8026303a148e31533891460666620437c009deca00ce3240882027c32820d42144c801fb87af8071e92, 0xc6701b188a002ec381ce13c8c66cf3f36248d64975041931b242932d89547e9dfe9c010d5e3e5f8cc95f9922b315b41a01d26202565841d8700020179195121c0f1e014b05031983144f39d1c0698ffe801119255f251551939c804a8093f047da3e066836341448ccca0f4b0f01fbe36a3c23351699c5b86790c5007ea5002d5004b1a104be6098033515091cc66625321210c500c200cb1ac18fca83c63d0011ada0010e819a2798809be, 0x8e61ea68d2f2631f2a108f0862801f803c0c7170e00bc3210bf401286208adc0060c410ba4975010daa77ce27a217d0b46e315888403b126ccff0ab330e4bce4b5901bb7c2ebb601e02ac029062811129af8c51ccf81390241bd40278340127c74e8c56a81966424d0c67513618d894d2e423142d75bffc63ee95c069494150604d719ab4ac0668341637c023cc4064b85a219362ad00283102bd1336a31f05ea296063a1ea80678c6c503, 0x10024acf52b3231b2256481806295600288c74c2e80ac0241d5c74d833334659084c40f6702ab016574f5d204a116c6012e03d39a257c466c75bc82f0d04dd59ff500f0fb2837631e0f7a5c18096bac1d6399248b844bd3218fb2a5c631474ec00c066e3c11a38806def006724a63f10011801159596c68656c13007b98a5d712bb532190025daa31f5e1000c0628b7d005c3d113b683d018a081ef84e92c2f580a74c543d21eda30e01b1, 0x75e400887bca70801c6096074c07ae39a49a0c55a895e42318a3d41bf0932790801a4c40efd00520d30c268e7c61c3ee4855401f7f080308c9cb3188cc9881b1300361993a62ff160360ab40309e889c503bd80214c965b201b0278757e3296a24038069cef282b28d65828746f7aa42e4833603355eda3c8c420d9856218fda9685af00887f0ecc43375504025c06eab7491400f22ad05550041ef30bea63f0ab401a0650ef54523b150a96, 0xad32706dca7ac33574edb7d8c7a159005d98817d4005618a0796087e31b48400365258c049d7a804804789a1013b754006262053b1614403c5374214bd518b0982c4963d8c032a31439082b3c62a80280490d30d6100067aa186d354a64c905c039c03adf9004424fdc39656218a03c2001600860321230c410e22ba0807debb8f4f318ad2000e293539dc13a98a85e780738cd1ad504ac01a184401c2c4834dc4bc0628d78c4ba8ca1589, 0x1602108d247d83140eb635bcc404f034200cfdfc2009f31040e8019a3140d68025864eab70044a4b4dcd001219b1466f4c23437bc0932004a0d9000b30f033c7f9719346f24b3403d5d06505066ecd5349980d1cd8924c4aa0eda003c3363f95588c64e4073dba98801b300a34a40358feb26201f64ee7c01e2c63f6c0c74ce2031519b9404c03034e5d79f80463e4e5963881207c60093007268c013001b55b803800505ed98f524b152c, 0xf349639f701f034d3f11fe640248371680804466602ea00915bca2203143dc9e7680811e7bd588065e0844181a619b71e346318d0c01bc69287f9c7fa554af2009b7a599d63f2833306c4030cc6aa1914cf00223d83d5632a0c4800c431d329000252580ed1dd48cc026a5dc731bba8401fc95488f403ed27a10b0021988167304c718f8487353401f0bc59dd406a099a15aa4b1f709271499b1065bd66275dfc002c0980e2967c98d97a5, 0x846001b205b002e3360d780354629044000100702637bd8012254002fa3332a0d0c3466c52835e60021eca00f419b030a850834889718bcd262843806518805d7008e18c1cfe14083152fa27558c840e121b6310c78f076e496238627a692d8710005066af2d8ad300220df3b7f01a0a4eff4404830c5b4a5886c670ff500797553a52324b4fe4eae04129e556c469a05c842418f40ae92d54a111e8196a6314ce00ee5278a6702e824b068b, 0x725a321abe8656292c496001fc04e6e6802198fc90c00c57aa06d24f0355c3f7dd59c080029c16e80407ea64fb31fb0e000b6328622a525c66a76b8a8d81690e99f0b00d875b30ae34c44c4011c07a9f8aa388d34c3162d331012a2013ec4851180139284e9e4d7f0cdc2f17eb21930ea2ba3a3153dc9731cc6e4e5c29798f53cd1e73314828a01903297ba000e8010f7ac7bc80d946a00d700e445e0064c423375f97c08449e006698da2f2, 0xa30089fce1efe334826d9054084427975e3d107a91ab03208ec8d37c31f10b5af3c012bc24c88813dddd3ccb4a0839a00dc93414c25dac03652285598c543d59e273249faa3fc033f06cc075c050690916b00a48ee00bd496461600ee6260404e38cc4c64834381904047002731028641b9494982f80315e98cec801a80d171500d302418e4005e63f64ae4be8c828d8928080c5f424ade18a19d70abe01f6f85ebcc06d20996169884468, 0xcd31897a2f8c4c384b724bd467e253001e00f9d0e0011014a82049de6317681a455e8848a802824b129e53740139139290c01b3dc9f16807e5eb005b30f96fd00241a0ab08a7a0314272dd5b8080cb8c90280d9aea7c573158c8c82903367ac00b0cc6712e92760cd97701d6731eaa06016864e66d003780922258ed518c550300c431aa56cbbaa315849e7e5c6924f29a201881ded82c849f83632cbc0370d30033c010a07806a8ca9407, 0xa100f2ce860d003207c000200844b3124230e078700bf312ac5514ce04207e07d1004e792a7c1004060901ac3100348f90c33f06c40284c4044b1d9a8d04ca7005e18a427aa5be0436a240359890bf19c90192c03f0cbe014845c59ee01b4ab17c6cc6612081ca0ca567382ff0274826021c6294e39158d2580e686a28d3e2215b11315b04d0d420084f3402bc66670e804f01208af351701fbde0dee693538080184668a7f35fb8020946, 0x1c700278698019462662682aac65117e024c98d22b458873103bbad5da314017403b067e908013b8cad18f0087496273f093665864214e7d872cd5025124d22000055009af0201c631a11fe53a0092e39a53c0c9d522973d01446b201e66208ebc0195e88738a1ed98815f5004019492b401ba620708d900c078c0fc4cd0c9d883004318f04708f68c3821b40370628b59376c8cddc6325a149ab04c013801c452558440104fb970f812dfc2, 0x7e1a0279ee4010463d0ed001f0c7855a8072988230b00c419a1f2324f262b620c03f527e8e18480988118c910a015334823fe9358b5e48a4062cd490083d51bcf751b7a7b0e135e894830584d21262d06adc980dda966b170040f1201806270a283220666d27259d24dc4a602ee31b0b5200126422f5403900800cd2dab00d8c31006100f23b407b2c3f23d00068c401ff1d28812047306070129822014c62047e406240682e1b7d28c7d087, 0x474a4954a106232b7e69d5fc6527b93d80a4c1300006b49636089ff231d339024ec662c49007a009c28a039e3201835157a04c6af800a06542b0c10698fc1b11f6418a8366e9563340ccc021d278f788003189a114024a314bf9a0bd663d4cf0000063c2e40036bd2088c41d17a42c04d3e8f443b5e18918a848c801d8d31d8218ba4a78c8eff0e026251021740964df4019007c946003700e255601ce314175c021465002b12a38125ded, 0x7d1a108fee9ac02a7a49607cc4060343580c510057dc90150278ff640084c74012c64ae8eb53418dd4fc43ad18f1032109c6268de8f649258f04007b99005e4001b01b0a72eb7a6360ba003412585b58078990922600a94a127060c7204b00fdc25404b153411ca5345ad3f9818d937c008863d43740945265011118d0c512ac000f626a4dc00d492c15a0df09290747220f8d0c7d9002901b4598945c63f05e9d1cc6985b385049885a96, 0x781f02006f462f231f3cfe513987ecd53aa698d918f9abd0073dda61f633325112f85e90b50c40298dca84001e620b60800b094282fccd606361d6b2439909b8900ca1a692b200c66204448939187001fb33a18851194f1f32117ad25a4c4b620e0b980362d6c6bc25381bd945c319b106834a31c13a0ffe062ae7505b500a9896007f02c16767b1e3414f36029869aa8344a9007953d002b004464c972e04213200271e88282ccb08d05503, 0x1bf43158aa0080862081382d58c6e8d8bcfe80a0db600773101dc804b063d7fc80b64026c65007f18f4ea92ab531b91dc003a3143acc0045e88172001798a612a5c0831eb16000a2c3873a245c804c8d8803e80c57087fb161c12f407243412566014c6784bfc0f8193099c09d362a3d7e92da0080d25d6f401cf670d0a0c509f6249401bb75400cc92c2fa400986511c3004a80fd3c31b4d32ca71a01066270eb4024069aee327849881f9a, 0x89c919b8008c0cc0417b88161c6924fb032c190630b8ae100e146a019003d90d802852585ca80348c5194901a401591dc16e664855614d48c62805b35b0c5019b6b3a627b354fb9604d6f850e5c62869ec80a30f5b2e70dd00e857b134a949323e355de88a4880470044e9e011d499281133203142a1181d1258dcb4135b0fd473007549e380a00560087ca4151402022f006f8d09ef253d8020ad58259601f7d4001306325dd05cc0d0d9c1, 0x5d4963ea447d2620683401d8c40744802e190827c9dea3211f62aa2e00f06cc118c66690842c919521170ae218abbba009231489648930010fb0368c004583202874a70b9b33a6009540c02dc06c8b23098806e1c442ff7a212b800c033f1e0928a8628f4700370ca243000133101842cdba03f1e4e4bdd87e25335c800999bf13923158f1e00de31a83cd248463a728b23424b0b03007549b04360096f444d19f91126cafa49c38c54349, 0x4e31b07c6028a31b73a81c4d2586e682c198f5b510011014bf1c01386272e740144c6a9d6b93b190d5f92e6932a0bca0058f48141803598960e43e378ccc17a2ce41a104590080c483999778d2585b1802580fd4916b7200f06b015683287b4d5028682eee802d809c04f404c312855a001063c43980194628fe6c9788d04ce42c23496394c009c01c285e435806b02f801ba521c0e009a49e99f201e4631817cf7918702eabd7b98f59c3, 0x6201eaf70ebbc035849e7878caa9b412c700a8364382619582f40042314365c018c07e3c129d78c51e083ae9310069878ec343301884400b24fb0039a4b04af680c19a226214be94b6a9d1f386280299c93192c9be8cb401b00a6a24c92c80a5ae1c0130e2a0ee8ca1ab4003c49620e000c063416ddfa112a8548bf0b0d0184900c218a3c804a1c34b047c23d98703c785cc99295f2000149e986493b6337225402cc04ccc7b5830c51729, 0x82403218c8c04603280bec00e8628809354d18822ad0063310471400b200829a000f4c68019872324f520a00e631a8842c5fc92c16a19f7987e07e32df3d50a1f017818a477a00c694224ae55746502de802a0d0538e32b0318a4b00002f4849682474652c49007d0074e5610a519aab2e01b2c4877c0002c6281cb85ef00ad66992c2013894c013a92c59e803e00106174d2f00cd47300fc318a85400803485b3402d80212180b7b806cf69, 0x7be601a169c6bbc033782016d4650cf9a932a504ca849db310304c76963257299f168664323807e8c6ce1d0bf549fc6f6012c6547afc015c628bf9c4da00219e063bb0218f128e3a027067d460401e2d3004200cce5a64340064526c54492c74ec0b94c62e69ba1f807542b00f83139288835a01c46a4035987093729fb0070a5a5da719b933800940413c780bf127e7d2c5eaa531e5e00454964716016003d6b8e66a866a2084f930d05b91, 0x94120241b54022001b1e1d71a4c7a5104a4b809972900ab3101c691a20f44311cd7d52909ba004ba539556896202593386a1493e1238015cc689d30036312619a754e18e809613a0c487e14b3a0c56a8300c080a441d07ea49ec65a499402b7f0802086a91853fdd00d9199412901e255c010a31d6248015c023175002e8c50c2e3f9a00986926abe03f3cfc017466e0e41d8199058b3003261c3e12c75a92c87100124c623080038009ce3c, 0x82107a28c8c102803f70e40040c40f1f18a10c746cd66063159f8800889543ae0f859870099bf1824f00537ea631816da0aa493574edc62cc786d500ee8044a1f00980242068ecfe63316b50c0d2863c7803e189d56e5fe93198688a2b062066a5e83c0223c48212988044900514aa3f5e018264c5ef80110087167326b813158927251a094f32958033655e684069a4e5b2ba00d9ed094d8013b2ae00cc6204d19835c62860db5618020ec9, 0x42013bf14f94c636001c01d5ea8a868dd630fdeed033161c3642096a62741d1e9b4020ff81fbf0c9ca0f0b3a01aabe4017a92c7574a1a8c402f2805418a613500fc0121ff2624202b640840c809803b98e6b121adc3b61321948a0112036553001a4c4084e003780f5584412432739e4593203d4d583310c4ec599dc780a9013002700424a469d86357b3a0b20c66e223e068cdc646869719aaf08f560c5457186d006b51e0ca360c9c99c, 0x6551a0a998018631f050803c5ea858d0fa7002446815a102d17025ca804b6408022c6287fb3fba1881fc20445496089208a602875380b4c01120b000919609c501560209c843676337509e25a4066fc00e68813ced700a132683b4f79800f267007d4650401804f1881ce5006549e213697983264ab0027404800e809b8045f3338454a41862768801e7e9c95c003c7b4ba8480dda7f0274004477246fe3148c0648fc084f8916b18c9cd19, 0x80018a178012e620274401a5268a53005498944d2025c3264262852c03f06ccc530024a6c49de8d0dcea58f1009013204ae33f6a2529280b0da9805f00d4d1500f83260cecf79493c241a134806a53c8fa80c51d2b019e1943c70963292c001001286291ae8029b1210f80cf918a094c012892c5fa0c798c8092d9e9a00990fb4289015164a1dce9310734bd90010af925628c51087006b7a244700062620555801f004a5c64aff8c9ca45, 0x19da19414e67b4262000e263a0080ada0fc48ccc1b32a6231b0630b3200088824088464e0278042190104b1f310040bca06966495bf01d4cc9891b2cc200fcb03860c18a0ec201f063d128e53b8086e450f70810d8480012324288c00cc0302b4000e98781b441063d141b100f2496286a472e314718e1ad807efe1340d0ccc4687c2319a05a6013694105994754628a818018988053872d87aa8fd4d7d000d0be5d7c40188d14dc900a9971, 0x7d4a01bb54e01249585d1c119066c542c94d98a403f044e1a13064928431439440bf4084da185a13d3581f007c1a6901b242893d33922440098c3ec3740ca61c514b818a37127fce00f0d32564806c35e433f80ad78431363109e7e244434c891c02700844ea26faa4c58265239004037a016c62086a092f0c7b029be1e8108dbe4b2b496075b33240426a9183a866ee2a805c9881eee68b01a01e4c023c01b6a25ae400108c7cfb30c5097a, 0xd54a1b54f3e440422c9630c00240a29ae00cd975e58f731a8d8800de3343be54864c9aafa329a0071c64007349609682c4002739440264c84a31148b804e2a6006800e3a9c2206f492881f2a529aaa0804c9908dcc35333208c8e4bf0341648a037cc907d0ba5724b41d400cf18a1dde7a843351dee7f40c48b4c00750c70cd1008a015326007ce31482fcb9e0050344baf2004dfc2025c19eab2e3a523338711fee406a234007200d806c, 0x79f332400f52ad8011160402b529a2c7805498d9b5e008602a3c9062c631c687801100850ab00160cc4d2e73440209950098292c86fd2751290e71805b0cc84af98014a42b8262c46353a42553587110d80d10101b873b92015aa0c0984629350c03b402283d005598ac12e3dd7327c052018a94866c4035c010cc845028d2c468682e007c38b0acc6254f3425012850ba1ab500d9fa71b8432cabeb353e02674edd048055140802d98c4715, 0x1b4960708013493c56ce72ca4a06188350812d6545d1e61e31c001563277e280088c682983d28b12205f9792327b04cfdacf4c74b0958cc40ae73d6b19098778a6e7a243a0d004028502c131868647a0057a4d46dd004f015306d075404b191c025de88ea6be900cd964a008d0249b5e000ef445611eb1d870e67807231515c700617aa14cc8e1e3141951f02c6501bbc97f9930a677574009bd94bca831c3c9dfefc66c03694e80c51be1, 0x86df00429b127f4955375402998a85608079a4b11a07f1a1aa3638c8f0334081800e4c4a37602df80406c01c5b1959a7aad083328a4dd7a403ef65003b25003ba313a496b20525f4628618c129d870e48957e81386bc92d2195341a498693c10a246f12a836012f88ca806d123b18a363a92ca01c65c5241c63e0f0ccc50cfd08486e401430fa6adac3906c6621de8a3c78008a4b0c117c7302736de01d2626410423ac01002e801531213f5, 0x9219b1d3cfe4633f2915af7c62921f8830188173e35a96240c01338434387162ae0c7a4ae35ab0025f8004d5310437e112a62041641d00c67014803a18d867a002a3242fc734fe6312a598c2c03c9eb807698d51f9001c31021586134627609a4a592b0c31b746a4ccbce94d2625b35435069553f7c00b8c4094f1ed9b1218e006900044358003a63f4f0dd79865623449340d09a0d7b8d1951d6e065001253ce028129ae31a4648048975, 0xeb19414fa007e933470c4b058a803a24a0188090500923202f7c002a0293bbc95e866a4829cb298cc03f861c027bf840d8c94c67153235258c9580598138a8b7a10498b99e00c262057acb27466e23441253d345ad009101abaa90108c4a399802bc6365ce807b8d3122d9dd9009865c4bc49497821ee6d29edd51717009c78f417c194b980a35a3142670b0ac680304804a24dcdcd0010014baac093e62b3118d4212584e5a4ab995585d, 0x739c027a31ec8123294f3c1200634e98b49181087d97b2900788d1054864c001c005928667580368c50904000000424b0f76c64e6329067c6520d9002499505080fc94a4a08e016c314624a5348c781590b40803d06e00474961ffcd7123148838037c6501d71d7e0cfcce24d7e3139e7e247c01f57d00038628c8520b319203cc003d19ba394036a3405bd5a1d8080d5f3acd807434c7c020080efe38c805a40b40324634eb8191f0d0405d, 0x340152222eb2601e8a052f04c4ccd49890a4b4f3f04be4a5b9d407183283d75acc8010c2e805a8c95f7c00ce194b64207203147441caa404873dc5f6809ca843b1f014017e4818f540ac80314c6afe6c209a4cc1d4009a1a121c4d04600f2f5803164a0e4a3d3498cdef0953819497b8768af548cc8014d870e8732b8002106e41c219b057a01dc31d36c997d4636a81ae7e80749f658e93100391118a0427e9e6268628178b1889885883, 0x6b6b01b8f12eb4a31d57d1e030066056005298d07ef3a5818a3ea0e9fe0296bb238c406e1a4801b0c50aa57df6324afb4001400813ec07c80369e6ba3900a868900c33103280006634e863d60bc03ed53b1e60d009500042006c448f9d633f05ea4dd866e1a48f880021d2c6b88310055a073e008618e63bc06a208002d18807157a1f1a685e201a00342e5a53500664ce006980f4acf23d118a2363371c63104cc01d8634710802f19210ab, 0x69e014a0a2b50400f888449086809d30022b126392004631f184a004c62078a8c76c092733491919082e800c649e353c00700087fbdfed40111b89acea4c5922003d62618ba013432b8241e88402002001c28c51b21009b4a4a6473e560436a5a5021870bcb804a98fcb9d00701a408f000b6c4364ac212c0683e3803a18c536800d60248f480042341503c036c03b00c0032b108ca66b1d004b204090b254180216dcc50f190078bd50733, 0x7eb67a2b0e001763401792492c022898846c80da2510317194bf7800209377e280184628961807db124997072b3203034014c01308b800e125afc53e14190508706ed49ebd820ab633777b52c78c56c59c38f98ce22a982200d8482fbe66295bde0ba4c860d8807a80712f9530819fb50c76d831f7c6c04ac6661eab36698ddc73028d004328e01e8342433a2100682b5611488d2c03f006e31020a4012e636839803c5286e1c805d312215a, 0x12c19991e8854201b06cc038469b0d992f22521e0800254963bc601ca33d1b901f498706c5805d2521bc424b40043386f79234e0014007c06d0ab00118c70a7301b100dc24ea2be01157180188c4109535f10c5559c003b024b5c6a9cc34d15424f60656b440d9c24dc00400984aa21bca2146203f1196e80329de95798d362ad007a1a13504f8c43264b700c112681d3802a31210463996319937cba2e94836b0035001e1452d96253d826, 0x1900040026ff8431c050003912608b700278d08a1800c04a71842ea04314554cce04c42d06c470002030d014f3101a1400320410ff801c863671e3a8e0c74a0f44ab9282be4c0883372a1000d92784a9805524c8681001d4a648204e520100f2801e8c6aefd49580c7d8837aaf19440350038f447aec0288c410c6a57f0c5154100d6320bc7c0bfe92c32980264660f1182658c65aa335144a08c8e06560135bdd5324060e489727a4b1baa, 0xd24a08347005e035301896ac09215bbe138d050877fc132a14fc199c33f0721ff28c527b93d0b8d34a8430b20212d2afd16337540c00f8628ac58d868098c27006449e928668bc6217bc2198c036dd52ec32538b630029019aadc00ce03f0000015c66e6223e1c8105f9a63881942bb4f73062087411354656b34a06a0c6c78f014701a13b8f4b2336655e6c00c6ad5daa2b3d30964000d00413fcd07a315540c1f10c4079f805b18f4d32, 0x923f015099000b4031695803386802cbb48281081b3006501541a4011ec4d602401f80851133aaa804454100e301fb256091a6423b25f6a129c6274dcc98d5d3b7481014303b016404208a407fc6369ee803f00218ee001301b0b227b3631428404538c80a5300709880c5a6b5e007b50c0b0e0270ade37080861a63e040d302d3311e00424de019062059bc4d6d27ecbb005a0c51f9c61b3321c38800ec042555001500630cd007898c5a15, 0x7f9731008d001e864c786dd6b063a4770dc20d6538d9fcb013487ec8f0343047c0264c9cc2fbfebb0e04680000624bfc0a6be00f7bc1c7ac0387c9801da4b0b078bab312b033313e01310b40384c410c43cdfa4f99c3066700447aec6c2315871400d4656622323518d8a6700c00141ce4d2780422d754514c406721a0098819225a5d00e9a404e6803f0d10b075286fe12a652531af15320004020e018494c3330ea098a856f30d7009e1c4, 0x9d6c319b65c00ac02739685d20686470b43e80dcd19008901b04188208329722ddb5864eaa0cfa500c4c40088b1a00f36005662046c21fd0c50f69cd728c7dc5500060204498080892c5e297be062b12e80583125a56649431894f2146263109a8018c669123b5a4002233b9a140193dda140c6330cba292009ef65005625254c5002149a1432058c62504e403f4010231006c19619ff1226310392205ae93265e80684650356801598d61bf, 0x1e18c429afff43148dc41f0864ee753e48807519d005e330292001686360db9e2600243f025340d0ca45009232620d924dc6370bc58e0c6360f081c28cd85a95fa349983621e2c93d7acd019cc96297007101317d900af1a6055c004802973ac8c58628c41a5f5250df1b7a2c020a781057034d55065dc8090d43989918dcf3f006d61c487d1eea01d0174a480c40d4b38df0074a67994d01b97ac024633f6120039527abc4259e80dca45, 0x74a4044a01f032a69de6089e8806226a900253cd47ee1999a52d75a3155ca545e463672000b218a51fe002a4963fc400d631d5b7002c8c40b1700848d2d0050050621a018f13c3152510003064b0cd231a0ca85bd8474195b2045bfa01b5dfc0319292a3b007aa5220a88a14021bf84018692c14e401a80800d100398cd99bd561e0040ba2015c01d606a2654c40dbd00e118f5baf0a4d18a8e5ce2726313361d6e5258e3906f624f4804, 0x382b0082d2a01183346fd401c8c4a824082d98ac951033a01b0a0ef95204e06ce00f0c40a78804ca4b0db20076324bfc0006462072514e2cc4112ebdc4252068a212f02d2b1200b404070f00141258631b849a4f07c60d0a320abea45de01b1e3d0b50c680a046b2813816a81e032782b83bdc0264c7d0a71258a1580731901511004d1a030eb0cc601b7b28ed21282c59a58424b11b100e618a2b4a2da2633251001f0084c1a800ba525360, 0x1f44a4854e017a6307e7c0398636c9581010c5213400284961a01359a64e26700298c7e71e40810122436006402080a72b9801b49f003d06821723d90007d9f4007f4ac18ba0112954545436d527a2a2801d24d034e42ce1a5901c76000402c580364c4ca8c27a300ac2f100f202a049f0e8831b2a39f5a4c6c366cab40ccca45644549e42d8c73434e8f05dfb8c4240a00179880e426882313836644ba63c3fb800f06829c500110cd1b88, 0x7b047aa0d1405c001003280234654ccb3c8f190cb6301640040f1e015892c900003c926b0dfca4f80d93d734f318a15a515623340101ef60c52156970d807068901cd49810625da26215e120a2cc7e2d681370d322082aed19528423c6c32a3470031925866e805b30e20e00bd619bc6f6eada01d06c8012cc4c0ee831f80d5d4d43dc4962bea1e1e00f20510a780180e69a440c7c5a6003031a3ef00750328059221d4c6e023ccdd1881eed, 0x1d18a22c2002a3542090ef18c42f8d80653121c8576ae4a58e5d342494e26f8163869e2d3254a8ca42437cfc0270d12019e6207980cacc08202e806c8091faf63403244810cd9e92d573801e4c408ab256900a83589a377a68c8c00e092c5c5c0164c9c599803818d8fc399e000e18f200620402770d19807e93e420f993186351643109c800018036473dc0e007863ba24aa4b0656273b321b04401f431478a9a4240851bcca6d8c6d883, 0x77b261f8b5afa4065800a00088082a07cf790cddcc000bf61ec0e801f26581035b38863a0cd806b98806a900914a01746a80c64c0d32393466e7288fa0006c468038701ac55f0b2a92c4f3403b464a74d806d1884abe42b900e8ec2b9683378010038c06c0320003004580c0c2f008bdc4ca7c01f313a36c469cc248018988171e160d31fb244ea4ac3840320034c7ac25800a1881baf00bf4a444f8d394f4428824b4807a1d680228ca1075, 0x51902c943e01740284bc4ea78050da9aee6189c11f00841ac3cb113200277e0124ec654c13006c8130a7423e53103a8407d063140a8926063e06246608ca465482dc49f894ceaa0011740d4de067e93e00f780fda892c681a1bf84efde337337990dcc7ac3800228045e406bd90043f0133a631438082250c406fc005f98813ad750d009aaa725ac03085fc970c064ae73a959881239339200db41b03246201500056c662e32491718fc4a6, 0x4e4b194b00a0b9a008194c03c9892a12807a0cd52f45592004bd76031634c8bb4102925867d3f0b013d55300ab31a0e88633a04c708834fd29298fb4eb8d09c8a7899004347402ee3400141ec84c56cfa004fa4b1d4328ef61fc6f600b034026149780092542436a0c5081449a81942c945958031403002480846dba9f38021daa00f43262e1cb4ca0276a9dec4d286dd512a918adef0993b3263712ff660356704019cc405903fe100a80ab, 0x373e02693ec9350314421057300b4670a4cf809d27c7ca39280a64131893d3c78c94006f093806400a9e4b425900604d4004c03111fe4c04c84a75a9e50c517758a42020b3c00100f545d4c0158c4a862aa8a8044d204f1f18a3382010a314503d35a40648de1f710c7dc73359d1a19e7f134693d5a200db006aa078057810e3d8582b00f839064509552804fecde96728a1ae192ddaa00b0313b4ae017064822bde545878c03004d24b138e, 0x591958f04fefe010698d3e24654103280398804939a801a13f0000663147e3a13a5292e31ccca24b15412ca101fb54f0cac0336ea82450c6e197415a0c6d4737eaf18a2be86072337648803686869e1ba3300a11996b7c193ab3801b06486995d49003afa8258b18fdf1b92807a424b000bc6208e2e037069c1033b9f25213607f7f3103da0d2ce3145d3d0e70690a833d39bd51ee225af49a823e4afe33544643a49e8835d803f2551c4b, 0x27ab18a09c1005e64114c8039cc400c836d500d5d7f005a4a41252076cc3c321cba9066a234340800a1bba0097198289000aa01304b995a069e7b932bd193c1b300094a1bf14db5a655115000c18902ac000d18f21e32cf7019836677160096a9c0380c6850c805300f5903004d624935c009c64033c401486289c180518c50c5a00b761c1a2aff92c384c75ad246283ec8ff10021a890aa519bbbba004092c412212acc421789cf50c521b2, 0xf18a0c6b0d3201c23ee75700223cbbfd280cca45132f3198f1ecff063715400178010b2b04470cd9a2c55df007839135def4d7bb5d0946682de96c500f406b00f9310226cd5b20430ab40350080b7d80600c50203002a18a3c42002c6374631480809c2bdba6824f115e0037313809e017e9424bd006c4086002803a0d00b1c86ed31ea9b058500406164011529894a80950c9db96420c024017201b4c48760941f4c40653a79380201b1, 0x48902139d3225234e6a74915d266f780073803c349002301806d4e3806553d28004406ca55ca050021e7c141731ebdc401ba9401e9a293409c8ccc0102534004002a321483e003492c427000dc06227e494201091f16b3701e85f2000c92c708e096cc9a2d6a5210048b5d005149623de96269482a940188638a4518cf8d2d90200277a22ad2017ac381a4420d926ec598202252464400ba496108c00b262959ce0bd06825f411a48c5046a, 0x3af3194040c4bf231444653acc03b016487d98f0dac0135007a79a01466204e28009d260022007e98a5ee800a402700c859783281824f7946508e020b881317fa299801f9e4b18c601229b8014c628303c5709925daa007601b1c9c006a33364ac00612831242ea7190d18c2caf6200cccfdae92c14c801c0c40c06004e30e0bff00f101506f401a463f3968b240668b4a8c2da508ec96b4d0040188015404224f40040038a19bc0500222ce, 0x5bfd013b04c03ae02b012e4938c84025821424f638780b70270990010894029d4039189502fbdbf8c519f40076313b0bafc380377f08c47cc662991d460c5041090c13182466d69800e34a5f4c64a0002005c00a5ef50030496041c298892d62cc02ac06b01c801818c214e001501e9176b88232b154003ec020bb3b33b806e25d001131020c925ea35a7398bccc010c84170e0045eca10160201331307803306c40020050c6844c680a0518, 0x7d2a19b8a64ca2c34f7f0869280107ef8056b13c1c811ee18fabe913ee6202d7421a867eeee8bed18cc814860c18daa451b9e0274f02579c63693e09e480211ea00173272e40047094e38d2149d27c5b19414a5095f0652918e97ad04083142f5802d06288fc806bbd10809002c499422000bc0364a8e098926ea39ba3498dd9aa001032601e2879a64d60880285e88a7621ba802053294dc1990f2695bc64f3a41d044c80c654324193c11f, 0x6459496218201e404278d003dc654700809c18a476400ec320c490ebea62132418cf129027a0d3f8c516ac452f32087382a7e05a05a800e401054fbd99012d9574f6101406ac970c31b7c6e3d0c62b150002cbd52366077132092b2015c3343b3cb0bc08035e160280c480184b831f823e0114627696e14ac056f881ee30ca40530080012960f05ac6201cb801c40987bd002c0d006ad00f13199c78f994f44421dc2a406097d00db98a630b, 0x310b19b0cfe04d292c070a7f88038701282e8d08bb8008a01820640038008208d9368086c8100450c9d1c30f67310c4540a220597cccb88d25a323006c0108d1000c20043ef8006c93c1c88963465312ebd260ca09a91ff01928366017e949006c0274026b560079015149263ff020aa068c1a00f067c010dea828326508c7472f691c0210d1229ce3141031ae7062887d803c988078f8c2f0211a38038a3146eb80368656343b56b00a4ec9, 0x42390082262018e0437aedd5d00260ea2bd58c9c34931c6008ab84281662b3018f41c081048c23624dc53200f73182256d1ec34c15852c18c4ea398d902554c2707d900dc0520ee003d16a5dfb9296aa0800bb12567a92ed32608181da2c390721a7e40860d9804d8c5230500f4624c6db3a9431f6e44025529232b28eb18811b174df7aa3a5f296664b540c15c46b2cafb1048cc5c76002e1940e5474206200ba0b0146686a8805aa4b19ad, 0x510243178e8dec3f3f746cb86289c6800230e1913001218ea7069eb000805e80315ea8a8a800a80f073b007418e80d8d54c62002e66a10656178c06518f0ee100877a6a4dd3386314011c00040511923d71007c532007c18a3c74211325473b8c704020ae100e980201c2921531b11c331d40270905e70de90e5b804e00d10ca0dba4a489c0008063557a1f1006841bbc25e0c6e1c49ac949605e24aac63f7bc03698c82653c19e0d384a7, 0x3e501a110e0032633824257746502c0cf94a4f4bef6bc700403362c8802b7aed4ae0010014190c190dcea5d6c0090a3a00e43140a3c044863aa66279a8c761b2428349ebda0015c031865801192586a83abc8c50b9900fa620b6ce00ea6203cb0e9240106ebb6ef00dc2e800bf18a2396017a04042d03fbd27a5433f4c310d9aa029f49929aa985c04b55ee1b54066aa9c0040ca4ce28ff031eba5862d264f324106cc022f5808de9930699, 0xd500e0152d37435a0e24eb1009e2344d5a009c00400ed19abcd400de3251bb00a14669104003b0c521742e8d3263afe018832a4a6c70e4c9ee75007424b14040182025c24e8748341272cd00c656ace003e01260d96a404962670f6e6314715608052b298f80348caa196909319aa79d30ae6200011199c03e694807c30e592b002e49e0201051ac3816b6120806c3b0b4ed80310c1007300e33fe05ce31e755996146510c60a3c18ad5ce, 0x618a2a8a00be33547e6146803c5aeb1cb0c9c1e1014701a11e2010e6350640025863afa231258cc623800f762a032493f601c6e6d87c40670e24d8900a983702a10042bb400b403d18d596c869ec8100970c51819353231bb7c264e804f0d25f3cc0528ce9ed699212ae83e849ea86801ba0242f3c03a8c7c177bf838151fa7002c1a11408400601141c05405266e318ae5816835700161a12abc3070333203802b52a8601248b0070957, 0x25674a01cdf0266f442d98dc7469e6030011007063d01cc193a232f720342001414480b2cafb648196496200ca496279e04f031e22e5eee001ebc20fcf8025fc2009f312bde8fe580418dc65a0de88c1280323d10015688749e42a0d77c008541a7dd807905c001a8c7d36a269b1a5ab9cc0d4c38550403f0c665ce806480de3d8547a007c388f51e9490adc29d4c7e197310c18a0f4e29e918a3d77157631f5670928de901590059a4f06ba, 0x632392a48111bdc62074ed4da005202580630c508a99b5f015154c286a01b463c5fd4c7e1a2496d8ca835e927e1993a8401840585f6563ccc402a80016988072f8b46195b8aabeea6270904022c656027962280f5ddd2c4e49634b08ad433f0eb400e86b0fbc4bf68c69baa5b5c496b04c01bcf448e1c005067822e92ee010824d10ab025186200c86202d20025987108a4fa5b0e155353a319ab57663ed2500adc0124c4058581358cd1da5, 0x8abf1a0c3a0d7a4008722a5b4806e4773f25988453223c618a19c800ee04355b803a1290173003d80fc04f7a43009b4ff2aa002815ca3e8cc82860804081016e47c0c327320400ee00d107d29dc054d23bfc70100381490618a120a00969374f0cb11d872234023599040157ceb01b3a7c012604050cc0fb4c40d90b4de80a50ed58f83103ee0011af447438033863a3562504bd1207200b301b37b7320604f6a9e7ba8c4f21fa3168ca8333, 0xd900f1d8d3d6c94d4ce1ae60010aa98ec63d11ee2427b18a025c00463146b28c0ec066baf000ca4c619600f462a02c400a6342061402ac03a246007c3d11eb3007301513a8015292c4bd159dc03ac31807f0cdc04f256d49632453938f44014cbb052865eb3f2a00d579700ee00d0cad009c31d693800a9290e779a8fa4dc24102d5310426914343275e1153c52984df0040810954c1c0949ac1867512649324002b925a027a469253d1ea, 0x71e201e2cb492ae01c4a36502002027a14f01880241955018ea33a009692c6d9d95a0038ee6c21e00455534caa4a09fe4b21e03f008c89e401e01fa5bda4b22a0006b7aa377ef8f032a0b4c950528608fb27518802c4028e49f809e012ec3c117650006288e521ad993566f7aae4993c104db0314207e0df4c40ce11a281881abb00a2019b4ae63e801e7681f1924a0f47002d18a157a0148314acf4d038621313818446284ad4309809d902, 0xdb7195a84ea96834c852a170c026c241d4f988015c97d702585f2007a34c2c30a544628eee87eda525244426b1a59338cb8c63d79f00198638d7417a8990ce1a79f162433060a3e010769408f866ab563ea9807189f013501b94a0e63604f403003e409912604fb8044e9c89de02612ae018cf4810f881a5870fc5170f98c58ce004600419b400ca3412024be2862805c89829882029000100e2fb3070695574ec95106524df16238cd47e0, 0x250131ce6005e6204a8dae140104bd25720d605bd7d5b3279ee40eba03f55ec1e29e8a675be2aa535eed342e320841ee55325035ac4f28c7e3c7c31a18fd77f001392a41500a5e00874bc68d069e343cc4500ac42d35d8019b0ee002002b6a9e69da4a0178cb0000d56bd85bd4a44412018a3367999df5525aa39ac8d0cfcd2900df01b08e260ac00f64898c8c038ada3d7c99206e892a8009a79b20946326cb9e83466cfc0001424b0682, 0x3b6020174d24886367d41eebc0523f04f4798f50a26d2a32780960050c38344c00ecc9c356004224b23ed00dd3201e1c00e4315013c022528628184bc18c13be342a31baefe00de3142f30004d26888b807598f0f0d25c801b0faeea7a6373240002cc90836800b8d341861d20620ab9c0566629736449ecc40b7eca0424b18b3823031b8362adc03377b401864c40f74434980d81f8004249b33d0099063788a935600128c7834a00f4c99, 0x3a91942c2a0acc0086fc93c48084156ca3c8d3143600e44963144f98cc3f19181e19264c480012810969600d40043ba326e60133b5e6a0589af769dd48070524002f31a09164e1432873a402f0c5050d3d03a524a8400154aa23ec06cc64865fc0d3d878d17a3c60c5180500d81944557290202833840124c6076a00069881ea148b80098aa066003370eb4751cc40a81c94180446c6218b1ad3ffa03dc31d5fcc525863ef5dcba92524229, 0x7bfa18a08d000dc6293084033cc407f78066988051a2fb7004057a73ca00832a00024665079c0e12535f5000be326101008ec31f124dd81069e5f43826bd261d000ff18a19b4920a3154211fb046831503abe190c1b301b201a0dec003803120255300c9a1a6000ea509d66805a92838e6011c024177ce2bc03ac2400608d0e0908246314abf2ba9e34f047c08986370939c5e9884241006331027a8b15a01e4be811f4096d53aff6a4cc17a, 0x36024a3de01a804c277003e4698f2c0430b0fe25d5e9a19eb8ecfc7662057d255cc636842463d81083d402b301fb0eed608036691c01d067816e981b00ddf1083bc4ad30c600f8f4c750618fc656cfa34dcbd118b0005f4962706013c01a53c8d7b5258c81007b80462df00c4326901b20a86248ca96f85266c132ded250d8268e83310ab9c948834c160628a86388ceb299003d50397ec3241f88018ac3d8c2c007527abfa802f1881c35, 0xc12015a79a00c0c381082096867e47a000a24c5b6e005302119be008a64178a80110038078cca580fe1c51fc0194a1db153c33e874191880848373fb08c7e00700463210918014463e49b801980106d5415618cd473004702720ca89e00087f800044020e9189730d3152742d949607fe01c031480607d74068a22801100212d45447626b8c6f70401f6ea801fd258f81ca5a809a2a000ac192a546c088f4416b5a168c40bc0803da4b1bce, 0x781100c804610b06370570569862906f8008a4f432d06bd4a49b5eeae0012896a19940103cb928ca50a25d6df53218096b0586373464025d2582e4007e8c5231d0136026b2be032e034646400e0c6cb2d9d008d01cbe13700098f1ed63834d1918004de88b8f3fa8b0e19c17f20021202600a29497ae001512909e9802400381a3897831012c40ec604108b800fcc6cec684dcb121880499319ea7ba0154f443ed9ae4003644e000b18d827c, 0x5662a28f0d30e01f3f740264c529da003e80203e295dd0219e4a04986407874033c06c44b30900c508e1743200d03a91d4c3378a81ad04010596a5a380784c82e2e4a583a91e783420e240384c4006f01ef80d5cfa006849633fc4aa60082f7212540b0373359c8025baa582c0139a320e9631c48d8173c65600242be00a5baa411b7a5bd952986c4f620ddcb1292aa0ca98804486982d6320aa82f95a31f06c590240104772fae18810ed, 0xc0013ba080e9e01b3cfdf3806860d8a5c4b0e08f43acb4a5b4fe1f9c34b7774d7ccc6d1ec06b58020a20631101aaa06f35c63e670c00cc6291771d3e18cce407aa802685e2a79c63366a9eb38c623c382e40d3ce518d901a7135200ac04088c5003925ad06bfbb0ca9f80148e499a78601980362751ea58020a3e80310cd0fec00f21a7267f047e6207a39efa925830100d318a418641893130c484a90620446401b527a790031980d235f, 0x5de849e04b001b4c4943fc8de40362c63f6a3120791176d31300ccd79601e00bd0ce0652802929598d511901b94a41d6a00fe649329c929c628c7e806e8121c492a5c02185d0016833234400048c6c37c038698c41cd54061a607ec00a200812040235292728374e98d987a001701e336a862e33706c403140828490e7a8cac6c2007e3141d9e039c0342b527df003d1bac8e5995560251bf31b894c006a028016d4448c4e253426880fd902, 0x681a18d88d0fcce00f09040248054283800f80744d01fc81938366835601b257001c526cf74013b9880a45437149b82f470f631f1540091062871116458cd800500d218a00d23ab4c398711b78806e8c7803a18d4e34234301f8b1805943315c42204cc6e7e2008b18a484600d461e0430eaae01e8de52eb127ef8d80651909d7b0057318a64000d492c1d9211b527e9de8020007cabe0a5e19437ea01ee34c6c480128c565e2804480d8025, 0x3531f8f0400880366f40f818c406233a290c51506000618a275a01106300ea1f080c9a32303e718d1236007b19f8a062d4c6432510020469c4aa809898a4d1805cb0040cdc01609367ed6504066e0623792b0f0363387f0131baa69be04b3945f4c8c56120bf5718a01bd009400819e600806310c580440668c3a8fa50c501b3005b7a2b257176a93e014c04f12605a0c9f981388d506ee19aad6400fa3145a7c931c066f782aec003dddd, 0x9cda0089e4c0922949837401f8066281ccbd8134550347e310937caef2314565c01e466aa67897e8d315094fd0008004e00ac937013e25f46570020063a4dd92b14b61a187aa22609357a1c03e187056397348d2c1b35498496008e0014c385ab801b18a8940832031240ec0070318baa0016c62079a88da0628f9e0000804230e0058026037c5902f486198a66c6282a80003250c1c2000c00c47b4c21893f87100b9c010ef79a670cfd77f, 0x20150418016a334200dfd400243ec9b3800d980506a092a159ca99e64d718c0fb406000e95fe8cdcce282e6025840c02e2328083402f406c07ebfaa80d833623a11998b1801560261b923ae007e0560ab9993d6f79a9600912c483a46545a6002d1e910a7332398859229f08007055a4a66658618d3fdc6844a8039f8c5446a4460320a9373f2601110040394c64a2721120ca1cbe00d41a1107401fc332744435ad284a562ca49881338, 0x22061a5937c0650631199800b1e88fbd35818021a7f061d18a182200e802a32b000900110f506a98cd4c1b00df320972a63546268dc667780982b9128500783643b05009263a947c314337800118909e3ae840c5499c0064498b504617c31b251002c98911ce3ab730e1da084c500e00ff2b8c340160629f80682b9297e00216bd988e3103c4e001a93c6c9628a4ca8949453f8031338003719421d001f003d7a24005006c4a400508ca0ccc, 0x2e74aa3255141401018d26a6807e0d880369881f4c002500e985c0196c5475ccfb38010099800424b1e54000118a24fd34d403f05e9fa71e88ce1c49c98a1a8c5376004a78001a26331e09de752923973f7619555b70154314c118959834e59280778020d7a45090cd18105dfd3219920d6303145bde5134c86a81ab4180217103a57319aefe00e094075e800300987bf80090c51c5669351a10b0200666317ba67664628af9266224b1976, 0x855c1a1b090d7d433734f66864c4c949433280d12bf005219a3cee2f8e33746740195298b5200303d114574375315b0450d760117e0000b00844f9a7cd0d3d883862818a164b13f6c3f0478f644c5278f35940020787773300d90280022948754c016cc691572f93b0e02411390313be3600b4620802400240848c390df00211eb00311a03b4b25e4049001000d5258ee7802d8c51d717408498381a016c03c3dcd8c05296a8d02eaa52d427, 0x684100e0110001ac3e34b99290668a1b3a2d00421c76bc90040bab344234d6088b07009240ccf8c80445d54b9049fa8e7314a63d6f85090d878950003f0121316005c31f3d0e12bc6210cba07400904daa2d980dc2ad05c200432bef9ce0366dbc00d4068f2632d5312048612be32199d612ae63612060370c9ae39a2044941fe0001e1953a11056a341550401ac01029b2e900c7c03f000e193b244d13663c02b92454c780d3120e807824d, 0x8fc04a6a182955a63305ea6af401ea39919e988147300f2195267e01c2c3850712b14026522a5cf80c5a0d00fc01343e4092a31f0308012d25a8e192f68020a9692fb01f894c014634c0ae9b214652432001ea5603a72d0918daefe018863d46a824340108cd01038ca198b34d4310c4ba0036c497ca898900681e30b730cc04ff8111327b41a01266201205fbc406d1babd9418859f4507d1a60a82e9ce00e5739d6c463e0d9af9b0c9c241, 0x14e7310094c28249335738029065266d3e048c6c17a0cbc3103e3601226333e958ed4657093805200c0d61003401e802a2a80033509c17bd292634001d24b1ef424b0499c3880f32c3940302cc8c7b0b63a6e0cac1d494b7318c43609203585ee8cc00c66d0681383d5072900c8199174a017e31478f80040c40661b2df2525c7f38b61ad210adac8011576803c4628f94cf1f80fcc405d7300997ac006e3541831ff90c6c5419c7b1880647, 0x6c4963aac01f803c7530b9ed896234202498cd5f994457a21ca200560584c488e74c40720000f18c8de13c0518f980cb38e31405165474628c65005598818a74afb004394c00a4c4c0e9e4c9cc9a8609a6a18ddef07d52194b090a8fe34d6f86534004ca7e00688049318003b3212e41174493d014e4801e88e1c96209885fc26f3f31ba10ed2b6c380478036402041e051f18f5ee7460a18a10c8011064d03b25b3c63aeee8f6798a4654, 0x9f5818a03640fb2621191c0308018a87cc57013899d5165013b50cee9a31f205001d4652d78c516310dd1280e432685e2c05092c44654d8c6289c380541881bf469ad49919b0c9fc62053f00efc066e244199bd1192b28a8194abe04bc894b047c9afd896ae7011e0cd059700bd7aa30f0e65a643090e19b4010200bfc624b1cea80af4a7007ed7bc00871ca007d286f7818fe8d522b0004a319a4213ed631d59a4d6586661208019a508db2, 0x6bdc18f056e3d0a0376121ac94666792825e18dc243921d3213980ca2e64c719192e1890ff02983802478f00974a404a01a5a94969d401d9258b79800318cda5757cf00f980c00d60080224013c681033213600a80472547496023e5a50008570954fc69cb4ac9385570ca7750d18e154c020e9492529bd6c0263cd1ae4b1046474fac31fb888019c0086524000c06008400050d08f5907bc18a1bcef6a693c68927490027093cd13809c95c, 0x66020046a0186f441a4406300525ffcd272521646003d31eba6cfd226423388035803c9ea3c5118ace1a3f6418fb9d45d4a333567185ed290b8ba26e00a81e500a831405f64a66940083d4901282a4dcd6aa4b1eed00a9015306a00aa330141a03e869a73300238d085615dc049e84b05b6e3276a192ddd89121f3fd701053cd6b5f0040f34ca1e0103545af0c686ace0027004418500a318e2df262f001026a4e9f06382b904882508b8c, 0x645719a39cc012a31c38b8003c63ae9e006e0091102003749e8b1eff6000829300050628196806a8109f4d008931b1a2724f264264082b1862a762001d80708e4908f01abee4a9f004e09340391e8875d80640d0a1c600e61a635aa0370333338801000205e4b42b00d06bc2c1501430b26b3a3347988b0b401c748171ba4fcbd6005b31a2874010664c522a002de88eee80050d083f67496319948a001a00e18d9a05466e08f00610c50ebb, 0x6bd51a4486cdd2465a28b1fc480231bc80208cd20c882c931fabf2005c3145cf04b40098f0800a48c6e25d037431b957d208a341083c01d0c5035a80460d240ec9f4401bbbbb34ba6556709b4800104024a91004daa71d8e320a4eae9ec31d3b12143462a79f80fe98a571e00441ac2fa401a63288c90ea58628c7600b78cd22fd00f800d3fd0c6e83147301387463efcd1f2e0c7cfc434b231039d4031004b06c81ad8698f1c407f25049cb, 0x51f731b9c8001b0f4416d9d478c6e0d980420d0a14a00d049b24573fb80486078039926a17792413150610846b1959338c3e03153018038401083d002198cd56e588a18a459cf44632749f2714d292cd235c600206661af9327937c6ec001174bc0364c4c3e98ca5004e2ce5f174a79d204ab2335733c02b007b03a001b188137400306212bd0fe043357e68012c690710354b98ad4fc00046242d9a01b80087f5c01606509c980268d08b38, 0x9eb301b8aa0079c92c7bc1d401292a1380471880568008e1942ad0f5d4620733cc7cc064cfd3ff98049ed07c1419948572efa013715403606287cb3dcf0125c55186401fc4ba011064e37318fc86822d325f00cd0a337efd4a400f524dc0254ef4006d2627acbfe581083364bf931ab41a00200428944018925916baa600105ddd0005193973a6e1234f0721a2e864efe100908c50a45518d4a4a77afd040366a927ecc03cf68006d00609ef, 0x16e61959ca2f0a00083360000cc84d4d27450d0c34451d43104540000c94d1a0977c52669dec121a4b11ea407d00d807ea2ec333390000f40b02e1806518c5ca500c9310271c01f6f5422e9ef2c63ea83014618aa415987b3219c812b3e33757d209c067e1ea807d00f462104c931b129a019092d140cea1c09ea81ba4580758ca00ab1951d560d940346f454a340670f980b280d242903783101724f7c434115e629ec09e0d9becd1925700, 0x280068b846c4a027463dbfac03ca2280598cd883a7c330198482f8069371918d73004e323cd590c7c2f1279032181f801d262a344c06d80691178005810051f463f00fb52c01be620846c4cd52663c7825e18804b800bc19aa0a33f30314678253d4098293c539810107172d919a94f2018cf448addf15469c8f512be809def00027314b98cd1d601c502c9db8c8498b9285bd1174100714a0003ade8a955380803c8c982a5028b8020a1f, 0x8e18f22ad35160080bc4e284c401970f9f004618c09204a51862030e340105801dd258689ccf00070356804832730ee012493d379ddfb0c521a2484119342c4028d00416cee806031245403e8650d859fb60c6c15c007e18a39b23f5431415e400c407e3aecd0c80fd47364bd19b941e01a83146d780080010b52801e00ad18f2f4d0040b52002864c6254b1646523ec9af60c7cc4e00d719e9526011e9404950b070048701211da4b5baa, 0x928a01eb872002e3273e9403d0c60163004298d9d7b6b2618a160608dc036337dd7d003ec38073124b4e907b1800faa0c008c6200eca51ac684a2a1ee08c50544381218fa84e006c03272440304c6a20918de989cc9006a5320291403cc6290054b0d8648d3184e1a4c8e0200df31a0ec0f8909356e59fd7c010ffbb8c298f479700b018a47950daa04834f47cc8628fb821a524b02413dfe7a20802a14231482e0005929a9373a1eb0e184b, 0x54211a643669f9e04f26700199892af9346e8d01c8a92a861c255800dc6341f9dfcec65001395b6190da0d00a47a2238e00646205ecc0290050a871ee8b10d5538c93019452601ac63f33ac00d466d0d982eb80a139e00107aa402075baf445360035cc68134807301220a802cb32447bb0fae6552464073066ae70380f80fa1d025f03100f26c44492c196d036466e672005818a4df8311f3102a0d0d9c626375c00b466312a006230e1617, 0x7f8b320bcf934a064d272cfd45260785ae5c993cc063a7819eb1d8eb7031d8c053c6c6289e6818c24c99fa7c4901383630d2201b5e124bd86828d8b75498ddf50007b49638d43caa01e51aa1b4dea834c004a18d23eb7f440188046fa746495a11772cc86c38003080224060f5518d9028016234213f1ef7cc68ee68050188095d7ae431e3dcf35063401b19d6b0c40ed543648cce007002e008811289f63418adc024407e486000b989c65b, 0xef49620248f8e01b0be408998a829e10ec816856f00450144498e72404f1005ab7867e15681cf802030905200042e9e0190f4b70e67a7866e8c780420ca045e008c19faadcfe5e0272915dcb52646518113b0f868b7c471a70f12ebfcc386cb8691469e4df00d0a4c9b0713c8195948a5da402b14c803acc942f2ba01010cd190045310398c010833f1aec0150668ccac14c989c1b1002d3102c5e006cc54497c06bc628072007225310d4, 0x871a6219784751c02873a403dde90c6d00670ca8e9e0090624388a320434f43f402fc69a02ebcef8c7c7d9007d624227a0046314107400ec66a30980568d247a4183c32711fa00e492c455911ba4a0c02ad0b98dc2ad820918d8362008e63c53894d1c03c156ca07806d5039dea32a8bca3ffc008816090c0056234400600a195c642300eb45804ee94916c9fc48068c2c9a681904e6f652919faa07137a3146c70b19404ad538002a5521eb, 0x4bfc1a1be36639e354066c9dc525898f823381086cf04c81943710177233746c64308020b761232a4cdf1b35220159032015c93c7c15543987081500540cd5fcd72904968c8e00086488f99c670c62bcbbe9018d9848002561c26a8012e03338f04599258b170012250109835f501eb7c211fa631174668692b41079e66a4c16a18488014a79b045834e40c040b86863f01d398100ea200cd00da786fe6600c0f500164c408ff2ef13120dac, 0x178004209000120363e792bc06285f400218c502e400da19ea0fcb9b43371541a274c510c6213b00dd50600cc18a3aa8018831d4a8defe8c411b88bb2a4cda5b25ce19400da00c80297ec5aff40101a64548bd15fc27d7418eb090588c3297dc0d47404c08fa7c90c7581e0cf2319ab9c019e314796c582066ead89f15a525b7d001c4961e62020834b30180118690f7d127080ccf3f982b18e2ac8aa9401f0ab40348c6c70fcb320c5415c, 0x5b013361c518431f011e41e0056208003c0d2636d612249608d4dfea31f1f81f700c93180349901300b94e9c49fbf143f140083334e820024a96004f18fdebb59a049f960600e2c388db551b86826034c6300fc241009d49ea66601c83147009d5e003ecd514108c79338289d31bbda003f401157c80b506560d90021802041d7128319af2ef89c93706c427a00111fb2ebc8c6cf72963400e4502ec1ac4b337906a98909b442c98cdd848, 0x2ec500f036626ae62187100228062d413a9b24b1d0392a0195be36ff6d25423c0978803c69101288c71f8500cc31000d2004a04259d0d80863a4324626809981f01cf00d97849e98c5421b641c0c78e5b92d80d04e6f00fb310487cc60294934e802e589050e82da0c51bf2827331bb88855fa0436704951865608fbf868151abb003c62a2e90f50403c5e20033529c9da3ae1002052e73b332185d001583147a55d71806eaa980330cfcb9d, 0x928c18e482e01d66207f34ffc863e4df4cc901049157f3201b06c9158831d3101d7cc038ab24544810955002d3313a2331b2262070b4023cc50874007d30f0338838649fabe885e631449d401b4c6494584cc98d9d0900bd18a2ce682b001e41ba09a0636e220032b10df8a86ca01b2cd200b0c5460851e4062809c80848d0125c0be2314c3b483e52547eb803c00629c7494d0ca53cd82cd310210e85e831f7f080398c4f04830be30e5883, 0x837a438e0c1d4643090402c0c6a73bbe5f98ac1b1652300fadeecb0664890fdf1b806407e004124f59c819ce1a1a1fae6bc3594c7c19640103750030989dc2d3cb919f3c96005a0420094c4086800f8004bb138412003f19f18c6007494069880878c6ed4b3f8998821c50045021bbba01be328409c03c4c522e6bdbe803cf720147199b0ef241755c3754273cc86197497701000b9008331f8a06ed2294b3379d444c50c248141a4c8b6b, 0x6a310ae8658f6f4877bc0098066806004ba4f4ca40040496226925e00300eec010066098db05324b17849a8e496179c1dc86498768013c63d0e3007b8045af97b4500f88d001786204cd6493003cd75414200cce4089c401988d0712c01100142570010db2006898dd7812c3118ec6e2004e620331d0444098423806db0e23f6006661fa0190e7094143040794c825858ca20075eb000577a21636005e63d1385207063eaa0c40398f4565, 0xfe31328520ece6202af8f21866a5c915a90cacce400bd18ebacce8cc949612d5030c9adf0b82f80c217571c1327869800d404252ae43e4c48a1480a88ca1ab84bdb3141a140016342865a23d40261743fad0d2d50325c80189ca24b8cc387d0803718a8dcf4c2598818222d0d18a389800a4637463c52ed26299c3c0f003d11900c40141dc603e403f01b402cc0a8869c06419616bd6d6b0040a1edebc01d38080019290ca2004e0c514cc, 0x5f823159d20935201370e9d0c92860ea10738c514b600b649630be59ce34846580a10ca8fec003c24d9d7100f2194ba7801260081c6649b5e881d6807e0cfcfa50052012012a01143333e95a6680843b0ba09b12d506009262427c20956f4486fc97bcc524df002d8ca08e2349a195c44201c86208c145720c9e62700f700fd454013a19429fc06ae3140c240248022f22804980c540a04ec1a0357001b83345f080045e8885600638020ad8, 0x7c2e19aa1fa018863484dc01fc0507a3124a31200e100d4626ba1c4a3a031241411bcc56984807281607c749e800e03ca01d663d8540018d2791d480000cf608c23b018d8b180d2c9496dda30000648d1004831213e3219a18a23d601b0f4418d4cc1463e956013e0c710810091020245e031e0118c749120056aa9806c18c44540059312b99a002c3280330aebcc66956162098819c123a90198b18ea54029740c451d8a85d9495c1951275, 0x2e5a01a205a021c31d4f3d4f0c628ef6c50c98fca459f3718e964a008ec482dfd0525290dbeba6f803ca456be000fb4fe008492c0bbcb2fcc60df300c480d10b4012231e1efc005c33635d002b5258cf200768071127000318a3e74710c63d7b28da78c4ce0b06688c7dddd3a95318365c01c294e86210ae809ae2a800c31247a4861000f1a52f9b801b05e80318c62271006a0ca9d545e52025bc10a6e633f3c95fc00080809b7a580745a9, 0x8995193ae5201a40113ea4a26187102fbfd3007d7846b290049338016e942113c025469ae4a38ee989985d009b18a276c00f83147df230640107d8c52718d98900084310376200f805827700040c40b0bc96725058831dba31bc38802dc334419c02bde90f96805824b11d100fe49b1fde01a66296b2991c40840559717a550e02000a3100b9a01ec94852b9eaa1278ff425ffa52192892077a22363300604204f1e9b462a08f976f98d1d7f, 0x7bd631038aa165804d8824d22c066bbf9ef80021b7d572300f903258e201d6705608005668ccaa1004dcc06454004085aad14315011d9001e88bdf9d60989ce40002d3139c3acbc063247f4014587ade7078318d094d8e0e18a3d1a94ec3300f5002a46363c100718020d205e277a5ae824a9293d5d065330c90e39c0161934fc4009c01ba0181c2494c30861970c6298ebee500a8bce418d0088a88c370c38871002ecc4075b00528c74568, 0x4231b09190e4264306c946e4c401d6ae9c004c99c00e832631a0f93231505ea70d9e8878f3f7730e1a8900d461c347a01ca632857d76f063ee1c805318cd00c0041310409e010631415a00a8926429eb25b803c4a652ba00f0b544baa92c2a103034c403130068188179684ab19297332414f545ab22ae525a0d8807d24ca184241c0041dae01bac3937364d7527ac0f80190150a3900ab0204852939c31f337800e987e8e1804d98d9236, 0x553918eb8c800cac4e5e28d87005643480890d2c6cd9f2b4aa9546008a03218d8196927af44aab080c8389008031007093e98c382b4803546663c14c07b10c93c61ac31fc38801d29434f0c3c580506110334a4d0c5d583a310388800100317a240824668be900228d04d1874db3108bcc00900081e319218c8447080010ca45d08af419a210a48acc4c103c0348669051804400fc28a000161c34ac0120c3831a0006466b09e8031a505b04, 0x1f11a6994e01d294201b002fcc4ae82c2a63d113cd009249612b26b5c03d39980f8466c9a9bab2007884f3d1301b384401f86203ace12a8c66f8d80498d30d0f3f8218d989ceac293c2fbc0358c9c70fbd508c7587700573102f26037204b5e013f08628b468a1d0c9d5ce85dc4a49396cb3695456853c9406863c802e8cd95592ed31941702005c34121197f08c7e79fb7410cae3015d23009c38a42de35929e401e4c9a585801a0021eb0, 0x31d40180d340b8232b77b5f6c80540fc004e00222df07c1193bbba4a5264b047c0269e9ef5d80160c54e3c94fe7a7aa06f42a93c31d628480563c4a979010d5f4830c499bea0906e01307217719268b5e80e2804541c53d832a2ce4851e63d5efdf1c009c4f1ca641938ce258424961d2101ca64d399800c0c6c44e804018805f0640a321482eeb5400889680388628435006e00a628c7c051a705a6010c04c03b80304c408e385eb0cfd1b1, 0x43cb4a6b04401da636598debb46281a48261a4f45c9079418a3de08c22314773638c80570e8050424b0fa500b318a3eb26186633609807a8c4e29725ee253d883179f49ec470cdc001b44662088c6ee2a8083010ca5000803140ab262d8011655ddeede8aa39a98a00ada7f9b373158fc133de33f16300000c409f9a16624b0ccd648918a231efd06010347003c0c98c3a006e01019196bf201b437c01b633d2ee8b3b807841600479880505, 0x7bfe015b754f86c32b1918921d8704df0011b0e02169fbd31e09c2c0d233f09040210678c5e00388131d2d00fb02a0e5200803273734006007a053075624cc64700fa0241572b10401f29166af8026178801a30e09f2041a19ac87c01b203d5c78015c056ab74329812dbaa001831a43bc7b2431e2d8c03f063af1d377e00760df6383325aa3401f603f140e3ad9296ae7006718dcdcd8317025c05200c262047820b6c09640a02ce0d3d9a9, 0x3932623a733c601b871401f806ca1f3c0200c57419f4900f3ca601029480c44036007e8e1b1ff0c6e1c500034962e3c003a01d901c96f5ea8d5db5840c5078300b07aa33a84ba862b047c01fa4a8b7a11ac8c50ce27a58014989ca7ae01d8630f7fc086f65006c8c50c994bbb195894c03a604b5d793838c6c4fb00518cd46dd008f499bf14004693284d1f3a4c9af473d02989802d001702431d4fccc620463c0389258154995099688fd, 0x5b5700db244019033f0a28da8c63ec1301449931e1d7c94195836317f66351735f9cd896299000e1960b0627cc0078688004af447b0402a0c62df00079a52480b24ec31b11dd2a6231425d5444867e68ca66224b1f8a056831ea4b0009292c7e393a2c652b8800768020fe89f8b01e4364074c6413540034de889c73fba80f20bd00fe0272956e82232459345188c86a740060bd10c9700d818a1e7d15cc64246761851ea83f52bcc0cfe221, 0x7bcc49bb754014a31448f406ccc40c0c80460cf476900a3496432c1a609376089fd4806e0d9b26a806d3c057b700f017201e862153a213c1870482800a1890214821f4a499bc016a6330a28023803808e844980fdc4809343131b58571a94d0769ffe80351a2006301022c05425310178b12960241db5ee10068f502ce10c7d8b300374963a22c8840377b2813f00271ec007318f445117c81a1a33a00de94935edd588650c24c4e30021784, 0x7e9401a9daef934c431918f5bde882a2432f80a61c5001949b3e06737462009a80304c9d0733589802032e533c00e8336746e64b69fc61b4c8674802778cdc243203d004128a007c3316eb9b02d2587d88036a505b6700ff4961a723d2ec3c3d8e3694c6907f3e1480a0140058718a1ad600e86290ec80020684ff6bff28ca067f006e61e326c01ce64c752029f4696c3b814f8021a2c002349a889401566354270013404e3c1001eb120fd9, 0x5e1a18f050cd03335488d83c63a618c12d0cfdc44994f02106b00d46340419dc2352591670e7fa508cdc84b7496b10600b801a4931a1ec0367ee9f798c70df7926d01e99c84a0464173a97524c600b8bcacb0f1983009f31f3dcedef2c480d8c01d063a2eb80510d21f638a0402a12c401ea34974592aa809c3eb802998d974934650041fba000e634786cefe068278f27cc8071ee30268027af2f016434d00115f9803e8063aaf0094b03, 0x82661a68e5d1e12314607c043d2644af00630d503c8981d18a284e009694112bc0c2463cb538025a4f2390093a194a706020431b6e59f0c0086522812e18d21310e4961c1b9ac2d033f871218bc6282ea80d50070d78000d0044706e7ca6370ba275b4022fb900a1a4c864d00aa3242ec80b7e92c3fbc00e9260ecabb18bd101df4fb21a79338adb801202e47750c82ae707688d0422e00ad19b04b62ee632960a0005cc40ac2382f80a1588, 0x3bcd18a2d10eb8e31f554c16cc66cef2b5d300f57582aeb3133590abfc31d7734006405062c454a8040bb83b3a01523327c9c3481d2c0181870c2fbf27809a37525444961ccc053c00812d00120c62287bd030c5174142f701a251a005a64d085804fc0504cc002718c46ea4f531952ca800243146791508529801f80258c522b775b5627aaa6832801b24564d3004cac28004003c04f003d18a3018d61031469388c1c64e2c60aa9993c03f, 0x813601b903328ec03456d0dd040961a62c48807c801651662a2a905c7a04b3dc80010010b1d80208ca93533e2218e040728d00311699f8d004cf67014a2504959219d02d0dccaf223256420023807eeeeccc300204106b071a435c6009c3285f08c7a126e79fbe0924cc646007d19f9c3a017892c25250f94c6e0bd00108d05e3e006a49ea704a7c2335047e13592b00a29e5f24f060000263100843251293d8deda19068202380393d5242e, 0x9a821a10f1200de334633e1cec0261a628808c7c4a610f44a7300a0084c38889002fc6a91d34b9e0120f427b88310aa0c5d1a92d2f5a084cc84802a7818c51b965faf498a3d401f69412e54044863ae2b002d0cd9af9872818e9bef275a620617407a003862aba77a56020f00e818a1ff403da01d57c814ed258eaa136524b0ca7006b1a600ace344c383f748a2466232a005c0d6125c003649bb2ec014005804a001ad25855280333d10a86, 0x8f9e61c0ba201e6634549e2a480109e03ac7004551a001d1991c4324aa31f8a81affc010654804418d14a6532f0041ee529be033567008ad27eeee9d810075aa775c361c0390dede31f15e400fc0608e4199e8ca643e712b324acb47154629057097d125abc23e2524d5784753818ebea0012e0121f0801112927ffb20c8024d19001f4964118322e32b2fa21aa862a0f0be8c4941427009a496344028c492c7c6c003129053580248134c31, 0x9c1a72ce055200261f6c00bc6503bd004018d5f3a004c3103b8d13440080ba1759c656bc2491180a415c2c891a41a8e015864c0b8dad64010dd5038b013582800f831abf6874bc62000fc1898010312c0688d39654901e00db872093a63648980174c9903ebd408d35ded42773141d93246c332385003ccc62554a0950cad51a003331000d801ee92c53b1c83467e5f400318c76134004831b366201ea32b77765cd00811ac82d5993608c, 0xbc19e814eb82064269e8000dea8668a23200996d875b131b3980aa04009403000058a804d806e0ca1e102c71025836682583413b5e5348090e39805e18d523d890d0210a3a01bc33619260808c6e32304fca50a35d58c83109a32a96e65801765c1c050600be17013884f3fd718d807ed02204b1e2494b0c84541806a98ac0c27cc119506ef05a233371116060c8668c88020101aee51f449e091207163341c961f70668435800f30e1809, 0x2a4a021a85601ec342647a08d0036720006a24b044a92971a60d8c004e9542c641e7cc97014caa10ca867f34960049fba03e43281e6d932c666b949c638ca415c92da0211c2803d404b1e1dea08c60db58049989e22a7ea502a194ea35a04c39f0035c022b18803c8ca00ca7f280040bc4f7a432a722a66c066af3e2ec8b0f232a004b6241e3494c0343129803e0c6ce33cd341935eed07237a2b872fd56f4429300c0866aa07b1f10cfd870, 0xd801e169b15fa0362f394ea1878554835a8d052c355203101f6201f69344789be5863c8880ccb80f16a19217320875af8e63420540f694c40737800330e22af5335193bde10d0c01e0cd9c16c09061ac31b8c510ed5dda31b96c6658c35a07c24a0403c70a015b8070c2200a902043fe017e03f7aec0295278a7c80658cd929b01d518a875b03dc94853142c6809a1170fd880fc46881954a09508093cc38329a6458c420bd353c012e1f3, 0x7673261c3e00500422c8d3a74c6c6c3298a80ddf80064019abc7cd0dc637047925dc038670cc5b8cfc5a6055b1a79289354235a743d51a869ae31806598821c6114e1a0304e9dc8f4406c639fd870b4820c530f0fd546f0004015c01b80485d9046d86382588d5a80cdded00f301b3c6801a494d25662a04036fe10006a505d1117df18e25c84a6c31f44656fbc0562a8359f0020a1000a301b39a2000293364ace940c7f0393aea0c50895, 0xc962a0c70017ac5463ec0270c489a1806a80d876b758f18e312cc714f4b61c0062cc822c7c16e253881405ac18a32beff56012794e626806e178be670ca50870054498456c00ccc48110499d529eae712728d30206008c009833675c6621057192b006e06245123120e316b1c01fb50d13ea63d8cb83ae8c96e7500ab8c762b708cc1999c781baa0085f7c36cd27aa094af48ca8869341a31aa79c01b6631671c020006c2b40298007139e, 0x3f3102ab8007034208410040c42afc80288ca22d600d83101a30000e342863deab863aef6801298d15098a5c31014f2930a328743e4a79283150005e18980c300771a405e73fb204209a816600b2c14006ea4d074c63c319599d72b2e03443a56b54c86156802d0c6641c824249f8c8cc31a01b7c6c009cc98245cf6f806c5a67e73009036600966202024e440c6232a001f1881ace0036019b256a3c46208dec0164c68b68806a98a55cf, 0x849719439cc16e263f10040178050f080038810216800637a219332cc431526fa4a10c5247a4a718cdd51a864d01aaf08010c6246f4c01dc684b9332028c748e1006e3100f4909e4633047803652591944c8e0101d08121f00434f0772092d7c6cdab466a09c824c9960b3a3bb331abf3407d60364442009c6904634293192185d02e40041fce016862007fdd914c862d6bd6d9934a842574321823e016c00822a4e0218a80b8aab58138d1c, 0x49c218a39d4916033136c8061467ec3b801524b080d92d23103106015a6421ab0c6fc0389cd807ca50debb4049013b41b1d0e32b8741eec92904501e9180a87d78ad0015bf00fb560295bdca600c40748400f1934532001c19a246909a69336ea8b20807a60329af8c50fc42647626253d13d494a2d8c005cc40facc52c00a811c7e1031e338601b83378f6002b8628cff026680a4e0200304a446368c9c3150d300228c86e1c80918021ef4, 0x9a18d809e167202a5fea4e812aa653807c188015f7faa1a6004e016031450290ca46863c7a8c981307ac5d4a7a417de008e3142c1dd010038f378cca193d0874ff602636a600463428f9219746285418174189db9616f11a19288307062043040b2409636686b88d3d1b16bbd02c12ae6a4c34d2d75ec28c402f311530ccc03f421a0141d45113c6262d610f20c863c780401881fb76f903103dce26029371e3d0638628e3917970021c8b, 0x2b2d021a01808b063731180f412780c64a2a806d59c6635310b9d406689403fe62848038f50003e98817175e0018f3cda0034008181c00c06289e783738cd0da02ae5324c2a0002203d25281664628af2800d24f0b0900f94989e1600aa0250d9e063c090f3a420900c10aa64ba00e933804de0421490011067ab2a829a25504b600291a427c2453233326f833dc636ae7004599512e6002718a1dce01d26480558a77c6280d8842ca4d1704, 0xc718a8f04054e93f696d3f7c67ea9102d224f003c820931038c6013e02609695e5c628c8425e28ccdf1b523a1a1b5129f5c64f620c91f926679fbc630cddcea342b013aefe27a432b1e3cfea9278bc4082f8130d217ca00130c8c009804c2e9802d52a902e003698c5a82953300d9e4a00de0412c1227840225103c2a002205f4f19015aa34b38632b5a3400bd2583a1be690cd5b963d001942c92683832b3100029c69a2c7c132b10c1b1, 0x25410088364005602a0754012808437602ab30e1d5409ed1a0a76c472a31512980f2c6660e40047b151bea65b431936d600f8c54295d4ff0c605048010c951d40254901eaeea74d86333f740390c405b8408681206627fe4313020e00b033d8c2c292cc4068c8182988122c002e4964715028af4404b80130c4120acd64bd108b0016719fc4ba01346205138eab463847d8079310d1c389a90138f1200320274f0dd45006a1ef00680021396, 0x6b4218a188001de02889263fa463a02e824a8d6209b02e218a0f1e776801183c80194098bb03e6598d83d553b2318a4db08b6c3f11a015ec6301f0806e006c28a02c17aa1de000960292b60015003893d811f30f8f24016b01a0a3ebb2a3154f365a8401e4df21058cd82067a5701402d5048c64d5504ad44c7e1d6c4b7009c99c70db4988fb201d692c791800acc7cf04a7a098dd8833bbf31bbe3616da01d5cfa1904036bc0211c0105ed0, 0x92f57a2aa0735f002751cdf3b587087ec34e802555300dd19504b6093ef44112411b86850c600698c51dcf5a0f310855afa4801314c80160011133bfee8120b929460025aa061d1c01f5e5debecc625e142a100d81b32c941942220011a3418fd40150c68d6a8046a5083b200614a698228e5a62007340251258937037d81248bb72bf928195c003a94d08593f94684bb8210c3d1041038c001a83910e9063c0d19d29c06a3cd3def007d51a, 0x8749aa99ef63231f67d01cdcc427483f2530e0cd8003019a2819156404e404da1906665eb00b098f0931844349fb75400780105c564b2c69c1160008a4b592b00cf18a42ce011033f64ac00c403cc1aba33b0f0e31757532a11d10592620205186c9870c418060b12643e00a001e21d80174641777c036d893046005f8ca1e7708d2315bf34331e32b1cba2b24656a8345498020915697f61c823c01246200859ea1867a2994d08b1340fc, 0x7101f96cd2ace333225403b8628b1d80030070ee37fcd61c0f340008c4b40300004c6672d412298841b1092849f1e3d1eba04d29e402fc084b38b01230e46467e423248a64cbe60542805d434686234002f802213d92204a5b106393c05974bdf44805449e00360021e45009231044b2faca654019909f803afb8003c815236635db61c44ba00ba92c554a01846283612e831880b635bf20198f2601ae62063d8033466cf31007000cd3c3, 0x6990013a84e007292c521409dc07a7cc250a0161ce9007c18a347adbd66492aa401c927a4d134a9bd6454006a461c1822b05862b34640864c687e584618cdc15c001c499097a078e64343b48d946289de802598c4b6d7feb020bcf8018c314481c221cc6ec5980528ccd1c3006831041b200a464d1a0880c1ea822fbf9c80d9d2b00990089bc60a4a335724401dc6801b513bca4f531f5b62015839001e404e59d1d649e9ef65001d0d3566f, 0x34a91958b4c01183148e29ae1c0550df07cd80ada8901ac1a042dcffd06277f0801dc084a1f3ac7004578058e918a045cd73c036320801a065245f471ba4cde0858d24993ec0008c010827002d4c40b109a7798a0541009d18a0dbcb11c6206f85628cc52d4b1c1c1899a0f6b4f0043980001465452ca4b0c653093a0ea8ca14368254321a8e6225664c1d10d35cc4208f806e00cd1c3040a02a125a0acc6367e8d206c024618a80e988012e, 0x884961d62003064072fc0008012ab700ec8ca125c2e3161c319d359664d7d41a090086a81804e8d05e2a011400ea90a0a3662b5a1264546502a0b5c30c522a023ed193894d0d1a036147504dc682f3e484e3104ca73b5331011dc006a3147d1259c066e023ba753150e31003219b1eaeff8804c0e0524b8666f7844eb8d2d72900cb62a16c201d06207d4a6985258dfd803e98c5c365378007a4f8fcbe0372518007805050b801124b1a00, 0x671249fba245d4c32835440310c40650804f00d5ce8345f18a1d4c00463141189867d2870e244e0b0e100b7414625aa34f718034166c01dcc6c4c4005e98a9d544d150139e7ec0e893d55049128026cd53e964941ded2481193c389338494305e80274652d8e802b8c51d6654824a6363a4a323373998020cc921e64a71bd11eca820a193b8880daa93d299c0288c4034880081881b0e64016258c8f09f06333cfe6aacc903e980508131284, 0x8c1200492b8ef183290d100ed8024958006e18816dc453d18fb41b293e02a47c5da8801eaa08025a534b0b7505009b7540074342689e4b75e891bdb45a8c6c1b33c4131024b0a6ac0092454474c010109006f0cccb9d8463015aa064b0892c25100108628ec243370c517842e9b4a5b7543a3263d29e5fcc068001386c5190deed64ff1a0b106007ec3803b04b18628d89a24f010df507de24a685e20a9232b2a11aa9c06c0ea80680150b89, 0x64897a2067c00fc3426be4046c0530d9c2fc18fe1c5001b012c334010ac485442089c666a3980420c502a9002218a44da019c01c03cc42806562bc926a80984a1030118a30c60d7c33532666a09284121892f004494569b918f8d8400aa6207bf97d98080656007d98fc28a1d79327aa06019e00f38f00260c6b0c4007da4b18de001f4a01c52fed83353a4117d86567484202a5018630e92499c052014ac486280974d296f04007da4ddaa7, 0x202020037c006a62000540284c40b2b007b255014125a249e9ca315fa92c6bb045f8010702003f98f4ec26b80004bd94171863f293002258710cd006f01358050ffc31a2428019a00e8952636462800201851954976006249e97e9018a62089a9f99006af3e002f3d35d0e40a418f3f4f012834a8f6002f4c80b7506110cacc0641d392a255cd6380085e01fbb808276baebc990dd423df401233f4019a31488900314c52e75803f0c508d3, 0x9a120268a6400a231d85d0036d8866e6cd2098ad4735d4a021c38ae0483425a564a4c6821d699bb989da0d001300428386b746203dc80318c9c68998740c6d92200c61a1c7b0189e634823d919469845099178cde1271fe30041c4801ea62914e50a6805266691af009c58c7e06021bf01250864257d028d4c96197211980f0f1e006a195818401ee31a326c010a4a0b14000a2534c63048602583901f42328336c02bcc9c13e1af7a4b4a84, 0x5f2631382f400da6354a78eda126ef8d84fa18d9fd25834192855a416493c1c000690652e48802e80217a394830044318c36cc4387124aa9e8915002e23d1048e03e501a87fc0144c485ad8f134c6a5c940280d21ba8843b49f83a8b48e02862d80be8c96603024430e0d2e001531e8fa2004492c65e802e98a8136a96319221cc860d1a12ca8017064c2864030c628405cc1824b00fc0c0e4992f4a552c043463c02700666e6c3780100ff7, 0xd11953f8c019293c6b7505f4c7ef654e0f8025ddd758249eb8720112f548b894d306284df21450c50ca715331ad4034bc5e31439400294c4005a2f3ba4fd74102b6193a78601aac487b9002792908efab7e8044b6777253279028002233406bc06e006e00280a180fd75e00ae00d17d20096327387403dd8785a6a8e68c5478f6b6401896fc014e92c6c84d13c64ebbf80f600a87ac04c362a06c6019603374100020628a0e275e0130893, 0x7e800d8c8f3a260118628b79c636f782ed09951ac8017801a01e6f872314191905fc06085100388c94d2e53d30042a06640401f0d300134c50be13fba80fca4520327aa0e4c0ba064f6488b80462a01f8059b125bb871311a70b529f1462b0bc40ddd27aec200668c5149994f832538e733020417aecfff927e728a118989926f42b8315aa8280f893f328e585001276b96270d020f2004d49616172be632821a5c798082bce92ab8cddef0, 0x7a5419b0f121d886207bc02a4c62a0e44bfc19222c84e6601a12b0003a64e6a6801b1884fda0077812480d071331a87fcf05033573a8018404a20f92239920e6600c401a2fb200d40085e740034c4108a00381881ddf6be218dab38364000860a0eaf4629003bb5f98845ad1dce009b3821c6e34363280130c5084c00e380fc1b2009562698c68ae03330ab5f978ca8adb804a98a53f30017496325082a401e6075f96804c05581c60d0cc4e, 0x364a6250c01c063617280154c4eed534c73d2d503411018e38fe004804003ccc57c06c4ce826024fc7a9008318a20a328a2335540d2cdd26ad06bacd80d5780000831e834c49e00280794fdc8c84bd280329881a56002e014900c24c2354233164ec66e343885e25080538c410219a5201286366a697da987040a03711880c1125441a09ca2d2ed55c3d2a4a6406113b80129880942136561f8f1e00f894d8ca26718c9cc241880a530c4e, 0x7531e1658c93a042904c03a8c604ab000f18d1dfc6ba900429d0005e9422c1c2ae925ad53b1350c7c12e232d18a387203626292034b2000501c0807e8c9d210000b4a10b9a4b206356098071cc52f35491400a9aea0045310129128d09325e5c7338c40d71802998a5fbc756d00ea31f1b2a3430d3000b8c68829805a00c15ab004d020b9f458d6040511400d8c40b8b2ea118fcc905d474a48f2284a89543de4020a4a8a71004280fd56e, 0x882e1ac4318fb3031f14c803a58a812ca32d8020f26001a004072e00ba63113f128d809d14080eb00cd18f02fa00404de014601c5da4946066a4a200538100b3b82353102a8215643284c180a0c636d44953f18824360760009989cbd9e04b5d0629d1e88d5e04e30ca4db2008c49aabd0c6906208c0493dc66ab46803b0c50c32052f4aa07400b0e63d64edff680a84ba80481939bce01f119a45da009892c05980434662432345680a06cf, 0x30242a72015231a318c030cc40fe9002998a985f008261c40b2016863c1dea671c096f652e87a522408005749ea158019e02764ae14d5290b17495c8cd446a757e00eabe87190629090d6c9806c4bac513a4b108700ca192857ebb8a93f339002e8c844a68048a4b4fa529e931ba612001a33465f09069e88f3e00588c74dcc985f4963044159e00844c40098c4062d836ba5306dc004b314aaac164a34d08b9c3c1e92cf02b1f0020656, 0x224501485d09f26337620da3e062afe134b0009dfc20a6618ab090fcbe01c0f50b6c0c4e68c97158c741c87ce919b20600082635112802180849e2804831322004fcc021005e00fe0586e00038cc62504800f3d107645d8519fc38a0958c491a44d2940364df263a1925819995d31e880249ec0082e640114628b6e12c3b0e00fc37db49e814cea646301999e6d927a654b2170d0c1b3044c928185cf920030295802a804e8e192ae0095f42, 0x20a07aabdc400ba0080c4c026d268efe4b5380216906b12008977012806262fbc03b52590ba005a18fe090008b18a0e5e5de003f554cd6d801e79fb08c009df1b66af18e8692201c62b15e5a05467e5eb003b0ca456800eb3100c40d05e34c57690641e983cbb5a08021b2e424562a2540cebe6364a2001f8c408703f1100d53c07e1d3158a647c0c3270d30964525af784a3f00dc99c002b19bb4b6013463160a5f21525832331ca0cad541, 0x34e64aa0d0304bec3951cc0e0126860d4217004d5036b6d004424e848c314124dae780110e2c54f012c46800ec7a22e1001c6943470c005c09c398000b98d578a64f67a22d10017c332728c03c003856a129a00a8f69002361c132e01d63142c813408012d44b0d898fce4000390042c630092c4a5418b2fc67847832480c9d9026872312836683c8637554c0205890901001980da05100e049ec6c701d404008a40c1989210b10ad8020817, 0x34e2321c4ba0124949562cadf4c9a99c4301009d7847c5e31f8bcc01e633f470e6bd8c96178c89999252ae197c19bbd1c5b246277bc26a5589c33617ac0c94f1e07e6313c052013e01f5d0d8b34c8107f0b860048698131f01b8f1e01cc02a855a19f8010fb9007918801da390218a303c9f320344e6c0259298cbe800b31215e000aa3191150e37e65549622891e9efe1004298810ff11c9310363a621493326719a58022bcb80671881bcb, 0x5e1a183912bf603f7e009ceccb22a0454030e0bc25e5d18fc4ba010e02a8b30c44dea85f7805a989d2100047018a722008064e034a1ba407ef6503ae98cc647982918fb7c2bc826260d19df7d27a5f40ba2a551fcf5dc431999205d403145e0402900105ffaf67812c0ac007018d98800c1894972a9df38696aa0a576804dbe171a6008a048dc1664f0eb4008c01e3c13d3e010495c014b1a0103cc20ec391e3c03140a8f1c80690cac12e, 0x114963cca016e62084d452e465253c88349880cd7002d1a1bbba000063f38748bf80223f520878d0441000a219aa9e4014e63564f9c2c0066d53964424b1d2b00de0142ed297fc92c620c02b18903189a41012c7937e3e01b8a64d7323141dee66f40846948003a4b0bca2eec19597ac0b8631f80100234c7ed2d80303d2debb1eac01b1e3c6278958195001d4698d8f931c98800c0085301a25b0011632a59c2558c6542c0800a80a4dab, 0x3d8f49b16c6e8be6426328320cc681f1832f802067a02b64982440214a6202f0c03dd26e8e1bad10cadeca8abe1aa17b8036c32986340818010c1900068ca8f59011401a245e014e02a1dac134466ae2b401ca534a8408ef49eb04b04aa33f4014bb9806cf490254a4b1fb44a47327b166002a31f7a61d248c4e52281200c50ca400ae192b56427bc3150d100125258765800498801860034021486200a69546bccb05463ace0a4a08072091, 0x86bb00e30fa695831489766e48c9e0d94a2a0c51baa893002a2aae0b7434f310001acc4050505270cac1c8010e194b215130432879ea41b8c6027100403d105f05dd2625aaa6014603c29fc03dc06321f1c370d6984901020182e8e00c092c3bbceb5529102c001c81242a73aa000934fe942c3144b700ef86285c9001a98d618d7bce3102b6e01d26204ed1250c628c9131f18cd86c68a6f1943064666600f0eb542006284fc8302313929e, 0x4dda18a0d7601d66200fe1acc8636d433e2a0d091ea840702a3a76a54004e2e056a8cc4e1568098003da8940d600417700100626873240f46285ee406c80d9755006c61c2ce640d6c3864ac112cc66d2db74730e48b0690002c303a9b4863f14b953f009a40c80613131f45039b01ac268012832901b0e928628d448144002020e7f3b49b9338858c03515e54540c52ea10b47809d741315d007101d351434e515136acc4e3c7ba900c513dd, 0x8adc3100fc0058e31c37813fd0c402350cab01206000056626958f30a404c56d0ec60054baa806d98c4c5289aa195b7c234c092c27d920bcc568f5004300d9836000e62a296401f00085bace758010b9f006a8d0c04f7509026b845256c63511a8dd55896a13a4f80c5094400cf01ea71cc346f4451cc5c64caa033000b8c50f144bb649638e673ac31b34a5d59c0980178e170d3e12700141a0486015789486e54d42926ef78006c1881383, 0x9feb01e8b4cfcc263714c8018cc428c6006f0078dc780719281ccc01706308b50017d29883aaa2280c16fd7e54008826675823331e3c26e0c40a7423b900dcd29001901f9cb4d7d800806c92934038da1a6240ca5a568a9719a0c12f62a64e3b1274bc628b9f00c88d022ed00761a61fb2f48262014b803ccc630cb3f423d5195f002f6241a22d36433483c80550068ac1003730f237e354d18fb2451d9a0090d240128062d6580409882340, 0x5a326830d245631d1e0c6e946b260d89bca52e029125e199951c00ce314755a0b9463a003c31a8c7189f009a18a20a453cc31420660bed258a3982b52525a0080ed3240d1e01c43337e280208c66027c319812d55300104a70320004031e6ee002700900c103aa8c55b96248f009164a006e33548f4000062829c80668cf50ff388731ea9b200263154e9c026126ad41002da550de526ec327ab9c0066c41059a005069ae39cc1380cc17a, 0x15801ab03201523270eb64c0803c81680021880d5077b91938e5d002064a39980e4d29252d2c608c68b0332ce4acabea0164c5440ed250c64ef8d80a78cce25d8458318382c0488933013c02a0030f0b43738c516694f7662a2e9e3afec380c88bb0c6290e2b43801001e5015d18d93ca032c333238411fc68290500611881bab00bd021481c016631465e8a1e0c9c7d8805f8cc619a079d00e3034f27a94932a4b31c03a3cd3fc5c9507c6, 0x93626c6504a92314047cb91de96fe125c00cfdf1b6b7e004b2aeffb6034255d0038c9203300480cd13a6000d4a48a4cd114327888401386788ae84580c522ad24f6313c38801f80251cae3c5c06c2d5004a253daa700d60073a1c009033c5dfa2690084e1140da2520d7b2573012215401680420de84dd80563c7c90d18ac4a6536301b109e00aec3c72a4014187017d002c00f1d8941037a2bd94e4ee93f2fa0023409831780f10d3081e, 0x2efe1a0bf84f9400113118010809cc1a9ec101045447cda01b1b7c01e292c00540f38c78bb6073a98dcc066b4418a3722bcf033005ba2ee4c56e2a800a30f4d1305fb1a7875a003ec385a7d0bb009112e0044250c04f1a5c1a782b8125a63079a0005c6280360065a4b14d569011a7808e20e801116a5d0c403a7624d3201391f125310210faf344c04031140050682b8f023424b0a6700791a0ba9afc6c0417b2a4bb126e178967b98a61c5, 0x9a074962d0828ec633463dfbc12607010056bd21e480dce7a20a8a002a9333734963063e08f803380c21658d5c7aa47e4764a32a47a802b0010d3dbfae80d497a80e36242a0ccc7e34b0d327614056e11004f00ddca635c218fadeea76ec384e1cb24007af5d804098cd3c316aa4a6a3de57923432004033c0525deab891880c314f9a4aa058eeba03142796467c09c029c0e6812174c82be18ea00a00040364195c0a4c48289431400384a1, 0x256d61c128801fc92c06189694c7a4e5bc69809057d00f97a2128aa3e69486418033c662e7d002b0c553c3261718a0180011a631082cf56c63ea8d3ac300d478735b301eb245295e3145e5e067c090cb1461481383d41de619a8e5eea8c01354680374038da6a5a324b44a634e7315aeff134062041d003e4628ea6807da4b14cf00fb49abcca6bb202b7155fc20c6c8ce833a8021ca59cc300483900090042141c38c0c42b7b80290d21448, 0x7318eb7a0042e008779124ac038c1bbbea0ca481441c50271e3cda6e00869d5fdb803a23400479880db205700043e6601c43143e78ca8063e1a600350045a2700f131e1d14005a6273969efba4a02a8005380c43e905034a5bbda3a580351998001c62895b0165002143c8a1e18daf0807843285d8420e4022b9f219a0c520044f4818a06892a5a3273c9401e0632e8b007e007466e42d292a120ccb8003f5670030c63a196ae4cb10da89, 0xe33149c68014292c743803a926b0cb00720c51c76005561c3770b07892c05e80279278aa3005f00762f274df01548264a0431c2a0cc628c5679f807cb151dba001c310177aa6543290b6c0351258b828013a4b0b8c004702137b675d83140b6e52bcc66253001c804420a0c69313ab9c011e92c79a8162c62832980750c5071537c41a4b8ecd698033227002c4c4086240490d2950600c50212dda5d8a64c151a01400271b8b5940020c90, 0x3815014b52c86d80431e3c0a60c62ae3001298d924f003031888fecb263545ab1f8b4c96299009d0cd000e84bc0159339044a33f51cc0c886284aa31d0810cbd67c000148486002031437dc02586b0ccac39c98dc322004e1939c78762c0582c5a41f8c60a8c26da0c50a02002a31009a4fc1604c40b4b024c6a3f0006a98c4174742d01527ae14d4315001c13d0c40bc50040a4b13741d0c310ad0884cc32b06cc03b927e6e6b61418c53e9, 0x8ddf32619aa529602787cc1f64083104ba5c8ccd9aa009300843fefd600373f741eb4c62c130d7e00cc2b700b43138a0600d492c7a1deda8c42522caea804033300853103cca7a6e331279603a4080cae011e18d0b3a003631017d8167832b8dee4860665014802498a02ca89f632a23fa5de602815ec04ec07ebac3f2a98d8bd6003d31841d2a9bc64d71542a88628ace002d1904e6900a2198a3b401489421a50d175258c13007918f5885, 0x253103a0b32a80081511a24801efe11ec48c99a238aa4020bf846b7294f047c51d06569e68003a53112a0fed1a5839001e80432cb5de30696397164f00d09702ed519fae5215b292c140e54bc03e792806c806c04f80e83101cf0136a93283d0038c636145005c2550e58163f00da0dc0060620501a115c680e878057188168f00e900faf0226ec31f291623bd870ae3001a0c519567ec10131d32eb0a011730272cc06e666c8ff2521fa1, 0x70ce01f091cac780085969ee6001cc5988390ca4f1e24ee021aaa6003692d4f0ddf8866639700fe80d1433006e0120742052231e8891bab4c6243687f58ccc81400994a4a65513e2643871576f066e5eb00688c54a0242cd4960dea00386203d40d5c4c6e120baba8cd612700181ac0ec0fa9032b3cfc77392581a4a35c00220f22463009b0e000ee33239290c60c5607e185f00ca3c100d631a332a00de33d73e8011d25868c002c1881e49, 0x640d00430e0eb843356a2459b86643cf02e08c5066e001d1a1b4b72eae01d06f4d23066eb94a0308c6cd19000c49b2f469fd60103a880b700540e1020a1880ca6360f0158b020e0a31f072169100504ac123924b034c00fb02127a8d92003628ee6d3803680600600c746357bc319532aef8d03360b4e490c066253001f3d1232d00d931437ea001431403bc0030c7eab7004c18816b227c24a1b044a29a6203998023c09c8c3b1f698c45d5, 0x637931bb9d4019031b55b9ac580123c4c95c24f62a07fdc319aa0c564034366a4015cc62b67006f8c5218d004d1941d9e3d1e93d1c0001586504838074188005400ea1ac336f0bee93d73a8066063660346fa8d040b900f3019839123e402b4f00d06cc404a22e890c7982600b418a1260025c333001c0148ca874100140d0c3497b531aa02b263c032a59280d48c8662734a280a06e64b8361c4052fdda00e03f26828068e5612190049669, 0xd94962db8042031c376c6f54628c143dcb0d06371747c015b914d64001e691c03f1264c834563813dbaa00bc315a318235e62030a003e40605b780583d5013f0083020992f316cf485704e59001ee2432fd98980387ec2027b20401c72501e90e9a806aaa9aa4f1881684795f49899533f7603d814dad64010d76006398d9dd10067624399c855e34e683401f12901d0806aa50dddd750618a912a018a03c141894e0062c1349372524004, 0x2d00e9b2e2dbe03756c5fb38c9275300703d10f2000877aa94409e3694f62cdaa9408428c0639804c15c004c19b2c62fb7465806f4009c68716738718d20c35006f32633db33180332f58038003e6c5cd390130c4568cb1a015fb1408c484a807d680667928041012c3490094326240801cc92c59be53e0098f50003c80f5e74758001b0238017031489a0011cc9c53b4d289960ec966f50043c19296c03f1e2401dcc7e90829823120454, 0x7003013c442597802a708800cd8700b320c38d0cbd67cd00043ea0009a620866a49406501af0ba025262ee9cf631a8cd937aac435e0153a809c6910066006ce3c09da4a120240358328633d9e506571b887fe255023f507400e8a82f8c801b06c59a38c6ae75003e25253ed00d231eac207b48013640801712a88c6805800f540a639349baa82c1dcc38191dfbe803e7b931768cf5f7c9272321065c922001c15ec2310c629fd001018805c8, 0xed4a6958ed60000850ac3a8cc57014c78c8cdd688944992846030d1203f6ea8d1c46283ae80090cada5b003e310270c2b2c34f313a691187e0d8cec49955ee79a131a714a04b4e9480274e2a0052d53ca120c51eca2c350069c34017e6271e0a7bf4c4c47412d78095e0800b402a2e72019232b38f00210c50cc5ca0c189d8830f281a59028061e0277aec0a1063c783832f98d56b26bdd01e833f14f8041874211300983733eb799205e5, 0xbd4961cd2327a34f421e56b466c4348037494241500fe4a4be9803f60111959e8c804a3c380100c9c6bb82279282a82f9a6026328c0168038b968017b0fa19a008b4a11a1496bc03647c415ccc56542482a98901dd6bd200696fc875031d15425448038a22801898f20a868e7020205af38c63c1f444cd063e3c7807600a5e2d74584a442e4f9c20357e6801a8054fa6a80c18800c2927c1a6267075303141a1c02a407efc50066bd11092, 0x75bd015928c016c0117c0c01592a810ebad218c43de07b219ab1bed03e01b346402c809c23880148c50a7069161ac994e00a631d6a68024d27ac2f814d8c7943500fc19a4138281e32908b803e467a3fea2c58d08d1c7aa77a2278110b66373998d78987212091fd0c508f400b51a097d2ef206202fa00255258b1880368c9c503732d0041e94001a32a776cabb8caa3f501400108a35281f18fa36201ee94c38fc03558846088018b120f60, 0x3dbc496142032f401d13ee285806caa839d1013debb857118e24b6f8a694d19180060652eb301118c50a8c004f49bb4b6beca63415180040c6efc500e10cfca837b953100af266620377aecc570c4ecfa002624b006c7e3318a0698004801b64ac007c0922c7800998a4ca100ea7a2290000b232a556416d86567e221af0104532035a313244806223288a60b040c6ea83008a0ca5f8f00b749e1c9120fa34f59a61a4c0243b0becd9880532, 0x1c6202d00fe01f001d5a95b3e003c46a807e8124f98002c3180054a82894c6c4e21ac628fb90060b12183300777a218c602f00111075d65c6925cc802424da06a00df7a240e8008662026ba48a40980f280250cd53ad006d00e2b0400e4011414843cc686fb83a36a4dc1d49f1f18a0803159434e16040378c4008c006b0ca9e66906a31e0e864a2833202b01bb0c6a64c886f8cddf7028040190eda013ec387ae9a4a58727ee805618da08f, 0xf149618d00048f443460033466ceed802f8cd8c5a36bf01383640120632365617e0c90648098f0cdc4a61ba1310271a01a86346fa1d6b006a5e10712b0e0a022f4c008a878f9500426dbc03a0c529ea10d1a4dca8400ef0218692001af4426c5af2006ecabbe2b8ca02d30067004179801e83375e040174c403b2007200d9064005e4a19b9a01489353374d0d462a6201d3ca4d834c00639283c543b1cc4180a4e824c4064812d4a5519fa, 0x4cef7a4891c084e0298f18be6cc6e70d1893188126f844f015c24f2eb831f00100365ea848000198131b87007632692b24ad23292510ee58c52876cd2618802f13dc07a421446e2693c5bec0044c400e1007418f0abd00483101046006401d8c99a490010f29803798940136b3b18a0188d9043592d7423ccc688dc803b98819284a0b00417ac01c603064d9c56927e9e02462a50d1ea4341310036336b063715e4973c0600e6bfe30cd59c1, 0xdd631bb04528b03436409a120068304000480da226000719e8f4800689422568ae8404e672006b0c5107047980040cb8d87601f71ca24440229e031ae0d381f000cf3101fd10192943129a510063a4ce28000d08541003b7a799d6000a025472cee4003ac8417030d202808ed631bc54000a9250503c0c1989820900390022018008b31018c515b6649790c0144010105002b1881bb869ff319836734b0c380bc403324a0050431ca4c5387, 0x85b61a1304c0014008709439386289d38db2bd15eed11d21a6304e00f064c6931d6c8c4036f80103d1126e09fd31b44da05f263501a53d80628fcd1d791880dd731ae3219e7e006e94e416402e069a8f7a1e198ac17a0353314360cceea02628040134c60786a1463d1232e006f0041299080493f7f08b7a064e3c7c95180cd3bd84aa4ac0da2096a620573c0f580210810844190c7e041fc008b8e4004862982fc02e52581113aed80d45d5, 0x6558324aa340f906273a40ebb064f003a86d010856f009d31039c0006a62b53a1aeec0105b1803024d509c002a4a09aa1200ec496cb9f58987e0620059b13166405cf625bbda190e6205d0cee080544ce802d0d3209c6b9900432aefd280411005fd118702f1002780a9e349a8e00782f4010031d034a649cc9c3668075b10c1c843cf3209a30a7743300ac9ff74c62fe14c710d01131362501594a10510f4433adff8c0822083e4a9921bfb, 0x779d4a1068801cc9341d120be86642d680420c50c5b71734a10698f8d52502064024187a00acc7f18813cd852d310c38a0058f441250034c090a71055780a466600e8319a0e8f51c32b801de200c6666c4cea8c51ed0023a0099d890d4c635047ca28469c6903acd00a57809e5202183900074942086cf50dea8851004180f51cb005e4a1215f049c92c16b53c44c4047a002680f42bf00ba4ac440002a20341d5175ac62abc2000e98d8bd5, 0x659100f82b800c6620742603bc09c7b48a09bd15ddd0bed008857a4c2892c124ca7306286033ff60120b1500bb19aa498015631b4f0cb0b64a912e002525052c200ec008841c005e62087a9d56cc66aa9804218a1e7738b432710c8666831f0eb4429929c618becf8d05be1002261e268a5ad26203138768d258a81cce7809cbd62c98194adee02f004b51525104666c41ca5a18800474d9e0048698935431f42100598c406a19233188004b, 0x8e081948588019832b27e400d64a0406b42d807cd1942b43158366012e0088629763526a0e1484b804da890107194b9b2003432a863d29506283970069990984d509e31016cc00106426069f78989a3233ba3a4b064785943200051098a33f047d3e8de88f76b5ae0c520537847007c4baff50c4040a82439292618bd6219246e824b6012a31e012492d65d9458c686b94caba0ca033334443102eff3ef231d640801c5258b9e1a6e00cda86, 0x9f7026ae7c011a3297095f1b801e0d8ce6980ddaec384d4aa12ea624092d0bc40295286c95bf998079013007c4a0333400c0630480a18340850df004098d2049008601eb1cc011863c4d14a7600264009c6418815f903e401b23bccaa834f540c156189615b8744809e0297e2e01baa06ffe432906cc01c5268cb28062b12850f0000024bce8bbb601024662bfc64e0ea003d00da406007f012c2e83d8c94913d1ccd409e6031481002002b, 0x75b001ab512013401b140c006462893403fa18d0e1f00933121c7c7bb40086b48015925ad2d803b1881fa301aa1949ff5354463d5258e120652627005e24b1a827c614a4b54e01ce31f2d9802c463283f003a993519a499819583c2001262017a804a009215eaa7119098489727320ae3c011c32b0508001cc5295180658c50cfa40d9319b52c046a6265a609428ca8d5dba2400a095796760048821248893c8d8d44f4c4225303848cdcc06, 0x69724a605890af464b3dc9f4a80847011c420c75b1c62833189c84bf3663f3464570d2aad980b5d8cde2a69fae18ab204ffe0f448dc5fe5a4a86d5001aa4cd97600f731034413d2c94f68340a08c968c7ccc6a5218053a6e0093fee00046317ae802a4c4045a047880d88aa6eb161cb8c6971431f0570025cc6c7f7801db13d00c1cd71a7b9d531ca04d57ca4ba12931808020990d1c300751a4acf400ea63203d8e164c6caf580260020197, 0x53830149ee4007a314818011c4c40fda0017992407a00304960048004c63c37b002200b02ab0073189426f926261c335200a092c068c030406cda7219c8c7d2dc6b5f18a444268686215dfc4c60628507b74dc94066e00aa198373c008a036792e2b8cca8f73b2f4992436c008b62487dad3eaf44292002b8c4107ecbfa190538e001f321bf141bc03294e34034d26a209310a0d30495826e31ab72c17aa343463c66acc868f51a228c545a6, 0x5afb00e9ca001463146a8c03e4c4104601798c78c78229a1aa0ea648f664028b03420c56002000ea4b0ecd00143268b1f12ae02a38500148c403a580941904216007719ac31affb801e2674014cc9055104210d0623800d149aaf14b3e601b5d6236acc98c0d0c3218adddd166919fb2440778637362daf7003a3c4ce578ca9a9d74df0083678dcd694e39be7db463ef65330d0d2e1270a734962786f7d8631874002a8c6e8c100120069d0e, 0xce67a2bd77241463047f6092463a39709e818dca45626a31a87646b403333cfd56906563f0150199543b4411300d9dae00a402590f802ac66d2050b3c18de2a600703262dd5094401c1b980099870f204aa798f45448a387a60056ef2c93c268802e8c6a9da3a0818fc1b3002c1a11e260cc063578f895e866e79f9d4b80ccfdd42bf624c2ea001e02755ba6794c860bd01430cd0c26991118f23d4017800863d8025806683a164f80a9669, 0x3f7314193e01ba63636a0012a4a0b37c79f007563b3958318828a0cac0082edd3e2cc40dcb43250c50007887331000cc01eec5414dc210406c58b010718a9c949e3f019aca8850a34149d63d45886cd41a660c519023099321b04cd1226373f740254c6834cbd0e990def000513101d54111a63d27dc003867b177000998a9bce006518a39d001b462562f8f03463d105afc88c6c24174cc1a016ce2ffc628350d91a46544a8002a988123d, 0x187a22814006033443a2506008447d8743189dcea00af01a3bb00f2264b191e0064c4118000240cd200f3a1e0240f0616cc34e7498260403e8c7be7da50c64601e401faca801bc6267b9d0b3cc48e8e001c9908e88229c01386987aae6427d80069466c8884d0a0d09e7a3a0131e922a00229354930bc48010acbbba81885473252818fbde00c5e011755803706982f200048cc641c2c8d1aa0a24004801e52ac0280680ad5cca00024f25, 0x7add6242be4f66631f11a2007cc40f3e00663121b1b01240082e5d084403656d268b4c9c802a9c78c51abb2feb19298620db86415ac83fc52a8e2d80190cf43fe580b01f9a32006c63c7d0215d8ca8db5c393b10c3227bc51953cfc00666363354d3e80227021d7e98816f77f6301b46f2a67e314090ce9352b01620aaba52c00400c600438ecf92a620191802d80543e0800e98813cf38db18f90321d2662b191c46d0628df812bc24c5cea, 0x995c3130dbed65a0093dc93389266d53cad18070527874818e8406ee7693d33adfd5c6a8df34ff180f6221014218da23200be62978b5c4e589f093bfc3804c1b35df24a40f22d2e8026620c03a1258f2dc0698129c7354cf0181a5c054c95440b002e4c66281804418a00f945df3100272c2c403f87100208c402c7a0cd98f10c700a27a7bbba005a334549d7dc8c500d238ae990102457d43101e3cf65234e655df1d063e32300551901578, 0x90531eac04015664203493ddc67eace002f8074607650b4a1438a004c6201a0a4bf0696c418038012535c00ea00e11e203e83334015e39062ac9145298cd4c40990f18a38e6010af4d318c00d1292b17002818d948b00d4320160d295c03f7228012cc40790301d0cdc17a863518a02f8f9e204e3fe0c4c926a74800559881cfb90ee009abe8019202950d5fc2867e79fb0cfb0fe1c41b661959032010603c3554d56863679f80238cfc04f, 0x946e0198f12f4d26317dc8033cc407a0896d0c6880600de027407735ac94922c00248092b694ced00d500c958f0080b0200643344874c41c0b051db2869881f50804e49f885af8f601119fc3c5c07e3c798a21920aa3008619a0d5a098093d70cdf26d2860d892b22505cea00090088ac23d9a31d58ec003c62854012f08d0806d86fd19f9c80700692d090620d86b42a081d98021d7f07f018a455efb6c34e60980268c52d78b702a53e029, 0x518a286a0a823595d3c913c63a34380098cf5346250a0042f2e26323372916637c056cfa00363d50a82806f3268008f8ee93d7a3813e862825c31ff810811c048b194afe7056634240c1ad1404a9fb275698a4c31685e18dbf840cd8f54032c0dac628916003f98806c48a4301597ac838601b79f1a29c050f71cac000a0a3500e232c01e24b363408f040159894af9003900fd36a1bbe4999160767a02815bc0bbc021155b05cb10c241, 0x631519b226334e004e7c49d524052e391f1a988222a005d18d212c9cac04b7774017c054da7003d98d5e658a6d00e0ae447f23148dec03b9284e30966980d047b75a3020306f059033f2384b3ec66034900338d3049f7f327a23f840018c386c10d120c4008f801b8c512f47f1901b88d0050a6268ca84ed866e3c7883198dc951014718a3bbc7fae93f7821f1e9e90dfd80328cad3c35c3d19b939600e401c75206158656f5d92da8108364, 0x7507310020e6e5893d1252081589a2d6a5350c510fd00034a08d9600d8c4861f80bf8c86d4b014a80206c680e500e045200d26406d88031c63867b97041901d7f841e014b51262bac548ca9f1d9258651cfe518dc3ad03784960f1efef001174ada25cc409b54d00bd106460011624351e006a029336800d46850d9bf6d80d4915427f4963ea0ea9801311a003780660279cd200205419e9e4a1b41ad04004b7229f53c66ea832091806c410, 0x9e4a41a6e01b40104970028cc7abc982738c50ca60089008bba2113c92c1299f018068da982e4a52125500b618a270c00d065409b4060c66a03480020c9c944006301b83911cb803f4f019334036253104b25044d51fd618a948a00346366f3a154c03f0e2800ea4b0e7700f1018158200d23428bfcb2a98900acc9228ca48f400120198f0495d2c3f81c80f00c4d08bad648cdd087005b19fbf14f5d294819582c3cc7ece1805800a09bd, 0x30c2310b04ceb7062000b412c8692d51805318810b249bb4a4277a02be3350b90eacd871093c9570cd822c006c014369a003294d60240060c6a224802a00a026b3e903191c492a0e34f11a001e8638337c05b98f203a7c001a702a0007292c2da4038cc520c800473d3dc3901ad1a03c7000709354a790c7d29a07e42bb996163b003a61e8be001da0363440d368666d434eef189c6df001001e9f6c56c002770e5eb89870bc0001e0c50470, 0x5dee325992001b29315ddc2d34c6cb9f3f24a525d127de518f341a4ff8c384c7dffb0052a15a5c0a4f5c7312721940e4a01380106c5c01e4c6cc26815ea4c822200537a228680086342701c95b9e88c9100300c51ce09afd32485e23ca204221900260682b594a32809ce408204321b88800fe62039a42ee804ca620003988119a004a18a4798041831c1ff94ea806693e1ec2312e029658d3103980ff7892c89689780656f7800549960530, 0x856f19f8f1e078c0340fbc036cc821ff006a98fdc397740008a31e00ba6207f8a6494684528003da50da5b0f511998688f4b600f5dfc0068698571804b19351ef277f4a181f812ac630142212a8656a81ba1d31521727fee314836600da0117f5cb2c58911e40044250cfa5006519b001200d692c57a192f4682e75000b8d04505014d014a8385df63144da801dc054012c2999930a12001c01e854e141601102b8008cc41075816da4c137b, 0x9647004205433880137299d178c6e2f33c12807434942ca4a62be1334c314328df1fcc40bc2015398f43f81f8f1a60b7b25169544d20f14cc8660300318c509f50ae649634b6010e6262a8df2c125849e001400d19929c9a31a883ceb26314849dd33863ac652668a5062d0943f18a188907fc92c67092d55870a39806d3d202255289324995055b26499020009807834281698d0d00500c119fa78600b464c00cd727863a4fb01a2a4f5545, 0x3e8249eb5a400146202e5403e92585f6003e0d38e0154d649e808ecb0603223f402f801088f80188100ad400a6310978b05ce62b711002b80108291df2a5200d84b9d61c06880be401067cd2f3d25a002359c8c5015c8e3a009c3a0df8431f7a39049cc86f6522a68cadc399f70499b41a003003d4780442c010ab9c25400c12b309ce49e21bd0d4c34f06cc047065090e80019880de2000961c18c6f4ae6493351f34c69af4729320d0d5f4, 0x646a02188d0e0b403285d402c0628e12a1551895a3a6f430131c04ba2e04255900100680ff89829006d826952a009a31f246264206c817d8c7a189832a2531667000718a3f1e008a3491da5d728c93117069998dde2711c73263bf87dbe31f39980034c663131acf24d815c504b18a02850878c4a3c9003acc525de80440cd03ec003402c275f3b0a9332d8d249064e79fbab43d203b47bfc320a79a04e064917944ff4c6e3c7806b8d01357, 0xa02313a472004c036834802c00849143a588ccc99c080061fbf1407f60367d1801a804ab6e007280d23240017012b4ad0d5801d2f5803e24a86f61dc900a15895d69496c05262de94d57d242b866f003b8810c9c04731ab31a0080fcc4f542880dbf463a4babdbc0c6c5e61af749993970cb6048531000e1284cff0010a504e6975a600faaa6670264939080de4c68f8309298101e10747518f8bccea00c380f7a089d886a39a9b59899672, 0xeb310166d14f893547a801ad870de709d78c55a4e00e33101cee016800e8c2cc4b067ec81000e807219e724c4a0037a018e0088c761dade9012c24e380717fa00fb01e2c1c00966487e7c0384662b0b8a9024b20df76c619b8e5c009262829f425352786f28063a4b00ec004800e3c2801baf4471a93e30054017a8cf9880243411601b357c2f580107e0105d0628e81cacf0c51877432418a0a65142663547a800acc4042293e80041979, 0x2c360188390aa0233715e4b8a40381c08f9a8c507e0942a021313f04a801b51ce0210c404bf94880c5100c5b9a015bbba01286580d3a4960078244b5d0006da86005c18a16d694d63140f541a84c68258805998ad1c3867718a331c005c0587b840d118a86551bf38d3dddd7c414a4354e067c04b2a11e8ccc621910ef9b0e44a6032c4aa3156fe7a0542d749050090b6c3e208cd0e3d54924a0800801f00252594c6c463a54180490135949, 0x3aa418a3cf8eb9832b7f080038c7a7f708132508f1e6c4e1ac92c40154631015db1d5870333074430e11c33ab100faa06037e31d4eda542067e44ac8b1992616c1a5218a1344a3ee3375671f6686545280fce0c94d29868301b2a7aeb8a65458093ce4c401a235cf00209e502cf0212816011a6273e941cb862ab7b815a98fe25d008d18a2fd53e58048741801792825f4c97780d9e53001e49abf68a780329663a57240502938007a4f4b29, 0x33008264868f86203944fb54c56df0b289a4f44e804bd3149a1404d664084c5ee18c822bc81ff0c51382005a4a4317858d262068e8021d87c22a177f8c54c4e1d9c320c052000a93227450fe8098344be2400d89e300a84a13d3600380330a29a4940202dec3280150c2736d318e9e3c01403353cf8e9812a8d9cad9398dd92200910209636a9ee34d715404e464e2351650a4b23d84aa102c30fae4100123d280188c6a66e80309881398, 0x9470013b9140156948863808b1282585b31e18849443f0c199b091054233f0d121981258ffb8ff50cc001400490241e88016663f013c0388030aef35b901204527aff18a3e8400223147ef00034637110c32b806d5531f8f31002f4c01063f090400d868203480451881b81605f4a1848200a001c29e006e466a9db3eee18d9f60952900e303a078600874400088c40469c12f00fc5ad007219ba30400c831426ae2865e88cf0005b01008f1, 0xf84963ae26b9c92c57d1f1806863234cdb80221d043501a08008cf746377300022067e71e0050bd2dddd7f9318a43a049c26312b4801e58701f980db8c514d5646a0212a7a014c31448280230c4ec910106a4fd3c3819d0242e2e84563142d98020464e14500268c5213c00ee31eac8601023142e31a5b004c023802d80204d5002d321bd773e100325899e4100686db000098d034e51cd31013961e6231b0d126540022528003d007c12e, 0x805561c179d086e6270bc4220066b09b412b0139d3e182418a058801f492c3d6400f007ae4a4d369880a840076024842c38dc34f8a8000fcc68687805118cd92b000431a448ef97a040224d63f406668ccc221881275000c62a376513fe6418a800c50686876800825286563dac0060d82f25c0348f3d29b408464124ab0c7cceb01221928273346663d0c3401086522e6805980a418563f57a240a6752cc4b69fc0100c40b3d006149518bc, 0x20f64a0928ac9c83298e2a0ac8c7ea39bab798c5b2e008f3243ace00503341d8197dd890eb3bfb80109199705b01a8fb297cc0304ce2677c0104ae004b3150e083d28324c87ec08a62016b5d26467e234001431256285ec31a1c4baea5c0308c31331189ceaa129600f42b701b10260ded211463c11459cb86b2a5633a600ae37198211a68a6529a8654617612dcc670e200230021b814fc302030fa0bfa02777b400f862874d88b20cd51eb, 0x10800ebaa800e493d12264f0003c03f80d48d007fa00ea4a49ea0823063c7eb80114628bfabbd33d145ad3270021a79abad20133dc80a98c4ee3940538d3630151ab3159c800d60340015993ecc784fbc5188c5079a25650151a4400226247bac01f0c408d2004118811ef7a2319e481008dc0420d58009527899300b60ca81c22599320b24400a204d017401846345d2803900a88c7006461c20a2009464c03e83b4069253c803e98d80d2, 0x69800409c4d74834c25400360c406f1bf99190a3d894ac18a1daeacd001168b0bb7c0805c0ac55007dddd00c30153a02071464919edd3acc6c762300da4fc24161c931a980cd81a31d6420854de882a0016398940b900d64960824919e92d5504002c010c72001a8020d9742b931a38c8eb6e31d0d313c2927e0bd32358d09e7e000118a3b003b486362670043527ef5dc506a4c0c7508e501b1fee01e80124e1884400b253c8c5a0c515c0, 0x17619aba9aee0462171122a946903e312b198a625d00ca19e992e010e940161c5be8686482b0870c52417260b61c194e01ae027140d606001e68c9ee180c4ad2426a01546ea0078333140ccdad27ed53800a99058f67ed54a1b0e0002cc3884d000e4c6e80603cf18860298b1b19bb7c2a4da03547ae48d92589de80798c51a0600d34a42a3ef670028511402c0c6e8e18009b120c4900c91a6c82a002692c4931afd06282d335810020bc2, 0x42a819599bd24e033566a414500106b5806218808463ddf18fa1da000c64247543b6d2963239bdd80763c65d0600f16c600be0080fce4ce527aac29dc88cd41c87a564a4bbda00f094d7439d3e929e0ea494d25682c40035004305e0052f448c2d002c64e5f44b928c5096241d04a1bd945864c3c8970035c63a48200600cf10ee0320013a5c313d63148f61953c0380a0045f8c522773d1e18a1cde01ba3151aec0148054032007f80c1e23, 0x7fc0007337e007263068bd1b08628e32005d989d92b007d4a42de800c4c388ca07590c570e2005e24f243a2422020980c010233f373545f5258d06c5ffa525805013e0140152011a3345424014129308ab1fd193c8ee285a7a2303f338262047a8a05003e9e01a89a4d8243685b19397ac0054620104a64dc686a81b24380d06e65f66499848200bc63d5238016404ac2e0a56990d18f25c8324b0baa70633349f002e4c7c85f86f90d3d922, 0x73a7027b8e4c11ac3f0905ada401e44e0068988020100701a018c87d926370011a024080c0ebc7980c575811c47a21c0800ac0359070003409d207124300a0b8128a818a4412eaf092c6a9da1d462a2342c89804debb53e001497b8133ec543c4248e406cf8933a00c514ac65b431a2d7a095c343090c0021258a23805cb0e0b0b353349e9ccc58ea0491542574c62902fba0380a4b2d1fc000ebe2000ec0282a9e7d9c0501351481002022e, 0x11a318f85d000da3355cf05fe8c9640a381680f048e00a93219b9a018202664b6532127ef6500118ca955e0813324348400a600f4f0c006c04c549a39b804d00c002f18a44700406629863403bc01107e8014253217a7f7b320aa069afe009849d2a78010d8e39a281680b931700098188088a62865f400b8c627eaa9b600dd5f400f461c25a915f402b655e64be4a03974379a4fc78f181261c094ccbae31f3dc801f0c4e71e04c524f0e7b, 0x3dca61f86880b10c3885d50b20698f3d0066a4c1c0600ed199851401b000d4d8a0d50010ce12155b109d541ae30042d58014a3498e48a3f863a206402d80d822900b91a4be5446d600826709670c8047ec30800c0cad007802103aad68e00f5d6001b0c56fc51d400071b5380f00141858d89a6592d75fb64c7a52633980cfc0fc8e4e18aa23315a034219fc0138010f81a9003d1136a01ea194a0a2d2ca0412880d28c666bbfc2a29921fb0, 0xa43103e7401aa314844418dd27aa0531eca5247db04284a4a49c48cc0368a042560c428c7806730e1b677b0519a8f34007662612b402ecc68ea4013da5383b2741f1921c62017031c80b403c806c37628de8d30f5780724a6939601689424ed1940c628a8d41480d0c17a289431baa8297ca3377c6c01d4038917c2118c7d50302b118da79a0c0ef5411112194026eee808080758a200c4019034665d03434f345cc52a8772b6c500ddcc0, 0x88318090c031a9322e4c16b929615bc4a3993c2ad00533130bca01ec6202bb40124092e4a01ce00c56dc8a1c32107aa0128627278002c926ce9e005b813075401451944139258c0498c0402dc03c66f847500fc1c888c30043dc4022803f5e00c69c09aa8d3ecd0098783001531044da0016627189a4880638470b4ea98f4a48343a3148f26fe5401053d18d9c01e720008800a17d975a3194807e27f831520500258c9ab3d34540c51fc2, 0x253701b049a01e26202035c98c66ed449af4a4fdef02c0262188d12a940287a814dc403ac81165a24d446a00e501e134c006004c3d180254c40fde00408125903299e0159e4a0d70f5459ac0219258f50a99500fd77f71581a000fe002e3142ffd9dac66e40c9d000c56007003a013869225f801f73000000092e550177812d8771dfc61c454044fe3310515229809e0e4270a80d18b6000f4961ca101500425d567e54c7885135481880145, 0x51c7320a9f801faf447380008cc40ca939b880207ea0b7800f8802004e64c50ea5d6c0827e200120c51d3c494800e108e976032b620c01cd2927698051988085692501a639ccebbac4045a80040c4095b006680444d5002b9283b8c01e2f444cf0be4002660318e1189a43f90da31e2082007431c753a07ecc8217880398021e4077953149028fce89545f7c0160c4076303650c51ee803ba194b594012c03d5b700444650c3a803f0151964, 0x9249620b10602e23297f35ed3069c4348ca19898c8400771a62a4c49ca03c56f4032cc405b4ba988ca58fd77431a790285dd2009291402e0c41052000530e0bd163333248236469e315620c003e4a104600350cd15689646004bcf800b0c3879a80a180247a49d020078047957718a189c8acc641211801b126e281b8e28c75b89540c32d00bb303231d905c54646289b000568cddca600fe32107c6017ac39470e7e44656d06cb4500cc78f, 0x8ca01fa018009492c8d7402a465265320678cdcbe82ce9024b7c2015c93c8a14020cc530c4001d9880f5c240661c3350a9c864130180351258919cca300a189f5cc53132b6e01b0620892257446283331f3a9881a5774894a5aa0cc3ce33530180f9ccaa1e025a824dd8832ef51a0094e05d293d51f5a8b0084ac497388c7e1c5045162496161a1832952b094c4056522805e0126415485b18a1e3c2c7e0273da40358068082000d18803ed, 0x7432c0fd6d03cc547ccc245001074e00daa4c915f9a0c0121946015034079618b3066002235a40078c8219cd026316d040a92d05e80650666366804f8ccd56e37b91a4bef8106c64c5c1001bc0825dd00318d2608c64757aa20f2f9d09483941ff1cc4a2343f2a01207db4b51007be3622ea3144de5ee4805023d806700c1160972b3103097243604e380801806367d2cb65802182500be4961e7c8456054056403acc40565804d80f47c9, 0x9a934a71ee505b5250337801fcc40f10b88e0c6c5a601f41a5800e01c80301cc803a0080da6827c98a41a418ba310041f3ff062090fc718409f093806fbd1120a005f4a48f3201ec028174cea20c6668cb71418f59c224f26240a1e70446366e060a88c9c00380f00c940b9003c31eb536008cc490151c45cc930c5001e004425b7f5501e00a6010e3354ad802c8c4a0858000988044a00b10203b8e007692c731c66f0c6ef4745dca529805, 0x571d18a39160172632444834d1292533ba8f19215f26f1a18fbee0209832930c40254c9c63880472508f3e00ba007aadc01020337e28f32403a363003330fd92b013d1941e9c062c33584d003fc01023480550cda183007b49e33e2f9c032a05411a9d258701006180fce3c8a44195ae523b2494157386358c9e323805f807199a8a127a613eed676009722835c9282afaa58524c43ad00bf01e9b5e008201a8fd4004c09c66fca72190c4a6, 0x3b9631021fac6ea3344ae5e54c050807aa0798f2024007f3210586402064876aa68e129617880fa8c750515de261faaa6200a01e4440008c668fbc280d0045ffd003231b3cc0010c92c004d8cb406ea8d0349804543556b101308e6027663539a53d2c084f4949460d0835e02ba49f8a06152a92c013d7570c566482f518c5202c4bdf61c3dda10303334f0e108d29876480568099ea70c9a024ae7c00c492c892002692667d280518c7e02c, 0x4314a0b2ca6264221926b3806c4b13add24c93bd00e831039d72896314612107d8c60c23c07a003982210e20263db66cbc011817c027866e71e00550cd5f3a00a74a60cd60088328419d89f18708c1043718ad74300e94960dba0024c397e28005006ab0bb5fe80407001cf049aacf0fd00f4441e49840628af8198530f617528f11a11143019603450600134c40f16802b8d093eb6bc000403a8ea1002b61c1ebb462815b800da4f5f6a, 0xf63260fd6008e0485f44f0e0c820e6bd9500d1b9b754c00eb9812462641620e1be0026bc23f8124b01d400de31f9f4a03883406c482b5062a470b24abd1187000d349e29ce012003c853a00b8c947e23dd898d57847f8200e4140016663116f800c18705d54d6bb0e08b048a718a1862012694814a94624c4201fb5768cad8b38aec18a14f2016c64c5b5816c066ee398f01a4c4e02496049e0c9524003418dec0170c41213c32300219f4, 0x2ea18db1d801d694284a8003528110e8050bd117f5005a4a681d8f594f4c4b9c0185284916129c1881e8d002049e180e01fc93d6f39d6e0078d7d00598cc43fe00c0496108b23fa64e334d0fc8c9a07e007d0d6176735db18f92889fb031d8dee2b7c038c2c80158ca1c3c00994a0124e3b9c9378710e000c52627003f24b11cb9405327349d059604274f804fc662ee684d00d04ebb12f401b32f3095263179f1f081258f4729bb8c75df1, 0x7c100211ff0002e05854100214628b52c14b0c74be8926c18abe36006604088bc00d8c400763a338ca1ffd392b0043ffae4a40376a240070c403e4804399213ab0096193b256012e3423aac0030010e6e005298c90ba24f20040096531802855900aa066898325b8812192800704a41bd828f43373b1002c406c888c65e0cdc7d9042b00414ce07580084090308462aaa0802a3109b2112b33101a5c01349420690cce0086f88004c49413ad, 0x213032d30c6b1800134a4e174803ee2ab2f5193d18f0036007b256004c33d0afc32e0c42c598e6f8d3c34c809b31eaa0d144c3282ee0029407e6e6804624d856800ce31005c8005802a59d1c3c403831a0074989c90c495000e0a30ff7c92c32a593286504a83f6c98801b23ba718a394c000004e1f050b54c6cd27003fbd2105b7bb17aa02b205c631e2744a730628d53803d9881cd92e3b61c0de32a8c03634a40308050539ca120c9c11f, 0xcee31a2cc737d66358ce00065ea90a7000a8c9d1b100e71a0b9c0003e0343cd00290654d13824f8cd5a067e921a607123a9065529e5d738c6c197253b98818b32cef0183d98009a33420d5a7b069e67206ee0c514124b7901b1c2801d232982fdf1a5258458038c18d0cd5002331019ba004c94c30680039278818806425214e225d50211ed2019831436300a0cc9e19741ff3d10a79755a1992af6018c92c62480350c6670ea9c280219aa, 0x7e31035950432627711006b8c823410007804ca02297818a039095cc314123807c8c52b37803624b205229b518a42eb259464b620e0028654ae125f4990df1b00237a2132e811600f1e3c02a127ec95c0200d2184b38c24aaa690091693f1aedec4c04e0bd000d98c45eb871019b86980fd831c387cea60637003bf2e24fd87063051a1b0e046c23143b12673c04c40700e98c551b100f43100d65197832905140ba8c68b8704ba0ca45d7, 0x928d02a24ea7a2231d5ca4ec58c56f8d80670c983e97f6001e0afb268e64e62427dbcc6e3ec9a1e25222286ba718a151c82e201e6a92629cc40e39a1279898761001861c1ce2011863d72dc030c69c50c4908812542700261a5869258be01d8dc414f928265396660cf10bb00611938f0532f431506c4d8d06365cc80eb003e1278ac67a6015cbf76c4869580188c62c238053c94167a019318ec71400ec9482c340244628849001e8c51bd0, 0x1dc69c542cca60100847],
  #[0x0, 0x2, 0x4, 0x8, 0x20, 0x200, 0x1, 0xa, 0x10, 0x80, 0x6, 0x4000, 0x12, 0x220, 0xc, 0x22, 0x10000, 0x2000, 0x8000, 0x3e, 0x14, 0x208, 0x10000000, 0x24, 0x18, 0x8000000, 0x210, 0x100000228, 0x480020000200, 0x200002001423e, 0x4084, 0x220040305c03e, 0x44a00081400a7, 0x211, 0xa30014c206, 0x10000000803f, 0x21a8616b7fabf, 0x30b801000023f, 0x1000040000211, 0xa0410080a633, 0x2000025014, 0x100803e, 0x100300004006, 0xa00004000, 0x81941423e, 0x2000000200e, 0x7ff7ddb67e2bf, 0x1000002, 0x801100000a, 0x3039a15f7aa7f, 0xa020022c, 0x4000800000006, 0xb000010203e, 0x300001000023e, 0x20010010882, 0x4200000000202, 0x400004012be, 0x401002004, 0x2a0d56457faff, 0x944a82558abf, 0x2408012800080, 0x7f4d837e2bf, 0x12000000022e4, 0x18020022012, 0x5800002006, 0x17dd98262bf, 0x4000b3df7f2bf, 0x800a23e, 0x20025c801, 0x80040080b, 0x1032084, 0x1040208, 0x6009000080, 0x709f00102a0be, 0x220040100223f, 0x600080000023f, 0x1000008000003, 0x1104880e, 0x5240000011030, 0x5fc3da6f7c23f, 0x4000404142015, 0xda10041020be, 0x100006000e228, 0xa800216823e, 0x200002001a29f, 0x818419812, 0x201044812, 0x400084, 0x400004020be, 0x1140010, 0x8500002, 0x1010010000084, 0x140040000220, 0x97f978f762be, 0x218000000022, 0x104000000002e, 0x101008800023f, 0x200000000003f, 0x424000800000a, 0x56f6edd6e2bf, 0x416ee1657fa3f, 0x7fd94b777fbbf, 0x9802040021c, 0x82810231, 0x44208dd560be, 0x6f42a6dd7fabf, 0x4409010, 0x3a840114a23e, 0x1008010284, 0x80002040020, 0x400000200208, 0x8030006, 0x819434008, 0x209a02400601e, 0x100405000002c, 0x4108006221, 0x20488ba75a23f, 0x3d402d7eabe, 0x2000000012, 0x80600000023e, 0x22822100001a, 0x400a878274000, 0x303a000c4e2bf, 0x4081943a23f, 0x5e4642800aabf, 0x120081021e2bf, 0x122b25597fabf, 0x726881f574a3f, 0x200081001e23f, 0x600080000a211, 0x4c4600800223f, 0x200219, 0x79bde77a7e2bf, 0x3a7f9784702bf, 0x3f959bd7e3bf, 0x4838420b62050, 0x441104028235, 0x43e3faf77f3bf, 0x5260099f7e23f, 0x5000000000a00, 0x8001041812, 0x80002000e00a, 0x8008004017, 0x2200401a, 0x200d04426423c, 0x20028060058a0, 0x6d038240642bf, 0x12220025018, 0x259fc5f76e2bf, 0x2ac0081c782be, 0x8002048012, 0x200081949a2a7, 0x104180401e23f, 0x28642d06dabf, 0x5802000a0e23f, 0x812204, 0x281c084, 0x1020020006, 0x800420092, 0x837c04d762bf]⟩⟩
def rootFact : Fact := (root.mask, root.bank, root.fuel+1, root.goal)
def rootCuts : List Fact := [p0Fact, p1Fact, p2Fact, p3Fact, p4Fact, p5Fact, p7Fact, p8Fact, p10Fact, p13Fact, p14Fact, p15Fact, p16Fact, p17Fact, p18Fact, p19Fact, p20Fact, p21Fact, p22Fact, p26Fact, p27Fact, p28Fact, p29Fact, p30Fact, p31Fact, p32Fact, p33Fact, p34Fact, p35Fact, p36Fact, p37Fact, p38Fact, p39Fact, p40Fact, p41Fact, p42Fact, p43Fact, p44Fact, p45Fact, p46Fact, p47Fact, p48Fact, p49Fact, p50Fact, p51Fact, p52Fact, p53Fact, p54Fact, p55Fact, p56Fact, p57Fact]
theorem rootKnown : Known rootCuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) p57Lower) p56Lower) p55Lower) p54Lower) p53Lower) p52Lower) p51Lower) p50Lower) p49Lower) p48Lower) p47Lower) p46Lower) p45Lower) p44Lower) p43Lower) p42Lower) p41Lower) p40Lower) p39Lower) p38Lower) p37Lower) p36Lower) p35Lower) p34Lower) p33Lower) p32Lower) p31Lower) p30Lower) p29Lower) p28Lower) p27Lower) p26Lower) p22Lower) p21Lower) p20Lower) p19Lower) p18Lower) p17Lower) p16Lower) p15Lower) p14Lower) p13Lower) p10Lower) p8Lower) p7Lower) p5Lower) p4Lower) p3Lower) p2Lower) p1Lower) p0Lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock0 : treeBlock 0 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock48 : treeBlock 48 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock96 : treeBlock 96 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock144 : treeBlock 144 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock192 : treeBlock 192 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock240 : treeBlock 240 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock288 : treeBlock 288 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock336 : treeBlock 336 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock384 : treeBlock 384 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock432 : treeBlock 432 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock480 : treeBlock 480 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock528 : treeBlock 528 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock576 : treeBlock 576 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock624 : treeBlock 624 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock672 : treeBlock 672 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock720 : treeBlock 720 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock768 : treeBlock 768 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock816 : treeBlock 816 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock864 : treeBlock 864 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock912 : treeBlock 912 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock960 : treeBlock 960 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock1008 : treeBlock 1008 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock1056 : treeBlock 1056 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock1104 : treeBlock 1104 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock1152 : treeBlock 1152 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock1200 : treeBlock 1200 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock1248 : treeBlock 1248 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock1296 : treeBlock 1296 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock1344 : treeBlock 1344 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock1392 : treeBlock 1392 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock1440 : treeBlock 1440 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock1488 : treeBlock 1488 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock1536 : treeBlock 1536 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock1584 : treeBlock 1584 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock1632 : treeBlock 1632 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock1680 : treeBlock 1680 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock1728 : treeBlock 1728 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock1776 : treeBlock 1776 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock1824 : treeBlock 1824 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock1872 : treeBlock 1872 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock1920 : treeBlock 1920 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock1968 : treeBlock 1968 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock2016 : treeBlock 2016 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock2064 : treeBlock 2064 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock2112 : treeBlock 2112 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock2160 : treeBlock 2160 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock2208 : treeBlock 2208 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock2256 : treeBlock 2256 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock2304 : treeBlock 2304 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock2352 : treeBlock 2352 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock2400 : treeBlock 2400 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock2448 : treeBlock 2448 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock2496 : treeBlock 2496 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock2544 : treeBlock 2544 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock2592 : treeBlock 2592 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock2640 : treeBlock 2640 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock2688 : treeBlock 2688 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock2736 : treeBlock 2736 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock2784 : treeBlock 2784 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock2832 : treeBlock 2832 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock2880 : treeBlock 2880 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock2928 : treeBlock 2928 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock2976 : treeBlock 2976 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock3024 : treeBlock 3024 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock3072 : treeBlock 3072 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock3120 : treeBlock 3120 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock3168 : treeBlock 3168 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock3216 : treeBlock 3216 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock3264 : treeBlock 3264 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock3312 : treeBlock 3312 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock3360 : treeBlock 3360 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock3408 : treeBlock 3408 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock3456 : treeBlock 3456 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock3504 : treeBlock 3504 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock3552 : treeBlock 3552 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock3600 : treeBlock 3600 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock3648 : treeBlock 3648 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock3696 : treeBlock 3696 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock3744 : treeBlock 3744 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock3792 : treeBlock 3792 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock3840 : treeBlock 3840 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock3888 : treeBlock 3888 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock3936 : treeBlock 3936 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock3984 : treeBlock 3984 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock4032 : treeBlock 4032 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock4080 : treeBlock 4080 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock4128 : treeBlock 4128 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock4176 : treeBlock 4176 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock4224 : treeBlock 4224 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock4272 : treeBlock 4272 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock4320 : treeBlock 4320 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock4368 : treeBlock 4368 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock4416 : treeBlock 4416 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock4464 : treeBlock 4464 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock4512 : treeBlock 4512 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock4560 : treeBlock 4560 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock4608 : treeBlock 4608 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock4656 : treeBlock 4656 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock4704 : treeBlock 4704 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock4752 : treeBlock 4752 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock4800 : treeBlock 4800 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock4848 : treeBlock 4848 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock4896 : treeBlock 4896 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock4944 : treeBlock 4944 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock4992 : treeBlock 4992 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock5040 : treeBlock 5040 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock5088 : treeBlock 5088 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock5136 : treeBlock 5136 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock5184 : treeBlock 5184 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock5232 : treeBlock 5232 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock5280 : treeBlock 5280 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock5328 : treeBlock 5328 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock5376 : treeBlock 5376 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock5424 : treeBlock 5424 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock5472 : treeBlock 5472 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock5520 : treeBlock 5520 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock5568 : treeBlock 5568 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock5616 : treeBlock 5616 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock5664 : treeBlock 5664 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock5712 : treeBlock 5712 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock5760 : treeBlock 5760 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock5808 : treeBlock 5808 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock5856 : treeBlock 5856 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock5904 : treeBlock 5904 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock5952 : treeBlock 5952 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock6000 : treeBlock 6000 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock6048 : treeBlock 6048 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock6096 : treeBlock 6096 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock6144 : treeBlock 6144 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock6192 : treeBlock 6192 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock6240 : treeBlock 6240 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock6288 : treeBlock 6288 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock6336 : treeBlock 6336 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock6384 : treeBlock 6384 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock6432 : treeBlock 6432 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock6480 : treeBlock 6480 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock6528 : treeBlock 6528 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock6576 : treeBlock 6576 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock6624 : treeBlock 6624 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock6672 : treeBlock 6672 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock6720 : treeBlock 6720 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock6768 : treeBlock 6768 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock6816 : treeBlock 6816 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock6864 : treeBlock 6864 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock6912 : treeBlock 6912 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock6960 : treeBlock 6960 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock7008 : treeBlock 7008 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock7056 : treeBlock 7056 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock7104 : treeBlock 7104 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock7152 : treeBlock 7152 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock7200 : treeBlock 7200 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock7248 : treeBlock 7248 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock7296 : treeBlock 7296 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock7344 : treeBlock 7344 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock7392 : treeBlock 7392 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock7440 : treeBlock 7440 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock7488 : treeBlock 7488 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock7536 : treeBlock 7536 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock7584 : treeBlock 7584 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock7632 : treeBlock 7632 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock7680 : treeBlock 7680 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock7728 : treeBlock 7728 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock7776 : treeBlock 7776 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock7824 : treeBlock 7824 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock7872 : treeBlock 7872 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock7920 : treeBlock 7920 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock7968 : treeBlock 7968 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock8016 : treeBlock 8016 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock8064 : treeBlock 8064 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock8112 : treeBlock 8112 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock8160 : treeBlock 8160 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock8208 : treeBlock 8208 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock8256 : treeBlock 8256 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock8304 : treeBlock 8304 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock8352 : treeBlock 8352 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock8400 : treeBlock 8400 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock8448 : treeBlock 8448 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock8496 : treeBlock 8496 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock8544 : treeBlock 8544 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock8592 : treeBlock 8592 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock8640 : treeBlock 8640 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock8688 : treeBlock 8688 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock8736 : treeBlock 8736 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock8784 : treeBlock 8784 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock8832 : treeBlock 8832 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock8880 : treeBlock 8880 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock8928 : treeBlock 8928 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock8976 : treeBlock 8976 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock9024 : treeBlock 9024 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock9072 : treeBlock 9072 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock9120 : treeBlock 9120 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock9168 : treeBlock 9168 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock9216 : treeBlock 9216 48 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBlock9264 : treeBlock 9264 18 (root.check rootCuts) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootAll : treeBlock 0 9282 (root.check rootCuts) = true := (@treeBlock_merge 0 4656 4626 (root.check rootCuts) (@treeBlock_merge 0 2304 2352 (root.check rootCuts) (@treeBlock_merge 0 1152 1152 (root.check rootCuts) (@treeBlock_merge 0 576 576 (root.check rootCuts) (@treeBlock_merge 0 288 288 (root.check rootCuts) (@treeBlock_merge 0 144 144 (root.check rootCuts) (@treeBlock_merge 0 48 96 (root.check rootCuts) rootBlock0 (@treeBlock_merge 48 48 48 (root.check rootCuts) rootBlock48 rootBlock96)) (@treeBlock_merge 144 48 96 (root.check rootCuts) rootBlock144 (@treeBlock_merge 192 48 48 (root.check rootCuts) rootBlock192 rootBlock240))) (@treeBlock_merge 288 144 144 (root.check rootCuts) (@treeBlock_merge 288 48 96 (root.check rootCuts) rootBlock288 (@treeBlock_merge 336 48 48 (root.check rootCuts) rootBlock336 rootBlock384)) (@treeBlock_merge 432 48 96 (root.check rootCuts) rootBlock432 (@treeBlock_merge 480 48 48 (root.check rootCuts) rootBlock480 rootBlock528)))) (@treeBlock_merge 576 288 288 (root.check rootCuts) (@treeBlock_merge 576 144 144 (root.check rootCuts) (@treeBlock_merge 576 48 96 (root.check rootCuts) rootBlock576 (@treeBlock_merge 624 48 48 (root.check rootCuts) rootBlock624 rootBlock672)) (@treeBlock_merge 720 48 96 (root.check rootCuts) rootBlock720 (@treeBlock_merge 768 48 48 (root.check rootCuts) rootBlock768 rootBlock816))) (@treeBlock_merge 864 144 144 (root.check rootCuts) (@treeBlock_merge 864 48 96 (root.check rootCuts) rootBlock864 (@treeBlock_merge 912 48 48 (root.check rootCuts) rootBlock912 rootBlock960)) (@treeBlock_merge 1008 48 96 (root.check rootCuts) rootBlock1008 (@treeBlock_merge 1056 48 48 (root.check rootCuts) rootBlock1056 rootBlock1104))))) (@treeBlock_merge 1152 576 576 (root.check rootCuts) (@treeBlock_merge 1152 288 288 (root.check rootCuts) (@treeBlock_merge 1152 144 144 (root.check rootCuts) (@treeBlock_merge 1152 48 96 (root.check rootCuts) rootBlock1152 (@treeBlock_merge 1200 48 48 (root.check rootCuts) rootBlock1200 rootBlock1248)) (@treeBlock_merge 1296 48 96 (root.check rootCuts) rootBlock1296 (@treeBlock_merge 1344 48 48 (root.check rootCuts) rootBlock1344 rootBlock1392))) (@treeBlock_merge 1440 144 144 (root.check rootCuts) (@treeBlock_merge 1440 48 96 (root.check rootCuts) rootBlock1440 (@treeBlock_merge 1488 48 48 (root.check rootCuts) rootBlock1488 rootBlock1536)) (@treeBlock_merge 1584 48 96 (root.check rootCuts) rootBlock1584 (@treeBlock_merge 1632 48 48 (root.check rootCuts) rootBlock1632 rootBlock1680)))) (@treeBlock_merge 1728 288 288 (root.check rootCuts) (@treeBlock_merge 1728 144 144 (root.check rootCuts) (@treeBlock_merge 1728 48 96 (root.check rootCuts) rootBlock1728 (@treeBlock_merge 1776 48 48 (root.check rootCuts) rootBlock1776 rootBlock1824)) (@treeBlock_merge 1872 48 96 (root.check rootCuts) rootBlock1872 (@treeBlock_merge 1920 48 48 (root.check rootCuts) rootBlock1920 rootBlock1968))) (@treeBlock_merge 2016 144 144 (root.check rootCuts) (@treeBlock_merge 2016 48 96 (root.check rootCuts) rootBlock2016 (@treeBlock_merge 2064 48 48 (root.check rootCuts) rootBlock2064 rootBlock2112)) (@treeBlock_merge 2160 48 96 (root.check rootCuts) rootBlock2160 (@treeBlock_merge 2208 48 48 (root.check rootCuts) rootBlock2208 rootBlock2256)))))) (@treeBlock_merge 2304 1152 1200 (root.check rootCuts) (@treeBlock_merge 2304 576 576 (root.check rootCuts) (@treeBlock_merge 2304 288 288 (root.check rootCuts) (@treeBlock_merge 2304 144 144 (root.check rootCuts) (@treeBlock_merge 2304 48 96 (root.check rootCuts) rootBlock2304 (@treeBlock_merge 2352 48 48 (root.check rootCuts) rootBlock2352 rootBlock2400)) (@treeBlock_merge 2448 48 96 (root.check rootCuts) rootBlock2448 (@treeBlock_merge 2496 48 48 (root.check rootCuts) rootBlock2496 rootBlock2544))) (@treeBlock_merge 2592 144 144 (root.check rootCuts) (@treeBlock_merge 2592 48 96 (root.check rootCuts) rootBlock2592 (@treeBlock_merge 2640 48 48 (root.check rootCuts) rootBlock2640 rootBlock2688)) (@treeBlock_merge 2736 48 96 (root.check rootCuts) rootBlock2736 (@treeBlock_merge 2784 48 48 (root.check rootCuts) rootBlock2784 rootBlock2832)))) (@treeBlock_merge 2880 288 288 (root.check rootCuts) (@treeBlock_merge 2880 144 144 (root.check rootCuts) (@treeBlock_merge 2880 48 96 (root.check rootCuts) rootBlock2880 (@treeBlock_merge 2928 48 48 (root.check rootCuts) rootBlock2928 rootBlock2976)) (@treeBlock_merge 3024 48 96 (root.check rootCuts) rootBlock3024 (@treeBlock_merge 3072 48 48 (root.check rootCuts) rootBlock3072 rootBlock3120))) (@treeBlock_merge 3168 144 144 (root.check rootCuts) (@treeBlock_merge 3168 48 96 (root.check rootCuts) rootBlock3168 (@treeBlock_merge 3216 48 48 (root.check rootCuts) rootBlock3216 rootBlock3264)) (@treeBlock_merge 3312 48 96 (root.check rootCuts) rootBlock3312 (@treeBlock_merge 3360 48 48 (root.check rootCuts) rootBlock3360 rootBlock3408))))) (@treeBlock_merge 3456 576 624 (root.check rootCuts) (@treeBlock_merge 3456 288 288 (root.check rootCuts) (@treeBlock_merge 3456 144 144 (root.check rootCuts) (@treeBlock_merge 3456 48 96 (root.check rootCuts) rootBlock3456 (@treeBlock_merge 3504 48 48 (root.check rootCuts) rootBlock3504 rootBlock3552)) (@treeBlock_merge 3600 48 96 (root.check rootCuts) rootBlock3600 (@treeBlock_merge 3648 48 48 (root.check rootCuts) rootBlock3648 rootBlock3696))) (@treeBlock_merge 3744 144 144 (root.check rootCuts) (@treeBlock_merge 3744 48 96 (root.check rootCuts) rootBlock3744 (@treeBlock_merge 3792 48 48 (root.check rootCuts) rootBlock3792 rootBlock3840)) (@treeBlock_merge 3888 48 96 (root.check rootCuts) rootBlock3888 (@treeBlock_merge 3936 48 48 (root.check rootCuts) rootBlock3936 rootBlock3984)))) (@treeBlock_merge 4032 288 336 (root.check rootCuts) (@treeBlock_merge 4032 144 144 (root.check rootCuts) (@treeBlock_merge 4032 48 96 (root.check rootCuts) rootBlock4032 (@treeBlock_merge 4080 48 48 (root.check rootCuts) rootBlock4080 rootBlock4128)) (@treeBlock_merge 4176 48 96 (root.check rootCuts) rootBlock4176 (@treeBlock_merge 4224 48 48 (root.check rootCuts) rootBlock4224 rootBlock4272))) (@treeBlock_merge 4320 144 192 (root.check rootCuts) (@treeBlock_merge 4320 48 96 (root.check rootCuts) rootBlock4320 (@treeBlock_merge 4368 48 48 (root.check rootCuts) rootBlock4368 rootBlock4416)) (@treeBlock_merge 4464 96 96 (root.check rootCuts) (@treeBlock_merge 4464 48 48 (root.check rootCuts) rootBlock4464 rootBlock4512) (@treeBlock_merge 4560 48 48 (root.check rootCuts) rootBlock4560 rootBlock4608))))))) (@treeBlock_merge 4656 2304 2322 (root.check rootCuts) (@treeBlock_merge 4656 1152 1152 (root.check rootCuts) (@treeBlock_merge 4656 576 576 (root.check rootCuts) (@treeBlock_merge 4656 288 288 (root.check rootCuts) (@treeBlock_merge 4656 144 144 (root.check rootCuts) (@treeBlock_merge 4656 48 96 (root.check rootCuts) rootBlock4656 (@treeBlock_merge 4704 48 48 (root.check rootCuts) rootBlock4704 rootBlock4752)) (@treeBlock_merge 4800 48 96 (root.check rootCuts) rootBlock4800 (@treeBlock_merge 4848 48 48 (root.check rootCuts) rootBlock4848 rootBlock4896))) (@treeBlock_merge 4944 144 144 (root.check rootCuts) (@treeBlock_merge 4944 48 96 (root.check rootCuts) rootBlock4944 (@treeBlock_merge 4992 48 48 (root.check rootCuts) rootBlock4992 rootBlock5040)) (@treeBlock_merge 5088 48 96 (root.check rootCuts) rootBlock5088 (@treeBlock_merge 5136 48 48 (root.check rootCuts) rootBlock5136 rootBlock5184)))) (@treeBlock_merge 5232 288 288 (root.check rootCuts) (@treeBlock_merge 5232 144 144 (root.check rootCuts) (@treeBlock_merge 5232 48 96 (root.check rootCuts) rootBlock5232 (@treeBlock_merge 5280 48 48 (root.check rootCuts) rootBlock5280 rootBlock5328)) (@treeBlock_merge 5376 48 96 (root.check rootCuts) rootBlock5376 (@treeBlock_merge 5424 48 48 (root.check rootCuts) rootBlock5424 rootBlock5472))) (@treeBlock_merge 5520 144 144 (root.check rootCuts) (@treeBlock_merge 5520 48 96 (root.check rootCuts) rootBlock5520 (@treeBlock_merge 5568 48 48 (root.check rootCuts) rootBlock5568 rootBlock5616)) (@treeBlock_merge 5664 48 96 (root.check rootCuts) rootBlock5664 (@treeBlock_merge 5712 48 48 (root.check rootCuts) rootBlock5712 rootBlock5760))))) (@treeBlock_merge 5808 576 576 (root.check rootCuts) (@treeBlock_merge 5808 288 288 (root.check rootCuts) (@treeBlock_merge 5808 144 144 (root.check rootCuts) (@treeBlock_merge 5808 48 96 (root.check rootCuts) rootBlock5808 (@treeBlock_merge 5856 48 48 (root.check rootCuts) rootBlock5856 rootBlock5904)) (@treeBlock_merge 5952 48 96 (root.check rootCuts) rootBlock5952 (@treeBlock_merge 6000 48 48 (root.check rootCuts) rootBlock6000 rootBlock6048))) (@treeBlock_merge 6096 144 144 (root.check rootCuts) (@treeBlock_merge 6096 48 96 (root.check rootCuts) rootBlock6096 (@treeBlock_merge 6144 48 48 (root.check rootCuts) rootBlock6144 rootBlock6192)) (@treeBlock_merge 6240 48 96 (root.check rootCuts) rootBlock6240 (@treeBlock_merge 6288 48 48 (root.check rootCuts) rootBlock6288 rootBlock6336)))) (@treeBlock_merge 6384 288 288 (root.check rootCuts) (@treeBlock_merge 6384 144 144 (root.check rootCuts) (@treeBlock_merge 6384 48 96 (root.check rootCuts) rootBlock6384 (@treeBlock_merge 6432 48 48 (root.check rootCuts) rootBlock6432 rootBlock6480)) (@treeBlock_merge 6528 48 96 (root.check rootCuts) rootBlock6528 (@treeBlock_merge 6576 48 48 (root.check rootCuts) rootBlock6576 rootBlock6624))) (@treeBlock_merge 6672 144 144 (root.check rootCuts) (@treeBlock_merge 6672 48 96 (root.check rootCuts) rootBlock6672 (@treeBlock_merge 6720 48 48 (root.check rootCuts) rootBlock6720 rootBlock6768)) (@treeBlock_merge 6816 48 96 (root.check rootCuts) rootBlock6816 (@treeBlock_merge 6864 48 48 (root.check rootCuts) rootBlock6864 rootBlock6912)))))) (@treeBlock_merge 6960 1152 1170 (root.check rootCuts) (@treeBlock_merge 6960 576 576 (root.check rootCuts) (@treeBlock_merge 6960 288 288 (root.check rootCuts) (@treeBlock_merge 6960 144 144 (root.check rootCuts) (@treeBlock_merge 6960 48 96 (root.check rootCuts) rootBlock6960 (@treeBlock_merge 7008 48 48 (root.check rootCuts) rootBlock7008 rootBlock7056)) (@treeBlock_merge 7104 48 96 (root.check rootCuts) rootBlock7104 (@treeBlock_merge 7152 48 48 (root.check rootCuts) rootBlock7152 rootBlock7200))) (@treeBlock_merge 7248 144 144 (root.check rootCuts) (@treeBlock_merge 7248 48 96 (root.check rootCuts) rootBlock7248 (@treeBlock_merge 7296 48 48 (root.check rootCuts) rootBlock7296 rootBlock7344)) (@treeBlock_merge 7392 48 96 (root.check rootCuts) rootBlock7392 (@treeBlock_merge 7440 48 48 (root.check rootCuts) rootBlock7440 rootBlock7488)))) (@treeBlock_merge 7536 288 288 (root.check rootCuts) (@treeBlock_merge 7536 144 144 (root.check rootCuts) (@treeBlock_merge 7536 48 96 (root.check rootCuts) rootBlock7536 (@treeBlock_merge 7584 48 48 (root.check rootCuts) rootBlock7584 rootBlock7632)) (@treeBlock_merge 7680 48 96 (root.check rootCuts) rootBlock7680 (@treeBlock_merge 7728 48 48 (root.check rootCuts) rootBlock7728 rootBlock7776))) (@treeBlock_merge 7824 144 144 (root.check rootCuts) (@treeBlock_merge 7824 48 96 (root.check rootCuts) rootBlock7824 (@treeBlock_merge 7872 48 48 (root.check rootCuts) rootBlock7872 rootBlock7920)) (@treeBlock_merge 7968 48 96 (root.check rootCuts) rootBlock7968 (@treeBlock_merge 8016 48 48 (root.check rootCuts) rootBlock8016 rootBlock8064))))) (@treeBlock_merge 8112 576 594 (root.check rootCuts) (@treeBlock_merge 8112 288 288 (root.check rootCuts) (@treeBlock_merge 8112 144 144 (root.check rootCuts) (@treeBlock_merge 8112 48 96 (root.check rootCuts) rootBlock8112 (@treeBlock_merge 8160 48 48 (root.check rootCuts) rootBlock8160 rootBlock8208)) (@treeBlock_merge 8256 48 96 (root.check rootCuts) rootBlock8256 (@treeBlock_merge 8304 48 48 (root.check rootCuts) rootBlock8304 rootBlock8352))) (@treeBlock_merge 8400 144 144 (root.check rootCuts) (@treeBlock_merge 8400 48 96 (root.check rootCuts) rootBlock8400 (@treeBlock_merge 8448 48 48 (root.check rootCuts) rootBlock8448 rootBlock8496)) (@treeBlock_merge 8544 48 96 (root.check rootCuts) rootBlock8544 (@treeBlock_merge 8592 48 48 (root.check rootCuts) rootBlock8592 rootBlock8640)))) (@treeBlock_merge 8688 288 306 (root.check rootCuts) (@treeBlock_merge 8688 144 144 (root.check rootCuts) (@treeBlock_merge 8688 48 96 (root.check rootCuts) rootBlock8688 (@treeBlock_merge 8736 48 48 (root.check rootCuts) rootBlock8736 rootBlock8784)) (@treeBlock_merge 8832 48 96 (root.check rootCuts) rootBlock8832 (@treeBlock_merge 8880 48 48 (root.check rootCuts) rootBlock8880 rootBlock8928))) (@treeBlock_merge 8976 144 162 (root.check rootCuts) (@treeBlock_merge 8976 48 96 (root.check rootCuts) rootBlock8976 (@treeBlock_merge 9024 48 48 (root.check rootCuts) rootBlock9024 rootBlock9072)) (@treeBlock_merge 9120 96 66 (root.check rootCuts) (@treeBlock_merge 9120 48 48 (root.check rootCuts) rootBlock9120 rootBlock9168) (@treeBlock_merge 9216 48 18 (root.check rootCuts) rootBlock9216 rootBlock9264))))))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootLower : Lower root.mask root.bank root.goal (root.fuel+1) := by
  apply PEqualNP.Outside.L_meta_42614.TableHashCert.lower root rootCuts rootKnown (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) rootAll
  · unfold Masked
    decide +kernel
  · unfold properWord
    decide +kernel

def witness : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.or, [3, 5]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [0, 7]⟩, ⟨.and, [8, 6]⟩, ⟨.and, [8, 2]⟩, ⟨.or, [10, 3]⟩, ⟨.or, [11, 4]⟩, ⟨.and, [11, 4]⟩, ⟨.or, [1, 13]⟩, ⟨.and, [2, 14]⟩, ⟨.or, [9, 15]⟩, ⟨.and, [16, 12]⟩], 17⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sizeUpper : PEqualNP.MetaComplexity.Monotone2 witness ∧ witness.size = 12 ∧
    ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = (fun x : Fin 6 → Bool => Nat.testBit (4277071584 * 2 ^ 32 + 4209044096) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) x := by
  refine ⟨?_, by decide +kernel, by decide +kernel⟩
  intro gate member
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_42614.Proof

open PEqualNP.Outside.L_meta_42614.Proof in
theorem PEqualNP.Outside.L_meta_42614 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071584 * 2 ^ 32 + 4209044096) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071584 * 2 ^ 32 + 4209044096) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  intro s h
  let raw : List (BitVec 64) := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
  let target : BitVec 64 := 0xfeeeeee0fae0ea80
  have bound : 12 ≤ s := hcsLower (n := 6) raw target 12 _ (by decide +kernel) (by decide +kernel) (show Lower (fullMask 64) (raw.map BitVec.toNat) target.toNat 12 from rootLower) s h
  obtain ⟨mono, sz, heval⟩ := sizeUpper
  exact ⟨witness, mono, sz.le.trans bound, heval⟩
