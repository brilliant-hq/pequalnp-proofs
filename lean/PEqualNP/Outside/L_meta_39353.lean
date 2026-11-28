import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_39353

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

def full : ℕ := ((1 <<< 144) - 1)

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

def rowM : ℕ := (1 <<< 0) ||| (1 <<< 12) ||| (1 <<< 24) ||| (1 <<< 36) ||| (1 <<< 48) ||| (1 <<< 60) ||| (1 <<< 72) ||| (1 <<< 84) ||| (1 <<< 96) ||| (1 <<< 108) ||| (1 <<< 120) ||| (1 <<< 132)

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
        (if ws.length == fuel + 1 then !dagPartition true ws goal (mask ^^^ goal)
         else !dagPartition false ws goal (mask ^^^ goal)) ||
        (if ws.length == fuel + 1 then
           chart.any (fun c => !PackedRect.rectOK1 (ws.map (chartWord c)))
         else false) || cut state))

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

def pageLinks (idx codeAt : Nat → Nat) (sizeBits tokenBits destinationBits trials : Nat) :
    (Nat → Nat → Option (Nat × Nat)) := fun parent token =>
  let entry := idx parent
  let size := entry &&& ((1 <<< sizeBits) - 1)
  let offset := entry >>> sizeBits
  (Nat.rec (motive := fun _ => Nat → Nat → Option (Nat × Nat)) (fun _ _ => none)
    (fun _ next lo hi =>
      if Nat.blt lo hi then
        let mid := (lo+hi)/2
        let code := codeAt mid
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

def moveStage0 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xa5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a, 3)], [(0x5050505050505050, 3)])
def moveStage1 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xcc33cc33cc33cc33, 0), (0xcc00cc00cc00cc, 6)], [(0x3300330033003300, 6)])
def moveStage2 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xf00ff00ff00ff00f, 0), (0xf000f000f000f0, 4)], [(0xf000f000f000f00, 4)])
def moveStage3 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xff00ff0000ff00ff, 0), (0xff00ff00, 24)], [(0xff00ff00000000, 24)])
def moveStage4 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xffff00000000ffff, 0), (0xffff0000, 16)], [(0xffff00000000, 16)])
def moveStage5 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xaa55aa55aa55aa55, 0), (0xaa00aa00aa00aa, 7)], [(0x5500550055005500, 7)])
def moveStages : Array (List (Nat × Nat) × List (Nat × Nat)) := [moveStage0, moveStage1, moveStage2, moveStage3, moveStage4, moveStage5].toArray
def sBase : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
def sGoal : Nat := 0xfeeefaeafeaaaaa8
def cbits (ws : List Nat) : Nat := ws.foldr (fun a z => (z <<< 64) ||| a) 0
def st13 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xcc33cc33cc33cc33, 0), (0xcc00cc00cc00cc, 6)], [(0x3300330033003300, 6)])
def pm0 : List (List (Nat × Nat) × List (Nat × Nat)) := [st13]
def st14 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xcccc3333cccc3333, 0), (0xcccc0000cccc, 14)], [(0x3333000033330000, 14)])
def pm1 : List (List (Nat × Nat) × List (Nat × Nat)) := [st13, st14]
def s0Blob175545 : Nat := (cbits [0x2402090100c0203, 0xc201100844140b04, 0x41a0506830190904, 0x30500c00030c0682, 0xc024140900024240, 0x44100b0102c020b0, 0x2130c0442411000, 0x190086420130104c, 0x4068041a0806410, 0x6c241b0506c201a, 0x404090800c10030c, 0xb0902c000b0802, 0x30004c1011010443, 0x506400190c04c141, 0x6c021b0006824190, 0x30030806c101b010, 0x1305044200b09024, 0x6c021a0106410])
def s0Blob175931 : Nat := (cbits [0xbff7fffe3ffff1ff, 0xd5f8e73fc71c7e93, 0xe6ff07cff81f8f1c, 0xf8fff80fffe00fe0])
def s0Blob176046 : Nat := (cbits [0x4010000009040025, 0x2a264a4642496692, 0x1942d41a90932b18, 0x78486ad24c24dc0])
def s0Mask : Nat := 0xf0f0f0f
abbrev s0Goal : Nat := sGoal &&& s0Mask
abbrev s0StockWords : List Nat := [0xa0a0a0a, 0xc0c0c0c, 0xf000f00, 0xf0f0000]
def s0Fact : Nat × List Nat × Nat × Nat := (s0Mask, s0StockWords, 6, s0Goal)
def s0Cuts : List (Nat × List Nat × Nat × Nat) := []
def s0Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[3, 9, 17, 26, 3, 9, 17, 26, 3, 9, 17, 26, 1, 10, 18, 24, 1, 10, 18, 24, 1, 10, 18, 24], rfl⟩
def s0Witnesses := unpackWitnesses s0StockWords [1538, 263681, 528897, 795137]
def s0Index (i : Nat) : Nat := unpack 0xa28301 6 i
def s0Codes (i : Nat) : Nat := unpack (cbits [0x31010c504010000f, 0x1492c6]) 17 i
def s0Forest (i : Nat) : Nat := unpack 0x3144010803c 15 i
def s0Links := pageLinks s0Index s0Codes 3 13 2 4
def s0Data (i : Nat) : Nat × Nat :=
  let e := s0Forest i
  (e &&& 3, e >>> 2)
def s0Sample : Nat × Nat := (s0Blob175545, 64)
def s0Tags := dagTraceTags s0Mask 64 (dagTagBases s0StockWords s0Blob175931 s0Blob176046 64) 5 s0Data
def s0States := dagTrace s0Mask s0StockWords 5 s0Data
def s0MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm0, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 3, 2, 1, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 3, 2, 1, 4, 5] 0 i.val))), (pm1, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 4, 2, 1, 3, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 3, 2, 4, 1, 5] 0 i.val)))]
def s0Moves := dagMoves s0MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Autos : DagMovesOK s0Mask s0Goal 64 s0Moves := dagMovesOfCheck (by decide +kernel)
def s0Check := dagCheckNode s0Mask s0Goal s0Chart (dagKnownCloses s0Goal s0Cuts) 3 s0States s0Moves s0Links s0Sample s0Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Roots : dagCheckRoots s0Mask s0Goal s0Chart (dagKnownCloses s0Goal s0Cuts) s0Witnesses (dagRef 3 s0States s0Moves s0Links 0) s0StockWords 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Block0 : treeBlock 0 3 s0Check = true := by decide +kernel
theorem s0Blocks : treeBlock 0 3 s0Check = true := s0Block0
theorem s0Known : Known s0Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Stock : Lower s0Mask s0StockWords s0Goal 6 := by
  apply lowerDag _ _ _ _ s0Autos _ _ _ s0Known _ s0Roots s0Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s0Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def s1Blob178889 : Nat := (cbits [0x1402050100c0203, 0xc1009008240c0702, 0x2110703c180d0502, 0x70a0542413080440, 0x9068141a0c0642c1, 0x70281c06070301a0, 0x30b0781c1e0c0, 0x50900c14030300c, 0xa01418050301400, 0x1c08070101c0207, 0x41409000242c0707, 0x40b0082c30090602, 0xd008341c0b0402c0, 0x303c1c0d04034080, 0x4400110603c140f0, 0x2130c0442811090, 0x150b04c20130104c, 0xb05420150205402, 0x86428170905c0c17, 0x8041a08064101900, 0xc1a080681c1a0406, 0xc0c06c241b0506c2, 0x80701c1c04070081, 0x74281d060742c1c0, 0x181e050780c1e0c0, 0x1f0c078281e09078, 0x400c08030b07c1c])
def s1Blob179454 : Nat := (cbits [0xffffffffff00ffff, 0xfc75293f038383f, 0xffc03fc70f0e1e1f, 0xf00fe01ff0f8631c, 0xff83e03fffc007, 0x3ffffff8000fffe0, 0xfff0000000fffc00, 0x3fffffff])
def s1Blob179638 : Nat := (cbits [0x1100220100000425, 0x2ec3529200000008, 0x32c51d438a27145a, 0xa84b509ce2d86318, 0x446d83c0755d4505, 0x99a9a990008d99c8, 0xcce0011088b6f800, 0x2e363626])
def s1Mask : Nat := 0xffffffff
abbrev s1Goal : Nat := sGoal &&& s1Mask
abbrev s1StockWords : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]
def s1Fact : Nat × List Nat × Nat × Nat := (s1Mask, s1StockWords, 7, s1Goal)
def s1Cuts : List (Nat × List Nat × Nat × Nat) := [s0Fact]
def s1Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[3, 5, 9, 17, 26, 28, 3, 5, 9, 17, 26, 28, 1, 14, 22, 24, 1, 14, 22, 24, 1, 14, 22, 24], rfl⟩
def s1Witnesses := unpackWitnesses s1StockWords [1538, 263681, 526849, 791041, 1057281]
def s1Index (i : Nat) : Nat := unpack 0 2 i
def s1Codes (i : Nat) : Nat := unpack 0 15 i
def s1Forest (i : Nat) : Nat := unpack 0 14 i
def s1Links := pageLinks s1Index s1Codes 1 13 1 2
def s1Data (i : Nat) : Nat × Nat :=
  let e := s1Forest i
  (e &&& 1, e >>> 1)
def s1Sample : Nat × Nat := (s1Blob178889, 96)
def s1Tags := dagTraceTags s1Mask 96 (dagTagBases s1StockWords s1Blob179454 s1Blob179638 96) 6 s1Data
def s1States := dagTrace s1Mask s1StockWords 6 s1Data
def s1MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s1Moves := dagMoves s1MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s1Autos : DagMovesOK s1Mask s1Goal 64 s1Moves := dagMovesOfCheck (by decide +kernel)
def s1Check := dagCheckNode s1Mask s1Goal s1Chart (dagKnownCloses s1Goal s1Cuts) 0 s1States s1Moves s1Links s1Sample s1Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s1Roots : dagCheckRoots s1Mask s1Goal s1Chart (dagKnownCloses s1Goal s1Cuts) s1Witnesses (dagRef 0 s1States s1Moves s1Links 0) s1StockWords 6 = true := by decide +kernel
theorem s1Blocks : treeBlock 0 0 s1Check = true := rfl
theorem s1Known : Known s1Cuts := (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s0Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s1Stock : Lower s1Mask s1StockWords s1Goal 7 := by
  apply lowerDag _ _ _ _ s1Autos _ _ _ s1Known _ s1Roots s1Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s1Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl <;> decide +kernel
def st25 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xf0f0f0f00f0f0f0f, 0), (0xf0f0f0f0, 28)], [(0xf0f0f0f00000000, 28)])
def pm2 : List (List (Nat × Nat) × List (Nat × Nat)) := [st13, st25]
def s2Mask : Nat := 0xf0f0f0f0f0f0f0f
abbrev s2Goal : Nat := sGoal &&& s2Mask
abbrev s2StockWords : List Nat := [0xa0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c, 0xf000f000f000f00, 0xf0f00000f0f0000, 0xf0f0f0f00000000]
def s2Fact : Nat × List Nat × Nat × Nat := (s2Mask, s2StockWords, 7, s2Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Stock : Lower s2Mask s2StockWords s2Goal 7 := dagShiftLower (width := 64) pm2 s1Stock (by decide +kernel)
def st15 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xcccccccc33333333, 0), (0xcccccccc, 30)], [(0x3333333300000000, 30)])
def st23 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xf00ff00ff00ff00f, 0), (0xf000f000f000f0, 4)], [(0xf000f000f000f00, 4)])
def st24 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xf0f00f0ff0f00f0f, 0), (0xf0f00000f0f0, 12)], [(0xf0f00000f0f0000, 12)])
def st12 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xc3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c, 2)], [(0x3030303030303030, 2)])
def pm3 : List (List (Nat × Nat) × List (Nat × Nat)) := [st15, st23, st24, st12]
def s3Mask : Nat := 0x3333333333333333
abbrev s3Goal : Nat := sGoal &&& s3Mask
abbrev s3StockWords : List Nat := [0x2222222222222222, 0x3030303030303030, 0x3300330033003300, 0x3333000033330000, 0x3333333300000000]
def s3Fact : Nat × List Nat × Nat × Nat := (s3Mask, s3StockWords, 7, s3Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s3Stock : Lower s3Mask s3StockWords s3Goal 7 := dagShiftLower (width := 64) pm3 s1Stock (by decide +kernel)
def pm4 : List (List (Nat × Nat) × List (Nat × Nat)) := [st12]
def s4Mask : Nat := 0x33333333
abbrev s4Goal : Nat := sGoal &&& s4Mask
abbrev s4StockWords : List Nat := [0x22222222, 0x30303030, 0x33003300, 0x33330000]
def s4Fact : Nat × List Nat × Nat × Nat := (s4Mask, s4StockWords, 6, s4Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s4Stock : Lower s4Mask s4StockWords s4Goal 6 := dagShiftLower (width := 64) pm4 s0Stock (by decide +kernel)
def st45 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xffff00000000ffff, 0), (0xffff0000, 16)], [(0xffff00000000, 16)])
def pm5 : List (List (Nat × Nat) × List (Nat × Nat)) := [st12, st45]
def s5Mask : Nat := 0x333300003333
abbrev s5Goal : Nat := sGoal &&& s5Mask
abbrev s5StockWords : List Nat := [0x222200002222, 0x303000003030, 0x330000003300, 0x333300000000]
def s5Fact : Nat × List Nat × Nat × Nat := (s5Mask, s5StockWords, 6, s5Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s5Stock : Lower s5Mask s5StockWords s5Goal 6 := dagShiftLower (width := 64) pm5 s0Stock (by decide +kernel)
def st35 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xff00ff0000ff00ff, 0), (0xff00ff00, 24)], [(0xff00ff00000000, 24)])
def st34 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xff0000ffff0000ff, 0), (0xff000000ff00, 8)], [(0xff000000ff0000, 8)])
def pm6 : List (List (Nat × Nat) × List (Nat × Nat)) := [st35, st34]
def s6Mask : Nat := 0xf000f000f000f
abbrev s6Goal : Nat := sGoal &&& s6Mask
abbrev s6StockWords : List Nat := [0xa000a000a000a, 0xc000c000c000c, 0xf0000000f0000, 0xf000f00000000]
def s6Fact : Nat × List Nat × Nat × Nat := (s6Mask, s6StockWords, 6, s6Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6Stock : Lower s6Mask s6StockWords s6Goal 6 := dagShiftLower (width := 64) pm6 s0Stock (by decide +kernel)
def pm7 : List (List (Nat × Nat) × List (Nat × Nat)) := [st12, st34]
def s7Blob189682 : Nat := (cbits [0x1402050100c0203, 0x4140b04024020902, 0x4130804402110603, 0xa0506830190a0542, 0xa070181c0c068241, 0x8c402100884301c0, 0x542b140a44825110, 0x31140b0482c060b0, 0x180c84432090c860, 0xe8543a1c0e46835, 0xc00031c0f0683c1c, 0x51100c24030500, 0x9120142805060140, 0xc024180905024000, 0x2c040b0082c50090, 0x80d00834540b040, 0x1109044001104034, 0x84c60110c04428, 0x5402150804c0413, 0x402191a054201502, 0x41a1c06420190406, 0xa15068201a040680, 0xc06c241b0506c701, 0x70201c04070081c0, 0x281d06074701c1a0, 0x211108400210c074, 0x88c60211408448])
def s7Blob190247 : Nat := (cbits [0xffffffc311f81fff, 0xe120e443ff8383ff, 0x8003fc03807803cc, 0x3803c310e47088c, 0xf87f0f003fc003c, 0x3ffffc003ffc03e, 0xfc00003ff007ff00, 0xfff8000003ffffff, 0xfc0000000000003f])
def s7Blob190459 : Nat := (cbits [0x8088000000080115, 0x6120644280000044, 0x801a40108508384, 0x1101381106430888, 0xb85b0e011a40028, 0x22caea80226788ae, 0x7802113bb006de00, 0xddf0000043735332, 0x786062204044223f])
def s7Mask : Nat := 0x3f3f3f3f3f3f3f3f
abbrev s7Goal : Nat := sGoal &&& s7Mask
abbrev s7StockWords : List Nat := [0x2a2a2a2a2a2a2a2a, 0xc0c0c0c0c0c0c0c, 0x3030303030303030, 0x3f003f003f003f00, 0x3f3f00003f3f0000, 0x3f3f3f3f00000000]
def s7Fact : Nat × List Nat × Nat × Nat := (s7Mask, s7StockWords, 10, s7Goal)
def s7Cuts : List (Nat × List Nat × Nat × Nat) := [s2Fact, s3Fact, s0Fact, s4Fact, s5Fact, s6Fact]
def s7Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[3, 5, 9, 17, 26, 28, 33, 44, 50, 3, 5, 9, 1, 12, 18, 42, 52, 56, 1, 12, 18, 42, 52, 56], rfl⟩
def s7Witnesses := unpackWitnesses s7StockWords [1538, 263681, 526849, 791041, 1057281, 1327617]
def s7Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 5 then (if j < 2 then (if j < 1 then (cbits [0x4014082b300d0001, 0x580150854015005, 0x6005801600580160, 0x16105801]) else (cbits [0x218006001800600, 0x860218086019446, 0x2048802184860218, 0x22808a02])) else (if j < 3 then (cbits [0xe023048a122808a0, 0x48ea23808e023808, 0xc00a652980a41288, 0x2c00b002]) else (if j < 4 then (cbits [0x402c84b202c04b00, 0xb6a2d04b402d00b, 0x380cc13300ca1328, 0x3430ce13]) else (cbits [0xa03a80e813a00e80, 0xec03a84ea03a80e, 0xb30ec03b00ec03b0, 0x41810413])))) else (if j < 8 then (if j < 6 then (cbits [0x6041810604181060, 0x1080420108041850, 0x6011804601180422, 0x46011804]) else (if j < 7 then (cbits [0xc44a292614905186, 0xd440510144051013, 0x28d4a052814a0510, 0x591150a5]) else (cbits [0xc35b016c05b016c0, 0x97235c817205c816, 0x2818a062818435e1, 0x62998a06]))) else (if j < 9 then (cbits [0xc067019c06701963, 0x9ac16b01a8267199, 0x1c007001ba36b9, 0x7029c007]) else (if j < 10 then (cbits [0xc87609d807601d42, 0x1f207c81f207b0dd, 0x10df297c81f207c8, 0x82820a08]) else (cbits [0xaa82820a082820a0, 0x23a08d0e229878a0, 0x23a78e823a08e8]))))) 14 (i % 16)
def s7Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 9 then (if j < 4 then (if j < 2 then (if j < 1 then (cbits [0x280090080200003f, 0xf00ac6e01f13804c, 0xe3142c010c980371, 0xc7cda31e310c74b, 0x637421880fc32b3c, 0x4724b110]) else (cbits [0x46c384da50d26937, 0x1002156f4452b10d, 0xc01e0300740a0130, 0x8c541402b04807e0, 0x337060cae0a31f05, 0x68d0e18])) else (if j < 3 then (cbits [0x1c92c8518de04620, 0x730e02494308a4dc, 0x631409bd1224c438, 0x24b00e6200224b00, 0xc38040ca40831404, 0x83d101e]) else (cbits [0x2a01e883d1020c38, 0xc01082e0360b00a8, 0x832a0d0c783204e0, 0x8d383c3420e8cd83, 0x62a1098a4406200f, 0x11a4b044]))) else (if j < 6 then (if j < 5 then (cbits [0x4d25012bd1048c38, 0xd8c723631c0d8ca0, 0x202a1400223631c0, 0x8cd86032a158ca05, 0x6361998a86462018, 0x1aa4b068]) else (cbits [0x5401c0d80a06cc38, 0x68c505801a0d8020, 0x401c17a4b05c6201, 0x205e6341698a05, 0x31c1c0c505201294, 0x1c8c7656])) else (if j < 7 then (cbits [0x7692c1d190866329, 0x500407af441e2508, 0xe0089798a25a6281, 0x8ca48231d200c507, 0x94e2225086833521, 0x2330e08a]) else (if j < 8 then (cbits [0x94f4424b13890c42, 0x380a08463025c940, 0xe620268c7a7e0082, 0xa4b0786412818d49, 0xc4e242504a493528, 0x2a3d10a6]) else (cbits [0x9c63c2bc940acf4e, 0xd24b0b20082a8070, 0x8c3824a534b69412, 0x4940acc4d2eb104b, 0x13100024040082f, 0x2000ac70]))))) else (if j < 14 then (if j < 11 then (if j < 10 then (cbits [0x631430a4b0c0314, 0x80240c008020c50, 0xe01f31806c560111, 0x1884d06202080acc, 0x343624b0d662b35, 0x328100c8]) else (cbits [0xe314160c70cc04c, 0x40c50d292c170c74, 0xc00834a4b05e31d0, 0x6e560111100260, 0x6202680dce401f37, 0x3a9884e6])) else (if j < 12 then (cbits [0xde0343bb0e0ec637, 0x60c70e204c380100, 0x8c38970c760e3149, 0x24b25e31d840c50e, 0x1d180044120083a, 0x3c809472]) else (if j < 13 then (cbits [0xf40343ea4b066029, 0x50020f804c3d8100, 0xe0312180a4620110, 0xa106c381a00d4f, 0x3144101310204040, 0x118c550a]) else (cbits [0xc0620278cdc6a31f, 0x330e00631443b0e0, 0x401d8500210c6204, 0x1051203d2800d47, 0x344500711af441e, 0x46013116])))) else (if j < 16 then (if j < 15 then (cbits [0x6c31f120c541c314, 0x9880b4343288cdc, 0x2c4347b0e0d86293, 0x3d101e620493d112, 0x8483d102062048, 0x2200a422]) else (cbits [0x900414a00f4a4035, 0xd494132f4e4c3d10, 0xe04c4b00a12a01c4, 0x81048a0290900212, 0xc38248135380492d, 0x50b10540])) else (if j < 17 then (cbits [0x3a01c51494132c4d, 0x70c513e0404f00a1, 0x43371e8cac4a3158, 0xa4b0ee62a2e0d0c9, 0xf4450310d1ec3843, 0x88188148]) else (if j < 18 then (cbits [0xa603589002120f44, 0xb01354c0492e8104, 0x294d50a5052292c2, 0xa14e01c5549413, 0x315098c515203454, 0x258cdc4c]) else (cbits [0x34c434930e0ae343, 0x523d11])))))) 22 (i % 16)
def s7Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 5 then (if j < 2 then (if j < 1 then (cbits [0x8020080100203f00, 0x80260492c0318a01, 0x492c073100380740, 0x218a8100ac0803e0, 0x7a4b0086860432b0, 0x61c0]) else (cbits [0x250c0926e04f440f, 0x403c2a009017a201, 0xa0421501b0a80a85, 0x51940d8c785409c2, 0xa8d085466c2a32a1, 0x1a70])) else (if j < 3 then (cbits [0x98a854c522a62015, 0x5e882ac38154960a, 0x82800980c9405, 0xc194140070a80545, 0x61880b06285801a2, 0x4961]) else (if j < 4 then (cbits [0x1880a066c5032a28, 0x1258506362831514, 0x3143800f80b0e0a, 0x84961c1908e063a7, 0xf80ac05e88709423, 0x41]) else (cbits [0x98c10863a7e3143f, 0xd29c7e9423f1949f, 0xec423f01423b0e0f, 0x19281fbd10fd89c7, 0x698f13863c9a0370, 0x3102])))) else (if j < 8 then (if j < 6 then (cbits [0xa4d5352589a6354d, 0x4038aaf444d62726, 0x20430192826bd393, 0x94a0aca4b164010b, 0xc94165882b2c385, 0x18a0]) else (if j < 7 then (cbits [0x8c7405258c031460, 0x80c80346400db1, 0x26206300fb181319, 0x3315b198858d258d, 0x7806db863c0292c6, 0x1a3]) else (cbits [0x7db8098de0406f, 0x8c42dcc387431037, 0x231f0161c3718ddb, 0xa0203d00d1e804af, 0xf8cac05258f204c7, 0x18b]))) else (if j < 9 then (cbits [0x8132000810002880, 0x86290a6200161c3f, 0x26370161c42b0e21, 0xa01a4500722807b1, 0x7a4b005e891204c8, 0x61c4]) else (if j < 10 then (cbits [0xbd123d8871ef4490, 0x40392a03d9449b80, 0x8f44940264a80a25, 0xc4a180c94251e9d2, 0xe80a2740393a0499, 0x204]) else (cbits [0xc9427188338c389c, 0x988602f44a461c00, 0xe028a700e5381269, 0x7a200c942980694]))))) 21 (i % 16)
def s7Links := pageLinks s7Index s7Codes 5 13 8 6
def s7Data (i : Nat) : Nat × Nat :=
  let e := s7Forest i
  (e &&& 255, e >>> 8)
def s7Sample : Nat × Nat := (s7Blob189682, 96)
def s7Tags := dagTraceTags s7Mask 96 (dagTagBases s7StockWords s7Blob190247 s7Blob190459 96) 9 s7Data
def s7States := dagTrace s7Mask s7StockWords 9 s7Data
def s7MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm7, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 2, 1, 4, 3, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 2, 1, 4, 3, 5] 0 i.val)))]
def s7Moves := dagMoves s7MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s7Autos : DagMovesOK s7Mask s7Goal 64 s7Moves := dagMovesOfCheck (by decide +kernel)
def s7Check := dagCheckNode s7Mask s7Goal s7Chart (dagKnownCloses s7Goal s7Cuts) 172 s7States s7Moves s7Links s7Sample s7Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s7Roots : dagCheckRoots s7Mask s7Goal s7Chart (dagKnownCloses s7Goal s7Cuts) s7Witnesses (dagRef 172 s7States s7Moves s7Links 0) s7StockWords 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s7Block0 : treeBlock 0 24 s7Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s7Block24 : treeBlock 24 24 s7Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s7Block48 : treeBlock 48 24 s7Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s7Block72 : treeBlock 72 24 s7Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s7Block96 : treeBlock 96 24 s7Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s7Block120 : treeBlock 120 24 s7Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s7Block144 : treeBlock 144 24 s7Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s7Block168 : treeBlock 168 4 s7Check = true := by decide +kernel
theorem s7Group0_48 : treeBlock 0 48 s7Check = true := treeBlock_merge (start := 0) (left := 24) (right := 24) (check := s7Check) s7Block0 s7Block24
theorem s7Group48_48 : treeBlock 48 48 s7Check = true := treeBlock_merge (start := 48) (left := 24) (right := 24) (check := s7Check) s7Block48 s7Block72
theorem s7Group0_96 : treeBlock 0 96 s7Check = true := treeBlock_merge (start := 0) (left := 48) (right := 48) (check := s7Check) s7Group0_48 s7Group48_48
theorem s7Group96_48 : treeBlock 96 48 s7Check = true := treeBlock_merge (start := 96) (left := 24) (right := 24) (check := s7Check) s7Block96 s7Block120
theorem s7Group144_28 : treeBlock 144 28 s7Check = true := treeBlock_merge (start := 144) (left := 24) (right := 4) (check := s7Check) s7Block144 s7Block168
theorem s7Group96_76 : treeBlock 96 76 s7Check = true := treeBlock_merge (start := 96) (left := 48) (right := 28) (check := s7Check) s7Group96_48 s7Group144_28
theorem s7Group0_172 : treeBlock 0 172 s7Check = true := treeBlock_merge (start := 0) (left := 96) (right := 76) (check := s7Check) s7Group0_96 s7Group96_76
theorem s7Blocks : treeBlock 0 172 s7Check = true := s7Group0_172
theorem s7Known : Known s7Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s6Stock) s5Stock) s4Stock) s0Stock) s3Stock) s2Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s7Stock : Lower s7Mask s7StockWords s7Goal 10 := by
  apply lowerDag _ _ _ _ s7Autos _ _ _ s7Known _ s7Roots s7Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s7Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s8Mask : Nat := 0xffffffffffff
abbrev s8Goal : Nat := sGoal &&& s8Mask
abbrev s8StockWords : List Nat := [0xaaaaaaaaaaaa, 0xcccccccccccc, 0xf0f0f0f0f0f0, 0xff00ff00ff00, 0xffff0000, 0xffff00000000]
def s8Fact : Nat × List Nat × Nat × Nat := (s8Mask, s8StockWords, 10, s8Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s8Stock : Lower s8Mask s8StockWords s8Goal 10 := dagShiftLower (width := 64) pm3 s7Stock (by decide +kernel)
def s9Mask : Nat := 0xff00ffffffffff
abbrev s9Goal : Nat := sGoal &&& s9Mask
abbrev s9StockWords : List Nat := [0xaa00aaaaaaaaaa, 0xcc00cccccccccc, 0xf000f0f0f0f0f0, 0xff00ff00, 0xff0000ffff0000, 0xff00ff00000000]
def s9Fact : Nat × List Nat × Nat × Nat := (s9Mask, s9StockWords, 10, s9Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s9Stock : Lower s9Mask s9StockWords s9Goal 10 := dagShiftLower (width := 64) pm2 s7Stock (by decide +kernel)
def pm8 : List (List (Nat × Nat) × List (Nat × Nat)) := [st13, st12, st25, st24]
def s10Mask : Nat := 0xf0fffff0f0fffff
abbrev s10Goal : Nat := sGoal &&& s10Mask
abbrev s10StockWords : List Nat := [0xa0aaaaa0a0aaaaa, 0xc0ccccc0c0ccccc, 0xf0f00000f0f0, 0xf00ff000f00ff00, 0xf0f00000f0f0000, 0xf0fffff00000000]
def s10Fact : Nat × List Nat × Nat × Nat := (s10Mask, s10StockWords, 10, s10Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s10Stock : Lower s10Mask s10StockWords s10Goal 10 := dagShiftLower (width := 64) pm8 s7Stock (by decide +kernel)
def pm9 : List (List (Nat × Nat) × List (Nat × Nat)) := [st23, st45]
def s11Mask : Nat := 0x33ff33ff33ff33ff
abbrev s11Goal : Nat := sGoal &&& s11Mask
abbrev s11StockWords : List Nat := [0x22aa22aa22aa22aa, 0xcc00cc00cc00cc, 0x30f030f030f030f0, 0x3300330033003300, 0x33ff000033ff0000, 0x33ff33ff00000000]
def s11Fact : Nat × List Nat × Nat × Nat := (s11Mask, s11StockWords, 10, s11Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s11Stock : Lower s11Mask s11StockWords s11Goal 10 := dagShiftLower (width := 64) pm9 s7Stock (by decide +kernel)
def pm10 : List (List (Nat × Nat) × List (Nat × Nat)) := [st12, st14, st13, st35]
def pm11 : List (List (Nat × Nat) × List (Nat × Nat)) := [st14, st35]
def pm12 : List (List (Nat × Nat) × List (Nat × Nat)) := [st14, st25, st23, st13]
def s12Blob197986 : Nat := (cbits [0x70301a09068141a, 0x81c1e0c070281c06, 0x826110980c260b07, 0xe140b0482c060b04, 0x10c82432150b81c2, 0xe868360b0d860321, 0x703c1a0f0703a150, 0x1a07068101a01068, 0x1c068541a0b06820, 0x701c1c04070081c, 0x8701c1a0702c1c08, 0x41e06078141e0307, 0x601098301e0a0782, 0x982c2607098082, 0xb0082c1a09854261, 0x542c100b01c2c040, 0x2e030b8702c1a0b0, 0x120b8442e060b814, 0xc82032010c8502e, 0x86832150c840320b, 0x836090d80c361c0c, 0xa180d84836110d82, 0x10e8303a090e8143, 0xf0183c180e8503a1, 0x503c120f0303c0a0, 0x3e0b0f81c3e180f0, 0x68703e1a0f854])
def s12Blob198554 : Nat := (cbits [0xf80fff80fe7fc7c7, 0x198fff8fc0fffff, 0x7ff03f01ffffffff, 0xfff01fffffe0f8ff, 0xffff00ffffffc001, 0xfffffffe00001fff, 0xffffe00001ffff00, 0x7fffffff])
def s12Blob198741 : Nat := (cbits [0x5945a5946a2bc3c3, 0x28985dd81c02cb2a, 0x2cb01548aa59cab5, 0x35649346cd60e86d, 0xb1dd00b6555540a1, 0x6a69a6cc06091c78, 0xc78e0060c1f6b600, 0x738e38f1])
def s12Mask : Nat := 0x5555555555555555
abbrev s12Goal : Nat := sGoal &&& s12Mask
abbrev s12StockWords : List Nat := [0x4444444444444444, 0x5050505050505050, 0x5500550055005500, 0x5555000055550000, 0x5555555500000000]
def s12Fact : Nat × List Nat × Nat × Nat := (s12Mask, s12StockWords, 7, s12Goal)
def s12Cuts : List (Nat × List Nat × Nat × Nat) := []
def s12Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[26, 28, 38, 44, 50, 26, 28, 38, 44, 50, 26, 28, 14, 22, 42, 52, 56, 14, 22, 42, 52, 56, 14, 22], rfl⟩
def s12Witnesses := unpackWitnesses s12StockWords [13336, 276504, 537618, 799754, 1068038]
def s12Index (i : Nat) : Nat := unpack 0x30341 6 i
def s12Codes (i : Nat) : Nat := unpack (cbits [0x880a31408020001f, 0x8b0e1a92c49]) 18 i
def s12Forest (i : Nat) : Nat := unpack 0x10807c 15 i
def s12Links := pageLinks s12Index s12Codes 3 13 2 4
def s12Data (i : Nat) : Nat × Nat :=
  let e := s12Forest i
  (e &&& 3, e >>> 2)
def s12Sample : Nat × Nat := (s12Blob197986, 96)
def s12Tags := dagTraceTags s12Mask 96 (dagTagBases s12StockWords s12Blob198554 s12Blob198741 96) 6 s12Data
def s12States := dagTrace s12Mask s12StockWords 6 s12Data
def s12MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm7, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 2, 1, 4, 3, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 2, 1, 4, 3, 5] 0 i.val))), (pm10, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 3, 1, 5, 2, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 2, 4, 1, 5, 3] 0 i.val))), (pm11, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 4, 2, 5, 1, 3] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 4, 2, 5, 1, 3] 0 i.val))), (pm12, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 5, 3, 4, 1, 2] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 4, 5, 2, 3, 1] 0 i.val)))]
def s12Moves := dagMoves s12MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s12Autos : DagMovesOK s12Mask s12Goal 64 s12Moves := dagMovesOfCheck (by decide +kernel)
def s12Check := dagCheckNode s12Mask s12Goal s12Chart (dagKnownCloses s12Goal s12Cuts) 2 s12States s12Moves s12Links s12Sample s12Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s12Roots : dagCheckRoots s12Mask s12Goal s12Chart (dagKnownCloses s12Goal s12Cuts) s12Witnesses (dagRef 2 s12States s12Moves s12Links 0) s12StockWords 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s12Block0 : treeBlock 0 2 s12Check = true := by decide +kernel
theorem s12Blocks : treeBlock 0 2 s12Check = true := s12Block0
theorem s12Known : Known s12Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s12Stock : Lower s12Mask s12StockWords s12Goal 7 := by
  apply lowerDag _ _ _ _ s12Autos _ _ _ s12Known _ s12Roots s12Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s12Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def s13Blob206400 : Nat := (cbits [0x1402050100c0203, 0xc1009008240c0702, 0x2110703c180d0502, 0x70a0542413080440, 0x9068141a0c0642c1, 0x70281c06070301a0, 0xc260b0781c1e0c0, 0x2c060b0482611098, 0x150b81c2e140b048, 0xd86032110c82432, 0x703a150e868360b, 0xc030000c703c1a0f, 0x51100c24030500c0, 0xa014180503014000, 0x1c04070081c48050, 0x90b01c1c07020, 0x90c024180905024, 0x402c040b0082c50, 0x34020d1502c1c0b, 0xc0c0f07034100d02, 0x41100044180f0503, 0x31804430110a0442, 0xb04c20130104c021, 0x5420150205402150, 0x24170305c68150b0, 0x190406402190a05c, 0x4068041a1c06420])
def s13Blob206965 : Nat := (cbits [0xfffffe000000ffff, 0xc7c752933fffffff, 0xc383c1c3e0f83e7f, 0xffc198fff8631c, 0xf8ff83e003fc01fc, 0xfc0001ffff0001e0, 0x1ff00fffc00, 0xff000000fffffe00, 0x1ff])
def s13Blob207161 : Nat := (cbits [0x2008000000000425, 0xc3c3529204044004, 0x41a284e342d0bc2b, 0x4e784985dd86318, 0xe86d83c002ea0969, 0xa80011b39e410960, 0x88211dd00b6f800, 0xb600000033733c00, 0x20402002100421f6])
def s13Mask : Nat := 0x55555555ffffffff
abbrev s13Goal : Nat := sGoal &&& s13Mask
abbrev s13StockWords : List Nat := [0xaaaaaaaa, 0x44444444cccccccc, 0x50505050f0f0f0f0, 0x55005500ff00ff00, 0x55550000ffff0000, 0x5555555500000000]
def s13Fact : Nat × List Nat × Nat × Nat := (s13Mask, s13StockWords, 10, s13Goal)
def s13Cuts : List (Nat × List Nat × Nat × Nat) := [s1Fact, s12Fact, s0Fact, s4Fact]
def s13Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[3, 5, 9, 17, 26, 28, 38, 44, 50, 3, 5, 9, 1, 14, 22, 42, 52, 56, 1, 14, 22, 42, 52, 56], rfl⟩
def s13Witnesses := unpackWitnesses s13StockWords [1538, 263681, 526849, 791041, 1057281, 1330182]
def s13Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 5 then (if j < 2 then (if j < 1 then (cbits [0x80148c33000e0001, 0x580160058016005, 0x8006001800584160, 0x18806011]) else (cbits [0xe019b06221880620, 0x7e21f807e01f807, 0x1048402084820208, 0x21808602])) else (if j < 3 then (cbits [0x6021c08602180860, 0xa602980a602980a, 0x984a602980a60298, 0x2a00a802]) else (if j < 4 then (cbits [0xb52a80aa02a80a81, 0xdc03700dc03510a, 0x800de13780dc1370, 0x3800e003]) else (cbits [0x813a00e803a00e04, 0xea13a80ea03a80e, 0x308f4c3d00ec43b0, 0x44011004])))) else (if j < 8 then (if j < 6 then (cbits [0x144011004401100, 0x116b458112244811, 0xb392c04b012c04b0, 0x54014844]) else (if j < 7 then (cbits [0x8056015045401500, 0x15a456815a056055, 0x58005f8562e588, 0x60818206]) else (cbits [0x20680582f6081820, 0x1a606905a406885a, 0xf81a6c6981a60698, 0x6f81be06]))) else (if j < 9 then (cbits [0xc07b01ec06fddbe0, 0x1ee07b81ec17b01e, 0xe81fa07e81ee67b8, 0x7fcdfa27]) else (if j < 10 then (cbits [0x6089062408902240, 0x2280898626089822, 0x3862938a022808a0, 0x94025009]) else (cbits [0x2098826209882509, 0x2840a10263198826, 0x6869a0a60684aa10, 0xa7269c0a]))))) 14 (i % 16)
def s13Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 11 then (if j < 5 then (if j < 2 then (if j < 1 then (cbits [0x240130080200003f, 0x100dc4402b89007c, 0xe043258108660419, 0x8cacd231f2e0c50a, 0x62bae1880f633738, 0xb898def6]) else (cbits [0x369334724b50092c, 0x30e15294352a4dd, 0xcf44d4b10f1cc39c, 0x807c0c0130100215, 0x31f810c501002b03, 0x838cae10])) else (if j < 3 then (cbits [0x1a62706188412620, 0x4a4b0206370798ac, 0x2c388824de1892d8, 0xa4b008620018c502, 0x92c8298800831402, 0x5b0e014]) else (if j < 4 then (cbits [0x16c3805a4b01c640, 0xa8d0828336098caa, 0x26320b98a82c6200, 0x19083863e0d18d83, 0xf441030e03e92c0f, 0xc24c042]) else (cbits [0x3a3280db0f23093c, 0x28ca448314118138, 0xe629131880343351, 0xa5085092c8f18d44, 0xc3e15b0e05494e14, 0x17310858])))) else (if j < 8 then (if j < 6 then (cbits [0x6525018bd105ec4e, 0xa0c5060c4816a530, 0xa3371d8cac7231f1, 0x98ae686201f0d0c7, 0x92c9f190e766379e, 0x2124b47e]) else (if j < 7 then (cbits [0x8c93f22a4dc86933, 0x130e67ec3823a50c, 0x2f44a3b10e8cc3fa, 0x24b06a620253d149, 0x9481c3d106ec381b, 0x1e312074]) else (cbits [0x80c389ba4b06c620, 0x431208894c20bd10, 0x2c389c24b0706202, 0x988498620a0bd108, 0x63f2898aca062727, 0x29990ca4]))) else (if j < 9 then (cbits [0xa493fa7a4b69892c, 0xb3d14aaf44a9a50e, 0x8948273d109a92c2, 0x80aa9cc382724b0a, 0x9412c24b24603611, 0x2d2524b2]) else (if j < 10 then (cbits [0xb2c41ac30e05e94d, 0xdc9425ec4dad3126, 0x802b8f807c040082, 0x9880680419300dc4, 0x92c3018dcbe62b2e, 0x31a4b4c2]) else (cbits [0xcec383324dcc8933, 0xa8104060083430e4, 0x8008af30e0bc92c1, 0x30e0bc92c1b01040, 0x41028020ca94c31, 0xaf24b06e]))))) else (if j < 16 then (if j < 13 then (if j < 12 then (cbits [0x26011030020c4c38, 0xc81342e029898074, 0x892cb51908d43361, 0x24f8de9363724c8d, 0xf443830e2de942b7, 0x358d0ae0]) else (cbits [0x28011038020da34c, 0xd8134340351280a4, 0xe635b01880d431e1, 0x24f8e692c39190cd, 0xc423c30f8ecc383a, 0x3d3d10f2])) else (if j < 14 then (cbits [0xee34c3aa530d631c, 0x380d42a011040020, 0xe6201e81343c0419, 0xa4f4f892cb79906b, 0xf443f30e0f29413e, 0x48020fe]) else (if j < 15 then (cbits [0x4202b10007d02013, 0x601087e0419880de, 0x631f410c54b00432, 0x8cdd0a333420cad0, 0x62b3098811034343, 0x3e18dce0]) else (cbits [0x12c38bd24dece92c, 0x6bd1118c4345b0e5, 0x410500210c3344, 0x30e0c492c2681088, 0xf4405802114f44b1, 0x6002114])))) else (if j < 19 then (if j < 17 then (cbits [0x8404d1400d51e011, 0x88ca92031e278138, 0xa34e4a0d092433e4, 0x24b0e66353198812, 0xc424b30fafc935b4, 0x4cb13930]) else (if j < 18 then (cbits [0x263284d494316f44, 0xe00a41a0084bb131, 0x83142801388604d4, 0x1880e83354e8ca4c, 0x92cba19073a629b2, 0x4fa5313c]) else (cbits [0x2cc385125394294d, 0xb3d1346c4251b105, 0xc00822253149250c, 0x8ca4ca3142201041, 0x92cba98d6ca6203a, 0xcbb0e12e]))) else (if j < 20 then (cbits [0x5202907802140f44, 0x281345c0419480d4, 0x2341330c50a204e2, 0x24b2f2641b31880f, 0xc38d1a4c9469314c, 0x533d1330]) else (if j < 21 then (cbits [0x200085449414ef4e, 0x78134b20411500a4, 0x4c41c630e13292c1, 0xc9414ec4d5631255, 0x855b13156f4856, 0x1900dc22]) else (cbits [0x34c3946b0e264043, 0x6bd1150c435230fd, 0x334f45c])))))) 22 (i % 16)
def s13Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 5 then (if j < 2 then (if j < 1 then (cbits [0x8020080100203f00, 0x9258066200318a01, 0x402b0200f81004c0, 0x261c0524b028c400, 0x1190038c4e046210, 0x3158]) else (cbits [0x804c058700463702, 0xc684263361319509, 0x6930183150998804, 0x361e0d98d84cc642, 0x999084c6503a63e1, 0x4960])) else (if j < 3 then (cbits [0x80ac05e8826c3813, 0xc652463142302711, 0x692c233149198808, 0x361c11a5388d2844, 0x1b1088d2985ac3e2, 0x6271]) else (if j < 4 then (cbits [0xc9408de8846c4830, 0x4c406a3143402080, 0x8f443561c1aa4b0d, 0xc1959a2520e863e6, 0xa0d0cd066e68c483, 0x4961]) else (cbits [0x24b4d1e8880c3840, 0x126e6894c444999a, 0x8c48484a19a24fcd, 0xc02100bd14d1e886, 0x63d11352589a6204, 0x310a])))) else (if j < 8 then (if j < 6 then (cbits [0x18fd30c56986274c, 0x1e889894854321a6, 0x92c5802180bd153, 0x19282c252561282b, 0xea4b178c40ba3140, 0x315a]) else (if j < 7 then (cbits [0xb0e189258ba6375d, 0x5298ca9335d496ae, 0x2c395d61c2ea4dd7, 0xa1a1358cd9a863e0, 0x524c9a8698da92c6, 0x49b3]) else (cbits [0x190dc865602c386a, 0x9298ea93e7249639, 0x4c3e721a63bb0e1c, 0xc19b80bd11c9884e, 0xe30e1f127af892c7, 0x7a23]))) else (if j < 9 then (cbits [0x8c56040270292c01, 0x86670232b8118fc0, 0x23438119bc08cd21, 0x161cc0bd12298710, 0x7a4b405e8902c438, 0x8c]) else (if j < 10 then (cbits [0x8cfa3c6551e31e8f, 0xc69d1e3428f19449, 0xec428f6264bb0fa3, 0xc49980c9423d89d1, 0xe24b270653380299, 0x4a64]) else (cbits [0x253a7129b38f44a0, 0x926e032509c620ce, 0x3250a67a7533d129, 0xa7a455b106a92860, 0x3d10064a154c49a]))))) 21 (i % 16)
def s13Links := pageLinks s13Index s13Codes 5 13 8 6
def s13Data (i : Nat) : Nat × Nat :=
  let e := s13Forest i
  (e &&& 255, e >>> 8)
def s13Sample : Nat × Nat := (s13Blob206400, 96)
def s13Tags := dagTraceTags s13Mask 96 (dagTagBases s13StockWords s13Blob206965 s13Blob207161 96) 9 s13Data
def s13States := dagTrace s13Mask s13StockWords 9 s13Data
def s13MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm7, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 2, 1, 4, 3, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 2, 1, 4, 3, 5] 0 i.val)))]
def s13Moves := dagMoves s13MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s13Autos : DagMovesOK s13Mask s13Goal 64 s13Moves := dagMovesOfCheck (by decide +kernel)
def s13Check := dagCheckNode s13Mask s13Goal s13Chart (dagKnownCloses s13Goal s13Cuts) 175 s13States s13Moves s13Links s13Sample s13Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s13Roots : dagCheckRoots s13Mask s13Goal s13Chart (dagKnownCloses s13Goal s13Cuts) s13Witnesses (dagRef 175 s13States s13Moves s13Links 0) s13StockWords 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s13Block0 : treeBlock 0 24 s13Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s13Block24 : treeBlock 24 24 s13Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s13Block48 : treeBlock 48 24 s13Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s13Block72 : treeBlock 72 24 s13Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s13Block96 : treeBlock 96 24 s13Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s13Block120 : treeBlock 120 24 s13Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s13Block144 : treeBlock 144 24 s13Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s13Block168 : treeBlock 168 7 s13Check = true := by decide +kernel
theorem s13Group0_48 : treeBlock 0 48 s13Check = true := treeBlock_merge (start := 0) (left := 24) (right := 24) (check := s13Check) s13Block0 s13Block24
theorem s13Group48_48 : treeBlock 48 48 s13Check = true := treeBlock_merge (start := 48) (left := 24) (right := 24) (check := s13Check) s13Block48 s13Block72
theorem s13Group0_96 : treeBlock 0 96 s13Check = true := treeBlock_merge (start := 0) (left := 48) (right := 48) (check := s13Check) s13Group0_48 s13Group48_48
theorem s13Group96_48 : treeBlock 96 48 s13Check = true := treeBlock_merge (start := 96) (left := 24) (right := 24) (check := s13Check) s13Block96 s13Block120
theorem s13Group144_31 : treeBlock 144 31 s13Check = true := treeBlock_merge (start := 144) (left := 24) (right := 7) (check := s13Check) s13Block144 s13Block168
theorem s13Group96_79 : treeBlock 96 79 s13Check = true := treeBlock_merge (start := 96) (left := 48) (right := 31) (check := s13Check) s13Group96_48 s13Group144_31
theorem s13Group0_175 : treeBlock 0 175 s13Check = true := treeBlock_merge (start := 0) (left := 96) (right := 79) (check := s13Check) s13Group0_96 s13Group96_79
theorem s13Blocks : treeBlock 0 175 s13Check = true := s13Group0_175
theorem s13Known : Known s13Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s4Stock) s0Stock) s12Stock) s1Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s13Stock : Lower s13Mask s13StockWords s13Goal 10 := by
  apply lowerDag _ _ _ _ s13Autos _ _ _ s13Known _ s13Roots s13Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s13Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel
def s14Mask : Nat := 0x5555ffff5555ffff
abbrev s14Goal : Nat := sGoal &&& s14Mask
abbrev s14StockWords : List Nat := [0xaaaa0000aaaa, 0x4444cccc4444cccc, 0x5050f0f05050f0f0, 0x5500ff005500ff00, 0x5555000055550000, 0x5555ffff00000000]
def s14Fact : Nat × List Nat × Nat × Nat := (s14Mask, s14StockWords, 10, s14Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s14Stock : Lower s14Mask s14StockWords s14Goal 10 := dagShiftLower (width := 64) pm9 s13Stock (by decide +kernel)
def s15Mask : Nat := 0x55ff55ff55ff55ff
abbrev s15Goal : Nat := sGoal &&& s15Mask
abbrev s15StockWords : List Nat := [0xaa00aa00aa00aa, 0x44cc44cc44cc44cc, 0x50f050f050f050f0, 0x5500550055005500, 0x55ff000055ff0000, 0x55ff55ff00000000]
def s15Fact : Nat × List Nat × Nat × Nat := (s15Mask, s15StockWords, 10, s15Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s15Stock : Lower s15Mask s15StockWords s15Goal 10 := dagShiftLower (width := 64) pm8 s13Stock (by decide +kernel)
def s16Mask : Nat := 0x5f5f5f5f5f5f5f5f
abbrev s16Goal : Nat := sGoal &&& s16Mask
abbrev s16StockWords : List Nat := [0xa0a0a0a0a0a0a0a, 0x4c4c4c4c4c4c4c4c, 0x5050505050505050, 0x5f005f005f005f00, 0x5f5f00005f5f0000, 0x5f5f5f5f00000000]
def s16Fact : Nat × List Nat × Nat × Nat := (s16Mask, s16StockWords, 10, s16Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s16Stock : Lower s16Mask s16StockWords s16Goal 10 := dagShiftLower (width := 64) pm2 s13Stock (by decide +kernel)
def s17Mask : Nat := 0x7777777777777777
abbrev s17Goal : Nat := sGoal &&& s17Mask
abbrev s17StockWords : List Nat := [0x2222222222222222, 0x4444444444444444, 0x7070707070707070, 0x7700770077007700, 0x7777000077770000, 0x7777777700000000]
def s17Fact : Nat × List Nat × Nat × Nat := (s17Mask, s17StockWords, 10, s17Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s17Stock : Lower s17Mask s17StockWords s17Goal 10 := dagShiftLower (width := 64) pm3 s13Stock (by decide +kernel)
def s18Blob214388 : Nat := (cbits [0x3c140b020140205, 0x8281508044021107, 0x805000141c1e0506, 0x10503c1c0b0082c2, 0x205402150a044001, 0x6c201a0706820150, 0x1c1f0a078141e050, 0xf0002c200507014, 0x5408110203c02, 0x6c021b0a068001a, 0xc201e02078201b07, 0x80b05014281f0507, 0x10a03c000f0802c0, 0x2068021a07054141, 0x7c001e0a06c001b0, 0x280b0807c081f008, 0x1b050541c110803c, 0x1f0087808])
def s18Blob214771 : Nat := (cbits [0x5fecff9cff27fe7f, 0xf9ff9eff9cfc1cc6, 0x1abc2cf82df1c9d2, 0xf9ff83ff83ff83e])
def s18Blob214886 : Nat := (cbits [0x2021000410010811, 0x8600614401b418c6, 0x552a94a98e2a552, 0x71052a4092908c])
def s18Mask : Nat := 0xcc33cc33
abbrev s18Goal : Nat := sGoal &&& s18Mask
abbrev s18StockWords : List Nat := [0x88228822, 0xcc00cc00, 0xc030c030, 0xcc330000]
def s18Fact : Nat × List Nat × Nat × Nat := (s18Mask, s18StockWords, 5, s18Goal)
def s18Cuts : List (Nat × List Nat × Nat × Nat) := []
def s18Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[5, 11, 17, 26, 5, 11, 17, 26, 5, 11, 17, 26, 1, 14, 20, 1, 14, 20, 1, 14, 20, 1, 14, 20], rfl⟩
def s18Witnesses := unpackWitnesses s18StockWords [2564, 267777, 526849, 795137]
def s18Index (i : Nat) : Nat := unpack 0x9 2 i
def s18Codes (i : Nat) : Nat := unpack 0xf 15 i
def s18Forest (i : Nat) : Nat := unpack 0x1e 14 i
def s18Links := pageLinks s18Index s18Codes 1 13 1 2
def s18Data (i : Nat) : Nat × Nat :=
  let e := s18Forest i
  (e &&& 1, e >>> 1)
def s18Sample : Nat × Nat := (s18Blob214388, 63)
def s18Tags := dagTraceTags s18Mask 63 (dagTagBases s18StockWords s18Blob214771 s18Blob214886 63) 4 s18Data
def s18States := dagTrace s18Mask s18StockWords 4 s18Data
def s18MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s18Moves := dagMoves s18MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s18Autos : DagMovesOK s18Mask s18Goal 64 s18Moves := dagMovesOfCheck (by decide +kernel)
def s18Check := dagCheckNode s18Mask s18Goal s18Chart (dagKnownCloses s18Goal s18Cuts) 1 s18States s18Moves s18Links s18Sample s18Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s18Roots : dagCheckRoots s18Mask s18Goal s18Chart (dagKnownCloses s18Goal s18Cuts) s18Witnesses (dagRef 1 s18States s18Moves s18Links 0) s18StockWords 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s18Block0 : treeBlock 0 1 s18Check = true := by decide +kernel
theorem s18Blocks : treeBlock 0 1 s18Check = true := s18Block0
theorem s18Known : Known s18Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s18Stock : Lower s18Mask s18StockWords s18Goal 5 := by
  apply lowerDag _ _ _ _ s18Autos _ _ _ s18Known _ s18Roots s18Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s18Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def s19Mask : Nat := 0xf00ff00f
abbrev s19Goal : Nat := sGoal &&& s19Mask
abbrev s19StockWords : List Nat := [0xa00aa00a, 0xc00cc00c, 0xf000f000, 0xf00f0000]
def s19Fact : Nat × List Nat × Nat × Nat := (s19Mask, s19StockWords, 5, s19Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s19Stock : Lower s19Mask s19StockWords s19Goal 5 := dagShiftLower (width := 64) pm4 s18Stock (by decide +kernel)
def s20Mask : Nat := 0xf00f0000f00f
abbrev s20Goal : Nat := sGoal &&& s20Mask
abbrev s20StockWords : List Nat := [0xa00a0000a00a, 0xc00c0000c00c, 0xf0000000f000, 0xf00f00000000]
def s20Fact : Nat × List Nat × Nat × Nat := (s20Mask, s20StockWords, 5, s20Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s20Stock : Lower s20Mask s20StockWords s20Goal 5 := dagShiftLower (width := 64) pm5 s18Stock (by decide +kernel)
def s21Blob218381 : Nat := (cbits [0x1402050100c0203, 0x301a0c0640c0702, 0x50300c00030c07, 0x70101c0207030140, 0xc06c041a00864080, 0x780c1e0c074081c0, 0x70101408030c0, 0x1b03068001a00064, 0x3070001c0106c02, 0x78041e02074021d, 0x430030c07c0c1f02, 0x21a0206404190c01, 0xc0306c001b020680, 0x3074001d01070021, 0x7c041f0087c001e0, 0x81b030643007020, 0x7c021e01074])
def s21Blob218742 : Nat := (cbits [0x3bfb33f333caff3f, 0x9cd7c3c7c3d73735, 0xe0e7fc0bfc1bc7c, 0xfbfff3ffe3f8])
def s21Blob218853 : Nat := (cbits [0x2408440110009005, 0x18292a114a8912a1, 0xe01a22a1a88544a, 0x4000e0002a0])
def s21Mask : Nat := 0xff0000ff
abbrev s21Goal : Nat := sGoal &&& s21Mask
abbrev s21StockWords : List Nat := [0xaa0000aa, 0xcc0000cc, 0xf00000f0, 0xff000000]
def s21Fact : Nat × List Nat × Nat × Nat := (s21Mask, s21StockWords, 5, s21Goal)
def s21Cuts : List (Nat × List Nat × Nat × Nat) := []
def s21Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[3, 5, 25, 26, 28, 3, 5, 25, 26, 28, 3, 5, 1, 6, 24, 1, 6, 24, 1, 6, 24, 1, 6, 24], rfl⟩
def s21Witnesses := unpackWitnesses s21StockWords [1538, 263681, 526849, 799233]
def s21Index (i : Nat) : Nat := unpack 0x119 3 i
def s21Codes (i : Nat) : Nat := unpack 0x231c000f 16 i
def s21Forest (i : Nat) : Nat := unpack 0x638803c 15 i
def s21Links := pageLinks s21Index s21Codes 1 13 2 2
def s21Data (i : Nat) : Nat × Nat :=
  let e := s21Forest i
  (e &&& 3, e >>> 2)
def s21Sample : Nat × Nat := (s21Blob218381, 60)
def s21Tags := dagTraceTags s21Mask 60 (dagTagBases s21StockWords s21Blob218742 s21Blob218853 60) 4 s21Data
def s21States := dagTrace s21Mask s21StockWords 4 s21Data
def s21MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s21Moves := dagMoves s21MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s21Autos : DagMovesOK s21Mask s21Goal 64 s21Moves := dagMovesOfCheck (by decide +kernel)
def s21Check := dagCheckNode s21Mask s21Goal s21Chart (dagKnownCloses s21Goal s21Cuts) 2 s21States s21Moves s21Links s21Sample s21Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s21Roots : dagCheckRoots s21Mask s21Goal s21Chart (dagKnownCloses s21Goal s21Cuts) s21Witnesses (dagRef 2 s21States s21Moves s21Links 0) s21StockWords 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s21Block0 : treeBlock 0 2 s21Check = true := by decide +kernel
theorem s21Blocks : treeBlock 0 2 s21Check = true := s21Block0
theorem s21Known : Known s21Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s21Stock : Lower s21Mask s21StockWords s21Goal 5 := by
  apply lowerDag _ _ _ _ s21Autos _ _ _ s21Known _ s21Roots s21Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s21Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def s22Mask : Nat := 0x3003300330033003
abbrev s22Goal : Nat := sGoal &&& s22Mask
abbrev s22StockWords : List Nat := [0x2002200220022002, 0x3000300030003000, 0x3003000030030000, 0x3003300300000000]
def s22Fact : Nat × List Nat × Nat × Nat := (s22Mask, s22StockWords, 5, s22Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s22Stock : Lower s22Mask s22StockWords s22Goal 5 := dagShiftLower (width := 64) pm3 s21Stock (by decide +kernel)
def s23Blob221921 : Nat := (cbits [0xb0182c0b078241a, 0x82c36090c8502c12, 0x41e060782c1a0406, 0x2100b0102c020b02, 0x20d82436100c82c3, 0x682c3e140e8243a1, 0x81e14068181a000, 0x32000c8002c04078, 0x100d80836140c848, 0xf8403a0b0e8103a, 0x8503e120f8243e06, 0x81e00078401a0206, 0x2020c82c2c140784, 0x40d81836000d8103, 0xf8483a060e8003a1, 0x481a100f8103e020, 0x36060c8242c10078, 0x3e020e810])
def s23Blob222307 : Nat := (cbits [0x7bffeffffbffc7e3, 0xeb71cf3c63899f2f, 0x99ff07ffc1ff0fe7, 0xf9ffe0fff83ff0f])
def s23Blob222422 : Nat := (cbits [0x400101200154563, 0x149c9a5528a925a7, 0x612d21248b204a5, 0x7241ac96115403])
def s23Mask : Nat := 0x4444111144441111
abbrev s23Goal : Nat := sGoal &&& s23Mask
abbrev s23StockWords : List Nat := [0x4444000044440000, 0x4040101040401010, 0x4400110044001100, 0x4444111100000000]
def s23Fact : Nat × List Nat × Nat × Nat := (s23Mask, s23StockWords, 5, s23Goal)
def s23Cuts : List (Nat × List Nat × Nat × Nat) := []
def s23Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[26, 44, 50, 26, 44, 50, 26, 44, 50, 26, 44, 50, 12, 22, 36, 40, 12, 22, 36, 40, 12, 22, 36, 40], rfl⟩
def s23Witnesses := unpackWitnesses s23StockWords [13320, 284712, 537618, 808972]
def s23Index (i : Nat) : Nat := unpack 0x9 2 i
def s23Codes (i : Nat) : Nat := unpack 0xf 15 i
def s23Forest (i : Nat) : Nat := unpack 0x1e 14 i
def s23Links := pageLinks s23Index s23Codes 1 13 1 2
def s23Data (i : Nat) : Nat × Nat :=
  let e := s23Forest i
  (e &&& 1, e >>> 1)
def s23Sample : Nat × Nat := (s23Blob221921, 63)
def s23Tags := dagTraceTags s23Mask 63 (dagTagBases s23StockWords s23Blob222307 s23Blob222422 63) 4 s23Data
def s23States := dagTrace s23Mask s23StockWords 4 s23Data
def s23MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s23Moves := dagMoves s23MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s23Autos : DagMovesOK s23Mask s23Goal 64 s23Moves := dagMovesOfCheck (by decide +kernel)
def s23Check := dagCheckNode s23Mask s23Goal s23Chart (dagKnownCloses s23Goal s23Cuts) 1 s23States s23Moves s23Links s23Sample s23Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s23Roots : dagCheckRoots s23Mask s23Goal s23Chart (dagKnownCloses s23Goal s23Cuts) s23Witnesses (dagRef 1 s23States s23Moves s23Links 0) s23StockWords 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s23Block0 : treeBlock 0 1 s23Check = true := by decide +kernel
theorem s23Blocks : treeBlock 0 1 s23Check = true := s23Block0
theorem s23Known : Known s23Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s23Stock : Lower s23Mask s23StockWords s23Goal 5 := by
  apply lowerDag _ _ _ _ s23Autos _ _ _ s23Known _ s23Roots s23Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s23Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def s24Mask : Nat := 0x5005500550055005
abbrev s24Goal : Nat := sGoal &&& s24Mask
abbrev s24StockWords : List Nat := [0x4004400440044004, 0x5000500050005000, 0x5005000050050000, 0x5005500500000000]
def s24Fact : Nat × List Nat × Nat × Nat := (s24Mask, s24StockWords, 5, s24Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s24Stock : Lower s24Mask s24StockWords s24Goal 5 := dagShiftLower (width := 64) pm7 s23Stock (by decide +kernel)
def s25Blob225547 : Nat := (cbits [0x7824130703c0403, 0x82432070b8442307, 0x4131100c2403110c, 0xe0108c1c1f090780, 0x90cc0432070bc442, 0x3c1c03070f844330, 0x241f010784413010, 0x33110bc042e0908c, 0x70fc443e090f804, 0x781c131103c240f, 0xc242e0708c041f11, 0x43f010f81c32010b, 0x3090bc441f110fc2, 0x10fc1c3])
def s25Blob225851 : Nat := (cbits [0xd82afcb79b76b717, 0xf1cf1cccbedbeda8, 0xefe0fe0fe0f0df1c])
def s25Blob225947 : Nat := (cbits [0x902a000000000000, 0x2302094441248018, 0x180a484442902441])
def s25Mask : Nat := 0xc00cc00cc00cc00c
abbrev s25Goal : Nat := sGoal &&& s25Mask
abbrev s25StockWords : List Nat := [0x8008800880088008, 0xc000c000c000c000, 0xc00c0000c00c0000, 0xc00cc00c00000000]
def s25Fact : Nat × List Nat × Nat × Nat := (s25Mask, s25StockWords, 5, s25Goal)
def s25Cuts : List (Nat × List Nat × Nat × Nat) := []
def s25Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[3, 30, 46, 50, 3, 30, 46, 50, 3, 30, 46, 50, 14, 18, 34, 14, 18, 34, 14, 18, 34, 14, 18, 34], rfl⟩
def s25Witnesses := unpackWitnesses s25StockWords [1538, 277522, 539662, 809998]
def s25Index (i : Nat) : Nat := unpack 0x9 2 i
def s25Codes (i : Nat) : Nat := unpack 0xf 15 i
def s25Forest (i : Nat) : Nat := unpack 0x1e 14 i
def s25Links := pageLinks s25Index s25Codes 1 13 1 2
def s25Data (i : Nat) : Nat × Nat :=
  let e := s25Forest i
  (e &&& 1, e >>> 1)
def s25Sample : Nat × Nat := (s25Blob225547, 48)
def s25Tags := dagTraceTags s25Mask 48 (dagTagBases s25StockWords s25Blob225851 s25Blob225947 48) 4 s25Data
def s25States := dagTrace s25Mask s25StockWords 4 s25Data
def s25MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s25Moves := dagMoves s25MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s25Autos : DagMovesOK s25Mask s25Goal 64 s25Moves := dagMovesOfCheck (by decide +kernel)
def s25Check := dagCheckNode s25Mask s25Goal s25Chart (dagKnownCloses s25Goal s25Cuts) 1 s25States s25Moves s25Links s25Sample s25Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s25Roots : dagCheckRoots s25Mask s25Goal s25Chart (dagKnownCloses s25Goal s25Cuts) s25Witnesses (dagRef 1 s25States s25Moves s25Links 0) s25StockWords 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s25Block0 : treeBlock 0 1 s25Check = true := by decide +kernel
theorem s25Blocks : treeBlock 0 1 s25Check = true := s25Block0
theorem s25Known : Known s25Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s25Stock : Lower s25Mask s25StockWords s25Goal 5 := by
  apply lowerDag _ _ _ _ s25Autos _ _ _ s25Known _ s25Roots s25Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s25Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def pm13 : List (List (Nat × Nat) × List (Nat × Nat)) := [st45]
def s26Blob228848 : Nat := (cbits [0x3c180d0100c0203, 0x241308044021107, 0x21008841c1e0607, 0x1070b8182c1108c4, 0x80c84432090c8603, 0x3444030900c00031, 0x110603c1c0d008, 0x130084c601109044, 0x80701c1c0804c04, 0x7c241e06078181d, 0xc602111084002107, 0xc2c1008c04230088, 0xe060b8182d100b01, 0x80c40231070bc442, 0xc82032010c840310, 0x6033110cc2433100, 0x3070f8603c060f0, 0x3440030800c1c, 0x4404110103c020f, 0x60131104c001310, 0x21d18070241c0007, 0xe01078201d070740, 0x1084241f0607c201, 0x8c24230008c20210, 0x602c110b0002c180, 0x2e100b41c2d008b4, 0x110bc182f100b804])
def s26Blob229411 : Nat := (cbits [0xf1c793f93ffc4e7f, 0x389fa94bce3f9c7f, 0xf039e07379f8e38e, 0x8e00fc0fc0e0318c, 0xff03c1f0ffc1ff83, 0x1fffc0fff000f, 0xffffff00003fe00, 0xfffe0000])
def s26Blob229595 : Nat := (cbits [0x1008008200211, 0x5259a94a02000401, 0x9493292618c8c52c, 0x1a00b40b40c0318c, 0xa60ac06044008800, 0x135534025520044, 0x45a44a6004134c00, 0xa9a00268])
def s26Mask : Nat := 0xf00ff00ff00ff00f
abbrev s26Goal : Nat := sGoal &&& s26Mask
abbrev s26StockWords : List Nat := [0xa00aa00aa00aa00a, 0xc00cc00cc00cc00c, 0xf000f000f000f000, 0xf00f0000f00f0000, 0xf00ff00f00000000]
def s26Fact : Nat × List Nat × Nat × Nat := (s26Mask, s26StockWords, 8, s26Goal)
def s26Cuts : List (Nat × List Nat × Nat × Nat) := [s6Fact, s19Fact, s20Fact, s22Fact, s24Fact, s25Fact]
def s26Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[3, 13, 17, 28, 33, 44, 50, 3, 13, 17, 28, 33, 1, 14, 18, 34, 48, 1, 14, 18, 34, 48, 1, 14], rfl⟩
def s26Witnesses := unpackWitnesses s26StockWords [1538, 263681, 530945, 795137, 1065473]
def s26Index (i : Nat) : Nat := unpack (cbits [0x705b585858430f01, 0x888873]) 8 i
def s26Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0xdc802b08020001f, 0x129373a4b0a314a0, 0xc381a4b04314bb0e, 0x4b30e0c92c10c526, 0x31880631]) else 0x10c38) 18 (i % 16)
def s26Forest (i : Nat) : Nat := unpack (cbits [0x9610c508010201f0, 0x60a4b18628202b14, 0x126e2c38849]) 17 i
def s26Links := pageLinks s26Index s26Codes 3 13 4 4
def s26Data (i : Nat) : Nat × Nat :=
  let e := s26Forest i
  (e &&& 15, e >>> 4)
def s26Sample : Nat × Nat := (s26Blob228848, 96)
def s26Tags := dagTraceTags s26Mask 96 (dagTagBases s26StockWords s26Blob229411 s26Blob229595 96) 7 s26Data
def s26States := dagTrace s26Mask s26StockWords 7 s26Data
def s26MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm13, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)))]
def s26Moves := dagMoves s26MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s26Autos : DagMovesOK s26Mask s26Goal 64 s26Moves := dagMovesOfCheck (by decide +kernel)
def s26Check := dagCheckNode s26Mask s26Goal s26Chart (dagKnownCloses s26Goal s26Cuts) 10 s26States s26Moves s26Links s26Sample s26Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s26Roots : dagCheckRoots s26Mask s26Goal s26Chart (dagKnownCloses s26Goal s26Cuts) s26Witnesses (dagRef 10 s26States s26Moves s26Links 0) s26StockWords 7 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s26Block0 : treeBlock 0 10 s26Check = true := by decide +kernel
theorem s26Blocks : treeBlock 0 10 s26Check = true := s26Block0
theorem s26Known : Known s26Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s25Stock) s24Stock) s22Stock) s20Stock) s19Stock) s6Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s26Stock : Lower s26Mask s26StockWords s26Goal 8 := by
  apply lowerDag _ _ _ _ s26Autos _ _ _ s26Known _ s26Roots s26Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s26Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s27Mask : Nat := 0xcccccccc33333333
abbrev s27Goal : Nat := sGoal &&& s27Mask
abbrev s27StockWords : List Nat := [0x8888888822222222, 0xcccccccc00000000, 0xc0c0c0c030303030, 0xcc00cc0033003300, 0xcccc000033330000]
def s27Fact : Nat × List Nat × Nat × Nat := (s27Mask, s27StockWords, 8, s27Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s27Stock : Lower s27Mask s27StockWords s27Goal 8 := dagShiftLower (width := 64) pm10 s26Stock (by decide +kernel)
def s28Blob233836 : Nat := (cbits [0x1402050100c0203, 0xc1009008240c0702, 0x2110703c180d0502, 0x70a0542413080440, 0x9068141a0c0642c1, 0x70281c06070301a0, 0x44230b0781c1e0c0, 0x2e150ac442603098, 0x110c82432150b81c, 0xc0003150e82c36, 0x444030900c140303, 0x805060140c050001, 0x70201c04070081c2, 0x502400090b01c1c0, 0x2c020b0c02418090, 0x540b0702c100b010, 0xd04034080d00834, 0x603c140f0303c1c, 0x442811090440011, 0xc20130104c02130c, 0x150205402150b04, 0x70905c0c170b0542, 0x8064101900864281, 0x681c1a04068041a0, 0x141b150682c1a080, 0x1c02070301b0906c, 0xb070201c0707010])
def s28Blob234404 : Nat := (cbits [0xfffffffc0900ffff, 0xffc752930703ffff, 0x7fc70f0e1f0f87f, 0xfe00ff8136f8631c, 0x38ff83e0f8007f00, 0xffff8000ffff0002, 0x3c0fffc00, 0xff000000ffffffff, 0x3])
def s28Blob234597 : Nat := (cbits [0x210080000000425, 0xffc3529200008110, 0xa3d438a271a2d17b, 0xb484e70912d86318, 0x386d83c0a8505a84, 0x35990008d9ce4212, 0x8842140b6f800, 0xad000000c6626cce, 0x80000001000042])
def s28Mask : Nat := 0xccccccccffffffff
abbrev s28Goal : Nat := sGoal &&& s28Mask
abbrev s28StockWords : List Nat := [0x88888888aaaaaaaa, 0xcccccccccccccccc, 0xc0c0c0c0f0f0f0f0, 0xcc00cc00ff00ff00, 0xcccc0000ffff0000, 0xcccccccc00000000]
def s28Fact : Nat × List Nat × Nat × Nat := (s28Mask, s28StockWords, 9, s28Goal)
def s28Cuts : List (Nat × List Nat × Nat × Nat) := [s27Fact, s1Fact, s0Fact, s4Fact]
def s28Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[3, 5, 9, 17, 26, 28, 38, 50, 3, 5, 9, 17, 1, 14, 22, 24, 42, 1, 14, 22, 24, 42, 1, 14], rfl⟩
def s28Witnesses := unpackWitnesses s28StockWords [1538, 263681, 526849, 791041, 1057281, 1330182]
def s28Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0x40500400e207401, 0x5054150541504511, 0x64190551]) else (if j < 2 then (cbits [0x6701b16c19264190, 0x5088e2088220881c, 0xa0253942]) else 0xac283a0280)) 10 (i % 16)
def s28Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0x708009020080003f, 0x37180331602b0c02, 0x92d3492c2a041220, 0x2c38409373a93338, 0x6c380492c44c394]) else (if j < 2 then (cbits [0x100280e01c0a34c, 0x281a01c1404c1204, 0x4c2004c1e0341c0, 0xa008283402633024, 0x2ec382c314240420]) else (cbits [0x10431432f4430c3f, 0x4d3c01136c382e34, 0x341063143e34c300, 0x36c3832]))) 20 (i % 16)
def s28Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0x492c08010080fc0, 0x270469828024161c, 0xc080380a0700e0e0, 0x8680cc10158204c1, 0x1a1a0283403]) else (if j < 2 then (cbits [0x2404c4806e08130d, 0x145808208d014198, 0x5e88b30fd661c2c3, 0x60a4b4161c3692c0, 0x1a63c0117926]) else 0xc39058700a4dc1)) 19 (i % 16)
def s28Links := pageLinks s28Index s28Codes 4 13 6 5
def s28Data (i : Nat) : Nat × Nat :=
  let e := s28Forest i
  (e &&& 63, e >>> 6)
def s28Sample : Nat × Nat := (s28Blob233836, 96)
def s28Tags := dagTraceTags s28Mask 96 (dagTagBases s28StockWords s28Blob234404 s28Blob234597 96) 8 s28Data
def s28States := dagTrace s28Mask s28StockWords 8 s28Data
def s28MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s28Moves := dagMoves s28MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s28Autos : DagMovesOK s28Mask s28Goal 64 s28Moves := dagMovesOfCheck (by decide +kernel)
def s28Check := dagCheckNode s28Mask s28Goal s28Chart (dagKnownCloses s28Goal s28Cuts) 35 s28States s28Moves s28Links s28Sample s28Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s28Roots : dagCheckRoots s28Mask s28Goal s28Chart (dagKnownCloses s28Goal s28Cuts) s28Witnesses (dagRef 35 s28States s28Moves s28Links 0) s28StockWords 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s28Block0 : treeBlock 0 24 s28Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s28Block24 : treeBlock 24 11 s28Check = true := by decide +kernel
theorem s28Group0_35 : treeBlock 0 35 s28Check = true := treeBlock_merge (start := 0) (left := 24) (right := 11) (check := s28Check) s28Block0 s28Block24
theorem s28Blocks : treeBlock 0 35 s28Check = true := s28Group0_35
theorem s28Known : Known s28Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s4Stock) s0Stock) s1Stock) s27Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s28Stock : Lower s28Mask s28StockWords s28Goal 9 := by
  apply lowerDag _ _ _ _ s28Autos _ _ _ s28Known _ s28Roots s28Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s28Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel
def s29Mask : Nat := 0xccccffffccccffff
abbrev s29Goal : Nat := sGoal &&& s29Mask
abbrev s29StockWords : List Nat := [0x8888aaaa8888aaaa, 0xcccccccccccccccc, 0xc0c0f0f0c0c0f0f0, 0xcc00ff00cc00ff00, 0xcccc0000cccc0000, 0xccccffff00000000]
def s29Fact : Nat × List Nat × Nat × Nat := (s29Mask, s29StockWords, 9, s29Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Stock : Lower s29Mask s29StockWords s29Goal 9 := dagShiftLower (width := 64) pm9 s28Stock (by decide +kernel)
def pm14 : List (List (Nat × Nat) × List (Nat × Nat)) := [st34]
def s30Blob238483 : Nat := (cbits [0x3c1009008240c07, 0x42c1708044021107, 0x2070b0781c1e0c06, 0x9000242c070701c0, 0xc04400110303c300, 0x641019008640c170, 0x1c1f0c0780c1e080, 0x90702400070b07c, 0xb03c100f0083c20, 0x5c02170b0441011, 0x8101e00064201707, 0x70c07c0c1f0807, 0xf0003c0c090801c1, 0xc05c001703044300, 0x7c001e0b0641c190, 0x30070807c101f008, 0x1707044200f0b024, 0x7c021e0306410])
def s30Blob238870 : Nat := (cbits [0xbfefff3fff3ffcff, 0xd5f36fdce7c49f49, 0xe6fc73e0fbf8e38e, 0xf8ff83ff03ff03f0])
def s30Blob238986 : Nat := (cbits [0x4020000420080412, 0x2a0c910a8b449b49, 0x194646494992498c, 0x78a4a9292a252e0])
def s30Mask : Nat := 0xc3c3c3c3
abbrev s30Goal : Nat := sGoal &&& s30Mask
abbrev s30StockWords : List Nat := [0x82828282, 0xc0c0c0c0, 0xc300c300, 0xc3c30000]
def s30Fact : Nat × List Nat × Nat × Nat := (s30Mask, s30StockWords, 6, s30Goal)
def s30Cuts : List (Nat × List Nat × Nat × Nat) := []
def s30Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[7, 9, 17, 30, 7, 9, 17, 30, 7, 9, 17, 30, 1, 14, 22, 24, 1, 14, 22, 24, 1, 14, 22, 24], rfl⟩
def s30Witnesses := unpackWitnesses s30StockWords [3590, 265729, 528897, 795137]
def s30Index (i : Nat) : Nat := unpack 0x28a28301 6 i
def s30Codes (i : Nat) : Nat := unpack (cbits [0x31010c504010000f, 0x1692c3]) 17 i
def s30Forest (i : Nat) : Nat := unpack 0x310118a100410078 16 i
def s30Links := pageLinks s30Index s30Codes 3 13 3 4
def s30Data (i : Nat) : Nat × Nat :=
  let e := s30Forest i
  (e &&& 7, e >>> 3)
def s30Sample : Nat × Nat := (s30Blob238483, 64)
def s30Tags := dagTraceTags s30Mask 64 (dagTagBases s30StockWords s30Blob238870 s30Blob238986 64) 5 s30Data
def s30States := dagTrace s30Mask s30StockWords 5 s30Data
def s30MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm14, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 4, 3, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 4, 3, 5] 0 i.val)))]
def s30Moves := dagMoves s30MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s30Autos : DagMovesOK s30Mask s30Goal 64 s30Moves := dagMovesOfCheck (by decide +kernel)
def s30Check := dagCheckNode s30Mask s30Goal s30Chart (dagKnownCloses s30Goal s30Cuts) 4 s30States s30Moves s30Links s30Sample s30Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s30Roots : dagCheckRoots s30Mask s30Goal s30Chart (dagKnownCloses s30Goal s30Cuts) s30Witnesses (dagRef 4 s30States s30Moves s30Links 0) s30StockWords 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s30Block0 : treeBlock 0 4 s30Check = true := by decide +kernel
theorem s30Blocks : treeBlock 0 4 s30Check = true := s30Block0
theorem s30Known : Known s30Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s30Stock : Lower s30Mask s30StockWords s30Goal 6 := by
  apply lowerDag _ _ _ _ s30Autos _ _ _ s30Known _ s30Roots s30Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s30Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def s31Mask : Nat := 0xc3c30000c3c3
abbrev s31Goal : Nat := sGoal &&& s31Mask
abbrev s31StockWords : List Nat := [0x828200008282, 0xc0c00000c0c0, 0xc3000000c300, 0xc3c300000000]
def s31Fact : Nat × List Nat × Nat × Nat := (s31Mask, s31StockWords, 5, s31Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s31Stock : Lower s31Mask s31StockWords s31Goal 5 := dagShiftLower (width := 64) pm9 s18Stock (by decide +kernel)
def pm15 : List (List (Nat × Nat) × List (Nat × Nat)) := [st23, st25, st24]
def s32Mask : Nat := 0xc300c300c300c3
abbrev s32Goal : Nat := sGoal &&& s32Mask
abbrev s32StockWords : List Nat := [0x82008200820082, 0xc000c000c000c0, 0xc3000000c30000, 0xc300c300000000]
def s32Fact : Nat × List Nat × Nat × Nat := (s32Mask, s32StockWords, 5, s32Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s32Stock : Lower s32Mask s32StockWords s32Goal 5 := dagShiftLower (width := 64) pm15 s18Stock (by decide +kernel)
def s33Blob243046 : Nat := (cbits [0x3c1009008240c07, 0x42c1708044021107, 0x2210b0781c1e0c06, 0xe140a40c26100840, 0xc0e42c36180c41c2, 0x242c070701c02071, 0xc0f140243009000, 0x1718044301100044, 0x80641019008640c, 0x7c301e030787019, 0x45021000842c1f07, 0x260b0981c261808, 0x9040a402290309c4, 0x40b80c2e1c0a4402, 0xc42031008c41c2f1, 0x6036030d87031100, 0x39140e430390b0dc, 0x1c0f82c3e070f860, 0x242009070240007, 0xc100f0083c700910, 0x110b04410110b03, 0x70705c02171c0444, 0x8064501900064201, 0x7c701e08078101e1, 0x202104084301f030, 0x261409800261c084, 0xb09c1c270089c60])
def s33Blob243614 : Nat := (cbits [0x1e7cf8f9fffeacff, 0x111d5349e3e3ffff, 0xfc7c70e1e3870f1e, 0xfc07f01fe1e2638e, 0xfe0383f0007f80fe, 0x7fff00fff8001f, 0xffffffe00003fc00, 0xff800000])
def s33Blob243800 : Nat := (cbits [0x8100020040412, 0x1119534920001020, 0xc020228262850b1a, 0xac46a14d44ca618c, 0x8c5382e04ad52952, 0x935a4a94d7508295, 0x9962c4c10882a800, 0x1a130c18])
def s33Mask : Nat := 0xc3c3c3c3c3c3c3c3
abbrev s33Goal : Nat := sGoal &&& s33Mask
abbrev s33StockWords : List Nat := [0x8282828282828282, 0xc0c0c0c0c0c0c0c0, 0xc300c300c300c300, 0xc3c30000c3c30000, 0xc3c3c3c300000000]
def s33Fact : Nat × List Nat × Nat × Nat := (s33Mask, s33StockWords, 8, s33Goal)
def s33Cuts : List (Nat × List Nat × Nat × Nat) := [s30Fact, s31Fact, s32Fact]
def s33Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[7, 9, 17, 30, 33, 38, 7, 9, 17, 30, 33, 38, 1, 14, 22, 56, 1, 14, 22, 56, 1, 14, 22, 56], rfl⟩
def s33Witnesses := unpackWitnesses s33StockWords [3590, 265729, 528897, 795137, 1065473]
def s33Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0x44e21108838c3a01, 0x2e170a1d028140a0, 0xb9dc]) else 0x341a0) 9 (i % 16)
def s33Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0x1e2002410040001f, 0x80ac900f90013140, 0xcd18f98315286294, 0x962062b38c4168ca, 0xcc4010c52e4]) else (cbits [0x81300d060144692c, 0xa4b0b310043141c0, 0xf496166200c6295])) 19 (i % 16)
def s33Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0x862820040403e0, 0x8050600784012131, 0x28100f8402610201, 0x118f8462a13102c6, 0x4963cc40]) else 0xc561) 18 (i % 16)
def s33Links := pageLinks s33Index s33Codes 4 13 5 5
def s33Data (i : Nat) : Nat × Nat :=
  let e := s33Forest i
  (e &&& 31, e >>> 5)
def s33Sample : Nat × Nat := (s33Blob243046, 96)
def s33Tags := dagTraceTags s33Mask 96 (dagTagBases s33StockWords s33Blob243614 s33Blob243800 96) 7 s33Data
def s33States := dagTrace s33Mask s33StockWords 7 s33Data
def s33MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm14, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 4, 3, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 4, 3, 5] 0 i.val)))]
def s33Moves := dagMoves s33MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s33Autos : DagMovesOK s33Mask s33Goal 64 s33Moves := dagMovesOfCheck (by decide +kernel)
def s33Check := dagCheckNode s33Mask s33Goal s33Chart (dagKnownCloses s33Goal s33Cuts) 17 s33States s33Moves s33Links s33Sample s33Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s33Roots : dagCheckRoots s33Mask s33Goal s33Chart (dagKnownCloses s33Goal s33Cuts) s33Witnesses (dagRef 17 s33States s33Moves s33Links 0) s33StockWords 7 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s33Block0 : treeBlock 0 17 s33Check = true := by decide +kernel
theorem s33Blocks : treeBlock 0 17 s33Check = true := s33Block0
theorem s33Known : Known s33Cuts := (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s32Stock) s31Stock) s30Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s33Stock : Lower s33Mask s33StockWords s33Goal 8 := by
  apply lowerDag _ _ _ _ s33Autos _ _ _ s33Known _ s33Roots s33Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s33Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl <;> decide +kernel
def s34Mask : Nat := 0xffff00000000ffff
abbrev s34Goal : Nat := sGoal &&& s34Mask
abbrev s34StockWords : List Nat := [0xaaaa00000000aaaa, 0xcccc00000000cccc, 0xf0f000000000f0f0, 0xff0000000000ff00, 0xffff000000000000]
def s34Fact : Nat × List Nat × Nat × Nat := (s34Mask, s34StockWords, 8, s34Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s34Stock : Lower s34Mask s34StockWords s34Goal 8 := dagShiftLower (width := 64) pm3 s33Stock (by decide +kernel)
def s35Blob248084 : Nat := (cbits [0x1402050100c0203, 0xc1009008240c0702, 0x2110703c180d0502, 0x70a0542413080440, 0x9068141a0c0642c1, 0x70281c06070301a0, 0x60310b0781c1e0c0, 0x361a0d46032090c8, 0x1c0e870391a0d82c, 0xc00031c0f0683c, 0x400050900c140303, 0x2070a01418050301, 0x70701c08070101c0, 0x60241409000242c0, 0x2c040b0082c30090, 0x80d008341c0b040, 0xf0303c1c0d04034, 0x904400110603c14, 0x84c60110c0442811, 0x42c130804c041300, 0xc150805408150085, 0x70905c0c171a0542, 0x8064101900864281, 0x68101a0106870190, 0x701a0b068201a070, 0x1c0c06c241b0506c, 0x80701c1c0407008])
def s35Blob248653 : Nat := (cbits [0xfffffffc4900ffff, 0xb6c752930e07ffff, 0xff8707838787c3c, 0x3f807fc338f8631c, 0xc0ff83e0f0007f80, 0xffff80003fff8003, 0xc0000003fffffc00, 0xff000000ffffffff, 0x3])
def s35Blob248853 : Nat := (cbits [0x88040000000425, 0x12c3529200008088, 0x46a834509c5168b8, 0x2d42738938d86318, 0xc06d83c050a05d41, 0x6b35000236672112, 0x80044223ffb6f800, 0xed0000008dc66e67, 0x104080400000003])
def s35Mask : Nat := 0xffff0000ffffffff
abbrev s35Goal : Nat := sGoal &&& s35Mask
abbrev s35StockWords : List Nat := [0xaaaa0000aaaaaaaa, 0xcccc0000cccccccc, 0xf0f00000f0f0f0f0, 0xff000000ff00ff00, 0xffff0000ffff0000, 0xffff000000000000]
def s35Fact : Nat × List Nat × Nat × Nat := (s35Mask, s35StockWords, 9, s35Goal)
def s35Cuts : List (Nat × List Nat × Nat × Nat) := [s34Fact, s1Fact, s0Fact, s4Fact]
def s35Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[3, 5, 9, 17, 26, 28, 50, 3, 5, 9, 17, 26, 1, 14, 22, 52, 56, 1, 14, 22, 52, 56, 1, 14], rfl⟩
def s35Witnesses := unpackWitnesses s35StockWords [1538, 263681, 526849, 791041, 1057281, 1336338]
def s35Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0x148120480f307801, 0x705c1705c1344c12, 0x681a05cd]) else (if j < 2 then (cbits [0x17c1f07c1e1691a0, 0x709c27085a10805f, 0xa86a09ce]) else (cbits [0x7b86e0b82e0aceb0, 0x3a0d9360d82f]))) 10 (i % 16)
def s35Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 2 then (if j < 1 then (cbits [0x70a009020080003f, 0x37200331802b0e02, 0x92d3892c300412c0, 0xa94148937409333c, 0x492c52c3950c384]) else (cbits [0xc0c34c08c3806941, 0x4c14040120281001, 0xc4c1cc3c1a94c160, 0x8034260282201c1e, 0x24010240402a34c2])) else (if j < 3 then (cbits [0xc2a03e0c0082e948, 0x4434c381e9353292, 0xc38323410431436f, 0x4c40420293ec4c3a, 0x60084493046c4c4]) else (cbits [0xe3e92c1e0351a029, 0x144ef444cc384693, 0xc413ac3836341083, 0x4e]))) 20 (i % 16)
def s35Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0x8492c08010080fc0, 0x4c180120b0e024a0, 0x50400708013823, 0x8680ac1026100402, 0x6261ac3c3529]) else (if j < 2 then (cbits [0x2204048038880cc1, 0x3704698880d11014, 0x5258c810414a42e0, 0xea4b017a232c386, 0x6263e92d0587]) else (cbits [0x42c40840530a4cc1, 0x38992820a4dc1626, 0x18720b0e017a24cc]))) 19 (i % 16)
def s35Links := pageLinks s35Index s35Codes 4 13 6 5
def s35Data (i : Nat) : Nat × Nat :=
  let e := s35Forest i
  (e &&& 63, e >>> 6)
def s35Sample : Nat × Nat := (s35Blob248084, 96)
def s35Tags := dagTraceTags s35Mask 96 (dagTagBases s35StockWords s35Blob248653 s35Blob248853 96) 8 s35Data
def s35States := dagTrace s35Mask s35StockWords 8 s35Data
def s35MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s35Moves := dagMoves s35MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s35Autos : DagMovesOK s35Mask s35Goal 64 s35Moves := dagMovesOfCheck (by decide +kernel)
def s35Check := dagCheckNode s35Mask s35Goal s35Chart (dagKnownCloses s35Goal s35Cuts) 42 s35States s35Moves s35Links s35Sample s35Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s35Roots : dagCheckRoots s35Mask s35Goal s35Chart (dagKnownCloses s35Goal s35Cuts) s35Witnesses (dagRef 42 s35States s35Moves s35Links 0) s35StockWords 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s35Block0 : treeBlock 0 24 s35Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s35Block24 : treeBlock 24 18 s35Check = true := by decide +kernel
theorem s35Group0_42 : treeBlock 0 42 s35Check = true := treeBlock_merge (start := 0) (left := 24) (right := 18) (check := s35Check) s35Block0 s35Block24
theorem s35Blocks : treeBlock 0 42 s35Check = true := s35Group0_42
theorem s35Known : Known s35Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s4Stock) s0Stock) s1Stock) s34Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s35Stock : Lower s35Mask s35StockWords s35Goal 9 := by
  apply lowerDag _ _ _ _ s35Autos _ _ _ s35Known _ s35Roots s35Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s35Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel
def s36Mask : Nat := 0xccffccffccffccff
abbrev s36Goal : Nat := sGoal &&& s36Mask
abbrev s36StockWords : List Nat := [0x88aa88aa88aa88aa, 0xcccccccccccccccc, 0xc0f0c0f0c0f0c0f0, 0xcc00cc00cc00cc00, 0xccff0000ccff0000, 0xccffccff00000000]
def s36Fact : Nat × List Nat × Nat × Nat := (s36Mask, s36StockWords, 9, s36Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s36Stock : Lower s36Mask s36StockWords s36Goal 9 := dagShiftLower (width := 64) pm11 s35Stock (by decide +kernel)
def s37Mask : Nat := 0xcfcfcfcfcfcfcfcf
abbrev s37Goal : Nat := sGoal &&& s37Mask
abbrev s37StockWords : List Nat := [0x8a8a8a8a8a8a8a8a, 0xcccccccccccccccc, 0xc0c0c0c0c0c0c0c0, 0xcf00cf00cf00cf00, 0xcfcf0000cfcf0000, 0xcfcfcfcf00000000]
def s37Fact : Nat × List Nat × Nat × Nat := (s37Mask, s37StockWords, 9, s37Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s37Stock : Lower s37Mask s37StockWords s37Goal 9 := dagShiftLower (width := 64) pm12 s35Stock (by decide +kernel)
def s38Blob257665 : Nat := (cbits [0x1c02050100c0203, 0x41c0f0502c020903, 0x41a0b05c24130084, 0x10b0781c1e090681, 0x10980c261108c022, 0xc8542e070b8542b1, 0x543a0b0d84432090, 0x30900c14030300c, 0x101c02070301444, 0x82c14090b01c1c07, 0x4540b0702c040b00, 0x40f0303c1c0d0083, 0x30104c0213090441, 0x305c2c15008542c1, 0x68041a0086424170, 0x141b150682c1a070, 0x1e050780c1e0906c, 0x110842c1f0707c24, 0x89454230108c0223, 0x82c2607098042600, 0x2291109c0c271509, 0xe110ac142b150a40, 0x70bc442e050b80c2, 0xc80432008c4542f0, 0x4433090cc54320b0, 0x37110d82436030d8, 0x110e8243a050e82c])
def s38Blob258238 : Nat := (cbits [0xe30ffffffe04c3ff, 0xdfffbf6b118e3f0f, 0xfff7f3f77ff6767b, 0x7c078783e09b324c, 0x11c3c701e07c3f8, 0xe007fc007ff807fc, 0x7ffff80001e03f80, 0x1ffc000fff80000, 0xffffffff80000000])
def s38Blob258452 : Nat := (cbits [0x8908840004095, 0xbfffbf6a00080409, 0xfff7fbf6fff76f77, 0x6463432322893248, 0x51c146012224160, 0x204698a429a00565, 0x5245480208a02b00, 0x1156800054a00040, 0x89452a8480800040])
def s38Mask : Nat := 0xeeeeeeeeeeeeeeee
abbrev s38Goal : Nat := sGoal &&& s38Mask
abbrev s38StockWords : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xe0e0e0e0e0e0e0e0, 0xee00ee00ee00ee00, 0xeeee0000eeee0000, 0xeeeeeeee00000000]
def s38Fact : Nat × List Nat × Nat × Nat := (s38Mask, s38StockWords, 9, s38Goal)
def s38Cuts : List (Nat × List Nat × Nat × Nat) := []
def s38Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[3, 5, 9, 17, 26, 33, 38, 50, 3, 5, 9, 17, 1, 14, 22, 42, 1, 14, 22, 42, 1, 14, 22, 42], rfl⟩
def s38Witnesses := unpackWitnesses s38StockWords [1538, 263681, 526849, 791041, 1057281, 1327617]
def s38Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 6 then (if j < 3 then (if j < 1 then (cbits [0x1f0032300388001, 0x801f003e007c00f8, 0xc01f883e047c00f, 0x2b8043508601]) else (if j < 2 then (cbits [0x2f005e00bc015c7, 0x402f065e00bc0178, 0x84730806100c2018, 0x34006800d001]) else (cbits [0x34066800d001a00, 0x436866d00d611ac, 0xc141807730e819c, 0x430084090802]))) else (if j < 4 then (cbits [0x4430086010c02180, 0x8045088a01140218, 0x38247008e011c023, 0x48829101200a]) else (if j < 5 then (cbits [0x4b0096012c02484, 0x405280a0152c5258, 0xa005286a5014a029, 0x5580a80d5002]) else (cbits [0x568cad015612ac0, 0x5a00b401660acc, 0xe815b86b6056812d, 0x6382c7017662])))) else (if j < 9 then (if j < 7 then (cbits [0x16480c8059003200, 0xc465a0cb01940b24, 0x7c06f80df01be036, 0x6f86df01be03]) else (if j < 8 then (cbits [0x27200e305c603881, 0x807300e601cc0390, 0x9c07380e605cc039, 0x7486e901ce13]) else (cbits [0x4761eec01d803b00, 0xc07f80ff01fe03ec, 0xfc27f80ff01fe03f, 0x808101020203]))) else (if j < 11 then (if j < 10 then (cbits [0x819d03020214040, 0x4088811102220444, 0x4c18981110a22044, 0x8a8314062804]) else (cbits [0x1948728062c94580, 0x4198812e0e5a0cb0, 0xcc0998132066404c, 0x9e05361a661c])) else (if j < 12 then (cbits [0xea0033e0a7c04f80, 0xa80150029e0d04, 0x580ab01540aa0254, 0xad015a02ac25]) else 0x2b42d680)))) 15 (i % 16)
def s38Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 11 then (if j < 5 then (if j < 2 then (if j < 1 then (cbits [0x120090080200003f, 0x9803c5200e068034, 0xc0271d807c6c01b1, 0xdc7e0339d80ae6, 0x314a2010e7e03f22, 0x318c54b8]) else (cbits [0xf831f330c78c831b, 0xe0caecc32ab20c9c, 0x337410cd8fc333b, 0xd0f04342bf0cfd2, 0x6274c988524620c8, 0x4e98ad36])) else (if j < 3 then (cbits [0x586375018d93c633, 0x924b1646435698fd, 0x4937d6a4cf3292dc, 0x250f40942cf24ff6, 0xc3f5c30e566c38d6, 0x60310d78]) else (if j < 4 then (cbits [0x4008dc3d1766f44, 0x20ca80831e018c50, 0xc620828d080a3368, 0xa50a0c92c0398d80, 0x318843d1010c3883, 0x58c7014]) else (cbits [0x18340060cd216328, 0xb00741e01c070022, 0xc0298780a03401e0, 0xd4360348d00aa2, 0x418d81004803611, 0x92010a44])))) else (if j < 8 then (if j < 6 then (cbits [0x4e63613188014314, 0x430e24e9429324b0, 0x31405802250f441, 0x98d824620088ca82, 0x280ab0e02892c09, 0xc00d02e]) else (if j < 7 then (cbits [0x3831406002032040, 0xf98d83c6200e8ca8, 0x1c10b0e04092c0, 0x8ca0460408c80a03, 0x334890ca02233412, 0x8f0d0038]) else (cbits [0x220341280a22601c, 0xa8cd0283288f8100, 0x601d150022423408, 0x81045a0359580a45, 0x6361818805e31496, 0x9824b062]))) else (if j < 9 then (cbits [0x64f441930e262942, 0x7010258028160102, 0xa0409a00d0680281, 0xd06e01c9a81306, 0x31c1d0130720401c, 0x1f0c9078]) else (if j < 10 then (cbits [0x8001c1e8c707a318, 0x18130840342080a0, 0x4334248c788a04e2, 0x18d0a034e268cf09, 0x94e2c24f0ae63529, 0x2db138b4]) else (cbits [0x8e328a301008c028, 0x3010890940a39900, 0xc31c2624c0966422, 0x1009e634260cd09, 0x324238108a2328a3, 0x298cd89e]))))) else (if j < 16 then (if j < 13 then (if j < 12 then (cbits [0xac6422a1890a2342, 0xca500a86342a98d0, 0x6328a38100aa6282, 0x20900402b18a09, 0x36ae80a8ba01e01, 0xaf0108bc]) else (cbits [0xc263630188006314, 0x130e2c2942b024b0, 0xe0282f8ca2c4f443, 0x20ca628178c60b, 0x1a3380647801102, 0x2480dcd6])) else (if j < 14 then (cbits [0xdc33e368cd8d8314, 0xb18d8ea62a3a1880, 0x29423c24b0ee6423, 0x8070f6f443d30e0f, 0x403480d0d00281e, 0x378040d4]) else (if j < 15 then (cbits [0xe063439a500e2334, 0x90ca0e00103918d0, 0xa3183e8090e63303, 0xa501006403f8ca0c, 0x312500a40a00840, 0x4380c906]) else (cbits [0x1232a440c52a0043, 0xb98d5146203b0cd5, 0xac384624b116642b, 0x711ef444731091, 0x402600d10a02842, 0x2580750c])))) else (if j < 19 then (if j < 17 then (cbits [0x3304880f2a2035, 0xa00d926019010021, 0x31a130c640c3144, 0x18daf062a3018806, 0x9424aa4b31464244, 0x4bb0e12c]) else (if j < 18 then (cbits [0xd86284d006130f44, 0xf8c70ea3344e0c70, 0x200e1380340e0084, 0x8c52b40432900a46, 0x32a408c96f231e30, 0x508cd912]) else (cbits [0x44625cb188316342, 0x4a5094e92c529909, 0x601d55bd1154c385, 0x1902e6328518070a, 0x1db90c72e001052, 0xab00d4ac]))) else (if j < 20 then (cbits [0x4c6345400614c634, 0xb0d00da31c2b80d5, 0xc328578c715c01c3, 0x3131626405818d0d, 0x31cd1a500de010d1, 0xd22500e2]) else (if j < 21 then (cbits [0x68019010020ee34c, 0x40c64103145b0095, 0x462a3118806431a1, 0xa4b31e642bd98d8f, 0xf44d5b10b30c384b, 0x5a80d16e]) else (cbits [0x186405d809172018, 0x418d17402853a501, 0xe6345f0cd17a0345, 0x8104b6035dfa4d17, 0x9405498d11c34cad, 0x352])))))) 22 (i % 16)
def s38Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 6 then (if j < 3 then (if j < 1 then (cbits [0x20080100203f00, 0x866c0431e0218a01, 0x2c380231b0118800, 0xb18e058c60280120, 0x700203801a023340, 0xe0]) else (if j < 2 then (cbits [0x1880406542031410, 0x98702092c1031b08, 0xe034170140b80743, 0xc01a070078380802, 0xe188070654383141, 0x31b0]) else (cbits [0x80d4398703892c1c, 0x86504a0360e02011, 0x2c380e31b0718803, 0xc00e950020a801c0, 0x50100b806a540402, 0x18a1]))) else (if j < 4 then (cbits [0xb0e0a8c6c546202a, 0x4080680283400780, 0xe0343700e1b806c0, 0xc00f808130dc0806, 0x8c90f06307a31c3, 0x198]) else (if j < 5 then (cbits [0xd1000508001c40, 0x809c8a0370102620, 0xa940461942300a11, 0xb321258cd11463c8, 0x70c71386788a9304, 0x31a2]) else (cbits [0x98d114650a234e45, 0xcc68aa6245319b29, 0x293c4531aa299094, 0x162722a53915280b, 0xf80d97403cba3140, 0x1942])))) else (if j < 9 then (if j < 7 then (cbits [0xb0e174c6cba6205d, 0x4c50ca31b0118a80, 0x286800cb38c780, 0x700d338101a0068d, 0x78cf99c66cce3146, 0x83]) else (if j < 8 then (cbits [0x98d1c8668de63470, 0xcc54ce620674a037, 0xe92c673213398d99, 0x17a233b0e19d284c, 0xf8ccc04048fa31f0, 0x1943]) else (cbits [0x8cd805280fe6407f, 0x510801c84018c1, 0x6314830194181021, 0x33214198820c6550, 0x1b10a0d8710692c8, 0x7a24]))) else (if j < 11 then (if j < 10 then (cbits [0x9880040792233701, 0xd259260369300cc9, 0x2f449361c49a50a4, 0xc31380806268c420, 0xf98cc04c560231c9, 0x18e4]) else (cbits [0x98968466d4263601, 0x8c8542640a300e51, 0x2018a84965098d29, 0x17a250b0e2852854, 0x70072b8c7e026370, 0x18e5])) else (if j < 12 then (cbits [0x990c04c815c634ae, 0x696a019b461c00, 0x2c39017a25a0096d, 0x10125c80a2e80317, 0xe8cd2f40697ac3f0, 0x31a5]) else 0xc4301)))) 21 (i % 16)
def s38Links := pageLinks s38Index s38Codes 6 13 8 7
def s38Data (i : Nat) : Nat × Nat :=
  let e := s38Forest i
  (e &&& 255, e >>> 8)
def s38Sample : Nat × Nat := (s38Blob257665, 96)
def s38Tags := dagTraceTags s38Mask 96 (dagTagBases s38StockWords s38Blob258238 s38Blob258452 96) 8 s38Data
def s38States := dagTrace s38Mask s38StockWords 8 s38Data
def s38MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm9, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 5, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 5, 4] 0 i.val)))]
def s38Moves := dagMoves s38MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s38Autos : DagMovesOK s38Mask s38Goal 64 s38Moves := dagMovesOfCheck (by decide +kernel)
def s38Check := dagCheckNode s38Mask s38Goal s38Chart (dagKnownCloses s38Goal s38Cuts) 193 s38States s38Moves s38Links s38Sample s38Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s38Roots : dagCheckRoots s38Mask s38Goal s38Chart (dagKnownCloses s38Goal s38Cuts) s38Witnesses (dagRef 193 s38States s38Moves s38Links 0) s38StockWords 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s38Block0 : treeBlock 0 24 s38Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s38Block24 : treeBlock 24 24 s38Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s38Block48 : treeBlock 48 24 s38Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s38Block72 : treeBlock 72 24 s38Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s38Block96 : treeBlock 96 24 s38Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s38Block120 : treeBlock 120 24 s38Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s38Block144 : treeBlock 144 24 s38Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s38Block168 : treeBlock 168 24 s38Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s38Block192 : treeBlock 192 1 s38Check = true := by decide +kernel
theorem s38Group0_48 : treeBlock 0 48 s38Check = true := treeBlock_merge (start := 0) (left := 24) (right := 24) (check := s38Check) s38Block0 s38Block24
theorem s38Group48_48 : treeBlock 48 48 s38Check = true := treeBlock_merge (start := 48) (left := 24) (right := 24) (check := s38Check) s38Block48 s38Block72
theorem s38Group0_96 : treeBlock 0 96 s38Check = true := treeBlock_merge (start := 0) (left := 48) (right := 48) (check := s38Check) s38Group0_48 s38Group48_48
theorem s38Group96_48 : treeBlock 96 48 s38Check = true := treeBlock_merge (start := 96) (left := 24) (right := 24) (check := s38Check) s38Block96 s38Block120
theorem s38Group168_25 : treeBlock 168 25 s38Check = true := treeBlock_merge (start := 168) (left := 24) (right := 1) (check := s38Check) s38Block168 s38Block192
theorem s38Group144_49 : treeBlock 144 49 s38Check = true := treeBlock_merge (start := 144) (left := 24) (right := 25) (check := s38Check) s38Block144 s38Group168_25
theorem s38Group96_97 : treeBlock 96 97 s38Check = true := treeBlock_merge (start := 96) (left := 48) (right := 49) (check := s38Check) s38Group96_48 s38Group144_49
theorem s38Group0_193 : treeBlock 0 193 s38Check = true := treeBlock_merge (start := 0) (left := 96) (right := 97) (check := s38Check) s38Group0_96 s38Group96_97
theorem s38Blocks : treeBlock 0 193 s38Check = true := s38Group0_193
theorem s38Known : Known s38Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s38Stock : Lower s38Mask s38StockWords s38Goal 9 := by
  apply lowerDag _ _ _ _ s38Autos _ _ _ s38Known _ s38Roots s38Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s38Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def s39Mask : Nat := 0xf0f0f0f0ffffffff
abbrev s39Goal : Nat := sGoal &&& s39Mask
abbrev s39StockWords : List Nat := [0xa0a0a0a0aaaaaaaa, 0xc0c0c0c0cccccccc, 0xf0f0f0f0f0f0f0f0, 0xf000f000ff00ff00, 0xf0f00000ffff0000, 0xf0f0f0f000000000]
def s39Fact : Nat × List Nat × Nat × Nat := (s39Mask, s39StockWords, 9, s39Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s39Stock : Lower s39Mask s39StockWords s39Goal 9 := dagShiftLower (width := 64) pm7 s28Stock (by decide +kernel)
def s40Mask : Nat := 0xf0f0fffff0f0ffff
abbrev s40Goal : Nat := sGoal &&& s40Mask
abbrev s40StockWords : List Nat := [0xa0a0aaaaa0a0aaaa, 0xc0c0ccccc0c0cccc, 0xf0f0f0f0f0f0f0f0, 0xf000ff00f000ff00, 0xf0f00000f0f00000, 0xf0f0ffff00000000]
def s40Fact : Nat × List Nat × Nat × Nat := (s40Mask, s40StockWords, 9, s40Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s40Stock : Lower s40Mask s40StockWords s40Goal 9 := dagShiftLower (width := 64) pm10 s35Stock (by decide +kernel)
def s41Mask : Nat := 0xf0fff0fff0fff0ff
abbrev s41Goal : Nat := sGoal &&& s41Mask
abbrev s41StockWords : List Nat := [0xa0aaa0aaa0aaa0aa, 0xc0ccc0ccc0ccc0cc, 0xf0f0f0f0f0f0f0f0, 0xf000f000f000f000, 0xf0ff0000f0ff0000, 0xf0fff0ff00000000]
def s41Fact : Nat × List Nat × Nat × Nat := (s41Mask, s41StockWords, 9, s41Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s41Stock : Lower s41Mask s41StockWords s41Goal 9 := dagShiftLower (width := 64) pm8 s28Stock (by decide +kernel)
def pm16 : List (List (Nat × Nat) × List (Nat × Nat)) := [st15, st24]
def s42Mask : Nat := 0xf3f3f3f3f3f3f3f3
abbrev s42Goal : Nat := sGoal &&& s42Mask
abbrev s42StockWords : List Nat := [0xa2a2a2a2a2a2a2a2, 0xc0c0c0c0c0c0c0c0, 0xf0f0f0f0f0f0f0f0, 0xf300f300f300f300, 0xf3f30000f3f30000, 0xf3f3f3f300000000]
def s42Fact : Nat × List Nat × Nat × Nat := (s42Mask, s42StockWords, 9, s42Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s42Stock : Lower s42Mask s42StockWords s42Goal 9 := dagShiftLower (width := 64) pm16 s35Stock (by decide +kernel)
def s43Mask : Nat := 0xfafafafafafafafa
abbrev s43Goal : Nat := sGoal &&& s43Mask
abbrev s43StockWords : List Nat := [0xaaaaaaaaaaaaaaaa, 0xc8c8c8c8c8c8c8c8, 0xf0f0f0f0f0f0f0f0, 0xfa00fa00fa00fa00, 0xfafa0000fafa0000, 0xfafafafa00000000]
def s43Fact : Nat × List Nat × Nat × Nat := (s43Mask, s43StockWords, 9, s43Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s43Stock : Lower s43Mask s43StockWords s43Goal 9 := dagShiftLower (width := 64) pm7 s38Stock (by decide +kernel)
def s44Mask : Nat := 0xff00ff00ffffffff
abbrev s44Goal : Nat := sGoal &&& s44Mask
abbrev s44StockWords : List Nat := [0xaa00aa00aaaaaaaa, 0xcc00cc00cccccccc, 0xf000f000f0f0f0f0, 0xff00ff00ff00ff00, 0xff000000ffff0000, 0xff00ff0000000000]
def s44Fact : Nat × List Nat × Nat × Nat := (s44Mask, s44StockWords, 9, s44Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s44Stock : Lower s44Mask s44StockWords s44Goal 9 := dagShiftLower (width := 64) pm7 s35Stock (by decide +kernel)
def s45Mask : Nat := 0xff00ffffff00ffff
abbrev s45Goal : Nat := sGoal &&& s45Mask
abbrev s45StockWords : List Nat := [0xaa00aaaaaa00aaaa, 0xcc00cccccc00cccc, 0xf000f0f0f000f0f0, 0xff00ff00ff00ff00, 0xff000000ff000000, 0xff00ffff00000000]
def s45Fact : Nat × List Nat × Nat × Nat := (s45Mask, s45StockWords, 9, s45Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s45Stock : Lower s45Mask s45StockWords s45Goal 9 := dagShiftLower (width := 64) pm10 s28Stock (by decide +kernel)
def s46Mask : Nat := 0xff0fff0fff0fff0f
abbrev s46Goal : Nat := sGoal &&& s46Mask
abbrev s46StockWords : List Nat := [0xaa0aaa0aaa0aaa0a, 0xcc0ccc0ccc0ccc0c, 0xf000f000f000f000, 0xff00ff00ff00ff00, 0xff0f0000ff0f0000, 0xff0fff0f00000000]
def s46Fact : Nat × List Nat × Nat × Nat := (s46Mask, s46StockWords, 9, s46Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s46Stock : Lower s46Mask s46StockWords s46Goal 9 := dagShiftLower (width := 64) pm2 s28Stock (by decide +kernel)
def s47Mask : Nat := 0xff33ff33ff33ff33
abbrev s47Goal : Nat := sGoal &&& s47Mask
abbrev s47StockWords : List Nat := [0xaa22aa22aa22aa22, 0xcc00cc00cc00cc00, 0xf030f030f030f030, 0xff00ff00ff00ff00, 0xff330000ff330000, 0xff33ff3300000000]
def s47Fact : Nat × List Nat × Nat × Nat := (s47Mask, s47StockWords, 9, s47Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s47Stock : Lower s47Mask s47StockWords s47Goal 9 := dagShiftLower (width := 64) pm3 s35Stock (by decide +kernel)
def s48Mask : Nat := 0xffaaffaaffaaffaa
abbrev s48Goal : Nat := sGoal &&& s48Mask
abbrev s48StockWords : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcc88cc88cc88cc88, 0xf0a0f0a0f0a0f0a0, 0xff00ff00ff00ff00, 0xffaa0000ffaa0000, 0xffaaffaa00000000]
def s48Fact : Nat × List Nat × Nat × Nat := (s48Mask, s48StockWords, 9, s48Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s48Stock : Lower s48Mask s48StockWords s48Goal 9 := dagShiftLower (width := 64) pm10 s38Stock (by decide +kernel)
def s49Mask : Nat := 0xffff00ffffff00ff
abbrev s49Goal : Nat := sGoal &&& s49Mask
abbrev s49StockWords : List Nat := [0xaaaa00aaaaaa00aa, 0xcccc00cccccc00cc, 0xf0f000f0f0f000f0, 0xff000000ff000000, 0xffff0000ffff0000, 0xffff00ff00000000]
def s49Fact : Nat × List Nat × Nat × Nat := (s49Mask, s49StockWords, 9, s49Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s49Stock : Lower s49Mask s49StockWords s49Goal 9 := dagShiftLower (width := 64) pm11 s28Stock (by decide +kernel)
def s50Mask : Nat := 0xffff0f0fffff0f0f
abbrev s50Goal : Nat := sGoal &&& s50Mask
abbrev s50StockWords : List Nat := [0xaaaa0a0aaaaa0a0a, 0xcccc0c0ccccc0c0c, 0xf0f00000f0f00000, 0xff000f00ff000f00, 0xffff0000ffff0000, 0xffff0f0f00000000]
def s50Fact : Nat × List Nat × Nat × Nat := (s50Mask, s50StockWords, 9, s50Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s50Stock : Lower s50Mask s50StockWords s50Goal 9 := dagShiftLower (width := 64) pm2 s35Stock (by decide +kernel)
def s51Mask : Nat := 0xffff3333ffff3333
abbrev s51Goal : Nat := sGoal &&& s51Mask
abbrev s51StockWords : List Nat := [0xaaaa2222aaaa2222, 0xcccc0000cccc0000, 0xf0f03030f0f03030, 0xff003300ff003300, 0xffff0000ffff0000, 0xffff333300000000]
def s51Fact : Nat × List Nat × Nat × Nat := (s51Mask, s51StockWords, 9, s51Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s51Stock : Lower s51Mask s51StockWords s51Goal 9 := dagShiftLower (width := 64) pm3 s28Stock (by decide +kernel)
def s52Mask : Nat := 0xffffaaaaffffaaaa
abbrev s52Goal : Nat := sGoal &&& s52Mask
abbrev s52StockWords : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcccc8888cccc8888, 0xf0f0a0a0f0f0a0a0, 0xff00aa00ff00aa00, 0xffff0000ffff0000, 0xffffaaaa00000000]
def s52Fact : Nat × List Nat × Nat × Nat := (s52Mask, s52StockWords, 9, s52Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s52Stock : Lower s52Mask s52StockWords s52Goal 9 := dagShiftLower (width := 64) pm11 s38Stock (by decide +kernel)
def s53Mask : Nat := 0xffffffff0000ffff
abbrev s53Goal : Nat := sGoal &&& s53Mask
abbrev s53StockWords : List Nat := [0xaaaaaaaa0000aaaa, 0xcccccccc0000cccc, 0xf0f0f0f00000f0f0, 0xff00ff000000ff00, 0xffff000000000000, 0xffffffff00000000]
def s53Fact : Nat × List Nat × Nat × Nat := (s53Mask, s53StockWords, 9, s53Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s53Stock : Lower s53Mask s53StockWords s53Goal 9 := dagShiftLower (width := 64) pm9 s35Stock (by decide +kernel)
def s54Mask : Nat := 0xffffffff00ff00ff
abbrev s54Goal : Nat := sGoal &&& s54Mask
abbrev s54StockWords : List Nat := [0xaaaaaaaa00aa00aa, 0xcccccccc00cc00cc, 0xf0f0f0f000f000f0, 0xff00ff0000000000, 0xffff000000ff0000, 0xffffffff00000000]
def s54Fact : Nat × List Nat × Nat × Nat := (s54Mask, s54StockWords, 9, s54Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s54Stock : Lower s54Mask s54StockWords s54Goal 9 := dagShiftLower (width := 64) pm8 s35Stock (by decide +kernel)
def s55Mask : Nat := 0xffffffff0f0f0f0f
abbrev s55Goal : Nat := sGoal &&& s55Mask
abbrev s55StockWords : List Nat := [0xaaaaaaaa0a0a0a0a, 0xcccccccc0c0c0c0c, 0xf0f0f0f000000000, 0xff00ff000f000f00, 0xffff00000f0f0000, 0xffffffff00000000]
def s55Fact : Nat × List Nat × Nat × Nat := (s55Mask, s55StockWords, 9, s55Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s55Stock : Lower s55Mask s55StockWords s55Goal 9 := dagShiftLower (width := 64) pm12 s28Stock (by decide +kernel)
def s56Mask : Nat := 0xffffffff33333333
abbrev s56Goal : Nat := sGoal &&& s56Mask
abbrev s56StockWords : List Nat := [0xaaaaaaaa22222222, 0xcccccccc00000000, 0xf0f0f0f030303030, 0xff00ff0033003300, 0xffff000033330000, 0xffffffff00000000]
def s56Fact : Nat × List Nat × Nat × Nat := (s56Mask, s56StockWords, 9, s56Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s56Stock : Lower s56Mask s56StockWords s56Goal 9 := dagShiftLower (width := 64) pm16 s28Stock (by decide +kernel)
def s57Mask : Nat := 0xffffffffaaaaaaaa
abbrev s57Goal : Nat := sGoal &&& s57Mask
abbrev s57StockWords : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcccccccc88888888, 0xf0f0f0f0a0a0a0a0, 0xff00ff00aa00aa00, 0xffff0000aaaa0000, 0xffffffff00000000]
def s57Fact : Nat × List Nat × Nat × Nat := (s57Mask, s57StockWords, 9, s57Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s57Stock : Lower s57Mask s57StockWords s57Goal 9 := dagShiftLower (width := 64) pm12 s38Stock (by decide +kernel)
def s58Mask : Nat := 0xcc33cc33cc33cc33
abbrev s58Goal : Nat := sGoal &&& s58Mask
abbrev s58StockWords : List Nat := [0x8822882288228822, 0xcc00cc00cc00cc00, 0xc030c030c030c030, 0xcc330000cc330000, 0xcc33cc3300000000]
def s58Fact : Nat × List Nat × Nat × Nat := (s58Mask, s58StockWords, 8, s58Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s58Stock : Lower s58Mask s58StockWords s58Goal 8 := dagShiftLower (width := 64) pm9 s33Stock (by decide +kernel)
def s59Mask : Nat := 0xcccc3333cccc3333
abbrev s59Goal : Nat := sGoal &&& s59Mask
abbrev s59StockWords : List Nat := [0x8888222288882222, 0xcccc0000cccc0000, 0xc0c03030c0c03030, 0xcc003300cc003300, 0xcccc333300000000]
def s59Fact : Nat × List Nat × Nat × Nat := (s59Mask, s59StockWords, 8, s59Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s59Stock : Lower s59Mask s59StockWords s59Goal 8 := dagShiftLower (width := 64) pm7 s26Stock (by decide +kernel)
def s60Mask : Nat := 0xf0f00f0ff0f00f0f
abbrev s60Goal : Nat := sGoal &&& s60Mask
abbrev s60StockWords : List Nat := [0xa0a00a0aa0a00a0a, 0xc0c00c0cc0c00c0c, 0xf0f00000f0f00000, 0xf0000f00f0000f00, 0xf0f00f0f00000000]
def s60Fact : Nat × List Nat × Nat × Nat := (s60Mask, s60StockWords, 8, s60Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s60Stock : Lower s60Mask s60StockWords s60Goal 8 := dagShiftLower (width := 64) pm8 s33Stock (by decide +kernel)
def s61Mask : Nat := 0xffff0000ffff
abbrev s61Goal : Nat := sGoal &&& s61Mask
abbrev s61StockWords : List Nat := [0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000]
def s61Fact : Nat × List Nat × Nat × Nat := (s61Mask, s61StockWords, 7, s61Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s61Stock : Lower s61Mask s61StockWords s61Goal 7 := dagShiftLower (width := 64) pm9 s1Stock (by decide +kernel)
def s62Mask : Nat := 0xff00ff00ff00ff
abbrev s62Goal : Nat := sGoal &&& s62Mask
abbrev s62StockWords : List Nat := [0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xf000f000f000f0, 0xff000000ff0000, 0xff00ff00000000]
def s62Fact : Nat × List Nat × Nat × Nat := (s62Mask, s62StockWords, 7, s62Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s62Stock : Lower s62Mask s62StockWords s62Goal 7 := dagShiftLower (width := 64) pm8 s1Stock (by decide +kernel)
def s63Mask : Nat := 0xff000000ff
abbrev s63Goal : Nat := sGoal &&& s63Mask
abbrev s63StockWords : List Nat := [0xaa000000aa, 0xcc000000cc, 0xf0000000f0, 0xff00000000]
def s63Fact : Nat × List Nat × Nat × Nat := (s63Mask, s63StockWords, 6, s63Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s63Stock : Lower s63Mask s63StockWords s63Goal 6 := dagShiftLower (width := 64) pm9 s0Stock (by decide +kernel)
def s64Mask : Nat := 0xcc330000cc33
abbrev s64Goal : Nat := sGoal &&& s64Mask
abbrev s64StockWords : List Nat := [0x882200008822, 0xcc000000cc00, 0xc0300000c030, 0xcc3300000000]
def s64Fact : Nat × List Nat × Nat × Nat := (s64Mask, s64StockWords, 6, s64Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s64Stock : Lower s64Mask s64StockWords s64Goal 6 := dagShiftLower (width := 64) pm9 s30Stock (by decide +kernel)
def s65Mask : Nat := 0xf0000f00f0000f
abbrev s65Goal : Nat := sGoal &&& s65Mask
abbrev s65StockWords : List Nat := [0xa0000a00a0000a, 0xc0000c00c0000c, 0xf0000000f00000, 0xf0000f00000000]
def s65Fact : Nat × List Nat × Nat × Nat := (s65Mask, s65StockWords, 6, s65Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s65Stock : Lower s65Mask s65StockWords s65Goal 6 := dagShiftLower (width := 64) pm8 s30Stock (by decide +kernel)
def pm17 : List (List (Nat × Nat) × List (Nat × Nat)) := [st25]
def s66Mask : Nat := 0xc030c030c030c03
abbrev s66Goal : Nat := sGoal &&& s66Mask
abbrev s66StockWords : List Nat := [0x802080208020802, 0xc000c000c000c00, 0xc0300000c030000, 0xc030c0300000000]
def s66Fact : Nat × List Nat × Nat × Nat := (s66Mask, s66StockWords, 5, s66Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s66Stock : Lower s66Mask s66StockWords s66Goal 5 := dagShiftLower (width := 64) pm17 s18Stock (by decide +kernel)
def pm18 : List (List (Nat × Nat) × List (Nat × Nat)) := [st25, st23]
def s67Mask : Nat := 0xc0c0c0c03030303
abbrev s67Goal : Nat := sGoal &&& s67Mask
abbrev s67StockWords : List Nat := [0x808080802020202, 0xc0c0c0c00000000, 0xc000c0003000300, 0xc0c000003030000]
def s67Fact : Nat × List Nat × Nat × Nat := (s67Mask, s67StockWords, 5, s67Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s67Stock : Lower s67Mask s67StockWords s67Goal 5 := dagShiftLower (width := 64) pm18 s18Stock (by decide +kernel)
def s68Blob374505 : Nat := (cbits [0x1402050100c0203, 0xc1009008240c0702, 0x2110703c180d0502, 0x70a0542413080440, 0x9068141a0c0642c1, 0x70281c06070301a0, 0x2210b0781c1e0c0, 0x2612094442310084, 0x140a44826110980c, 0xb0482c060b0542b, 0x86031150b81c2e14, 0x835180c84432090c, 0xa1c0e468360b0d86, 0xc0f0683c1c0e8543, 0xc14030300c00031, 0xc05000144403090, 0x712014280506014, 0x701c08070101c02, 0x241409000242c07, 0xc020b14024300906, 0x40b0702c100b0102, 0xd04034080d008345, 0x603c140f0303c1c0, 0x4428110904400110, 0x4130084c60110c0, 0x15008542c130804c, 0x1a0542c150805408])
def s68Blob375072 : Nat := (cbits [0xfffc24418f00ffff, 0x74c75293ffffffff, 0x78387c1f07cdbb1, 0xff831c3e78f8631c, 0x80ff83e0f803f801, 0x3fffe0003e03f, 0x3ffc000fffc00, 0xff000000fffc0000, 0x3ffff])
def s68Blob375270 : Nat := (cbits [0x1000000001000425, 0x34c3529208800840, 0x4509c685a17849b1, 0xcf091c1658d86318, 0x806d83c0d412d209, 0x23673c8212e03b, 0x423bec000b6f800, 0xee000000e6780011, 0x804004200843f76d])
def s68Mask : Nat := 0xffffffffffffffff
abbrev s68Goal : Nat := sGoal &&& s68Mask
abbrev s68StockWords : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
def s68Fact : Nat × List Nat × Nat × Nat := (s68Mask, s68StockWords, 12, s68Goal)
def s68Cuts : List (Nat × List Nat × Nat × Nat) := [s8Fact, s9Fact, s10Fact, s11Fact, s7Fact, s13Fact, s14Fact, s15Fact, s16Fact, s17Fact, s28Fact, s29Fact, s36Fact, s37Fact, s38Fact, s39Fact, s40Fact, s41Fact, s42Fact, s43Fact, s44Fact, s45Fact, s46Fact, s47Fact, s48Fact, s35Fact, s49Fact, s50Fact, s51Fact, s52Fact, s53Fact, s54Fact, s55Fact, s56Fact, s57Fact, s33Fact, s58Fact, s59Fact, s27Fact, s60Fact, s34Fact, s1Fact, s61Fact, s62Fact, s2Fact, s3Fact, s12Fact, s0Fact, s4Fact, s63Fact, s5Fact, s64Fact, s6Fact, s65Fact, s66Fact, s67Fact]
def s68Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[3, 5, 9, 17, 26, 28, 33, 38, 44, 50, 3, 5, 1, 14, 22, 42, 52, 56, 1, 14, 22, 42, 52, 56], rfl⟩
def s68Witnesses := unpackWitnesses s68StockWords [1538, 263681, 526849, 791041, 1057281, 1327617]
def s68Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 78 then (if j < 39 then (if j < 19 then (if j < 9 then (if j < 4 then (if j < 2 then (if j < 1 then (cbits [0xb202190003000001, 0x62000c4001784022, 0x40c6001881031000, 0x8f81900032000630, 0x4380083100c]) else (cbits [0x920010e5821c0, 0x9200124002480049, 0x124002480049000, 0x4002480049000920, 0x49800920412])) else (if j < 3 then (cbits [0x80099001320024c6, 0x9b0013210264004c, 0x13e0026c404d800, 0x6002ac00558009f3, 0x55800ab0015]) else (cbits [0x800ab00156002ac0, 0xb100156302ac0055, 0x4162002c40058800, 0xc002f8005f000b13, 0x5f040be0017]))) else (if j < 6 then (if j < 5 then (cbits [0x40c200184003002, 0xca24190103104061, 0x1aac834c2069800, 0x4003c80079000ee1, 0x79800f2041e]) else (cbits [0xa0f4001e8003cc1, 0xf9001f2003e4007a, 0x41f4003e4107c800, 0x6103ec007d800fa0, 0x7e800fd001f])) else (if j < 7 then (cbits [0xa0fe001fc003f41, 0x3042060040c007f, 0x20c004102082001, 0xc004a84083481060, 0x971812e0025]) else (if j < 8 then (cbits [0x13a00274004e80, 0x3a24274004e8009d, 0x2860050c00a1801, 0x60050c00a1801430, 0xa1881430028]) else (cbits [0x8e1470028e0051c0, 0x4e0c29c0053800a3, 0x2a20054400a8801, 0x60054810a8821510, 0xab80153102a]))))) else (if j < 14 then (if j < 11 then (if j < 10 then (cbits [0x44158002ae0855c0, 0x7c002f4105e800ac, 0x2fa005f010be001, 0xe005f420be8017d0, 0xc60017f342f]) else (cbits [0x8018d0031a006301, 0x8e0031c0063410c6, 0x831c7063800c7001, 0xe0067810cf0019c0, 0xcf8019f0033])) else (if j < 12 then (cbits [0x19f3433e0067c0, 0xac00358006b000d6, 0x378006b100d6001, 0xa006f400de021bc0, 0xde801bd0037]) else (if j < 13 then (cbits [0x901bd0037a006f40, 0xc90038a2071400de, 0x3926872400e4801, 0xc0075800eb001d60, 0xeb341d6003a]) else (cbits [0x1f73c3ee007c07, 0x60040c008180103, 0x450088a00103442, 0xa008d4011a802293, 0x11a802350046])))) else (if j < 16 then (if j < 15 then (cbits [0x8a2350046a008d40, 0x3c00478008e8211a, 0x8484008f0611e002, 0xa009101122002420, 0x123062450448]) else (cbits [0x24a08492089240, 0x910050c58933a126, 0x452400a441148802, 0x610a8c0149a02920, 0x153002a50454])) else (if j < 17 then (cbits [0x802a80454c10a980, 0xaa0055400aa41154, 0x56428aac7155022, 0xadc115b802b70, 0x15c842b80457]) else (if j < 18 then (cbits [0x802bc0457800aec1, 0xcb0059600af4e15e, 0x859e00b2c4165802, 0xa00b44c168802cf0, 0x16e802dd005b]) else (cbits [0x822e3005bc28b741, 0xf0005c860b900171, 0x5e230bc01178002, 0x208bdc217b802f70, 0x181022fa205f])))))) else (if j < 29 then (if j < 24 then (if j < 21 then (if j < 20 then (cbits [0x843250064808c0e1, 0x3a0064e98c9c0192, 0x68000ce8619d003, 0x478d0801a0043400, 0x1a8803510068]) else (cbits [0x8c351006a200d440, 0x5bb06b210d5c21a8, 0x471408e2801c3863, 0x808e3001c60038b0, 0x1c68638d0071])) else (if j < 22 then (cbits [0x803d30077ab0e42d, 0xd4087a800f4c11e9, 0x47ae00f5811eb003, 0x10f6001ec003d70, 0x1ed803da047b]) else (if j < 23 then (cbits [0x3f4107b6c8f6c0, 0xf8007f000fe001fc, 0x47f200fe401fc023, 0xc00ff801ff003f91, 0x1ff023fe007f]) else (cbits [0x400007fe08ffc0, 0x200804010002200, 0x808010100201044, 0x20102402020a4040, 0x205004090481])))) else (if j < 26 then (if j < 25 then (cbits [0x4a40c00818010282, 0x370086e010c46206, 0x86e590dc021b804, 0x6011081221004420, 0x221804430088]) else (cbits [0x80443008860110c0, 0x43088860110c0221, 0x88a491140222804, 0xc0113802270044e0, 0x2270044e0089])) else (if j < 27 then (cbits [0x864510089e111381, 0x54008a8011500228, 0x8bc01178022a144, 0xc11178022f0045e0, 0x23002460008b]) else (if j < 28 then (cbits [0x804620c8c2091840, 0x68048d0011943232, 0x8ea091a8b234824, 0xc111d8023b004760, 0x23c08478008e]) else (cbits [0x48d0c8f8891f00, 0x9400920212400248, 0x492809250024a004, 0x20125c224b024950, 0x24cdc4990093]))))) else (if j < 34 then (if j < 31 then (if j < 30 then (cbits [0x804cf0098e4131c0, 0xcf0899e0133c0267, 0x9a2113440268804, 0x8193500269824d30, 0x26b824d7009a]) else (cbits [0x4d9349b2013601, 0xe9089cc193980273, 0xc9d6113ac0275804, 0x4013c02278004ed0, 0x279044f2009e])) else (if j < 32 then (cbits [0x5010c9fe113d0b, 0x1f0ca3e01411b282, 0xa48014882291005, 0x6414966292025240, 0x2a98055300a9]) else (if j < 33 then (cbits [0x5530caa60154c0, 0x5900aac1955802ab, 0xaba1956442ac805, 0x61158422b0025600, 0x2b28856500ac]) else (cbits [0x8856b00ad2115a40, 0x8d04adef15bc02b5, 0xb3401638c2c7005, 0x60966c02cd0259a0, 0x2ce2659c00b3])))) else (if j < 36 then (if j < 35 then (cbits [0x805af08b5e016bc0, 0xb108b62016c402d8, 0x8b6c096d802d9865, 0x40176802dcc25b70, 0x2ed025da00bb]) else (cbits [0x45dc00bb60976c0, 0x190cc0aa177a72ee, 0x4c3a09874030e026, 0x20987ca30f8061e0, 0x3150062a00c5])) else (if j < 37 then (cbits [0x8062b00c54098a80, 0x2e00c56198ac0315, 0x4c62018c40317066, 0x8118d00319046310, 0x31bb263604c6]) else (if j < 38 then (cbits [0x65400ca0219400, 0x5418ca801950032a, 0xcb601968132d006, 0xa01994032d9465b0, 0x3328066500cc]) else (cbits [0x8066900cd2019944, 0x6c0ccd6099a42334, 0x8ce0219bc1337806, 0xa019d9733b006740, 0x3480068d0cd1]))))))) else (if j < 58 then (if j < 48 then (if j < 43 then (if j < 41 then (if j < 40 then (cbits [0x69600d2c01a406, 0x9608d2c01a58034b, 0xd3001a60034c006, 0x201a64034c026980, 0x34f0069914d3]) else (cbits [0x269f1cd3e01a781, 0xa700d4e01a9c0353, 0x4db401b38c353ce6, 0x801b6c136d806da0, 0x36f006dc08db])) else (if j < 42 then (cbits [0x46e000dc001b782, 0xe200dc401b880370, 0xdc401b880371006, 0xc09b980373006e21, 0x378806e728dc]) else (cbits [0x806f100de201bc40, 0xf100de201bc40378, 0x4de401bc41378806, 0xe01bfc037f806f23, 0x37f846ff00df]))) else (if j < 45 then (if j < 44 then (cbits [0x70104e0201c040, 0x300e0409c080381, 0xe0a01c0c2381807, 0xa01c3c6382947050, 0x38a8071500e2]) else (cbits [0x8e71500e2a01c540, 0x1c00e3801c70038a, 0xe3a01c74038e027, 0x219c7c238e8471d0, 0x3928272404e4])) else (if j < 46 then (cbits [0x272800e5001c982, 0x3400e5259ca40394, 0xe6801cd0039a007, 0xa09cd0139a007340, 0x39b1673600e6]) else (if j < 47 then (cbits [0x8074100e8201d040, 0x4308e8601d0423a0, 0xe8c61d1803a2827, 0x401d4803a9007520, 0x3a90075200ea]) else (cbits [0x8275500ea419d480, 0x572ceae01d5813aa, 0xec401d8803b1007, 0x801d8823b1007620, 0x3b88076434ec]))))) else (if j < 53 then (if j < 50 then (if j < 49 then (cbits [0x8677100ee201dc40, 0x7414ee801dd003b8, 0x4ef401de803bc827, 0x811df083bd8277a0, 0x3c30078600f0]) else (cbits [0x79400f1061e182, 0x9700f2819e5003ca, 0xcf3c01e7803cb8e7, 0x601ea423d48079e2, 0x3df8a7ab50f5])) else (if j < 51 then (cbits [0x7c400f8801f100, 0xc500f8809f1003e2, 0x4f8e01f1813e2827, 0x409f2803e4047c70, 0x3e5807cb00f9]) else (if j < 52 then (cbits [0x807cb00f9601f2c0, 0xcd04f9809f2c13e5, 0xfb221f6403e7167, 0xa01f7403ee807dd0, 0x3f0807dd10fb]) else (cbits [0x47e104fc201f840, 0xe674fc811f9003f1, 0x1018020300401927, 0x80203004060080c0, 0x4068280c0501])))) else (if j < 55 then (if j < 54 then (cbits [0x8080f0901c0a0380, 0x1301026020442408, 0x102c020580409868, 0x205c940b028160, 0x410008200104]) else (cbits [0x2821050400a0800, 0x25010461208c0411, 0x9058020b004128e8, 0xc2a0b804170082c0, 0x419988330105])) else (if j < 56 then (cbits [0x8483f0107e020fc0, 0x412508202104041f, 0x50966a1281425008, 0x60a168142c828580, 0x42e0085c010b]) else (if j < 57 then (cbits [0x9a869010cc1a170a, 0x7c010f8021d86434, 0x10f8121f0043e008, 0xe021f8143f0087e0, 0x4428087f190f]) else (cbits [0x28850d10a022140, 0xaf0515e022266444, 0x116e022c07458008, 0xe022dc045b808b70, 0x45b808b70116])))))) else (if j < 68 then (if j < 63 then (if j < 60 then (if j < 59 then (cbits [0x9a8b901172022dc2, 0xc60118c02318045c, 0x118c023180463008, 0x2023240463068c60, 0x465008c90519]) else (cbits [0x808cb09196023281, 0xcf0119e023342466, 0x11a0523400467828, 0x822370046d048da0, 0x470808e0051b])) else (if j < 61 then (cbits [0x8e30d1c40a3841, 0xf1011e00a398a473, 0x11e2123c40478808, 0xc5a3d80479868f30, 0x48080901011e]) else (if j < 62 then (cbits [0x8290359206024042, 0x1b2d23602468148c, 0x524c024980493009, 0xe0249c0493809260, 0x493849270124]) else (cbits [0x8092b092540a4a41, 0x3001260024b43496, 0x9262124c01498009, 0x45a528049aaa9330, 0x4aa809550129])))) else (if j < 65 then (if j < 64 then (cbits [0x80955012aa025540, 0x56052ac0255414aa, 0x52b20255c24ab809, 0xe0a5bc04ad2a9590, 0x4b804970012d]) else (cbits [0xb8973012e40a5c80, 0x91013220263c24b9, 0x134c0269804c8aa9, 0xa69824d3009a60, 0x4d5009a90535])) else (if j < 66 then (cbits [0x69ac01354126a80, 0xb60d368126bc54d6, 0xd37e226e854dc829, 0x80272824e3089c30, 0x4e7009cc0939]) else (if j < 67 then (cbits [0x9e2293a28a7383, 0xee053da0a7b014f6, 0x93ea127d404f78c9, 0x4128080500829f72, 0x5028aa040540]) else (cbits [0x2aa0b0d4140a8280, 0x23054460288c0507, 0xd44c02894151202a, 0xa02914852280a267, 0x52880a4d1149]))))) else (if j < 73 then (if j < 70 then (if j < 69 then (cbits [0x82a51014a2029440, 0x5b014b6029489528, 0x14b60296c052d80a, 0xc12978052d86a5b0, 0x53002a60014b]) else (cbits [0x80a6b094c2529840, 0x84014f8429b4f536, 0x150802a10054200a, 0x612a21b54400a841, 0x55280aa50154])) else (if j < 71 then (cbits [0x80ab50156a02a950, 0xb90d56e12ad4255a, 0x15bc52af2255e00a, 0x802bb0057600ae81, 0x57800aec115d]) else (if j < 72 then (cbits [0xaf2015e012bc00, 0x10395e6eabc81579, 0x163c02c78058f00b, 0xc02c78058f00b1e0, 0x58f02b1e0163]) else (cbits [0x80b1f0163e02c7c0, 0x1f2d63e02c7c058f, 0x165402ca8059500b, 0x40aca8059500b2a0, 0x59580b2b0165])))) else (if j < 75 then (if j < 74 then (cbits [0xb2d2565612cac0, 0x360166c02cd8059b, 0xd67002cdc159b02b, 0x1acfc159d88b380, 0x5a580b432168]) else (cbits [0x8b502969e0ad2c4, 0x5e016bc02d7805ad, 0x16c002d8005af04b, 0xa3ad8155b000b600, 0x5be00b7c016e])) else (if j < 76 then (cbits [0xb7c016f802df00, 0x830170602df075be, 0x170652e0c05c180b, 0xa02e3405c680b8d0, 0x5c680b8d0171]) else (if j < 77 then (cbits [0x80b950172a02e348, 0x991d73202e5445ca, 0x174002e8005d000b, 0x2e8085d000ba00, 0x5d402ba80175]) else (cbits [0x8bb20175442ea41, 0xc80d77c52ed885d9, 0x57960af2c05e580b, 0xc22f3415e680bcc0, 0x5e900bd20179])))))))) else (if j < 117 then (if j < 97 then (if j < 87 then (if j < 82 then (if j < 80 then (if j < 79 then (cbits [0x24bd4017a802f482, 0xeb017d602f9855ea, 0x17d64afac05f580b, 0x802fd005fa00bf40, 0x5fa00bf4017e]) else (cbits [0x80bfb017f602fd07, 0xd0181612fed05fd, 0x181e03034260680c, 0x60304c060788c0f0, 0x60980c130182])) else (if j < 81 then (cbits [0x80c13118260304c0, 0x1b0182e2305c060b, 0x184a03094060d94c, 0xa43094061280c250, 0x61700c2d0584]) else (cbits [0x10c3209860130b82, 0x3e1d878130f0061a, 0x58a40313c362294c, 0x80314c162980c520, 0x62a00c54018a]))) else (if j < 84 then (if j < 83 then (cbits [0x2c5a018b0131504, 0x7d418b71316c062d, 0x191a03234064680c, 0xa13235864680c8d0, 0x65380ca70194]) else (cbits [0x80caf0194e4329c0, 0xaf1595e032bc0657, 0x196c032d0265a00c, 0x2032d8b65b00cb60, 0x66100cc10598])) else (if j < 85 then (cbits [0x1acc201984033080, 0xcf0599e0333c0661, 0x19a003340066800c, 0x51b390666828cd00, 0x68d00d0d359d]) else (if j < 86 then (cbits [0xd1a01a34034680, 0x1a01a3403468068d, 0x1a3c03478068d08d, 0x80b47c568f02d1e0, 0x69280d2501a4]) else (cbits [0x80d2b01a4a334940, 0x2b35a56034ac0695, 0x1a74034e0269c00d, 0x4034e8069d00d3a0, 0x69d00d3a01a7]))))) else (if j < 92 then (if j < 89 then (if j < 88 then (cbits [0x80d3f09a7e034e85, 0x4705a823350406a0, 0x9a946b52806a404d, 0x80356436ac80d570, 0x6b1c0d5c1dab]) else (cbits [0x80d8b01b121360c6, 0x9801b300362cd6c5, 0x5b320366406cc02d, 0xc0367416cd06d990, 0x6d200d9e19b3])) else (if j < 90 then (cbits [0x80da415b48036900, 0xb101b600b6a476d4, 0x1b64036c806d882d, 0xd3b6e456d90edb20, 0x6f600de51db7]) else (if j < 91 then (cbits [0x4dec19bd8037b00, 0xf401be8037d006f9, 0x1bea0b7d406fa02d, 0xa037dc66fb02df60, 0x6fe96dfd01bf]) else (cbits [0xe0801c10038200, 0x831c10038200704, 0x1c2a0b850170a00e, 0x803930072114e16b, 0x72600e4c01c9])))) else (if j < 94 then (if j < 93 then (cbits [0xe5611c98539300, 0x5a01cb403968072d, 0x1cbc03978072d08e, 0x22b980172f04e5e0, 0x73300e6601cc]) else (cbits [0xe6a01ccc239980, 0x6a05cd4039a80735, 0x1ce40b9ac773580e, 0xe039dc073b80e731, 0x73c02e7705ce])) else (if j < 95 then (cbits [0x80e7d01cfa039e44, 0x7e05cfc039f4173e, 0x5d0e03a14273f8ce, 0x26ba44074412e870, 0x74f00e9e01d2]) else (if j < 96 then (cbits [0x2e9e01d3c03a780, 0xad01d5a03a7ce74f, 0x9d5a03ab4075680e, 0x403abcb75780ead0, 0x75d00eba01d7]) else (cbits [0xecb0dd7683ae81, 0xe701dbe43b391767, 0x1dd603b9c477380e, 0xbbe0077b82eeb3, 0x77c80ef901df])))))) else (if j < 107 then (if j < 102 then (if j < 99 then (if j < 98 then (cbits [0xefd25dfa03be44, 0x611e0c03c180783, 0xde1b0bc30178504f, 0xa33cd4079a80f2e1, 0x79e80f3b09e6]) else (cbits [0x80f3f01e7a13cf40, 0x4009e7e0bcfc079f, 0x5e840bd0807a100f, 0x433d1067a200f430, 0x7a830f5001e9])) else (if j < 100 then (cbits [0x80f8509ef45bda12, 0x8701f0e03e1c07c3, 0x5f1343e2407c384f, 0x403ee807dd00fb12, 0x7e208fba29f7]) else (if j < 101 then (cbits [0x80fc815f9003f200, 0xd101f9a23f3407e6, 0x9fa803f4437e880f, 0xe63f5817eb00fd40, 0x7f180fe301fa]) else (cbits [0x700429fc70bf8c0, 0x1102022040440807, 0xe0286404c1808850, 0xe0409c0813810201, 0x814810270a04])))) else (if j < 104 then (if j < 103 then (cbits [0x9502a06054040a41, 0x370206a140d40815, 0xe0752c0e4181b850, 0xc041b808350905f2, 0x8370906e020d]) else (cbits [0x1072120e4041c80, 0x760e0ec041d8083b, 0x20fc041f8083c8b0, 0x2041f8383f0107e0, 0x846010812e10])) else (if j < 105 then (cbits [0x308c02118042300, 0x950612a042348846, 0x212c0c258084b010, 0xe2425c084b810970, 0x84d8109b0212]) else (if j < 106 then (cbits [0x8109c2e1380426c1, 0xb2021505429c1853, 0x21664c2c81859010, 0xe042fc085e070bc0, 0x8600b0bf0617]) else (cbits [0x8b0c50218a043140, 0xca06194043280862, 0x21b2043544865950, 0x404364186c810d90, 0x86d010da021b]))))) else (if j < 112 then (if j < 109 then (if j < 108 then (cbits [0x930eb021cc2c368c, 0xf6021ec043d02875, 0x21f2043dc287b030, 0x4400087c8f0f90, 0x880011000220]) else (cbits [0xa51050a2080c4004, 0x1b022340c4641883, 0xa23a0c470188d831, 0x20448098900111e0, 0x8a09b1296225])) else (if j < 110 then (cbits [0x8314e5e29c045380, 0x67022cc0c59808b2, 0x62e2045c408b3951, 0x60c5cc08b9031710, 0x8ba03174022e]) else (if j < 111 then (cbits [0x118f0e31c0c5d59, 0x92063240464808c9, 0xa32a0464c28c9811, 0x46e008d59b1955, 0x8dd071b80a37]) else (cbits [0x831bd0237a046f40, 0xc00e37e0c6f818de, 0xe38a8c71408e1851, 0x20476408ec811d60, 0x8ec811d9023b])))) else (if j < 114 then (if j < 113 then (cbits [0x171da523b4047641, 0xfa0e3f20c7e408f7, 0x63fa0c7f408fe811, 0xf0c80768ff851fe0, 0x939812586e46]) else (cbits [0x1274024e60c9cc0, 0x75024ea049d0193a, 0xa4ea049d4093a812, 0xe049dc093b812750, 0x93d81277124e])) else (if j < 115 then (cbits [0x127c024f8049ec1, 0x7e024fc049f0293e, 0xe50004a00093f052, 0xe0ca3c0947812803, 0x948012900251]) else (if j < 116 then (cbits [0x12920252404a402, 0x926e52404a480949, 0x255c04ab41956812, 0xe04abc0957032ae0, 0x958012af0655]) else (cbits [0x12b00a56004ac00, 0xb60256424ac80959, 0xa58a04b10195b1d2, 0xe04b1c0963812c50, 0x965072c70e58]))))))) else (if j < 136 then (if j < 126 then (if j < 121 then (if j < 119 then (if j < 118 then (cbits [0x92d20a5a404b345, 0xdf065bc0cb60696a, 0x65cc2cb8c3970072, 0x634bbc4976072eb0, 0x97e812f9125e]) else (cbits [0x893019a60204bf44, 0x2c1265804cac1993, 0x26600ccc00998013, 0x4d2009a2873315, 0x9a4013480269])) else (if j < 120 then (cbits [0x853490269204d201, 0x4b0269604d2c09a4, 0x269804d3009a5833, 0x83cd3009a60134c0, 0x9ab013530e69]) else (cbits [0x1358126ae0cd581, 0x5c526b804d7009ae, 0x26e604dcc09b8073, 0x804dd009b9833730, 0x9ba01374026e]))) else (if j < 123 then (if j < 122 then (cbits [0x8b37b026e83cdd00, 0x810270204e0019bd, 0xe71434e0499c0813, 0xc24e5809c9873900, 0x9d08539a1e72]) else (cbits [0x8b3a81674824e8c1, 0xb6167661cec819d6, 0xe77cbceec39dd813, 0x204f6409ec033d50, 0x9ed053d9067b])) else (if j < 124 then (cbits [0x813dc0e7b804f700, 0xe1067be14f7c09ef, 0x27ca04f9409f1073, 0xe1cf9c09f2853e50, 0x9f5013ea027c]) else (if j < 125 then (cbits [0x97400b67ea5cfa8b, 0x39028700d0e00a16, 0x6872050e40a1c814, 0xc150e9ca1d014390, 0xa2c81458068a]) else (cbits [0x91459028b2051640, 0x67028c2351840a2c, 0x28ce0d19c0a33814, 0x2451a40a34034680, 0xa3901471068d]))))) else (if j < 131 then (if j < 128 then (if j < 127 then (cbits [0x3477068ee051c85, 0x83028f44d1e41a3c, 0x29060d20c0a41814, 0x2052144a42034840, 0xa44834890291]) else (cbits [0x34951e926152289, 0x9f0693c0d2741a4e, 0xa946152881a50054, 0xc052a0ea53834a50, 0xa5b054b60296])) else (if j < 129 then (cbits [0x834b816970052e00, 0xbe0a97c052f80a5e, 0xa98c053141a600b4, 0x4fd3602a64214c60, 0xa7d014f9069b]) else (if j < 130 then (cbits [0x834fb029f6053e81, 0x6029f8553f00a7d, 0xea101541c1a83035, 0xd4600a8a8750a2, 0xa8c8151902a3]) else (cbits [0x352c02a560d4652, 0x2f06a5c0d4b41a96, 0x6aa80d514fa982b5, 0xe0d55c0aab035550, 0xaac0755802aa])))) else (if j < 133 then (if j < 132 then (cbits [0x8157102adc1d56d3, 0x7202ae20d5c40ab8, 0x2af00d5e00ab90d5, 0x2055e40abc815790, 0xac0015791eaf]) else (cbits [0x158202b020d6001, 0x9602b126d6087ac1, 0x2b2c056580acb015, 0x20565caacb035960, 0xad1855a10ab4])) else (if j < 134 then (cbits [0x75a906b4a256940, 0xb02ab5c156b41ad5, 0x2b943d7184add195, 0x20d7440ae8815d10, 0xaea015d20aba]) else (if j < 135 then (cbits [0x835e702ba89d7500, 0xe806bd0057a00af3, 0xec48057cb2af4935, 0xe0d89c0b13816240, 0xb160162812c4]) else (cbits [0x1d62c02c58058b00, 0x3a02c74058e80b16, 0x2c76258e81b1d016, 0xa058fceb1f8163f0, 0xb268d64d02c9])))))) else (if j < 146 then (if j < 141 then (if j < 138 then (if j < 137 then (cbits [0x876530aca60594c0, 0x6102cc00d9608b2a, 0xacc2cd9840b30816, 0x8159f00b3e0167a0, 0xb3f0367e02cf]) else (cbits [0x368106cfe159fc0, 0x9016d0865a0c1b41, 0x2d2c45a541b4a816, 0x615ad85b4f3169e0, 0xb5f016bd06d7])) else (if j < 139 then (cbits [0x816be0ed7c05af80, 0xd016d8475b041b60, 0x2dac05b580b6a836, 0xe05b581b6b016d60, 0xb6c816d70ada]) else (if j < 140 then (cbits [0x56de02dbc05b645, 0xe60adc22db801b6f, 0x2e2e05c3c8b744f6, 0x47dc680b8b877170, 0xb948172902e3]) else (cbits [0x1972c02e560dca42, 0x3806e7005ce00b96, 0xee7805cf00b9c877, 0xdd7c1bab9173c6, 0xbb10376106ec])))) else (if j < 143 then (if j < 142 then (cbits [0x57640aec60dd8c0, 0x6d36ed41dda02bb3, 0xaf000de000bbd0d7, 0x615e0c0bc1817810, 0xbc29178502f0]) else (cbits [0x17a60af461de356, 0xb512f5655ea03bd4, 0x2f7205ee40bdc817, 0x23def64bdc897b90, 0xbf4017e802fc])) else (if j < 144 then (cbits [0x817eb0afd605fa03, 0xee06fda0dfb40bf6, 0x2fe06dfbc1bf7817, 0xcc5ff41bfe817fd0, 0xc0e838161eff]) else (if j < 145 then (cbits [0x838301703e8e0781, 0x3a1b06c260d80c1a, 0xb080561000c20018, 0xc361302c260184a0, 0xc2b478540b09]) else (cbits [0x187e030fc061e45, 0x7e030fc061f80c3f, 0xb0ff8e1fc0c3f038, 0x62fc1c5f038b03, 0xc60c38c00718]))))) else (if j < 151 then (if j < 148 then (if j < 147 then (cbits [0x99909032082e38a2, 0x160322a0e4540c84, 0xb22e1645c0c8b039, 0xc064902c8f8b9191, 0xc93019260324]) else (cbits [0x819290b24c1e4980, 0x2b07256064ac0c95, 0xf266ae4b85c96059, 0xa0656c2cad819484, 0xcae9395d032b])) else (if j < 149 then (cbits [0x1966032cc065980, 0x690b2d2065983cb3, 0x32da165b40cb5859, 0x69e5ec0cbd8196f3, 0xcc70198e032f]) else (if j < 150 then (cbits [0x199e0331e7e6381, 0x9f2b33e066781ccf, 0x3358066b00cd4879, 0xe0e6cc4cd60f9ac0, 0xcdc079b80336]) else (cbits [0x899bc7f3760e6ec0, 0xdf073be0677c0ced, 0x33d6067a42cf0139, 0x6667ac0cf5819eb0, 0xcfb819f7033d])))) else (if j < 153 then (if j < 152 then (cbits [0x8d9ff033fe067dc8, 0xa034120e8144cff, 0x3434568641d051fa, 0x6068d85d1225a240, 0xd1e01a3b0747]) else (cbits [0x55a3d0747a068f01, 0x840b4f25e9a11d1f, 0x350e06a181d4301a, 0x406a480d4397a870, 0xd4919a920352])) else (if j < 154 then (cbits [0x5a9e0353c06a780, 0xa00354006a800d4f, 0x355206aa40d5013a, 0xe06ad42d5691aa91, 0xd5b83ab70356]) else (if j < 155 then (cbits [0x1ac3675705eae00, 0xdf0b5b81eb700d6e, 0x35de46b84ed7081a, 0x436be02d7b83af70, 0xd8181b000f5f]) else (cbits [0x1b180362436c0cf, 0x19076300ec600d8c, 0xd8d25b]))))))))) 19 (i % 16)
def s68Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 217 then (if j < 108 then (if j < 54 then (if j < 27 then (if j < 13 then (if j < 6 then (if j < 3 then (if j < 1 then (cbits [0x240004010000003f, 0x1f023300980a780, 0x980dcc8cc0564466, 0x8ce3147233021b11, 0x83858c7c194062a0, 0x6e123c333170b195, 0x1a18c8f0cfc26086, 0x1982]) else (if j < 2 then (cbits [0x9c9940c4248ce620, 0x6372982315948f18, 0x1190d2478c7e8e16, 0xca092d346749624c, 0xacc124dd64792666, 0x72c8cec38570b4a1, 0x7a24385b10d99418, 0x7467]) else (cbits [0x3c0008012eca0f45, 0x1b0048009800600, 0x6009c812003e4018, 0x180333048015980, 0xb80600fd812006ec, 0x2a00d43147048021, 0x19580798c7c03586, 0x10f3]))) else (if j < 4 then (cbits [0xfc051466e025e333, 0x62011451a188978c, 0x7989c8358c4240d4, 0x1e66372145315909, 0x20a2990d04bcc7e8, 0x6661ac92d306a496, 0x4a1a8a2a4dd44bd2, 0x50f3]) else (if j < 5 then (cbits [0xd8359872c0d4c38, 0xf45706a7a24079b1, 0x31884000cc40e1ac, 0xe6370007315800, 0x8005990c0024c7e2, 0x58201664f1009325, 0x499900324b4800d2, 0x2009]) else (cbits [0x2d001d2864016937, 0xc38400b4a7a004a5, 0x4b0fcc0198726006, 0xec4f500b621a80, 0xb0033d15800de88a, 0xa2e00725080077a7, 0x61c000224b1c01a4, 0x1004])))) else (if j < 9 then (if j < 7 then (cbits [0xc040164a0000af44, 0x8000a18e000400, 0xe00ac0040054001a, 0x38037101001b000, 0xf8108007407c2, 0x4e203e04e101d025, 0x31008120ccc00906, 0x27]) else (if j < 8 then (cbits [0xd800ccc56005262a, 0x642103331b881498, 0xca4b040d0c9c0068, 0x7e933003e496801, 0x8021a50c010926e0, 0x722072c3800444a7, 0x6278822310c40f98, 0x1043]) else (cbits [0x40011de9e008af44, 0x636000e3150822c9, 0x7b0e0003d258201c, 0x24336001118a080, 0xa1908004cc400, 0x84002c9360015496, 0x61c000c2538005d2, 0x19]))) else (if j < 11 then (if j < 10 then (cbits [0xb0006e4a00034f44, 0x6410020310000f24, 0xc25040085258002e, 0x4725000227a7080, 0x1324d000940200, 0x5820223360011195, 0x4081430e000a12, 0xe]) else (cbits [0x8000986322024036, 0x92c002b321001518, 0x7250800b526c0058, 0x60c38002f4a7001, 0x19494000c5e880, 0x58005c6410035310, 0x7a70817a50400d92, 0x37])) else (if j < 12 then (cbits [0x5000e804a0071250, 0x33e101919b00078c, 0x8d380080684003c, 0x609360028496081, 0x81b253800d52842, 0xa00078f44003b61c, 0x49a00098cd000f64, 0x2a]) else (cbits [0x104c500080028, 0x28002d320000b01, 0x598a0005c0980028, 0x30058002e326001, 0xd0cd800bccb00, 0x6c204634e101b1a1, 0x4a70819250800c52, 0x1038]))))) else (if j < 20 then (if j < 16 then (if j < 14 then (cbits [0x4040f5e880078c38, 0x658002202c002349, 0x60c540124628006e, 0x9a337004d195802, 0x80288d0c013c67e2, 0x5820a234f104f1a5, 0x499802ba4b401492, 0x59]) else (if j < 15 then (cbits [0x2c017128600b6937, 0xc3800614a7802fa5, 0xfb0fc415d87220a4, 0xb8c4f1061621882, 0x8032bd140189e882, 0xa220c525000677a7, 0x61c002524b041964, 0x104a]) else (cbits [0xc0412e4a00096f44, 0x25005019a002700, 0xa30e00128c4000a6, 0xad25000557a2002, 0x2d0ca001600480, 0x9800bc648005d1a4, 0x3100031809401812, 0x4b]))) else (if j < 18 then (if j < 17 then (cbits [0x404159e8800aac38, 0x3540066012003249, 0x5802401a4ca800d0, 0xea01b006e007803, 0x883a809c01f803e0, 0x6e0104033107e015, 0x21884100fc02340, 0x108d]) else (cbits [0x7c80e46360006315, 0x32b303919390290c, 0x10cdd811466660a4, 0xc4343704519fb03, 0x804e98840248c40e, 0x6e016262b00a8313, 0x321806118fc02dcc, 0xc8])) else (if j < 19 then (cbits [0xcc427525a212492c, 0x94310c849b886124, 0x7b0e40339870216e, 0x19cf4400d1621806, 0x3618a8433de8a2, 0x7000da92c106c31b, 0x1b003780a841b58, 0x106f]) else (cbits [0xa841c009c00e0042, 0x342107119b00388c, 0x9a4b041c869c00e4, 0xe8f44107361c003, 0x3b00d841d24a00, 0x4a00f004e0077021, 0x4a1003ca4b080e8c, 0x7a])))) else (if j < 23 then (if j < 21 then (cbits [0x4001f1e8800f6c38, 0x3250071007003ec9, 0xb0e00200c4000fe, 0x1080360083015004, 0x44813802140980, 0xa00116c38008a496, 0x4960043188002324, 0x87]) else (if j < 22 then (cbits [0x3002186980110f44, 0x33d007200700438d, 0x824b0023cc40011c, 0xda009009101e004, 0x9039806c024c01e4, 0x66411e02b208a013, 0x1fa04080dd01ec0, 0x408b]) else (cbits [0x6c01b462a8120043, 0x32b107b19380398c, 0x78cdc02286662102, 0x120343108b19f804, 0x981e189c0010c422, 0x6ec0786333055315, 0x321b82318fd8154c, 0x7064]))) else (if j < 25 then (if j < 24 then (cbits [0xcc025925a012892c, 0x943009949b804ba4, 0xb30e482518700134, 0x136f44209a621904, 0x4ab0e00271e8a0, 0x70013094c10957a2, 0x7204abd1042558, 0x9e]) else (cbits [0x94020065200f2325, 0x932204a314901418, 0x12508028526c013e, 0x14a94e00a34a5005, 0x533d1042598700, 0x80014032800a7928, 0xf0054807002912, 0xaa])) else (if j < 26 then (cbits [0x802acc40403c319, 0x92c10ad327005699, 0x724d802b926a013e, 0x13ec3800af4a1085, 0x583d1042bd89c2, 0x58014031410b0928, 0x188056003042812, 0xb2]) else (cbits [0xc4c0d464a406a319, 0x62500a131000598c, 0xa4b042b8c4c015c, 0x16ac4200b461c085, 0x5b3d1042d589c0, 0x7a00f401910b6928, 0x198a0180c6402e00, 0x6031])))))) else (if j < 40 then (if j < 33 then (if j < 30 then (if j < 28 then (cbits [0x980288c40017233d, 0x931109a496005798, 0xaa50402f127a0174, 0x17cc4e00bd61c005, 0x603d3802fde880, 0x6c017694c00c1928, 0x32100621900030cc, 0xc6]) else (if j < 29 then (cbits [0xe0031d29a014692c, 0xf4410ba626884bb0, 0xc24b00290c40c160, 0x18ac3810bb4a0884, 0xa01b0c6403240920, 0x400194349903819e, 0x496006398f40294c, 0x1099]) else (cbits [0xe042d529a0196949, 0xf4400c0626b05b30, 0xa006c03364a00198, 0x118033607c013b03, 0x803a0c6e01f407f0, 0x7e20fa333007c193, 0x3138002988442306, 0x203b]))) else (if j < 31 then (cbits [0xdcc0f4c6640a862b, 0x643903d31f982b18, 0x324b4825125920ac, 0x16c93700b0499805, 0x305b250d82c127e0, 0x86214ec39109b61c, 0x7a2c04dbd1043058, 0x80a7]) else (if j < 32 then (cbits [0x48259258c096641, 0xc41109c61c005ea5, 0x3c9400341e9c2198, 0x6433100d2024c85, 0x698d2640c867b0, 0x92017c635209a310, 0x496006019340350c, 0x309a]) else (cbits [0x344351292217c941, 0xf4400d061c086025, 0xb803c03564a021a0, 0x1b003300d8013806, 0x80138c64001862a2, 0x4e009831f004918e, 0x199902b8cac80f86, 0x303e])))) else (if j < 36 then (if j < 34 then (cbits [0x3d819468660ae337, 0x62b00d931538328d, 0x98dc4364c6c01c2, 0x1ce64200e231f087, 0x87399384388c940, 0x6601d292d209d496, 0x4a18076a4dc03ad2, 0xee]) else (if j < 35 then (cbits [0xe4c27587001e094f, 0xc4f10f06218874b0, 0x8bd3d833de8821dc, 0xd802870cf928007, 0x6d0c9480a86320, 0x5801b864200db310, 0x49b006ea4c802792, 0xde]) else (cbits [0xe0038129c01be942, 0x25060bd7a2185130, 0x298a8038cc50e1a1, 0x13e92c00e631b007, 0x721880c28d8704, 0x82414262030a4496, 0x4a09852a4b0037cc, 0x10e0]))) else (if j < 38 then (if j < 37 then (cbits [0x3243324a001d0f4e, 0x62800db49a007500, 0x781200378c8001d8, 0x1be64c00dc314007, 0x7901500380cb00, 0x1a000e00900e832c, 0x98019803c00a40, 0x4d]) else (cbits [0x7c80cc0364052019, 0x2700f4012902680, 0x180cc03e405601ee, 0x8603f305c01b982, 0xb823812d8170086c, 0x2a01b23147067027, 0x19b807d0cd803846, 0x103])) else (if j < 39 then (cbits [0x280418686020a33f, 0x34f010f1a580838d, 0x98848364c400222, 0x20c6372105319907, 0x1081990c83e8c844, 0x9e421e64b2107325, 0x4968089a4b08444c, 0x116]) else (cbits [0xd80465266022e932, 0x93e011f49b808da4, 0xda508846527e422e, 0x24094a211f4a1908, 0x8092253804892960, 0x72616ec3801274a7, 0x621809430fcc3b98, 0x12c]))))) else (if j < 47 then (if j < 43 then (if j < 41 then (cbits [0x1582dde88025ac4f, 0x250212d7a7b0773d, 0xa8021c3c64a2e1a3, 0x9c31e000818a007, 0x6d188081386540, 0x8441b492c00f631b, 0x7a2185cb0e083d92, 0x60b9]) else (if j < 42 then (cbits [0x9003e0668e1a7250, 0x19202b006807c00, 0xb00c4c0ac04a01ec, 0x1f633220dc18a087, 0x800d2803f06840, 0x5821f66250102310, 0x4a7088024f8c3712, 0x10fc]) else (cbits [0x4182f9e882204c38, 0x93c00fd318385f49, 0x8d0003f8c8001fe, 0x1fc64010fd4a6008, 0x1082253004112802, 0x840218336010819a, 0x61c0086a4b08400c, 0x30af]))) else (if j < 45 then (if j < 44 then (cbits [0xd80439e9ac174f44, 0x92c010931010808c, 0x5b10582ed8700214, 0x21263440fe19a008, 0x207e9900042c6680, 0x6c022495801101a0, 0x27108a010804500, 0x115]) else (cbits [0x8080b064a0058319, 0x64a010231b004f18, 0x125088279258021a, 0x17ec38210d4a5108, 0xb86ac94182fde886, 0x9c01ba314305d01a, 0x1a0386a494004618, 0x10fb])) else (if j < 46 then (cbits [0x6400b401a0234c40, 0x31302e012901700, 0xf988003786280238, 0x23ac3830df496106, 0x88f313804798840, 0x60e18125060c07a2, 0x61c3834013404692, 0x30bc]) else (cbits [0x3582f1e880242c4d, 0xd012362c1090bd, 0xb80f480bc032005e, 0x1c03140125024b81, 0x985aa4b08380c400, 0x9ac16ac38111e4a6, 0x92838743d1104798, 0x126])))) else (if j < 50 then (if j < 48 then (cbits [0x4a46680246948, 0x64c212931a08800d, 0x5b16004a92688200, 0x202640110119a009, 0x87e0cd004792988, 0xa8421c64851181aa, 0x4a4008c24c14484c, 0x121]) else (if j < 49 then (cbits [0xd044792b0025c954, 0xd0009004887f8c, 0x7807c04c0026003a, 0xb202b203f013802, 0xb027810cc17c06e4, 0x500264314905f027, 0x195009d0ca404d06, 0x13c]) else (cbits [0x38050866c028232b, 0x62b00e231030a10d, 0x798dc441cc6c020a, 0x2866420143320888, 0x9075a4b482a1258c, 0x9ec20a943014449b, 0x627986130e185112, 0x5128]))) else (if j < 52 then (if j < 51 then (cbits [0x3e041de9cc1c4f44, 0x33490c29284087bd, 0x5a4b004cc01c0262, 0x26a01b0050009905, 0x983000ac04d803e0, 0x2920c0043605001b, 0x19588840ca8038c6, 0x1110]) else (cbits [0xac04e0c42026e620, 0x92c6139321809c98, 0x1b0e144ad2866188, 0x220c438108621307, 0x7218824311e890, 0x70618a92c110a315, 0x7a24085310983918, 0x90c5])) else (if j < 53 then (cbits [0x6404ed2580262011, 0x25205a00e902080, 0x60cd80394628027a, 0x27c63620ec310088, 0x9fa4b184f8c9c0, 0x70c28094e014049b, 0x7a73072bd10c3198, 0x810c]) else (cbits [0x800398629218d250, 0x94e014031a905698, 0x1c94144a989ca252, 0x18ec3820ae496486, 0x80a00d0004f86506, 0x26006800d000b004, 0xf9021006c01440, 0x205b]))))))) else (if j < 81 then (if j < 67 then (if j < 60 then (if j < 57 then (if j < 55 then (cbits [0xc4c1840566088027, 0x3d605101bb01a00, 0x2012c051c086028c, 0x1ce3149061027c82, 0x88888cac041863e0, 0x9ec2863320143198, 0x3109058988005206, 0x20ed]) else (if j < 56 then (cbits [0xdc0524c564288627, 0x641014a31eb08318, 0x2192c052cc864236, 0x19092c4149327a0a, 0xb0a424dcc3c125a6, 0x862248941014c49e, 0x61c2896253c05352, 0x60e7]) else (cbits [0x280539e890222c4f, 0xf4f81247a730a63d, 0x8494643224a0c29a, 0x194c3820b3496487, 0x40893d62432a4a06, 0x592197250011e626, 0x9281866b0e082d12, 0x90cd]))) else (if j < 58 then (cbits [0x9c058003c02a001b, 0x33216001510a800, 0x800fcc58006c62a0, 0x2a004b616002130a, 0x80c10c79c58009ce, 0x56430432a01c018f, 0x19b98c10cd887006, 0x31c0]) else (if j < 59 then (cbits [0x398700686c304342, 0x62071c01a7b8c10d, 0xd98ac07ccc42039c, 0x42863f11fb31b80f, 0x890a192c08a8c860, 0x5a439c92c122a327, 0x49b910a24cc87cd2, 0x222a]) else (cbits [0x3d085129683f6943, 0xc3931ce61c211525, 0x5310d485187e63e6, 0x39cf4451fb627a91, 0x40fdbd3d87cde8ac, 0x10e3e725171ce928, 0x2100a900d805440, 0x1152])))) else (if j < 63 then (if j < 61 then (cbits [0x58055009c02a604a, 0x332115402d08a981, 0xb98d8455467c02aa, 0x2b264e115732100a, 0xada4b04564cb40, 0x9c22b8942015c49b, 0x61c08aea56805752, 0x15e]) else (if j < 62 then (cbits [0x70057e4a022bcf44, 0x10000a00e08afd5, 0xc18a005592680010, 0x2ac324015a32000a, 0xad19000560c500, 0x5602c8315016118a, 0x19f88b28cdc05946, 0x166]) else (cbits [0x3c459869602d0343, 0x92d016949608b40d, 0x924dc05c126602dc, 0x2ec94b01734a180b, 0x88b4b0e005e529e0, 0x8622ecc3f116e61c, 0x7a208b9b13c45e58, 0x17a]))) else (if j < 65 then (if j < 64 then (cbits [0x4005fde9e02faf45, 0x92c117d92888bd49, 0x1bd10458987002c4, 0x2ce334116392800b, 0xb1188005a804a0, 0xa002d8f44016b61c, 0x19400b7809005b64, 0x171]) else (cbits [0xa005d4c9002e8348, 0x2501784a600bb80, 0x630e0058cc4002f6, 0x2f9250116d7a200b, 0xc00d5005f80480, 0x6642ae027018132a, 0x25b0ac80fcc55c0, 0x7159])) else (if j < 66 then (cbits [0xa8061c62a0306314, 0x336019419580c40c, 0xa8cfc465066e2310, 0x33e34301981a100c, 0x88cc0d3846546960, 0x640340626119f1a7, 0x32500d118f84680c, 0x11a2]) else (cbits [0xcc06b125a034c92c, 0x94301b049b80d724, 0xb253c06cd2960362, 0x358c3911a661c00d, 0x88db310c46cd87e2, 0x8a036ef4411b1627, 0x92800df3d3c06f1e, 0x11b7]))))) else (if j < 74 then (if j < 70 then (if j < 68 then (cbits [0xc80610c4c2379251, 0xc38018549608c218, 0x349400619e88230a, 0x312620215800c88c, 0xc599280628c840, 0x84031c936018d496, 0x61c00c82538063d2, 0x191]) else (if j < 69 then (cbits [0x64e4a00324f44, 0x64c019619a00c619, 0xc98818568062032e, 0x33492c018f32080c, 0xcdb0e046412820, 0xa0033af4e019c7a2, 0x18a00cb8cf0067a4, 0x184]) else (cbits [0x38068d2580342f44, 0x1901a592800d23d, 0x2988006a004a034e, 0x332642119131b00c, 0xd1a4f84668c9c0, 0xa00354f4401a961c, 0x31a00d6809006ae4, 0x189]))) else (if j < 72 then (if j < 71 then (cbits [0xa00638680035e328, 0x648018f1a600c50c, 0x58cd006d06500364, 0x31832801b54a600c, 0x80dc006406406b00, 0x6c030c62001ba012, 0x32708c999080648c, 0x119e]) else (cbits [0xe046952940342932, 0x25011ab7a200d530, 0xe809006e40800377, 0x33a358019b32600d, 0x8d219200690c780, 0x84038233601bf32a, 0x1ad00e20d3847046, 0x11c4])) else (if j < 73 then (cbits [0x80720c6c038e620, 0x65a01c932708e419, 0x524f807292642392, 0x39695601cb4a508e, 0x8e63d1007318702, 0x50239b55c01cd928, 0x31200e18cc007086, 0x21c3]) else (cbits [0xf00718690038a340, 0x328000a32430e318, 0x18cd007146800384, 0x38c34c000a19410e, 0x80e7803c0018012c, 0x3e03aa01d01d000c, 0x1580ec009c075c0, 0x1da])))) else (if j < 77 then (if j < 75 then (cbits [0xfc476806e23b0033, 0x4b01df02180ee00, 0xf0c9c477c09e23b8, 0x2bc333216919510a, 0x30af8cfcc5a466c6, 0x9ce2be34b617a1a1, 0x31590d318a9c5e86, 0x21cc]) else (if j < 76 then (cbits [0x8c730c6e634c636, 0x64e61cd321b0db99, 0xa4b1c734c9ee36e, 0x3ca93301e449680f, 0x80f4a50c07a126e0, 0x7003dc94f01eb4a5, 0x61f88f230e447858, 0x11eb]) else (cbits [0x1047a589e23dcc43, 0xf4f01f07a280f7bd, 0x8494447be4a003e2, 0x3a203601d101508f, 0x8e9013807480842, 0x8823a6c3801d3496, 0x49608ea49400751e, 0x1d6]))) else (if j < 79 then (if j < 78 then (cbits [0xd0076405023acc38, 0x2801db19810d3a4, 0xc253007780b003ba, 0x3c034861b932030d, 0x90eb00a4874c04a0, 0x6c03ac32901d3192, 0x32730b61908c5b0c, 0x717c]) else (cbits [0x3986a92846354936, 0xf4401e261c38dda5, 0x780a0078e4a043c4, 0x30a934216231a100, 0xf398a007980504, 0x9063326342199314, 0x32020c898a007a86, 0x6192])) else (if j < 80 then (cbits [0xa007b529803d8628, 0x25919e32620cd18, 0x598d8075064ac3a8, 0x2da64e316d32110b, 0x18d5a50886a526d2, 0x8843c4c3891ab4a7, 0x32640f1c940478de, 0x6163]) else (cbits [0x7c86a8c30c94c, 0x19919332640c999, 0x88078003403803e8, 0x2c2328015b19280a, 0x10b70cd805906540, 0xb4c2fa34e316e1a1, 0x31480c198a1c5f46, 0x1c7])))))) else (if j < 94 then (if j < 87 then (if j < 84 then (if j < 82 then (cbits [0x886b0c6c030e62a, 0x65a61bc32718d619, 0xaa50807d526ce378, 0x3f494e01f74a508f, 0x8fd256847dd2ac0, 0xa063c8f4421e461c, 0xe38f8557187c24, 0xe]) else (if j < 83 then (cbits [0xa08624c5003ec330, 0x64001f949a00fc18, 0x280780570032c336, 0x2ca02a215c01280b, 0xff00c407f00604, 0x84040003601ff019, 0x2d30b98138c5cc0, 0x717f]) else (cbits [0x78072063a031031c, 0x329218819400ca0c, 0x8cc886506544390, 0x362342020419b010, 0x38df0d6986c469c6, 0xac040e64201f5310, 0x4a710faa4b00820c, 0x2207]))) else (if j < 85 then (cbits [0xf8082d8704410956, 0xc4a020e621010630, 0x83158883989c4418, 0x3d2f44021262d010, 0x38f8d57187a64a06, 0x6c03ec620002518a, 0x4a110fb24b007f4c, 0x21fd]) else (if j < 86 then (cbits [0x4187a9e8863d4c38, 0x34c02021a038f949, 0x2b0f0080c6b04404, 0x40cc542205624010, 0x8fe80f007f40480, 0x386314334218a18e, 0x32010c58ca008246, 0x20a]) else (cbits [0xd00634c50431831c, 0x334317402010c698, 0x70c70083c078041a, 0x31e334218f19400c, 0x1088cd1c6000b06, 0x50032031c021302a, 0xcb8ce8d3086406, 0x153])))) else (if j < 90 then (if j < 88 then (cbits [0xd80598054042a01e, 0x4e317602110b800, 0xb8c7245d80b4c2cc, 0x43431e021918e810, 0x10d70cd806546540, 0xb4c32a34e31b31a1, 0x31a010e188246cc6, 0x21e]) else (if j < 89 then (cbits [0x80898c6c044a635, 0x92c622832d011419, 0x4a534482128403ee, 0x3cac3862294a7011, 0x30fbc940c7ade884, 0x6923d755c820892d, 0x2718bb80d808586, 0x9177]) else (cbits [0x4482466c03f0314, 0x62062181a1010c0d, 0x630e0879d2580266, 0x412f4e61f87a218f, 0x10d8cd247b24a10, 0x4c02ce01e021d006, 0x1b011000a8087c0, 0x3178]))) else (if j < 92 then (if j < 91 then (cbits [0x7a45e009cc2ce042, 0x32a022119300cb0c, 0xb0d08c6d466c0446, 0x3f262091b51a730c, 0x11224b04828c6c0, 0x9cc3f2f4431ed61c, 0x19a48f6c9420829e, 0x222]) else (cbits [0x700858038c44434c, 0x302171014010d8c, 0xa0cd086bc650044e, 0x32e328021818e18d, 0xb4007805740320, 0x7a62f20362172015, 0x24b0b4010985740, 0x22b])) else (if j < 93 then (cbits [0x7245e40b4045804e, 0x31e01c918e80cc0c, 0xb0cd886c0654033e, 0x39234161981a018d, 0x1168d39867c684c, 0x7a03f462091b61ad, 0x496311498f808a4c, 0x21e8]) else (cbits [0xe0883929a045c949, 0xc4d023062498f730, 0x9494187e9e882424, 0x42525a623092b011, 0x1178ca247baab90, 0x980338628023119a, 0x480c100218670c, 0x1c0]))))) else (if j < 101 then (if j < 97 then (if j < 95 then (cbits [0xc48d006e046802b, 0x314124e027812701, 0x30ca80a0462a04d6, 0x50c336031d195814, 0x19b0cfc4c7466e2, 0x9606f034303451a1, 0x1a789a28d384cd86, 0x1378]) else (if j < 96 then (cbits [0xf84dfcc6406fe626, 0x92c138232501c118, 0x524cc0f4525a0726, 0x80494303fa49b81f, 0x219253c10812960, 0x7e27a2c39139361c, 0x6278a19310c50818, 0x1402]) else (cbits [0x3c114de8a0872f44, 0x2511439928022dbd, 0xa8168070401028a7, 0x476328023918a011, 0x11218ca8090c6520, 0x9c048c3420244198, 0x31201250d6809246, 0x2244]))) else (if j < 99 then (if j < 98 then (cbits [0x888e5258049664a, 0x95a22464a71124a5, 0x63d10892d87c4494, 0x49b55c224c928012, 0x11c013008d80380, 0x98046e6402238326, 0x4011d189008dc6, 0x1c2]) else (cbits [0xb008d809c0478026, 0x942023f49b011f24, 0xb0e0090129c447e, 0x48525022417a2012, 0x11b810008f40980, 0x70447492c01c3004, 0x327011f990009158, 0x247])) else (if j < 100 then (cbits [0x3088fcc98049093c, 0x634024032c011c01, 0x118d00914c780482, 0x46a03601c4004012, 0x1278c5208d40b42, 0x8004aa3360250195, 0x1a1012f0d0409686, 0x625e]) else (cbits [0x98098c6b404be348, 0x648625f31e013218, 0x424b0099ccac04ca, 0x4c894962504a0813, 0xb131b10409a5870c, 0x8804d4c5b6267624, 0xaae312abd69893de, 0x6269])))) else (if j < 104 then (if j < 102 then (cbits [0x20094928004a2640, 0x2802547ad0129a5, 0xb25218950c82246c, 0x4b0c480257620012, 0x91b80a00965eb40, 0x9c247002a01c5004, 0x320812d988208e00, 0x252]) else (if j < 103 then (cbits [0x10095d28204b892c, 0x25062577a7012ebd, 0x18980718010c4b9, 0x4c4c380261496013, 0x312bb16248e00980, 0x40001400802601a4, 0x7ac013324b00874c, 0x6256]) else (cbits [0xf00984c9004b6640, 0x64002664a43130a4, 0x6009c0988c9004b8, 0x306314126c019813, 0x811c8cac071c62a0, 0x9e049e343123919b, 0x31901369898493c6, 0x126d]))) else (if j < 106 then (if j < 105 then (cbits [0xcc09d525a04de92c, 0x943027949b813c24, 0x7b0e009f129e04f4, 0x4f8c43127561c893, 0x813ebd1049e989e2, 0x2824fb250027f7a7, 0x7a2011d0ca406106, 0x26e]) else (cbits [0x8009c404a04e000d, 0xf44027261c00c298, 0xb003009d24a004e6, 0x4f66480277012013, 0x13724c80618c400, 0xa024e8f44027361c, 0x18a0140195009fa4, 0x187])) else (if j < 107 then (cbits [0xc84a08c840504636, 0xc38128449f014224, 0x18cc04a15e88050a, 0x3900090188004014, 0x1121807c08ec03a0, 0x6e05320270287013, 0x278128010c49180, 0x1255]) else (cbits [0xcc0a94c42053a620, 0x64202a731b815318, 0xd19280adcc860552, 0x5a464f02cf325815, 0x816da4b40b512580, 0x6e05bc93602dc499, 0x4a10172a4fc0b8d2, 0x2e8])))))))) else (if j < 162 then (if j < 135 then (if j < 121 then (if j < 114 then (if j < 111 then (if j < 109 then (cbits [0x380bcd29605e0943, 0xc3802fb4a7817aa5, 0x2b0fc0c0987205fa, 0x616c4f030a621818, 0x818a3d140c41e880, 0xa2063325003167a7, 0xe814400200c6e4, 0x289]) else (if j < 110 then (cbits [0x340a340820516035, 0x6420290310014781, 0xaa4b00a48c940522, 0x52ef44029661c014, 0x14501300a624a00, 0x980518034028c020, 0x20014500700a380, 0x28e]) else (cbits [0xa50c80052601c, 0x58029b026014d01, 0xe807008f06500538, 0x312314029e009011, 0x13824b00a4064c0, 0x9c0540942029f49b, 0x7a2015130e00a852, 0x2a3]))) else (if j < 112 then (cbits [0x200aa12800549250, 0x35029100d00c500, 0x598800aa867c04a2, 0x55a92c02ac318815, 0x158a53c0ab92620, 0x880568c4e02b361c, 0x14015b49400ad5e, 0x2af]) else (if j < 113 then (cbits [0x40ac9898056094c, 0x94c02b81a4015925, 0xd8070062c0100572, 0x52402602c100e815, 0x16499080b08c800, 0x9a0596c3802ca496, 0x18a01673d100b318, 0x2bc]) else (cbits [0xb00af4c40052631a, 0xc3802bf4a0815f24, 0xa006806300100580, 0x58862002c3199014, 0x16325040b152580, 0x50058e33c02c861c, 0x194016225000af46, 0x2be])))) else (if j < 117 then (if j < 115 then (cbits [0x200afc038058a940, 0x64002c632001668d, 0x800700b00650058e, 0x5a695802d1326016, 0x16b01080b5406c0, 0x52031a31402d7027, 0x4a1013824b008f86, 0x2ab]) else (if j < 116 then (cbits [0x100b61870059494a, 0x33002da928016cbd, 0x700200b75880052a, 0x47e029023f00e80c, 0x14f98800b7c0642, 0x8405c0c38129f496, 0x7a20970b1380b858, 0x2e2]) else (cbits [0xc00b9007825c5250, 0xc4c02ac326016ea4, 0x780200b9c67805cc, 0x4a4035223f00e80c, 0x1750cf80ba407c0, 0x8205d692c02a0310, 0x7a2017630e00b852, 0x2ed]))) else (if j < 119 then (if j < 118 then (cbits [0x200bbe4a005dcf4e, 0x93c02f21a4017881, 0xa31600b9d27805cc, 0x48001d0190004017, 0x17b0128495c0820, 0x9a05ee92c02a1310, 0x626817c30e04b852, 0x2ee]) else (cbits [0x500bea4a005f2f44, 0x1902f44a4017e01, 0x88c500bfc06205fc, 0x52c332024119480c, 0x156a5080a892580, 0x8405b0c3802cb4a5, 0x7a2017bb1380bad8, 0x300])) else (if j < 120 then (cbits [0xc00c0c0300603250, 0x34129f620018200, 0x719300c1cc68060c, 0x612c58030849a015, 0x15819000abc6800, 0x9a248e03502e14a6, 0x32101860d51c9500, 0x2b1]) else (cbits [0x600c38ca80598648, 0x648030f7a68970a5, 0x68d200c35e9a059a, 0x62202502b2320018, 0x80c90c500c480620, 0x58052e3322241194, 0x61c016725280a8d2, 0x2d9]))))) else (if j < 128 then (if j < 124 then (if j < 122 then (cbits [0x100be189c05c4c42, 0x30031392801803d, 0x631300acd298062a, 0x4b204d0254020817, 0x15a19000c5c6a82, 0x9a05dc958031832a, 0x18a018d00c40c3d8, 0x193]) else (if j < 123 then (cbits [0xb00a606640484329, 0xc3802b64a7015224, 0x7b1384b8988405b4, 0x62725003017a2017, 0x17cb1600c700600, 0x6004860290194004, 0x18a019180c80c780, 0x282]) else (cbits [0x380c946940648342, 0x35a03271ab01930d, 0x625380ca92580652, 0x65ec3e032e61c019, 0x198b1380cc18840, 0xa00666f44033262d, 0x18a019ad5700cd24, 0x283]))) else (if j < 126 then (if j < 125 then (cbits [0x100c81870063e92c, 0x94003229280190bd, 0x40d000ae52980550, 0x65602402d34ac019, 0x19699200c7c6600, 0x78064233c032019e, 0x880ca80200c886, 0x337]) else (cbits [0x80cec66c0670334, 0x642032531b019e0d, 0xa4c80cf4c98264e, 0x688f44034261c01a, 0x9940cd806580100, 0x100674c380339496, 0x496019f1898065c0, 0x33f])) else (if j < 127 then (cbits [0x700cf8c980680c38, 0x640033f4a601a180, 0xc00200d012980674, 0x49201f01c900480c, 0x812d00d449280560, 0x4024c604f625e01b, 0x31381a698840d18c, 0x34e]) else (cbits [0x40d44c6e06a062b, 0x64b0353321817419, 0xda4b00d68c9e06ac, 0x6c2937036049681a, 0x81b1250c4bd52820, 0x9e06ccc3803644a7, 0x7a701b63d100da58, 0x36e])))) else (if j < 131 then (if j < 129 then (cbits [0x440dd64a006e4f4f, 0x314034701e81bbc9, 0x424b0096c66a0332, 0x692c3812f74a081a, 0x1a5bd380d29e880, 0x98054094c034c928, 0x1a40170b1300d3cc, 0x352]) else (if j < 130 then (cbits [0x200d500900572f4c, 0x640035700e01aa8d, 0x73d600d64c9806b0, 0x334314035c01e817, 0x81a424b0097066a0, 0x8806bac3802eb4a0, 0x92809a5bd380d79e, 0x35f]) else (cbits [0x204b4de982542c4c, 0xf5803651aa01b181, 0x4a4b0066c62825dc, 0x6bac3802ec4a081a, 0x1b3bd384be58820, 0xb006d43540368928, 0x1a080ce0c500dade, 0x25d]))) else (if j < 133 then (if j < 132 then (cbits [0x400d79870069492c, 0x35019d00401b6c9, 0x78129c95c082c4ae, 0x69662003701a501b, 0x89a5a4b00bb8c9a0, 0x8806cec3812ee4a6, 0x2a01b8c9404d9de, 0x373]) else (cbits [0x500dd809206e8354, 0x92c625c1a080cf0c, 0xfb0e00bbd29a0698, 0x6d0f4412f862681a, 0x9b3c9600db64a00, 0x5404bc041019f004, 0x19e09948cd80c986, 0x33d])) else (if j < 134 then (cbits [0xb00de8c4c06f235a, 0xc3803314a681bda4, 0xec9684cc989a06f8, 0x6d6f58037eaae01b, 0x19f98f00cf86780, 0x120340008034031e, 0x21912200a407280, 0x264]) else (cbits [0xfc0a1062a04da314, 0xf44037a1a181a08c, 0x8c500e05e8a0700, 0x4dc620224519a80d, 0x80e5802406880100, 0x82049602b026500e, 0x4960933813d897c0, 0x383])))))) else (if j < 148 then (if j < 141 then (if j < 138 then (if j < 136 then (cbits [0x3c0e21296070e92d, 0x250038d7a701c5a5, 0x201040e4a4a20723, 0x4cc32901a318a01c, 0x1c2bd3989846820, 0x9807126280386928, 0x401c619600e292, 0x1a4]) else (if j < 137 then (cbits [0x240e15258e4ac041, 0x250038f7a201c725, 0x10d3406946280721, 0x71f258038661c313, 0x81ca804c0e5001e0, 0x3e073c01b039700c, 0x1981d100940e7c0, 0x3aa]) else (cbits [0xc0ebc07e075a037, 0x4f03b302581d881, 0x60c540698628076c, 0x4d0343124c19b80e, 0x8137988049a469e0, 0x6e25fa6360285310, 0x32101a118fc4cccc, 0x346]))) else (if j < 139 then (cbits [0x384d10c9606f6643, 0x93e137c32789ad99, 0xd30e40ee18700706, 0x780c4303bc61f81d, 0x81e1bd100f0589e0, 0xa00794f4f03c87a2, 0x1801e7c9440f324, 0x396]) else (if j < 140 then (cbits [0x380e640840730036, 0xc3801a731001cd01, 0xec9400e71e880736, 0x74293003a001801c, 0x1d180d80e840540, 0x3c074a04e03a4021, 0x19901d00ca80e586, 0x3a6]) else (cbits [0xd809c52580350620, 0xf4403a761c097f24, 0x580a00ea64a00750, 0x74c33003ac02c01d, 0x1d800a00eb92780, 0x500764948038449e, 0x4aa01da81000ed00, 0x3b7])))) else (if j < 144 then (if j < 142 then (cbits [0x944e9c0622736025, 0x62003a719881cd8c, 0x4250809c92580352, 0x772f4413484a701a, 0x1dd80c04ee64a00, 0x68077a33412a24a0, 0x62c096599000ef8c, 0x3bf]) else (if j < 143 then (cbits [0x304b14c68257c328, 0x65812ad31a097b99, 0x200940f092a825d6, 0x73832503c601881e, 0xd518800ea06620, 0x9c26029420273496, 0x92801dcbd104d7d2, 0x3c7]) else (cbits [0x300f24060078a040, 0x93c034b32c01a4a5, 0x680940f2d2a8070a, 0x73a32503ce01881e, 0xd598800ea46620, 0x9c26009420274496, 0x7a201c331280d312, 0x13b9]))) else (if j < 146 then (if j < 145 then (cbits [0x600f40060078f250, 0x1903d200909aea5, 0xe80940f5404807a6, 0x47233501ac18a01e, 0x814e98d009d4c404, 0x84054a636032a31a, 0x32d01a699384c08c, 0x1360]) else (cbits [0x80f7987c070e94a, 0xc5603e162701f031, 0xd3d100f9d8b407c6, 0x7d355c03e892809d, 0x1ea00d00a78c680, 0x9c07ae04203d601b, 0x31000d68c500f600, 0x277])) else (if j < 147 then (cbits [0xc84c0cc6c0656629, 0xf4413bb61c01eca4, 0xd18a00f724a007b6, 0x7be63403d901201e, 0x14f99000f680300, 0x6807c494802a0326, 0x62601f298d00f906, 0x3e6]) else (cbits [0xf6c6600542658, 0x94003dc1980151a5, 0x580a406b80100548, 0x7d8328027818a01f, 0x1f90ca80fc46520, 0x9c254c34202a619b, 0x49609a70d680d386, 0x3f3]))))) else (if j < 155 then (if j < 151 then (if j < 149 then (cbits [0xe04fd52b407ea94e, 0xc4203f662081ef30, 0xf3d100fdd89c27ec, 0x7f325013f77ad09e, 0xd780204fe6ab80, 0x8407be62003ed013, 0x4a101f7a4b00fb8c, 0x34f]) else (if j < 150 then (cbits [0x384f7d870269e94e, 0x25003f07a209f731, 0x78d300fd004827e1, 0x7f064803ee19401a, 0x80d800200fc0c680, 0x2864920352249014, 0x19b01538ca809e46, 0x12a7]) else (cbits [0x80cc068205bc340, 0x35a03501a701fd8d, 0xb24c40f8125826a0, 0x7c0c3813f649901f, 0x1ff3d380ff1e882, 0xb6080125013fe7ad, 0x120a00557010064, 0x3fd]))) else (if j < 153 then (if j < 152 then (cbits [0x300ffcc9005c234c, 0x2901b1004017119, 0x5016d8940082448c, 0x552328027a18a093, 0x15b8ca80cb06520, 0x9806a2342130b19b, 0x1a701988d340ba06, 0x403]) else (cbits [0x281018c9026c835a, 0x93203e1496020919, 0x9b0f44f0587007ee, 0x7fcc4d0416624820, 0x20cbd10105d8b60, 0xb40837250041a7ad, 0x19e020fd57010764, 0x404])) else (if j < 154 then (cbits [0xa406c8010080a348, 0x3146253020912400, 0x68ca4101c63c04f6, 0x61833602b8195019, 0x9b28d380d486842, 0x9c08126360408310, 0x49901f124b01028c, 0x3f8]) else (cbits [0x3c102d87a2784c38, 0xf4e040f7a20206b1, 0x68d0010464a00820, 0x58e334040c626096, 0x89868cd81039e982, 0x50080a31c040e620, 0x1a02020d300aa86, 0x414])))) else (if j < 158 then (if j < 156 then (cbits [0x204b30680055c328, 0x1c041562c020599, 0x80ca04afc050055e, 0x81863c12c619a015, 0x1588ca04c386800, 0xc0081a64812b119a, 0x194020c3d605034c, 0x2b2]) else (if j < 157 then (cbits [0x201038c782564334, 0x64c02b331a0a0719, 0xa0ca0103d29005d8, 0x82063c130f19b015, 0x20e0090106189a0, 0xa805dc35802b531a, 0x32c015b18d01078c, 0x2ef]) else (cbits [0xa006cc0100822954, 0x3280425014821080, 0x78cd80ae8668084c, 0x6ac34e13051a1016, 0x21425080e20c940, 0x70085c94e04294a6, 0x7a2021831640f8d8, 0x13bc]))) else (if j < 160 then (if j < 159 then (cbits [0x7010c64a02826f59, 0x3602d000f015d80, 0x218800d5c084260c, 0x84692c042232681f, 0xa0a31344ef58700, 0x50057832804247a2, 0x401608ca00b006, 0x1b4]) else (cbits [0x84c2126c07ca620, 0xf4413be61c01aca5, 0x40d004c1c668084e, 0x58432801b5004098, 0x9848cd80b446540, 0x58085863e042a1a1, 0x62689dfb0e00f992, 0x1415])) else (if j < 161 then (cbits [0x7010ac678085af44, 0x63402c319402158c, 0xc0d000b246500590, 0x71463c03591a601a, 0x21100a010bcc900, 0x80084e634042419a, 0x1480db00200b38c, 0x224a]) else (cbits [0xa809f0628e4c604d, 0x342130a19b01690c, 0xa8d604d8469c06b4, 0x86635a03321ac817, 0x81f3a4b00e2cc7c0, 0xaa2780c3804304a4, 0x7a209ff316410d18, 0x435]))))))) else (if j < 189 then (if j < 175 then (if j < 168 then (if j < 165 then (if j < 163 then (cbits [0x7010da4a0083af59, 0x65802f832c021bd5, 0xd003c10e004805f2, 0x886025043b00c821, 0x822600fc11280660, 0x2a036e314044e025, 0x1a191260cdc07346, 0x124d]) else (if j < 164 then (cbits [0xd809f4c40e4d234f, 0x642033431b818818, 0xa99384cd4c862632, 0x700932137e32789b, 0x81e1b0e04e452940, 0x8607f2c3f03e861c, 0x6278218b12c10018, 0x435]) else (cbits [0x3c4fa5e8a2798f44, 0x25104509280a0fbd, 0xe810010f006c08a3, 0x88204e0440021021, 0x1e230e006e0c400, 0x28088525013cd7a2, 0x61c01e2a4b006e46, 0x43e]))) else (if j < 166 then (cbits [0xd810fc698087ef44, 0x4e0445021022200, 0x40cf8111c664088c, 0x78cc3801ba310022, 0x224c9404f39e880, 0x80088e330044b014, 0x198022680a00c452, 0x448]) else (if j < 167 then (cbits [0xc4510804a089e028, 0x33104421928a2480, 0xf24b006ecc400892, 0x62694e03134a1013, 0x9e3c9400f1de882, 0x4826d09580452018, 0x1a680de0c5011500, 0x624f]) else (cbits [0x304c6cc840628636, 0x932137732d01b319, 0x430e04e492ac0702, 0x79ef44041962681e, 0x22cc96850d9e9a2, 0x6c08aa02a1451aae, 0x18a022b813811580, 0x1bd])))) else (if j < 171 then (if j < 169 then (cbits [0x384f41870079292c, 0x241452928022c3d, 0x7a5200d9ccb008b0, 0x37c008045a4aa09c, 0x392a813589540820, 0x6c062c32a027f18a, 0x1a701b48d084c586, 0x1369]) else (if j < 170 then (cbits [0x680df46b206dc358, 0x648038d31e022e0d, 0x19958117cca8271a, 0x80293703ca496023, 0x8232255410692820, 0x9a2794c38041d4ac, 0x62c8a32315450698, 0x141d]) else (cbits [0x7051664a008b2f44, 0x354045d1a40232d5, 0xc010406fc01008bc, 0x5003147258026b12, 0x18b8ca8118063c0, 0x9c06d4342131719b, 0x315023098804da86, 0x462]))) else (if j < 173 then (if j < 172 then (cbits [0xe00f2d25828c4636, 0x250045a7a209e5b0, 0xe8d60117863828b5, 0x71c648031819a022, 0x1c8252011980480, 0x1e08d000913904aa, 0xd8250804c11d00, 0x4ab]) else (cbits [0xac52ac04e09a801f, 0x3704e20198a6a00, 0xb010c538807e0a2c, 0x39c315006a18a0a8, 0x99c98cac8e4c63e0, 0x40e872343643919b, 0x31382a618841490c, 0x57e])) else (if j < 174 then (cbits [0xfc16e4c6e0b3862b, 0x92c0618321830198, 0x1a4cc553125a2a48, 0xb72943161849b8b0, 0x8317b0e418b98702, 0x8a2c5cf440638621, 0x18a80358c5058bde, 0x6]) else (cbits [0xb051a4c6c08d262a, 0x93304704968236a4, 0x6b0e011cd26e08e4, 0xd8314147061c8a3, 0x235a4d811a8c400, 0x4008dc00d046c61c, 0x61c0a3624d801b4c, 0x46f]))))) else (if j < 182 then (if j < 178 then (if j < 176 then (cbits [0x11a926808e200c, 0x2a0161004023599, 0xa80d8121005608ea, 0x90a042148401b8a3, 0x8a428138123c0860, 0x660920327148f027, 0x31580e8188052406, 0x2394]) else (if j < 177 then (cbits [0x3d90e8c866728637, 0x92d04914963a1d19, 0xca4dc125d266092c, 0x93894f049a4a1824, 0x8a4b30e452458700, 0x882934c4f149c621, 0x928024fbd3c1275e, 0x149d]) else (cbits [0x5011dc04a08ec019, 0x636047831000e88c, 0xd993811e8c8408f2, 0x8fa936047c496023, 0x240253811f92840, 0xa00904f44048161c, 0x18a023f80f0120e4, 0x1d2]))) else (if j < 180 then (if j < 179 then (cbits [0x4121cc6a090c620, 0x9350488496023f19, 0x5313852012820912, 0x918f4e048b7a2024, 0x2468120123a4a00, 0x1a08ec0340477008, 0x19b00b10c5012480, 0x1481]) else (cbits [0xb0522069c090c342, 0xf44049361c00e9a4, 0xc0cd012564a00928, 0x8f20280498014023, 0x23e810051e40680, 0x98090e040047a014, 0x8024d8d2011f80, 0x47f])) else (if j < 181 then (cbits [0x60522409808f6028, 0x336016318a024001, 0x70d38520c6840904, 0x928c3801d44960a4, 0x24f49405255e880, 0xb0291404c048a020, 0x802500d5012300, 0x48d]) else (cbits [0xac075c62a03aa314, 0x92c339519b91ca8c, 0x4a4cc129925a0944, 0x944c3804aa49b825, 0x8251803452998722, 0x7003ac62004a4012, 0x120253803012958, 0x4a8])))) else (if j < 185 then (if j < 183 then (cbits [0x812cc06c095801e, 0x31b04bf027025c01, 0xc188401d4c400920, 0x73c62b239731480e, 0xb225190ccebcc6e4, 0x84098692c744e327, 0x61c0265250c13152, 0x4cb]) else (if j < 184 then (cbits [0x10133d89e099cc43, 0x25004d27a782683d, 0x69880076462809a7, 0x95e94204ae496025, 0x258bd1012c18700, 0x3a00ec31404b2928, 0x62119d80ca48e646, 0x4b4]) else (cbits [0x4012d9e88096ac4e, 0x31d007718a025bc9, 0xc9881912c66a4730, 0x96894104ba496025, 0x25e3d1012ed89c0, 0x28097d25004bd7a7, 0x1a091cd0c7401e06, 0x744f]))) else (if j < 187 then (if j < 186 then (cbits [0xe012d529a098092c, 0xc4d04c26208260b0, 0xc8d0812b8654097a, 0x988f440079496025, 0x803d188012bc03c0, 0x9c098c92c631131a, 0x92802643d10131d8, 0x4c9]) else (cbits [0x3812e8684096032a, 0x935007b49602600d, 0x63d1013198844738, 0x96804c04cd928026, 0x2588ca812d40b00, 0x58098234e04b61a1, 0x61c11cda4d401f12, 0x4c4])) else (if j < 188 then (cbits [0x13464a00998f44, 0x5804c2026025d81, 0x90ca8131d280097a, 0x97c34e04b71a1025, 0x11cea4d401f52580, 0xa0099af4404c9627, 0x18a803f0c5013464, 0x1da]) else (cbits [0x80cec466e473e31f, 0x63304d8310826a98, 0xe30e0136cc6e09b2, 0x9ac02504df61c826, 0x26bb0e00200c400, 0x6009b4940246e018, 0x18826e80341368c, 0x4de])))))) else (if j < 203 then (if j < 196 then (if j < 192 then (if j < 190 then (cbits [0x30135d2580102620, 0x1e04e1018027000, 0x780d813a005409c6, 0xa0c04e04f3026027, 0x80ee18840208c400, 0x82676663723aa315, 0x4963a26193d90ecc, 0x50c]) else (if j < 191 then (cbits [0x3c144126e0a1e92d, 0xc4f051261c0288a5, 0xe8c5014564a00a28, 0x9ca92c04e431000e, 0x273c94013998700, 0x82475631d008318a, 0x4960274988190f06, 0x4ea]) else (cbits [0xe013b129c09d6936, 0x31404ee9280276b0, 0x8d04ced06520108, 0x9d663504f0310322, 0x279494013c589c0, 0x3e03bc315008518a, 0x19a99da8cac8eb06, 0x643d]))) else (if j < 194 then (if j < 193 then (cbits [0x8013dc68609e833f, 0x62b04fd310827d18, 0x190c13fcc7e09fc, 0xa069430501496028, 0x282bd141411e880, 0x9009ec33404f5194, 0x310027c992013e00, 0x86]) else (cbits [0x1013ed258c78a635, 0x6350087310027e3d, 0x13d1013ed258c87e, 0x87c6410088310028, 0x28130e013f1258c, 0x82c880335008918a, 0x32082839881d1346, 0x508])) else (if j < 195 then (cbits [0x4142525809d864d, 0x25004f14a6828525, 0x80cd813946540a17, 0xa0e34e04fa1a6027, 0x31e2250402292580, 0x980a1d250050d61c, 0x1ac02748cd013ecc, 0x4fd]) else (cbits [0x3013f80b009d6040, 0x32a04ec02c028401, 0x8d3013b466c09cc, 0x11692c05091a7028, 0x286b0e191092820, 0xb00a1404c0513928, 0x19b02738ca813c40, 0x4ee])))) else (if j < 199 then (if j < 197 then (cbits [0x34023125809e4342, 0xf44050e61c41e6a5, 0xf8c5402346280a26, 0x76c32b23ad18f80e, 0x828d9884145cc406, 0x580a3c62b051d313, 0x1e829124b4147d2, 0x518]) else (if j < 198 then (cbits [0xf01465258011e620, 0x3c051c024028d00, 0x81880148407a0a40, 0x1226200519496004, 0x8291812014692580, 0x360a4a00f246d004, 0x139251007c92440, 0x250c]) else (cbits [0xdd132c0664a2e02b, 0x43451201fa26e00, 0x88c6c11b462a8a3e, 0x99632704a218f824, 0x82860ccc53706562, 0x862a2433f051719b, 0x31080491880547c6, 0x1e1]))) else (if j < 201 then (if j < 200 then (cbits [0xd8f0cc6e678662b, 0x92d052b4963a2819, 0xda4dc14d52660a60, 0xa56c3805424a1829, 0x12a1310c94c18724, 0x100a96f45054a7a2, 0x150249009811a80, 0x526]) else (cbits [0x38949c0840a4e036, 0x32a246e18a029401, 0x7188113746844946, 0x9ba63604a3315023, 0x294b0e0024d2582, 0x360a5525025297a2, 0x199a4a009c54a40, 0x5513])) else (if j < 202 then (cbits [0x9c14a4636a99a03f, 0x33f44cd199924a0c, 0x9989c11bcc428a26, 0xa1a63304a5315824, 0x8a8698fc1464c6e0, 0x5a012892c1519321, 0x4a1b1e3a4dc07892, 0x73c7]) else (cbits [0xc14b98720a58c38, 0xf45152c7a20297b1, 0x6bd1002558702a5c, 0x9ae635053100d029, 0x1939a4d402592582, 0x880a66c4e0532621, 0x310029a494094b9e, 0x97]))))) else (if j < 210 then (if j < 206 then (if j < 204 then (cbits [0x3814dd2980a6c629, 0x620053a928029ca5, 0xe00f414e1e880130, 0x132620253c19e829, 0xc1af98d54d7cc520, 0x700a6492c053d31e, 0x7a7029fbd1094c98, 0x540]) else (if j < 205 then (cbits [0x2414f8c980a83250, 0x34914c619282a181, 0x98a40268c400a88, 0xa8a6497313320a98, 0x9297b0e014cd2580, 0x880a80c4d0547620, 0x32002a4c9401521e, 0x546]) else (cbits [0xfdd344066e93c027, 0x327052a18dca6880, 0x60cfc9438666492a, 0x9986330495313a26, 0x804da4b01438c7e2, 0x86677293701e3496, 0x61c8a9630e18ee52, 0x534]))) else (if j < 208 then (if j < 207 then (cbits [0x1015058860a74c3f, 0x92c25347a2a2963d, 0x730e1c9f929a0138, 0xa5cf4405486268a9, 0x82a680389521e9a8, 0x3c0aaa01b0554007, 0x18a82ad00fc15580, 0x470]) else (cbits [0x94129863e092c31b, 0x32b04d519482618c, 0x78cfc537c66e09b0, 0xa4434f051b1a1828, 0x80f218840274c402, 0x6e450a62b226f314, 0x327b1f4190ccf20c, 0x7451])) else (if j < 209 then (cbits [0x8158126c0ab6932, 0x94a056e4a182b2a5, 0x830e015d129c0ade, 0xaecc4f05756218a9, 0x82bcbd1415e1e880, 0x6c0afb250057b7a7, 0x2702a7810815380, 0x550]) else (cbits [0xd8129c63c08e2314, 0x629009e3100a700c, 0x8a508135925844e0, 0xaa4f44153161c02a, 0x2ab8064154e4a00, 0x880ab0942200f18a, 0x194223600d01565e, 0x55c])))) else (if j < 213 then (if j < 211 then (cbits [0x81574c52013e620, 0x314055f7a202af25, 0x498a40284c400140, 0xac4c4e056162119a, 0x2b24940158de880, 0x7a0ab001e0551007, 0x31a8051188015986, 0x62a3]) else (if j < 212 then (cbits [0x454cd2580ace63d, 0xc4e056a61c02b0a5, 0x63d3894c5e880ad6, 0xad0634056d92802b, 0x8051988015a4c980, 0x840ae29400570314, 0x31032afbd1015cd2, 0xa4]) else (cbits [0x40294c400ae4c38, 0x94d153249649b419, 0x63135958d8700ac4, 0xaee05405614a602b, 0xb2a9003415892b00, 0x540aa431a64c4018, 0x496026218c415646, 0xa6]))) else (if j < 215 then (if j < 214 then (cbits [0x8157d87c44e4935, 0xc4e655f62502b1b1, 0xa494054d1e88cac6, 0xad4c4c057a006429, 0x2b5a50015f00a80, 0x580aa631a056c4ac, 0x621113a24d4029d2, 0x564]) else (cbits [0x40d4b9e880adac4e, 0xf0472004c29a49, 0xf807012a4026092e, 0xb0401f058000f02b, 0x8a6c80dc13640560, 0x282a3a04f051d021, 0x18e80f28c5402a06, 0x583])) else (if j < 216 then (cbits [0xdc8d086560b1231f, 0x34f64311a199a10c, 0x699081628c40e862, 0xab692c158d32702c, 0xac8a4d8164526a0, 0x700b3294305934a1, 0x6278ac9b138556d8, 0x1599]) else (cbits [0x40166de9e0b34f44, 0x900a90040acd49, 0x180ac8d0c02603cc, 0xab892c055c18a19a, 0x82c0804402a80102, 0x8403ce3140584012, 0x3103a120d3990906, 0x55d]))))))))) else (if j < 326 then (if j < 271 then (if j < 244 then (if j < 230 then (if j < 223 then (if j < 220 then (if j < 218 then (cbits [0x85614c6c0b0a635, 0xc38058749602c319, 0x43d10561989c2aba, 0x580334158892802c, 0x2c580301604038c, 0x280156620058c007, 0x19a80568c5002b06, 0x6427]) else (if j < 219 then (cbits [0x38163989c0abc620, 0x29059092802c7bd, 0x28c7402b862809b4, 0xb24f44233f19482c, 0x82c30c7402bc6280, 0x9c0b2894e62ce19a, 0x92802cbbd1016598, 0x598]) else (cbits [0x8016552800b2a940, 0x94e0588314805818, 0x93104157d8702b20, 0xa7525015987a702c, 0xac719301638c810, 0x980b2c940058f32c, 0x78239802456598, 0x499]))) else (if j < 221 then (cbits [0xac136c03e0954013, 0x37059d0188a6d80, 0xf010c144007e0b40, 0xa3c04f1510025828, 0x80f40c5402c46282, 0x5246f631f234618e, 0x19899bd8caccd186, 0x5a1]) else (if j < 222 then (cbits [0x3d90d46860b4e337, 0x62505603103a1a8d, 0x4190c5644c4c0b22, 0xac092c05aa32782d, 0xad4253c56a92862, 0x860b5cc4205ab61c, 0x6278ad7313816d18, 0x15b4]) else (cbits [0x3c16dde8a0b6af44, 0x25115b592802dc3d, 0xf013816780842b6f, 0x68e62900b23100ac, 0x2cfbd10cd1cc6a4, 0x840b44340159f928, 0x1a70ad10d3016946, 0x15a5])))) else (if j < 226 then (if j < 224 then (cbits [0xe0569a4a00b4cf44, 0x64c05a47a202d1b0, 0x4b16016a58982b48, 0x16862005ac0070ad, 0x19a518d48d28c520, 0x7a2b5b25005ad7a2, 0x18e805a8c5016bc0, 0x42f7]) else (if j < 225 then (cbits [0x818be066a6696329, 0xc38156249602b098, 0x93d3816c5e880b60, 0xb6c03d05b392802d, 0x805b1880167c67a0, 0x7a66986352348314, 0x49882b1a4b01698c, 0x592]) else (cbits [0x3816b5e882ac8c38, 0xf4c85419280ad9bd, 0xd003c16c98b00b60, 0x99401b04c500c824, 0x82dd00f4533c04e0, 0x282a2804b05bf01f, 0x18e80f48c5402dc6, 0x42fd]))) else (if j < 228 then (if j < 227 then (cbits [0xd4cf28656866631f, 0x33d633419bb1880c, 0x80d0c173067e0b80, 0xaca620941f1a782e, 0x82c9989815b8c420, 0x960b5062b0599313, 0x49602ea993c1750c, 0x1542]) else (cbits [0xdc175d2622aec92d, 0x93f05df49e82ef24, 0x2a50c16b92820bc6, 0xbd4c3805e64a782f, 0x2f9313c17b189c0, 0x960bf0f4505f37a2, 0x7a782fdbd3817e5e, 0x5ff])) else (if j < 229 then (cbits [0x2018064a20c01250, 0x4e05bc01b02dd80, 0xc1880126c6340b7a, 0x62464142ff314805, 0xaa230e01599258c, 0x6c0b8233405be928, 0x1a702e30d3017146, 0x5c9]) else (cbits [0xb18c84c84864062a, 0xf44154561c02b3a4, 0x41880172e4a00b94, 0xb86c3805c249602b, 0x2b498801711e880, 0x880b8ec381546496, 0x32602e199001721e, 0x5c7]))))) else (if j < 237 then (if j < 233 then (if j < 231 then (cbits [0x6017346680b88640, 0x640429631402e70d, 0x88120173cc98c52e, 0xba494805cf19e02e, 0x2eb3d60174e4a80, 0x52859631d00ba18a, 0x4a702eca53017606, 0x5dc]) else (if j < 232 then (cbits [0x7256624a00bbaf44, 0x31d00bb18a215f0c, 0xdbd101769870858a, 0xb52f4c05da62602e, 0x2f00ca402f06280, 0x980bc525005e1627, 0x31202f224f017918, 0x594]) else (cbits [0x3017852782bc2654, 0xf5805e97aa02f3b1, 0x430f01654c480b64, 0x17a62005e862602f, 0x2e518f50a88c520, 0x822a90c38056a496, 0x7a732a93d1016c18, 0x5eb]))) else (if j < 235 then (if j < 234 then (cbits [0x50131c0332adb250, 0x34142ad18e805f0c, 0xb189815acc41256c, 0xa8e92c05ed32502c, 0x82f730e0179d2822, 0xa00be0f4405ef61e, 0x702eb3d6017c64, 0x5f4]) else (cbits [0x9417d809c0bea036, 0x62900bf31002640c, 0x8a4b18b64c8285b0, 0xa92c380597499129, 0x32a93d10177587a2, 0xb00bef25005ee7a7, 0x2482fd496017bd8, 0x5fc])) else (if j < 236 then (cbits [0xd50bac63a0180314, 0x62092ef1a0b1710c, 0x9253455012580ad8, 0xbfaf4405eb61c02d, 0x82fd3d2017fa4a00, 0x4b2b7c04994c901e, 0x31002df0d2413246, 0xc1]) else (cbits [0x258c00c828600629, 0x932056d49602e599, 0xc30f4d4bd8700b30, 0xb66c4d05e2624cac, 0x2fbc94255b5e880, 0xb00be0f580602024, 0x18a80610c5017f64, 0x1eb])))) else (if j < 240 then (if j < 238 then (cbits [0xdd0d106560c0831d, 0x63663f91a199de0c, 0x899081824c800c0e, 0xba8943056f496030, 0x8a9ab0e0185529a0, 0x882baec4d0616621, 0x18a030bbd159669e, 0x1ec]) else (if j < 239 then (cbits [0x3415c0c40677a336, 0xc380606496030299, 0x43d10576189a2a6c, 0x77c32900c318a32c, 0x42c83d1018218846, 0x3e03da31500c418a, 0x19999df8cad0ce86, 0x60a]) else (cbits [0xb015c4c400c18337, 0x941060e49b8a9ba4, 0x830e4183d8702bb2, 0xc1a03c060b19a030, 0x2b924b00314c400, 0x282bb6c41153861c, 0x31031f80cd403186, 0x573]))) else (if j < 242 then (if j < 241 then (cbits [0x4184926a2a7292c, 0xc3815dc4a6830425, 0x38c501851e880c26, 0x680329060518e806, 0x30919019649e888, 0x1e0c2694c0608326, 0x198a67009c12700, 0x511]) else (cbits [0x5403206280c32049, 0x31f435b18e80f70c, 0xcdccf0065686f8, 0x6fc34393751a0b20, 0x3118d3c18706932, 0x6e0b5462b0574310, 0x496030a98f41754c, 0x153b])) else (if j < 243 then (cbits [0xdc58592662aea92d, 0x94915de4a1831224, 0x3a53c56b929a0c4a, 0xc50c3965b561c031, 0x82fdb13418a58860, 0xa00c56f44062a627, 0x21030d00d818b24, 0x61b]) else (cbits [0x350d70c520192620, 0xf44353c61c49bb19, 0xf8cd81874668cb6c, 0xc4434206201a0030, 0x32d33d1054f58700, 0x590b48c38061e496, 0x7ac0310b0e054f92, 0x5b2])))))) else (if j < 257 then (if j < 250 then (if j < 247 then (if j < 245 then (cbits [0x6018986520196314, 0x62005d692c02f5bd, 0x930e10d74c520198, 0xac8f4415b06269a9, 0x316803817f5e9b0, 0x9a86bc62900cd310, 0x7a20a9fb0e24db4c, 0x65ad]) else (if j < 246 then (cbits [0xcd934004ec93a01b, 0x31b84d301fc28a80, 0x98ccc134064e093a, 0x19c620151519f8a6, 0x91dc18ac07bcc420, 0x59279864333cc31b, 0x49982bc24b494ad2, 0x59a]) else (cbits [0xd966927e0b6a937, 0xc39154a61c32daa5, 0x53d1058018862afa, 0x19e620857d7a2c2a, 0x91dd18ac07c0c420, 0x9ec4fa64133cf31b, 0x496929824b24fa4c, 0x579]))) else (if j < 248 then (cbits [0x2c17a92820b6e937, 0xc3806284a7830ba5, 0xb13c58ad8822a96, 0xafb25006307a70b0, 0x8068188018da4a32, 0x580c6264992a4320, 0x4a6831a252494cd2, 0x5eb]) else (if j < 249 then (cbits [0x3457c18826a90c38, 0x25006357a20afeb1, 0x9990018c8c690aa7, 0xc6b2580637006031, 0x8269006c127c01e0, 0x960c7204914d2013, 0x18a80688c5018f00, 0x1f1]) else (cbits [0xd4cf04656478231f, 0x341833519bc18c8c, 0xe8d264cd46872632, 0xc8834f06411a5831, 0x82bd98849508c400, 0x6a0b7062b059b313, 0x32182f918dc17b0c, 0x629])))) else (if j < 253 then (if j < 251 then (cbits [0x341924c960c8e649, 0x92c064b32782fd99, 0x4a4dc55ed25a6a84, 0xbe494315ec4a08b1, 0x8b24a52c591d2922, 0x702c9694f15fb4a6, 0x9280b183d1018c18, 0x64c]) else (if j < 252 then (cbits [0xa818e80100c9f251, 0x31a163b01b031d80, 0xd19040348c400940, 0xa8692c931a326c18, 0x31f0ca0d50d8704, 0x6c2c7c3340640195, 0x3274191190859006, 0x9322]) else (cbits [0x10d5158704a8a92c, 0x62016319280318bd, 0x930e0d5192580c7e, 0xc8432816337a2031, 0x414c190059086680, 0xa80c866589298326, 0x32a03218d2019140, 0x646]))) else (if j < 255 then (if j < 254 then (cbits [0x7403506282c8c954, 0x94006347a203240c, 0x5192019292b00bda, 0xc9c02a064d007032, 0x806a9880593806c0, 0x5925b464d82da320, 0x61c02f8a50495252, 0x3549]) else (cbits [0x42154de882be2c4d, 0x120651007caa9c9, 0x100cc198804e0cb0, 0x3e631500d618a0b3, 0x81408c7c09ac63a0, 0x8667a233723d1195, 0x3153a298d3d914c6, 0x668])) else (if j < 256 then (cbits [0xdc59a0c6c0d4c62b, 0x64206af31f0b5318, 0x119385abcc940d84, 0xd9a92d254c4960b6, 0x836fa4dc1b452660, 0x700df094f06e94a1, 0x6218b66b0e4d5318, 0x16f8]) else (cbits [0x3d98bde882dd2c4f, 0x8762f9280380bd, 0x90108194806c02c8, 0xcac33e06561990b2, 0x32ba4d807d0c402, 0x884aaac3816574a1, 0x1803298090d555e, 0x654]))))) else (if j < 264 then (if j < 260 then (if j < 258 then (cbits [0xd019500200caa628, 0x80655014032980, 0x900ac0544012001a, 0xcb262a33d201b91e, 0x92ab24b05964c6c0, 0x6e0cbe933065d496, 0x61c9aab30e019852, 0x165d]) else (if j < 259 then (cbits [0x988a7803a001c008, 0x92c065b310032d0c, 0xc30e0197126c094e, 0xcb6934065e00c1aa, 0x32e19001980c500, 0x8408d2028066300f, 0x310032b0c6819900, 0xd8]) else (cbits [0x88f4cc6a04d8629, 0xf44066761c033325, 0x599001994c686ab4, 0x8d6040066501a023, 0x32b803c11a86680, 0x282ccc0330659009, 0x18e80fa8c5403646, 0x229d]))) else (if j < 262 then (if j < 261 then (cbits [0x9c19a464a465431f, 0x337067b195833b0c, 0xc8d3d906468667c2, 0xd00621067d3103a2, 0x34118dc1a04c660, 0x9e0d106430683321, 0x49682a6a4b01a28c, 0x68b]) else (cbits [0xd81a3d2660d18932, 0x942069349b8348a4, 0xc25381a5d2860d28, 0xacac3806994a7834, 0x834eb10c1a698726, 0x9ecbd4f44069e627, 0x19a3b1849401a89e, 0x66a])) else (if j < 263 then (cbits [0x819b86800cda336, 0x34e06711a603380d, 0xaa4b08c7cc540ce8, 0xb94f44356761c033, 0x3359881d8c64a0c, 0x88cb8ec38066c496, 0x49613359881d8c9e, 0x3569]) else (cbits [0x81d8cde880cdec38, 0xc383568496033918, 0x598d019cde88cb86, 0xce464c266b320033, 0x33c0d3019dc6800, 0x68452062806791ac, 0x192119580c019e8c, 0x67a])))) else (if j < 267 then (if j < 265 then (cbits [0x78996c03c0cf8c3c, 0x62500db310032d8c, 0xf24d813592580cea, 0xcfe94e267e4a1033, 0x32b53d10d5a98700, 0x7c08d69407635928, 0x19a806e0c501a100, 0x62b3]) else (if j < 266 then (cbits [0x38d5ad2580aa2620, 0x25006877a20342b1, 0x481201a18c912be1, 0xd1a32900dd18a034, 0x3b1a49401a3989c0, 0x280cb80120690620, 0x19491500c7403786, 0x32a0]) else (cbits [0xe059f92580cfc620, 0xc4e069262102d630, 0x5c94197ade882d24, 0xd2a03e06904983af, 0x914f8c74037c6280, 0x584cfc62062ec19a, 0x7a203492504d5b12, 0x5f4]))) else (if j < 269 then (if j < 268 then (cbits [0x2257f64a00d2cf4e, 0x31d00e018a034481, 0xf9881cd9c6824542, 0xd2494d3561496033, 0x34b313596c18702, 0x600d3600c062d928, 0x4a60b3f31001a700, 0x692]) else (cbits [0xc01a80ca80d3e054, 0x95806a14aa034724, 0x299001a8c0a82d24, 0xd4a95406a432a034, 0x34319001a592b00, 0x52050431d00e118a, 0x32103538cc48a946, 0x6ab])) else (if j < 270 then (cbits [0xf81ab18704d0092c, 0xf4406ae6210356b0, 0x48d301aa06806adc, 0x50662806aa1ac035, 0x80710c5011ad2800, 0x560d6031d01f718a, 0x31419f18cdc8f786, 0x6b2]) else (cbits [0xb01afcc6c0d7462a, 0x93706c049692ada4, 0xc0c50d5bd8700d82, 0xd6262033e419b00f, 0x1ab830e095752580, 0x3603f231500e318a, 0x195835b0c7c1acc6, 0x33e6]))))))) else (if j < 298 then (if j < 284 then (if j < 277 then (if j < 274 then (if j < 272 then (cbits [0xac1ae0c420d6e620, 0x3343571496035c98, 0xd00901ad46980d68, 0xae492c00e431011e, 0x11ef8c7403946286, 0x580d7863606bb310, 0x61c035f24d81af52, 0x3573]) else (if j < 273 then (cbits [0x80cf9465201cc314, 0x93406be31a92af18, 0xf19001af0c500d76, 0x3f431500e718a035, 0x99f38cac8f8063e0, 0x41286c34f636619a, 0x313836198849580c, 0x6c4]) else (cbits [0x3c1a50c820d8c62b, 0x92d3574496036399, 0x4a53c5a612820d90, 0xc5725006cb7a7036, 0x362993099f92992, 0x980d2cf580692626, 0x7ac0365015059fd8, 0x1696]))) else (if j < 275 then (cbits [0xd403a06280d9804a, 0x62092f91a0c17c8c, 0x124b01a58c9a4ac4, 0xc9b25016964a69ab, 0x135600341b380180, 0x4a4cba01e06ac007, 0x198832e8c78999c0, 0x667]) else (if j < 276 then (cbits [0xd409d4c5201d2620, 0x935067d49a113a98, 0xd25081a0126c4d00, 0xd8694e06c04a50b4, 0x136030f85b212b40, 0xb48d34c4e26c3621, 0x9281abcbd111b218, 0x6579]) else (cbits [0x81b3c06cec6d55c, 0x31406d0027136781, 0xb0ca409d863a01d4, 0xd36636246e310113, 0x234da50811b92582, 0xa0caf4f44357a61c, 0x15032f8049d8de4, 0x6d2])))) else (if j < 280 then (if j < 278 then (cbits [0xa409e063a01d6314, 0x62906d6314036a0c, 0x98d81b64c540db0, 0xd8864e1681321034, 0x36d24b05b10cb40, 0x702db895a06dc4a7, 0x621036eb1049b018, 0x16dd]) else (if j < 279 then (cbits [0x68db01e880dbcc4e, 0x55c66179280b6f3d, 0xa80c01b4c638ec2f, 0x1d83140660009036, 0x36b99089aecc400, 0x702d8a94e06c54a1, 0x7a20b6bb138daed8, 0x6613]) else (cbits [0x301b4c038ec27250, 0x62806c5326036d80, 0xf419840240dae, 0x4f231d00ed18a037, 0x99a68cd48d346520, 0x6c0d0462a06e119e, 0x320834899005a08c, 0x6ae]))) else (if j < 282 then (if j < 281 then (cbits [0x381b04c940dc8642, 0x65a16c132b036319, 0xea4c49b0d2582d8c, 0xd86c3816dd499036, 0x373bd381b95e886, 0xb8cc5125016e77ad, 0x194023580a1d8a2a, 0x6e2]) else (cbits [0x305b8c6b00dc634c, 0x64c06e8024037300, 0x681281ba80900d24, 0x4f431d00ee18a037, 0xb18a0d050c086520, 0x540d0662806ee1a4, 0x3260b4f18d81a20c, 0x694])) else (if j < 283 then (cbits [0xb05b24cb40de464e, 0xc3806de499234d24, 0x3b1341bcd8926af6, 0xdeb25006f47ad037, 0x4b00d5701bda4b40, 0x6c0d2a01d46cf004, 0x18a037601381bac0, 0xef]) else (cbits [0xa98c546828608329, 0x64e169f31b034498, 0xe30e11a712582d94, 0xd0862896029281ab, 0x3778ca01a54c980, 0x780de235806f01a0, 0x3140b5019001a540, 0x685]))))) else (if j < 291 then (if j < 287 then (if j < 285 then (cbits [0xd016ec0504dcc00c, 0x65806f702a0343a4, 0xe0c7403c06280d2c, 0x6ee34d4360194813, 0x34518a81be46ab2, 0xb00d8e642169d31b, 0x496037e99681a60c, 0x46c8]) else (if j < 286 then (cbits [0x641bf98aa6aeac38, 0xf5965b77a20b73b1, 0xd0ca01bfeab80dec, 0xdf834c06fb1a0037, 0x38101501c000180, 0x3a01e2314070402b, 0x1a6c18d8d0409fc6, 0x931b]) else (cbits [0xd81a88c540e0a355, 0x65a06cb32c0b5118, 0xa250495d92580e10, 0xdec95907094aa837, 0x8b7a3134d5d98700, 0xb82decc59170962a, 0xec36800201c2aa, 0x6cc]))) else (if j < 289 then (if j < 288 then (cbits [0x505c0c06c0e0602a, 0x34d831c1a080790c, 0x198d81a8cc552638, 0xaeec3825774960b5, 0x3830ca01b30cb06, 0x902e0e340070719a, 0x6035218d01b300, 0x8700]) else (cbits [0x2403cc0100c74028, 0x13028600880fd80, 0xe807c8a1803a063a, 0xec2027070c012918, 0x9a0100dc1ea00560, 0x28e8b604f6402021, 0x19b03530c5419a06, 0x7c1])) else (if j < 290 then (cbits [0xc206467e1018337, 0x34b08261a5040f8d, 0x41880218069e10ac, 0x3263326a6310933, 0x93e09908a07cc6e5, 0x96504c64a280c321, 0x4961430193ca158c, 0x867]) else (cbits [0xcc2251264111092d, 0x93708b649b044d24, 0xd24fca25127c1192, 0x19294328b64a1144, 0x46fa52c23552945, 0x7011f894f08eb4a7, 0x61f9b74b0e4d6e58, 0x900])))) else (if j < 294 then (if j < 292 then (cbits [0x10246189e121cc43, 0xf4f66e97a2b2dcbd, 0xc945d8e24a05230, 0xe52036070d01a3b8, 0x139481089c340800, 0x3c0e8c04e0735026, 0x310118f0ca80c786, 0x669]) else (if j < 293 then (cbits [0xdc1d34c560d4e621, 0x643074f31f83a718, 0xb993c1d4cc960ea4, 0xd4e92d266949603a, 0x93a924dc9d3d2664, 0x9e4ea694b274e4a1, 0x61c9ae030e09d5d2, 0x36ee]) else (cbits [0x3c1d6d8860eb0c3f, 0xf4565c07a203ae31, 0xec9409d71e9ecddc, 0xcd43147705928bb1, 0x9a028c7c1aa062a0, 0x660e1e32b070e193, 0x19f83890cdc1c406, 0x713]))) else (if j < 296 then (if j < 295 then (cbits [0x8499b8c400e2a343, 0x62b0716313935498, 0xc98fc1c60c6e0e2e, 0xe3a92c071c321838, 0x838fa4cc1c7925a0, 0x860e4493f072149b, 0x61cb2e330e01c8d2, 0x66f1]) else (cbits [0x15d8f9e880e4cc43, 0x33407110083b83bd, 0xd99001c680380e28, 0xcde92c066c310038, 0x3b1fbd1197218704, 0x900e4834807204a6, 0x32403938d201c94c, 0x728])) else (if j < 297 then (cbits [0x80cbc86520cda314, 0x629072a312933818, 0x7a4b01cacc6a66aa, 0xe5c942072c49f1b7, 0x39930e01cbd29c0, 0x880e68c4e0733621, 0x4a63b2049419725e, 0x72d]) else (cbits [0x501cc4c900e60348, 0x31f06aa18a83388c, 0xb8ccc1cd8656e8bc, 0xe7433f073919b839, 0x933898801cf06860, 0x564e6e62726aa310, 0x31f939b18dc9ce4c, 0x273a])))))) else (if j < 312 then (if j < 305 then (if j < 301 then (if j < 299 then (cbits [0xb4d7052584e78643, 0x937073d4999b7824, 0xa50c1d0127e0e7e, 0xde0c3965c161c03a, 0x13a0b10c9d0187ec, 0x200e8af4507447a2, 0x4a6039d8cd01ce00, 0x73e]) else (if j < 300 then (cbits [0x801d0cc900e84348, 0xc382673496033998, 0xa0c519709e886b84, 0x6e8341074719e833, 0x93a398f499d0c40e, 0x826b8a92c9374320, 0x61c039a25341d252, 0x65c5]) else (cbits [0x109cd189a4e92c41, 0x334074c9283b833d, 0x599201d286900e90, 0x80a04c340502003a, 0x197900d1d1780b0c, 0x380e6c0582718026, 0x26038801001d400, 0x272a]))) else (if j < 303 then (if j < 302 then (cbits [0xd01d446380e6e058, 0x340738026038880, 0x581318d540800e24, 0xea801c073902c139, 0x138c81301c4c0800, 0x800eaa31c074702c, 0x20038a18d01d58c, 0x271a]) else (cbits [0x309c6c0800e28034, 0x40071501a03a401, 0xc80d1cdd00984e38, 0xe5804c072c02003a, 0x3ad31601cf40b04, 0x800e5a034073e626, 0x1a039f01309cb40, 0x72e])) else (if j < 304 then (cbits [0x601ccc0984e5c040, 0x40072f01a039f81, 0xa01601d240984e4c, 0xebe954075d32a039, 0x39800d01d780380, 0x500e9404c2728020, 0x20039880d01d800, 0x2727]) else (cbits [0x741d880100e9604c, 0x40276501483b280, 0x81081df00820ed2, 0xef804d276902603c, 0x83c281609e0409c4, 0x280f2405a079002c, 0x18e81438c7008046, 0x299])))) else (if j < 308 then (if j < 306 then (cbits [0xa48a1c650064631e, 0x3342323195114c8c, 0xd8cd81e6066a0f2e, 0xf38642067631003c, 0x133b24b01e74cac0, 0x704f3a956279c4a7, 0x62103d130f81e858, 0x7a4]) else (if j < 307 then (cbits [0x589e9189c4f44c4a, 0xf4407a762d03d2b1, 0xd57197324a06b98, 0x51031c00080183b2, 0x3b18cd08a206500, 0x980ecc0400764012, 0x19403b401601d9c0, 0x2289]) else (cbits [0x440808010451401c, 0x29229b00e814d00, 0x70cd819dc6280ed4, 0xcf0620076f1a503b, 0x3b919281dc4c844, 0x6c680e9320775496, 0x4a103bb24f8cba92, 0x778]))) else (if j < 310 then (if j < 309 then (cbits [0xe01de929c0ef294a, 0x25065ce7a203bdb0, 0x624f01dad260ec85, 0xee0334076d4a403b, 0x3ba19001dcc0380, 0x500ecc01c0777014, 0x2c03be81309d9c0, 0x77f]) else (cbits [0xd08a34650051631c, 0x1c028c00803c00c, 0x700701df80504518, 0xf04334077e020114, 0x197524d01e0d2600, 0x220406008078449e, 0x14914e00740a700, 0x786])) else (if j < 311 then (cbits [0x281e2466c0cf2314, 0x642267931003c50d, 0x624b09e28c944f12, 0xf1c936078d49903c, 0x13c725089e3527c0, 0x70e6e094e74604a5, 0x92832e6bd10d7358, 0x78f]) else (cbits [0x209e1d2780f0e930, 0x1c078b19a03c425, 0xf81009da00500ed0, 0x51e31c277f02603b, 0x3c88cd08a3c6500, 0x904f2664807931a4, 0x4aa39b825301e552, 0x796]))))) else (if j < 319 then (if j < 315 then (if j < 313 then (cbits [0xd41d8c0100f28334, 0x4d278002083c000, 0xd188019e86280f22, 0xb9ef4435cf61c133, 0x3b50101d90e4a0c, 0x780f0c058276a026, 0x62a13ccb1201e658, 0x79a]) else (if j < 314 then (cbits [0x309db00800ed6034, 0x40078801a03c381, 0x100d09db40980eda, 0xf12058277102603c, 0x3cf00708a446380, 0xb04ee404c076f020, 0x19403cf8c701e4c0, 0x2292]) else (cbits [0xd08a4c0380f40640, 0x34277302003b80c, 0xa01309dd00800ee0, 0xeea340229418e03c, 0x3c60d609dd46980, 0x68452a6340295314, 0x2603c181001e100, 0x2776]))) else (if j < 317 then (if j < 316 then (cbits [0x1e8c6680f1a058, 0x4c32ea01a13bb81, 0xb00d01e380b04ef0, 0xef204c077902003c, 0x3d30cd01e540b04, 0x984ef4040077a01a, 0x1201020021cdc00, 0x797]) else (cbits [0x501e6c04c0f30025, 0x35607a91a1033d8c, 0x4993899ecc400f5c, 0xf6292c27ae32b13d, 0x3db25081ed127c0, 0xac4f6c94e27b44a5, 0x61e03de25681ee92, 0x7bf])) else (if j < 318 then (cbits [0x101f018a84f7ec48, 0x55c65d09281ae83d, 0x625201ea8c60ec89, 0xf5694807ad4aa03d, 0x3d78d001eacc600, 0x900f64c3c07b061e, 0x1a003d9b1509ec98, 0x7aa]) else (cbits [0xf01eac6800f6ac54, 0x95407b84a403db80, 0xdb1201eed8780f72, 0xf7c93007bd02a13d, 0x810280209ef92780, 0x940cf83140799012, 0x49613d619081ec06, 0x7b2])))) else (if j < 322 then (if j < 320 then (cbits [0x381eed2944f70942, 0x25065d37a203df25, 0xd00940818010ec8d, 0xf5a64e07ad1a103c, 0x3daa4f81ecd2584, 0x9c4f6a94a07b94a1, 0x9281ae93d109ee52, 0x65d2]) else (if j < 321 then (cbits [0x44081c01201f4008, 0x1b232c009915480, 0x480a41ea403e0f38, 0xf38033332c015995, 0xb20d010c5ea406e2, 0x644d06314741a027, 0x1a103e50cdc1f086, 0x7cb]) else (cbits [0x3c1fbc6940fd6343, 0x62107fb31003fd0d, 0x518ac5f08c4a0ffc, 0xf94637080031983e, 0x8402990c2004c7e0, 0x58101264f0806325, 0x4a18bf7a4f8da0d2, 0x17fa]))) else (if j < 324 then (if j < 323 then (cbits [0xe05fad29e2f9694e, 0xc3f17fe61c8bfdb0, 0xb12c6025886300c, 0xbd8f4418056278c0, 0x4053d3d9bd1e8ac, 0x10ede925175ec928, 0x1483e1804403ec0, 0x32ac]) else (cbits [0x801f106842f54035, 0xc3807c74a703e318, 0x6bd101f2587c0f90, 0xf8a93c75ef92832f, 0x807e00201f146680, 0x9ec56803532b400e, 0x18c83e60c51d0600, 0x17c7])) else (if j < 325 then (cbits [0x3c1f406968f8e331, 0x630368531003e88d, 0xe19381f6cc7c0fa4, 0xfc692c07e232783e, 0x83f224f09f6d2620, 0x964fce93e07e749e, 0x61c03f5253c1fa12, 0x6685]) else (cbits [0x109f8989e4fb8c4e, 0xf4f27e87a593f1bd, 0x698c1d79e4a04fd4, 0xf9c64007cf49e03e, 0x3e9807403f40100, 0x840fa864007cd18a, 0x61c03ed24b01f60c, 0x27da])))))))) else (if j < 380 then (if j < 353 then (if j < 339 then (if j < 332 then (if j < 329 then (if j < 327 then (cbits [0x5003f8010eb2af44, 0x62007d519903e70c, 0xbb0e09f592580fac, 0xfac94007d919e03e, 0x395901058ac80520, 0x802fba63007dd1a4, 0x4a103f025041f7d2, 0x17e0]) else (if j < 328 then (cbits [0xc01f792800fc2c48, 0x62427de19e03ef0c, 0xf24c0df78c782fbc, 0xfc0c4c67de4a033e, 0x807f80201f692604, 0x400f9e31407e5014, 0x4960bee9908da18c, 0x7e6]) else (cbits [0x111f75884cd0cc38, 0x94807e962c3af43d, 0x125681fb06b40fd2, 0xfdcf5a07ed6240bf, 0x80800020df812980, 0x80655c02907f0008, 0x31003fb0d081fc46, 0x7f8]))) else (if j < 330 then (cbits [0x101fe58702fa494c, 0x94c32af01432cb3d, 0x8007404040102fa6, 0xfa864007f218a195, 0x3fa24c81fcd2582, 0x802fac64007f561c, 0x4a00bea99005f392, 0x17d7]) else (if j < 331 then (cbits [0x1fdd2782fb064c, 0x94c07f23200bec99, 0x6b1301fccc802fb4, 0xff802907ec1a10be, 0x91558c7404086280, 0x644aa262032b5194, 0x32503e619081f18c, 0x7f8]) else (cbits [0x385fe527c6d0e92c, 0xf4407fd61c0bf1a5, 0xf80d1d7c64a0cbdc, 0xf8e34c17c849803f, 0x401a56820092988, 0x9c100925a17e862d, 0x4ad040118f05fa52, 0x17ea])))) else (if j < 335 then (if j < 333 then (cbits [0xc0201cc680fa034e, 0x25937db62c0be4a4, 0x88d085f14c601011, 0x562011080331f03e, 0xc1878104cac40524, 0x824fb8340930f026, 0x31e93f10d081fb86, 0x804]) else (if j < 334 then (cbits [0x30202cca81010649, 0x94e17ee4a69bee25, 0x23124602187a6fc4, 0xfba340180b62a0c0, 0x80818020df852984, 0x4a456e01d0324008, 0x1e995b80d41d380, 0x174e]) else (cbits [0x3820346940d56314, 0x35a180d1ab04078d, 0x818f89a20c40301e, 0xfd664e0811320840, 0xc0824c420492584, 0x821028940181149b, 0x4a70c08a50820452, 0x816]))) else (if j < 337 then (if j < 336 then (cbits [0x68da21870102e95a, 0xf4e18127a21bf5b1, 0x949406059eb4302e, 0xbe555c081892db2f, 0x1bf625682038022e, 0x220208008081301a, 0x14915c80740aa00, 0x32b9]) else (cbits [0x81b9987008d6314, 0xf441815627040ab1, 0xab131d75a4a0cbac, 0xfc464c181562c040, 0x808280215f898b08, 0x52064a01d081a008, 0x1a103a780c48a980, 0x81b])) else (if j < 338 then (cbits [0xe09a05258101a642, 0xf44081e621040e30, 0x70d081d440606ba8, 0x3a01c0750318040, 0x8193004404180101, 0x820ea402522a700e, 0x31004078cd98d440, 0x2682]) else (cbits [0xd82081258502264d, 0x94d28144a6041124, 0xab0e0208d2b45022, 0x48c5b18176269ae, 0x4b14d57020964b41, 0xb0102ac4c0821020, 0x4ac1bf60cd12055e, 0x4815]))))) else (if j < 346 then (if j < 342 then (if j < 340 then (cbits [0x440820012020e008, 0x2722ba00e841380, 0xb80dc1eb80560f3a, 0x5e334641302199f, 0x13f79908211066c1, 0x66109c92d084b496, 0x4a1842924dc21412, 0x853]) else (if j < 341 then (cbits [0xcdb798726b26c38, 0xf4d65d77a2042a31, 0xd8070082401010aa, 0xf3e02622c100e915, 0x4140c5190500840, 0x584fe0642079e193, 0x49b841524cc20a52, 0x82c]) else (cbits [0x1020b58866b0cc38, 0x31c082e7a6b2ec3d, 0x5b1008af46504578, 0x57e01c082b498041, 0x23e999020afc0804, 0x2204140090108004, 0xf83d0006c8b080, 0x7af]))) else (if j < 344 then (if j < 343 then (cbits [0xdc20d00561060027, 0x62027f119b320a80, 0xd189c20e4c42106c, 0x78637083b315841, 0x842024b420f52581, 0x82cbb2c38084249b, 0x1404188070210d8, 0x832]) else (cbits [0x5020d4c601066040, 0x63622c418e80848c, 0xd30e020dd2584fe4, 0xfac6340838620b2e, 0x80850c5020f803a8, 0x584fea63622c818e, 0x620b2edb0e020dd2, 0x83f])) else (if j < 345 then (cbits [0x2021040388fae634, 0x3522c6008808580, 0xc18811f50669058c, 0x70f44083f496041, 0x9164804404300113, 0x404fec34233ee014, 0x314842318942114c, 0x83b]) else (cbits [0x8db5d258108e631, 0xf44084961c042425, 0xc0d002129e9acbb8, 0x21a314084c00ea3e, 0x11650ca420a463a0, 0x84108a636083631a, 0x7a21acbb0e09fe12, 0x65dd])))) else (if j < 349 then (if j < 347 then (cbits [0x20e0c68109af4d, 0x640084f00e23ed25, 0x38ca020a80221072, 0xa2c4008461a0042, 0x416004420ac0221, 0x6810a2930083b19a, 0x19a0416804420f06, 0x848]) else (if j < 348 then (cbits [0x7420b8022021c008, 0x33482cc020916600, 0x91900212866c1086, 0xb28c38084d49623e, 0x8087802261364a06, 0x52064e01d0857008, 0x1a003a980c48b3c0, 0x858]) else (cbits [0xe06034c8410b8342, 0xc42085f61f042eb0, 0x800a0d665e88303c, 0x1c3420755018116, 0x808800201d50c603, 0x4a45a201d0328008, 0x49b042ca4b01d580, 0x85a]))) else (if j < 351 then (if j < 350 then (cbits [0x70216926810b6c38, 0x80859320042f00, 0x900740ca40220222, 0x6d204d0757012916, 0x13451880603c66ce, 0x5810c265927fa321, 0x49b043224c821892, 0x1822]) else (cbits [0x6421992b010ca942, 0xc5935a861c0430a5, 0x2bd659779e88302c, 0x2af580863026041, 0x8169804404480109, 0x58e6d604122d300e, 0x61c0c0aa534d6a52, 0x65a9])) else (if j < 352 then (cbits [0x241c024a0902ac4d, 0x130869007843400, 0x900d821b406610d8, 0xda03f087701b843, 0x943b810ca1c80845, 0x9e10f604e0878025, 0x18a80898c5021f40, 0x20b]) else (cbits [0xa40cb863e05a831d, 0x337232e195916a0c, 0x28d3d906c6866836, 0xd58621054d3103a3, 0x83fd98d821a0c560, 0x86103863f081231b, 0x325842599282080c, 0x85d])))))) else (if j < 366 then (if j < 359 then (if j < 356 then (if j < 354 then (cbits [0xb4953525810c464f, 0x937281c499935624, 0x9250c9fed2845040, 0xba94b284b4a5140, 0x9af9b0e0a18929e5, 0x8610fcc3f36f561c, 0x7a20441b13c22098, 0x65f3]) else (if j < 355 then (cbits [0x40a20de9ecdeaf45, 0x28770a928bb2649, 0x58c70a1a806810d4, 0xdc028086b006043, 0x438013021bc0681, 0x220228008087102c, 0x18a116b00740b540, 0x54e]) else (cbits [0xa4953cc401026329, 0x94235bb496141098, 0xab10821d129c10e6, 0xbecf440876627043, 0x3fe18d1d93a4a0c, 0x8050f20340879014, 0x4143d013021e80, 0x115]))) else (if j < 357 then (cbits [0x508b5c03a05ae011, 0x62008631a082a80c, 0xaa4b0a18cc824aa0, 0xec94d087c4a09af, 0x943e310597d58701, 0x68ec74f442876626, 0x320044018d021fc0, 0x17f9]) else (if j < 358 then (cbits [0x611fe52985100934, 0x94017f331a0440b1, 0x9810021cc0688fe6, 0xe80340875026143, 0x442015021f00981, 0xa82fc6634087602c, 0x4aa1426a5202218c, 0x887]) else (cbits [0x48222401c110a040, 0x4e088c021044580, 0xb0c5022380b45118, 0x5b632902db18e808, 0x3d88cd41e846624, 0xac0ffc642068b310, 0x4a71345a4b02138c, 0x27fe])))) else (if j < 362 then (if j < 360 then (cbits [0x8224187c509c956, 0xc4e28906250448b1, 0x9b16822498ac5122, 0xbf125035f87a2044, 0x4450071d93eab8c, 0x680ffe334288a014, 0x1a0447a53022352, 0x6cf]) else (if j < 361 then (cbits [0xd022340682f90640, 0x8088f026036800, 0x7804c0830012022e, 0x8c804f0895014819, 0x83568c541a30628e, 0x9c10c834f085f1a5, 0x928bb23c94022618, 0x7709]) else (cbits [0xb01a34628041a008, 0x2500897627044b24, 0xc00215d79290ec91, 0x6300410897014808, 0x83470c515d74092e, 0xa0ed48f4408991a6, 0x8808c8021621a4, 0x2dc]))) else (if j < 364 then (if j < 363 then (cbits [0xc4226c05245ca01d, 0x31407b401a83d100, 0x80d045f086800d1e, 0x264e08501ab0c0, 0x450a568228129c5, 0x821148c40089061c, 0x62b0456b13822b18, 0x8af]) else (cbits [0x6822cde9c1164c5a, 0x25b65f9928045a3d, 0x18091d926ab8116b, 0xf0893017c31a003d, 0x44fbd6822712800, 0x680ed6930089d018, 0x4a40be20cd022780, 0x8a2])) else (if j < 365 then (cbits [0x205f146681146954, 0x1d02dd008808d00, 0x280c4227005245cc, 0xa234a069018a045, 0x45430e0a008c841, 0x881154c4e08a9621, 0x9280455bd3d97e9e, 0x764a]) else (cbits [0x1dac06845ce028, 0x33408a7026045301, 0x499002278050113a, 0x15cc5a08a962623f, 0x451a4d05f246801, 0xb01160c4008a24ac, 0x62c1401990822c5e, 0x8aa]))))) else (if j < 373 then (if j < 369 then (if j < 367 then (cbits [0x8227c0521152c4c, 0xc4808ae621140219, 0x4193022a98b01162, 0x23600808ab62023f, 0x816f004408380120, 0x3e45d001d0330009, 0x15997400a48cc40, 0x3331]) else (if j < 368 then (cbits [0xc22e806e116e033, 0x314741d027b20e81, 0x88c7c1ab862a0d22, 0x3c33f1811195840, 0x8c0f0d2c20886861, 0x864d2862018221a7, 0x4961432993ca058c, 0x3694]) else (cbits [0xe0e05929e70ca943, 0xc3f08bf61c845e30, 0x2b10c23098841180, 0x184c4e18c0625846, 0xb2fdbd10631589e3, 0xa0118cf4f66f67a2, 0x143b7b4945d7ee4, 0x22ea]))) else (if j < 371 then (if j < 370 then (cbits [0x6022e009865d4034, 0x32802df18e0c5c01, 0xc8d00cba466845d2, 0x176f4808b9018045, 0x45e80a462edea81, 0x6c317a03516cf015, 0x27045f01081b3c0, 0x18be]) else (cbits [0xa40b8063a023a314, 0x62032ed19a91768c, 0xa30e097d12580b58, 0xbfd25065fe7a21af, 0x44680d06234050e, 0x22023c00808c17a6, 0x14917080740b840, 0x32ee])) else (if j < 372 then (cbits [0x801a48628c5dc035, 0xc383696496134918, 0x23d38230de88cd2c, 0x182c3c75b2928046, 0x4643150231c6a81, 0x22023e00808c462c, 0x12917800740b8c0, 0x7a4]) else (cbits [0xf4d00c06a0f6c029, 0x336069318a046500, 0xb988021486ac0f94, 0xa66562805327134, 0x845224c022452585, 0x9c515a94a08ac498, 0x4ad0467255823352, 0x8d0])))) else (if j < 376 then (if j < 374 then (cbits [0x382345e886de4c38, 0x25008d37ad04693d, 0x5d57023524b6cbff, 0x80a04022f20143b2, 0x4660160232c0986, 0x6845e232802e418e, 0x4980452b0f01edc6, 0x8a6]) else (if j < 375 then (cbits [0x602055898114e930, 0x28181562c0467bd, 0x4a4c022a18783026, 0x15493028a949e045, 0x23f51930233d2901, 0x10515c94808ab498, 0x148108002404800, 0x8d6]) else (cbits [0xe19058086682c037, 0xc3f36f361c9aefb0, 0xf3134237188611b2, 0xde6f4565df7a2046, 0x1088020a379e9ac, 0x9a6bc0c3808d7496, 0x7a6b2f03d1023618, 0x28d8]))) else (if j < 378 then (if j < 377 then (cbits [0x602369268aec0948, 0x25808dd4a6046db1, 0xc00a40484010f18f, 0xebe049530e01a846, 0xb2f0bd115a81870a, 0x10b10f25078c77a6, 0xe8179804404880, 0x22f3]) else (cbits [0xd41e9406211c0029, 0x64e08061a103dd00, 0x1a538238d284500c, 0x15ec3e089261c147, 0x1457b12823398841, 0xb211c8c5828ce627, 0x7a79af1bd1023a18, 0x8e9])) else (if j < 379 then (cbits [0x65978e4a011d4f59, 0x93007a6012147549, 0x1012023852b00f2c, 0xe33407884a4047, 0x451a4f022c12601, 0x3a05e80110123004, 0x24847080a48bd00, 0x8e5]) else (cbits [0x10233d89a6bc8c38, 0x25028cf7a6b2f23d, 0x301001e2006811cf, 0x1c433428e6026047, 0x14041938df6c6801, 0x10119ec5808b161e, 0x88109002404900, 0x2f5]))))))) else (if j < 407 then (if j < 393 then (if j < 386 then (if j < 383 then (if j < 381 then (cbits [0x7c8bd403a0664013, 0x3733fe015919900, 0xe810dcdb8082c7fc, 0x1de04f08ec025b9b, 0x84308c7c1a606281, 0x4010463370817195, 0x31b941198ac9a60c, 0x2817]) else (if j < 382 then (cbits [0xccdb9d25a6b5c92c, 0x94308f449b8478a4, 0x1253423d5296f04a, 0xb5cc3808f74a78c6, 0xcc12b10d9b9d872c, 0x9e9184c4d28f5625, 0x9283b65bd10a3dd8, 0x8f8]) else (cbits [0x23b406811f7251, 0x31c7370026147681, 0x78d308bd865005ec, 0x1dc04808ee1ac39b, 0x1478315023c12a81, 0xb011e695808f24a6, 0x4a4047b31602311e, 0x8f6]))) else (if j < 384 then (cbits [0x34a3e408411f2036, 0x31406d0027047d01, 0xd0ca40be863a024c, 0xc5a62073711a6917, 0x1ad8b0e098b52580, 0x98ec9b25065b17a2, 0x880938020223c0, 0x2fb]) else (if j < 385 then (cbits [0xa41e9c04a45f601d, 0x55745c02683de00, 0x48cd81a6462811fa, 0x126422699310040, 0x45924c8224d2585, 0x84516493e08d049b, 0x4a484722520a3412, 0x8e8]) else (cbits [0x10234d8b26bcac38, 0x25028d37acb2f2bd, 0xf010023feab8ee11, 0x8bc05828fe026047, 0x117e0ca00bf0638e, 0x9011cac5407bd19a, 0x40473b15023992, 0x128])))) else (if j < 389 then (if j < 387 then (cbits [0x948c1403a060a011, 0x334090101a83ac00, 0x218d05fbc6801208, 0xfc92c47ef326148, 0x483a4d424152681, 0xb011e295a08d94ab, 0xaae0486316824218, 0x759b]) else (if j < 388 then (cbits [0xd08c18038060c010, 0x93c47f03260bf80c, 0x48020240d2981204, 0x1006202307008809, 0x80950021d63a4a01, 0x70461001d0308008, 0x9280479b13824198, 0x758f]) else (cbits [0x740c240220256008, 0x334075a012918480, 0xa4b11fc4c802fe2, 0x21494e09094a5044, 0xbfa0cd0242e4a01, 0x982fea64047f4320, 0x3200bfb0cd11fd52, 0x47f6]))) else (if j < 391 then (if j < 390 then (cbits [0x5023c929811b6948, 0x33408f34ac0486a5, 0x600211fdcc802fee, 0x61401d030a008809, 0xa9b200d41d6c04a4, 0xb6121e0498364020, 0x19b034e8c51d0040, 0x17fa]) else (cbits [0x8021506ac302e34d, 0x64d47fa321134e98, 0x124b0a150cac902e, 0xca93608b3498844, 0xb432a508a2cd27a7, 0x9a118494c09144a4, 0x4ab048aa53823492, 0x8dc])) else (if j < 392 then (cbits [0xe023d12b411d2957, 0xf44582462dab64b0, 0xb49422091eb70d92, 0xb7155c78c692d048, 0x148800a02440038e, 0xb41224058091101a, 0x4048b80c0244c0, 0x12d]) else (cbits [0x948c5803a0616011, 0x43530b01a83ae00, 0xe0155cc5809ac82e, 0xf96334069e18a2ba, 0x8bf58cd8dfac66a2, 0xacb13035408241a1, 0x3100c0b0d6562d06, 0x26a2]))))) else (if j < 400 then (if j < 396 then (if j < 394 then (cbits [0x20a060c865014642, 0x65658de32a142a99, 0x1a4b0a094cb2b1d4, 0x1689310898498044, 0x145aa4fce05926c1, 0x9051a894328c64a1, 0x4a70475252423792, 0x7825]) else (if j < 395 then (cbits [0x5824752aa1232954, 0x95918c24ac2c8ea5, 0xf30e1634d2b411a6, 0xbccf445824621ab4, 0xbc0c3d3de029e9ac, 0xb6f18cf5978b57ab, 0xaae3b514941e351e, 0x5883]) else (cbits [0x502468052025c008, 0x33517e419a03508c, 0x298805fb466c6fda, 0x23692c280b321135, 0x2b50b0e024712841, 0xa0f016f4d65e97a2, 0x31a0bf28cd1da964, 0x17e6]))) else (if j < 398 then (if j < 397 then (cbits [0x2404bc0102fce340, 0x13091f008810a00, 0x500ac0cd803e1252, 0x66c043342001b91f, 0x49b8c52508009ec, 0x5412b43290938194, 0x19b04b90cac25846, 0x976]) else (cbits [0xac1abcc40d2ec34e, 0x637182631b040c98, 0xc190825e0c8230ac, 0xda292d257e49634b, 0xb40ca50c25e926e4, 0x9e6c06c38697a4a7, 0x7a73357bd1164018, 0x8826])) else (if j < 399 then (cbits [0x22580e4a110acf4f, 0x130219004810b80, 0x80d88fac056066e, 0x66e043342501b9a1, 0x4a12813e508409cc, 0x56066e31f06b018a, 0x19b8c138cd820686, 0x1857]) else (cbits [0x81a4806841240341, 0x6270923310849118, 0x398dc2498c561248, 0x24e64f6337321849, 0x936a24b4960d258d, 0x9ed034943092849b, 0x6279b0230e1a4a12, 0x5901])))) else (if j < 403 then (if j < 401 then (cbits [0x3e209de9ccd60f44, 0x89604928442bbd, 0x9880d08806c0430, 0xc0ac382585496049, 0x1a118cd804cc6286, 0x6c0d6262094231a7, 0x3210490990460a0c, 0x6921]) else (if j < 402 then (cbits [0x10d8198704b0e92c, 0x25088287a73358bd, 0x2989024952692c0d, 0x5b25a335701a049, 0x4950cd008680111, 0x64126a92c093019b, 0x412c4b0e024d92, 0x21b]) else (cbits [0x9824b4c401256026, 0x34092f496049718, 0x880c1a4b00981258, 0x2686300933312049, 0x3499013024c80681, 0x681268328092d31a, 0x18a80990c5024cc6, 0x21c]))) else (if j < 405 then (if j < 404 then (cbits [0xb4962925847e632b, 0x90134004136d24, 0xc806c0ce0026043c, 0x85202b094900f849, 0x4a14810d8ce006e6, 0x56305e32a06b218a, 0x31084a6188061606, 0x950]) else (cbits [0xb1a554c8612aa62b, 0xc3859084a19b04a4, 0xc310e20bd884cd64, 0x27400896097a2442, 0x849f00d024ec03a1, 0x82128a036094301a, 0x26b49f0131a4ec0, 0x6943])) else (if j < 406 then (cbits [0xa40884628d28a04e, 0x620094719504a30c, 0x424b060c0c6c0d66, 0xd66f44360a61c04a, 0x4b05494220c1e9cc, 0x10127a04c093c01a, 0x18a049f807408880, 0x6b4]) else (cbits [0xb02504c40128032a, 0xc4266b561c04a124, 0xe0072582de891066, 0x28804c693d020049, 0xc190cd060c46501, 0x68d27e04c093f01a, 0x434a08d3025046, 0x223])))))) else (if j < 421 then (if j < 414 then (if j < 410 then (if j < 408 then (cbits [0x50251c034128c019, 0x620183419b035b0c, 0x59938252cc6c1294, 0xd6cf44360c61c34a, 0xcb06494220d1e9cc, 0x56129c013094d007, 0x18a34a7810c253c0, 0x137]) else (if j < 409 then (cbits [0xac0ce463e0448315, 0x343633919b9a168c, 0xe98a81adcc41285a, 0xc1e92c185b3158c1, 0x335bb0e1642d2866, 0x8910b6c43883d621, 0x70c1f18a2583de, 0x951]) else (cbits [0x38254c06c12a4012, 0x325013818a34a981, 0xc188025286521290, 0x2a8936184031b035, 0x1b0830e1a55129c1, 0xa11080f4e66b87a2, 0x40c208ca258424, 0x139]))) else (if j < 412 then (if j < 411 then (cbits [0xc4d0a8052129601d, 0x62006b918a04ab00, 0x53138256587012a8, 0xc1d25088427a72c8, 0x1a1580d0255c0392, 0x1202740080958026, 0x138495004408940, 0x95b]) else (cbits [0xb4257925812ba02b, 0x40092e00e04b024, 0x58c71a5700b012b8, 0x2be01d092c008049, 0x4978c7404ec6281, 0x12027800826d300e, 0xe819d804c08980, 0x23ec])) else (if j < 413 then (cbits [0xac258804e47e201f, 0x43342e01b84b280, 0xd0c5250b809ec676, 0xb8337184419b035, 0x136c18849b58c403, 0x9c12d6637096631b, 0x49634b5993da598c, 0x96c]) else (cbits [0xdc25bd26c12dc92d, 0x94f696f4a704b8a4, 0x6313cd845870d2e2, 0x88f4e66ba7a22c8, 0x4b08c9422171e9f1, 0x50d2c60580963020, 0x1204b20cd08fb46, 0x964])))) else (if j < 417 then (if j < 415 then (cbits [0xc4cd60052027c008, 0x62006bc18a04b380, 0x9313825a987012d2, 0xc2525088487a72c7, 0x4b40130255c0392, 0x28d2da04e096d01b, 0x31011f78ca404fc6, 0x6bd]) else (if j < 416 then (cbits [0x3825a526c3092636, 0xf44361461c34b4a5, 0xa49422125e9ccd7a, 0x69e01d01400044b0, 0x35f0c50cd640524, 0x9c12e0c3826c5310, 0x44b04494163cd8, 0x141]) else (cbits [0xc48fc80521260011, 0xc3826d949604b980, 0xa010024d003812ea, 0x26231c697402c04b, 0x80a1002024c80201, 0x3e06780130228004, 0x279a1300a48fd40, 0x9428]))) else (if j < 419 then (if j < 418 then (cbits [0x80206c63e0d7e314, 0x63526dc31092c698, 0x2253825dcc9e12de, 0xc0f25059056272c8, 0x80a1802163cd8b12, 0x3a12400110229004, 0x1b91fb00ac0cf40, 0x3430]) else (cbits [0xdc9b7525a4b2292c, 0x8361561c04bca4, 0x700a424a00220288, 0x2f603d335601a91a, 0x4b58ca825986501, 0xb41300342096f1a0, 0x32083609881a5dc6, 0x81e])) else (if j < 420 then (cbits [0x109b1125812f264d, 0x25a58f17ad04c0bd, 0xe0072585aab910a9, 0x2fc04c097d01404b, 0x4b398d025fc0b01, 0x6812d03280957194, 0x480a2802025a8c, 0x22a]) else (cbits [0x7c0de0026068a011, 0x35343201591fd00, 0x180f58de006ec68a, 0x86404f099a02184c, 0x840f8c7c1b086292, 0x6412f03311860195, 0x31004d00d3da5e06, 0x259c]))))) else (if j < 428 then (if j < 424 then (if j < 422 then (cbits [0xaca5e8c4e4dbe621, 0x63d681f31b84d098, 0x3990ca2d8c821348, 0x34264f497a32584d, 0x9b7c24b4d8612589, 0x82135893d69a049b, 0x4a784d7a50c63ad2, 0x590e]) else (if j < 423 then (cbits [0x12218189ecd84c38, 0xf4e69ac7a504db3d, 0xc4941a6bde9f11d6, 0x30802896f8928cb0, 0x4c700d026280541, 0x9cd31c04c099601b, 0x49692d0a4b1a6580, 0x26e1]) else (cbits [0x2c266526e52f6933, 0xc3869994a7a4bda5, 0x7b13cdbe58726c38, 0xdf3251961c9282c8, 0x84c318842614c412, 0x7e131262b0987313, 0x49634c4990da61cc, 0x3620]))) else (if j < 426 then (if j < 425 then (cbits [0x1164492866df892d, 0x92c96fc7a2cb103d, 0x40c725885e886c42, 0x2fa63226e231004c, 0x24be9928262cc6c5, 0x6c131892c698b327, 0x61c34c6a53826352, 0x3622]) else (cbits [0x82588a4a0b226c4f, 0x62726e331092d118, 0xf98fc2640c56131e, 0x32492c0991321a4b, 0x84ca24fc264d25a1, 0x8b2c3af4409954a1, 0x7a212d1a4b25bede, 0x961e])) else (if j < 427 then (cbits [0xa4a5f8c4a4b4a620, 0x92c098d31a84cb98, 0xc30e1644129c6df4, 0xc3f250591162704c, 0x4cb80d0262c0512, 0x10d322058098d020, 0x32092d3988008b40, 0x99b]) else (cbits [0x4d88d258133a649, 0x55c699e7ad04cf25, 0x5bd2026700912c47, 0x290008099f024139, 0xb1b080d40de40220, 0x824b546207361026, 0x496041199642194c, 0x35aa])))) else (if j < 431 then (if j < 429 then (cbits [0x6061952b23046941, 0x11014900444333d, 0xd00a48d4003a06a0, 0x6b4041299901899a, 0x83630c502664092c, 0x4012f233d082219a, 0x32694bc98949b18c, 0x2822]) else (if j < 430 then (cbits [0xe0e08d29a6d8e92c, 0xc4c682362104d130, 0x1b138268d89a1184, 0xd8ef4458f462d14d, 0x447a4968a68a4a0c, 0x1202940087624aae, 0x404d2807408b80, 0x22f]) else (cbits [0x44052c010134c92c, 0x3523fb00e81a980, 0x40124266c082c6a6, 0xc5492c26e431004d, 0x14d1a53426a92826, 0xb4135725069aa7ad, 0xe4b155571268e4, 0x355]))) else (if j < 433 then (if j < 432 then (cbits [0x318d540801352034, 0x31c69a902c139581, 0xe0d318d5068006a8, 0x4201c08157a604c, 0x80a600202084080d, 0x9e135a0290230004, 0x928cb12c94250d00, 0x96fe]) else (cbits [0x4026b98700462008, 0x11014d0044b1349, 0x900d4d0cc05206c4, 0x360049099e020b1b, 0x84d5190496d0c401, 0x58534664d09b3324, 0x92804da3d68dbf52, 0x9b5])) else (if j < 434 then (cbits [0xa2589eab8b22b25a, 0x58637402004d880, 0x98d000d8c6381364, 0x2af58099f1a631b, 0x80a70c50618c080b, 0x5606d831d023218a, 0x1a09a1b8cdc8ff06, 0x636c]) else (cbits [0xb496ad259286e34f, 0x93729814999372a4, 0x1253d26052965344, 0xdfec39362c61c24d, 0xcb164941645989e6, 0x96ff928])))))))))) 29 (i % 16)
def s68Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 78 then (if j < 39 then (if j < 19 then (if j < 9 then (if j < 4 then (if j < 2 then (if j < 1 then (cbits [0x400801000203f000, 0x892c004310001802, 0x5801988400de8800, 0x28c7e00603000831, 0xf0023218018c700, 0x718a803801001a0, 0x4960]) else (cbits [0x804462802202a00d, 0x26420113100088cd, 0x1008a4d804525802, 0x4587002294e0114a, 0x2b00d928008bd100, 0x6a4b007807c01a0, 0x210])) else (if j < 3 then (cbits [0x8081258040620020, 0xa32700d9280103d3, 0x6a4d009402004, 0xa8c5401a92c02831, 0x2c02a32101518800, 0x1525080a926c0549, 0x4a70]) else (cbits [0xa9e88054c3802a, 0xa64200d315806c94, 0x701aa4b00d4c4006, 0xe925801b2500357a, 0x4403a61c01d00940, 0x6a4b40364a0074f, 0x4998]))) else (if j < 6 then (if j < 5 then (cbits [0xc034c50080028040, 0xa94f00d4a1806a4d, 0x7806c940119e8801, 0x286280920130027a, 0x150497a202524b01, 0x2480c01386560923, 0x19f8]) else (cbits [0x124686092334050, 0x6c38053012829a4b, 0x6824c94014de880a, 0x6926609202405849, 0x4304949b8248ca01, 0x2499201746900ba9, 0x4a58])) else (if j < 7 then (cbits [0x12529e09294c060, 0x3250063012831bd1, 0x78248090199e8a09, 0x8ca80d03540687a, 0x2a06c0048358c500, 0x37803c1ad2580d86, 0x150]) else (if j < 8 then (cbits [0x81bc6540de04206f, 0x6f4406f4960378d0, 0x103b00d81d80360d, 0xd92580ec04e07602, 0x4407661c03b25081, 0x3f807c1ae4a00ecf, 0x1928]) else (cbits [0xc1ad8700fe62007f, 0x603608301504180c, 0x6043188021809810, 0xc09c106f4408649, 0x5008361c041a4b02, 0x470cf423806e0d72, 0x3100]))))) else (if j < 14 then (if j < 11 then (if j < 10 then (cbits [0x1ac07812292c08e, 0xa92c093007849988, 0x9849a4b424d87012, 0x4d26e12694c09849, 0x450937a2049a50c2, 0x4f0038278c420d6f, 0x4990]) else (cbits [0x827926c13c3280a0, 0xc9400a44a504f250, 0x804f3d1027929c13, 0xa403815262706b92, 0xc0ac31005480782, 0x54a4d42a4c841520, 0x4a10])) else (if j < 12 then (cbits [0x42c8c560d6f440a9, 0x4c380b219885900c, 0xb835bd102c988416, 0xe067a17003d0b831, 0x3d0b84a605da4c42, 0x5c31382e18701709, 0x7a20]) else (if j < 13 then (cbits [0xc1ae4a0170f4e0b8, 0xa6400c331b06198f, 0x6861990830d87018, 0x2409219264306b4a, 0x440c94a48648d243, 0x35b0e01ae4a0192f, 0x61c8]) else (cbits [0x43498860d6f4e0d0, 0x46490d21a4869012, 0x786b8c5400a4a01a, 0x68c541ae0270d700, 0x420da31006d0c943, 0x6d24d83692641b46, 0x4a10])))) else (if j < 16 then (if j < 15 then (cbits [0x835cc561ae94e0da, 0x66200e431407198f, 0x106b98d838cc541c, 0xa925a1aef4e0e832, 0x280ec49986b80303, 0x77a50c35d26e1ae6, 0x240]) else (cbits [0x3c9e9e1ae94f0d7, 0xa0250f418f801015, 0x387a18d83d40101e, 0xd00561e83340f801, 0x420fb19907d8cd83, 0x7e99003f8c601fa3, 0x49e0])) else (if j < 17 then (cbits [0x3ec68020234a0fb, 0x894010419b87a188, 0x507a0d0c3d067e1e, 0x24c402123341081a, 0x36108620884a4b04, 0x7a3d344212582103, 0x1a58]) else (if j < 18 then (cbits [0x44869e1e8340110, 0x803611449607a256, 0x907a24b43d009c22, 0x692661e8c4e11849, 0x3111c49b07a31004, 0x7a31084718702380, 0x49b8]) else (cbits [0xc3d189a24294a0f4, 0xa94e0f462c091a52, 0x787a494049409224, 0xa4668252c3f0f44a, 0x430f462c094a4d04, 0x125504b989e1e8c, 0x1998])))))) else (if j < 29 then (if j < 24 then (if j < 21 then (if j < 20 then (cbits [0x4c0668262013130, 0xa3281300070998c5, 0x9a807c4d403626, 0xc0c5626a62113531, 0x2a13049609d8ca44, 0x9e98d84f404a27a3, 0x4960]) else (cbits [0x84c065626093613d, 0x49371303208980cd, 0x18a300f451866e00, 0x18c5628c34f14602, 0x3d1463218a318f45, 0xbd1051928628c9, 0x48])) else (if j < 22 then (cbits [0x85440102a201b150, 0x204e1510250a880d, 0xb0a8a4d05586642a, 0x68c9c2a262815831, 0x361514960a899005, 0xa8b0e054529c2a29, 0x9280]) else (if j < 23 then (cbits [0x5886282c201e150, 0x23151617a20b124b, 0xa0b38cfc5846562c, 0xa92582c234316119, 0x4416a61c0b500945, 0xb7a4b45864a02d4f, 0x120]) else (cbits [0xc5846502e2933161, 0x83481744a18b0a4d, 0x40bba52c584c902e, 0x8529e2c294c17701, 0x5017b0128bdbd105, 0xb080905f9e8a2c32, 0x7a78])))) else (if j < 26 then (if j < 25 then (cbits [0x8540ca8300354180, 0x862618418a0c18c7, 0xa8c1bd1061125830, 0x24c4031232a18318, 0x4018c3250c499086, 0xc4a4d86252583126, 0x4a10]) else (cbits [0x62587031294e189, 0x632b1839280c4bd1, 0x60cb0cd065867e30, 0x64c4033234218332, 0x4419961c0cca4b06, 0xc1c940665e9c332f, 0x1a18])) else (if j < 27 then (cbits [0x860de88342626183, 0x6f4e1a34960d198f, 0xc8d3a4b060e4a034, 0x9d87034e0251a700, 0x2d1839280d3bd106, 0xd7a4cc60c04835a9, 0x1940]) else (if j < 28 then (cbits [0x6c9286306937183, 0x83281b44a58c1992, 0x20c1a53c60d29836, 0xe00803720191b87a, 0x451839280dc00946, 0xdfbd3c60c04837af, 0x32a0]) else (cbits [0x70866c38231f150, 0xa34e1c11980e10ca, 0xe08d2071468038, 0x4c9c3826361c131, 0x381c14a50e0a4c87, 0xe798805424a0382c, 0x78]))))) else (if j < 34 then (if j < 31 then (if j < 30 then (cbits [0x87440543a20191cf, 0xef441d14960e8810, 0xf8e7a4b075803a39, 0x3c0503b20271cf00, 0x3f1cf1980ed80ac7, 0xe781607740503ba0, 0x218]) else (cbits [0x78925839e3481e0, 0xe92d1cf9280f130e, 0x40f300a079926639, 0xa928639e9371cf31, 0x281ec4a58e78d207, 0xe7a53c73d2983d86, 0x7a20])) else (if j < 32 then (cbits [0x7c9e9e39ef451cf, 0x80191f43108a80d5, 0x50fa0cc07d926c3e, 0xd12683f06281f84a, 0x301fc3158a825387, 0xfe00c47f0c6c3fa0, 0x190]) else (if j < 33 then (cbits [0x8086643f80361fc, 0xa3361fc1ac1010d0, 0x10fe315081587840, 0x246384126561fc32, 0x3e1fc61c0fe19008, 0x7b1087f066841ac, 0x1e1]) else (cbits [0x87f0668422c561fc, 0xa63f15002a109b16, 0xe10a8cd085803c42, 0x5463a42a34121818, 0x2021519a10d8c788, 0xf98d085401843a6, 0x131])))) else (if j < 36 then (if j < 35 then (cbits [0x88864c43e02a21f, 0xa92c21f19510f8cd, 0x811398d8854c6a42, 0x4129a42a64221501, 0x4e22b024915990c5, 0x17a5248ac69c4560, 0x1941]) else (cbits [0x8ac668462c4922b, 0xa02b234009800c94, 0x11b80708d80b446, 0xe862846a04c23632, 0x2623c19411a98908, 0x1e24b08f009847a0, 0x49b1])) else (if j < 37 then (cbits [0x8f187047894e23c, 0xa33023519491ac94, 0x71238d088d587048, 0xd469c46a93c24732, 0x4423532511a8d688, 0x27810c8d2ab846af, 0x18a1]) else (if j < 38 then (cbits [0x944c804a232a24f, 0xef5a2514a4128a50, 0x12b252095866c49, 0x3deb44acc4825662, 0x2c25b31012d8d009, 0x278d0493de884b69, 0x1a41]) else (cbits [0x9812584c0626260, 0xe62624f1ad127b0e, 0xb127a4b0998c9049, 0x3d87049e92c24f32, 0x2726c18a11a316c9, 0x363d109b8c4c4d80, 0x4961]))))))) else (if j < 58 then (if j < 48 then (if j < 43 then (if j < 41 then (if j < 40 then (cbits [0x9c004a4e000d270, 0x92502707a213830e, 0x213b00309d925a4d, 0xb126e4d893326c01, 0x4f26c32413da50c9, 0x3649409f9e884d89, 0x7a79]) else (cbits [0x8a0862a468654280, 0x493228219814198d, 0x31438ca88d187050, 0x2803a51000828801, 0x4028c01a9440130a, 0x440130a380825100, 0x269])) else (if j < 42 then (cbits [0x8a20c84510620288, 0x64029300e149992, 0x214430e0a2125851, 0x6804e50f2502887a, 0x5829a02614d0100a, 0x4f0048a78c4050e0, 0x49b1]) else (cbits [0xa7929c53c94229e, 0xf25029e7a214f30e, 0xb94398cca1cc4250, 0xa8c8450e9402a831, 0x312aa3101550cf8a, 0x57a4c4aa92585546, 0x141]))) else (if j < 45 then (if j < 44 then (cbits [0xac929e55494c2af, 0x4c4e2aa61c155313, 0x1943c940aa9e8855, 0x1d2985703482b832, 0x142bc00e15d9928a, 0x5e24b0af0c405783, 0x4a09]) else (cbits [0xaec03a576c382bc, 0x66202c3199161990, 0xe163a504b0d25858, 0xecc84576c382c319, 0x4d2bb61c15da4b0a, 0x43bd10aec69059ac, 0x3259])) else (if j < 46 then (cbits [0xca1cc985a001c2d0, 0xa92c2874ac169993, 0x716a8108b5406c5a, 0x55e885aac382d502, 0x33287496943c940b, 0x6fa4d8a1d8805ba9, 0x191]) else (if j < 47 then (cbits [0xb7d8845bec382df, 0xe03c2e449b943bd1, 0xe173b130b9927e50, 0xa407c5d294228719, 0x382e94961748cf8b, 0x74bd38ba5e885d2c, 0x9281]) else (cbits [0xbc40905e2943287, 0xec582f44a59438d2, 0x617b0128bd929c50, 0xd9e885ecc382f649, 0x542fc4a7943c940b, 0x7f0064bf987050e0, 0x189]))))) else (if j < 53 then (if j < 50 then (if j < 49 then (cbits [0x4a1e4a05fcf442fe, 0xe03030300c181b0e, 0xa18300d0c1987e50, 0x1d8b060c93430631, 0x5430c627943b10ca, 0x861950c31e9a61a3, 0x7a69]) else (cbits [0x4c4404a622f44287, 0xaf4528792818880c, 0xa18bbd3ca1c06062, 0x6a4a050e6543171a, 0x3031c92894380c4c, 0x8f80c0c786564680, 0x4961])) else (if j < 51 then (cbits [0xc7de8863ec3831f, 0xc34231e01918f494, 0xb18f0d38c7869463, 0x786b463c3403281a, 0x4e31e012195a4b0c, 0x8f30e0c78c9065a9, 0x61f1]) else (if j < 52 then (cbits [0x8c7989c63cc4231e, 0xd25031e7a218f316, 0x899b8cfc8d2ab863, 0xe525867233433700, 0x4233719b19bb0e0c, 0x9f1898cf8c9866e3, 0x4961]) else (cbits [0xcdd26466ec3833e, 0x8f4433700e1a1b0e, 0xe9a39880d1868446, 0x1d87068e92c34701, 0x503477a71a3bd10d, 0xa7989cd18c4268d2, 0x3261])))) else (if j < 55 then (if j < 54 then (cbits [0xd48c6e68c62b346, 0x80483543219a30d2, 0xe1ab992cd186906a, 0x18c986ae64035700, 0x3d35c4961a3193cd, 0xae3d10d718706b80, 0x9281]) else (cbits [0xcd1926e68c92d346, 0xa94f3460241b1a50, 0x71b3b0e0d186a86c, 0xa989e68d2503677a, 0x443467ac1b50d50d, 0xb7bd38d1a4a06daf, 0x251])) else (if j < 56 then (cbits [0xcd1a4a06de34a36f, 0xc35437302a1b9bd3, 0x89a30124dda4a068, 0xe46b46f234323492, 0x383794961bc9898d, 0x1a5570de64b46f2c, 0x3131]) else (if j < 57 then (cbits [0x88d1e8a700f44380, 0x80413844961c198f, 0x69c1c940e11e9c70, 0x24c5071294b38349, 0x5838c4a79c1a530e, 0xc72524e39e9c7066, 0x7a21]) else (cbits [0x4e0e4a070725038e, 0x800f39449611a494, 0xc9ca00c0e5802672, 0x6008473003639800, 0x4439861c1cc0138e, 0xca006ce524a0730f, 0xf9])))))) else (if j < 68 then (if j < 63 then (if j < 60 then (if j < 59 then (cbits [0x4e512607400303a0, 0x60423a301b1d1809, 0xc1d18cc8e8c09c74, 0x524a0746f443a361, 0x583ab0141d580cce, 0xca24f0eb806e7280, 0x1f9]) else (cbits [0xec80867280283b0, 0x80283b40259ca252, 0xa1db813ce5008076, 0x51e88772c383944a, 0x3f3940181ddb0e4e, 0xde98d0ef466877ac, 0x62c1])) else (if j < 61 then (cbits [0xf0989e728c43394, 0xa0253c47a21ca255, 0x81e200c4f1008078, 0x50060792f4539492, 0x503944aa1e5bd3ce, 0xca00c4f3404a79b2, 0x9289]) else (if j < 62 then (cbits [0x8f4925a4680303d0, 0x40343d400c9e9004, 0x11eb00d8f580487a, 0x692647ac04e3d602, 0x503d67a21eb18a0f, 0xefb0f8f4804a7a52, 0x31a1]) else (cbits [0xf8989c7a4c423d2, 0x83343e462b1e9252, 0xd1e93130f90c687c, 0xd2ab87a52503d262, 0x283eb0149f5a4cc8, 0xf69908fb404c7da3, 0x4961])))) else (if j < 65 then (if j < 64 then (cbits [0x8fac6527d6f443ed, 0x60243f44961f58ca, 0x71f5b104fad29c7d, 0xd24a07d66483f862, 0x443fb1a11fda4dc8, 0xffbd38fec0487faf, 0x3241]) else (cbits [0xc8d24b67f72503fb, 0x833c4041a7201a50, 0xf203992100c69080, 0x1cc6c80e62040718, 0x4c40c61ea0399390, 0x3bd3103989e80ec, 0x7a22])) else (if j < 66 then (cbits [0x900e4a080ef4e407, 0x803441461ea01992, 0xda01b12500d8b082, 0xde88806f5841862, 0x2441c928201bd690, 0x1995107a4b48060, 0xaae2]) else (if j < 67 then (cbits [0x508805084294b234, 0x2f44422496211193, 0x22138ca108405284, 0xa92988429424217a, 0x3e42a19e2158d090, 0x17a539085e888546, 0x3242]) else (cbits [0xc8d24a0842c59421, 0x6c554331ad219a53, 0xe219c9410cde8886, 0xe9e88468024438aa, 0x3643c00ca1d003d0, 0x1f30e10f80808780, 0x7a22]))))) else (if j < 73 then (if j < 70 then (if j < 69 then (cbits [0x10f009c87804243c, 0x8036444012a1d494, 0x9222013911008488, 0xea4a088833e44419, 0x3f43a01422580cd0, 0x27812d0e805089a0, 0x142]) else (cbits [0x114a4a287525043a, 0xa0244547a291a00c, 0x722a80d91540548a, 0x6a4b48a8f4e45502, 0x5a45c7a791a25511, 0x2e0d511746908ba3, 0x32a2])) else (if j < 71 then (cbits [0x9180c408c031e460, 0x895545c32b22e18a, 0xa000809119aab88b, 0xa8c548d200946818, 0x3846a49b23518811, 0x3700351b92588d2c, 0x61c2]) else (if j < 72 then (cbits [0xd1a40188e292d469, 0xa00f46849ba34a4c, 0x2a3b00651d80548e, 0xd8c6c8ec62047601, 0x2c47632723b19091, 0x3fa5091d926c8ec9, 0x1e2]) else (cbits [0x11d98708ec94e476, 0xa02b47592823b3d1, 0xaa4318812180848e, 0x1926a90c92c48631, 0x4e4867a224331392, 0x3ac94121809091af, 0x21a])))) else (if j < 75 then (if j < 74 then (cbits [0x52492588ea327475, 0x4f4449261c249003, 0x9a3aa4b51d64a092, 0xd526e8ea02849849, 0x4f4751a424da50d1, 0x3ac941279e888ea9, 0x7a7a]) else (cbits [0x12880268d03544a0, 0x60254a3006a51a4b, 0x6253a4b528987094, 0x892669440244a700, 0x1e4ac00da3424dd2, 0x56a4b12b4c4095a0, 0x4a12])) else (if j < 76 then (cbits [0x12b5e8895ac384ad, 0x8c424b401b256494, 0x825a3d112d189c96, 0xe4c409720424ac92, 0x444b962725ca4b12, 0x5649412e5e9c972f, 0x272]) else (if j < 77 then (cbits [0x530187098092c4c0, 0x8f444c4496256310, 0x726324b131928495, 0xb24a098cf444c662, 0x444cc61c256250d2, 0x56310d2b24a0998f, 0x627a]) else (cbits [0xd2b24a09a2f444ac, 0xa01f4689282563d3, 0xc26b0095358c409a, 0x68c669aa6214d561, 0x384d531ba6aa5013, 0x6a80c537401a9bac, 0x61ca])))))))) else (if j < 117 then (if j < 97 then (if j < 87 then (if j < 82 then (if j < 80 then (if j < 79 then (cbits [0xd1a00609c000c4e0, 0x86204e400f27180c, 0x827230e13912589c, 0xa4c409d202a4e392, 0x4e4e949b274a4b13, 0x71c9413a58709d29, 0x1b2]) else (cbits [0x13c189c9e06204f0, 0xa33f4f4026271c94, 0x1a7a0cd13d46509e, 0xd0c909f00484f81a, 0x444fb49627d98813, 0x7a18ad3d0c429e8f, 0x31fa])) else (if j < 81 then (cbits [0x14092589e86434f4, 0x8f444f44a1a7a3d1, 0x283813938de8a9e, 0x1d258a0e64150731, 0x2c4e3928283a5054, 0x71c941435870a1a9, 0x496a]) else (cbits [0x138d29e9c69374e3, 0x6c4f4e3928289b0e, 0x28b80dd1a24a09c, 0x69258a3003d51831, 0x4851c310a8b80f14, 0x8b98ad45cc4ea2e0, 0x4962]))) else (if j < 84 then (if j < 83 then (cbits [0x545c07aa4003c520, 0xa620468024291a4b, 0xb29300a949801ea4, 0x99870a4c04e52601, 0x3852c496292c9414, 0x9630e54b1e88a5ac, 0x621a]) else (cbits [0x94c4034a6292d525, 0xb250531627298b10, 0x629b18a54d9266a4, 0xd929ca6cf445384a, 0x3d53c49ba92c9414, 0x9e19314f8c7aa780, 0x7a22])) else (if j < 85 then (cbits [0xd4964a0a78f4e53c, 0x6349543024aa1a50, 0xaa19901518c92a8, 0x964a0a86f4454362, 0x214687a2a92bd114, 0xa700d953801ca9a6, 0x212]) else (if j < 86 then (cbits [0x1539284a9c04e54e, 0xa00f54d9282a73d1, 0xcaab8079534036a9, 0x35e88aae94255700, 0x2855c4992a680fd5, 0xae2509570c52ab83, 0x7a22]) else (cbits [0x9585884ac293654d, 0xb2505617a22b0b13, 0xeab30cf5599284a9, 0x98c98ad063456831, 0x4e5666272b330e15, 0xa6a50d5364a0accf, 0x4a52]))))) else (if j < 92 then (if j < 89 then (if j < 88 then (cbits [0x15c9280ae0629570, 0xa94e54d4a12b830e, 0xa2bbb13d535886a9, 0xe9e8aa9af4454d02, 0x5457c7a7aa680315, 0xbf989d1a24a0a9a0, 0xe2]) else (cbits [0xd5fc022b0201e57f, 0x802558418eabf807, 0x62c21909610c6ab0, 0xfc63eafef4458449, 0xe58b0062c598815, 0xc73139638c84afe0, 0x7a72])) else (if j < 90 then (cbits [0x164926aaff25058e, 0xa94e5944a12bfbd1, 0x22ca3139651280b2, 0xfd286aff2505947a, 0x2b4687a7abfbd115, 0xcf0109678062b3a6, 0x7a22]) else (if j < 91 then (cbits [0x1688662b3a03759d, 0x4f445a361c2d18d0, 0xbacebd11688684b4, 0x75898b5264359d19, 0xe5ac61c2ce993d6, 0xd7b109675e88b580, 0x1ea]) else (cbits [0x96bde88b5ec385af, 0xac4359d9282d7bd3, 0x2ace80f56d9e88b3, 0xe8c6e8d0f4f59d7a, 0x365bb0042dd80f56, 0xdd49416ec09cb760, 0x1fa])))) else (if j < 94 then (if j < 93 then (cbits [0x1708668b8233d5ba, 0x2f445c261c2e124b, 0xc2e38d3170466cb8, 0x469cb82f445c761, 0x3f5ba9282e0bd117, 0xe68d61734668b9a3, 0x3262]) else (cbits [0x1744090ba23435ba, 0x464b5ba92a2e8a52, 0x8add3d61758c9eb7, 0x69298bb03295d849, 0x4e5d87a22ed30e17, 0xdd24dd6e9e88bb09, 0x49ea])) else (if j < 95 then (cbits [0x178189cbc03295e0, 0x4c4c5e449fadd494, 0x62f3a53d6e9286b7, 0xe9ea8bcec3c5e862, 0x4e5ba7a72f5b0e16, 0xf6b0e17b4c94bdac, 0x61ea]) else (if j < 96 then (cbits [0xd6ea4a0bdaf445ed, 0x800e5f47a22dd313, 0x82fa01397d006cbe, 0xe9e96b74f455ba92, 0x495fc7a72dd49617, 0xdd49417f1e88bf80, 0x7a7a]) else (cbits [0x180a4a2b752505ba, 0xa31d60431fa34012, 0xb30224b1814c9ac0, 0x28c80c08c4260831, 0x3760a19a3058ccd8, 0x524dd828078c1a3, 0x61c3])))))) else (if j < 107 then (if j < 102 then (if j < 99 then (if j < 98 then (cbits [0x5848c84c08c3960a, 0x8f4461261c30924d, 0x2b02310d81129ac0, 0x68092c326434687a, 0x4961902130d00d98, 0xea4b1878668c3a3, 0x19b3]) else (cbits [0x9875870c4234061d, 0x29376191a7b0c8d0, 0x7b0c8ca5899292c3, 0x65886c32c396194a, 0x506197a230cb13d8, 0x3430e11a001cc5b2, 0x61ca])) else (if j < 100 then (cbits [0x18c8c92c62f4e630, 0x294963132031918d, 0x631bc9458c1e88c6, 0xe8092c72c4346800, 0x4b63901531d00218, 0x1f8ca18f8692c720, 0x3103]) else (if j < 101 then (cbits [0x1908696c7232a63e, 0xa34f63932c3210ca, 0x4b1c99519140a8c8, 0x28c96c7231d64832, 0x50639327b1ca5619, 0x1c80a993401cc9b2, 0x928b]) else (cbits [0x994801eca2315001, 0x603065301232980d, 0xb3290cc9948c50ca, 0x68c54cb201265149, 0x3665a31032d0c999, 0x2c806197925acb29, 0x499b])))) else (if j < 104 then (if j < 103 then (cbits [0xd94526ecb2628660, 0xa04266300f331809, 0xc331a50998cc68cc, 0xa864acd262a65161, 0x2c66b3103358cd19, 0x378d019a866ccd49, 0x61c3]) else (cbits [0x19c8698cd434266a, 0x434e66a7a2339188, 0x33b8c9d9a5258cd, 0xdc6b0cee34c6771a, 0x3c67c195b3498d19, 0x3f24d99f8c40cd2c, 0x4a73])) else (if j < 105 then (cbits [0xd9a4c66cd2621669, 0x803e68432133498d, 0x23421921a1989cd0, 0xa4090d126436697a, 0x32669496b34993d9, 0x34b139a34652d1a9, 0x499b]) else (if j < 106 then (cbits [0x9a4926ccd2c40690, 0xa94266949bb34b10, 0x1b34bd39a5407cd2, 0xa529ecd294e6694a, 0x3069b00634db0e59, 0x4fb13d9a5886cd20, 0x2a3]) else (cbits [0xd9a52a8d3e65469f, 0x66546a302a351bd3, 0x8b5398ad9452a8d4, 0xa0698d503406a819, 0x386a73213538d61a, 0x28b109a9d87cd4ec, 0x31f3]))))) else (if j < 112 then (if j < 109 then (if j < 108 then (cbits [0x1ac0c40d6231d6b0, 0x83346b418db5998a, 0x3598c7dacc698d6, 0xc0c56d666216b331, 0x366bb31035d98a9a, 0x5824d9aed258d766, 0x31b3]) else (cbits [0x994526ed6092d6b0, 0xa6276c3310b61990, 0x7b6198adb0cc98d8, 0x2929ed8692d6c332, 0x4a6cc7a73618151b, 0x678031b3925aca20, 0x1b3])) else (if j < 110 then (cbits [0x9b49266ca204e6cf, 0xa3296d218e36980a, 0x136b98a1b48060da, 0x48c54da46296d232, 0x4e6d200636da4b1b, 0x28b139b49882da49, 0x49bb]) else (if j < 111 then (cbits [0x1b8867adc003d6e0, 0x6426e01a63710ca, 0x73700031b99e88dc, 0xa9286ca20486e87a, 0x4e6eb01b3758121b, 0x778d25ba8094dd40, 0x1943]) else (cbits [0x9ba86b0dde3406ef, 0x4f5a6ea624b75193, 0xa37bc969baa4a0dd, 0xe86aadf294f65102, 0x4c6fa1a037d0ca1b, 0x7cb155be4cb4df23, 0xaae3])))) else (if j < 114 then (if j < 113 then (cbits [0x1c09e9eca200c700, 0x4056702015381815, 0xa3830ca1c186aae0, 0x92aae0465a70219, 0x2570c18f800d571c, 0x870c9dc38068e1a0, 0x195b]) else (cbits [0xdc38020e2233370e, 0xc33471419fb870cd, 0x5b87189dc38686e1, 0x68c7ee1c63770e31, 0x4370e32038d0071c, 0x8724b5c39258e1c6, 0x499b])) else (if j < 115 then (cbits [0xdc3926ee1c94c720, 0x83487244a1b8724f, 0x4393b10dc38c90e4, 0xa806ce1a6487271a, 0x3e72a31ab951895c, 0x952509ca9298e5a9, 0x4a73]) else (if j < 116 then (cbits [0x1ca8c90e60348730, 0xac4e72a62139530e, 0x9b9b0cadcd8098e1, 0xd866ee6c01073819, 0x4373619a39d8cfdc, 0x9b2531cf9266e6c3, 0x49bb]) else (cbits [0x1d09286e6c93f736, 0xcf447363243a10d2, 0xeba38139c35e8ae6, 0x29282e8e33474819, 0x507473243a50d21d, 0x8698ddc34c56e1b2, 0x31fb]))))))) else (if j < 136 then (if j < 126 then (if j < 121 then (if j < 119 then (if j < 118 then (cbits [0xdc34638ea001c750, 0x801c754325b86990, 0x7b869901d50638ea, 0x64068eb2c3f70d32, 0x4f70d621b86b161d, 0xae8071d78ca8ebac, 0x4aa3]) else (cbits [0x1d8804ee18028760, 0x402476419a3b1802, 0x63b30101d9803aec, 0xa8080ec405876602, 0x3c76b4983b580a5d, 0xb50cd9da9290ed69, 0x1a53])) else (if j < 120 then (cbits [0x9da8c84ed4334770, 0x464077300e3b9992, 0x43bba4f9da9258ed, 0xa9294ed494276a01, 0x4176261c3b52539d, 0xbe80a1df8098efa0, 0x2c3]) else (cbits [0x1e08084ec433477d, 0x493c7824983c10cd, 0x83c380a5e180b0ec, 0x1866cf0c94878749, 0x2c78619a3c58d29e, 0xc324d9e19264f0c9, 0x9283]))) else (if j < 123 then (if j < 122 then (cbits [0x9d88668f22059762, 0x63347941a43c9816, 0xa3b12551e4d290f2, 0x65878f3233576219, 0x4276219b3b13151e, 0xcf0071e78cacec46, 0x18e3]) else (cbits [0x9d89870ec464079e, 0x4c4276219a3d1b0f, 0xd3b10cd1e998acec, 0xa8684f5202b70c62, 0x487aa4a43d598c1e, 0xd78d59ea52a8f549, 0x1a03])) else (if j < 124 then (cbits [0x1ec9258f52c3c7af, 0xa93e7a962a3d930f, 0xe3dba509ea58a8f6, 0xa52a8f6e9487b701, 0x5a7a961e3dda559e, 0xd4a4c1ef40a8f7a9, 0x61e3]) else (if j < 125 then (cbits [0x9f0866ce18c547a9, 0xa3427c3008be18cc, 0x73e19881f0d278f8, 0x987cf86c387c34a, 0x147cc1a13e10cddf, 0xe69901f38c60f9a3, 0x49e3]) else (cbits [0x1f3069ef9834b7cc, 0xa6407d300ebe998c, 0xc3ea9881f54664fa, 0x4c678fb26427d361, 0x4e7cc31f3e624b1f, 0xeea501f78690fba6, 0x4a03]))))) else (if j < 131 then (if j < 128 then (if j < 127 then (cbits [0xdf31890fba9417dd, 0xa93c7cc4963e6193, 0xebe624b1f94052fc, 0x318b0fd294b7cc49, 0x5a7ec1a1be1253df, 0xe13d69fb1890fd83, 0x1a53]) else (cbits [0x1fc8680fe00117f0, 0x49327f24963f90c5, 0xe3fb8d09fc1870fe, 0x9870fe06207f049, 0x297fc3103e10d3df, 0xff9885f09870ff80, 0x1a3])) else (if j < 129 then (cbits [0x2008c7ef846337c2, 0x525a8024ad401253, 0xa403992df08c86f8, 0x8c9ef8525980731, 0x3770c32a405bd3df, 0x6804603869501a3, 0x1a74]) else (if j < 130 then (cbits [0x2034c8301a63e80d, 0xa94080d01a409a4b, 0xd406a53a03588502, 0x6867ee1925b80d4a, 0x3881a1a140d00460, 0x86310a06803903ac, 0x1a1b]) else (cbits [0xa08008104292c820, 0xc5b8204ad41024d, 0x8c138d29c324b504, 0xa125905031482800, 0x37828620415a4ce0, 0x13bd360a18870509, 0x19a4])))) else (if j < 133 then (if j < 132 then (cbits [0x20c4039062027830, 0xa02b83002041880a, 0x641b98820c0c6106, 0xc0c43060c4183749, 0x37830315c18189e0, 0x1f00760f92590606, 0x620c]) else (cbits [0xe0c003908292d830, 0xa336827620c1824d, 0x8c229896114c4108, 0x1587108a94284531, 0x1d84c496413bd361, 0x27a4b609de9b0980, 0xe4])) else (if j < 134 then (cbits [0xe09d8810a2933827, 0xec438274a1c13a4d, 0x8c2b8d2dc31e9b04, 0x652590b234085700, 0x4285761c42ca4da1, 0x2b80721798710ae3, 0x61f4]) else (if j < 135 then (cbits [0x2184cb30c234f70c, 0x2932861026431a4b, 0x638625621852850c, 0xa801f0d000986849, 0x1386818e43500a21, 0x3700a21b80670d00, 0x1a4]) else (cbits [0xa1a00b10dc04c86e, 0x694e8734a143980d, 0xbc34313a1cd8850e, 0xe40510f204b86801, 0x4187c02743401021, 0x3fb0fe1a009f0d09, 0x1a4])))))) else (if j < 146 then (if j < 141 then (if j < 138 then (if j < 137 then (cbits [0xe1a18b10fe63487f, 0xa054884627c34310, 0xa442195221008110, 0x2801d11292d70c4a, 0x4288900944480722, 0x47816a22526911a0, 0x4a64]) else (cbits [0xa225885112c3e889, 0xa93270c62d444b15, 0x744b24b225805312, 0x3069b132c4e89562, 0x4089c014c4da4cdc, 0x4e00d227806113a9, 0x7ad4])) else (if j < 139 then (cbits [0x22892b513694e89b, 0xac4089b4aa451252, 0x6453010229806314, 0x9588514ac388a502, 0x4189b7a7c52b13a2, 0x4db16a2b989d136c, 0x62b4]) else (if j < 140 then (cbits [0xa26deb1160c408b0, 0x6f5a89b7a744db16, 0x9c5ba4d9c324b713, 0xdc68117004c8b801, 0x388b77a445d80de2, 0x5b810a2f405317ac, 0x61cc]) else (cbits [0xa2dde99182c3f8b7, 0xef4e8c37a2461b10, 0xa463bd3e2dd88716, 0x2926ee18c548c71a, 0x588cb02646580f63, 0x67a55a32929d1940, 0x7ac4])))) else (if j < 143 then (if j < 142 then (cbits [0xa329e8919495a8ca, 0x925b8ca7ad4653d3, 0x646b80a6359294e1, 0x6987f1acc4d8d749, 0x438d662c46d24d23, 0x8631363592991bac, 0x4a5b]) else (cbits [0x23892b11c20298e0, 0xac588e04a1470012, 0x847281023980931c, 0x81e9f1c0c598e092, 0x4b8ec4a73863d663, 0x760d623b40691da0, 0x27c])) else (if j < 144 then (cbits [0x23c92671d89548f0, 0x89378ec4ac479253, 0x7c7631623d92971d, 0xe406d1f32508ec4a, 0x4f70c928c7601363, 0x7e81023f80ab1fa9, 0xaae4]) else (if j < 145 then (cbits [0x240806b202c3f70c, 0x23349014a6481a4f, 0xac80b0e241926920, 0x25295212c5890149, 0x5a901928484a53a4, 0x87b10dc312a921ac, 0x24c]) else (cbits [0x244006922001c910, 0xe94990f02d488016, 0x848bc94243d29d21, 0x692a9232c4f70c01, 0x4291a49648d00a64, 0x8f8ccc0052ab2329, 0x8c]))))) else (if j < 151 then (if j < 148 then (if j < 147 then (cbits [0x2480c41242341920, 0xa627920310c90188, 0xbc9018ae48126924, 0xa802723e93792031, 0x3492c0134958cd24, 0x95989a4acc412560, 0x4964]) else (cbits [0x24c806126233692a, 0x463093131249880d, 0xa48fa4ca4a925925, 0xe803727232891f18, 0x3493c00ec9d00224, 0x9f80d24e80992780, 0xec])) else (if j < 149 then (cbits [0x24fcc4127e32a93f, 0x404c94401ac9d24b, 0x549d0ca64e806d27, 0x2803f27292c93a19, 0x2093931b4a518825, 0xa6804e53401f29a6, 0x15c]) else (if j < 150 then (cbits [0xa54401d2a2621939, 0x293695101b4a8804, 0xe4ab80c6558c5727, 0x7d8712ac04c95700, 0x4095c013cad8ca64, 0xafa4b256c0572b60, 0xec]) else (cbits [0xe58865523e92d95b, 0x43349630204b1809, 0x8cb398da5880572c, 0x9cc412ce04c96801, 0x2c96231bcb130e25, 0xb124b658806d2da9, 0x49b4])))) else (if j < 153 then (if j < 152 then (cbits [0xe47d26f2c4c38970, 0x6040974018cb98ca, 0x7cbb8cda47d8712e, 0x7d26f2f264191f32, 0x1c97c01ecbda4de4, 0xbe01325f00512f80, 0x2c4]) else (cbits [0xc005e892f634297b, 0xa02898401ecc18cd, 0x3cc29886614c4130, 0x10c5730a31c98831, 0x2c98b31b4c580aa6, 0xc780d261126d3169, 0x313c])) else (if j < 154 then (cbits [0x263cc8731e62b98f, 0xe93f98f496cc7a4b, 0x4ccb80da61128731, 0xd26f308c3899731, 0x4899c320ccd810e6, 0xcfa50666cc933360, 0x244]) else (if j < 155 then (cbits [0x2688c5730634f983, 0xa63d983626cd130e, 0x1cc1a4b269803b34, 0xa00693520499a832, 0x3d9839284d425066, 0xc1b0e26b805335a9, 0x4a1c]) else (cbits [0x26c40513620499b0, 0xf5a9b0324cd8016, 0x3d1260e4a136]))))))))) 25 (i % 16)
def s68Links := pageLinks s68Index s68Codes 6 13 12 7
def s68Data (i : Nat) : Nat × Nat :=
  let e := s68Forest i
  (e &&& 4095, e >>> 12)
def s68Sample : Nat × Nat := (s68Blob374505, 96)
def s68Tags := dagTraceTags s68Mask 96 (dagTagBases s68StockWords s68Blob375072 s68Blob375270 96) 11 s68Data
def s68States := dagTrace s68Mask s68StockWords 11 s68Data
def s68MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm9, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 5, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 5, 4] 0 i.val))), (pm7, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 2, 1, 4, 3, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 2, 1, 4, 3, 5] 0 i.val))), (pm10, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 3, 1, 5, 2, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 2, 4, 1, 5, 3] 0 i.val))), (pm8, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 2, 4, 1, 5, 3] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 3, 1, 5, 2, 4] 0 i.val))), (pm2, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 3, 5, 1, 4, 2] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 3, 5, 1, 4, 2] 0 i.val))), (pm11, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 4, 2, 5, 1, 3] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 4, 2, 5, 1, 3] 0 i.val))), (pm12, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 5, 3, 4, 1, 2] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 4, 5, 2, 3, 1] 0 i.val))), (pm3, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 4, 5, 2, 3, 1] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 5, 3, 4, 1, 2] 0 i.val))), (pm16, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 5, 4, 3, 2, 1] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 5, 4, 3, 2, 1] 0 i.val)))]
def s68Moves := dagMoves s68MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Autos : DagMovesOK s68Mask s68Goal 64 s68Moves := dagMovesOfCheck (by decide +kernel)
def s68Check := dagCheckNode s68Mask s68Goal s68Chart (dagKnownCloses s68Goal s68Cuts) 2487 s68States s68Moves s68Links s68Sample s68Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Roots : dagCheckRoots s68Mask s68Goal s68Chart (dagKnownCloses s68Goal s68Cuts) s68Witnesses (dagRef 2487 s68States s68Moves s68Links 0) s68StockWords 11 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block0 : treeBlock 0 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block24 : treeBlock 24 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block48 : treeBlock 48 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block72 : treeBlock 72 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block96 : treeBlock 96 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block120 : treeBlock 120 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block144 : treeBlock 144 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block168 : treeBlock 168 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block192 : treeBlock 192 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block216 : treeBlock 216 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block240 : treeBlock 240 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block264 : treeBlock 264 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block288 : treeBlock 288 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block312 : treeBlock 312 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block336 : treeBlock 336 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block360 : treeBlock 360 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block384 : treeBlock 384 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block408 : treeBlock 408 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block432 : treeBlock 432 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block456 : treeBlock 456 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block480 : treeBlock 480 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block504 : treeBlock 504 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block528 : treeBlock 528 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block552 : treeBlock 552 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block576 : treeBlock 576 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block600 : treeBlock 600 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block624 : treeBlock 624 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block648 : treeBlock 648 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block672 : treeBlock 672 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block696 : treeBlock 696 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block720 : treeBlock 720 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block744 : treeBlock 744 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block768 : treeBlock 768 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block792 : treeBlock 792 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block816 : treeBlock 816 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block840 : treeBlock 840 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block864 : treeBlock 864 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block888 : treeBlock 888 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block912 : treeBlock 912 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block936 : treeBlock 936 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block960 : treeBlock 960 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block984 : treeBlock 984 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block1008 : treeBlock 1008 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block1032 : treeBlock 1032 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block1056 : treeBlock 1056 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block1080 : treeBlock 1080 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block1104 : treeBlock 1104 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block1128 : treeBlock 1128 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block1152 : treeBlock 1152 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block1176 : treeBlock 1176 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block1200 : treeBlock 1200 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block1224 : treeBlock 1224 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block1248 : treeBlock 1248 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block1272 : treeBlock 1272 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block1296 : treeBlock 1296 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block1320 : treeBlock 1320 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block1344 : treeBlock 1344 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block1368 : treeBlock 1368 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block1392 : treeBlock 1392 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block1416 : treeBlock 1416 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block1440 : treeBlock 1440 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block1464 : treeBlock 1464 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block1488 : treeBlock 1488 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block1512 : treeBlock 1512 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block1536 : treeBlock 1536 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block1560 : treeBlock 1560 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block1584 : treeBlock 1584 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block1608 : treeBlock 1608 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block1632 : treeBlock 1632 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block1656 : treeBlock 1656 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block1680 : treeBlock 1680 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block1704 : treeBlock 1704 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block1728 : treeBlock 1728 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block1752 : treeBlock 1752 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block1776 : treeBlock 1776 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block1800 : treeBlock 1800 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block1824 : treeBlock 1824 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block1848 : treeBlock 1848 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block1872 : treeBlock 1872 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block1896 : treeBlock 1896 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block1920 : treeBlock 1920 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block1944 : treeBlock 1944 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block1968 : treeBlock 1968 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block1992 : treeBlock 1992 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block2016 : treeBlock 2016 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block2040 : treeBlock 2040 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block2064 : treeBlock 2064 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block2088 : treeBlock 2088 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block2112 : treeBlock 2112 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block2136 : treeBlock 2136 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block2160 : treeBlock 2160 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block2184 : treeBlock 2184 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block2208 : treeBlock 2208 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block2232 : treeBlock 2232 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block2256 : treeBlock 2256 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block2280 : treeBlock 2280 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block2304 : treeBlock 2304 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block2328 : treeBlock 2328 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block2352 : treeBlock 2352 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block2376 : treeBlock 2376 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block2400 : treeBlock 2400 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block2424 : treeBlock 2424 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block2448 : treeBlock 2448 24 s68Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block2472 : treeBlock 2472 15 s68Check = true := by decide +kernel
theorem s68Group24_48 : treeBlock 24 48 s68Check = true := treeBlock_merge (start := 24) (left := 24) (right := 24) (check := s68Check) s68Block24 s68Block48
theorem s68Group0_72 : treeBlock 0 72 s68Check = true := treeBlock_merge (start := 0) (left := 24) (right := 48) (check := s68Check) s68Block0 s68Group24_48
theorem s68Group96_48 : treeBlock 96 48 s68Check = true := treeBlock_merge (start := 96) (left := 24) (right := 24) (check := s68Check) s68Block96 s68Block120
theorem s68Group72_72 : treeBlock 72 72 s68Check = true := treeBlock_merge (start := 72) (left := 24) (right := 48) (check := s68Check) s68Block72 s68Group96_48
theorem s68Group0_144 : treeBlock 0 144 s68Check = true := treeBlock_merge (start := 0) (left := 72) (right := 72) (check := s68Check) s68Group0_72 s68Group72_72
theorem s68Group168_48 : treeBlock 168 48 s68Check = true := treeBlock_merge (start := 168) (left := 24) (right := 24) (check := s68Check) s68Block168 s68Block192
theorem s68Group144_72 : treeBlock 144 72 s68Check = true := treeBlock_merge (start := 144) (left := 24) (right := 48) (check := s68Check) s68Block144 s68Group168_48
theorem s68Group216_48 : treeBlock 216 48 s68Check = true := treeBlock_merge (start := 216) (left := 24) (right := 24) (check := s68Check) s68Block216 s68Block240
theorem s68Group264_48 : treeBlock 264 48 s68Check = true := treeBlock_merge (start := 264) (left := 24) (right := 24) (check := s68Check) s68Block264 s68Block288
theorem s68Group216_96 : treeBlock 216 96 s68Check = true := treeBlock_merge (start := 216) (left := 48) (right := 48) (check := s68Check) s68Group216_48 s68Group264_48
theorem s68Group144_168 : treeBlock 144 168 s68Check = true := treeBlock_merge (start := 144) (left := 72) (right := 96) (check := s68Check) s68Group144_72 s68Group216_96
theorem s68Group0_312 : treeBlock 0 312 s68Check = true := treeBlock_merge (start := 0) (left := 144) (right := 168) (check := s68Check) s68Group0_144 s68Group144_168
theorem s68Group336_48 : treeBlock 336 48 s68Check = true := treeBlock_merge (start := 336) (left := 24) (right := 24) (check := s68Check) s68Block336 s68Block360
theorem s68Group312_72 : treeBlock 312 72 s68Check = true := treeBlock_merge (start := 312) (left := 24) (right := 48) (check := s68Check) s68Block312 s68Group336_48
theorem s68Group408_48 : treeBlock 408 48 s68Check = true := treeBlock_merge (start := 408) (left := 24) (right := 24) (check := s68Check) s68Block408 s68Block432
theorem s68Group384_72 : treeBlock 384 72 s68Check = true := treeBlock_merge (start := 384) (left := 24) (right := 48) (check := s68Check) s68Block384 s68Group408_48
theorem s68Group312_144 : treeBlock 312 144 s68Check = true := treeBlock_merge (start := 312) (left := 72) (right := 72) (check := s68Check) s68Group312_72 s68Group384_72
theorem s68Group480_48 : treeBlock 480 48 s68Check = true := treeBlock_merge (start := 480) (left := 24) (right := 24) (check := s68Check) s68Block480 s68Block504
theorem s68Group456_72 : treeBlock 456 72 s68Check = true := treeBlock_merge (start := 456) (left := 24) (right := 48) (check := s68Check) s68Block456 s68Group480_48
theorem s68Group528_48 : treeBlock 528 48 s68Check = true := treeBlock_merge (start := 528) (left := 24) (right := 24) (check := s68Check) s68Block528 s68Block552
theorem s68Group576_48 : treeBlock 576 48 s68Check = true := treeBlock_merge (start := 576) (left := 24) (right := 24) (check := s68Check) s68Block576 s68Block600
theorem s68Group528_96 : treeBlock 528 96 s68Check = true := treeBlock_merge (start := 528) (left := 48) (right := 48) (check := s68Check) s68Group528_48 s68Group576_48
theorem s68Group456_168 : treeBlock 456 168 s68Check = true := treeBlock_merge (start := 456) (left := 72) (right := 96) (check := s68Check) s68Group456_72 s68Group528_96
theorem s68Group312_312 : treeBlock 312 312 s68Check = true := treeBlock_merge (start := 312) (left := 144) (right := 168) (check := s68Check) s68Group312_144 s68Group456_168
theorem s68Group0_624 : treeBlock 0 624 s68Check = true := treeBlock_merge (start := 0) (left := 312) (right := 312) (check := s68Check) s68Group0_312 s68Group312_312
theorem s68Group648_48 : treeBlock 648 48 s68Check = true := treeBlock_merge (start := 648) (left := 24) (right := 24) (check := s68Check) s68Block648 s68Block672
theorem s68Group624_72 : treeBlock 624 72 s68Check = true := treeBlock_merge (start := 624) (left := 24) (right := 48) (check := s68Check) s68Block624 s68Group648_48
theorem s68Group720_48 : treeBlock 720 48 s68Check = true := treeBlock_merge (start := 720) (left := 24) (right := 24) (check := s68Check) s68Block720 s68Block744
theorem s68Group696_72 : treeBlock 696 72 s68Check = true := treeBlock_merge (start := 696) (left := 24) (right := 48) (check := s68Check) s68Block696 s68Group720_48
theorem s68Group624_144 : treeBlock 624 144 s68Check = true := treeBlock_merge (start := 624) (left := 72) (right := 72) (check := s68Check) s68Group624_72 s68Group696_72
theorem s68Group792_48 : treeBlock 792 48 s68Check = true := treeBlock_merge (start := 792) (left := 24) (right := 24) (check := s68Check) s68Block792 s68Block816
theorem s68Group768_72 : treeBlock 768 72 s68Check = true := treeBlock_merge (start := 768) (left := 24) (right := 48) (check := s68Check) s68Block768 s68Group792_48
theorem s68Group840_48 : treeBlock 840 48 s68Check = true := treeBlock_merge (start := 840) (left := 24) (right := 24) (check := s68Check) s68Block840 s68Block864
theorem s68Group888_48 : treeBlock 888 48 s68Check = true := treeBlock_merge (start := 888) (left := 24) (right := 24) (check := s68Check) s68Block888 s68Block912
theorem s68Group840_96 : treeBlock 840 96 s68Check = true := treeBlock_merge (start := 840) (left := 48) (right := 48) (check := s68Check) s68Group840_48 s68Group888_48
theorem s68Group768_168 : treeBlock 768 168 s68Check = true := treeBlock_merge (start := 768) (left := 72) (right := 96) (check := s68Check) s68Group768_72 s68Group840_96
theorem s68Group624_312 : treeBlock 624 312 s68Check = true := treeBlock_merge (start := 624) (left := 144) (right := 168) (check := s68Check) s68Group624_144 s68Group768_168
theorem s68Group960_48 : treeBlock 960 48 s68Check = true := treeBlock_merge (start := 960) (left := 24) (right := 24) (check := s68Check) s68Block960 s68Block984
theorem s68Group936_72 : treeBlock 936 72 s68Check = true := treeBlock_merge (start := 936) (left := 24) (right := 48) (check := s68Check) s68Block936 s68Group960_48
theorem s68Group1032_48 : treeBlock 1032 48 s68Check = true := treeBlock_merge (start := 1032) (left := 24) (right := 24) (check := s68Check) s68Block1032 s68Block1056
theorem s68Group1008_72 : treeBlock 1008 72 s68Check = true := treeBlock_merge (start := 1008) (left := 24) (right := 48) (check := s68Check) s68Block1008 s68Group1032_48
theorem s68Group936_144 : treeBlock 936 144 s68Check = true := treeBlock_merge (start := 936) (left := 72) (right := 72) (check := s68Check) s68Group936_72 s68Group1008_72
theorem s68Group1104_48 : treeBlock 1104 48 s68Check = true := treeBlock_merge (start := 1104) (left := 24) (right := 24) (check := s68Check) s68Block1104 s68Block1128
theorem s68Group1080_72 : treeBlock 1080 72 s68Check = true := treeBlock_merge (start := 1080) (left := 24) (right := 48) (check := s68Check) s68Block1080 s68Group1104_48
theorem s68Group1152_48 : treeBlock 1152 48 s68Check = true := treeBlock_merge (start := 1152) (left := 24) (right := 24) (check := s68Check) s68Block1152 s68Block1176
theorem s68Group1200_48 : treeBlock 1200 48 s68Check = true := treeBlock_merge (start := 1200) (left := 24) (right := 24) (check := s68Check) s68Block1200 s68Block1224
theorem s68Group1152_96 : treeBlock 1152 96 s68Check = true := treeBlock_merge (start := 1152) (left := 48) (right := 48) (check := s68Check) s68Group1152_48 s68Group1200_48
theorem s68Group1080_168 : treeBlock 1080 168 s68Check = true := treeBlock_merge (start := 1080) (left := 72) (right := 96) (check := s68Check) s68Group1080_72 s68Group1152_96
theorem s68Group936_312 : treeBlock 936 312 s68Check = true := treeBlock_merge (start := 936) (left := 144) (right := 168) (check := s68Check) s68Group936_144 s68Group1080_168
theorem s68Group624_624 : treeBlock 624 624 s68Check = true := treeBlock_merge (start := 624) (left := 312) (right := 312) (check := s68Check) s68Group624_312 s68Group936_312
theorem s68Group0_1248 : treeBlock 0 1248 s68Check = true := treeBlock_merge (start := 0) (left := 624) (right := 624) (check := s68Check) s68Group0_624 s68Group624_624
theorem s68Group1272_48 : treeBlock 1272 48 s68Check = true := treeBlock_merge (start := 1272) (left := 24) (right := 24) (check := s68Check) s68Block1272 s68Block1296
theorem s68Group1248_72 : treeBlock 1248 72 s68Check = true := treeBlock_merge (start := 1248) (left := 24) (right := 48) (check := s68Check) s68Block1248 s68Group1272_48
theorem s68Group1344_48 : treeBlock 1344 48 s68Check = true := treeBlock_merge (start := 1344) (left := 24) (right := 24) (check := s68Check) s68Block1344 s68Block1368
theorem s68Group1320_72 : treeBlock 1320 72 s68Check = true := treeBlock_merge (start := 1320) (left := 24) (right := 48) (check := s68Check) s68Block1320 s68Group1344_48
theorem s68Group1248_144 : treeBlock 1248 144 s68Check = true := treeBlock_merge (start := 1248) (left := 72) (right := 72) (check := s68Check) s68Group1248_72 s68Group1320_72
theorem s68Group1416_48 : treeBlock 1416 48 s68Check = true := treeBlock_merge (start := 1416) (left := 24) (right := 24) (check := s68Check) s68Block1416 s68Block1440
theorem s68Group1392_72 : treeBlock 1392 72 s68Check = true := treeBlock_merge (start := 1392) (left := 24) (right := 48) (check := s68Check) s68Block1392 s68Group1416_48
theorem s68Group1464_48 : treeBlock 1464 48 s68Check = true := treeBlock_merge (start := 1464) (left := 24) (right := 24) (check := s68Check) s68Block1464 s68Block1488
theorem s68Group1512_48 : treeBlock 1512 48 s68Check = true := treeBlock_merge (start := 1512) (left := 24) (right := 24) (check := s68Check) s68Block1512 s68Block1536
theorem s68Group1464_96 : treeBlock 1464 96 s68Check = true := treeBlock_merge (start := 1464) (left := 48) (right := 48) (check := s68Check) s68Group1464_48 s68Group1512_48
theorem s68Group1392_168 : treeBlock 1392 168 s68Check = true := treeBlock_merge (start := 1392) (left := 72) (right := 96) (check := s68Check) s68Group1392_72 s68Group1464_96
theorem s68Group1248_312 : treeBlock 1248 312 s68Check = true := treeBlock_merge (start := 1248) (left := 144) (right := 168) (check := s68Check) s68Group1248_144 s68Group1392_168
theorem s68Group1584_48 : treeBlock 1584 48 s68Check = true := treeBlock_merge (start := 1584) (left := 24) (right := 24) (check := s68Check) s68Block1584 s68Block1608
theorem s68Group1560_72 : treeBlock 1560 72 s68Check = true := treeBlock_merge (start := 1560) (left := 24) (right := 48) (check := s68Check) s68Block1560 s68Group1584_48
theorem s68Group1656_48 : treeBlock 1656 48 s68Check = true := treeBlock_merge (start := 1656) (left := 24) (right := 24) (check := s68Check) s68Block1656 s68Block1680
theorem s68Group1632_72 : treeBlock 1632 72 s68Check = true := treeBlock_merge (start := 1632) (left := 24) (right := 48) (check := s68Check) s68Block1632 s68Group1656_48
theorem s68Group1560_144 : treeBlock 1560 144 s68Check = true := treeBlock_merge (start := 1560) (left := 72) (right := 72) (check := s68Check) s68Group1560_72 s68Group1632_72
theorem s68Group1728_48 : treeBlock 1728 48 s68Check = true := treeBlock_merge (start := 1728) (left := 24) (right := 24) (check := s68Check) s68Block1728 s68Block1752
theorem s68Group1704_72 : treeBlock 1704 72 s68Check = true := treeBlock_merge (start := 1704) (left := 24) (right := 48) (check := s68Check) s68Block1704 s68Group1728_48
theorem s68Group1776_48 : treeBlock 1776 48 s68Check = true := treeBlock_merge (start := 1776) (left := 24) (right := 24) (check := s68Check) s68Block1776 s68Block1800
theorem s68Group1824_48 : treeBlock 1824 48 s68Check = true := treeBlock_merge (start := 1824) (left := 24) (right := 24) (check := s68Check) s68Block1824 s68Block1848
theorem s68Group1776_96 : treeBlock 1776 96 s68Check = true := treeBlock_merge (start := 1776) (left := 48) (right := 48) (check := s68Check) s68Group1776_48 s68Group1824_48
theorem s68Group1704_168 : treeBlock 1704 168 s68Check = true := treeBlock_merge (start := 1704) (left := 72) (right := 96) (check := s68Check) s68Group1704_72 s68Group1776_96
theorem s68Group1560_312 : treeBlock 1560 312 s68Check = true := treeBlock_merge (start := 1560) (left := 144) (right := 168) (check := s68Check) s68Group1560_144 s68Group1704_168
theorem s68Group1248_624 : treeBlock 1248 624 s68Check = true := treeBlock_merge (start := 1248) (left := 312) (right := 312) (check := s68Check) s68Group1248_312 s68Group1560_312
theorem s68Group1896_48 : treeBlock 1896 48 s68Check = true := treeBlock_merge (start := 1896) (left := 24) (right := 24) (check := s68Check) s68Block1896 s68Block1920
theorem s68Group1872_72 : treeBlock 1872 72 s68Check = true := treeBlock_merge (start := 1872) (left := 24) (right := 48) (check := s68Check) s68Block1872 s68Group1896_48
theorem s68Group1968_48 : treeBlock 1968 48 s68Check = true := treeBlock_merge (start := 1968) (left := 24) (right := 24) (check := s68Check) s68Block1968 s68Block1992
theorem s68Group1944_72 : treeBlock 1944 72 s68Check = true := treeBlock_merge (start := 1944) (left := 24) (right := 48) (check := s68Check) s68Block1944 s68Group1968_48
theorem s68Group1872_144 : treeBlock 1872 144 s68Check = true := treeBlock_merge (start := 1872) (left := 72) (right := 72) (check := s68Check) s68Group1872_72 s68Group1944_72
theorem s68Group2040_48 : treeBlock 2040 48 s68Check = true := treeBlock_merge (start := 2040) (left := 24) (right := 24) (check := s68Check) s68Block2040 s68Block2064
theorem s68Group2016_72 : treeBlock 2016 72 s68Check = true := treeBlock_merge (start := 2016) (left := 24) (right := 48) (check := s68Check) s68Block2016 s68Group2040_48
theorem s68Group2088_48 : treeBlock 2088 48 s68Check = true := treeBlock_merge (start := 2088) (left := 24) (right := 24) (check := s68Check) s68Block2088 s68Block2112
theorem s68Group2136_48 : treeBlock 2136 48 s68Check = true := treeBlock_merge (start := 2136) (left := 24) (right := 24) (check := s68Check) s68Block2136 s68Block2160
theorem s68Group2088_96 : treeBlock 2088 96 s68Check = true := treeBlock_merge (start := 2088) (left := 48) (right := 48) (check := s68Check) s68Group2088_48 s68Group2136_48
theorem s68Group2016_168 : treeBlock 2016 168 s68Check = true := treeBlock_merge (start := 2016) (left := 72) (right := 96) (check := s68Check) s68Group2016_72 s68Group2088_96
theorem s68Group1872_312 : treeBlock 1872 312 s68Check = true := treeBlock_merge (start := 1872) (left := 144) (right := 168) (check := s68Check) s68Group1872_144 s68Group2016_168
theorem s68Group2208_48 : treeBlock 2208 48 s68Check = true := treeBlock_merge (start := 2208) (left := 24) (right := 24) (check := s68Check) s68Block2208 s68Block2232
theorem s68Group2184_72 : treeBlock 2184 72 s68Check = true := treeBlock_merge (start := 2184) (left := 24) (right := 48) (check := s68Check) s68Block2184 s68Group2208_48
theorem s68Group2280_48 : treeBlock 2280 48 s68Check = true := treeBlock_merge (start := 2280) (left := 24) (right := 24) (check := s68Check) s68Block2280 s68Block2304
theorem s68Group2256_72 : treeBlock 2256 72 s68Check = true := treeBlock_merge (start := 2256) (left := 24) (right := 48) (check := s68Check) s68Block2256 s68Group2280_48
theorem s68Group2184_144 : treeBlock 2184 144 s68Check = true := treeBlock_merge (start := 2184) (left := 72) (right := 72) (check := s68Check) s68Group2184_72 s68Group2256_72
theorem s68Group2352_48 : treeBlock 2352 48 s68Check = true := treeBlock_merge (start := 2352) (left := 24) (right := 24) (check := s68Check) s68Block2352 s68Block2376
theorem s68Group2328_72 : treeBlock 2328 72 s68Check = true := treeBlock_merge (start := 2328) (left := 24) (right := 48) (check := s68Check) s68Block2328 s68Group2352_48
theorem s68Group2400_48 : treeBlock 2400 48 s68Check = true := treeBlock_merge (start := 2400) (left := 24) (right := 24) (check := s68Check) s68Block2400 s68Block2424
theorem s68Group2448_39 : treeBlock 2448 39 s68Check = true := treeBlock_merge (start := 2448) (left := 24) (right := 15) (check := s68Check) s68Block2448 s68Block2472
theorem s68Group2400_87 : treeBlock 2400 87 s68Check = true := treeBlock_merge (start := 2400) (left := 48) (right := 39) (check := s68Check) s68Group2400_48 s68Group2448_39
theorem s68Group2328_159 : treeBlock 2328 159 s68Check = true := treeBlock_merge (start := 2328) (left := 72) (right := 87) (check := s68Check) s68Group2328_72 s68Group2400_87
theorem s68Group2184_303 : treeBlock 2184 303 s68Check = true := treeBlock_merge (start := 2184) (left := 144) (right := 159) (check := s68Check) s68Group2184_144 s68Group2328_159
theorem s68Group1872_615 : treeBlock 1872 615 s68Check = true := treeBlock_merge (start := 1872) (left := 312) (right := 303) (check := s68Check) s68Group1872_312 s68Group2184_303
theorem s68Group1248_1239 : treeBlock 1248 1239 s68Check = true := treeBlock_merge (start := 1248) (left := 624) (right := 615) (check := s68Check) s68Group1248_624 s68Group1872_615
theorem s68Group0_2487 : treeBlock 0 2487 s68Check = true := treeBlock_merge (start := 0) (left := 1248) (right := 1239) (check := s68Check) s68Group0_1248 s68Group1248_1239
theorem s68Blocks : treeBlock 0 2487 s68Check = true := s68Group0_2487
theorem s68Known : Known s68Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s67Stock) s66Stock) s65Stock) s6Stock) s64Stock) s5Stock) s63Stock) s4Stock) s0Stock) s12Stock) s3Stock) s2Stock) s62Stock) s61Stock) s1Stock) s34Stock) s60Stock) s27Stock) s59Stock) s58Stock) s33Stock) s57Stock) s56Stock) s55Stock) s54Stock) s53Stock) s52Stock) s51Stock) s50Stock) s49Stock) s35Stock) s48Stock) s47Stock) s46Stock) s45Stock) s44Stock) s43Stock) s42Stock) s41Stock) s40Stock) s39Stock) s38Stock) s37Stock) s36Stock) s29Stock) s28Stock) s17Stock) s16Stock) s15Stock) s14Stock) s13Stock) s7Stock) s11Stock) s10Stock) s9Stock) s8Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Stock : Lower s68Mask s68StockWords s68Goal 12 := by
  apply lowerDag _ _ _ _ s68Autos _ _ _ s68Known _ s68Roots s68Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s68Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
end PEqualNP.Outside.L_meta_39353

open PEqualNP.Outside.L_meta_39353 in
theorem PEqualNP.Outside.L_meta_39353 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074666 * 2 ^ 32 + 4272597672) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074666 * 2 ^ 32 + 4272597672) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  intro t h
  let raw : List (BitVec 64) := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
  let goal : BitVec 64 := 0xfeeefaeafeaaaaa8
  have root : Lower (fullMask 64) (raw.map BitVec.toNat) goal.toNat 12 :=
    hcsLowerEq (by decide +kernel) (by decide +kernel) (by decide +kernel) s68Stock
  have size : 12 ≤ t :=
    hcsLower (n := 6) raw goal 12 _ (by decide +kernel) (by decide +kernel) root t h
  let circuit : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [0, 1]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [6, 5]⟩, ⟨.or, [8, 3]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [0, 10]⟩, ⟨.and, [7, 9]⟩, ⟨.or, [0, 12]⟩, ⟨.or, [7, 9]⟩, ⟨.and, [11, 14]⟩, ⟨.or, [15, 4]⟩, ⟨.and, [13, 16]⟩], 17⟩
  refine ⟨circuit, ?_, ?_, by decide +kernel⟩
  · intro gate member
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · exact Nat.le_trans (by decide +kernel : circuit.size ≤ 12) size

