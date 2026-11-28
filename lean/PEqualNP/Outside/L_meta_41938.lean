import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_41938

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
def sGoal : Nat := 0xfee8eee8eee8e8e0
def cbits (ws : List Nat) : Nat := ws.foldr (fun a z => (z <<< 64) ||| a) 0
def s0Blob175105 : Nat := (cbits [0x34120d0502c120b, 0x4100b06038140e06, 0x40f0483c100e0403, 0xe05034180b0603c1, 0x403c120])
def s0Blob175230 : Nat := 0xefbcdf73becf
def s0Blob175271 : Nat := 0x182824124205
def s0Mask : Nat := 0xff00
abbrev s0Goal : Nat := sGoal &&& s0Mask
abbrev s0StockWords : List Nat := [0xaa00, 0xcc00, 0xf000]
def s0Fact : Nat × List Nat × Nat × Nat := (s0Mask, s0StockWords, 4, s0Goal)
def s0Cuts : List (Nat × List Nat × Nat × Nat) := []
def s0Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[11, 13, 14, 11, 13, 14, 11, 13, 14, 11, 13, 14, 9, 10, 12, 9, 10, 12, 9, 10, 12, 9, 10, 12], rfl⟩
def s0Witnesses := unpackWitnesses s0StockWords [5642, 267785, 530953]
def s0Index (i : Nat) : Nat := unpack 0x9 2 i
def s0Codes (i : Nat) : Nat := unpack 0x7 15 i
def s0Forest (i : Nat) : Nat := unpack 0xe 14 i
def s0Links := pageLinks s0Index s0Codes 1 13 1 2
def s0Data (i : Nat) : Nat × Nat :=
  let e := s0Forest i
  (e &&& 1, e >>> 1)
def s0Sample : Nat × Nat := (s0Blob175105, 16)
def s0Tags := dagTraceTags s0Mask 16 (dagTagBases s0StockWords s0Blob175230 s0Blob175271 16) 3 s0Data
def s0States := dagTrace s0Mask s0StockWords 3 s0Data
def s0MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s0Moves := dagMoves s0MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Autos : DagMovesOK s0Mask s0Goal 64 s0Moves := dagMovesOfCheck (by decide +kernel)
def s0Check := dagCheckNode s0Mask s0Goal s0Chart (dagKnownCloses s0Goal s0Cuts) 1 s0States s0Moves s0Links s0Sample s0Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Roots : dagCheckRoots s0Mask s0Goal s0Chart (dagKnownCloses s0Goal s0Cuts) s0Witnesses (dagRef 1 s0States s0Moves s0Links 0) s0StockWords 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Block0 : treeBlock 0 1 s0Check = true := by decide +kernel
theorem s0Blocks : treeBlock 0 1 s0Check = true := s0Block0
theorem s0Known : Known s0Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Stock : Lower s0Mask s0StockWords s0Goal 4 := by
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
def st12 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xc3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c, 2)], [(0x3030303030303030, 2)])
def pm0 : List (List (Nat × Nat) × List (Nat × Nat)) := [st12]
def st01 : List (Nat × Nat) × List (Nat × Nat) := ([( 0x9999999999999999, 0), (0x2222222222222222, 1)], [(0x4444444444444444, 1)])
def pm1 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01]
def st02 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xa5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a, 3)], [(0x5050505050505050, 3)])
def pm2 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01, st02]
def pm3 : List (List (Nat × Nat) × List (Nat × Nat)) := [st02, st01]
def s1Blob178829 : Nat := (cbits [0x34120d0502c120b, 0x8703906038140e06, 0xd0402c703c1c0e, 0xf0503c120f040381, 0xc0ec143a048e4180, 0x2c703e1c0f4183c1, 0x100f04838140d060, 0x3b048ec103a040e4, 0x60f4123d040f014, 0x2c703f060f8143e, 0x414391c038700d1c, 0x3b060e8123a060e, 0xe040f4143c048f01, 0x60fc143f048fc103, 0xf8143d060ec700f0, 0x103f048])
def s1Blob179169 : Nat := (cbits [0x59dfa4dcdb6af64f, 0x1f4f37e3978ed9bd, 0xc3f0381dfe0df877, 0xf7ff8ff])
def s1Blob179275 : Nat := (cbits [0x920890048809005, 0x100a088820882090, 0x340380280a0a009, 0x800780])
def s1Mask : Nat := 0xff0000000000ff00
abbrev s1Goal : Nat := sGoal &&& s1Mask
abbrev s1StockWords : List Nat := [0xaa0000000000aa00, 0xcc0000000000cc00, 0xf00000000000f000, 0xff00000000000000]
def s1Fact : Nat × List Nat × Nat × Nat := (s1Mask, s1StockWords, 7, s1Goal)
def s1Cuts : List (Nat × List Nat × Nat × Nat) := [s0Fact]
def s1Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[11, 13, 14, 57, 58, 60, 11, 13, 14, 57, 58, 60, 9, 10, 12, 56, 9, 10, 12, 56, 9, 10, 12, 56], rfl⟩
def s1Witnesses := unpackWitnesses s1StockWords [5642, 267785, 530953, 815625]
def s1Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0x4028050088c18001, 0x44c8180b005c2a0d, 0x84308200b656]) else 0x9c730622440) 11 (i % 16)
def s1Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0x820024040100000f, 0xc940361601305007, 0xa823141001595807, 0xb8b18fc28c6d1062, 0x5b2188584c40a032, 0x7031]) else (if j < 2 then (cbits [0x111880086282492c, 0x200680c02803496, 0x81201007008050c7, 0xa0a0060480a01c03, 0xb260ca83806c1802, 0x4e19]) else (cbits [0x700483c0501a01c, 0xc4c52223292e00f, 0x8866200318a07804, 0x18d25]))) 21 (i % 16)
def s1Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0x60862820040401e0, 0xc050600784012149, 0x3860082406860081, 0xc00e34054c009846, 0x143c06c]) else 0x12581194c40561) 18 (i % 16)
def s1Links := pageLinks s1Index s1Codes 5 13 5 6
def s1Data (i : Nat) : Nat × Nat :=
  let e := s1Forest i
  (e &&& 31, e >>> 5)
def s1Sample : Nat × Nat := (s1Blob178829, 55)
def s1Tags := dagTraceTags s1Mask 55 (dagTagBases s1StockWords s1Blob179169 s1Blob179275 55) 6 s1Data
def s1States := dagTrace s1Mask s1StockWords 6 s1Data
def s1MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm0, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 2, 1, 3, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 2, 1, 3, 4, 5] 0 i.val))), (pm1, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val))), (pm2, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [2, 0, 1, 3, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 2, 0, 3, 4, 5] 0 i.val))), (pm3, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 2, 0, 3, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [2, 0, 1, 3, 4, 5] 0 i.val)))]
def s1Moves := dagMoves s1MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s1Autos : DagMovesOK s1Mask s1Goal 64 s1Moves := dagMovesOfCheck (by decide +kernel)
def s1Check := dagCheckNode s1Mask s1Goal s1Chart (dagKnownCloses s1Goal s1Cuts) 19 s1States s1Moves s1Links s1Sample s1Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s1Roots : dagCheckRoots s1Mask s1Goal s1Chart (dagKnownCloses s1Goal s1Cuts) s1Witnesses (dagRef 19 s1States s1Moves s1Links 0) s1StockWords 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s1Block0 : treeBlock 0 19 s1Check = true := by decide +kernel
theorem s1Blocks : treeBlock 0 19 s1Check = true := s1Block0
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
def st24 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xf0f00f0ff0f00f0f, 0), (0xf0f00000f0f0, 12)], [(0xf0f00000f0f0000, 12)])
def st25 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xf0f0f0f00f0f0f0f, 0), (0xf0f0f0f0, 28)], [(0xf0f0f0f00000000, 28)])
def pm4 : List (List (Nat × Nat) × List (Nat × Nat)) := [st24, st25]
def s2Mask : Nat := 0xf0000f00f0000f00
abbrev s2Goal : Nat := sGoal &&& s2Mask
abbrev s2StockWords : List Nat := [0xa0000a00a0000a00, 0xc0000c00c0000c00, 0xf0000000f0000000, 0xf0000f0000000000]
def s2Fact : Nat × List Nat × Nat × Nat := (s2Mask, s2StockWords, 7, s2Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Stock : Lower s2Mask s2StockWords s2Goal 7 := dagShiftLower (width := 64) pm4 s1Stock (by decide +kernel)
def pm5 : List (List (Nat × Nat) × List (Nat × Nat)) := [st24]
def s3Mask : Nat := 0xf000f0000f000f00
abbrev s3Goal : Nat := sGoal &&& s3Mask
abbrev s3StockWords : List Nat := [0xa000a0000a000a00, 0xc000c0000c000c00, 0xf000f00000000000, 0xf00000000f000000]
def s3Fact : Nat × List Nat × Nat × Nat := (s3Mask, s3StockWords, 7, s3Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s3Stock : Lower s3Mask s3StockWords s3Goal 7 := dagShiftLower (width := 64) pm5 s1Stock (by decide +kernel)
def s4Blob183857 : Nat := (cbits [0x64121906034120d, 0x45029048a4381d0c, 0x83c0e0f07039160b, 0xd0e034100d1c0f05, 0xc064381904064580, 0xa4301d06074121d1, 0x122d1c0a45829040, 0x39048e4502d060b4, 0xc0f0183c140e430, 0xf4583d0e0f4503c, 0x4181914034300d1c, 0x1d16074101d1406, 0xd040b43029060a47, 0xe0e410391c0b4382, 0xf4123d040f058390, 0x700d140f4303d060, 0x2d0e0a4501d16064, 0x40f4123c060e430])
def s4Blob184247 : Nat := (cbits [0xbff7fffe3ffff1ff, 0xd5f8e73fc71c7e93, 0xe6ff07cff81f8f1c, 0xf8fff80fffe00fe0])
def s4Blob184362 : Nat := (cbits [0x4010000009040025, 0x2a264a4642496692, 0x1942d41a90932b18, 0x78486ad24c24dc0])
def s4Mask : Nat := 0x3300330033003300
abbrev s4Goal : Nat := sGoal &&& s4Mask
abbrev s4StockWords : List Nat := [0x2200220022002200, 0x3000300030003000, 0x3300000033000000, 0x3300330000000000]
def s4Fact : Nat × List Nat × Nat × Nat := (s4Mask, s4StockWords, 6, s4Goal)
def s4Cuts : List (Nat × List Nat × Nat × Nat) := []
def s4Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[13, 25, 41, 60, 13, 25, 41, 60, 13, 25, 41, 60, 9, 28, 44, 56, 9, 28, 44, 56, 9, 28, 44, 56], rfl⟩
def s4Witnesses := unpackWitnesses s4StockWords [6668, 268809, 537097, 807433]
def s4Index (i : Nat) : Nat := unpack 0xa28301 6 i
def s4Codes (i : Nat) : Nat := unpack (cbits [0x31010c504010000f, 0x1492c6]) 17 i
def s4Forest (i : Nat) : Nat := unpack 0x3144010803c 15 i
def s4Links := pageLinks s4Index s4Codes 3 13 2 4
def s4Data (i : Nat) : Nat × Nat :=
  let e := s4Forest i
  (e &&& 3, e >>> 2)
def s4Sample : Nat × Nat := (s4Blob183857, 64)
def s4Tags := dagTraceTags s4Mask 64 (dagTagBases s4StockWords s4Blob184247 s4Blob184362 64) 5 s4Data
def s4States := dagTrace s4Mask s4StockWords 5 s4Data
def s4MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm5, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 4, 3, 2, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 4, 3, 2, 5] 0 i.val))), (pm4, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 5, 3, 2, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 4, 3, 5, 2] 0 i.val)))]
def s4Moves := dagMoves s4MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s4Autos : DagMovesOK s4Mask s4Goal 64 s4Moves := dagMovesOfCheck (by decide +kernel)
def s4Check := dagCheckNode s4Mask s4Goal s4Chart (dagKnownCloses s4Goal s4Cuts) 3 s4States s4Moves s4Links s4Sample s4Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s4Roots : dagCheckRoots s4Mask s4Goal s4Chart (dagKnownCloses s4Goal s4Cuts) s4Witnesses (dagRef 3 s4States s4Moves s4Links 0) s4StockWords 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s4Block0 : treeBlock 0 3 s4Check = true := by decide +kernel
theorem s4Blocks : treeBlock 0 3 s4Check = true := s4Block0
theorem s4Known : Known s4Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s4Stock : Lower s4Mask s4StockWords s4Goal 6 := by
  apply lowerDag _ _ _ _ s4Autos _ _ _ s4Known _ s4Roots s4Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s4Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def s5Mask : Nat := 0x5500550055005500
abbrev s5Goal : Nat := sGoal &&& s5Mask
abbrev s5StockWords : List Nat := [0x4400440044004400, 0x5000500050005000, 0x5500000055000000, 0x5500550000000000]
def s5Fact : Nat × List Nat × Nat × Nat := (s5Mask, s5StockWords, 6, s5Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s5Stock : Lower s5Mask s5StockWords s5Goal 6 := dagShiftLower (width := 64) pm1 s4Stock (by decide +kernel)
def s6Mask : Nat := 0xff00ff00
abbrev s6Goal : Nat := sGoal &&& s6Mask
abbrev s6StockWords : List Nat := [0xaa00aa00, 0xcc00cc00, 0xf000f000, 0xff000000]
def s6Fact : Nat × List Nat × Nat × Nat := (s6Mask, s6StockWords, 5, s6Goal)
def s6Witnesses := unpackWitnesses s6StockWords [5642, 267785, 530953, 799241]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6Stock : Lower s6Mask s6StockWords s6Goal 5 := by
  apply essentialLift (witnesses := s6Witnesses) (cut := s0Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s0StockWords) (by decide +kernel)
  · exact s0Stock
  · decide +kernel
def st45 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xffff00000000ffff, 0), (0xffff0000, 16)], [(0xffff00000000, 16)])
def pm6 : List (List (Nat × Nat) × List (Nat × Nat)) := [st45]
def s7Mask : Nat := 0xff000000ff00
abbrev s7Goal : Nat := sGoal &&& s7Mask
abbrev s7StockWords : List Nat := [0xaa000000aa00, 0xcc000000cc00, 0xf0000000f000, 0xff0000000000]
def s7Fact : Nat × List Nat × Nat × Nat := (s7Mask, s7StockWords, 5, s7Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s7Stock : Lower s7Mask s7StockWords s7Goal 5 := dagShiftLower (width := 64) pm6 s6Stock (by decide +kernel)
def pm7 : List (List (Nat × Nat) × List (Nat × Nat)) := [st25, st24]
def s8Mask : Nat := 0xf000f000f000f00
abbrev s8Goal : Nat := sGoal &&& s8Mask
abbrev s8StockWords : List Nat := [0xa000a000a000a00, 0xc000c000c000c00, 0xf0000000f000000, 0xf000f0000000000]
def s8Fact : Nat × List Nat × Nat × Nat := (s8Mask, s8StockWords, 5, s8Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s8Stock : Lower s8Mask s8StockWords s8Goal 5 := dagShiftLower (width := 64) pm7 s6Stock (by decide +kernel)
def s9Mask : Nat := 0xf000f00
abbrev s9Goal : Nat := sGoal &&& s9Mask
abbrev s9StockWords : List Nat := [0xa000a00, 0xc000c00, 0xf000000]
def s9Fact : Nat × List Nat × Nat × Nat := (s9Mask, s9StockWords, 4, s9Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s9Stock : Lower s9Mask s9StockWords s9Goal 4 := dagShiftLower (width := 64) pm5 s0Stock (by decide +kernel)
def s10Mask : Nat := 0xf0000000f00
abbrev s10Goal : Nat := sGoal &&& s10Mask
abbrev s10StockWords : List Nat := [0xa0000000a00, 0xc0000000c00, 0xf0000000000]
def s10Fact : Nat × List Nat × Nat × Nat := (s10Mask, s10StockWords, 4, s10Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s10Stock : Lower s10Mask s10StockWords s10Goal 4 := dagShiftLower (width := 64) pm4 s0Stock (by decide +kernel)
def pm8 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01, st24]
def pm9 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01, st24, st25]
def s11Blob193946 : Nat := (cbits [0x34120d0502c120b, 0x4121906038140e06, 0x81d0c068141a0c06, 0xa140a412290e0783, 0x60b8582d140a8142, 0xf0383c1c0e870391, 0x100d0402c703c160, 0xe04038580d0e034, 0x503c120f1603838, 0x64381904064180f, 0xc701a0e068101a1c, 0x21d0c06c141b0486, 0xe05078301d060741, 0x40a4381f0c078181, 0xa8102a1c0a458290, 0x142b048ac702a160, 0x2d060b4122d140ac, 0x140b8182e050b850, 0xe43039048e4582f, 0xc503a0c0e8143a14, 0x3c0c0f0183c1c0e, 0xe1c0f4583d0e0f45, 0x602c703e160f8383, 0x34140d1402c300b0, 0x300e04838500d0c0, 0xf0e03c100f14038, 0x1406418190506458])
def s11Blob194515 : Nat := (cbits [0x1f8f1f8fc78534cf, 0xf88acb33fc7e388f, 0x1f8fc0f1e3f1e3f1, 0xfc01fc01ff730c3c, 0x7c0fc01ff1ff01, 0xe001fffe0001fffe, 0xfffe0000007ff000, 0x1ffff])
def s11Blob194698 : Nat := (cbits [0x480048040001045, 0x8000411200800002, 0x2010001021002100, 0x4825482536330c28, 0x125c0e805802d901, 0x9256aa40049926c, 0x926c0048246fa000, 0x9249b4c9])
def s11Mask : Nat := 0xff00ff00ff00ff00
abbrev s11Goal : Nat := sGoal &&& s11Mask
abbrev s11StockWords : List Nat := [0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000]
def s11Fact : Nat × List Nat × Nat × Nat := (s11Mask, s11StockWords, 9, s11Goal)
def s11Cuts : List (Nat × List Nat × Nat × Nat) := [s2Fact, s3Fact, s1Fact, s4Fact, s5Fact, s6Fact, s7Fact, s8Fact, s0Fact, s9Fact, s10Fact]
def s11Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[11, 13, 14, 25, 26, 41, 42, 60, 11, 13, 14, 25, 9, 10, 28, 44, 56, 9, 10, 28, 44, 56, 9, 10], rfl⟩
def s11Witnesses := unpackWitnesses s11StockWords [5642, 267785, 530953, 799241, 1069577]
def s11Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0x5204c32d0035001, 0x8058058058052352, 0x8008008007e15935]) else (if j < 2 then (cbits [0x184d840840802800, 0x20a20a20a01a009e, 0xbe0b83a4aa21a20a]) else (cbits [0x6d2dd01c65be4be0, 0xec]))) 12 (i % 16)
def s11Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 4 then (if j < 2 then (if j < 1 then (cbits [0x140130080200001f, 0x980dd2602b09807c, 0x632ba98c7e823146, 0x188438620e98cdf2, 0x6331198ac4262710, 0x3198dcc2]) else (cbits [0x429335024b53892c, 0x30e5b8c3891a4de, 0x832b020c7c043147, 0x98840a620620cdd0, 0x6330498ac1062703, 0x2498dc90])) else (if j < 3 then (cbits [0x1093343a4b50a92c, 0x3b0e58ac3884a4de, 0x6c3841a4b0066206, 0x30e00c92c0198818, 0x424580d81602a23, 0xa58ca996]) else (cbits [0x1a620e58d0b16336, 0x719091c6360718a8, 0x49370824cc1e92c6, 0xb0e0a49432824fc2, 0xf4489310e20c3f47, 0x600719e]))) else (if j < 6 then (if j < 5 then (cbits [0x16012a88ca022028, 0x70ca42831da20c50, 0xc6420b18d82a6200, 0xa508329360c24b0a, 0xf440db10c34c382c, 0x60040b4]) else (cbits [0xa3140b99302ec42, 0xd0cdd3432b078c7c, 0x4637cd18ae8a6206, 0xb0e03e9370ea4b3b, 0xc38a324b00c6202e, 0x38c503c])) else (if j < 7 then (cbits [0xaa629a398802a329, 0x1007420013040022, 0x2012b10c76903141, 0x74240130480202, 0x430c80d52c0290b, 0xa48c51b6]) else (cbits [0xb2335cb0ca6ac31d, 0xfbd1048c42ed8d0e, 0xe0354b80a42e01d6, 0x8cd72e329ab8c75a, 0xeb])))) 22 (i % 16)
def s11Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0x6314080100807c0, 0x2c18c4010c7c2310, 0x4c561189c2310849, 0x58070c015160130, 0x4961662a2cc4]) else (if j < 2 then (cbits [0x829372c0508a4ccb, 0x3650c40a0c75400f, 0x126ca24b146212e6, 0x8e98801621a8c385, 0x49bbac387925]) else (cbits [0x8201d88c4e098841, 0x310a4315]))) 19 (i % 16)
def s11Links := pageLinks s11Index s11Codes 5 13 6 6
def s11Data (i : Nat) : Nat × Nat :=
  let e := s11Forest i
  (e &&& 63, e >>> 6)
def s11Sample : Nat × Nat := (s11Blob193946, 96)
def s11Tags := dagTraceTags s11Mask 96 (dagTagBases s11StockWords s11Blob194515 s11Blob194698 96) 8 s11Data
def s11States := dagTrace s11Mask s11StockWords 8 s11Data
def s11MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm6, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val))), (pm5, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 4, 3, 2, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 4, 3, 2, 5] 0 i.val))), (pm4, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 5, 3, 2, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 4, 3, 5, 2] 0 i.val))), (pm7, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 4, 3, 5, 2] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 5, 3, 2, 4] 0 i.val))), (pm1, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val))), (pm8, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 4, 3, 2, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 4, 3, 2, 5] 0 i.val))), (pm9, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 5, 3, 2, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 4, 3, 5, 2] 0 i.val)))]
def s11Moves := dagMoves s11MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s11Autos : DagMovesOK s11Mask s11Goal 64 s11Moves := dagMovesOfCheck (by decide +kernel)
def s11Check := dagCheckNode s11Mask s11Goal s11Chart (dagKnownCloses s11Goal s11Cuts) 37 s11States s11Moves s11Links s11Sample s11Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s11Roots : dagCheckRoots s11Mask s11Goal s11Chart (dagKnownCloses s11Goal s11Cuts) s11Witnesses (dagRef 37 s11States s11Moves s11Links 0) s11StockWords 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s11Block0 : treeBlock 0 24 s11Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s11Block24 : treeBlock 24 13 s11Check = true := by decide +kernel
theorem s11Group0_37 : treeBlock 0 37 s11Check = true := treeBlock_merge (start := 0) (left := 24) (right := 13) (check := s11Check) s11Block0 s11Block24
theorem s11Blocks : treeBlock 0 37 s11Check = true := s11Group0_37
theorem s11Known : Known s11Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s10Stock) s9Stock) s0Stock) s8Stock) s7Stock) s6Stock) s5Stock) s4Stock) s1Stock) s3Stock) s2Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s11Stock : Lower s11Mask s11StockWords s11Goal 9 := by
  apply lowerDag _ _ _ _ s11Autos _ _ _ s11Known _ s11Roots s11Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s11Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def st03 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xaa55aa55aa55aa55, 0), (0xaa00aa00aa00aa, 7)], [(0x5500550055005500, 7)])
def pm10 : List (List (Nat × Nat) × List (Nat × Nat)) := [st03, st01, st24]
def s12Mask : Nat := 0xa0a0a0a
abbrev s12Goal : Nat := sGoal &&& s12Mask
abbrev s12StockWords : List Nat := [0x8080808, 0xa000a00, 0xa0a0000]
def s12Fact : Nat × List Nat × Nat × Nat := (s12Mask, s12StockWords, 4, s12Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s12Stock : Lower s12Mask s12StockWords s12Goal 4 := dagShiftLower (width := 64) pm10 s0Stock (by decide +kernel)
def st13 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xcc33cc33cc33cc33, 0), (0xcc00cc00cc00cc, 6)], [(0x3300330033003300, 6)])
def pm11 : List (List (Nat × Nat) × List (Nat × Nat)) := [st13, st24]
def s13Mask : Nat := 0xc0c0c0c
abbrev s13Goal : Nat := sGoal &&& s13Mask
abbrev s13StockWords : List Nat := [0x8080808, 0xc000c00, 0xc0c0000]
def s13Fact : Nat × List Nat × Nat × Nat := (s13Mask, s13StockWords, 4, s13Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s13Stock : Lower s13Mask s13StockWords s13Goal 4 := dagShiftLower (width := 64) pm11 s0Stock (by decide +kernel)
def st23 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xf00ff00ff00ff00f, 0), (0xf000f000f000f0, 4)], [(0xf000f000f000f00, 4)])
def pm12 : List (List (Nat × Nat) × List (Nat × Nat)) := [st24, st23]
def s14Mask : Nat := 0xf0f0000
abbrev s14Goal : Nat := sGoal &&& s14Mask
abbrev s14StockWords : List Nat := [0xa0a0000, 0xc0c0000, 0xf000000]
def s14Fact : Nat × List Nat × Nat × Nat := (s14Mask, s14StockWords, 4, s14Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s14Stock : Lower s14Mask s14StockWords s14Goal 4 := dagShiftLower (width := 64) pm12 s0Stock (by decide +kernel)
def st34 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xff0000ffff0000ff, 0), (0xff000000ff00, 8)], [(0xff000000ff0000, 8)])
def pm13 : List (List (Nat × Nat) × List (Nat × Nat)) := [st34]
def pm14 : List (List (Nat × Nat) × List (Nat × Nat)) := [st13]
def st14 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xcccc3333cccc3333, 0), (0xcccc0000cccc, 14)], [(0x3333000033330000, 14)])
def pm15 : List (List (Nat × Nat) × List (Nat × Nat)) := [st13, st14]
def pm16 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01, st34]
def pm17 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01, st03]
def st04 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xaaaa5555aaaa5555, 0), (0xaaaa0000aaaa, 15)], [(0x5555000055550000, 15)])
def pm18 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01, st03, st04]
def pm19 : List (List (Nat × Nat) × List (Nat × Nat)) := [st03, st01]
def pm20 : List (List (Nat × Nat) × List (Nat × Nat)) := [st03, st01, st14]
def pm21 : List (List (Nat × Nat) × List (Nat × Nat)) := [st03, st14]
def s15Blob202271 : Nat := (cbits [0x84c140b0482c060b, 0x412190904c221301, 0x41a0506830190886, 0xb0102c020b0c0682, 0x804c04130084c100, 0x6820190406402190, 0x61b08068101a010, 0x1b0886c141b0486c, 0x882c000b0c06c24, 0x84c00130c02c240b, 0x400190c04c141304, 0x1a0906414190186, 0xb08868121a018680, 0x806c101b0106c021, 0x6804190404c200b0, 0x1b008])
def s15Blob202613 : Nat := (cbits [0x1fdfc3ffff1ff1ff, 0x1ff1f7fe1ffff1ff, 0xfff1ff1dfff0ffff, 0xf7fff87])
def s15Blob202720 : Nat := (cbits [0x16a078888b0490db, 0x12d18845c88a9093, 0x1241b602444e8992, 0xc44477])
def s15Mask : Nat := 0xf0f0f0f
abbrev s15Goal : Nat := sGoal &&& s15Mask
abbrev s15StockWords : List Nat := [0xa0a0a0a, 0xc0c0c0c, 0xf000f00, 0xf0f0000]
def s15Fact : Nat × List Nat × Nat × Nat := (s15Mask, s15StockWords, 7, s15Goal)
def s15Cuts : List (Nat × List Nat × Nat × Nat) := [s12Fact, s13Fact, s9Fact, s14Fact]
def s15Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[11, 19, 25, 26, 11, 19, 25, 26, 11, 19, 25, 26, 3, 9, 10, 17, 18, 24, 3, 9, 10, 17, 18, 24], rfl⟩
def s15Witnesses := unpackWitnesses s15StockWords [5642, 267785, 529923, 796163]
def s15Index (i : Nat) : Nat := unpack 0x4c242e4702cc3401 9 i
def s15Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0xb0600f020080000f, 0x1b42314360272601, 0x6276262096327863, 0x4620043147292ca6, 0x18332083263492c2]) else 0xa6245863248626) 20 (i % 16)
def s15Forest (i : Nat) : Nat := unpack (cbits [0x7918a200410078, 0x31251934]) 16 i
def s15Links := pageLinks s15Index s15Codes 4 13 3 5
def s15Data (i : Nat) : Nat × Nat :=
  let e := s15Forest i
  (e &&& 7, e >>> 3)
def s15Sample : Nat × Nat := (s15Blob202271, 55)
def s15Tags := dagTraceTags s15Mask 55 (dagTagBases s15StockWords s15Blob202613 s15Blob202720 55) 6 s15Data
def s15States := dagTrace s15Mask s15StockWords 6 s15Data
def s15MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm13, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 4, 3, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 4, 3, 5] 0 i.val))), (pm14, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 3, 2, 1, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 3, 2, 1, 4, 5] 0 i.val))), (pm15, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 4, 2, 1, 3, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 3, 2, 4, 1, 5] 0 i.val))), (pm1, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val))), (pm16, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 2, 4, 3, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 2, 4, 3, 5] 0 i.val))), (pm17, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [3, 0, 2, 1, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 3, 2, 0, 4, 5] 0 i.val))), (pm18, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [4, 0, 2, 1, 3, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 3, 2, 4, 0, 5] 0 i.val))), (pm19, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 3, 2, 0, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [3, 0, 2, 1, 4, 5] 0 i.val))), (pm20, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 4, 2, 0, 3, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [3, 0, 2, 4, 1, 5] 0 i.val))), (pm21, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [3, 4, 2, 0, 1, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [3, 4, 2, 0, 1, 5] 0 i.val)))]
def s15Moves := dagMoves s15MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s15Autos : DagMovesOK s15Mask s15Goal 64 s15Moves := dagMovesOfCheck (by decide +kernel)
def s15Check := dagCheckNode s15Mask s15Goal s15Chart (dagKnownCloses s15Goal s15Cuts) 6 s15States s15Moves s15Links s15Sample s15Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s15Roots : dagCheckRoots s15Mask s15Goal s15Chart (dagKnownCloses s15Goal s15Cuts) s15Witnesses (dagRef 6 s15States s15Moves s15Links 0) s15StockWords 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s15Block0 : treeBlock 0 6 s15Check = true := by decide +kernel
theorem s15Blocks : treeBlock 0 6 s15Check = true := s15Block0
theorem s15Known : Known s15Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s14Stock) s9Stock) s13Stock) s12Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s15Stock : Lower s15Mask s15StockWords s15Goal 7 := by
  apply lowerDag _ _ _ _ s15Autos _ _ _ s15Known _ s15Roots s15Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s15Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel
def s16Mask : Nat := 0xf0f0f0f0f0f0f0f
abbrev s16Goal : Nat := sGoal &&& s16Mask
abbrev s16StockWords : List Nat := [0xa0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c, 0xf000f000f000f00, 0xf0f00000f0f0000, 0xf0f0f0f00000000]
def s16Fact : Nat × List Nat × Nat × Nat := (s16Mask, s16StockWords, 8, s16Goal)
def s16Witnesses := unpackWitnesses s16StockWords [5642, 267785, 529923, 796163, 1066499]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s16Stock : Lower s16Mask s16StockWords s16Goal 8 := by
  apply essentialLift (witnesses := s16Witnesses) (cut := s15Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s15StockWords) (by decide +kernel)
  · exact s15Stock
  · decide +kernel
def s17Blob210482 : Nat := (cbits [0x84c061306038180d, 0x4381e0e074241308, 0x80e01038380d0083, 0x30084c180f0183c3, 0x8874181d0804c041, 0x34381f09078181e0, 0xe08834060d000, 0xf0083c240e01838, 0x87400130e03c04, 0x87c201e01078201d, 0x4241f0887c181f01, 0xe00838200d0103, 0x30903c220f0003c2, 0x9074061d00074381, 0x7c221e01878001e0, 0x240d0807c041f008, 0x1d0604c200f08838, 0x1f0087804])
def s17Blob210863 : Nat := (cbits [0x5de3f9f9f8f3f9bd, 0xf77e3f3f3f8e7f2f, 0x9dffefffefffc7f8, 0xf1ff80ff803fc0f])
def s17Blob210978 : Nat := (cbits [0x223912288ac2288c, 0xc8a590650b24250a, 0x200100408054558, 0xf24eaca49350af])
def s17Mask : Nat := 0xf00ff00f
abbrev s17Goal : Nat := sGoal &&& s17Mask
abbrev s17StockWords : List Nat := [0xa00aa00a, 0xc00cc00c, 0xf000f000, 0xf00f0000]
def s17Fact : Nat × List Nat × Nat × Nat := (s17Mask, s17StockWords, 5, s17Goal)
def s17Cuts : List (Nat × List Nat × Nat × Nat) := []
def s17Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[13, 14, 19, 13, 14, 19, 13, 14, 19, 13, 14, 19, 3, 17, 18, 28, 3, 17, 18, 28, 3, 17, 18, 28], rfl⟩
def s17Witnesses := unpackWitnesses s17StockWords [6668, 269324, 530945, 796163]
def s17Index (i : Nat) : Nat := unpack 0x9 2 i
def s17Codes (i : Nat) : Nat := unpack 0xf 15 i
def s17Forest (i : Nat) : Nat := unpack 0x1e 14 i
def s17Links := pageLinks s17Index s17Codes 1 13 1 2
def s17Data (i : Nat) : Nat × Nat :=
  let e := s17Forest i
  (e &&& 1, e >>> 1)
def s17Sample : Nat × Nat := (s17Blob210482, 63)
def s17Tags := dagTraceTags s17Mask 63 (dagTagBases s17StockWords s17Blob210863 s17Blob210978 63) 4 s17Data
def s17States := dagTrace s17Mask s17StockWords 4 s17Data
def s17MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s17Moves := dagMoves s17MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s17Autos : DagMovesOK s17Mask s17Goal 64 s17Moves := dagMovesOfCheck (by decide +kernel)
def s17Check := dagCheckNode s17Mask s17Goal s17Chart (dagKnownCloses s17Goal s17Cuts) 1 s17States s17Moves s17Links s17Sample s17Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s17Roots : dagCheckRoots s17Mask s17Goal s17Chart (dagKnownCloses s17Goal s17Cuts) s17Witnesses (dagRef 1 s17States s17Moves s17Links 0) s17StockWords 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s17Block0 : treeBlock 0 1 s17Check = true := by decide +kernel
theorem s17Blocks : treeBlock 0 1 s17Check = true := s17Block0
theorem s17Known : Known s17Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s17Stock : Lower s17Mask s17StockWords s17Goal 5 := by
  apply lowerDag _ _ _ _ s17Autos _ _ _ s17Known _ s17Roots s17Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s17Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def s18Mask : Nat := 0xf00f0000f00f
abbrev s18Goal : Nat := sGoal &&& s18Mask
abbrev s18StockWords : List Nat := [0xa00a0000a00a, 0xc00c0000c00c, 0xf0000000f000, 0xf00f00000000]
def s18Fact : Nat × List Nat × Nat × Nat := (s18Mask, s18StockWords, 5, s18Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s18Stock : Lower s18Mask s18StockWords s18Goal 5 := dagShiftLower (width := 64) pm6 s17Stock (by decide +kernel)
def s19Blob214040 : Nat := (cbits [0x78381d0904c2213, 0xc383c190cc62330e, 0x21d1904c62130804, 0x3088cc381f090782, 0xe0f4603c180cc243, 0x4c643e0e0f8623d0, 0x201e18874201d180, 0x330907c221f19078, 0x190f0623c080f020, 0xf8243e180f4223d, 0xc643f188fc383f18, 0x21e18074241d0e04, 0xf1887c201f180782, 0x80f4243c088f0641, 0xfc623e080f8643d0, 0x641d180fc243f088, 0x3d0e0cc601f18878, 0x203f088f824])
def s19Blob214429 : Nat := (cbits [0xdde673f31ce6f7b7, 0x377c3e7e0f9c7ddd, 0x1dffffdffbf7c713, 0xf1ff00ffe03fc0e])
def s19Blob214544 : Nat := (cbits [0x2230a42144842511, 0x8a2a0a245082511, 0x200002400028413, 0xf28d4d5856b066])
def s19Mask : Nat := 0xf00f0000f00f0000
abbrev s19Goal : Nat := sGoal &&& s19Mask
abbrev s19StockWords : List Nat := [0xa00a0000a00a0000, 0xc00c0000c00c0000, 0xf0000000f0000000, 0xf00f000000000000]
def s19Fact : Nat × List Nat × Nat × Nat := (s19Mask, s19StockWords, 5, s19Goal)
def s19Cuts : List (Nat × List Nat × Nat × Nat) := []
def s19Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[19, 29, 30, 60, 19, 29, 30, 60, 19, 29, 30, 60, 28, 49, 50, 28, 49, 50, 28, 49, 50, 28, 49, 50], rfl⟩
def s19Witnesses := unpackWitnesses s19StockWords [9746, 271889, 539153, 817180]
def s19Index (i : Nat) : Nat := unpack 0x9 2 i
def s19Codes (i : Nat) : Nat := unpack 0xf 15 i
def s19Forest (i : Nat) : Nat := unpack 0x1e 14 i
def s19Links := pageLinks s19Index s19Codes 1 13 1 2
def s19Data (i : Nat) : Nat × Nat :=
  let e := s19Forest i
  (e &&& 1, e >>> 1)
def s19Sample : Nat × Nat := (s19Blob214040, 63)
def s19Tags := dagTraceTags s19Mask 63 (dagTagBases s19StockWords s19Blob214429 s19Blob214544 63) 4 s19Data
def s19States := dagTrace s19Mask s19StockWords 4 s19Data
def s19MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s19Moves := dagMoves s19MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s19Autos : DagMovesOK s19Mask s19Goal 64 s19Moves := dagMovesOfCheck (by decide +kernel)
def s19Check := dagCheckNode s19Mask s19Goal s19Chart (dagKnownCloses s19Goal s19Cuts) 1 s19States s19Moves s19Links s19Sample s19Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s19Roots : dagCheckRoots s19Mask s19Goal s19Chart (dagKnownCloses s19Goal s19Cuts) s19Witnesses (dagRef 1 s19States s19Moves s19Links 0) s19StockWords 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s19Block0 : treeBlock 0 1 s19Check = true := by decide +kernel
theorem s19Blocks : treeBlock 0 1 s19Check = true := s19Block0
theorem s19Known : Known s19Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s19Stock : Lower s19Mask s19StockWords s19Goal 5 := by
  apply lowerDag _ _ _ _ s19Autos _ _ _ s19Known _ s19Roots s19Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s19Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def s20Mask : Nat := 0xf00ff00f00000000
abbrev s20Goal : Nat := sGoal &&& s20Mask
abbrev s20StockWords : List Nat := [0xa00aa00a00000000, 0xc00cc00c00000000, 0xf000f00000000000, 0xf00f000000000000]
def s20Fact : Nat × List Nat × Nat × Nat := (s20Mask, s20StockWords, 5, s20Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s20Stock : Lower s20Mask s20StockWords s20Goal 5 := dagShiftLower (width := 64) pm6 s19Stock (by decide +kernel)
def s21Blob218034 : Nat := (cbits [0x84c061306038180d, 0xc381e0e074241308, 0x82d1108c42230188, 0xc190cc6233160b85, 0xe034020d160f0383, 0x38380e01038580d0, 0x2130603c060f160, 0x131884c20130104c, 0x6078221d0607464, 0x8c02230e07c241e, 0x464231888c402301, 0x42e060b8422d060b, 0x3088cc0633160bc4, 0x80cc4433108cc243, 0xf4383d180f0183c1, 0x583e0e0f8623d160, 0xd01834000d190f8, 0x1838000e1083422, 0x3c020f11038240e, 0xc00131603c380f01, 0x21d1804c44131084, 0xe18874581d080740, 0x9078581e08078041, 0x7c221f0607c061f1, 0x24230888c0023090, 0x2d0e0b4022d1808c, 0xe0b8042e188b440])
def s21Blob218603 : Nat := (cbits [0x3c73f9fe7fc737bd, 0x9ff83bde3ffc3ffc, 0xc3ffc3ffc383fe7f, 0xfffc0f83e0ffcc63, 0xff00f07cfc3ffc3f, 0x3fffc003fff003, 0x3fffffc0000ff80, 0xffc00000])
def s21Blob218788 : Nat := (cbits [0xb840b1244941118c, 0x1248229424942484, 0x4126410b8a015449, 0x1b40a82a0b6cc63, 0x5c12707888091030, 0xabb2aa1112da6063, 0x236b8d701824bf00, 0x320333a2])
def s21Mask : Nat := 0xf00ff00ff00ff00f
abbrev s21Goal : Nat := sGoal &&& s21Mask
abbrev s21StockWords : List Nat := [0xa00aa00aa00aa00a, 0xc00cc00cc00cc00c, 0xf000f000f000f000, 0xf00f0000f00f0000, 0xf00ff00f00000000]
def s21Fact : Nat × List Nat × Nat × Nat := (s21Mask, s21StockWords, 8, s21Goal)
def s21Cuts : List (Nat × List Nat × Nat × Nat) := [s17Fact, s18Fact, s19Fact, s20Fact]
def s21Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[13, 14, 19, 35, 60, 13, 14, 19, 35, 60, 13, 14, 3, 28, 44, 49, 50, 3, 28, 44, 49, 50, 3, 28], rfl⟩
def s21Witnesses := unpackWitnesses s21StockWords [6668, 269324, 530945, 796163, 1066499]
def s21Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0xcc26130983d03c01, 0x2e161b0546834098, 0xd85d]) else 0x7c369b0) 9 (i % 16)
def s21Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0xf0a009020080001f, 0x1f1201b100130c00, 0x31b8a31582314160, 0xe6211a6209631f92, 0x431460c382092c1]) else (cbits [0xc48c380892c06620, 0x241401c0e00c0e31, 0x92c8662006314183, 0x8620083145cc381c, 0x22c381c92c8])) 20 (i % 16)
def s21Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0x862820040403e0, 0xc01e100485258231, 0x38a00d84026118e1, 0xe31004648c00f840, 0x31085258]) else 0x61c452581) 18 (i % 16)
def s21Links := pageLinks s21Index s21Codes 4 13 5 5
def s21Data (i : Nat) : Nat × Nat :=
  let e := s21Forest i
  (e &&& 31, e >>> 5)
def s21Sample : Nat × Nat := (s21Blob218034, 96)
def s21Tags := dagTraceTags s21Mask 96 (dagTagBases s21StockWords s21Blob218603 s21Blob218788 96) 7 s21Data
def s21States := dagTrace s21Mask s21StockWords 7 s21Data
def s21MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm6, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val))), (pm1, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val)))]
def s21Moves := dagMoves s21MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s21Autos : DagMovesOK s21Mask s21Goal 64 s21Moves := dagMovesOfCheck (by decide +kernel)
def s21Check := dagCheckNode s21Mask s21Goal s21Chart (dagKnownCloses s21Goal s21Cuts) 18 s21States s21Moves s21Links s21Sample s21Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s21Roots : dagCheckRoots s21Mask s21Goal s21Chart (dagKnownCloses s21Goal s21Cuts) s21Witnesses (dagRef 18 s21States s21Moves s21Links 0) s21StockWords 7 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s21Block0 : treeBlock 0 18 s21Check = true := by decide +kernel
theorem s21Blocks : treeBlock 0 18 s21Check = true := s21Block0
theorem s21Known : Known s21Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s20Stock) s19Stock) s18Stock) s17Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s21Stock : Lower s21Mask s21StockWords s21Goal 8 := by
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
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel
def s22Mask : Nat := 0xf0f00000f0f
abbrev s22Goal : Nat := sGoal &&& s22Mask
abbrev s22StockWords : List Nat := [0xa0a00000a0a, 0xc0c00000c0c, 0xf0000000f00, 0xf0f00000000]
def s22Fact : Nat × List Nat × Nat × Nat := (s22Mask, s22StockWords, 7, s22Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s22Stock : Lower s22Mask s22StockWords s22Goal 7 := dagShiftLower (width := 64) pm6 s15Stock (by decide +kernel)
def pm22 : List (List (Nat × Nat) × List (Nat × Nat)) := [st03, st01, st25, st24]
def s23Mask : Nat := 0xa0a0a0a0a0a0a0a
abbrev s23Goal : Nat := sGoal &&& s23Mask
abbrev s23StockWords : List Nat := [0x808080808080808, 0xa000a000a000a00, 0xa0a00000a0a0000, 0xa0a0a0a00000000]
def s23Fact : Nat × List Nat × Nat × Nat := (s23Mask, s23StockWords, 5, s23Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s23Stock : Lower s23Mask s23StockWords s23Goal 5 := dagShiftLower (width := 64) pm22 s6Stock (by decide +kernel)
def pm23 : List (List (Nat × Nat) × List (Nat × Nat)) := [st13, st25, st24]
def s24Mask : Nat := 0xc0c0c0c0c0c0c0c
abbrev s24Goal : Nat := sGoal &&& s24Mask
abbrev s24StockWords : List Nat := [0x808080808080808, 0xc000c000c000c00, 0xc0c00000c0c0000, 0xc0c0c0c00000000]
def s24Fact : Nat × List Nat × Nat × Nat := (s24Mask, s24StockWords, 5, s24Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s24Stock : Lower s24Mask s24StockWords s24Goal 5 := dagShiftLower (width := 64) pm23 s6Stock (by decide +kernel)
def pm24 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01, st45]
def s25Blob228739 : Nat := (cbits [0x834140b0482c060b, 0xc180e05038180d04, 0x2190904c22130184, 0xa050683019088641, 0xe078381d0c068241, 0xa444231088c06230, 0x142a140a44229048, 0x2e160b4502a110a8, 0x188e46433188cc58, 0xf0703a190e87039, 0xc020b1c0f0583c0e, 0xd00834100b0102, 0xe01038580d0e0341, 0x183c580e0e038100, 0x4c180f0503c120f0, 0x62130804c0413008, 0x190406402191904c, 0x1c06462190e06420, 0x68201a04068041a, 0xc061b1c068641a0e, 0x41b0886c141b0486, 0xd06074121d0c06c2, 0x6078141e0c074221, 0x8c381f0c078241e0, 0x62231008c0423008, 0x29040a402291908c, 0x1c0a46229160a440])
def s25Blob229311 : Nat := (cbits [0xfffe1fc1e8fd1f9f, 0x771ee3e7fff0ffc0, 0x3ff0fff03ffe1c6, 0x1ffe3818030078, 0x9fe3fc7f001ff000, 0xfc1ffffffc1fffff, 0xffe0003fe003ff80, 0xfffc0000001fffff, 0xffe000000000003f])
def s25Blob229524 : Nat := (cbits [0x45260240a06c0d8b, 0x431462a5452052c0, 0x2450551024a2082, 0x2011981818030050, 0x1da3b47e20122008, 0xa81bb9aaa81ddd3d, 0xf380882fe003db00, 0xfed80000c31cce3c, 0xf3800030c3011037])
def s25Mask : Nat := 0xff0fff0fff0fff0f
abbrev s25Goal : Nat := sGoal &&& s25Mask
abbrev s25StockWords : List Nat := [0xaa0aaa0aaa0aaa0a, 0xcc0ccc0ccc0ccc0c, 0xf000f000f000f000, 0xff00ff00ff00ff00, 0xff0f0000ff0f0000, 0xff0fff0f00000000]
def s25Fact : Nat × List Nat × Nat × Nat := (s25Mask, s25StockWords, 11, s25Goal)
def s25Cuts : List (Nat × List Nat × Nat × Nat) := [s11Fact, s16Fact, s21Fact, s15Fact, s22Fact, s4Fact, s5Fact, s23Fact, s24Fact]
def s25Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[11, 13, 14, 19, 25, 26, 35, 41, 42, 60, 11, 13, 3, 9, 10, 28, 44, 49, 50, 56, 3, 9, 10, 28], rfl⟩
def s25Witnesses := unpackWitnesses s25StockWords [5642, 267785, 530953, 792067, 1058307, 1328643]
def s25Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 6 then (if j < 3 then (if j < 1 then (cbits [0xe00d9022a00c0001, 0x448012003e50f803, 0x5804a612804a0120, 0x15805601]) else (if j < 2 then (cbits [0x4016945a01588560, 0x8660198064119006, 0x7651d046a5198, 0x269080d2]) else (cbits [0xc02b00a442900a21, 0xb232c80ae22b04a, 0xf00ba12e04b802e0, 0x2f90bc12]))) else (if j < 4 then (cbits [0xca3720ca93188c60, 0x10614181060400ce, 0x4811204481085420, 0x46811244]) else (if j < 5 then (cbits [0x2048811a446811a0, 0xd2c14a85281488d2, 0xf093824d853414b8, 0x51814034]) else (cbits [0xa452054615181460, 0x1540548552054814, 0xba96c1598d549550, 0x62818245])))) else (if j < 9 then (if j < 7 then (cbits [0xc163018a162818a0, 0x5924648192063898, 0xa89a0567859c1668, 0x6c85ae26]) else (if j < 8 then (cbits [0x8272bdc056f09b44, 0x1ee57b81ec17b01e, 0x5a1fae7e81f817e0, 0x8a062618]) else (cbits [0x228c822e28b062a1, 0x6484908e4018d963, 0x8025a3950e521940, 0x98026009]))) else (if j < 10 then (cbits [0xa8998a660988a601, 0x28a0a2067e59e8a6, 0xa06a80aa029a7a2a, 0xabaaaa2a]) else (if j < 11 then (cbits [0xa0b206c42b102c21, 0x2da0b682cc7b286c, 0x88ae20b882da4b68, 0xba82e62b]) else (cbits [0xd2c41afe9bc9aea4, 0xb4a0d207480d0131, 0x35c0d41b4e1d28]))))) 14 (i % 16)
def s25Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 13 then (if j < 6 then (if j < 3 then (if j < 1 then (cbits [0xe80240100400003f, 0xf8e40130c401e0, 0x146780864f00dc98, 0xf4c0c7e1d18ac023, 0xb031073c343a7866, 0x2cd88658b0e0]) else (if j < 2 then (cbits [0x28c5002007b62f44, 0x19b82031f02c62a0, 0x38060c40890d0c12, 0x48cbd101b621832c, 0x47a220604e00c08, 0x1801e824940]) else (cbits [0x5310c0861c00e620, 0x315012f44421e880, 0x2c434c9c0699080c, 0x887c9400f7a201c9, 0xd18a02292c03062, 0x51e8809b138]))) else (if j < 4 then (cbits [0xb25201792802af4e, 0x18d81c62101cc400, 0x4303cc4204188004, 0x804a4b01a7a222e6, 0x131a082633502862, 0x724a00a8d35]) else (if j < 5 then (cbits [0x38d082519503c31e, 0x310c1662049c69c1, 0x4f0b0c861598ac2a, 0xe173d102d4962586, 0x1f18a25d2500c1e9, 0x91e881098c0]) else (cbits [0xc5020318249250, 0x7a2046c38088c401, 0x1d83062811a4f123, 0x14313a0d18a04c3, 0x2619403e6280a64a, 0x90c550724b0])))) else (if j < 9 then (if j < 7 then (cbits [0x7c9420f49625264e, 0x1425034c0a06801, 0x4e14c0842580a832, 0x83724b05918e2a60, 0x6f9280e2f4f1bde8, 0x110c40198041]) else (if j < 8 then (cbits [0x3990c4731b88c621, 0x7a2094c43121870a, 0x190dc01e1a002148, 0x61f8c543d18a0720, 0x4149628033710065, 0x50587021a4dc]) else (cbits [0xb30e03649606a314, 0x18d0740080e06489, 0x380f12581d988038, 0x81d8c643518a278c, 0x3618a27cc380f925, 0xf8c401e0c94]))) else (if j < 11 then (if j < 10 then (cbits [0x2b0e03d18e084c38, 0x18e07c628515e882, 0x2c1046382000403f, 0x2118a0497a208a9, 0x5249609801010c02, 0x144c40268090]) else (cbits [0x818804f00889c008, 0x6270a231c1406482, 0x50159e9c2abd1054, 0xc198070574a40b12, 0x5c1920b431413003, 0x1a8c40338c94])) else (if j < 12 then (cbits [0x5bd106d6218d6c38, 0x7a20b6c380d0638b, 0x1413403c1b18a15b, 0x6308c7c6018a8ba3, 0x633102c433718865, 0x19926e3224b0]) else (cbits [0xf18804e18f2c8c38, 0xe2bec3817d2582, 0x3817cc402f18804f, 0x340c50390140cac, 0x3a1942d2f441a587, 0x18cc481e0cd0]))))) else (if j < 20 then (if j < 16 then (if j < 14 then (cbits [0x218c05b310082328, 0x31a0d8f441a4c623, 0x2410c03832a4f042, 0xc240cd06a3140cc3, 0x709280d662856069, 0x1b1268249900]) else (if j < 15 then (cbits [0xa013054020094028, 0x40da31c1580b0a, 0x141cc0542c80301e, 0x43b98827319543c3, 0x873188f66301e8c5, 0x628c9c451908]) else (cbits [0xabd3c937a212492c, 0x1980e801c64e4a04, 0x4e1e00843b0c5075, 0x3cbd105a18c2f00, 0x210040b66245e64a, 0x1d40542e0030]))) else (if j < 18 then (if j < 17 then (cbits [0xe188275195442314, 0x31b90062b1fcc423, 0x3820d258c0990c81, 0x8c23d1086621908c, 0x761950ba31808862, 0x9d8c55111880]) else (cbits [0xf3d107e61c0fa92c, 0x18c0be624178c48b, 0x4e18801830803060, 0x83ea4b06318c104c, 0x233100c831808c62, 0x215e883f24b2])) else (if j < 19 then (cbits [0x118d4660060ca624, 0x3100ce00c608c824, 0x186264a044bd1088, 0xc45a4f06918c0d03, 0x8c49612125023d89, 0x239e8846b108]) else (cbits [0x731209102411a930, 0x18a1069301a86304, 0x2c890c40358c6024, 0xc44a4f48449e0f29, 0x6c31212925064129, 0x1b401842b120])))) else (if j < 23 then (if j < 21 then (cbits [0x799308f32010c630, 0x412e628258ca8c, 0x1584062839804825, 0x24e0c9c9918ec563, 0x2600413a92c1e865, 0x26804c3a0040]) else (if j < 22 then (cbits [0xd98829a18d44c314, 0x310534628a6d2584, 0x1409c0104d98a611, 0x24f8cfe2c18ac243, 0xa562714234f22868, 0x2b1e9c54bd10]) else (cbits [0x13130a019415f250, 0x626146c3c291ea85, 0x14298094140020a3, 0x510d048f19ac263, 0xaa02715125029d87, 0x29de9d0a1880]))) else (if j < 25 then (if j < 24 then (cbits [0x6a5221518a157250, 0x18a15c92c8586285, 0x50240c9b0b988029, 0x6168c541818a1572, 0x1831012431f1b863, 0x64629169886]) else (cbits [0x98c7c6f18d85c315, 0x310c326206bc6864, 0x202c9e89d7990e2e, 0x638189c2f3108346, 0x2f496c3492c250c5, 0xc00120d8022])) else (if j < 26 then (cbits [0x280d4950098e200f, 0x2696804b6940825, 0x1586c6285c013cac, 0x7d28d06a519ac603, 0xb81a7d5834dad069, 0x2ee4a25d4942]) else (cbits [0x30d30a61a016a028, 0x2416e9482d86b0d, 0x142dc0905ca550b6, 0xd40d34a81a08383, 0xa8326d50641870c4, 0x3])))))) 23 (i % 16)
def s25Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 6 then (if j < 3 then (if j < 1 then (cbits [0x803c080100203f00, 0x862804f440302101, 0x2c380631003003c1, 0xc18a81310c19e881, 0x624b030c841862a0, 0x7a20]) else (if j < 2 then (cbits [0x8cdc092582231f02, 0x9e9c26f441362709, 0x46200292809a5205, 0xc621813d10698700, 0xf8c7878012032501, 0x18a0]) else (cbits [0x188088c603e63020, 0x86543cf441f61c11, 0xc4e281a10f0c749, 0xe3158f18847a4a05, 0x7bd10792583c6431, 0x9281]))) else (if j < 4 then (cbits [0x80a0c801e02f4f1e, 0x46286a0083400819, 0x8324380079a24b0d, 0xa3101d0020e80326, 0xa24b0f86286892c3, 0x18a9]) else (if j < 5 then (cbits [0x30e1092586832b34, 0xd8708a6203349b9a, 0x2c383331b999884c, 0xc01519310ccde889, 0x70021380489a0104, 0x8a]) else (cbits [0x24b130c409a6204e, 0x1e88a8c4e5402119, 0x5250544a42bbd395, 0xa61c2d8c51686386, 0xf188178628ba3245, 0x4962])))) else (if j < 9 then (if j < 7 then (cbits [0x8cad7463eba3155d, 0x5870ca92c5d3102e, 0x31468192ad24dd7, 0xc61c2d188169870d, 0x924b0c9886b4f446, 0x7a21]) else (if j < 8 then (cbits [0x804c05e9e6525070, 0x8660e801c7401539, 0x4278310398c51d, 0xc3183998a9cde88f, 0xe30e1f5258fa6207, 0x310b]) else (cbits [0x313a08c6ef862b7c, 0x1e890ac387c4963e, 0x62088318b9b10df, 0xc49e459909cde891, 0x5bd12318851892c8, 0x6274]))) else (if j < 10 then (cbits [0xa4b1cc091232508b, 0x9e9ee7250947a239, 0x201f013144b99525, 0x93104d009a6863b3, 0xf80dc05259323279, 0x19fc]) else (if j < 11 then (cbits [0xb1328869f3e328a0, 0x989d3ef54a261e51, 0xf250a661c53012a9, 0xf92855013aa9e893, 0xfa4b2b92915af4e9, 0x9284]) else (cbits [0xbd12c98700262001, 0x40516a04bb462180, 0x204fb44a45b8d62d, 0x928da4942d12a97]))))) 21 (i % 16)
def s25Links := pageLinks s25Index s25Codes 5 13 8 6
def s25Data (i : Nat) : Nat × Nat :=
  let e := s25Forest i
  (e &&& 255, e >>> 8)
def s25Sample : Nat × Nat := (s25Blob228739, 96)
def s25Tags := dagTraceTags s25Mask 96 (dagTagBases s25StockWords s25Blob229311 s25Blob229524 96) 10 s25Data
def s25States := dagTrace s25Mask s25StockWords 10 s25Data
def s25MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm6, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val))), (pm1, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val))), (pm24, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 5, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 5, 4] 0 i.val)))]
def s25Moves := dagMoves s25MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s25Autos : DagMovesOK s25Mask s25Goal 64 s25Moves := dagMovesOfCheck (by decide +kernel)
def s25Check := dagCheckNode s25Mask s25Goal s25Chart (dagKnownCloses s25Goal s25Cuts) 188 s25States s25Moves s25Links s25Sample s25Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s25Roots : dagCheckRoots s25Mask s25Goal s25Chart (dagKnownCloses s25Goal s25Cuts) s25Witnesses (dagRef 188 s25States s25Moves s25Links 0) s25StockWords 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s25Block0 : treeBlock 0 24 s25Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s25Block24 : treeBlock 24 24 s25Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s25Block48 : treeBlock 48 24 s25Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s25Block72 : treeBlock 72 24 s25Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s25Block96 : treeBlock 96 24 s25Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s25Block120 : treeBlock 120 24 s25Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s25Block144 : treeBlock 144 24 s25Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s25Block168 : treeBlock 168 20 s25Check = true := by decide +kernel
theorem s25Group0_48 : treeBlock 0 48 s25Check = true := treeBlock_merge (start := 0) (left := 24) (right := 24) (check := s25Check) s25Block0 s25Block24
theorem s25Group48_48 : treeBlock 48 48 s25Check = true := treeBlock_merge (start := 48) (left := 24) (right := 24) (check := s25Check) s25Block48 s25Block72
theorem s25Group0_96 : treeBlock 0 96 s25Check = true := treeBlock_merge (start := 0) (left := 48) (right := 48) (check := s25Check) s25Group0_48 s25Group48_48
theorem s25Group96_48 : treeBlock 96 48 s25Check = true := treeBlock_merge (start := 96) (left := 24) (right := 24) (check := s25Check) s25Block96 s25Block120
theorem s25Group144_44 : treeBlock 144 44 s25Check = true := treeBlock_merge (start := 144) (left := 24) (right := 20) (check := s25Check) s25Block144 s25Block168
theorem s25Group96_92 : treeBlock 96 92 s25Check = true := treeBlock_merge (start := 96) (left := 48) (right := 44) (check := s25Check) s25Group96_48 s25Group144_44
theorem s25Group0_188 : treeBlock 0 188 s25Check = true := treeBlock_merge (start := 0) (left := 96) (right := 92) (check := s25Check) s25Group0_96 s25Group96_92
theorem s25Blocks : treeBlock 0 188 s25Check = true := s25Group0_188
theorem s25Known : Known s25Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s24Stock) s23Stock) s5Stock) s4Stock) s22Stock) s15Stock) s21Stock) s16Stock) s11Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s25Stock : Lower s25Mask s25StockWords s25Goal 11 := by
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
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def st35 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xff00ff0000ff00ff, 0), (0xff00ff00, 24)], [(0xff00ff00000000, 24)])
def pm25 : List (List (Nat × Nat) × List (Nat × Nat)) := [st24, st23, st35]
def s26Mask : Nat := 0xf0f00f0f00000000
abbrev s26Goal : Nat := sGoal &&& s26Mask
abbrev s26StockWords : List Nat := [0xa0a00a0a00000000, 0xc0c00c0c00000000, 0xf0f0000000000000, 0xf0000f0000000000]
def s26Fact : Nat × List Nat × Nat × Nat := (s26Mask, s26StockWords, 7, s26Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s26Stock : Lower s26Mask s26StockWords s26Goal 7 := dagShiftLower (width := 64) pm25 s1Stock (by decide +kernel)
def s27Mask : Nat := 0xf0f00f0f
abbrev s27Goal : Nat := sGoal &&& s27Mask
abbrev s27StockWords : List Nat := [0xa0a00a0a, 0xc0c00c0c, 0xf0f00000, 0xf0000f00]
def s27Fact : Nat × List Nat × Nat × Nat := (s27Mask, s27StockWords, 5, s27Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s27Stock : Lower s27Mask s27StockWords s27Goal 5 := dagShiftLower (width := 64) pm13 s17Stock (by decide +kernel)
def pm26 : List (List (Nat × Nat) × List (Nat × Nat)) := [st35, st34]
def s28Mask : Nat := 0xf0000f00f0000f
abbrev s28Goal : Nat := sGoal &&& s28Mask
abbrev s28StockWords : List Nat := [0xa0000a00a0000a, 0xc0000c00c0000c, 0xf0000000f00000, 0xf0000f00000000]
def s28Fact : Nat × List Nat × Nat × Nat := (s28Mask, s28StockWords, 5, s28Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s28Stock : Lower s28Mask s28StockWords s28Goal 5 := dagShiftLower (width := 64) pm26 s17Stock (by decide +kernel)
def s29Blob236887 : Nat := (cbits [0x8a412290e0742815, 0x383c1a0d4502910, 0x8150e05402151a0f, 0x9008a4281d048746, 0x8d42835100a4102, 0xf4383d140f0283c1, 0x42150485400151a0, 0x291a074101d00874, 0x100d43835008d400, 0xf4123d100f0103c, 0x41015140f4423d0a, 0x1d10874001d1005, 0x5000d468290e0a45, 0x48f0003c140d4123, 0xf4103d008f4423c0, 0x2829100745015100, 0xf4023c040d4])
def s29Blob237254 : Nat := (cbits [0x3bf8fffcfff3ff3f, 0xdeeffe7ffefff1fe, 0xfcdbf1f3f1e3cf8, 0xf3ff83ff03fe])
def s29Blob237365 : Nat := (cbits [0x340e42142382290c, 0x561001808483516e, 0x4b8252cc6544984a, 0xe496b2892a8])
def s29Mask : Nat := 0x3030030330300303
abbrev s29Goal : Nat := sGoal &&& s29Mask
abbrev s29StockWords : List Nat := [0x2020020220200202, 0x3030000030300000, 0x3000030030000300, 0x3030030300000000]
def s29Fact : Nat × List Nat × Nat × Nat := (s29Mask, s29StockWords, 5, s29Goal)
def s29Cuts : List (Nat × List Nat × Nat × Nat) := []
def s29Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[21, 41, 60, 21, 41, 60, 21, 41, 60, 21, 41, 60, 9, 28, 33, 40, 52, 9, 28, 33, 40, 52, 9, 28], rfl⟩
def s29Witnesses := unpackWitnesses s29StockWords [10772, 272897, 545313, 807433]
def s29Index (i : Nat) : Nat := unpack 0x119 3 i
def s29Codes (i : Nat) : Nat := unpack 0x2624000f 16 i
def s29Forest (i : Nat) : Nat := unpack 0xc48803c 15 i
def s29Links := pageLinks s29Index s29Codes 1 13 2 2
def s29Data (i : Nat) : Nat × Nat :=
  let e := s29Forest i
  (e &&& 3, e >>> 2)
def s29Sample : Nat × Nat := (s29Blob236887, 60)
def s29Tags := dagTraceTags s29Mask 60 (dagTagBases s29StockWords s29Blob237254 s29Blob237365 60) 4 s29Data
def s29States := dagTrace s29Mask s29StockWords 4 s29Data
def s29MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s29Moves := dagMoves s29MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Autos : DagMovesOK s29Mask s29Goal 64 s29Moves := dagMovesOfCheck (by decide +kernel)
def s29Check := dagCheckNode s29Mask s29Goal s29Chart (dagKnownCloses s29Goal s29Cuts) 2 s29States s29Moves s29Links s29Sample s29Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Roots : dagCheckRoots s29Mask s29Goal s29Chart (dagKnownCloses s29Goal s29Cuts) s29Witnesses (dagRef 2 s29States s29Moves s29Links 0) s29StockWords 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block0 : treeBlock 0 2 s29Check = true := by decide +kernel
theorem s29Blocks : treeBlock 0 2 s29Check = true := s29Block0
theorem s29Known : Known s29Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Stock : Lower s29Mask s29StockWords s29Goal 5 := by
  apply lowerDag _ _ _ _ s29Autos _ _ _ s29Known _ s29Roots s29Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s29Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def s30Mask : Nat := 0x5050050550500505
abbrev s30Goal : Nat := sGoal &&& s30Mask
abbrev s30StockWords : List Nat := [0x4040040440400404, 0x5050000050500000, 0x5000050050000500, 0x5050050500000000]
def s30Fact : Nat × List Nat × Nat × Nat := (s30Mask, s30StockWords, 5, s30Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s30Stock : Lower s30Mask s30StockWords s30Goal 5 := dagShiftLower (width := 64) pm1 s29Stock (by decide +kernel)
def s31Mask : Nat := 0xa0a0a0a00a0a0a0a
abbrev s31Goal : Nat := sGoal &&& s31Mask
abbrev s31StockWords : List Nat := [0x8080808008080808, 0xa0a0a0a000000000, 0xa000a0000a000a00, 0xa0a000000a0a0000]
def s31Fact : Nat × List Nat × Nat × Nat := (s31Mask, s31StockWords, 5, s31Goal)
def s31Witnesses := unpackWitnesses s31StockWords [5641, 281089, 529923, 796163]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s31Stock : Lower s31Mask s31StockWords s31Goal 5 := by
  apply essentialLift (witnesses := s31Witnesses) (cut := s12Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s12StockWords) (by decide +kernel)
  · exact s12Stock
  · decide +kernel
def s32Mask : Nat := 0xa0a00a0aa0a00a0a
abbrev s32Goal : Nat := sGoal &&& s32Mask
abbrev s32StockWords : List Nat := [0x8080080880800808, 0xa0a00000a0a00000, 0xa0000a00a0000a00, 0xa0a00a0a00000000]
def s32Fact : Nat × List Nat × Nat × Nat := (s32Mask, s32StockWords, 5, s32Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s32Stock : Lower s32Mask s32StockWords s32Goal 5 := dagShiftLower (width := 64) pm6 s31Stock (by decide +kernel)
def s33Mask : Nat := 0xc0c00c0cc0c00c0c
abbrev s33Goal : Nat := sGoal &&& s33Mask
abbrev s33StockWords : List Nat := [0x8080080880800808, 0xc0c00000c0c00000, 0xc0000c00c0000c00, 0xc0c00c0c00000000]
def s33Fact : Nat × List Nat × Nat × Nat := (s33Mask, s33StockWords, 5, s33Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s33Stock : Lower s33Mask s33StockWords s33Goal 5 := dagShiftLower (width := 64) pm24 s31Stock (by decide +kernel)
def pm27 : List (List (Nat × Nat) × List (Nat × Nat)) := [st03, st01, st24, st25]
def s34Mask : Nat := 0xa0a00000a0a
abbrev s34Goal : Nat := sGoal &&& s34Mask
abbrev s34StockWords : List Nat := [0x80800000808, 0xa0000000a00, 0xa0a00000000]
def s34Fact : Nat × List Nat × Nat × Nat := (s34Mask, s34StockWords, 4, s34Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s34Stock : Lower s34Mask s34StockWords s34Goal 4 := dagShiftLower (width := 64) pm27 s0Stock (by decide +kernel)
def pm28 : List (List (Nat × Nat) × List (Nat × Nat)) := [st13, st24, st25]
def s35Mask : Nat := 0xc0c00000c0c
abbrev s35Goal : Nat := sGoal &&& s35Mask
abbrev s35StockWords : List Nat := [0x80800000808, 0xc0000000c00, 0xc0c00000000]
def s35Fact : Nat × List Nat × Nat × Nat := (s35Mask, s35StockWords, 4, s35Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s35Stock : Lower s35Mask s35StockWords s35Goal 4 := dagShiftLower (width := 64) pm28 s0Stock (by decide +kernel)
def pm29 : List (List (Nat × Nat) × List (Nat × Nat)) := [st35]
def pm30 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01, st35]
def s36Blob258889 : Nat := (cbits [0x54140b0482c060b, 0xc381e0e07428160a, 0x2291108c42230188, 0xa050a85029108a41, 0xa0d86835140a8442, 0x2c020b1a0f0383c1, 0x381500854100b010, 0x160e05804161a054, 0x487428170185c68, 0x7c281e05078281d, 0x440230108c02230e, 0x42a100a41029008a, 0xb018ac402a040a80, 0x10ac422b050ac122, 0xd842350a0d4502b1, 0x283c1a0dc44360a0, 0x3e1a0f4383d140f0, 0x1082c000b1a0f838, 0x85400151402c440b, 0x8001610854121501, 0x2171105814160185, 0xd1a05c38170105c0, 0x1078681d04074021, 0x7c061f1a078101e0, 0x230a07c141f048, 0x291408c14230488c, 0x110a41429018a400])
def s36Blob259460 : Nat := (cbits [0xcc9fe3f9e3f11faf, 0x7c72e3d7fff1fc3f, 0xffe3fc3f0e7fc7e, 0x3ff8000fff8f0078, 0x807cfc6700fffffc, 0xf0ffc003ff07ff8f, 0x3ffffff0000fff80, 0xff000000])
def s36Blob259647 : Nat := (cbits [0x80116090a0900d83, 0x24206285223044b8, 0xe4520b890042a422, 0x3da8000d5b0f0078, 0x8944b46600893000, 0x4e6491121604c90a, 0xaad71240120bdb00, 0x88092223])
def s36Mask : Nat := 0xf0f00f0ff0f00f0f
abbrev s36Goal : Nat := sGoal &&& s36Mask
abbrev s36StockWords : List Nat := [0xa0a00a0aa0a00a0a, 0xc0c00c0cc0c00c0c, 0xf0f00000f0f00000, 0xf0000f00f0000f00, 0xf0f00f0f00000000]
def s36Fact : Nat × List Nat × Nat × Nat := (s36Mask, s36StockWords, 10, s36Goal)
def s36Cuts : List (Nat × List Nat × Nat × Nat) := [s22Fact, s2Fact, s26Fact, s27Fact, s28Fact, s29Fact, s30Fact, s32Fact, s33Fact, s34Fact, s35Fact]
def s36Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[11, 21, 22, 35, 41, 42, 60, 11, 21, 22, 35, 41, 3, 9, 10, 28, 33, 34, 40, 52, 3, 9, 10, 28], rfl⟩
def s36Witnesses := unpackWitnesses s36StockWords [5642, 267785, 535041, 792067, 1066499]
def s36Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 15 then (if j < 7 then (if j < 3 then (if j < 1 then (cbits [0x401022f00300001, 0x4a004a004240420, 0x58004a704a004a0, 0x580058005800580]) else (if j < 2 then (cbits [0x5e005e005830580, 0x640064005e305e0, 0x6a006a006430640, 0x861086006ae06a0]) else (cbits [0x8a008a008810880, 0x8e208e008a208a0, 0x96b092209200920, 0xac00ac00ac00ac0]))) else (if j < 5 then (if j < 4 then (cbits [0xac00ac00ac00ac0, 0xb800b800ac60ac0, 0xb870b800b800b80, 0xc800c610c600c60]) else (cbits [0xca00ca00c810c80, 0xd800d800d800ca7, 0xea20da80da00d81, 0x10220eea0ee00ee0])) else (if j < 6 then (cbits [0x11a011a011621068, 0x1580154212f311aa, 0x15c015c015821580, 0x16201620162015c3]) else (cbits [0x1662166016601622, 0x174016a516a016a0, 0x1740174017401740, 0x17e017e017e01745])))) else (if j < 11 then (if j < 9 then (if j < 8 then (cbits [0x18a017e617e017e0, 0x18a018a018a018a0, 0x1960196018a618a0, 0x1960196019601960]) else (cbits [0x1a201a201a201966, 0x1b801a2b1a201a20, 0x1bc01b821b801b80, 0x1c801bc61bc01bc0])) else (if j < 10 then (cbits [0x1e2b1de21de01c8b, 0x22c0222521a41f91, 0x22c122c022c022c0, 0x24042327230122e1]) else (cbits [0x2480248024802480, 0x24c124a124812480, 0x25242520250124e1, 0x25e025e025e025a2]))) else (if j < 13 then (if j < 12 then (cbits [0x2680260425e125e0, 0x286027e426aa2681, 0x2880286128602860, 0x290028a328a02881]) else (cbits [0x2a2029a429a02905, 0x2b002b002ac22a25, 0x2b402b402b402b02, 0x2be82be02be02b45])) else (if j < 14 then (cbits [0x2e632e412d0a2ce1, 0x32e430362eea2ec1, 0x33a133a033a03362, 0x33e033e033c133c0]) else (cbits [0x34803480348033e5, 0x3540354035023484, 0x3563356035603541, 0x3681360435e135c1]))))) else (if j < 22 then (if j < 18 then (if j < 16 then (cbits [0x36e136c136a136a0, 0x37a037a037a03705, 0x38a0380537e137a2, 0x390538e138a238a0]) else (if j < 17 then (cbits [0x3b673b4139cc39a1, 0x3c8c3c613c603c41, 0x4086408040803e14, 0x4140414041404140]) else (cbits [0x4164416041414140, 0x42604222420141e1, 0x4380428842614260, 0x43e0438343804380]))) else (if j < 20 then (if j < 19 then (cbits [0x44434440440243e1, 0x4528450144a344a0, 0x48a048a048434631, 0x48e048e048a248a0]) else (cbits [0x4a0149c249c048e7, 0x4a604a414a214a20, 0x4b004a654a604a60, 0x4b414b404b404b02])) else (if j < 21 then (cbits [0x4c404c404b674b60, 0x4d004ce14c644c41, 0x4e804da74d434d02, 0x4f674f414e864e80]) else (cbits [0x52c052c052635051, 0x53075300530052c2, 0x5421542053e253e0, 0x5521544754405440])))) else (if j < 26 then (if j < 24 then (if j < 23 then (cbits [0x5564554155405540, 0x57265647560255e1, 0x5a0459e1580f57e1, 0x5b605a875a805a80]) else (cbits [0x5bc05b635b605b60, 0x5c235c205c205bc3, 0x5dc05d825c885c80, 0x61625f135dca5dc0])) else (if j < 25 then (cbits [0x61e361e061a261a0, 0x6282628062426240, 0x63806380638062c6, 0x6440644063866380]) else (cbits [0x6500650064466440, 0x66b4654b65026500, 0x6a0069c269a16924, 0x6a036a006a006a00]))) else (if j < 28 then (if j < 27 then (cbits [0x6ac36a826a616a60, 0x6ba86b816b236b20, 0x6f006f006ec26cb1, 0x70406f676f606f03]) else (cbits [0x70e0704570407040, 0x73e271d170e770e0, 0x7561748774237420, 0x7641758675807580])) else (if j < 29 then (cbits [0x796979227809766d, 0x7d367c097a8c7a80, 0x80c080a180437fe3, 0x81838180812380c3]) else 0x82cc8282828081e5))))) 16 (i % 16)
def s36Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 33 then (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then (cbits [0x800900200800001f, 0x1f1aa01312600f0a, 0x29e03324e02720e0, 0xc31f2fa3152d0314, 0x2036a33334e32732, 0x38c93338892c37e6]) else (cbits [0x800f0040093a4c38, 0x2702001f01201300, 0x383140300330280, 0x432706831f054315, 0x2c09262008633307, 0xa6c3809e93309a9])) else (if j < 3 then (cbits [0xc62000a31e006620, 0xe010f4400ec3800, 0x1663201431400a0, 0xcc3801a92c01863e, 0x2c02231401ef4401, 0x2a01e026f440249]) else (cbits [0x201e02ef4402c620, 0x9036c3803462003, 0x4001303c00f03a0, 0x603304402704201f, 0x2702231f00631504, 0x4862003433302c3]))) else (if j < 6 then (if j < 5 then (cbits [0x2c3805093304c92c, 0x2c03e00c03e31c05, 0x4a92c44ac3804a9, 0xec3844a92c04ec38, 0x3e05803205602a04, 0x1431d00c31905a0]) else (cbits [0x63e05e63205c62a, 0x44064c3806292c06, 0x6a92c05c314066f, 0xc3e06ec3806c931, 0x2a076314072f4407, 0x5e62007a33e0783])) else (if j < 7 then (cbits [0x4f44080c3e07e92c, 0x1408262807c32808, 0x7a33208a32a0883, 0xcc3847e92c060620, 0x1f09062808ec3d08, 0x6262104862001a3]) else (cbits [0x492c47e63307e627, 0x2c494c3809893309, 0xe31b096c3804a9, 0x633302432b01c31f, 0x2b06462104c62003, 0x9492c08c63306a6])))) else (if j < 12 then (if j < 10 then (if j < 9 then (cbits [0x6c3804e92c09cc38, 0x1d07a31905031409, 0x8e33d0803310a03, 0x892c0a462a0a2620, 0x1b09033c08233009, 0x2632b01e31f0103]) else (cbits [0x662105262002e333, 0x2c08463307262b06, 0xaa01a09cc384949, 0xe0320b602a0b001e, 0x1e0ca31a0c403e0b, 0xf03320e232a0d63])) else (if j < 11 then (cbits [0x262110a6200fe33e, 0x3f11663311462b11, 0x11ec3811a92c1186, 0xcc38124f44122c3f, 0x440b2c380aef440a, 0xba92c0b83140b4f]) else (cbits [0x2f440c06200bcf44, 0x2a0c8c380c66200c, 0xd092c0ce6200cc3, 0x83140d4f440d2c38, 0x380dc63e0da6320d, 0xe43140e0f440dec]))) else (if j < 14 then (if j < 13 then (cbits [0xa9310e892c0e6331, 0x1e0eef440ecc3e0e, 0xf66200f432a0f23, 0xcf440fac3e0f892c, 0x2010232a10031e0f, 0x106c384f892c1046]) else (cbits [0xe01d10c019108c3d, 0x3e0c03320b832a10, 0xf66320e462a0c63, 0x4c3886292c10463e, 0x280ce624110f4486, 0xf86320d06260d86])) else (if j < 15 then (cbits [0xcc3886292c4f863e, 0x2a0ac32651cf4411, 0xc833e0ba3360b23, 0x86360de62a0d2626, 0x3886492c10663e0e, 0xfa33c120f4411cc]) else (cbits [0x432a0ae326108348, 0x260c233e0bc3360b, 0xee6360e062a0d46, 0xcc3811092c0fc63e, 0x2a128008120f4451, 0x15403215002b13a0]))))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then (cbits [0x831c0ca31416203e, 0x1f18e31e18831d16, 0x19662019432b1923, 0xc3819c92c19a62b, 0x1c1a8f441a4c3f1a, 0x136c3813492c12a3]) else (cbits [0xe31412c00e138f44, 0x3813092c12e62003, 0x13062812e628132c, 0xc0100cc008132628, 0x3f14892c14631413, 0x14ef4414cc3814a9])) else (if j < 19 then (cbits [0x292c14063313e620, 0x1013e31c144c3814, 0x14431c14231c1400, 0xc02a15602815231c, 0x2c160f4415e92c15, 0x15a33415ac381589]) else (cbits [0xe92c16402a556028, 0x855a334166c3855, 0x15201f13c01e12a0, 0x633317232716a314, 0x3317e92c17a62017, 0x16c012186c381829]))) else (if j < 22 then (if j < 21 then (cbits [0xc3816e92c03e314, 0x14178c3d174c3e17, 0x57cc3817c92c12e3, 0xe62013e32a130314, 0x1c180c3817c92c16, 0x17433114002a1840]) else (cbits [0x432a13231417833d, 0x3857c92c17062014, 0x18cf4418ac38180c, 0x632a190f4498ac38, 0x388d092c0ce62014, 0x134314198f448d2c])) else (if j < 23 then (cbits [0x62055e33e15e332, 0x388d092c17a6280d, 0x17c93459ef4419ec, 0x633e148336136314, 0x2917e6280d262016, 0x8d292c98a62a18a6]) else (cbits [0x9341a2f4419ec38, 0x1c14a0361a602818, 0x1383141840101823, 0x462016033e14e336, 0x2a18c6291866280d, 0x59ec3819892c1906])))) else (if j < 28 then (if j < 26 then (if j < 25 then (cbits [0x800c0d60081a2f44, 0xf18e00e18800d16, 0x1ba0331ac02a1920, 0x632a1be3141bc03f, 0x201d233f1d03331c, 0x1e66321da62a1d46]) else (cbits [0x863f1f263e1ee633, 0x3f200c381fc92c1f, 0x1ae03020cf44204c, 0x8f441b693f1b492c, 0x301b2c381b092c1b, 0xd83141b233c1b03])) else (if j < 27 then (cbits [0xec381c263e1c0632, 0x2c1c80301c4f448d, 0x1cef441cc93f9b49, 0xa33c1cac389b092c, 0x441d6c3816a3181c, 0x17062416e6241d8f]) else (cbits [0x2c3c1e09301dc92c, 0x381dec3c1e4f441e, 0x5dec3c1de92c5dec, 0x862a1c03140da008, 0xc1ecf441ea92c1e, 0x17400c1f0f4a1720]))) else (if j < 30 then (if j < 29 then (cbits [0x462a1c23140dc008, 0xc1f6c385ea92c1f, 0x17800c1faf491760, 0xa93e1ea93217a318, 0x245fef441fec385e, 0x17e3180de31417c6]) else (cbits [0x433698a31a18a319, 0x2c9b46368de6201b, 0x1f693e1dc9361d69, 0x624202f441fec38, 0x3620602a18200c18, 0x1cc33620a32a1b60])) else (if j < 31 then (cbits [0x801c1fa6491f063d, 0x180e031420801c20, 0x19031a18c3191863, 0xe6361c46201b8336, 0x3e1e49361d892c1c, 0x202f445fec381ec9]) else (if j < 32 then (cbits [0xc01219400f0e2008, 0x1421203f2100271a, 0x22032721e3152143, 0xa33522a333224331, 0x3123292c23033f1d, 0x24093f23e93323a9]) else (cbits [0xac3f248c3e244c38, 0x2c0e431424cf4424, 0x218c3821693186a9, 0x232821cf4421ac3e, 0x381ae01c0e600822, 0x1b0328228f44226c]))))))) else (if j < 50 then (if j < 41 then (if j < 37 then (if j < 35 then (if j < 34 then (cbits [0xef4a22cc3d1b2328, 0x1e0e831462232822, 0x22663186a6201b43, 0x6c3e234c381dc635, 0x140ea008238f4423, 0x22c33d23cf442163]) else (cbits [0x86202426281b6012, 0x8246f44234c3821, 0x23692c21a3140ec0, 0x831e0ee31422e33d, 0x4122863d21c6201b, 0x23cc3d238c381e46])) else (if j < 36 then (cbits [0x401a250008246f44, 0x2a25c01f25801e15, 0x27203e27002b25e0, 0x32b1ba31f0f0314, 0x2b28462128062021, 0x29292c28863f2866]) else (cbits [0x262029cf44298c3e, 0x8256f4425492c25, 0xf400825af440f20, 0x233fa2231d260314, 0x4426cc3826a93e26, 0x268c4826432826ef]))) else (if j < 39 then (if j < 38 then (cbits [0x833d26633426663c, 0x2a27602827401c26, 0x27e92c27c62027a0, 0xc32827892c87c314, 0x3e26032a25231487, 0x87e92c0f662027c3]) else (cbits [0x2028282f44880c3e, 0x3626203628a01ca2, 0x28cc3c290f4828e6, 0xc01ce68c48264028, 0x14e6864226804228, 0x27e33e15e3262543])) else (if j < 40 then (cbits [0x4c3e87e92c0f8620, 0x1426a036296f4429, 0x88062029a3280fa3, 0x2314294c3829063d, 0x2a16032625631488, 0xfc62026e33625a3]) else (cbits [0x8296c3828292c, 0x1f2a601e16201a2a, 0x2b802b2ac02a2aa0, 0xc31f0fe314272032, 0x212ba62021232b1b, 0x2c46332c262b2c06])))) else (if j < 45 then (if j < 43 then (if j < 42 then (cbits [0xcc3d2cac3869292c, 0x3865492c2a26202c, 0x2a8c381000082a4c, 0x231d2ae314102008, 0x3d2b292c2b0327e2, 0x6643282b6c382b49]) else (cbits [0x2314668331668c48, 0x2027c3322ae32a2a, 0x88cc38c7e92c1046, 0x20282be6282bcc3d, 0x362b00362c601ce2, 0x68cc3c690f482c86])) else (if j < 44 then (cbits [0x4314a68c48664028, 0x362a832a1663262a, 0x88c92c1066202b23, 0x83142b4036696c38, 0x3d2bc6202ce32810, 0x2be314694c386906]) else (cbits [0xa0132d400f2d2009, 0x332e60272e201f2d, 0x10a3150383142ec0, 0xa33328032721431f, 0x3389a92c8926202b, 0x3a3142f8c382f09]))) else (if j < 47 then (if j < 46 then (cbits [0xec3810c6202d631e, 0x142d600e2d8f4480, 0x2de63e2dc63210e3, 0xf4481cc3881a92c, 0x4482492c0423142e, 0x446202e801e2e4f]) else (cbits [0x66202ee01e2eaf44, 0x19050314836c3804, 0x8803312f231d27c3, 0x662a2f46202bc33d, 0x3c88233089892c2f, 0x2e031f2d831b2be3])) else (if j < 48 then (cbits [0x26202ea3332e432b, 0x3321c62b11062105, 0x89cc38c9492c2826, 0x402a3000122fc00e, 0x1430c03e30803230, 0x1963191123150543]) else (if j < 49 then (cbits [0x433321e32b1be31d, 0x3230e62a2c033f28, 0x91a92c32063e3186, 0xaf44328c3f91ec38, 0x382fef448acc3832, 0x56008302f448b2c]) else (cbits [0x8314306f448ba92c, 0x3805a31430af4405, 0x31033105c3148c8c, 0x4c3e3129318e892c, 0x1d05e314316f4431, 0x8f892c31c62a31a3])))))) else (if j < 58 then (if j < 54 then (if j < 52 then (if j < 51 then (cbits [0x31431ef448fac3e, 0x2c32462a32231d06, 0x326c3d906c38cf89, 0xe31a3266488fa63c, 0x3e30633630231e2f, 0x19862506662030a3]) else (cbits [0xe93e3169361c4629, 0x8920f44d1cc3831, 0x19a00f1140090680, 0xe0312860271c6011, 0x3f1da03533203332, 0x33832730e3142c20])) else (if j < 53 then (cbits [0xc931a3292c33a33f, 0x3834293f34093333, 0x34ac3f348c3e344c, 0x6201c831c34cf44, 0x28330f44a26c3831, 0x336f4a334c3d1ca6]) else (cbits [0xef4431231406c008, 0x281cc01133403d33, 0xa34c3806e314a426, 0x4314070008346f44, 0x1433603da3692c31, 0x33033d1ce31d0723]))) else (if j < 56 then (if j < 55 then (cbits [0x8c383166201e4341, 0x8346f4433ec3da3, 0x15400d1160090740, 0x1f354013350011, 0x142c403f22002b1d, 0x36032b35a32a3563]) else (cbits [0x862b31862036233e, 0x44a98c3ea9292c33, 0x352f4431a314368f, 0x8f44a5492c076314, 0x3f22201d07800835, 0xa6a93e31c3142c80])) else (if j < 57 then (cbits [0xa00835ef4435cc38, 0x2aa7632836401007, 0x84314a7e92c3663, 0x862035231d160319, 0x3831e92c35e63635, 0x118009086008a96c]) else (cbits [0xe01336c01116200d, 0x3323002b1d201f36, 0x37232a3703142880, 0x62036233237832b, 0x38e9292c33a62b32, 0x32231437ac3dacac])))) else (if j < 62 then (if j < 60 then (if j < 59 then (cbits [0x492c088314aa8c38, 0x1d08a008aa4c38e5, 0x32431428e0276220, 0x6c3837493dab292c, 0x3d08e008e6803137, 0x3266203743362900]) else (cbits [0x8e94c3837c628, 0x1b11a31509231409, 0x2923271fc31f19c3, 0xa621892620692333, 0x2ce92633a9262791, 0x780c383849333809])) else (if j < 61 then (cbits [0xe62711c621094620, 0x2c6966331fe62b19, 0xe9693391c92d8949, 0x6c3809692c382c38, 0x3127e32509831489, 0x89862069433d2943]) else (cbits [0x463da94631a7e625, 0x1509a31438692ce9, 0x20031f1a031b11e3, 0xa6202ca33323232b, 0x33a3262b91e62189, 0x38ac3838092caca6]))) else (if j < 64 then (if j < 63 then (cbits [0x262712062109c620, 0x2c23863720262b1a, 0xa3893792092d89c9, 0x200909e008382c38, 0x192040131a400f12, 0x39001f38e01d2720]) else (cbits [0xc03d29803124002b, 0x193283152f03142c, 0x39831f39631d3623, 0xa33da9833134232b, 0x2b39e62a39c62037, 0x29a03038492c3a26])) else (if j < 65 then (cbits [0x60122f23142ce03c, 0x1039463639231d20, 0xa9a3300a00082080, 0x201d20a01137c33c, 0x200a231439a63639, 0xa400838692c2f46]) else (if j < 66 then (cbits [0x231d2f631424201d, 0x1d39401d3a0c38a4, 0x1243150a631439a3, 0xc32b20c31f1a831b, 0x212f862029c33324, 0x36863334c62b32a6]) else 0x38ac3878092c))))))) 24 (i % 16)
def s36Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 15 then (if j < 7 then (if j < 3 then (if j < 1 then (cbits [0x120200400403e00, 0x8f01401e0231000c, 0x880561c014c40051, 0x90286280a009809e, 0xa496028c7c0a31, 0x7a202987]) else (if j < 2 then (cbits [0x2581118a04403e02, 0xf05404e027a2045, 0x66027a2054c40150, 0xc064c401900f0640, 0xe1d0048746280261, 0x18e07c01]) else (cbits [0x4e1d00f8740261d, 0x96094c401d019874, 0x661d61c09d2581d4, 0x50ac62a0261c0752, 0x42b01f0ac0642b01, 0x3190acc5]))) else (if j < 5 then (if j < 4 then (cbits [0x8702b4960acc7c2b, 0x960d463e027a20ad, 0x7c3561c0d5262354, 0xa0ec64e027a20d58, 0x3e19f0ec6543b18, 0x4960ec65]) else (cbits [0xe883b31410587c3b, 0x9511062844199809, 0x504861e911870441, 0xc12d2584a310008c, 0x4e4960092664a61, 0x49980987])) else (if j < 6 then (cbits [0xc545031014063a50, 0xd1540120161c008, 0x3c557a2159870560, 0x5155e885961c1640, 0x85c4961706285c01, 0x19155e8]) else (cbits [0x7c557a2180c4060, 0x8d1558706331018c, 0x5866310198654661, 0xf155e886661c1992, 0xc6c3191b06286c18, 0x61c1b0c7])))) else (if j < 11 then (if j < 9 then (if j < 8 then (cbits [0x62872195155e886c, 0x989c9258721989c8, 0x64557a21c987c724, 0x1e46547918f1e46, 0x87961f1e52587931, 0x19f155e8]) else (cbits [0xc408019520063c80, 0x1015587a8061c200, 0x888600ea18032863, 0x9954c5655310955e, 0x8e496154c7e5531, 0x61c15587])) else (if j < 10 then (cbits [0xe885561f955e8890, 0x8e25401094007805, 0x589631025801c961, 0xc2552589561c2592, 0x9e015251e889561, 0x31027c02]) else (cbits [0x8709f49627cc669f, 0x9fa792589e18a279, 0x56947a22798709e4, 0x42ac0649418e2a40, 0x4ab61c2b1258ac01, 0x4962ac05]))) else (if j < 13 then (if j < 12 then (cbits [0x54b201f251e88ab, 0x8a2d46389461c2c8, 0x70b64962d8024b61, 0x9ad587cba193ad58, 0x8be3102d587abc19, 0x4962d525]) else (cbits [0x38c2499ad5870c0, 0x1c31463a9461c2d4, 0x88c818f251e88c56, 0x2506569418fa51e, 0x894315a51e88cc31, 0x61c33d25])) else (if j < 14 then (cbits [0x87e947a234587094, 0x9805e889401434d, 0x58d801835c054d60, 0xfb5d258d761c3612, 0xed6019b59e88d749, 0x18a35807]) else (cbits [0xe88e031f380c64e0, 0x1c394060e4195359, 0x66d67a239127ee46, 0xc3acc40d619fb586, 0x8ee315359e88eb61, 0x61e3bd25]))))) else (if j < 22 then (if j < 18 then (if j < 16 then (cbits [0xe88ee61e3b9260ee, 0x963d0c54f4319359, 0x94f8319b59e88f44, 0xc3e8c54fa31f359e, 0x8d67a4bf4c7ed661, 0x61c3fd25]) else (if j < 17 then (cbits [0x87ed67a2405870d6, 0x9540c0390401540d, 0x4f0800f805e88d61, 0x8c2c6290801fc200, 0x90b61f42d8710b49, 0x18ac21e8]) else (cbits [0x6630819444464f08, 0x99c21e891361c44c, 0x7f087a545987b161, 0xf4698711a4964206, 0x91e498c21e891a61, 0x499c21e8]))) else (if j < 20 then (if j < 19 then (cbits [0x8710831448527f08, 0x1fc2187d087a248d, 0x1128013805e89086, 0x24a5259293104a40, 0xf287a24b403d287a, 0x154a003]) else (cbits [0x6513219fcc062930, 0x9f4c18913231e4cc, 0x57287a24c1871304, 0x44e80393a01f4a00, 0x13a0154e92593c01, 0x4964e8c4])) else (if j < 21 then (cbits [0xc43287a2504c4128, 0xe514c7f28315ca0, 0x914531b515879460, 0x252987d4a4964a1e, 0x92819453587d287a, 0x19805e8]) else (cbits [0x8715131054401150, 0xfd418715400f541, 0x4f5718a55c055500, 0xc55d27b5749655c6, 0xb5e3105400575061, 0x31457d87])))) else (if j < 26 then (if j < 24 then (if j < 23 then (cbits [0xc6750315d40c4350, 0x1c540c6d6300e58c, 0x280119459d87b506, 0xf5ac01f69004da46, 0x56e009da5e896b18, 0x31f5b8c6]) else (cbits [0xe897200fda5e896e, 0xa25d003d74013da5, 0x676900f5dc067697, 0x55e4c417918ede52, 0xd7e18a8058716931, 0x7a25fc01])) else (if j < 25 then (cbits [0x557e7a26040257e, 0xa26140657e7a260c, 0x63883155f807d7e7, 0x262187d88498e206, 0x58d18ee34c657e7a, 0x7a2634c5]) else (cbits [0xc559118ee44c7d7e, 0xa25f987f7e61ee44, 0x8998018e5c63e017, 0x566987b9a019e5de, 0x39719fe5c64f977a, 0x7a267d26]))) else (if j < 28 then (if j < 27 then (cbits [0x8719749fe5d26797, 0x1fe5d87d977a268d, 0x23a8193805e89976, 0xa6a0027a87a26a40, 0x1ae1956a1e89ac18, 0x7a26b987]) else (cbits [0x21b219f6a0657a8, 0x99805e89a81956c8, 0x29b6009ed8023b61, 0xc6e927bba1956d86, 0x1be61eed8657b661, 0x310004c5])) else (if j < 29 then (cbits [0x267c061c705259c0, 0x1c7152580149670d, 0x3fc700ef1d266016, 0xef1cc6dc918ef240, 0x1c731b73463fc718, 0x31571cc4]) else (cbits [0x87001315f1d871d0, 0x1])))))) 22 (i % 16)
def s36Links := pageLinks s36Index s36Codes 5 13 9 6
def s36Data (i : Nat) : Nat × Nat :=
  let e := s36Forest i
  (e &&& 511, e >>> 9)
def s36Sample : Nat × Nat := (s36Blob258889, 96)
def s36Tags := dagTraceTags s36Mask 96 (dagTagBases s36StockWords s36Blob259460 s36Blob259647 96) 9 s36Data
def s36States := dagTrace s36Mask s36StockWords 9 s36Data
def s36MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm29, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 5, 4, 3] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 5, 4, 3] 0 i.val))), (pm1, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val))), (pm30, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 2, 5, 4, 3] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 2, 5, 4, 3] 0 i.val)))]
def s36Moves := dagMoves s36MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s36Autos : DagMovesOK s36Mask s36Goal 64 s36Moves := dagMovesOfCheck (by decide +kernel)
def s36Check := dagCheckNode s36Mask s36Goal s36Chart (dagKnownCloses s36Goal s36Cuts) 467 s36States s36Moves s36Links s36Sample s36Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s36Roots : dagCheckRoots s36Mask s36Goal s36Chart (dagKnownCloses s36Goal s36Cuts) s36Witnesses (dagRef 467 s36States s36Moves s36Links 0) s36StockWords 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s36Block0 : treeBlock 0 24 s36Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s36Block24 : treeBlock 24 24 s36Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s36Block48 : treeBlock 48 24 s36Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s36Block72 : treeBlock 72 24 s36Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s36Block96 : treeBlock 96 24 s36Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s36Block120 : treeBlock 120 24 s36Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s36Block144 : treeBlock 144 24 s36Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s36Block168 : treeBlock 168 24 s36Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s36Block192 : treeBlock 192 24 s36Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s36Block216 : treeBlock 216 24 s36Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s36Block240 : treeBlock 240 24 s36Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s36Block264 : treeBlock 264 24 s36Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s36Block288 : treeBlock 288 24 s36Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s36Block312 : treeBlock 312 24 s36Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s36Block336 : treeBlock 336 24 s36Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s36Block360 : treeBlock 360 24 s36Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s36Block384 : treeBlock 384 24 s36Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s36Block408 : treeBlock 408 24 s36Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s36Block432 : treeBlock 432 24 s36Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s36Block456 : treeBlock 456 11 s36Check = true := by decide +kernel
theorem s36Group0_48 : treeBlock 0 48 s36Check = true := treeBlock_merge (start := 0) (left := 24) (right := 24) (check := s36Check) s36Block0 s36Block24
theorem s36Group72_48 : treeBlock 72 48 s36Check = true := treeBlock_merge (start := 72) (left := 24) (right := 24) (check := s36Check) s36Block72 s36Block96
theorem s36Group48_72 : treeBlock 48 72 s36Check = true := treeBlock_merge (start := 48) (left := 24) (right := 48) (check := s36Check) s36Block48 s36Group72_48
theorem s36Group0_120 : treeBlock 0 120 s36Check = true := treeBlock_merge (start := 0) (left := 48) (right := 72) (check := s36Check) s36Group0_48 s36Group48_72
theorem s36Group120_48 : treeBlock 120 48 s36Check = true := treeBlock_merge (start := 120) (left := 24) (right := 24) (check := s36Check) s36Block120 s36Block144
theorem s36Group192_48 : treeBlock 192 48 s36Check = true := treeBlock_merge (start := 192) (left := 24) (right := 24) (check := s36Check) s36Block192 s36Block216
theorem s36Group168_72 : treeBlock 168 72 s36Check = true := treeBlock_merge (start := 168) (left := 24) (right := 48) (check := s36Check) s36Block168 s36Group192_48
theorem s36Group120_120 : treeBlock 120 120 s36Check = true := treeBlock_merge (start := 120) (left := 48) (right := 72) (check := s36Check) s36Group120_48 s36Group168_72
theorem s36Group0_240 : treeBlock 0 240 s36Check = true := treeBlock_merge (start := 0) (left := 120) (right := 120) (check := s36Check) s36Group0_120 s36Group120_120
theorem s36Group240_48 : treeBlock 240 48 s36Check = true := treeBlock_merge (start := 240) (left := 24) (right := 24) (check := s36Check) s36Block240 s36Block264
theorem s36Group312_48 : treeBlock 312 48 s36Check = true := treeBlock_merge (start := 312) (left := 24) (right := 24) (check := s36Check) s36Block312 s36Block336
theorem s36Group288_72 : treeBlock 288 72 s36Check = true := treeBlock_merge (start := 288) (left := 24) (right := 48) (check := s36Check) s36Block288 s36Group312_48
theorem s36Group240_120 : treeBlock 240 120 s36Check = true := treeBlock_merge (start := 240) (left := 48) (right := 72) (check := s36Check) s36Group240_48 s36Group288_72
theorem s36Group360_48 : treeBlock 360 48 s36Check = true := treeBlock_merge (start := 360) (left := 24) (right := 24) (check := s36Check) s36Block360 s36Block384
theorem s36Group432_35 : treeBlock 432 35 s36Check = true := treeBlock_merge (start := 432) (left := 24) (right := 11) (check := s36Check) s36Block432 s36Block456
theorem s36Group408_59 : treeBlock 408 59 s36Check = true := treeBlock_merge (start := 408) (left := 24) (right := 35) (check := s36Check) s36Block408 s36Group432_35
theorem s36Group360_107 : treeBlock 360 107 s36Check = true := treeBlock_merge (start := 360) (left := 48) (right := 59) (check := s36Check) s36Group360_48 s36Group408_59
theorem s36Group240_227 : treeBlock 240 227 s36Check = true := treeBlock_merge (start := 240) (left := 120) (right := 107) (check := s36Check) s36Group240_120 s36Group360_107
theorem s36Group0_467 : treeBlock 0 467 s36Check = true := treeBlock_merge (start := 0) (left := 240) (right := 227) (check := s36Check) s36Group0_240 s36Group240_227
theorem s36Blocks : treeBlock 0 467 s36Check = true := s36Group0_467
theorem s36Known : Known s36Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s35Stock) s34Stock) s33Stock) s32Stock) s30Stock) s29Stock) s28Stock) s27Stock) s26Stock) s2Stock) s22Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s36Stock : Lower s36Mask s36StockWords s36Goal 10 := by
  apply lowerDag _ _ _ _ s36Autos _ _ _ s36Known _ s36Roots s36Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s36Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s37Mask : Nat := 0xf0f0f0f00f0f0f0f
abbrev s37Goal : Nat := sGoal &&& s37Mask
abbrev s37StockWords : List Nat := [0xa0a0a0a00a0a0a0a, 0xc0c0c0c00c0c0c0c, 0xf0f0f0f000000000, 0xf000f0000f000f00, 0xf0f000000f0f0000]
def s37Fact : Nat × List Nat × Nat × Nat := (s37Mask, s37StockWords, 10, s37Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s37Stock : Lower s37Mask s37StockWords s37Goal 10 := dagShiftLower (width := 64) pm6 s36Stock (by decide +kernel)
def s38Blob269570 : Nat := (cbits [0xd46235190cc6233, 0x460331a0d864361a, 0x437188dc6036180d, 0x6190d468331a0dc6, 0x180dc623])
def s38Blob269697 : Nat := 0xefbcdf73becf
def s38Blob269739 : Nat := 0x182824124205
def s38Mask : Nat := 0xff000000000000
abbrev s38Goal : Nat := sGoal &&& s38Mask
abbrev s38StockWords : List Nat := [0xaa000000000000, 0xcc000000000000, 0xf0000000000000]
def s38Fact : Nat × List Nat × Nat × Nat := (s38Mask, s38StockWords, 4, s38Goal)
def s38Cuts : List (Nat × List Nat × Nat × Nat) := []
def s38Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[51, 53, 54, 51, 53, 54, 51, 53, 54, 51, 53, 54, 49, 50, 52, 49, 50, 52, 49, 50, 52, 49, 50, 52], rfl⟩
def s38Witnesses := unpackWitnesses s38StockWords [26162, 288305, 551473]
def s38Index (i : Nat) : Nat := unpack 0x9 2 i
def s38Codes (i : Nat) : Nat := unpack 0x7 15 i
def s38Forest (i : Nat) : Nat := unpack 0xe 14 i
def s38Links := pageLinks s38Index s38Codes 1 13 1 2
def s38Data (i : Nat) : Nat × Nat :=
  let e := s38Forest i
  (e &&& 1, e >>> 1)
def s38Sample : Nat × Nat := (s38Blob269570, 16)
def s38Tags := dagTraceTags s38Mask 16 (dagTagBases s38StockWords s38Blob269697 s38Blob269739 16) 3 s38Data
def s38States := dagTrace s38Mask s38StockWords 3 s38Data
def s38MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s38Moves := dagMoves s38MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s38Autos : DagMovesOK s38Mask s38Goal 64 s38Moves := dagMovesOfCheck (by decide +kernel)
def s38Check := dagCheckNode s38Mask s38Goal s38Chart (dagKnownCloses s38Goal s38Cuts) 1 s38States s38Moves s38Links s38Sample s38Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s38Roots : dagCheckRoots s38Mask s38Goal s38Chart (dagKnownCloses s38Goal s38Cuts) s38Witnesses (dagRef 1 s38States s38Moves s38Links 0) s38StockWords 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s38Block0 : treeBlock 0 1 s38Check = true := by decide +kernel
theorem s38Blocks : treeBlock 0 1 s38Check = true := s38Block0
theorem s38Known : Known s38Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s38Stock : Lower s38Mask s38StockWords s38Goal 4 := by
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
def pm31 : List (List (Nat × Nat) × List (Nat × Nat)) := [st23]
def s39Mask : Nat := 0xf0f000000000000
abbrev s39Goal : Nat := sGoal &&& s39Mask
abbrev s39StockWords : List Nat := [0xa0a000000000000, 0xc0c000000000000, 0xf00000000000000]
def s39Fact : Nat × List Nat × Nat × Nat := (s39Mask, s39StockWords, 4, s39Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s39Stock : Lower s39Mask s39StockWords s39Goal 4 := dagShiftLower (width := 64) pm31 s38Stock (by decide +kernel)
def s40Blob273268 : Nat := (cbits [0x8cc140b0482c060b, 0x87039188e4643318, 0x40b0082c703a190e, 0x9180cc06330402c0, 0x80e8143a180e4123, 0x2c703b190ec623b1, 0x7033010cc0233000, 0x3a190e41039008e4, 0x18ec623a040e804, 0x82c603b050ec123b, 0xc00331c02c640b18, 0x639000e41433048c, 0xa018e8003a050e40, 0x40ec043b008ec123, 0xe80439040cc600b0, 0x3b008])
def s40Blob273612 : Nat := (cbits [0xcfdf8fff8ffcfe7f, 0xf3f9f7f8fff8ff9f, 0xfbfe3f1dff8fff8f, 0xf7ff8ff])
def s40Blob273719 : Nat := (cbits [0x4aa0e489c244522b, 0x52518896894c448a, 0x23d43f029268c944, 0x800789])
def s40Mask : Nat := 0xf0f000000000f0f
abbrev s40Goal : Nat := sGoal &&& s40Mask
abbrev s40StockWords : List Nat := [0xa0a000000000a0a, 0xc0c000000000c0c, 0xf00000000000f00, 0xf0f000000000000]
def s40Fact : Nat × List Nat × Nat × Nat := (s40Mask, s40StockWords, 7, s40Goal)
def s40Cuts : List (Nat × List Nat × Nat × Nat) := [s39Fact]
def s40Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[11, 51, 57, 58, 11, 51, 57, 58, 11, 51, 57, 58, 3, 9, 10, 49, 50, 56, 3, 9, 10, 49, 50, 56], rfl⟩
def s40Witnesses := unpackWitnesses s40StockWords [5642, 267785, 529923, 812547]
def s40Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0x4028050088c18001, 0xd85b0360644a15, 0x802e8dd03817]) else 0x9c730622421) 11 (i % 16)
def s40Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0x820024040100000f, 0xc940361a01305007, 0xa823141001396807, 0x78d18fc28c6d1062, 0x3b2188584c40a032, 0x7031]) else (if j < 2 then (cbits [0x111880086282492c, 0x82464c0c31c03496, 0x9663249313058cc, 0xa312040c901c63, 0x8071890180181863, 0xf31]) else (cbits [0x58c68200180e00c, 0xc5262226312b193, 0x8866200318a060c9, 0x18d25]))) 21 (i % 16)
def s40Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0x60862820040401e0, 0xc638600784012149, 0x48a19318648718c1, 0xe00984c60c19918c, 0x31838c48]) else 0x12581318c404e1) 18 (i % 16)
def s40Links := pageLinks s40Index s40Codes 5 13 5 6
def s40Data (i : Nat) : Nat × Nat :=
  let e := s40Forest i
  (e &&& 31, e >>> 5)
def s40Sample : Nat × Nat := (s40Blob273268, 55)
def s40Tags := dagTraceTags s40Mask 55 (dagTagBases s40StockWords s40Blob273612 s40Blob273719 55) 6 s40Data
def s40States := dagTrace s40Mask s40StockWords 6 s40Data
def s40MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm14, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 3, 2, 1, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 3, 2, 1, 4, 5] 0 i.val))), (pm1, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val))), (pm17, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [3, 0, 2, 1, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 3, 2, 0, 4, 5] 0 i.val))), (pm19, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 3, 2, 0, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [3, 0, 2, 1, 4, 5] 0 i.val)))]
def s40Moves := dagMoves s40MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s40Autos : DagMovesOK s40Mask s40Goal 64 s40Moves := dagMovesOfCheck (by decide +kernel)
def s40Check := dagCheckNode s40Mask s40Goal s40Chart (dagKnownCloses s40Goal s40Cuts) 19 s40States s40Moves s40Links s40Sample s40Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s40Roots : dagCheckRoots s40Mask s40Goal s40Chart (dagKnownCloses s40Goal s40Cuts) s40Witnesses (dagRef 19 s40States s40Moves s40Links 0) s40StockWords 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s40Block0 : treeBlock 0 19 s40Check = true := by decide +kernel
theorem s40Blocks : treeBlock 0 19 s40Check = true := s40Block0
theorem s40Known : Known s40Cuts := (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s39Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s40Stock : Lower s40Mask s40StockWords s40Goal 7 := by
  apply lowerDag _ _ _ _ s40Autos _ _ _ s40Known _ s40Roots s40Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s40Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl <;> decide +kernel
def pm32 : List (List (Nat × Nat) × List (Nat × Nat)) := [st13, st12]
def s41Mask : Nat := 0x3333000000000000
abbrev s41Goal : Nat := sGoal &&& s41Mask
abbrev s41StockWords : List Nat := [0x2222000000000000, 0x3030000000000000, 0x3300000000000000]
def s41Fact : Nat × List Nat × Nat × Nat := (s41Mask, s41StockWords, 4, s41Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s41Stock : Lower s41Mask s41StockWords s41Goal 4 := dagShiftLower (width := 64) pm32 s38Stock (by decide +kernel)
def pm33 : List (List (Nat × Nat) × List (Nat × Nat)) := [st03, st01, st12]
def s42Mask : Nat := 0x5555000000000000
abbrev s42Goal : Nat := sGoal &&& s42Mask
abbrev s42StockWords : List Nat := [0x4444000000000000, 0x5050000000000000, 0x5500000000000000]
def s42Fact : Nat × List Nat × Nat × Nat := (s42Mask, s42StockWords, 4, s42Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s42Stock : Lower s42Mask s42StockWords s42Goal 4 := dagShiftLower (width := 64) pm33 s38Stock (by decide +kernel)
def pm34 : List (List (Nat × Nat) × List (Nat × Nat)) := [st12, st13]
def pm35 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01, st23]
def pm36 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01, st02, st03]
def pm37 : List (List (Nat × Nat) × List (Nat × Nat)) := [st02, st01, st13]
def pm38 : List (List (Nat × Nat) × List (Nat × Nat)) := [st02, st13]
def s43Blob278613 : Nat := (cbits [0xd46235190cc6233, 0x462391a0d864361a, 0x83c1c0e8643a1c0e, 0x6180d460331c0f06, 0xa0dc6437188dc603, 0xec623b180e860391, 0x623d180f0703b190, 0x3e190f8703d1a0f4, 0x1c0cc68331c0f868, 0xd862361c0d46435, 0x86839190e460371c, 0x23c180ec683a188e, 0xf180f8603d190f06, 0xc0fc683f190fc623, 0xf8643d1a0ec70371, 0x603f188])
def s43Blob278958 : Nat := (cbits [0x99dfd273c777b0cf, 0xfb0f37f1ce7c3de9, 0xff81f81dff07cfe0, 0xf7ffc07])
def s43Blob279065 : Nat := (cbits [0x8920448401108045, 0x810a084410841080, 0x8801500240501480, 0xc00154])
def s43Mask : Nat := 0xffff000000000000
abbrev s43Goal : Nat := sGoal &&& s43Mask
abbrev s43StockWords : List Nat := [0xaaaa000000000000, 0xcccc000000000000, 0xf0f0000000000000, 0xff00000000000000]
def s43Fact : Nat × List Nat × Nat × Nat := (s43Mask, s43StockWords, 7, s43Goal)
def s43Cuts : List (Nat × List Nat × Nat × Nat) := [s38Fact, s39Fact, s41Fact, s42Fact]
def s43Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[51, 53, 54, 57, 58, 60, 51, 53, 54, 57, 58, 60, 49, 50, 52, 56, 49, 50, 52, 56, 49, 50, 52, 56], rfl⟩
def s43Witnesses := unpackWitnesses s43StockWords [26162, 288305, 551473, 815665]
def s43Index (i : Nat) : Nat := unpack 0x4c242e4702cc3401 9 i
def s43Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0xf06013020080000f, 0x1f423143602b2601, 0x62b626209632b863, 0x4620043147292ca6, 0x180360802a3492c2]) else 0xa01c583364832a) 20 (i % 16)
def s43Forest (i : Nat) : Nat := unpack (cbits [0x9918a200410078, 0xe50154]) 16 i
def s43Links := pageLinks s43Index s43Codes 4 13 3 5
def s43Data (i : Nat) : Nat × Nat :=
  let e := s43Forest i
  (e &&& 7, e >>> 3)
def s43Sample : Nat × Nat := (s43Blob278613, 55)
def s43Tags := dagTraceTags s43Mask 55 (dagTagBases s43StockWords s43Blob278958 s43Blob279065 55) 6 s43Data
def s43States := dagTrace s43Mask s43StockWords 6 s43Data
def s43MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm31, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val))), (pm0, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 2, 1, 3, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 2, 1, 3, 4, 5] 0 i.val))), (pm34, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 3, 1, 2, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 2, 3, 1, 4, 5] 0 i.val))), (pm1, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val))), (pm35, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 3, 2, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 3, 2, 4, 5] 0 i.val))), (pm2, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [2, 0, 1, 3, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 2, 0, 3, 4, 5] 0 i.val))), (pm36, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [3, 0, 1, 2, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 2, 3, 0, 4, 5] 0 i.val))), (pm3, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 2, 0, 3, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [2, 0, 1, 3, 4, 5] 0 i.val))), (pm37, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 3, 0, 2, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [2, 0, 3, 1, 4, 5] 0 i.val))), (pm38, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [2, 3, 0, 1, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [2, 3, 0, 1, 4, 5] 0 i.val)))]
def s43Moves := dagMoves s43MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s43Autos : DagMovesOK s43Mask s43Goal 64 s43Moves := dagMovesOfCheck (by decide +kernel)
def s43Check := dagCheckNode s43Mask s43Goal s43Chart (dagKnownCloses s43Goal s43Cuts) 6 s43States s43Moves s43Links s43Sample s43Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s43Roots : dagCheckRoots s43Mask s43Goal s43Chart (dagKnownCloses s43Goal s43Cuts) s43Witnesses (dagRef 6 s43States s43Moves s43Links 0) s43StockWords 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s43Block0 : treeBlock 0 6 s43Check = true := by decide +kernel
theorem s43Blocks : treeBlock 0 6 s43Check = true := s43Block0
theorem s43Known : Known s43Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s42Stock) s41Stock) s39Stock) s38Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s43Stock : Lower s43Mask s43StockWords s43Goal 7 := by
  apply lowerDag _ _ _ _ s43Autos _ _ _ s43Known _ s43Roots s43Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s43Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel
def s44Mask : Nat := 0xffff
abbrev s44Goal : Nat := sGoal &&& s44Mask
abbrev s44StockWords : List Nat := [0xaaaa, 0xcccc, 0xf0f0, 0xff00]
def s44Fact : Nat × List Nat × Nat × Nat := (s44Mask, s44StockWords, 5, s44Goal)
def s44Witnesses := unpackWitnesses s44StockWords [2564, 265220, 526849, 792067]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s44Stock : Lower s44Mask s44StockWords s44Goal 5 := by
  apply essentialLift (witnesses := s44Witnesses) (cut := s0Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s0StockWords) (by decide +kernel)
  · exact s0Stock
  · decide +kernel
def s45Mask : Nat := 0xff0000000000ff
abbrev s45Goal : Nat := sGoal &&& s45Mask
abbrev s45StockWords : List Nat := [0xaa0000000000aa, 0xcc0000000000cc, 0xf00000000000f0, 0xff000000000000]
def s45Fact : Nat × List Nat × Nat × Nat := (s45Mask, s45StockWords, 5, s45Goal)
def s45Witnesses := unpackWitnesses s45StockWords [2564, 265220, 526849, 812547]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s45Stock : Lower s45Mask s45StockWords s45Goal 5 := by
  apply essentialLift (witnesses := s45Witnesses) (cut := s38Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s38StockWords) (by decide +kernel)
  · exact s38Stock
  · decide +kernel
def s46Mask : Nat := 0x3333000000003333
abbrev s46Goal : Nat := sGoal &&& s46Mask
abbrev s46StockWords : List Nat := [0x2222000000002222, 0x3030000000003030, 0x3300000000003300, 0x3333000000000000]
def s46Fact : Nat × List Nat × Nat × Nat := (s46Mask, s46StockWords, 5, s46Goal)
def s46Witnesses := unpackWitnesses s46StockWords [2564, 264705, 553521, 815625]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s46Stock : Lower s46Mask s46StockWords s46Goal 5 := by
  apply essentialLift (witnesses := s46Witnesses) (cut := s41Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s41StockWords) (by decide +kernel)
  · exact s41Stock
  · decide +kernel
def s47Mask : Nat := 0x5555000000005555
abbrev s47Goal : Nat := sGoal &&& s47Mask
abbrev s47StockWords : List Nat := [0x4444000000004444, 0x5050000000005050, 0x5500000000005500, 0x5555000000000000]
def s47Fact : Nat × List Nat × Nat × Nat := (s47Mask, s47StockWords, 5, s47Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s47Stock : Lower s47Mask s47StockWords s47Goal 5 := dagShiftLower (width := 64) pm1 s46Stock (by decide +kernel)
def s48Blob292987 : Nat := (cbits [0x82c060b0181c0205, 0x46235188cc120d04, 0x207048140605188e, 0xf0183c020d0082c0, 0x48e46237018cc120, 0x1c6205188f4623b0, 0x2330083c060d048, 0x3b008e40637008d4, 0x188fc123d048ec06, 0x8cc620d1882c6207, 0x40237048d4063504, 0x63f008f4023b018e, 0xd048dc620f048fc0, 0x8fc063])
def s48Blob293292 : Nat := (cbits [0x7753bd4bb5a5ec2e, 0xf8ce789cfe75c6f9, 0xeff8ff0f80e0df86])
def s48Blob293388 : Nat := (cbits [0x44901440a106, 0x6022421800000000, 0x1007801d00e02828])
def s48Mask : Nat := 0xaaaa00000000aaaa
abbrev s48Goal : Nat := sGoal &&& s48Mask
abbrev s48StockWords : List Nat := [0x8888000000008888, 0xa0a000000000a0a0, 0xaa0000000000aa00, 0xaaaa000000000000]
def s48Fact : Nat × List Nat × Nat × Nat := (s48Mask, s48StockWords, 5, s48Goal)
def s48Cuts : List (Nat × List Nat × Nat × Nat) := []
def s48Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[5, 11, 51, 57, 5, 11, 51, 57, 5, 11, 51, 57, 3, 9, 49, 3, 9, 49, 3, 9, 49, 3, 9, 49], rfl⟩
def s48Witnesses := unpackWitnesses s48StockWords [5641, 264705, 529923, 812547]
def s48Index (i : Nat) : Nat := unpack 0x9 2 i
def s48Codes (i : Nat) : Nat := unpack 0xf 15 i
def s48Forest (i : Nat) : Nat := unpack 0x1e 14 i
def s48Links := pageLinks s48Index s48Codes 1 13 1 2
def s48Data (i : Nat) : Nat × Nat :=
  let e := s48Forest i
  (e &&& 1, e >>> 1)
def s48Sample : Nat × Nat := (s48Blob292987, 48)
def s48Tags := dagTraceTags s48Mask 48 (dagTagBases s48StockWords s48Blob293292 s48Blob293388 48) 4 s48Data
def s48States := dagTrace s48Mask s48StockWords 4 s48Data
def s48MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s48Moves := dagMoves s48MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s48Autos : DagMovesOK s48Mask s48Goal 64 s48Moves := dagMovesOfCheck (by decide +kernel)
def s48Check := dagCheckNode s48Mask s48Goal s48Chart (dagKnownCloses s48Goal s48Cuts) 1 s48States s48Moves s48Links s48Sample s48Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s48Roots : dagCheckRoots s48Mask s48Goal s48Chart (dagKnownCloses s48Goal s48Cuts) s48Witnesses (dagRef 1 s48States s48Moves s48Links 0) s48StockWords 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s48Block0 : treeBlock 0 1 s48Check = true := by decide +kernel
theorem s48Blocks : treeBlock 0 1 s48Check = true := s48Block0
theorem s48Known : Known s48Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s48Stock : Lower s48Mask s48StockWords s48Goal 5 := by
  apply lowerDag _ _ _ _ s48Autos _ _ _ s48Known _ s48Roots s48Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s48Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def s49Mask : Nat := 0xcccc00000000cccc
abbrev s49Goal : Nat := sGoal &&& s49Mask
abbrev s49StockWords : List Nat := [0x8888000000008888, 0xc0c000000000c0c0, 0xcc0000000000cc00, 0xcccc000000000000]
def s49Fact : Nat × List Nat × Nat × Nat := (s49Mask, s49StockWords, 5, s49Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s49Stock : Lower s49Mask s49StockWords s49Goal 5 := dagShiftLower (width := 64) pm1 s48Stock (by decide +kernel)
def s50Blob305966 : Nat := (cbits [0x180406020140205, 0xc120b0182c060702, 0x40e06034120d0502, 0x5190cc6233060381, 0xa0d864361a0d4623, 0xe8643a1c0e462391, 0x51c0f0683c1c0, 0x606014120501814, 0x601814060181800, 0x82c08070101c0207, 0x4020d0402c040b00, 0x80e01038100d0203, 0xf0483c060f040380, 0x80cc06330603c140, 0xdc6237180d860351, 0x6039048e46837190, 0x3b188ec603a050e8, 0x180f0183c1c0ec64, 0xf8703d1a0f4623d, 0x404051c0f8683e19, 0x2061a01462050401, 0x71a0186406040180, 0x601c14070481c000, 0x34000d0602c000b0, 0x60e00038140d018, 0xf0103c020f04838, 0x10cc02330403c08])
def s50Blob306532 : Nat := (cbits [0x39f7f1ff0f0cf3f3, 0xf0333cfcfc7fc3c7, 0xff8ffc383e7bfe3f, 0xc07cffc7ffc3cf1f, 0xfc0fe03ff3ffff, 0x3ffc003fff80fff8, 0xffff000000fff000, 0xc000003f])
def s50Blob306718 : Nat := (cbits [0x891304926045171, 0x621124b447208501, 0x8961104812215212, 0x4040848488428a0a, 0xcca80fc0100a2212, 0x224b88a46280e920, 0xbd7e000000fff000, 0x333f])
def s50Mask : Nat := 0xffff00000000ffff
abbrev s50Goal : Nat := sGoal &&& s50Mask
abbrev s50StockWords : List Nat := [0xaaaa00000000aaaa, 0xcccc00000000cccc, 0xf0f000000000f0f0, 0xff0000000000ff00, 0xffff000000000000]
def s50Fact : Nat × List Nat × Nat × Nat := (s50Mask, s50StockWords, 10, s50Goal)
def s50Cuts : List (Nat × List Nat × Nat × Nat) := [s40Fact, s1Fact, s43Fact, s44Fact, s45Fact, s46Fact, s47Fact, s48Fact, s49Fact, s0Fact, s38Fact, s41Fact, s42Fact]
def s50Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[5, 6, 11, 51, 57, 58, 60, 5, 6, 11, 51, 57, 3, 9, 10, 12, 49, 50, 52, 56, 3, 9, 10, 12], rfl⟩
def s50Witnesses := unpackWitnesses s50StockWords [2564, 265220, 526849, 792067, 1074691]
def s50Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 11 then (if j < 5 then (if j < 2 then (if j < 1 then (cbits [0x80208bc0180001, 0xa001400213842, 0x5000a00140028005, 0xb4016802828]) else (cbits [0xc4016902d005a0, 0xc00c4a1880310062, 0x6c00d801b0036006, 0xe401c803618])) else (if j < 3 then (cbits [0x1120023843970720, 0x6212c02580491090, 0x9eb134426804d009, 0x16802d005a00]) else (if j < 4 then (cbits [0x16802d005a00b40, 0x2018402d1c5a00b4, 0xc27184030806100c, 0x1a0234006800]) else (cbits [0x1a8034846900d20, 0x201c4038806a38d4, 0xe4b1c8038847100e, 0x1fc03f807d10])))) else (if j < 8 then (if j < 6 then (cbits [0x2235045888150fe2, 0xf325d04b8097012a, 0x6c02d805b00b2213, 0x2e405b0cb601]) else (if j < 7 then (cbits [0x2f005c8cb901720, 0xe22fc05f80bc1978, 0x8a031406090c1017, 0x31506280c501]) else (cbits [0x33406680cd019a0, 0x80334e6680cd019a, 0xa8035006a00d401a, 0x36006c00d421]))) else (if j < 9 then (cbits [0x37806f00d831b00, 0x237846f00de01bc, 0xda038967100e201c, 0x3dc076a8ed01]) else (if j < 10 then (cbits [0x443867ec4f829ee1, 0xa145408a81150222, 0x4a0480a8ba5160a2, 0x494092812502]) else (cbits [0x14982928525024a0, 0x434a809485280a4e, 0x5c04b8097012d0a5, 0x4c8098852e1a]))))) else (if j < 16 then (if j < 13 then (if j < 12 then (cbits [0x4f0c99293202640, 0x415080a101420284, 0x8845100a18543028, 0x520aa4014802]) else (cbits [0x35448a8814d229a0, 0x5600ac015802aa, 0xc8958c2b1055852b, 0x5c42b70d6d0a])) else (if j < 14 then (cbits [0x6442c61576b2e44, 0x6064c0c981920b24, 0x3016600c99593032, 0x66c8cd05990b]) else (if j < 15 then (cbits [0x467c0cf819f033e0, 0xa168c4d181a3033e, 0x5426a80d501a6234, 0x6dc2d6a9ac0b]) else (cbits [0x1714ee205b95b701, 0x4075a8e6a5cd0398, 0xdc27b42f50dea03d, 0x7c02f801f003])))) else (if j < 19 then (if j < 17 then (cbits [0x7c86f901f10be20, 0x27dc2fa89f503ea, 0x428080fd9dfa0bf, 0x82a3021a0404]) else (if j < 18 then (cbits [0x88010e8e1d04362, 0x2189c5101e200440, 0x5628ac115062a045, 0x8b4116822d04]) else (cbits [0x8cc51982320c5a5, 0x418d891a8635046a, 0x7c38f431d8a3b047, 0x928124864144]))) else (if j < 20 then (cbits [0x19489278e4a2c940, 0x809a4734826714ad, 0xe609b0f36026c04d, 0x9d41398a7304]) else (if j < 21 then (cbits [0x9f433e827544ea0, 0x8da247419a7e2cfc, 0x5e2a917510a994d1, 0xae9958a6b105]) else (cbits [0x1ba477292cfb58c9, 0x42bc817696ed05d8, 0x17bb2f41de])))))) 15 (i % 16)
def s50Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 24 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then (cbits [0xb80240100400001f, 0xf9a001324401e2, 0x144cc06687009cf6, 0xf7b0c7e5718ac023, 0x47310666333c3864, 0x541266a724b1]) else (if j < 2 then (cbits [0x2003c02004ab2c38, 0x1382201f0300260, 0x150806280e00cc16, 0x61d8c9c3518f8563, 0x5049609662011066, 0x1598702924cc]) else (cbits [0x30c7805015006620, 0x49601062a01cc400, 0xe02de880530e009, 0x80718c80d18a00c0, 0x1218a020c3803d25, 0x51264098c94]))) else (if j < 4 then (cbits [0xc00a81700f02ac38, 0x7a203492c064c400, 0x380792580e98801b, 0x610803e0300483ec, 0x19013c2401f08c02, 0xc62b0e80ce]) else (if j < 5 then (cbits [0xe8ccc1919382431f, 0x49984e92c090c400, 0xc0886381530e029, 0x81330e0254960440, 0x26496050c3809525, 0xb00541430e0]) else (cbits [0x38c642e01f05a032, 0x31905e62a03463a0, 0x380c92581898f830, 0x8040034347a2066c, 0x3749906c92c0bc62, 0xe58701c24f8])))) else (if j < 9 then (if j < 7 then (cbits [0xe8ca83c18a074f44, 0x4960606200f867c1, 0x2810de8820b0f840, 0x4228c504231a07e3, 0x3131007c33211865, 0x12187023a4b0]) else (if j < 8 then (cbits [0x48c6c4a31a092c3d, 0x19983432703c63e0, 0x270c8c421218801e, 0x62624b0473198806, 0x2549609ec3813926, 0x9925826b0e0]) else (cbits [0x80c7c0a18d89ac38, 0x31003e3330546560, 0x330e4c5619988427, 0x828b0e04c4960906, 0x2918a09ac380a125, 0x14c6521f0c94]))) else (if j < 10 then (cbits [0x718804919e882331, 0x1920aa92c150c522, 0x3302c636250cf042, 0x61a18842a3100363, 0x4f4960866330e8c5, 0x16003428b0e0]) else (if j < 11 then (cbits [0x200c8610150ba01e, 0x18f0d231a19c07c3, 0x3e1f06643b0ca86e, 0x64318862b3101003, 0x8931f91063321cc5, 0x2358704524b0]) else (cbits [0xc80a8907a211ec3f, 0x61c0b692c168c542, 0x3817d2582f00a85c, 0x1160c50620090c0c, 0x2d3100ca02a18d87, 0x8b8c403324b2]))))) else (if j < 18 then (if j < 15 then (if j < 13 then (cbits [0x598806a1950d092c, 0x150dac381b12583, 0x321c0654378c5062, 0x39a4b07231f0e26, 0x5e0090eaf441d187, 0x1dc64b178c50]) else (if j < 14 then (cbits [0xd30e07949f0f0932, 0x1950fa31e1ede883, 0x1e1fd2591818807e, 0x9189880821951023, 0x8561e908c3820d25, 0x1bcc50359890]) else (cbits [0xd8c987018e0b4018, 0x19f0cc33217c6542, 0x321ccc5436189868, 0x11924b08331f0fe6, 0x5c193118f4422d87, 0x18c66c300ca8]))) else (if j < 16 then (cbits [0xd18d8743150da626, 0x61c46692c210c7c3, 0x2a214690473d108b, 0x11a24b07b31b0ea6, 0x9200411cf4423187, 0x2940564c80a8]) else (if j < 17 then (cbits [0x48c50ac01f14e032, 0x18f18631d2c46383, 0x2031c656630c7ec3, 0x6424b2c7315cd26, 0xcf7a219ac3f32d87, 0x25d258498c70]) else (cbits [0x10c5094007130c38, 0x31412c92c254c401, 0x101a80104b18a095, 0x9500048a00089340, 0xa261c14292c9a862, 0x291e8851b0fc])))) else (if j < 21 then (if j < 19 then (cbits [0xea4b09c310136008, 0x18e13ec382792664, 0x1c2780204e8c709c, 0x45400a0a618e13e3, 0xa931015692c2a805, 0x2bc0545680a0]) else (if j < 20 then (cbits [0x98020ae31016092c, 0x18a14c01f26803c4, 0x202e46665b8c9cb2, 0x6024ccbe4961766, 0x2218a16601230987, 0x2d0c404d8c78]) else (cbits [0xc30f8b661c16a92c, 0x31012a3142e987a5, 0x142f58705e24b0b4, 0x85a98809d19512c3, 0x9e00f17ec382f125, 0x2e06626080a0]))) else (if j < 22 then (cbits [0xb18809f19517433d, 0x1517ec382f52585, 0x143158706224b0a0, 0x580cf8ab19912e3, 0xc43149766281b0c4, 0x9b12596218a8]) else (if j < 23 then (cbits [0xe24d0ca7a2192c38, 0x19b1303142f52685, 0x292f8c50369880a2, 0x136a4b2c531518a6, 0xbf49a198f4432587, 0x3380685180a8]) else (cbits [0x20cd8c100818031c, 0x7a2194c38308c505, 0xd2c4018370020cc, 0x463003ec30071860, 0xd801f9ae03334405, 0xb44655370c50])))))) else (if j < 36 then (if j < 30 then (if j < 27 then (if j < 25 then (cbits [0xc9882d819fdae333, 0x3199c6632378c546, 0x2c3acc7e7418f8e6, 0x87930fcf061c1da9, 0xd20124e00083d5e8, 0x35587e6a30e0]) else (if j < 26 then (cbits [0x98cc0d34961acf44, 0x4961643183680546, 0x24375e886e30e0db, 0x5b1890b53121686, 0xe161c1c093c37d26, 0x1c4010713d10]) else (cbits [0x2a4b0e43154e2314, 0x61cef4a2dc0187, 0x2a9c8628390020b8, 0x25c8030ea4961d26, 0x7318a17400c3b1e9, 0x3106325d8c60]))) else (if j < 28 then (cbits [0xda4b27331058831a, 0x61c1d493e3952646, 0x242f0c4877bd10ee, 0x25f0c607418a17a6, 0xd419b58a31a31463, 0xb50c6d3a1880]) else (if j < 29 then (cbits [0x730e0e149b1b892c, 0x617e6243c5e887, 0x2a3cc06c6a80a8c0, 0x27398f6f319b5aa3, 0x7518a1e80283b0c9, 0x35866c610c60]) else (cbits [0xea4b2d631b4ea620, 0x7a21dec3838926c6, 0x1231c01e3b0020f1, 0x87c00fcf70199a20, 0xf9192d0e3158d462, 0x3786527d8c9c])))) else (if j < 33 then (if j < 31 then (cbits [0x124b10019f9fc333, 0x49f20c9334152648, 0x3f4258708424fd07, 0x83b80210d7a2216c, 0xd31941f4c3834803, 0x3f58947e30f8]) else (if j < 32 then (cbits [0xb1881011941fe328, 0x4208f4440d8711, 0x83f06631b8c5078, 0x87e8cc63818a0f20, 0x393101a831e1e862, 0x384c6a7d18c6]) else (cbits [0xa80490a7a2206c38, 0x18f0f6314430c686, 0x38388c6b1d1880d6, 0x48780210a7a2208c, 0x1400fa2201e29c03, 0x4780568a80a9]))) else (if j < 34 then (cbits [0xb8c7c7c18a23e03e, 0x310c766203dc6566, 0x2c498c7f7f18ae88, 0x993d113061f2589, 0x7d00422092c8f0c4, 0x44de888924b0]) else (if j < 35 then (cbits [0xf8c763d18a0fc008, 0x61f23492c45867f7, 0x4845c6508ebd111b, 0x88c0ca11861e232f, 0x2000e23233d47006, 0x4900549100a1]) else (cbits [0x98812549647c620, 0x1942466208fc6289, 0x3645806c93807121, 0x9430f12b7a42526, 0x18014254f4845c05, 0x46406c940071]))))) else (if j < 42 then (if j < 39 then (if j < 37 then (cbits [0x58c991018a254636, 0x31024a33e4486545, 0x444b587d2024b07f, 0x88d80a92e31a25ef, 0x2b31ec826204c466, 0x47003c96a4b1]) else (if j < 38 then (cbits [0x98ca92e310484314, 0x61c48692c47466c8, 0x1e2b00349a00212f, 0x69d00a93900fa6c0, 0x8018a23e0324fc05, 0x3e06566c0c7c]) else (cbits [0x18ae89310c88620, 0x61c28092cc98c678, 0x2c914c40a2b0f544, 0x9ba4b08100426a9, 0x4618a1040084e187, 0xca4667808c76]))) else (if j < 40 then (cbits [0xeb0f53c61c27692c, 0x18a65433d4f80689, 0x324dc654580c9935, 0x123a4b08331024a3, 0x4331a284c3d50587, 0x4f066c9c0ca9]) else (if j < 41 then (cbits [0xb0e248496108620, 0x19a10a3144f4054a, 0x2ccacc7b24988146, 0x1250c513e00f2849, 0x8a18a89631450cc4, 0x3b463e640c6c]) else (cbits [0x5988140199a58327, 0x319e58627a28c432, 0x38529266a424b340, 0xe4598844c31029ac, 0x413199dc62b324c4, 0xa2d25b2624b1])))) else (if j < 45 then (if j < 43 then (cbits [0x6a4b14961c682933, 0x19289c3149358702, 0x3d4b4662a58ca525, 0x39298964e3102843, 0x4231ee5a631d2cc5, 0x4b8648a624b3]) else (if j < 44 then (cbits [0x618844f31028633c, 0x3199de62b328c4e4, 0x33a3125b27a4b12f, 0xa280c514961c65e9, 0xf018f99631b23462, 0x510666848cac]) else (cbits [0x498ae8d310ca0620, 0x61c29092cd10c678, 0x27238c422898814f, 0x88518dcf13159986, 0xa49bd1c92d94525, 0x148010a4b0e3]))) else (if j < 47 then (if j < 46 then (cbits [0x9004ccd00791e009, 0x14a3e02542c03e7, 0x3d4c0062a900ad51, 0xf478c565218a28a0, 0x51194e3e325c2c63, 0xcc0663a90caf]) else (cbits [0xa98a54a31068a33d, 0x122b092c55cc56a, 0x2094c628a300f131, 0x2a98ca4f30092966, 0x540041e8010550c5, 0x950628860074])) else (if j < 48 then (cbits [0xa00a55661c61831d, 0x3100aa314d50652a, 0x15158628a624b255, 0x67a8c7ccf18d9203, 0x5631026433343465, 0xc34c57481886]) else (cbits [0x7b0e14d496664633, 0xa]))))))) 23 (i % 16)
def s50Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 11 then (if j < 5 then (if j < 2 then (if j < 1 then (cbits [0x120200400403e00, 0x1501401e0231000c, 0x540531001463c050, 0x201587005496014c, 0x40d18a034026027a, 0x496034c6]) else (cbits [0x6281200f8098700d, 0x1c04926412192848, 0x541700f05c04e026, 0x205d2581731005c0, 0x81d310074066027a, 0x61c07525])) else (if j < 3 then (cbits [0x6382200788462802, 0x96094c4021009884, 0x7028496085870254, 0xa809870214998858, 0xc2c0190b00542c18, 0x3150b007]) else (if j < 4 then (cbits [0x2582c31f0b0c642c, 0x8f809e882c61c0b1, 0x7c364990d9258361, 0x3809e883661c0d92, 0xc3c1950f06283c19, 0x1940fc67]) else (cbits [0xc684261f0f12583c, 0x8a114666027a20f0, 0x7045496114654451, 0x8c684a61e9158, 0x64c61c1352584c31, 0x61c13126])))) else (if j < 8 then (if j < 6 then (cbits [0x2660261c14525802, 0x9614cc525319494d, 0x3458004805870024, 0x6164c54590151640, 0x45e00f1618705949, 0x49617805]) else (if j < 7 then (cbits [0x24620151618705e, 0x151940645861c188, 0x586801f161258650, 0x1a86546a18d1612, 0xc5861c1a92586a31, 0x18a1bc63]) else (cbits [0xc7c6f3191bc6546f, 0xa21bd8706f4961bc, 0x64771929dc654587, 0x21dd8707749f1dd2, 0x47d18f1f4664587a, 0x4961f465]))) else (if j < 9 then (cbits [0x6548118f20467c58, 0x1ea0587081496204, 0x6658315960c42586, 0xc22d2585831f960c, 0x88e61c161e888b61, 0x61f961e8]) else (if j < 10 then (cbits [0x1092007805e8858, 0x1025001c9418e24c, 0x709349624d258943, 0x426c0209a0152498, 0x69b49626cc409b00, 0x61c26d26]) else (cbits [0x8709a4962680229a, 0x15a49e889a61fa69, 0x50a8019248638a60, 0x62a0054a83102a40, 0xae0142b407c9249, 0x152b4c4]))))) else (if j < 16 then (if j < 13 then (if j < 12 then (cbits [0x628b218e249258ad, 0x962ccc40b30092cc, 0x7cb8193ac9870b34, 0x2c987aba199ac98, 0x8b261c2f1258bc31, 0x61c2fd25]) else (cbits [0x870b2014305266b2, 0x1c311258c418ea49, 0x5892195a4863e926, 0xc249e88c961c3252, 0x8ce61fa49e88cc61, 0x7a224806])) else (if j < 14 then (cbits [0x48d201534402601, 0x1fb49870d249634c, 0x7ed1019b45e88d26, 0x6368054da3103440, 0x4d17a2369870da49, 0x49837cc5]) else (if j < 15 then (cbits [0xe88df61c37d278df, 0x96390c54e4319345, 0x7cd17a539cc66d14, 0xfb45258e93153a4c, 0xee496345e92ec31, 0x7a23b987]) else (cbits [0x87ed17a23c5870d1, 0xa2344050f401b3cd, 0x7ef7019bdc03e017, 0x3bdd870fa192bdc0, 0x6f76253f187cfc19, 0x1943fc66])))) else (if j < 19 then (if j < 17 then (cbits [0x258f719440467ef7, 0x993dde890361c40d, 0x7ef749f3dd266f74, 0xfbdde890a61c3dd2, 0xe017a23dcc690c61, 0x443c04]) else (if j < 18 then (cbits [0x2591200f43d25910, 0x1543c03f0f7a2449, 0x791819445c67f160, 0xf459259167a445d8, 0x70f7a24580691c61, 0x1f43c05]) else (cbits [0x512031048403920, 0x964800552031048c, 0x792800e49cc7f0f4, 0x449de912a31b49d8, 0x92e61f4b52590f7a, 0x7a24b4c6]))) else (if j < 20 then (cbits [0xe890f19a4c587d0f, 0x964d401134019805, 0x71374964dc03d344, 0x64ec0553400fcd18, 0x93e61eced8713b49, 0x15cd006]) else (if j < 21 then (cbits [0x87b4161c50525934, 0x1ecd18713431a50d, 0x5948310004669466, 0x4d2d2674861c5252, 0x80161c5212594b19, 0x61c53d25]) else (cbits [0x5751014d4526601, 0x14d44c5353194d4c, 0x5951315d45871563, 0x61c0052])))))) 22 (i % 16)
def s50Links := pageLinks s50Index s50Codes 5 13 9 6
def s50Data (i : Nat) : Nat × Nat :=
  let e := s50Forest i
  (e &&& 511, e >>> 9)
def s50Sample : Nat × Nat := (s50Blob305966, 96)
def s50Tags := dagTraceTags s50Mask 96 (dagTagBases s50StockWords s50Blob306532 s50Blob306718 96) 9 s50Data
def s50States := dagTrace s50Mask s50StockWords 9 s50Data
def s50MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm1, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val)))]
def s50Moves := dagMoves s50MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s50Autos : DagMovesOK s50Mask s50Goal 64 s50Moves := dagMovesOfCheck (by decide +kernel)
def s50Check := dagCheckNode s50Mask s50Goal s50Chart (dagKnownCloses s50Goal s50Cuts) 346 s50States s50Moves s50Links s50Sample s50Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s50Roots : dagCheckRoots s50Mask s50Goal s50Chart (dagKnownCloses s50Goal s50Cuts) s50Witnesses (dagRef 346 s50States s50Moves s50Links 0) s50StockWords 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s50Block0 : treeBlock 0 24 s50Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s50Block24 : treeBlock 24 24 s50Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s50Block48 : treeBlock 48 24 s50Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s50Block72 : treeBlock 72 24 s50Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s50Block96 : treeBlock 96 24 s50Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s50Block120 : treeBlock 120 24 s50Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s50Block144 : treeBlock 144 24 s50Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s50Block168 : treeBlock 168 24 s50Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s50Block192 : treeBlock 192 24 s50Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s50Block216 : treeBlock 216 24 s50Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s50Block240 : treeBlock 240 24 s50Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s50Block264 : treeBlock 264 24 s50Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s50Block288 : treeBlock 288 24 s50Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s50Block312 : treeBlock 312 24 s50Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s50Block336 : treeBlock 336 10 s50Check = true := by decide +kernel
theorem s50Group24_48 : treeBlock 24 48 s50Check = true := treeBlock_merge (start := 24) (left := 24) (right := 24) (check := s50Check) s50Block24 s50Block48
theorem s50Group0_72 : treeBlock 0 72 s50Check = true := treeBlock_merge (start := 0) (left := 24) (right := 48) (check := s50Check) s50Block0 s50Group24_48
theorem s50Group72_48 : treeBlock 72 48 s50Check = true := treeBlock_merge (start := 72) (left := 24) (right := 24) (check := s50Check) s50Block72 s50Block96
theorem s50Group120_48 : treeBlock 120 48 s50Check = true := treeBlock_merge (start := 120) (left := 24) (right := 24) (check := s50Check) s50Block120 s50Block144
theorem s50Group72_96 : treeBlock 72 96 s50Check = true := treeBlock_merge (start := 72) (left := 48) (right := 48) (check := s50Check) s50Group72_48 s50Group120_48
theorem s50Group0_168 : treeBlock 0 168 s50Check = true := treeBlock_merge (start := 0) (left := 72) (right := 96) (check := s50Check) s50Group0_72 s50Group72_96
theorem s50Group168_48 : treeBlock 168 48 s50Check = true := treeBlock_merge (start := 168) (left := 24) (right := 24) (check := s50Check) s50Block168 s50Block192
theorem s50Group216_48 : treeBlock 216 48 s50Check = true := treeBlock_merge (start := 216) (left := 24) (right := 24) (check := s50Check) s50Block216 s50Block240
theorem s50Group168_96 : treeBlock 168 96 s50Check = true := treeBlock_merge (start := 168) (left := 48) (right := 48) (check := s50Check) s50Group168_48 s50Group216_48
theorem s50Group264_48 : treeBlock 264 48 s50Check = true := treeBlock_merge (start := 264) (left := 24) (right := 24) (check := s50Check) s50Block264 s50Block288
theorem s50Group312_34 : treeBlock 312 34 s50Check = true := treeBlock_merge (start := 312) (left := 24) (right := 10) (check := s50Check) s50Block312 s50Block336
theorem s50Group264_82 : treeBlock 264 82 s50Check = true := treeBlock_merge (start := 264) (left := 48) (right := 34) (check := s50Check) s50Group264_48 s50Group312_34
theorem s50Group168_178 : treeBlock 168 178 s50Check = true := treeBlock_merge (start := 168) (left := 96) (right := 82) (check := s50Check) s50Group168_96 s50Group264_82
theorem s50Group0_346 : treeBlock 0 346 s50Check = true := treeBlock_merge (start := 0) (left := 168) (right := 178) (check := s50Check) s50Group0_168 s50Group168_178
theorem s50Blocks : treeBlock 0 346 s50Check = true := s50Group0_346
theorem s50Known : Known s50Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s42Stock) s41Stock) s38Stock) s0Stock) s49Stock) s48Stock) s47Stock) s46Stock) s45Stock) s44Stock) s43Stock) s1Stock) s40Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s50Stock : Lower s50Mask s50StockWords s50Goal 10 := by
  apply lowerDag _ _ _ _ s50Autos _ _ _ s50Known _ s50Roots s50Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s50Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s51Mask : Nat := 0xffffffff
abbrev s51Goal : Nat := sGoal &&& s51Mask
abbrev s51StockWords : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]
def s51Fact : Nat × List Nat × Nat × Nat := (s51Mask, s51StockWords, 8, s51Goal)
def s51Witnesses := unpackWitnesses s51StockWords [2564, 265220, 526849, 792067, 1058307]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s51Stock : Lower s51Mask s51StockWords s51Goal 8 := by
  apply essentialLift (witnesses := s51Witnesses) (cut := s15Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s15StockWords) (by decide +kernel)
  · exact s15Stock
  · decide +kernel
def s52Mask : Nat := 0x3333000033330000
abbrev s52Goal : Nat := sGoal &&& s52Mask
abbrev s52StockWords : List Nat := [0x2222000022220000, 0x3030000030300000, 0x3300000033000000, 0x3333000000000000]
def s52Fact : Nat × List Nat × Nat × Nat := (s52Mask, s52StockWords, 5, s52Goal)
def s52Witnesses := unpackWitnesses s52StockWords [10772, 272913, 537105, 817180]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s52Stock : Lower s52Mask s52StockWords s52Goal 5 := by
  apply essentialLift (witnesses := s52Witnesses) (cut := s41Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s41StockWords) (by decide +kernel)
  · exact s41Stock
  · decide +kernel
def s53Mask : Nat := 0x3333333300000000
abbrev s53Goal : Nat := sGoal &&& s53Mask
abbrev s53StockWords : List Nat := [0x2222222200000000, 0x3030303000000000, 0x3300330000000000, 0x3333000000000000]
def s53Fact : Nat × List Nat × Nat × Nat := (s53Mask, s53StockWords, 5, s53Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s53Stock : Lower s53Mask s53StockWords s53Goal 5 := dagShiftLower (width := 64) pm6 s52Stock (by decide +kernel)
def s54Blob321553 : Nat := (cbits [0x34120d020140205, 0x412190a054221506, 0x2250e07430190886, 0x9108a41229120944, 0xa0d46235160b4502, 0xf0383c1c0e462391, 0x51c0f0683c160, 0x508814180504814, 0x83448051081428, 0x34380d04034080d, 0x4201502054021516, 0x2191a05462150e05, 0x90e0642019040640, 0x6074121d1c064621, 0x94301d0a074221d0, 0x5825100940825008, 0x29008a4682518894, 0x188a45829100a410, 0x8b4182d048b47029, 0x42235140b4482d10, 0x35120d442350a0d, 0x90c0e42239048e46, 0x60f06039140e4423, 0xf0483c0c0f0283c0, 0x583d0e0f4603c140, 0x51c0f4683d188f4, 0x1001438050801410])
def s54Blob322119 : Nat := (cbits [0xffffffffff0fffff, 0xfff38e3fff81ffff, 0xfffe07fe07ff03ff, 0xf81ffc0f80fcf3cc, 0xff03f00ffff83f, 0xfffffc0001ffff0, 0xffe0000000fffc00, 0xfffffff])
def s54Blob322303 : Nat := (cbits [0x8a254510aa0534d5, 0x54728a2a0200594a, 0x45960294454a22ad, 0x5113a88e06b8d34c, 0x18df03b059aaa827, 0x6ecd34c1861cf3c4, 0xe780c30860efec00, 0x8f71c739])
def s54Mask : Nat := 0x3333333333333333
abbrev s54Goal : Nat := sGoal &&& s54Mask
abbrev s54StockWords : List Nat := [0x2222222222222222, 0x3030303030303030, 0x3300330033003300, 0x3333000033330000, 0x3333333300000000]
def s54Fact : Nat × List Nat × Nat × Nat := (s54Mask, s54StockWords, 8, s54Goal)
def s54Cuts : List (Nat × List Nat × Nat × Nat) := [s4Fact, s52Fact, s53Fact, s41Fact]
def s54Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[5, 25, 41, 60, 5, 25, 41, 60, 5, 25, 41, 60, 9, 28, 44, 49, 52, 56, 9, 28, 44, 49, 52, 56], rfl⟩
def s54Witnesses := unpackWitnesses s54StockWords [2564, 264705, 537105, 799241, 1069577]
def s54Index (i : Nat) : Nat := unpack (cbits [0xc0201008034c3801, 0x2c16099cc2613081, 0xb158]) 9 i
def s54Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0x3c800908020001f, 0x320334809cc01328, 0x33368c9d831550c5, 0xc10c53cc38724b3a, 0x9b0e0692]) else (cbits [0xc53063c418c0e624, 0x6314db0e1692c10, 0x5988])) 18 (i % 16)
def s54Forest (i : Nat) : Nat := unpack (cbits [0x9610c508010201f0, 0x23804c401e200914, 0x58c50404e2630731, 0x24b0464e23151496]) 17 i
def s54Links := pageLinks s54Index s54Codes 4 13 4 5
def s54Data (i : Nat) : Nat × Nat :=
  let e := s54Forest i
  (e &&& 15, e >>> 4)
def s54Sample : Nat × Nat := (s54Blob321553, 96)
def s54Tags := dagTraceTags s54Mask 96 (dagTagBases s54StockWords s54Blob322119 s54Blob322303 96) 7 s54Data
def s54States := dagTrace s54Mask s54StockWords 7 s54Data
def s54MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm6, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)))]
def s54Moves := dagMoves s54MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s54Autos : DagMovesOK s54Mask s54Goal 64 s54Moves := dagMovesOfCheck (by decide +kernel)
def s54Check := dagCheckNode s54Mask s54Goal s54Chart (dagKnownCloses s54Goal s54Cuts) 15 s54States s54Moves s54Links s54Sample s54Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s54Roots : dagCheckRoots s54Mask s54Goal s54Chart (dagKnownCloses s54Goal s54Cuts) s54Witnesses (dagRef 15 s54States s54Moves s54Links 0) s54StockWords 7 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s54Block0 : treeBlock 0 15 s54Check = true := by decide +kernel
theorem s54Blocks : treeBlock 0 15 s54Check = true := s54Block0
theorem s54Known : Known s54Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s41Stock) s53Stock) s52Stock) s4Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s54Stock : Lower s54Mask s54StockWords s54Goal 8 := by
  apply lowerDag _ _ _ _ s54Autos _ _ _ s54Known _ s54Roots s54Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s54Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel
def s55Mask : Nat := 0x5555555555555555
abbrev s55Goal : Nat := sGoal &&& s55Mask
abbrev s55StockWords : List Nat := [0x4444444444444444, 0x5050505050505050, 0x5500550055005500, 0x5555000055550000, 0x5555555500000000]
def s55Fact : Nat × List Nat × Nat × Nat := (s55Mask, s55StockWords, 8, s55Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s55Stock : Lower s55Mask s55StockWords s55Goal 8 := dagShiftLower (width := 64) pm1 s54Stock (by decide +kernel)
def s56Mask : Nat := 0xff00ff
abbrev s56Goal : Nat := sGoal &&& s56Mask
abbrev s56StockWords : List Nat := [0xaa00aa, 0xcc00cc, 0xf000f0, 0xff0000]
def s56Fact : Nat × List Nat × Nat × Nat := (s56Mask, s56StockWords, 5, s56Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s56Stock : Lower s56Mask s56StockWords s56Goal 5 := dagShiftLower (width := 64) pm13 s44Stock (by decide +kernel)
def s57Mask : Nat := 0xaaaaaaaa
abbrev s57Goal : Nat := sGoal &&& s57Mask
abbrev s57StockWords : List Nat := [0x88888888, 0xa0a0a0a0, 0xaa00aa00, 0xaaaa0000]
def s57Fact : Nat × List Nat × Nat × Nat := (s57Mask, s57StockWords, 5, s57Goal)
def s57Witnesses := unpackWitnesses s57StockWords [5641, 264705, 529923, 796163]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s57Stock : Lower s57Mask s57StockWords s57Goal 5 := by
  apply essentialLift (witnesses := s57Witnesses) (cut := s12Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s12StockWords) (by decide +kernel)
  · exact s12Stock
  · decide +kernel
def s58Mask : Nat := 0xcccccccc
abbrev s58Goal : Nat := sGoal &&& s58Mask
abbrev s58StockWords : List Nat := [0x88888888, 0xc0c0c0c0, 0xcc00cc00, 0xcccc0000]
def s58Fact : Nat × List Nat × Nat × Nat := (s58Mask, s58StockWords, 5, s58Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s58Stock : Lower s58Mask s58StockWords s58Goal 5 := dagShiftLower (width := 64) pm1 s57Stock (by decide +kernel)
def s59Mask : Nat := 0xffff0000
abbrev s59Goal : Nat := sGoal &&& s59Mask
abbrev s59StockWords : List Nat := [0xaaaa0000, 0xcccc0000, 0xf0f00000, 0xff000000]
def s59Fact : Nat × List Nat × Nat × Nat := (s59Mask, s59StockWords, 5, s59Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s59Stock : Lower s59Mask s59StockWords s59Goal 5 := dagShiftLower (width := 64) pm13 s6Stock (by decide +kernel)
def s60Blob330573 : Nat := (cbits [0x180406020140205, 0xc120b0182c060702, 0x40e06034120d0502, 0x30884c0613060381, 0x9058281508854241, 0x6422190486428160, 0x301a09068141a0c0, 0x2611098381e0e074, 0x140a8442a050a848, 0xe86836190d8582e, 0x583c0e0f0703a19, 0x60500014703c1a0f, 0x5088141805048140, 0x1818000612014280, 0x1824060601814060, 0x2071201844060a0, 0xb0082c08070101c, 0x2034020d0402c04, 0x38580d0e034100d, 0x8380e04038080e01, 0x40f0483c060f1603, 0x30104c02130603c1, 0x205402151904c201, 0x5868150e05420150, 0x3816080580816010, 0x170185c681619058, 0x86428170905c22])
def s60Blob331140 : Nat := (cbits [0xff00fe000239f3f3, 0xfdc67cfcf81fff07, 0x7fe0fff83fff001f, 0xc7ffffe71e078f1f, 0xe7f80fe07fff0fff, 0x80000ffff80001f9, 0x1fe07fff000, 0xf8000000fffff000, 0x1ff])
def s60Blob331338 : Nat := (cbits [0x49022c000018b171, 0x68c254b498011300, 0x2a20a5081256040a, 0x84a8d0e516050a0a, 0xa7680fc0455a08d6, 0x1080ee7200c1971, 0x3061be07b7e000, 0xd8000000779cc042, 0x610808400c081df])
def s60Mask : Nat := 0x55555555ffffffff
abbrev s60Goal : Nat := sGoal &&& s60Mask
abbrev s60StockWords : List Nat := [0xaaaaaaaa, 0x44444444cccccccc, 0x50505050f0f0f0f0, 0x55005500ff00ff00, 0x55550000ffff0000, 0x5555555500000000]
def s60Fact : Nat × List Nat × Nat × Nat := (s60Mask, s60StockWords, 10, s60Goal)
def s60Cuts : List (Nat × List Nat × Nat × Nat) := [s51Fact, s55Fact, s15Fact, s5Fact, s44Fact, s56Fact, s58Fact, s59Fact]
def s60Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[5, 6, 11, 19, 25, 26, 42, 60, 5, 6, 11, 19, 3, 9, 10, 17, 28, 44, 50, 52, 56, 3, 9, 10], rfl⟩
def s60Witnesses := unpackWitnesses s60StockWords [2564, 265220, 526849, 792067, 1058307, 1332234]
def s60Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0x400f13c0a506401, 0x6054550451104050, 0x58960581]) else (cbits [0x789d1741b260d80, 0x849c670986068020, 0xb0a])) 10 (i % 16)
def s60Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0x4e40c54118a0003f, 0xa4b1419ba0333386, 0xdc61cb6c3869266b, 0x1c0a9330d25810cd, 0x118703b0e466]) else (if j < 2 then (cbits [0x70518f8931908c38, 0x9880b3261af44318, 0xa3102234c3de884, 0x262492c2c6289b0e, 0x59278aa4b123]) else (cbits [0x6e998ccc31086620, 0x24b1961cb0c3854c, 0xcd3108c620146282, 0x1c0e62061870798c, 0x196]))) 19 (i % 16)
def s60Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0x60866e218a0407e0, 0x9870249989870449, 0x7c93192462a161c8, 0x17a22587093262cc, 0x7a23c64e]) else (cbits [0xc4525921a6446661, 0x527954965466e161, 0x66161ce187184960, 0x1872161c052])) 18 (i % 16)
def s60Links := pageLinks s60Index s60Codes 4 13 5 5
def s60Data (i : Nat) : Nat × Nat :=
  let e := s60Forest i
  (e &&& 31, e >>> 5)
def s60Sample : Nat × Nat := (s60Blob330573, 96)
def s60Tags := dagTraceTags s60Mask 96 (dagTagBases s60StockWords s60Blob331140 s60Blob331338 96) 9 s60Data
def s60States := dagTrace s60Mask s60StockWords 9 s60Data
def s60MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s60Moves := dagMoves s60MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s60Autos : DagMovesOK s60Mask s60Goal 64 s60Moves := dagMovesOfCheck (by decide +kernel)
def s60Check := dagCheckNode s60Mask s60Goal s60Chart (dagKnownCloses s60Goal s60Cuts) 29 s60States s60Moves s60Links s60Sample s60Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s60Roots : dagCheckRoots s60Mask s60Goal s60Chart (dagKnownCloses s60Goal s60Cuts) s60Witnesses (dagRef 29 s60States s60Moves s60Links 0) s60StockWords 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s60Block0 : treeBlock 0 24 s60Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s60Block24 : treeBlock 24 5 s60Check = true := by decide +kernel
theorem s60Group0_29 : treeBlock 0 29 s60Check = true := treeBlock_merge (start := 0) (left := 24) (right := 5) (check := s60Check) s60Block0 s60Block24
theorem s60Blocks : treeBlock 0 29 s60Check = true := s60Group0_29
theorem s60Known : Known s60Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s59Stock) s58Stock) s56Stock) s44Stock) s5Stock) s15Stock) s55Stock) s51Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s60Stock : Lower s60Mask s60StockWords s60Goal 10 := by
  apply lowerDag _ _ _ _ s60Autos _ _ _ s60Known _ s60Roots s60Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s60Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s61Mask : Nat := 0x33333333ffffffff
abbrev s61Goal : Nat := sGoal &&& s61Mask
abbrev s61StockWords : List Nat := [0x22222222aaaaaaaa, 0xcccccccc, 0x30303030f0f0f0f0, 0x33003300ff00ff00, 0x33330000ffff0000, 0x3333333300000000]
def s61Fact : Nat × List Nat × Nat × Nat := (s61Mask, s61StockWords, 10, s61Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s61Stock : Lower s61Mask s61StockWords s61Goal 10 := dagShiftLower (width := 64) pm1 s60Stock (by decide +kernel)
def s62Mask : Nat := 0x3333ffff3333ffff
abbrev s62Goal : Nat := sGoal &&& s62Mask
abbrev s62StockWords : List Nat := [0x2222aaaa2222aaaa, 0xcccc0000cccc, 0x3030f0f03030f0f0, 0x3300ff003300ff00, 0x3333000033330000, 0x3333ffff00000000]
def s62Fact : Nat × List Nat × Nat × Nat := (s62Mask, s62StockWords, 10, s62Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s62Stock : Lower s62Mask s62StockWords s62Goal 10 := dagShiftLower (width := 64) pm24 s60Stock (by decide +kernel)
def s63Mask : Nat := 0xff00ff00ff00ff
abbrev s63Goal : Nat := sGoal &&& s63Mask
abbrev s63StockWords : List Nat := [0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xf000f000f000f0, 0xff000000ff0000, 0xff00ff00000000]
def s63Fact : Nat × List Nat × Nat × Nat := (s63Mask, s63StockWords, 6, s63Goal)
def s63Witnesses := unpackWitnesses s63StockWords [2564, 265220, 526849, 796163, 1066499]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s63Stock : Lower s63Mask s63StockWords s63Goal 6 := by
  apply essentialLift (witnesses := s63Witnesses) (cut := s38Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s38StockWords) (by decide +kernel)
  · exact s38Stock
  · decide +kernel
def pm39 : List (List (Nat × Nat) × List (Nat × Nat)) := [st34, st35]
def s64Mask : Nat := 0xff000000ff
abbrev s64Goal : Nat := sGoal &&& s64Mask
abbrev s64StockWords : List Nat := [0xaa000000aa, 0xcc000000cc, 0xf0000000f0, 0xff00000000]
def s64Fact : Nat × List Nat × Nat × Nat := (s64Mask, s64StockWords, 5, s64Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s64Stock : Lower s64Mask s64StockWords s64Goal 5 := dagShiftLower (width := 64) pm39 s44Stock (by decide +kernel)
def s65Mask : Nat := 0x5555000055550000
abbrev s65Goal : Nat := sGoal &&& s65Mask
abbrev s65StockWords : List Nat := [0x4444000044440000, 0x5050000050500000, 0x5500000055000000, 0x5555000000000000]
def s65Fact : Nat × List Nat × Nat × Nat := (s65Mask, s65StockWords, 5, s65Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s65Stock : Lower s65Mask s65StockWords s65Goal 5 := dagShiftLower (width := 64) pm1 s52Stock (by decide +kernel)
def s66Mask : Nat := 0x5555555500000000
abbrev s66Goal : Nat := sGoal &&& s66Mask
abbrev s66StockWords : List Nat := [0x4444444400000000, 0x5050505000000000, 0x5500550000000000, 0x5555000000000000]
def s66Fact : Nat × List Nat × Nat × Nat := (s66Mask, s66StockWords, 5, s66Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s66Stock : Lower s66Mask s66StockWords s66Goal 5 := dagShiftLower (width := 64) pm24 s52Stock (by decide +kernel)
def s67Blob345424 : Nat := (cbits [0x180406020140205, 0xc180e05038060702, 0x2150904c22130184, 0xa0a05824160a0542, 0xe078301a09068141, 0x9444231088c06230, 0x4826110984825108, 0x2e140a8442a050a8, 0x188d46433188cc58, 0xe86836190d86835, 0x583c0e0f0703a19, 0x60500014703c1a0f, 0x50a0142205060140, 0x1818000612014420, 0x1824060601814060, 0x2071201844060a0, 0xe0103808070101c, 0x16038380e0403808, 0x84c20130104c0213, 0x4081500854641318, 0x8151885438150805, 0x6080580816010586, 0x185c681619058381, 0x6828170905c22170, 0x381a08068101a010, 0x1e05078701a19068, 0xc078281e0907818])
def s67Blob345994 : Nat := (cbits [0x700fe01e07c0f93, 0x7f9ff3fc001e07ff, 0xfffff81fffff001e, 0xffffffe791e23c7f, 0x1e03c060f81fffe0, 0xffe00000f80001f8, 0x1ffe003ff80, 0xfffc0000ffffffff, 0x1ff])
def s67Blob346191 : Nat := (cbits [0x1025400a02c0591, 0x4694d2b400060229, 0x2a2a88120a56040a, 0xd4a8a8e51142284a, 0x1a03406051115540, 0x9d404100e00c0970, 0x403031bfe003bf00, 0xfdf80000e79de79c, 0x601861880c0c1df])
def s67Mask : Nat := 0x55ff55ff55ff55ff
abbrev s67Goal : Nat := sGoal &&& s67Mask
abbrev s67StockWords : List Nat := [0xaa00aa00aa00aa, 0x44cc44cc44cc44cc, 0x50f050f050f050f0, 0x5500550055005500, 0x55ff000055ff0000, 0x55ff55ff00000000]
def s67Fact : Nat × List Nat × Nat × Nat := (s67Mask, s67StockWords, 10, s67Goal)
def s67Cuts : List (Nat × List Nat × Nat × Nat) := [s55Fact, s5Fact, s63Fact, s56Fact, s64Fact, s45Fact, s65Fact, s66Fact]
def s67Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[5, 6, 19, 26, 35, 42, 60, 5, 6, 19, 26, 35, 3, 10, 28, 44, 49, 50, 52, 56, 3, 10, 28, 44], rfl⟩
def s67Witnesses := unpackWitnesses s67StockWords [2564, 265220, 526849, 799762, 1058307, 1328643]
def s67Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 6 then (if j < 3 then (if j < 1 then (cbits [0xc0149436e00e8001, 0x85c017005c017005, 0x8806201804600170, 0x1a006231]) else (if j < 2 then (cbits [0x1c006a31a80681, 0x7781d807601c0c7, 0xa80aa02988a60298, 0x2a90aa02]) else (cbits [0x602c88b202c80b20, 0x4bc02d8cb602d80b, 0x180c602f90be02f0, 0x3200c613]))) else (if j < 4 then (cbits [0x803a00cce3300c82, 0xee33b80ee03a0ce, 0xd84f603d04f403d0, 0x3e08f803]) else (if j < 5 then (cbits [0xc03f00fc03f00fc0, 0x12c04b011c83f40f, 0xb0d2c04b012c04b0, 0x4c813204]) else (cbits [0x204e153804c8d320, 0x1480508d42050814, 0x589503528d481520, 0x5e0d5af5])))) else (if j < 9 then (if j < 7 then (cbits [0x260017e15f817e0, 0x18a1628184361018, 0x58d8e463058c0630, 0x67019c06]) else (if j < 8 then (cbits [0xa36a819e667059c0, 0x5b406c09b006c01a, 0x301c826da5b606d0, 0x7301cc07]) else (cbits [0x787581d037309cc0, 0x608081860608181d, 0x3820e0828a0a0820, 0x85020e38]))) else (if j < 11 then (if j < 10 then (cbits [0xe087821648582141, 0xa240880a20087861, 0x1024029002400893, 0x91024409]) else (cbits [0x40938e4459102440, 0x2620988256695065, 0xd0274098a6620988, 0x9d827419])) else (if j < 12 then (cbits [0x60a40e76d9d82760, 0x2aa0a892966a5829, 0x382c64aabaaa0aa8, 0xb51ece3b]) else (cbits [0xc0b912e40b902e21, 0x3022c083001bb2ae]))))) 14 (i % 16)
def s67Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then (cbits [0x2e3140080a80003f, 0xe8c7c8831b188c54, 0x4337388cccd63272, 0x9882f4343b88cfcf, 0x63350989d3062141, 0x5518dd4a]) else (if j < 2 then (cbits [0x6292cd5190f4a63f, 0xd30e36a93f5aa4cd, 0x8c435f30fd7ac395, 0x237af45dd3d118, 0x1304003c0e00901, 0x600dc14]) else (cbits [0x1e315068c5218043, 0x98d0c26337088c64, 0x8f440b310c28c388, 0x8c64083140180662, 0x40833d100cc3802, 0x84813012]))) else (if j < 4 then (cbits [0x1cc38020c5016630, 0x2802020624873d10, 0xc314081880240110, 0xa82af440718800, 0x3270c8c7c3031b01, 0xe0ccc34]) else (if j < 5 then (cbits [0x3a3438e0cfc3a337, 0x1189c426210f1882, 0x863f1298dc486331, 0x24cc4c92c92990e4, 0xc391530e25093f14, 0x16b0fc58]) else (cbits [0x58f45953d105ec43, 0x200a8060340d8042, 0xf441030e03e92c0, 0xa4b00a0341180724, 0x2893bd104ec380f, 0x30cd852])))) else (if j < 9 then (if j < 7 then (cbits [0x56f4413b0e04092c, 0x730f060948173d30, 0x632a190c980e0361, 0x18c86e62a1a18986, 0x64a1f19087863e1d, 0x9f193a78]) else (if j < 8 then (cbits [0x86f442130e08292c, 0xb19006a01ca1c940, 0x293c1c24c26c64c1, 0x99307601c9ca5207, 0x10203d207e93c1e, 0x2600488a]) else (cbits [0xa0335278c5010036, 0x90d30ac341290d00, 0x6291a1882ac34da, 0xb0e0b492c2c98a8b, 0x8ae4940b8f442d, 0x2380a48c]))) else (if j < 10 then (cbits [0x92620240c786a314, 0x5bd1096c382524b0, 0xc04c2701009a034a, 0x8d30a23402680429, 0x6201b0c501202aa8, 0x2a24b0a6]) else (if j < 11 then (cbits [0xa2334270040aaf44, 0x48070900102b8d30, 0x401ca99930a66402, 0x8c72a864c2a19009, 0x3140500daaa64c25, 0x2c0c646e]) else (cbits [0xc292c2f1880b231a, 0x2a4f0c893131a4c0, 0xe949b2a520ce93d3, 0x4940d4f4434b0e2c, 0x9483024f0be930b5, 0x310042c0]))))) else (if j < 18 then (if j < 15 then (if j < 13 then (cbits [0x723142f988070314, 0x43120ccf44301880, 0xe32a360042ccc483, 0x8020e092c1d1880d, 0x1c3718807631436, 0x390ca8dc]) else (if j < 14 then (cbits [0xec6411e1880e634c, 0xe8c50f32503c24b0, 0x834c3a9880e83351, 0xa8ea64c3bbd20e, 0x6203b0cc47c31406, 0x3f18f4f6]) else (cbits [0x2f484024f0fe92c, 0xebd20f893c414941, 0x3143e18807e3143, 0x80a8fa6203b8cc48, 0x327428c7d0831b06, 0x440ccd0c]))) else (if j < 16 then (cbits [0x14343c40cfd14337, 0x8189c826210f1883, 0x63f3d98dcf06333, 0xa4cd1a92cbd990ef, 0xc3948b0e31e93f47, 0x4a30fd26]) else (if j < 17 then (cbits [0x26f45c8bd112cc43, 0x5a4f11234c438043, 0xcc380fa4b118f484, 0xcd920028c73d111, 0xf444730e04092c07, 0x4abd3124]) else (cbits [0x1e0364ab0f12e948, 0x98813431e4c8c68, 0x69322f18a4b46251, 0xa5293c9424ea4f93, 0xf444fb0e33c94ece, 0xd0494140])))) else (if j < 21 then (if j < 19 then (cbits [0x4401c0800d138028, 0x20c74443140880d1, 0x63141180213692c5, 0xc50240344e18814, 0x9414ea4b14c31d12, 0x543d394e]) else (if j < 20 then (cbits [0x4a3140980a953250, 0x398c53c620558cf4, 0xec4a56a4c55892c5, 0x18815c0285849415, 0x62b2d989c8462113, 0x3f98dcd2]) else (cbits [0x3e92d46a4b2fe643, 0x930e3589435624dd, 0xe92cd93d1168c435, 0xa166f444730e04, 0x6205c0ca4503145b, 0x5c98a51e]))) else (if j < 23 then (if j < 22 then (cbits [0x203141480215a641, 0xa0cd96e92c570cd5, 0x8627219884546200, 0x190ef263f3518acb, 0x93f5024b52292cc1, 0xd8250f52]) else (cbits [0x78f455dbd1164c38, 0x930e05692c0a9909, 0x692c16188166f444, 0x8cd45a314de49412, 0x6416098d5286205f, 0xd799355e])) else (if j < 24 then (cbits [0x5c31460313184f4c, 0xa98818633d600cd4, 0xa349178c502c02a4, 0x18f5506314b18818, 0x9485a24b18c649d4, 0x6130f18e]) else (cbits [0x2e620180c5186f48, 0x1])))))) 22 (i % 16)
def s67Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 6 then (if j < 3 then (if j < 1 then (cbits [0x8020080540203f00, 0xc632063140300c81, 0x200f020048130e00, 0x231805804c080801, 0x130e038628040370, 0x18a8]) else (if j < 2 then (cbits [0x44486320462410, 0x9e882ac380219b81, 0x31b1818a00b10c0, 0x80080d8c9c6063e3, 0xf98806066e303331, 0x4960]) else (cbits [0x989c60c4230c381f, 0xc6e306331800e11, 0x29331861c13a4b06, 0x87a215b0e0600505, 0xc3d30b987e30c391, 0x6218]))) else (if j < 4 then (cbits [0xc98c862a0294830, 0x40386a6263219519, 0x93038315191900d, 0x200e1d98c8c92787, 0xf9908c8c987a63e3, 0x49e1]) else (if j < 5 then (cbits [0x30e0c925864f483f, 0x80208a31b017a219, 0xc31e46014a300211, 0x561c2324b118c408, 0x28101340689a0124, 0x18a2]) else (cbits [0x8d0114680a233545, 0x5e88a692c5331029, 0xa629451a62b8d051, 0x561c22a4b114c548, 0xf98817863e02f444, 0x4982])))) else (if j < 9 then (if j < 7 then (cbits [0x4189258bc93c5f, 0x9278bc9315e4982f, 0xcc486849eaf3d119, 0xc19380bd1179870b, 0x61881b4010da0106, 0x1953]) else (if j < 8 then (cbits [0xca9c86660292c6c, 0x8c40e8335741a639, 0x492c727a43b9905c, 0xc3103d8cdc064a0e, 0xd98f5ede90f893c7, 0x4963]) else (cbits [0xc941ede90f693c7b, 0x63f0831b8431000, 0x233384008438c9e1, 0xb49e458cde106991, 0x230e23925908f488, 0x499c]))) else (if j < 11 then (if j < 10 then (cbits [0x3d12498710802890, 0x1e992ac3f8461cc2, 0x2621014a44bb10e1, 0xc4994c8c7a646353, 0xca50a6527d320289, 0x61c4]) else (cbits [0x807288c4e02f4499, 0x8c660231da218a51, 0xcf4ea64a0d30c769, 0xb19ed598dc064a14, 0x580a2b92635692ca, 0x6255])) else (if j < 12 then (cbits [0xb0e2c925803250ab, 0x926602c43b27a259, 0xc329b64965b80a2d, 0xb7a25db0e004c536, 0xfb0fc0587202f45b, 0x19ad]) else (cbits [0xbd32fcc6b7ec4cc0, 0x46938ac430119ee1, 0x4a46299271]))))) 21 (i % 16)
def s67Links := pageLinks s67Index s67Codes 5 13 8 6
def s67Data (i : Nat) : Nat × Nat :=
  let e := s67Forest i
  (e &&& 255, e >>> 8)
def s67Sample : Nat × Nat := (s67Blob345424, 96)
def s67Tags := dagTraceTags s67Mask 96 (dagTagBases s67StockWords s67Blob345994 s67Blob346191 96) 9 s67Data
def s67States := dagTrace s67Mask s67StockWords 9 s67Data
def s67MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm6, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)))]
def s67Moves := dagMoves s67MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s67Autos : DagMovesOK s67Mask s67Goal 64 s67Moves := dagMovesOfCheck (by decide +kernel)
def s67Check := dagCheckNode s67Mask s67Goal s67Chart (dagKnownCloses s67Goal s67Cuts) 200 s67States s67Moves s67Links s67Sample s67Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s67Roots : dagCheckRoots s67Mask s67Goal s67Chart (dagKnownCloses s67Goal s67Cuts) s67Witnesses (dagRef 200 s67States s67Moves s67Links 0) s67StockWords 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s67Block0 : treeBlock 0 24 s67Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s67Block24 : treeBlock 24 24 s67Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s67Block48 : treeBlock 48 24 s67Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s67Block72 : treeBlock 72 24 s67Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s67Block96 : treeBlock 96 24 s67Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s67Block120 : treeBlock 120 24 s67Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s67Block144 : treeBlock 144 24 s67Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s67Block168 : treeBlock 168 24 s67Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s67Block192 : treeBlock 192 8 s67Check = true := by decide +kernel
theorem s67Group0_48 : treeBlock 0 48 s67Check = true := treeBlock_merge (start := 0) (left := 24) (right := 24) (check := s67Check) s67Block0 s67Block24
theorem s67Group48_48 : treeBlock 48 48 s67Check = true := treeBlock_merge (start := 48) (left := 24) (right := 24) (check := s67Check) s67Block48 s67Block72
theorem s67Group0_96 : treeBlock 0 96 s67Check = true := treeBlock_merge (start := 0) (left := 48) (right := 48) (check := s67Check) s67Group0_48 s67Group48_48
theorem s67Group96_48 : treeBlock 96 48 s67Check = true := treeBlock_merge (start := 96) (left := 24) (right := 24) (check := s67Check) s67Block96 s67Block120
theorem s67Group168_32 : treeBlock 168 32 s67Check = true := treeBlock_merge (start := 168) (left := 24) (right := 8) (check := s67Check) s67Block168 s67Block192
theorem s67Group144_56 : treeBlock 144 56 s67Check = true := treeBlock_merge (start := 144) (left := 24) (right := 32) (check := s67Check) s67Block144 s67Group168_32
theorem s67Group96_104 : treeBlock 96 104 s67Check = true := treeBlock_merge (start := 96) (left := 48) (right := 56) (check := s67Check) s67Group96_48 s67Group144_56
theorem s67Group0_200 : treeBlock 0 200 s67Check = true := treeBlock_merge (start := 0) (left := 96) (right := 104) (check := s67Check) s67Group0_96 s67Group96_104
theorem s67Blocks : treeBlock 0 200 s67Check = true := s67Group0_200
theorem s67Known : Known s67Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s66Stock) s65Stock) s45Stock) s64Stock) s56Stock) s63Stock) s5Stock) s55Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s67Stock : Lower s67Mask s67StockWords s67Goal 10 := by
  apply lowerDag _ _ _ _ s67Autos _ _ _ s67Known _ s67Roots s67Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s67Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s68Mask : Nat := 0x33ff33ff33ff33ff
abbrev s68Goal : Nat := sGoal &&& s68Mask
abbrev s68StockWords : List Nat := [0x22aa22aa22aa22aa, 0xcc00cc00cc00cc, 0x30f030f030f030f0, 0x3300330033003300, 0x33ff000033ff0000, 0x33ff33ff00000000]
def s68Fact : Nat × List Nat × Nat × Nat := (s68Mask, s68StockWords, 10, s68Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Stock : Lower s68Mask s68StockWords s68Goal 10 := dagShiftLower (width := 64) pm1 s67Stock (by decide +kernel)
def s69Blob352540 : Nat := (cbits [0x82c060b020180406, 0xc180e05038140b04, 0x4160904c22130184, 0x90886412190a0582, 0xc068241a05068301, 0x8c42230188c381e0, 0x1229120984426110, 0x2a050a85029108a4, 0x188cc582e140a844, 0x8e46836190d86433, 0x703a190e8703918, 0x3c1a0f0583c0e0f, 0x6050180606000187, 0x1018280609018180, 0x2c040b0082c48061, 0x100e02038040e040, 0x130084c580e0e038, 0x1904c62130804c04, 0x582016020580416, 0x402191a05864160e, 0x2190e06420190406, 0xa04068041a1c0646, 0xc068641a0e068201, 0x6c141b0486c061b1, 0x141e0c06c241b088, 0x1e0a078241e06078, 0x1008c04230088c30])
def s69Blob353113 : Nat := (cbits [0xf83800198738739c, 0xf8ff8fffe0fc0fc0, 0xfffff03ffffff867, 0x7c7ff8640c40c63, 0x7f07f07c1f00003f, 0x1fffffc007f807f8, 0xf80007ff8007ff80, 0xfff800001fffffff, 0xe0000000000007ff])
def s69Blob353328 : Nat := (cbits [0x480810088318318c, 0x186986b5202c0440, 0x455510119052b023, 0x685438440840842, 0x6d06d0780a00822a, 0x139aaa88072065d0, 0xe20186ff80076f00, 0xf6f000001ce3cf3c, 0x80030c30c406077f])
def s69Mask : Nat := 0x5f5f5f5f5f5f5f5f
abbrev s69Goal : Nat := sGoal &&& s69Mask
abbrev s69StockWords : List Nat := [0xa0a0a0a0a0a0a0a, 0x4c4c4c4c4c4c4c4c, 0x5050505050505050, 0x5f005f005f005f00, 0x5f5f00005f5f0000, 0x5f5f5f5f00000000]
def s69Fact : Nat × List Nat × Nat × Nat := (s69Mask, s69StockWords, 10, s69Goal)
def s69Cuts : List (Nat × List Nat × Nat × Nat) := [s16Fact, s55Fact, s15Fact, s22Fact, s5Fact, s24Fact]
def s69Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[6, 11, 19, 25, 26, 35, 41, 42, 60, 6, 11, 19, 3, 9, 10, 28, 44, 49, 50, 52, 56, 3, 9, 10], rfl⟩
def s69Witnesses := unpackWitnesses s69StockWords [5642, 265220, 527362, 792067, 1058307, 1328643]
def s69Index (i : Nat) : Nat := unpack (cbits [0x50850203260a4601, 0x29]) 7 i
def s69Codes (i : Nat) : Nat := unpack (cbits [0xc9c631508c50003f, 0x8632124b1092c30, 0x62021880e3142b0e, 0x298844]) 18 i
def s69Forest (i : Nat) : Nat := unpack (cbits [0x8a8a4b08628203f0, 0xa38c9c5870863241, 0x92c118]) 17 i
def s69Links := pageLinks s69Index s69Codes 3 13 4 4
def s69Data (i : Nat) : Nat × Nat :=
  let e := s69Forest i
  (e &&& 15, e >>> 4)
def s69Sample : Nat × Nat := (s69Blob352540, 96)
def s69Tags := dagTraceTags s69Mask 96 (dagTagBases s69StockWords s69Blob353113 s69Blob353328 96) 9 s69Data
def s69States := dagTrace s69Mask s69StockWords 9 s69Data
def s69MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s69Moves := dagMoves s69MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s69Autos : DagMovesOK s69Mask s69Goal 64 s69Moves := dagMovesOfCheck (by decide +kernel)
def s69Check := dagCheckNode s69Mask s69Goal s69Chart (dagKnownCloses s69Goal s69Cuts) 9 s69States s69Moves s69Links s69Sample s69Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s69Roots : dagCheckRoots s69Mask s69Goal s69Chart (dagKnownCloses s69Goal s69Cuts) s69Witnesses (dagRef 9 s69States s69Moves s69Links 0) s69StockWords 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s69Block0 : treeBlock 0 9 s69Check = true := by decide +kernel
theorem s69Blocks : treeBlock 0 9 s69Check = true := s69Block0
theorem s69Known : Known s69Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s24Stock) s5Stock) s22Stock) s15Stock) s55Stock) s16Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s69Stock : Lower s69Mask s69StockWords s69Goal 10 := by
  apply lowerDag _ _ _ _ s69Autos _ _ _ s69Known _ s69Roots s69Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s69Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s70Mask : Nat := 0x3f3f3f3f3f3f3f3f
abbrev s70Goal : Nat := sGoal &&& s70Mask
abbrev s70StockWords : List Nat := [0x2a2a2a2a2a2a2a2a, 0xc0c0c0c0c0c0c0c, 0x3030303030303030, 0x3f003f003f003f00, 0x3f3f00003f3f0000, 0x3f3f3f3f00000000]
def s70Fact : Nat × List Nat × Nat × Nat := (s70Mask, s70StockWords, 10, s70Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s70Stock : Lower s70Mask s70StockWords s70Goal 10 := dagShiftLower (width := 64) pm1 s69Stock (by decide +kernel)
def s71Mask : Nat := 0x5555ffff5555ffff
abbrev s71Goal : Nat := sGoal &&& s71Mask
abbrev s71StockWords : List Nat := [0xaaaa0000aaaa, 0x4444cccc4444cccc, 0x5050f0f05050f0f0, 0x5500ff005500ff00, 0x5555000055550000, 0x5555ffff00000000]
def s71Fact : Nat × List Nat × Nat × Nat := (s71Mask, s71StockWords, 10, s71Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s71Stock : Lower s71Mask s71StockWords s71Goal 10 := dagShiftLower (width := 64) pm6 s60Stock (by decide +kernel)
def pm40 : List (List (Nat × Nat) × List (Nat × Nat)) := [st23, st24]
def pm41 : List (List (Nat × Nat) × List (Nat × Nat)) := [st23, st24, st25]
def pm42 : List (List (Nat × Nat) × List (Nat × Nat)) := [st24, st35]
def s72Blob358072 : Nat := (cbits [0x88c06130182c0607, 0x683c160f0383c01, 0x60f0402c08071c0f, 0x70185c20130603c0, 0xe07c301b0186c281, 0xac48270189c40230, 0x633160bc502b018, 0x3c1c0ec6837180cc, 0x120f0303c0a0f018, 0x1c0007180f0503c, 0xc000b1201c280706, 0x80f1402c300b0602, 0x31603c380f0403c0, 0x804c30130a04c001, 0x5c38170805c08171, 0x381b0806c101b1a0, 0x1f0607c061f1c06c, 0x1208c00230c07c28, 0x9c08271808c5023, 0xc102b1a09c582710, 0x62f1c0ac582b100a, 0x3140bc482f060bc0, 0xc0cc6833100cc203, 0xdc48370a0dc06371, 0x503b0c0ec063b180, 0x3c040f0083c180ec, 0x160fc383f100f020])
def s72Blob358644 : Nat := (cbits [0xfffffffc0fffff0f, 0xf49a6df1c3ffffff, 0xfc3c3c3c3c3c3c3f, 0x3fc03fc3f8e38ef2, 0xff03f0f4ffc03fc0, 0xffffc0003fffc003, 0xc0000003fffc00f8, 0xffffffff])
def s72Blob358832 : Nat := (cbits [0x40000000128a40f, 0xb492497000440400, 0xc41919349934b4b8, 0x2b513b8958c30ab0, 0x6e0350d0c9822b51, 0x52ab422233bb9112, 0x822222238ed400e0, 0xa333b3bb])
def s72Mask : Nat := 0x9999999999999999
abbrev s72Goal : Nat := sGoal &&& s72Mask
abbrev s72StockWords : List Nat := [0x8888888888888888, 0x9090909090909090, 0x9900990099009900, 0x9999000099990000, 0x9999999900000000]
def s72Fact : Nat × List Nat × Nat × Nat := (s72Mask, s72StockWords, 8, s72Goal)
def s72Cuts : List (Nat × List Nat × Nat × Nat) := []
def s72Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[7, 11, 19, 35, 60, 7, 11, 19, 35, 60, 7, 11, 3, 28, 44, 52, 56, 3, 28, 44, 52, 56, 3, 28], rfl⟩
def s72Witnesses := unpackWitnesses s72StockWords [3588, 265731, 529923, 796163, 1066499]
def s72Index (i : Nat) : Nat := unpack (cbits [0x40480900f941f001, 0xc1516a04e39c120e, 0xc03802f0de0b]) 11 i
def s72Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 2 then (if j < 1 then (cbits [0x820024040100001f, 0xcd40360e01305007, 0x68e02b450139b807, 0x50918a2b80dd5406, 0x3870c7c306361631, 0x1c19]) else (cbits [0x170cdcb06663c32b, 0xdb0c4e7662139310, 0x8fc6377c319b718a, 0x78c499a5a4b52525, 0x42db0e5658711c93, 0x200])) else (if j < 3 then (cbits [0x21a4b0ccc4006314, 0x580680c0285361c, 0x8306300831213010, 0x318a010020a0c7, 0x41530e0692581462, 0xd31]) else 0x1a318)) 21 (i % 16)
def s72Forest (i : Nat) : Nat := unpack (cbits [0x8a100208010201f0, 0x9880a1801e200911, 0x8988286282624800, 0xc7c4c51a31b118a]) 17 i
def s72Links := pageLinks s72Index s72Codes 5 13 4 6
def s72Data (i : Nat) : Nat × Nat :=
  let e := s72Forest i
  (e &&& 15, e >>> 4)
def s72Sample : Nat × Nat := (s72Blob358072, 96)
def s72Tags := dagTraceTags s72Mask 96 (dagTagBases s72StockWords s72Blob358644 s72Blob358832 96) 7 s72Data
def s72States := dagTrace s72Mask s72StockWords 7 s72Data
def s72MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm13, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 4, 3, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 4, 3, 5] 0 i.val))), (pm39, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 5, 3, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 4, 5, 3] 0 i.val))), (pm31, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val))), (pm40, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 4, 2, 3, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 4, 2, 5] 0 i.val))), (pm41, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 5, 2, 3, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 4, 5, 2] 0 i.val))), (pm12, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 4, 2, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 4, 2, 3, 5] 0 i.val))), (pm25, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 5, 2, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 4, 2, 5, 3] 0 i.val))), (pm42, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 4, 5, 2, 3] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 4, 5, 2, 3] 0 i.val)))]
def s72Moves := dagMoves s72MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s72Autos : DagMovesOK s72Mask s72Goal 64 s72Moves := dagMovesOfCheck (by decide +kernel)
def s72Check := dagCheckNode s72Mask s72Goal s72Chart (dagKnownCloses s72Goal s72Cuts) 15 s72States s72Moves s72Links s72Sample s72Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s72Roots : dagCheckRoots s72Mask s72Goal s72Chart (dagKnownCloses s72Goal s72Cuts) s72Witnesses (dagRef 15 s72States s72Moves s72Links 0) s72StockWords 7 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s72Block0 : treeBlock 0 15 s72Check = true := by decide +kernel
theorem s72Blocks : treeBlock 0 15 s72Check = true := s72Block0
theorem s72Known : Known s72Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s72Stock : Lower s72Mask s72StockWords s72Goal 8 := by
  apply lowerDag _ _ _ _ s72Autos _ _ _ s72Known _ s72Roots s72Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s72Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def s73Mask : Nat := 0xaaaaaaaaaaaaaaaa
abbrev s73Goal : Nat := sGoal &&& s73Mask
abbrev s73StockWords : List Nat := [0x8888888888888888, 0xa0a0a0a0a0a0a0a0, 0xaa00aa00aa00aa00, 0xaaaa0000aaaa0000, 0xaaaaaaaa00000000]
def s73Fact : Nat × List Nat × Nat × Nat := (s73Mask, s73StockWords, 6, s73Goal)
def s73Witnesses := unpackWitnesses s73StockWords [5641, 264705, 529923, 796163, 1066499]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s73Stock : Lower s73Mask s73StockWords s73Goal 6 := by
  apply essentialLift (witnesses := s73Witnesses) (cut := s12Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s12StockWords) (by decide +kernel)
  · exact s12Stock
  · decide +kernel
def s74Mask : Nat := 0xcccccccccccccccc
abbrev s74Goal : Nat := sGoal &&& s74Mask
abbrev s74StockWords : List Nat := [0x8888888888888888, 0xc0c0c0c0c0c0c0c0, 0xcc00cc00cc00cc00, 0xcccc0000cccc0000, 0xcccccccc00000000]
def s74Fact : Nat × List Nat × Nat × Nat := (s74Mask, s74StockWords, 6, s74Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s74Stock : Lower s74Mask s74StockWords s74Goal 6 := dagShiftLower (width := 64) pm1 s73Stock (by decide +kernel)
def s75Mask : Nat := 0xcccc0000cccc
abbrev s75Goal : Nat := sGoal &&& s75Mask
abbrev s75StockWords : List Nat := [0x888800008888, 0xc0c00000c0c0, 0xcc000000cc00, 0xcccc00000000]
def s75Fact : Nat × List Nat × Nat × Nat := (s75Mask, s75StockWords, 5, s75Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s75Stock : Lower s75Mask s75StockWords s75Goal 5 := dagShiftLower (width := 64) pm24 s57Stock (by decide +kernel)
def s76Blob371499 : Nat := (cbits [0x82c0607020180406, 0xc180e05038140b01, 0x8160905824130184, 0xe0c068241a050682, 0x109844230188c381, 0xa8442a050a848261, 0x6436190cc582e140, 0x3c1c0e8643a1a0d8, 0x1c0f0683c160f038, 0x181406018180006, 0x844060a018240606, 0x40b0201c04071201, 0xe02038040e0402c0, 0x183c580e0e038100, 0x4c04130603c140f0, 0x816010586413080, 0x1619058381608058, 0xa05c24170185c68, 0x68201a04068041a, 0xc061b1c068641a0e, 0x41e0c06c241b0506, 0xe0a078241e060781, 0x8c04230e07c301, 0x9808260109864231, 0x6826190985826100, 0x2a1209c44270189c, 0x160a8402a040a804])
def s76Blob372069 : Nat := (cbits [0xe07e0f000081819c, 0xfffffff0e0783c0, 0xffffffffffffffff, 0xff8ff3fff3464667, 0xfc7878780ff8fc00, 0xf000ffff000ffc00, 0xfff00000ff807f80, 0xffff80000000ffff, 0xffff000000000000])
def s76Blob372284 : Nat := (cbits [0x200200020000808c, 0x59b9bbd02000040, 0x168d15d168d61556, 0x9509a2a872444442, 0xb86868708950a808, 0xa040ceaa040dc80c, 0xde608030df807700, 0xeff700000184f33c, 0xcde60030184100c0])
def s76Mask : Nat := 0xdddddddddddddddd
abbrev s76Goal : Nat := sGoal &&& s76Mask
abbrev s76StockWords : List Nat := [0x8888888888888888, 0xcccccccccccccccc, 0xd0d0d0d0d0d0d0d0, 0xdd00dd00dd00dd00, 0xdddd0000dddd0000, 0xdddddddd00000000]
def s76Fact : Nat × List Nat × Nat × Nat := (s76Mask, s76StockWords, 10, s76Goal)
def s76Cuts : List (Nat × List Nat × Nat × Nat) := [s55Fact, s72Fact, s5Fact, s74Fact, s58Fact, s75Fact, s24Fact, s65Fact, s66Fact]
def s76Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[6, 11, 19, 26, 35, 42, 60, 6, 11, 19, 26, 35, 3, 10, 28, 44, 50, 52, 56, 3, 10, 28, 44, 50], rfl⟩
def s76Witnesses := unpackWitnesses s76StockWords [5642, 265220, 527362, 792067, 1058307, 1328643]
def s76Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 5 then (if j < 2 then (if j < 1 then (cbits [0x801b1837b00e8001, 0xc7861e007801e007, 0x2888a022808a0210, 0x24848e22]) else (cbits [0xa025889602504940, 0xa0028009a326809, 0xc00b002c00b00282, 0x2c00b002])) else (if j < 3 then (cbits [0xe02f80b072c00b00, 0xc002f84be02f80b, 0x580d60340cd00302, 0x3900d673]) else (if j < 4 then (cbits [0xc13b00ec03910e40, 0x50404100fe33ba0e, 0x5810e44381064410, 0x45891604]) else (cbits [0xe14a0d1a746811a0, 0x93a04c913204c052, 0x2814a052053e54e8, 0x53014a15])))) else (if j < 8 then (if j < 6 then (cbits [0x40588562054254c2, 0xd701591964059016, 0xe857815e017805c8, 0x5f157c05]) else (if j < 7 then (cbits [0xc163018826201861, 0x191063858e063818, 0xe01b236c81b016c0, 0x6e81b816]) else (cbits [0x207005c007001ba3, 0x5d207481c477085c, 0x881dc3758dd41748, 0x7885e207]))) else (if j < 9 then (cbits [0x407d01f407b11e44, 0x9f817d85f417d01f, 0x58212284060e17ea, 0x86021618]) else (if j < 10 then (cbits [0xe091921d58686181, 0xe50194024e193824, 0xb026c09b02606949, 0x9c066c29]) else (cbits [0x84a6029049d3a721, 0x2b6cac0eae1a81e9, 0xb402ce1b38]))))) 14 (i % 16)
def s76Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 11 then (if j < 5 then (if j < 2 then (if j < 1 then (cbits [0x683140080780003f, 0x48c7c8231b1f0c54, 0xc3372b0ccca03272, 0x9882bc343ab0cfcb, 0x6333d189cea62133, 0x4418dcfe]) else (cbits [0x2292cc4190efe63f, 0x30e33093f4c24cd, 0xec435230fd46c395, 0x2346f45d03d114, 0x2707806c0e00d01, 0x900cc20])) else (if j < 3 then (cbits [0x303360a8c522403f, 0xd0e30342100cdc, 0xa627121884426209, 0x18fc4e6371318cc4, 0x9331424b24e64393, 0x9524fc54]) else (if j < 4 then (cbits [0x60c3f17b0e45ac38, 0x7bd165af4419b10c, 0x8620818d08063369, 0x3d100cc3802a4b00, 0x6208401001003483, 0x6a4b018]) else (cbits [0x12314873d101cc38, 0x48cd016c38051880, 0x4340050cd2123400, 0x80702201c858d021, 0xc380b24b02804c09, 0x8bbd102e])))) else (if j < 8 then (if j < 6 then (cbits [0x343140c80c406008, 0xe9894386200d8c94, 0x83140fbd103c93e0, 0x190834636060c640, 0xf4411b0e04492c8d, 0xd8d0246]) else (if j < 7 then (cbits [0x2c620068c640a314, 0x124b2386420e18d8, 0x632894bd1052c381, 0xc50586280e8d005, 0x6420b98801c31903, 0x11a4b23e]) else (cbits [0x62334173d1052c38, 0x93d323c34c0f0d00, 0xa620010c7864c3c1, 0xa4b2706431c18dc6, 0xf441eb10c76c381c, 0x1b24b276]))) else (if j < 9 then (cbits [0x631c9bbd106ec38, 0xd30e06c92c0298a8, 0xe92c0318aa74f441, 0x98c878f441d30e06, 0x3400380a080c381f, 0xa10d3084]) else (if j < 10 then (cbits [0x90f442330e08a632, 0x1a4b01001ca44940, 0x6328050ca088f442, 0x99001a3342380701, 0x64c070cd28664c21, 0x2524c288]) else (cbits [0x9a94826a4f098932, 0x730e09692c27b0e2, 0x2aa731209cc3c2, 0x9880a432a288c502, 0xf4429a4b08a6261f, 0x2abd3ca8]))))) else (if j < 17 then (if j < 14 then (if j < 12 then (cbits [0x2402a088072a9250, 0xda4b0b034c2b8ca8, 0x601c2ec940b8c382, 0x24b0b26200a00782, 0x63c2d1930b264c2d, 0x30a4b0be]) else (if j < 13 then (cbits [0xccf4832a4f4c693c, 0x13d20c093c3024b0, 0x273124b0c892c3, 0x9882d203f3480ccd, 0x63f2d98cca66271a, 0x35a4b2b6]) else (cbits [0xdec38b6a4fcda933, 0xa310ce4c3f38b0e4, 0x404cb8bd16def443, 0x3d10d8c381b24b0d, 0xc381ba4b0dc328b6, 0x383d10d8]))) else (if j < 15 then (cbits [0xec03239b0f0e6f4c, 0xba538ee9420a8ca0, 0x32503cbd10f0c38b, 0x80702e6340b18d2f, 0x620bf4940fcf443d, 0x3eb0e0f8]) else (if j < 16 then (cbits [0x1c3e8ca2faf44, 0x3c9410cf4e42b0e1, 0x6c424124b1026204, 0x807104328423d110, 0x1e0c00710832841, 0x1c0c5040]) else (cbits [0x1492c3b98811233d, 0x7b1291a93d45a4c5, 0x83280c80a1212504, 0xa1180280e80703, 0x32a0f8ca03c01c47, 0x1c988050])))) else (if j < 20 then (if j < 18 then (cbits [0x9e62b23189c80621, 0xe18fcc26372e18cc, 0x92d35a4b2c2643a, 0xa4fd1493742a4ccf, 0xc394930e314943c2, 0x4ab0fd28]) else (if j < 19 then (cbits [0x28f45c93d112ec43, 0x630e07492c1498db, 0xcc3c4b3d3126f443, 0x9881320281500792, 0xf4e4599053a62936, 0x4fc9413c]) else (cbits [0x18335160ca4dc314, 0xe3d1136c424d24b1, 0x60281600d05601c4, 0x98805a32a4e0cd13, 0x63f2a18cc906271d, 0x37a4b2ba]))) else (if j < 21 then (cbits [0xe93f3f24ccf292d, 0xfb0fd24c38c8250f, 0xc636513d1542f44c, 0xbd10e0c381e24b05, 0xc3838a4b05e32a49, 0xd1494128]) else (if j < 22 then (cbits [0x4a6353918806001e, 0xaa4b31e64d479905, 0x401e1880714cf4c4, 0x80792c92c3998806, 0x3492a8c9c7a31419, 0x3a188150]) else (cbits [0x2e92cc318f50c631, 0x4a5273c93d4f24c5, 0x5500a14cc3c5])))))) 22 (i % 16)
def s76Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 5 then (if j < 2 then (if j < 1 then (cbits [0x80200803c0203f00, 0xd258066200319b01, 0x2034080068130e00, 0x861c049880246281, 0x130e021258106200, 0xd8]) else (cbits [0x80cc080382202702, 0x86280404c1300e09, 0x23360261c0b24b05, 0x91928c8c50640623, 0xca4f864c4a326201, 0x7a20])) else (if j < 3 then (cbits [0x24b088c400433702, 0x8c4e046210261c11, 0x292c0231b8118cc0, 0xb19415a4cc098705, 0x13d10b9870046282, 0x61c8]) else (if j < 4 then (cbits [0x3d30c466862c3f02, 0x8c406a3140162181, 0xa6373561c1b24b0d, 0xc61c1ab0e0e92586, 0xf8c54058866af443, 0x3191]) else (cbits [0x8d010863602c383f, 0x8c6484f444349621, 0x2f444200e23b0e10, 0xa49625a4c12863e0, 0x530e139278949324, 0x61c2])))) else (if j < 8 then (if j < 6 then (cbits [0x8ca944628a232701, 0x5e9ea2f445149628, 0x234c571952b8ccc0, 0x74962ba4b164c40b, 0xf8cdc064a0aec385, 0x31e2]) else (if j < 7 then (cbits [0xbd2189258be92c60, 0xd27abe92c6449e2f, 0x276831000bd217, 0xc496340131a8066d, 0x40ca1b9266d0c386, 0x61c3]) else (cbits [0xb0fda1872d0f4470, 0x8c4202c43687a639, 0xcc38764a13b00c9d, 0xc00e3d989c05e88e, 0xbd11ed870f86207, 0x3198]))) else (if j < 9 then (cbits [0xa4b204c410201c80, 0x187100f448162140, 0x263701928403d3a0, 0xc498c4a4b22467b1, 0x480a23927b120288, 0x6254]) else (if j < 10 then (cbits [0xb0e2492580325089, 0x987f24c39927a249, 0x293301621c93d325, 0xa6214d24b2680513, 0xcbd3a64c5332f449, 0x9284]) else (cbits [0xbd1685e8942c3801, 0x4c6b4ac3f0161c80, 0x349a862180bd329, 0xa2a92935]))))) 21 (i % 16)
def s76Links := pageLinks s76Index s76Codes 5 13 8 6
def s76Data (i : Nat) : Nat × Nat :=
  let e := s76Forest i
  (e &&& 255, e >>> 8)
def s76Sample : Nat × Nat := (s76Blob371499, 96)
def s76Tags := dagTraceTags s76Mask 96 (dagTagBases s76StockWords s76Blob372069 s76Blob372284 96) 9 s76Data
def s76States := dagTrace s76Mask s76StockWords 9 s76Data
def s76MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm6, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)))]
def s76Moves := dagMoves s76MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s76Autos : DagMovesOK s76Mask s76Goal 64 s76Moves := dagMovesOfCheck (by decide +kernel)
def s76Check := dagCheckNode s76Mask s76Goal s76Chart (dagKnownCloses s76Goal s76Cuts) 171 s76States s76Moves s76Links s76Sample s76Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s76Roots : dagCheckRoots s76Mask s76Goal s76Chart (dagKnownCloses s76Goal s76Cuts) s76Witnesses (dagRef 171 s76States s76Moves s76Links 0) s76StockWords 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s76Block0 : treeBlock 0 24 s76Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s76Block24 : treeBlock 24 24 s76Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s76Block48 : treeBlock 48 24 s76Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s76Block72 : treeBlock 72 24 s76Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s76Block96 : treeBlock 96 24 s76Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s76Block120 : treeBlock 120 24 s76Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s76Block144 : treeBlock 144 24 s76Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s76Block168 : treeBlock 168 3 s76Check = true := by decide +kernel
theorem s76Group0_48 : treeBlock 0 48 s76Check = true := treeBlock_merge (start := 0) (left := 24) (right := 24) (check := s76Check) s76Block0 s76Block24
theorem s76Group48_48 : treeBlock 48 48 s76Check = true := treeBlock_merge (start := 48) (left := 24) (right := 24) (check := s76Check) s76Block48 s76Block72
theorem s76Group0_96 : treeBlock 0 96 s76Check = true := treeBlock_merge (start := 0) (left := 48) (right := 48) (check := s76Check) s76Group0_48 s76Group48_48
theorem s76Group96_48 : treeBlock 96 48 s76Check = true := treeBlock_merge (start := 96) (left := 24) (right := 24) (check := s76Check) s76Block96 s76Block120
theorem s76Group144_27 : treeBlock 144 27 s76Check = true := treeBlock_merge (start := 144) (left := 24) (right := 3) (check := s76Check) s76Block144 s76Block168
theorem s76Group96_75 : treeBlock 96 75 s76Check = true := treeBlock_merge (start := 96) (left := 48) (right := 27) (check := s76Check) s76Group96_48 s76Group144_27
theorem s76Group0_171 : treeBlock 0 171 s76Check = true := treeBlock_merge (start := 0) (left := 96) (right := 75) (check := s76Check) s76Group0_96 s76Group96_75
theorem s76Blocks : treeBlock 0 171 s76Check = true := s76Group0_171
theorem s76Known : Known s76Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s66Stock) s65Stock) s24Stock) s75Stock) s58Stock) s74Stock) s5Stock) s72Stock) s55Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s76Stock : Lower s76Mask s76StockWords s76Goal 10 := by
  apply lowerDag _ _ _ _ s76Autos _ _ _ s76Known _ s76Roots s76Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s76Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s77Mask : Nat := 0xbbbbbbbbbbbbbbbb
abbrev s77Goal : Nat := sGoal &&& s77Mask
abbrev s77StockWords : List Nat := [0xaaaaaaaaaaaaaaaa, 0x8888888888888888, 0xb0b0b0b0b0b0b0b0, 0xbb00bb00bb00bb00, 0xbbbb0000bbbb0000, 0xbbbbbbbb00000000]
def s77Fact : Nat × List Nat × Nat × Nat := (s77Mask, s77StockWords, 10, s77Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s77Stock : Lower s77Mask s77StockWords s77Goal 10 := dagShiftLower (width := 64) pm1 s76Stock (by decide +kernel)
def s78Mask : Nat := 0xff00ff00ffffffff
abbrev s78Goal : Nat := sGoal &&& s78Mask
abbrev s78StockWords : List Nat := [0xaa00aa00aaaaaaaa, 0xcc00cc00cccccccc, 0xf000f000f0f0f0f0, 0xff00ff00ff00ff00, 0xff000000ffff0000, 0xff00ff0000000000]
def s78Fact : Nat × List Nat × Nat × Nat := (s78Mask, s78StockWords, 10, s78Goal)
def s78Witnesses := unpackWitnesses s78StockWords [2564, 265220, 526849, 792067, 1058307, 1331721]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s78Stock : Lower s78Mask s78StockWords s78Goal 10 := by
  apply essentialLift (witnesses := s78Witnesses) (cut := s11Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s11StockWords) (by decide +kernel)
  · exact s11Stock
  · decide +kernel
def s79Mask : Nat := 0xff00ffffff00ffff
abbrev s79Goal : Nat := sGoal &&& s79Mask
abbrev s79StockWords : List Nat := [0xaa00aaaaaa00aaaa, 0xcc00cccccc00cccc, 0xf000f0f0f000f0f0, 0xff00ff00ff00ff00, 0xff000000ff000000, 0xff00ffff00000000]
def s79Fact : Nat × List Nat × Nat × Nat := (s79Mask, s79StockWords, 10, s79Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s79Stock : Lower s79Mask s79StockWords s79Goal 10 := dagShiftLower (width := 64) pm6 s78Stock (by decide +kernel)
def s80Mask : Nat := 0xff33ff33ff33ff33
abbrev s80Goal : Nat := sGoal &&& s80Mask
abbrev s80StockWords : List Nat := [0xaa22aa22aa22aa22, 0xcc00cc00cc00cc00, 0xf030f030f030f030, 0xff00ff00ff00ff00, 0xff330000ff330000, 0xff33ff3300000000]
def s80Fact : Nat × List Nat × Nat × Nat := (s80Mask, s80StockWords, 10, s80Goal)
def s80Witnesses := unpackWitnesses s80StockWords [2564, 267785, 526849, 799249, 1061385, 1331721]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s80Stock : Lower s80Mask s80StockWords s80Goal 10 := by
  apply essentialLift (witnesses := s80Witnesses) (cut := s11Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s11StockWords) (by decide +kernel)
  · exact s11Stock
  · decide +kernel
def s81Mask : Nat := 0xff55ff55ff55ff55
abbrev s81Goal : Nat := sGoal &&& s81Mask
abbrev s81StockWords : List Nat := [0xaa00aa00aa00aa00, 0xcc44cc44cc44cc44, 0xf050f050f050f050, 0xff00ff00ff00ff00, 0xff550000ff550000, 0xff55ff5500000000]
def s81Fact : Nat × List Nat × Nat × Nat := (s81Mask, s81StockWords, 10, s81Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s81Stock : Lower s81Mask s81StockWords s81Goal 10 := dagShiftLower (width := 64) pm1 s80Stock (by decide +kernel)
def s82Mask : Nat := 0xffaaffaaffaaffaa
abbrev s82Goal : Nat := sGoal &&& s82Mask
abbrev s82StockWords : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcc88cc88cc88cc88, 0xf0a0f0a0f0a0f0a0, 0xff00ff00ff00ff00, 0xffaa0000ffaa0000, 0xffaaffaa00000000]
def s82Fact : Nat × List Nat × Nat × Nat := (s82Mask, s82StockWords, 10, s82Goal)
def s82Witnesses := unpackWitnesses s82StockWords [5642, 267785, 526849, 792067, 1058307, 1328643]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s82Stock : Lower s82Mask s82StockWords s82Goal 10 := by
  apply essentialLift (witnesses := s82Witnesses) (cut := s11Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s11StockWords) (by decide +kernel)
  · exact s11Stock
  · decide +kernel
def s83Mask : Nat := 0xffccffccffccffcc
abbrev s83Goal : Nat := sGoal &&& s83Mask
abbrev s83StockWords : List Nat := [0xaa88aa88aa88aa88, 0xcccccccccccccccc, 0xf0c0f0c0f0c0f0c0, 0xff00ff00ff00ff00, 0xffcc0000ffcc0000, 0xffccffcc00000000]
def s83Fact : Nat × List Nat × Nat × Nat := (s83Mask, s83StockWords, 10, s83Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s83Stock : Lower s83Mask s83StockWords s83Goal 10 := dagShiftLower (width := 64) pm1 s82Stock (by decide +kernel)
def s84Mask : Nat := 0xfff0fff0fff0fff0
abbrev s84Goal : Nat := sGoal &&& s84Mask
abbrev s84StockWords : List Nat := [0xaaa0aaa0aaa0aaa0, 0xccc0ccc0ccc0ccc0, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xfff00000fff00000, 0xfff0fff000000000]
def s84Fact : Nat × List Nat × Nat × Nat := (s84Mask, s84StockWords, 10, s84Goal)
def s84Witnesses := unpackWitnesses s84StockWords [2564, 265220, 530953, 817204, 1061385, 1331721]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s84Stock : Lower s84Mask s84StockWords s84Goal 10 := by
  apply essentialLift (witnesses := s84Witnesses) (cut := s11Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s11StockWords) (by decide +kernel)
  · exact s11Stock
  · decide +kernel
def s85Mask : Nat := 0xff0000ff00000000
abbrev s85Goal : Nat := sGoal &&& s85Mask
abbrev s85StockWords : List Nat := [0xaa0000aa00000000, 0xcc0000cc00000000, 0xf00000f000000000, 0xff00000000000000]
def s85Fact : Nat × List Nat × Nat × Nat := (s85Mask, s85StockWords, 7, s85Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s85Stock : Lower s85Mask s85StockWords s85Goal 7 := dagShiftLower (width := 64) pm39 s1Stock (by decide +kernel)
def s86Mask : Nat := 0xff0000ffff0000ff
abbrev s86Goal : Nat := sGoal &&& s86Mask
abbrev s86StockWords : List Nat := [0xaa0000aaaa0000aa, 0xcc0000cccc0000cc, 0xf00000f0f00000f0, 0xff000000ff000000, 0xff0000ff00000000]
def s86Fact : Nat × List Nat × Nat × Nat := (s86Mask, s86StockWords, 8, s86Goal)
def s86Witnesses := unpackWitnesses s86StockWords [2564, 265220, 526849, 799233, 1066499]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s86Stock : Lower s86Mask s86StockWords s86Goal 8 := by
  apply essentialLift (witnesses := s86Witnesses) (cut := s85Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s85StockWords) (by decide +kernel)
  · exact s85Stock
  · decide +kernel
def s87Mask : Nat := 0xffff0000ffff0000
abbrev s87Goal : Nat := sGoal &&& s87Mask
abbrev s87StockWords : List Nat := [0xaaaa0000aaaa0000, 0xcccc0000cccc0000, 0xf0f00000f0f00000, 0xff000000ff000000, 0xffff000000000000]
def s87Fact : Nat × List Nat × Nat × Nat := (s87Mask, s87StockWords, 8, s87Goal)
def s87Witnesses := unpackWitnesses s87StockWords [9746, 271889, 535057, 799249, 1079324]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Stock : Lower s87Mask s87StockWords s87Goal 8 := by
  apply essentialLift (witnesses := s87Witnesses) (cut := s43Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s43StockWords) (by decide +kernel)
  · exact s43Stock
  · decide +kernel
def s88Mask : Nat := 0xf0f000000f0f0000
abbrev s88Goal : Nat := sGoal &&& s88Mask
abbrev s88StockWords : List Nat := [0xa0a000000a0a0000, 0xc0c000000c0c0000, 0xf0f0000000000000, 0xf00000000f000000]
def s88Fact : Nat × List Nat × Nat × Nat := (s88Mask, s88StockWords, 7, s88Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s88Stock : Lower s88Mask s88StockWords s88Goal 7 := dagShiftLower (width := 64) pm12 s1Stock (by decide +kernel)
def s89Mask : Nat := 0xff00000000ff0000
abbrev s89Goal : Nat := sGoal &&& s89Mask
abbrev s89StockWords : List Nat := [0xaa00000000aa0000, 0xcc00000000cc0000, 0xf000000000f00000, 0xff00000000000000]
def s89Fact : Nat × List Nat × Nat × Nat := (s89Mask, s89StockWords, 7, s89Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s89Stock : Lower s89Mask s89StockWords s89Goal 7 := dagShiftLower (width := 64) pm13 s1Stock (by decide +kernel)
def s90Blob401965 : Nat := (cbits [0x743019020140205, 0x70391209442250e, 0x20500014703c0e0f, 0x90e0640219120144, 0x209402250c074701, 0xf042390c0e440250, 0x703d0e0f4483c0c0, 0x190006440050e014, 0x1c074081d0087442, 0xe43839008e40025, 0x4303d100f0083c10, 0x8190c014483d108f, 0xd10874001d100640, 0xe470250e094481, 0xf4423c000f048390, 0x7005100f4083d008, 0x390c094401d12064, 0x3d008f008])
def s90Blob402349 : Nat := (cbits [0xdfe7ffcfff9ffe7f, 0x36fcf9f8f3f3c7dd, 0x1dbf9f7fbe7e3c73, 0xf1ff03fe03fe03e])
def s90Blob402464 : Nat := (cbits [0x2030208230111411, 0x922628a21611455, 0x240609120ea3873, 0xf2ad3512aa89ae])
def s90Mask : Nat := 0x3300003333000033
abbrev s90Goal : Nat := sGoal &&& s90Mask
abbrev s90StockWords : List Nat := [0x2200002222000022, 0x3000003030000030, 0x3300000033000000, 0x3300003300000000]
def s90Fact : Nat × List Nat × Nat × Nat := (s90Mask, s90StockWords, 5, s90Goal)
def s90Cuts : List (Nat × List Nat × Nat × Nat) := []
def s90Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[5, 25, 60, 5, 25, 60, 5, 25, 60, 5, 25, 60, 28, 33, 36, 56, 28, 33, 36, 56, 28, 33, 36, 56], rfl⟩
def s90Witnesses := unpackWitnesses s90StockWords [2564, 264705, 537089, 817180]
def s90Index (i : Nat) : Nat := unpack 0x9 2 i
def s90Codes (i : Nat) : Nat := unpack 0xf 15 i
def s90Forest (i : Nat) : Nat := unpack 0x1e 14 i
def s90Links := pageLinks s90Index s90Codes 1 13 1 2
def s90Data (i : Nat) : Nat × Nat :=
  let e := s90Forest i
  (e &&& 1, e >>> 1)
def s90Sample : Nat × Nat := (s90Blob401965, 63)
def s90Tags := dagTraceTags s90Mask 63 (dagTagBases s90StockWords s90Blob402349 s90Blob402464 63) 4 s90Data
def s90States := dagTrace s90Mask s90StockWords 4 s90Data
def s90MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s90Moves := dagMoves s90MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s90Autos : DagMovesOK s90Mask s90Goal 64 s90Moves := dagMovesOfCheck (by decide +kernel)
def s90Check := dagCheckNode s90Mask s90Goal s90Chart (dagKnownCloses s90Goal s90Cuts) 1 s90States s90Moves s90Links s90Sample s90Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s90Roots : dagCheckRoots s90Mask s90Goal s90Chart (dagKnownCloses s90Goal s90Cuts) s90Witnesses (dagRef 1 s90States s90Moves s90Links 0) s90StockWords 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s90Block0 : treeBlock 0 1 s90Check = true := by decide +kernel
theorem s90Blocks : treeBlock 0 1 s90Check = true := s90Block0
theorem s90Known : Known s90Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s90Stock : Lower s90Mask s90StockWords s90Goal 5 := by
  apply lowerDag _ _ _ _ s90Autos _ _ _ s90Known _ s90Roots s90Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s90Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def s91Mask : Nat := 0x5500005555000055
abbrev s91Goal : Nat := sGoal &&& s91Mask
abbrev s91StockWords : List Nat := [0x4400004444000044, 0x5000005050000050, 0x5500000055000000, 0x5500005500000000]
def s91Fact : Nat × List Nat × Nat × Nat := (s91Mask, s91StockWords, 5, s91Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s91Stock : Lower s91Mask s91StockWords s91Goal 5 := dagShiftLower (width := 64) pm1 s90Stock (by decide +kernel)
def s92Blob411515 : Nat := (cbits [0x180406020140205, 0xc22130184c060702, 0x4160a05422150904, 0xa0c06422190a0582, 0xe078381d0c068241, 0x9444231088c06230, 0x4826110984825108, 0x35188d46433188cc, 0x188e46836190d868, 0xf0703a190e87039, 0x400051c0f0683c0e, 0x2050a01422050181, 0x6018180006120144, 0x201844060a018240, 0x4c08070101c02071, 0x62130804c0413008, 0x150205402151904c, 0x1a05462150e05420, 0x582016020580416, 0xc06171a05864160e, 0x2190a05c24170885, 0x9188643819080640, 0xe068201a01068701, 0x6c061b1c068641a0, 0x221d0c06c241b088, 0x1e09078301d0a074, 0x88c381f0c07828])
def s92Blob412086 : Nat := (cbits [0xfffc0fc19e7d33f3, 0x679eccfcc7f07fc0, 0xf8ff83ff03fff006, 0xfc1ffff879e30f1f, 0x8003f0007f0003ff, 0x7ffffc000000003f, 0xffe0003ffe03ffe0, 0xfffc00007fffffff, 0x800000000000003f])
def s92Blob412302 : Nat := (cbits [0x452425808a2c1171, 0x249444b4813024c0, 0x854815102496082, 0xa8128a1851430a0a, 0x3a0005202122a, 0x648a50082000002d, 0xf380c33ffe03ffc0, 0xfff800007fef7bbc, 0xc6030c3030c37])
def s92Mask : Nat := 0xffff00ffffff00ff
abbrev s92Goal : Nat := sGoal &&& s92Mask
abbrev s92StockWords : List Nat := [0xaaaa00aaaaaa00aa, 0xcccc00cccccc00cc, 0xf0f000f0f0f000f0, 0xff000000ff000000, 0xffff0000ffff0000, 0xffff00ff00000000]
def s92Fact : Nat × List Nat × Nat × Nat := (s92Mask, s92StockWords, 10, s92Goal)
def s92Cuts : List (Nat × List Nat × Nat × Nat) := [s86Fact, s87Fact, s88Fact, s89Fact, s85Fact, s43Fact, s63Fact, s56Fact, s64Fact, s90Fact, s52Fact, s91Fact, s65Fact]
def s92Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[5, 6, 19, 25, 26, 35, 60, 5, 6, 19, 25, 26, 3, 28, 49, 50, 52, 56, 3, 28, 49, 50, 52, 56], rfl⟩
def s92Witnesses := unpackWitnesses s92StockWords [2564, 265220, 526849, 799249, 1058307, 1328643]
def s92Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then (cbits [0xe013802f000d8001, 0x452014804e213804, 0x5845601504540148, 0x16045801]) else (cbits [0x8017185c016845a0, 0x6841a006801a006, 0xc847201c047001c0, 0x1d047401])) else (if j < 3 then (cbits [0xe123807c91f00763, 0x920248090124008, 0x6809a026809a0249, 0x27049a12]) else (cbits [0x462d00b402c089e9, 0xcc03300cc03018b, 0x404ce13380cc1330, 0x3484d203]))) else (if j < 6 then (if j < 5 then (cbits [0x23708dc03684d43, 0xcea03a80ea0390ce, 0xc80f203c80f013a8, 0x4184f2a3]) else (cbits [0xe243050a14281081, 0xd140448512044810, 0x98926048891a4450, 0x4c852a44])) else (if j < 7 then (cbits [0xa05a81681588d357, 0x17005a8d6a05a816, 0xd017215c057005c0, 0x5e857435]) else (cbits [0x60017c25f017c0, 0x18a0609182060058, 0x61194265018a5628, 0x6809a006])))) else (if j < 12 then (if j < 10 then (if j < 9 then (cbits [0x696d05b21691da40, 0x1d207481d207215b, 0x511d407485d20748, 0x7701dc07]) else (cbits [0x40778ddc17701dc0, 0xe0c07ac5e817909e, 0x6061428502121830, 0x86861a08])) else (if j < 11 then (cbits [0x38802200870a1c0, 0xa2a08a0628089862, 0xe823a08e823628a9, 0x8f823a28]) else (cbits [0x4490c64208f8a3e0, 0x66c09b026c09b026, 0xd827039b866e09b0, 0x9e027619]))) else (if j < 14 then (if j < 13 then (cbits [0x139f0a7c09e86781, 0x2aa8aa82aa0a98a8, 0xe82ba0ae82ba0ae8, 0xae9eba0a]) else (cbits [0xe4b28ac81b202c80, 0x3040c087001b5d6c, 0x483066c183041c10, 0xc703125c])) else (if j < 15 then (cbits [0xcf0b3c0cf031d0, 0xb409d003400d0034, 0x903640d59f560d48, 0xe183651d]) else (cbits [0xa7ea83aa0e247861, 0xee03a]))))) 14 (i % 16)
def s92Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 15 then (if j < 7 then (if j < 3 then (if j < 1 then (cbits [0x420090080200003f, 0x1806cbe01317803c, 0x402b54009d2c01f4, 0x8c56023146180c56, 0x327cb0c7f0631b90, 0xd90caf50]) else (if j < 2 then (cbits [0xbe6216a188386331, 0x824b1da62b73989d, 0x601b01003de692d7, 0xc540a31402009c0, 0x327060c7c1431b04, 0x80cac1c]) else (cbits [0x346210b988024331, 0xfa4b03c62b0e189c, 0xe92c0318804092d0, 0xa4f0163340498f00, 0x314088cf01e32806, 0xa0ca826]))) else (if j < 5 then (if j < 4 then (cbits [0x2a92c0898d812620, 0x31880300310b30e0, 0x603c0ca4b02a6310, 0x98803a6240ea4d03, 0x260ca4b02c63103, 0x118c7844]) else (cbits [0x5033c138cd84a32a, 0x6a4b05863d841880, 0xc93c1218f05cc381, 0x24b212620148ca84, 0x63c1518f056c3815, 0x1800a856])) else (if j < 6 then (cbits [0x9003c2200d866034, 0xca4ccb092c268c70, 0x20102f30e0ba9372, 0x1880680101918d86, 0x9311f24b07a6271e, 0x21a4f47e]) else (cbits [0x6e3141b00946a008, 0xd98c4726251c1880, 0xe31c1d24c0749301, 0x18a4720101c0c706, 0x1020a4f084c3c20, 0x2098a474])))) else (if j < 11 then (if j < 9 then (if j < 8 then (cbits [0x8a0102130f076010, 0x480a08e629231894, 0x46202624b09602a2, 0x80a8680281880789, 0x331278c6c9c31422, 0x291880a2]) else (cbits [0xae92c2b18aca6627, 0xb00d0a03341a8ca0, 0xa9342a00706e3281, 0xcf0783342a9890a, 0x402d00a0a462826, 0x298c708c])) else (if j < 10 then (cbits [0xb66342a0040b8c40, 0x900a0aa31c2d80a0, 0x89302b0c708e0341, 0x8030460082b98a0b, 0x363280acc002a26, 0x3480f4cc]) else (cbits [0xca32bb00caa46314, 0x51882d233db30cda, 0x62a36989cd66263, 0x18f0e86363898ace, 0x9333da4b0f263d3b, 0x4024dcf8]))) else (if j < 13 then (if j < 12 then (cbits [0xc633d3080d904c38, 0x8078c46303218d8, 0xc3183418a4ce028b, 0x19009e00c3618d09, 0xc3c280030de94837, 0x39b120e4]) else (cbits [0x48314120020ea630, 0x88030f092c3b98aa, 0x4636b18cd8c60362, 0x24f0a431837a4c8f, 0x3283e80a0a600c3c, 0x3f3102fa])) else (if j < 14 then (cbits [0xac00c3f98c0aa00c, 0x20ca0d00343200a0, 0xc9304098f2d0334b, 0x70ae3183fa4c0f, 0x364600d11401e42, 0x488ca920]) else (cbits [0x2892c4918f614620, 0x30c510a01e4ab0e1, 0x292c4418810e3314, 0x8cc616314458cf11, 0x1047a4b11c62046, 0x4980710a]))))) else (if j < 22 then (if j < 18 then (if j < 16 then (cbits [0x1032846810116028, 0x2802112328470cd1, 0x201a32804cc00121, 0xca6183144b80f52, 0x6204e0cf53033738, 0x5018d93c]) else (if j < 17 then (cbits [0x4693c5124d94292c, 0x3b0e14c9495224f5, 0x693c4c98d0c20105, 0x18d0c40104d18913, 0x124fa4f13a3284d, 0x4c8ca4c8]) else (cbits [0x3e620868c504c008, 0x480714ac4852b121, 0xe02a5680a15801e5, 0xc516092c8718815, 0x620878c515662055, 0x5880415c]))) else (if j < 20 then (if j < 19 then (cbits [0xcc01213802156328, 0x80c516e03d5980f0, 0x83355c0ca73031f8, 0x98a5746205c8cf4e, 0x92c5118d57a6315d, 0x5fb0e17c]) else (cbits [0x2231461312580c3d, 0xb30f56ac385a1882, 0x125a0cf0ce0105, 0x24d178624cc8c74d, 0x4860bd216a33c5e, 0x60bd216c])) else (if j < 21 then (cbits [0x8c01f24006988008, 0x40c519a02b6380a9, 0x63364b8cacd231f1, 0x1886246205b8cdd6, 0x637ce18af2462796, 0x6724b372]) else (cbits [0xa6c386924dda292d, 0x480218a92c899881, 0x620ce8c76283141, 0xa4d99492c6498d99, 0x31467803598c3865, 0x260c998a])))) else (if j < 26 then (if j < 24 then (if j < 23 then (cbits [0x2a92c5a18d854620, 0x480a1903346830e2, 0x6620660cd9960406, 0x803da0c388b24b05, 0x1fea806dac0136a, 0x6c009fac]) else (cbits [0x2e3146d80c5b202b, 0xd8c7cb031b168c54, 0xc3315d0cad603273, 0x189e5a6218b98819, 0x92ce718c77462bd8, 0x6f24b5ba])) else (if j < 25 then (cbits [0xb403c6b98f19e03c, 0xd0cdb9e026678069, 0x8c388c24b0306206, 0x18c4326206e0cc5b, 0x12e824c63292c68, 0xf00079c0]) else (cbits [0xc603d7100f1c2036, 0xf0ca5283250d0c51, 0x86258d1881a233d4, 0x24cba263dcf18a72, 0x3147330e1ca93672, 0x8d988036]))) else (if j < 28 then (if j < 27 then (cbits [0xf80132c803c38008, 0x40c7638314740074, 0x89357524d1c892cf, 0x8021d26343e8049d, 0x1d3f004cb800f0e, 0x8e8c51d2]) else (cbits [0x3c00875a4b3d231d, 0x75000132e803c, 0x403d5100d5760295, 0x8ca74031d8f0c51a, 0x620e90cf744335dd, 0x751891ca])) else (if j < 29 then (cbits [0xdec387724b1d8625, 0x8806de200f75a4c1, 0xc3150f8c51e4027f, 0x8c9d0431f2f0c6c5, 0x620698cc54e32b4a, 0x9718863e]) else (cbits [0xa6631d398af2a627, 0xa0099cc92d6ea4b3, 0x6205f0cd4403147, 0x24d5bc92cdf18d64, 0x77])))))) 22 (i % 16)
def s92Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then (cbits [0x3c080100203f00, 0x8628040270200d81, 0x2315024960318801, 0x219a058c6c08c781, 0x78c9c092781a31f0, 0x1940]) else (cbits [0x8cc4086782232b02, 0xd2582632a1318a09, 0x31183100130e04, 0x201e0d9884092583, 0x118ac092683a6270, 0x4960])) else (if j < 3 then (cbits [0x98880120292d02, 0x86544463c2418f11, 0x233c2219b1124f09, 0x261c14a4b0a46545, 0xb0e0892584463d2, 0x78]) else (cbits [0x18d8c40206202a30, 0x40106a0103401a18, 0xa6203518a1a8094d, 0x43189aa4c0e8c4a6, 0xa24b0d0c4e686203, 0x4989]))) else (if j < 6 then (if j < 5 then (cbits [0x30f1012788262940, 0x40208a0363049e9a, 0x203c30314a298951, 0x9015249881280509, 0x70c51386386092c4, 0x18da]) else (cbits [0x1881386629c33450, 0x9268a801c54313a7, 0x92c304962718ad3, 0xa31a2d80a1692666, 0xb0e0c126e60c405, 0x98])) else (if j < 7 then (cbits [0x98c18806cc202a60, 0x56c06366119eb0, 0x629670143380d98, 0xc3133018818007ac, 0x71901b8c4ec06346, 0x4a43]) else (cbits [0x30f1c8c56c062a60, 0xc60ea6366062439, 0x92c773153b98f18, 0x4963018d9e8c7ac, 0xfb101f4050fa9336, 0x3183])))) else (if j < 12 then (if j < 10 then (if j < 9 then (cbits [0xb0e180c790293760, 0x403d0a01c8400d80, 0xa62085198c28c521, 0x419e45807a112590, 0x69882346631a0348, 0x4964]) else (cbits [0x98f6106550803684, 0x58710892c8400e49, 0x23379701ecb807c0, 0x749e4c989268c693, 0xf98825c6513a33d9, 0x49e4])) else (if j < 11 then (cbits [0xa4da5d2592e63697, 0xd8914a93d9749e4b, 0x20270161c4ba5265, 0x9310550c52a80395, 0x49882b80515201ea, 0x155]) else (cbits [0x80ac040216292ca9, 0x187168620b401e59, 0x6329b301ed9b0f6d, 0xc314d99882cc67b6, 0x9a4b2ccc6366624b, 0x61c5]))) else (if j < 14 then (if j < 13 then (cbits [0xb126cde9182c3db3, 0x12598a008c401880, 0x620c801562007f1, 0x849b6424b320c6d9, 0x7a4b31005788c38c, 0x6e]) else (cbits [0x24df1125b88c38cf, 0x401faa6200161c62, 0xa027d531e6b804f5, 0xc018ea80f368057a, 0xa4b755259aac38d, 0x3108])) else (if j < 15 then (cbits [0xf38006dc0012e0, 0x126dc0932e001ef0, 0x201de831380b0e38, 0x849675a4d3a0c69d, 0x724b3b8c5602935e, 0x61c7]) else (cbits [0x809fc401fe292c01, 0x26f449680]))))) 21 (i % 16)
def s92Links := pageLinks s92Index s92Codes 5 13 8 6
def s92Data (i : Nat) : Nat × Nat :=
  let e := s92Forest i
  (e &&& 255, e >>> 8)
def s92Sample : Nat × Nat := (s92Blob411515, 96)
def s92Tags := dagTraceTags s92Mask 96 (dagTagBases s92StockWords s92Blob412086 s92Blob412302 96) 9 s92Data
def s92States := dagTrace s92Mask s92StockWords 9 s92Data
def s92MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm1, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val)))]
def s92Moves := dagMoves s92MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s92Autos : DagMovesOK s92Mask s92Goal 64 s92Moves := dagMovesOfCheck (by decide +kernel)
def s92Check := dagCheckNode s92Mask s92Goal s92Chart (dagKnownCloses s92Goal s92Cuts) 245 s92States s92Moves s92Links s92Sample s92Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s92Roots : dagCheckRoots s92Mask s92Goal s92Chart (dagKnownCloses s92Goal s92Cuts) s92Witnesses (dagRef 245 s92States s92Moves s92Links 0) s92StockWords 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s92Block0 : treeBlock 0 24 s92Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s92Block24 : treeBlock 24 24 s92Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s92Block48 : treeBlock 48 24 s92Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s92Block72 : treeBlock 72 24 s92Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s92Block96 : treeBlock 96 24 s92Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s92Block120 : treeBlock 120 24 s92Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s92Block144 : treeBlock 144 24 s92Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s92Block168 : treeBlock 168 24 s92Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s92Block192 : treeBlock 192 24 s92Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s92Block216 : treeBlock 216 24 s92Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s92Block240 : treeBlock 240 5 s92Check = true := by decide +kernel
theorem s92Group0_48 : treeBlock 0 48 s92Check = true := treeBlock_merge (start := 0) (left := 24) (right := 24) (check := s92Check) s92Block0 s92Block24
theorem s92Group72_48 : treeBlock 72 48 s92Check = true := treeBlock_merge (start := 72) (left := 24) (right := 24) (check := s92Check) s92Block72 s92Block96
theorem s92Group48_72 : treeBlock 48 72 s92Check = true := treeBlock_merge (start := 48) (left := 24) (right := 48) (check := s92Check) s92Block48 s92Group72_48
theorem s92Group0_120 : treeBlock 0 120 s92Check = true := treeBlock_merge (start := 0) (left := 48) (right := 72) (check := s92Check) s92Group0_48 s92Group48_72
theorem s92Group144_48 : treeBlock 144 48 s92Check = true := treeBlock_merge (start := 144) (left := 24) (right := 24) (check := s92Check) s92Block144 s92Block168
theorem s92Group120_72 : treeBlock 120 72 s92Check = true := treeBlock_merge (start := 120) (left := 24) (right := 48) (check := s92Check) s92Block120 s92Group144_48
theorem s92Group216_29 : treeBlock 216 29 s92Check = true := treeBlock_merge (start := 216) (left := 24) (right := 5) (check := s92Check) s92Block216 s92Block240
theorem s92Group192_53 : treeBlock 192 53 s92Check = true := treeBlock_merge (start := 192) (left := 24) (right := 29) (check := s92Check) s92Block192 s92Group216_29
theorem s92Group120_125 : treeBlock 120 125 s92Check = true := treeBlock_merge (start := 120) (left := 72) (right := 53) (check := s92Check) s92Group120_72 s92Group192_53
theorem s92Group0_245 : treeBlock 0 245 s92Check = true := treeBlock_merge (start := 0) (left := 120) (right := 125) (check := s92Check) s92Group0_120 s92Group120_125
theorem s92Blocks : treeBlock 0 245 s92Check = true := s92Group0_245
theorem s92Known : Known s92Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s65Stock) s91Stock) s52Stock) s90Stock) s64Stock) s56Stock) s63Stock) s43Stock) s85Stock) s89Stock) s88Stock) s87Stock) s86Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s92Stock : Lower s92Mask s92StockWords s92Goal 10 := by
  apply lowerDag _ _ _ _ s92Autos _ _ _ s92Known _ s92Roots s92Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s92Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s93Blob421835 : Nat := (cbits [0x34120d020140205, 0x422150904c221306, 0x2190a05824160a05, 0xa090683019088641, 0x894381e0e074301, 0xa44229048a448251, 0x6433188cc582d140, 0x36190d86835188d4, 0x190e87039188e468, 0xf0583c0e0f0703a, 0x4120500014703c1a, 0x2050a01422050601, 0xd02034020d120144, 0x84c580d0e034100, 0x5464131884c20130, 0x3815080540815008, 0x1602058681518854, 0x1a05864160e05820, 0x86428170905c2217, 0x4381908064101900, 0x1a0406870191886, 0xb1c068641a0e0682, 0xc06c241b0886c121, 0x74221d06074121d0, 0x241e06078301d0a0, 0x250e07c301e0a078, 0x1609440250209402])
def s93Blob422406 : Nat := (cbits [0x7ffffe067fe9cff, 0x99816330f87fc1ff, 0xf83fe07f81e0001, 0xffe1fffe1e4783cf, 0xe079fc0cfffc0007, 0xffffff80001f01f, 0xfffe001fff81fff0, 0xfffe00000fffffff, 0xf00000000000001f])
def s93Blob422619 : Nat := (cbits [0x22a1540229a0c55, 0x890021201014c089, 0x101100240100000, 0xad41aa8e1445828a, 0x4069d40caaa80844, 0x8cce6b502101c0d7, 0xf79c831bff81fbf0, 0xfff600000f73bde7, 0xc0003180c6190c1d])
def s93Mask : Nat := 0xffff3333ffff3333
abbrev s93Goal : Nat := sGoal &&& s93Mask
abbrev s93StockWords : List Nat := [0xaaaa2222aaaa2222, 0xcccc0000cccc0000, 0xf0f03030f0f03030, 0xff003300ff003300, 0xffff0000ffff0000, 0xffff333300000000]
def s93Fact : Nat × List Nat × Nat × Nat := (s93Mask, s93StockWords, 10, s93Goal)
def s93Cuts : List (Nat × List Nat × Nat × Nat) := [s54Fact, s87Fact, s88Fact, s89Fact, s43Fact, s4Fact, s59Fact, s65Fact]
def s93Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[5, 19, 22, 25, 26, 41, 60, 5, 19, 22, 25, 26, 9, 28, 44, 49, 50, 52, 56, 9, 28, 44, 49, 50], rfl⟩
def s93Witnesses := unpackWitnesses s93StockWords [2564, 271889, 526849, 799249, 1061385, 1331721]
def s93Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 4 then (if j < 2 then (if j < 1 then (cbits [0x31401400c801b001, 0x9018118017117014, 0x1e01d11a31911901]) else (cbits [0x2572412132101e3, 0xd02d02d02c12c02c, 0x3562f62e12e02d12])) else (if j < 3 then (cbits [0x3b13b03b03b03b0, 0x103f23e13d13c13c, 0x4804534504414134]) else (cbits [0x5805714cb4b1483, 0x5a65a05a058258, 0x6116106016006006]))) else (if j < 6 then (if j < 5 then (cbits [0x2684662660633621, 0x7006e26e06e06c, 0x7607607247207027]) else (cbits [0x8107f27f07f0769, 0x8388087182581181, 0x9909098f18b48b08])) else (if j < 7 then (cbits [0x29b09b09b09b0992, 0x40a319f49d29d09b, 0xbb1b83aaea46a40a]) else (if j < 8 then (cbits [0xbf2bd2bd0bc1bc0, 0x52c41c40c31c12c1, 0xcf0ce1cc2c84c71c]) else (cbits [0x2e0ade2de0de0cff, 0xed3ec1ec0ea]))))) 12 (i % 16)
def s93Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 7 then (if j < 3 then (if j < 1 then (cbits [0x260090080200003f, 0x1809c6201f0e806c, 0xe6272e98849e6202, 0xa4f4d893135a4b0c, 0x62001809c0401b41, 0x4988408]) else (if j < 2 then (cbits [0x1893105a4b014627, 0x324c40a92c08a4f4, 0xec3c03b0f01093d0, 0xa4b00c62002a4b00, 0x6200730f01ec3c06, 0x724b00e]) else (cbits [0x2492c04188020c38, 0xa009820c3c07b0f0, 0x92c0b0ca82a0320, 0x312434c3d0cb0e03, 0xf480dbd202e93c0e, 0xf007036]))) else (if j < 5 then (if j < 4 then (cbits [0x50c3813a4b04c32a, 0xf80785ec491530f4, 0x492c109880403140, 0x30f04a93d11a4c44, 0x3280f804048c3c12, 0x14804042]) else (cbits [0x5603411807044328, 0x200705893c16bd20, 0xa01c170100580341, 0x24f05af481800d04, 0x6201300682c00817, 0x1a24b064])) else (if j < 6 then (cbits [0x7893d1c24f06a932, 0x30f47ec381f2524, 0xc93c19a4f084c492, 0x98802e0081bb0f06, 0xc381b24c87292c19, 0x1db0f474]) else (cbits [0x74c3c1eb1207ac48, 0xbd206e93c1b24c0, 0x801c20bd20769482, 0x30f09492c2380a88, 0x93c2318808a31426, 0x24b0f090])))) else (if j < 11 then (if j < 9 then (if j < 8 then (cbits [0x9202a25b0f08c328, 0x730e09692c268cd8, 0x402728804ca000f2, 0xc9c30315020c50a, 0x93d2b24c4aa92c25, 0x29b0f0b6]) else (cbits [0xa6031029880a8c48, 0xba4b096331030c50, 0xe3142c30f0b2c3c2, 0xc4b4c382c24b00, 0xc3c2e24b0103142a, 0x2d30f0b2])) else (if j < 10 then (cbits [0x123142f80c8bc012, 0x124c864329138c94, 0xcc493230f4c6c383, 0xf0c2c483030f0c, 0xf483080f0caf4830, 0x50020ca]) else (cbits [0xc492c351880d001d, 0xc8c541631434a4f0, 0xa92c1f8cac503270, 0x241800831a4b4a, 0x2720007c5401b0d, 0x3980acda]))) else (if j < 13 then (if j < 12 then (cbits [0xc86212b188098031, 0xda4b0f262b3a989c, 0xc01c3fb0f0fa92d3, 0xb0f0e4f483800a0d, 0x28378070e2c3c37, 0x2680c0e2]) else (cbits [0xf0f483b24d0e8c48, 0xb1890ee9343ba4f0, 0xa3143b9890f4c483, 0x30f0ae92c270cc41, 0xf482c24b01c3143e, 0x78020fc])) else (if j < 14 then (cbits [0x8201f16806c36009, 0xdce802b39009c, 0x627329884b26204, 0x24b1026373d18acf, 0x3144130e0fc92d3e, 0x2d24b020]) else (cbits [0x5e01b0e002422008, 0xd98810802b21007c, 0xe92c4318accc6212, 0xbd2100c483fb0f10, 0x92c090c5102c4842, 0x4130f0b8]))))) 22 (i % 16)
def s93Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 4 then (if j < 2 then (if j < 1 then (cbits [0x6c080100203f00, 0x52580a6200201381, 0x493d0561e03a4c41, 0x249601189c08c420, 0x6b0f0392581a9310, 0x61e0]) else (cbits [0xa4b04927a04c3810, 0x64280261400480, 0x892c1449e0b8ca85, 0x47a40db0f4518702, 0xf80707803602c491, 0xf0])) else (if j < 3 then (cbits [0xa4b07cc403e3141f, 0x927a3ec3c244988f, 0x2c381e4960f0ca87, 0xc01a15b0f4780205, 0xf0100b9e905693c2, 0x6248]) else (cbits [0x9880c803e0203430, 0x92646492c3249e19, 0x293c3261e1b24f0d, 0x261e9cb0e0e52587, 0x92524c98907a93d3, 0x61c1]))) else (if j < 6 then (if j < 5 then (cbits [0xb124c9e9082c3d32, 0x46288a01c4401380, 0x93c480152218811, 0x461e25a4b1118789, 0xb0e13466c9ac3c4, 0x3100]) else (cbits [0x809d40026a000f50, 0x1258a0c485361e29, 0xec3c584962ba4c54, 0xc49ea830e169878a, 0xf004978c420292c5, 0x192])) else (if j < 7 then (cbits [0x24c979890c0c3c60, 0x9e90cac3d5e61c2f, 0x201d6831380b1257, 0x1496009881a1278d, 0x78071b804eda9310, 0x61e3]) else (if j < 8 then (cbits [0xbd21b9878e20286e, 0x8c4edac4874015b6, 0xaf487649e3ba4d1d, 0xc49636b121e8c56d, 0x6bd21f925adac3c7, 0x61e3]) else (cbits [0xb0e200c6f0003780, 0x1e910a02b8449e80, 0x4964218ae1]))))) 21 (i % 16)
def s93Links := pageLinks s93Index s93Codes 4 13 8 5
def s93Data (i : Nat) : Nat × Nat :=
  let e := s93Forest i
  (e &&& 255, e >>> 8)
def s93Sample : Nat × Nat := (s93Blob421835, 96)
def s93Tags := dagTraceTags s93Mask 96 (dagTagBases s93StockWords s93Blob422406 s93Blob422619 96) 9 s93Data
def s93States := dagTrace s93Mask s93StockWords 9 s93Data
def s93MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s93Moves := dagMoves s93MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s93Autos : DagMovesOK s93Mask s93Goal 64 s93Moves := dagMovesOfCheck (by decide +kernel)
def s93Check := dagCheckNode s93Mask s93Goal s93Chart (dagKnownCloses s93Goal s93Cuts) 136 s93States s93Moves s93Links s93Sample s93Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s93Roots : dagCheckRoots s93Mask s93Goal s93Chart (dagKnownCloses s93Goal s93Cuts) s93Witnesses (dagRef 136 s93States s93Moves s93Links 0) s93StockWords 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s93Block0 : treeBlock 0 24 s93Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s93Block24 : treeBlock 24 24 s93Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s93Block48 : treeBlock 48 24 s93Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s93Block72 : treeBlock 72 24 s93Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s93Block96 : treeBlock 96 24 s93Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s93Block120 : treeBlock 120 16 s93Check = true := by decide +kernel
theorem s93Group24_48 : treeBlock 24 48 s93Check = true := treeBlock_merge (start := 24) (left := 24) (right := 24) (check := s93Check) s93Block24 s93Block48
theorem s93Group0_72 : treeBlock 0 72 s93Check = true := treeBlock_merge (start := 0) (left := 24) (right := 48) (check := s93Check) s93Block0 s93Group24_48
theorem s93Group96_40 : treeBlock 96 40 s93Check = true := treeBlock_merge (start := 96) (left := 24) (right := 16) (check := s93Check) s93Block96 s93Block120
theorem s93Group72_64 : treeBlock 72 64 s93Check = true := treeBlock_merge (start := 72) (left := 24) (right := 40) (check := s93Check) s93Block72 s93Group96_40
theorem s93Group0_136 : treeBlock 0 136 s93Check = true := treeBlock_merge (start := 0) (left := 72) (right := 64) (check := s93Check) s93Group0_72 s93Group72_64
theorem s93Blocks : treeBlock 0 136 s93Check = true := s93Group0_136
theorem s93Known : Known s93Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s65Stock) s59Stock) s4Stock) s43Stock) s89Stock) s88Stock) s87Stock) s54Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s93Stock : Lower s93Mask s93StockWords s93Goal 10 := by
  apply lowerDag _ _ _ _ s93Autos _ _ _ s93Known _ s93Roots s93Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s93Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s94Mask : Nat := 0xffff5555ffff5555
abbrev s94Goal : Nat := sGoal &&& s94Mask
abbrev s94StockWords : List Nat := [0xaaaa0000aaaa0000, 0xcccc4444cccc4444, 0xf0f05050f0f05050, 0xff005500ff005500, 0xffff0000ffff0000, 0xffff555500000000]
def s94Fact : Nat × List Nat × Nat × Nat := (s94Mask, s94StockWords, 10, s94Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s94Stock : Lower s94Mask s94StockWords s94Goal 10 := dagShiftLower (width := 64) pm1 s93Stock (by decide +kernel)
def s95Mask : Nat := 0xffffffff00000000
abbrev s95Goal : Nat := sGoal &&& s95Mask
abbrev s95StockWords : List Nat := [0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf0f0f0f000000000, 0xff00ff0000000000, 0xffff000000000000]
def s95Fact : Nat × List Nat × Nat × Nat := (s95Mask, s95StockWords, 8, s95Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s95Stock : Lower s95Mask s95StockWords s95Goal 8 := dagShiftLower (width := 64) pm6 s87Stock (by decide +kernel)
def s96Blob432309 : Nat := (cbits [0x82c060b0181c0205, 0x422130184c120d04, 0x6230886412190885, 0x51089444231088c0, 0x48a4482611098482, 0xa8442a140a442290, 0x6233160b8582d140, 0x361a0d46235190cc, 0x1c0e462391a0d864, 0xf0583c1c0e8643a, 0x4120501814703c1a, 0x2071201442050881, 0xf16034020d0082c0, 0x884c02130483c060, 0x5462150085464131, 0x2190885c06171a0, 0x1b0186c701918864, 0x8874121d0886c12, 0x8c62231008c0223, 0x4582510094022519, 0x8261009868251889, 0x70189c6826190985, 0x8a448271109c422, 0xa46229160a440290, 0x642a160a8402a1c0, 0x2b048ac062b1c0a8, 0x48b4502b110ac42])
def s96Blob432879 : Nat := (cbits [0xffffffe0cf4e7fff, 0x33b19c6efc3fe1ff, 0x7fc1fe0f38c7cc03, 0xc0f8f7fc3cc1e093, 0xc0fe031c8001fff0, 0xfffe0000ff00f81f, 0xffff001fff0003e0, 0xfffffc0000000000, 0xffffffff0000001f])
def s96Blob433095 : Nat := (cbits [0xfbdbdde045062fff, 0x121094269c126095, 0x2500a80808444021, 0x20220c28c14000, 0x80ea011800891540, 0xcaa804405400a056, 0xa6b6009bff0002c0, 0xfffdf8000330198c, 0x73fddfee0636231f])
def s96Mask : Nat := 0xffffffffaaaaaaaa
abbrev s96Goal : Nat := sGoal &&& s96Mask
abbrev s96StockWords : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcccccccc88888888, 0xf0f0f0f0a0a0a0a0, 0xff00ff00aa00aa00, 0xffff0000aaaa0000, 0xffffffff00000000]
def s96Fact : Nat × List Nat × Nat × Nat := (s96Mask, s96StockWords, 10, s96Goal)
def s96Cuts : List (Nat × List Nat × Nat × Nat) := [s95Fact, s26Fact, s85Fact, s43Fact, s73Fact, s57Fact, s23Fact, s53Fact, s66Fact]
def s96Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[5, 11, 19, 25, 35, 38, 41, 42, 60, 5, 11, 19, 3, 9, 44, 49, 50, 52, 56, 3, 9, 44, 49, 50], rfl⟩
def s96Witnesses := unpackWitnesses s96StockWords [17954, 267785, 526849, 792067, 1058307, 1328643]
def s96Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 6 then (if j < 3 then (if j < 1 then (cbits [0x200f882c900d4001, 0x421108042010804, 0x2004801108440110, 0x13004821]) else (if j < 2 then (cbits [0x61158056014884c3, 0x464019005a516045, 0xa146611980660190, 0x1d007211]) else (cbits [0xc61e087801d08740, 0x88c023008c022087, 0x4049002400900230, 0x25809222]))) else (if j < 4 then (cbits [0x402884a202804965, 0x8a812a00a422900a, 0xd80b602d80b602a9, 0x2d80b602]) else (if j < 5 then (cbits [0x203004c002f84b64, 0xea0390cc6f3088c, 0xd00ea53a80ea03a8, 0x3d00f403]) else (cbits [0x453d00f403d00f40, 0x8fe13f80fe03f80f, 0x10d0404101040400, 0x42850a04])))) else (if j < 9 then (if j < 7 then (cbits [0x604d8117045810c5, 0x53e04f813644d813, 0xd40050014004f8, 0x51a14605]) else (if j < 8 then (cbits [0x8056015615581560, 0x5620580558456015, 0xa016425901640588, 0x5e816895]) else (cbits [0xa05e817a05e817a0, 0x18c463018a15ea17, 0x5019406501940650, 0x66359426]))) else (if j < 10 then (cbits [0x616d81b416d01b21, 0x5ba06e05b806e01b, 0x801c6d7105c406e9, 0x7809e007]) else (if j < 11 then (cbits [0x807b19ec07911e40, 0x1fc17f01fc07e09f, 0x1aa06081820607f9, 0x86821a08]) else (cbits [0x20908240190021b3, 0x242c908242090824, 0x25a0968]))))) 14 (i % 16)
def s96Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 9 then (if j < 4 then (if j < 2 then (if j < 1 then (cbits [0x1e0090080200003f, 0x1806c380130a803c, 0xe02b1c009c5e01f1, 0xc54c23142280f47, 0x3273e8c7cea31b37, 0x470cad08]) else (cbits [0x5062751188536620, 0xba4b55e92c5618ad, 0xc31f028c54043145, 0x18801232b038c9c0, 0x92d06a4b01862b05, 0x198801c])) else (if j < 3 then (cbits [0x6620040ca00892c, 0x5a4b00862005a4b0, 0x8c38099880203480, 0x992024c380898802, 0x360b00a82464808, 0xc0c702e]) else (cbits [0x3292c0db0e03492c, 0xe8c503000c0c98a0, 0x4c381019203e6320, 0xb0e03c3140f19204, 0x1c10a5203231810, 0x13807848]))) else (if j < 6 then (if j < 5 then (cbits [0x586201580d850034, 0x324b04a31416b0e0, 0x23341524b0523141, 0xc504c3281700405, 0x9481a24c86433718, 0x1bb0e06a]) else (cbits [0x6231419a4f062948, 0xc80786cc481b30e0, 0x86201d8cd87402a1, 0x80987cc381ea4b07, 0xc482124b0803141d, 0x20b12088])) else (if j < 7 then (cbits [0x8692c208c5086c48, 0x580a89401f230020, 0x3142900dca202b2, 0x98acac6212998802, 0x92c2d98dcb06332b, 0x2f24dcb8]) else (if j < 8 then (cbits [0x8e6203030e4bec38, 0x60c5092c382424b0, 0xe92c2718d89a31d2, 0xca88e3142830e09, 0xc382a24b02262026, 0x2680a0aa]) else (cbits [0x903142d18d0b201c, 0x700a0bac382a24b0, 0x4620280cd8923142, 0x3cbac382aa4b02, 0x31432009cc601b31, 0x98c5404]))))) else (if j < 14 then (if j < 11 then (if j < 10 then (cbits [0x78327180c7c5831b, 0x29880a633d200cac, 0x662b35189cd06213, 0xf4da92d3624b0d, 0x92c2a18f40662033, 0x348120ce]) else (cbits [0xce92c2a98f408620, 0xe8c740a3143780c8, 0x26363818a8ac3490, 0x3120e8c3839a4b0e, 0x3363c0cd0ec01039, 0x3db0e0f4])) else (if j < 12 then (cbits [0xf801c3ca4b0ee92c, 0xb81240c0083b8c70, 0xe6363f1880e03142, 0x24d9029324024b0f, 0x1003802106c3841, 0x2c01250a]) else (if j < 13 then (cbits [0x16636450ca90e328, 0x324b11ac384624b1, 0x6202d00f4100084, 0x98d10c31c44a4b11, 0x4919007c1200844, 0x388c50b6]) else (cbits [0x2262947988116326, 0xab0e12692c4118d5, 0x4c494c31212cc3d4, 0x3121249484831213, 0x620390c512ef484a, 0x4918a520])))) else (if j < 16 then (if j < 15 then (cbits [0x2ef484a24b132635, 0xf00f53a0274e006d, 0xa3270d0c6c143144, 0x9884ca6202e0cf47, 0x92c4798ad1862739, 0x50a4b540]) else (cbits [0x3e33d4fb0e0cc92c, 0x3a4b0ba63d059881, 0x620520121460323, 0xb0e14c9363f18a4d, 0x34852b0e0d262053, 0x350c514a])) else (if j < 17 then (cbits [0x56c385524d95231d, 0x58c50bc049060021, 0x4335488ca4fe31d3, 0xa4b1546265318810, 0x1358003d5cc3856, 0x59806d62]) else (if j < 18 then (cbits [0x6c02b5a809d6801f, 0xd8c6c28315068c51, 0xe32b168c9c4431f0, 0x1884d86202f8cf46, 0x92c4198acf66273a, 0x53a4b540]) else (cbits [0x7202a5c007964648, 0x10cd47c331070c51, 0xa631369880c03492, 0xa4c54292c4998d51, 0x15a93555])))))) 22 (i % 16)
def s96Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 6 then (if j < 3 then (if j < 1 then (cbits [0x8c50080100203f00, 0x862a0492c0331001, 0x432808193810c7c0, 0x2496059880086560, 0xa4b4092580462b0, 0x48]) else (if j < 2 then (cbits [0x30e044c402234810, 0x801e02c381031008, 0x231c1601b0b00a85, 0x161c0b24b0592583, 0xe9920786283a0130, 0x3190]) else (cbits [0xb0e075870426481d, 0x46284a01c2400d80, 0x20342400f1224b09, 0x401b1224b0a46285, 0x8040b9870486202, 0xf8]))) else (if j < 4 then (cbits [0x8cdcc12906231430, 0x9290609323049e19, 0x20270161c1830e0d, 0x919b1c80a8e403c7, 0xb0e0e5258726203, 0x158]) else (if j < 5 then (cbits [0xa4b1018908231440, 0x807a02c484062421, 0xe92c473102380211, 0xc01523007d198708, 0x618d93063a983144, 0x4962]) else (cbits [0xdd180568cc384c, 0x9870a892c5431023, 0x263346315a318851, 0x631ba318d164038b, 0x324dd19870ba92c4, 0x61c2])))) else (if j < 9 then (if j < 7 then (cbits [0x3d8862802c3946, 0x8c40c40276200db1, 0x2621624963300f59, 0x2315b1189d88090d, 0x78c540525ac492c6, 0x193]) else (if j < 8 then (cbits [0xb121c8c6cde62a6f, 0x863602c386f49637, 0x2334764963b8041d, 0xc61c3b0cd9d9258f, 0xf1881f863e0201c7, 0x31b3]) else (cbits [0x24d9f9264fc92c7e, 0x80210a3270161c3f, 0x6208819442a4b21, 0x531b428caa152591, 0x78cac058710a92c8, 0x3104]))) else (if j < 10 then (cbits [0xa52248c531ec4890, 0xd8711ec489449647, 0x2c488f7a44bb0f63, 0xc31000b1263cc6b3, 0xf80f67004f3801b9, 0x61c4]) else (if j < 11 then (cbits [0x98840525b3892c9c, 0xd8714a048a301951, 0x26270161c51a4da8, 0x161c54a4daa463b5, 0xb0e2b52595a62b0, 0x4960]) else (cbits [0x1922c80276000fb0, 0x4f6001fb000dd8, 0x1eb84968080aec, 0x557]))))) 21 (i % 16)
def s96Links := pageLinks s96Index s96Codes 5 13 8 6
def s96Data (i : Nat) : Nat × Nat :=
  let e := s96Forest i
  (e &&& 255, e >>> 8)
def s96Sample : Nat × Nat := (s96Blob432309, 96)
def s96Tags := dagTraceTags s96Mask 96 (dagTagBases s96StockWords s96Blob432879 s96Blob433095 96) 9 s96Data
def s96States := dagTrace s96Mask s96StockWords 9 s96Data
def s96MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s96Moves := dagMoves s96MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Autos : DagMovesOK s96Mask s96Goal 64 s96Moves := dagMovesOfCheck (by decide +kernel)
def s96Check := dagCheckNode s96Mask s96Goal s96Chart (dagKnownCloses s96Goal s96Cuts) 186 s96States s96Moves s96Links s96Sample s96Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Roots : dagCheckRoots s96Mask s96Goal s96Chart (dagKnownCloses s96Goal s96Cuts) s96Witnesses (dagRef 186 s96States s96Moves s96Links 0) s96StockWords 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block0 : treeBlock 0 24 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block24 : treeBlock 24 24 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block48 : treeBlock 48 24 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block72 : treeBlock 72 24 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block96 : treeBlock 96 24 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block120 : treeBlock 120 24 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block144 : treeBlock 144 24 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block168 : treeBlock 168 18 s96Check = true := by decide +kernel
theorem s96Group0_48 : treeBlock 0 48 s96Check = true := treeBlock_merge (start := 0) (left := 24) (right := 24) (check := s96Check) s96Block0 s96Block24
theorem s96Group48_48 : treeBlock 48 48 s96Check = true := treeBlock_merge (start := 48) (left := 24) (right := 24) (check := s96Check) s96Block48 s96Block72
theorem s96Group0_96 : treeBlock 0 96 s96Check = true := treeBlock_merge (start := 0) (left := 48) (right := 48) (check := s96Check) s96Group0_48 s96Group48_48
theorem s96Group96_48 : treeBlock 96 48 s96Check = true := treeBlock_merge (start := 96) (left := 24) (right := 24) (check := s96Check) s96Block96 s96Block120
theorem s96Group144_42 : treeBlock 144 42 s96Check = true := treeBlock_merge (start := 144) (left := 24) (right := 18) (check := s96Check) s96Block144 s96Block168
theorem s96Group96_90 : treeBlock 96 90 s96Check = true := treeBlock_merge (start := 96) (left := 48) (right := 42) (check := s96Check) s96Group96_48 s96Group144_42
theorem s96Group0_186 : treeBlock 0 186 s96Check = true := treeBlock_merge (start := 0) (left := 96) (right := 90) (check := s96Check) s96Group0_96 s96Group96_90
theorem s96Blocks : treeBlock 0 186 s96Check = true := s96Group0_186
theorem s96Known : Known s96Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s66Stock) s53Stock) s23Stock) s57Stock) s73Stock) s43Stock) s85Stock) s26Stock) s95Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Stock : Lower s96Mask s96StockWords s96Goal 10 := by
  apply lowerDag _ _ _ _ s96Autos _ _ _ s96Known _ s96Roots s96Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s96Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s97Mask : Nat := 0xffffaaaaffffaaaa
abbrev s97Goal : Nat := sGoal &&& s97Mask
abbrev s97StockWords : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcccc8888cccc8888, 0xf0f0a0a0f0f0a0a0, 0xff00aa00ff00aa00, 0xffff0000ffff0000, 0xffffaaaa00000000]
def s97Fact : Nat × List Nat × Nat × Nat := (s97Mask, s97StockWords, 10, s97Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s97Stock : Lower s97Mask s97StockWords s97Goal 10 := dagShiftLower (width := 64) pm6 s96Stock (by decide +kernel)
def s98Mask : Nat := 0xffffccccffffcccc
abbrev s98Goal : Nat := sGoal &&& s98Mask
abbrev s98StockWords : List Nat := [0xaaaa8888aaaa8888, 0xcccccccccccccccc, 0xf0f0c0c0f0f0c0c0, 0xff00cc00ff00cc00, 0xffff0000ffff0000, 0xffffcccc00000000]
def s98Fact : Nat × List Nat × Nat × Nat := (s98Mask, s98StockWords, 10, s98Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s98Stock : Lower s98Mask s98StockWords s98Goal 10 := dagShiftLower (width := 64) pm24 s96Stock (by decide +kernel)
def s99Mask : Nat := 0xffffff00ffffff00
abbrev s99Goal : Nat := sGoal &&& s99Mask
abbrev s99StockWords : List Nat := [0xaaaaaa00aaaaaa00, 0xcccccc00cccccc00, 0xf0f0f000f0f0f000, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffff0000000000]
def s99Fact : Nat × List Nat × Nat × Nat := (s99Mask, s99StockWords, 10, s99Goal)
def s99Witnesses := unpackWitnesses s99StockWords [5642, 267785, 530953, 799249, 1061385, 1331721]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s99Stock : Lower s99Mask s99StockWords s99Goal 10 := by
  apply essentialLift (witnesses := s99Witnesses) (cut := s11Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s11StockWords) (by decide +kernel)
  · exact s11Stock
  · decide +kernel
def s100Mask : Nat := 0xffffffff00ff00ff
abbrev s100Goal : Nat := sGoal &&& s100Mask
abbrev s100StockWords : List Nat := [0xaaaaaaaa00aa00aa, 0xcccccccc00cc00cc, 0xf0f0f0f000f000f0, 0xff00ff0000000000, 0xffff000000ff0000, 0xffffffff00000000]
def s100Fact : Nat × List Nat × Nat × Nat := (s100Mask, s100StockWords, 10, s100Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s100Stock : Lower s100Mask s100StockWords s100Goal 10 := dagShiftLower (width := 64) pm6 s92Stock (by decide +kernel)
def s101Mask : Nat := 0xffffffff33333333
abbrev s101Goal : Nat := sGoal &&& s101Mask
abbrev s101StockWords : List Nat := [0xaaaaaaaa22222222, 0xcccccccc00000000, 0xf0f0f0f030303030, 0xff00ff0033003300, 0xffff000033330000, 0xffffffff00000000]
def s101Fact : Nat × List Nat × Nat × Nat := (s101Mask, s101StockWords, 10, s101Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s101Stock : Lower s101Mask s101StockWords s101Goal 10 := dagShiftLower (width := 64) pm6 s93Stock (by decide +kernel)
def s102Mask : Nat := 0xffffffff55555555
abbrev s102Goal : Nat := sGoal &&& s102Mask
abbrev s102StockWords : List Nat := [0xaaaaaaaa00000000, 0xcccccccc44444444, 0xf0f0f0f050505050, 0xff00ff0055005500, 0xffff000055550000, 0xffffffff00000000]
def s102Fact : Nat × List Nat × Nat × Nat := (s102Mask, s102StockWords, 10, s102Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s102Stock : Lower s102Mask s102StockWords s102Goal 10 := dagShiftLower (width := 64) pm24 s93Stock (by decide +kernel)
def s103Mask : Nat := 0xffffffffcccccccc
abbrev s103Goal : Nat := sGoal &&& s103Mask
abbrev s103StockWords : List Nat := [0xaaaaaaaa88888888, 0xcccccccccccccccc, 0xf0f0f0f0c0c0c0c0, 0xff00ff00cc00cc00, 0xffff0000cccc0000, 0xffffffff00000000]
def s103Fact : Nat × List Nat × Nat × Nat := (s103Mask, s103StockWords, 10, s103Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s103Stock : Lower s103Mask s103StockWords s103Goal 10 := dagShiftLower (width := 64) pm1 s96Stock (by decide +kernel)
def s104Mask : Nat := 0xffffffffff00ff00
abbrev s104Goal : Nat := sGoal &&& s104Mask
abbrev s104StockWords : List Nat := [0xaaaaaaaaaa00aa00, 0xcccccccccc00cc00, 0xf0f0f0f0f000f000, 0xff00ff00ff00ff00, 0xffff0000ff000000, 0xffffffff00000000]
def s104Fact : Nat × List Nat × Nat × Nat := (s104Mask, s104StockWords, 10, s104Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s104Stock : Lower s104Mask s104StockWords s104Goal 10 := dagShiftLower (width := 64) pm6 s99Stock (by decide +kernel)
def s105Mask : Nat := 0xffffffffffff
abbrev s105Goal : Nat := sGoal &&& s105Mask
abbrev s105StockWords : List Nat := [0xaaaaaaaaaaaa, 0xcccccccccccc, 0xf0f0f0f0f0f0, 0xff00ff00ff00, 0xffff0000, 0xffff00000000]
def s105Fact : Nat × List Nat × Nat × Nat := (s105Mask, s105StockWords, 9, s105Goal)
def s105Witnesses := unpackWitnesses s105StockWords [2564, 265220, 526849, 792067, 1058307, 1328643]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s105Stock : Lower s105Mask s105StockWords s105Goal 9 := by
  apply essentialLift (witnesses := s105Witnesses) (cut := s15Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s15StockWords) (by decide +kernel)
  · exact s15Stock
  · decide +kernel
def s106Mask : Nat := 0xff00ffffffffff
abbrev s106Goal : Nat := sGoal &&& s106Mask
abbrev s106StockWords : List Nat := [0xaa00aaaaaaaaaa, 0xcc00cccccccccc, 0xf000f0f0f0f0f0, 0xff00ff00, 0xff0000ffff0000, 0xff00ff00000000]
def s106Fact : Nat × List Nat × Nat × Nat := (s106Mask, s106StockWords, 9, s106Goal)
def s106Witnesses := unpackWitnesses s106StockWords [2564, 265220, 526849, 792067, 1058307, 1328643]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s106Stock : Lower s106Mask s106StockWords s106Goal 9 := by
  apply essentialLift (witnesses := s106Witnesses) (cut := s15Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s15StockWords) (by decide +kernel)
  · exact s15Stock
  · decide +kernel
def s107Mask : Nat := 0xffffff00ffffff
abbrev s107Goal : Nat := sGoal &&& s107Mask
abbrev s107StockWords : List Nat := [0xaaaaaa00aaaaaa, 0xcccccc00cccccc, 0xf0f0f000f0f0f0, 0xff000000ff00, 0xff000000ff0000, 0xffffff00000000]
def s107Fact : Nat × List Nat × Nat × Nat := (s107Mask, s107StockWords, 9, s107Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107Stock : Lower s107Mask s107StockWords s107Goal 9 := dagShiftLower (width := 64) pm6 s106Stock (by decide +kernel)
def s108Mask : Nat := 0xf0f0f0fffffffff
abbrev s108Goal : Nat := sGoal &&& s108Mask
abbrev s108StockWords : List Nat := [0xa0a0a0aaaaaaaaa, 0xc0c0c0ccccccccc, 0xf0f0f0f0, 0xf000f00ff00ff00, 0xf0f0000ffff0000, 0xf0f0f0f00000000]
def s108Fact : Nat × List Nat × Nat × Nat := (s108Mask, s108StockWords, 9, s108Goal)
def s108Witnesses := unpackWitnesses s108StockWords [2564, 265220, 526849, 792067, 1058307, 1328643]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s108Stock : Lower s108Mask s108StockWords s108Goal 9 := by
  apply essentialLift (witnesses := s108Witnesses) (cut := s15Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s15StockWords) (by decide +kernel)
  · exact s15Stock
  · decide +kernel
def s109Mask : Nat := 0xf0fffff0f0fffff
abbrev s109Goal : Nat := sGoal &&& s109Mask
abbrev s109StockWords : List Nat := [0xa0aaaaa0a0aaaaa, 0xc0ccccc0c0ccccc, 0xf0f00000f0f0, 0xf00ff000f00ff00, 0xf0f00000f0f0000, 0xf0fffff00000000]
def s109Fact : Nat × List Nat × Nat × Nat := (s109Mask, s109StockWords, 9, s109Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s109Stock : Lower s109Mask s109StockWords s109Goal 9 := dagShiftLower (width := 64) pm6 s108Stock (by decide +kernel)
def s110Mask : Nat := 0xfff0fff0fff0fff
abbrev s110Goal : Nat := sGoal &&& s110Mask
abbrev s110StockWords : List Nat := [0xaaa0aaa0aaa0aaa, 0xccc0ccc0ccc0ccc, 0xf000f000f000f0, 0xf000f000f000f00, 0xfff00000fff0000, 0xfff0fff00000000]
def s110Fact : Nat × List Nat × Nat × Nat := (s110Mask, s110StockWords, 9, s110Goal)
def s110Witnesses := unpackWitnesses s110StockWords [2564, 265220, 526849, 792067, 1058307, 1328643]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s110Stock : Lower s110Mask s110StockWords s110Goal 9 := by
  apply essentialLift (witnesses := s110Witnesses) (cut := s15Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s15StockWords) (by decide +kernel)
  · exact s15Stock
  · decide +kernel
def s111Mask : Nat := 0x7777777777777777
abbrev s111Goal : Nat := sGoal &&& s111Mask
abbrev s111StockWords : List Nat := [0x2222222222222222, 0x4444444444444444, 0x7070707070707070, 0x7700770077007700, 0x7777000077770000, 0x7777777700000000]
def s111Fact : Nat × List Nat × Nat × Nat := (s111Mask, s111StockWords, 9, s111Goal)
def s111Witnesses := unpackWitnesses s111StockWords [2564, 265220, 526849, 799249, 1061385, 1331721]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s111Stock : Lower s111Mask s111StockWords s111Goal 9 := by
  apply essentialLift (witnesses := s111Witnesses) (cut := s54Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s54StockWords) (by decide +kernel)
  · exact s54Stock
  · decide +kernel
def s112Mask : Nat := 0xaaaaaaaaffffffff
abbrev s112Goal : Nat := sGoal &&& s112Mask
abbrev s112StockWords : List Nat := [0xaaaaaaaaaaaaaaaa, 0x88888888cccccccc, 0xa0a0a0a0f0f0f0f0, 0xaa00aa00ff00ff00, 0xaaaa0000ffff0000, 0xaaaaaaaa00000000]
def s112Fact : Nat × List Nat × Nat × Nat := (s112Mask, s112StockWords, 9, s112Goal)
def s112Witnesses := unpackWitnesses s112StockWords [2564, 265220, 526849, 792067, 1058307, 1328643]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s112Stock : Lower s112Mask s112StockWords s112Goal 9 := by
  apply essentialLift (witnesses := s112Witnesses) (cut := s15Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s15StockWords) (by decide +kernel)
  · exact s15Stock
  · decide +kernel
def s113Mask : Nat := 0xaaaaffffaaaaffff
abbrev s113Goal : Nat := sGoal &&& s113Mask
abbrev s113StockWords : List Nat := [0xaaaaaaaaaaaaaaaa, 0x8888cccc8888cccc, 0xa0a0f0f0a0a0f0f0, 0xaa00ff00aa00ff00, 0xaaaa0000aaaa0000, 0xaaaaffff00000000]
def s113Fact : Nat × List Nat × Nat × Nat := (s113Mask, s113StockWords, 9, s113Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s113Stock : Lower s113Mask s113StockWords s113Goal 9 := dagShiftLower (width := 64) pm6 s112Stock (by decide +kernel)
def s114Mask : Nat := 0xafafafafafafafaf
abbrev s114Goal : Nat := sGoal &&& s114Mask
abbrev s114StockWords : List Nat := [0xaaaaaaaaaaaaaaaa, 0x8c8c8c8c8c8c8c8c, 0xa0a0a0a0a0a0a0a0, 0xaf00af00af00af00, 0xafaf0000afaf0000, 0xafafafaf00000000]
def s114Fact : Nat × List Nat × Nat × Nat := (s114Mask, s114StockWords, 9, s114Goal)
def s114Witnesses := unpackWitnesses s114StockWords [5642, 267785, 526849, 792067, 1058307, 1328643]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s114Stock : Lower s114Mask s114StockWords s114Goal 9 := by
  apply essentialLift (witnesses := s114Witnesses) (cut := s15Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s15StockWords) (by decide +kernel)
  · exact s15Stock
  · decide +kernel
def s115Mask : Nat := 0xccccccccffffffff
abbrev s115Goal : Nat := sGoal &&& s115Mask
abbrev s115StockWords : List Nat := [0x88888888aaaaaaaa, 0xcccccccccccccccc, 0xc0c0c0c0f0f0f0f0, 0xcc00cc00ff00ff00, 0xcccc0000ffff0000, 0xcccccccc00000000]
def s115Fact : Nat × List Nat × Nat × Nat := (s115Mask, s115StockWords, 9, s115Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s115Stock : Lower s115Mask s115StockWords s115Goal 9 := dagShiftLower (width := 64) pm1 s112Stock (by decide +kernel)
def s116Mask : Nat := 0xccccffffccccffff
abbrev s116Goal : Nat := sGoal &&& s116Mask
abbrev s116StockWords : List Nat := [0x8888aaaa8888aaaa, 0xcccccccccccccccc, 0xc0c0f0f0c0c0f0f0, 0xcc00ff00cc00ff00, 0xcccc0000cccc0000, 0xccccffff00000000]
def s116Fact : Nat × List Nat × Nat × Nat := (s116Mask, s116StockWords, 9, s116Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s116Stock : Lower s116Mask s116StockWords s116Goal 9 := dagShiftLower (width := 64) pm24 s112Stock (by decide +kernel)
def s117Mask : Nat := 0xcfcfcfcfcfcfcfcf
abbrev s117Goal : Nat := sGoal &&& s117Mask
abbrev s117StockWords : List Nat := [0x8a8a8a8a8a8a8a8a, 0xcccccccccccccccc, 0xc0c0c0c0c0c0c0c0, 0xcf00cf00cf00cf00, 0xcfcf0000cfcf0000, 0xcfcfcfcf00000000]
def s117Fact : Nat × List Nat × Nat × Nat := (s117Mask, s117StockWords, 9, s117Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s117Stock : Lower s117Mask s117StockWords s117Goal 9 := dagShiftLower (width := 64) pm1 s114Stock (by decide +kernel)
def s118Blob475157 : Nat := (cbits [0x180406020140205, 0xc180e06034060702, 0x2150904c22130184, 0xd0a05824160a0542, 0x88c06230e078381, 0x9848251089444231, 0x582e160b44826110, 0x35188d46433188cc, 0xe0f06836190d868, 0x81400051a0f0583c, 0x4280508814180501, 0x6060001848051081, 0x60a0182406060180, 0x101c020712018440, 0x34080d0083408070, 0x80e01038580d0e0, 0xf0183c580e0e038, 0x804c04130084c18, 0x5402151904c6213, 0x462150e054201502, 0x160205804161a05, 0x71a05864160e0582, 0xa05c24170885c061, 0x78281d08874181d0, 0x381f0a078241e060, 0x231008c04230088c, 0x209402251908c62])
def s118Blob475725 : Nat := (cbits [0xf87f01fc1e9f4fb3, 0x6767b3dcff1fc0ff, 0x3fe3ff03ff87fe00, 0x1ffffffff9f8fc7f, 0x8180c060c1fffffc, 0x1fc00001ff80003, 0xe0000003fe00ff80, 0xffff000001ffffff, 0xfe00000000000003])
def s118Blob475941 : Nat := (cbits [0x280904a80a0b0591, 0x242512945208c045, 0x2441510248825408, 0x1774a953d1d0e86a, 0x8180c06081b62aa8, 0x124082016600811, 0x82203062fe00ff00, 0x7ffe000031dbbcf3, 0x380030c30440c183])
def s118Mask : Nat := 0xf0fff0fff0fff0ff
abbrev s118Goal : Nat := sGoal &&& s118Mask
abbrev s118StockWords : List Nat := [0xa0aaa0aaa0aaa0aa, 0xc0ccc0ccc0ccc0cc, 0xf0f0f0f0f0f0f0f0, 0xf000f000f000f000, 0xf0ff0000f0ff0000, 0xf0fff0ff00000000]
def s118Fact : Nat × List Nat × Nat × Nat := (s118Mask, s118StockWords, 9, s118Goal)
def s118Cuts : List (Nat × List Nat × Nat × Nat) := [s21Fact, s63Fact, s56Fact, s64Fact]
def s118Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[5, 6, 19, 35, 60, 5, 6, 19, 35, 60, 5, 6, 3, 28, 44, 49, 50, 52, 3, 28, 44, 49, 50, 52], rfl⟩
def s118Witnesses := unpackWitnesses s118StockWords [2564, 265220, 526849, 817204, 1058307, 1328643]
def s118Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 2 then (if j < 1 then (cbits [0x4c02600ea4078001, 0xa005002801400984, 0x580a445012801400, 0x2b21]) else (cbits [0x6803401810c005e1, 0xf467a03639b00d04, 0x3050888024002000, 0x4702])) else (if j < 3 then (cbits [0x920480a3851c08e0, 0x680b405622b0125a, 0xf01742b625b02d05, 0x5e02]) else (if j < 4 then (cbits [0xce16703381792bc0, 0xb42da06d03605a08, 0x721b80dc06e03701, 0x7603]) else (cbits [0xee17703b05d80ec0, 0x2010468203d21e04, 0x8834402])))) 13 (i % 16)
def s118Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 4 then (if j < 2 then (if j < 1 then (cbits [0x160090080200003f, 0xe006c2c01307003c, 0xa02b1200a44401f0, 0xc505e0431700dc5, 0x31f1a0c6c6631518, 0x920ca470]) else (cbits [0x783431d8cdc7432b, 0x98dc806211e9880, 0xa9322224b0866432, 0xb10c8ec3862a4f88, 0x31401009494f4424, 0x20ca406])) else (if j < 3 then (cbits [0x1093203a4b00c620, 0x53d1012c384424f8, 0x83344298f00a6300, 0x80d11a63c0698c01, 0xc4a0a30f82231c07, 0x8004128]) else (cbits [0x26932090c6020028, 0x98c702a02849a4f8, 0xe3340b80d02200c0, 0xb0f8346340c18922, 0x93209003136c4a0d, 0x4ca4f832]))) else (if j < 6 then (if j < 5 then (cbits [0x3a01c0c98c02600c, 0x8cd04004c0f8100, 0x63300f00403c0281, 0x80982e0120600204, 0x6200d0c760831410, 0x1318c04a]) else (cbits [0x5263d5318f052631, 0x63d1058c3815a4b1, 0xe92c828c501a0085, 0xa4c05493c1430e04, 0x255424f14e93c13, 0x18c5204])) else (if j < 7 then (cbits [0xe92c83188208329, 0x8b0e31093e8424ca, 0xa0108618d064f441, 0x98d06e34c1b0d006, 0x3141c80c23c02890, 0x158ca40c]) else (if j < 8 then (cbits [0x7c9329598a60c620, 0xfbd107ec385f24f8, 0xe3146124f0849305, 0x3c100088398800, 0x314230074360130a, 0xa30c7610]) else (cbits [0x123142124d47c92c, 0x618d462620160cd4, 0x4314243d107e92c9, 0x18d464620560cd41, 0x243d117e92cd6]))))) 22 (i % 16)
def s118Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 2 then (if j < 1 then (cbits [0x2012820040101f80, 0x2318051948218a0, 0xc024990249602310, 0x9a0c004817a20261, 0x1a0f007813180d1]) else (cbits [0x218c1218e0f00810, 0x810141561f0f4991, 0x9193121701a17009, 0xd8161f1731a1749, 0x201d0141e00e1d0])) else (if j < 3 then (cbits [0x300f8119a1d0261d, 0x2531025014811982, 0x8a561c2749627318, 0x1c254962549e2a31, 0x218101b81015816]) else (if j < 4 then (cbits [0x17a23161c3118a01, 0x350083518d8118a8, 0x83918f811a6351a0, 0xa18119b811958101, 0x61c3e4993e310011]) else (cbits [0x14984231b8131081, 0xc649901496013218, 0x1817a24861c0100e, 0x7a20162])))) 20 (i % 16)
def s118Links := pageLinks s118Index s118Codes 5 13 7 6
def s118Data (i : Nat) : Nat × Nat :=
  let e := s118Forest i
  (e &&& 127, e >>> 7)
def s118Sample : Nat × Nat := (s118Blob475157, 96)
def s118Tags := dagTraceTags s118Mask 96 (dagTagBases s118StockWords s118Blob475725 s118Blob475941 96) 8 s118Data
def s118States := dagTrace s118Mask s118StockWords 8 s118Data
def s118MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm6, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val))), (pm1, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val))), (pm24, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 5, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 5, 4] 0 i.val)))]
def s118Moves := dagMoves s118MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s118Autos : DagMovesOK s118Mask s118Goal 64 s118Moves := dagMovesOfCheck (by decide +kernel)
def s118Check := dagCheckNode s118Mask s118Goal s118Chart (dagKnownCloses s118Goal s118Cuts) 75 s118States s118Moves s118Links s118Sample s118Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s118Roots : dagCheckRoots s118Mask s118Goal s118Chart (dagKnownCloses s118Goal s118Cuts) s118Witnesses (dagRef 75 s118States s118Moves s118Links 0) s118StockWords 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s118Block0 : treeBlock 0 24 s118Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s118Block24 : treeBlock 24 24 s118Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s118Block48 : treeBlock 48 24 s118Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s118Block72 : treeBlock 72 3 s118Check = true := by decide +kernel
theorem s118Group0_48 : treeBlock 0 48 s118Check = true := treeBlock_merge (start := 0) (left := 24) (right := 24) (check := s118Check) s118Block0 s118Block24
theorem s118Group48_27 : treeBlock 48 27 s118Check = true := treeBlock_merge (start := 48) (left := 24) (right := 3) (check := s118Check) s118Block48 s118Block72
theorem s118Group0_75 : treeBlock 0 75 s118Check = true := treeBlock_merge (start := 0) (left := 48) (right := 27) (check := s118Check) s118Group0_48 s118Group48_27
theorem s118Blocks : treeBlock 0 75 s118Check = true := s118Group0_75
theorem s118Known : Known s118Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s64Stock) s56Stock) s63Stock) s21Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s118Stock : Lower s118Mask s118StockWords s118Goal 9 := by
  apply lowerDag _ _ _ _ s118Autos _ _ _ s118Known _ s118Roots s118Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s118Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel
def s119Mask : Nat := 0xf3f3f3f3f3f3f3f3
abbrev s119Goal : Nat := sGoal &&& s119Mask
abbrev s119StockWords : List Nat := [0xa2a2a2a2a2a2a2a2, 0xc0c0c0c0c0c0c0c0, 0xf0f0f0f0f0f0f0f0, 0xf300f300f300f300, 0xf3f30000f3f30000, 0xf3f3f3f300000000]
def s119Fact : Nat × List Nat × Nat × Nat := (s119Mask, s119StockWords, 9, s119Goal)
def s119Witnesses := unpackWitnesses s119StockWords [2564, 265220, 526849, 799249, 1061385, 1331721]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s119Stock : Lower s119Mask s119StockWords s119Goal 9 := by
  apply essentialLift (witnesses := s119Witnesses) (cut := s54Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s54StockWords) (by decide +kernel)
  · exact s54Stock
  · decide +kernel
def s120Mask : Nat := 0xf5f5f5f5f5f5f5f5
abbrev s120Goal : Nat := sGoal &&& s120Mask
abbrev s120StockWords : List Nat := [0xa0a0a0a0a0a0a0a0, 0xc4c4c4c4c4c4c4c4, 0xf0f0f0f0f0f0f0f0, 0xf500f500f500f500, 0xf5f50000f5f50000, 0xf5f5f5f500000000]
def s120Fact : Nat × List Nat × Nat × Nat := (s120Mask, s120StockWords, 9, s120Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s120Stock : Lower s120Mask s120StockWords s120Goal 9 := dagShiftLower (width := 64) pm1 s119Stock (by decide +kernel)
def s121Mask : Nat := 0xaaaa0000aaaa
abbrev s121Goal : Nat := sGoal &&& s121Mask
abbrev s121StockWords : List Nat := [0x888800008888, 0xa0a00000a0a0, 0xaa000000aa00, 0xaaaa00000000]
def s121Fact : Nat × List Nat × Nat × Nat := (s121Mask, s121StockWords, 5, s121Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s121Stock : Lower s121Mask s121StockWords s121Goal 5 := dagShiftLower (width := 64) pm6 s57Stock (by decide +kernel)
def s122Blob485888 : Nat := (cbits [0x81c0806020140205, 0x4120d0482c060b01, 0x2130184c180e0603, 0x90a0582815088542, 0xe078381d08864121, 0x9442251088c06230, 0x4229048a44826120, 0x35188cc582e160b4, 0x188e468361a0d462, 0x814683c160f0383c, 0x4220506014120501, 0x6061201442050a01, 0x7120182806060180, 0x834020b0201c020, 0x38580d0e034080d0, 0x60f16038380e020, 0x130084c180f0483c, 0xe05408150085462, 0x5808161a0546215, 0xc22170185c68160e, 0x2190e06402190a05, 0xd0886c121b0186c6, 0xa074221d06074121, 0x8c381f0a078181e0, 0x825008946223008, 0x261a094622516094, 0x189c68261609808])
def s122Blob486459 : Nat := (cbits [0xff1fc3f8bbbddefb, 0x4c4e273c8ff3ffe3, 0xf07c38fc1fe1fc00, 0xe7feffff767339cf, 0x8783c1f0ff9fc0ff, 0x1fff0007ff0007, 0xf8000007f803fe00, 0xfffc0000001fffff, 0xffe0000000000007])
def s122Blob486674 : Nat := (cbits [0x3b034558999cce79, 0x4021884e17d61, 0x8000082001000408, 0xc4fcbaa766633186, 0x68341e07b1e829e, 0x2214d20886d80833, 0x904810c5f803bc00, 0xff7800004c5b26db, 0x6e40041310902306])
def s122Mask : Nat := 0xfafafafafafafafa
abbrev s122Goal : Nat := sGoal &&& s122Mask
abbrev s122StockWords : List Nat := [0xaaaaaaaaaaaaaaaa, 0xc8c8c8c8c8c8c8c8, 0xf0f0f0f0f0f0f0f0, 0xfa00fa00fa00fa00, 0xfafa0000fafa0000, 0xfafafafa00000000]
def s122Fact : Nat × List Nat × Nat × Nat := (s122Mask, s122StockWords, 9, s122Goal)
def s122Cuts : List (Nat × List Nat × Nat × Nat) := [s73Fact, s57Fact, s121Fact, s23Fact]
def s122Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[5, 6, 11, 19, 25, 35, 41, 60, 5, 6, 11, 19, 3, 9, 28, 44, 49, 52, 3, 9, 28, 44, 49, 52], rfl⟩
def s122Witnesses := unpackWitnesses s122StockWords [2564, 265220, 526849, 792067, 1058307, 1328643]
def s122Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 2 then (if j < 1 then (cbits [0x380380323038001, 0xc23c03c038238038, 0x5404c44064004003]) else (cbits [0x1541540540540540, 0x8068068058858056, 0x6e06c16c06826806])) else (if j < 3 then (cbits [0x47407407407406e3, 0xe17e07c17c07c074, 0x9009009008088007]) else 0x9a09a0905)) 12 (i % 16)
def s122Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 2 then (if j < 1 then (cbits [0x20a00f020080003f, 0x271801a120190c01, 0x31f363152c3142a0, 0x63374432b3e3273a, 0x4e62b48620c63434]) else (cbits [0xd5692cd264352637, 0x38dc9435c9375a92, 0x12def4462c435ec, 0xe0080892c0631404, 0x1692c146201092c0])) else (if j < 3 then (cbits [0xc24314220121a010, 0x8a8f4428c382692, 0xc382092c1e6201c0, 0xe00d2031c1e31ca0, 0x2431a14319063142]) else (if j < 4 then (cbits [0x434c383292c30620, 0x240e31c3800cb4f4, 0x34c42340403283c0, 0xcc384a92c30620c2, 0x5403c50030ccf444]) else (cbits [0x6163251031e08314, 0x384a92c326202632, 0x62028326d8f4458c, 0xf4458c384c92c34, 0x6])))) 20 (i % 16)
def s122Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 2 then (if j < 1 then (cbits [0x401208010080fc0, 0x120401e0a4b0218a, 0x80320a4b070040e0, 0x680681496146202, 0x3101c0083802]) else (cbits [0x1a314340246a4b0e, 0x140404e0b0e0d496, 0xd258b98817006ae3, 0xe08031c18a82c385, 0x193820247863])) else (if j < 3 then (cbits [0x8232b0468100ca20, 0x389525929880119b, 0x8c6e080c2831582c, 0xa0b0e2c4960203ca, 0x61c029370525]) else 0x18860bd130)) 19 (i % 16)
def s122Links := pageLinks s122Index s122Codes 5 13 6 6
def s122Data (i : Nat) : Nat × Nat :=
  let e := s122Forest i
  (e &&& 63, e >>> 6)
def s122Sample : Nat × Nat := (s122Blob485888, 96)
def s122Tags := dagTraceTags s122Mask 96 (dagTagBases s122StockWords s122Blob486459 s122Blob486674 96) 8 s122Data
def s122States := dagTrace s122Mask s122StockWords 8 s122Data
def s122MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm6, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)))]
def s122Moves := dagMoves s122MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s122Autos : DagMovesOK s122Mask s122Goal 64 s122Moves := dagMovesOfCheck (by decide +kernel)
def s122Check := dagCheckNode s122Mask s122Goal s122Chart (dagKnownCloses s122Goal s122Cuts) 50 s122States s122Moves s122Links s122Sample s122Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s122Roots : dagCheckRoots s122Mask s122Goal s122Chart (dagKnownCloses s122Goal s122Cuts) s122Witnesses (dagRef 50 s122States s122Moves s122Links 0) s122StockWords 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s122Block0 : treeBlock 0 24 s122Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s122Block24 : treeBlock 24 24 s122Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s122Block48 : treeBlock 48 2 s122Check = true := by decide +kernel
theorem s122Group24_26 : treeBlock 24 26 s122Check = true := treeBlock_merge (start := 24) (left := 24) (right := 2) (check := s122Check) s122Block24 s122Block48
theorem s122Group0_50 : treeBlock 0 50 s122Check = true := treeBlock_merge (start := 0) (left := 24) (right := 26) (check := s122Check) s122Block0 s122Group24_26
theorem s122Blocks : treeBlock 0 50 s122Check = true := s122Group0_50
theorem s122Known : Known s122Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s23Stock) s121Stock) s57Stock) s73Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s122Stock : Lower s122Mask s122StockWords s122Goal 9 := by
  apply lowerDag _ _ _ _ s122Autos _ _ _ s122Known _ s122Roots s122Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s122Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel
def s123Mask : Nat := 0xfcfcfcfcfcfcfcfc
abbrev s123Goal : Nat := sGoal &&& s123Mask
abbrev s123StockWords : List Nat := [0xa8a8a8a8a8a8a8a8, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xfc00fc00fc00fc00, 0xfcfc0000fcfc0000, 0xfcfcfcfc00000000]
def s123Fact : Nat × List Nat × Nat × Nat := (s123Mask, s123StockWords, 9, s123Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s123Stock : Lower s123Mask s123StockWords s123Goal 9 := dagShiftLower (width := 64) pm1 s122Stock (by decide +kernel)
def s124Mask : Nat := 0xfffff0f0fffff0f0
abbrev s124Goal : Nat := sGoal &&& s124Mask
abbrev s124StockWords : List Nat := [0xaaaaa0a0aaaaa0a0, 0xccccc0c0ccccc0c0, 0xf0f0f0f0f0f0f0f0, 0xff00f000ff00f000, 0xffff0000ffff0000, 0xfffff0f000000000]
def s124Fact : Nat × List Nat × Nat × Nat := (s124Mask, s124StockWords, 9, s124Goal)
def s124Witnesses := unpackWitnesses s124StockWords [2564, 265220, 535057, 799249, 1079340, 1341468]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s124Stock : Lower s124Mask s124StockWords s124Goal 9 := by
  apply essentialLift (witnesses := s124Witnesses) (cut := s43Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s43StockWords) (by decide +kernel)
  · exact s43Stock
  · decide +kernel
def s125Mask : Nat := 0xfffffffff0f0f0f0
abbrev s125Goal : Nat := sGoal &&& s125Mask
abbrev s125StockWords : List Nat := [0xaaaaaaaaa0a0a0a0, 0xccccccccc0c0c0c0, 0xf0f0f0f0f0f0f0f0, 0xff00ff00f000f000, 0xffff0000f0f00000, 0xffffffff00000000]
def s125Fact : Nat × List Nat × Nat × Nat := (s125Mask, s125StockWords, 9, s125Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s125Stock : Lower s125Mask s125StockWords s125Goal 9 := dagShiftLower (width := 64) pm6 s124Stock (by decide +kernel)
def s126Mask : Nat := 0xffffffffffff0000
abbrev s126Goal : Nat := sGoal &&& s126Mask
abbrev s126StockWords : List Nat := [0xaaaaaaaaaaaa0000, 0xcccccccccccc0000, 0xf0f0f0f0f0f00000, 0xff00ff00ff000000, 0xffff0000ffff0000, 0xffffffff00000000]
def s126Fact : Nat × List Nat × Nat × Nat := (s126Mask, s126StockWords, 9, s126Goal)
def s126Witnesses := unpackWitnesses s126StockWords [9746, 271889, 535057, 799249, 1079340, 1341468]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s126Stock : Lower s126Mask s126StockWords s126Goal 9 := by
  apply essentialLift (witnesses := s126Witnesses) (cut := s43Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s43StockWords) (by decide +kernel)
  · exact s43Stock
  · decide +kernel
def s127Mask : Nat := 0xffff0000ffff
abbrev s127Goal : Nat := sGoal &&& s127Mask
abbrev s127StockWords : List Nat := [0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000]
def s127Fact : Nat × List Nat × Nat × Nat := (s127Mask, s127StockWords, 8, s127Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s127Stock : Lower s127Mask s127StockWords s127Goal 8 := dagShiftLower (width := 64) pm6 s51Stock (by decide +kernel)
def s128Blob515233 : Nat := (cbits [0x180406020140205, 0xc120b0182c060702, 0x40e06034120d0502, 0x30884c0613060381, 0x9058281508854241, 0x6422190486428160, 0x301a09068141a0c0, 0x230188c381e0e074, 0x1209442251108c42, 0x8a41229120984426, 0x8442a050a8502910, 0x233160b8582d140a, 0x61a0d46235190cc6, 0xc0e462391a0d8643, 0xf0383c1c0e8643a1, 0x51c0f0683c160, 0x506014120501814, 0x1201442050a01422, 0x181406018180006, 0x844060a018240606, 0x8070101c02071201, 0xd0402c040b0082c0, 0xe034100d02034020, 0x38080e01038580d0, 0x60f16038380e040, 0x130603c140f0483c, 0x1884c20130104c02])
def s128Blob515803 : Nat := (cbits [0xff033d1cfa39f3f3, 0x3dc67cfcff07ff00, 0xfff83fff000ccee3, 0xfff0f303c6078f1f, 0x7f80fe00fffc7ff, 0xffff80000ff03fc, 0xfffc0007fff000, 0xf8000000f0000000, 0xffffff])
def s128Blob516006 : Nat := (cbits [0x5601140c5818b171, 0x28c254b493004902, 0x2508125602044861, 0xa870a30286050a0a, 0x7680fc008d684a8, 0xee7200c0cba03b4, 0x30dffc0007b7e000, 0xf0000000c0420030, 0x808400c0c0efffdb])
def s128Mask : Nat := 0xffffffffffffffff
abbrev s128Goal : Nat := sGoal &&& s128Mask
abbrev s128StockWords : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
def s128Fact : Nat × List Nat × Nat × Nat := (s128Mask, s128StockWords, 12, s128Goal)
def s128Cuts : List (Nat × List Nat × Nat × Nat) := [s25Fact, s36Fact, s37Fact, s50Fact, s61Fact, s62Fact, s68Fact, s70Fact, s60Fact, s71Fact, s67Fact, s69Fact, s77Fact, s76Fact, s78Fact, s79Fact, s80Fact, s81Fact, s82Fact, s83Fact, s84Fact, s92Fact, s93Fact, s94Fact, s97Fact, s98Fact, s99Fact, s100Fact, s101Fact, s102Fact, s96Fact, s103Fact, s104Fact, s11Fact, s105Fact, s106Fact, s107Fact, s108Fact, s109Fact, s110Fact, s111Fact, s112Fact, s113Fact, s114Fact, s115Fact, s116Fact, s117Fact, s118Fact, s119Fact, s120Fact, s122Fact, s123Fact, s124Fact, s125Fact, s126Fact, s51Fact, s127Fact, s16Fact, s54Fact, s55Fact, s87Fact, s95Fact, s15Fact, s22Fact, s1Fact, s43Fact, s4Fact, s5Fact, s63Fact, s73Fact, s74Fact, s44Fact, s56Fact, s57Fact, s58Fact, s64Fact, s121Fact, s75Fact, s23Fact, s24Fact, s8Fact, s65Fact]
def s128Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[5, 6, 11, 19, 25, 26, 35, 41, 42, 60, 5, 6, 3, 9, 10, 28, 44, 49, 50, 52, 56, 3, 9, 10], rfl⟩
def s128Witnesses := unpackWitnesses s128StockWords [2564, 265220, 526849, 792067, 1058307, 1328643]
def s128Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 15 then (if j < 7 then (if j < 3 then (if j < 1 then (cbits [0x5c4031600370001, 0x6c006c006c00644, 0x6e106e006c106c0, 0x8e0086407490702]) else (if j < 2 then (cbits [0x8e008e008e008e0, 0x9430940094008e3, 0xa6409a609a009a0, 0xae00ae00ae00ae0]) else (cbits [0xb400b400b400ae3, 0xbe00be00b640b41, 0xf860c980c230be2, 0x1040104010401040]))) else (if j < 5 then (if j < 4 then (cbits [0x118211801180104a, 0x1200120011c211c0, 0x1240122112201201, 0x14c2127312601241]) else (cbits [0x1500150015001500, 0x1549154015401502, 0x16ea16c116a11662, 0x1ae01ac118351820])) else (if j < 6 then (cbits [0x1ba01ba01ba01ae6, 0x1c001ba31ba01ba0, 0x1c401c211c011c00, 0x1ce11ce01c451c40]) else (cbits [0x1d801d801d041d00, 0x1da91da01d811d80, 0x1f601f031f001ec2, 0x200020001f651f60])))) else (if j < 11 then (if j < 9 then (if j < 8 then (cbits [0x212020a420a02005, 0x2283214a21402121, 0x230022e122e022e0, 0x2422234723402302]) else (cbits [0x2502246524602460, 0x2644260225842542, 0x27402740274026c4, 0x2832280127842742])) else (if j < 10 then (cbits [0x2b812b612b222a66, 0x2ce42c452c402ba5, 0x2d622d602d602d60, 0x2fc32f062de92da2]) else (cbits [0x323431e2308b3023, 0x36c036c0362534ac, 0x372036c336c036c0, 0x37c0372537203720]))) else (if j < 13 then (if j < 12 then (cbits [0x37c537c037c037c0, 0x3865386038603860, 0x39c139c039063900, 0x3b203b0139e939e0]) else (cbits [0x3b803b803b233b20, 0x3c403c403c403b86, 0x3d403cc43cc03c44, 0x3e613d683d603d41])) else (if j < 14 then (cbits [0x3ee13ea23e813e80, 0x4080408040423f0a, 0x40e940c140824080, 0x4280420442004200]) else (cbits [0x4304430043004284, 0x4480442343a44381, 0x44a3448144804480, 0x47c0472545114500]))))) else (if j < 23 then (if j < 19 then (if j < 17 then (if j < 16 then (cbits [0x47e047c147c047c0, 0x48a048a0488147e5, 0x4a6249c548a948a0, 0x4c304be24ae84aa2]) else (cbits [0x4fc24fc04fa14e2c, 0x50a0500550005000, 0x50a050a050a050a0, 0x51c05163516050a6])) else (if j < 18 then (cbits [0x5262526051c551c0, 0x52e052e052a252a0, 0x53825342532152e2, 0x53e253c153c053c0]) else (cbits [0x564055e3544d5421, 0x5643564056405640, 0x57005700570056a3, 0x57e3574557215701]))) else (if j < 21 then (if j < 20 then (cbits [0x593d588558615841, 0x5e215e205e015cca, 0x5e805e805e425e40, 0x5ec75ec05ea15e81]) else (cbits [0x600060005fa35fa0, 0x6080608060806004, 0x622061c361c0608a, 0x62c0622562206220])) else (if j < 22 then (cbits [0x63226320632062c3, 0x6403636563606360, 0x6480648064806461, 0x656064e464e06483]) else (cbits [0x6641660266006565, 0x688366af66816661, 0x698068e568e068e0, 0x6984698069806980])))) else (if j < 27 then (if j < 25 then (if j < 24 then (cbits [0x6ba06a0d6a006a00, 0x6bc06bc06bc06ba1, 0x6c0d6c006c006bc2, 0x6e006dc26dc06da1]) else (cbits [0x6f206e286e016e00, 0x70006fe16fe06f26, 0x70c370c070a17005, 0x71c271c071a17124])) else (if j < 26 then (cbits [0x7265720372007200, 0x76e0760773187300, 0x770076e176e076e0, 0x77c077c077c07706]) else (cbits [0x7a41794877cc77c0, 0x7cc07c257a8d7a61, 0x7f007e467ccc7cc0, 0x80407fe37f267f01]))) else (if j < 29 then (if j < 28 then (cbits [0x8240822180ac8043, 0x8300830082a38243, 0x84c184c08444830a, 0x866685c584e784e0]) else (cbits [0x89a28924878d8723, 0x8c678b0b8ae189e8, 0x8ec78dc88d828d42, 0x92a991a890898fa7])) else (if j < 30 then (cbits [0x95409502950093ca, 0x9628958595809542, 0x9b4a98d498069727, 0x9f299e669da69c89]) else (cbits [0xa2a1a2a0a189a04a, 0xa408a308a2e1a2c1, 0xa8a7a7c7a68aa50c, 0xa98c])))))) 16 (i % 16)
def s128Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 43 then (if j < 21 then (if j < 10 then (if j < 5 then (if j < 2 then (if j < 1 then (cbits [0x400900200800003f, 0x1f2640131fc00f14, 0x9443158023143500, 0x8621380620b5031f, 0x3f3ae63739c63339, 0x3b292c7ae64379c6]) else (cbits [0xec387be93f3be933, 0x433d4c3f3d2c393c, 0x7d2f457cef443d6c, 0x203301802700401b, 0x1505231443203f03, 0xea6200cc31f0983])) else (if j < 3 then (cbits [0x863710c633108621, 0x2c51864350c63f11, 0x52a93f12a93311c9, 0xec3f13cc39138c38, 0x45538f44140c4313, 0x1062000601e53cf]) else (if j < 4 then (cbits [0x8314016c38014621, 0x3800c63200a62000, 0x8328012c3800ec, 0xa62001292c00e32a, 0x2c02462b02262101, 0x42a94f02a9430269]) else (cbits [0xd250030f4f02cf44, 0x4401e92c01c00d42, 0x1e92c421250020f, 0x92c429250028f44, 0x1e02f250028c3802, 0x4662103e6200340])))) else (if j < 7 then (if j < 6 then (cbits [0x125004ef4e048c38, 0x3803863203631405, 0x40c3803d25003ac, 0x6328045250042f4e, 0x4e04092c03a32a03, 0x4262004d25004af]) else (cbits [0x492c03c32a04ac38, 0x1b05400f04cf4404, 0x83e03381a0278100, 0xa32701031bc3e03f, 0x2043e33f03e33301, 0x7263306e62105e6])) else (if j < 8 then (cbits [0x664347263f076637, 0x3f08693307a92c47, 0x90c3908cc384869, 0xcf44094c43092c3f, 0x3205602a490f4548, 0x5ac3805892c01c0]) else (if j < 9 then (cbits [0xf45d25005cf44, 0x1b06202786001b06, 0x1e62781e3270583, 0xcc43068c3806492c, 0x44066c38468f4406, 0x6af44066c38466f]) else (cbits [0x892c074c38070c38, 0x3381232705a31b07, 0x12627c4033f8403, 0x492c44063f040633, 0x3707493307092d06, 0x47894347493f0789]))))) else (if j < 15 then (if j < 12 then (if j < 11 then (cbits [0x2c3f080c3907cc38, 0x4547cf44084c4308, 0x7ef44066c38480f, 0xc31b08b250088f4e, 0x33c4433f82033305, 0x6892c44463f0206]) else (cbits [0xef4448ac3f07cc38, 0x3807ef4406ac3808, 0x84203108292c080c, 0x2331096049c4203d, 0x2089634944233d04, 0x8893108492c06c6])) else (if j < 13 then (cbits [0x432709a00e48893d, 0x4b04633f02233301, 0xaa92c09e62a4463, 0x69430b293f0b092d, 0x384b694f4b294b0b, 0x4bcc4b0bcc3f0b8c]) else (if j < 14 then (cbits [0x6f4b0c4f450c0f44, 0x514c12500c8f4f0c, 0xa032509cc384c52, 0x6c380a49320a2620, 0x384a92500a8f440a, 0x4af2500aef440acc]) else (cbits [0xc31a0b46280a2934, 0x440acc380a693609, 0xbe6344bb2500baf, 0xaf440aec380a8936, 0x250ca0540c32500b, 0x9e3140240330ce0])))) else (if j < 18 then (if j < 16 then (cbits [0xec380d89320d2620, 0x500e6f4f0e2f440d, 0xd0c380a06204e32, 0x6c380d49320a2620, 0x2c0d46200a43140d, 0x4dd2500dcf440da9]) else (if j < 17 then (cbits [0x692c0a66200d0331, 0x204e12500e0f440d, 0xe0f440dcc3e0a86, 0xc00f0e89540e5250, 0x270f60270f201b0e, 0xaa62105e6200263]) else (cbits [0x6c43102c380fa92c, 0x2c0ee02a502f4410, 0xf4c380f0c388609, 0x31b06292c0f802a, 0x2d06492c0f43270f, 0x100c430fcc380ac9]))) else (if j < 19 then (cbits [0xef44066c384fcf44, 0x2d06892c0286330f, 0x104f440fcc380ae9, 0xc6200fef4406ac38, 0x2106e62010092c06, 0x10ac380d26290b06]) else (if j < 20 then (cbits [0x23140d693507092c, 0x3810e31d0b231507, 0x11092c0b4314116c, 0x4620114c38112932, 0x1402a02711462907, 0x11a92c0b63150763]) else (cbits [0x8333016327078620, 0x2107a62044833f04, 0xfa92c0de62b0b86, 0xa93711693310a92d, 0x3851a94351693f11, 0x124c3f122c3911ec])))))) else (if j < 32 then (if j < 26 then (if j < 23 then (if j < 22 then (cbits [0x2f4551ef44126c43, 0x2d07c92c44c63f52, 0xfcc380e09370ba9, 0xef4407ec38120f44, 0x3108262008092c0f, 0x12834944a33d04a3]) else (cbits [0x631410092c084620, 0x4e12c3290bc31508, 0xbe314137250134f, 0x3250130f4e12ec38, 0x2013032908831413, 0x2c33313263508a6])) else (if j < 24 then (cbits [0x62108c62045033f, 0x3810292c0e262b0c, 0x13af44536c3f11ec, 0x292d08e92c02e63f, 0x44104c380e49370c, 0xc4621090620120f]) else (if j < 25 then (cbits [0x6315092314122c38, 0x3103002712492c0c, 0x14204944e03d04e0, 0x631f0c8315094314, 0x3112692c1066200e, 0x89662053493d1349]) else (cbits [0x832a14631e128c38, 0x2b19a62189862017, 0x1c492d1b492c1a66, 0x894b1d49431c893f, 0x3f1d8c385d494f5c, 0x1f0f445e6c4b1e6c])))) else (if j < 29 then (if j < 27 then (cbits [0x8f4f1f6f4b1f4f45, 0x145f52515f12501f, 0x15832b15232a1483, 0x492c16263315a632, 0x3856a94f16a94316, 0x174f4f170f4416cc]) else (if j < 28 then (cbits [0xc92c14a632571250, 0x50150f4414ec3814, 0x156f44154c385512, 0xc62014a314557250, 0x50160f4415e92c15, 0x15e93214c6205612]) else (cbits [0x9250168f44166c38, 0x3815463614e62056, 0x56f25016ef44166c, 0x93e156636150620, 0x5016ef44168c3816, 0x89e3141766541732]))) else (if j < 30 then (cbits [0x62017e31f17a315, 0x4418ec3818693218, 0x593250196f4f192f, 0x29328a262017c030, 0x298a4314184c3818, 0x18a92c1826201883]) else (if j < 31 then (cbits [0x662058d25018cf44, 0x50190f4418492c8a, 0x18cc3e8a86205912, 0x8954195250190f44, 0x3614862819c00c19, 0x1a0c3897a93617a6]) else (cbits [0x555c1a52501a2f44, 0x1814c93419ec385a, 0x15093414e93419e3, 0x831e15231c1a8030, 0x2c97a62017e32a15, 0x1b0f441aec3e1ac9]))))) else (if j < 37 then (if j < 34 then (if j < 33 then (cbits [0xc6205b355c1b3250, 0x281aa33c1aac3897, 0x1b60271566281546, 0xa92c16462a1b8033, 0x441bac381a092d8a, 0x5bf2501c2f4f1bef]) else (cbits [0xcf448acc38166936, 0x381689365bd2501b, 0x1c12501bcf448aec, 0xc9358b092c180634, 0x281849401c6f441a, 0x1d06298b26201ca3])) else (if j < 35 then (cbits [0xc9328b43141d2f44, 0x1e1ce6341cec381c, 0x1d6c388b662016a3, 0x892c18e63616c62a, 0x381b09371a292d8b, 0x1d2c3f1c6c391bac]) else (if j < 36 then (cbits [0x6c4f5d2c4b1d6c43, 0x4b1def451daf445d, 0x5db2501e2f4f1e0f, 0x94216e9365df251, 0x501bcf448bac3819, 0x1e83341e43541dd2]) else (cbits [0xd25a1ea6358bc620, 0x2a8be3141ef55c1e, 0x8c092c1926361706, 0xec381b29371a492d, 0x505eef4b1daf441b, 0x1949421729361f32])))) else (if j < 40 then (if j < 38 then (cbits [0xd2501c0f448c2c38, 0x201def448c492c1d, 0x1fa0541e0c388c66, 0x862019632a17431e, 0x3d1e2c381c292c8c, 0x8ca6205ecc491ecc]) else (if j < 39 then (cbits [0x92c1fe02a1e4c38, 0x4323293f22e92d22, 0x63c94f63294b23c9, 0xcc4b24cc3f240c38, 0x4b25ef4525af4464, 0x65b250262f4f260f]) else (cbits [0x464220062065f251, 0x2d20a92c60464e20, 0x2149432129332109, 0xaf44216c3861494f, 0x3861b25021ef4f21, 0x20892c206620202c]))) else (if j < 41 then (cbits [0xcc3860694e206942, 0x2c60f25020ef4420, 0x60894e2089422029, 0x9250218f4420cc38, 0x50218f4420ec3861, 0x224c3822203321d2]) else (if j < 42 then (cbits [0x925022cf4f228f44, 0x44627250226f4462, 0x20033422b250226f, 0x4028202640230f44, 0x3823692c23af4423, 0x204028238334238c]) else (cbits [0x633620833423ec38, 0x3f230c39224c3821, 0x63ac4b23ec4323ac, 0x6f45242f4463ec4f, 0x5024af4f248f4b24, 0x2186426472516432]))))))) else (if j < 64 then (if j < 53 then (if j < 48 then (if j < 45 then (if j < 44 then (cbits [0xe034245250226f44, 0x3825955c25725a24, 0x255250252f4e250c, 0xa336254340252034, 0x4b242f44228c3821, 0x21c64225d250658f]) else (cbits [0x6f4424525022af44, 0x2c21e02a248c3824, 0x256c3d24ac3822c9, 0x602a146008656c49, 0x2a94631428602b26, 0x28e620a8632ba663])) else (if j < 46 then (cbits [0xe62b2aa6272a4621, 0x3f2e26332ca6322b, 0x2f492c6ee64b2ee6, 0x494331693f30e92d, 0x3872494f71694b32, 0x736c4b336c3f328c]) else (if j < 47 then (cbits [0x6f4b344f45340f44, 0x51741250348f4f34, 0x26801e9520087452, 0x633327031926c314, 0x4427cc3827862027, 0x681250284f4f280f]) else (cbits [0x263226ec3826ac38, 0x38272624274c3827, 0x26a32a95431427ac, 0xa92c27462526e620, 0x1467f25027ef4427, 0x28325027ef449563])))) else (if j < 50 then (if j < 49 then (cbits [0xac3e28863e958314, 0x2a29003228cf4428, 0x29292ca6c62a26c3, 0xac3869894f298943, 0x502a2f4f29ef4429, 0x296f44294c3869f2]) else (cbits [0xe93626e636697250, 0x5029cf44294c38a6, 0x29cf44296c3869d2, 0x8f442a693e2a1250, 0x34a703342700342a, 0x2baf442b693e2ac9])) else (if j < 51 then (cbits [0x4c382b29322ae930, 0x342720342b092c2b, 0x2bc0282b8934a723, 0x4c40a74640274340, 0x3c2c063e2ac6242b, 0x2c8f442c6c3e2c2c]) else (if j < 52 then (cbits [0x9302c4c382ae624, 0x82b49302b26242b, 0x95a31428802b15a0, 0x62b2cc620a8832b, 0x432d692d2d292c2d, 0x2dac3e6d894f2d89]) else (cbits [0xf4f2dcf446dac4a, 0x2015c3146dd2502e, 0x15e3142ce92c95c6, 0x4f442ce92c95e620, 0x201603146d52502d, 0x2df2502d4c389606]))))) else (if j < 58 then (if j < 55 then (if j < 54 then (cbits [0x2314276036162008, 0x362e4620a7633696, 0x2b69322a692c2e66, 0xb2502e8c382c0936, 0x246eb55c2ed25b2e, 0x2f355c2f0f442b86]) else (cbits [0xa025af60192f600d, 0x201643143000332f, 0x2d293229292c9646, 0x6f44302c382e8933, 0x3870725030af4f30, 0x2fec382fc3322f8c])) else (if j < 56 then (cbits [0x83252f83192fc330, 0x2c1666202fe331af, 0x304f44294c389669, 0x892c168620705250, 0x442d4c3e296c3896, 0x30c954309250304f]) else (if j < 57 then (cbits [0x8634278334310024, 0x38314f442d693ea7, 0x27a640312330312c, 0x8328318028a7a940, 0x38322f4431c628b1, 0x320c3831e93031ac]) else (cbits [0x934b1a63431a334, 0x2096a31416a00832, 0x326c382d86322986, 0xc33727c33616c314, 0x37a7c63696c62028, 0x2a892d29a92ca8c6])))) else (if j < 61 then (if j < 59 then (cbits [0x93f2c89372ba933, 0x39302c386f094b2f, 0x326c43322c3f314c, 0xaf44726c4f722c4b, 0x4f330f4b32ef4532, 0x72f25172b250332f]) else (if j < 60 then (cbits [0xe92c27e64216e620, 0x4429cc38a7e94296, 0x33495432d250304f, 0xa634b38334338034, 0x5c33d25a2da63c33, 0x28033617031433f5]) else (cbits [0xe92ca80636970620, 0x4b2ea93f2dc93e29, 0x32af44306c386f29, 0x262034325073ef4b, 0x4297292c28264217, 0x2dec4a2a0c38a829]))) else (if j < 62 then (cbits [0xef4432d250308f44, 0x2a174008330c3832, 0xa8432a9743142840, 0xc6332e06322a2620, 0x2c34e65534a6542e, 0x33cc3d332c3830a9]) else (if j < 63 then (cbits [0x631417600873cc49, 0x3830c92c34c62a97, 0x266012178008334c, 0x63158cc314286013, 0x3235862035231f9a, 0x378f4436ec383609]) else (cbits [0xe00877925037cf4f, 0x3e97e31426801017, 0x356f44b54c3e3549, 0x831e18031426a31c, 0x329ac6218d262027, 0x18231435ec3835a9])))))) else (if j < 75 then (if j < 69 then (if j < 66 then (if j < 65 then (cbits [0x462035c92c8d4620, 0x88d692c27a62a18, 0x8d831428a0131860, 0x232935431f9ae315, 0x2c35a62036432b36, 0x36cf4f368f443669]) else (cbits [0xa314188008769250, 0x1435c92c8da62018, 0x36b2508dc62018c3, 0xc31f27c31e18e314, 0x2b9b06218de62028, 0x370f4435e92c3566])) else (if j < 67 then (cbits [0x620771250374f4f, 0x508e092c27e62a19, 0x192314376c543732, 0x26218e262028031e, 0x50370f44368c3e9b, 0x28262a19462037b2]) else (if j < 68 then (cbits [0x325036af4a8e492c, 0x1428401219600837, 0x37e95436c9328e63, 0x8314198008374c38, 0x1b38200f376c388e, 0xea314386027b820]) else (cbits [0x431f22031b1b4315, 0x2c9b46218ea6202f, 0x396c43392c3838a9, 0x292c2f662a792f44, 0x36384c389b692d8f, 0x38801e8f4c382f89])))) else (if j < 72 then (if j < 70 then (cbits [0x86210f6620b8802a, 0x2c30062b2226271b, 0x8f892c9b892d8f69, 0xa620b8432738431b, 0x2b2246271ba6210f, 0x9ba92d8fa92c3026]) else (if j < 71 then (cbits [0xcf44390c4338cc38, 0x331bc92d0fc92c78, 0x8fcc383049372269, 0xec3838ef449bcc39, 0x2c1006208fef440f, 0x1be6211026209009]) else (cbits [0x292c30662b228627, 0x4438cc389be92d90, 0x1c092d10492c394f, 0x4c3830893722a933, 0x1438ef449c0c3990, 0x22c31b1c23151063]))) else (if j < 73 then (cbits [0x262190662030a31f, 0x1510831439092c9c, 0x30e31f22e31b1c43, 0x4621908620358329, 0x2039ac38b586299c, 0x2306271c662110a6]) else (if j < 74 then (cbits [0xa92c35e63531462b, 0x8b5e9359c692d90, 0x23200f1c800910c0, 0xc31439e01d316013, 0x38b9e31d9c831590, 0x3180121ca0083acc]) else (cbits [0x3279d031590e314, 0x323a292c31c3293a, 0x3aac383a89333a69, 0xc0083a4c38910620, 0x1e1ce3149123141c, 0x32063591462031a3]))))) else (if j < 80 then (if j < 77 then (if j < 76 then (cbits [0x23151163143a4c38, 0x2932231f23a31b1d, 0x9d26219166203aa3, 0x4009118008baa629, 0x1432401323c00f1d, 0x3b092c9d43159183]) else (cbits [0xe31b1d631511a314, 0x2191a62032631f23, 0x1d831511c3149d66, 0xe32b32831f24031b, 0x2b9d862191c62036, 0x39a92d38a92cb6e6])) else (if j < 78 then (cbits [0xc93f3b09373ac933, 0x393b4c387b09437a, 0x3bcc433bac3f3b8c, 0xe6207b8f457b4f44, 0x2b2426271da62111, 0x91e92c37063732a6]) else (if j < 79 then (cbits [0xcc38b709379da92d, 0x2d12092c3b6f4438, 0x32c9372449331dc9, 0xcc39920c38372943, 0x2038ef44b72c439d, 0x2466271de6211226]) else (cbits [0xe92d92292c32e62b, 0x1b1e03151243149d, 0x92462033031f2483, 0x23151263149e0621, 0x2b33231f24a31b1e, 0x9e26219266203743])))) else (if j < 83 then (if j < 81 then (cbits [0xa00839092cb7462b, 0x1324c00f1e600912, 0x92a3143c00293360, 0xaf4ebc03299e6315, 0x121e80083cd2503c, 0x9ea31592c3143380]) else (if j < 82 then (cbits [0x4c3833a3353c2333, 0x203c92503c6f4e3c, 0x93262093031492e6, 0x600f1ec009134008, 0x143c602933c01325, 0xbc63299ec3159343]) else (cbits [0x831b1ee315136314, 0x203c833533e31f25, 0xbc86359ee6219366, 0xa31b1f0315138314, 0x2037832b34031f25, 0xb7862b9f06219386]))) else (if j < 84 then (cbits [0xcc3f3b4c3839292c, 0x2113a6203d0f447c, 0x34262b25c6271f26, 0x292d93a92c37a637, 0x44394c38b7a9379f, 0x1f431513c3143b6f]) else (if j < 85 then (cbits [0xc62034431f25e31b, 0x83b8c389f462193, 0x26000f1f600913e0, 0x631593e314346013, 0x91400083ba92c9f, 0x34801326200f1f80]) else (cbits [0x831594031437c01f, 0x2c396620b7c31f9f, 0x7ca93d3ca9313bc9])))))))) 24 (i % 16)
def s128Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 15 then (if j < 7 then (if j < 3 then (if j < 1 then (cbits [0x360200400407e00, 0x100106280400f00c, 0x400361c010c64043, 0xc00cc420361c024c, 0xa0e31003404e0261, 0x49603801]) else (if j < 2 then (cbits [0xc560d310835e880e, 0xa1835e8814496034, 0x9e0d92805de880d4, 0xa06c03c1a019809e, 0x1b61c06cc641b18, 0x31006a4a]) else (cbits [0x4a0207a708187020, 0xa70958701a31086a, 0xa01a7a706a4a0257, 0x50ac01e2a18a00a4, 0x82b61c0ad2582b01, 0x3100a9e8]))) else (if j < 5 then (if j < 4 then (cbits [0x258300138c001e30, 0xa20d58703061c0cd, 0x70383108a9886307, 0xb8a98703a3198a98, 0x3e4960a92583c31, 0x7a20fd87]) else (cbits [0x8863e61f8f98723e, 0x28111e9c444998a9, 0x722a7a211d8702a9, 0x492d8862a61f8a98, 0x4e00713462a0202, 0x31513587])) else (if j < 6 then (cbits [0x2645031014064a50, 0x96135e885061c141, 0x5a4d7a2159870564, 0x1934c505a49f9352, 0xe4d7a21758704d4a, 0x31a17d87]) else (cbits [0xe8a4d928185e884d, 0x2a195e9e4d7a5935, 0x706801299c63e020, 0xc1a92646a31019d8, 0x86d4961b52646761, 0x61c19de8])))) else (if j < 11 then (if j < 9 then (if j < 8 then (cbits [0x4a0727a219de8870, 0x100092a8747a799e, 0x70770151dc01e763, 0x39d98707a00d9d98, 0x7e4961d80547c01, 0x7a21fd87]) else (cbits [0xe888261c1d98867e, 0x1c214c42026219d9, 0x588818ea1cc66026, 0xc21d870884992212, 0x802496234c6e0261, 0x61c23d25])) else (if j < 10 then (cbits [0x87e8f61ca3de8890, 0x9980869294621a3d, 0x9c9761c25c652964, 0x8259e9c9692825de, 0x2027a22758700292, 0x61f80987]) else (cbits [0x1201024a8588602, 0x19294628a418f28c, 0x88a561c295258a53, 0x22a9870aa195291e, 0xae319290656a47a, 0x4962b8c4]))) else (if j < 13 then (if j < 12 then (cbits [0x258a4319a91e88ae, 0xa1a91e88b361c2cd, 0x88a47a22dd870a44, 0xa2ede9ea49282e5e, 0xbe18aaf4654a332, 0x18faf406]) else (cbits [0x870c1499304c40bd, 0x96310652c44992f5, 0x88c861c2f5e88c44, 0x7af64a0ca7a22f5e, 0x8ce310a8d2a8cc7a, 0x61c33c01])) else (if j < 14 then (cbits [0x4a0ce7a2339870ce, 0x1c354060d4315a8e, 0x88d461f351258d46, 0x3b6d258a3928351e, 0x8de61c36c066db01, 0x7a236de8]) else (cbits [0x25aa37a7b6e4a0e0, 0x9439527ea37a238d, 0x52e561c399264e61, 0xc3ad286a37a2394c, 0xee7a23b5870a361, 0x7a2bb64a]))))) else (if j < 23 then (if j < 19 then (if j < 17 then (if j < 16 then (cbits [0x6a8f27a7bb5e96ed, 0x1abd0668f461fa8c, 0x88a3aae3d24b4f43, 0x5a8de8aa39283e5e, 0xe0102a3f5e9ea37a, 0x153fc01]) else (cbits [0xc850061c404c4100, 0x964012590331040c, 0x5b007a2419871064, 0xc40128700499c012, 0x10e7a2401e890c61, 0x7a7c024a])) else (if j < 18 then (cbits [0x87111019c45258ff, 0x28455e89117a244d, 0x8918496bfde9f119, 0x646c0511a49fbfde, 0x6ff7a24698711b49, 0x61c47d28]) else (cbits [0x4a1227a2485870ff, 0xa7c85e97217a2c86, 0x712801a49d87eff7, 0xd49e4a1287a74a18, 0x12e7a23feab92792, 0x7a2bfe4a]))) else (if j < 21 then (if j < 20 then (cbits [0x26017a7bfde96ff, 0x1c4d403d340154cc, 0x333461c4dc629346, 0x9cd1871393194e46, 0x13461c4f4c413419, 0x7a24fd87]) else (cbits [0xe9f34928505e8934, 0x1f510c7d44015ccd, 0x65483104cde89446, 0x25298714a4965200, 0x94e61c521287487a, 0x7a2521e8])) else (if j < 22 then (cbits [0xc43337a7d224a150, 0x13ccde895349f54c, 0x595849855d269563, 0xf5598715749955d2, 0x15e7a25592695c49, 0x315ccc05]) else (cbits [0x8716261e580c7d60, 0x194cde896061f581, 0x576649659cc41663, 0x6d99e896a496598c, 0x96661f5992876649, 0x9285bde8])))) else (if j < 27 then (if j < 25 then (if j < 24 then (cbits [0xc4172319ccde9f66, 0x285c98717231b5c8, 0x897831fcce4b7729, 0x6ded25933aae5e1e, 0x57e012ded8717c00, 0x61c5f866]) else (cbits [0xe898261c5ec0677b, 0xa7dee4a1847a25ed, 0x4988496ccd2a9867, 0xfccde898861c6240, 0x18c61c6340518c49, 0x49863cc5])) else (if j < 26 then (cbits [0x287337a26318718f, 0xa26558713361c64d, 0x97957a2e564a1967, 0xfccd2a99a7a7e55e, 0x59c31a6700699c61, 0xaae6724b]) else (cbits [0xe8b33928685e8933, 0x2a695e9f337a5ccd, 0x3e0132ae94c55a63, 0x26a927daa18fea40, 0x9ae4996b4c41a97a, 0x61c6b525]))) else (if j < 29 then (if j < 28 then (cbits [0x657b1194ec5265a9, 0x286d5e89b14966c4, 0x89b861c6a5e9fb19, 0xa6ede9fb89286e5e, 0xfa99286f5e89a962, 0x4aa6fde9]) else (cbits [0x871c2007f04c4001, 0x9670403dc4013f05, 0x87c67a271d871c64, 0x1f05e89ca61c7058, 0x60161c734c420162, 0xef3cc6])) else (if j < 30 then (cbits [0x871d249674064fd0, 0x1c741267d0499741, 0x59d831b805871cf6, 0x276d871da4960052, 0x7da61ff69873da7a, 0x49980588]) else (cbits [0x871e1199f84053e0, 0xa77824a1e17a7785, 0x89e861c0064a1e07, 0x180587e0161c805e, 0x62])))))) 22 (i % 16)
def s128Links := pageLinks s128Index s128Codes 5 13 9 6
def s128Data (i : Nat) : Nat × Nat :=
  let e := s128Forest i
  (e &&& 511, e >>> 9)
def s128Sample : Nat × Nat := (s128Blob515233, 96)
def s128Tags := dagTraceTags s128Mask 96 (dagTagBases s128StockWords s128Blob515803 s128Blob516006 96) 11 s128Data
def s128States := dagTrace s128Mask s128StockWords 11 s128Data
def s128MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm6, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val))), (pm1, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val))), (pm24, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 5, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 5, 4] 0 i.val)))]
def s128Moves := dagMoves s128MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s128Autos : DagMovesOK s128Mask s128Goal 64 s128Moves := dagMovesOfCheck (by decide +kernel)
def s128Check := dagCheckNode s128Mask s128Goal s128Chart (dagKnownCloses s128Goal s128Cuts) 492 s128States s128Moves s128Links s128Sample s128Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s128Roots : dagCheckRoots s128Mask s128Goal s128Chart (dagKnownCloses s128Goal s128Cuts) s128Witnesses (dagRef 492 s128States s128Moves s128Links 0) s128StockWords 11 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s128Block0 : treeBlock 0 24 s128Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s128Block24 : treeBlock 24 24 s128Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s128Block48 : treeBlock 48 24 s128Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s128Block72 : treeBlock 72 24 s128Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s128Block96 : treeBlock 96 24 s128Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s128Block120 : treeBlock 120 24 s128Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s128Block144 : treeBlock 144 24 s128Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s128Block168 : treeBlock 168 24 s128Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s128Block192 : treeBlock 192 24 s128Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s128Block216 : treeBlock 216 24 s128Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s128Block240 : treeBlock 240 24 s128Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s128Block264 : treeBlock 264 24 s128Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s128Block288 : treeBlock 288 24 s128Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s128Block312 : treeBlock 312 24 s128Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s128Block336 : treeBlock 336 24 s128Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s128Block360 : treeBlock 360 24 s128Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s128Block384 : treeBlock 384 24 s128Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s128Block408 : treeBlock 408 24 s128Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s128Block432 : treeBlock 432 24 s128Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s128Block456 : treeBlock 456 24 s128Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s128Block480 : treeBlock 480 12 s128Check = true := by decide +kernel
theorem s128Group0_48 : treeBlock 0 48 s128Check = true := treeBlock_merge (start := 0) (left := 24) (right := 24) (check := s128Check) s128Block0 s128Block24
theorem s128Group72_48 : treeBlock 72 48 s128Check = true := treeBlock_merge (start := 72) (left := 24) (right := 24) (check := s128Check) s128Block72 s128Block96
theorem s128Group48_72 : treeBlock 48 72 s128Check = true := treeBlock_merge (start := 48) (left := 24) (right := 48) (check := s128Check) s128Block48 s128Group72_48
theorem s128Group0_120 : treeBlock 0 120 s128Check = true := treeBlock_merge (start := 0) (left := 48) (right := 72) (check := s128Check) s128Group0_48 s128Group48_72
theorem s128Group120_48 : treeBlock 120 48 s128Check = true := treeBlock_merge (start := 120) (left := 24) (right := 24) (check := s128Check) s128Block120 s128Block144
theorem s128Group192_48 : treeBlock 192 48 s128Check = true := treeBlock_merge (start := 192) (left := 24) (right := 24) (check := s128Check) s128Block192 s128Block216
theorem s128Group168_72 : treeBlock 168 72 s128Check = true := treeBlock_merge (start := 168) (left := 24) (right := 48) (check := s128Check) s128Block168 s128Group192_48
theorem s128Group120_120 : treeBlock 120 120 s128Check = true := treeBlock_merge (start := 120) (left := 48) (right := 72) (check := s128Check) s128Group120_48 s128Group168_72
theorem s128Group0_240 : treeBlock 0 240 s128Check = true := treeBlock_merge (start := 0) (left := 120) (right := 120) (check := s128Check) s128Group0_120 s128Group120_120
theorem s128Group240_48 : treeBlock 240 48 s128Check = true := treeBlock_merge (start := 240) (left := 24) (right := 24) (check := s128Check) s128Block240 s128Block264
theorem s128Group312_48 : treeBlock 312 48 s128Check = true := treeBlock_merge (start := 312) (left := 24) (right := 24) (check := s128Check) s128Block312 s128Block336
theorem s128Group288_72 : treeBlock 288 72 s128Check = true := treeBlock_merge (start := 288) (left := 24) (right := 48) (check := s128Check) s128Block288 s128Group312_48
theorem s128Group240_120 : treeBlock 240 120 s128Check = true := treeBlock_merge (start := 240) (left := 48) (right := 72) (check := s128Check) s128Group240_48 s128Group288_72
theorem s128Group384_48 : treeBlock 384 48 s128Check = true := treeBlock_merge (start := 384) (left := 24) (right := 24) (check := s128Check) s128Block384 s128Block408
theorem s128Group360_72 : treeBlock 360 72 s128Check = true := treeBlock_merge (start := 360) (left := 24) (right := 48) (check := s128Check) s128Block360 s128Group384_48
theorem s128Group456_36 : treeBlock 456 36 s128Check = true := treeBlock_merge (start := 456) (left := 24) (right := 12) (check := s128Check) s128Block456 s128Block480
theorem s128Group432_60 : treeBlock 432 60 s128Check = true := treeBlock_merge (start := 432) (left := 24) (right := 36) (check := s128Check) s128Block432 s128Group456_36
theorem s128Group360_132 : treeBlock 360 132 s128Check = true := treeBlock_merge (start := 360) (left := 72) (right := 60) (check := s128Check) s128Group360_72 s128Group432_60
theorem s128Group240_252 : treeBlock 240 252 s128Check = true := treeBlock_merge (start := 240) (left := 120) (right := 132) (check := s128Check) s128Group240_120 s128Group360_132
theorem s128Group0_492 : treeBlock 0 492 s128Check = true := treeBlock_merge (start := 0) (left := 240) (right := 252) (check := s128Check) s128Group0_240 s128Group240_252
theorem s128Blocks : treeBlock 0 492 s128Check = true := s128Group0_492
theorem s128Known : Known s128Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s65Stock) s8Stock) s24Stock) s23Stock) s75Stock) s121Stock) s64Stock) s58Stock) s57Stock) s56Stock) s44Stock) s74Stock) s73Stock) s63Stock) s5Stock) s4Stock) s43Stock) s1Stock) s22Stock) s15Stock) s95Stock) s87Stock) s55Stock) s54Stock) s16Stock) s127Stock) s51Stock) s126Stock) s125Stock) s124Stock) s123Stock) s122Stock) s120Stock) s119Stock) s118Stock) s117Stock) s116Stock) s115Stock) s114Stock) s113Stock) s112Stock) s111Stock) s110Stock) s109Stock) s108Stock) s107Stock) s106Stock) s105Stock) s11Stock) s104Stock) s103Stock) s96Stock) s102Stock) s101Stock) s100Stock) s99Stock) s98Stock) s97Stock) s94Stock) s93Stock) s92Stock) s84Stock) s83Stock) s82Stock) s81Stock) s80Stock) s79Stock) s78Stock) s76Stock) s77Stock) s69Stock) s67Stock) s71Stock) s60Stock) s70Stock) s68Stock) s62Stock) s61Stock) s50Stock) s37Stock) s36Stock) s25Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s128Stock : Lower s128Mask s128StockWords s128Goal 12 := by
  apply lowerDag _ _ _ _ s128Autos _ _ _ s128Known _ s128Roots s128Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s128Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
end PEqualNP.Outside.L_meta_41938

open PEqualNP.Outside.L_meta_41938 in
theorem PEqualNP.Outside.L_meta_41938 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276678376 * 2 ^ 32 + 4008241376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276678376 * 2 ^ 32 + 4008241376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  intro t h
  let raw : List (BitVec 64) := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
  let goal : BitVec 64 := 0xfee8eee8eee8e8e0
  have root : Lower (fullMask 64) (raw.map BitVec.toNat) goal.toNat 12 :=
    hcsLowerEq (by decide +kernel) (by decide +kernel) (by decide +kernel) s128Stock
  have size : 12 ≤ t :=
    hcsLower (n := 6) raw goal 12 _ (by decide +kernel) (by decide +kernel) root t h
  let circuit : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.and, [0, 1]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [2, 4]⟩, ⟨.and, [9, 5]⟩, ⟨.or, [6, 10]⟩, ⟨.and, [11, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [7, 13]⟩, ⟨.or, [2, 14]⟩, ⟨.and, [8, 15]⟩, ⟨.or, [16, 12]⟩], 17⟩
  refine ⟨circuit, ?_, ?_, by decide +kernel⟩
  · intro gate member
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · exact Nat.le_trans (by decide +kernel : circuit.size ≤ 12) size

