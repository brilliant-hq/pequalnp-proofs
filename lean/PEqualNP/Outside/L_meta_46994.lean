import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_46994

def uP (packed width index : Nat) : Nat :=
  (packed >>> (width * index)) &&& ((1 <<< width) - 1)

def tB (start count : Nat) (check : Nat → Bool) : Bool :=
  (Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ next i => check i && next (i + 1)) count) start

theorem treeBlock_at {start count i : Nat} {check : Nat → Bool}
    (h : tB start count check = true) (lo : start ≤ i) (hi : i < start + count) :
    check i = true := by
  induction count generalizing start with
  | zero => omega
  | succ count ih =>
    change (check start && tB (start + 1) count check) = true at h
    rcases Bool.and_eq_true_iff.mp h with ⟨here,rest⟩
    by_cases eq : i = start
    · simpa [eq] using here
    · exact ih rest (by omega) (by omega)

theorem tM {start left right : Nat} {check : Nat → Bool}
    (a : tB start left check = true)
    (b : tB (start + left) right check = true) :
    tB start (left + right) check = true := by
  induction left generalizing start with
  | zero => simpa using b
  | succ left ih =>
    rw [Nat.succ_add]
    change (check start && tB (start + 1) (left + right) check) = true
    change (check start && tB (start + 1) left check) = true at a
    rcases Bool.and_eq_true_iff.mp a with ⟨here,rest⟩
    exact Bool.and_eq_true_iff.mpr ⟨here,ih rest (by
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using b)⟩

def rootWords (base : List Nat) (token : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun word _ next bits =>
      let tail := next (bits >>> 1)
      if bits &&& 1 == 0 then tail else word :: tail) base token

def rootState (base : List Nat) (fuel token : Nat) : (Nat × List Nat × List (Nat × Nat × Nat)) :=
  (fuel,rootWords base token,[])

def insertWord (w : Nat) (ws : List Nat) : List Nat :=
  List.rec [w] (fun a tail next => if w ≤ a then w :: a :: tail else a :: next) ws

def childState (mask token : Nat) (state : (Nat × List Nat × List (Nat × Nat × Nat))) : Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  let (fuel,ws,history) := state
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
      some (fuel - 1,insertWord w rest,(w,x,y) :: history)

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
    (fun (out,a,b) _ next seen =>
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
    (fun (w,a,b) _ next bank =>
      let v := w &&& mask
      if needed.contains v && !availableB mask bank v &&
          recipeGate mask bank v (a &&& mask) (b &&& mask) then
        v :: next (v :: bank)
      else next bank) recipes bank

def boundCloses (target : Nat) (state : (Nat × List Nat × List (Nat × Nat × Nat))) (bound : (Nat × List Nat × Nat × Nat)) : Bool :=
  let (mask,stock,lower,goal) := bound
  let (fuel,ws,history) := state
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
  (∃ a,AvailableWord mask bank a ∧ out = mask ^^^ a) ∨
  (∃ a b,AvailableWord mask bank a ∧ AvailableWord mask bank b ∧
    (out = a &&& b ∨ out = a ||| b))

def WordBuilds (mask : Nat) (roots : List Nat) : List Nat → Prop
  | [] => True
  | w :: ws => GateWord mask roots w ∧ WordBuilds mask (w :: roots) ws

def Lower (mask : Nat) (roots : List Nat) (target : Nat) (minimum : Nat) : Prop :=
  ∀ values,WordBuilds mask roots values →
    AvailableWord mask (values ++ roots) target → minimum ≤ values.length

def Known (bounds : List (Nat × List Nat × Nat × Nat)) : Prop :=
  ∀ bound ∈ bounds,Lower bound.1 bound.2.1 bound.2.2.2 bound.2.2.1

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
  rcases gate with ⟨a,ha,rfl⟩ | ⟨a,b,ha,hb,eq | eq⟩
  · refine Or.inl ⟨a &&& cut,av ha,?_⟩
    apply Nat.eq_of_testBit_eq
    intro i
    have cutAt := congrArg (fun n : Nat => n.testBit i) submask
    simp only [Nat.testBit_and,Nat.testBit_xor] at cutAt ⊢
    cases h : cut.testBit i
    · simp
    · simp [h] at cutAt
      simp [cutAt]
  · subst out
    refine Or.inr ⟨a &&& cut,b &&& cut,av ha,av hb,Or.inl ?_⟩
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and]
    cases cut.testBit i <;> simp
  · subst out
    refine Or.inr ⟨a &&& cut,b &&& cut,av ha,av hb,Or.inr ?_⟩
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and,Nat.testBit_or]
    cases cut.testBit i <;> simp

theorem availableWeaken {mask : Nat} {small big : List Nat} {w : Nat}
    (sub : ∀ x ∈ small,AvailableWord mask big x)
    (av : AvailableWord mask small w) : AvailableWord mask big w := by
  rcases av with rfl | rfl | h
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact sub w h

theorem gateWeaken {mask : Nat} {small big : List Nat} {out : Nat}
    (sub : ∀ x ∈ small,AvailableWord mask big x)
    (gate : GateWord mask small out) : GateWord mask big out := by
  rcases gate with ⟨a,ha,rfl⟩ | ⟨a,b,ha,hb,eq⟩
  · exact Or.inl ⟨a,availableWeaken sub ha,rfl⟩
  · exact Or.inr ⟨a,b,availableWeaken sub ha,availableWeaken sub hb,eq⟩

theorem eK {bound : (Nat × List Nat × Nat × Nat)} {bounds : List (Nat × List Nat × Nat × Nat)}
    (old : Known bounds)
    (new : Lower bound.1 bound.2.1 bound.2.2.2 bound.2.2.1) :
    Known (bound :: bounds) := by
  intro x h
  rcases List.mem_cons.mp h with rfl | h
  · exact new
  · exact old _ h

def AgreesAt (i j : Nat) (word : Nat) : Prop :=
  word.testBit i = word.testBit j

theorem buildsMap {m n : Nat} (f : Nat → Nat)
    (zero : f 0 = 0) (ones : f m = n)
    (invert : ∀ a,f (m ^^^ a) = n ^^^ f a)
    (meet : ∀ a b,f (a &&& b) = f a &&& f b)
    (join : ∀ a b,f (a ||| b) = f a ||| f b)
    {roots : List Nat} {bank : List Nat}
    (supply : ∀ v ∈ roots,AvailableWord n bank (f v))
    {values : List Nat} (h : WordBuilds m roots values) :
    WordBuilds n bank (values.map f) := by
  have av {bank roots : List Nat} {v : Nat}
      (src : ∀ v ∈ roots,AvailableWord n bank (f v))
      (h : AvailableWord m roots v) : AvailableWord n bank (f v) := by
    rcases h with rfl | rfl | hv
    · exact Or.inl zero
    · exact Or.inr (Or.inl ones)
    · exact src _ hv
  induction values generalizing roots bank with
  | nil => trivial
  | cons v vs ih =>
    refine ⟨?_,ih ?_ h.2⟩
    · rcases h.1 with ⟨a,ha,eq⟩ | ⟨a,b,ha,hb,eq | eq⟩
      · exact Or.inl ⟨f a,av supply ha,eq ▸ invert a⟩
      · exact Or.inr ⟨f a,f b,av supply ha,av supply hb,Or.inl (eq ▸ meet a b)⟩
      · exact Or.inr ⟨f a,f b,av supply ha,av supply hb,Or.inr (eq ▸ join a b)⟩
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact Or.inr (Or.inr List.mem_cons_self)
      · exact availableWeaken (fun x hx => Or.inr (Or.inr (List.mem_cons_of_mem _ hx))) (supply _ hw)

theorem lowerMap {m n : Nat} (f : Nat → Nat)
    (zero : f 0 = 0) (ones : f m = n)
    (invert : ∀ a,f (m ^^^ a) = n ^^^ f a)
    (meet : ∀ a b,f (a &&& b) = f a &&& f b)
    (join : ∀ a b,f (a ||| b) = f a ||| f b)
    {roots bank : List Nat} {goal : Nat} {minimum : Nat}
    (supply : ∀ v ∈ roots,AvailableWord n bank (f v))
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
    (supply : ∀ w ∈ small,AvailableWord mask big w) (build : WordBuilds mask small values) :
    WordBuilds mask big values := by
  induction values generalizing small big with
  | nil => trivial
  | cons v vs ih =>
    refine ⟨gateWeaken supply build.1,ih ?_ build.2⟩
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact Or.inr (Or.inr List.mem_cons_self)
    · exact availableWeaken (fun x hx => Or.inr (Or.inr (List.mem_cons_of_mem _ hx))) (supply _ hw)

def pW (mask word : Nat) : Prop := word ≠ 0 ∧ word ≠ mask

def binWord (isOr : Bool) (a b : Nat) : Nat :=
  if isOr then a ||| b else a &&& b

theorem binWord_comm (d : Bool) (a b : Nat) : binWord d a b = binWord d b a := by
  cases d <;> simp [binWord,Nat.land_comm,Nat.lor_comm]

variable {mask : Nat} {target : Nat}

def LiveWord (mask : Nat) (target : Nat) : Nat → Nat → Finset (Nat) → Prop
  | 0,t,S => t=0 ∧ S={target} ∧ pW mask target
  | k+1,t,S =>
    (∃ (u : Nat) (U : Finset (Nat)) (a : Nat),t=u+1 ∧ S=insert a U ∧ pW mask a ∧
      (mask ^^^ a) ∉ insert a U ∧ LiveWord mask target k u (insert ((mask ^^^ a)) U)) ∨
    (∃ (U : Finset (Nat)) (a b : Nat) (d : Bool),S=insert a (insert b U) ∧ pW mask a ∧ pW mask b ∧ a ≠ b ∧
      binWord d a b ∉ insert a (insert b U) ∧ LiveWord mask target k t (insert (binWord d a b) U))
theorem LiveWord.stop {target : Nat} (hp : pW mask target) : LiveWord mask target 0 0 {target} := ⟨rfl,rfl,hp⟩
theorem LiveWord.unary {target : Nat} {k t : Nat} {U : Finset (Nat)} {a : Nat} (ha : pW mask a)
    (hfresh : (mask ^^^ a) ∉ insert a U) (tail : LiveWord mask target k t (insert ((mask ^^^ a)) U)) :
    LiveWord mask target (k+1) (t+1) (insert a U) :=
  Or.inl ⟨t,U,a,rfl,rfl,ha,hfresh,tail⟩
theorem LiveWord.binary {target : Nat} {k t : Nat} {U : Finset (Nat)} {a b : Nat} {d : Bool}
    (ha : pW mask a) (hb : pW mask b) (hab : a ≠ b)
    (hfresh : binWord d a b ∉ insert a (insert b U)) (tail : LiveWord mask target k t (insert (binWord d a b) U)) :
    LiveWord mask target (k+1) t (insert a (insert b U)) :=
  Or.inr ⟨U,a,b,d,rfl,ha,hb,hab,hfresh,tail⟩
theorem LiveWord.ind {target : Nat} {motive : ∀ (k t : Nat) (S : Finset (Nat)),LiveWord mask target k t S → Prop}
    (stop : ∀ (hp : pW mask target),motive 0 0 {target} (LiveWord.stop hp))
    (unary : ∀ {k t : Nat} {U : Finset (Nat)} {a : Nat} (ha : pW mask a)
      (hfresh : (mask ^^^ a) ∉ insert a U) (tail : LiveWord mask target k t (insert ((mask ^^^ a)) U)),
      motive k t (insert ((mask ^^^ a)) U) tail → motive (k+1) (t+1) (insert a U) (LiveWord.unary ha hfresh tail))
    (binary : ∀ {k t : Nat} {U : Finset (Nat)} {a b : Nat} {d : Bool}
      (ha : pW mask a) (hb : pW mask b) (hab : a ≠ b)
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

theorem liveWordProper {k t S} (h : LiveWord mask target k t S) : ∀ a ∈ S,pW mask a := by
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
  w ∈ ws ∨ ¬pW mask w

def wordWitness (mask : Nat) (ws : List Nat) (w : Nat) : Prop :=
  (∃ a ∈ ws,pW mask a ∧ w = mask ^^^ a) ∨
  ∃ d a b,a ∈ ws ∧ b ∈ ws ∧ pW mask a ∧ pW mask b ∧
    a ≠ b ∧ w = binWord d a b

theorem pullWord {w : List (Nat)} {z : Nat} {k t S} (h : LiveWord mask target k t S)
    (hz : wordRep mask w z ∨ wordWitness mask w z) (sub : ∀ a ∈ S,a ∈ w++[z]) :
    ∃ k' t' S',k' ≤ k+1 ∧ LiveWord mask target k' t' S' ∧ ∀ a ∈ S',a ∈ w := by
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
        have hu : ∀ v ∈ U,v ∈ w := by
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
        have hu : ∀ v ∈ U,v ∈ w := by
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
    (all : ∀ w ∈ bank,Masked mask w) (aw : AvailableWord mask bank word) :
    Masked mask word := by
  rcases aw with rfl | rfl | hw
  · simp [Masked]
  · simp [Masked]
  · exact all _ hw

theorem maskedGate {bank : List Nat} {out : Nat}
    (all : ∀ w ∈ bank,Masked mask w) (g : GateWord mask bank out) :
    Masked mask out := by
  rcases g with ⟨a,ha,rfl⟩ | ⟨a,b,ha,hb,ea | ea⟩
  · have h := projectGate (mask := mask) (cut := mask) (by simp)
      (roots := bank) (out := mask ^^^ a) (Or.inl ⟨a,ha,rfl⟩)
    have ma := maskedAvailable all ha
    unfold Masked at ma ⊢
    apply Nat.eq_of_testBit_eq
    intro i
    have bit := congrArg (fun n : Nat => n.testBit i) ma
    simp only [Nat.testBit_and,Nat.testBit_xor] at bit ⊢
    cases hm : mask.testBit i <;> simp_all
  · subst out
    have ma := maskedAvailable all ha
    have mb := maskedAvailable all hb
    simp only [Masked] at ma mb ⊢
    rw [Nat.land_assoc,mb]
  · subst out
    have ma := maskedAvailable all ha
    have mb := maskedAvailable all hb
    unfold Masked at ma mb ⊢
    apply Nat.eq_of_testBit_eq
    intro i
    have bitA := congrArg (fun n : Nat => n.testBit i) ma
    have bitB := congrArg (fun n : Nat => n.testBit i) mb
    simp only [Nat.testBit_and,Nat.testBit_or] at bitA bitB ⊢
    cases hm : mask.testBit i <;> simp_all

def binaryWitness (mask : Nat) (bank : List Nat) (out : Nat) : Prop :=
  ∃ d a b,a ∈ bank ∧ b ∈ bank ∧ pW mask a ∧ pW mask b ∧
    a ≠ b ∧ out = binWord d a b

theorem classifyBinary {bank : List Nat}
    (all : ∀ w ∈ bank,Masked mask w) (d : Bool) {a b : Nat}
    (ha : AvailableWord mask bank a) (hb : AvailableWord mask bank b) :
    wordRep mask bank (binWord d a b) ∨ binaryWitness mask bank (binWord d a b) := by
  have c0 : wordRep mask bank 0 := Or.inr fun h => h.1 rfl
  have cm : wordRep mask bank mask := Or.inr fun h => h.2 rfl
  have classify {w : Nat} (hw : AvailableWord mask bank w) :
      w = 0 ∨ w = mask ∨ w ∈ bank ∧ pW mask w := by
    by_cases zh : w = 0
    · exact Or.inl zh
    by_cases mh : w = mask
    · exact Or.inr (Or.inl mh)
    exact Or.inr (Or.inr ⟨(hw.resolve_left zh).resolve_left mh,zh,mh⟩)
  have ma : a &&& mask = a := maskedAvailable all ha
  have mb : b &&& mask = b := maskedAvailable all hb
  have absorbA : a ||| mask = mask := by
    apply Nat.eq_of_testBit_eq
    intro i
    have h := congrArg (fun n : Nat => n.testBit i) ma
    simp only [Nat.testBit_and,Nat.testBit_or] at h ⊢
    cases hm : mask.testBit i <;> simp_all
  have absorbB : b ||| mask = mask := by
    apply Nat.eq_of_testBit_eq
    intro i
    have h := congrArg (fun n : Nat => n.testBit i) mb
    simp only [Nat.testBit_and,Nat.testBit_or] at h ⊢
    cases hm : mask.testBit i <;> simp_all
  rcases classify ha with rfl | hma | ⟨ha',pa⟩
  · rw [binWord_comm]
    cases d
    · exact Or.inl (by simpa [binWord] using c0)
    · rcases hb with hz | hm | hv
      · exact Or.inl (by simpa [binWord,hz] using c0)
      · exact Or.inl (by simpa [binWord,hm] using cm)
      · exact Or.inl (by simpa [binWord,wordRep] using
          (Or.inl hv : wordRep mask bank b))
  · rw [hma,binWord_comm]
    cases d
    · rcases hb with hz | hm | hv
      · exact Or.inl (by simpa [binWord,hz] using c0)
      · exact Or.inl (by simpa [binWord,hm] using cm)
      · exact Or.inl (by simpa [binWord,mb,wordRep] using
          (Or.inl hv : wordRep mask bank b))
    · exact Or.inl (by simpa [binWord,absorbB] using cm)
  rcases classify hb with rfl | hmb | ⟨hb',pb⟩
  · cases d
    · exact Or.inl (by simpa [binWord] using c0)
    · exact Or.inl (by simpa [binWord,wordRep] using
        (Or.inl ha' : wordRep mask bank a))
  · rw [hmb]
    cases d
    · exact Or.inl (by simpa [binWord,ma,wordRep] using
        (Or.inl ha' : wordRep mask bank a))
    · exact Or.inl (by simpa [binWord,absorbA] using cm)
  by_cases eq : a = b
  · subst b
    cases d <;> exact Or.inl (by simpa [binWord,wordRep] using
      (Or.inl ha' : wordRep mask bank a))
  exact Or.inr ⟨d,a,b,ha',hb',pa,pb,eq,rfl⟩

theorem classifyWord {bank : List Nat} {out : Nat}
    (all : ∀ w ∈ bank,Masked mask w) (gate : GateWord mask bank out) :
    wordRep mask bank out ∨ wordWitness mask bank out := by
  have c0 : wordRep mask bank 0 := Or.inr fun h => h.1 rfl
  have cm : wordRep mask bank mask := Or.inr fun h => h.2 rfl
  have classify {w : Nat} (hw : AvailableWord mask bank w) :
      w = 0 ∨ w = mask ∨ w ∈ bank ∧ pW mask w := by
    by_cases zh : w = 0
    · exact Or.inl zh
    by_cases mh : w = mask
    · exact Or.inr (Or.inl mh)
    exact Or.inr (Or.inr ⟨(hw.resolve_left zh).resolve_left mh,zh,mh⟩)
  rcases gate with ⟨a,ha,rfl⟩ | ⟨a,b,ha,hb,h | h⟩
  · rcases classify ha with rfl | hma | ⟨hm,hp⟩
    · exact Or.inl (by simpa using cm)
    · exact Or.inl (by simpa [hma] using c0)
    · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
  · subst out; exact (classifyBinary all false ha hb).imp id Or.inr
  · subst out; exact (classifyBinary all true ha hb).imp id Or.inr

theorem extractWordLive {roots values : List Nat}
    (all : ∀ w ∈ roots,Masked mask w) (builds : WordBuilds mask roots values)
    (hit : AvailableWord mask (values ++ roots) target) (p : pW mask target) :
    ∃ k t S,k ≤ values.length ∧ LiveWord mask target k t S ∧ ∀ w ∈ S,w ∈ roots := by
  have hm := (hit.resolve_left p.1).resolve_left p.2
  induction values generalizing roots with
  | nil =>
    exact ⟨0,0,{target},Nat.zero_le _,LiveWord.stop p,by simpa using hm⟩
  | cons w ws ih =>
    have next : ∀ v ∈ w :: roots,Masked mask v := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact maskedGate all builds.1
      · exact all _ hv
    have ht : AvailableWord mask (ws ++ w :: roots) target := by
      exact Or.inr (Or.inr (by simpa [List.mem_append,List.mem_cons,or_assoc,or_left_comm] using hm))
    obtain ⟨k,t,S,hk,live,sub⟩ :=
      ih next builds.2 ht ((ht.resolve_left p.1).resolve_left p.2)
    have available : ∀ v ∈ S,v ∈ roots ++ [w] := by
      intro v h
      simpa [or_comm] using sub v h
    obtain ⟨k',t',S',hk',hl,hsub⟩ := pullWord live (classifyWord all builds.1) available
    exact ⟨k',t',S',by simp only [List.length_cons]; omega,hl,hsub⟩

theorem insertWordMem {x w : Nat} {ws : List Nat} :
    x ∈ insertWord w ws ↔ x = w ∨ x ∈ ws := by
  induction ws with
  | nil => simp [insertWord]
  | cons a tail ih =>
    change x ∈ (if w ≤ a then w :: a :: tail else a :: insertWord w tail) ↔ _
    split <;> simp [ih,or_assoc,or_left_comm]

theorem insertWordNodup {w : Nat} {ws : List Nat} (nd : ws.Nodup) (fresh : w ∉ ws) :
    (insertWord w ws).Nodup := by
  induction ws with
  | nil => simp [insertWord]
  | cons a tail ih =>
    change (if w ≤ a then w :: a :: tail else a :: insertWord w tail).Nodup
    split
    · exact List.nodup_cons.mpr ⟨fresh,nd⟩
    have hn := List.nodup_cons.mp nd
    have hnot : w ≠ a ∧ w ∉ tail := by simpa using fresh
    exact List.nodup_cons.mpr ⟨by simp [insertWordMem,hnot.1.symm,hn.1],ih hn.2 hnot.2⟩

theorem insertWordSet (w : Nat) (ws : List Nat) :
    (insertWord w ws).toFinset = insert w ws.toFinset := by
  ext x
  simp [insertWordMem]

theorem eraseWordSet {ws : List Nat} (nd : ws.Nodup) (w : Nat) :
    (ws.erase w).toFinset = ws.toFinset.erase w := by
  ext x
  simp [nd.mem_erase_iff,and_comm]

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
    ∀ v ∈ keepWord save w ws,v ∈ ws := by
  cases save
  · exact fun _ h => List.mem_of_mem_erase h
  · exact fun _ h => h

theorem keepSet {ws : List Nat} (nd : ws.Nodup) {w : Nat} {U : Finset Nat}
    (eq : ws.toFinset = insert w U) :
    (keepWord (decide (w ∈ U)) w ws).toFinset = U := by
  by_cases hw : w ∈ U
  · simp [keepWord,hw,eq,Finset.insert_eq_of_mem hw]
  · simp [keepWord,hw,eraseWordSet nd,eq]

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
  simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem inb] using
    List.getElem_idxOf inb

theorem unaryChild {mask fuel a : Nat} {ws : List Nat}
    {history : List (Nat × Nat × Nat)} {x : Nat} {keep : Nat}
    (ha : a < ws.length) (ha64 : a < 64) (hf : fuel ≠ 0) (hk : keep < 2)
    (hx : ws.getD a 0 = x) (p : pW mask (mask ^^^ x)) (fresh : mask ^^^ x ∉ ws) :
    childState mask (gateToken a a 2 keep) (fuel,ws,history) =
      some (fuel - 1,insertWord (mask ^^^ x) (keepWord (keep.testBit 0) x ws),
        (mask ^^^ x,x,x) :: history) := by
  obtain ⟨ke,op,aa,bb⟩ := gateTokenFields (a := a) ha64 (by decide : 2 < 3) (by omega : keep < 4)
  simp only [childState,ke,op,aa,bb,hx]
  simp [hf,Nat.not_le_of_lt ha,Nat.not_le_of_lt hk,p.1,p.2,fresh,keepWord]

theorem binaryChild {mask fuel a b : Nat} {ws : List Nat}
    {history : List (Nat × Nat × Nat)} {x y : Nat} {keep : Nat}
    (d : Bool) (hab : a < b) (hb : b < ws.length) (hb64 : b < 64)
    (hf : fuel ≠ 0) (hk : keep < 4)
    (hx : ws.getD a 0 = x) (hy : ws.getD b 0 = y)
    (p : pW mask (binWord d x y)) (fresh : binWord d x y ∉ ws) :
    childState mask (gateToken a b (if d then 1 else 0) keep) (fuel,ws,history) =
      some (fuel - 1,insertWord (binWord d x y)
        (keepWord (keep.testBit 1) y (keepWord (keep.testBit 0) x ws)),
        (binWord d x y,x,y) :: history) := by
  have oh : (if d then 1 else 0) < 3 := by cases d <;> decide
  obtain ⟨ke,op,aa,bb⟩ := gateTokenFields (a := a) hb64 oh hk
  simp only [childState,ke,op,aa,bb,hx,hy]
  cases d <;>
    simp_all [Nat.not_le_of_lt hab,Nat.not_le_of_lt hb,keepWord,binWord,pW]

def WordViable (mask : Nat) (target : Nat) (state : (Nat × List Nat × List (Nat × Nat × Nat))) : Prop :=
  state.2.1.Nodup ∧ ∃ k t,k ≤ state.1 ∧ LiveWord mask target k t state.2.1.toFinset

def HasChild (mask : Nat) (state child : (Nat × List Nat × List (Nat × Nat × Nat))) : Prop :=
  ∃ a b op keep,a < state.2.1.length ∧
    ((a = b ∧ op = 2 ∧ keep < 2) ∨
      (a < b ∧ b < state.2.1.length ∧ op < 2 ∧ keep < 4)) ∧
    childState mask (gateToken a b op keep) state = some child

theorem unaryProgress {mask fuel k t : Nat} {x target : Nat} {U : Finset Nat} {ws : List Nat}
    {history : List (Nat × Nat × Nat)}
    (nd : ws.Nodup) (wide : ws.length ≤ 64) (hk : k + 1 ≤ fuel)
    (he : ws.toFinset = insert x U) (fresh : mask ^^^ x ∉ insert x U)
    (tail : LiveWord mask target k t (insert (mask ^^^ x) U)) :
    ∃ child,HasChild mask (fuel,ws,history) child ∧ WordViable mask target child := by
  let a := ws.idxOf x
  have xm : x ∈ ws := by
    rw [← List.mem_toFinset,he]
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
  have fn : mask ^^^ x ∉ ws := by simpa [← List.mem_toFinset,he] using fresh
  let rest := keepWord save x ws
  let child : (Nat × List Nat × List (Nat × Nat × Nat)) := (fuel - 1,insertWord (mask ^^^ x) rest,(mask ^^^ x,x,x) :: history)
  refine ⟨child,⟨a,a,2,keep,ha,Or.inl ⟨rfl,rfl,keepLt⟩,?_⟩,?_⟩
  · have eq := unaryChild (fuel := fuel) (history := history) ha (by omega) (by omega) keepLt hx p fn
    rw [keepBit] at eq
    exact eq
  · refine ⟨insertWordNodup (keepNodup nd save x) (fun h => fn (keepSubset save x ws _ h)),
      k,t,by change k ≤ fuel - 1; omega,?_⟩
    change LiveWord mask target k t (insertWord (mask ^^^ x) rest).toFinset
    rw [insertWordSet,keepSet nd he]
    exact tail

theorem binaryProgress {mask fuel k t : Nat} {x y target : Nat} {d : Bool} {U : Finset Nat}
    {ws : List Nat} {history : List (Nat × Nat × Nat)}
    (nd : ws.Nodup) (wide : ws.length ≤ 64) (hk : k + 1 ≤ fuel)
    (he : ws.toFinset = insert x (insert y U)) (xy : x ≠ y)
    (ordered : ws.idxOf x < ws.idxOf y) (fresh : binWord d x y ∉ insert x (insert y U))
    (tail : LiveWord mask target k t (insert (binWord d x y) U)) :
    ∃ child,HasChild mask (fuel,ws,history) child ∧ WordViable mask target child := by
  let a := ws.idxOf x
  let b := ws.idxOf y
  have xm : x ∈ ws := by rw [← List.mem_toFinset,he]; simp
  have ym : y ∈ ws := by rw [← List.mem_toFinset,he]; simp
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
  obtain ⟨keepLt,bx,by'⟩ := fields
  have fn : v ∉ ws := by simpa [← List.mem_toFinset,he] using fresh
  let rest := keepWord saveY y (keepWord saveX x ws)
  let child : (Nat × List Nat × List (Nat × Nat × Nat)) := (fuel - 1,insertWord v rest,(v,x,y) :: history)
  refine ⟨child,⟨a,b,if d then 1 else 0,keep,ha,Or.inr ⟨hab,hb,?_,keepLt⟩,?_⟩,?_⟩
  · cases d <;> decide
  · have eq := binaryChild (fuel := fuel) (history := history) d hab hb (by omega) (by omega) keepLt hx hy p fn
    rw [bx,by'] at eq
    exact eq
  · refine ⟨insertWordNodup (keepNodup (keepNodup nd saveX x) saveY y)
      (fun h => fn (keepSubset saveX x ws _ (keepSubset saveY y _ _ h))),k,t,by change k ≤ fuel - 1; omega,?_⟩
    change LiveWord mask target k t (insertWord v rest).toFinset
    rw [insertWordSet,keepPairSet nd xy he]
    exact tail

theorem wordProgress {mask : Nat} {target : Nat} {state : (Nat × List Nat × List (Nat × Nat × Nat))}
    (width : state.2.1.length ≤ 64) (h : WordViable mask target state) :
    target ∈ state.2.1 ∨ ∃ child,HasChild mask state child ∧ WordViable mask target child := by
  obtain ⟨fuel,ws,history⟩ := state
  obtain ⟨nd,k,t,cap,live⟩ := h
  cases k with
  | zero =>
    obtain ⟨_,eq,_⟩ := live
    left
    change ws.toFinset = {target} at eq
    rw [← List.mem_toFinset,eq]
    simp
  | succ k =>
    right
    rcases live with ⟨u,U,x,_,eq,px,fresh,tail⟩ | ⟨U,x,y,d,eq,px,py,xy,fresh,tail⟩
    · exact unaryProgress nd width cap eq fresh tail
    have xm : x ∈ ws := by rw [← List.mem_toFinset,eq]; simp
    have ym : y ∈ ws := by rw [← List.mem_toFinset,eq]; simp
    have diff : ws.idxOf x ≠ ws.idxOf y := by
      intro same
      apply xy
      rw [← getWord xm,same,getWord ym]
    by_cases h : ws.idxOf x < ws.idxOf y
    · exact binaryProgress nd width cap eq xy h fresh tail
    · have eq' : ws.toFinset = insert y (insert x U) := by rw [eq,Finset.insert_comm]
      have fresh' : binWord d y x ∉ insert y (insert x U) := by
        rw [binWord_comm d y x,Finset.insert_comm]; exact fresh
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
    ∃ token < 2 ^ base.length,(rootWords base token).toFinset = base.toFinset ∩ S := by
  induction base with
  | nil => exact ⟨0,by simp,by simp [rootWords]⟩
  | cons w ws ih =>
    obtain ⟨token,htoken,ih⟩ := ih
    let bit : Nat := if w ∈ S then 1 else 0
    have hbit : bit < 2 := by dsimp [bit]; split <;> decide
    let code := 2 * token + bit
    have low : code &&& 1 = bit := by
      rw [show (1 : Nat) = 2 ^ 1 - 1 from rfl,Nat.and_two_pow_sub_one_eq_mod]
      dsimp [code]
      omega
    have high : code >>> 1 = token := by
      rw [Nat.shiftRight_eq_div_pow]
      change code / 2 = token
      dsimp [code]
      omega
    refine ⟨code,?_,?_⟩
    · simp only [List.length_cons,pow_succ]
      dsimp [code]
      omega
    · change (if code &&& 1 == 0 then rootWords ws (code >>> 1)
        else w :: rootWords ws (code >>> 1)).toFinset = _
      rw [low,high]
      by_cases hw : w ∈ S
      · simp [bit,hw,ih]
      · simp [bit,hw,ih]

theorem liveAgrees {i j k t : Nat} {S : Finset Nat}
    (h : LiveWord mask target k t S) (m : AgreesAt i j mask)
    (all : ∀ w ∈ S,AgreesAt i j w) : AgreesAt i j target := by
  induction h using LiveWord.ind with
  | stop => exact all _ (Finset.mem_singleton_self _)
  | @unary k t U a pa fresh tail ih =>
    apply ih
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · simp only [AgreesAt,Nat.testBit_xor]
      rw [show mask.testBit i = mask.testBit j from m,
        show a.testBit i = a.testBit j from all a (Finset.mem_insert_self _ _)]
    · exact all _ (Finset.mem_insert_of_mem hw)
  | @binary k t U a b d pa pb ab fresh tail ih =>
    apply ih
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · have aa : a.testBit i = a.testBit j := all a (Finset.mem_insert_self _ _)
      have bb : b.testBit i = b.testBit j := all b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      cases d <;> simp [AgreesAt,binWord,Nat.testBit_and,Nat.testBit_or,aa,bb]
    · exact all _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw))

theorem positiveInMask {i : Nat} (mt : Masked mask target) (ht : target.testBit i = true) :
    mask.testBit i = true := by
  have h := congrArg (fun n : Nat => n.testBit i) mt
  simpa [Nat.testBit_and,ht] using h

variable {rows : Nat}

def fM (rows : Nat) : Nat := 2 ^ rows - 1

theorem notNat (v : BitVec rows) : (~~~v).toNat = fM rows ^^^ v.toNat := by
  rw [← BitVec.xor_allOnes,BitVec.toNat_xor,Nat.xor_comm,BitVec.toNat_allOnes]
  rfl

theorem gateOfAvailable {bank : List Nat} {w : Nat}
    (av : AvailableWord mask bank w) : GateWord mask bank w :=
  Or.inr ⟨w,0,av,Or.inl rfl,Or.inr (by simp)⟩

theorem toNatAvailable (bank : List (BitVec rows)) (i : Nat) :
    AvailableWord (fM rows) (bank.map BitVec.toNat) (bank.getD i 0).toNat := by
  rw [List.getD_eq_getElem?_getD]
  cases h : bank[i]? with
  | none => exact Or.inl rfl
  | some a => exact Or.inr (Or.inr (List.mem_map_of_mem (List.mem_of_getElem? h)))

def buildable (m g : Nat) : Nat → Finset (Nat) → Prop
  | 0,s => g ∈ s
  | n+1,s => buildable m g n s ∨
    (∃ a ∈ s,buildable m g n (insert (m ^^^ a) s)) ∨
    (∃ a ∈ s,∃ b ∈ s,∃ d,buildable m g n (insert (binWord d a b) s))

theorem supplyPool {m g : Nat} {n s q} (sub : s ⊆ q) (h : buildable m g n s) : buildable m g n q := by
  induction n generalizing s q with
  | zero => exact sub h
  | succ n ih =>
    rcases h with h | ⟨a,ha,h⟩ | ⟨a,ha,b,hb,d,h⟩
    · exact Or.inl (ih sub h)
    · exact Or.inr (Or.inl ⟨a,sub ha,ih (Finset.insert_subset_insert _ sub) h⟩)
    · exact Or.inr (Or.inr ⟨a,sub ha,b,sub hb,d,ih (Finset.insert_subset_insert _ sub) h⟩)

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
  simp only [Nat.testBit_and,Nat.testBit_xor] at h ⊢
  cases he : m.testBit i
  · simp
  · have hm : mask.testBit i = true := by simpa [he] using h
    simp [hm]

theorem cofBinary (m a b : Nat) (d : Bool) :
    binWord d a b &&& m = binWord d (a &&& m) (b &&& m) := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases d <;> simp only [binWord,Bool.false_eq_true,ite_false,ite_true,Nat.testBit_and,Nat.testBit_or] <;>
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
    simp [binWord,ha,hb]

theorem simpleBin {m a b : Nat} {d : Bool} (h : maskedFlat m a ∨ maskedFlat m b) :
    binWord d a b &&& m = 0 ∨ binWord d a b &&& m = m ∨
      binWord d a b &&& m = a &&& m ∨ binWord d a b &&& m = b &&& m := by
  rw [cofBinary]
  have top1 (x : Nat) : m &&& (x &&& m) = x &&& m := by
    rw [Nat.land_comm x m,← Nat.land_assoc]
    simp
  have top2 (x : Nat) : m ||| (x &&& m) = m := by
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_or,Nat.testBit_and]
    cases x.testBit i <;> cases m.testBit i <;> rfl
  have right1 (x : Nat) : (x &&& m) &&& m = x &&& m := restrictWord m x
  have right2 (x : Nat) : (x &&& m) ||| m = m := by rw [Nat.lor_comm,top2]
  rcases h with (ha|ha)|(hb|hb) <;> cases d <;>
    simp [binWord, *,top1,top2,right1,right2]

def projectedStock (m : Nat) (s : Finset (Nat)) := insert 0 (insert m (visibleWords m s))

theorem maskedBuild {goal : Nat} {k t s} (run : LiveWord mask goal k t s) (m : Nat) (submask : mask &&& m = m) (properGoal : ¬ maskedFlat m goal) :
    ∃ n,n+(flatSet m s).card ≤ k ∧ buildable m (goal &&& m) n (projectedStock m s) := by
  induction run using LiveWord.ind with
  | stop =>
    refine ⟨0,?_,?_⟩
    · simp only [flatSet,Finset.filter_singleton,properGoal,ite_false,Finset.card_empty,
        Nat.add_zero,Nat.le_refl]
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
  simp [availableB,AvailableWord,or_assoc]

theorem recipeGate_spec {mask : Nat} {bank : List Nat} {v a b : Nat}
    (h : recipeGate mask bank v a b = true) : GateWord mask bank v := by
  simp only [recipeGate,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,availableB_spec] at h
  rcases h with ⟨ha,first | ⟨hb,second⟩⟩
  · exact Or.inl ⟨a,ha,first⟩
  · exact Or.inr ⟨a,b,ha,hb,second⟩

theorem replayRecipesBuilds (mask : Nat) (needed : List Nat) (recipes : List (Nat × Nat × Nat))
    (bank : List Nat) : WordBuilds mask bank (replayRecipes mask needed recipes bank) := by
  induction recipes generalizing bank with
  | nil => trivial
  | cons recipe recipes ih =>
    obtain ⟨w,a,b⟩ := recipe
    change WordBuilds mask bank
      (if needed.contains (w &&& mask) && !availableB mask bank (w &&& mask) &&
          recipeGate mask bank (w &&& mask) (a &&& mask) (b &&& mask) then
        (w &&& mask) :: replayRecipes mask needed recipes ((w &&& mask) :: bank)
      else replayRecipes mask needed recipes bank)
    split
    · rename_i yes
      exact ⟨recipeGate_spec (Bool.and_eq_true_iff.mp yes).2,ih _⟩
    · exact ih _

theorem flatCountCard (mask : Nat) {words : List Nat} (nodup : words.Nodup) :
    flatCount mask words = (flatSet mask words.toFinset).card := by
  induction words with
  | nil => rfl
  | cons w ws ih =>
    have nd := List.nodup_cons.mp nodup
    have fresh : w ∉ ws.toFinset := by simpa using nd.1
    have bool : maskFlat mask w = true ↔ maskedFlat mask w := by
      simp [maskFlat,maskedFlat]
    change (if maskFlat mask w then flatCount mask ws + 1 else flatCount mask ws) = _
    rw [List.toFinset_cons,flIns fresh,ih nd.2]
    by_cases h : maskedFlat mask w
    · simp [h,bool.mpr h]
    · have no : maskFlat mask w = false := Bool.eq_false_iff.mpr (fun ht => h (bool.mp ht))
      simp [h,no]

theorem buildsAppend {mask : Nat} {roots first second : List Nat}
    (left : WordBuilds mask roots first)
    (right : WordBuilds mask (first ++ roots) second) :
    WordBuilds mask roots (first ++ second) := by
  induction first generalizing roots with
  | nil => exact right
  | cons w ws ih =>
    refine ⟨left.1,ih left.2 ?_⟩
    have same (bank other vals : List Nat) (perm : bank.Perm other)
        (h : WordBuilds mask bank vals) : WordBuilds mask other vals := by
      induction vals generalizing bank other with
      | nil => trivial
      | cons v vs ih =>
        exact ⟨gateWeaken (fun x hx => Or.inr (Or.inr (perm.mem_iff.mp hx))) h.1,
          ih _ _ (perm.cons v) h.2⟩
    exact same _ _ _ (List.perm_middle (a := w) (l₁ := ws) (l₂ := roots)).symm right

theorem buildableWords {mask goal n : Nat} {pool : Finset Nat} {bank : List Nat}
    (h : buildable mask goal n pool) (supply : ∀ w ∈ pool,AvailableWord mask bank w) :
    ∃ values,values.length ≤ n ∧ WordBuilds mask bank values ∧
      AvailableWord mask (values ++ bank) goal := by
  induction n generalizing pool bank with
  | zero => exact ⟨[],Nat.le_refl _,trivial,supply _ h⟩
  | succ n ih =>
    have add {w : Nat} (g : GateWord mask bank w)
        (tail : buildable mask goal n (insert w pool)) :
        ∃ values,values.length ≤ n+1 ∧ WordBuilds mask bank values ∧
          AvailableWord mask (values ++ bank) goal := by
      have growing : ∀ v ∈ insert w pool,AvailableWord mask (w :: bank) v := by
        intro v hv
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact Or.inr (Or.inr List.mem_cons_self)
        · exact availableWeaken (fun _ hh => Or.inr (Or.inr (List.mem_cons_of_mem _ hh))) (supply _ hv)
      obtain ⟨values,budget,build,hit⟩ := ih tail growing
      refine ⟨w :: values,by simp only [List.length_cons]; omega,⟨g,build⟩,?_⟩
      rcases hit with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (by simp only [List.mem_append,List.mem_cons] at *; tauto))
    rcases h with h | ⟨a,ha,h⟩ | ⟨a,ha,b,hb,d,h⟩
    · obtain ⟨values,cap,build,hit⟩ := ih h supply
      exact ⟨values,by omega,build,hit⟩
    · exact add (Or.inl ⟨a,supply a ha,rfl⟩) h
    · apply add (w := binWord d a b) ?_ h
      exact Or.inr ⟨a,b,supply a ha,supply b hb,by cases d <;> simp [binWord]⟩

theorem boundClosesSound {state : (Nat × List Nat × List (Nat × Nat × Nat))} {bound : (Nat × List Nat × Nat × Nat)}
    (known : Lower bound.1 bound.2.1 bound.2.2.2 bound.2.2.1)
    (submask : mask &&& bound.1 = bound.1)
    (viable : WordViable mask target state) :
    boundCloses target state bound = false := by
  obtain ⟨fuel,ws,history⟩ := state
  obtain ⟨cut,stock,minimum,goal⟩ := bound
  obtain ⟨nd,k,t,steps,live⟩ := viable
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
  simp only [Bool.and_eq_true,beq_iff_eq,bne_iff_ne] at hc
  obtain ⟨⟨⟨goalEq,nonzero⟩,nonflat⟩,scan⟩ := hc
  split at scan <;> try contradiction
  split at scan <;> try contradiction
  split at scan <;> try contradiction
  rcases Bool.and_eq_true_iff.mp scan with ⟨length,sources⟩
  simp only [decide_eq_true_eq] at length
  have pn : ¬maskedFlat cut target := by simpa [maskedFlat,goalEq] using And.intro nonzero nonflat
  obtain ⟨n,hn,build⟩ := maskedBuild live cut submask pn
  rw [← flatCountCard cut nd] at hn
  change n + flatCount cut ws ≤ k at hn
  have supply : ∀ w ∈ projectedStock cut ws.toFinset,AvailableWord cut (replay ++ stock) w := by
    intro w hw
    simp only [projectedStock,visibleWords,Finset.mem_insert,Finset.mem_image,
      List.mem_toFinset] at hw
    rcases hw with rfl | rfl | ⟨v,hv,rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact availableB_spec.mp (List.all_eq_true.mp sources v hv)
  obtain ⟨ys,hy,built,avail⟩ := buildableWords build supply
  have both := buildsAppend (replayRecipesBuilds cut _ history.reverse stock) built
  have hit : AvailableWord cut ((replay ++ ys) ++ stock) goal := by
    rw [← goalEq]
    exact availableWeaken (fun v hv => Or.inr (Or.inr (by
      simpa [List.mem_append,or_assoc,or_left_comm,or_comm] using hv))) avail
  have enough := known (replay ++ ys) both hit
  simp only [List.length_append] at enough
  omega

theorem knownClosesSound {bounds : List (Nat × List Nat × Nat × Nat)} {state : (Nat × List Nat × List (Nat × Nat × Nat))}
    (known : Known bounds) (submask : ∀ b ∈ bounds,mask &&& b.1 = b.1)
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
  simp only [encodePoint,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]

theorem encodeAnd (a b : (Fin rows → Bool)) :
    encodePoint (fun i => a i && b i) = encodePoint a &&& encodePoint b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and,encodeBit a ⟨i,hi⟩,encodeBit b ⟨i,hi⟩,encodeBit _ ⟨i,hi⟩]

theorem encodeOr (a b : (Fin rows → Bool)) :
    encodePoint (fun i => a i || b i) = encodePoint a ||| encodePoint b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_or,encodeBit a ⟨i,hi⟩,encodeBit b ⟨i,hi⟩,encodeBit _ ⟨i,hi⟩]

def pointWord (f : (Fin rows → Bool)) : Nat := (encodePoint f).toNat

def relabel (sourceIndex : Fin rows → Fin rows) (word : Nat) : Nat :=
  pointWord fun i => word.testBit (sourceIndex i).val

theorem pointZero : pointWord (fun _ : Fin rows => false) = 0 := by
  have eq : encodePoint (fun _ : Fin rows => false) = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [encodeBit _ ⟨i,hi⟩]
    simp
  simp [pointWord,eq]

theorem relabelZero (sourceIndex : Fin rows → Fin rows) : relabel sourceIndex 0 = 0 := by
  simpa [relabel] using (pointZero (rows := rows))

theorem relabelAnd (sourceIndex : Fin rows → Fin rows) (a b : Nat) :
    relabel sourceIndex (a &&& b) = relabel sourceIndex a &&& relabel sourceIndex b := by
  simp only [relabel,Nat.testBit_and,pointWord,encodeAnd,BitVec.toNat_and]

theorem relabelOr (sourceIndex : Fin rows → Fin rows) (a b : Nat) :
    relabel sourceIndex (a ||| b) = relabel sourceIndex a ||| relabel sourceIndex b := by
  simp only [relabel,Nat.testBit_or,pointWord,encodeOr,BitVec.toNat_or]

theorem relabelXor (sourceIndex : Fin rows → Fin rows) (a b : Nat) :
    relabel sourceIndex (a ^^^ b) = relabel sourceIndex a ^^^ relabel sourceIndex b := by
  have eq : encodePoint (fun i => (a ^^^ b).testBit (sourceIndex i).val) =
      encodePoint (fun i => a.testBit (sourceIndex i).val) ^^^
      encodePoint (fun i => b.testBit (sourceIndex i).val) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_xor,encodeBit _ ⟨i,hi⟩,encodeBit _ ⟨i,hi⟩,encodeBit _ ⟨i,hi⟩]
    exact Nat.testBit_xor ..
  simpa only [relabel,pointWord,BitVec.toNat_xor] using congrArg BitVec.toNat eq

theorem relabelBit (sourceIndex : Fin rows → Fin rows) (word : Nat) (i : Fin rows) :
    (relabel sourceIndex word).testBit i.val = word.testBit (sourceIndex i).val :=
  encodeBit _ i

theorem relabelOutside (sourceIndex : Fin rows → Fin rows) (word i : Nat) (h : rows ≤ i) :
    (relabel sourceIndex word).testBit i = false := by
  apply Nat.testBit_lt_two_pow
  exact Nat.lt_of_lt_of_le (show (encodePoint _).toNat < 2 ^ rows from BitVec.isLt _)
    (Nat.pow_le_pow_right (by decide) h)

theorem relabelInj (sourceIndex : Fin rows → Fin rows) (onto : Function.Surjective sourceIndex)
    {a b : Nat} (ba : Masked (fM rows) a) (bb : Masked (fM rows) b)
    (eq : relabel sourceIndex a = relabel sourceIndex b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases inside : i < rows
  · obtain ⟨j,h⟩ := onto ⟨i,inside⟩
    have bit := congrArg (fun w : Nat => w.testBit j.val) eq
    simpa only [relabelBit,h] using bit
  · have ea := congrArg (fun w : Nat => w.testBit i) ba
    have eb := congrArg (fun w : Nat => w.testBit i) bb
    simp only [Nat.testBit_and,fM,Nat.testBit_two_pow_sub_one,inside,decide_false,
      Bool.and_false] at ea eb
    rw [← ea,← eb]

theorem kw_step (goal : Nat) (D D' : Finset Nat) (u v w : ℕ) (c : ℕ → ℕ → Bool) (f : ℕ → ℕ → ℕ)
    (hu : u ∈ D) (hv : v ∈ D) (huv : u ≠ v) (huD : u ∉ D') (hvD : v ∉ D')
    (hsub : ∀ x ∈ D',x ≠ w → x ∈ D)
    (hf : ∀ e i,goal.testBit e = true → goal.testBit i = false →
      f e i ∈ D' ∧ (f e i).testBit e = true ∧ (f e i).testBit i = false)
    (hr : ∀ e i e' i',goal.testBit e = true → goal.testBit e' = true → goal.testBit i = false → goal.testBit i' = false → f e i = f e' i' → f e i' = f e i)
    (hcu : ∀ e i,w.testBit e = true → w.testBit i = false → c e i = true →
      u.testBit e = true ∧ u.testBit i = false)
    (hcv : ∀ e i,w.testBit e = true → w.testBit i = false → c e i = false →
      v.testBit e = true ∧ v.testBit i = false)
    (hc : ∀ e i e' i',c e i = c e' i' → c e i' = c e i) :
    ∃ g : ℕ → ℕ → ℕ,
      (∀ e i,goal.testBit e = true → goal.testBit i = false →
        g e i ∈ D ∧ (g e i).testBit e = true ∧ (g e i).testBit i = false) ∧
      (∀ e i e' i',goal.testBit e = true → goal.testBit e' = true → goal.testBit i = false → goal.testBit i' = false → g e i = g e' i' → g e i' = g e i) := by
  have hg : ∀ e i,goal.testBit e = true → goal.testBit i = false → f e i = w →
      ((if f e i = w then (cond (c e i) u v) else f e i) = u ∧ c e i = true) ∨
      ((if f e i = w then (cond (c e i) u v) else f e i) = v ∧ c e i = false) := by
    intro e i _ _ h
    rw [ite_eq_left (h)]
    cases c e i
    · exact Or.inr ⟨rfl,rfl⟩
    · exact Or.inl ⟨rfl,rfl⟩
  refine ⟨fun e i => if f e i = w then (cond (c e i) u v) else f e i,?_,?_⟩
  · intro e i he hi
    obtain ⟨h1,h2,h3⟩ := hf e i he hi
    show (if f e i = w then (cond (c e i) u v) else f e i) ∈ D ∧
      (if f e i = w then (cond (c e i) u v) else f e i).testBit e = true ∧
      (if f e i = w then (cond (c e i) u v) else f e i).testBit i = false
    by_cases hw : f e i = w
    · rw [hw] at h2 h3
      rcases hg e i he hi hw with ⟨hx,hcc⟩ | ⟨hx,hcc⟩
      · rw [hx]; exact ⟨hu,hcu e i h2 h3 hcc⟩
      · rw [hx]; exact ⟨hv,hcv e i h2 h3 hcc⟩
    · rw [ite_eq_right (hw)]; exact ⟨hsub _ h1 hw,h2,h3⟩
  · intro e i e' i' he he' hi hi' heq
    show (if f e i' = w then (cond (c e i') u v) else f e i') =
      (if f e i = w then (cond (c e i) u v) else f e i)
    have heq' : (if f e i = w then (cond (c e i) u v) else f e i) =
      (if f e' i' = w then (cond (c e' i') u v) else f e' i') := heq
    by_cases h1 : f e i = w
    · by_cases h2 : f e' i' = w
      · have h3 : f e i' = w := (hr e i e' i' he he' hi hi' (h1.trans h2.symm)).trans h1
        have hcc : c e i = c e' i' := by
          rcases hg e i he hi h1 with ⟨hx,hx'⟩ | ⟨hx,hx'⟩ <;>
            rcases hg e' i' he' hi' h2 with ⟨hy,hy'⟩ | ⟨hy,hy'⟩
          · rw [hx',hy']
          · exact absurd (hx.symm.trans (heq'.trans hy)) huv
          · exact absurd (hy.symm.trans (heq'.symm.trans hx)) huv
          · rw [hx',hy']
        rw [ite_eq_left (h3),ite_eq_left (h1),hc e i e' i' hcc]
      · exfalso
        rw [ite_eq_right (h2)] at heq'
        have hm := (hf e' i' he' hi').1
        rcases hg e i he hi h1 with ⟨hx,_⟩ | ⟨hx,_⟩
        · exact huD (by rw [← hx,heq']; exact hm)
        · exact hvD (by rw [← hx,heq']; exact hm)
    · by_cases h2 : f e' i' = w
      · exfalso
        rw [ite_eq_right (h1)] at heq'
        have hm := (hf e i he hi).1
        rcases hg e' i' he' hi' h2 with ⟨hx,_⟩ | ⟨hx,_⟩
        · exact huD (by rw [← hx,← heq']; exact hm)
        · exact hvD (by rw [← hx,← heq']; exact hm)
      · have h1n : (if f e i = w then (cond (c e i) u v) else f e i) = f e i := ite_eq_right h1
        have h2n : (if f e' i' = w then (cond (c e' i') u v) else f e' i') = f e' i' := ite_eq_right h2
        rw [h1n,h2n] at heq'
        have h3 := hr e i e' i' he he' hi hi' heq'
        have h3n : ¬ f e i' = w := by rw [h3]; exact h1
        rw [h1n,ite_eq_right (h3n)]
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
    (∀ e i,goal.testBit e = true → goal.testBit i = false →
      f e i ∈ ws ∧ (f e i).testBit e = true ∧ (f e i).testBit i = false) ∧
    (∀ e i e' i',goal.testBit e = true → goal.testBit e' = true →
      goal.testBit i = false → goal.testBit i' = false → f e i = f e' i' → f e i' = f e i)

theorem kwFromLive {mask goal : Nat} {k : Nat} {S : Finset Nat}
    (live : LiveWord mask goal k 0 S) (tight : S.card = k + 1) : KWPartition goal S := by
  induction k generalizing S with
  | zero =>
    obtain ⟨_,eq,_⟩ := live
    subst S
    exact ⟨fun _ _ => goal,fun _ _ hp hn => ⟨by simp,hp,hn⟩,fun _ _ _ _ _ _ _ _ _ => rfl⟩
  | succ k ih =>
    rcases live with ⟨u,U,a,eq,_⟩ | ⟨U,a,b,op,rfl,pa,pb,ab,fresh,tail⟩
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
    obtain ⟨f,hf,hr⟩ := ih tail (by
      change (insert w U).card = k + 1
      rw [Finset.card_insert_of_notMem wU]
      omega)
    have keepA : a ∉ insert w U := by simp [wA.symm,aU]
    have keepB : b ∉ insert w U := by simp [wB.symm,bU]
    have other : ∀ x ∈ insert w U,x ≠ w → x ∈ insert a (insert b U) := by
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
    ∃ w ∈ S,w.testBit p = true ∧ w.testBit n = false := by
  induction k generalizing S with
  | zero =>
    obtain ⟨_,rfl,_⟩ := live
    exact ⟨goal,by simp,hp,hn⟩
  | succ k ih =>
    rcases live with ⟨u,U,a,ueq,_⟩ | ⟨U,a,b,op,rfl,pa,pb,ab,fresh,tail⟩
    · omega
    obtain ⟨w,hw,wp,wn⟩ := ih tail
    rcases Finset.mem_insert.mp hw with eq | hU
    · subst w
      cases op
      · by_cases ha : a.testBit n = false
        · exact ⟨a,Finset.mem_insert_self ..,and_cu a b p n wp wn (by simp [ha])⟩
        · exact ⟨b,Finset.mem_insert_of_mem (Finset.mem_insert_self ..),
            and_cv a b p n wp wn (by cases h : a.testBit n <;> simp_all)⟩
      · by_cases ha : a.testBit p = true
        · exact ⟨a,Finset.mem_insert_self ..,or_cu a b p n wp wn ha⟩
        · exact ⟨b,Finset.mem_insert_of_mem (Finset.mem_insert_self ..),
            or_cv a b p n wp wn (by cases h : a.testBit p <;> simp_all)⟩
    · exact ⟨w,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU),wp,wn⟩

namespace PackedRect

theorem tb4095 (i : ℕ) : (4095 : ℕ).testBit i = decide (i < 12) := by
  have e : (4095 : ℕ) = 2 ^ 12 - 1 := by norm_num
  rw [e,Nat.testBit_two_pow_sub_one]

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

theorem rect_tb (x J i : ℕ) (hJ : J.testBit i = true) : ∀ n e : ℕ,e < n → x.testBit e = true →
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
      rw [tb_eq,hx]
      simp [Nat.testBit_shiftLeft,hJ]
    · rw [ih e (by omega) hx]
      simp

theorem rectW_tb (x e i : ℕ) (he : e < 12) (hi : i < 12) (h1 : x.testBit e = true)
    (h2 : x.testBit (12 + i) = false) : (rectW x).testBit (12 * e + i) = true := by
  apply rect_tb _ _ _ _ 12 e he h1
  show ((x >>> 12) ^^^ 4095).testBit i = true
  rw [Nat.testBit_xor,Nat.testBit_shiftRight,h2,tb4095]
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
  rw [full_eq,Nat.testBit_two_pow_sub_one]

theorem land_sub (h a : ℕ) (H : ∀ q,h.testBit q = true → a.testBit q = true) :
    Nat.land h a = h := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [tb_land]
  cases hh : h.testBit q
  · rfl
  · rw [H q hh]; rfl

theorem land_disj (a h : ℕ) (H : ∀ q,a.testBit q = true → h.testBit q = true → False) :
    Nat.land a h = 0 := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [tb_land,Nat.zero_testBit]
  cases ha : a.testBit q
  · rfl
  · cases hh : h.testBit q
    · rfl
    · exact (H q ha hh).elim

def orS (x s : ℕ) : ℕ := Nat.lor x (Nat.shiftRight x s)

def orSL (x s : ℕ) : ℕ := Nat.lor x (Nat.shiftLeft x s)

theorem orS_tb (x s q : ℕ) : (orS x s).testBit q = (x.testBit q || x.testBit (s + q)) := by
  show (x ||| x >>> s).testBit q = _
  rw [Nat.testBit_or,Nat.testBit_shiftRight]

theorem orSL_tb (x s q : ℕ) :
    (orSL x s).testBit q = (x.testBit q || (decide (s ≤ q) && x.testBit (q - s))) := by
  show (x ||| x <<< s).testBit q = _
  simp only [Nat.testBit_or,Nat.testBit_shiftLeft,ge_iff_le]

theorem orS_ex (k p x n s : ℕ)
    (hx : ∀ q,x.testBit q = true → ∃ j,j < n ∧ p.testBit (k * j + q) = true) (q : ℕ)
    (h : (orS x (k * s)).testBit q = true) : ∃ j,j < n + s ∧ p.testBit (k * j + q) = true := by
  rw [orS_tb,Bool.or_eq_true] at h
  rcases h with h | h
  · obtain ⟨j,hj,hp⟩ := hx q h
    exact ⟨j,by omega,hp⟩
  · obtain ⟨j,hj,hp⟩ := hx _ h
    refine ⟨j + s,by omega,?_⟩
    rw [Nat.mul_add,Nat.add_assoc]; exact hp

theorem orSL_ex (k p x n s : ℕ)
    (hx : ∀ q,x.testBit q = true → ∃ j,j < n ∧ k * j ≤ q ∧ p.testBit (q - k * j) = true)
    (q : ℕ) (h : (orSL x (k * s)).testBit q = true) :
    ∃ j,j < n + s ∧ k * j ≤ q ∧ p.testBit (q - k * j) = true := by
  rw [orSL_tb,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at h
  rcases h with h | ⟨hs,h⟩
  · obtain ⟨j,hj,hq,hp⟩ := hx q h
    exact ⟨j,by omega,hq,hp⟩
  · obtain ⟨j,hj,hq,hp⟩ := hx _ h
    have e : q - k * (j + s) = q - k * s - k * j := by rw [Nat.mul_add]; omega
    refine ⟨j + s,by omega,?_,?_⟩
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
  have hall : ∀ q : ℕ,q < 144 → rowM.testBit q = true → q % 12 = 0 := by decide +kernel
  exact ⟨hlt,hall q hlt h⟩

def rowsOf (p : ℕ) : ℕ := Nat.land (orS (orS (orS (orS p 6) 3) 1) 1) rowM

def colsOf (p : ℕ) : ℕ := Nat.land (orS (orS (orS (orS p 96) 48) 24) 12) 4095

def hullC (p : ℕ) : ℕ :=
  Nat.land (orSL (orSL (orSL (orSL (rowsOf p) 6) 3) 1) 1)
    (orSL (orSL (orSL (orSL (colsOf p) 96) 48) 24) 12)

def hull (p : ℕ) : ℕ := hullC (Nat.land p full)

theorem rowsOf_tb (p q : ℕ) (h : (rowsOf p).testBit q = true) :
    (q < 144 ∧ q % 12 = 0) ∧ ∃ j,j < 12 ∧ p.testBit (j + q) = true := by
  unfold rowsOf at h
  rw [tb_land,Bool.and_eq_true] at h
  refine ⟨rowM_tb q h.2,?_⟩
  have h0 : ∀ q,p.testBit q = true → ∃ j,j < 1 ∧ p.testBit (1 * j + q) = true :=
    fun q hq => ⟨0,by norm_num,by simpa using hq⟩
  have h1 := orS_ex 1 p _ 1 6 h0
  have h2 := orS_ex 1 p _ _ 3 h1
  have h3 := orS_ex 1 p _ _ 1 h2
  have h4 := orS_ex 1 p _ _ 1 h3
  obtain ⟨j,hj,hp⟩ := h4 q h.1
  exact ⟨j,by omega,by simpa using hp⟩

theorem colsOf_tb (p q : ℕ) (h : (colsOf p).testBit q = true) :
    q < 12 ∧ ∃ j,j < 16 ∧ p.testBit (12 * j + q) = true := by
  unfold colsOf at h
  rw [tb_land,Bool.and_eq_true,tb4095,decide_eq_true_eq] at h
  refine ⟨h.2,?_⟩
  have h0 : ∀ q,p.testBit q = true → ∃ j,j < 1 ∧ p.testBit (12 * j + q) = true :=
    fun q hq => ⟨0,by norm_num,by simpa using hq⟩
  have h1 := orS_ex 12 p _ 1 8 h0
  have h2 := orS_ex 12 p _ _ 4 h1
  have h3 := orS_ex 12 p _ _ 2 h2
  have h4 := orS_ex 12 p _ _ 1 h3
  obtain ⟨j,hj,hp⟩ := h4 q h.1
  exact ⟨j,by omega,hp⟩

theorem hullC_spec (p : ℕ) (hp : ∀ q,p.testBit q = true → q < 144) (q : ℕ)
    (h : (hullC p).testBit q = true) :
    q < 144 ∧ ∃ i e',i < 12 ∧ e' < 12 ∧ p.testBit (12 * (q / 12) + i) = true ∧
      p.testBit (12 * e' + q % 12) = true := by
  unfold hullC at h
  rw [tb_land,Bool.and_eq_true] at h
  obtain ⟨hR,hC⟩ := h
  have r0 : ∀ q,(rowsOf p).testBit q = true →
      ∃ j,j < 1 ∧ 1 * j ≤ q ∧ (rowsOf p).testBit (q - 1 * j) = true :=
    fun q hq => ⟨0,by norm_num,by omega,by simpa using hq⟩
  have r1 := orSL_ex 1 (rowsOf p) _ 1 6 r0
  have r2 := orSL_ex 1 (rowsOf p) _ _ 3 r1
  have r3 := orSL_ex 1 (rowsOf p) _ _ 1 r2
  have r4 := orSL_ex 1 (rowsOf p) _ _ 1 r3
  obtain ⟨j,hj,hjq,hr⟩ := r4 q hR
  obtain ⟨⟨hb,hm⟩,i,hi,hpi⟩ := rowsOf_tb p _ hr
  have c0 : ∀ q,(colsOf p).testBit q = true →
      ∃ j,j < 1 ∧ 12 * j ≤ q ∧ (colsOf p).testBit (q - 12 * j) = true :=
    fun q hq => ⟨0,by norm_num,by omega,by simpa using hq⟩
  have c1 := orSL_ex 12 (colsOf p) _ 1 8 c0
  have c2 := orSL_ex 12 (colsOf p) _ _ 4 c1
  have c3 := orSL_ex 12 (colsOf p) _ _ 2 c2
  have c4 := orSL_ex 12 (colsOf p) _ _ 1 c3
  obtain ⟨j',hj',hjq',hc⟩ := c4 q hC
  obtain ⟨hlt,e',he',hpe⟩ := colsOf_tb p _ hc
  have e1 : i + (q - 1 * j) = 12 * (q / 12) + i := by omega
  have e2 : q - 12 * j' = q % 12 := by omega
  rw [e1] at hpi
  rw [e2] at hpe
  have hb' := hp _ hpe
  exact ⟨by omega,i,e',hi,by omega,hpi,hpe⟩

theorem hull_spec (p q : ℕ) (h : (hull p).testBit q = true) :
    q < 144 ∧ ∃ i e',i < 12 ∧ e' < 12 ∧ p.testBit (12 * (q / 12) + i) = true ∧
      p.testBit (12 * e' + q % 12) = true := by
  have hp : ∀ q,(Nat.land p full).testBit q = true → q < 144 := by
    intro q hq
    rw [tb_land,full_tb,Bool.and_eq_true,decide_eq_true_eq] at hq
    exact hq.2
  obtain ⟨h1,i,e',hi,he,ha,hb⟩ := hullC_spec _ hp q h
  rw [tb_land,Bool.and_eq_true] at ha hb
  exact ⟨h1,i,e',hi,he,ha.1,hb.1⟩

def tw : List ℕ → ℕ → ℕ → ℕ
  | [],_,t => t
  | a :: l,o,t => tw l (Nat.lor o a) (Nat.lor t (Nat.land o a))

def priv (t a : ℕ) : ℕ := hull (Nat.land a (Nat.xor t full))

def hullsOK (t : ℕ) : List ℕ → ℕ → Bool
  | [],_ => true
  | a :: l,acc => Nat.beq (Nat.land (priv t a) a) (priv t a) &&
      (Nat.beq (Nat.land acc (priv t a)) 0 && hullsOK t l (Nat.lor acc (priv t a)))

def avOK1 (as : List ℕ) : Bool := hullsOK (tw as 0 0) as 0

def rectOK1 (l : List ℕ) : Bool := avOK1 (l.map rectW)

def IsRect (R : ℕ → Prop) : Prop :=
  ∀ e i e' i' : ℕ,e < 12 → i < 12 → e' < 12 → i' < 12 →
    R (12 * e + i) → R (12 * e' + i') → R (12 * e + i')

def Part (zs : List ((ℕ → Prop) × ℕ)) : Prop :=
  (∀ z ∈ zs,IsRect z.1) ∧
  (∀ z ∈ zs,∀ q,z.1 q → q < 144) ∧
  (zs.Pairwise (fun z z' => ∀ q,z.1 q → z'.1 q → False)) ∧
  (∀ q,q < 144 → ∃ z ∈ zs,z.1 q) ∧
  (∀ z ∈ zs,∀ q,z.1 q → z.2.testBit q = true)

theorem Part.rect {zs : List ((ℕ → Prop) × ℕ)} (h : Part zs) :
    ∀ z ∈ zs,IsRect z.1 := h.1

theorem Part.disj {zs : List ((ℕ → Prop) × ℕ)} (h : Part zs) :
    zs.Pairwise (fun z z' => ∀ q,z.1 q → z'.1 q → False) := h.2.2.1

theorem Part.cov {zs : List ((ℕ → Prop) × ℕ)} (h : Part zs) :
    ∀ q,q < 144 → ∃ z ∈ zs,z.1 q := h.2.2.2.1

theorem Part.sub {zs : List ((ℕ → Prop) × ℕ)} (h : Part zs) :
    ∀ z ∈ zs,∀ q,z.1 q → z.2.testBit q = true := h.2.2.2.2

theorem pw_forall {α : Type} {R : α → α → Prop} (hs : ∀ a b,R a b → R b a) :
    ∀ l : List α,l.Pairwise R → ∀ a ∈ l,∀ b ∈ l,a ≠ b → R a b := by
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

theorem tw_spec (q : ℕ) : ∀ (as : List ℕ) (o t : ℕ),(tw as o t).testBit q = false →
    t.testBit q = false ∧ (o.testBit q = true → ∀ a ∈ as,a.testBit q = false) ∧
    as.Pairwise (fun a b => ¬ (a.testBit q = true ∧ b.testBit q = true)) := by
  intro as
  induction as with
  | nil => intro o t h; exact ⟨h,fun _ a ha => by simp at ha,List.Pairwise.nil⟩
  | cons a l ih =>
    intro o t h
    obtain ⟨h1,h2,h3⟩ := ih (Nat.lor o a) (Nat.lor t (Nat.land o a)) h
    rw [tb_lor,Bool.or_eq_false_iff,tb_land] at h1
    refine ⟨h1.1,?_,?_⟩
    · intro ho b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · have h4 := h1.2
        rw [ho] at h4
        simpa using h4
      · exact h2 (by rw [tb_lor,ho]; rfl) b hb
    · refine List.pairwise_cons.mpr ⟨?_,h3⟩
      intro b hb hab
      have h4 := h2 (by rw [tb_lor,hab.1]; simp) b hb
      rw [h4] at hab
      exact Bool.noConfusion hab.2

theorem priv_in {zs : List ((ℕ → Prop) × ℕ)} (hP : Part zs) : ∀ z ∈ zs,∀ q,
    (priv (tw (zs.map Prod.snd) 0 0) z.2).testBit q = true → z.1 q := by
  intro z hz q hq
  obtain ⟨hq144,i,e',hi,he',ha,hb⟩ := hull_spec _ q hq
  have key : ∀ x,x < 144 →
      (Nat.land z.2 (Nat.xor (tw (zs.map Prod.snd) 0 0) full)).testBit x = true → z.1 x := by
    intro x hx hbit
    rw [tb_land,tb_xor,full_tb,Bool.and_eq_true] at hbit
    obtain ⟨hzx,ht⟩ := hbit
    have ht' : (tw (zs.map Prod.snd) 0 0).testBit x = false := by simpa [hx] using ht
    obtain ⟨_,_,hpw⟩ := tw_spec x _ 0 0 ht'
    rw [List.pairwise_map] at hpw
    obtain ⟨z',hz',hzq⟩ := hP.cov x hx
    by_cases hzz : z' = z
    · rw [← hzz]; exact hzq
    · exfalso
      exact pw_forall (fun a b h h' => h ⟨h'.2,h'.1⟩) zs hpw z' hz' z hz hzz
        ⟨hP.sub z' hz' x hzq,hzx⟩
  have h1 := key _ (by omega) ha
  have h2 := key _ (by omega) hb
  have h3 := hP.rect z hz (q / 12) i e' (q % 12) (by omega) hi he' (Nat.mod_lt _ (by norm_num))
    h1 h2
  rwa [Nat.div_add_mod] at h3

theorem hullsOK_sound (t : ℕ) : ∀ (zs : List ((ℕ → Prop) × ℕ)) (acc : ℕ),
    (∀ z ∈ zs,∀ q,(priv t z.2).testBit q = true → z.1 q) →
    (∀ z ∈ zs,∀ q,z.1 q → z.2.testBit q = true) →
    zs.Pairwise (fun z z' => ∀ q,z.1 q → z'.1 q → False) →
    (∀ q,acc.testBit q = true → ∀ z ∈ zs,¬ z.1 q) →
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
        rw [tb_lor,Bool.or_eq_true] at hq
        rcases hq with hq | hq
        · exact ha q hq z' (List.mem_cons_of_mem _ hz') hz'q
        · exact hd.1 z' hz' q (hz q hq) hz'q)
    show (Nat.beq (Nat.land (priv t z.2) z.2) (priv t z.2) &&
      (Nat.beq (Nat.land acc (priv t z.2)) 0 &&
        hullsOK t (zs.map Prod.snd) (Nat.lor acc (priv t z.2)))) = true
    rw [e1,e2,e3,Nat.beq_refl]
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
    (sub : ∀ w ∈ S,w ∈ stock) (live : LiveWord mask target k t S) :
    witnessWord entry ∈ S := by
  obtain ⟨w,p,n⟩ := entry
  simp only [essentialB,Bool.and_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨mp,mn⟩,tp⟩,tn⟩,unequal⟩,rest⟩ := ok
  by_contra no
  have all : ∀ x ∈ S,AgreesAt p n x := by
    intro x hx
    have h := List.all_eq_true.mp rest x (sub x hx)
    have hw : x ≠ w := fun e => no (by simpa [witnessWord,e] using hx)
    simpa [hw,AgreesAt] using h
  have agree := liveAgrees live (mp.trans mn.symm) all
  have falseBit : target.testBit n = false := by simpa using tn
  simp [AgreesAt,tp,falseBit] at agree

theorem essentialWordsIn {stock : List Nat} {witnesses : List (Nat × Nat × Nat)} {S : Finset Nat} {k t : Nat}
    (ok : witnesses.all (essentialB mask target stock) = true)
    (sub : ∀ w ∈ S,w ∈ stock) (live : LiveWord mask target k t S) :
    (witnesses.map witnessWord).toFinset ⊆ S := by
  intro w hw
  obtain ⟨entry,mem,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hw)
  exact essentialRequired (List.all_eq_true.mp ok entry mem) sub live

theorem eL {stock cutStock : List Nat} {witnesses : List (Nat × Nat × Nat)} {minimum cut prior : Nat}
    (proper : pW mask target)
    (masked : ∀ w ∈ stock,Masked mask w)
    (ok : witnesses.all (essentialB mask target stock) = true)
    (submask : mask &&& cut = cut)
    (cutProper : pW cut (target &&& cut))
    (supplies : ∀ w ∈ stock,AvailableWord cut cutStock (w &&& cut))
    (known : Lower cut cutStock (target &&& cut) prior)
    (bound : minimum ≤ prior + (flatSet cut (witnesses.map witnessWord).toFinset).card) :
    Lower mask stock target minimum := by
  intro values build hit
  obtain ⟨k,t,S,hk,live,sub⟩ := extractWordLive masked build hit proper
  have subW := essentialWordsIn ok sub live
  have subFlat : flatSet cut (witnesses.map witnessWord).toFinset ⊆ flatSet cut S :=
    Finset.filter_subset_filter _ subW
  have card := Finset.card_le_card subFlat
  have pf : ¬maskedFlat cut target := by simpa [maskedFlat,pW] using cutProper
  obtain ⟨n,budget,built⟩ := maskedBuild live cut submask pf
  have starts : ∀ w ∈ projectedStock cut S,AvailableWord cut cutStock w := by
    intro w hw
    simp only [projectedStock,visibleWords,Finset.mem_insert,Finset.mem_image] at hw
    rcases hw with rfl | rfl | ⟨x,hx,rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact supplies _ (sub _ hx)
  obtain ⟨ys,len,built',out⟩ := buildableWords built starts
  have lower := known ys built' out
  omega

def uW (stock : List Nat) (codes : List Nat) : List (Nat × Nat × Nat) :=
  List.rec [] (fun code _ rest =>
    (stock.getD (code >>> 18) 0,(code >>> 9) &&& 511,code &&& 511) :: rest) codes

def DagAuto (mask goal : Nat) (select : Fin rows → Fin rows) : Prop :=
  Function.Surjective select ∧ relabel select mask = mask ∧ relabel select goal = goal

def mixStep (m : (List (Nat × Nat) × List (Nat × Nat))) (w : Nat) : Nat :=
  let left := List.rec 0 (fun (part,n) _ acc => ((w &&& part) <<< n) ||| acc) m.1
  let right := List.rec 0 (fun (part,n) _ acc => ((w &&& part) >>> n) ||| acc) m.2
  left ||| right

def BitLinear (f : Nat → Nat) : Prop :=
  ∀ w i,(f w).testBit i = true ↔ ∃ j,w.testBit j = true ∧ (f (2 ^ j)).testBit i = true

theorem bitLinearZero : BitLinear (fun _ => 0) := by
  simp [BitLinear]

theorem bitLinearOr {f g : Nat → Nat} (hf : BitLinear f) (hg : BitLinear g) :
    BitLinear (fun w => f w ||| g w) := by
  intro w i
  change ((f w ||| g w).testBit i = true) ↔ _
  simp only [Nat.testBit_or,Bool.or_eq_true]
  rw [hf w i,hg w i]
  constructor
  · rintro (⟨j,hw,hj⟩ | ⟨j,hw,hj⟩)
    · exact ⟨j,hw,Or.inl hj⟩
    · exact ⟨j,hw,Or.inr hj⟩
  · rintro ⟨j,hw,hj | hj⟩
    · exact Or.inl ⟨j,hw,hj⟩
    · exact Or.inr ⟨j,hw,hj⟩

theorem bitLinearLeft (mask n : Nat) : BitLinear (fun w => (w &&& mask) <<< n) := by
  intro w i
  simp only [Nat.testBit_shiftLeft,Nat.testBit_and,Nat.testBit_two_pow,
    Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨h,hw,hm⟩
    exact ⟨i-n,hw,h,rfl,hm⟩
  · rintro ⟨j,hw,h,rfl,hm⟩
    exact ⟨h,hw,hm⟩

theorem bitLinearRight (mask n : Nat) : BitLinear (fun w => (w &&& mask) >>> n) := by
  intro w i
  simp only [Nat.testBit_shiftRight,Nat.testBit_and,Nat.testBit_two_pow,
    Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨hw,hm⟩
    exact ⟨n+i,hw,rfl,hm⟩
  · rintro ⟨j,hw,rfl,hm⟩
    exact ⟨hw,hm⟩

theorem mixStepLinear (move : (List (Nat × Nat) × List (Nat × Nat))) : BitLinear (mixStep move) := by
  obtain ⟨left,right⟩ := move
  unfold mixStep
  apply bitLinearOr
  · induction left with
    | nil => exact bitLinearZero
    | cons entry rest ih =>
      obtain ⟨part,count⟩ := entry
      exact bitLinearOr (bitLinearLeft part count) ih
  · induction right with
    | nil => exact bitLinearZero
    | cons entry rest ih =>
      obtain ⟨part,count⟩ := entry
      exact bitLinearOr (bitLinearRight part count) ih

def mixMove (move : (List (List (Nat × Nat) × List (Nat × Nat)))) (w : Nat) : Nat :=
  (List.rec (motive := fun _ => Nat → Nat) id
    (fun step _ next w => next (mixStep step w)) move) w

theorem bitLinearId : BitLinear id := by
  intro w i
  change w.testBit i = true ↔ ∃ j,w.testBit j = true ∧ (2 ^ j).testBit i = true
  simp [Nat.testBit_two_pow]

theorem bitLinearComp {f g : Nat → Nat} (hf : BitLinear f) (hg : BitLinear g) :
    BitLinear (fun w => f (g w)) := by
  intro w i
  change (f (g w)).testBit i = true ↔ ∃ j,w.testBit j = true ∧ (f (g (2 ^ j))).testBit i = true
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

def pA (axes : List Nat) (offset row : Nat) : Nat :=
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
      rw [relabelBit,Nat.testBit_two_pow]
      simp
    · rintro ⟨j,h,bit⟩
      change (relabel select (2^j)).testBit ii.val = true at bit
      rw [relabelBit,Nat.testBit_two_pow,decide_eq_true_eq] at bit
      exact bit ▸ h
  · rw [relabelOutside _ _ _ (Nat.le_of_not_gt inside)]
    simp [relabelOutside _ _ _ (Nat.le_of_not_gt inside)]

theorem wordMoveAgreement {select : Fin rows → Fin rows} {mask : Nat} {move : (List (List (Nat × Nat) × List (Nat × Nat)))}
    (bounded : Masked (fM rows) mask)
    (basis : ∀ i : Fin rows,mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = relabel select (2 ^ i.val))
    {w : Nat} (masked : Masked mask w) : mixMove move w = relabel select w := by
  apply Nat.eq_of_testBit_eq
  intro i
  apply Bool.eq_iff_iff.mpr
  rw [mixMoveLinear,relabelLinear]
  have source {j : Nat} (bit : w.testBit j = true) :
      mixMove move (2^j) = relabel select (2^j) := by
    have m : mask.testBit j = true := by
      have eq := congrArg (fun x : Nat => x.testBit j) masked
      simpa [Nat.testBit_and,bit] using eq
    have within : j < rows := by
      have eq := congrArg (fun x : Nat => x.testBit j) bounded
      simpa [Nat.testBit_and,fM,Nat.testBit_two_pow_sub_one,m] using eq
    exact basis ⟨j,within⟩ m
  constructor <;> rintro ⟨j,hj,hi⟩
  · exact ⟨j,hj,by rwa [← source hj]⟩
  · exact ⟨j,hj,by rwa [source hj]⟩

theorem relabelBasis {select inverse : Fin rows → Fin rows}
    (left : ∀ i,inverse (select i) = i) :
    ∀ j : Fin rows,select (inverse j) = j →
      relabel select (2 ^ j.val) = 2 ^ (inverse j).val := by
  intro j right
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases inside : i < rows
  · let pos : Fin rows := ⟨i,inside⟩
    change (relabel select (2 ^ j.val)).testBit pos.val = _
    rw [relabelBit,Nat.testBit_two_pow,Nat.testBit_two_pow]
    apply (Bool.eq_iff_iff).mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro eq
      have e : j = select pos := Fin.ext eq
      rw [e,left]
    · intro eq
      have hp : inverse j = pos := Fin.ext eq
      rw [← hp,right]
  · rw [relabelOutside _ _ _ (Nat.le_of_not_gt inside),Nat.testBit_two_pow]
    have ne : (inverse j).val ≠ i := by have := (inverse j).isLt; omega
    simp [ne]

theorem zf {select inverse : Fin rows → Fin rows} {mask goal : Nat} {move : (List (List (Nat × Nat) × List (Nat × Nat)))}
    (left : ∀ i,inverse (select i) = i)
    (right : ∀ i,select (inverse i) = i)
    (bm : Masked (fM rows) mask)
    (gm : Masked mask goal)
    (basis : ∀ i : Fin rows,mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = 2 ^ (inverse i).val)
    (sameMask : mixMove move mask = mask) (sameGoal : mixMove move goal = goal) :
    DagAuto mask goal select ∧ ∀ w,Masked mask w → mixMove move w = relabel select w := by
  have agree {w : Nat} (hw : Masked mask w) : mixMove move w = relabel select w :=
    wordMoveAgreement bm (fun i h => (basis i h).trans (relabelBasis left i (right i)).symm) hw
  exact ⟨⟨fun i => ⟨inverse i,right i⟩,(agree (by simp [Masked])).symm.trans sameMask,
    (agree gm).symm.trans sameGoal⟩,fun _ h => agree h⟩

theorem maskedBelow {mask w : Nat} (bm : Masked (fM rows) mask)
    (bw : Masked mask w) : Masked (fM rows) w := by
  unfold Masked at *
  rw [← bw,Nat.land_assoc,bm,bw]

theorem liveMaskedImage {mask goal : Nat} {select : Fin rows → Fin rows}
    (auto : DagAuto mask goal select) (maskBounds : Masked (fM rows) mask)
    {k t : Nat} {S : Finset Nat} (live : LiveWord mask goal k t S)
    (masked : ∀ w ∈ S,Masked mask w) :
    LiveWord mask goal k t (S.image (relabel select)) := by
  let f := relabel select
  have hmask : f mask = mask := auto.2.1
  have inj {a b : Nat} (ma : Masked mask a) (mb : Masked mask b) :
      f a = f b → a = b :=
    relabelInj select auto.1 (maskedBelow maskBounds ma) (maskedBelow maskBounds mb)
  have proper {a : Nat} (ma : Masked mask a) (ha : pW mask a) :
      pW mask (f a) := by
    exact ⟨fun eq => ha.1 (inj ma (by simp [Masked]) (eq.trans (relabelZero select).symm)),
      fun eq => ha.2 (inj ma (by simp [Masked]) (eq.trans hmask.symm))⟩
  have freshImage {S : Finset Nat} {v : Nat} (hv : v ∉ S) (mv : Masked mask v)
      (ms : ∀ w ∈ S,Masked mask w) : f v ∉ S.image f := by
    intro hw
    obtain ⟨w,hs,eq⟩ := Finset.mem_image.mp hw
    exact hv (inj (ms w hs) mv eq ▸ hs)
  induction live using LiveWord.ind with
  | stop hp =>
    rw [Finset.image_singleton,auto.2.2]
    exact LiveWord.stop hp
  | @unary k t U a ha fresh tail ih =>
    let v := mask ^^^ a
    have ma := masked a (Finset.mem_insert_self ..)
    have mv : Masked mask v := by
      apply maskedGate (bank := [a]) (by simpa using ma)
      exact Or.inl ⟨a,Or.inr (Or.inr (by simp)),rfl⟩
    have hnew : ∀ w ∈ insert v U,Masked mask w := by
      intro w h
      rcases Finset.mem_insert.mp h with rfl | hU
      · exact mv
      · exact masked _ (Finset.mem_insert_of_mem hU)
    have fve : f v = mask ^^^ f a := by
      change relabel select (mask ^^^ a) = _
      rw [relabelXor,auto.2.1]
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
        cases op <;> simp [v,binWord]⟩
    have hnew : ∀ w ∈ insert v U,Masked mask w := by
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
    rw [Finset.image_insert,Finset.image_insert,fve] at hf
    rw [Finset.image_insert,Finset.image_insert]
    exact LiveWord.binary (proper ma pa) (proper mb pb) (fun h => ab (inj ma mb h)) hf ht

def zbp (m : (List (List (Nat × Nat) × List (Nat × Nat)))) (ws : List Nat) : List Nat :=
  List.rec [] (fun w _ next => insertWord (mixMove m w) next) ws

theorem zbC {m : (List (List (Nat × Nat) × List (Nat × Nat)))} {ws : List Nat} {select : Fin rows → Fin rows}
    (agree : ∀ w ∈ ws,mixMove m w = relabel select w) :
    (zbp m ws).toFinset = ws.toFinset.image (relabel select) := by
  induction ws with
  | nil => simp [zbp]
  | cons w ws ih =>
    change (insertWord (mixMove m w) (zbp m ws)).toFinset = _
    rw [insertWordSet,ih (fun w hw => agree _ (List.mem_cons_of_mem _ hw)),
      agree _ List.mem_cons_self,List.toFinset_cons,Finset.image_insert]

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
    rw [Nat.testBit_or,Nat.testBit_and,Nat.testBit_shiftRight,Nat.testBit_shiftLeft]
    cases i with
    | zero => simp
    | succ i =>
      have lt : i < rows.length := by simpa using hi
      simp [ih i lt,Nat.testBit_succ]

def chartWord (chart : ({ rows : List Nat // rows.length = 24 })) (w : Nat) : Nat := chartBits w chart.val

def ChartOK (goal : Nat) (chart : ({ rows : List Nat // rows.length = 24 })) : Prop :=
  (∀ i : Fin 12,goal.testBit (chartRow chart i.val) = true) ∧
  (∀ i : Fin 12,goal.testBit (chartRow chart (12+i.val)) = false)

def chartCheck (goal : Nat) (chart : Option ({ rows : List Nat // rows.length = 24 })) : Bool :=
  chart.all fun c => @decide (ChartOK goal c) (by unfold ChartOK; infer_instance)

theorem cK {goal : Nat} {chart : Option ({ rows : List Nat // rows.length = 24 })}
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
  obtain ⟨f,good,rectangle⟩ := kw
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
      rw [(divmod p n hn).1,(divmod p n hn).2] at h1
      rw [(divmod p' n' hn').1,(divmod p' n' hn').2] at h2
      refine ⟨by omega,?_⟩
      rw [(divmod p n' hn').1,(divmod p n' hn').2]
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
      exact ⟨_,List.mem_map.mpr ⟨_,List.mem_toFinset.mp member,rfl⟩,hq,rfl⟩
    · intro z hz q hq
      obtain ⟨w,_,rfl⟩ := List.mem_map.mp hz
      obtain ⟨bound,same⟩ := hq
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
  simpa only [PackedRect.rectOK1,List.map_map,Function.comp_def,part] using hw

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

def zr {α : Type} (word : Nat) (cont : Nat → α) : α :=
  Nat.rec (cont 0) (fun k _ => cont (k + 1)) word

theorem zM {α : Type} (word : Nat) (cont : Nat → α) :
    zr word cont = cont word := by cases word <;> rfl

def zW (words : List Nat) (cont : List Nat → Bool) : Bool :=
  (List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k [])
    (fun w _ next k => zr w (fun v => next (fun rest => k (v :: rest)))) words) cont

theorem zag (words : List Nat) (cont : List Nat → Bool) :
    zW words cont = cont words := by
  induction words generalizing cont with
  | nil => rfl
  | cons w ws ih =>
    change zr w (fun v => zW ws (fun rest => cont (v :: rest))) = _
    rw [zM,ih]

def zm (target : Nat) (state : (Nat × List Nat × List (Nat × Nat × Nat))) (bound : (Nat × List Nat × Nat × Nat)) : Bool :=
  let (mask,stock,lower,goal) := bound
  let (fuel,ws,history) := state
  (target &&& mask) == goal && goal != 0 && goal != mask &&
    zr (fuel - flatCount mask ws) (fun remaining =>
      if Nat.blt remaining lower then
        zW (recipeStart mask stock ws) (fun start =>
          if Nat.blt (start.length + remaining) lower then
            zW (recipeClosure mask stock history start) (fun needed =>
              if Nat.blt (needed.length + remaining) lower then
                zW (replayRecipes mask needed history.reverse stock) (fun replay =>
                  decide (replay.length + remaining < lower) &&
                    ws.all (fun w => availableB mask (replay ++ stock) (w &&& mask)))
              else false)
          else false)
      else false)

theorem zb (target : Nat) (state : (Nat × List Nat × List (Nat × Nat × Nat))) (bound : (Nat × List Nat × Nat × Nat)) :
    zm target state bound = boundCloses target state bound := by
  obtain ⟨fuel,ws,history⟩ := state
  obtain ⟨mask,stock,lower,goal⟩ := bound
  simp [zm,boundCloses,zag,zM,Nat.blt_eq]

def zt (target : Nat) (bounds : List (Nat × List Nat × Nat × Nat)) (state : (Nat × List Nat × List (Nat × Nat × Nat))) : Bool :=
  List.rec false (fun bound _ later => zm target state bound || later) bounds

theorem zaR (target : Nat) (bounds : List (Nat × List Nat × Nat × Nat)) (state : (Nat × List Nat × List (Nat × Nat × Nat))) :
    zt target bounds state = knownCloses target bounds state := by
  induction bounds with
  | nil => rfl
  | cons bound bounds ih =>
    change (zm target state bound || zt target bounds state) =
      (boundCloses target state bound || knownCloses target bounds state)
    rw [zb,ih]

def za (witnesses : List (Nat × Nat × Nat)) (ws : List Nat) : Bool :=
  witnesses.all (fun entry => ws.contains (witnessWord entry))

def zam (mask : Nat) (stock : List Nat) (fuel : Nat) (forest : (Nat → Nat × Nat))
    (i : Nat) : Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
    (fun _ previous j =>
      let (parent,token) := forest j
      if parent == 0 then
        if token < 2 ^ stock.length then some (rootState stock fuel token) else none
      else (previous (parent - 1)).bind (childState mask token)) (fuel + 1)) i

def zD (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (moves : Array (List (List (Nat × Nat) × List (Nat × Nat)))) (links : (Nat → Nat → Option (Nat × Nat))) (parent token : Nat) (state : (Nat × List Nat × List (Nat × Nat × Nat))) : Bool :=
  match links parent token with
  | none => false
  | some (destination,auto) =>
    Nat.blt destination count &&
      match states destination with
      | none => false
      | some saved =>
        saved.1 == state.1 &&
          if auto == 0 then saved.2.1 == state.2.1
          else match moves[auto-1]? with
               | none => false
               | some m => saved.2.1 == zbp m state.2.1

def zbh (directed : Bool) (ws : List Nat) : Nat → Nat → Bool :=
  List.rec
    (fun p n => Nat.beq p 0 || Nat.beq n 0)
    (fun w _ rest p n =>
      Nat.beq p 0 || Nat.beq n 0 ||
      zr (p &&& w) (fun up =>
        zr (n &&& w) (fun down =>
          rest up down &&
            zr (p ^^^ up) (fun offP =>
              zr (if directed then n else n ^^^ down) (rest offP))))) ws

theorem zbw {v w : Nat} {i : Nat} (bit : (v ^^^ (v &&& w)).testBit i = true) :
    v.testBit i = true ∧ w.testBit i = false := by
  rw [Nat.testBit_xor,Nat.testBit_and] at bit
  cases hv : v.testBit i <;> cases hw : w.testBit i <;> simp [hv,hw] at bit ⊢

theorem zbi {directed : Bool} {ws : List Nat} {positive negative : Nat}
    (fail : zbh directed ws positive negative = false) :
    ∃ p n,positive.testBit p = true ∧ negative.testBit n = true ∧
      ∀ w ∈ ws,if directed then w.testBit p = true → w.testBit n = true
                  else w.testBit p = w.testBit n := by
  have nonempty {w : Nat} (hn : w ≠ 0) : ∃ j,w.testBit j = true := by
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
      zr (positive &&& w) (fun up =>
        zr (negative &&& w) (fun down =>
          zbh directed ws up down &&
            zr (positive ^^^ up) (fun offP =>
              zr (if directed then negative else negative ^^^ down)
                (zbh directed ws offP))))) = false at fail
    simp only [zM,Bool.or_eq_false_iff,Bool.and_eq_false_iff] at fail
    rcases fail.2 with on | off
    · obtain ⟨p,n,hp,hn,agree⟩ := ih on
      rw [Nat.testBit_and,Bool.and_eq_true] at hp hn
      refine ⟨p,n,hp.1,hn.1,?_⟩
      intro a ha
      rcases List.mem_cons.mp ha with rfl | tail
      · simp [hp.2,hn.2]
      · exact agree _ tail
    · obtain ⟨p,n,hp,hn,agree⟩ := ih off
      have hp' := zbw hp
      cases mode : directed
      · have hn' : negative.testBit n = true ∧ w.testBit n = false := by
          apply zbw
          simpa [mode] using hn
        refine ⟨p,n,hp'.1,hn'.1,?_⟩
        intro a ha
        rcases List.mem_cons.mp ha with rfl | tail
        · simp [hp'.2,hn'.2]
        · simpa [mode] using agree _ tail
      · have hn' : negative.testBit n = true := by simpa [mode] using hn
        refine ⟨p,n,hp'.1,hn',?_⟩
        intro a ha
        rcases List.mem_cons.mp ha with rfl | tail
        · simp [hp'.2]
        · simpa [mode] using agree _ tail

theorem zbt {mask goal : Nat} {ws : List Nat} {k t : Nat} {directed : Bool}
    (goalMask : Masked mask goal) (live : LiveWord mask goal k t ws.toFinset)
    (noNot : directed = true → t = 0) :
    zbh directed ws goal (mask ^^^ goal) = true := by
  by_contra fail
  have openPair : zbh directed ws goal (mask ^^^ goal) = false := by
    cases h : zbh directed ws goal (mask ^^^ goal) <;> simp_all
  obtain ⟨p,n,hp,hn,agree⟩ := zbi openPair
  have pm := positiveInMask goalMask hp
  have nm : mask.testBit n = true ∧ goal.testBit n = false := by
    rw [Nat.testBit_xor] at hn
    have implied := fun ht : goal.testBit n = true => positiveInMask goalMask ht
    cases hm : mask.testBit n <;> cases ht : goal.testBit n <;> simp_all
  cases mode : directed with
  | false =>
    have same := liveAgrees live (pm.trans nm.1.symm) (fun w hw => by
      simpa [mode,AgreesAt] using agree w (List.mem_toFinset.mp hw))
    simp [AgreesAt,hp,nm.2] at same
  | true =>
    have ht := noNot mode
    subst t
    obtain ⟨w,hw,a,b⟩ := liveDirected live hp nm.2
    have same := agree w (List.mem_toFinset.mp hw)
    simp [mode,a,b] at same

def zH (tags : List (Nat × Nat)) (use : List (Nat × Nat) → Bool) : Bool :=
  (List.rec (motive := fun _ => (List (Nat × Nat) → Bool) → Bool) (fun k => k [])
    (fun tag _ next k =>
      zr tag.1 (fun up => zr tag.2 (fun down =>
        next (fun tail => k ((up,down)::tail))))) tags) use

theorem zaw (tags : List (Nat × Nat)) (use : List (Nat × Nat) → Bool) :
    zH tags use = use tags := by
  induction tags generalizing use with
  | nil => rfl
  | cons tag rest ih =>
    obtain ⟨a,b⟩ := tag
    change zr a (fun up => zr b (fun down =>
      zH rest (fun tail => use ((up,down)::tail)))) = _
    simp only [zM,ih]

def zV (directed : Bool) (full : Nat) (tag : (Nat × Nat)) : Nat :=
  if directed then tag.1 &&& (tag.2 ^^^ full) else tag.1 ^^^ tag.2

def zk (acc : (Nat × Nat × Nat)) (column : Nat) : (Nat × Nat × Nat) :=
  (acc.1 ||| column,acc.2.1 ||| (acc.1 &&& column),acc.2.2 ||| (acc.2.1 &&& column))

def zg (directed : Bool) (full : Nat) (tags : List (Nat × Nat))
    (use : (Nat × Nat × Nat) → Bool) : Bool :=
  (List.rec (motive := fun _ => ((Nat × Nat × Nat) → Bool) → Bool) (fun k => k (0,0,0))
    (fun tag _ more k =>
      zr (zV directed full tag) (fun column =>
        more (fun acc =>
          zr (acc.1 ||| column) (fun once =>
            zr (acc.2.1 ||| (acc.1 &&& column)) (fun twice =>
              zr (acc.2.2 ||| (acc.2.1 &&& column)) (fun thrice => k (once,twice,thrice)))))))
    tags) use

theorem zi (directed : Bool) (full : Nat) (tags : List (Nat × Nat))
    (use : (Nat × Nat × Nat) → Bool) : zg directed full tags use =
    use (tags.foldr (fun tag acc => zk acc (zV directed full tag)) (0,0,0)) := by
  induction tags generalizing use with
  | nil => rfl
  | cons tag tags ih =>
    change zr (zV directed full tag) (fun column =>
      zg directed full tags (fun acc =>
        zr (acc.1 ||| column) (fun once =>
          zr (acc.2.1 ||| (acc.1 &&& column)) (fun twice =>
            zr (acc.2.2 ||| (acc.2.1 &&& column)) (fun thrice => use (once,twice,thrice)))))) = _
    simp only [zM,ih]
    rfl

def zaB (value : Nat) : Nat :=
  (Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ offset => offset)
    (fun i next w offset =>
      let shift := 1 <<< i
      zr (w >>> shift) (fun upper =>
        if Nat.beq upper 0 then next w offset else next upper (offset+shift))) 8) value 0

def zN (sample : (Nat × Nat)) (full : Nat) (normal tight : (Nat × Nat × Nat))
    (x y out : (Nat × Nat)) (directed : Bool) (op keep : Nat) : List Nat :=
  let counts := if directed then tight else normal
  let dx := if keep.testBit 0 then 0 else zV directed full x
  let dy := if op == 2 || keep.testBit 1 then 0 else zV directed full y
  let rest := counts.2.2 ||| (counts.2.1 ^^^ (counts.2.1 &&& dx &&& dy)) |||
    (counts.1 ^^^ (counts.1 &&& (dx ||| dy)))
  zr ((rest ||| zV directed full out) ^^^ full) (fun missing =>
    if Nat.beq missing 0 then [] else [uP sample.1 18 (zaB missing)])

def zbv (mask goal : Nat) (directed : Bool) (ws : List Nat) (pairs : List Nat) : Bool :=
  pairs.any fun code =>
    let p := code &&& 511
    let n := code >>> 9
    goal.testBit p && mask.testBit n && !goal.testBit n &&
      ws.all (fun w => if directed then !(w.testBit p) || w.testBit n
                       else w.testBit p == w.testBit n)

theorem zbx {mask goal : Nat} {ws : List Nat} {pairs : List Nat} {k t : Nat} {directed : Bool}
    (masked : Masked mask goal) (live : LiveWord mask goal k t ws.toFinset)
    (noNot : directed = true → t = 0) : zbv mask goal directed ws pairs = false := by
  apply Bool.eq_false_iff.mpr
  intro close
  obtain ⟨code,_,check⟩ := List.any_eq_true.mp close
  simp only [Bool.and_eq_true,Bool.not_eq_true,List.all_eq_true] at check
  obtain ⟨⟨⟨hp,mn⟩,hn⟩,bank⟩ := check
  have neg : goal.testBit (code >>> 9) = false := by simpa using hn
  cases mode : directed
  · have h := liveAgrees live ((positiveInMask masked hp).trans mn.symm) (fun w hw => by
      have pair := bank _ (List.mem_toFinset.mp hw)
      simpa [mode,AgreesAt] using pair)
    simp [AgreesAt,hp,neg] at h
  · have ht := noNot mode
    subst t
    obtain ⟨word,mem,on,off⟩ := liveDirected live hp neg
    have pair := bank _ (List.mem_toFinset.mp mem)
    simp [mode,on,off] at pair

def zI (mask goal : Nat) (chart : Option ({ rows : List Nat // rows.length = 24 }))
    (cut : ((Nat × List Nat × List (Nat × Nat × Nat)) → Bool)) (state : (Nat × List Nat × List (Nat × Nat × Nat))) : Bool :=
  let (fuel,ws,_) := state
  ws.length > fuel + 1 ||
    (!ws.contains goal &&
      (fuel == 0 ||
        (if ws.length == fuel + 1 then !zbh true ws goal (mask ^^^ goal)
         else !zbh false ws goal (mask ^^^ goal)) ||
        (if ws.length == fuel + 1 then
           chart.any (fun c => !PackedRect.rectOK1 (ws.map (chartWord c)))
         else false) || cut state))

def zR (n op keep : Nat) : Nat :=
  (n - (if keep.testBit 0 then 0 else 1) -
    (if op == 2 || keep.testBit 1 then 0 else 1)) + 1

def zq (n fuel token : Nat) : Bool :=
  zR n (token / 4 % 3) (token % 4) > (fuel-1) + 1

def zaI (ws : List Nat) (op keep x y : Nat) : List Nat :=
  keepWord (op == 2 || keep.testBit 1) y (keepWord (keep.testBit 0) x ws)

def zK (mask op x y : Nat) : Nat :=
  if Nat.beq op 0 then x &&& y else if Nat.beq op 1 then x ||| y else mask ^^^ x

def zj (mask : Nat) (state : (Nat × List Nat × List (Nat × Nat × Nat))) (a b op keep x y out : Nat) : Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  let (fuel,ws,history) := state
  if fuel == 0 || b ≥ ws.length || (if op == 2 then a != b || keep ≥ 2 else a ≥ b) then none
  else if out == 0 || out == mask || ws.contains out then none
  else
    some (fuel-1,insertWord out (zaI ws op keep x y),(out,x,y) :: history)

theorem zbf {mask a b op keep : Nat} {state : (Nat × List Nat × List (Nat × Nat × Nat))}
    (hb : b < 64) (hop : op < 3) (hk : keep < 4) :
    let x := state.2.1.getD a 0
    let y := state.2.1.getD b 0
    zj mask state a b op keep x y (zK mask op x y) =
      childState mask (gateToken a b op keep) state := by
  obtain ⟨fuel,ws,history⟩ := state
  obtain ⟨keepEq,opEq,aEq,bEq⟩ := gateTokenFields (a := a) hb hop hk
  simp only [childState,keepEq,opEq,aEq,bEq]
  rfl

def zA (stock : List Nat) (positive negative width : Nat) : List (Nat × (Nat × Nat)) :=
  (List.rec (motive := fun _ => Nat → List (Nat × (Nat × Nat))) (fun _ => [])
    (fun w _ next i => (w,uP positive width i,uP negative width i) :: next (i+1)) stock) 0

def zby (bank : List (Nat × (Nat × Nat))) (token : Nat) : List (Nat × (Nat × Nat)) :=
  (List.rec (motive := fun _ => Nat → List (Nat × (Nat × Nat))) (fun _ => [])
    (fun tag _ next k =>
      if Nat.beq (k &&& 1) 0 then next (k >>> 1) else tag :: next (k >>> 1)) bank) token

def zap (keep : Bool) (w : Nat) (bank : List (Nat × (Nat × Nat))) : List (Nat × (Nat × Nat)) :=
  if keep then bank
  else List.rec [] (fun tag tail next => if Nat.beq tag.1 w then tail else tag :: next) bank

def zaq (tag : (Nat × (Nat × Nat))) (bank : List (Nat × (Nat × Nat))) : List (Nat × (Nat × Nat)) :=
  List.rec [tag] (fun old tail next => if Nat.ble tag.1 old.1 then tag :: old :: tail else old :: next) bank

def zbD (mask full token : Nat) (bank : List (Nat × (Nat × Nat))) : List (Nat × (Nat × Nat)) :=
  let keep := token % 4
  let op := token / 4 % 3
  let x := bank.getD (token / (4*3*64)) (0,0,0)
  let y := bank.getD (token / (4*3) % 64) (0,0,0)
  let tag := (zK mask op x.1 y.1,zK full op x.2.1 y.2.1,zK full op x.2.2 y.2.2)
  zaq tag (zap (op == 2 || keep.testBit 1) y.1 (zap (keep.testBit 0) x.1 bank))

def zac (mask width : Nat) (root : List (Nat × (Nat × Nat))) (fuel : Nat) (forest : (Nat → Nat × Nat))
    (i : Nat) : List (Nat × Nat) :=
  let tags := (Nat.rec (motive := fun _ => Nat → List (Nat × (Nat × Nat))) (fun _ => [])
    (fun _ previous j =>
      let (parent,token) := forest j
      if Nat.beq parent 0 then zby root token
      else zbD mask (fM width) token (previous (parent-1))) (fuel+1)) i
  List.rec [] (fun tag _ rest => tag.2 :: rest) tags

def zbn (ws : List Nat) : Nat :=
  List.rec 0 (fun w _ tail => (w &&& fM 64) ||| (tail <<< 64)) ws

def zaQ (n : Nat) : Nat :=
  Nat.rec 0 (fun _ more => 1 ||| (more <<< 64)) n

def zbk (a b : Nat) (left right : Bool) : Nat :=
  (if left then 0 else 1 <<< (64*a)) ||| (if right then 0 else 1 <<< (64*b))

def zbr (mask goal packed marks erased out : Nat) (directed : Bool) (pairs : List Nat) : Bool :=
  pairs.any fun code =>
    zr code (fun code =>
      zr (code &&& 511) (fun p =>
        zr (code >>> 9) (fun n =>
          let up := (packed >>> p) &&& marks
          let down := (packed >>> n) &&& marks
          let contrast := if directed then up &&& (down ^^^ marks) else up ^^^ down
          let gateOK := if directed then !out.testBit p || out.testBit n else out.testBit p == out.testBit n
          goal.testBit p && mask.testBit n && !goal.testBit n && Nat.blt p 64 && Nat.blt n 64 &&
            gateOK && Nat.beq (contrast &&& (marks ^^^ erased)) 0)))

theorem zn {ws : List Nat} {i row : Nat} (inside : i < ws.length) (width : row < 64) :
    (zbn ws).testBit (64*i+row) = (ws.getD i 0).testBit row := by
  induction ws generalizing i with
  | nil => simp at inside
  | cons w ws ih =>
    change ((w &&& fM 64) ||| (zbn ws <<< 64)).testBit (64*i+row) = _
    have test (n j : Nat) : (fM n).testBit j = decide (j < n) := by simp [fM,Nat.testBit_two_pow_sub_one]
    rw [Nat.testBit_or,Nat.testBit_and,Nat.testBit_shiftLeft,test]
    cases i with
    | zero => simp [fM,Nat.testBit_two_pow_sub_one,width,Nat.not_le.mpr width]
    | succ i =>
      have hi : i < ws.length := by simpa using inside
      have crossed : 64 ≤ 64*i.succ+row := by omega
      have offset : 64*i.succ+row-64 = 64*i+row := by omega
      have past : ¬ 64*i.succ+row < 64 := by omega
      simp [crossed,offset,fM,Nat.testBit_two_pow_sub_one,past,ih hi]

theorem zbb {length i : Nat} (inside : i < length) :
    (zaQ length).testBit (64*i) = true := by
  induction length generalizing i with
  | zero => omega
  | succ length ih =>
    change (1 ||| (zaQ length <<< 64)).testBit (64*i) = true
    rw [Nat.testBit_or,Nat.testBit_shiftLeft]
    cases i with
    | zero => simp
    | succ i =>
      have hi : i < length := by omega
      have crossed : 64 ≤ 64*i.succ := by omega
      have offset : 64*i.succ-64 = 64*i := by omega
      simp [crossed,offset,ih hi]

def zd (mask goal : Nat) (chart : Option ({ rows : List Nat // rows.length = 24 })) (cut : ((Nat × List Nat × List (Nat × Nat × Nat)) → Bool))
    (reference : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool) (state : (Nat × List Nat × List (Nat × Nat × Nat))) (sample : (Nat × Nat)) (tags : List (Nat × Nat)) : Bool :=
  let n := state.2.1.length
  (n ≤ 64) && !state.2.1.contains goal &&
  zr (zbn state.2.1) (fun packed =>
    zr (zaQ n) (fun marks =>
      zH tags (fun tags =>
    zr (fM sample.2) (fun full =>
      zg false full tags (fun normal =>
        zg true full tags (fun tight =>
          let visit := fun a b op retains =>
            zr (state.2.1.getD a 0) (fun x =>
              zr (state.2.1.getD b 0) (fun y =>
                zr (zK mask op x y) (fun out =>
                  let xs := tags.getD a (0,0)
                  let ys := tags.getD b (0,0)
                  zr (zK full op xs.1 ys.1) (fun up =>
                    zr (zK full op xs.2 ys.2) (fun down =>
                      tB 0 retains (fun keep =>
                        let token := gateToken a b op keep
                        if zq n state.1 token then true else
                          let directed := zR n op keep == (state.1-1)+1
                          let pairs := zN sample full normal tight xs ys (up,down) directed op keep
                          let erased := zbk a b (keep.testBit 0) (op == 2 || keep.testBit 1)
                          if zbr mask goal packed marks erased out directed pairs then true
                          else match zj mask state a b op keep x y out with
                          | none => true
                          | some (fuel,ws,history) => zW ws (fun forced =>
                            let child := (fuel,forced,history)
                            reference token child || zI mask goal chart cut child)))))))
          tB 0 n (fun a =>
            visit a a 2 2 && tB (a+1) (n-(a+1)) (fun b =>
              tB 0 2 (fun op => visit a b op 4)))))))))

def zF (mask : Nat) (ws : List Nat) : Bool :=
  (ws.dedup.length == ws.length) && ws.all (fun w => w &&& mask == w)

theorem zU {mask : Nat} {ws : List Nat} (ok : zF mask ws = true) :
    ws.Nodup ∧ ∀ w ∈ ws,Masked mask w := by
  simp only [zF,Bool.and_eq_true,beq_iff_eq,List.all_eq_true] at ok
  exact ⟨List.nodup_iff_length_dedup_eq.mpr ok.1,ok.2⟩

def zc (mask goal : Nat) (chart : Option ({ rows : List Nat // rows.length = 24 })) (cut : Nat → ((Nat × List Nat × List (Nat × Nat × Nat)) → Bool))
    (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (moves : Array (List (List (Nat × Nat) × List (Nat × Nat)))) (links : (Nat → Nat → Option (Nat × Nat)))
    (sample : (Nat × Nat)) (tags : Nat → List (Nat × Nat)) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some (fuel,ws,history) => zW ws (fun forced =>
      zF mask forced && zd mask goal chart (cut i)
        (zD count states moves links (i+1)) (fuel,forced,history) sample (tags i))

def ze (mask goal : Nat) (chart : Option ({ rows : List Nat // rows.length = 24 })) (cut : ((Nat × List Nat × List (Nat × Nat × Nat)) → Bool))
    (witnesses : List (Nat × Nat × Nat)) (reference : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool) (stock : List Nat)
    (fuel : Nat) : Bool :=
  tB 0 (2^stock.length) fun token =>
    let state := rootState stock fuel token
    !za witnesses state.2.1 || zI mask goal chart cut state || reference token state

theorem zaP {mask goal : Nat} {chart : Option ({ rows : List Nat // rows.length = 24 })}
    {cut : ((Nat × List Nat × List (Nat × Nat × Nat)) → Bool)} {state : (Nat × List Nat × List (Nat × Nat × Nat))}
    (masked : Masked mask goal) (chartOK : ∀ c,chart = some c → ChartOK goal c)
    (viable : WordViable mask goal state) (noCut : cut state = false) :
    zI mask goal chart cut state = false := by
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
    simp [zI,fit,hm]
  by_cases tight : ws.length = fuel + 1
  · have ht : t = 0 := by omega
    subst t
    have dir := zbt (directed := true) masked live (fun _ => rfl)
    have noChart : chart.any (fun c => !PackedRect.rectOK1 (ws.map (chartWord c))) = false := by
      cases opt : chart with
      | none => rfl
      | some c =>
        have vt : WordViable mask goal (fuel,ws,[]) := viable
        have ok := tightChart (chartOK c opt) tight vt
        simp [ok]
    simp [zI,fit,hz,tight,dir,noCut,noChart]
  · have sep := zbt (directed := false) masked live (by simp)
    simp [zI,fit,hz,tight,sep,noCut]

theorem zbo (w : Nat) (ws : List Nat) :
    (insertWord w ws).length = ws.length + 1 := by
  induction ws with
  | nil => rfl
  | cons a ws ih =>
    change (if w ≤ a then w :: a :: ws else a :: insertWord w ws).length = _
    split <;> simp [ih]

theorem zX (keep : Bool) (w : Nat) (ws : List Nat) :
    ws.length - (if keep then 0 else 1) ≤ (keepWord keep w ws).length := by
  cases keep
  · exact List.le_length_erase
  · simp [keepWord]

theorem zah {mask token : Nat} {state child : (Nat × List Nat × List (Nat × Nat × Nat))}
    (eval : childState mask token state = some child)
    (wide : zq state.2.1.length state.1 token = true) :
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
    some (fuel - 1,insertWord z rest,(z,x,y) :: history)) = some child at eval
  by_cases hb : bad = true
  · simp [hb] at eval
  by_cases hs : stale = true
  · simp [hb,hs] at eval
  have eq : (fuel-1,insertWord z rest,(z,x,y) :: history) = child := by simpa [hb,hs] using eval
  rw [← eq]
  change (insertWord z rest).length > fuel - 1 + 1
  rw [zbo]
  have h1 := zX a x ws
  have h2 := zX b y (keepWord a x ws)
  have h : ws.length - (if a then 0 else 1) - (if b then 0 else 1) + 1 > fuel - 1 + 1 :=
    of_decide_eq_true wide
  dsimp only [rest]
  omega

theorem zL {ws : List Nat} {x w : Nat} {keep : Bool}
    (nd : ws.Nodup) (h : w ∈ keepWord keep x ws) : w ∈ ws ∧ (keep = true ∨ w ≠ x) := by
  cases keep
  · simpa [keepWord,nd.mem_erase_iff,and_comm] using h
  · simpa [keepWord] using h

theorem zaC {ws : List Nat} (nd : ws.Nodup) (keep : Bool) (x : Nat) :
    (keepWord keep x ws).Nodup := by
  cases keep
  · exact nd.erase x
  · exact nd

theorem zbB {mask goal out : Nat} {ws : List Nat} {directed : Bool}
    {pairs : List Nat} {a b : Nat} {left right : Bool}
    (nd : ws.Nodup)
    (checked : zbr mask goal (zbn ws) (zaQ ws.length)
      (zbk a b left right) out directed pairs = true) :
    zbv mask goal directed
      (out :: keepWord right (ws.getD b 0) (keepWord left (ws.getD a 0) ws)) pairs = true := by
  obtain ⟨code,mem,verdict⟩ := List.any_eq_true.mp checked
  apply List.any_eq_true.mpr
  refine ⟨code,mem,?_⟩
  simp only [zM,Bool.and_eq_true,Nat.blt_eq] at verdict
  obtain ⟨⟨⟨⟨⟨⟨hp,hn⟩,neg⟩,wp⟩,wn⟩,output⟩,closure⟩ := verdict
  refine Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨
    Bool.and_eq_true_iff.mpr ⟨hp,hn⟩,neg⟩,List.all_eq_true.mpr ?_⟩
  intro w hw
  rcases List.mem_cons.mp hw with rfl | later
  · exact output
  have rightMem := zL (zaC nd left (ws.getD a 0)) later
  have leftMem := zL nd rightMem.1
  obtain ⟨i,inside,eq⟩ := List.mem_iff_getElem.mp leftMem.1
  have atIndex : ws.getD i 0 = w := by
    simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem inside] using eq
  have omitted : (zbk a b left right).testBit (64*i) = false := by
    have cleared (j : Nat) (keep : Bool) (h : keep = true ∨ w ≠ ws.getD j 0) :
        (if keep then 0 else 1 <<< (64*j)).testBit (64*i) = false := by
      rcases h with yes | diff
      · simp [yes]
      · have ne : i ≠ j := fun same => diff (same ▸ atIndex).symm
        cases keep <;> simp [Nat.shiftLeft_eq,Nat.testBit_two_pow,show 64*j ≠ 64*i by omega]
    simp [zbk,Nat.testBit_or,cleared a left leftMem.2,cleared b right rightMem.2]
  let p := code &&& 511
  let n := code >>> 9
  let marks := zaQ ws.length
  let signal := zbn ws
  have mark : marks.testBit (64*i) = true := zbb inside
  have test {j : Nat} (within : j < 64) :
      ((signal >>> j) &&& marks).testBit (64*i) = w.testBit j := by
    rw [Nat.testBit_and,Nat.testBit_shiftRight,mark,Bool.and_true,
      Nat.add_comm j,zn inside within,atIndex]
  have h := congrArg (fun word => Nat.testBit word (64*i)) (Nat.beq_eq.mp closure)
  simp only [Nat.zero_testBit] at h
  change (((if directed then (signal >>> p &&& marks) &&& ((signal >>> n &&& marks) ^^^ marks)
      else (signal >>> p &&& marks) ^^^ (signal >>> n &&& marks)) &&&
    (marks ^^^ zbk a b left right)).testBit (64*i)) = false at h
  have pt := test (j := p) wp
  have nt := test (j := n) wn
  cases directed <;> cases px : w.testBit p <;> cases nx : w.testBit n <;>
    simp [px,nx,pt,nt,Nat.testBit_and,Nat.testBit_xor,mark,omitted,p,n] at h ⊢

theorem zbq {mask goal a b op keep out : Nat} {state child : (Nat × List Nat × List (Nat × Nat × Nat))}
    (masked : Masked mask goal) (viable : WordViable mask goal child)
    (parent : state.2.1.Nodup) (eval : zj mask state a b op keep
      (state.2.1.getD a 0) (state.2.1.getD b 0) out = some child) (pairs : List Nat) :
    zbr mask goal (zbn state.2.1) (zaQ state.2.1.length)
      (zbk a b (keep.testBit 0) (op == 2 || keep.testBit 1)) out
      (zR state.2.1.length op keep == (state.1-1)+1) pairs = false := by
  obtain ⟨fuel,ws,history⟩ := state
  let x := ws.getD a 0
  let y := ws.getD b 0
  apply Bool.eq_false_iff.mpr
  intro closed
  have closed := zbB parent closed
  let bad : Bool := fuel == 0 || b ≥ ws.length || (if op == 2 then a != b || keep ≥ 2 else a ≥ b)
  let stale : Bool := out == 0 || out == mask || ws.contains out
  let bank := zaI ws op keep x y
  change (if bad then none else if stale then none else
    some (fuel-1,insertWord out bank,(out,x,y)::history)) = some child at eval
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
  rw [List.toFinset_card_of_nodup nd,zbo] at size
  have same : (out::bank).toFinset = (insertWord out bank).toFinset := by
    ext w
    simp only [List.mem_toFinset,List.mem_cons,insertWordMem]
  have openBank := zbx (pairs := pairs)
    (directed := zR ws.length op keep == (fuel-1)+1) masked (show LiveWord mask goal k t (out::bank).toFinset by rwa [same])
  have available : (zR ws.length op keep == (fuel-1)+1) = true → t = 0 := by
    intro directed
    have exactBudget := beq_iff_eq.mp directed
    have first := zX (keep.testBit 0) x ws
    have second := zX (op == 2 || keep.testBit 1) y (keepWord (keep.testBit 0) x ws)
    change zR ws.length op keep = (fuel-1)+1 at exactBudget
    unfold zR at exactBudget
    dsimp only [bank,zaI] at size
    omega
  have refuses := openBank available
  exact Bool.noConfusion (closed.symm.trans refuses)

theorem zl {mask goal : Nat} {chart : Option ({ rows : List Nat // rows.length = 24 })}
    {cut : ((Nat × List Nat × List (Nat × Nat × Nat)) → Bool)} {ref : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool} {state child : (Nat × List Nat × List (Nat × Nat × Nat))} {sample : (Nat × Nat)} {tags : List (Nat × Nat)} {a b op keep : Nat}
    (checked : zd mask goal chart cut ref state sample tags = true)
    (ha : a < state.2.1.length)
    (legal : (a = b ∧ op = 2 ∧ keep < 2) ∨ (a < b ∧ b < state.2.1.length ∧ op < 2 ∧ keep < 4))
    (eval : childState mask (gateToken a b op keep) state = some child)
    (masked : Masked mask goal) (viable : WordViable mask goal child) (nd : state.2.1.Nodup)
    (openChild : zI mask goal chart cut child = false) :
    ref (gateToken a b op keep) child = true := by
  have narrow : zq state.2.1.length state.1 (gateToken a b op keep) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have tooMany := zah eval h
    obtain ⟨f,w,path⟩ := child
    simp [zI,tooMany] at openChild
  simp only [zd,zaw,zM,zi,
    Bool.and_eq_true,decide_eq_true_eq] at checked
  have width := checked.1.1
  have atA := treeBlock_at checked.2 (i := a) (Nat.zero_le _) (by simpa using ha)
  rcases Bool.and_eq_true_iff.mp atA with ⟨unary,binary⟩
  rcases legal with ⟨rfl,rfl,hk⟩ | ⟨ab,hb,hop,hk⟩
  · have atKeep := treeBlock_at unary (i := keep) (Nat.zero_le _) (by simpa using hk)
    have fields := zbf (mask := mask) (state := state) (a := a) (b := a) (op := 2)
      (keep := keep) (by omega) (by decide) (by omega)
    have direct := fields.trans eval
    have early := zbq masked viable nd direct
    rcases child with ⟨fuel,ws,history⟩
    simpa only [narrow,Bool.false_eq_true,ite_false,fields,eval,zag,early,openChild,Bool.or_false] using atKeep
  · have atB := treeBlock_at binary (i := b) (by omega) (by omega)
    have atOp := treeBlock_at atB (i := op) (Nat.zero_le _) (by simpa using hop)
    have atKeep := treeBlock_at atOp (i := keep) (Nat.zero_le _) (by simpa using hk)
    have fields := zbf (mask := mask) (state := state) (a := a) (b := b) (op := op)
      (keep := keep) (by omega) (by omega) hk
    have direct := fields.trans eval
    have early := zbq masked viable nd direct
    rcases child with ⟨fuel,ws,history⟩
    simpa only [narrow,Bool.false_eq_true,ite_false,fields,eval,zag,early,openChild,Bool.or_false] using atKeep

theorem childStateData {mask token : Nat} {state child : (Nat × List Nat × List (Nat × Nat × Nat))}
    (eval : childState mask token state = some child)
    (masked : ∀ w ∈ state.2.1,Masked mask w) :
    child.1 < state.1 ∧ ∀ w ∈ child.2.1,Masked mask w := by
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
    some (fuel - 1,insertWord z rest,(z,x,y) :: history)) = some child at eval
  by_cases hb : bad = true
  · simp [hb] at eval
  by_cases hs : stale = true
  · simp [hb,hs] at eval
  have eq : (fuel-1,insertWord z rest,(z,x,y) :: history) = child := by simpa [hb,hs] using eval
  subst child
  have pos : 0 < fuel := by
    by_contra! h
    have he : fuel = 0 := by omega
    simp [bad,he] at hb
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

def dM (mask goal : Nat) (width : Nat) (moves : Array (List (List (Nat × Nat) × List (Nat × Nat)))) : Prop :=
  ∀ (i : Nat) (m : (List (List (Nat × Nat) × List (Nat × Nat)))),moves[i]? = some m →
    ∃ select : Fin width → Fin width,DagAuto mask goal select ∧
      ∀ w,Masked mask w → mixMove m w = relabel select w

def zZ (cert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin width → Fin width) × (Fin width → Fin width)))) : Array (List (List (Nat × Nat) × List (Nat × Nat))) := (cert.map Prod.fst).toArray

def zbu {width : Nat} (mask goal : Nat) (entry : ((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin width → Fin width) × (Fin width → Fin width))) : Prop :=
  let (move,select,inverse) := entry
  (∀ i,inverse (select i) = i) ∧ (∀ i,select (inverse i) = i) ∧
    (mask &&& fM width = mask) ∧ (goal &&& mask = goal) ∧
    (∀ i : Fin width,mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = 2 ^ (inverse i).val) ∧
    mixMove move mask = mask ∧ mixMove move goal = goal

def zaU {width : Nat} (mask goal : Nat) (entry : ((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin width → Fin width) × (Fin width → Fin width))) : Bool :=
  let (move,select,inverse) := entry
  decide ((∀ i,inverse (select i) = i) ∧ (∀ i,select (inverse i) = i) ∧
    (mask &&& fM width = mask) ∧ (goal &&& mask = goal) ∧
    (∀ i : Fin width,mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = 2 ^ (inverse i).val) ∧
    mixMove move mask = mask ∧ mixMove move goal = goal)

theorem zbA {width : Nat} {mask goal : Nat} {entry : ((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin width → Fin width) × (Fin width → Fin width))}
    (ok : zaU mask goal entry = true) : zbu mask goal entry := by
  rcases entry with ⟨move,select,inverse⟩
  unfold zbu
  exact of_decide_eq_true ok

theorem zad {width : Nat} {mask goal : Nat} {cert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin width → Fin width) × (Fin width → Fin width)))}
    (ok : cert.all (zaU mask goal) = true) :
    dM mask goal width (zZ cert) := by
  intro i m get
  simp only [zZ,List.getElem?_toArray,List.getElem?_map] at get
  cases e : cert[i]? with
  | none => simp [e] at get
  | some entry =>
    have eq : entry.1 = m := by simpa [e] using get
    rcases entry with ⟨move,select,inverse⟩
    obtain ⟨left,right,bm,gm,basis,mm,mg⟩ :=
      zbA (List.all_eq_true.mp ok _ (List.mem_of_getElem? e))
    subst m
    exact ⟨select,zf left right bm gm basis mm mg⟩

theorem zak {mask goal : Nat} {width count : Nat} {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {moves : Array (List (List (Nat × Nat) × List (Nat × Nat)))} {links : (Nat → Nat → Option (Nat × Nat))} {parent token : Nat} {state : (Nat × List Nat × List (Nat × Nat × Nat))}
    (bounds : Masked (fM width) mask)
    (valid : dM mask goal width moves)
    (masked : ∀ w ∈ state.2.1,Masked mask w)
    (ok : zD count states moves links parent token state = true)
    {k t : Nat} (live : LiveWord mask goal k t state.2.1.toFinset) :
    ∃ i saved,i < count ∧ states i = some saved ∧ saved.1 = state.1 ∧
      LiveWord mask goal k t saved.2.1.toFinset := by
  unfold zD at ok
  split at ok
  · contradiction
  next destination auto h =>
    have hd := Nat.blt_eq.mp (Bool.and_eq_true_iff.mp ok).1
    have finish := (Bool.and_eq_true_iff.mp ok).2
    cases eq : states destination with
    | none => simp [eq] at finish
    | some saved =>
      simp only [eq,Bool.and_eq_true,beq_iff_eq] at finish
      refine ⟨destination,saved,hd,eq,finish.1,?_⟩
      have last := finish.2
      split at last
      · have same : saved.2.1 = state.2.1 := beq_iff_eq.mp last
        rwa [same]
      · split at last
        · contradiction
        next m hm =>
          obtain ⟨select,auto,agree⟩ := valid _ _ hm
          have same : saved.2.1 = zbp m state.2.1 := beq_iff_eq.mp last
          rw [same,zbC (fun w hw => agree w (masked w hw))]
          exact liveMaskedImage auto bounds live (fun w hw => masked _ (List.mem_toFinset.mp hw))

theorem zwJ {mask goal : Nat} {width count : Nat}
    {chart : Option ({ rows : List Nat // rows.length = 24 })}
    {cut : Nat → ((Nat × List Nat × List (Nat × Nat × Nat)) → Bool)} {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))} {moves : Array (List (List (Nat × Nat) × List (Nat × Nat)))} {links : (Nat → Nat → Option (Nat × Nat))} {sample : (Nat × Nat)}
    {tags : Nat → List (Nat × Nat)}
    (maskBounds : Masked (fM width) mask)
    (goalMask : Masked mask goal)
    (chartOK : ∀ c,chart = some c → ChartOK goal c)
    (cutSound : ∀ i s,WordViable mask goal s → cut i s = false)
    (autos : dM mask goal width moves)
    (verified : tB 0 count (zc mask goal chart cut count
      states moves links sample tags) = true):
    ∀ cap i saved,i < count → states i = some saved →
      saved.1 = cap → ∀ k t,k ≤ cap → ¬LiveWord mask goal k t saved.2.1.toFinset := by
  intro cap
  induction cap using Nat.strong_induction_on with
  | ind cap ih =>
    intro i s iBound stateEq sFuel k t kBound live
    rcases s with ⟨remaining,words,history⟩
    let s : (Nat × List Nat × List (Nat × Nat × Nat)) := (remaining,words,history)
    change states i = some s at stateEq
    have checked := treeBlock_at verified (Nat.zero_le i) (by simpa using iBound)
    change zc mask goal chart cut count states moves links sample tags i = true at checked
    simp only [zc,stateEq,zag,Bool.and_eq_true] at checked
    obtain ⟨nd,masked⟩ := zU checked.1
    have ok := checked.2
    have viable : WordViable mask goal s := ⟨nd,k,t,sFuel ▸ kBound,live⟩
    have scanned := ok
    simp only [zd,Bool.and_eq_true,decide_eq_true_eq] at scanned
    have wide := scanned.1.1
    have absent := scanned.1.2
    rcases wordProgress wide viable with hit | ⟨child,possible,cv⟩
    · simpa [hit] using absent
    obtain ⟨a,b,op,keep,ha,legal,eval⟩ := possible
    have r := zl ok ha legal eval goalMask cv nd (zaP goalMask chartOK cv (cutSound i _ cv))
    have ⟨less,cm⟩ := childStateData eval masked
    have below : child.1 < cap := sFuel ▸ less
    obtain ⟨_,k',t',fits,clive⟩ := cv
    obtain ⟨j,dest,bound,restore,fuelEq,tail⟩ :=
      zak maskBounds autos cm r clive
    exact ih child.1 below j dest bound restore fuelEq k' t' fits tail

def cutPick {α : Type} : List α → Nat → List α
  | [],_ => []
  | x :: xs,n => if n = 0 then [] else if n.testBit 0 then x :: cutPick xs (n >>> 1) else cutPick xs (n >>> 1)
theorem cutPickMem {α : Type} (l : List α) (n : Nat) : cutPick l n ⊆ l := by
  induction l generalizing n with
  | nil => simp [cutPick]
  | cons x xs ih =>
    unfold cutPick
    split
    · simp
    · split
      · exact List.cons_subset_cons _ (ih _)
      · exact List.Subset.trans (ih _) (List.subset_cons_self ..)

theorem lowerDag {mask goal : Nat} {width fuel count : Nat}
    {stock : List Nat} {chart : Option ({ rows : List Nat // rows.length = 24 })}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))} {moves : Array (List (List (Nat × Nat) × List (Nat × Nat)))} {links : (Nat → Nat → Option (Nat × Nat))} {sample : (Nat × Nat)}
    {tags : Nat → List (Nat × Nat)}
    {bounds : List (Nat × List Nat × Nat × Nat)} {witnesses : List (Nat × Nat × Nat)}
    (choices : Nat → Nat)
    (maskBounds : Masked (fM width) mask)
    (goalMask : Masked mask goal) (proper : pW mask goal)
    (chartOK : ∀ c,chart = some c → ChartOK goal c)
    (autos : dM mask goal width moves)
    (stockMasked : ∀ w ∈ stock,Masked mask w) (stockNd : stock.Nodup)
    (essential : witnesses.all (essentialB mask goal stock) = true)
    (known : Known bounds) (submasks : ∀ b ∈ bounds,mask &&& b.1 = b.1)
    (rootCheck : ze mask goal chart (zt goal bounds) witnesses
      (zD count states moves links 0)
      stock fuel = true)
    (nodeCheck : tB 0 count (zc mask goal chart (fun i => zt goal (cutPick bounds (choices i)))
      count states moves links sample tags) = true) :
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
  have cutOpen (s : (Nat × List Nat × List (Nat × Nat × Nat))) (h : WordViable mask goal s) : zt goal bounds s = false := by
    rw [zaR]
    exact knownClosesSound known submasks h
  have openRoot := zaP goalMask chartOK v (cutOpen _ v)
  have allowed : za witnesses state.2.1 = true := by
    apply List.all_eq_true.mpr
    intro entry mem
    apply List.contains_iff_mem.mpr
    rw [← List.mem_toFinset,eq']
    exact essentialRequired (List.all_eq_true.mp essential entry mem) sub live
  have checked := treeBlock_at rootCheck (Nat.zero_le token) (by simpa using tokenBound)
  change (!za witnesses state.2.1 || zI mask goal chart (zt goal bounds) state ||
    zD count states moves links 0 token state) = true at checked
  simp only [allowed,openRoot,Bool.not_true,Bool.false_or] at checked
  have slim (i : Nat) (s) (h : WordViable mask goal s) : zt goal (cutPick bounds (choices i)) s = false := by
    rw [zaR]
    exact knownClosesSound (fun b hb => known b (cutPickMem _ _ hb)) (fun b hb => submasks b (cutPickMem _ _ hb)) h
  have finish := zwJ maskBounds goalMask chartOK slim autos nodeCheck
  have fits : k ≤ fuel := by omega
  have still : LiveWord mask goal k t state.2.1.toFinset := by rwa [eq']
  have stateMask : ∀ w ∈ state.2.1,Masked mask w := by
    intro w hw
    exact stockMasked _ ((rootWordSublist stock token).subset hw)
  obtain ⟨i,s,hi,restore,cap,plan⟩ := zak maskBounds autos stateMask checked still
  exact finish fuel i s hi restore cap k t fits plan

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

theorem sM {mask : Nat} {stock : List Nat}
    (h : stock.all (fun w => w &&& mask == w) = true) :
    ∀ w ∈ stock,Masked mask w := by
  intro w hw
  exact beq_iff_eq.mp (List.all_eq_true.mp h w hw)

theorem uC {oldMask : Nat} {old new : List Nat} {rename : Nat → Nat}
    (h : new.all (fun w => availableB oldMask old (rename w)) = true) :
    ∀ w ∈ new,AvailableWord oldMask old (rename w) := by
  intro w hw
  exact availableB_spec.mp (List.all_eq_true.mp h w hw)

def zu (mask : Nat) (move : (List (List (Nat × Nat) × List (Nat × Nat)))) (word : Nat) : Nat :=
  mixMove move (word &&& mask)

def zbd (mask : Nat) (move : (List (List (Nat × Nat) × List (Nat × Nat)))) : Nat → Nat → Bool :=
  Nat.rec (fun _ => true) (fun i next occupied =>
    if mask.testBit i then
      zr (mixMove move (2^i)) (fun col =>
        Nat.beq (col &&& occupied) 0 && zr (occupied ||| col) next)
    else next occupied)

theorem zaD (mask : Nat) (move : (List (List (Nat × Nat) × List (Nat × Nat)))) : BitLinear (zu mask move) := by
  apply bitLinearComp (mixMoveLinear move)
  simpa using bitLinearRight mask 0

theorem zJ (mask : Nat) (move : (List (List (Nat × Nat) × List (Nat × Nat)))) (i : Nat) :
    zu mask move (2 ^ i) = if mask.testBit i then mixMove move (2^i) else 0 := by
  have select : 2 ^ i &&& mask = if mask.testBit i then 2^i else 0 := by
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases same : i = j
    · subst j
      simp only [Nat.testBit_and,Nat.testBit_two_pow,decide_true,Bool.true_and]
      cases mask.testBit i <;> simp
    · cases h : mask.testBit i <;> simp [Nat.testBit_and,Nat.testBit_two_pow,same,h]
  rw [zu,select]
  split
  · rfl
  · apply Nat.eq_of_testBit_eq
    intro j
    apply Bool.eq_iff_iff.mpr
    rw [mixMoveLinear]
    simp

theorem zC {mask : Nat} {move : (List (List (Nat × Nat) × List (Nat × Nat)))} {n : Nat} {occupied : Nat}
    (ok : zbd mask move n occupied = true) :
    (∀ j < n,∀ b,(zu mask move (2^j)).testBit b = true → occupied.testBit b = false) ∧
    (∀ j < n,∀ k < n,∀ b,(zu mask move (2^j)).testBit b = true →
      (zu mask move (2^k)).testBit b = true → j = k) := by
  induction n generalizing occupied with
  | zero => simp
  | succ n ih =>
    let col := mixMove move (2^n)
    change (if mask.testBit n then zr col (fun w =>
      Nat.beq (w &&& occupied) 0 && zr (occupied ||| w) (zbd mask move n))
      else zbd mask move n occupied) = true at ok
    cases active : mask.testBit n
    · simp [active,zM] at ok
      obtain ⟨existing,unique⟩ := ih ok
      have dead : zu mask move (2^n) = 0 := by simp [zJ,active]
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
    · simp only [active,ite_true,zM,Bool.and_eq_true] at ok
      have disjoint := Nat.beq_eq.mp ok.1
      obtain ⟨existing,unique⟩ := ih ok.2
      have colEq : zu mask move (2^n) = col := by simp [zJ,active,col]
      have old {j b : Nat} (hj : j < n) (h : (zu mask move (2^j)).testBit b = true) :
          occupied.testBit b = false ∧ col.testBit b = false := by
        simpa [Nat.testBit_or,Bool.or_eq_false_iff] using existing j hj b h
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

theorem zB {mask : Nat} {move : (List (List (Nat × Nat) × List (Nat × Nat)))} {width : Nat}
    (bounded : Masked (fM width) mask) (checked : zbd mask move width 0 = true) :
    (∀ a b,zu mask move (a &&& b) = zu mask move a &&& zu mask move b) ∧
    (∀ a b,zu mask move (a ||| b) = zu mask move a ||| zu mask move b) ∧
    (∀ a b,zu mask move (a ^^^ b) = zu mask move a ^^^ zu mask move b) := by
  let f := zu mask move
  have lin := zaD mask move
  have uniq {j k i : Nat} (hj : (f (2^j)).testBit i = true) (hk : (f (2^k)).testBit i = true) : j = k := by
    have within {m : Nat} (a : (f (2^m)).testBit i = true) : m < width := by
      by_contra! big
      have eq := congrArg (fun w => Nat.testBit w m) bounded
      have zero : mask.testBit m = false := by
        simpa [Masked,fM,Nat.testBit_and,Nat.testBit_two_pow_sub_one,show ¬m < width by omega] using eq.symm
      simp [f,zJ,zero] at a
    exact (zC checked).2 j (within hj) k (within hk) i hj hk
  refine ⟨?_,?_,?_⟩
  · intro a b
    apply Nat.eq_of_testBit_eq; intro i
    apply Bool.eq_iff_iff.mpr
    rw [Nat.testBit_and,Bool.and_eq_true,lin,lin,lin]
    constructor
    · rintro ⟨j,hj,h⟩
      rw [Nat.testBit_and,Bool.and_eq_true] at hj
      exact ⟨⟨j,hj.1,h⟩,⟨j,hj.2,h⟩⟩
    · rintro ⟨⟨j,hj,q⟩,⟨k,hk,r⟩⟩
      have same := uniq q r
      subst k
      exact ⟨j,by simp [Nat.testBit_and,hj,hk],q⟩
  · intro a b
    apply Nat.eq_of_testBit_eq; intro i
    apply Bool.eq_iff_iff.mpr
    rw [lin (a ||| b) i,Nat.testBit_or,Bool.or_eq_true,lin a i,lin b i]
    simp only [Nat.testBit_or,Bool.or_eq_true]
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

def zO (width mask goal oldMask oldGoal : Nat) (stock old : List Nat) (move : (List (List (Nat × Nat) × List (Nat × Nat)))) : Bool :=
  Nat.beq (mask &&& fM width) mask && zbd mask move width 0 &&
    Nat.beq (zu mask move mask) oldMask && Nat.beq (zu mask move goal) oldGoal &&
    stock.all (fun w => availableB oldMask old (zu mask move w))

theorem zp {width mask goal oldMask oldGoal : Nat} {stock old : List Nat} {min : Nat}
    (move : (List (List (Nat × Nat) × List (Nat × Nat)))) (origin : Lower oldMask old oldGoal min)
    (ok : zO width mask goal oldMask oldGoal stock old move = true) :
    Lower mask stock goal min := by
  simp only [zO,Bool.and_eq_true,Nat.beq_eq] at ok
  obtain ⟨⟨⟨⟨bounded,unique⟩,masks⟩,goals⟩,supply⟩ := ok
  obtain ⟨andG,orG,xorG⟩ := zB bounded unique
  have zero : zu mask move 0 = 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    apply Bool.eq_iff_iff.mpr
    rw [zaD]
    simp
  apply lowerMap (zu mask move) zero masks (fun w => by rw [xorG,masks]) andG orG (uC supply)
  rwa [goals]

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
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases bank[k]? <;> simp

theorem hcsAndBit {rows : Nat} (xs : List (BitVec rows)) (i : Fin rows) :
    (xs.foldr (· &&& ·) (BitVec.allOnes rows)).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).all id := by
  induction xs with
  | nil => simp [i.isLt]
  | cons a t ih => simp only [List.foldr_cons,BitVec.getLsbD_and,List.map_cons,List.all_cons,id_eq,ih]

theorem hcsOrBit {rows : Nat} (xs : List (BitVec rows)) (i : Fin rows) :
    (xs.foldr (· ||| ·) 0).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).any id := by
  induction xs with
  | nil => simp
  | cons a t ih => simp only [List.foldr_cons,BitVec.getLsbD_or,List.map_cons,List.any_cons,id_eq,ih]

theorem hcsGateBit {rows : Nat} (bank : List (BitVec rows)) (i : Fin rows)
    (g : PEqualNP.CircuitLowerBounds.Gate)
    (hop : g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp)) :
    (hcsGateVal bank g).getLsbD i.val =
      g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false) := by
  obtain ⟨op,ins⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · simp only [hcsGateVal,PEqualNP.CircuitLowerBounds.GateOp.eval,hcsAndBit,List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hcsGetDBit bank i.val k
  · simp only [hcsGateVal,PEqualNP.CircuitLowerBounds.GateOp.eval,hcsOrBit,List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hcsGetDBit bank i.val k
  · simp only [hcsGateVal,PEqualNP.CircuitLowerBounds.GateOp.eval,BitVec.getLsbD_not,i.isLt,
      decide_true,Bool.true_and]
    cases ins with
    | nil => simp
    | cons k _ => simp only [List.map_cons,List.headD_cons,hcsGetDBit]

theorem hcsFoldBits {rows : Nat} (bank : List (BitVec rows)) (i : Fin rows)
    (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (hfan : ∀ g ∈ gs,g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
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
      simp only [hcsStep,List.map_append,List.map_cons,List.map_nil,
        hcsGateBit bank i g (hfan g List.mem_cons_self).1]
    rw [ih (hcsStep bank g) (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg')),hstep]

theorem hcsGateWord {rows : Nat} (bank : List (BitVec rows))
    (g : PEqualNP.CircuitLowerBounds.Gate)
    (hop : g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp))
    (hlen : g.inputs.length ≤ 2) :
    GateWord (fM rows) (bank.map BitVec.toNat) (hcsGateVal bank g).toNat := by
  obtain ⟨op,ins⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop
  have zeroAv : AvailableWord (fM rows) (bank.map BitVec.toNat) 0 := Or.inl rfl
  have maskAv : AvailableWord (fM rows) (bank.map BitVec.toNat) (fM rows) :=
    Or.inr (Or.inl rfl)
  rcases hop with rfl | rfl | rfl
  · cases ins with
    | nil => exact gateOfAvailable (by simpa [hcsGateVal,fM] using maskAv)
    | cons a t =>
      cases t with
      | nil => exact gateOfAvailable (by simpa [hcsGateVal] using toNatAvailable bank a)
      | cons b t =>
        cases t with
        | nil =>
          exact Or.inr ⟨_,_,toNatAvailable bank a,toNatAvailable bank b,
            Or.inl (by simp [hcsGateVal,BitVec.toNat_and])⟩
        | cons c t => simp at hlen
  · cases ins with
    | nil => exact gateOfAvailable (by simpa [hcsGateVal] using zeroAv)
    | cons a t =>
      cases t with
      | nil => exact gateOfAvailable (by simpa [hcsGateVal] using toNatAvailable bank a)
      | cons b t =>
        cases t with
        | nil =>
          exact Or.inr ⟨_,_,toNatAvailable bank a,toNatAvailable bank b,
            Or.inr (by simp [hcsGateVal,BitVec.toNat_or])⟩
        | cons c t => simp at hlen
  · cases ins with
    | nil => exact Or.inl ⟨0,zeroAv,by simpa [hcsGateVal] using notNat (0 : BitVec rows)⟩
    | cons a _ => exact Or.inl ⟨_,toNatAvailable bank a,by simpa [hcsGateVal] using notNat (bank.getD a 0)⟩

theorem hcsBuilds {rows : Nat} (bank : List (BitVec rows))
    (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (hfan : ∀ g ∈ gs,g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      g.inputs.length ≤ 2) :
    ∃ vs,vs.length = gs.length ∧ WordBuilds (fM rows) (bank.map BitVec.toNat) vs ∧
      ∀ v ∈ gs.foldl hcsStep bank,v.toNat ∈ vs ++ bank.map BitVec.toNat := by
  induction gs generalizing bank with
  | nil => exact ⟨[],rfl,trivial,fun _ h => List.mem_map_of_mem h⟩
  | cons g gs ih =>
    let v := hcsGateVal bank g
    have hg := hfan g List.mem_cons_self
    obtain ⟨xs,len,build,sub⟩ := ih (hcsStep bank g) (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))
    have eq : (hcsStep bank g).map BitVec.toNat = bank.map BitVec.toNat ++ [v.toNat] := by
      simp [hcsStep,v]
    rw [eq] at build
    refine ⟨v.toNat :: xs,by simp [len],⟨hcsGateWord bank g hg.1 hg.2,buildsWeaken ?_ build⟩,?_⟩
    · intro u hu; exact Or.inr (Or.inr (by simpa [or_comm] using hu))
    · intro u hu; have m := sub u hu; rw [eq] at m
      simpa [List.mem_append,or_assoc,or_left_comm,or_comm] using m

def hcsCheckPow (p : Nat → Bool) : Nat → Nat → Bool
  | 0,s => p s
  | k + 1,s => hcsCheckPow p k s && hcsCheckPow p k (s + 2 ^ k)

theorem hcsCheckPow_spec {p : Nat → Bool} {k s i : Nat}
    (h : hcsCheckPow p k s = true) (lo : s ≤ i) (hi : i < s + 2 ^ k) : p i = true := by
  induction k generalizing s with
  | zero =>
    have e : i = s := by omega
    simpa [hcsCheckPow,e] using h
  | succ k ih =>
    simp only [hcsCheckPow,Bool.and_eq_true] at h
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
    (hev : ∀ x,C.eval (List.ofFn x) = f x) :
    (C.gates.foldl hcsStep raw).getD C.output 0 = goal := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let y : Fin n → Bool := fun k => j.testBit k.val
  have hbank : raw.map (fun v => v.getLsbD j) = List.ofFn y :=
    beq_iff_eq.mp (hcsCheckPow_spec hRaw (Nat.zero_le j) (Nat.zero_add _ ▸ hj))
  have hfg : goal.getLsbD j = f y :=
    beq_iff_eq.mp (hcsCheckPow_spec hGoal (Nat.zero_le j) (Nat.zero_add _ ▸ hj))
  have hbits := hcsFoldBits raw ⟨j,hj⟩ C.gates hfan
  have hevj : (C.wires (List.ofFn y)).getD C.output false = f y := hev y
  change (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
    (List.ofFn y)).getD C.output false = f y at hevj
  rw [← hbank,← hbits] at hevj
  rw [hfg,← hevj,← hcsGetDBit]

theorem hcsLower {n : Nat} (raw : List (BitVec (2 ^ n))) (goal : BitVec (2 ^ n)) (min : Nat)
    (f : (Fin n → Bool) → Bool)
    (hRaw : hcsCheckPow (fun r => (raw.map fun v => v.getLsbD r) == List.ofFn fun j : Fin n => r.testBit j.val) n 0 = true)
    (hGoal : hcsCheckPow (fun r => goal.getLsbD r == f (fun j : Fin n => r.testBit j.val)) n 0 = true)
    (claim : Lower (fM (2 ^ n)) (raw.map BitVec.toNat) goal.toNat min)
    (t : Nat) (h : PEqualNP.MetaComplexity.HasCircuitSize n f t) : min ≤ t := by
  obtain ⟨C,hfan,hsz,hev⟩ := h
  obtain ⟨vs,len,built,sub⟩ := hcsBuilds raw C.gates hfan
  let eb := C.gates.foldl hcsStep raw
  have same : eb.getD C.output 0 = goal := hcsEvalWord raw goal f hRaw hGoal C hfan hev
  have av : AvailableWord (fM (2 ^ n)) (vs ++ raw.map BitVec.toNat) goal.toNat := by
    rw [← same,List.getD_eq_getElem?_getD]
    cases h : eb[C.output]? with
    | none => exact Or.inl rfl
    | some v => exact Or.inr (Or.inr (sub v (List.mem_of_getElem? h)))
  have lb := claim vs built av
  have hs : C.gates.length ≤ t := hsz
  omega

def gZ : Nat := 0xfffefeeafeeaecc8
def bI (j k a b : Nat) : Nat := if j < k then a else b

def cB (ws : List Nat) : Nat := ws.foldr (fun a z => (z <<< 64) ||| a) 0
def materialize (raw : List Nat) (shift mask maxCount entry : Nat) : List Nat :=
  let base := rootWords raw (entry &&& 63)
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => base)
    (fun _ rest c => if Nat.beq c 0 then base else
      insertWord ((c &&& mask) - 1) (rest (c >>> shift))) maxCount (entry >>> 6)
def shortHist (mask fuel : Nat) (atWords : Nat → List Nat) (forest : Nat → Nat × Nat) (i : Nat) : List (Nat × Nat × Nat) :=
  (Nat.rec (motive := fun _ => Nat → List (Nat × Nat × Nat)) (fun _ => [])
    (fun _ prev j => let (p,token) := forest j
                     if Nat.beq p 0 then [] else
                     let ws := atWords (p-1)
                     let x := ws.getD (token / 768) 0
                     let y := ws.getD ((token / 12) % 64) 0
                     let op := token / 4 % 3
                     (zK mask op x y,x,y) :: prev (p-1)) (fuel+1)) i
def zas : Nat := (cB [0x540a15060340a0d,0x4080d0a070181c0a,0x81d02874081c0205,0xc06054280d0a0741,0x20740a1])
def zba : Nat := 0xefbcdf73becf
def zaH : Nat := 0x182824124205
def zv : Nat := 0x30303030
abbrev zT : Nat := gZ &&& zv
abbrev zQ : List Nat := [0x20202020,0x30003000,0x30300000]
def zS : Nat × List Nat × Nat × Nat := (zv,zQ,4,zT)
def zbg : List (Nat × List Nat × Nat × Nat) := []
def zaa : Option ({rows : List Nat // rows.length = 24}) := some ⟨[13,21,28,13,21,28,13,21,28,13,21,28,5,12,20,5,12,20,5,12,20,5,12,20],rfl⟩
def zaY := uW zQ [6668,268805,535045]
def zbz (i : Nat) : Nat := uP 0x9 2 i
def zaM (i : Nat) : Nat := uP 0x7 15 i
def zao (i : Nat) : Nat := uP 0xe 14 i
def zab := pageLinks zbz zaM 1 13 1 2
def zaV (i : Nat) : Nat × Nat :=
  let e := zao i
  (e &&& 1,e >>> 1)
def zal : Nat × Nat := (zas,16)
def zan := zac zv 16 (zA zQ zba zaH 16) 3 zaV
def zat := zam zv zQ 3 zaV
def zaj : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def zbj := zZ zaj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zaK : dM zv zT 64 zbj := zad (by decide +kernel)
def zaW (i : Nat) : Nat :=
  let j := i / 16
  uP 0x0 1 (i % 16)
def zaE := zc zv zT zaa (fun i => zt zT (cutPick zbg (zaW i))) 1 zat zbj zab zal zan
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zaf : ze zv zT zaa (zt zT zbg) zaY (zD 1 zat zbj zab 0) zQ 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zaZ : tB 0 1 zaE = true := by decide +kernel
theorem zaL : tB 0 1 zaE = true := zaZ
theorem zy : Known zbg := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zG : Lower zv zQ zT 4 := by
  apply lowerDag zaW _ _ _ _ zaK _ _ _ zy _ zaf zaL
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold pW; decide +kernel
  · exact cK (by decide +kernel)
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [zbg,List.mem_cons,List.not_mem_nil,or_false]
    intro b h
    exact False.elim h
def st01 : List (Nat × Nat) × List (Nat × Nat) := ([( 0x9999999999999999,0),(0x2222222222222222,1)],[(0x4444444444444444,1)])
def st05 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xaaaaaaaa55555555,0),(0xaaaaaaaa,31)],[(0x5555555500000000,31)])
def st03 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xaa55aa55aa55aa55,0),(0xaa00aa00aa00aa,7)],[(0x5500550055005500,7)])
def st34 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xff0000ffff0000ff,0),(0xff000000ff00,8)],[(0xff000000ff0000,8)])
def pm0 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01,st05,st03,st34]
def zdA : Nat := 0x1010101010101010
abbrev ziF : Nat := gZ &&& zdA
abbrev zkb : List Nat := [0x1000100010001000,0x1010000010100000,0x1010101000000000]
def zgz : Nat × List Nat × Nat × Nat := (zdA,zkb,4,ziF)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zhV : Lower zdA zkb ziF 4 := zp (width := 64) pm0 zG (by decide +kernel)
def st02 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xa5a5a5a5a5a5a5a5,0),(0xa0a0a0a0a0a0a0a,3)],[(0x5050505050505050,3)])
def st23 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xf00ff00ff00ff00f,0),(0xf000f000f000f0,4)],[(0xf000f000f000f00,4)])
def pm1 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01,st05,st02,st23,st34]
def zdu : Nat := 0x1100110011001100
abbrev zgX : Nat := gZ &&& zdu
abbrev zjE : List Nat := [0x1000100010001000,0x1100000011000000,0x1100110000000000]
def zon : Nat × List Nat × Nat × Nat := (zdu,zjE,4,zgX)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zns : Lower zdu zjE zgX 4 := zp (width := 64) pm1 zG (by decide +kernel)
def st24 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xf0f00f0ff0f00f0f,0),(0xf0f00000f0f0,12)],[(0xf0f00000f0f0000,12)])
def pm2 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01,st05,st02,st24]
def zfN : Nat := 0x1111000011110000
abbrev zlb : Nat := gZ &&& zfN
abbrev zlv : List Nat := [0x1010000010100000,0x1100000011000000,0x1111000000000000]
def zgr : Nat × List Nat × Nat × Nat := (zfN,zlv,4,zlb)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ziJ : Lower zfN zlv zlb 4 := zp (width := 64) pm2 zG (by decide +kernel)
def pm3 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01,st05,st02]
def zfc : Nat := 0x1111111100000000
abbrev ziA : Nat := gZ &&& zfc
abbrev zkD : List Nat := [0x1010101000000000,0x1100110000000000,0x1111000000000000]
def zjn : Nat × List Nat × Nat × Nat := (zfc,zkD,4,ziA)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zjO : Lower zfc zkD ziA 4 := zp (width := 64) pm3 zG (by decide +kernel)
def st45 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xffff00000000ffff,0),(0xffff0000,16)],[(0xffff00000000,16)])
def pm4 : List (List (Nat × Nat) × List (Nat × Nat)) := [st45]
def pm5 : List (List (Nat × Nat) × List (Nat × Nat)) := [st34]
def st35 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xff00ff0000ff00ff,0),(0xff00ff00,24)],[(0xff00ff00000000,24)])
def pm6 : List (List (Nat × Nat) × List (Nat × Nat)) := [st34,st35]
def pm7 : List (List (Nat × Nat) × List (Nat × Nat)) := [st23]
def pm8 : List (List (Nat × Nat) × List (Nat × Nat)) := [st23,st45]
def pm9 : List (List (Nat × Nat) × List (Nat × Nat)) := [st23,st24]
def st25 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xf0f0f0f00f0f0f0f,0),(0xf0f0f0f0,28)],[(0xf0f0f0f00000000,28)])
def pm10 : List (List (Nat × Nat) × List (Nat × Nat)) := [st23,st24,st25]
def pm11 : List (List (Nat × Nat) × List (Nat × Nat)) := [st24,st23]
def pm12 : List (List (Nat × Nat) × List (Nat × Nat)) := [st24,st23,st35]
def pm13 : List (List (Nat × Nat) × List (Nat × Nat)) := [st24,st35]
def zto : Nat := (cB [0xb0301c0a070181c,0x2834140b0482c06,0x380c0e06034120d,0xc04070081c180e05,0xb0102c020b0201,0xe04034080d008341,0x183c100e02038040,0x3c120f0303c0a0f0,0x12070001c180f050,0xb0002c18070501c,0x34180b0302c0a,0x38140d03034060d,0xc120e02838060e00,0xf0203c040f0083,0xe01034080b0401c1,0x3c020])
def zvY : Nat := (cB [0x1fdfc3ffff1ff1ff,0x1ff1f7fe1ffff1ff,0xfff1ff1dfff0ffff,0xf7fff87])
def zsG : Nat := (cB [0x16a078888b0490db,0x12d18845c88a9093,0x1241b602444e8992,0xc44477])
def zbR : Nat := 0x1111111111111111
abbrev zcn : Nat := gZ &&& zbR
abbrev zcv : List Nat := [0x1010101010101010,0x1100110011001100,0x1111000011110000,0x1111111100000000]
def zhB : Nat × List Nat × Nat × Nat := (zbR,zcv,7,zcn)
def zcN : List (Nat × List Nat × Nat × Nat) := [zgz,zon,zgr,zjn]
def zld : Option ({rows : List Nat // rows.length = 24}) := some ⟨[28,44,52,56,28,44,52,56,28,44,52,56,12,20,24,36,40,48,12,20,24,36,40,48],rfl⟩
def znd := uW zcv [14360,276500,538636,808972]
def zui (i : Nat) : Nat := uP 0x4c242e4702cc3401 9 i
def zvc (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 1 (cB [0xb0600f020080000f,0x1b42314360272601,0x6276262096327863,0x4620043147292ca6,0x18332083263492c2]) 0xa6245863248626) 20 (i % 16)
def zvq (i : Nat) : Nat := uP (cB [0x7918a200410078,0x31251934]) 16 i
def zmg := pageLinks zui zvc 4 13 3 5
def zlA (i : Nat) : Nat × Nat :=
  let e := zvq i
  (e &&& 7,e >>> 3)
def znn : Nat × Nat := (zto,55)
def zuj := zac zbR 55 (zA zcv zvY zsG 55) 6 zlA
def zhK := zam zbR zcv 6 zlA
def zxx : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm4,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,3,5,4] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,3,5,4] 0 i.val))),(pm5,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,4,3,5] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,4,3,5] 0 i.val))),(pm6,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,5,3,4] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,4,5,3] 0 i.val))),(pm7,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,3,2,4,5] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,3,2,4,5] 0 i.val))),(pm8,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,3,2,5,4] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,3,2,5,4] 0 i.val))),(pm9,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,4,2,3,5] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,3,4,2,5] 0 i.val))),(pm10,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,5,2,3,4] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,3,4,5,2] 0 i.val))),(pm11,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,3,4,2,5] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,4,2,3,5] 0 i.val))),(pm12,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,3,5,2,4] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,4,2,5,3] 0 i.val))),(pm13,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,4,5,2,3] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,4,5,2,3] 0 i.val)))]
def zet := zZ zxx
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zvL : dM zbR zcn 64 zet := zad (by decide +kernel)
def zkx (i : Nat) : Nat :=
  let j := i / 16
  uP 0x101f 4 (i % 16)
def zhS := zc zbR zcn zld (fun i => zt zcn (cutPick zcN (zkx i))) 6 zhK zet zmg znn zuj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zqD : ze zbR zcn zld (zt zcn zcN) znd (zD 6 zhK zet zmg 0) zcv 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zrO : tB 0 6 zhS = true := by decide +kernel
theorem zrs : tB 0 6 zhS = true := zrO
theorem zmR : Known zcN := (eK (eK (eK (eK (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) zjO) ziJ) zns) zhV)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zif : Lower zbR zcv zcn 7 := by
  apply lowerDag zkx _ _ _ _ zvL _ _ _ zmR _ zqD zrs
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold pW; decide +kernel
  · exact cK (by decide +kernel)
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [zcN,List.mem_cons,List.not_mem_nil,or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel
def zdE : Nat := 0x303000003030
abbrev zij : Nat := gZ &&& zdE
abbrev zhH : List Nat := [0x202000002020,0x300000003000,0x303000000000]
def ziw : Nat × List Nat × Nat × Nat := (zdE,zhH,4,zij)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zgp : Lower zdE zhH zij 4 := zp (width := 64) pm4 zG (by decide +kernel)
def pm14 : List (List (Nat × Nat) × List (Nat × Nat)) := [st35,st34]
def zdh : Nat := 0x30003000300030
abbrev zmq : Nat := gZ &&& zdh
abbrev ziR : List Nat := [0x20002000200020,0x30000000300000,0x30003000000000]
def zkZ : Nat × List Nat × Nat × Nat := (zdh,ziR,4,zmq)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zkX : Lower zdh ziR zmq 4 := zp (width := 64) pm14 zG (by decide +kernel)
def pm15 : List (List (Nat × Nat) × List (Nat × Nat)) := [st03]
def pm16 : List (List (Nat × Nat) × List (Nat × Nat)) := [st03,st45]
def st04 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xaaaa5555aaaa5555,0),(0xaaaa0000aaaa,15)],[(0x5555000055550000,15)])
def pm17 : List (List (Nat × Nat) × List (Nat × Nat)) := [st03,st04]
def pm18 : List (List (Nat × Nat) × List (Nat × Nat)) := [st03,st04,st05]
def pm19 : List (List (Nat × Nat) × List (Nat × Nat)) := [st04,st03]
def pm20 : List (List (Nat × Nat) × List (Nat × Nat)) := [st04,st03,st35]
def pm21 : List (List (Nat × Nat) × List (Nat × Nat)) := [st04,st35]
def zrN : Nat := (cB [0x540a15060340a0d,0x40a250a070181c0a,0x834120b0182c1209,0xc02054080d120d02,0xa074181d02874081,0xb40a2d020b008250,0xa35020d0482d060,0x3c060f048350a0d4,0x12034280d120f028,0x700a1c120541815,0x282506094081d12,0xa34020b4282c028b,0xd020f00835060d00,0x20f4283d060f40a3,0xf018350a0b4481d1,0x83d028])
def zuR : Nat := (cB [0x99dfd273c777b0cf,0xfb0f37f1ce7c3de9,0xff81f81dff07cfe0,0xf7ffc07])
def zqu : Nat := (cB [0x8920448401108045,0x810a084410841080,0x8801500240501480,0xc00154])
def zbL : Nat := 0x3030303030303030
abbrev zcb : Nat := gZ &&& zbL
abbrev zbP : List Nat := [0x2020202020202020,0x3000300030003000,0x3030000030300000,0x3030303000000000]
def zcD : Nat × List Nat × Nat × Nat := (zbL,zbP,7,zcb)
def zda : List (Nat × List Nat × Nat × Nat) := [zS,ziw,zkZ,zgz]
def zix : Option ({rows : List Nat // rows.length = 24}) := some ⟨[13,21,28,37,44,52,13,21,28,37,44,52,5,12,20,36,5,12,20,36,5,12,20,36],rfl⟩
def zse := uW zbP [6668,268805,535045,805381]
def zpS (i : Nat) : Nat := uP 0x4c242e4702cc3401 9 i
def zpv (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 1 (cB [0xf06013020080000f,0x1f423143602b2601,0x62b626209632b863,0x4620043147292ca6,0x180360802a3492c2]) 0xa01c583364832a) 20 (i % 16)
def zov (i : Nat) : Nat := uP (cB [0x9918a200410078,0xe50154]) 16 i
def zia := pageLinks zpS zpv 4 13 3 5
def zkI (i : Nat) : Nat × Nat :=
  let e := zov i
  (e &&& 7,e >>> 3)
def zxq : Nat × Nat := (zrN,55)
def zpz := zac zbL 55 (zA zbP zuR zqu 55) 6 zkI
def zjb := zam zbL zbP 6 zkI
def zuo : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm4,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,3,5,4] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,3,5,4] 0 i.val))),(pm5,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,4,3,5] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,4,3,5] 0 i.val))),(pm6,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,5,3,4] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,4,5,3] 0 i.val))),(pm15,(fun i : Fin 64 => Fin.ofNat 64 (pA [3,1,2,0,4,5] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [3,1,2,0,4,5] 0 i.val))),(pm16,(fun i : Fin 64 => Fin.ofNat 64 (pA [3,1,2,0,5,4] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [3,1,2,0,5,4] 0 i.val))),(pm17,(fun i : Fin 64 => Fin.ofNat 64 (pA [4,1,2,0,3,5] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [3,1,2,4,0,5] 0 i.val))),(pm18,(fun i : Fin 64 => Fin.ofNat 64 (pA [5,1,2,0,3,4] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [3,1,2,4,5,0] 0 i.val))),(pm19,(fun i : Fin 64 => Fin.ofNat 64 (pA [3,1,2,4,0,5] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [4,1,2,0,3,5] 0 i.val))),(pm20,(fun i : Fin 64 => Fin.ofNat 64 (pA [3,1,2,5,0,4] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [4,1,2,0,5,3] 0 i.val))),(pm21,(fun i : Fin 64 => Fin.ofNat 64 (pA [4,1,2,5,0,3] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [4,1,2,5,0,3] 0 i.val)))]
def zeO := zZ zuo
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zny : dM zbL zcb 64 zeO := zad (by decide +kernel)
def zjq (i : Nat) : Nat :=
  let j := i / 16
  uP 0x401f 4 (i % 16)
def zkm := zc zbL zcb zix (fun i => zt zcb (cutPick zda (zjq i))) 6 zjb zeO zia zxq zpz
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zxU : ze zbL zcb zix (zt zcb zda) zse (zD 6 zjb zeO zia 0) zbP 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zrw : tB 0 6 zkm = true := by decide +kernel
theorem ztX : tB 0 6 zkm = true := zrw
theorem ztk : Known zda := (eK (eK (eK (eK (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) zhV) zkX) zgp) zG)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zbK : Lower zbL zbP zcb 7 := by
  apply lowerDag zjq _ _ _ _ zny _ _ _ ztk _ zxU ztX
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold pW; decide +kernel
  · exact cK (by decide +kernel)
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [zda,List.mem_cons,List.not_mem_nil,or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel
def zep : Nat := 0x3300330033003300
abbrev zjI : Nat := gZ &&& zep
abbrev ziz : List Nat := [0x2200220022002200,0x3000300030003000,0x3300000033000000,0x3300330000000000]
def zdw : Nat × List Nat × Nat × Nat := (zep,ziz,7,zjI)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zfb : Lower zep ziz zjI 7 := zp (width := 64) pm7 zbK (by decide +kernel)
def zwP : Nat := (cB [0xe00a25028540a0d,0x4100d180e050380c,0x250c0740a1d0805,0x5028d4502d028b44,0xe02038040e0603,0x54500d0c034000d1,0x101d180543015000,0x2514094002508074,0x80d4402d040b460,0xf40a3d000e04035,0x4200d180f4503d0c,0x1d1005410151003,0x504094601d140740,0x80b4302d000b4202,0xf450350c0d400351,0x600d100f4203d040,0x2d0c094401d14054,0xf40a38040d420])
def znS : Nat := (cB [0xbffffffdfffc7fc7,0xd5e39cfe631f9b79,0xe6fc1f3f83e3e3ba,0xf8ffe03ffc03fc3c])
def ztz : Nat := (cB [0x4000000400002907,0x2a39291829589258,0x194b506892c942a8,0x7921ab158925430])
def zca : Nat := 0x2121212121212121
abbrev zch : Nat := gZ &&& zca
abbrev zcs : List Nat := [0x2020202020202020,0x2100210021002100,0x2121000021210000,0x2121212100000000]
def zlT : Nat × List Nat × Nat × Nat := (zca,zcs,6,zch)
def zcF : List (Nat × List Nat × Nat × Nat) := []
def ziN : Option ({rows : List Nat // rows.length = 24}) := some ⟨[13,21,37,56,13,21,37,56,13,21,37,56,5,24,40,48,5,24,40,48,5,24,40,48],rfl⟩
def zrv := uW zcs [6664,268805,535045,805381]
def zur (i : Nat) : Nat := uP 0xa28301 6 i
def zrq (i : Nat) : Nat := uP (cB [0x31010c504010000f,0x1492c6]) 17 i
def zmL (i : Nat) : Nat := uP 0x3144010803c 15 i
def zlp := pageLinks zur zrq 3 13 2 4
def zhX (i : Nat) : Nat × Nat :=
  let e := zmL i
  (e &&& 3,e >>> 2)
def zrt : Nat × Nat := (zwP,64)
def zsE := zac zca 64 (zA zcs znS ztz 64) 5 zhX
def zlC := zam zca zcs 5 zhX
def zvX : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm5,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,4,3,5] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,4,3,5] 0 i.val))),(pm6,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,5,3,4] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,4,5,3] 0 i.val)))]
def zfy := zZ zvX
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zsT : dM zca zch 64 zfy := zad (by decide +kernel)
def zhx (i : Nat) : Nat :=
  let j := i / 16
  uP 0x0 1 (i % 16)
def zhW := zc zca zch ziN (fun i => zt zch (cutPick zcF (zhx i))) 3 zlC zfy zlp zrt zsE
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zqm : ze zca zch ziN (zt zch zcF) zrv (zD 3 zlC zfy zlp 0) zcs 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem znO : tB 0 3 zhW = true := by decide +kernel
theorem zqN : tB 0 3 zhW = true := znO
theorem zpE : Known zcF := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zbU : Lower zca zcs zch 6 := by
  apply lowerDag zhx _ _ _ _ zsT _ _ _ zpE _ zqm zqN
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold pW; decide +kernel
  · exact cK (by decide +kernel)
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [zcF,List.mem_cons,List.not_mem_nil,or_false]
    intro b h
    exact False.elim h
def zdT : Nat := 0x2211221122112211
abbrev zlP : Nat := gZ &&& zdT
abbrev zjP : List Nat := [0x2200220022002200,0x2010201020102010,0x2211000022110000,0x2211221100000000]
def zvS : Nat × List Nat × Nat × Nat := (zdT,zjP,6,zlP)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zup : Lower zdT zjP zlP 6 := zp (width := 64) pm7 zbU (by decide +kernel)
def pm22 : List (List (Nat × Nat) × List (Nat × Nat)) := [st03,st24,st05,st02]
def zfq : Nat := 0x3333000000003333
abbrev zgP : Nat := gZ &&& zfq
abbrev zgl : List Nat := [0x2222000000002222,0x3030000000003030,0x3300000000003300,0x3333000000000000]
def zhn : Nat × List Nat × Nat × Nat := (zfq,zgl,6,zgP)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zjk : Lower zfq zgl zgP 6 := zp (width := 64) pm22 zbU (by decide +kernel)
def zeB : Nat := 0x33333333
abbrev zks : Nat := gZ &&& zeB
abbrev zeu : List Nat := [0x22222222,0x30303030,0x33003300,0x33330000]
def zcW : Nat × List Nat × Nat × Nat := (zeB,zeu,5,zks)
def zsi := uW zeu [6668,268809,530949,795137]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zcd : Lower zeB zeu zks 5 := by
  apply eL (witnesses := zsi) (cut := zv)
  · unfold pW; decide +kernel
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold pW; decide +kernel
  · exact uC (old := zQ) (by decide +kernel)
  · exact zG
  · decide +kernel
def zfK : Nat := 0x333300003333
abbrev zgo : Nat := gZ &&& zfK
abbrev zkd : List Nat := [0x222200002222,0x303000003030,0x330000003300,0x333300000000]
def zfg : Nat × List Nat × Nat × Nat := (zfK,zkd,5,zgo)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zft : Lower zfK zkd zgo 5 := zp (width := 64) pm4 zcd (by decide +kernel)
def pm23 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01,st23,st24]
def zcK : Nat := 0x55550000
abbrev zie : Nat := gZ &&& zcK
abbrev zds : List Nat := [0x44440000,0x50500000,0x55000000]
def zwc : Nat × List Nat × Nat × Nat := (zcK,zds,4,zie)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zkn : Lower zcK zds zie 4 := zp (width := 64) pm23 zG (by decide +kernel)
def zeW : Nat := 0x55555555
abbrev zgq : Nat := gZ &&& zeW
abbrev zfH : List Nat := [0x44444444,0x50505050,0x55005500,0x55550000]
def zdR : Nat × List Nat × Nat × Nat := (zeW,zfH,5,zgq)
def zxv := uW zfH [3076,265218,529410,800780]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zcA : Lower zeW zfH zgq 5 := by
  apply eL (witnesses := zxv) (cut := zcK)
  · unfold pW; decide +kernel
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold pW; decide +kernel
  · exact uC (old := zds) (by decide +kernel)
  · exact zkn
  · decide +kernel
def pm24 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01,st24,st35]
def zeT : Nat := 0x33003300330033
abbrev zjZ : Nat := gZ &&& zeT
abbrev zjz : List Nat := [0x22002200220022,0x30003000300030,0x33000000330000,0x33003300000000]
def zdJ : Nat × List Nat × Nat × Nat := (zeT,zjz,5,zjZ)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zdV : Lower zeT zjz zjZ 5 := zp (width := 64) pm24 zcA (by decide +kernel)
def pm25 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01,st25,st34,st23]
def zey : Nat := 0x303030303030303
abbrev zmo : Nat := gZ &&& zey
abbrev zjo : List Nat := [0x202020202020202,0x300030003000300,0x303000003030000,0x303030300000000]
def zdD : Nat × List Nat × Nat × Nat := (zey,zjo,5,zmo)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zdG : Lower zey zjo zmo 5 := zp (width := 64) pm25 zcA (by decide +kernel)
def zfA : Nat := 0xf0f0f0f0
abbrev zlj : Nat := gZ &&& zfA
abbrev zef : List Nat := [0xa0a0a0a0,0xc0c0c0c0,0xf000f000,0xf0f00000]
def zcI : Nat × List Nat × Nat × Nat := (zfA,zef,5,zlj)
def zsZ := uW zef [6668,265220,530949,797189]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zbG : Lower zfA zef zlj 5 := by
  apply eL (witnesses := zsZ) (cut := zv)
  · unfold pW; decide +kernel
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold pW; decide +kernel
  · exact uC (old := zQ) (by decide +kernel)
  · exact zG
  · decide +kernel
def zeb : Nat := 0x3333000033330000
abbrev zkj : Nat := gZ &&& zeb
abbrev zlH : List Nat := [0x2222000022220000,0x3030000030300000,0x3300000033000000,0x3333000000000000]
def ztS : Nat × List Nat × Nat × Nat := (zeb,zlH,5,zkj)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zow : Lower zeb zlH zkj 5 := zp (width := 64) pm2 zbG (by decide +kernel)
def zdx : Nat := 0x3333333300000000
abbrev ziY : Nat := gZ &&& zdx
abbrev zid : List Nat := [0x2222222200000000,0x3030303000000000,0x3300330000000000,0x3333000000000000]
def znH : Nat × List Nat × Nat × Nat := (zdx,zid,5,ziY)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zuk : Lower zdx zid ziY 5 := zp (width := 64) pm3 zbG (by decide +kernel)
def zfp : Nat := 0x33003300
abbrev zin : Nat := gZ &&& zfp
abbrev zlz : List Nat := [0x22002200,0x30003000,0x33000000]
def zkC : Nat × List Nat × Nat × Nat := (zfp,zlz,4,zin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zml : Lower zfp zlz zin 4 := zp (width := 64) pm7 zG (by decide +kernel)
def zew : Nat := 0x330000003300
abbrev zhQ : Nat := gZ &&& zew
abbrev zlW : List Nat := [0x220000002200,0x300000003000,0x330000000000]
def zrY : Nat × List Nat × Nat × Nat := (zew,zlW,4,zhQ)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ztb : Lower zew zlW zhQ 4 := zp (width := 64) pm8 zG (by decide +kernel)
def pm26 : List (List (Nat × Nat) × List (Nat × Nat)) := [st25,st23,st34]
def zeR : Nat := 0x300030003000300
abbrev zkg : Nat := gZ &&& zeR
abbrev zgL : List Nat := [0x200020002000200,0x300000003000000,0x300030000000000]
def zwB : Nat × List Nat × Nat × Nat := (zeR,zgL,4,zkg)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zsl : Lower zeR zgL zkg 4 := zp (width := 64) pm26 zG (by decide +kernel)
def znV : Nat := (cB [0x844180d048340a0d,0x4281502854201100,0x81c0607030190486,0x51008402210c0702,0x40a41229120940a2,0xc4502c120b0182c1,0x6034120d02834180,0xd180e050380c0e0,0x44100d0203402,0x442811048440a11,0x408150085460110c,0x190406402190805,0xd08070101c020702,0xa074181d048740a1,0x840a2100084301d0,0x6021140844821048,0x2910094082500894,0x20b04029040a402,0x8b40a2d100b0102c,0x4502d120b4182d04,0x834100c42031008c,0x5028d44034080d00,0x40e06035120d4283,0xe41239100e020380,0x183c180e450390c0,0x3c120f0303c0a0f0,0xa034000d180f050])
def zwC : Nat := (cB [0x7fffc7fff023f1ff,0x71dcce67c0f1e3fc,0xff01fc7f8e07f8e0,0xf007ff007e1f0f87,0x8fe00ff8fffe007f,0x3fffff800007ffff,0xfff800000ffff000,0x3fffffff])
def zoJ : Nat := (cB [0x1230c123100150ab,0x20ccc6650010208c,0x8b00e43484534845,0x20a5920a46170b86,0xb600d5015720059,0xa6a549000106249c,0x49c000100dbaa000,0x38c99262])
def zbJ : Nat := 0x3333333333333333
abbrev zce : Nat := gZ &&& zbJ
abbrev zbO : List Nat := [0x2222222222222222,0x3030303030303030,0x3300330033003300,0x3333000033330000,0x3333333300000000]
def zgx : Nat × List Nat × Nat × Nat := (zbJ,zbO,10,zce)
def zdc : List (Nat × List Nat × Nat × Nat) := [zhB,zcD,zdw,zlT,zvS,zhn,zcW,zfg,zdJ,zdD,ztS,znH,zS,zkC,ziw,zrY,zkZ,zwB,zgr,zjn]
def zlI : Option ({rows : List Nat // rows.length = 24}) := some ⟨[13,17,28,33,44,52,56,13,17,28,33,44,5,9,12,20,24,36,40,48,5,9,12,20],rfl⟩
def zxy := uW zbO [6668,268809,530949,795137,1065473]
def zpK (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 7 (bI j 3 (bI j 1 (cB [0x2079208b40180001,0x600a44148029004e,0x5810b0015842b005,0xd801b002d48]) (bI j 2 (cB [0xf401b1c36006c0,0xa00f501e803d007a,0x9a011cc238045108,0x15802a844d40]) (cB [0x617a82f005928ac3,0x1e003c007800e4,0xf401e043c007800f,0x1e843d007a00]))) (bI j 5 (bI j 4 (cB [0x11f403e047c00f80,0x8021003f187e00fa,0x1032200421084010,0x234445888b01]) (cB [0xc2640499893011e4,0x2c005708a54932,0x6442c425880b0096,0x2d805b00b601])) (bI j 6 (cB [0x2f845f00be016c8,0x2131486280c02980,0x9c933806510ca019,0x3b8a6c58d709]) (cB [0x33d407988f301e60,0xe03f447c14f801ea,0xfe13fc07f80ff01f,0x410081850019])))) (bI j 10 (bI j 8 (cB [0x142808485061a082,0x40444288050b2a14,0x2c845428a81121a2,0x47868f011e02]) (bI j 9 (cB [0x448c091052202421,0xf14b82939d270246,0x92151c4a381403a5,0x5280a5014a02]) (cB [0x53c2a60d4c02942,0x405480a8095002a0,0xb6055c8ab055222a,0x5880ad9d5b02]))) (bI j 12 (bI j 11 (cB [0x5c82b901710ac4f,0x5d46ba817312e6,0x1015e9cbd017812f,0x6296c4858903]) (cB [0x16a02cacd95032a0,0xa06a86d501aa0352,0x6406c80d695ad035,0x714eda45b213])) (bI j 13 (cB [0x7442e805d003984,0x17594ea09d213a4,0xc967900f201e11bc,0x7f84ff01fa23]) 0x4003)))) 15 (i % 16)
def ztp (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 16 (bI j 8 (bI j 4 (bI j 2 (bI j 1 (cB [0x100ac0100400001f,0x18d88631448806e1,0x2061c666438c9c5d,0x9c398ce87313c866,0xbd49996292d27d25,0x67d87065a4dc]) (cB [0x60c6c0218a362c39,0x31022233304464e0,0x2cc44c6708989e02,0xe0e24cc1a49682c9,0x1a61ca2cc3808126,0x14c4e019881])) (bI j 3 (cB [0x424b40649620a633,0x61c0169370252660,0x380112588430e506,0x3b0e004496208c,0xd18a01493002988,0x43867c070cc8]) (cB [0x7a4c90f31f01e632,0x7a2020c38c3d27d0,0x3e03864c090c5110,0x102a4b00f3130263,0x1701b82af4405187,0x40c4e031880]))) (bI j 6 (bI j 5 (cB [0xaa4ce0649622a633,0x496032c390618718,0x31020c4103b0e007,0xd0a24c6084960286,0x918a232f4406d87,0x824c40098c94]) (cB [0xdb0e01d496426625,0x620236f4407d8800,0x2c828c40050c501e,0x108cf40b18a03c9,0x1f49844263d82cc4,0xa8636118c50])) (bI j 7 (cB [0x88ccc2e19885a327,0x313c466200cc67e1,0x3f8c4c671718c62d,0x41c24fc354964666,0x3d61f076c380e528,0xfd8841f30fc]) (cB [0x21880427a2882f44,0x61c04c9420952581,0x100a5e8814310827,0x817b0e02c6270560,0x34008064f4a0c1e8,0xbcc62129880])))) (bI j 12 (bI j 10 (bI j 9 (cB [0xb30fa2f498c4a92c,0x18d84c3140dde881,0x200e92611318802c,0x81e3d122749604e6,0x3219e8749400d925,0xa06291918f4]) (cB [0x18f22831008033c,0x49606063d0a4c412,0x440dd8711824f629,0xe118cac0218a078f,0x4b31388862048c66,0x13d258a598cc])) (bI j 11 (cB [0xda4dc564998a892d,0x3102a8c3953d8702,0x2c490c6e1218ac03,0xe2424cc4749688a9,0x4761ca8ac3812926,0x1198700224b1]) (cB [0x28c5049498092c40,0x7a209a64213063a0,0x2014406628009c4e,0x622a4b12931b80c6,0x5361c8a4c3853926,0x11987003a4b0]))) (bI j 14 (bI j 13 (cB [0x3a4b02531a810620,0x18a2a6f441558842,0x40120c402b8ca409,0x2050c50584a00b2c,0x5a61c09262016065,0x98652058c50]) (cB [0x51880281a0a4c335,0x61c0b29301552582,0x81698782e3d1155,0xe30804c5e0088180,0x6318a2540430a806,0x1b066c328cc8])) (bI j 15 (cB [0x60d096519f0e0337,0x31f0e86325c0686b,0x38dd127d3a24c974,0x63f30fc7d61c8f6c,0x7d7a2af6f4421588,0x4ac0841580d9]) (cB [0x3d106061c0be620,0x18a2c434e188684b,0x8591e883230e00d,0x3480446600801c0,0x6718a0d6f441a868,0x1a06383430e0]))))) (bI j 24 (bI j 20 (bI j 18 (bI j 17 (cB [0x7bd126d3120da324,0x4980dc6301b98703,0x4e1c469c3100466e,0x390d00724a00e6c,0x6d19a0ea01d03c01,0x1e9e883c24f8]) (cB [0xb0074770140ec93e,0x3200f2628dd80523,0x2018063a080c506e,0xcb799096b31f0c86,0x7c7a26f4c3e5e927,0x2046683f80d4])) (bI j 19 (cB [0x1250080626106f4c,0x31f10433420006a4,0x410b006b4224f884,0x4b98d047319aa580,0x8361e50c94a218c9,0x440104230f0]) (cB [0x680dc8e009910011,0x19311e3144cc0861,0x43254684488cf865,0xf25a4b07431312e3,0x9c621934c3826127,0x279e8a4ebd10]))) (bI j 22 (bI j 21 (cB [0x4988075193268042,0x61c11493f9312584,0x3022c05046bd108c,0x8090c507700c0ec3,0x92008026008241e8,0x24c6284a0044]) (cB [0x500449649649a620,0x318132328e280524,0x1d0506283c8c6078,0x84dbd10963211183,0x9031011a31d05462,0x1e92643598c8])) (bI j 23 (cB [0x249b7a249cc38,0x1394801b2880265,0x142a006e5300cea4,0xe2798814119b82c3,0x4f49633a6331ecc4,0x2a9871cea4ce]) (cB [0x1bd10a17a215cc39,0x49614af449418705,0x1429de8928b0e051,0xed08024a961c02e3,0xa300f95a0132ac01,0xe94066d2809d])))) (bI j 28 (bI j 26 (bI j 25 (cB [0x28c9ca318f942315,0x496030620a946665,0x1c9498703e24cc52,0xc578078ac0061583,0xa719ed600322c004,0x64c40548d04]) (cB [0xda4f45349626e641,0x9736c3d94d870c,0x3eacc04c598068b2,0xa0d0c50b50211680,0x543102843430d466,0x268c623e989c])) (bI j 27 (cB [0xd24c65449633c63f,0x62116cc3ee7927f4,0x442f1e8ad73d10b9,0xa0d8c51b07a235ef,0x55310170f442dc66,0x9552585d18f4]) (cB [0xc3d20bb61c57493d,0x148380082ede985,0x430e006e6100acbe,0xa3f0c6c5618a2700,0x91312cac62024464,0x2d98706224b2]))) (bI j 30 (bI j 29 (cB [0x4b108c962098cc40,0x18a36cf44329886e,0x2c95cc403f8c6c57,0x860b0e0bf4a016e9,0x8018d8b03146dde8,0x3012592c1880]) (cB [0xe8c50c3626180c40,0x61c03c3143158800,0x2b2fc0520f8020ac,0x6418c6c5918a1860,0xc7319cb262031c66,0x32187062a4b2])) (bI j 31 (cB [0xd24b05a310108626,0x148400082b18712,0x140fc0829c80d439,0x64e0c9c8518d8b63,0xce19f99833d67066,0xa70c4f2d9880]) (bI j 32 (cB [0x718fecc31ef38633,0x49898c9302e52596,0x38329266e4a4c8c9,0x2108020cf7a2372c,0xba7a2174c3833402,0x31d878431899]) (cB [0x430f25c4960b8620,0x6]))))))) 23 (i % 16)
def zrB (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 6 (bI j 3 (bI j 1 (cB [0x8c50080100201f00,0xcc4e0692c0431001,0x692d0361c03a4b00,0x249b81b100292660,0x68cc8346281a31b0,0x3190]) (bI j 2 (cB [0xc504864e04c380d,0x9e8824c381219f09,0xec381701b8ba4b00,0x261f0da4b4098722,0xeb100792583a9330,0x6200]) (cB [0x80ac0467a4293702,0x1258486202418a11,0x8c422461c1225089,0xb008158c6c8de884,0x78cc48c64e46c4e2,0x61c1]))) (bI j 4 (cB [0xbd28c866646f442f,0x9258460103419f91,0x693f237a21b30f8d,0xc61c11a4c0e92844,0x1b0fc8d87c46f443,0x6211]) (bI j 5 (cB [0xbd148de884633c40,0x92588a6204418a00,0x293345496a2b0e11,0xc313a224dd158809,0x23d1130c849831d4,0x4962]) (cB [0x30e140066a002750,0x1884aa92d4461ca8,0xe94058194aba4cd1,0xc49ba230e169880a,0xf80457863602f445,0x3102])))) (bI j 9 (bI j 7 (cB [0xd0988026bcc385f,0x8664bcc386418a2f,0xcc386718a3380419,0xe7a2330d0198022c,0x6b0e1b8648da3365,0x7a23]) (bI j 8 (cB [0xa501c869ce23375e,0x803aea6325e62738,0x293e750143ba4f9d,0xc61c2f3d11d4c50f,0xfb0fd79872bcf447,0x1ab]) (cB [0xa50208668fec4c80,0x9886bc63e847a63f,0x20118819380992a1,0x901445a4fe24c411,0x4004e21e8912c388,0x18a4]))) (bI j 11 (bI j 10 (cB [0x80424867d10f4490,0x8685100119218a49,0x293f881a1c424b25,0x87a24db0e2206513,0xbd1621e8910c438,0x4960]) (cB [0x804e81e8942009a0,0x1e894a01ba07a251,0x2037a07a25380ce8,0xc007d5b0e2818715,0x7b0e6800275631ca,0xf5])) (bI j 12 (cB [0x4ac925a02026af,0x80856403eb200d59,0x4f44b719adbb0fac,0x261c5d18f6e98856,0xf80a6f926602f45b,0x4a05]) (cB [0x80aef98717e92cc0,0x98818a92cbe62661,0xcc38c7199e3b102f,0xc49b80b10ef98837,0x60cff300239a33dc,0x7a26]))))) 21 (i % 16)
def zki := pageLinks zpK ztp 5 13 8 6
def zju (i : Nat) : Nat × Nat :=
  let e := zrB i
  (e &&& 255,e >>> 8)
def znv : Nat × Nat := (znV,96)
def ztM := zac zbJ 96 (zA zbO zwC zoJ 96) 9 zju
def zkU := zam zbJ zbO 9 zju
def zxY : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm4,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,3,5,4] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,3,5,4] 0 i.val))),(pm7,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,3,2,4,5] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,3,2,4,5] 0 i.val))),(pm8,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,3,2,5,4] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,3,2,5,4] 0 i.val)))]
def zfF := zZ zxY
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zxD : dM zbJ zce 64 zfF := zad (by decide +kernel)
def zgj (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 6 (bI j 3 (bI j 1 (cB [0x1000070000700007,0x100000000000000,0x0,0x7000000000000,0x400048000100002c]) (bI j 2 (cB [0x5000008000700002,0x700000000000000,0x100000400,0x700000c000700,0x400010000000000c]) (cB [0x70040700000c0007,0x100000000001100,0x1000200000010,0x2000180070300,0x20b47000000]))) (bI j 4 (cB [0x200000,0x80487000480064,0x4430040100000000,0xc3f0344180,0xf0700401034470]) (bI j 5 (cB [0x7808608084720e01,0x1000070000,0x0,0x50070000000,0x400700000000000]) (cB [0x10000000000,0x700000150070000,0x10000000000050,0x150070000001,0xcc7001070])))) (bI j 9 (bI j 7 (cB [0xf000020000300000,0x86008c700002003c,0x0,0x447000408088600,0x600000406064]) (bI j 8 (cB [0x2000020000200306,0x40004086850000,0x0,0x2004870000400,0x3420c5860]) (cB [0x2000020000600000,0xf06000000000,0x94700087000,0x0,0x83ef00001000000]))) (bI j 11 (bI j 10 (cB [0x22c2022c700000,0x80987000000000,0x4000080000,0x82000000808700,0x700860008470]) (cB [0x4c08700000004a7,0x2700000444070000,0xc0a700000404,0x700,0x487000000])) (bI j 12 (cB [0x74c3e70048700000,0xa78cbe743467649a,0x4a700400000000c0,0xcc0000400000040,0x40007c0307000c70]) (cB [0x10000000000,0x4703060033e70000,0x4874002000000004,0x30700c07000004c,0x40f2700002000012]))))) 20 (i % 16)
def zbm := zc zbJ zce zlI (fun i => zt zce (cutPick zdc (zgj i))) 208 zkU zfF zki znv ztM
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zqp : ze zbJ zce zlI (zt zce zdc) zxy (zD 208 zkU zfF zki 0) zbO 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zpi : tB 0 24 zbm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zpV : tB 24 24 zbm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem znI : tB 48 24 zbm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem znr : tB 72 24 zbm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem znh : tB 96 24 zbm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zxS : tB 120 24 zbm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zqZ : tB 144 24 zbm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zoY : tB 168 24 zbm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zuG : tB 192 16 zbm = true := by decide +kernel
theorem zrr : tB 0 48 zbm = true := tM (start := 0) (left := 24) (right := 24) (check := zbm) zpi zpV
theorem zoC : tB 48 48 zbm = true := tM (start := 48) (left := 24) (right := 24) (check := zbm) znI znr
theorem zoL : tB 0 96 zbm = true := tM (start := 0) (left := 48) (right := 48) (check := zbm) zrr zoC
theorem znT : tB 96 48 zbm = true := tM (start := 96) (left := 24) (right := 24) (check := zbm) znh zxS
theorem zop : tB 168 40 zbm = true := tM (start := 168) (left := 24) (right := 16) (check := zbm) zoY zuG
theorem znz : tB 144 64 zbm = true := tM (start := 144) (left := 24) (right := 40) (check := zbm) zqZ zop
theorem zvu : tB 96 112 zbm = true := tM (start := 96) (left := 48) (right := 64) (check := zbm) znT znz
theorem zwf : tB 0 208 zbm = true := tM (start := 0) (left := 96) (right := 112) (check := zbm) zoL zvu
theorem zxE : tB 0 208 zbm = true := zwf
theorem zom : Known zdc := (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) zjO) ziJ) zsl) zkX) ztb) zgp) zml) zG) zuk) zow) zdG) zdV) zft) zcd) zjk) zup) zbU) zfb) zbK) zif)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zcp : Lower zbJ zbO zce 10 := by
  apply lowerDag zgj _ _ _ _ zxD _ _ _ zom _ zqp zxE
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold pW; decide +kernel
  · exact cK (by decide +kernel)
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [zdc,List.mem_cons,List.not_mem_nil,or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def zdb : Nat := 0x5555555555555555
abbrev zlD : Nat := gZ &&& zdb
abbrev zga : List Nat := [0x4444444444444444,0x5050505050505050,0x5500550055005500,0x5555000055550000,0x5555555500000000]
def zhi : Nat × List Nat × Nat × Nat := (zdb,zga,10,zlD)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zdF : Lower zdb zga zlD 10 := zp (width := 64) pm24 zcp (by decide +kernel)
def zfI : Nat := 0x5555000055550000
abbrev zjF : Nat := gZ &&& zfI
abbrev zjr : List Nat := [0x4444000044440000,0x5050000050500000,0x5500000055000000,0x5555000000000000]
def zfh : Nat × List Nat × Nat × Nat := (zfI,zjr,7,zjF)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zex : Lower zfI zjr zjF 7 := zp (width := 64) pm23 zbK (by decide +kernel)
def pm27 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01,st23,st24,st25]
def zee : Nat := 0x5555555500000000
abbrev zhO : Nat := gZ &&& zee
abbrev zhu : List Nat := [0x4444444400000000,0x5050505000000000,0x5500550000000000,0x5555000000000000]
def zgI : Nat × List Nat × Nat × Nat := (zee,zhu,7,zhO)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zlX : Lower zee zhu zhO 7 := zp (width := 64) pm27 zbK (by decide +kernel)
def pm28 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01,st03,st02]
def zfC : Nat := 0x5005500550055005
abbrev zkY : Nat := gZ &&& zfC
abbrev zgs : List Nat := [0x4004400440044004,0x5000500050005000,0x5005000050050000,0x5005500500000000]
def zej : Nat × List Nat × Nat × Nat := (zfC,zgs,6,zkY)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zeH : Lower zfC zgs zkY 6 := zp (width := 64) pm28 zbU (by decide +kernel)
def zev : Nat := 0x555500005555
abbrev zhg : Nat := gZ &&& zev
abbrev zjh : List Nat := [0x444400004444,0x505000005050,0x550000005500,0x555500000000]
def zhc : Nat × List Nat × Nat × Nat := (zev,zjh,5,zhg)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zlV : Lower zev zjh zhg 5 := zp (width := 64) pm4 zcA (by decide +kernel)
def zfV : Nat := 0x55005500550055
abbrev zjA : Nat := gZ &&& zfV
abbrev zhe : List Nat := [0x44004400440044,0x50005000500050,0x55000000550000,0x55005500000000]
def zhq : Nat × List Nat × Nat × Nat := (zfV,zhe,5,zjA)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zgv : Lower zfV zhe zjA 5 := zp (width := 64) pm24 zcd (by decide +kernel)
def zeA : Nat := 0x505050505050505
abbrev zkq : Nat := gZ &&& zeA
abbrev zgD : List Nat := [0x404040404040404,0x500050005000500,0x505000005050000,0x505050500000000]
def ziX : Nat × List Nat × Nat × Nat := (zeA,zgD,5,zkq)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zjp : Lower zeA zgD zkq 5 := zp (width := 64) pm25 zcd (by decide +kernel)
def pm29 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01,st24,st35,st23]
def pm30 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01,st25,st34]
def zwN : Nat := (cB [0x28040a020180406,0x8180d048340a0d04,0xa150804402110603,0x90a05824160a0540,0xc068241a0c064121,0x84301c0a070181c0,0x4825028944021008,0x29048a4482611098,0x60b0502a110a850,0xc86031140b0482c,0x2834180c8443209,0x380c0e06034120d,0x6028180006180e05,0x1018280609018180,0x28120a0002848061,0x440a0c028240a060,0xd02034020d14028,0x4038080e0103810,0x441211028440011,0x460110c044281109,0x4160805408150085,0x9008642016020580,0x4068041a08064101,0x70101c02070201a0,0x181d048740a1d080,0x1e06078301d0a074,0x84301e0a07824])
def zoq : Nat := (cB [0x1c00000419e0cf70,0x6603308f87c0e3ff,0x78071c00e3fff038,0xfc07f1c3879c3cf3,0xf81fc0fc7ff81f80,0x7fffe000fff80e03,0xffc001fff00,0xffe000007fffffff,0x8000000000000fff])
def ztU : Nat := (cB [0x410200008a04530,0x2201100500c02086,0x1001040821428018,0x482560c1858c2cd2,0xd816c0e82b480912,0x4d92402492b04602,0xc18b6c001bba00,0x7740000076249278,0x4003060db7])
def zbY : Nat := 0x7777777777777777
abbrev zcg : Nat := gZ &&& zbY
abbrev zcB : List Nat := [0x2222222222222222,0x4444444444444444,0x7070707070707070,0x7700770077007700,0x7777000077770000,0x7777777700000000]
def zoB : Nat × List Nat × Nat × Nat := (zbY,zcB,12,zcg)
def zcY : List (Nat × List Nat × Nat × Nat) := [zgx,zhi,zcD,zdw,zfh,zgI,zhn,zej,zcW,zdR,zfg,zhc,zdJ,zhq,zdD,ziX]
def zib : Option ({rows : List Nat // rows.length = 24}) := some ⟨[6,10,13,17,28,33,44,50,52,56,6,10,5,9,12,18,20,24,34,36,40,48,5,9],rfl⟩
def zsN := uW zcB [6668,265220,527362,791554,1057281,1327617]
def zpX (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 12 (bI j 6 (bI j 3 (bI j 1 (cB [0x409100abc01a0001,0xc001800300058,0x6620c82190030106,0xdc01a883500]) (bI j 2 (cB [0x1104020803f106e8,0xc011802110420082,0x90011c2230446008,0x130026004820]) (cB [0x168827ac4e08982,0xc019802f205e00bc,0xd401a8033106600c,0x1c0238006a30]))) (bI j 4 (cB [0x41cd639047108e20,0xe0208a41008200fc,0x1402280450087190,0x228845008a01]) (bI j 5 (cB [0x240648008e111c0,0xae25404988930126,0x4e029c05380a3212,0x2ac05390a701]) (cB [0x2d4655a8ab01560,0x452e805d00b81170,0x7e22fc05f80bf017,0x31806094c101])))) (bI j 9 (bI j 7 (cB [0x332006308c6018c0,0x33c26780cb2190,0xa6134446880d009a,0x35c06a88d409]) (bI j 8 (cB [0x2374a6e04d729ae0,0x403a047210e401c4,0xd6b3a827500ea01d,0x3e967d00f621]) (cB [0x424a848109020a4,0xf440087090e021c,0x48048c291811f222,0x4a809485242a]))) (bI j 10 (cB [0x24b4296812c0a542,0x434c429881300a5c,0x7a14ec49b9135126,0x50c4a1813e2a]) (bI j 11 (cB [0x55190a301450a8a0,0x8e555eaa8153129c,0xf405e80bb8d722ac,0x5f40be817a1a]) (cB [0x6048c0817f12fa2,0x2161c4c38185130a,0x18e62c2c5058a031,0x67c6cd159a03]))))) (bI j 18 (bI j 15 (bI j 13 (cB [0x69c0d289a503443,0x46a00d401a70b4e,0x5c86b80d609ac035,0x7106dc31b613]) (bI j 14 (cB [0x7280e501c71b8e0,0x807300e509ca0394,0xa287440e805cc239,0x7a06edb5d913]) (cB [0x7c02f611ec03d61,0x607c82f901f10be2,0xee57dc0fb05f31be,0x80810085fc2b]))) (bI j 16 (cB [0x18a011212176c055,0x818c8514a6290450,0x7018d851a8635046,0x8f8f1f02392c]) (bI j 17 (cB [0x691c1230646048a1,0x8098852d224d6c8e,0xd2199493282640cc,0x9ac135826a0c]) (cB [0x9d433a827314d68,0x609ec13d067624ec,0xfe09f453e827b14f,0xa105410a7f1c])))) (bI j 21 (bI j 19 (cB [0xa543498a8e2d0c8,0x1a7854c96961d2c,0x4e1a907508ea1054,0xaa8b540aa805]) (bI j 20 (cB [0x4aed35a9ab3155e4,0x61b2c16582c81d88,0xa83b4856696cc0d9,0xbac971a2d765]) (cB [0xbc437806f005de1,0x44be057996f20de4,0x6cc0838086fe1df,0xc6058b0b0f3e]))) (bI j 23 (bI j 22 (cB [0x9c88191032016346,0x43cc8198872b3644,0x94ccda99b03350e6,0xd681ad035626]) (cB [0xd74dae835a1eb40,0xc1da89b19f6306c6,0xe80dcc3b7936f06d,0xdd89bb037416])) (bI j 24 (cB [0xe1c1c20f7c46f42,0xe5e355c49387170e,0x402e709ce039c072,0xea8dd123a207]) (cB [0xec83d887b107601,0x766])))))) 15 (i % 16)
set_option maxRecDepth 16000 in
def zxj (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 30 (bI j 15 (bI j 7 (bI j 3 (bI j 1 (cB [0x1884004c4000003f,0x62a662b0ef313853,0xa31f8be98dc568c6,0xb50052586fa64335,0xfa93755a499a5324,0x1c3bea50dd6927ea,0x8016]) (bI j 2 (cB [0xb10e3bd87f14cc39,0x754cf45a017a24a9,0xf02180780dc00805,0xcc0c925a04292c20,0x8e93f07549b823a4,0x1c83db0e09d52864,0x7e6]) (cB [0xbd1028d88610ec3f,0x4006c3e27e7a293d,0xa7a28043d1080d89,0x40035e9e016f4b00,0x8c3820a92890449,0x280033d100158940,0x79]))) (bI j 5 (bI j 4 (cB [0x3d200264a040ef4a,0x801925800561e003,0x4960063d200398a,0x2c05527a02692d01,0x38f4a01a4a780ca5,0xa5010494407e4a00,0x117]) (cB [0x24b0051890025250,0x28c380174a500b,0xb7aa00ba5200624a,0x1005d27a02292c01,0x24c3801e92800ebd,0x980f49500618920,0x220])) (bI j 6 (cB [0xcdd840086820037,0x204ac382101a1808,0x162181630fc0a587,0xf88a5e8a44af4403,0x48f4422332501198,0xf813004c8924a00,0x4260]) (cB [0xd0c09063f012043,0xa04ef44212321b09,0xa00f01500480a1e8,0xd48a24a0056f4a42,0x5cc3842d19a81680,0x280183d300ade880,0x22b9])))) (bI j 11 (bI j 9 (bI j 8 (cB [0x30f00bd87005ef4c,0xe026343033009018,0x662501b30f884c69,0x2c101e8a07cf4423,0x7d2500457a78213d,0xa501a0cf89024a24,0x2341]) (cB [0x8cd48d64a006af44,0x8070c4a02a61c01b,0x919a01ec9400f1e8,0x440ed26807463403,0x7af4a03518f01f80,0xa402080420a24a04,0x3c7])) (bI j 10 (cB [0x49600e1878086040,0x2088f4804662a022,0x902782600ac12005,0x2814125a09a92c21,0xd694f0644a5828a5,0xa2036312c0d98700,0x707]) (cB [0xc9441ca4a00e2f4b,0x8092c4a037496039,0xe025025c940129e8,0x400fde88054c3804,0xa802a052014027c9,0x1402d8ca815c6500,0x5d3]))) (bI j 13 (bI j 12 (cB [0x30e01892580c262a,0x4c72500637a201c,0x37a2029b0e00e4c4,0xa81586380aa01c25,0xb292c03a31002c0c,0xe12d3d101698700,0x550]) (cB [0x98801786540b831c,0x80c0c3805f49601d,0xc18e02b0070981e8,0xd0168c680a633405,0xcc32806501403024,0x2603531601a0c500,0x673])) (bI j 14 (cB [0x98a019c6500d264c,0xda93006a4a4034,0xa19a83798a01b865,0x1018d89407ec3804,0xda93ce3d92801e3d,0x1c0258cd792c06a0,0x4f6]) (cB [0xd38f64a007af44,0x443404f26362a03a,0xa92883cc9401d9e9,0x501e24a00eef4407,0x3e03707c00983c49,0xa18040cde0200878,0x21f1]))))) (bI j 22 (bI j 18 (bI j 16 (cB [0x30fc0f987204ac38,0xb04af44279621939,0xd32503e98fa0f9e8,0x4a89a4a084cf4487,0x4034f00a19b83f80,0x1e82030e40a58704,0x706]) (bI j 17 (cB [0x3d289e989e4e6c4b,0x410b251a3e928041,0xa61c0408d2820066,0xe020c68347f25042,0x6af4406361e815b0,0x2a04300402124a10,0x849]) (cB [0xdc22006a01602b,0x208492d02c496045,0xa49b84624cc14526,0xe09c52960e293f09,0x4f440a061c84e30,0x961414940289e981,0x42d4]))) (bI j 20 (bI j 19 (cB [0xc94020d87011293d,0x11a02808b7ac141,0x762004998a023c65,0xd0239e9813325809,0x229400927a604818,0xa604a18d0244c681,0x967]) (cB [0xca0254c6812a940,0x130c4c094314048,0xe01404a98a024465,0x258c5012432808,0x36f5809749804c31,0x1c04e80c82612601,0x2e6])) (bI j 21 (cB [0xc940279e9906af44,0x5ec3809f01ed1a,0xb01b80600ac2864b,0xcc11125a06092c08,0x3cc3809b49b84ca4,0x9600680ac2858721,0x314]) (cB [0x30f029129208a92d,0x408cc380a5496051,0xb4a505da4f829d26,0xfc32d872864c382b,0x9ac4b0d8621866b0,0xa2c3f3d10b6189e5,0xdb7])))) (bI j 26 (bI j 24 (bI j 23 (cB [0x49403b1e9e1baf4b,0xc06692c2db928d3f,0x84a5058a50c2a127,0xfc2c987056294f2a,0x4f442b3625859b0,0xa785b3d2c2d1e8b1,0xba7]) (cB [0x8ca0ad24a3505250,0x815ec380ac314054,0xa496531c9402c1e8,0xb2981e88156c380a,0xb4f440ae61c056a4,0x1a056a4d02a8c694,0xab3])) (bI j 25 (cB [0xb1282bd87c15c934,0x95092508847a2157,0x74a005831202d406,0x2e18981732580b,0xfe92c0b97a405c25,0xa505e24dc2a12640,0xbd4]) (cB [0xb0e50d987018094f,0xe188c4b0c361f860,0x87a5863bd1031989,0xa03264a34e12500c,0x70c380bf31405f0c,0x9655849422c1e888,0x43a4]))) (bI j 28 (bI j 27 (cB [0xa4b2ab9e8915cc38,0x9556f448ab61c21d,0x549a057b0f030806,0x122c1894160c3e0c,0x94034a3c92821e3d,0x1e0660042ac18a81,0xb26]) (cB [0xbd28b058ac182c4a,0x910b2506c17ab260,0x69284433d12a16ab,0xc033c06c19c034a8,0x6693e0d049905424,0x1c162255830d2941,0xd46])) (bI j 29 (cB [0xc941305e881aac56,0x898492ce73aae664,0x119473a4943329e8,0xd034d2b01a46280d,0xb29480d731a06b0c,0xae06d4958b192ac1,0xe7aa]) (cB [0x30f8370021cf1250,0x8592c560c762405a,0x492b664bd25101e8,0x4110587148155c8b,0xbe0420de020520c9,0x9f05ea4f02d92641,0xe14])))))) (bI j 45 (bI j 37 (bI j 33 (bI j 31 (cB [0x30e0b212ac19094a,0x1d2f440d561ea21,0x4aae075c9622d24a,0x422d587088692cab,0xc43280e07ac55ac9,0x2c07324d0390c501,0xe89]) (bI j 32 (cB [0xbd30395e981c6f4c,0x81ca6280e3194073,0x21075496039d26,0xe03a127c1729320e,0x749320ea7a222230,0x2aa22b0e03b52a81,0xee6]) (cB [0x18811198701d6f48,0xe20863e0fe310878,0x4325099190c47cc7,0xb0cc8c9e63e64b30,0x8e93f13c49a053a4,0x1fa53b0e0d1d2962,0x5476]))) (bI j 35 (bI j 34 (cB [0xbd1621de88e8ec4b,0x29ef4f14b7a5c6e,0x101f56ec946a1e4a,0x2cbc40941e603f0f,0xea93403349617981,0xa2c4e3d110cd8701,0x8e97]) (cB [0x49403f1e9e1f4f4b,0x6892cae9928d4e,0xd9280793d390d187,0xcc3d804a1e8c40a9,0x3cc382f401f87a00,0x2187bb0fe3a98731,0xf96])) (bI j 36 (cB [0xb0e2ba9e8b53cf44,0x81f0f4ca9f7a244f,0xb92c07ba4d03e187,0x203c80781f09340f,0xf29340fd02a17901,0x2b07f81283ede901,0x2ff0]) (cB [0xb100c052b420294e,0x154155c8a0928081,0x1f08124d040188,0x3840928460004a10,0x432508a17a218125,0x8e08500784140395,0x10f1])))) (bI j 41 (bI j 39 (bI j 38 (cB [0x1928460c4022831e,0x823c64f11c32688d,0xd7a225430e02a125,0x7ab564a34a32508b,0x106200a918a08300,0x1c254a4b0424c862,0x8bf6]) (cB [0x9882b5de8b4baf44,0x14bef44a5e7a2083,0xe1a70860d3042c02,0x12971e894c325010,0x5831411000f086bd,0x96089990c448c401,0x4ac4])) (bI j 40 (cB [0x3d1695de8917cc38,0x94b0f4411131056b,0x51a60858042965e8,0x1296e4a022e34e11,0xc525011902408b3d,0xe48d8c7046c0394,0x10c0]) (cB [0x8ca04764a022a31c,0x821c01c116314086,0x518e090007045c63,0x684b929825465812,0xc325013162009825,0xa70908d02a32ab91,0x1231]))) (bI j 43 (bI j 42 (cB [0xc942391e88248634,0x1528f44122194549,0x561c0910cd2a5587,0x3849868152cf448e,0xc4f4412931a0940d,0xa20938ca2a3e4a11,0xa907]) (cB [0xb0e049c669522c38,0x8256640a927a2471,0xc3144733d104b526,0x7239d87025863412,0x5664c12618e09080,0xe54bc9404bd2682,0x1220])) (bI j 44 (cB [0x3d104b0c8024e31c,0x825031c12300e54c,0xd3260948c7049003,0x423a1e8825e94012,0x5c63c10131054cc9,0x960999968cc0cac2,0xb14]) (cB [0xc9592c5870272934,0x8268628a9aaae09d,0x87aa19bbd204dd8a,0x20cd587826a94813,0x6c62813531409b31,0x2709798c0408c402,0x1343]))))) (bI j 52 (bI j 48 (bI j 46 (cB [0x1902a6e4a0274f4a,0x27064c33532609b,0x531009d24d0cdccb,0xdc4c4c662066210f,0x7264333131f89c98,0x1fc75b0e62898706,0x13d6]) (bI j 47 (cB [0xbd16a89e8828cc43,0xa27c6340f7310575,0xb61c0a218d8508c6,0x40515e99172f448f,0x7e9408b849655cc9,0x9655c3d105058702,0x1404]) (cB [0xb13050d898280c40,0xa27e6340f83104a1,0x861c4a198d850cc6,0x905158781f26208f,0x912504b37a20a418,0x8e0a480729c6ab91,0x14a1]))) (bI j 50 (bI j 49 (cB [0x3d129bde894db250,0x23463c0fa310537,0xe3210a71904530c8,0xe04f526816c92c94,0x6d2508fa7a225b30,0x1055b55724f64b11,0xb73]) (cB [0xb0e12dd25827c628,0x29af4493e62645b,0x17a60a0a4d2ade4a,0x82511eb028493494,0x7492c15032a07e18,0xa425d30e05192681,0x93d7])) (bI j 51 (cB [0x18905486382a201c,0x86a8c4a15461f09e,0xf7a5c763d1628de8,0x46a8e4a02aef4f94,0xa0c4a15561c57649,0x28476bd1055989f2,0xaa49]) (cB [0x1892a964a15dd251,0x128cf4815862a0a3,0x23108ad988056587,0xdc594c6620863216,0xca64b9043250b818,0x9985da4b25c0c9f2,0x1474])))) (bI j 56 (bI j 54 (bI j 53 (cB [0xb0e511d8702ea94b,0xe2ecc4b97561fa66,0x77a5c5dbd105e989,0xcab364a348f25094,0xb804a15e0198ae00,0x1c03fa4b25780972,0x44d6]) (cB [0x313c57d8969a8c39,0x349b25087f7a20b0,0xd62704024b2b524a,0xc293a4a1102f4415,0xc205495d0240ae80,0xa14b1815858c07c2,0x1644])) (bI j 55 (cB [0x5571141e892c895a,0x2d231c16600e528,0xf4ad0b725005b0cb,0xd2992ab89a0f4416,0xa2c381681a70b38c,0x9a534bd129a24a09,0x16a1]) (cB [0x49413498702d634e,0x2da634a677a2533,0xa18e0b3807134d87,0x729aa4a02da64c16,0xc862016b18e0b400,0x2d4b799585b8c602,0x1713]))) (bI j 58 (bI j 57 (cB [0x49405d1eac17892c,0x2e4954a6baae460,0x33200b9b1525c989,0x12520c492e465817,0x8755c8c39282363d,0x1a08d18c057cc415,0x1773]) (cB [0x24b1de4c6c2f2635,0xd88f4475f61c062,0x531076255723124a,0x105e1870d8a92c0c,0xc0620ec5928462bd,0xa206324b05ecca82,0x8c67])) (bI j 59 (cB [0xa4b25f06382f801c,0x62fc93d4d8496a3a,0xe7a50c0a53dde929,0xb2b624a34eb25097,0x94f77b4a50bfa4,0x28d3b49413658703,0xada9]) (cB [0xbd10609ea94ef250,0xc1]))))))) 25 (i % 16)
def ztE (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 12 (bI j 6 (bI j 3 (bI j 1 (cB [0x560231000407e00,0x250118700461f00c,0x8803928011e88046,0x580de8a03928025e,0x80e7a780e4b00c7a,0x1b8098a]) (bI j 2 (cB [0x4a0117a504525810,0x9e84189014496842,0xa0164a5059258164,0xa06d29e104a58424,0x1d7a2075e94107a,0x9280424a]) (cB [0x262249600a4a210,0x1c089e882331f08c,0x8a267a2098026266,0x50a80242a61c889e,0x2d01a8b587e227a,0x7a60bd87]))) (bI j 4 (cB [0x25a02621889e982d,0xa20d067c340090cd,0x943719a8dd87c337,0xa0e4c683919a0e58,0x8339280dde883749,0x88fde8]) (bI j 5 (cB [0xe9633008105e8a33,0xa78ce4b04302010d,0x52484998098a8467,0x8125e88496251240,0x44e4961200564892,0x92813809]) (cB [0x50524a512125a48,0xe1540545261c14c,0x5458194148638550,0x5149870584961606,0x45e3141486385c19,0x49617865])))) (bI j 9 (bI j 7 (cB [0x258523151498705e,0x14195296487a2149,0x506532619c650650,0x79218b0653261a4c,0x6e4981b5896484a,0x3141b865]) (bI j 8 (cB [0x4a0487a5921e8848,0x9b80806874928922,0xa0777a21dde94764,0xc00a4a2769281da4,0x20231f1f40267c61,0x91fd87]) (cB [0xe947f1a520066480,0x289fe4a0831a0a0d,0x6a8861f808020869,0xc22c06e8849ea240,0x88e014235266887a,0x194235e9]))) (bI j 10 (cB [0xe98904a0244c6890,0xa0254c6894314235,0x9898620235e98944,0xc26d26e8892c2358,0x89d019275870887a,0x1ea7de9]) (bI j 11 (cB [0xe988892c28587288,0x96295292a4621809,0x7ca849929cc42014,0xc2a9258aa1942a52,0xad4962b4c50a961,0x61c2a587]) (cB [0x870a84a1aa1e88a9,0x1a2d5e8aa861faa1,0x98b84a02dde96a80,0xf29de9ea892c2dd8,0xbe4a52f126ebc49,0x3142f865]))))) (bI j 18 (bI j 15 (bI j 13 (cB [0x68c261caf129ebc,0x9a315896bc61faf0,0x96bc7a22f189ebc4,0xca9c068ca928af1e,0x8ce61fa9c020cc61,0x1b33806]) (bI j 14 (cB [0xc50d1194345264ce,0x2b339870ce4ac344,0x86a731a358668d66,0x2a9e4acd94a43658,0xde7a5a9c020dc7a,0x2137808]) (cB [0x650e249f379eb0e0,0xa6394c50e27a638c,0xb0e27a639d268e27,0xc37a4b0ea7a237a4,0xaed4aa3b5e9ea792,0x3138058a]))) (bI j 16 (cB [0xe9cf201f3c4c40f0,0x9a3c5880f401fbc5,0x98f861fbd804af64,0xc3ede96f1621bd9e,0x2f002a3f5e9ef192,0x253fcc4]) (bI j 17 (cB [0x269024a73fd88100,0xe414c7cf06203fd,0x410631041c03d060,0x842c03d05321c18c,0xd0b7a24346990b00,0x18e41469]) (cB [0xc411031044403d10,0xa645463d05321c40,0x41051a7455e89161,0xe46cc9505024464c,0xf05928474c9b0500,0x31fbc0c9])))) (bI j 21 (bI j 19 (cB [0x651221a048403920,0x8e480c69211a7484,0x9d2619449c681261,0x4accb12031a4986,0x92049a4acc512c32,0x49a4bd29]) (bI j 20 (cB [0xc86f06204812b520,0xa44d4c513432d4cc,0xa93462a4d1891354,0xb4cde953a49a4cde,0x93e61fcf5268f092,0x4a04fcc6]) (cB [0xc6b3e61c4fd25940,0xa64f8c6d3e62650c,0x494849fbc18873d7,0x5bc06394900e524c,0x34c7a2534c814c7a,0x7a7bc0c8]))) (bI j 23 (bI j 22 (cB [0x6395100e544ca950,0x1c55587d54315804,0xa9587a7d5189f556,0x56cc660161c5658,0x75c6275740655c31,0x625d7006]) (cB [0xc435b02a58589f5c,0x19d6d2856301f58c,0x9d6719a59c039663,0x75a86696a18e5986,0x16631a5b4cb1661a,0x4ad59928])) (bI j 24 (cB [0x2a97232d5c4c6f5b,0xa5d6dead7162a5c9,0x717831a5dd8975b4,0xa5ed89f5b31addd8,0xb7e31b8040397c32,0x4965fd27]) (cB [0xea9824a7df929f7f,0x7a260d])))))) 22 (i % 16)
def zkM := pageLinks zpX zxj 5 13 9 6
def zil (i : Nat) : Nat × Nat :=
  let e := ztE i
  (e &&& 511,e >>> 9)
def ztF : Nat × Nat := (zwN,96)
def zpj := zac zbY 96 (zA zcB zoq ztU 96) 11 zil
def ztN (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 4 (bI j 2 (bI j 1 (cB [0x8000000007777777,0xc00000003bbbbbbb,0xe000001ddddddddd,0x700000e0e00ee0ee,0xb800007770777077,0x38383bbbbbb,0xee0001dc01dc01dc,0xeeee0000ee,0xbb80007777777700,0xddc0003bbbbbbbbb,0xeee001c001c001dd,0x777000e00ee0e0ee,0x9998007777700077,0x5554019999999999,0xeeee015555555555,0xe0eeee00e0]) (cB [0x8077007700770077,0xc03b803b803bbbbb,0xe01dc1ddc01dc1dd,0xeee0ee00eee0e,0xb807777770000000,0xdc03bbbbb803bbbb,0x2201dddddddddddd,0x3302222222022222,0xaa83333333033333,0xc002aaaaaa82aaaa,0xe0e1c01dc001c01d,0xe0e0e0e0e0e0,0xb800707777700000,0xdddc383bbbb83803,0xee01c1ddddc1c1d,0xee00ee00ee0])) (bI j 3 (cB [0x777000007770000,0xc3bb83bb83bb8000,0x1ddc1ddc1ddc1dd,0x70eeeeeee0000000,0x1077777770777777,0x1111111111111111,0x111111111111111,0xe0000000000000,0x70000000700000,0x38003800380000,0xeefc001c001c001c,0xe000eeeee000e,0x7070000000000,0x3838000038000,0xeeefc1c00001c1c0,0xe0e00000eeee]) (cB [0x7070700070707000,0x3838383800000000,0x1c1c1c1c1c1c0000,0x7e0e0e0e0e0e0e0e,0x1707700777077007,0x8b91111111111111,0x45c8888889c88888,0x22e444e444e44444,0x1172722222222222,0x1139391111391111,0x889d1111111d1111,0x444e888e888e8888,0x3337474444444444,0x3b3333333b333,0x1dc0000000000,0xee000000ee00]))) (bI j 6 (bI j 5 (cB [0x7700000077777777,0x3b80038000000000,0x1dc001c001c001c0,0xee000e00ee000e0,0x770070007700700,0x3b803b800000000,0x1dc01dc01c00000,0xee00ee00ee0000,0x77007700770077,0x3b838000000000,0x1dc1c0001dc1c0,0x707ee0e0e0e00000,0x383f707070707070,0x3b838383bb838,0xee0fdc1ddc1ddc1c,0xee0eee0eee0e]) (cB [0x7722222222222222,0xbba2222222222222,0x1dd9999999999999,0xeee00000eee0000,0x777077000000000,0x3bb83b803838000,0x1ddc1dc01dc01dc,0xeee0ee00eee0ee,0xb877707770777000,0x3bb83bb83bb83b,0x1dddc000000000,0xeeee0000e0000,0x3bf777000077770,0x3bbb803b803b8,0xe0fdddc1c1c0000,0xeeee0e0e0e0e])) (bI j 7 (cB [0xf777070777000700,0x3bbb8383bbbb8383,0x1ddddc0000000000,0xeeeee000e000e00,0x777770007777700,0xc3bbbb8383b80380,0x1ddddc1c1ddddc1,0xeeeeee00000000,0x8077777700770077,0x3bbbbb803bbbbb,0x1dddddddc00000,0xeeeeeeeee0000,0x7777777770007,0x888bbbbbbbbb8380,0x8889ddddddddc888,0xeeeeeeeee888]) (cB [0x7777777777000000,0x3bbbbbbbbb803800,0x1dddddddddc01dc0,0xeeeeeeeeeee0000,0x777777777777000])))) 63 (i % 16)
def zkG (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 12 (bI j 6 (bI j 3 (bI j 1 (cB [0x1cee80000003fb,0xcee0000a073b9000,0xc0003843b7000259,0xb3822b7000251ced,0x22b8012ce026dc04,0x8a0704022dc05038,0x6e81cee00503823b,0x1cee3adba070b701,0xe40009e73b701d68,0x311ce]) (bI j 2 (cB [0xce11cdc062384738,0x1ee311c220937017,0x443847370188e1,0x3853b7000221cee,0x9b7000211cedc00,0x8018a31cee004438,0x309cedc073c473b,0x6edc000be73b800,0xe005f3809b70000e,0x188e026]) (cB [0xe11ce4062380bb8,0x1cdc023384738000,0x119c2222370084e1,0x622223700708888e,0xa3738444020dce1,0x70070888ce0e1110,0x708888dc01c2c473,0x11cdc05b384738b6,0xd801c222b370178e,0xea7088a0]))) (bI j 4 (cB [0x4e11ce3adb384437,0xcee00003847b901d,0xc0004273b7000119,0x384738008ce08ad,0x47370138e11cdc04,0x60002691cd803f38,0x48e11c5805138472,0x824de01c22223701,0xdc01c2222b880708,0x70b08a]) (bI j 5 (cB [0xe16edc01c2223b8,0xcedc05b3847b8000,0x3adb3844b70002f1,0x838473701d4e11ee,0x73b8000201cee404,0x7000261cedc0009c,0x38e026dc04e3822b,0x16ee004e8073b801,0xdc0003857b70000e,0x70b026]) (cB [0x1f9cee0040385bb8,0x8ad80000137b7000,0x80009affb7000268,0xa5379600028cde9,0x7386000289ce9c00,0x60000e0fe98053a2,0x45f9ce9c0513822a,0x1ce5c052a2738601,0x58053a4738600029,0xe0ee])))) (bI j 9 (bI j 7 (cB [0x9f9ce5c052382296,0x8adc000385fb7014,0xc0407e73b800fce0,0x18073a700026c0ed,0x739701c689c69805,0x701c691c65805280,0xc601cee00717e71b,0x9cedc0468073b801,0x58000a273a60001f,0x291ce]) (bI j 8 (cB [0xe01cee00403822b8,0x2ee00403809b8016,0x40008273b70100e0,0xd073b8000351cee,0x9b70000e03edc00,0x801a8e026e006838,0xe08ae406a380bb,0x88adc01f3822b800,0xe00003823b90070d,0xf9ce]) (cB [0xe9cedc000386fb7,0x8adc05b3822b8000,0x2d9c1008b70180e0,0x382bb70070402ee,0x73b80002d9cee400,0x8000219cedc000c0,0x82d9c2dc060b673b,0xcdedc05b7e73b8eb,0x9c075b734b60002d,0x16e89ce]))) (bI j 10 (cB [0x689c094069a27326,0xce5fadba270a6eba,0x4069a47316016e91,0xba47096eba691c05,0x703601a5f9ccdfad,0x8eb6df9c2dfae97e,0xa6d9c2dc069b673b,0x7edc000382bb8eb,0xd80753828b70000e,0x705092]) (bI j 11 (cB [0xce0a2dc05b382bb8,0xcee4075b670b8eb6,0xc0009073b80003a9,0x73fa0000e12ed,0x73b8000159cee400,0x60001b9ce9c00052,0xdce08a9803738472,0x11c5800076739700,0xdc03b38229600ece,0xa4e11c]) (cB [0x559cee00293822b7,0xcee002b384738019,0xc02b3823b8010159,0xb5673b8000161ced,0x70b6000321cedc05,0x8eb6d59c2dc075c8,0x179cee40755673b,0x9cee00585e73b800,0x5c0007273a700016,0x1e9ce]))))) (bI j 18 (bI j 15 (bI j 13 (cB [0xce11ee006e5e73b8,0xcee00006a73b700b,0xc0465e73b8010179,0x35e73b80002b1ced,0x73b800bce08ae007,0x700bce02ee005b5e,0xe11fe40006073b,0x1cfe4000008ff800,0xe0000013bf800020,0x2740f]) (bI j 14 (cB [0x1b9ce9c0405273b8,0xc6dc040767397010,0x385bf801b201,0xa273e70001f9cfe,0x73f9000291cf5c00,0x8000189cee0000d4,0xe08fe4000d073f,0x9cfe4000007ff800,0xe00000183f80002d,0x305bf]) (cB [0xd69cee0075c16cf7,0xc29805b7273a7016,0x805b7a7397eb6dc9,0xbae7337eb6de9c25,0x70b7eb6eb9c0d805,0x70000e0afe3adb5a,0xd6d9c3e00753828f,0x9cee0000ea73f901,0xe80009073f800019,0x2bf]))) (bI j 16 (cB [0x21fe0000008ff9,0x1fe0000ea86f7000,0x5a46873700011a,0x4683370002d23ce,0x8c36016ed23cdc00,0x801d6d23cdfadbb4,0xd6da33dc000b68ff,0x22fdc000ea8ff801,0xe0000568ff900000,0x15a1f]) (bI j 17 (cB [0x32a3fe005a568737,0x3ce0065b48f37000,0xa7f901695a,0x7cdfc70000037fa,0x6be70001b98f1800,0x800037b7f9c00000,0x1db7f1c0006ea7e,0x81798000d8dde700,0x60000d8dfe70001b,0x3bf]) (cB [0x1d98f180007cefc7,0xbf5c0000067d7000,0xc00076a7d8000383,0x7605d6000363b75,0x97f8000363bf5c00,0x800000247dc00000,0x36f9c00000a3f,0x817dc000d8a5f800,0xe4000d8a7f800014,0x15a9f])))) (bI j 21 (bI j 19 (cB [0x32b7b9c0006eafe8,0x7f9c065b4de26000,0x5a6eaf2700036b,0xcaeed70001dabf6,0xefd70196d3b85800,0x80169dabc5c000da,0x36653dc000d8adf,0x2b4dc06ccb683600,0xdc000caa6f801b2d,0x196d298]) (bI j 20 (cB [0x95a9ce0000daa7f8,0x5fe0000caaff9016,0x806dcb6b3700036e,0xc96b360196e5a8d,0x93f700032dcbdc00,0x70196d2bce000001,0x31abfe0063b4af3,0x2bce0000b4af3900,0xd8000c96b37016ed,0x1d725a0]) (cB [0x2d05cd8075b41435,0xb0d8064b4af37000,0xc064b76b37eb92d2,0x5b4af38eb6ed2b0d,0xa7f800017abfe407,0x70000037f9c00000,0x2dabfe400000efd,0x5fdc0000193f800,0xe4000c8aff800000,0x3aabf]))) (bI j 23 (bI j 22 (cB [0x38f9c00000abf8,0xafe800000f3d7000,0x153f9000005,0xe953f8000000dfe,0x67f80003adafe400,0xa000000bfdc00001,0x1ffe400000bff,0x9bddc000006ff800,0xe00003e6ff800039,0x231ff]) (cB [0x1efdc000e67ff8,0xbfe00005e7ff9000,0x4000b07ff8000179,0x6ebfe800017a9fe,0xdfe70002c37d9c00,0x70001daff60000dc,0x373bf5c000b0ef5,0x585dc000d8bdf800,0xe0000b0a77800036,0x3729f])) (bI j 24 (cB [0x3758fe0000b0bff9,0x6fdc000b11f77000,0x4000aabff8000005,0x8cbff9000192ffe,0x33f70000056fe000,0x90002b2ffe000000,0x2efe0000e6bff,0x67fe800000ebe700,0xe00000117f900000,0x13f]) (cB [0x39e7fe4000e517f8,0x4fdc000019bf8000])))))) 38 (i % 16)
def zrV (i : Nat) := materialize [37,38,51,72,92,106] 7 127 4 (zkG i >>> 4)
def zlG (i : Nat) := (zrV i).map ztN
def zlJ (i : Nat) : Option (Nat × List Nat × List (Nat × Nat × Nat)) := some (zkG i &&& 15,zlG i,shortHist zbY 11 zlG zil i)
def zqB : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm4,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,3,5,4] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,3,5,4] 0 i.val))),(pm7,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,3,2,4,5] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,3,2,4,5] 0 i.val))),(pm8,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,3,2,5,4] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,3,2,5,4] 0 i.val))),(pm24,(fun i : Fin 64 => Fin.ofNat 64 (pA [1,0,4,5,2,3] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [1,0,4,5,2,3] 0 i.val))),(pm29,(fun i : Fin 64 => Fin.ofNat 64 (pA [1,0,5,4,2,3] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [1,0,4,5,3,2] 0 i.val))),(pm25,(fun i : Fin 64 => Fin.ofNat 64 (pA [1,0,4,5,3,2] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [1,0,5,4,2,3] 0 i.val))),(pm30,(fun i : Fin 64 => Fin.ofNat 64 (pA [1,0,5,4,3,2] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [1,0,5,4,3,2] 0 i.val)))]
def zeh := zZ zqB
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zqF : dM zbY zcg 64 zeh := zad (by decide +kernel)
def zjf (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 12 (bI j 6 (bI j 3 (bI j 1 (cB [0x2f000f00070003,0x40000000,0x400800180000001f,0x1f000000080000]) (bI j 2 (cB [0x1800000000001f,0x4000000000370000,0x840100000,0x3f00000000001f]) (cB [0x37000f0030,0x30000001f0004,0x3f0000,0x3f]))) (bI j 4 (cB [0x3f003f003f0013,0x3f00000000,0x0,0x3f00000000]) (bI j 5 (cB [0x800000018,0x3f000000180000,0x40004027,0x403f0004]) (cB [0x10340070018,0x1000000000000,0x0,0x30000])))) (bI j 9 (bI j 7 (cB [0x700000000,0x0,0x0,0x40000030]) (bI j 8 (cB [0x20003f0038003f,0x401f001f0000,0x170028003f0000,0x3f003f0000002f]) (cB [0x3f00000000,0x3f001000300010,0x44000400f]))) (bI j 10 (cB [0x0,0x0,0x0,0x130000403f]) (bI j 11 (cB [0x3f001700400030,0x403f003f0000403f,0x80014027,0x20000000004003]) (cB [0x4014003f40000020,0x400000000010,0x403f403000000000,0x40038001400f4000]))))) (bI j 18 (bI j 15 (bI j 13 (cB [0x400c000000084000,0x3f402800004000,0x3f000000204034,0x40004127003f053f]) (bI j 14 (cB [0x4000400040004000,0x40044404,0x3f4004403f003f,0x4000500f003f113f]) (cB [0x400040000000,0x400000004000,0x1f000041040000,0x3f4004403f003f]))) (bI j 16 (cB [0x10000100052f503f,0x1000000710070000,0x100110000000000,0x410503f00000010]) (bI j 17 (cB [0x10b7000004100000,0xa8005c1f543f,0x5c015c010400a801,0x541f000000005c01]) (cB [0x540300005400,0x54025402,0x5701550355035523,0x503f040001005403])))) (bI j 21 (bI j 19 (cB [0x2017701f701f,0x1016501e501f3017,0x503f503f10170000,0x1037503f10370037]) (bI j 20 (cB [0x10501f10370020,0x10001000100010,0x110001010170010,0x17003710370007]) (cB [0x0,0x543f103700170000,0x553f041e081d053f,0x503f00000000003f]))) (bI j 23 (bI j 22 (cB [0xf503270315033,0x3f0400012f043f,0x443f003f0000003f,0x50004000000153f]) (cB [0x408443f00000008,0x4c1d4c1f443f1008,0x441e441f0000,0x20443f443f443f])) (bI j 24 (cB [0x80008441f,0x3f553f453f0108,0x442b443f00000000,0x13f103f00174c29]) 0x3f003f1000))))) 16 (i % 16)
def zx := zc zbY zcg zib (fun i => zt zcg (cutPick zcY (zjf i))) 388 zlJ zeh zkM ztF zpj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zqk : ze zbY zcg zib (zt zcg zcY) zsN (zD 388 zlJ zeh zkM 0) zcB 11 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zwF : tB 0 24 zx = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem znm : tB 24 24 zx = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zpP : tB 48 24 zx = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zno : tB 72 24 zx = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zne : tB 96 24 zx = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zuZ : tB 120 24 zx = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zxm : tB 144 24 zx = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zwl : tB 168 24 zx = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem znC : tB 192 24 zx = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zrc : tB 216 24 zx = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zng : tB 240 24 zx = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zvy : tB 264 24 zx = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zsF : tB 288 24 zx = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ztl : tB 312 24 zx = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zmx : tB 336 24 zx = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zmu : tB 360 24 zx = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zvZ : tB 384 4 zx = true := by decide +kernel
theorem zwz : tB 0 48 zx = true := tM (start := 0) (left := 24) (right := 24) (check := zx) zwF znm
theorem zvf : tB 48 48 zx = true := tM (start := 48) (left := 24) (right := 24) (check := zx) zpP zno
theorem zvM : tB 0 96 zx = true := tM (start := 0) (left := 48) (right := 48) (check := zx) zwz zvf
theorem zmJ : tB 96 48 zx = true := tM (start := 96) (left := 24) (right := 24) (check := zx) zne zuZ
theorem zoW : tB 144 48 zx = true := tM (start := 144) (left := 24) (right := 24) (check := zx) zxm zwl
theorem zuf : tB 96 96 zx = true := tM (start := 96) (left := 48) (right := 48) (check := zx) zmJ zoW
theorem zuT : tB 0 192 zx = true := tM (start := 0) (left := 96) (right := 96) (check := zx) zvM zuf
theorem zrx : tB 192 48 zx = true := tM (start := 192) (left := 24) (right := 24) (check := zx) znC zrc
theorem zwW : tB 240 48 zx = true := tM (start := 240) (left := 24) (right := 24) (check := zx) zng zvy
theorem zrR : tB 192 96 zx = true := tM (start := 192) (left := 48) (right := 48) (check := zx) zrx zwW
theorem zvA : tB 288 48 zx = true := tM (start := 288) (left := 24) (right := 24) (check := zx) zsF ztl
theorem zsy : tB 360 28 zx = true := tM (start := 360) (left := 24) (right := 4) (check := zx) zmu zvZ
theorem znp : tB 336 52 zx = true := tM (start := 336) (left := 24) (right := 28) (check := zx) zmx zsy
theorem zpg : tB 288 100 zx = true := tM (start := 288) (left := 48) (right := 52) (check := zx) zvA znp
theorem zwn : tB 192 196 zx = true := tM (start := 192) (left := 96) (right := 100) (check := zx) zrR zpg
theorem zqS : tB 0 388 zx = true := tM (start := 0) (left := 192) (right := 196) (check := zx) zuT zwn
theorem zsA : tB 0 388 zx = true := zqS
theorem zxG : Known zcY := (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) zjp) zdG) zgv) zdV) zlV) zft) zcA) zcd) zeH) zjk) zlX) zex) zfb) zbK) zdF) zcp)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zmM : Lower zbY zcB zcg 12 := by
  apply lowerDag zjf _ _ _ _ zqF _ _ _ zxG _ zqk zsA
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold pW; decide +kernel
  · exact cK (by decide +kernel)
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [zcY,List.mem_cons,List.not_mem_nil,or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def zfG : Nat := 0x33333333ffffffff
abbrev zlg : Nat := gZ &&& zfG
abbrev zdj : List Nat := [0x22222222aaaaaaaa,0xcccccccc,0x30303030f0f0f0f0,0x33003300ff00ff00,0x33330000ffff0000,0x3333333300000000]
def zpY : Nat × List Nat × Nat × Nat := (zfG,zdj,11,zlg)
def zqJ := uW zdj [1538,263681,527362,791554,1057281,1327617]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zcJ : Lower zfG zdj zlg 11 := by
  apply eL (witnesses := zqJ) (cut := zbJ)
  · unfold pW; decide +kernel
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold pW; decide +kernel
  · exact uC (old := zbO) (by decide +kernel)
  · exact zcp
  · decide +kernel
def zeM : Nat := 0x3333ffff3333ffff
abbrev zhs : Nat := gZ &&& zeM
abbrev zhv : List Nat := [0x2222aaaa2222aaaa,0xcccc0000cccc,0x3030f0f03030f0f0,0x3300ff003300ff00,0x3333000033330000,0x3333ffff00000000]
def zvC : Nat × List Nat × Nat × Nat := (zeM,zhv,11,zhs)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zvK : Lower zeM zhv zhs 11 := zp (width := 64) pm4 zcJ (by decide +kernel)
def zfv : Nat := 0x33ff33ff33ff33ff
abbrev zli : Nat := gZ &&& zfv
abbrev zdo : List Nat := [0x22aa22aa22aa22aa,0xcc00cc00cc00cc,0x30f030f030f030f0,0x3300330033003300,0x33ff000033ff0000,0x33ff33ff00000000]
def zoF : Nat × List Nat × Nat × Nat := (zfv,zdo,11,zli)
def zwu := uW zdo [1538,263681,527362,793093,1057281,1327617]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zcZ : Lower zfv zdo zli 11 := by
  apply eL (witnesses := zwu) (cut := zbJ)
  · unfold pW; decide +kernel
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold pW; decide +kernel
  · exact uC (old := zbO) (by decide +kernel)
  · exact zcp
  · decide +kernel
def zdY : Nat := 0x3f3f3f3f3f3f3f3f
abbrev zll : Nat := gZ &&& zdY
abbrev zgM : List Nat := [0x2a2a2a2a2a2a2a2a,0xc0c0c0c0c0c0c0c,0x3030303030303030,0x3f003f003f003f00,0x3f3f00003f3f0000,0x3f3f3f3f00000000]
def zmZ : Nat × List Nat × Nat × Nat := (zdY,zgM,11,zll)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zmv : Lower zdY zgM zll 11 := zp (width := 64) pm7 zcZ (by decide +kernel)
def zfR : Nat := 0x55555555ffffffff
abbrev zlM : Nat := gZ &&& zfR
abbrev zgR : List Nat := [0xaaaaaaaa,0x44444444cccccccc,0x50505050f0f0f0f0,0x55005500ff00ff00,0x55550000ffff0000,0x5555555500000000]
def zrz : Nat × List Nat × Nat × Nat := (zfR,zgR,11,zlM)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zrg : Lower zfR zgR zlM 11 := zp (width := 64) pm24 zcZ (by decide +kernel)
def zfO : Nat := 0x5555ffff5555ffff
abbrev zla : Nat := gZ &&& zfO
abbrev zhU : List Nat := [0xaaaa0000aaaa,0x4444cccc4444cccc,0x5050f0f05050f0f0,0x5500ff005500ff00,0x5555000055550000,0x5555ffff00000000]
def zqH : Nat × List Nat × Nat × Nat := (zfO,zhU,11,zla)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ztO : Lower zfO zhU zla 11 := zp (width := 64) pm29 zcZ (by decide +kernel)
def zeP : Nat := 0x55ff55ff55ff55ff
abbrev zhb : Nat := gZ &&& zeP
abbrev zkQ : List Nat := [0xaa00aa00aa00aa,0x44cc44cc44cc44cc,0x50f050f050f050f0,0x5500550055005500,0x55ff000055ff0000,0x55ff55ff00000000]
def zwv : Nat × List Nat × Nat × Nat := (zeP,zkQ,11,zhb)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zpO : Lower zeP zkQ zhb 11 := zp (width := 64) pm24 zcJ (by decide +kernel)
def zdn : Nat := 0x5f5f5f5f5f5f5f5f
abbrev zlL : Nat := gZ &&& zdn
abbrev zlc : List Nat := [0xa0a0a0a0a0a0a0a,0x4c4c4c4c4c4c4c4c,0x5050505050505050,0x5f005f005f005f00,0x5f5f00005f5f0000,0x5f5f5f5f00000000]
def zug : Nat × List Nat × Nat × Nat := (zdn,zlc,11,zlL)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zsJ : Lower zdn zlc zlL 11 := zp (width := 64) pm25 zcJ (by decide +kernel)
def zdt : Nat := 0xbbbbbbbbbbbbbbbb
abbrev zhJ : Nat := gZ &&& zdt
abbrev zfS : List Nat := [0xaaaaaaaaaaaaaaaa,0x8888888888888888,0xb0b0b0b0b0b0b0b0,0xbb00bb00bb00bb00,0xbbbb0000bbbb0000,0xbbbbbbbb00000000]
def zmQ : Nat × List Nat × Nat × Nat := (zdt,zfS,11,zhJ)
def zqg := uW zfS [6668,263681,530953,793093,1057281,1327617]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zgt : Lower zdt zfS zhJ 11 := by
  apply eL (witnesses := zqg) (cut := zbJ)
  · unfold pW; decide +kernel
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold pW; decide +kernel
  · exact uC (old := zbO) (by decide +kernel)
  · exact zcp
  · decide +kernel
def zer : Nat := 0xdddddddddddddddd
abbrev zjR : Nat := gZ &&& zer
abbrev zjJ : List Nat := [0x8888888888888888,0xcccccccccccccccc,0xd0d0d0d0d0d0d0d0,0xdd00dd00dd00dd00,0xdddd0000dddd0000,0xdddddddd00000000]
def zvw : Nat × List Nat × Nat × Nat := (zer,zjJ,11,zjR)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zob : Lower zer zjJ zjR 11 := zp (width := 64) pm24 zgt (by decide +kernel)
def zdL : Nat := 0xf3f3f3f3f3f3f3f3
abbrev ziE : Nat := gZ &&& zdL
abbrev zdU : List Nat := [0xa2a2a2a2a2a2a2a2,0xc0c0c0c0c0c0c0c0,0xf0f0f0f0f0f0f0f0,0xf300f300f300f300,0xf3f30000f3f30000,0xf3f3f3f300000000]
def zos : Nat × List Nat × Nat × Nat := (zdL,zdU,11,ziE)
def znX := uW zdU [6668,265220,530953,793093,1057281,1327617]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zcV : Lower zdL zdU ziE 11 := by
  apply eL (witnesses := znX) (cut := zbJ)
  · unfold pW; decide +kernel
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold pW; decide +kernel
  · exact uC (old := zbO) (by decide +kernel)
  · exact zcp
  · decide +kernel
def zeL : Nat := 0xf5f5f5f5f5f5f5f5
abbrev zhj : Nat := gZ &&& zeL
abbrev zfu : List Nat := [0xa0a0a0a0a0a0a0a0,0xc4c4c4c4c4c4c4c4,0xf0f0f0f0f0f0f0f0,0xf500f500f500f500,0xf5f50000f5f50000,0xf5f5f5f500000000]
def zmP : Nat × List Nat × Nat × Nat := (zeL,zfu,11,zhj)
def zsL := uW zfu [6668,265220,527362,791554,1059333,1329669]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zcX : Lower zeL zfu zhj 11 := by
  apply eL (witnesses := zsL) (cut := zdb)
  · unfold pW; decide +kernel
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold pW; decide +kernel
  · exact uC (old := zga) (by decide +kernel)
  · exact zdF
  · decide +kernel
def zfe : Nat := 0xff33ff33ff33ff33
abbrev zhG : Nat := gZ &&& zfe
abbrev zkf : List Nat := [0xaa22aa22aa22aa22,0xcc00cc00cc00cc00,0xf030f030f030f030,0xff00ff00ff00ff00,0xff330000ff330000,0xff33ff3300000000]
def zsx : Nat × List Nat × Nat × Nat := (zfe,zkf,11,zhG)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zuE : Lower zfe zkf zhG 11 := zp (width := 64) pm7 zcV (by decide +kernel)
def zgi : Nat := 0xff55ff55ff55ff55
abbrev zkV : Nat := gZ &&& zgi
abbrev zjg : List Nat := [0xaa00aa00aa00aa00,0xcc44cc44cc44cc44,0xf050f050f050f050,0xff00ff00ff00ff00,0xff550000ff550000,0xff55ff5500000000]
def zwL : Nat × List Nat × Nat × Nat := (zgi,zjg,11,zkV)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zmO : Lower zgi zjg zkV 11 := zp (width := 64) pm7 zcX (by decide +kernel)
def zgg : Nat := 0xffff3333ffff3333
abbrev zmc : Nat := gZ &&& zgg
abbrev zjH : List Nat := [0xaaaa2222aaaa2222,0xcccc0000cccc0000,0xf0f03030f0f03030,0xff003300ff003300,0xffff0000ffff0000,0xffff333300000000]
def znM : Nat × List Nat × Nat × Nat := (zgg,zjH,11,zmc)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zpC : Lower zgg zjH zmc 11 := zp (width := 64) pm24 zcX (by decide +kernel)
def zek : Nat := 0xffff5555ffff5555
abbrev zhd : Nat := gZ &&& zek
abbrev zkw : List Nat := [0xaaaa0000aaaa0000,0xcccc4444cccc4444,0xf0f05050f0f05050,0xff005500ff005500,0xffff0000ffff0000,0xffff555500000000]
def ztg : Nat × List Nat × Nat × Nat := (zek,zkw,11,zhd)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zpe : Lower zek zkw zhd 11 := zp (width := 64) pm24 zcV (by decide +kernel)
def zeo : Nat := 0xffffffff33333333
abbrev zlR : Nat := gZ &&& zeo
abbrev zgy : List Nat := [0xaaaaaaaa22222222,0xcccccccc00000000,0xf0f0f0f030303030,0xff00ff0033003300,0xffff000033330000,0xffffffff00000000]
def zor : Nat × List Nat × Nat × Nat := (zeo,zgy,11,zlR)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zpy : Lower zeo zgy zlR 11 := zp (width := 64) pm29 zcX (by decide +kernel)
def zeX : Nat := 0xffffffff55555555
abbrev zgn : Nat := gZ &&& zeX
abbrev zho : List Nat := [0xaaaaaaaa00000000,0xcccccccc44444444,0xf0f0f0f050505050,0xff00ff0055005500,0xffff000055550000,0xffffffff00000000]
def zol : Nat × List Nat × Nat × Nat := (zeX,zho,11,zgn)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zpA : Lower zeX zho zgn 11 := zp (width := 64) pm29 zcV (by decide +kernel)
def pm31 : List (List (Nat × Nat) × List (Nat × Nat)) := [st02]
def pm32 : List (List (Nat × Nat) × List (Nat × Nat)) := [st02,st03]
def zuN : Nat := (cB [0x1804060100c0203,0xc100a010280a0702,0x80d048340a0d0482,0x30280c0003060381,0x60180a0600018120,0x2808070101c02070,0x20b06028120a000,0xd00834100b0102c,0x2038040e0403408,0x3c120f0283c100e,0x802060400c080306,0x8070481c00070401,0xb0002c080a008281,0x38000d0602c0a0,0x3c020f048380a0e0,0x18030403c080f010,0xb02828100704818,0x3c020e0103408])
def zsH : Nat := (cB [0xb5f1e73e3f1c7793,0xdffeffffc7fff8ff,0xe6ff07cff81f8f1c,0xf8fff80fffe00fe0])
def zmw : Nat := (cB [0x4a1c4a4609456391,0x2020000042080026,0x1944d41a90932d18,0x78886ad24c24ec0])
def zbV : Nat := 0xffff
abbrev zci : Nat := gZ &&& zbV
abbrev zct : List Nat := [0xaaaa,0xcccc,0xf0f0,0xff00]
def zkK : Nat × List Nat × Nat × Nat := (zbV,zct,6,zci)
def zcR : List (Nat × List Nat × Nat × Nat) := []
def zkA : Option ({rows : List Nat // rows.length = 24}) := some ⟨[3,6,10,13,3,6,10,13,3,6,10,13,2,5,9,12,2,5,9,12,2,5,9,12],rfl⟩
def zoc := uW zct [1538,263681,527362,791554]
def zvm (i : Nat) : Nat := uP 0xa28301 6 i
def zmT (i : Nat) : Nat := uP (cB [0x31010c504010000f,0x1292c5]) 17 i
def zoT (i : Nat) : Nat := uP 0x3144010803c 15 i
def zjd := pageLinks zvm zmT 3 13 2 4
def zmb (i : Nat) : Nat × Nat :=
  let e := zoT i
  (e &&& 3,e >>> 2)
def znQ : Nat × Nat := (zuN,64)
def zuU := zac zbV 64 (zA zct zsH zmw 64) 5 zmb
def zgw := zam zbV zct 5 zmb
def zps : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm31,(fun i : Fin 64 => Fin.ofNat 64 (pA [2,1,0,3,4,5] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [2,1,0,3,4,5] 0 i.val))),(pm32,(fun i : Fin 64 => Fin.ofNat 64 (pA [3,1,0,2,4,5] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [2,1,3,0,4,5] 0 i.val)))]
def zes := zZ zps
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zwD : dM zbV zci 64 zes := zad (by decide +kernel)
def zhr (i : Nat) : Nat :=
  let j := i / 16
  uP 0x0 1 (i % 16)
def zhY := zc zbV zci zkA (fun i => zt zci (cutPick zcR (zhr i))) 3 zgw zes zjd znQ zuU
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zwp : ze zbV zci zkA (zt zci zcR) zoc (zD 3 zgw zes zjd 0) zct 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zxt : tB 0 3 zhY = true := by decide +kernel
theorem zrT : tB 0 3 zhY = true := zxt
theorem zpI : Known zcR := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zeE : Lower zbV zct zci 6 := by
  apply lowerDag zhr _ _ _ _ zwD _ _ _ zpI _ zwp zrT
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold pW; decide +kernel
  · exact cK (by decide +kernel)
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [zcR,List.mem_cons,List.not_mem_nil,or_false]
    intro b h
    exact False.elim h
def st15 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xcccccccc33333333,0),(0xcccccccc,30)],[(0x3333333300000000,30)])
def pm33 : List (List (Nat × Nat) × List (Nat × Nat)) := [st03,st01,st24,st15]
def zeq : Nat := 0xcccc3333
abbrev zht : Nat := gZ &&& zeq
abbrev ziy : List Nat := [0x88882222,0xcccc0000,0xc0c03030,0xcc003300]
def znZ : Nat × List Nat × Nat × Nat := (zeq,ziy,6,zht)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zpR : Lower zeq ziy zht 6 := zp (width := 64) pm33 zbU (by decide +kernel)
def zfz : Nat := 0xff00ff00
abbrev zlF : Nat := gZ &&& zfz
abbrev zhF : List Nat := [0xaa00aa00,0xcc00cc00,0xf000f000,0xff000000]
def zha : Nat × List Nat × Nat × Nat := (zfz,zhF,5,zlF)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zjK : Lower zfz zhF zlF 5 := zp (width := 64) pm7 zbG (by decide +kernel)
def zdk : Nat := 0xffff0000
abbrev zhk : Nat := gZ &&& zdk
abbrev zhT : List Nat := [0xaaaa0000,0xcccc0000,0xf0f00000,0xff000000]
def ziZ : Nat × List Nat × Nat × Nat := (zdk,zhT,5,zhk)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zjG : Lower zdk zhT zhk 5 := zp (width := 64) pm23 zbG (by decide +kernel)
def zmX : Nat := (cB [0x1804060100c0203,0xc100a010280a0702,0x80d048340a0d0482,0x3080440211060381,0x9058281502854241,0x6830190486428160,0x281c06070301a090,0x30280c00030c070,0x281800060900c12,0x81c2806090181806,0x8000a0201c040700,0xa09028180a0482,0xd0402c040b0082c3,0x1038100d02034020,0x3c0a0f04038080e0,0xa1100044180f048,0x110a044241104844,0x804c04130084c30,0x582015020540215,0xc0a1708058081601,0x190086428170905,0xa04068041a080641,0xc06c241b0486c201,0x74201c04070081c0,0x281d06074121d028,0x1e09078181e0c074,0x400c08030c07828])
def ztx : Nat := (cB [0xfff1f8383c19f793,0xfc6648ffc3e38fc7,0xfc03f1f8e07e3fff,0x7fc03fc3878f1c,0x3f80fe03ffc01ff,0x3ffffe00007fffc0,0xff80000003fff000,0x3fffffff])
def zrP : Nat := (cB [0x2330488898089391,0x2022402600608241,0x801108844021212,0x954812589858d18,0x12d80ec055a40152,0xa6caa40012692581,0x9c00060623776000,0x3b1349a4])
def zbH : Nat := 0xffffffff
abbrev zcl : Nat := gZ &&& zbH
abbrev zbI : List Nat := [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000]
def zvT : Nat × List Nat × Nat × Nat := (zbH,zbI,9,zcl)
def zcQ : List (Nat × List Nat × Nat × Nat) := [zkK,znZ,zcW,zdR,zcI,zha,ziZ,zS,zkC,zwc]
def zkz : Option ({rows : List Nat // rows.length = 24}) := some ⟨[3,6,10,13,17,28,3,6,10,13,17,28,5,9,12,18,20,24,5,9,12,18,20,24],rfl⟩
def ztC := uW zbI [1538,263681,527362,791554,1057281]
def znR (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 4 (bI j 2 (bI j 1 (cB [0x80160037100e8001,0x4600180060016105,0x9046401884620180,0x198c6601]) (cB [0x401d007401b106c0,0x7831d847601d047,0x3808e023808e01fa,0x238c8e02])) (bI j 3 (cB [0xa42a8094b2500940,0x4b202c80b202c80a,0xe80b622d04b402c8,0x2e90ba02]) (cB [0x263080c203080c20,0xd203404d003384c,0x700dc03494d20348,0x372cdc03]))) (bI j 6 (bI j 5 (cB [0xa03e80f433c84f20,0x90254080fa43e80f,0x7091064401100430,0x48012004]) (cB [0x4249012404809200,0x13a04e813244a152,0xf293a14e813a04e8,0x56015044])) (bI j 7 (cB [0x158016005611580,0x17415d01686588d6,0x6019805dc57605d8,0x66119806]) (bI j 8 (cB [0x66680da006801a00,0x1b2f6c81b206c81a,0x605d237481d01740,0x7691da07]) (cB [0xc27a85e437885e20,0x1f107c01e]))))) 14 (i % 16)
def zsm (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 8 (bI j 4 (bI j 2 (bI j 1 (cB [0x300090080200001f,0x7006c420130f003c,0x602b97009c6601f1,0x8c547c3141d00de6,0x3272a0c7c9631b23,0xaa0cae96]) (cB [0xd4620328cdcb8335,0x98acee627399884,0x692db524b1066374,0x3d0ac38c1a4dee,0x31481809c0601b01,0x40c5408])) (bI j 3 (cB [0x14327060c7c1431b,0x818801c335860cae,0xc62b0a189c266210,0xb0e22692d8824b02,0x92c0318800a0310b,0x3b0e20c]) (cB [0x1a930058cd012640,0x7a4b01e620048c50,0x292c0798d40c6208,0x98902a9340930e02,0xc380924b00e6200a,0xc809a24]))) (bI j 6 (bI j 5 (cB [0x3632a0d0c7a32032,0xea4b0386208d8cd8,0xe0340f80a23ac380,0xc50340081001023,0x620138d044634011,0x14989850]) (cB [0x569331524b252632,0x20c505af449530e0,0xa92c13189c4a6201,0xca04a6401219024,0x6201780784c34c16,0x18a4b060])) (bI j 7 (cB [0x680370d802064c38,0xc30e06e9321b18c8,0xa0351a98c072f441,0x98f4786201d8c506,0xf9ea4f67892c1e,0x2000c47e]) (cB [0x6031b0e0c5408314,0x988076337980c9c,0xac38a0a4b0886272,0x24b00c6200298808,0x62023003886c3821,0x21a4b00e])))) (bI j 12 (bI j 10 (bI j 9 (cB [0x4431d040c5286c38,0x53d1092642241900,0x40082330e0123142,0xcd09e0112600401,0x31429bd10a434028,0x2730e09a]) (cB [0x9c31c28b0e016008,0xaa4c018008289900,0x6f442d30e0b29322,0xa4b0ac02b068020b,0x82c30f0b0c382b,0x1180441c])) (bI j 11 (cB [0xba620240c504e013,0xea4b0c663330189c,0xe3143230e2c6933a,0xb0e0bc92c128c741,0x93e308c704c0112f,0xb130f8c4]) (cB [0xbe92c231880c4932,0x3188092314afb0e0,0xc92c3498f4ce6273,0x804cd031cb4a4f6c,0x3143680dcd802b35,0xe8c5420]))) (bI j 14 (bI j 13 (cB [0x7032b990c9c5431f,0xd18ac826201e0cde,0xc92c3318dcba635a,0x30e0e29373824b4d,0x9352124b02262039,0x37b0e0bc]) (cB [0xdec3821a4b024620,0x88c94263143a0048,0xcf44b830e0ea9321,0x74560130a0020e,0x351b00a4f201f3c,0x220c526c])) (bI j 15 (cB [0xce343300d04f631d,0xf24d0ea92c3e1880,0x4940403d12eac383,0xd08c2340160044f,0x1f0a8020fa93434,0x3e9880f4]) (bI j 16 (cB [0x2c0083fb100fec38,0xfa4c104f443f1890,0xe3144224f6e292c3,0x8cdc7232b168c7c2,0x6272518848a6209c,0x2d98aca6]) (cB [0xe492cad98dea6633,0x124dd009333b24b4,0xbb30e6e4c384])))))) 22 (i % 16)
def zqO (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 4 (bI j 2 (bI j 1 (cB [0x3c080100201f00,0x40620a3140200d81,0x23150261c0298801,0x219a058c6c08c801,0x78cd4092601a31f0,0x3100]) (cB [0x30e0452582262002,0x92682a6270231081,0x20090161c0118ac0,0x91950c8c786404c3,0xf803c05258326201,0x140])) (bI j 3 (cB [0xc5088026020401f,0xc4048314241a011,0x4620221a091189c9,0xc4999124b088c4c4,0x7806c05e88443282,0xf1]) (cB [0xb0e0bd2585e6202f,0xc606a0373400f80,0x8c38344991a18c8d,0xb18a1d80dc05e886,0xf8c5004c7a766203,0x79]))) (bI j 6 (bI j 5 (cB [0x24b108c407e0313f,0x98707e6273f61c21,0x6404818a8080391,0xc18d80bd1120c849,0x630e1346289a0104,0x8a]) (cB [0xd0131870a23344c,0x9260aa31f017a226,0xac38564962b00ad5,0x17a22ab0e155264a,0xf24b178c40ba3350,0x61c2])) (bI j 7 (cB [0xa4f984638c26275d,0x866e02c385d319ae,0xc31c68313b318819,0xb009b5988004c7ac,0x7a4b1ac06ed602b6,0x61c3]) (bI j 8 (cB [0xb0e1ad26ed692d6b,0x1264e80127431080,0x1d7831380bd11d,0x818ebc2501e803ef,0xfa4d1e1268fa6207,0x61c3]) (cB [0xbd1208c5602f4478,0x18700293d8431b80]))))) 21 (i % 16)
def ziC := pageLinks znR zsm 5 13 8 6
def zgC (i : Nat) : Nat × Nat :=
  let e := zqO i
  (e &&& 255,e >>> 8)
def zrE : Nat × Nat := (zmX,96)
def zuz := zac zbH 96 (zA zbI ztx zrP 96) 8 zgC
def zgG := zam zbH zbI 8 zgC
def zuv : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm7,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,3,2,4,5] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,3,2,4,5] 0 i.val)))]
def zel := zZ zuv
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zrQ : dM zbH zcl 64 zel := zad (by decide +kernel)
def zmh (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 4 (bI j 2 (bI j 1 (cB [0x10020082401,0x208000010000,0x201000]) (cB [0x1,0x6000020d0040,0xc73fd000])) (bI j 3 (cB [0xe0400ff5cd,0x10000000,0x8027d000]) (cB [0x2740000000,0x275100010001,0x185000]))) (bI j 6 (bI j 5 (cB [0x4800000020581,0x847d4410058563c0,0x1]) (cB [0x2509d007c5000a4,0xc400020050000000,0x207])) (bI j 7 (cB [0x9e6010000020080,0x91008000000,0x1000]) (bI j 8 (cB [0x3f40100000,0x2c000000017f40,0x94000]) 0x80400b74002f400)))) 10 (i % 16)
def zbE := zc zbH zcl zkz (fun i => zt zcl (cutPick zcQ (zmh i))) 134 zgG zel ziC zrE zuz
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zwa : ze zbH zcl zkz (zt zcl zcQ) ztC (zD 134 zgG zel ziC 0) zbI 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zri : tB 0 24 zbE = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zvz : tB 24 24 zbE = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zoG : tB 48 24 zbE = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zoy : tB 72 24 zbE = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zuL : tB 96 24 zbE = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zud : tB 120 14 zbE = true := by decide +kernel
theorem zqE : tB 24 48 zbE = true := tM (start := 24) (left := 24) (right := 24) (check := zbE) zvz zoG
theorem ztR : tB 0 72 zbE = true := tM (start := 0) (left := 24) (right := 48) (check := zbE) zri zqE
theorem zuu : tB 96 38 zbE = true := tM (start := 96) (left := 24) (right := 14) (check := zbE) zuL zud
theorem zsO : tB 72 62 zbE = true := tM (start := 72) (left := 24) (right := 38) (check := zbE) zoy zuu
theorem zmG : tB 0 134 zbE = true := tM (start := 0) (left := 72) (right := 62) (check := zbE) ztR zsO
theorem zuJ : tB 0 134 zbE = true := zmG
theorem zqI : Known zcQ := (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) zkn) zml) zG) zjG) zjK) zbG) zcA) zcd) zpR) zeE)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zbN : Lower zbH zbI zcl 9 := by
  apply lowerDag zmh _ _ _ _ zrQ _ _ _ zqI _ zwa zuJ
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold pW; decide +kernel
  · exact cK (by decide +kernel)
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [zcQ,List.mem_cons,List.not_mem_nil,or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def zdP : Nat := 0xffffffffffff
abbrev zit : Nat := gZ &&& zdP
abbrev zem : List Nat := [0xaaaaaaaaaaaa,0xcccccccccccc,0xf0f0f0f0f0f0,0xff00ff00ff00,0xffff0000,0xffff00000000]
def zus : Nat × List Nat × Nat × Nat := (zdP,zem,10,zit)
def zvx := uW zem [1538,263681,527362,791554,1057281,1327617]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zjN : Lower zdP zem zit 10 := by
  apply eL (witnesses := zvx) (cut := zbH)
  · unfold pW; decide +kernel
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold pW; decide +kernel
  · exact uC (old := zbI) (by decide +kernel)
  · exact zbN
  · decide +kernel
def zfm : Nat := 0xff00ffffffffff
abbrev zkF : Nat := gZ &&& zfm
abbrev zdq : List Nat := [0xaa00aaaaaaaaaa,0xcc00cccccccccc,0xf000f0f0f0f0f0,0xff00ff00,0xff0000ffff0000,0xff00ff00000000]
def znx : Nat × List Nat × Nat × Nat := (zfm,zdq,10,zkF)
def zoj := uW zdq [1538,263681,527362,791554,1057281,1327617]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zde : Lower zfm zdq zkF 10 := by
  apply eL (witnesses := zoj) (cut := zbH)
  · unfold pW; decide +kernel
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold pW; decide +kernel
  · exact uC (old := zbI) (by decide +kernel)
  · exact zbN
  · decide +kernel
def zeU : Nat := 0xffffff00ffffff
abbrev zhD : Nat := gZ &&& zeU
abbrev zjT : List Nat := [0xaaaaaa00aaaaaa,0xcccccc00cccccc,0xf0f0f000f0f0f0,0xff000000ff00,0xff000000ff0000,0xffffff00000000]
def zwS : Nat × List Nat × Nat × Nat := (zeU,zjT,10,zhD)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zxh : Lower zeU zjT zhD 10 := zp (width := 64) pm4 zde (by decide +kernel)
def zfn : Nat := 0xf0f0f0fffffffff
abbrev zka : Nat := gZ &&& zfn
abbrev zhp : List Nat := [0xa0a0a0aaaaaaaaa,0xc0c0c0ccccccccc,0xf0f0f0f0,0xf000f00ff00ff00,0xf0f0000ffff0000,0xf0f0f0f00000000]
def zni : Nat × List Nat × Nat × Nat := (zfn,zhp,10,zka)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zsh : Lower zfn zhp zka 10 := zp (width := 64) pm7 zde (by decide +kernel)
def zfW : Nat := 0xf0fffff0f0fffff
abbrev zgZ : Nat := gZ &&& zfW
abbrev zke : List Nat := [0xa0aaaaa0a0aaaaa,0xc0ccccc0c0ccccc,0xf0f00000f0f0,0xf00ff000f00ff00,0xf0f00000f0f0000,0xf0fffff00000000]
def zxN : Nat × List Nat × Nat × Nat := (zfW,zke,10,zgZ)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ztZ : Lower zfW zke zgZ 10 := zp (width := 64) pm8 zde (by decide +kernel)
def zeG : Nat := 0xfff0fff0fff0fff
abbrev zjX : Nat := gZ &&& zeG
abbrev zkW : List Nat := [0xaaa0aaa0aaa0aaa,0xccc0ccc0ccc0ccc,0xf000f000f000f0,0xf000f000f000f00,0xfff00000fff0000,0xfff0fff00000000]
def zrh : Nat × List Nat × Nat × Nat := (zeG,zkW,10,zjX)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zrW : Lower zeG zkW zjX 10 := zp (width := 64) pm24 zjN (by decide +kernel)
def zeD : Nat := 0xaaaaaaaaffffffff
abbrev zkc : Nat := gZ &&& zeD
abbrev zfr : List Nat := [0xaaaaaaaaaaaaaaaa,0x88888888cccccccc,0xa0a0a0a0f0f0f0f0,0xaa00aa00ff00ff00,0xaaaa0000ffff0000,0xaaaaaaaa00000000]
def ztP : Nat × List Nat × Nat × Nat := (zeD,zfr,10,zkc)
def zvP := uW zfr [1538,263681,527362,791554,1057281,1327617]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zcL : Lower zeD zfr zkc 10 := by
  apply eL (witnesses := zvP) (cut := zbH)
  · unfold pW; decide +kernel
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold pW; decide +kernel
  · exact uC (old := zbI) (by decide +kernel)
  · exact zbN
  · decide +kernel
def zfM : Nat := 0xaaaaffffaaaaffff
abbrev zgF : Nat := gZ &&& zfM
abbrev zlo : List Nat := [0xaaaaaaaaaaaaaaaa,0x8888cccc8888cccc,0xa0a0f0f0a0a0f0f0,0xaa00ff00aa00ff00,0xaaaa0000aaaa0000,0xaaaaffff00000000]
def zqn : Nat × List Nat × Nat × Nat := (zfM,zlo,10,zgF)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zxJ : Lower zfM zlo zgF 10 := zp (width := 64) pm4 zcL (by decide +kernel)
def zez : Nat := 0xccccccccffffffff
abbrev zlQ : Nat := gZ &&& zez
abbrev zfY : List Nat := [0x88888888aaaaaaaa,0xcccccccccccccccc,0xc0c0c0c0f0f0f0f0,0xcc00cc00ff00ff00,0xcccc0000ffff0000,0xcccccccc00000000]
def zoe : Nat × List Nat × Nat × Nat := (zez,zfY,10,zlQ)
def zoh := uW zfY [1538,263681,527362,791554,1057281,1336338]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zcM : Lower zez zfY zlQ 10 := by
  apply eL (witnesses := zoh) (cut := zbH)
  · unfold pW; decide +kernel
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold pW; decide +kernel
  · exact uC (old := zbI) (by decide +kernel)
  · exact zbN
  · decide +kernel
def zei : Nat := 0xaaffaaffaaffaaff
abbrev zgJ : Nat := gZ &&& zei
abbrev zgu : List Nat := [0xaaaaaaaaaaaaaaaa,0x88cc88cc88cc88cc,0xa0f0a0f0a0f0a0f0,0xaa00aa00aa00aa00,0xaaff0000aaff0000,0xaaffaaff00000000]
def zrL : Nat × List Nat × Nat × Nat := (zei,zgu,10,zgJ)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zoZ : Lower zei zgu zgJ 10 := zp (width := 64) pm24 zcM (by decide +kernel)
def zeF : Nat := 0xafafafafafafafaf
abbrev zhL : Nat := gZ &&& zeF
abbrev zjs : List Nat := [0xaaaaaaaaaaaaaaaa,0x8c8c8c8c8c8c8c8c,0xa0a0a0a0a0a0a0a0,0xaf00af00af00af00,0xafaf0000afaf0000,0xafafafaf00000000]
def ztc : Nat × List Nat × Nat × Nat := (zeF,zjs,10,zhL)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zmY : Lower zeF zjs zhL 10 := zp (width := 64) pm25 zcM (by decide +kernel)
def zfl : Nat := 0xccccffffccccffff
abbrev zhw : Nat := gZ &&& zfl
abbrev zku : List Nat := [0x8888aaaa8888aaaa,0xcccccccccccccccc,0xc0c0f0f0c0c0f0f0,0xcc00ff00cc00ff00,0xcccc0000cccc0000,0xccccffff00000000]
def zty : Nat × List Nat × Nat × Nat := (zfl,zku,10,zhw)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zsk : Lower zfl zku zhw 10 := zp (width := 64) pm4 zcM (by decide +kernel)
def zfs : Nat := 0xccffccffccffccff
abbrev ziT : Nat := gZ &&& zfs
abbrev zjV : List Nat := [0x88aa88aa88aa88aa,0xcccccccccccccccc,0xc0f0c0f0c0f0c0f0,0xcc00cc00cc00cc00,0xccff0000ccff0000,0xccffccff00000000]
def zod : Nat × List Nat × Nat × Nat := (zfs,zjV,10,ziT)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zuH : Lower zfs zjV ziT 10 := zp (width := 64) pm24 zcL (by decide +kernel)
def zec : Nat := 0xcfcfcfcfcfcfcfcf
abbrev zlf : Nat := gZ &&& zec
abbrev ziO : List Nat := [0x8a8a8a8a8a8a8a8a,0xcccccccccccccccc,0xc0c0c0c0c0c0c0c0,0xcf00cf00cf00cf00,0xcfcf0000cfcf0000,0xcfcfcfcf00000000]
def zrJ : Nat × List Nat × Nat × Nat := (zec,ziO,10,zlf)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zvr : Lower zec ziO zlf 10 := zp (width := 64) pm25 zcL (by decide +kernel)
def zdv : Nat := 0xf0f0f0f0ffffffff
abbrev ziU : Nat := gZ &&& zdv
abbrev zeK : List Nat := [0xa0a0a0a0aaaaaaaa,0xc0c0c0c0cccccccc,0xf0f0f0f0f0f0f0f0,0xf000f000ff00ff00,0xf0f00000ffff0000,0xf0f0f0f000000000]
def zth : Nat × List Nat × Nat × Nat := (zdv,zeK,10,ziU)
def zsY := uW zeK [1538,263681,527362,791554,1057281,1329669]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zbT : Lower zdv zeK ziU 10 := by
  apply eL (witnesses := zsY) (cut := zbH)
  · unfold pW; decide +kernel
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold pW; decide +kernel
  · exact uC (old := zbI) (by decide +kernel)
  · exact zbN
  · decide +kernel
def zdQ : Nat := 0xf0f0fffff0f0ffff
abbrev zjc : Nat := gZ &&& zdQ
abbrev zko : List Nat := [0xa0a0aaaaa0a0aaaa,0xc0c0ccccc0c0cccc,0xf0f0f0f0f0f0f0f0,0xf000ff00f000ff00,0xf0f00000f0f00000,0xf0f0ffff00000000]
def zpp : Nat × List Nat × Nat × Nat := (zdQ,zko,10,zjc)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ztA : Lower zdQ zko zjc 10 := zp (width := 64) pm4 zbT (by decide +kernel)
def zfD : Nat := 0xffff0000ffffffff
abbrev zhf : Nat := gZ &&& zfD
abbrev zdZ : List Nat := [0xaaaa0000aaaaaaaa,0xcccc0000cccccccc,0xf0f00000f0f0f0f0,0xff000000ff00ff00,0xffff0000ffff0000,0xffff000000000000]
def zwE : Nat × List Nat × Nat × Nat := (zfD,zdZ,10,zhf)
def zsP := uW zdZ [1538,263681,527362,791554,1057281,1336338]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zcE : Lower zfD zdZ zhf 10 := by
  apply eL (witnesses := zsP) (cut := zbH)
  · unfold pW; decide +kernel
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold pW; decide +kernel
  · exact uC (old := zbI) (by decide +kernel)
  · exact zbN
  · decide +kernel
def zff : Nat := 0xf0fff0fff0fff0ff
abbrev ziq : Nat := gZ &&& zff
abbrev zlS : List Nat := [0xa0aaa0aaa0aaa0aa,0xc0ccc0ccc0ccc0cc,0xf0f0f0f0f0f0f0f0,0xf000f000f000f000,0xf0ff0000f0ff0000,0xf0fff0ff00000000]
def ztI : Nat × List Nat × Nat × Nat := (zff,zlS,10,ziq)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zwH : Lower zff zlS ziq 10 := zp (width := 64) pm24 zcE (by decide +kernel)
def zdO : Nat := 0xf0f0f0f0f0f0f0f0
abbrev zhZ : Nat := gZ &&& zdO
abbrev zfL : List Nat := [0xa0a0a0a0a0a0a0a0,0xc0c0c0c0c0c0c0c0,0xf000f000f000f000,0xf0f00000f0f00000,0xf0f0f0f000000000]
def zdr : Nat × List Nat × Nat × Nat := (zdO,zfL,8,zhZ)
def zoA := uW zfL [6668,265220,530949,797189,1067525]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zcu : Lower zdO zfL zhZ 8 := by
  apply eL (witnesses := zoA) (cut := zbL)
  · unfold pW; decide +kernel
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold pW; decide +kernel
  · exact uC (old := zbP) (by decide +kernel)
  · exact zbK
  · decide +kernel
def zea : Nat := 0xf0f00000f0f0
abbrev zlh : Nat := gZ &&& zea
abbrev zgm : List Nat := [0xa0a00000a0a0,0xc0c00000c0c0,0xf0000000f000,0xf0f000000000]
def zrD : Nat × List Nat × Nat × Nat := (zea,zgm,5,zlh)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zvp : Lower zea zgm zlh 5 := zp (width := 64) pm4 zbG (by decide +kernel)
def zdI : Nat := 0xf000f000f000f0
abbrev zhy : Nat := gZ &&& zdI
abbrev zgK : List Nat := [0xa000a000a000a0,0xc000c000c000c0,0xf0000000f00000,0xf000f000000000]
def zdM : Nat × List Nat × Nat × Nat := (zdI,zgK,5,zhy)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zfk : Lower zdI zgK zhy 5 := zp (width := 64) pm14 zbG (by decide +kernel)
def pm34 : List (List (Nat × Nat) × List (Nat × Nat)) := [st05,st03,st34]
def zgh : Nat := 0x5050505050505050
abbrev ziI : Nat := gZ &&& zgh
abbrev ziM : List Nat := [0x4040404040404040,0x5000500050005000,0x5050000050500000,0x5050505000000000]
def zhR : Nat × List Nat × Nat × Nat := (zgh,ziM,5,ziI)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zlZ : Lower zgh ziM ziI 5 := zp (width := 64) pm34 zbG (by decide +kernel)
def znF : Nat := (cB [0x81c0806010180403,0x8180d02834040a02,0x8150285424130603,0xc090682816090582,0x289444230a070181,0xa848261109848250,0x2432120b0182c110,0x3120d02834110c8,0x281844030900c0a,0x182806090181806,0x808070101c480611,0x40b11028240a0602,0xf02038040e020340,0x205404130603c0a0,0x5c0a170205804160,0x241b010682817090,0x1d060740a1d02070,0xa078241e0607828,0x980426020940423,0x848271109c0a2702,0xa2d020b0442b010a,0xe060b8482d060b40,0x90cc0432120b8442,0xd40a35020d044330,0x2836090d848350a0,0x3a090e84836110d8,0x120f0283c060f044])
def zoa : Nat := (cB [0x1d73cc6070070769,0xf339399f00761d73,0x1f87e1fde1fdf7ff,0xfe7ef87f8cdedeee,0xe0e0f0e7f8fe7e,0xf800ff80ff80ff80,0xffff00000f00ff00,0xfff0000ffff0000,0xffffffff00000000])
def zxH : Nat := (cB [0x410400090020228,0x6329291300100410,0x1a8741a541a5172a,0xbe5ae8d59cd6d6ec,0x4040c0e578be5a,0x2000280028008081,0xd16001062500bd00,0x4abd000049a20000,0x9644d16000000218])
def zbS : Nat := 0xfcfcfcfcfcfcfcfc
abbrev zcc : Nat := gZ &&& zbS
abbrev zcz : List Nat := [0xa8a8a8a8a8a8a8a8,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfc00fc00fc00fc00,0xfcfc0000fcfc0000,0xfcfcfcfc00000000]
def zpk : Nat × List Nat × Nat × Nat := (zbS,zcz,10,zcc)
def zcP : List (Nat × List Nat × Nat × Nat) := [zdr,zcD,zcI,zrD,zdM,zhR]
def zic : Option ({rows : List Nat // rows.length = 24}) := some ⟨[3,6,10,13,21,28,37,44,50,52,3,6,5,12,18,20,34,36,5,12,18,20,34,36],rfl⟩
def zsz := uW zcz [1538,265220,527362,791554,1059333,1329669]
def zva (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 4 (bI j 2 (bI j 1 (cB [0x128c2b000d0001,0x504140050014005,0x7805a21680581160,0x17805e01]) (cB [0xa0190c64019005e3,0xc6e11b046c01a846,0x18486021807e41c1,0x22048802])) (bI j 3 (cB [0xe02b80a4526948a8,0x4b012b84ae02b80a,0xc002e8cb432c8,0x3004c003]) (cB [0x6331a0c603104c21,0x112139d8e033708d,0x6091804509140450,0x47011c04]))) (bI j 6 (bI j 5 (cB [0x447851e047051c0,0x52a14a812814a012,0x1054404f112e74b0,0x51814605]) (cB [0xa252814a05281462,0x552c53894e053814,0xb856e05b056c05a8,0x5c017005])) (bI j 7 (cB [0xe263818e05c3d700,0x19e9678192664818,0x81ba46e81b816c1,0x7085c207]) (cB [0x807509cc47285c43,0x5ecd7a09d887601d,0x818])))) 14 (i % 16)
def zrU (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 8 (bI j 4 (bI j 2 (bI j 1 (cB [0x300090080200003f,0x480cc6c02b0f809c,0xe0436480fcae0372,0xa4ce3092d80a4b1a,0x943e4a4feae937a4,0x3030e3ae]) (cB [0xeec4333b0fccac39,0x10065caf45703d10,0xc03f0300cc0a0270,0xa4cc1292d03a4b10,0x94345a4fc1c93705,0x7b0e11c])) (bI j 3 (cB [0x2ec430930fc22c39,0x1a4b122f4547bd10,0x6025423d1008c380,0x3d1010c38018c960,0x94c060ca01402444,0x20c941a]) (cB [0x26334083d1010c38,0xaa5002cf4c0a24d0,0x20240b30f02a9340,0x8d383a3420e0cd83,0x2500f3d1212c384e,0xd0ca93d]))) (bI j 6 (bI j 5 (cB [0x36f440db0e21492c,0x70363300d0061,0x204c180108520401,0xbd10643345801395,0x3141080a16b2501a,0x138c644c]) (cB [0x44008543d1050c38,0x2a4b048620118034,0x6028110ca14ac381,0x30e054028128cd04,0x92c1598805ef4417,0x16b0e058])) (bI j 7 (cB [0x62028168cd058334,0x880d854034108040,0x692c588109540401,0xc7168f441a30e06,0x31c558d005633412,0x568d004a]) (cB [0x68640578d3050328,0xb8108640240e0020,0x204f5b8138720431,0xa50e6e9428e24b17,0xc38dca53f6e94e9c,0x1e30fc74])))) (bI j 12 (bI j 10 (bI j 9 (cB [0x78c4b20310c7ec42,0x13d1180c4f5fb139,0x5250243d3c86f4b2,0x8cc0760241c18d18,0x2541f31607a33419,0x1a0cc083]) (cB [0x8ac40a2250088040,0x331008cc4c23c960,0xe0342500708ef482,0x8138a604c2900d89,0x3142b494216c382a,0x260c6496])) (bI j 11 (cB [0x9a328273d121892c,0x6a4b0a2f442824b0,0x2340270ca0a8f448,0x80ac6e02a0e8020a,0x9358724b0b004e1c,0x1fa504b4]) (cB [0xbaf442e3138b6c38,0xca500bf2502f3d38,0x200f2c8100700282,0x8c50c403fb080ccc,0x3371a8ccc3c31507,0x6b0cfc84]))) (bI j 14 (bI j 13 (cB [0x3cc3987b0e1be343,0x1bd13bec43eb30fe,0xf44081880c8f453,0xb0e0b6341088c522,0x250333d3ab6c4188,0x90021c9]) (cB [0xde0353400d08602b,0x424d22492c388cd0,0x86203abd32de935b,0x30e0d69403498de2,0x62b8a9880d494c37,0x3624b0d4])) (bI j 15 (cB [0x8802a363100dac38,0x324d4e0c4c22a504,0x6620390cc8260082,0x8c70e60103a30e22,0x342380ac2c008b9,0x3800d4d6]) (bI j 16 (cB [0xe0935b5a4d22c92c,0x6b100da3403b3d12,0x80352400ac2e008b,0xa4b0bc04d6e0104b,0x94dee2506b89358b,0x3330e2bc]) (cB [0xf1250733d10eac3c,0x3b3d20])))))) 22 (i % 16)
def zpN (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 4 (bI j 2 (bI j 1 (cB [0x300c820040101f80,0x820138261c034960,0x68261c0849602019,0x940c499820120a49,0x61c0249b824a60c1]) (cB [0x361f8261c827a210,0x134a01549a1319a1,0x21900481621827a6,0x9b1961c1a1951a01,0x13817a2191a1191])) (bI j 3 (cB [0x2004220142100e20,0x214962231022006a,0x2061c2118ca118a,0x962b3102b0142a02,0x7a22a61c2a61c2b4]) (cB [0x319a200143102120,0x817a22061c334963,0x1b731a3802137015,0x1fb70123b61c3702,0x6213762c3d19a3d6]))) (bI j 6 (bI j 5 (cB [0x77a23792a41621b7,0x4662044020447a5b,0x9817a7b792c44626,0x8ccb18a4b00e4a01,0x1a4a7a24b1944d1]) (cB [0xa01b4a7a25049650,0x4a0274a7a2540264,0x590275801b81928,0x275861c5849ad84a,0x928587a7587a2586])) (bI j 7 (cB [0x101fe1007e161c01,0x6661c817a2e17a26,0xbe901a6861f817a7,0x966c4a0694a66a31,0x1ae861c6961c6c4]) (cB [0x31997219a6862670,0x767a66861c720087,0x92878621817a2])))) 20 (i % 16)
def zjv := pageLinks zva zrU 5 13 7 6
def zjy (i : Nat) : Nat × Nat :=
  let e := zpN i
  (e &&& 127,e >>> 7)
def zpW : Nat × Nat := (znF,96)
def zvR := zac zbS 96 (zA zcz zoa zxH 96) 9 zjy
def zgU := zam zbS zcz 9 zjy
def zsf : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm4,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,3,5,4] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,3,5,4] 0 i.val))),(pm15,(fun i : Fin 64 => Fin.ofNat 64 (pA [3,1,2,0,4,5] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [3,1,2,0,4,5] 0 i.val))),(pm16,(fun i : Fin 64 => Fin.ofNat 64 (pA [3,1,2,0,5,4] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [3,1,2,0,5,4] 0 i.val)))]
def zdp := zZ zsf
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zwe : dM zbS zcc 64 zdp := zad (by decide +kernel)
def zis (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 4 (bI j 2 (bI j 1 (cB [0x400c00400238c3,0xc000084]) (cB [0x8ff000000021000,0xfc100100])) (bI j 3 0x3cc0080000080071 (cB [0x536ff240013000,0x10000000]))) (bI j 6 (bI j 5 (cB [0x9bc0000000001000,0xac000202]) (cB [0x2186fc5000ac1000,0x601])) (bI j 7 (cB [0xf3c0fc00c004b,0x400000c]) 0xfc01c0000341))) 6 (i % 16)
def zbF := zc zbS zcc zic (fun i => zt zcc (cutPick zcP (zis i))) 121 zgU zdp zjv zpW zvR
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zoX : ze zbS zcc zic (zt zcc zcP) zsz (zD 121 zgU zdp zjv 0) zcz 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zrZ : tB 0 24 zbF = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zsB : tB 24 24 zbF = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zvG : tB 48 24 zbF = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zsV : tB 72 24 zbF = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zvD : tB 96 24 zbF = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zti : tB 120 1 zbF = true := by decide +kernel
theorem zxp : tB 24 48 zbF = true := tM (start := 24) (left := 24) (right := 24) (check := zbF) zsB zvG
theorem zun : tB 0 72 zbF = true := tM (start := 0) (left := 24) (right := 48) (check := zbF) zrZ zxp
theorem zoR : tB 96 25 zbF = true := tM (start := 96) (left := 24) (right := 1) (check := zbF) zvD zti
theorem zvW : tB 72 49 zbF = true := tM (start := 72) (left := 24) (right := 25) (check := zbF) zsV zoR
theorem zmF : tB 0 121 zbF = true := tM (start := 0) (left := 72) (right := 49) (check := zbF) zun zvW
theorem zxB : tB 0 121 zbF = true := zmF
theorem zul : Known zcP := (eK (eK (eK (eK (eK (eK (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) zlZ) zfk) zvp) zbG) zbK) zcu)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zdg : Lower zbS zcz zcc 10 := by
  apply lowerDag zis _ _ _ _ zwe _ _ _ zul _ zoX zxB
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold pW; decide +kernel
  · exact cK (by decide +kernel)
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [zcP,List.mem_cons,List.not_mem_nil,or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def zeQ : Nat := 0xff00ff00ffffffff
abbrev zmm : Nat := gZ &&& zeQ
abbrev zln : List Nat := [0xaa00aa00aaaaaaaa,0xcc00cc00cccccccc,0xf000f000f0f0f0f0,0xff00ff00ff00ff00,0xff000000ffff0000,0xff00ff0000000000]
def zxQ : Nat × List Nat × Nat × Nat := (zeQ,zln,10,zmm)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zvg : Lower zeQ zln zmm 10 := zp (width := 64) pm7 zbT (by decide +kernel)
def zeI : Nat := 0xff00ffffff00ffff
abbrev zkB : Nat := gZ &&& zeI
abbrev zlu : List Nat := [0xaa00aaaaaa00aaaa,0xcc00cccccc00cccc,0xf000f0f0f000f0f0,0xff00ff00ff00ff00,0xff000000ff000000,0xff00ffff00000000]
def zvE : Nat × List Nat × Nat × Nat := (zeI,zlu,10,zkB)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zxK : Lower zeI zlu zkB 10 := zp (width := 64) pm8 zbT (by decide +kernel)
def zdB : Nat := 0xff0fff0fff0fff0f
abbrev zlB : Nat := gZ &&& zdB
abbrev zig : List Nat := [0xaa0aaa0aaa0aaa0a,0xcc0ccc0ccc0ccc0c,0xf000f000f000f000,0xff00ff00ff00ff00,0xff0f0000ff0f0000,0xff0fff0f00000000]
def znN : Nat × List Nat × Nat × Nat := (zdB,zig,10,zlB)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zsn : Lower zdB zig zlB 10 := zp (width := 64) pm25 zcE (by decide +kernel)
def zfU : Nat := 0xffccffccffccffcc
abbrev zmj : Nat := gZ &&& zfU
abbrev zhM : List Nat := [0xaa88aa88aa88aa88,0xcccccccccccccccc,0xf0c0f0c0f0c0f0c0,0xff00ff00ff00ff00,0xffcc0000ffcc0000,0xffccffcc00000000]
def zmS : Nat × List Nat × Nat × Nat := (zfU,zhM,10,zmj)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ztD : Lower zfU zhM zmj 10 := zp (width := 64) pm7 zdg (by decide +kernel)
def zgf : Nat := 0xffff00ffffff00ff
abbrev zhA : Nat := gZ &&& zgf
abbrev ziW : List Nat := [0xaaaa00aaaaaa00aa,0xcccc00cccccc00cc,0xf0f000f0f0f000f0,0xff000000ff000000,0xffff0000ffff0000,0xffff00ff00000000]
def zwg : Nat × List Nat × Nat × Nat := (zgf,ziW,10,zhA)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zvv : Lower zgf ziW zhA 10 := zp (width := 64) pm24 zbT (by decide +kernel)
def zfa : Nat := 0xffff0f0fffff0f0f
abbrev zkS : Nat := gZ &&& zfa
abbrev zlK : List Nat := [0xaaaa0a0aaaaa0a0a,0xcccc0c0ccccc0c0c,0xf0f00000f0f00000,0xff000f00ff000f00,0xffff0000ffff0000,0xffff0f0f00000000]
def zuM : Nat × List Nat × Nat × Nat := (zfa,zlK,10,zkS)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zrG : Lower zfa zlK zkS 10 := zp (width := 64) pm25 zbT (by decide +kernel)
def zfx : Nat := 0xffffaaaaffffaaaa
abbrev ziu : Nat := gZ &&& zfx
abbrev zii : List Nat := [0xaaaaaaaaaaaaaaaa,0xcccc8888cccc8888,0xf0f0a0a0f0f0a0a0,0xff00aa00ff00aa00,0xffff0000ffff0000,0xffffaaaa00000000]
def zxl : Nat × List Nat × Nat × Nat := (zfx,zii,10,ziu)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zxr : Lower zfx zii ziu 10 := zp (width := 64) pm24 zdg (by decide +kernel)
def zfT : Nat := 0xffff0000ffff0000
abbrev zlw : Nat := gZ &&& zfT
abbrev zjw : List Nat := [0xaaaa0000aaaa0000,0xcccc0000cccc0000,0xf0f00000f0f00000,0xff000000ff000000,0xffff000000000000]
def zgk : Nat × List Nat × Nat × Nat := (zfT,zjw,8,zlw)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zgV : Lower zfT zjw zlw 8 := zp (width := 64) pm23 zcu (by decide +kernel)
def pm35 : List (List (Nat × Nat) × List (Nat × Nat)) := [st35]
def pm36 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01,st24]
def znL : Nat := (cB [0x340a0d0281c0806,0x4241308044180e06,0x8160905828150285,0xc0c068241a0c0642,0x2894301c0a070181,0xb0182c1209848250,0x6032090c86031120,0x38180d048340a0d0,0x60180a06180e030,0x1c48060a0182406,0xc0a0f02038080d02,0x811090440a110603,0x50804c60110c0442,0x8058081608054081,0x6428170905c0a170,0x301b0906c201a080,0x1d02874201c02070,0x6078301d0a07418,0x94301e0a078241e,0x48270289c082602,0x82d060b40a2d020b,0x2080c4482e060b84,0x20d06033090cc203,0xd42835028d420340,0x2836090d86035120,0x39080e06036120d8,0xc0e8243a180e430])
def zrm : Nat := (cB [0x79bcffd8004609ee,0xc18836533079a768,0xc781d87781df20ef,0xfe1fc0ffce3fc79f,0x3031f81c07fe1fff,0xf8001f87ffe000f0,0xffffff003fc1ffe0,0x3ffe0000ffffe007,0xfffffff800000000])
def zqA : Nat := (cB [0x804014040020086,0x80124000080120,0x4080800100880201,0xba1545fec63ec59f,0x90116818033a1ffa,0x90000a04d1000880,0x65fabe033bc1bf60,0x2d6c0000fdd5e007,0x2661144000001004])
def zbW : Nat := 0xfffff0f0fffff0f0
abbrev zck : Nat := gZ &&& zbW
abbrev zcw : List Nat := [0xaaaaa0a0aaaaa0a0,0xccccc0c0ccccc0c0,0xf0f0f0f0f0f0f0f0,0xff00f000ff00f000,0xffff0000ffff0000,0xfffff0f000000000]
def zqQ : Nat × List Nat × Nat × Nat := (zbW,zcw,10,zck)
def zcT : List (Nat × List Nat × Nat × Nat) := [zdr,zgk,zcD,zfh,zcI,zdM]
def zkt : Option ({rows : List Nat // rows.length = 24}) := some ⟨[6,13,17,26,28,37,44,50,52,56,6,13,5,12,18,20,24,36,48,5,12,18,20,24],rfl⟩
def zwA := uW zcw [6668,265220,535570,793093,1059333,1329669]
def zqv (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 1 (cB [0x60525050503b0e01,0xbaa39998988a7a63]) 0xe9cc) 8 (i % 16)
def zxi (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 1 (cB [0xf0a92d0292c0003f,0x4542f441e9430e93,0xf4506f440403f4af,0x28492500cc4e08,0x126401ac4c903281]) (cB [0x16c38146201892c,0x4492328120281494,0x92c96634163341cf,0x12504cf441a93c0c,0x1cc482])) 20 (i % 16)
def zpJ (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 1 (cB [0x20807e24960407e0,0x589c649685e8a27a,0x40a32024050849f8,0xe62621258961c28c,0x4a185e88]) 0x24a10) 18 (i % 16)
def zhN := pageLinks zqv zxi 3 13 5 4
def zkN (i : Nat) : Nat × Nat :=
  let e := zpJ i
  (e &&& 31,e >>> 5)
def ztj : Nat × Nat := (znL,96)
def zpF := zac zbW 96 (zA zcw zrm zqA 96) 9 zkN
def zih := zam zbW zcw 9 zkN
def zsb : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm35,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,5,4,3] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,5,4,3] 0 i.val))),(pm36,(fun i : Fin 64 => Fin.ofNat 64 (pA [1,0,4,3,2,5] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [1,0,4,3,2,5] 0 i.val)))]
def zfd := zZ zsb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zuA : dM zbW zck 64 zfd := zad (by decide +kernel)
def zkH (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 1 (cB [0x1f7fc0fc03c0bcf,0xfc07c000]) 0x0) 6 (i % 16)
def zle := zc zbW zck zkt (fun i => zt zck (cutPick zcT (zkH i))) 17 zih zfd zhN ztj zpF
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zux : ze zbW zck zkt (zt zck zcT) zwA (zD 17 zih zfd zhN 0) zcw 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zpw : tB 0 17 zle = true := by decide +kernel
theorem zxf : tB 0 17 zle = true := zpw
theorem zue : Known zcT := (eK (eK (eK (eK (eK (eK (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) zfk) zbG) zex) zbK) zgV) zcu)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zcS : Lower zbW zcw zck 10 := by
  apply lowerDag zkH _ _ _ _ zuA _ _ _ zue _ zux zxf
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold pW; decide +kernel
  · exact cK (by decide +kernel)
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [zcT,List.mem_cons,List.not_mem_nil,or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def zeY : Nat := 0xffffff00ffffff00
abbrev zjx : Nat := gZ &&& zeY
abbrev zlO : List Nat := [0xaaaaaa00aaaaaa00,0xcccccc00cccccc00,0xf0f0f000f0f0f000,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffff0000000000]
def zxF : Nat × List Nat × Nat × Nat := (zeY,zlO,10,zjx)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zqM : Lower zeY zlO zjx 10 := zp (width := 64) pm7 zcS (by decide +kernel)
def zfX : Nat := 0xffffffff0000ffff
abbrev zjC : Nat := gZ &&& zfX
abbrev zip : List Nat := [0xaaaaaaaa0000aaaa,0xcccccccc0000cccc,0xf0f0f0f00000f0f0,0xff00ff000000ff00,0xffff000000000000,0xffffffff00000000]
def zpB : Nat × List Nat × Nat × Nat := (zfX,zip,10,zjC)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zwI : Lower zfX zip zjC 10 := zp (width := 64) pm4 zcE (by decide +kernel)
def zeJ : Nat := 0xffffffff00ff00ff
abbrev zlE : Nat := gZ &&& zeJ
abbrev zgW : List Nat := [0xaaaaaaaa00aa00aa,0xcccccccc00cc00cc,0xf0f0f0f000f000f0,0xff00ff0000000000,0xffff000000ff0000,0xffffffff00000000]
def zpb : Nat × List Nat × Nat × Nat := (zeJ,zgW,10,zlE)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zqh : Lower zeJ zgW zlE 10 := zp (width := 64) pm29 zbT (by decide +kernel)
def zdH : Nat := 0xffffffff0f0f0f0f
abbrev zkO : Nat := gZ &&& zdH
abbrev zje : List Nat := [0xaaaaaaaa0a0a0a0a,0xcccccccc0c0c0c0c,0xf0f0f0f000000000,0xff00ff000f000f00,0xffff00000f0f0000,0xffffffff00000000]
def zum : Nat × List Nat × Nat × Nat := (zdH,zje,10,zkO)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ztV : Lower zdH zje zkO 10 := zp (width := 64) pm30 zbT (by decide +kernel)
def zdy : Nat := 0xffffffffaaaaaaaa
abbrev zhE : Nat := gZ &&& zdy
abbrev zjM : List Nat := [0xaaaaaaaaaaaaaaaa,0xcccccccc88888888,0xf0f0f0f0a0a0a0a0,0xff00ff00aa00aa00,0xffff0000aaaa0000,0xffffffff00000000]
def zvs : Nat × List Nat × Nat × Nat := (zdy,zjM,10,zhE)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zrb : Lower zdy zjM zhE 10 := zp (width := 64) pm29 zdg (by decide +kernel)
def zgd : Nat := 0xfffffffff0f0f0f0
abbrev ziL : Nat := gZ &&& zgd
abbrev zjW : List Nat := [0xaaaaaaaaa0a0a0a0,0xccccccccc0c0c0c0,0xf0f0f0f0f0f0f0f0,0xff00ff00f000f000,0xffff0000f0f00000,0xffffffff00000000]
def zuI : Nat × List Nat × Nat × Nat := (zgd,zjW,10,ziL)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zsu : Lower zgd zjW ziL 10 := zp (width := 64) pm4 zcS (by decide +kernel)
def zgb : Nat := 0xffffffffff00ff00
abbrev zmf : Nat := gZ &&& zgb
abbrev zjB : List Nat := [0xaaaaaaaaaa00aa00,0xcccccccccc00cc00,0xf0f0f0f0f000f000,0xff00ff00ff00ff00,0xffff0000ff000000,0xffffffff00000000]
def zxc : Nat × List Nat × Nat × Nat := (zgb,zjB,10,zmf)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zsv : Lower zgb zjB zmf 10 := zp (width := 64) pm8 zcS (by decide +kernel)
def zeN : Nat := 0xffff0000ffff
abbrev zgS : Nat := gZ &&& zeN
abbrev zja : List Nat := [0xaaaa0000aaaa,0xcccc0000cccc,0xf0f00000f0f0,0xff000000ff00,0xffff00000000]
def zxk : Nat × List Nat × Nat × Nat := (zeN,zja,9,zgS)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zwQ : Lower zeN zja zgS 9 := zp (width := 64) pm4 zbN (by decide +kernel)
def zfj : Nat := 0xff00ff00ff00ff
abbrev ziS : Nat := gZ &&& zfj
abbrev zlm : List Nat := [0xaa00aa00aa00aa,0xcc00cc00cc00cc,0xf000f000f000f0,0xff000000ff0000,0xff00ff00000000]
def zpx : Nat × List Nat × Nat × Nat := (zfj,zlm,9,ziS)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zsM : Lower zfj zlm ziS 9 := zp (width := 64) pm24 zbN (by decide +kernel)
def zed : Nat := 0xf0f0f0f0f0f0f0f
abbrev zlY : Nat := gZ &&& zed
abbrev ziH : List Nat := [0xa0a0a0a0a0a0a0a,0xc0c0c0c0c0c0c0c,0xf000f000f000f00,0xf0f00000f0f0000,0xf0f0f0f00000000]
def zoH : Nat × List Nat × Nat × Nat := (zed,ziH,9,zlY)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zww : Lower zed ziH zlY 9 := zp (width := 64) pm25 zbN (by decide +kernel)
def zfB : Nat := 0xf000f000f000f
abbrev zjY : Nat := gZ &&& zfB
abbrev zjQ : List Nat := [0xa000a000a000a,0xc000c000c000c,0xf0000000f0000,0xf000f00000000]
def ziK : Nat × List Nat × Nat × Nat := (zfB,zjQ,6,zjY)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zji : Lower zfB zjQ zjY 6 := zp (width := 64) pm24 zeE (by decide +kernel)
def zY : Nat := (cB [0x38180d0100c0203,0x241308044021106,0x20d0900c00030607,0x100044180f010380,0x804c04130084c241,0x78181e06074201c0,0xe000342003090,0x110103c020f09038,0x9070001c0004c04,0x78041e08074021d,0x418030907c181f08,0xe00838200d0103,0xc06044240f0003c2,0x9074001d01070021,0x7c041f0087c001e0,0x18130803c240d080,0x7c021e01074])
def zaJ : Nat := (cB [0xbbfb39f33ccbf777,0x8cdbc1e7c2f739b4,0xf0effdfbfcfbc1c,0xf3fe03ff03fe])
def zar : Nat := (cB [0x2408420104008411,0x8c25290a49a214a4,0x2601002050001810,0xe2152a82664])
def zE : Nat := 0xf00ff00f
abbrev zaA : Nat := gZ &&& zE
abbrev zaT : List Nat := [0xa00aa00a,0xc00cc00c,0xf000f000,0xf00f0000]
def zbe : Nat × List Nat × Nat × Nat := (zE,zaT,5,zaA)
def zaz : List (Nat × List Nat × Nat × Nat) := []
def zbs : Option ({rows : List Nat // rows.length = 24}) := some ⟨[3,13,14,17,28,3,13,14,17,28,3,13,1,12,18,1,12,18,1,12,18,1,12,18],rfl⟩
def zst := uW zaT [1538,263681,530945,795137]
def zP (i : Nat) : Nat := uP 0x119 3 i
def zai (i : Nat) : Nat := uP 0x2328000f 16 i
def zaG (i : Nat) : Nat := uP 0x650803c 15 i
def zbl := pageLinks zP zai 1 13 2 2
def zaN (i : Nat) : Nat × Nat :=
  let e := zaG i
  (e &&& 3,e >>> 2)
def zaX : Nat × Nat := (zY,60)
def zof := zac zE 60 (zA zaT zaJ zar 60) 4 zaN
def zaO := zam zE zaT 4 zaN
def zw : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def zaS := zZ zw
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zaF : dM zE zaA 64 zaS := zad (by decide +kernel)
def zav (i : Nat) : Nat :=
  let j := i / 16
  uP 0x0 1 (i % 16)
def zz := zc zE zaA zbs (fun i => zt zaA (cutPick zaz (zav i))) 2 zaO zaS zbl zaX zof
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zbc : ze zE zaA zbs (zt zaA zaz) zst (zD 2 zaO zaS zbl 0) zaT 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zae : tB 0 2 zz = true := by decide +kernel
theorem zay : tB 0 2 zz = true := zae
theorem zau : Known zaz := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zax : Lower zE zaT zaA 5 := by
  apply lowerDag zav _ _ _ _ zaF _ _ _ zau _ zbc zay
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold pW; decide +kernel
  · exact cK (by decide +kernel)
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [zaz,List.mem_cons,List.not_mem_nil,or_false]
    intro b h
    exact False.elim h
def zeS : Nat := 0xf00f0000f00f
abbrev zhC : Nat := gZ &&& zeS
abbrev zkJ : List Nat := [0xa00a0000a00a,0xc00c0000c00c,0xf0000000f000,0xf00f00000000]
def zuO : Nat × List Nat × Nat × Nat := (zeS,zkJ,5,zhC)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zwU : Lower zeS zkJ zhC 5 := zp (width := 64) pm4 zax (by decide +kernel)
def st14 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xcccc3333cccc3333,0),(0xcccc0000cccc,14)],[(0x3333000033330000,14)])
def pm37 : List (List (Nat × Nat) × List (Nat × Nat)) := [st15,st14]
def zdl : Nat := 0x3003300330033003
abbrev zik : Nat := gZ &&& zdl
abbrev zjj : List Nat := [0x2002200220022002,0x3000300030003000,0x3003000030030000,0x3003300300000000]
def zwm : Nat × List Nat × Nat × Nat := (zdl,zjj,5,zik)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zmW : Lower zdl zjj zik 5 := zp (width := 64) pm37 zax (by decide +kernel)
def pm38 : List (List (Nat × Nat) × List (Nat × Nat)) := [st14]
def pm39 : List (List (Nat × Nat) × List (Nat × Nat)) := [st14,st15]
def zoI : Nat := (cB [0x38180d0100c0203,0x241308044021106,0x4231008402210607,0x2090c86031060b04,0x900c0003180c8443,0x3c040e0083444030,0x6011090440011060,0x1c0804c04130084c,0x9078181e0607420,0x88c6021110840021,0x4402c1008c042300,0x231110b8182e060b,0x2010c84031080c40,0x10cc2433100c8203,0xc603c060f060331,0xe000344003080,0xf0083c440e09038,0x4c40110104404,0x70001c1804c4413,0x8201d00874601c09,0x41f0607c201e0107,0x30008c2021010842,0x10b0002c1808c242,0xb8402d008b4602c1,0x442f060bc402e010,0x32110c42431000c4,0x80cc0433008cc00])
def zgO : Nat := (cB [0xf8e71cbf2fef1777,0xce37e44bef98fe63,0xf1e0e7839f67e338,0x1f9803c0f038088c,0xffc0f0f001ff07fc,0xfe0007ffe01ffc00,0x1fffff0000ff00,0xfffff800])
def ztw : Nat := (cB [0x800040802080111,0x8496644220080020,0x4d224c8936032212,0x801806020088c,0x9982b06000800200,0x8404d55a02354804,0x445692660104d600,0x9568013])
def zbX : Nat := 0xf00ff00ff00ff00f
abbrev zcf : Nat := gZ &&& zbX
abbrev zcx : List Nat := [0xa00aa00aa00aa00a,0xc00cc00cc00cc00c,0xf000f000f000f000,0xf00f0000f00f0000,0xf00ff00f00000000]
def zuF : Nat × List Nat × Nat × Nat := (zbX,zcx,9,zcf)
def zdf : List (Nat × List Nat × Nat × Nat) := [ziK,zej,zbe,zuO,zwm]
def zhP : Option ({rows : List Nat // rows.length = 24}) := some ⟨[3,13,14,17,28,33,44,50,3,13,14,17,1,12,18,34,48,1,12,18,34,48,1,12],rfl⟩
def zmr := uW zcx [1538,263681,530945,795137,1065473]
def znk (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 2 (bI j 1 (cB [0x5202618b4006a001,0xa805212901480a40,0xe00ec25cd2b19504,0x3c01]) (cB [0x7c03e01f00f42781,0xfe67c13e01f00f80,0xb01580a63520a900,0x5602])) (bI j 3 (cB [0xce0660abbd5c0ac1,0xb40d436a035019c6,0x7a1b82dc06d0b681,0x7703]) (bI j 4 (cB [0xa0840bbb5dc0ee0,0x4050ca850c282141,0xa225012809214902,0x9c04]) (cB [0x3d39d0ce06701380,0x1790b34d906c43])))) 13 (i % 16)
def zmU (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 6 (bI j 3 (bI j 1 (cB [0x5804c0100400001f,0x1ba1602b06003e0,0x1f0b462a108c518b,0x6218cac371938623,0x473101863372dc66,0x6c4c6e9898ac]) (bI j 2 (cB [0xba4cd2d496a4292c,0x61cb42c3890d26f1,0x1f01462a010c51ad,0x6048cac0719380c3,0xa31011233721c66,0x618c6e8318ac]) (cB [0x3a4cd05496a0492c,0x61cb04c3882526f0,0x3801125801988185,0x40c900831a108c,0x8361c20692c00cc4,0x386280600a9]))) (bI j 4 (cB [0x80d081019b01e32a,0x31b02662a048c404,0x380552584a190814,0x84b3d101762182cc,0x1162101a01c03403,0x30024088d30]) (bI j 5 (cB [0xc8c518c021218036,0x19982632906863a0,0x4326c67e0f8cdc1b,0x8cd19091a31b13e3,0x934a122693608125,0x86d87e8cb0e1]) (cB [0x68041997a243ec43,0x32003a3280700200,0x3308804e0f0cc01e,0x60c8c7c0218a1440,0x2431032c33745865,0x298c6e1318ac])))) (bI j 9 (bI j 7 (cB [0x524cc2949684e92c,0x61c94ec380b126e1,0x2c00cc40118100a9,0x8021880a561c04a9,0x2b620050c3809525,0x1462815a4c0]) (bI j 8 (cB [0x798d82e31501c31d,0x61c06092c2bcc841,0x11018010d4bd1129,0x80980a41a00e81e0,0xb21a10643360b862,0xd526c1a24b0]) (cB [0xb310d2661c16a942,0x1a6066c42699e881,0x2b0e002203802033,0x81e0d083a1950360,0x424960826420f4c6,0x6a9e88a0b108]))) (bI j 11 (bI j 10 (cB [0xe80743919a03802a,0x88100080ec6680,0x200ec63c0f007c39,0x2024d83f49607c6,0x3e49a0809406ad87,0x40022048020]) (cB [0xa00d51001483e01f,0x18f05e31465c0860,0x2030467c1e8c9032,0x61a98d5323148886,0x4149f25e92c6d8c8,0x11988422b0e2])) (bI j 12 (cB [0xf98c03e312358f44,0x1aa220290440221,0x30100648198c7991,0xd998d5333149803,0x1518f81431490126,0x65466e8a8cac]) (cB [0x1189c30310848620,0x31b984633110c562,0x334c125a9224b0c4,0x2d230e24449bc849,0x6c187]))))) 23 (i % 16)
def zxe (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 2 (bI j 1 (cB [0x318a020040100f80,0x8218a82496033100,0x58231a081938218f,0x150c009813100219,0x1950c18a0c00e0d0]) (cB [0xc3100c6211119b0c,0xc4960c31b0c3150,0xa1900f816218c61c,0x81c1999918e9918,0x19b993201c1941c0])) (bI j 3 (cB [0x3013a218a0149619,0xa249625310220202,0x6a261c2849622315,0x9ba26202b499a249,0x31b2e3152e18a814]) (bI j 4 (cB [0x319b3218f814962e,0xb249b32496326213,0xa39008b819381621,0xa13819a3b1953819,0x4963e3103e31a381]) (cB [0x1496383213849b3e,0x4461c44310441958,0x31001621])))) 20 (i % 16)
def ziD := pageLinks znk zmU 5 13 7 6
def zio (i : Nat) : Nat × Nat :=
  let e := zxe i
  (e &&& 127,e >>> 7)
def zvF : Nat × Nat := (zoI,96)
def zwk := zac zbX 96 (zA zcx zgO ztw 96) 8 zio
def ziQ := zam zbX zcx 8 zio
def zuV : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm4,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,3,5,4] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,3,5,4] 0 i.val))),(pm38,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,4,2,3,1,5] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,4,2,3,1,5] 0 i.val))),(pm39,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,5,2,3,1,4] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,4,2,3,5,1] 0 i.val))),(pm37,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,4,2,3,5,1] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,5,2,3,1,4] 0 i.val)))]
def zeC := zZ zuV
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zvo : dM zbX zcf 64 zeC := zad (by decide +kernel)
def zlN (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 2 (bI j 1 (cB [0x1784000000000463,0x802]) 0x83f000006000a) (bI j 3 (cB [0x800100261,0x3e]) (bI j 4 (cB [0xf8000025e0,0x18]) 0x18000f8084))) 5 (i % 16)
def zbQ := zc zbX zcf zhP (fun i => zt zcf (cutPick zdf (zlN i))) 72 ziQ zeC ziD zvF zwk
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ztt : ze zbX zcf zhP (zt zcf zdf) zmr (zD 72 ziQ zeC ziD 0) zcx 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zwj : tB 0 24 zbQ = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zqW : tB 24 24 zbQ = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zxR : tB 48 24 zbQ = true := by decide +kernel
theorem zqw : tB 24 48 zbQ = true := tM (start := 24) (left := 24) (right := 24) (check := zbQ) zqW zxR
theorem zqU : tB 0 72 zbQ = true := tM (start := 0) (left := 24) (right := 48) (check := zbQ) zwj zqw
theorem zqz : tB 0 72 zbQ = true := zqU
theorem zxT : Known zdf := (eK (eK (eK (eK (eK (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) zmW) zwU) zax) zeH) zji)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zly : Lower zbX zcx zcf 9 := by
  apply lowerDag zlN _ _ _ _ zvo _ _ _ zxT _ ztt zqz
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold pW; decide +kernel
  · exact cK (by decide +kernel)
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [zdf,List.mem_cons,List.not_mem_nil,or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def zge : Nat := 0xffff00000000ffff
abbrev zjS : Nat := gZ &&& zge
abbrev ziP : List Nat := [0xaaaa00000000aaaa,0xcccc00000000cccc,0xf0f000000000f0f0,0xff0000000000ff00,0xffff000000000000]
def zqy : Nat × List Nat × Nat × Nat := (zge,ziP,9,zjS)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zqj : Lower zge ziP zjS 9 := zp (width := 64) pm24 zly (by decide +kernel)
def zoi : Nat := (cB [0x81c04060100c0203,0x40a0d0482c040a02,0xa150904c02110483,0x1090681219090580,0x10980a251108c022,0xc82432110a812291,0x24030480c0a03110,0x6090180a061100c,0x482804070081c44,0x2c020b11028240a,0xc0a0f01038020d01,0x411048440a110483,0x60085404130084c2,0x86424170285c041,0x74241b0486c041a0,0xa2109078121d028,0x230088c442104884,0x289c04260089404,0x8ac042a008a44427,0x8122d028b4442b04,0x433010c80231110b,0x6090d80a35110cc2,0x10e8243a048e4443,0x1c24070481c02061,0x240b0282c020a110,0xe048380a0e1102c,0x103c020f1103824])
def zoN : Nat := (cB [0xbf7bbfdc63c5d7eb,0xfffaaa3fc3b89d7b,0xffff6e9dd89dd8ef,0xe0e1e0f07c030ccc,0x800c30f0fc3c70e1,0xffc380fe00fe00ff,0xffff0000303f00,0x3fc0000003ff00,0x3ffffff000000])
def zrn : Nat := (cB [0xab6aabd4a4c555e9,0x5b3aaa164ccc916a,0xb3336e955495542b,0x8120814004410448,0x808410a004801020,0x808804802480280,0x91040109102a00,0x122a800011112400,0x2222489104000002])
def zbZ : Nat := 0xeeeeeeeeeeeeeeee
abbrev zcm : Nat := gZ &&& zbZ
abbrev zcy : List Nat := [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xe0e0e0e0e0e0e0e0,0xee00ee00ee00ee00,0xeeee0000eeee0000,0xeeeeeeee00000000]
def zru : Nat × List Nat × Nat × Nat := (zbZ,zcy,9,zcm)
def zcO : List (Nat × List Nat × Nat × Nat) := []
def zlq : Option ({rows : List Nat // rows.length = 24}) := some ⟨[3,6,10,13,17,33,50,3,6,10,13,17,5,9,18,34,5,9,18,34,5,9,18,34],rfl⟩
def zwt := uW zcy [1538,263681,527362,791554,1057281,1327617]
def zws (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 3 (bI j 1 (cB [0x803a00c0a01bc001,0x4e803a00e803a00e,0xb00f4e3d00ec23a0,0x4e012c34]) (bI j 2 (cB [0xc053014c04e15380,0x55825601580530d4,0xe017415d01644580,0x6d0978f5]) (cB [0x427101bc26f01bc0,0x1d007401cc17301c,0xa01e417901e01741,0x7d05e837]))) (bI j 4 (cB [0xc27f01fc07e05f80,0x21c083120c08109f,0xb06281870e1c0870,0x980630c8]) (bI j 5 (cB [0xc1990a6409902640,0x68c3a3027079c026,0xf0aac4aa069c3a60,0xb502c44a]) 0xb50ad40))) 14 (i % 16)
def zpl (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 6 (bI j 3 (bI j 1 (cB [0x400240100400003f,0x7c1600e02c01a0,0x1f07403c0d806c19,0x68e80a91b0138660,0x3a01b86c0334cc05,0x2e80865b00fc]) (bI j 2 (cB [0xb0c6e0818ac02314,0x195e6c3278e863f1,0x3787466d0d8ccf3a,0x74e8d0a9b19fc663,0x4231087a620acc68,0x130c5622989c]) (cB [0x698fc5031b89a633,0x496a7a92c340c866,0x3f54126ea6a4cd42,0x31eb0e1d04a1b9a9,0x4c621c8ac3f90987,0xb09e8b5ebd12]))) (bI j 4 (cB [0x180a80300f004008,0x1a100a3360106288,0x3841925803188085,0x8048c60877a200ec,0xc00411434002866,0x434052068074]) (bI j 5 (cB [0xb00d81401a820034,0x211280412400800,0x2c05cc40048c5096,0x4c3d101861c22e9,0x8f02001e03403805,0x44628050020]) (cB [0x9b0e012496222620,0x2021e02803c0380,0x40244680088cd015,0x8d00d01a0141263,0x1c19453404c86808,0x78023028020])))) (bI j 9 (bI j 7 (cB [0x280d82300d042019,0x19304e3142940841,0x202b8684170cd828,0x18a4b03031505e6,0x1f18c164f440c987,0x7c038101890]) (bI j 8 (cB [0x201002401a044028,0x19a0520100980505,0x1c0b4c50558d002b,0x1500402c18e0540,0x260141583340b065,0x70030168c60]) (cB [0xa8d003519a068324,0x1a0700280dc0385,0x3c8786681c813138,0x90f8cd03c7a40763,0x3e00680400888066,0x5c632030c50]))) (bI j 10 (cB [0x398813119543031a,0x4965646428c8c6d0,0x28305e8820b0e040,0x138ca04300607e0,0x2801408c01c11005,0x11c6389400d0]) (bI j 11 (cB [0x5a4d0c9326092640,0x1942520280a40202,0x280ac03815007048,0x1600704a3142560,0x4a31a09031c0b405,0xc0068651900]) (cB [0x70c704e00e096624,0xe49e64c13cc692,0x1170cd02e]))))) 23 (i % 16)
def zwy (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 3 (bI j 1 (cB [0x2004020040101f80,0x219b0218a0200f0,0xc090048161c02310,0x40c0068119a0a18,0x1a0e0140e00e8c0]) (bI j 2 (cB [0x14961118a1101a0c,0xc0201501a8c61c1,0x78161c0c3100c01b,0x941c00d810141a00,0x18c1f0089e00f011]) (cB [0xe0142200c9e3121f,0x2601b1e01a2400d1,0x8291931e18a1e014,0x8e2c19a2900e2a00,0x3101e19b1e314291]))) (bI j 4 (cB [0x161c1e4961e3151e,0x8119a351923400f8,0x6370143700e37019,0xa43b19e3b01b8102,0x143f006be310017]) (bI j 5 (cB [0x33108161c3e4963e,0x4631381014440064,0x461944818e4600e,0x158149a463144a32,0x31a4e00e4e319813]) 0x31b81))) 20 (i % 16)
def zjL := pageLinks zws zpl 6 13 7 7
def zmk (i : Nat) : Nat × Nat :=
  let e := zwy i
  (e &&& 127,e >>> 7)
def zub : Nat × Nat := (zoi,96)
def zxa := zac zbZ 96 (zA zcy zoN zrn 96) 8 zmk
def zkR := zam zbZ zcy 8 zmk
def zms : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm4,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,3,5,4] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,3,5,4] 0 i.val))),(pm7,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,3,2,4,5] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,3,2,4,5] 0 i.val))),(pm8,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,3,2,5,4] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,3,2,5,4] 0 i.val))),(pm24,(fun i : Fin 64 => Fin.ofNat 64 (pA [1,0,4,5,2,3] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [1,0,4,5,2,3] 0 i.val))),(pm29,(fun i : Fin 64 => Fin.ofNat 64 (pA [1,0,5,4,2,3] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [1,0,4,5,3,2] 0 i.val))),(pm25,(fun i : Fin 64 => Fin.ofNat 64 (pA [1,0,4,5,3,2] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [1,0,5,4,2,3] 0 i.val)))]
def zfZ := zZ zms
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zvk : dM zbZ zcm 64 zfZ := zad (by decide +kernel)
def zlx (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 3 (bI j 1 0x0 (bI j 2 0x0 0x0)) (bI j 4 0x0 (bI j 5 0x0 0x0))) 1 (i % 16)
def zbM := zc zbZ zcm zlq (fun i => zt zcm (cutPick zcO (zlx i))) 81 zkR zfZ zjL zub zxa
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zwG : ze zbZ zcm zlq (zt zcm zcO) zwt (zD 81 zkR zfZ zjL 0) zcy 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zuC : tB 0 24 zbM = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zrd : tB 24 24 zbM = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zsI : tB 48 24 zbM = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zrj : tB 72 9 zbM = true := by decide +kernel
theorem zqP : tB 0 48 zbM = true := tM (start := 0) (left := 24) (right := 24) (check := zbM) zuC zrd
theorem zqs : tB 48 33 zbM = true := tM (start := 48) (left := 24) (right := 9) (check := zbM) zsI zrj
theorem zqr : tB 0 81 zbM = true := tM (start := 0) (left := 48) (right := 33) (check := zbM) zqP zqs
theorem zqG : tB 0 81 zbM = true := zqr
theorem zsq : Known zcO := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zpf : Lower zbZ zcy zcm 9 := by
  apply lowerDag zlx _ _ _ _ zvk _ _ _ zsq _ zwG zqG
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold pW; decide +kernel
  · exact cK (by decide +kernel)
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [zcO,List.mem_cons,List.not_mem_nil,or_false]
    intro b h
    exact False.elim h
def zdX : Nat := 0xfafafafafafafafa
abbrev zgA : Nat := gZ &&& zdX
abbrev zdK : List Nat := [0xaaaaaaaaaaaaaaaa,0xc8c8c8c8c8c8c8c8,0xf0f0f0f0f0f0f0f0,0xfa00fa00fa00fa00,0xfafa0000fafa0000,0xfafafafa00000000]
def zmA : Nat × List Nat × Nat × Nat := (zdX,zdK,9,zgA)
def zmI := uW zdK [6668,263681,530953,793093,1057281,1327617]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zcU : Lower zdX zdK zgA 9 := by
  apply eL (witnesses := zmI) (cut := zbL)
  · unfold pW; decide +kernel
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold pW; decide +kernel
  · exact uC (old := zbP) (by decide +kernel)
  · exact zbK
  · decide +kernel
def zfi : Nat := 0xffaaffaaffaaffaa
abbrev zjl : Nat := gZ &&& zfi
abbrev zmp : List Nat := [0xaaaaaaaaaaaaaaaa,0xcc88cc88cc88cc88,0xf0a0f0a0f0a0f0a0,0xff00ff00ff00ff00,0xffaa0000ffaa0000,0xffaaffaa00000000]
def zqe : Nat × List Nat × Nat × Nat := (zfi,zmp,9,zjl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zpt : Lower zfi zmp zjl 9 := zp (width := 64) pm7 zcU (by decide +kernel)
def zdm : Nat := 0xfff0fff0fff0fff0
abbrev zlr : Nat := gZ &&& zdm
abbrev zdN : List Nat := [0xaaa0aaa0aaa0aaa0,0xccc0ccc0ccc0ccc0,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xfff00000fff00000,0xfff0fff000000000]
def zwq : Nat × List Nat × Nat × Nat := (zdm,zdN,9,zlr)
def zpL := uW zdN [6668,265220,530953,793093,1059333,1329669]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zkT : Lower zdm zdN zlr 9 := by
  apply eL (witnesses := zpL) (cut := zbL)
  · unfold pW; decide +kernel
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold pW; decide +kernel
  · exact uC (old := zbP) (by decide +kernel)
  · exact zbK
  · decide +kernel
def zfw : Nat := 0xffffccccffffcccc
abbrev zmn : Nat := gZ &&& zfw
abbrev zjt : List Nat := [0xaaaa8888aaaa8888,0xcccccccccccccccc,0xf0f0c0c0f0f0c0c0,0xff00cc00ff00cc00,0xffff0000ffff0000,0xffffcccc00000000]
def zre : Nat × List Nat × Nat × Nat := (zfw,zjt,9,zmn)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zxO : Lower zfw zjt zmn 9 := zp (width := 64) pm24 zcU (by decide +kernel)
def zdi : Nat := 0xffffffffcccccccc
abbrev zgE : Nat := gZ &&& zdi
abbrev zkh : List Nat := [0xaaaaaaaa88888888,0xcccccccccccccccc,0xf0f0f0f0c0c0c0c0,0xff00ff00cc00cc00,0xffff0000cccc0000,0xffffffff00000000]
def zwO : Nat × List Nat × Nat × Nat := (zdi,zkh,9,zgE)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zuy : Lower zdi zkh zgE 9 := zp (width := 64) pm29 zcU (by decide +kernel)
def zfJ : Nat := 0xffffffffffff0000
abbrev zlU : Nat := gZ &&& zfJ
abbrev zgQ : List Nat := [0xaaaaaaaaaaaa0000,0xcccccccccccc0000,0xf0f0f0f0f0f00000,0xff00ff00ff000000,0xffff0000ffff0000,0xffffffff00000000]
def zxX : Nat × List Nat × Nat × Nat := (zfJ,zgQ,9,zlU)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem znP : Lower zfJ zgQ zlU 9 := zp (width := 64) pm24 zkT (by decide +kernel)
def zdC : Nat := 0xff00ff00ff00ff00
abbrev zkp : Nat := gZ &&& zdC
abbrev ziv : List Nat := [0xaa00aa00aa00aa00,0xcc00cc00cc00cc00,0xf000f000f000f000,0xff000000ff000000,0xff00ff0000000000]
def zpd : Nat × List Nat × Nat × Nat := (zdC,ziv,8,zkp)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zqY : Lower zdC ziv zkp 8 := zp (width := 64) pm7 zcu (by decide +kernel)
def zeV : Nat := 0xffffffff00000000
abbrev zir : Nat := gZ &&& zeV
abbrev zky : List Nat := [0xaaaaaaaa00000000,0xcccccccc00000000,0xf0f0f0f000000000,0xff00ff0000000000,0xffff000000000000]
def znc : Nat × List Nat × Nat × Nat := (zeV,zky,8,zir)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zvH : Lower zeV zky zir 8 := zp (width := 64) pm27 zcu (by decide +kernel)
def st13 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xcc33cc33cc33cc33,0),(0xcc00cc00cc00cc,6)],[(0x3300330033003300,6)])
def st12 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xc3c3c3c3c3c3c3c3,0),(0xc0c0c0c0c0c0c0c,2)],[(0x3030303030303030,2)])
def pm40 : List (List (Nat × Nat) × List (Nat × Nat)) := [st13,st12]
def zdz : Nat := 0xa050a050a050a05
abbrev zkE : Nat := gZ &&& zdz
abbrev ziV : List Nat := [0xa000a000a000a00,0x804080408040804,0xa0500000a050000,0xa050a0500000000]
def zqV : Nat × List Nat × Nat × Nat := (zdz,ziV,6,zkE)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zpH : Lower zdz ziV zkE 6 := zp (width := 64) pm40 zbU (by decide +kernel)
def zdW : Nat := 0x4444111144441111
abbrev ziG : Nat := gZ &&& zdW
abbrev zkv : List Nat := [0x4444000044440000,0x4040101040401010,0x4400110044001100,0x4444111100000000]
def zxb : Nat × List Nat × Nat × Nat := (zdW,zkv,6,ziG)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zoQ : Lower zdW zkv ziG 6 := zp (width := 64) pm23 zbU (by decide +kernel)
def zfQ : Nat := 0xff000000ff00
abbrev zme : Nat := gZ &&& zfQ
abbrev zlt : List Nat := [0xaa000000aa00,0xcc000000cc00,0xf0000000f000,0xff0000000000]
def zwd : Nat × List Nat × Nat × Nat := (zfQ,zlt,5,zme)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zsg : Lower zfQ zlt zme 5 := zp (width := 64) pm8 zbG (by decide +kernel)
def zgc : Nat := 0xffff00000000
abbrev zhh : Nat := gZ &&& zgc
abbrev zhz : List Nat := [0xaaaa00000000,0xcccc00000000,0xf0f000000000,0xff0000000000]
def zxg : Nat × List Nat × Nat × Nat := (zgc,zhz,5,zhh)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zwx : Lower zgc zhz zhh 5 := zp (width := 64) pm27 zbG (by decide +kernel)
def zwX : Nat := (cB [0x834100a010280a07,0xc301a090680a1502,0xa09028000a0101,0x7080540a0f040343,0x4068041a0905c0a1,0x1c301d02874201a0,0xd080282407000,0x150403c040f0c034,0x105c30150905400,0x74101d000682017,0xc301f0907c0a1f08,0x40d0282820070401,0xf0903c000f080340,0x5c101501054300,0x7c241d0007430170,0x30070807c101f010,0x1a0405c200f09034,0x1f010740a])
def znG : Nat := (cB [0xeffffdfdff78f899,0xaef339f9c673ebf3,0x1dbe1f9f83e7c7db,0xf1ff00ffe03fc0e])
def zpm : Nat := (cB [0x1000021000085019,0x111852105220c151,0x251503112848311,0xf28d2d2c5a94cc])
def zco : Nat := 0xa5a5a5a5
abbrev zcq : Nat := gZ &&& zco
abbrev zcC : List Nat := [0xa0a0a0a0,0x84848484,0xa500a500,0xa5a50000]
def zcH : List (Nat × List Nat × Nat × Nat) := []
def zls : Option ({rows : List Nat // rows.length = 24}) := some ⟨[7,10,13,21,7,10,13,21,7,10,13,21,5,18,24,5,18,24,5,18,24,5,18,24],rfl⟩
def zpq := uW zcC [3586,265733,529410,797189]
def zxd (i : Nat) : Nat := uP 0x9 2 i
def zvU (i : Nat) : Nat := uP 0xf 15 i
def znl (i : Nat) : Nat := uP 0x1e 14 i
def zgT := pageLinks zxd zvU 1 13 1 2
def zjU (i : Nat) : Nat × Nat :=
  let e := znl i
  (e &&& 1,e >>> 1)
def zpc : Nat × Nat := (zwX,63)
def zmN := zac zco 63 (zA zcC znG zpm 63) 4 zjU
def zkr := zam zco zcC 4 zjU
def zwi : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def zfo := zZ zwi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zvt : dM zco zcq 64 zfo := zad (by decide +kernel)
def zgY (i : Nat) : Nat :=
  let j := i / 16
  uP 0x0 1 (i % 16)
def zkL := zc zco zcq zls (fun i => zt zcq (cutPick zcH (zgY i))) 1 zkr zfo zgT zpc zmN
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zoK : ze zco zcq zls (zt zcq zcH) zpq (zD 1 zkr zfo zgT 0) zcC 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem znE : tB 0 1 zkL = true := by decide +kernel
theorem znA : tB 0 1 zkL = true := znE
theorem zpU : Known zcH := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zxs : Lower zco zcC zcq 5 := by
  apply lowerDag zgY _ _ _ _ zvt _ _ _ zpU _ zoK znA
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold pW; decide +kernel
  · exact cK (by decide +kernel)
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [zcH,List.mem_cons,List.not_mem_nil,or_false]
    intro b h
    exact False.elim h
def zfP : Nat := 0xcc003300cc0033
abbrev zhl : Nat := gZ &&& zfP
abbrev zgN : List Nat := [0x88002200880022,0xcc000000cc0000,0xc0003000c00030,0xcc003300000000]
def zqX : Nat × List Nat × Nat × Nat := (zfP,zgN,5,zhl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zuh : Lower zfP zgN zhl 5 := zp (width := 64) pm24 zxs (by decide +kernel)
def pm41 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01,st23,st25,st24]
def zen : Nat := 0xff000000ff0000
abbrev zlk : Nat := gZ &&& zen
abbrev zhm : List Nat := [0xaa000000aa0000,0xcc000000cc0000,0xf0000000f00000,0xff000000000000]
def zsU : Nat × List Nat × Nat × Nat := (zen,zhm,5,zlk)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zqx : Lower zen zhm zlk 5 := zp (width := 64) pm41 zbG (by decide +kernel)
def pm42 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01,st23,st25]
def zeg : Nat := 0xff00ff00000000
abbrev zgH : Nat := gZ &&& zeg
abbrev zgB : List Nat := [0xaa00aa00000000,0xcc00cc00000000,0xf000f000000000,0xff000000000000]
def zvQ : Nat × List Nat × Nat × Nat := (zeg,zgB,5,zgH)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem znK : Lower zeg zgB zgH 5 := zp (width := 64) pm42 zbG (by decide +kernel)
def zfE : Nat := 0xf000f000f000f00
abbrev zim : Nat := gZ &&& zfE
abbrev zkk : List Nat := [0xa000a000a000a00,0xc000c000c000c00,0xf0000000f000000,0xf000f0000000000]
def zuD : Nat × List Nat × Nat × Nat := (zfE,zkk,5,zim)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zra : Lower zfE zkk zim 5 := zp (width := 64) pm26 zbG (by decide +kernel)
def pm43 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01,st25,st24]
def zeZ : Nat := 0xf0f00000f0f0000
abbrev zjm : Nat := gZ &&& zeZ
abbrev zhI : List Nat := [0xa0a00000a0a0000,0xc0c00000c0c0000,0xf0000000f000000,0xf0f000000000000]
def znU : Nat × List Nat × Nat × Nat := (zeZ,zhI,5,zjm)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zss : Lower zeZ zhI zjm 5 := zp (width := 64) pm43 zbG (by decide +kernel)
def zxw : Nat := (cB [0x1804060100c0203,0xc100a010280a0702,0x80d048340a0d0482,0x3080440211060381,0x9058281502854241,0x6830190486428160,0x281c06070301a090,0x231008402210c070,0x1109848250289444,0xa85029048a44826,0x482c060b0502a11,0x432090c86031140b,0x4120d02834180c84,0x80e050380c0e0603,0xc12030280c00031,0xa06000184403090,0x60a018240606018,0x101c02071201844,0x28120a000280807,0x8440a0c028240a06,0xb0102c020b1402,0xe04034080d008341,0x283c100e02038040,0x4400110603c120f0,0x2811090441211028,0x130084c60110c044,0x205402150804c04])
def zsW : Nat := (cB [0xc07c01067c19f793,0x906648fffffe3f01,0x380fc7fffffc0e19,0xff8070e1e3878f1c,0x3f80fe0c00ff801,0xffffe000380fe,0x3ff0003fff000,0xfc000000fff00000,0x3ffff])
def ztY : Nat := (cB [0x4118000224089391,0x9022402648660904,0x1080425094600608,0x2b08306161858d18,0x2d80ec0812a9009,0x24d24ac021180b6,0xc22db0003776000,0xd800000027800030,0x40000c030436ddd])
def zcj : Nat := 0xffffffffffffffff
abbrev zcr : Nat := gZ &&& zcj
abbrev zdd : List Nat := [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]
def zcG : List (Nat × List Nat × Nat × Nat) := [zoB,zpY,zvC,zoF,zmZ,zrz,zqH,zwv,zug,zmQ,zvw,zos,zmP,zsx,zwL,znM,ztg,zor,zol,zgx,zhi,zus,znx,zwS,zni,zxN,zrh,ztP,zqn,zrL,ztc,zoe,zty,zod,zrJ,zth,zpp,ztI,zpk,zxQ,zvE,znN,zmS,zwE,zwg,zuM,zxl,zqQ,zxF,zpB,zpb,zum,zvs,zuI,zxc,zvT,zxk,zpx,zoH,zuF,zqy,zru,zmA,zqe,zwq,zre,zwO,zxX,zdr,zpd,zgk,znc,zhB,zcD,zdw,zfh,zgI,zkK,ziK,zqV,zlT,zxb,zej,zcW,zdR,zcI,zha,ziZ,zfg,zhc,zwd,zxg,zdJ,zhq,zqX,zdM,zsU,zvQ,zdD,ziX,zuD,znU,zhR]
def zmi : Option ({rows : List Nat // rows.length = 24}) := some ⟨[3,6,10,13,17,28,33,44,50,52,56,3,5,9,12,18,20,24,34,36,40,48,5,9],rfl⟩
def zmC := uW zdd [1538,263681,527362,791554,1057281,1327617]
set_option maxRecDepth 16000 in
def znB (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 56 (bI j 28 (bI j 14 (bI j 7 (bI j 3 (bI j 1 (cB [0xcd00419000fc0001,0xbe102c9809ac01,0xc20030040c000300,0x1032000c42030840,0x32800c8]) (bI j 2 (cB [0x6080cc6033000ca1,0xe22038040dc203,0xfe003f800fe0039b,0x1040000fe103f800,0x409c100]) (cB [0x8801201047081106,0x8126304904122104,0x42304d1c130204b0,0x55041486052001,0x5580156]))) (bI j 5 (bI j 4 (cB [0x9381640058841566,0x19c006608180c05,0x9e10678019c10670,0x69001a02068001,0x69081a4]) (cB [0xb001a8206a001a80,0x1ba006e041ac606,0xbe006f801ba206e8,0x73881c0706f841,0x74801d2])) (bI j 6 (cB [0x5881d60075801d22,0xc1e000768c1da007,0xee007b801e640780,0x307c0c1ee107b801,0x7f001f6]) (cB [0x38c1fe807f041fc0,0x421c508510214008,0x32008c8023010899,0xd09088238508c8c2,0x981c246])))) (bI j 10 (bI j 8 (cB [0xc80272009c8026e2,0x274109d00272109,0x7a009e04276109d8,0x40a000280009e8c2,0xa214280]) (bI j 9 (cB [0x68029a00a6802924,0x429c10a68429a00a,0xaa10a8902a010a78,0x20ac002ac20ab002,0xad0c2b0]) (cB [0x2082c040af082ba1,0x82d020b3842cc10b,0xde00b7802d830b50,0x60b9802e220b7882,0xbc982e6]))) (bI j 12 (bI j 11 (cB [0xd0432860c0cc2fe2,0x33630cd8033600c,0x3c10cf0033c00cf0,0x10d38034c10cf9c3,0xd40034e]) (cB [0x48035200d4043500,0x8356e0d58035220d,0x8410dd9c37600dc8,0xe29438620e1803,0xe504394])) (bI j 13 (cB [0xe003b610e6b83962,0x43c000f0003b840e,0xc460f0843c200f00,0x20f5803d600f40c3,0xf6803d6]) (cB [0xaac3ea00f9883da6,0x40eb1028840050f,0x3e010e0c424a1090,0x411298440510f844,0x11f9c457]))))) (bI j 21 (bI j 17 (bI j 15 (cB [0x50049021240048c2,0x4496012504494012,0xa401290049861258,0x129844a60129044,0x12a284a8]) (bI j 16 (cB [0x2804c8112f944bc1,0x4d4c135004ca513,0x913d184f4013b1,0x5145105140144845,0x149ac51c]) (cB [0xf805764156b853cf,0x4582015f8857e015,0x8a01628058431608,0x165005940162945,0x16504594]))) (bI j 19 (bI j 18 (cB [0x90c5a21168045965,0x45b0416b085aa116,0xc8116f185ba116e0,0xd173885cc1172845,0x17b185d2]) (cB [0xe885fa017e805f81,0x46001180005fe117,0x671818060411808,0x81869061a01850c6,0x18c88622])) (bI j 20 (cB [0x28464a01910c6367,0xc65c61951064c419,0x78819c1066e119a0,0x11a70c68e71a20c6,0x1a9086a2]) (cB [0x69c6b911ac106a84,0x86ee11bb046e821b,0xfa21bd886f411bc0,0x11c59c700b1bf846,0x1c9a0724])))) (bI j 24 (bI j 22 (cB [0x82475271d30c736b,0x8776b1dd8077221d,0xb001ec007a841e33,0x11ed807b601ec0c7,0x1ee087b6]) (bI j 23 (cB [0x807be21ef047bc0,0xc7c401f0847c201f,0xce01f2887ca01f10,0x31f5887ce41f3807,0x1f8187da]) (cB [0x41480841fd287ec4,0xc81a52068081a020,0x5c9212a482b02090,0xe2253c88e321bc08,0x2338c8b2]))) (bI j 26 (bI j 25 (cB [0x6888d81236008d42,0x88e60237908de023,0x11923f288ea92398,0x25d109629250c09,0x25f0097c]) (cB [0x10098402608497c3,0x98a026280984326,0xa85262bc98a02628,0x126e009b8026c8c9,0x26e909b8])) (bI j 27 (cB [0x1009c21270809c20,0x9cc0271109c4027,0xd40275009cc42730,0x327ab49d6a275049,0x28280a04]) (cB [0x308a0c028284a0a0,0xa1602840ca10028,0x1a028680a1622858,0x128904a1c428684a,0x28a18a26])))))) (bI j 42 (bI j 35 (bI j 31 (bI j 29 (cB [0xf88a3e028d90a341,0xa583291a4a42228,0x66029790a5e02978,0x29a14a66129980a,0x29c90a72]) (bI j 30 (cB [0x4a8002a000a7a3,0xca8892a200a8232a,0xaa72a814aa002a68,0x42b00cac002ae10a,0x2b3e0ac6]) (cB [0x900b2402c710afef,0xb2802ca00b2422c,0x3052cc00b2842ca0,0x12d000b4002ce8cb,0x2d084b40]))) (bI j 33 (bI j 32 (cB [0xb00b6252d424b446,0xcb7e02de0cb6c62d,0x9862e394b8452df8,0x2eb10bac02e910b,0x2f524bb5]) (cB [0xb14bec02fb00be63,0x4bfc02ff00bf632f,0xa030014bfe12ff0,0x30700c14430294c,0x3070cc1c])) (bI j 34 (cB [0xb00c26330888c220,0x8c48830f94c2c930,0x6a331a80c6433161,0x431e10c78031c10c,0x32240c80]) (cB [0xb00cac032a08ca80,0xccac532b00cac032,0xbc132f00cbc032d8,0x53373ccc0e32f84c,0x34100cfa])))) (bI j 38 (bI j 36 (cB [0x204d08034200d042,0xcd14034294d0a034,0x1c134684d1a03450,0x3560cd3ed347c0d,0x35784d5e]) (bI j 37 (cB [0xa04d62335804d600,0x8d6c135a84d6a035,0x88336010d7a335b9,0x436888d96636390d,0x36b90da6]) (cB [0x800dd843729cdb6a,0xdeab37988de0337,0x30338728e1063802,0xe38eace3a038d88e,0x39b10e50]))) (bI j 40 (bI j 39 (cB [0xd84e76039d04e740,0xe7c039f00e78239,0x8003a000e7c239f0,0x23a288e8053a000e,0x3a4a4e8e]) (cB [0xaeceaa03a988ea41,0xf0413be18ee0c3a,0xc13c18cf0603c18,0x13c384f0e03c380f,0x3c488f10])) (bI j 41 (cB [0x800f1c23c58cf160,0xf2603c80cf2003c,0x2a23c988f2603c98,0x13cc80f3203cb88f,0x3cd18f32]) (cB [0x190f4223d080f401,0xf5623d580f4e43d,0x6203d70cf5a13d68,0x83d988f6223d880f,0x3dea8f6a]))))) (bI j 49 (bI j 45 (bI j 43 (cB [0x488f9203e480f8e2,0xf9c03e58cf9603e,0xa203e804f9c23e70,0x13e98cfa413e884f,0x3eb8cfac]) (bI j 44 (cB [0x8fb843ed84fb41,0xcfc403f100fc403f,0xcc43f300fca13f10,0x3f684fd813f508f,0x3f728fdc]) (cB [0x10500403fe94ff05,0x1006140181006040,0xc14020900804020,0x24039500e0403810,0x4070d018]))) (bI j 47 (bI j 46 (cB [0xf0103c040e09022b,0x504204108103c340,0x4444110104404108,0x415110502413090,0x4171105c]) (cB [0xfa1066c419810641,0x109004238508e041,0x9604250509024240,0x14268909a0425890,0x4281109e])) (bI j 48 (cB [0xa890aa042a810a81,0x50b2042c810ae242,0xbe042e890b4342c8,0x433050c0642f850,0x433890ce]) (cB [0x9010e024368d0d24,0x50e63439810e4143,0xf8f43d090ee343b0,0x144f851345445bd0,0x45091140])))) (bI j 52 (bI j 50 (cB [0x49114e24538114a2,0x516414571115a145,0x7c045d8d16874598,0x245f8917c145f011,0x46199182]) (bI j 51 (cB [0x50d1940465011921,0x119c14670119a146,0xa464688519e24678,0x146d011b4046c091,0x46d8d1b4]) (cB [0x851c20470051bc2,0x51ca0472051c4247,0xd22474051cc24728,0x9476051d80475851,0x47b151da]))) (bI j 54 (bI j 53 (cB [0x6a1204b47e191f61,0xd236248d0522a548,0x5c149495240948e8,0x649c192627497892,0x4a20d27c]) (cB [0x38928e04a38128e0,0x529404a50129214a,0x9824a60129614a50,0x14a8092a004a7092,0x4a9b52a4])) (bI j 55 (cB [0x4812d014b4012c08,0x52d804b48d2d204b,0xdc14b6852da04b60,0x34b9812e604b7912,0x4bb052e6]) (cB [0xd012f404bb8d2ee0,0x12f824bd092f404b,0xe04c2892fc74bf0,0x54c80531464c38d3,0x4cb05322]))))))) (bI j 84 (bI j 70 (bI j 63 (bI j 59 (bI j 57 (cB [0xd8533604cb9132e0,0x133e34ce0d33804c,0x5a04d60535424d12,0x4d80135c24d6853,0x4d80d360]) (bI j 58 (cB [0xa8136814da013661,0xd37074db8536a24d,0x8824e18538414df8,0x14e60939234e30d3,0x4e78939c]) (cB [0xf0d3aa94e9893a22,0x13c804f1853c224e,0xcc04f3013c824f20,0x44f5013cc44f3013,0x4ff093d5]))) (bI j 61 (bI j 60 (cB [0x2314080500114000,0x942a750a81420550,0x6005178544c950e2,0x151b8146e05181d4,0x51c0d46e]) (cB [0x301486351da14760,0x549e4523a148c152,0xd4252ad54a815298,0x5390d4d86536014,0x53a814ea])) (bI j 62 (cB [0x14eca53a854ea0,0x1504154009500054,0xa25428150625418,0x154a3d510c543855,0x55201546]) (cB [0x4995520554815485,0x555e25578155e055,0x6615590556405588,0x155d1d574055a195,0x56105582])))) (bI j 66 (bI j 64 (cB [0x41d58a3561895860,0xd5baa5683559e156,0xd40575015d405738,0x5576815da05750d5,0x579015da]) (bI j 65 (cB [0xe055e8857a015e42,0x96348587ad5fb257,0x8b359a4566805914,0x5ad816b605ac0d6,0x5ada16b6]) (cB [0x50d6cc45b3016c63,0x96de05b7816da25b,0xe675b8896e205b78,0x5c6096f715bd056,0x5c72171c]))) (bI j 68 (bI j 67 (cB [0xa174015cb2972c0,0xd75625d50575215d,0x7c65d83976005d68,0xe5e38978e05e20d7,0x5eb9d792]) (cB [0x2cd7c625f1057bc4,0x18103601957f0b5f,0x1616058181606058,0x36068581a0606058,0x6088181c])) (bI j 69 (cB [0xf018382608ad8220,0x1844060f1183c060,0x4606118184416110,0x3614858501611958,0x61681854]) (cB [0x8b986206180585a3,0x188406210187e361,0x8a06228188436210,0x26278188aa622818,0x6288189e]))))) (bI j 77 (bI j 73 (bI j 71 (cB [0xa9d8aa06290d8a21,0x18ba062e818b8162,0xc4562e958ba062e8,0x634018ce1633818,0x634098d0]) (bI j 72 (cB [0x8058d65635058d40,0x18ee0638998e2063,0x80641098eeb63b8,0xf648119127642159,0x65191928]) (cB [0x38194e06538194e0,0xd95606550594e365,0x5e16570595c06558,0x6658819601658019,0x65b81962]))) (bI j 75 (bI j 74 (cB [0xa9982065d9996e4,0x19b2566c05996d66,0xbc066f019bc066f0,0x672819c6266f159,0x672819ca]) (cB [0x4019ce1673059ca1,0x99d606740d9d0067,0xe4a679019da56758,0x68201a06167e1d9,0x68201a08])) (bI j 76 (cB [0x485a0e268289a081,0x5a18068509a14068,0x22a6870da1a16860,0x68f01a3c068d8da,0x68f05a3c]) (cB [0x18da46068f91a3e0,0x9a56569581a4c569,0x78269b19a6446980,0x16a885a9a469f3da,0x6a985aa4])))) (bI j 80 (bI j 78 (cB [0xf01abc06ad11aa86,0xdac206af0dabc06a,0xcc16b209ac806b08,0xa6b91dae026b3a5a,0x6c189af2]) (bI j 79 (cB [0xd91b3416c731b0a9,0x1b3e06cf81b3e06c,0x4a06d189b3e46cf8,0x16d41db4a36d281b,0x6d801b5e]) (cB [0x901b6216d881b601,0x1b7e46dba1b6456d,0xa446e3adb8e06e19,0x46eb01bac06eb01b,0x6ed41bac]))) (bI j 82 (bI j 81 (cB [0xfadbec96f98dbd49,0xdc5ac70ae1c14b6f,0x84272101c80271c9,0x172209c88072201c,0x72381c8c]) (cB [0x581c92272405c8e1,0x1ca417259dc96072,0xaa672a81ca627298,0x273085cb6672d81c,0x73205cc4])) (bI j 83 (cB [0x521cd4073311cca1,0x9cfe7739b1ce4173,0x10274401d1007430,0x74505d14074501d,0x74581d16]) (cB [0x885d1a474681d162,0x1d28074909d24074,0x38074d85d28774a0,0x74f19d3c074e09d,0x75201d48])))))) (bI j 98 (bI j 91 (bI j 87 (bI j 85 (cB [0x581d54175485d485,0x5d60775801d56575,0x7d275c19d70075b8,0x76d81db2276825d,0x76d85db6]) (bI j 86 (cB [0x509dbad76e05db80,0x1dd8977601dd8077,0x10078309df2d77a9,0x378919e12978405e,0x78d81e30]) (cB [0xfa5e3e078e0de361,0x5e54079409e50078,0x76179c0de6e17953,0x7aa85e9e679e4de,0x7ab09eac]))) (bI j 89 (bI j 88 (cB [0x285eca07ac35eb00,0x9ee097b801ecca7b,0xfa77be05ef617bc8,0xb7c785f08b7c201e,0x7cdb5f20]) (cB [0x601f5047d401f500,0x1f5e27d60df5807d,0x6637d905f6217d88,0x47e101f6eb7db05f,0x7e301f84])) (bI j 90 (cB [0x485f9017e401f8c2,0x1fa417e619f9427e,0xca67ecb1fa667e98,0x87f981fd687f581f,0x7fdc9fe6]) (cB [0x49a02d380a8601a8,0x2076e818aa05e281,0xb4182d020b21824c,0x82f060b6382d820,0x82f8a0be])))) (bI j 94 (bI j 92 (cB [0x8920c8d831860c22,0xe0f8183a9e0ea083,0x1628440e110083ea,0x48470611a1846821,0x8498211e]) (bI j 93 (cB [0x18a144184ab61262,0x615618529a14a085,0x84185f8e17a28564,0xa8666a19428619e1,0x878261cc]) (cB [0xd061f4087c861f20,0x62004880021f6587,0x1208829220a08820,0x58892a2221884a22,0x89086238]))) (bI j 96 (bI j 95 (cB [0x2862443891022440,0x624c68930224c089,0x6808969e25a08960,0x689a06268089a022,0x89d9626a]) (cB [0xd862b228ab0e2816,0x22d698af362b828a,0xf618ba9a2e818ba0,0x18bfba2fc18be0a2,0x8c75a31a])) (bI j 97 (cB [0x8238018da323490,0xa39628e50638298e,0xace8ea0a3a618e69,0x28f4823c858f2023,0x8fd863d3]) (cB [0xbce4074901063f86,0x246c291b02454c90,0x72091c06470091c0,0x92386472e91c824,0x9240a490]))))) (bI j 105 (bI j 101 (bI j 99 (cB [0x60e4961925824941,0xa4b2092c0649e992,0xd42935024c6792ca,0x937124d82936024,0x939164e4]) (bI j 100 (cB [0x3064fa993c164ee1,0xa516a9439250e094,0x3c194f02536394a9,0x95312540694f865,0x95502554]) (cB [0x61a5580955865541,0x259cb95c5a564695,0xc20970825c2096ca,0x19718a5c41970865,0x9734e5ca]))) (bI j 103 (bI j 102 (cB [0x4126100983865f2e,0x261e99868a618198,0x4609900e630898c0,0x995026467991826,0x99536654]) (cB [0xc8a670199c0266e1,0x2676a99d82676099,0x9469a50269219a29,0x19ad866a0b9a8026,0x9b68a6b9])) (bI j 104 (cB [0xb8e6ea29b8166de1,0xa70ec9c3066f4c9b,0x3ca9ce8673249c99,0x29d4c675209d4067,0x9de0e774]) (cB [0x13678219e00677e1,0x67ae99eb0679e79e,0xe249f78a7c2e9f00,0x2a089a80ea9faca7,0xa0c8682e])))) (bI j 109 (bI j 107 (bI j 106 (cB [0xe168361a0d068340,0x28520a12928424a0,0x5e1a15168521a148,0x3a1c9a8701a18228,0xa210287e]) (cB [0xd8689cda21328840,0x28baca2e068b80a2,0xde8a37828d26a348,0x1a3c2e8ee1a3b828,0xa423a906])) (bI j 108 (cB [0xcba9301a49969241,0x6970aa5b0a94efa4,0xa85a62be9862a610,0x7a78ae9b76a6c8a9,0xa818a9f8]) (cB [0xb92a207a870aa0a9,0x6a3b3a8e06a361a8,0x702a9c02a6a3a981,0xaaf2ea973a9d46a,0xab486ad2]))) (bI j 111 (bI j 110 (cB [0x602ad80ab50aad40,0x6ad8eab602ad80ab,0xf80abd86af60abd0,0xabe8aafa0abe06a,0xabfa6afe]) (cB [0x80ab108ac402b100,0x2b2e0ac916b240ac,0x461ad182b460acbb,0x3adb02b5e7ad22eb,0xadc82b6c])) (bI j 112 (cB [0xf92b7e0add92b722,0x2b865ae182b860ad,0xb41aeb8eba07ae42,0x7aef02bbc0aed8eb,0xaf28ebbc]) (cB [0xa16bd88af412bd00,0x6c26cb0146bf29af,0x6a0b1a82c605b0fc,0xb2082c820b1ab2c])))))))) 18 (i % 16)
set_option maxRecDepth 16000 in
def zpo (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 178 (bI j 89 (bI j 44 (bI j 22 (bI j 11 (bI j 5 (bI j 2 (bI j 1 (cB [0x4c001004000003f,0xe402b09c803e0c48,0x8619010c43201ba4,0x195c86431f800462,0x9c86871390cdf432,0x9c5cc3108a08620a,0x1aecc5630898]) (cB [0x8fc70431b8d94633,0x892c3c10c867651,0xeb6524cd5cc496aa,0x4a1bd9493f5c1126,0x73187328230e1f04,0x126bb621cc22c3f9,0xb731e8b6823d])) (bI j 3 (cB [0xcac03218f8004314,0xda34301b466e8190,0xe06e98840a031010,0x319828262b03f8c4,0x554c7e0b818dc155,0xb50a049612e06432,0x455526686ea4]) (bI j 4 (cB [0x50d95549fa2e0937,0xf4c3905dd870cb82,0x80c4310c17c61f82,0x31012f4f4525dde8,0x78c4e00b1884003,0xdc02b319805062b0,0x20acc7e01798]) (cB [0x4b5003496105e643,0x5e93740ad26680b2,0xc17a50d82b49fa0,0x61fc02cc39800d87,0xde89014310e01e,0xb4004496502cf45a,0x35266005a4])))) (bI j 8 (bI j 6 (cB [0x50c80d49f801e937,0x24c390045870407a,0x800ab10c01361f80,0x61c1024f452045e8,0x2187e003b0e4005,0x148057a20014c430,0x19e88403bd]) (bI j 7 (cB [0xd1000961e0012f4c,0x1d25020324a00063,0x2002b0e001092800,0x621901cc3f003187,0x31e8b002bd10810,0xb280c928000ec388,0x51e9800424]) (cB [0xf000a496001292c,0x2ec39402d87000a3,0x600cb10c01861f80,0x7a21032c4f206189,0x6de9600d3d16012,0x46812928003af4f0,0x724b040d49]))) (bI j 9 (cB [0xd1001f49a0038f48,0x4af4b806de8b009b,0x3409c9400277a780,0x61cc028c38a06e4a,0x9188601030fe01c,0xd281c7a2d028f440,0x8de9801098]) (bI j 10 (cB [0xf002231a0044940,0x409340098c80011b,0x801098a202092c00,0x7a40048934808589,0x55e8800f9892020,0x3e0277a5c03af458,0xa0564a0014bd]) (cB [0x150024312503b251,0x1ac388091e900153,0xe016312d01861ca0,0x928d01b25000b989,0x3d25801698d2818,0x3d82e4a5a03292d4,0xa03e4a001825]))))) (bI j 16 (bI j 13 (bI j 12 (cB [0x8800317aa5033251,0x96c38010cc6c0199,0x602b30fc05461c80,0x62790acc4b017188,0x191e8a030bd1085c,0x4006b7a780caf4b0,0x21924a2430c9]) (cB [0xfc03661c8068c38,0x6ec4b00e588601bb,0xa01dbd1083962790,0x7a7807cf4b00f5e8,0xf64a241dc940041,0xd0835928006af442,0xe929001c18])) (bI j 14 (cB [0x90003c928006af44,0x8495401024b001f9,0xa0223d100407a400,0x7a7808ef4b0119e8,0x11a4a2422494004a,0x600481a0008b2502,0x125e90024c9]) (bI j 15 (cB [0xd1404c7a2006892c,0xa4f4f013de960273,0x427494484c92800,0x320009b25000d587,0x14d8a8028c960050,0x4003649600a2f480,0x2156ab802ac9]) (cB [0x57003731000ae334,0xb033200e062802dd,0x2d494005961c00,0x4a400726200168c8,0xe8c40030557005d,0x5005f92800bc92c0,0xed25802fb1])))) (bI j 19 (bI j 17 (cB [0xd1404c7a20088942,0xc0f4f216de9602ab,0x31c94406292810,0x928008ac4e00f187,0x11928401ea4b004d,0x863aae009cf440,0xf8c400330d]) (bI j 18 (cB [0x96004f61c008e636,0x9032a00fc6280354,0x802824b006719f00,0x31000d032801a5e8,0x14587002498d8040,0x5004a31b00826200,0x14987003625]) (cB [0xe004231000d4f48,0xf462101b8c40029b,0x604898ac07d31380,0x496013464f0258c9,0x25929683d24b506e,0x4009d625213494f4,0x27e4a204f49]))) (bI j 20 (cB [0x52c07249680de92c,0xeec4a01d529e039a,0x403cc94407892800,0x31400e325001c189,0x1c125803b3d50074,0x5907261c00e2c380,0x1f2ab803dbd]) (bI j 21 (cB [0xd5808849a00fc31c,0xfe3280242ab80473,0x404298c408431000,0x18a010f250021989,0x20927c0408c94080,0xd00803140106f440,0x2086500408c]) (cB [0x4f007f18e0106634,0x1b250022d894044a,0x80410c7008a7a201,0x62401066280230c6,0x23cc800430c7008a,0xa008c31401169340,0x23588004398])))))) (bI j 33 (bI j 27 (bI j 24 (bI j 23 (cB [0xd580926240110624,0x126240256ab804a3,0x804524c009392801,0x7aa011a930022cc4,0x1cd87004b8c70093,0xb009931881306204,0x41d525883a24]) (cB [0xd110764960136f54,0xf662101dcc4004e3,0x804a18ac08e31380,0x49620f692d41dd25,0x24126603e24b4078,0xe507861c012a9370,0x1e525883e30])) (bI j 25 (cB [0xcc0a1013a0f2c38,0x662022a807e0550,0x603718dd04b31580,0x496816a92c21b8c8,0x33d26e064a4cc0c0,0xe08cf4a1919293f0,0x35587206930]) (bI j 26 (cB [0xd100dc62181aec3f,0x44f442355e8a4693,0xe052bd2c0a47a281,0x928914525002a5e9,0x298080051c9408a4,0x200a892c014ec400,0x2ac06c0543d]) (cB [0x12c0af61c815ac38,0x6725002c989e0583,0x5649400b492881,0x1a1016203402ba4a,0x2d801e0573d100ac,0xcd8ad01fa15a0330,0x22b467e0568c])))) (bI j 30 (bI j 28 (cB [0x50c06f49b800892c,0x76c3902e1870437a,0x805fb10c0bc61f81,0x7a21176f4522e1e8,0x2dc63645bc9400b7,0xe08ae31fb15c33f0,0x21c5886002b0]) (bI j 29 (cB [0xd100ba7a28172f44,0x75250001d8700033,0x205ea4d400849611,0x7a610e094d01c128,0x29258004a4b00be,0x2c0af19f817cc3c0,0x2d2584578d]) (cB [0x53c0724a1a068935,0x82c4e03058844392,0x6062bd140c37a211,0x9280190f4f0319e9,0x30a4a0462c9448c3,0x390356208018c380,0x3124a04613d]))) (bI j 31 (cB [0x12c0c77a4018f258,0x946290034c404580,0x2066c94087332781,0x61c10e864e033a4a,0x3925806649400cb,0x808b202581989350,0x21d4c9e00798]) (bI j 32 (cB [0x9440d0928018292c,0x84c380041258068c,0x84598cfc0a219981,0x4a1a098937004525,0x30d87205c30e0878,0x108d0621919ac3f0,0x351e8a069bd]) (cB [0x10e00561c014663f,0x88f4502e5e88826b,0x605d3d1200c61c01,0x496116834b029066,0x1e529e82724dc012,0x2c0c561c8176c382,0x234589e46731]))))) (bI j 38 (bI j 35 (bI j 34 (cB [0x9c0d692891a9250,0x9e62b004cc400528,0xa03b99040d831aa0,0x496817892c21dcc9,0x36de9806d24d40c6,0x100bd49620a062a0,0x29c04a06cbd]) (cB [0x8ac0143100150027,0x8e92d02f92588289,0x600a98800a901381,0x496817e92c4148c5,0x58c4006db0f00c8,0xd05431b80666290,0x21e8c9e03d19])) (bI j 36 (cB [0x5380e74a101bc936,0xdcc394301870473a,0x6079b10c0f061f81,0x7a211e6c4f23c189,0x3e5e9607c3d140f5,0x448f592801faf4f0,0x37d25847c49]) (bI j 37 (cB [0xd2c0e37a281c2f44,0xc32500399e9e0723,0x703d108e392891,0x92801c0c3823824a,0x395e90072c9600e2,0x2c0e8496a18292c0,0x3a929e074a5]) (cB [0xd500ed92881d9250,0x2e92c4309870075b,0x81b250403649a80,0x62d01d0c4e037d88,0x3a1eb48743d388e8,0x308efaae01df2506,0x60c400703d])))) (bI j 41 (bI j 39 (cB [0x5680f131a806e629,0x7062803caab8474a,0x401c98a401931000,0xaae21d0c3823a92b,0xed26b00924b00f4,0x887c4a7a0aa9430,0x23b189c070b1]) (bI j 40 (cB [0xd2c0ef7a2a186f44,0xed25023d1e9e4793,0x3003b0e00f792881,0x92801c4f4e00f188,0xf526a00d24b10c4,0x108ed62d01c6c420,0x23deab8862bd]) (cB [0x90403e3148036620,0xf665901ecc9a07d1,0x286330e00e449b10,0x31401f925803ed88,0x100c5200e188003f,0x810c761c01ca9360,0x104c5200e98]))) (bI j 42 (cB [0xd210c861c01cc936,0xfe31d007862807e3,0x843e8d3c07d1a181,0x7a2826af44047526,0x501e9e09cbd2c138,0x8938928926b2500,0x21f869c03f0d]) (bI j 43 (cB [0x4b410f4960200634,0x28943044927e088a,0x848a253c9124a582,0x7a5822ef450455e8,0x4564a008e3d3c118,0x807f19b122f2512,0x404c4043f8d]) (cB [0x8dc1043198206621,0xc6432410c7e0831,0xe084b0e410761c12,0x7a2021cc43042987,0x200c6c484bd14907,0x1010261c11006420,0x2046804813d]))))))) (bI j 66 (bI j 55 (bI j 49 (bI j 46 (bI j 45 (cB [0x908105318020a940,0x10f4404092584419,0x80410d0010b19a02,0x7a60218634220869,0x210c84086b0f010d,0x1010149a110864e0,0x24424a00883d]) (cB [0xd301034a00204c40,0x26c4c0410c800428,0x808318d010531a02,0x4a0110e64e044d27,0x45a4a008830e0107,0x1094a00210c4c0,0x21869808c8d])) (bI j 47 (cB [0x50010a31a110c358,0x16328046e4b008d2,0x808698d010c31402,0x18a0236f480438c6,0x22066e0800c7401f,0xcc11e49611103430,0x249d27e093a4]) (bI j 48 (cB [0xfc12c61c8252c38,0x52f4404d1886096b,0x208fb0e092c7a292,0x6218244c3f048587,0x485e8a48fbd10126,0x3012349a0240f442,0x491280092bd]) (cB [0x94012561e0248934,0xe6298050c400944,0xe08fb0e088d32182,0x7a28254f4424a187,0x42126b004a4b012b,0xa601c3100240f440,0x48587008498])))) (bI j 52 (bI j 50 (cB [0xc7402018a1257250,0x1634104b866a0850,0x809798d088b1a681,0x18e0266f4c048925,0x84628086190010b,0x410c19a81183290,0x48cc404460d]) (bI j 51 (cB [0xc5013261c0260940,0x6292c0490c400110,0xa0118c5013162002,0x4960260634043463,0x43863a0120c50125,0x8013361e024c92c0,0x454c5300998]) (cB [0x940129620112064f,0x1092c04de4a209b4,0x80953d3011649ac0,0x314c03662004ade9,0x4deab80963100117,0x411818e804a3142,0x23869a09d0d]))) (bI j 53 (cB [0x4d013b320111c359,0x3231c04fe4b0096a,0x809724d011a32602,0x1a0811e335009862,0x4bcc504478d3411a,0x5013e7a20278c4c0,0x4c0c510108c]) (bI j 54 (cB [0x4d013149a027ac38,0x4031404f5e980992,0x809e190011b18ec0,0x18e804e31404cd26,0x4fde9009a24d011c,0xa404318e80503140,0x2446868218c]) (cB [0x8900de310112234f,0x84c38437925808e9,0x84a4b12c14961f82,0x7a5829cf45052de8,0x52e4a00a93d3c14f,0x1011e498129d2512,0x515e8a0a1bd]))))) (bI j 60 (bI j 57 (bI j 56 (cB [0x9401487a7828cf4b,0x3ec3c25164a24a1c,0x80903d2014492802,0x92c0244930048587,0x499260092a4c0147,0x70127312028ef480,0x4a12600a555]) (cB [0x8d4044314c02a620,0xc292c2254c9e8221,0x8870b0e012949801,0x9281294f4b050de8,0x292580a6c94414c,0xe10454a0808a9358,0x4a987807130])) (bI j 58 (cB [0xf014492821c4f44,0x8c6298074c40095b,0x71a4b104631a80,0x7a221c6c3804b126,0x9c6284a6d570145,0x5047194808e31d8,0x25069a0a80d]) (bI j 59 (cB [0x8900e43101128359,0x8cc3843912580969,0x240c7015192c02,0x18a025c624412065,0x1246520248c76024,0xb013331201ca6204,0x51d870872a4]) (cB [0xca404a18e8052314,0x686240398c408250,0x80a430e10e649602,0x18a02a2f48054d8a,0xac6280aa0cd402a,0x3d05619b82ac31d0,0x5a0c6c44b0d])))) (bI j 63 (bI j 61 (cB [0x12d0f061ca192c38,0xdd25005b589e0b5b,0xc82b8cd816f92882,0x49682ae92c225c69,0x57526e0ad24cc159,0xe01604a782bc94b0,0x43c587286530]) (bI j 62 (cB [0x94016462782c2c4b,0xb2636059e4a20b34,0x865b0e089832720,0x4ac20b034005624a,0x5712600ae310015b,0x2015f62c11323580,0x5886680afa5]) (cB [0x9081654aa02c6934,0x98f44056187082d1,0x80b5494416992821,0x19a82c231d00b062,0xb46280b618d1961,0x7402e18a02c63350,0x63a58700b20c]))) (bI j 64 (cB [0x90c166314d01a620,0x9af4405a528482d9,0x340c18810f27a2a1,0x7a202d4942059cc5,0x1706560178c510ce,0xb00e7310113434f4,0x43cd25a867a4]) (bI j 65 (cB [0x9401714a7b2da94b,0x6031405da4a20bac,0x8c7524b00ea31000,0x1a0806231405c9ea,0x3ad2580759880173,0xde80f31002e8f446,0x3b125883018]) (cB [0x8810f461ca1a0c38,0xa2c3803b525940c9,0xe03098ae00331021,0x496113c6434184c6,0x4d526607aa4b40d2,0xc96e49f82969370,0x43498704baa5])))))) (bI j 77 (bI j 71 (bI j 68 (bI j 67 (cB [0x10d96e61fa1eac39,0xf2f4505e1e88cbab,0x603124de00449602,0x61c81a6c38418928,0x53188609b30fc0f6,0xb10f67a2a1a6f440,0x18d26f005a4]) (cB [0xe40d461c20c6943,0x9ac4304dd87e07bb,0x87bbd150d47a202,0x31b80c862b8058c4,0x35525844f993d064,0xdc13849981f092d0,0x25bd2960a724])) (bI j 69 (cB [0xe50d561c12ec94f,0xecc4f65bd89687c3,0x80bdc94497992832,0x7a201acc38805d25,0x19463f00f0c510d6,0x417d19aa0ca32b0,0x227469a04e8d]) (bI j 70 (cB [0x89c0f931081ae620,0xc635053cc5609c9,0xa87ca4b50d749603,0x18f030ef4c461926,0x360c408330ca8066,0xac13a31381f46210,0x5f8c7e0a818]) (cB [0x4b50d84960304643,0x494345f927e87d2,0xc2bd141847a223,0x4a602fe634019c65,0x600c800340c70181,0x2018131e03006280,0x1a4c540c1a5])))) (bI j 74 (bI j 72 (cB [0xe00d949620d2636,0xf692d436925886cb,0x60350c7e01f18a21,0x31081b662041a865,0x544c5609f989c0fc,0x510fc496a1b692c0,0x1ac63f0140c]) (bI j 73 (cB [0x8840dc31020d632b,0xa462b0500c4e07e9,0x887ea4b50dc49602,0x1b031402a061d87,0x62869d0c50d0918a,0xb41fd49603bc620a,0x8ad26610f24]) (cB [0x50c25c49f84b0937,0xdc94f29712961372,0xe90f30e51fd61c14,0x625a4dcc43497187,0x7f5e88d37313da5c,0x3e22b7a5c43cf458,0xa7f64a112c3d]))) (bI j 75 (cB [0x13818b021543d251,0x5663206606284c58,0xe0e630e41c461c03,0x62583a6c43073987,0x755e884e9b13c9ce,0x3c1d97a583b0f450,0x27564a00eebd]) (bI j 76 (cB [0xc9818c00413b1251,0x2a92d064d2580c78,0x40cba53c1964a583,0x928c327250863d89,0x6392580c68c9a195,0x2218e928431ac4a0,0x6418940c680]) (cB [0xc5019119a0325250,0x2925086498940c70,0x44c60d3818c1a103,0x61c833cc380664c6,0x68d8860d0b0fc1a0,0x109a36279342c4b0,0x699e8a0d23d]))))) (bI j 83 (bI j 80 (bI j 78 (cB [0x9401aa7a7834ef4b,0x3431c269a4a24d24,0x84c68d3818d1a103,0x310133b2500675e8,0x671e880ce30e019b,0x3818e32103386282,0x67de884c719]) (bI j 79 (cB [0x9381a219a133f250,0x3ef44067527d4c71,0x80d40d001a592803,0x92c531a358863469,0x6b00380d4bd201a9,0x5098f027031e0420,0x6ede880cc8c]) (cB [0xd3c1be7a5837af45,0x7b25126ee4a00e1b,0x20d6988019a00413,0x31b836063306bcc4,0x6c8c864d818fc1b2,0xfc1b661c8368c382,0x6e98860dbb0]))) (bI j 81 (cB [0xc509b67a29368f44,0x5cf4406b98700cd8,0xd98cf01b14a013,0x496033831406c4c6,0x6e0c680dabd101ae,0xa01b961e0372f4c0,0x264869c0da0c]) (bI j 82 (cB [0x8d01bc928033a620,0x6e01c06d86500da9,0xc801301bf02003,0x92c038064026400b,0x6440680dc0d001c2,0x3099102603700400,0x6e40380e0b1]) (cB [0xd201ba00e0382640,0x2634e064c6840e13,0xa0e2bd1019e31013,0x7a78390f4b071de8,0x71e4a24e2c9401cb,0x4019f496132864e2,0x7246800e349])))) (bI j 86 (bI j 84 (cB [0x9629921ac432434c,0x2a34e0729e900e54,0xd018809951ad03,0x1a139b55c07364a,0x6846284cb01681cf,0xe01a200403a555c0,0x7464a00e830]) (bI j 85 (cB [0xc5099702d03a2340,0x2634e0752ab80d18,0x80dda4f81a431053,0x7a5839af450715e8,0x75a4a04ea3d3c9d2,0x281a549603af2510,0x71a4a00de31]) (cB [0x4f81a6310532a35a,0xaf55c071de880dea,0x10c781301da02013,0x319034e314a63c0b,0x7724b00e430e01be,0xb01bf19303500080,0x76de880e4a4]))) (bI j 87 (cB [0xe01c23190352314,0x8663206a86280e53,0x40ee3d201cb61c03,0x3212330336066065,0x77d2594cc193a198,0xdc1f049983de92d0,0x7e527e0fc24]) (bI j 88 (cB [0x53c9f94a583f8943,0xdec39477d8704fe2,0x68fe310d1f961fa3,0x7a233f8c4f67e589,0x7c1e970f7bd161df,0x469df92843f0f4f8,0x4678c6d4f7c9]) (cB [0xe29a44a74348942,0xc6c3f07898720f03,0xe4f1b12c1e662183,0x7a283cef44279989,0x7b9e9e0f4bd2c1e8,0x89e892893cf2500,0xa69589d0d2b1])))))))) (bI j 133 (bI j 111 (bI j 100 (bI j 94 (bI j 91 (bI j 90 (cB [0x8d09e192803c2f44,0x3e94207952680f21,0xf0bd1299f62723,0x4a003d464087864a,0x6752b10cea5301ec,0x3219c31a03db258a,0x7ad8994ce19]) (cB [0x9081ed7a403d6640,0x4c95a869929c8d01,0x90f449411e27a253,0x19a03e2328a7a2ab,0x7ccc508cc8d00199,0x29a732d434e64e0,0x87a64a00fbb1])) (bI j 92 (cB [0xd3a1a81a153d355c,0xd8f4407c92594d40,0x80cd0c729ec92843,0x49603e8634466866,0x7aa4a10f53d101f6,0x121eb61c03ea620a,0x66cc514f5bd]) (bI j 93 (cB [0x8a01f549a2336634,0x5264e86a4c840fa1,0xd4f6c9421ed7a253,0x498535465a86a8c9,0x7baab90f749401f7,0xa11a11a103f4328a,0xa684cb50fd18]) (cB [0xd3a9e3aae23c6f44,0xc8c3807ed2594d10,0x48d18cda9e592823,0xaae23ccc38a68ccb,0x754c848e20cda9e6,0xe01df49653aa64e8,0x8218720ff30])))) (bI j 97 (bI j 95 (cB [0x12c2116218414c3f,0x26f44284589e5053,0xe10abd2c2147a284,0x92894272500875e9,0x75929d0eb2508a14,0x141ff7a203c0c38a,0x809e96100bd]) (bI j 96 (cB [0x9449ff928040ef4f,0xc2f44a71989c500c,0x101990020092803,0x4ac437894c081528,0x6d4c6810349629bc,0x204626536a64c8,0x819e9010219]) (cB [0xe29d74ad43ae94e,0x1355c08264a00f13,0x410718d020b19a14,0xaae03c692ce748cb,0x790c41ce88d38210,0x8020d9280418c380,0x83d8700f298]))) (bI j 98 (cB [0x50020d320741b250,0xcc92ce750cb5d06a,0xc8e29908212aae03,0x7a203cec38a71529,0x841e96104bd141ff,0x461ff9281424f4f2,0x471cc85104c9]) (bI j 99 (cB [0xd101e861c539a95a,0x90336a826ab8100b,0x810d19002161a023,0x496537665886ecc9,0x8724b010130e01e9,0x829b41a643683340,0x80d2580f518]) (cB [0x8802197a2042ec4c,0x30c3808112580f59,0x94d719321ae32004,0x310239232a0861e9,0x86de88102a4b01ec,0xb02171a023943360,0x8198700f6a4]))))) (bI j 105 (bI j 102 (bI j 101 (cB [0xe01ee4962396336,0x983420871e90103b,0x94ec196a1d832723,0x7a2a410f4407bd25,0x88de9e1103d2c21f,0x40a237ad9440f570,0x8924a310a49]) (cB [0x57022a92d844b257,0x423402892abb50a5,0x81130d3022232004,0x332437a65808a0c9,0x6d8680114d5929bd,0x302277ac536c3588,0x8a64a81138d])) (bI j 103 (cB [0x1001ab01a0458028,0xb234e08e86508d58,0xf818829d91ad43,0x928c42b250093d88,0x95e4b612ac95e225,0xaa25aaed42b55c0,0xa76809d0ed01]) (bI j 104 (cB [0x4b422d49603e2314,0x6494308bd27e1172,0x8519253ca2f4a584,0x7a5c450f458869e8,0x86a4a011cbd3c234,0x3a1db1a15451251a,0x7c8c414ed8d]) (cB [0xa2a1b9284436f44,0x6725408c52b01180,0x10df813023502004,0x92c046c940a6fc0b,0x6e00990dc00d0238,0x202374a0046ec4ca,0x6b003811c3d])))) (bI j 108 (bI j 106 (cB [0x8d01f318a2358034,0x8e92d091925811d9,0x6125250c24849f84,0x7a2149494f292129,0x92de971133d16216,0x46a16928049cf4f0,0x7d062951349]) (bI j 107 (cB [0x8cc23d3108478620,0x7c63f0900c6e11f1,0x310bb0e0a4032194,0x6218482c3f889d87,0x89de8b50bbd10245,0x1221861c03ea620a,0x8fd28150c3d]) (cB [0x8d024201a047e630,0x869400911e9911b9,0x12230f024301a04,0x310235a33406b465,0x865e8811e24d01f6,0x1af19454332508,0x8f52808d78d]))) (bI j 109 (cB [0x9011b0020036001c,0x6201c092589811f1,0x811f98d11b101a03,0x31a236403406c803,0x6dc038124a4f0240,0xd024c020236e0340,0x88d928012098]) (bI j 110 (cB [0x130242194049b258,0x7203406e40391213,0x812218d224202023,0x31a237403406e803,0x8ec650126bd20245,0x829dc1a743b83420,0x8871e880fb98]) (cB [0xd3c2507a5c452f45,0x53251a8724a012a3,0x1208ca224d02054,0x1ac438434c88e068,0x94e4b0128a5029c2,0x322371a043823340,0x9498994e08d])))))) (bI j 122 (bI j 116 (bI j 113 (bI j 112 (cB [0x5002441944488040,0xa6f4809146501292,0xdf00d023401404,0x194449604c46f808,0x6f86b111a0d3024b,0x2564a6537c3648,0x8942ac812831]) (cB [0x1311c001a0380028,0x6c34c870068011b0,0x128a4d29c01ac44,0x1a04720288945eb,0x9386508e181001c3,0x3a25092a04a8c400,0xa7746b50ee8d])) (bI j 114 (cB [0x94024f49803f0620,0xaf25788aa4a310ec,0xb50ed57025992dc4,0x7b004a8930a8aaab,0x96c08112a495025a,0x825d01444b63400,0x89746508e701]) (bI j 115 (cB [0xd101f9310539c35a,0xd6f574881e8a9053,0xb505557026d7ad84,0x18a539e04ea882ab,0x97d25a12f24b01fa,0x2c26249b84c09330,0x99929e131a5]) (cB [0x12d22161ca416c38,0x1d25009a989e133b,0x14e80d3aa22928d4,0x9282418c3807ecc4,0x985260130b102a0f,0xd02654a004c80280,0x9a526813400])))) (bI j 119 (bI j 117 (cB [0xca1a6702004ce028,0xd8940e99c6811338,0x11348d0026902004,0x1b44d432809a805,0x7f0c414e98d691d3,0x5d22361ca422c380,0x9bd8b6d36b1]) (bI j 118 (cB [0x982a23aaed42355c,0xe234c09c40981384,0xb0368c5018a00944,0x1a1853a33709cc63,0xb84c4055f0d3c2be,0x3834d32106126320,0xd792585a699]) (cB [0x4fc39549b070c933,0x5ac382e852961d0a,0x61edb0fc3c861c87,0x62797b6c4b0fd188,0x19e8a201bd10bf4,0x4042d7a78810f4b1,0x301a4a2601c9]))) (bI j 120 (cB [0xfc27e61c84e8c38,0xc4b0a258861403,0xa1473d10a8962795,0x7a78524f4b0a45e8,0xa464a2547494029c,0x2c2777a284eaf442,0x9f5e9e13c3d]) (bI j 121 (cB [0x940a7792894eb250,0xf664009e468013b4,0x13d313027c92c04,0x92804f8f4809e868,0xa0406853fd57027f,0xe0288aae05083340,0xa0e4a014130]) (cB [0x94028661c050a036,0xe6400a0c680143c,0x8146d57028a4a405,0x62a05192500a2d25,0x9fde8a13abd1028c,0x40a8d7a79510f4b0,0xa424a2147c9]))))) (bI j 127 (bI j 124 (bI j 123 (cB [0x5702777a204ed250,0x303400a4c0805485,0x814dc96027861c05,0x626052894309e525,0x9e925814bbd10295,0x82967a6052cc380,0x9ed25814c81]) (cB [0xe02950200534f44,0x36f4809f587013e3,0x15630e029e49e05,0x92b85612510aba4a,0xabaab815cc96c2b1,0xc29f496156155d2,0x2a8529e150a5])) (bI j 125 (cB [0xd142a47a20544c38,0x56f4f0a9de961533,0x85534944aa492805,0x7a215412500a81e8,0xa81870551c9402a3,0x2a59280546f440,0xaaa4b015425]) (bI j 126 (cB [0xd202a94a00552c4c,0x5b2500a898781553,0x151bd20aadaae05,0xaae055af440a9189,0xa99890152bd502af,0xf02b51a6056404c0,0xadaac8153a4]) (cB [0x1302b47ac056694e,0x6e9540aa927815a0,0x155a4f02b819405,0x92a0578f600ae92c,0xade4a815d8ca02b6,0x402bd0200570f480,0xafcc640c580])))) (bI j 130 (bI j 128 (cB [0xe42d961c059e948,0xbcc5b0b718ae16db,0xb16cd5722bf7ab05,0x18e031e0108b6eab,0xb31eac16425202c0,0xc42c1310059d55c0,0xb10c9e16118]) (bI j 129 (cB [0x702c7928058ac4a,0x92f4a0b180681618,0x16519002cb92805,0x18e458a040064002,0xb2529016699002c5,0x702ca31803220100,0xb1cc500c90c]) (cB [0x4b02c83190596c54,0xa494f0b4926e1682,0x616ab0e42d361c45,0x7a505b0c4f0b5989,0xb564a3169c9422c8,0xe22d192805a2c388,0x8b2de94168b0]))) (bI j 131 (cB [0xc702d749a05a9250,0x9cf560b4d8900c98,0x80ca18a02daaae45,0x62a032a31c0b51ea,0xb740680cb00402d5,0x402d64aa45ba3340,0xb612900cb80]) (bI j 132 (cB [0xca22df93005be960,0xdcc390b898701700,0x617bb10c2f261f85,0x7a215eec4f2bc989,0xbfde9617f3d142fb,0x44afb928060ef4f0,0xb8c07e57f49]) (cB [0xd142e47a215c604b,0xd8f4f0b9de961733,0x5734944ae492805,0x92c05d06400b964a,0xba4c80174b1302ea,0x202ed62a05d6c480,0xbade901753d]))))))) (bI j 155 (bI j 144 (bI j 138 (bI j 135 (bI j 134 (cB [0x940aef7ad05def4e,0xe0c482bc6ab8178c,0x17b55702f319a05,0x32005eb2500bd187,0xbbd87017c25202f5,0x402f061c05f555c0,0xbe58a817cc9]) (cB [0xd2c2f17a285c8f44,0xf92502be9e9e57b3,0x8172c9402fd92885,0x1a015fb55c0b99e8,0xc11882173b0e0300,0x302e8496060b2580,0xc0de88180b1])) (bI j 136 (cB [0xd3030261c05d292c,0xc9480c046801813,0x8175b0e02ea61c06,0x7a405d8c380c212a,0xc19e90176b0e0305,0x7609d18a03560120,0xafc6861850c]) (bI j 137 (cB [0x4d031e496157e34f,0x7294b0ce527e194a,0x61a03d1433d7a216,0x9280698f4f0d05e9,0x6b00205a04944b3d,0xb0ac01a705803420,0xc3525a185a4]) (cB [0x52c3124a1861c93f,0x28f442c4929e5872,0xe18bbd2c3167a286,0x92896292500c75e9,0xb04c840d68c70b16,0x4030c7a2158264e0,0x6b8c5058649])))) (bI j 141 (bI j 139 (cB [0xa01b0008035e31c,0x22c4c0b086981878,0x18819002c302006,0x8062002806c402,0xc4cc905620d681b2,0x701b3008062293c0,0x2b1cc9c0da0c]) (bI j 140 (cB [0x8a03159280618c38,0x6e01006d86380da9,0x818d0d0031802003,0x4a0158a3580b1469,0xb1806818e496031b,0x40319626158c04c0,0x6e40200dc00]) (cB [0xd201ba0080632040,0x42f450c7de8818e3,0x1943d3c3227a586,0x92816432512c7e4a,0xc952801918d00320,0x30324626064f2580,0xc9068019331]))) (bI j 142 (cB [0xe03277a4064c940,0x5cc3f0cb58721953,0xa5953d1033862186,0x7a28656f442cb5e8,0xcbc068596494032c,0x3377a606666340,0xcc987019825]) (bI j 143 (cB [0x500331620066292c,0x6a92c0cd987019a2,0x819800d033562006,0x4a0066ec3c0cd0c6,0xcee4a019e557033a,0x801bb18f0676c4c0,0xc50c5303b98]) (cB [0x10031f61c159c64f,0x7d2502cf18961953,0x80de18a833f92886,0x7a2062a93581c125,0xcb1e98195bd30320,0xa607b310037a31e0,0xc8587018b18]))))) (bI j 149 (bI j 146 (bI j 145 (cB [0x48b3faae065ac40,0x1c3140d080800df0,0xa1a30d0431718ec1,0x32015983590b3069,0xcb926819124b0347,0x4608600406972580,0x8b1406a18c00]) (cB [0x8a0323310558a04d,0x8af440d0d8981979,0x18c804608200406,0x61c06606280c90c4,0xcc9268198a4d0344,0x701bf0080688f4c0,0xc6cc9818d0c])) (bI j 147 (cB [0xcd608f18a0380012,0x9a34d0c6c6821668,0x819998a032531015,0x90694f440d2189,0xc98c410460c501c1,0xd034961c06686280,0xcd926819aa4]) (bI j 148 (cB [0x1001c20090692f4c,0x3831d822c6281a18,0x8193a4b034832006,0x18a03860120cdd26,0xca125818e8c76094,0xb034b7a406709340,0xd4925a1a724]) (cB [0x9403594a786ac94b,0x9e04b0d764a21ae4,0x41a8c94435092806,0x7aa06ab55c0d4d8b,0xd612581ab80a0354,0xb035a7aa06a692c0,0xd6de881aa24])))) (bI j 152 (bI j 150 (cB [0xe035561c86a0c38,0xbec380c792641a8b,0x61b6b0fc36a61c86,0x62796dac4b0dd588,0xde9e8a1bbbd10b75,0x403857a786f6f4b0,0x2dea4a25bbc9]) (bI j 151 (cB [0xd10b6002586c003f,0xc8f4b0d8de8a1b0b,0x25b0c9403697a786,0x1a006c52502d8e4a,0xda24b01b31900365,0x2036732006cec4c0,0xdade9c1b43d]) (cB [0x57036c92816d6f5a,0xe03340db80685b65,0x41b7c940374aae06,0x92806e4c380dc4c6,0xdccc801b78d00373,0xf8376aae06d6c380,0xd85e8818fb0]))) (bI j 153 (cB [0xd3cb747a586d8f45,0xf32510de24a05bb3,0xc1b149403207a506,0xaae06c6f440c8587,0xdf46801be0100b79,0x436461c06449320,0xe124b01c1b1]) (bI j 154 (cB [0x8f832331306ca92c,0xc4c0d992581bf1,0xc1bfb1303827a207,0x49606fe6320c90c4,0xe05e981c0b0e0367,0xe032749907003400,0xca12641b430]) (cB [0x1283847a406d2c38,0x172502e1d8ac1c3b,0x61c7495c38d92887,0xaae971755c0e524b,0xe2aab81c43100b8d,0x583897a607132500,0xe32ab85c53d])))))) (bI j 166 (bI j 160 (bI j 157 (bI j 156 (cB [0x5903914a6071e04c,0x24f580e41eb01c9d,0x81c9253039002607,0x7a206526240e4e4a,0xe69e961ccbd14396,0x44b969280740f4f0,0xca92605ccc9]) (cB [0xf0398928872f250,0x5a9300cb1878195b,0x81cd8100b98aae06,0x18c073f2580cb8c4,0xe79e881ce313032f,0x9039d61c06603180,0xcc8c4819898])) (bI j 158 (cB [0x89039c020073af4c,0x3ef480ce0c4819b9,0xc1d1250833931f07,0x7a28748f440e1d87,0xea9eb61d3bd5c3a6,0xc03acaae875755c0,0xe2126019d18]) (bI j 159 (cB [0xf033b49e074755c,0x500400e96ab81c4b,0xc19e25283a94a007,0x9280714f4a0e8d89,0xec007e1d700cc3a5,0x801c418f176004b0,0x9d0c5304f18]) (cB [0x4b0ad932785b2643,0x9c94e0d392841712,0x61d230fc35f61c16,0x7a28764f442e9189,0xf11e9e1db3d2c3b5,0x40bb592897652500,0x2ebeab81d7c9])))) (bI j 163 (bI j 161 (cB [0xd10b4f62d05c6c38,0x5e33f0ec6ab81b03,0x80e298a8bb11a587,0x4a784ea93581e125,0xd4189c17230e0ada,0x40ba57a586c2f442,0xed24a21d9c9]) (bI j 162 (cB [0x10607161c038c936,0xc52500b95e8813b3,0xb03e24b01c731506,0x62d05ccc3809dd26,0xed2ab81b1bd10b51,0x803b71a0039031e2,0x9e0c5304818]) (cB [0x9662ce326877c641,0xc8c380b9d2595671,0xb0438c503c092c06,0x1a6c58e33509e463,0xee0c7c1741882ac7,0x103ba62606cc92c0,0xee58981debd]))) (bI j 164 (cB [0x88027a18ec106314,0xce92c0ee4c641749,0x81de30e03bb49e86,0x314039231c0ef1e9,0x72863c1dfb12027b,0xa608d31007743400,0xba925813e18]) (bI j 165 (cB [0x1243c162406d0c38,0x846358228c401e1b,0xc1dd8d302eb49607,0x314c12a620072c63,0xda587017624b027d,0x203c762a878ac540,0x824cc401e03d]) (cB [0xd202ed496078c635,0x872540f09e901e0b,0xe60c783c901907,0x32084fc629827cc4,0xb6ccb616d993c2ac,0x683524a705dc92c2,0xda98705a925]))))) (bI j 172 (bI j 169 (bI j 167 (cB [0xd38ba662b874cc4b,0xa32502f2deb41e5b,0x61ea495c3d392887,0xaae97a355c0f664b,0xf2aab81e54940bd3,0xe0b534ad05de92c2,0xf318901b5b0]) (bI j 168 (cB [0x4b03d0aae079ec49,0x9d2500f358701782,0x41e50cf83ce7aa07,0x49ac0f292c0734c5,0xbc5870156a53427f,0x6836c7a216aac5a0,0xf4aab85e849]) (cB [0xd603d7ab207aa34c,0xb0c540f586981eb3,0x81ebc9503da63007,0x1a039c0120f624a,0xa0063b04b0c503dc,0x80adc1ad87d83350,0x2d58cb417918]))) (bI j 170 (cB [0x570ba74ab86da92c,0x2e0080fceaba1f95,0xe1ee80dc281008c1,0x19905e63142b7409,0xdc0c405ab8d383df,0xe43e261c175064b0,0xf958961f230]) (bI j 171 (cB [0x9443ea92807d2c4f,0x320080f786601f5c,0x1ef00d43e0008c1,0x18a07c32500dc4c4,0xbd0c401410c76098,0x4037249616b064e0,0xf980681f1c9]) (cB [0xd03e74a607d0f58,0xe83140fa18901f38,0xc17a988028318ed0,0x7a206e692c0f84c7,0xfb40840e780403e3,0xf2add1ad050831c0,0xfc1e881f724])))) (bI j 175 (bI j 173 (cB [0x94028500807e355c,0xc62807406381f7c,0x14398a01d118e05,0x1a003a431e0fbd89,0xa20c5343998803ea,0xe02f649607e26410,0xfac6801ba30]) (bI j 174 (cB [0xc7609a18a03a6012,0xee6202b786b61448,0x1baa4b0b5932d05,0x4ab87fe9490fd529,0x6ab81e5b0e0baa,0xa609b18a080555d1,0xfe46561fb0c]) (cB [0x4b02f831015be34f,0x98c380ff129e1fd2,0xc1ff49443fd92807,0x92807ee92c2b8069,0xf3587104e18803f8,0xd687631007f72500,0xbe52581fc18]))) (bI j 176 (cB [0xd103ce7a207f6c38,0xa831e1002ab81e7b,0x814698a687531003,0x62a06ecc380be925,0xf41e8820031543fd,0x801d518f07fcc540,0xa38c5303718]) (bI j 177 (cB [0x4b2ad9327855c643,0xb894e0cf527c17da,0x41c5b0fc37761c16,0x7a21756c4b0e5988,0xfc9e961e8bd143b2,0x444049281802f4f2,0x758c54202c9]) (cB [0x53c28f49ac0de92c,0x7cc4a0bf1870157a,0xc1c63d2c3787a206,0x92887672500e5de9,0x1c92580eb98a83d2,0x282fd61c05209358,0xde5e8819fb1]))))))))) (bI j 267 (bI j 222 (bI j 200 (bI j 189 (bI j 183 (bI j 180 (bI j 179 (cB [0xc783b49280730f4e,0x2262981e8c400ec0,0x956d996c2b032185,0x4ad068093e0bf925,0xe3587e1bd30e0b5d,0x10bac62b8732c420,0xf4de8a1dabd]) (cB [0x570c027ad97e6f57,0xb2012101eaba602d,0xb03e8c5040902003,0x1a085623370a4863,0xafc6b315f8d34422,0xb034131905fe620a,0xe392661bda4])) (bI j 181 (cB [0xe43b661c0734936,0x5125810998821ea3,0x6149804607e00408,0x21c5800350ac805,0xc00629560013440a,0x8040e19f06843260,0xe3cc4e1be98]) (bI j 182 (cB [0x4b43b7496073662a,0x32943104927e1eaa,0xa2103d1041b62608,0x4a0881633c1085e8,0x214010206b16040c,0x62c201a881e0118,0xab0809a20581]) (cB [0x1303b849606fc620,0x8604c8b0c068208b,0x3040802041062655,0x49606fe620104002,0x5989820980a43b9,0x604144a60830f581,0x105005220abd])))) (bI j 186 (bI j 184 (cB [0x100415014882ec4c,0x660290a5002220bb,0x220601062c401a85,0x62c082c93cab100b,0x1fc01020ba4c041a,0xdc2b4015852a0118,0xc0462820680]) (bI j 185 (cB [0x8804111990686326,0x3862a0e40c4e1c01,0xa1dd24b041c31e87,0x49b88309330f5925,0x7d87220f30e041a,0x5041d7a20776c381,0xa5863b0400c]) (cB [0x4b03443190604620,0x3a93d0e7526c1c0a,0xb0420c503bc61c08,0x1a6c5823410a5c63,0xd14c641819882ac1,0xe039e49b070492c0,0x1079e981deb0]))) (bI j 187 (cB [0x1381da008083ef58,0x6a3360a606382118,0x212252034631905,0x8084b2500ef987,0x76c6381dfb0e0299,0xb030431005346280,0x109d2901c1a4]) (bI j 188 (cB [0xc5041b02003b8012,0x6c3370a6c63b0440,0x81a598c830531005,0x49b07269330e1125,0xb1292214a52039f,0x503d761c8780c381,0x10a86530448c]) (cB [0xe0306310056e337,0x703360f618721e0b,0x81e130e042b49605,0x90786f44107009,0xa7063b0488c501dd,0xc830731005723370,0xe152581a618]))))) (bI j 194 (bI j 191 (bI j 190 (cB [0x5503a049b0728933,0x88c3810c52aa2172,0x82143d203d961c87,0x19b885e329824862,0xf1587018418802ba,0xd84297a407b4c390,0x10c125815d8c]) (cB [0xd2042a7a4078cc38,0x592540f1de88215b,0x62198c7e03218a08,0x1a7c4e633550cc65,0x1f4c422291882a9d,0x2c4ca31589246271,0x13d0c9e26f99])) (bI j 192 (cB [0x52d47d496a8a492c,0xfcc3853d129ea6fa,0x2281494050162709,0x31b0868620140e4a,0x129870220252043d,0x6c44d62b8898c391,0x90d1e88227b1]) (bI j 193 (cB [0x57644aaae487af5a,0x72c3810d52912265,0x821dbd6843a7a208,0x7a2086cc3810f2ab,0xd989021c4940437,0x1043862a086ec481,0x10f9eb521dbd]) (cB [0x4b0435310087f55c,0x8694f110d26e220a,0x622330e444461c48,0x7a20892c4f111d89,0x11a4a32224942435,0xb24429280884c389,0x110987021b24])))) (bI j 197 (bI j 195 (cB [0x4d04459284870f44,0x88c4810e52582242,0x921fbd6a43c7a208,0x62a088af54112eab,0x13866822700d0446,0x804494a4088e9549,0x91424c022825]) (bI j 196 (cB [0x12c45301388a2028,0x9462b8184c4022b8,0x9557193e28e31aa8,0x4a588c492d116d25,0x1dd870238a53c468,0x4447b92808f4c4e1,0x1151e8823e49]) (cB [0xd8456aae08aaf5a,0xb4f44116587022c0,0x6a2c812c45c00788,0x49ac0c492c116469,0x175871557a53e28f,0x4446092808bec4e1,0x80f1870230c9]))) (bI j 198 (cB [0xe204549608bd250,0xbcf4489d9883026b,0x2a1ca4d606349608,0x7a208c6c5a8a4128,0x19eab82333d68465,0x8046919408c8f541,0x11b8c5382d98]) (bI j 199 (cB [0xc504707a26510641,0xd492cca1c66b82d0,0x236b0e046b49888,0x624650664011b065,0x180c4023698d046f,0xe0463496651a635c,0x11d1ea823930]) (cB [0x8d705f31008e6f54,0xc892c11d4c839461,0x623b3d1047361c08,0x49608b434b115066,0xab529fa1e24de03b,0x2c46561c88bac38a,0x11c989e23831])))))) (bI j 211 (bI j 205 (bI j 202 (bI j 201 (cB [0xe047992888f1250,0xaa0271179e8901ab,0x9a1f98ae04431008,0x19988cc92d117d25,0x12d26f02624b0456,0xe446061c44ea9415,0x11e1e88233b0]) (cB [0xe227f4a0c0aa92c,0xc862011e5e88230b,0x2a2618dc434314c0,0x49b556065b8a44c8,0x189870241a56847e,0x6c48962b8910c395,0x1235e88245b1])) (bI j 203 (cB [0x574490aae091ef5a,0xf4411fd258248d,0x824155704817ad09,0x7aa0908c38518d25,0x191258242bd50486,0x4877a2090ac385,0x122866823fb1]) (bI j 204 (cB [0x4d603d4960919260,0x8c5a120188421d2,0x24755714657a209,0x49b08766298118c4,0x139258a3330e0481,0xa2774a688789358,0x519de8824131]) (cB [0xc5049300e091d250,0x2434112a463b0328,0x825ca4d2ab11adc5,0xaae098ef5a1315e8,0x198010264d5744c8,0x3e29801a892801f8,0x1254c4155a81])))) (bI j 208 (bI j 206 (cB [0x92c49a3188932621,0x48c38128cc9e2509,0x2253c9404a662709,0x18a453204012a24a,0x25987114d0cd6069,0x20498928092ec4e1,0x126c03903380]) (bI j 207 (cB [0x94049f326093c01d,0x3af441270c402504,0x824e8ca206800409,0x496407e314128803,0x120010252c940496,0x605018a092e6208,0x126125913d8d]) (cB [0xd004a57a2094093d,0x54634aac86b51498,0x258a5044b049609,0x7a2096895b12c929,0x2e2ab825bbd684b6,0x82ab41a7452a3341,0x12b0c6a25598]))) (bI j 209 (cB [0x9404ae627095ac38,0xf46408a58c68257c,0x4255a4d229732044,0x9280958634aacc6b,0x2d64c114a0d004b3,0x304ae31a095a9401,0x12bd28113c99]) (bI j 210 (cB [0xc7606a18a0966c54,0x6c34f8a6c66a2550,0x25f252c4ba49655,0x9280984c4e130187,0x2ed87026249444c3,0xa04bd9280978c4e1,0x8100c4025f80]) (cB [0x9404bb61c095a629,0x5c31d8124628260c,0x302898804bc49609,0x61c44f864112bcc5,0x290650260bd104bd,0x4b6314c07c6201,0x131aab826031]))))) (bI j 216 (bI j 213 (bI j 212 (cB [0x704c17a6094a634,0x6e31d811c6282530,0x2538ca04c249a09,0x3268970629813cc4,0x31a4a0261b102278,0x504c462009503281,0x10f463b0358c]) (cB [0xd6e29c1a0a87a329,0x7262411f8c4155c8,0x265b0e147e49609,0x7a209b0c57133d89,0x376ab826e3d684da,0x104ba49809bd55d1,0x1335eb42663d])) (bI j 214 (cB [0x4c04bb61e099d55c,0xd831412f587825e2,0x955e0d3c4d019ac0,0x92889ad2501351e8,0x34587155e8d384d7,0x804d392809a4f441,0x1348c8302118]) (bI j 215 (cB [0x90605331009ab250,0xb203413564a02699,0x25f8c604be31209,0x31ac8766298104c4,0x30126024024b343b,0x204cc7a22900c381,0x136eab826a3d]) (cB [0xc504d592a0982c3c,0x7c32910f863b0250,0x8261189048131028,0x310099ac38520525,0xfcc6a21f98a6052,0xc048249644fa64d5,0x5209870261a4])))) (bI j 219 (bI j 217 (cB [0x9404d67aa099cf44,0xaef54131126026dc,0xb02b0c504e000e09,0x1a0a89a33713b063,0x1a187027898da280,0x204f37a22912c395,0x138403f02b80]) (bI j 218 (cB [0x88228401aa89c02b,0xca6271390c422711,0x827398c44e631589,0x61c291492d51a525,0x16462914281004eb,0xe146a496450c3358,0x8160010271b0]) (cB [0xe04ea00e89d001c,0xd892c13a4c40a35b,0x271a4b203818a28,0x1a0689c33651b587,0x3b9282276a4b2281,0x1146e61c09de9481,0x8a08c802783d]))) (bI j 220 (cB [0xca04f27a228dec38,0xe062980dcc402758,0x8a383d104f24a109,0x19aa89e32b817062,0x1c52582419882289,0x504f561c291692d5,0x80e4c4027c3d]) (bI j 221 (cB [0xd5147261c090892c,0xee64180e8c4027b3,0x8a39b0e048549609,0x19ae8a032b817462,0x3ec68627c8d0628a,0xb5474496090c6201,0x13f1286a4624]) (cB [0xca84fd7a209ecc38,0xeec3851d5259a288,0x302f18804fa7a209,0x61c090e92c8a2cc8,0xd0c570199881476,0xb2aac327e8686379,0x123525a23ba4]))))))) (bI j 244 (bI j 233 (bI j 227 (bI j 224 (bI j 223 (cB [0x52c4da49b898a933,0xeec3813d529e279a,0xea79b12d48d61ca8,0x92889ff25053d589,0xe526f01a24b0500,0xe447861c68729439,0x131987e24730]) (cB [0xd154787a209b6c43,0xf2c3880d9258a473,0xf0218c514797a208,0x310687a32b90f463,0x31cc4e247988447a,0xb547a49609b862b1,0x812cc40a47a4])) (bI j 225 (cB [0x90744a31bc89462b,0x2092d11ed25913a1,0x26ea4dc4c849989,0x7a22920c3951ed87,0x130c5702a18804ff,0xb227e320e8986379,0x124525a23e24]) (bI j 226 (cB [0xe04de49b8992933,0xf445245872a3e3,0xe29200cc5050138a,0x18f8140314349007,0x14866e9d68cac1fd,0xae17731018a43431,0x900cc6fa8118]) (cB [0x4b45494965806643,0x3093715f52662b52,0x6cc250cd7d49f8b,0x61f8b42c39167987,0x679e882e3310c5a5,0x850600f1b42f453,0x344409c28881])))) (bI j 230 (bI j 228 (cB [0x93c4533218142620,0x32f451451e886299,0x2913d3c51b7a58a,0x3101a3325134524a,0x42de8a284bd10507,0x405107a78a18f4b1,0x342e4a2684c9]) (bI j 229 (cB [0x4b0d089280a10f44,0x1a340142a4a02842,0x287313050f92c0a,0x9280a1ef48143868,0x454096289c944512,0xb0d121a70a1232a1,0x315929e05124]) (cB [0x705189288a2f250,0x46c381428c6c28b0,0x86898d6850b19501,0x92d08a894d029125,0x43003c68c557051a,0x40a53100a380401,0x147d88028e99]))) (bI j 231 (cB [0x700a618a0a41258,0x1c01c1479eb02868,0x28780780a73100a,0x9280a3c64102a0c4,0x2a4c402880078521,0x10c5532688aa6410,0x1481e9028d3d]) (bI j 232 (cB [0x950523aae1a35250,0x62036149403c290c,0xe05518805340270a,0x61c18ae64f4ec0c6,0x4fd89629e30e4537,0x445459280a86c4f1,0x1498c402a449]) (cB [0x12c52b61c8a52c38,0x5f25014b989e2963,0x293b0e05309288a,0x9280a4e92c14a24a,0x4a12582968cd052a,0x3c0ab18a0a54f441,0x14ca4a062c0d]))))) (bI j 238 (bI j 235 (bI j 234 (cB [0x4b00ac3100a67251,0x7004b14d925a29aa,0x829a8d385291950a,0x92818b294f02b525,0x4e403829dc94453a,0xa80ae61c0a546361,0x14d86b42958c]) (cB [0xd692e34a0815e92c,0x5801e14faab829eb,0xa058188054001a0a,0x18a0a84c4c1504c6,0x4b803c29680700b1,0xe1b4f31a81646201,0x15124a029eb0])) (bI j 236 (cB [0xd0852f1950a8c03f,0x6294302cd2582990,0x829f3d1453a7a227,0x1a10a6032a151c03,0x1692b205a24b0533,0x3c5447ac8a76f443,0x54dc0662a500]) (bI j 237 (cB [0xcfc537199ba6e03f,0xfc62b02d4c4069b8,0x862d990c45b31b83,0x4a1c80893785e125,0x55d8722a8b0e2c04,0x105666218ab6c3f1,0x355de8a6a8bd]) (cB [0x53c45c4a1816c92c,0x9af45152de8862e2,0x2a83d3c54e7a58a,0x61c1a9b251352e4a,0x53e4b02a649400b7,0x6c5520078a9ef481,0x945c07eaa900])))) (bI j 241 (bI j 239 (cB [0x8fdd3a19f8a9631b,0xfe93702e125869d1,0x7069b0e0c604a183,0x7a28aaaf44aecd88,0x5524a02a98138556,0x9cd5400dca9800f1,0x1550636eaa00]) (bI j 240 (cB [0xe054c313aaa8327,0x72f44080188605cb,0x862f31340ba61c41,0x18dd5caf4d8311e8,0x4ecc96e9d8d2c54d,0x420149b817692c3,0x318529e22ea5]) (cB [0x13e2fc620c1ecc38,0xad2501561e9d5e93,0x907130e055a9289a,0x78ab32581565e8,0x808c5605e188054e,0xd61364960ab86350,0x8cf92822b024]))) (bI j 242 (cB [0x8a85627a6567c94d,0x2a93584592581019,0x82aeb132b154a6c6,0x496040862a157de8,0x579e982af30e2108,0x10205314817a6201,0x153c01e2b0bd]) (bI j 243 (cB [0x88156319f8ac603f,0xba6350818c5605f1,0x9195a50612a4960a,0x61c0aca0361591e8,0x59c0962a8003e120,0xac0bf3102ace34b1,0x117cc6a10398]) (cB [0x53614c49618be641,0xc4c3c15618711cba,0x2b44940d587a20a,0x61c0ad2036158de9,0x595e902b23d22144,0x80d3c1a58a7833f1,0x820c5606018])))))) (bI j 255 (bI j 249 (bI j 246 (bI j 245 (cB [0x93c462321a5c4635,0xfe93585e52586311,0x5602a53e4054a1e9,0x7a21ad6c4e15ad88,0x5d5e962b9bd14570,0x44d709280af6f4f1,0x34f46966b9c9]) (cB [0xe0c633278182620,0xdf25115ba4a02b63,0x806124b056d9280a,0x258ae201b15b5e8,0x30d25869f192e518,0x3d2e44a084129370,0x8351870633a5])) (bI j 247 (cB [0xd3abb4627e8f0c41,0xe5251955a4a06b73,0x2062a4b0d6d92c0a,0x61c08ca94d4b9928,0xbf589ba4731060f7,0x68d6f7ad0ad8f4c8,0x35caab82ba49]) (bI j 248 (cB [0x9052e731a818c620,0x8c93584dd2582bb1,0x319fa5345784a0e9,0x31a0af3258acfd2b,0xba4c682bbbd612e8,0xd40c7310694a9344,0x15dcc8297518]) (cB [0x5374c149ac25692c,0x9062015ea4a11962,0xa23319052ec31a81,0x49ac29a92c3198c9,0x5d1e891cc25674db,0x70d749280af2f481,0x15ea4a82be55])))) (bI j 252 (bI j 250 (cB [0xc7c0c918a1a7e04b,0xd034f15f86521050,0xe2c598a716e31018,0x9280b2694eefc8c9,0x5fc0662cbc944594,0x3820b18f1a8204b1,0xc598c406348d]) (bI j 251 (cB [0xe3bf13278b00637,0x8c4b160d8722c0b,0x22c4c9405886278b,0x327041862a162a4a,0x60a4a18ac24b0c6a,0x6058531a18d63581,0x31b06982c3bd]) (cB [0x12058631a0b0c94c,0x9892c0834c542c3b,0x863699605827a271,0x19b841c31d032862,0xfa8c9c6370d3c58c,0x2c58e61c8b1ac38e,0x164589e2c7b1]))) (bI j 253 (cB [0x880592928fb13250,0xc694e083cc520659,0x1df09963d8292877,0x4ac0b20c481641eb,0x5a4c406a100f7af5,0xac0cd3100b2a00fc,0x1624c6a10818]) (bI j 254 (cB [0x103d8949af19a92c,0x146350338c402cb0,0xbc7924b0c7032c8b,0x25f5ec959164926,0x84463e0678c50d43,0x80c711a7a69c3290,0xcd70c6b8ba98]) (cB [0xe056b496780264f,0x3b251166e4a02ccb,0xf87624b0d441a58b,0x9280ad8c38ef4129,0x67001e2cd4947d6e,0xd421231581a06201,0xe3412589a818]))))) (bI j 261 (bI j 258 (bI j 256 (cB [0xd1056e61c66a0941,0xa26350344c41eb73,0x3c7a24b0c7232ca6,0x61c75f4959cd5528,0x67c01e2cd3d1056f,0xce51401fea8a0331,0x351467e28a0c]) (bI j 257 (cB [0x8dc21331581a4620,0xa492c31ecc869d91,0x15d9250f47b49bc1,0x61f8ae0c39154587,0x545e886cdb10cd94,0x385a00214ae0f459,0x5549e892d001]) (cB [0xd3cd957a58ae2f45,0xe3251b54a4a06ce3,0x628c8cced539284a,0x31581aa620352069,0x1dcc829da98dc214,0xde0f549618f864f1,0x8bed283a4824]))) (bI j 259 (cB [0xe455761c57a294f,0x2ec4b16658822b9b,0x2d13d38d9d6279b,0x1998b49251b5c24a,0x20926f070a4b051a,0x1057461c8ab0c38d,0x83818702d1bd]) (bI j 260 (cB [0x5340d64960ab2f44,0xdec3831e52b223ca,0x9578b1662f1626c1,0x7ac8b34f4d1569e8,0x46c04e2d1c960d9a,0xac21518f81ae3141,0x169866a9db0c]) (cB [0x8d74c8315c26a620,0x7a64d8cf4c822db1,0xa2baa4b455b49656,0x138b80f4c16fd26,0x85863c2d380fc51d,0xae115310276e32a0,0x8c50c6ba5c18])))) (bI j 264 (bI j 262 (cB [0x4b2b143268b52643,0x5693f15d925a2ae2,0x82d8b1305af4a18b,0x7ac0b6af4516d1e8,0xee06682d531605a8,0x305ae7ac0b58c4c4,0x4ee46682d6b1]) (bI j 263 (cB [0x1605ac49e0b5ac40,0x3c02716b52602d83,0x410b8c785a80198a,0x315c20e6204ee865,0x5752582d518df4af,0xdc5ae4998aee92d1,0x16c98702d824]) (cB [0x8d82183150b66c39,0xbcc3884092589de1,0x89de98d82193150a,0x4a6c618941844125,0x6c9e982afb0e2b0c,0x740d818a0b66f581,0x4ef865610d0c]))) (bI j 265 (cB [0x4b34a73150b6e343,0x7093f15e125a2b02,0xa2debd105bc4a18b,0x31a0b7232816f9e8,0x2746382ddb1334a0,0xf05ba1940b74640d,0x364c402dda4]) (bI j 266 (cB [0xe349849b0436629,0xb4314147c04a2b0b,0x82e080fc52001381,0x195843831f036c62,0x4a4c402d88cd53c0,0xb232a320e98662b8,0x15e525a2b124]) (cB [0xe05c47a20b8493f,0x86629c4a0c40ab1b,0x82908ccc5c50150b,0x61c697a937847d25,0x5958702bd30e4564,0x505c70258a440271,0x87463e06e0c])))))))) (bI j 312 (bI j 289 (bI j 278 (bI j 272 (bI j 269 (bI j 268 (cB [0xd0447a19aa78832b,0xba62b852cc4063d0,0xa2b324b2396326e9,0x61c0b9094b15ed25,0x689e882e030f05a2,0x2156761c0b952503,0xc528c402e0bd]) (cB [0xd205c27a40b92629,0x46333172c0542e1b,0x1a6724de1434960a,0x7a40af8c3915a187,0x715e902b4b0e05c4,0xa421e18f81ba3141,0x4f2066e1708c])) (bI j 270 (cB [0x880c7d1a788fa343,0x663793f8c530bd1,0xd603193e406321ea,0x4a70bb8942173526,0x7bd872ab530e0ddc,0x2c5fc6218be8c3f1,0x37f189e6fa31]) (bI j 271 (cB [0xd2c5fe7a2cb42f44,0x432501835e9e2ffb,0x606f0c50dfe928db,0x49618fc34f11f868,0x74de8b2d13d105ce,0x405da7a78baaf4b1,0x374e4a36d149]) (cB [0x93c47f32181be620,0x9ef45968de8863f9,0x2e93d3c5d07a58b,0x92c1b9f251b68e4a,0x38cc402e8bd205d1,0x685cf61c090064d0,0xb5d2ab82ea49])))) (bI j 275 (bI j 273 (cB [0x4b05d61a081c8314,0xaef5817624b02e82,0x82eb8d040e518a0b,0x18a0bb3250174525,0x20469a2408d040e6,0x205d47a20ba492c3,0x37524a02ec3d]) (bI j 274 (cB [0xc505d992a0bb755c,0x634f4f2c6560738,0x62eea4b556b49619,0x61c0bca94f178529,0x7ba4a36ccc9405ed,0x692ef31a81d06201,0x1781e882ef31]) (cB [0xc505df7aa5b3555c,0xc8f4417886520748,0x20750c505e36240b,0x61c0bbc92c6d4c65,0x7b24a02f43d505e6,0xa40eb18a0bcef541,0x17a4682daa0c]))) (bI j 276 (cB [0xd105e761c0bbe92c,0xd725417ae4a02f53,0x62f030e556c61c0b,0x9280bccc4f179189,0x3b4c412f04946d6c,0x6556f61c19086590,0x9781e882f631]) (bI j 277 (cB [0x8d421f31581dc620,0x1064f4bb8c821771,0xb0bda4b0c8832d89,0x4a7ea00941940126,0x739881603a56e407,0x38ddd62d0bbac4e1,0x7775eb4aeebd]) (cB [0x95c5f0928cb49250,0x4955c17ce4b62f8c,0x2e7bd30df0aaedb,0x6202bc12581781eb,0x7458802f955905d0,0x505f292a0ba4c401,0x88063e0780c]))))) (bI j 283 (bI j 280 (bI j 279 (cB [0xd6c5f519a85e4329,0xe6629c5bcc406448,0x5df9996c5f831ac9,0xaae0bf4c5a37852b,0x88463c2fdd577d97,0x80c8a1ad05e63280,0x93c0c538b398]) (cB [0xd10de24ad0bec942,0xe8634f64aab82fbb,0x1110c740f118a05,0x7a277d665a93acc5,0x38d269ec555705f9,0x924f2314e2d46209,0x3cc6286f231])) (bI j 281 (cB [0xcd42f7194844631f,0xec620322c6b69a90,0x79ae99064f5314e2,0x61c1bca95af008cb,0x676ab9af73d115dd,0x80de66320bfb55df,0x890c5607c18]) (bI j 282 (cB [0x9353d332185fc635,0xf092c3244cb62469,0xba48a50e48d49ac1,0x62157a695b8bf929,0x7b98b42f6b1305d3,0x345f07a2aae6f443,0x37edeafaf73d]) (cB [0x5725d392d1bfaf5b,0xf231497c2abb6b9d,0xe17f8ca422518f81,0x3100c003414f5066,0x324c6f26298a6138,0x663403268c0c641d,0x175526d5a019])))) (bI j 286 (bI j 284 (cB [0x1045f161caaeac38,0x4c31e18264b03043,0x9ea8cd830019404,0x320c96c629845cc4,0x75926d58b1966316,0x6157661c0c0294e1,0x18164a0301bd]) (bI j 285 (cB [0xca022718f0c04c58,0x126204f5866c1808,0x42eba4da4ad314c2,0x7a22aeec38180928,0xc0cc6818118d0604,0x740fa18a0c092580,0x9290c501140c]) (cB [0x94157861c6950636,0xf63149259268303c,0xe07e0c5030419481,0x19b860a32908a463,0x4b0c403018d053d7,0x374c431bc9806298,0x176126d19699]))) (bI j 287 (cB [0x12c5f261caaf2c38,0x1802a182e4a03053,0x525da4d61214960c,0x18a2af4f44176588,0xc1c6521150c7c0fd,0x3448f1a0a7b23370,0x8538c406478d]) (bI j 288 (cB [0x9674de31bc9b4629,0xf6c38176926d1cc9,0x8307315c5f361caa,0x9280c12f48974de8,0x82a4a8307d572dd3,0xd61454960c2002a1,0x176d88526624]) (cB [0x95060b92a2af8f44,0x5601303f80103064,0xa18480a461200e84,0x2789240434c2406,0x91063b0be0c50c92,0xac081a7c8103431,0x3a24c9c34499])))))) (bI j 300 (bI j 294 (bI j 291 (bI j 290 (cB [0xd165a57a20d14934,0x70f4f1ac9e972ffb,0x56ffc946da59280d,0x27092604208b002,0x84c6570be8c50c93,0xb2c221a7c8443431,0x188d25a30da4]) (cB [0x52c6314a18c4c93f,0x6cf4438c529e7132,0xe31abd2e6067a2cb,0x928db6d250190de9,0x2500b424a013ae06,0xb2c231ad484634e3,0x185529430a24])) (bI j 292 (cB [0x568e154ab0c3094e,0x6f250186987070c2,0x30b0ca2db7aae4b,0x1f8c33254185d2b,0x8b463c70e012c61c,0x80c951a7092a3420,0x9094c870c218]) (bI j 293 (cB [0xd165bd7a2584a64f,0x44f4f1879e97303b,0x9703c946dbd9280c,0x92c0c3e340187403,0x8806803103130621,0x20c971a6092e3401,0x8b863c310bd]) (cB [0x880c991ad093234e,0x48c4e1850c6b0c29,0x92df4940e2462d0c,0x90c4b254b6faab,0x2840b424d013022f,0xa462719442fc3143,0x185466a3160c])))) (bI j 297 (bI j 295 (cB [0x5706306260c5c958,0x3604018a00556dc5,0x30b18a8ca202709,0x9280c5692c18a4c8,0x6e9e883151882db9,0x4062a4a00938340b,0x127809811800]) (bI j 296 (cB [0x4862d4a60c2c328,0xfe314127c0801188,0x8317a500617194c2,0x1944302314860062,0x8bd2983168ca4629,0x682320095b772501,0x860862865181]) (cB [0x4f06244960c30329,0x6925418c92b43182,0x4319bd52dbcaae0c,0x194c30631408cc02,0x8d0024312a4b0619,0x613a18a0c6c0400,0x8d1869a31d0d]))) (bI j 298 (cB [0x50061e496568c359,0x85258190128231da,0xb18d00d61190040c,0x6260c3e620ac6809,0x42c01031cbd10637,0x3063861c0c406208,0x8d402031c3d]) (bI j 299 (cB [0xcd611a18a046c012,0x78c4cac6c69b18d8,0x811b804863f7a20c,0x61e8c7ac38843062,0x905eb031ebd3063e,0x5063702004700121,0x18852590970c]) (cB [0x486414a08c78940,0x4c04c129808011c8,0x31124b215018a19,0x881fe0081909e9,0x914056185007423a,0x3c4a9021a6140351,0x902468465481]))))) (bI j 306 (bI j 303 (bI j 301 (cB [0x4b064e31a581234e,0xea93f19cd25a336a,0xe73aa52c67c4a18c,0x7a2cb4cf4439f129,0xa1de9e3413d2e600,0x3ae00928db4d2501,0xb0286b52050d]) (bI j 302 (cB [0x52864a4960c8c640,0x96956193129c325a,0x326b0e0e4c4ad1c,0x1a15b5355c96a64a,0x91cc416068d3a40d,0xb0e483270c906421,0x96a9e88324a4]) (cB [0xd306474a05b55250,0x90634b0306b52058,0x208000206494a00c,0x1b8c8c01f08ec02,0x6c66c655010c4aa,0x8464f31058363429,0x195cc6632a98]))) (bI j 304 (cB [0x90ce5731f8cbc637,0x6c3996c587072f1,0x8335b10c66561fcc,0x19dc06f45b6c5e8,0x40462872800fc650,0xc4ab19b847831d0,0x9078c6c6558d]) (bI j 305 (cB [0xe65b261c583c642,0xa8c43194987f3023,0x17023d16db27a20c,0x3204c70634194405,0x94de995a21932344,0xf239d32646626401,0x40c628329b0]) (cB [0x908647194847a31d,0xac942b07cc9d20f9,0x12d9bd10e564a70c,0x88208008b6ce4a,0x4468032c007423e,0x65a327583034e9,0xb6ba4a032da5])))) (bI j 309 (bI j 307 (cB [0x902c151a74820340,0x7e011041401032c9,0x560b8d0865900e84,0x7a20cbac38197126,0x9000220830022dad,0x384ac01a8c9001d0,0x1958c4160d0d]) (bI j 308 (cB [0x4f865f3270cb6630,0xc4f449809870330a,0x16d849406647a70c,0xe0cb8630198189,0x42801032ea4f0663,0xd066601a84820110,0x8d0c68131b8c]) (cB [0x8d0652310568634c,0xd2f4c19a0c6b31e1,0x918c8cd02420080c,0x80ccec4cac6469,0x9100220868020243,0x823301a00cce0350,0x19a9e8832998]))) (bI j 310 (cB [0xd4245008821c008,0x3834c32b80822570,0x332193465431047,0x7a20cd2c3c975d87,0x9a9e903364942dd7,0x50e6e0258cdc03f1,0x91863a0878c]) (bI j 311 (cB [0xd0d30b19a8616329,0x4064232c069e2580,0x8327a4d2c2032748,0x7a5cc0af4596d1e8,0x6d24a03393d3c670,0x66f0145c0b251b,0x194526832831]) (cB [0x9623453264c72640,0xe325819492695a29,0x329a4d23323260c,0x7a40ca89348e78cb,0x91c63a0888c50671,0x464a19a861a3290,0x9084c9c9868d]))))))) (bI j 334 (bI j 323 (bI j 317 (bI j 314 (bI j 313 (cB [0x1386554a0584265a,0x6b25039d18b433a3,0x32b24d2db5aae4b,0xe8490011044801,0x92c06a33b00a430e,0x6a40e1a6261c0411,0x195cc816090d]) (cB [0x5706796260cf095a,0x1e0400c3c0396d5d,0x16098d6a40f1a626,0xe0cee94c1960c8,0x5069c98800d0310,0x2065a31a0cb2634b,0x92402208980])) (bI j 315 (cB [0xd4677014862201d,0xb6634b05869c9888,0x33dbd2c67a7a20c,0x40cba940b6b24a,0xc4803a1250044114,0x531201a8c980290,0x32d00b625881]) (bI j 316 (cB [0x4b065e31a583235a,0xfa95a19e527833a2,0xe33f49426017a20c,0xaae0d0325a1a024a,0x8cdea832f98a2daf,0x206624a00cfe01c9,0x198cc6833d31]) (cB [0x2066431a0cf693c,0x2e01d092c02208c0,0x341810531701a86,0x1ac468434c98d868,0x9c125833298d2b42,0x606844a0cc769401,0x930020342c9])))) (bI j 320 (bI j 318 (cB [0xd0131801a063001c,0xcc634ac606b118c0,0x33418d26667ac0c,0xe849a011046c01,0x99808298e00d431c,0xb066931a465e34c9,0x1a1a4a0338a4]) (bI j 319 (cB [0x4411c0040cd4940,0x3a0350c7403a1270,0x65b81344b7020a6,0x4960cd66348e6c6b,0x759e88340a564672,0x72dd69280d0af489,0x19b128034455]) (cB [0xd3e18618a0d0d254,0x11251b6fe4a16130,0x2127804c11d0045c,0x2189720370ca405,0x93863b0c38c50cb9,0xb2c281a1c8503371,0x1a71266345a4]))) (bI j 321 (cB [0xe65c061c1d3893f,0x5cc431a8187f304b,0x5704bd16dc07a20d,0x19b823c3141a3002,0x71187065d0d0c4ba,0xc69261fcc16c399,0xb711e8834d31]) (bI j 322 (cB [0xe65c561c5c16f45,0x22c431a3587f3063,0x97063d16dc57a20d,0x4a00d20f4c1a3926,0xa41878347a4d068f,0xd412218a0d1a0121,0x1a4d2693430c]) (cB [0xc5068e0090d30f4c,0x2ec381a512800918,0x80920c5068f0090d,0x6200d2cc381a5525,0x4946283480048695,0x1069449a4cd43350,0x1a5988034cbd]))))) (bI j 328 (bI j 325 (bI j 324 (cB [0xcd412618a0d22012,0xb2c3832f068225e0,0x16ecbd1069861e4b,0x40d32f481a6e4a,0x2f809e34e80a4127,0x46dc29280d3e94e3,0x32fc09d70549]) (cB [0x22dc39280d3cc38,0x5c02909400260968,0xb09f8c5268501a86,0x1a0cc84335199463,0xa84c695a58d3634b,0x206ac7a60d2492c1,0x94402609780])) (bI j 326 (cB [0xc506a201b866601d,0x783358d2065309e0,0x15a40d046a419bcc,0x61c0d4a9401a4cc4,0xa8d298355b0e46a9,0x4c1300044d4694c1,0xcd003a12900]) (bI j 327 (cB [0xcae13018a0d4602b,0x286208cd066b3518,0xa353a4b06a63198d,0x18a4d28c381aa125,0x4c4c4019a8ca4131,0xe0695496466a6358,0x1aa803d34ab0]) (cB [0x8803361948264314,0x926418d24c6b09e9,0x8353b10069749656,0x982660081aa189,0x9a406a19b80a4253,0x466918ec2663149,0x1a94c6919b8d])))) (bI j 331 (bI j 329 (cB [0xd106ad49f8d3092c,0x680081a98c8134c3,0xa19c00a425400982,0x18a1984041130806,0xe7c69a3358c76151,0xe06af4a58d3492c8,0x1ab18792ec30]) (bI j 330 (cB [0xd206b09285bb0f44,0x8e6201ac403c356b,0x34db0e066c314c2,0x44d20f489a61e9,0x8d403a12a804c139,0x534101a86820291,0x84e462934101]) (cB [0xd366351a08d0431d,0x66640ad046b31a08,0x135049606a049a0d,0xe84ac01304ec01,0x8ec0829a380a4347,0xd613b18a0d680431,0x98ec6831a38c]))) (bI j 332 (cB [0x8a2b471a6cd68343,0x6af449a858983509,0x35118a06b77a28d,0xf0d6c0129a918b,0xd2865209f0c526b6,0x613e31026943350,0xad28c9b1a519]) (bI j 333 (cB [0xd326a97a60d52934,0x56f581aad2693553,0xa12b804c1400044d,0x1a8698029190c03,0x31c09a263810534c,0x6468718ec29e3143,0x1ab92691cd0d]) (cB [0x9426a07a44baaf44,0x7401e1ae6ab96eac,0x34418a61463100d,0x6204d252541ac188,0x504011346c9506b1,0xc39501a84b00130,0x332809e26501])))))) (bI j 345 (bI j 339 (bI j 336 (bI j 335 (cB [0xca650118ec310314,0x5a34f90b4687a808,0x834518905cd31058,0x61f8d78c38573525,0x719e88760b12c6c1,0x3e6b87a5cc1af459,0xb71a4a0362bd]) (cB [0xc506bd0095c1b251,0x9634f132c6860a10,0xb2e53d1068b49819,0x7a7cd72f4b983de8,0x83e4a36e549406bf,0x165cb7a20d18930b,0x9ae9e973083d])) (bI j 337 (cB [0x946dcb9280d7cf4f,0x62f481a452617084,0x20a40c506be0094d,0x498199a34d133468,0xac1e912edbd1069a,0xf06c0aae5bb72509,0x9a6e4a834db0]) (bI j 338 (cB [0x16c6c201a8292008,0x88c5a1a70c4866c0,0x57075576dc8aae0d,0x7a20d3a62433640b,0xa792616e4d5706c3,0x4c1520040d3e6241,0xe8006a12c80]) (cB [0xc50cdc02689b8041,0xb8329937063b0a90,0x82ed18823a01ace9,0x61c2bb492c1ab8c4,0xb258ae36331506bf,0x426ae7a44bb4f441,0x9afeab96ed49])))) (bI j 342 (bI j 340 (cB [0xd425a00982a6008,0x8e335854c6283638,0x10aa0c5025b0094d,0x92a0d5e6241b2187,0x9700260aa80226af,0x3d3db01b8d9601d0,0x855462866f81]) (bI j 341 (cB [0xd3f4df19bcd9631d,0x64e1c00c6d5ed8,0x6afa30e557d61c4e,0x9280e06c4f1c0589,0x9740256fa4946d7d,0x50ce002727b80360,0x1b306570ab0c]) (cB [0x4b2bec1a7e9d8337,0xc29331b7925a36aa,0xe375252c6e649b8d,0x61caafcc381bd929,0xbf589e37bb12d5f5,0xadf8928db172501,0x33840b49ee81]))) (bI j 343 (cB [0x4f86cd49657da35a,0xa09561b3d2843672,0x836a30e06d34ad0d,0x205b1955c5601e8,0xb492803688ca13de,0x786d80258dac0331,0x4f8866c12f0c]) (bI j 344 (cB [0x8de15731019c434e,0x2c38afc0c9fa769,0xe36d312d5f761cab,0x928db1b2501b7189,0xb6403836b8072df9,0xd06dd02a0db63341,0x97c63cdac0c]) (cB [0x880ce41ad27c8342,0xbec421b34c6b0ac9,0x8ac1bd106e062d0d,0x2004c0012b63aab,0x57862867281693df,0x6ce19a8dc43298,0xb63eab837231]))))) (bI j 351 (bI j 348 (bI j 346 (cB [0x486e34a027c0040,0xc6329857c6281308,0x56c849406e561c0d,0x18a19cc05a098802,0x3b866a3678ca6160,0x686e44980dbe92cd,0x57d9870373a5]) (bI j 347 (cB [0x5706e97a20dd0c5a,0xc60121b958796c8d,0x867381613e502104,0x1948dd6328856862,0xbc92803680cd46f0,0x106f562c0de89421,0x1bb0054ac23d]) (cB [0x8a8ce802627cc036,0xde92c1bb4c983689,0x9f380a958561c0d,0x1a62b0c92c1bb8c4,0x9900203772530ce9,0x606d119419d40580,0x994024378a5]))) (bI j 349 (cB [0xe06d2194c2b6314,0xb83144fa006c379b,0x3788ca46ed19442,0x1b04cc012561d87,0xb4c6530ae8c513e9,0x206e749b0dc092c1,0x562187037aa5]) (bI j 350 (cB [0xc506f801a04ce012,0xb492c1be466b0b08,0x37e24d46fa49a0d,0x61c0db6620858801,0x9a40241340041edb,0x486fb61c42c63140,0x6d5c06813500]) (cB [0x4d46dc49642c8314,0xc4c381bf92a83742,0x37f8ca616518a3b,0x2782d0008778d87,0x7ea4a36c9c940cf1,0x7426b00982d6008b,0x7bdc06a37b80])))) (bI j 354 (bI j 352 (cB [0xcd66f718ec2d6314,0xd80081c08c69f7b8,0x837d00d426c00982,0x44df433585b062,0xbf403a136804c16d,0x7616d18a36ac0351,0xed5869b37e8c]) (bI j 353 (cB [0x23de19283bc2c38,0x9a01d09b80260b80,0x867a013d3f401586,0x19ae9e832b85c062,0x770c415fa0d3e34d,0x2d5fc496ab3092c1,0x1c1529ef81a5]) (cB [0x946d989284bb8c38,0xde01305c40116fe4,0x8dac80a435900e84,0x1a6c6b233585c462,0x7952582f29883b59,0x407067aa4bcac387,0x5c8011ef2c9]))) (bI j 355 (cB [0xa435a00e84e0013,0x120431c1c082dad0,0x31ad0cd617218a0e,0x1a6ce123439c1c68,0x7a12582f41883b5a,0x1470a7a24bd0c387,0xf7a24a03863d]) (bI j 356 (cB [0x88217318a04e2012,0x10f4477a52582f49,0x9385807870b0090e,0x19a86b632905d062,0xd6cc830ba1881b5b,0xe05ea49676b664d8,0x97a9e88ef530]) 0x7bd5250))))))))) 27 (i % 16)
set_option maxRecDepth 16000 in
def znD (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 56 (bI j 28 (bI j 14 (bI j 7 (bI j 3 (bI j 1 (cB [0xa00200400101f800,0x549600431000318,0x61c8057a200661c0,0x18057a600961f805,0x47a200c49680462,0x49b80492800e4998]) (bI j 2 (cB [0xc80461c004928010,0x47a601461f80461,0x61c8173108036218,0x281762181761f817,0x1792c01c7a58177a,0x49a01f3138037a78]) (cB [0x2231a02161f820,0x1f6218207a60214a,0x7a781f3200267a58,0xa02a7a7829315803,0x2d62582c31980362,0x31b80362782c31a0]))) (bI j 5 (bI j 4 (cB [0xf8027aa0314a7830,0x3561c03431003318,0x61f83461c8347a20,0x403a62183431a038,0x3492803c7a20344a,0x32003f7a58347a28]) (cB [0xa0427a783492c03f,0x457a204431b0334a,0x7a58447a28449280,0x784492c0481a0048,0x4d7a204c61c0337a,0x7a584c7a284c9280])) (bI j 6 (cB [0x784c92c050320050,0x5561c83362a0537a,0x19a05761f8339280,0x805861c058199058,0x5d621833aae05792,0x92805e49605e4a40]) (cB [0x80627a2033aae05d,0x337a283392886292,0x19f0671a00667a58,0xc0667a2067194068,0x24aa06c7a783392,0x49606f31006e19b8])))) (bI j 10 (bI j 8 (cB [0x686f928070625070,0x6f3140744a586f49,0x62506f7aa0764a78,0x86e92886f92806f,0x6eaae07b7ab07b31,0x19407f18e07e3138]) (bI j 9 (cB [0xf08019288018a080,0x7f31007f7a208049,0x92807f62507f3188,0x208a49e08949a07e,0x8931a08c6250897a,0x32008f7ab07e9280]) (cB [0x409231586eaae07e,0x927ab09292809362,0x18e09732586eaae0,0x786e318898310098,0x6e7a209c7aa09b32,0x92886e92806e6250]))) (bI j 12 (bI j 11 (cB [0x20a20138a1310002,0xa27a28a29280a37a,0x6200a60200a67a58,0x98a17a78a292c0a6,0xab9280ac01b0ab01,0x61c8ab9280ae61c0]) (cB [0x78ab01a0b16258ab,0xa19288ab9280ab62,0x7a20b70078b64960,0x28b97a20b961c0b6,0xbd61f8b661c8b67a,0x6218b67a60bd49a8])) (bI j 13 (cB [0x80c26210c14968a1,0xc19280c47a20c192,0x92c0c77a58c17a28,0x48ca4998a17a78c1,0xca9280cb61c0cb31,0x49b8a19288ca9280]) (cB [0xc0a19288d09280d0,0xa17a28d37a20d361,0x61f8a19288d661c8,0xa8d87a20d931a8d8,0x26218a17a60d849,0x4960df49b0de3108]))))) (bI j 21 (bI j 17 (bI j 15 (cB [0x80e27a20df7a20e0,0xe57a58df7a28df92,0x4a10de7a78df92c0,0x78e84a58e84968e8,0xe89280e87aa0eb4a,0x9280ef61c8de9288]) (bI j 16 (cB [0xe0f131a8f161f8de,0xdeaae0f46218deaa,0x9288f69280f67a20,0x8fa7a58de7a28de,0xde92c0fa6208fa32,0x18e8ff3138027a78]) (cB [0xc10231010131a100,0x531990131090161,0x61c10131b9014a01,0xf90161c9017a2108,0xb31a10b19a10b61,0x4961006219017a61]))) (bI j 19 (bI j 18 (cB [0xf9004969007a2110,0x4a190062611349,0x7a29009281167a21,0x1191a01197a5900,0xff7a790092c1194a,0x61c11f49611e49a0]) (cB [0xf91f61c91f7a2120,0x234a012449a12361,0x49991e62191f7a61,0x212a61c11e928128,0x1e61c91e7a292a7a,0x31a12e19a92e61f9])) (bI j 20 (cB [0xc1304961314a0130,0xff62191e7a612e61,0x9289369281367a20,0x93a7a58ff7a28ff,0x3d62613c32013a1a,0x92c13a7a213c61c1]) (cB [0xc1423158027a78ff,0x439281447a214361,0x92c1477a59437a29,0xe14a61f9427a7943,0x4c92814c7a2142aa,0x7a59427a29429289])))) (bI j 24 (bI j 22 (cB [0x794292c1501a0950,0x219a95462a1537a,0x49615718e9563198,0x9957496957928158,0x5762015b4ac15b49,0x62c15f4a595749b9]) (bI j 23 (cB [0xa1626259574a7957,0x6562795749a16219,0x9289579281574aa1,0x896992816931b156,0x5631a16c62595692,0x9289569281566279]) (cB [0xa1724a797131b802,0x717a21731a09737a,0x61c0029289719281,0xc8027a29787a2178,0x7d61f80292897b61,0x31a17f31f97e19a9]))) (bI j 26 (bI j 25 (cB [0x197e4a617f320180,0x7e7a217e4a418332,0x7a617d31a97d7a29,0x518a009801621802,0x8d00418c02118b01,0x19318c49618d1931]) (cB [0x819019a191625190,0x8c92819449618c92,0x4a798c4a598c4969,0xe19a31919918a18b,0x9a61c19b31019b18,0x7a219f61c1997a21])) (bI j 27 (cB [0xa1a261f99961c999,0xa57a219962199919,0x7a59997a29999281,0x799992c1a81a01a8,0xad00e1ac31918b7a,0x3109ad61c1ae3101]) (cB [0xb9ad4a01b13199ad,0xb561c1ad19e1b331,0x61f9ad61c9ad7a21,0x19ad7a61b831a1b8,0xac9281bc7a21ac62,0x201bf7a59ac7a29])))))) (bI j 42 (bI j 35 (bI j 31 (bI j 29 (cB [0xc1bf6261c13201bf,0xc561c18b7a79ac92,0x7a29c59281c67a21,0xc1c91a01c97a59c5,0xcd61c98b7a79c592,0x1a1cf61f98b9281]) (bI j 30 (cB [0xe1cf9281d061c1d0,0x8baae1d462198baa,0x9289d69281d67a21,0x1da7a598b7a298b,0x8b92c1da7a21db02,0x4961df31018a7a79]) (cB [0xc9e07a21e161c1e0,0xe431a1e461f9e061,0x7a21e06219e049a1,0x1ea7a59e07a29e0,0xea4a01ea6261eb32,0x4969df7a79e092c1]))) (bI j 33 (bI j 32 (cB [0x61f21941f14999df,0xf531a1f43141f149,0x6201f14961f43101,0x41fa49f9df49b9df,0x8a4a19df4961fb19,0x7a21ff61c1fe4961]) (cB [0x59ff7a29ff928200,0x36262043202037a,0x7a79ff92c2034a02,0xf9fe92820961c9fe,0xc61c20c19a20b61,0x61c20f31a20b9282])) (bI j 34 (cB [0xe2126219feaae20b,0xfe7a29fe7a21feaa,0x6262171a02167a59,0x2167a221761c218,0xfe92c2167a221b32,0x7a2a1f49698a7a79]) (cB [0x2211a02217a5a1f,0x1f928a1f7a7a1f32,0x7ac2271a622692ba,0xda1fab2226326226,0x2d01422c49998a92,0x49fa2d496a2d4962])))) (bI j 38 (bI j 36 (cB [0x1a2d4ac230014230,0x357a5a2d92a2334a,0x6262374a02350202,0x422c7a7a2d92c235,0x3c31023c31a23b19,0x4a023f319a3c310a]) (bI j 37 (cB [0xa24261fa3c31ba3c,0x3c7a62424a024301,0x496a3b49623b621a,0x1a3b62624949fa3b,0x4c02024c7a5a3b4a,0x62022c7a7a3b92c2]) (cB [0x62524a02517a5a50,0x2c7a7a5092c25162,0x92da2c4a625692ba,0x25a92da5949b98a,0x5d49f98a02025b7b,0x496a5e49625e0142]))) (bI j 40 (bI j 39 (cB [0xba5e620261499a5e,0x640142644a5a5e49,0x625a5e4a7a5e4a02,0x7a5e49a26801a268,0x5d4a026c7aba5d62,0x62da6f4a198a7ada]) (cB [0xf801026271930270,0x7561c27418ea7300,0x7a2a759282767a22,0x627a1a02797a5a75,0x7592c27932027962,0x92827f61ca747a7a])) (bI j 41 (cB [0xc28201a28161fa74,0x8519a28192828261,0x92828561c28501b2,0x428a621a74aae281,0x8a92828b49628b4a,0x92828f7a2274aae2]) (cB [0x5a747a2a74928a8f,0x944a1a940202937a,0x7a229461c2966262,0x22990212991a0293,0x737a7a7492c2937a,0x49629f49e29e19ba]))))) (bI j 49 (bI j 45 (bI j 43 (cB [0xc29f4a1a9f7a22a0,0xa57a229f7a22a361,0x7a5a9f7a2a9f9282,0xc2a86262a94a02a8,0xad61c29e7a7a9f92,0xaae2af92829e9282]) (bI j 44 (cB [0x62b292ba9e928a9e,0xb27ac2b34a72b302,0x4aa2b7ab22b21a62,0x2ba92da9e1942b8,0xbd7b02ba1942bb4b,0x3192bf1a1a730202]) (cB [0x8ac13102c118e2c0,0xc1327ac100e2c331,0x9282c101a2c66252,0x2ca7a52c94a42c0,0xcd7ab2c09282c932,0x4a42bfaae2c03202]))) (bI j 47 (bI j 46 (cB [0xbad061c2d14962d0,0xd09282d461c2d049,0x49a2d7625ad061ca,0xe2da61c2bf627ad0,0xdd62babf61cabfaa,0x4b02df62dabf01a2]) (cB [0xc2e23102731942e0,0xe57a22e301fae361,0x7a5ae37a2ae39282,0xc2e86262e93202e8,0xed7a7ae36242eb92,0x7a72ef61cae262a2])) (bI j 48 (cB [0xfae29282ef6242f0,0xf461c2f419a2f361,0x621ae2aae2f39282,0xe2f89282f94a42f8,0xfc9282fc7a22e2aa,0x7a5ae27a2ae2928a]) (cB [0xc3026263011a0300,0x620b007a230161,0x7a7ae24a430692c3,0xeb0a3192734aa308,0xb7a230c49630b18,0x1430f49fb0b496b])))) (bI j 52 (bI j 50 (cB [0x1b0b62630f320310,0x157a230b3243134a,0x7a5b0b7a2b0b9283,0x318626319020318,0xb92c3184a03181a,0x7a231f49630a7a7b]) (bI j 51 (cB [0x5b1f7a2b1f928320,0x236263241a03237a,0x92c3236263264a03,0xc32a49a30a7a7b1f,0x2a7a2b2b7a232b61,0x1a32f61fb2a61cb]) (cB [0xc3304963314a0330,0x354a033431a32f61,0x7a632f61c3344963,0x33a49fb0a621b2a,0xaaae33a92833b4a,0x928b3e92833e7a23]))) (bI j 54 (bI j 53 (cB [0x3427a5b0a7a2b0a,0x4361c34462634302,0x3203421a0b427a23,0x234861c349626348,0x737a7b0a92c3427a,0x25b4f49634e3212]) (cB [0x6b4e928b4f92834f,0x537aa35462d35349,0x143574a5b4eaae3,0xa35a4a7b4e496358,0x4e92834e7a235b7a,0x61c35f496273928b])) (bI j 55 (cB [0x83627a236001fb60,0x657a5b607a2b6092,0x6263673203651a03,0xcb5f7a7b6092c365,0x5f92836b7a736b61,0x92836f01a36e61fb]) (cB [0xc37131937119a36e,0x5faae36e92837161,0x7a235faae376621b,0x2b5f928b78928378,0x7c02037c7a5b5f7a,0x62637f31f37e1a03]))))))) (bI j 84 (bI j 70 (bI j 63 (bI j 59 (bI j 57 (cB [0x237e61c38162637e,0x5f92c37c620b7c7a,0x625387499a737a7b,0xe388928389620388,0x87aae38c928387aa,0x2638f92bb87928b]) (bI j 58 (cB [0xc3924a638f7ac390,0x7392db87ab238f7a,0x9283977a239649b2,0x5b967a2b96928b97,0x9d62639c02039b7a,0x92c39b7a239c61c3]) (cB [0x13a249fa737a7b96,0xa57a23a2aae3a34a,0x7abba27a2ba2aae3,0xdba24a03a80203a8,0x73aaeba2aae3a27a,0x9283af019bae61c2]))) (bI j 61 (bI j 60 (cB [0x23aeaae3b101fbae,0xae928bb39283b37a,0x1a03b77a5bae7a2b,0x63b86263b931f3b8,0xb861c3bb49ebbb62,0x6243bf320bb77a23]) (cB [0xabc26243c192c3b7,0xc57a7bae624bc131,0x62abc531abc662a3,0x83ca0193c961ca73,0xcd6243cc7a73c992,0x624bcc9283cd61c3])) (bI j 62 (cB [0xe3d29283c9aae3cc,0xd592bbc9928bc9aa,0xab23d57ac3d61a63,0x3da92dbc962a3d8,0xdd01a3dc61fa7363,0x1993dd1983de01bb]) (cB [0xc3dd9283e0008be0,0xdd61cbdd9283e361,0x4a63e701a3e6625b,0x83dd627bdd7ac3e6,0xed19abdc928bdd92,0x9283ef49e3ed0213])))) (bI j 66 (bI j 64 (cB [0xe3dcaae3ed7a23ed,0xf5621a73aaebdcaa,0x4963f7194bf64a43,0x63f6195bf69283f7,0xf64a7bf69283fb49,0x4a4bf5928bf69283]) (bI j 65 (cB [0xebf5aae3f5aae400,0x49284047a2273aa,0xaaec077a2a73928c,0x1c0a0204097a5a73,0xb4a0c0b19e40b02,0x8c0f19f40a62c4]) (cB [0xfc0a62640f626410,0x144a6414014c1349,0x6264176264137ac4,0xc41a4a1c0a7ac413,0x1d31ec1c62640a62,0x61cc1c61c41c7a24]))) (bI j 68 (bI j 67 (cB [0xc097a2c0a7a240a,0x234a44230274231a,0x4a4427620c099284,0x4c2a4a442992c409,0x734a4c2949642b19,0x194c2f4aa42e7a7a]) (cB [0xb8014aac2e496430,0x3531043418fc3301,0x7a243661c4364a44,0x243561c435928436,0x34aae4357ad4357a,0xaae43e7ad43e31b4])) (bI j 69 (cB [0xc4424964414a4434,0x4561c44149bc4161,0x625c4161cc419284,0xc434627c4149a448,0x3461cc34aae44b61,0x62dc3401a44e62bc]) (cB [0x4330144514b0450,0x547a2454013c5331,0x25c53aae4547ad4,0x245861c45801b458,0x5c007c5c4964537a,0x62745c92845e61c4]))))) (bI j 77 (bI j 73 (bI j 71 (cB [0x6c53928c5c92845c,0x637aa46462d46349,0xaae4637ad4637a24,0x646a1944694a5c53,0x6a19446c498c6a49,0x62446f314c6961c4]) (bI j 72 (cB [0xc4724a7c537a2469,0x757aa4727aa47361,0x61c4537a2475320c,0x7453928c78928478,0x33928c5392845362,0x49647f49b47e310c]) (cB [0xe47f7ad47f7a247f,0x8561c4844ad47eaa,0x7a24877aa4847aa4,0xa48a62bc7e61cc7e,0x7e93048c62dc7e19,0x7ad47eaae48e7a24]))) (bI j 75 (bI j 74 (cB [0x3c33aaec7eaae47e,0x9400fc9400e49331,0x62749661c4963104,0x8c94310c94928496,0x9c31049c00e49b31,0x32649b00ec9b7a24]) (cB [0xe4a2325c9492849b,0xa561c494327c9400,0x9284946274949284,0xa4aa18ec93928c94,0xab31acab3104ab31,0x9284ab6274ab61c4])) (bI j 76 (cB [0x44aa4a0caa4964aa,0xb54adcaa9284b34a,0x7ad4aa7a24aa9304,0x64ba49a493aae4aa,0xbb6274bb61c4bb49,0x144bf4a5cba9284]) (cB [0x74ba9284c161c4ba,0x93928cba9284ba62,0x7ad493aae4c67a24,0x5c33aaec93aae493,0xcc7a24cc61c4cb31,0x6244cbaae4cc7ad4])))) (bI j 80 (bI j 78 (cB [0x24d161c4d119acd0,0xd57a24d09284d17a,0x928cd09284d09284,0x24cb01a4d962bccb,0xcb7ad4cbaae4db7a,0x325c33aaeccbaae4]) (bI j 79 (cB [0x4e100fce100e4e0,0xe1310ce161c4e331,0x318ce1315ce1313c,0xece83104e900e4e8,0xed18ece061c4e100,0x4a44ed4a0ced4964]) (cB [0x24f231b4e07a24ed,0xf5327c337a24e07a,0x320cf77aa4f661c4,0x24fa1a0cf97aa4f5,0xf94a1cf91a1cf97a,0x9284ff61c4337a24]))) (bI j 82 (bI j 81 (cB [0x8433627433928cff,0x5310001928c3392,0x31050700f506013d,0x850a7a25077a2508,0xd7a5d077a2d0792,0x92c50d62650e1a05]) (cB [0x85120215067a7d07,0x157a2506928d1292,0x92851500e516025d,0xd51a7a2d06928d15,0x1c02051c7a5d0692,0x62051c7ac51e320d])) (bI j 83 (cB [0x7d0692852192c51c,0x25019d05aae5237a,0x61c52731052600f5,0x852a61c526928527,0x2d625d2661cd2692,0x928526627d2619a5]) (cB [0x853201b525928d26,0x35027525928d3292,0x61c525496d354965,0x853800e539025d38,0x3d61cd25928d3892,0x625d25aae53d7ad5])))))) (bI j 98 (bI j 91 (bI j 87 (bI j 85 (cB [0x654031ad4001a540,0x25928544627d2562,0xe54701fd469285,0x7d4a496505928d25,0x4b92854c7a254b00,0x92c54f7a5d4b7a2d]) (bI j 86 (cB [0x7d5261c54a7a7d4b,0x5292855302755300,0x61cd4a7a2d527a25,0x8d587a25597a7558,0x5d31ad5c61fd4a92,0x7a255d61c55e6265]) (cB [0x655c7a256149ad5c,0x657a256301fd637a,0x25d67621d4a01b5,0x6d0501b569928567,0x6d61c56c62156b49,0x928d6c92856c9285]))) (bI j 89 (bI j 88 (cB [0x8d7100dd717a256b,0x6b92d5747a2d6b92,0x7ac577320d767a5d,0x857a92c5764a0d76,0x5aae57c7a7d6b92,0x19d7f194d7e499d]) (cB [0x858261c57f31bd7f,0x85625d7f61cd7f92,0x7ac5854a658631a5,0x8d7f92857f627d7f,0x8c19bd8c314d7e92,0x625d8c61cd8c61c5])) (bI j 90 (cB [0x8d8c627d8c7ac590,0x9592857e4a757e92,0x928d7e020596007d,0x8d9a61c59949bd05,0x99007d9c92859992,0x7d9f61c505928d]) (cB [0x75a261cd050215a0,0x5928da27a25a37a,0x1fda719ada661fd,0xc5aa321da77ac5a8,0xad6265ac49fda762,0x4a1da77ac5ac6265])))) (bI j 94 (bI j 92 (cB [0xc5b26265a762c5b0,0xa77a25a761cdb261,0x1a1db731ada67a2d,0x5ba1945b949fdb7,0xb74a1db76265b932,0x49ada67a2db77a25]) (bI j 93 (cB [0xfdc101fdc17a65a6,0xc57a25c1314dc349,0x25dc7621d050155,0x85c7314dc94a5dc7,0xcd3108010155cb92,0x7a2dcf4965ce49b5]) (cB [0x7dcf92c5d17a5dcf,0xce92d5d47a2dce7a,0x7ac5d71a0dd67a5d,0x7dce9285d992c5d6,0xdd4a15cdaae5db7a,0x7aa5df62d5de496d]))) (bI j 96 (bI j 95 (cB [0x4de24a5ddd7a25de,0xdd7a25e26245e319,0x7aa5e761c5e64a7d,0x25e91a0de97aa5e6,0xdd9285e69285e97a,0x61cdcd928ddd61c5]) (cB [0x25f292bdf0928df0,0xf561fdcd92ddf0ab,0x7a25f64a15f619ad,0xd5f57a25f931adf5,0xfd621dcdaaedf562,0x7a5dcd7a2dcdaaed])) (bI j 97 (cB [0xc6024a76011a0e00,0x17a26047ac60162,0x928607320e009286,0x5e0a92c600620e00,0xcd01560c92860a62,0xaae60e62be0e7a7d]) (cB [0xee12313801015610,0x14496614195e1300,0x4ac6161946164a56,0xc61492a6194a7614,0x1d01fe1c49661361,0x1a061f7a5e1c00e6]))))) (bI j 105 (bI j 101 (bI j 99 (cB [0x7e1c92c61f626620,0x25627624496e137a,0x19462749fe1392a6,0x62a320628015628,0x2d194e2749662831,0x4a062f4ac6274a66]) (bI j 100 (cB [0xd6324a1e13626627,0x1392a6327aa6334a,0x6266370206367a5e,0xe367a263761c638,0x3d62663c4a06361a,0x7a263c61ee3d61c6]) (cB [0xc6367ac6414a0e36,0x4518ee127a7e1392,0x310647320646015e,0x6646496647321647,0x464a76464a564649,0x31064f31a64561c6]))) (bI j 103 (bI j 102 (cB [0xfe50014651019e50,0x4f621e507a665361,0x319e4f4a1656310e,0x765832065900ee58,0x5c49965c4a065832,0x32765f31be4f61c6]) (cB [0x265f49f65f624660,0x4f7a765f00e6637a,0x62666701ae6661fe,0x266a7a666631ae66,0x4592866c621e4f7a,0x1466f01fe6e4966])) (bI j 104 (cB [0x7e6e92c6717a5e6e,0x45627674496e457a,0x4a6677014e7649fe,0x267a6266764ad676,0x7d4a1e457a5e7a7a,0xe67f92867d4ad6]) (cB [0x5e4592d67d92be7d,0x834a0e83020e837a,0x7a7e4592868692c6,0xa612321612aae688,0x8d00968c49668b49,0x4a068f49a68e61fe])))) (bI j 109 (bI j 107 (bI j 106 (cB [0xfe8c621e8d7a668e,0x954a069449a69361,0x61c69461c6954966,0x1e8c7a26997a6693,0x9d499e8b92869b62,0x4a769d61c69e014e]) (cB [0xbea231a6a161fe8b,0xa219bea24a66a301,0x4966a6319ea64a06,0xf6aa61c6a2496ea6,0xad7a66a161cea200,0x4a5eaf621e8b49fe])) (bI j 108 (cB [0x5e1200f6b19286af,0xb4021eb43206b37a,0x7a2eb40096b67a26,0xf6baaae6b97a7e12,0xbd61c6bc31580100,0x7a7ebd7a7ebe0096]) (cB [0xaec261febcaae6c0,0xbc62d6c27a26c301,0x1aec762a6c67a7e,0x980162bec661c6c8,0xcd195ecc00eecb31,0x4a16cd49f6cd4966]))) (bI j 111 (bI j 110 (cB [0x6d11946d14ab6cd,0xcc61c6cd4ad6cd4a,0xe6d7019ed64966,0x5ed600e6d9025ed6,0xdd627ed619a6db62,0x6216df496ecc02a6]) (cB [0x4ee2499ecc62d6df,0xe56206e24a06e319,0x4ad6e749becc61c6,0x5ecc7a26e762d6e7,0xec0156ec1946eb4a,0x4966ec3106ee3266])) (bI j 112 (cB [0x6eb4ac6f1194eeb,0xeb4a16eb61c6f34a,0x625ecc4a7ecc62c6,0xa6f819aef801a6f8,0xcc49aef861c6fb49,0x194eff4aa6fe627e]) (cB [0xa702625ecb31b6cb,0x531b801627ecb31,0x20f077aa7064a7f,0x2707021f077a2708,0x7a2f0700970b7a])))))))) 24 (i % 16)
def zma := pageLinks znB zpo 5 13 11 6
def zjD (i : Nat) : Nat × Nat :=
  let e := znD i
  (e &&& 2047,e >>> 11)
def zvJ : Nat × Nat := (zxw,96)
def zpa := zac zcj 96 (zA zdd zsW ztY 96) 12 zjD
set_option maxRecDepth 16000 in
def zuw (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 9 (bI j 4 (bI j 2 (bI j 1 (cB [0xffff,0xf0f0f0f,0xff00ff00,0xffffffff,0xff000000ff,0x33300000333,0x50500550555,0x55505550555,0xf0f00000f0f,0xf0f00ff0fff,0xfff0fff0fff,0x111103031313,0x33330f0f3f3f,0x333333333333,0x555500ff55ff,0x55550f0f5f5f]) (cB [0x555555555555,0xffff00000000,0xffff0000ffff,0x3111300031113,0x5000500055555,0x5005500050055,0x5005500ff00ff,0x5005505055555,0x5555500055555,0xf000f000f000f,0x33333300333333,0x55005555555555,0x55555500555555,0xfa00fa00fa00fa,0xff000000ff0000,0xff00ff00000000])) (bI j 3 (cB [0xff00ff00ff0000,0xff00ff00ff00ff,0x101010101013333,0x101013301010133,0x101111101011111,0x101111133333333,0x101333311113333,0x111011101110111,0x111333301113333,0x303030333333333,0x30303ff030303ff,0x303333303033333,0x303575703035757,0x333000003330000,0x333033303330333,0x500550005005500]) (cB [0x505050505050505,0x505050555555555,0x50505ff050505ff,0x505373705053737,0x505555500000000,0x505555505005500,0x505555505055555,0x537053705370537,0x555000005550000,0x555055505550555,0xf000f000f000f00,0xf00ffff0f000f00,0xf0a0a0a0f0a0a0a,0xf0f00000f0f0000,0xf0f0000ff0fff00,0xf0f0a0a0a0a0a0a]))) (bI j 6 (bI j 5 (cB [0xf0f0f0f00000000,0xf0f0f0f0f0f0000,0xf0f0f0f0f0f0f0f,0xfff00ff0f0f0000,0x1111111111111111,0x3333333333333333,0x5050555550505555,0x5055505550555055,0x5555555555555555,0xaaaaaaaaaaaaaaaa,0xaaaaafafaaffafff,0xaaaaafffafffafff,0xaaafaaafaaafaaaf,0xafaaafaaafaaafaa,0xafaaffaaafaaffaa,0xafafaaaaafafaaaa]) (cB [0xafafffffaaaaaaaa,0xafffaaaaafffaaaa,0xcccccccccccccccc,0xccccccccccccffff,0xcccccfffcccccfff,0xcccccfffcfffcfff,0xcfffcccccfffcccc,0xeeeeeeeeeeeeeeee,0xf000f000f000f000,0xf0a0a0a0f0a0a0a0,0xf0c0c0c0f0c0c0c0,0xf0f00000f0f00000,0xf0f0a0a0a0a0a0a0,0xf0f0c0c0c0c0c0c0,0xf0f0f0f000000000,0xf0f0f0f0f0f0f0f0])) (bI j 7 (cB [0xfa00aa00fa00aa00,0xfa00fa00aa00aa00,0xfa00fa00fa00fa00,0xfaaa0000faaa0000,0xfaaafaaa00000000,0xfaaafaaafaaafaaa,0xfac8c8c8fac8c8c8,0xfac8fac8fac8fac8,0xfafa0000aaaa0000,0xfafa0000fafa0000,0xfafaaaaa00000000,0xfafaaaaafa00aa00,0xfafaaaaafafaaaaa,0xfafac8c8c8c8c8c8,0xfafac8c8fafac8c8,0xfafaf8c8fafaf8c8]) (bI j 8 (cB [0xfafafa00fa00fa00,0xfafafa00fafafa00,0xfafafafaaaaaaaaa,0xfafafafafa00fa00,0xfafafafafafa0000,0xfafafafafafafafa,0xfc00cc00fc00cc00,0xfccc0000fccc0000,0xfccca888fccca888,0xfcccfcccfcccfccc,0xfcecececfcececec,0xfcfc0000cccc0000,0xfcfca8a8cccc8888,0xfcfca8a8fcfca8a8,0xfcfccccc00000000,0xfcfcccccfc00cc00]) (cB [0xfcfcccccfcfccccc,0xfcfcecececececec,0xfcfcfc00fcfcfc00,0xfcfcfcfccccccccc,0xfcfcfcfcfc00fc00,0xfcfcfcfcfcfc0000,0xfcfcfcfcfcfcfcfc,0xfecceeccfecceecc,0xfeeeaaaafeeeaaaa,0xfeeeccccfeeecccc,0xfeeeeeeefeeeeeee,0xfeeefeeecccccccc,0xfeeefeeefeeefeee,0xfefecccceeeecccc,0xfefeeeeecccccccc,0xfefeeeeeeeeeeeee]))))) (bI j 13 (bI j 11 (bI j 10 (cB [0xfefeeeeefecceecc,0xfefeeeeefefeeeee,0xfefefeccfefefecc,0xfefefefeeeeeeeee,0xfefefefefeaafeaa,0xfefefefefeccfecc,0xfefefefefefecccc,0xff000000ff000000,0xff000000ff0f0f0f,0xff00aa00aa00aa00,0xff00cc00cc00cc00,0xff00fc00fc00fc00,0xff00ff0000000000,0xff00ff00ff000000,0xff00ff00ff00ff00,0xff00ff0fff00ff0f]) (cB [0xff050505ff050505,0xff0fff000f0f0000,0xff0fff00ff0fff00,0xff0fff0fff00ff00,0xffaa0000aaaa0000,0xffaaaaaa00000000,0xffaaaaaaffaaaaaa,0xffaaeeaaeeaaeeaa,0xffaaf0a0aaaaa0a0,0xffaaffaaaaaaaaaa,0xffccaa88cccc8888,0xffcccccc00000000,0xffccccccffcccccc,0xffcceecceecceecc,0xffccffcccccccccc,0xffccffccffcc0000])) (bI j 12 (cB [0xffccffccffcccccc,0xffccffccffccffcc,0xffeecccceeeecccc,0xffeeeeeecccccccc,0xffeeeeeeffeeeeee,0xffeeffeeffeeaaaa,0xfff00000fff00000,0xfff0aaa0fff0aaa0,0xfff0ccc0fff0ccc0,0xfff0fcc0fff0fcc0,0xfff0ff00f0f00000,0xfff0ff00fff0ff00,0xfff0ffc0ffc0ffc0,0xfff0fff000000000,0xfff0fff0ff00ff00,0xfff0fff0fff00000]) (cB [0xfff0fff0fff0fff0,0xfffaaaaafffaaaaa,0xfffafafafffafafa,0xfffaff00fafa0000,0xfffaff00fffaff00,0xfffaffaafafaaaaa,0xfffaffaaff00ff00,0xfffaffaafffaffaa,0xfffaffc8fafac8c8,0xfffaffc8fffaffc8,0xfffafffaaaaaaaaa,0xfffafffaffaaffaa,0xfffafffafffaaaaa,0xfffafffafffafffa,0xfffceeecfffceeec,0xfffcffa8fcfca8a8]))) (bI j 15 (bI j 14 (cB [0xfffcffa8fffcffa8,0xfffcffccfcfccccc,0xfffcffccfffcffcc,0xfffcfffcfffccccc,0xffff000000000000,0xffff0000ffff0000,0xffff050505050505,0xffff0f000f000f00,0xffff0f00ffff0f00,0xffffaaaaaaaaaaaa,0xffffaaaaf0f0a0a0,0xffffaaaafccca888,0xffffaaaaff00aa00,0xffffaaaaffffaaaa,0xffffcccccccccccc,0xffffccccf0f0c0c0]) (cB [0xffffccccff00cc00,0xffffccccffffcccc,0xffffeeeeeeeeeeee,0xffffeeeefcfcecec,0xffffeeeeffcceecc,0xfffff000f000f000,0xfffff000fffff000,0xfffff0f0f0f0f0f0,0xfffff0f0ff00f000,0xfffff0f0fffff0f0,0xfffffa00fa00fa00,0xfffffaaa00000000,0xfffffaaafaaa0000,0xfffffaaafaaafaaa,0xfffffaaafffffaaa,0xfffffac8fac8fac8])) (bI j 16 (cB [0xfffffac8fffffac8,0xfffffafafafafafa,0xfffffafaffaafaaa,0xfffffccc00000000,0xfffffcccfcccfccc,0xfffffcccfffffccc,0xfffffcfcfcfcfcfc,0xfffffcfcffccfccc,0xfffffcfcffffcccc,0xffffff00ff00ff00,0xffffff00ffff0000,0xffffff00ffffff00,0xffffffaaffaaffaa,0xffffffaafff0ffa0,0xffffffccffccffcc,0xffffffff00000000]) (bI j 17 (cB [0xffffffff000000ff,0xffffffff0f0f0000,0xfffffffff0f0f0f0,0xfffffffffaaa0000,0xfffffffffaaafaaa,0xfffffffffafaaaaa,0xfffffffffafafa00,0xfffffffffc00cc00,0xfffffffffccc0000,0xfffffffffcccfccc,0xfffffffffcfccccc,0xffffffffff000000,0xffffffffff00ff00,0xffffffffffaaaaaa,0xffffffffffcccccc,0xfffffffffff00000]) (cB [0xffffffffffff0000,0xfffffffffffffccc])))))) 64 (i % 16)
set_option maxRecDepth 16000 in
def zkl (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 56 (bI j 28 (bI j 14 (bI j 7 (bI j 3 (bI j 1 (cB [0x3fc,0x127eb,0x2491bca,0x492310f89,0x92462188b08,0x1248c431104e07,0x2491886220981006,0x1248c431104f07,0x35492462188b07,0x88b5492462188806,0x44492462188b07,0x92462188b88,0x1248c431104e87,0x130492310f88,0x26092462181187,0x1f8492310f88]) (bI j 2 (cB [0x3f092462181187,0x92462184e88,0x92462184f88,0x1aa492310f88,0x445aa492310c87,0x222492310f88,0x492310fc9,0x92462188bc8,0x130492310fc8,0x1f8492310fc8,0x92462184fc8,0x1aa492310fc8,0x445aa492310cc7,0x222492310fc8,0x592491bc9,0x182592491b08]) (cB [0x35582592491b07,0x1ccc12491b06,0x445ccc12491805,0x88b5582592491806,0x44582592491b07,0x1aa592491bc8,0xe62491bc7,0x222592491bc8,0xc12491bc9,0x222c12491bc8,0xc02491bc7,0x5c2491bc9,0x13a5c2491bc8,0xbb2491bc7,0x21a5c2491bc8,0xea2491bc9]))) (bI j 5 (bI j 4 (cB [0x21aea2491bc8,0xe92491bc7,0x43927ea,0x872490fa9,0x10e492188b28,0x21c92431104e27,0x10e492188ba8,0x130872490fa8,0x15a872490f87,0x1f8872490fa8,0x832490fa7,0x10e492184ea8,0x21c924309810a7,0x10e492184fa8,0x1aa872490fa8,0x1be872490f87]) (cB [0x445aa872490ca7,0x222872490fa8,0x862490fa7,0xc143927a9,0x182872484ea8,0x3050e4909810a7,0x182872484fa8,0x1aac143927a8,0x1bec14392787,0x445aac143924a7,0x222c143927a8,0x872488b69,0x10e491104e68,0x21c92220981067,0x10e491104f68,0x1aa872488b68])) (bI j 6 (cB [0x1be872488b47,0x445aa872488867,0x222872488b68,0x862488b67,0x872488be9,0x10e491104ee8,0x9843927e9,0xad43927c8,0x15a872d92787,0x872486fc7,0x15a8724811c7,0x1308724811e8,0xfc43927e9,0x41927e8,0x248afe7,0x8324811e7]) (cB [0x1f88724811e8,0x872484ee9,0x10e4909810e8,0x10e4909812e8,0x872484fe9,0xd543927e9,0xdf43927c8,0x1be872f12787,0x1bebd4392706,0x872483bc7,0x222d543924e8,0x11143927e9,0x43127e8,0x71127ea,0xe22490fa9,0x1c4492188b28])))) (bI j 10 (bI j 8 (cB [0x389aa492188a27,0x38892431101127,0x1c4492188ba8,0x1c49d2490fa8,0x1c4af2490f87,0x21ae22490fa8,0xe12490fa7,0x1c4d52490ea8,0x1c44921811a8,0x1c44921813a8,0xe22490fe9,0x1c4d52490ee8,0x1c44921811e8,0xe22c927e9,0xe23d127c8,0x1c4c13d12707]) (bI j 9 (cB [0x1c4c1248bf06,0x389827a3c12606,0x389aac13d12606,0x389827a2481106,0xe2248bfc7,0x1c47a3c126c7,0x1c4d53d126c7,0x1c47a24811c7,0x1c4c12c92728,0xb92c92727,0x172592481126,0x389aac12c92627,0x1cce26092626,0x38982592481127,0x1c4d52c926e8,0xe671126e7]) (cB [0x1c45924811e8,0xe260927e9,0x5c927e8,0xb924811e7,0x1c4d560926e8,0x1c4c124811e8,0xe22f927e9,0xe242127c8,0xe2248abc7,0x1c4843e126c7,0x10371127e9,0x70127e8,0x24837e7,0xe26a926e9,0xe224811e9,0xe224813e9]))) (bI j 12 (bI j 11 (cB [0x2490faa,0x49218efa9,0x92431d84ea8,0x124863b09810a7,0x92431d84fa8,0x1aa49218efa8,0xd82490fa7,0x1f449218ef27,0x445aa49218eca7,0x22249218efa8,0x49218fba9,0xa32490fa8,0x1464921811a7,0x92431f08b28,0x124863e1101127,0x92431f08ba8]) (cB [0x13a49218fba8,0xa22490fa7,0x21a49218fba8,0x92431f011a8,0x92431f013a8,0x492188b29,0x92431106b28,0x12486220d04e27,0x92431104e28,0x12486220981027,0x12486220981227,0x92431104f28,0x1aa492188b28,0x1be492188b27,0x445aa492188827,0x222492188b28])) (bI j 13 (cB [0x492188ba9,0x1f8492188b28,0x3f092431101127,0x92431104ea8,0x124862209810a7,0x92431104fa8,0x1aa492188ba8,0x445aa4921888a7,0x222492188ba8,0x982490fa9,0xad2490fa8,0x492186fa7,0x15a4921811a7,0x1304921811a8,0x1304921813a8,0xfc2490fa9]) (cB [0x1f84921811a8,0x1f84921813a8,0x492184ea9,0x924309810a8,0x924309812a8,0x492184fa9,0x924309813a8,0xd52490fa9,0xdf2490fa8,0x492183ba7,0xfa2490fa8,0x222d52490ca8,0x1112490fa9,0x2490fea,0xc12490fa9,0x182492188b28]))))) (bI j 21 (bI j 17 (bI j 15 (cB [0x30492431104e27,0x182492184ea8,0x304924309810a7,0x182492184fa8,0x1aac12490fa8,0x445aac12490ca7,0x222c12490fa8,0xea2490fa9,0x1d4492188ba8,0x1d49d2490fa8,0x21aea2490fa8,0xe92490fa7,0x1d44921811a8,0x1d44921813a8,0x492188be9,0x92431104ee8]) (bI j 16 (cB [0x982490fe9,0xad2490fe8,0x1304921811e8,0xfc2490fe9,0x1f84921811e8,0x492184ee9,0x924309810e8,0x924309812e8,0x492184fe9,0xd52490fe9,0xdf2490fe8,0xfa2490fe8,0x222d52490ce8,0x1112490fe9,0x2c927ea,0x3d127e9]) (cB [0xc13d12728,0xc1248bf27,0x182491784e26,0x1827a248bf27,0x1827a3c12727,0x1ecc13c12626,0x1ecc13d12727,0x1827a2484e27,0x304f4490981026,0x1827a2484f27,0x1aac13d12727,0x1bec13d12706,0xf56092726,0x445aac13d12426,0x222c13d12727,0x248bfe8]))) (bI j 19 (bI j 18 (cB [0x491784ee7,0x7a248bfe8,0x7a3c127e8,0xf63c126e7,0xf63d127e8,0x7a2484ee8,0xf44909810e7,0x7a2484fe8,0xd53d127e8,0xdf3d127c7,0x7a927e7,0x222d53d124e7,0x1113d127e8,0xc12c92729,0x592486b28,0xb2490d04e27]) (cB [0x164921a0981026,0xb2490d04f27,0x1aa592486b27,0xe62486b26,0x222e62486825,0x445aa592486826,0x222592486b27,0x182b72c92728,0x3056e592481127,0x182592484e28,0x304b2490981027,0x304b2490981227,0x182592484f28,0x1aac12c92728,0x1bec12c92727,0xe66092727])) (bI j 20 (cB [0x222e66092426,0x222c12482c25,0xc12482f26,0x445aac12c92427,0x222c12c92728,0x592484ee9,0xb24909810e8,0xb24909812e8,0x592484fe9,0xd52c927e9,0xdf2c927e8,0x73127e8,0x11173124e7,0x1112482ce6,0x2482fe7,0x222d52c924e8]) (cB [0x1112c927e9,0x60927ea,0x2486be9,0x490d04ee8,0x921a09810e7,0x490d04fe8,0xd52486be8,0x222d524868e7,0x1112486be8,0xc15b927e9,0x182b724811e8,0xc12484ee9,0x1824909810e8,0x1824909812e8,0xc12484fe9,0xd560927e9])))) (bI j 24 (bI j 22 (cB [0xdf60927e8,0x222d560924e8,0x11160927e9,0x60127e8,0x6a127e7,0x2e127ea,0x40927e9,0x248b3e8,0x4916011e7,0x81248b3e8,0x813b927e8,0x10840925e7,0xd33b92767,0xd340927e8,0x813f927e8,0x10b3f925e7]) (bI j 23 (cB [0x10b40927e8,0x9d40927e8,0xaf40927c7,0x69127e7,0x10d40927e8,0x40127e7,0x8124811e8,0x8124813e8,0x5e127e9,0xbc24811e8,0xbc24813e8,0x9d2e127e9,0x5d927e8,0x10d2e127e9,0x5c24811e9,0x5c24813e9]) (cB [0x75127ea,0x10d75127e9,0x74927e8,0x7c127e7,0x2482be7,0xea24811e9,0xea24813e9,0x2484eea,0x4909810e9,0x4909812e9,0x2484fea,0x4909813e9,0x6a927ea,0x6f927e9,0xdf2f127e8,0xdf5e92767]))) (bI j 26 (bI j 25 (cB [0xf75e92726,0xf72f127a7,0xf76f927e8,0xdf4e12767,0x2483be8,0xdf2483be8,0x74127e9,0x1116a924e9,0x88927ea,0x163fb,0x3b163ea,0xe23b163c9,0xe23b117c8,0x1c4762c91787,0x1c4762288b47,0x1c4762c96388]) (cB [0x389aa762c96287,0x1cce23b16286,0x388ec592c01187,0x1c4762c08b48,0x388ec581101147,0x1c4762c08bc8,0x1c49d3b163c8,0x21ae23b163c8,0x3b117e9,0x762c917a8,0x7a3b11787,0x76228bf86,0xf4762284e86,0xec592284ea7,0x762288b68,0xec451104e67])) (bI j 27 (cB [0x762288be8,0x983b117e8,0xad3b117c7,0xfc3b117e8,0x762284ee8,0xec4509810e7,0x762284fe8,0xd53b117e8,0xdf3b117c7,0x222d53b114e7,0x1113b117e8,0x762c963a9,0x7a3b16388,0x762c0bf87,0xec581784e86,0xf4762c0bf87]) (cB [0xf4783b16387,0x1ec783b16286,0x1ec7a3b16387,0x7a3816386,0xf4762c04e87,0x1e8ec580981086,0xf4762c04f87,0x1aa7a3b16387,0xf53b16386,0x445aa7a3b16086,0x2227a3b16387,0xec592c04ea8,0x1d8b25809810a7,0xec592c04fa8,0x1aa762c963a8,0x1be762c96387])))))) (bI j 42 (bI j 35 (bI j 31 (bI j 29 (cB [0xe63b163a7,0x222e63b160a6,0x445aa762c960a7,0x222762c963a8,0x762c08b69,0xec581104e68,0x1d8b0220981067,0xec581104f68,0x1aa762c08b68,0x1be762c08b47,0x445aa762c08867,0x222762c08b68,0x762c08be9,0xec581104ee8,0x983b163e9,0xad3b163c8]) (bI j 30 (cB [0x762c06fc7,0x15a762c011c7,0x130762c011e8,0xfc3b163e9,0x1f8762c011e8,0x762c04ee9,0xec5809810e8,0xec5809812e8,0x762c04fe9,0xd53b163e9,0xdf3b163c8,0x762c03bc7,0x222d53b160e8,0x1113b163e9,0x117fa,0x2290fb9]) (cB [0x452188b38,0x8a431104e37,0x452188bb8,0x982290fb8,0xa72290fa7,0xad2290f97,0xfc2290fb8,0x452184eb8,0x452184fb8,0xd52290fb8,0xda2290fa7,0x222da2290ca6,0xdf2290f97,0x222d52290cb7,0x1112290fb8,0x2290ff9]))) (bI j 33 (bI j 32 (cB [0x2c917f9,0x33117e8,0x228ebe7,0x3d117d8,0xc13d11717,0xc1228bf16,0x228bfd7,0xc12c91738,0x60917f9,0x2e117f9,0x36917e8,0x228dfe7,0x75117f9,0x2c10fba,0x582188b39,0xb0431104e38]) (cB [0x16086220981037,0xb0431104f38,0x1aa582188b38,0x1b4582188b27,0x445b4582188826,0x1be582188b17,0x445aa582188837,0x222582188b38,0x582188bb9,0xb0431104eb8,0x982c10fb9,0xa72c10fa8,0x5821877a7,0x14e5821811a7,0xad2c10f98,0x582186f97])) (bI j 34 (cB [0x1305821811b8,0xfc2c10fb9,0x1f85821811b8,0x582184eb9,0x582184fb9,0xd52c10fb9,0xda2c10fa8,0x222da2c10ca7,0x2225821844a6,0x5821847a7,0xdf2c10f98,0x582183b97,0x222d52c10cb8,0x1112c10fb9,0x2c10ffa,0x582188bf9]) (cB [0x982c10ff9,0xa72c10fe8,0xad2c10fd8,0xfc2c10ff9,0x582184ff9,0xd52c10ff9,0xda2c10fe8,0x222da2c10ce7,0xdf2c10fd8,0x222d52c10cf8,0x1112c10ff9,0x2c963fa,0x33163e9,0x2c0ebe8,0x662c0ebe8,0x6632163e8])))) (bI j 38 (bI j 36 (cB [0x8a33163c7,0x10433161e7,0xef33163e8,0xec33161e7,0xd533163e8,0xdf33163c7,0x77163e7,0x11177160e6,0x222d533160e7,0x11133163e8,0x3d163d9,0xc13d16318,0xc12c0bf17,0x1827a2c0bf17,0x1827a3c16317,0x1ecc13c16216]) (bI j 37 (cB [0x1ecc13d16317,0x1aac13d16317,0x1b4c13d16306,0x445b4c13d16005,0x445aac13d16016,0x222c13d16317,0x2c0bfd8,0x7a2c0bfd8,0x7a3c163d8,0xf63c162d7,0xf63d163d8,0xd53d163d8,0xda3d163c7,0x222d53d160d7,0x1113d163d8,0xc12c96339]) (cB [0x1aac12c96338,0xe66096337,0x222e66096036,0x445aac12c96037,0x222c12c96338,0xd52c963f9,0x73163f8,0x1112c963f9,0x60963fa,0x11160963f9,0x60163f8,0x66963e7,0x2e163fa,0x36963e9,0x2c0dfe8,0x6d2c0dfe8]))) (bI j 40 (bI j 39 (cB [0x6d30963e8,0xc83096367,0xc836963e8,0x6d35963e8,0x8f36963c7,0xc73696367,0x10636963e8,0x9d36963e8,0xaf36963c7,0x63163e7,0x10d36963e8,0x9d2e163f9,0x5d963f8,0x10d2e163f9,0x75163fa,0x10d75163f9]) (cB [0x74963f8,0x79963e7,0x1dbfb,0x439dbba,0x873b08b39,0x10e761104e38,0x21cec220981037,0x10e761104f38,0x1aa873b08b38,0x1b4873b08b27,0x445b4873b08826,0x1be873b08b17,0x445aa873b08837,0x222873b08b38,0x873b08bb9,0x10e761104eb8])) (bI j 41 (cB [0x98439dbb9,0xa7439dba8,0x873b077a7,0x14e873b011a7,0xad439db98,0x16aad439db87,0x873b06f97,0x15a873b01197,0x130873b011b8,0xfc439dbb9,0x419dbb8,0x3b0afb7,0x833b011b7,0x1f8873b011b8,0x873b04eb9,0x10e7609810b8]) (cB [0x10e7609812b8,0x873b04fb9,0xd5439dbb9,0xda439dba8,0x1fada439dba7,0x222da439d8a7,0x222873b044a6,0x873b047a7,0xdf439db98,0x1c6df439db87,0x873b03b97,0x222d5439d8b8,0x111439dbb9,0x591dbfa,0x1a3f9,0xe3f8]))))) (bI j 49 (bI j 45 (bI j 43 (cB [0x1c04ef7,0x789a3f8,0x3408b78,0x681104e77,0x3404ef8,0x6809810f7,0x3404ff8,0x6a9a3f8,0x3c3f7,0x88bc0f6,0x1116a9a0f7,0x889a3f8,0xb23b08b79,0x164761104e78,0xb23b04ef9,0x1647609810f8]) (bI j 44 (cB [0xb23b04ff9,0xd5591dbf9,0xda591dbe8,0x1fada591db67,0x222da591d8e7,0xdf591dbd8,0x222d5591d8f8,0xd5591d4f7,0xd55925cd6,0x111591dbf9,0x591d7f8,0x5925fd7,0x581dbf8,0x5b1dbe7,0x711dbfa,0xe23b167b9]) (cB [0xe23d1db98,0xe23b0bf97,0x1c47a3c1da97,0x1c4893d1da86,0x214e23d1db97,0x1c4d53d1da97,0x1c4da3d1da86,0x1c47a3b01197,0x37967b8,0xd537966b7,0x731beb6,0x6f2c811b7,0x1c4d53b166b8,0xe6711dab7,0x1c4762c811b8,0x1bff9]))) (bI j 47 (bI j 46 (cB [0xd3f8,0x1a08b77,0x651bff8,0x3788b78,0x6f1101177,0x3788bf8,0x4e9bff8,0x327f7,0x869bff8,0xe23b08b79,0x1c4761101178,0xe23b08bf9,0xe24e9dbf9,0xe2551dbe8,0x10d711dbf9,0x711d3f8]) (cB [0x7125bd7,0x3b10fba,0x762188b39,0xec431107f38,0xec431104e38,0x1d886220981037,0xec431104f38,0x1aa762188b38,0x1b4762188b27,0x445b4762188826,0x445aa762188837,0x1aa752188836,0x222762188b38,0x752188b37,0x762188bb9,0x1f8762188b38])) (bI j 48 (cB [0x722188b37,0xec431104eb8,0x983b10fb9,0xa73b10fa8,0x7621877a7,0x14e7621811a7,0x1307621811b8,0xfc3b10fb9,0x3910fb8,0x7221811b7,0x1f87621811b8,0x762184eb9,0xec4309810b8,0xec4309812b8,0x762184fb9,0xd53b10fb9]) (cB [0xda3b10fa8,0x222da3b10ca7,0x2227621844a6,0x7621847a7,0xfa3b10fb8,0x222d53b10cb8,0xd53a90cb7,0x1113b10fb9,0x3a90fb8,0x3b167ba,0x3d1dbb9,0x3b0bfb8,0x761784eb7,0x7a3b0bfb8,0x7a3c1dbb8,0x893d1dba7])))) (bI j 52 (bI j 50 (cB [0xf6449daa6,0xf63c1dab7,0xf63d1dbb8,0x3d1c3b7,0x7a3b04eb8,0xf47609810b7,0x7a3b04fb8,0xd53d1dbb8,0xda3d1dba7,0x222da3d1d8a6,0xdf3d1db97,0x7a9dbb7,0x222d53d1d8b7,0x1113d1dbb8,0x2c8c7b9,0x591884eb8]) (bI j 51 (cB [0xb23109810b7,0x591884fb8,0xd52c8c7b8,0xda2c8c7a7,0x222da2c8c4a6,0x730c7b7,0x111730c4b6,0x222d52c8c4b7,0x1112c8c7b8,0x6716739,0xce2c84e38,0x19c590981037,0x19c590981237,0xce2c84f38,0xd56716738,0xda6716727]) (cB [0x222da6716426,0x222ce2c84425,0xce2c84726,0x7333b37,0x1117333836,0x1116702c35,0x6702f36,0x222d56716437,0x1116716738,0x7635167b9,0xc53b16738,0x18a762c81137,0xec6a2c811b8,0x762c84eb9,0xec5909810b8,0xec5909812b8]))) (bI j 54 (bI j 53 (cB [0x762c84fb9,0xd53b167b9,0xda3b167a8,0x222da3b164a7,0x222762c844a6,0x762c847a7,0xdf3b167b8,0x731dbb8,0x111731d8b7,0x1113b02cb6,0x3b02fb7,0x222d53b164b8,0x1113b167b9,0x751dbba,0xea3b08b39,0x1d4761108338]) (cB [0x1d4761101138,0x1d4761101338,0xea3b08bb9,0x21aea3b08b38,0xe93b08b37,0x1d47611011b8,0xea4e9dbb9,0xea551dba8,0xea3b073a7,0x10d751dbb9,0x749dbb8,0x3b02bb7,0xea3b011b9,0xea3b013b9,0xc7fa,0x1888b79])) (bI j 55 (cB [0x311107f78,0x311104e78,0x62220981077,0x311104f78,0xd51888b78,0x6b88b77,0xda1888b67,0x222da1888866,0x222d51888877,0x1111888b78,0x1888bf9,0xfc1888b78,0x311104ef8,0x4c0c7f9,0x287f8,0x50811f7]) (cB [0x538c7e8,0xa72d0c7a7,0x18877e7,0xa718811e7,0x9818811f8,0x7e0c7f9,0xfc18811f8,0x1884ef9,0x3109810f8,0x3109812f8,0x1884ff9,0x6a8c7f9,0x35ff8,0x6d0c7e8,0xda2e8c7a7,0x222da2e8c4a6]))))))) (bI j 84 (bI j 70 (bI j 63 (bI j 59 (bI j 57 (cB [0x1116d0c4e7,0x11118844e6,0x18847e7,0x7d0c7f8,0x1116a8c4f8,0x888c7f9,0x3b18ffa,0x3518ff9,0x6298f78,0xc53181177,0x6a31811f8,0x763184ef9,0xec6309810f8,0x763184ff9,0xd53b18ff9,0xda3b18fe8]) (bI j 58 (cB [0x222da3b18ce7,0x759dbf8,0x111759d8f7,0x222d53b18cf8,0x1113b18ff9,0x33bfa,0x6704ef9,0xce09810f8,0xce09812f8,0x6704ff9,0x6ab3bf9,0x6d33be8,0x1116d338e7,0x11167044e6,0x67047e7,0x1116ab38f8]) (cB [0x88b3bf9,0x3b1abfa,0x629dbf9,0xc53b011f8,0x763508b79,0xec6a1101178,0x763508bf9,0x9d3b1abf9,0xaa3b1abe8,0x621dbf8,0x10d3b1abf9,0x7635011f9,0x7635013f9,0x3b08b7a,0x761107b79,0xec220f04e78]))) (bI j 61 (bI j 60 (cB [0x761107f79,0xec220f81178,0x761104e79,0xec220981078,0xec220981278,0x761104f79,0xd53b08b79,0xda3b08b68,0x1b4762e88b27,0x445b4762e88826,0x222da3b08867,0x1b4763a88866,0x222761104466,0x761104767,0xdf3b08b78,0x3708b77]) (cB [0x222d53b08878,0xd53a88877,0xd54b88876,0x1aa763a88877,0x1113b08b79,0x3a88b78,0x4b88b77,0x763a88b78,0x3b08bfa,0x3b07bf9,0x760f04ef8,0xfc3b08b79,0x3908b78,0x1988b77,0x721101177,0x763908b78])) (bI j 62 (cB [0x1f8761101178,0x761104ef9,0xec2209810f8,0x761104ff9,0xd53b08bf9,0xda3b08be8,0x222da3b088e7,0x222d53b088f8,0xd53a888f7,0x1113b08bf9,0x3a88bf8,0x4c1dbfa,0x539dbe9,0xb5539dbe8,0xb53b16ba7,0xa73b16ba8]) (cB [0xa73d9dba7,0x14e762d011a7,0x3b077e8,0x760e811e7,0xa73b077e8,0xa7531dbe8,0xb4539dbc7,0x10e5a1d9c6,0x10e531d9e7,0x10e539dbe8,0xa73b011e8,0xa73b013e8,0x569dbf9,0xb5569dbe8,0x19ff8,0x33811f7])))) (bI j 66 (bI j 64 (cB [0x3b06ff8,0xad3b011f8,0x983b011f9,0x983b013f9,0x7e1dbfa,0x1cbf9,0x24ff8,0x93f7,0x49811f7,0x499cbf8,0xcff8,0x19811f7,0x839cbf8,0x39011f8,0x39013f8,0x3b1cbf9]) (bI j 65 (cB [0x7639011f8,0xfc3b011f9,0xfc3b013f9,0x3b04efa,0x7609810f9,0x7609812f9,0x3b04ffa,0x7609813f9,0x6a9dbfa,0x6d1dbe9,0xe36d1dbe8,0xe33b177a7,0xfd719dbe7,0x222e36d1d8e7,0xda3b177a8,0xda411dba7]) (cB [0x222da411d8a6,0x222da3b174a7,0xda4d1dbe8,0xda571dbe7,0xfd571db66,0x222da571d8e6,0xfd4d1db67,0x222fd4d1d866,0x222da4d1d8e7,0xfd6d1dbe8,0x222fd6d1d8e7,0x1116d1d8e8,0xda3b1d4e7,0x763a844e6,0x1113b044e7,0x222da3b044e7]))) (bI j 68 (bI j 67 (cB [0x3b047e8,0xda3b047e8,0x6f9dbf9,0xe36f9dbe8,0x1bbf8,0x3b03bf8,0x7d1dbf9,0x1c7f8,0x1116a9d8f9,0x6a9d4f8,0x6aa5cf7,0x6a88cf6,0xd53b1d4f8,0x889dbfa,0x1d7f9,0x25ff8]) (cB [0x8ff7,0x3b1d7f9,0x37bfb,0x6f21ffa,0xde4390fb9,0x3f10fb8,0x7e2188b37,0x7e2184eb7,0x7e21811b7,0x1bc872188b38,0x1bc872184eb8,0x222de4390eb8,0x1bc8721811b8,0xde60a1fb9,0x222de60a1eb8,0x1bcc143811b8])) (bI j 69 (cB [0x1fbf9,0xb7f8,0x1688b77,0x689fbf8,0x3f08b78,0x7e1101177,0x3f08bf8,0x4e9fbf8,0x343f7,0x869fbf8,0xde4388b79,0x1bc871101178,0xde4388bf9,0xde4ea1ff9,0xde5521fe8,0x10d6f21ff9]) (cB [0x6f217f8,0x6f257e7,0x6f10fba,0xde218efb9,0x1bc431d84eb8,0x222de218eeb8,0x1bc431d811b8,0xde21907b9,0xde5210fb8,0x1bc432088b38,0x1bc432084eb8,0xde2188b39,0x1bc431106b38,0x1bc431104e38,0x37886220981037,0x222de2188a38]))))) (bI j 77 (bI j 73 (bI j 71 (cB [0x1bc431101138,0x1bc431101338,0xde2188bb9,0x21ade2188b38,0xdd2188b37,0x1bc431104eb8,0x222de2188ab8,0x1bc4311011b8,0xde4e90fb9,0xde5510fa8,0xde21873a7,0x1bcaa5290ea7,0x1bcb35510e86,0x1bcaa2184ea7,0xde5790fb8,0x5590fb7]) (bI j 72 (cB [0x1bc9d2184eb8,0x10d6f10fb9,0x21ade2184eb8,0xdd2184eb7,0x6e90fb8,0x7290fb7,0x2183fb7,0xde2184eb9,0x1bc4309810b8,0x1bc4309812b8,0x1116f10eb9,0xde21811b9,0xde21813b9,0x6f10ffa,0xde6090fb9,0x1bcc12188b38]) (cB [0x1bcc12184eb8,0x222de6090eb8,0x1bcc121811b8,0x1036f10fb9,0x206de2184eb8,0xdb2184eb7,0x6d90fb8,0x21843b7,0xde2188bf9,0xde4e90ff9,0xde5510fe8,0x10d6f10ff9,0x6e90ff8,0xde2184ef9,0x1bc4309810f8,0x1116f10ef9]))) (bI j 75 (bI j 74 (cB [0xde21811f9,0xde21813f9,0x6f167fa,0x6f19be9,0xde4699be8,0x6f0ebe8,0xde1d04ee7,0x1116f0eae7,0xde1d011e7,0xde330ebe8,0xde33192e8,0xde4519ac7,0xde330a6c6,0x1bc8a33010c6,0xde4519ae7,0x1046f198e7]) (cB [0x1bc6632010e7,0xde33197e8,0xde4619bc7,0x1056f19be8,0xde3304ee8,0x1bc6609810e7,0x1116f19ae8,0xde33011e8,0xde33013e8,0x6f1ebf9,0xde609eb38,0xde608bf37,0x1ecde609ea37,0x1bcc13d04e37,0x222de609ea37,0x1bcc13d01137])) (bI j 76 (cB [0x6f0bff8,0xf66f1eaf8,0x1e7f8,0x3c811f7,0x10a6f1ebf8,0x6e1ebf7,0xde3d04ef8,0x1116f1eaf8,0xde3d011f8,0xde6096739,0xde2c86b38,0x1bc590d04e37,0x222de2c86a37,0x1bc590d01137,0x1bcc15f16738,0x1bccb6096727]) (cB [0x1bcc12c84e38,0x37982590981037,0x222de6096638,0x1bcc12c81138,0x1bcc12c81338,0xde2c84ef9,0x1bc5909810f8,0x1116f166f9,0xde2c811f9,0xde2c813f9,0x6f307fa,0x6f06bf9,0xde0d04ef8,0x1116f06af8,0xde0d011f8,0x2e3f9])))) (bI j 80 (bI j 78 (cB [0x33ff8,0x53f7,0x6784ef7,0x67811f7,0x5c04ef8,0xb809810f7,0x5c011f8,0x5c013f8,0xde60afbf9,0xde65b07e8,0xde6084ef9,0x1bcc109810f8,0x1116f306f9,0xde60811f9,0xde60813f9,0x6f17ffa]) (bI j 79 (cB [0x6f1cfe9,0xde4a1cfe8,0x6f0cbe8,0xde1904ee7,0xde398cbe8,0xde3998be8,0xde661cfe8,0xde399a6e8,0xde471cec7,0xde3989ec6,0xde471cee7,0xde3984ee8,0x6f213f9,0x6f0abf8,0xf96f212f8,0x1f7f8]) (cB [0xde4204ef8,0x6f2fff9,0xde5f84ef8,0xde2f84ef9,0x81b7bfa,0x1036f04ef9,0x6d84ef8,0x7204ef7,0x36ff9,0x393f8,0x33f7,0x7236ff8,0x7f36ff8,0x43f8,0x6f04efa,0xde09810f9]))) (bI j 82 (bI j 81 (cB [0xde09812f9,0x88b7afa,0x6f011fa,0x6f013fa,0x10fbb,0x218efba,0x2710fb9,0x2410fb8,0x482184eb7,0x4e2184eb8,0x9c4309810b7,0x4e2184fb8,0xd52710fb8,0xda2710fa7,0x222da2710ca6,0x222d52710cb7]) (cB [0x1112710fb8,0x6c90fb9,0xd921811b8,0xd921813b8,0x431d84eb9,0x863b0984ab8,0x431e04eb7,0x863b09810b8,0x863b09812b8,0x431d84fb9,0x222431d84eb8,0xd5218efb9,0x6c10fb8,0xda218efb8,0x222da218ecb7,0xfa218ef38])) (bI j 83 (cB [0x222d5218ecb8,0x1aa431d804b7,0x111218efb9,0x431d807b8,0x218fbba,0x2810fb9,0x2390fb8,0x472188b37,0x4721811b7,0x502188b38,0xa0431101137,0x502188bb8,0x9d2810fb8,0xaa2810fa7,0x10d2810fb8,0x5021811b8]) (cB [0x5021813b8,0x5190fb9,0xa321811b8,0xa321813b8,0x8110fb9,0x1022188b38,0x1022188bb8,0x431f08b39,0x863e1108338,0x442188b37,0x863e1101138,0x863e1101338,0x431f08bb9,0x21a431f08b38,0x863e11011b8,0x9d218fbb9])))))) (bI j 98 (bI j 91 (bI j 87 (bI j 85 (cB [0x5110fb8,0xaa218fbb8,0xfb218fab8,0x10d218fbb9,0x21a431f011b8,0x431f011b9,0x863e0200db8,0x431f811b7,0x431f013b9,0x2188b3a,0x431106b39,0x86220d04e38,0x10c441a0981037,0x86220d04f38,0x1aa431106b38,0x445aa431106837]) (bI j 86 (cB [0x222431106b38,0x431104e39,0x86220981638,0x202431104e37,0x10c44130281037,0x86220981038,0x86220981238,0x431104f39,0x222431104e38,0x44486220981037,0x86220981338,0xd52188b39,0xda2188b38,0x222da2188837,0x222431104436,0x431104737]) (cB [0xdf2188b38,0x431103b37,0x222d52188838,0x445aa431108437,0x1aa431100437,0x1aa542188836,0x1112188b39,0x222431108738,0x431100738,0x542188b37,0x2188bba,0xfc2188b39,0x1f8431104e38,0x3f086220981037,0x1f8431101138,0x1f8431101338]))) (bI j 89 (bI j 88 (cB [0x431104eb9,0x862209826b8,0x862209812b8,0x431104fb9,0x222431104eb8,0xd52188bb9,0xda2188bb8,0x222da21888b7,0xdf2188bb8,0x222d521888b8,0x1aa4311004b7,0x1112188bb9,0x4311007b8,0x4c10fba,0x5390fb9,0xa7218f7b8]) (cB [0xb55390fb8,0x21877b8,0x430e811b7,0xa721877b8,0xa75310fb8,0xb45390f97,0x10e5a10d96,0x10e5310db7,0x10e5390fb8,0xa721811b8,0xa721813b8,0x5690fb9,0xb55690fb8,0x2186fb8,0xad2186fb8,0xad5610fb8])) (bI j 90 (cB [0x10f5610db7,0x10f5690fb8,0xad21813b8,0x8610fb9,0x9821811b9,0x1304302009b8,0x9921811b7,0x9821813b9,0x7e10fba,0xfc2184eb9,0x1f84309812b8,0xfc21811b9,0x1f84302009b8,0xfc21813b9,0x2184eba,0x4309826b9]) (cB [0xa02184eb8,0x2184fba,0x1112184eb9,0x2224309810b8,0x4309813b9,0x6a90fba,0x6d10fb9,0xda21903b8,0x222da21900b7,0xe36d10fb8,0x222e36d10cb7,0xda4d10fb8,0xfd4d10f37,0x222fd4d10c36,0x222da4d10cb7,0xfd6d10fb8])))) (bI j 94 (bI j 92 (cB [0x222fd6d10cb7,0x1116d10cb8,0x11121844b7,0x222da21844b7,0x21847b8,0xda21847b8,0x6f90fb9,0xe36f90fb8,0xdf4d90fb8,0xdf5410fa7,0xff5410f26,0xff4d90f37,0xff6f90fb8,0x2183bb8,0xdf2183bb8,0x7d10fb9]) (bI j 93 (cB [0x1116a90cb9,0x222d521908b8,0x222d54f10cb8,0x222d55890cb7,0xd521804b8,0xd52a10cb7,0x8890fba,0x1112190bb9,0x1114f10fb9,0x1115890fb8,0x21807b9,0x2a10fb8,0x10ffb,0x6090fba,0xc12188b39,0x182431104f38]) (cB [0x1aac12188b38,0x445aac12188837,0x222c12188b38,0xc12184fb9,0x222c12184eb8,0xd56090fb9,0xda6090fb8,0x222da6090cb7,0x222d56090cb8,0x1aac121804b7,0x1116090fb9,0xc121807b8,0x7510fba,0xea2188bb9,0x21aea2188b38,0xe92188b37]))) (bI j 96 (bI j 95 (cB [0x1d4431104eb8,0xea4e90fb9,0xea5510fb8,0x5490fb7,0x1d49d2184eb8,0x10d7510fb9,0x21aea2184eb8,0xe92184eb7,0x7490fb8,0x7990fb7,0x2182bb7,0xe921811b7,0x21aea21811b8,0xea2184eb9,0xea21813b9,0x2188bfa]) (cB [0x431104ff9,0xd52188bf9,0x222d521888f8,0x1112188bf9,0x4c10ffa,0x5390ff9,0xc35390fb8,0x21877f8,0x5690ff9,0x2186ff8,0x8610ff9,0x9821813f9,0x7e10ffa,0xfc21813f9,0x2184ffa,0x6a90ffa])) (bI j 97 (cB [0x6d10ff9,0xf26d10fb8,0x222f26d10cb7,0x1116d10cf8,0x11121844f7,0x21847f8,0x6f90ff9,0x2183bf8,0x7d10ff9,0x1116a90cf9,0x222d54f10cf8,0xd521804f8,0xd52a10cf7,0x8890ffa,0x1114f10ff9,0x21807f9]) (cB [0x2a10ff8,0x167fb,0x19bfa,0x4699bf9,0x468ebf8,0x46993f8,0x46a2bd7,0x82235f7,0x77a37f8,0x76235f7,0x330a3f8,0xebf9,0x1d0e7f8,0x290ebe7,0x6a8ebf8,0x6d0ebe7]))))) (bI j 105 (bI j 101 (bI j 99 (cB [0x1116d0e8e6,0x1116a8e8f7,0x888ebf8,0x330ebf9,0x778ebf8,0x760e9f7,0x33193f9,0x4519bd8,0x8b4519bc7,0x77a2ad7,0x778a6d6,0x330a7d7,0x4519bf8,0x77a2af7,0x82199f8,0x823bcf7]) (bI j 100 (cB [0x77992f8,0x7799bf9,0x82bbff8,0x3bbf7,0x76199f8,0x6a99bf9,0x6d19be8,0x1116d198e7,0x11133044e6,0x33047e7,0x6f99bf8,0x3bbf8,0x88bb8f7,0x88820f6,0x773b4f6,0x23f7]) (cB [0x7719bf8,0x11177198f7,0x1116a998f8,0x8899bf9,0x1ebfa,0x469ebf9,0xc1469eb38,0xc1468bf37,0xf660a3737,0xc13d0a337,0x468bff8,0x469e3f8,0x7b237f8,0x3d0a3f8,0x609eb39,0x608bf38]))) (bI j 103 (bI j 102 (cB [0xc1178bb37,0xc12b8bf16,0xd5608bf37,0x222d5608bc36,0x111608bf37,0xc13d0bf38,0xf6608bf37,0xc13d1e338,0xc1449eb37,0xf660a2636,0x109609eb37,0xf6609e237,0xf65d1e236,0xc13c01a36,0xf6609eb38,0x10a7b30737]) (cB [0x7ab0736,0xf65d1eb37,0xc13d01b37,0xc13d15716,0x112609eb37,0xd5609eb38,0xda609eb37,0x222da609e836,0xf5609eb37,0x222d5609e837,0x1aac13d00436,0x111609eb38,0xc13d00737,0xbff9,0x178bbf8,0x2b8bfd7])) (bI j 104 (cB [0x6a8bff8,0x1116a8bcf7,0x888bff8,0x3d0bff9,0x7b0bff8,0x3d1e3f9,0x449ebf8,0x7b226f7,0x849ebf8,0x7b1e2f8,0x3c01af7,0xf67a1e2f7,0x7b1ebf9,0x853dbf8,0x3d01bf8,0x3d157d7]) (cB [0xf67a1ebf8,0x891ebf8,0x6a9ebf9,0x6d1ebf8,0x7a9ebf8,0x1116a9e8f8,0xd53d004f7,0x889ebf9,0x3d007f8,0x39ffa,0x609673a,0x2c86b39,0x2c93738,0xd52c93737,0x7313736,0x1117313435])))) (bI j 109 (bI j 107 (bI j 106 (cB [0x222d52c93436,0x1112c93737,0xd52c86b38,0x7306b37,0x1117306836,0x1110d02c35,0xe60d00435,0xd02f36,0x222d52c86837,0x1aa590d00436,0x1112c86b38,0x590d00737,0xc15b96739,0xc26096738,0xc12c86737,0x1106096738]) (cB [0xd56096739,0x7330738,0xee7330737,0x222ee7330436,0xf57330737,0x1117330437,0x222e660b0036,0x1116082c36,0x222e66082c36,0x6082f37,0x6095b36,0xe66082f37,0x222d56096438,0x445aac16016437,0x1116096739,0x222c16016738])) (bI j 108 (cB [0xc12c80738,0xc12c95337,0x6a967fa,0x39bf9,0x7739bf8,0x2ff8,0x133f7,0x7302ff8,0x88967fa,0x2c807f9,0x2c953f8,0x307fb,0x6bfa,0x137f9,0x88937f8,0x8886bf9]) (cB [0xd007f8,0x60adffa,0x61307f9,0x60867f8,0x88307f9,0x88b07fa,0x303f9,0x337f8,0x57f7,0x11160b03f9,0x173fb,0x1b7fa,0x491b7f9,0x490dff8,0x49187f8,0x6424bf8]))) (bI j 111 (bI j 110 (cB [0x491aff8,0x4923fd7,0x63a4b77,0x8324bf8,0x36897f8,0xdff9,0x1b8c3f8,0x278dfe7,0x1b8d7f8,0x288dfe7,0x4e8dff8,0x550dfe7,0x868dff8,0xdbf7,0x368dff9,0x640dff8]) (cB [0x830dff8,0x36987f9,0x441b7f8,0x6422377,0x6418778,0x3085b77,0x641b7f9,0x83323f8,0x10d641b778,0x3685bf8,0x369aff9,0x479b7d8,0x90479b7c7,0x8323dd7,0x83099d6,0x3689bd7])) (bI j 112 (cB [0x479b7f8,0x8323df7,0x639b778,0x3685f77,0x639b7f8,0x831adf8,0x831b7f9,0x4e9b7f9,0x551b7e8,0x579b7f8,0x31bf8,0x63f7,0x631b7f8,0x869b7f9,0x1b3f8,0x247f7]) (cB [0x2f3fa,0x4e973fa,0x2eff9,0x86973fa,0x3abfb,0x86babfa,0x3a7f9,0x3cff8,0x1ff7,0x79ba7f8,0x2bf8,0x12ff7,0x7482bf8])))))))) 64 (i % 16)
def zqT (i : Nat) := materialize [73,82,95,158,213,255] 9 511 6 (zkl i >>> 4)
def ziB (i : Nat) := (zqT i).map zuw
def zkP (i : Nat) : Option (Nat × List Nat × List (Nat × Nat × Nat)) := some (zkl i &&& 15,ziB i,shortHist zcj 12 ziB zjD i)
def zmB : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm4,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,3,5,4] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,3,5,4] 0 i.val))),(pm7,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,3,2,4,5] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,3,2,4,5] 0 i.val))),(pm8,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,3,2,5,4] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,3,2,5,4] 0 i.val))),(pm24,(fun i : Fin 64 => Fin.ofNat 64 (pA [1,0,4,5,2,3] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [1,0,4,5,2,3] 0 i.val))),(pm29,(fun i : Fin 64 => Fin.ofNat 64 (pA [1,0,5,4,2,3] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [1,0,4,5,3,2] 0 i.val))),(pm25,(fun i : Fin 64 => Fin.ofNat 64 (pA [1,0,4,5,3,2] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [1,0,5,4,2,3] 0 i.val))),(pm30,(fun i : Fin 64 => Fin.ofNat 64 (pA [1,0,5,4,3,2] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [1,0,5,4,3,2] 0 i.val)))]
def zdS := zZ zmB
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zua : dM zcj zcr 64 zdS := zad (by decide +kernel)
set_option maxRecDepth 16000 in
def zmd (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 56 (bI j 28 (bI j 14 (bI j 7 (bI j 3 (bI j 1 (cB [0x1801ff,0xea80f8000000000,0x0,0x7fe004000,0x2220000000000000,0x40008000000003fc,0x1f81990000000,0x6000600000,0x8,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xc11200000000000,0x8200c082300083,0x0,0x800000000000000,0x3800000005c000,0x80,0x0,0x204000030c00200,0x182007]) (bI j 2 (cB [0x0,0xf30aa8000000000,0x5000280000000,0xa640008660114000,0x20000002000140,0x8000b00000000700,0x3800010000000,0x8000000000,0x1c09000000cc0008,0x7fe444000000c080,0x800102088e000,0x440080000000000,0x4020400,0x1004000000008000,0x0,0x802004100,0x4028040080000000,0x8000,0x2008000000004,0x0,0x0,0x8020050000000000,0x137fe00400000000,0x600018000000,0x83f300200,0x40200]) (cB [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1000000,0x0,0x0,0x80000000000,0x100000001900000,0x3107a08000001ff8,0x6,0x4000,0x0,0xff00200000000000,0x28000a000000057,0x20000000000,0x0,0x0,0x800000000000000,0x28001000000,0x10000003ff00200,0x14a00f]))) (bI j 5 (bI j 4 (cB [0x800000000000,0x0,0x0,0x1000075507c000,0xa3e00000000401e0,0xf000488003a9,0x600180c110000000,0x300180004,0x0,0x0,0x840800090800,0x80010000000000,0xc00,0x2008000,0x0,0x20,0x0,0x182200000000000,0x800500048a003,0x0,0x0,0x8000208000000,0x80000000000002,0x10000100,0x40000000]) (cB [0x0,0x0,0x2000,0x0,0x81e0000000000000,0x862040000c0003ab,0x1808090000000,0x4100000006,0x10000000040,0x200000000000,0x8000,0xc0000000100000,0x420000,0x0,0x400000000,0x10,0x80000000200,0xa692e00000000000,0x8600f000084003,0x430018041100000,0x46000800,0x0,0x0,0x10004000104,0x800040000000,0x2000])) (bI j 6 (cB [0x200000,0x0,0x0,0x10000000000000,0x0,0x0,0x2001844990000000,0x430038413e,0x1000121000000000,0xe010540000002100,0x40400e00010002,0x8e012000020000,0x1000000000000600,0x0,0x0,0x1,0x8020000000,0x0,0x2004000080010,0x400018641100000,0x88000000c2007818,0xc00021800c140,0x65]) (cB [0x4000000000,0xe6a2d8000000000,0x42803c0002080,0x10600601044000,0x300080,0x1000100008100000,0x1001904550000000,0x8500382395,0x1c00020001c02098,0xc000040000002080,0x600011600,0x0,0x0,0x0,0x0,0x0,0x800010000e010440,0x3082200000020000,0x30000f030080003,0x418018880100000,0xf800000382002000,0x103c00220000eaa0,0x75343c00000042,0x29481e001010,0xc0030080a00,0x1c6001])))) (bI j 10 (bI j 8 (cB [0x0,0x800,0x0,0x140800000000000,0x1080080,0x840000000000800,0x2000000000000,0x0,0x800200000000000,0x0,0x0,0x7000060000,0x500000018040100,0x9002800404801804,0x400000000000000a,0x4000400400,0xe2099f0006054540,0x29481,0x102000000000004,0x540000000000000,0x6800000021004000,0x103400220026c020,0x12400004000000c2,0x20001800001c,0x820000200,0x140200]) (bI j 9 (cB [0x0,0x0,0x0,0x0,0x2000000,0x0,0x0,0x0,0x0,0x0,0x20000000000000,0x10000000000,0x500000000000000,0x100800040041804,0x20c40008000000a,0x240000000000,0x0,0x0,0x100000000000000,0x0,0x80000000,0x0,0x0,0x200000000000,0x0,0x100000]) (cB [0x600000004000000,0xc0e028000000042,0x71883d0422000,0x89800622004000,0x13ac01a0,0x10,0x0,0x8310000000,0x4020000000000,0xe0101c0000000000,0x31081a00110005,0x80b026000020000,0x10000900,0x0,0x0,0x0,0xe821100006070140,0x110020000006a401,0x346004100019003,0x0,0xd800000000000000,0x100400000001e6a0,0x6d50f400000070,0x63081e001102,0x1c19910038084e00,0x31840d]))) (bI j 12 (bI j 11 (cB [0x4000000001d490f,0x6ea4878000000000,0xd000300001000,0x8001400024000,0x48001c0,0x0,0x8000000000000,0x400100002,0x1000000,0x0,0x0,0x0,0x0,0x0,0x0,0x400000010,0x400004002f5243c0,0xc00200000048001,0x4400a800f00042,0x0,0x2800000000000000,0x38000080018000,0x90,0x0,0x200100000000,0x4004]) (cB [0x200000,0x800,0x0,0x4000000000000,0xa0000000000010,0x4000b00002001200,0x2000000000000,0x800080001,0x3000000000e94c38,0x4020040000000000,0x68001800006000,0x0,0xc300000000000400,0x7000000001ca9,0x80000008,0x0,0x0,0x2008a00000000000,0x10000e071002052,0x30000300000,0x7800,0x0,0xc0000400000000,0x200000000000,0x60000023000200,0x306003])) (bI j 13 (cB [0x6041182041d698f,0x830008000000010,0x60800408b8000,0x0,0x1120000000000000,0x200e0a010409208,0x0,0x0,0x808880004000000,0x8000000000004000,0x800800000000,0x0,0x0,0x2002011000000000,0x5ea48780000000,0x80003800000,0xc0000120062b0340,0x500,0x0,0x0,0x2800000000000000,0x3c000000048000,0x280000000000000,0x20002000000,0x20c00003ad21e00,0x10e00f]) (cB [0x301068000106001,0x890,0x400040804000,0x73252c000,0x2d20000002000140,0xb00000000359,0x813400230000003,0x104005a4008,0x2814c80810ee4a78,0x8000000000004000,0x20200208200000,0x7a921e0000,0x700000000000b00,0x1001800406001a8c,0x0,0x0,0x6001e00004180040,0x2921600000010c00,0x101008000000007,0x1dc90f00000,0xf80000018d807812,0x204111e000eac8,0x75643c00000000,0x8c41e820990,0x4104cc0820300200,0x40007]))))) (bI j 21 (bI j 17 (bI j 15 (cB [0x4000000,0x80c008000000000,0x1280050013a00,0x0,0x0,0x800201002000000,0x2000000000000,0x210400000,0x0,0x0,0x100000002000000,0x40a0003ab21e0000,0x14800f01,0x2002008020000000,0x20000000000000,0x2002004000,0x20000000000000,0x0,0x0,0x580010180100000,0xa800200a,0x4040040000000,0x1041466400000004,0x41830cef8,0x4400800000000,0x204]) (bI j 16 (cB [0x708223c00b01115,0x80000001010,0x80000002200,0x2000000000,0x2220000000040100,0xe00f134c780020e,0x1,0x100400820,0x2844116010e6cad8,0x4044440000004000,0x168208900c,0x10020000000000,0x5500000020000150,0x50abb3d021111,0x18088980000008,0x802c4111e,0x110000000400,0x400,0x6200000440000,0x2240030111100000,0x8800000080804002,0xc03c4d11e0008c88,0x1375407c000000c6,0x600018000000,0x3003af83e00,0xc0c]) (cB [0x1d1407,0xc00008000000201,0x1000400000002,0x0,0x0,0x8000,0x40000000000000,0x0,0x0,0x0,0x2000000000,0x3100020000,0x4000000,0x0,0x200000000,0x40000000000,0x0,0x0,0x0,0x0,0x8000,0x0,0x40,0x200000000000,0xf0830503200,0xc0c]))) (bI j 19 (bI j 18 (cB [0x0,0x0,0x2,0x10000000000,0x0,0x0,0x6000000000000000,0x0,0x3000000c00c560c8,0x220,0x0,0x2000000080000,0x10840000,0x2000,0x10000000000000,0x0,0x18000000000,0x0,0x100000000000000,0x0,0x7800000280200000,0x80000000020e880,0x1074203c00000000,0x80420000000,0x820000200,0x40010]) (cB [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x970000a0000,0x24020200,0x0,0x20e482580000000,0x40080800000,0x104000040,0x0,0x0,0x8110411004500000,0x1800000080101020,0x80c000000218000,0x0,0x1000000000000,0x60000200,0x3])) (bI j 20 (cB [0x100001,0x800,0x0,0x0,0x20000000000000,0x8600,0x41180010000001,0x58000180800,0x3800000022e682d8,0x400024000000c000,0x1e00000010,0x88000000000,0x4d00000001000100,0x400702391104d100,0x278000580000018,0x3c00000,0x18100000000,0x200000000000,0xf000000087,0x410000100000,0x80006000,0x0,0x0,0x0,0x860001200,0x10100c]) (cB [0x781800004d18009,0xeac0f80000018c8,0x1883d0402000,0x209e00075607c000,0x200000008c4188,0x4600e4104d000201,0x0,0x0,0x804008000000000,0x8000000000000000,0x100c00000000000,0x0,0x0,0x900000000000000,0x15c080280000000,0x191883800110,0x0,0x9b0b600000000040,0x10e20f4000a0003,0x580010180100000,0xc006000,0x5000040000000,0x44611400000004,0x21c41e8ae544,0x4100800060300600,0x620f])))) (bI j 24 (bI j 22 (cB [0x44000000000,0x180c008000004000,0x4000300402000,0x6010000466004000,0x200000160001e8,0x4747000300,0xf,0x0,0x2800000015ea80f8,0x77707c0000008000,0x101400100a00,0x80f0431102a0000,0x80a00,0x0,0x100000000000000,0x0,0x84000200,0x0,0x0,0x0,0x0,0x20000000,0x800000000000000]) (bI j 23 (cB [0x0,0x2000000000000000,0x0,0x800000000,0x0,0x0,0x0,0x10040000040,0x20000010000000,0x6a30540000000000,0x2001400100a00,0x1000000040000,0x1f00000021080000,0x20074007b0001d70,0x8300080000004,0xa50028003d8,0x1100200000000000,0xe00000002800,0xf00000005e,0x258000100000,0x2800000200007800,0x3f082000158300,0xa6d40f400000085,0x400016000000,0x1c11110568004e00,0x21000b]) (cB [0x7808040001d581f,0x83c008000000850,0xc0003f0c22000,0x28ee000600004000,0x6000000,0xc00000,0x0,0x0,0x3c04024000dac1e8,0x50608c000000c680,0x63401e3a232200,0x39a0b60000,0x7900000010000200,0x1800000001ad0,0x401f683d80000018,0xc2000c60044,0x408e4440077417c0,0xa00ce00000020000,0x3010031c7333006,0x3d501f00000,0xf800000000001800,0xc00223000fea0,0xc0004000000000]))) (bI j 26 (bI j 25 (cB [0x800000000000000,0x0,0x20000000000000,0x0,0x0,0x0,0x7803a80070000008,0x180044,0x1000000,0x75607c0000000000,0x844160001e000,0x72a0360000,0x1f00000010100000,0xc807818000001dd0,0xc00ff80000018,0x8013c82220,0x1002008780,0xca00000000c419,0x16a4ca000000000,0x60100000,0xa5260000,0x1000000000000000,0x12,0x80000000000,0x800008000,0x368484]) (cB [0x0,0xa00,0x5000000000000,0x0,0xa20000000908000,0xee48400000000000,0x1,0x2000000000,0x1000090000000000,0x3100,0x9498000000000,0x0,0x1f00000004000a00,0x1064000000400806,0x2204030080000002,0xd0031000000,0x8000001000018040,0x8190,0x40000000000000,0x0,0x20000000,0x0,0x20180400000010,0x88088000001])) (bI j 27 (cB [0x200002000000000,0x20,0x882000000000,0x0,0x0,0x800000000000,0x400886010000001,0xa002000000,0x0,0x100000000000,0x28000000800000,0x0,0x2208000,0x0,0x0,0x40000000000,0x20000000000000,0x243c00000020000,0x3600c4000000081,0x20008169000000,0x8800000030662000,0x3210000000000020,0x10,0x80000000000,0x0,0x40000]) (cB [0x4000000,0x200,0x1000000000000,0x800000000000,0x800000,0x400000000000000,0x2910000000,0x2444200000,0x0,0x1000,0x9080000000000,0x0,0x4004000,0x0,0x2,0x10000000000,0x0,0x1042200000008080,0x240084000000081,0x0,0x2000000020000000,0x200000,0x52,0x80080000000,0x0,0x40000])))))) (bI j 42 (bI j 35 (bI j 31 (bI j 29 (cB [0x0,0x200,0x5000000000000,0x0,0x2800000,0x5900000000000000,0x400822170000001,0x7306600000,0x1000000200441088,0x400000005900,0x0,0x4000000000280000,0x1000000014000000,0x1060000000000000,0x0,0x0,0x400,0x2000000020000,0x100000010000000,0x3a06008021800000,0x8000000073062041,0x10000100000000,0x2a0085000000001,0x4c418c000001,0x100a000,0x200060806]) (bI j 30 (cB [0x0,0x0,0x0,0x40000,0x4200000000041800,0xec00f03880080104,0x100000001,0x8000400000,0x28000002004410d8,0x2a08440000005883,0x6c000000000100,0x240000,0x1400000024000010,0x1061023910500882,0x201401090000000b,0x38830c00000,0x6000000000a00c00,0x200c000,0x0,0x4028021000000,0x80000000b0800000,0x403c0e0002004410,0xe0601ffc000000de,0x80411101,0x20888070303dde00,0x40048]) (cB [0x610444018005601,0x0,0x0,0x100080000200000,0x1000080,0x2000000000001000,0x0,0x0,0x0,0x0,0x30008004000000,0x888050012c020000,0x400000000000a20,0x1004000100000,0x10000000000008,0x8000000000,0x0,0x0,0x100000000000000,0x0,0x0,0x0,0x40,0x202080000000,0x30ccf0f0302e2200,0x40048]))) (bI j 33 (bI j 32 (cB [0x261044407cd80689,0x2b008000001900,0x308200032,0x800000,0xc020000000000000,0xc0c208000c8200,0x41006010000000,0x2012010400,0x0,0x10000000001000,0x0,0x800038300c020000,0x100000004024020,0x3127b0c44078181e,0x3d5c032280000006,0xa8012882220,0x4401001480058040,0x40000000000021,0x0,0x44078181e0100000,0x78000000a502790c,0x813c82200200c0c7,0x8061e19c00000018,0x1cc09e410001,0x200000e031a00200,0xe001]) (cB [0x0,0x20000000000,0x4200080200008,0x800000000,0x40000000000800,0x0,0x0,0x8000000000,0x100,0x0,0x20000000000000,0x8000000000000000,0x8900000012000000,0x3027945580641850,0x1000004000000005,0x21001000200,0xe41100102e041140,0x840a00000040409,0x2006200000601,0x0,0x2000000000000000,0x0,0x42510400000000,0x500c40000c])) (bI j 34 (cB [0x2000000000800000,0xc38008000000000,0x6b801c8a30020,0x100000000000000,0x1560000003400000,0x6a04f200800a0333,0x521890450000001,0x9502792dd0,0x3c82200201c08118,0x20080c0000002081,0x420600100060,0x800001004060000,0x10300000,0x0,0x8,0x0,0x6001006004a50840,0x400,0x0,0x4004038100100000,0x800000081802004,0xc01c8b200200cc80,0x6067fc000000ce,0xc409e6199e1,0xcc0c800030000,0xc620c]) (cB [0x2400004040800100,0x20000000210,0x82000002000,0x10000000500000,0x2000000000840000,0xe2008010c8080000,0x520001040000001,0xa500500e05,0x2000020201000800,0x80000001081,0x410000010000,0x80000000000000,0x2000000010200000,0x1000000040000001,0x2000008000000002,0x50802000020,0x38101000004000,0x3fe0000002c401,0x32004f20888009b,0x6018521f00000,0x800000010026104,0x30820003204290,0x1000082001000000,0x80000000,0x800009000])))) (bI j 38 (bI j 36 (cB [0x8,0x40000000000,0x0,0x820000,0x100000002000000,0x0,0x80000001,0x2000000,0x0,0x8000000000000,0x0,0x0,0x800000010000000,0x0,0x400000008,0x40000002000,0x8410018006017840,0x9c000000004189,0x60240208000003,0x410000100000,0x1000020100104,0x100000000200024,0x1000000000000010,0x80000000000,0x0,0x40000]) (bI j 37 (cB [0x800000000000400,0x400000000200,0x1001000000000,0x0,0x0,0x0,0x0,0x2000000000,0x2000000000000,0x4010040000001000,0x181841001810,0x80009000040,0x8000000000004000,0x40000,0x0,0x0,0x18000012000,0x10000000000000,0x40000000002,0x0,0x0,0x4,0x20000000000,0x800010000,0x208080083001de00,0x60243]) (cB [0x2000000004200000,0x200,0x1000000000000,0x0,0x2800000,0x4000000000000000,0x1,0xb000000400,0x21c00000,0x6000000000000001,0x4008000000000,0x8000080000000000,0xff00000013904000,0x3127b0c440001819,0xc000000000007,0x58000006020,0x0,0x40000000004008,0x0,0x44002b801ff00000,0xf800000150027904,0x52880200280c090,0x4820480400000008,0x800000214401001,0x400040800,0x40]))) (bI j 40 (bI j 39 (cB [0x2000004,0x0,0x0,0x810000,0x480000000000000,0x4000,0x40000000,0x0,0x20,0x8100000000000,0x40000000000040,0x80000,0x4000,0x0,0x10000000000,0x0,0x1000000000100,0x40020,0x4000000004c,0x0,0x10020000,0x102002000100000,0x6067fc000000ad,0x2d409e431100,0x8108800030000000,0x3e0000]) (cB [0x2000000000180000,0x1000000001f00,0xc000000000000,0x1010000600ffc000,0xdde00000000411e4,0x208400008000303,0x200187e670000000,0x4304200004,0x21000c0f008,0x40000000380,0x0,0x80000000020000,0x100000000800000,0x40000040000000,0x0,0x0,0x0,0x0,0x0,0x100000,0x800000000000000,0x200000000,0x80607a2400000000,0x10c108104708,0x40000000200,0x6004])) (bI j 41 (cB [0x4300004000b81e45,0x4404008000001010,0x80180002000,0x1,0x80,0x400000000000,0x2009010010000000,0x10000100300004,0x1200000000,0x0,0x800,0x4000000000000,0x100000000000000,0x42000040000000,0xc3f0080000000,0x60801c0a020,0x4000108006028000,0x32400,0x0,0x0,0x800000000000000,0x0,0x667aac00000000,0x21410c000100,0x8000303c0200,0x1a004]) (cB [0x4000000001,0xc0f228000000080,0x42821810ca088,0x10000e0788c000,0x200000010410e0,0x200700008030501,0x200,0x0,0x1000020000404008,0x804080,0x0,0x0,0x100000000000000,0x1001800040003010,0x2000000000000800,0x0,0x0,0x3c0200000000000,0x102004000080007,0x4000199e0100000,0xf800000181003814,0x823c82220000c03f,0x60dffc00000011,0x40000bc01e000000,0x840306c0200,0x5a083]))))) (bI j 49 (bI j 45 (bI j 43 (cB [0x0,0x10000000000000,0x20000,0x808060d804008,0xb00060,0x0,0x1836010000000,0x2d00180000,0x10000,0x80000000000000,0x1000400000000,0x4040000000,0x0,0x4000000,0x0,0x0,0x80000,0x400000000000000,0x419000000000000,0x4622018270900000,0x20007904,0x20000301000000,0x40601c2400000000,0x29c11a401104,0x800000000000,0x4008]) (bI j 44 (cB [0x500644110000000,0x1800000000000260,0x1822c0022000,0x10000800000000,0x80100,0x0,0x0,0x200400004,0x20001000000,0x4000000000000100,0x801000010000,0x0,0x800,0x4000000000000,0xc000000000000,0x11002006220,0x1000000040000,0x80801,0x8000004000,0x0,0x201040000,0x2000000,0x601ffc00000000,0x29491e411100,0x8800830090800,0x348485]) (cB [0x4200000204100000,0xa00,0x1000000000000,0x0,0x800000,0x4000000000000000,0x0,0x0,0x0,0x5000,0x28000000000000,0x0,0x4000000,0x6002000000041880,0x8000008,0x0,0x0,0x0,0x10c000000000000,0x0,0xa0000000,0x0,0x50,0x90808000000,0x312ffe00,0x20015e00f]))) (bI j 47 (bI j 46 (cB [0x4280000410189601,0x8010002f2,0x1000000000000,0x24000000,0xc022004000800100,0x5e00500000000312,0x90000000001,0x2000000000,0x1000010000048000,0x240000000001100,0x8000000000001,0x0,0x4000000,0xa005400000000090,0x100c038280010002,0x73923c82021,0x10100000000000,0x8000,0xc4004008ac4400,0x400040000000000,0x25240004,0x100020200020000,0x10,0x80014411100,0x0,0x200008400]) (cB [0x100000000,0xc0df78000000000,0x10823cc303220,0x181119061ed9c000,0x8c11e6,0x8800020000000,0x4741013010000000,0x2600098804,0x0,0x0,0x1000403800040,0x4000000000,0x8b00,0x2000,0x0,0x0,0x0,0x0,0x0,0x0,0x6,0x0,0x90404e2400000000,0x8c11e71c799,0x80000000000000,0x2000])) (bI j 48 (cB [0x0,0x0,0x180100001012,0x1819102c04d14000,0x20200000048011e6,0x420463040c8e1002,0x0,0x0,0x4000000,0x0,0x11000000002,0xccc88020e6020000,0x100000014200f32,0x8000803300301850,0xa,0x0,0x10000000000000,0x3375600000000400,0x14a08f3100c8a03,0x645810130100000,0x2d002208,0x5c00000400000,0x48404d1400000004,0x29411e6be595,0x30c0c88060264600,0x4208f]) (cB [0x2188206458201101,0x1008808000000210,0x5080000103200,0x0,0x0,0x0,0x0,0x8000000104000002,0x1003032201809808,0xc000040000005080,0x28000000800000,0xc0c8802326020000,0x100000034200f32,0x20038a2800181910,0x20c08778000001a,0xc0021000000,0x8000000006053bc0,0x81200000008190,0x40c84000004083,0x0,0x20000000,0x200000,0x1000000000000010,0x80000000000,0x0,0x40040])))) (bI j 52 (bI j 50 (cB [0x0,0x200,0x1000000000000,0x800000000000,0x800000,0x400000000000000,0x1884090000000,0x2444200000,0x0,0x100000001000,0x29080000000000,0x2000000000,0x4000000,0x20000000000000,0x2,0x50000000000,0x0,0x8008,0x8040000000004000,0x0,0xa0000000,0x1000000000000000,0x10600bbc00000050,0x680108000081,0x408820010200,0x240084]) (bI j 51 (cB [0x0,0x0,0x200000000002,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xc800000000000000,0x20c007780000000,0x10020000000,0x4000000106602ac0,0x200000028010,0x40080000000082,0x0,0x2000000000000000,0x208104008a08002,0x10c0008800000050,0x80106000000,0x3840000000,0x400c3]) (cB [0x4000000004000000,0xa00,0x0,0x0,0x0,0x4008300000000600,0x1000000000000,0xa004000000,0x0,0x0,0x0,0x86000000000,0x14008000,0x41804000041180,0x25c00620000001a,0xd0021800000,0xc000000106000000,0x48810,0x4000000000,0x0,0x5800000080040000,0x21800000020cc85,0x10400204000000c0,0x108000000,0x800000000,0x10000]))) (bI j 54 (bI j 53 (cB [0x43021901141000c4,0x1800510000001840,0x21c0000002,0x70800000000,0x18e0,0x108400000008000,0x1000001,0x0,0x0,0x0,0x8008000000800,0x86000002000,0x8700,0x42000000001000,0x8000008,0x0,0x0,0x10000000000000,0x101084000000086,0x411808010000,0x788000018c843814,0x821804028000c087,0x61c19c00000052,0x29410c0201c0,0x100000000008000]) (cB [0x807000101041,0x200000000a90,0x400000400000,0x247c880404320000,0x8000000029410c1,0x0,0x0,0x0,0x1000010000000200,0xc041880000000000,0x29410a02014001,0x80008000800000,0x2014204501,0x0,0x8382000000000,0xd0801e8c228,0x28080004000000,0x68400,0x0,0x50001e10cd00000,0x10000001ad043808,0x82143446c4408083,0xe0604ffc000000d6,0x8c110410101,0x208080b030e6ee00,0x4208c])) (bI j 55 (cB [0x10000000,0x809808100000010,0x5082188202024,0x0,0x0,0x200200c00020000,0x2000000000000,0x100010400,0x0,0x0,0x0,0x0,0x0,0x800000000000000,0x0,0x420004000,0x8514f89e0404e240,0x8c10,0x88020000000,0x202000000000000,0x2800000002042000,0x8218820203c5809a,0x260410000000090,0xa400e014400]) (cB [0x2310004070801001,0x210,0x0,0x2000000000,0x0,0x0,0x8000000000000,0x100000000,0x3c8e2203c0839808,0x5182,0x11004000000,0x8080d03327760000,0x100000014608a20,0x3001904040601013,0x40000000000001a,0x8004c0000,0x449e545e0404d140,0x264600000028c10,0x46083208080f06,0x8000038102000000,0x800000023003924,0x830c000202c10080,0x11]))))))) (bI j 84 (bI j 70 (bI j 63 (bI j 59 (bI j 57 (cB [0x4000004000201001,0xa38,0x0,0x800000000,0x0,0x408000040040000,0x603013010000000,0xa384000004,0x3c8e0203c08c9808,0x6047fc000000d1c2,0x68411800000003,0x1e021980000,0x34200600,0x3103000000009010,0x12,0x0,0x20001000,0x231200000020000,0x34208600200000b,0x100000000,0x40000,0x8208018000840080,0x80400000000042,0x4106000000,0x40200000,0x80]) (bI j 58 (cB [0x4000000000001000,0x1000000800000000,0x20c0010000,0x0,0x2000000001000,0x8000000000002,0x10001000000,0x8000000c84200c00,0x30820200c0c09ff8,0x664eec0000001182,0x29c11c40010060,0x80302004020000,0x5e08c00,0x8000100000080000,0x8c08012200000000,0x53823893ca8,0xe41010060c008880,0x8c11,0x460cf000080304,0x400030000000000,0x2a3046000,0x0,0x100,0x0,0x80800060040000,0x54608c]) (cB [0x4791c04018118200,0x5c08ff8000003a30,0x19082280000000,0x1e0040618404000,0xa8c51d0,0x8000040000000,0x3811450000001,0x40032104300010,0x200,0x1000000000082,0xc10800048082,0xc000800010,0x4000000000208000,0x1040000000004000,0x20000000000000,0x820000000,0x5400000000001000,0x228a20000002c11,0x242083040000013,0x8000820004000000,0xb8000001090408a0,0x823c82020100c31b,0x60c60400000001,0x1100684108000600,0x200000,0x4]))) (bI j 61 (bI j 60 (cB [0x4390414022300345,0x1410,0x82000008000,0x100c0678ccc000,0x60200000021c11e4,0x1c00400008070200,0x80000000000003,0x10800098000,0x1c9b428984801a28,0xc00c8c0000004382,0xc10e41010080,0x80b04000020000,0x404700,0x0,0x0,0x0,0x8000100008000040,0x20a00,0x0,0x0,0x0,0x0,0x0,0x80000100,0x8045200000,0x4]) (cB [0x200404020300301,0x1808008000000828,0x10000000000000,0x0,0x0,0x0,0x201183010000000,0x18e80790d04,0x1c104000c0c88008,0x1c700,0x0,0x20000000,0xff00000000000000,0x30479453e2201863,0xc18c080000000,0x2200108212082c0,0x40000,0xc60200000000010,0x18800f23aa80402,0x1003018500100000,0xcc000801,0x0,0x0,0x0,0x200000])) (bI j 62 (cB [0x400400000000000,0x4801c48000000000,0x43821ca817118,0x8080000000000,0x80080,0xc00602e24061000,0x202000000000001,0x304380002,0x1000010001000000,0x100,0x800800008000,0x40400000000000,0x400400,0x0,0x1000000000000000,0x100100e810,0x8000000000040000,0x7fe00000000800,0x20208f208080017,0x407098001f00000,0x1067100,0x2040000,0x0,0x0,0x20220000,0x40020000e]) (cB [0x0,0x0,0x0,0x101c2000004000,0x80000008c4,0x0,0x8000000000000,0x20000004000000,0x4000100,0x80,0x2,0x0,0x0,0x0,0x2840000000000000,0x0,0xc000101c20000040,0x42008,0x210000300000010,0x448018a70c00000,0x100021463904,0x2000000,0x262d80000080010,0x4000a400e000001,0x8101600000,0x1])))) (bI j 66 (bI j 64 (cB [0x4000004400000400,0x800000000,0x1000002000,0x1010022400d14000,0x42410e0,0x1208130000011400,0x1863ff0000002,0x8704791c44,0x3c00880180c28ff8,0x6010004000004780,0x381800041112c0,0x0,0x0,0x4000000,0x4000000000000,0x8000,0x2004c00c06140040,0x20000023000,0x0,0x0,0x880000000001000,0x400880180c280,0x46,0x20002000000,0x22006030a20000,0x100000152087]) (bI j 65 (cB [0x1000,0x831808000000000,0xc700380e26004,0x5020020000000000,0x7760000004200126,0xa08f20008020330,0x181f83990000001,0x18d04780004,0x1ce00644c1801918,0x660ffc000000c682,0x21411e49e54440,0xd000304000000000,0xff00000031900334,0x1047904040003803,0x2c1c000f80000000,0x832c00020,0x8000001008000000,0x0,0x0,0x2000000000000,0x0,0x2000000,0x7000440000000000,0x40000016000000,0x40]) (cB [0x0,0x800000000000800,0x804000200000002,0x10800000400,0x80,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x42000,0x2c10000000000000,0x1c00000,0x1000000008,0x3000000000004,0x103088000080007,0x20100000000,0x80000021040000,0x0,0x80000400000000,0x40202000000100,0x40000000,0x20000080]))) (bI j 68 (bI j 67 (cB [0x2180004058200001,0x1000000000100000,0x800002000000000,0x11118006a1c18000,0x2008418e4,0x4000000000080000,0x403a96000000100,0x8000802300380000,0x22000002000,0x418c004000000002,0x10c50e411f0000,0x20000070a0002000,0xbb10000008600308,0x1846004040003803,0x1c08dd80000008,0x100802000000,0xe000400,0x8000,0x0,0x38110000000,0xf880000021040000,0xc23c8e020000cc1f,0x606447fc000000c6,0xe3c01e082000,0x88c3030082000,0x340c03]) (cB [0x0,0xc88800000000000,0xd1821c104000c,0x1000000600ffc400,0xffe00000001001e0,0xa00f00808000300,0x440180e510000000,0x780424,0x1400000200c87008,0x2000000500,0x0,0x0,0x0,0x0,0x0,0x20,0x100000000000,0x4000000000000,0x1000000,0x400000000000000,0x4000000000000000,0x801402030000c052,0x6000a000000020,0x2080,0x400000001000])) (bI j 69 (cB [0x780000000190fff,0xc870080020000f0,0x5001400000a0,0x201,0x0,0x0,0x190e010004000,0xa00280000,0x0,0x0,0x800800000000,0x8000000000,0x0,0x0,0x0,0x100005000200000,0x6010108806019440,0x10801,0x80000,0x2422000000000000,0x42002004,0x8014020200020000,0x2080000000000002,0x8000100,0x80800000000000]) (cB [0x400000000000,0x2000040,0x8,0x1000100606bbc000,0x59200000001401e0,0x4800d00804081a00,0x2,0x402,0x400000000100,0x0,0x1008000,0x801080e004c60000,0x4800d00,0x4000000000,0x800000,0x2000002004,0x4010020000000000,0xf4ce00000000000,0xe00f008000c03,0x0,0x800000000102004,0x800412000b808812,0x1,0x0,0x90000022004200,0x208000]))))) (bI j 77 (bI j 73 (bI j 71 (cB [0x400068100241,0x10b0,0x8400041200004,0x1460990400b24000,0x1c01e1,0x800000000,0x0,0x0,0x1002000100000000,0x800000000100,0x200000,0x8000400000000000,0x6300000000400400,0x5006804000407002,0x1c30000080000000,0x801402000,0x200000000,0x8000000000000,0x0,0x0,0x0,0x410000,0x0,0x802010000,0x82000000]) (bI j 72 (cB [0x180400000400000,0x831208000000000,0x84801e0a30020,0x1000000000000000,0x0,0x0,0x281940410000000,0x10900600408,0x0,0x0,0x0,0x8002a03335d60000,0x4100000000200f04,0xd002004001581102,0x400000000000000,0x4400412000,0x2012000006462ac0,0xc359a00000043201,0x21a00f008000903,0x880c910026300000,0xf80000010d006a64,0x803c4311e200c0df,0x40690400000002,0x108401e830991,0x80000800000000,0x800000]) (cB [0x400000000000,0x100000004000,0x40000,0x1000000000000000,0x4820000010000000,0x5000f51809080203,0x2,0x400,0x0,0x6441040000000000,0x4a800821002120,0x0,0x0,0x3106004220640000,0x2020000000000000,0x2802402000,0x10000208000000,0x400,0x2008408400800,0x0,0x8800000001004000,0x803c56116a90881a,0x0,0x4010010001,0x10d4588022026000,0x219009]))) (bI j 75 (bI j 74 (cB [0x7a0623449100351,0x80000000000010d0,0x8480255200424,0x1000013600ffc000,0x3e00000041001e0,0x800e008000e9300,0x140000000000000,0x0,0x30020003a0000008,0x0,0x0,0x0,0x0,0x0,0x200000000000000,0x1000000000002000,0xc010000004400000,0x2000000800040001,0xc008000002,0x400,0x0,0x0,0x0,0x0,0x80000022000000,0x400020000c]) (cB [0x0,0x100000000000,0x200000000002,0x10000000000,0x0,0x28000,0x1748100410000002,0x602400,0x4000000,0x800000000000,0x41001801000002,0x8000e90000020080,0x21000c00,0x8000024000008000,0xc00c172c00000010,0x800002303c02000,0x2010000006009000,0x400009000,0x8000000,0x1000000000,0x1000000000000,0x20000000000,0x8000000000,0x10000002000,0x80000000000000])) (bI j 76 (cB [0x400100000000,0x80000000020000,0x0,0x1064b800008,0x80003001a0,0x8020,0x0,0x0,0x0,0x0,0x1000400,0x1000000000400008,0x840000,0x200004000000000,0x20c017780000000,0x202080c02000,0x2010000104009040,0x8042,0x0,0x8000000002000000,0x0,0x0,0x0,0x10002010000,0x1040000000]) (cB [0x82400114110241,0x4000,0x0,0x1200010440080000,0x4820000004120000,0x1000000800018200,0x8000000000000a,0x10800082400,0x3c120008a2881648,0x8000,0x401000010,0x900008a201500000,0xc900000021900c00,0xc0068040000c9002,0x620000000000010,0x86000412000,0xe83010000606ffc0,0x348200000101c41,0x4620d4184f0002,0x0,0x100004,0x4000000001,0x0,0x400010000,0x8440c03223fe00,0x81e00f])))) (bI j 80 (bI j 78 (cB [0x441e0180400,0x606,0x0,0x0,0x0,0x0,0x601910010000000,0x40800080023,0x0,0x6440040000000000,0x102000200088180,0x0,0x1000100,0x4100804000000000,0x410000000000040,0x200000000000,0xe890144404469040,0x100001,0x8000000,0x8400019182000000,0x800000104806a0c,0x380602404080d2,0x2000000000000284,0x420002890020,0x800002f007fe00,0x800f]) (bI j 79 (cB [0x58040005938001f,0x8000000000000040,0xc,0x1000164000004000,0x120,0x10000,0x90000000000000,0x1000000000400,0x48000000,0x0,0x64,0x8000102200800010,0x82000000b00,0x4804000081100,0x41000,0x0,0x0,0x2008200000000000,0x9048002b24,0x403001a0e5200000,0x8004206804,0x4020008000000,0x4000000001000,0x20000002000000,0x2361c0000,0x41000c00d]) (cB [0x80400100000000,0x831200002000000,0x22100340a3d400,0x1000000000000000,0x4c60000010000000,0xf04800222a20,0x181bff0000000,0x10d007a0c04,0x3d1202888088d208,0x6441040000008000,0x40801809006520,0x0,0xff00000000000000,0xf007804008481911,0xa40c020000020010,0x90000102221,0x0,0x0,0x1,0x0,0x800200000000004,0x304000c240c882,0x40660fec00001085,0x1e090004,0x8002303f07b200,0x21800f]))) (bI j 82 (bI j 81 (cB [0x78e408998310263,0xc80dd8000001088,0x8640040240000,0x1000020780f74000,0x7fe00000043001e0,0x1800f1c9111103c0,0x1818ef0000002,0x400000,0x3000010006c0c778,0x616bbc0000001000,0x8009841000060,0x80007820a7034000,0x4004c20,0x0,0xc08294080000000,0x12013080000,0x0,0x0,0x8000008000200,0x20000000000,0x100000000000000,0x10000]) (cB [0x400000010000,0xccc778000002000,0x52503807c8002,0x3e40010060004000,0x2b08180,0x1100000100000000,0x5998ab0000000,0x2000700002,0x2000000,0x0,0x0,0x40000001120000,0x4000f00,0x8000800020004000,0x8960006680000000,0x12003814c90,0x80000000000,0x15600000000200,0x4000f00004001c,0x200038000100000,0x100020020007800,0x100000000,0x80000000,0x0,0xc400180000200,0x20000004400b])) (bI j 83 (cB [0x600002000200089,0x208,0x0,0x5808003060224000,0xb201e0,0x4000000,0xb818ef0000004,0x2000500001,0x2880000140c8d778,0x444d070000001005,0x80284410000e8,0x0,0x0,0x0,0x1408892080000000,0x11010880000,0x0,0x0,0x4100000000400,0x40000000000,0x200000080000000,0x10000,0x0,0x400000,0x5022248300,0x50142]) (cB [0x10000008000000,0xc3c778000000080,0x11043a003c001,0x1e0008018004000,0xa82140,0x1000080010000000,0x21e18ef0000000,0x128405fe080,0x9f0400010300008,0x9520,0x800110000000,0x200070f0ce0000,0x4000e00,0x2000,0x0,0x0,0xe000040000001140,0x8001,0x10001000020004,0x19224a000cd00000,0x22007041,0x2000080000000,0x200000000000000,0x8008000040,0x2001c000ce00,0x4000f])))))) (bI j 98 (bI j 91 (bI j 87 (bI j 85 (cB [0x380001000580001,0x2000002200,0x800,0x804002800005000,0x8a00000029080a0,0x5400fa20c200140c,0x0,0x40001,0x2c00008004f0c668,0x1000,0x2,0x0,0x6700000000000000,0x8005a6089089a000,0xc3c3380000002,0x3000000,0x80000600061e19c0,0x300200000108441,0x84000e010010000,0x0,0x2000,0x18040080000000,0x80000000000002,0x1000018000000,0x0,0x4]) (bI j 86 (cB [0x200000000000000,0xcfc118000000009,0x380000000,0x6020000018004000,0x30001c0,0x0,0x0,0x0,0x3c00000000ffc008,0x80008c0000000000,0x1001f80000225,0x10022533f0ce0000,0x100000000000e07,0x7000027800100180,0x10000000000008,0x0,0x2082000008000000,0xf0ce00000000200,0xf000000007,0x6015526100000,0x800000003021800,0x8280,0x40]) (cB [0x21800006000aac07,0x30,0x0,0xe1e08c000,0x20180,0x0,0x2000010000000,0x8001000000,0x0,0x67e19c0000000000,0x3e01e01c00000,0x0,0x100000000000400,0xc00783c800000180,0x8,0x0,0x81046089061e3bc0,0xf0ce00000000401,0x8a00f02ae00403,0x7012080600100000,0xc1000815,0x0,0x8001800400000000,0x124000055e00,0x201000000000000,0x10001]))) (bI j 89 (bI j 88 (cB [0x70500822499f8ab,0x10,0x100100401000,0x20001000000000,0x19a0000000000031,0x200e0f33066d000,0x0,0x200201100,0x3c208c1121000558,0x2000000000180,0x820000000080,0x1000000,0x800000000000000,0x2000000402000000,0x1210004480000000,0x100c03000801,0x0,0x3011200000000000,0x41f00f0ae304480,0x0,0x7800000000002011,0x3800000005c0c7,0x20656bbc00000000,0x409c400001,0x220000,0x8]) (cB [0x200,0x48a9608000000000,0x338800001c,0x0,0x0,0x1000,0x8000200000000,0x400000,0x0,0x0,0x0,0x0,0x0,0x100000,0x240aa96080000000,0x4811800000,0x400000200000800,0x179de00000002000,0x4284e000009003,0x40000000,0x6800000000000000,0x213800021c044560,0x200000000000000,0x0,0x100000000])) (bI j 90 (cB [0x0,0x0,0x0,0x200000008000,0x1de0000000210000,0x1280f3c3300003c3,0x9e18cd0000002,0x780000,0x2400000004000000,0x0,0x0,0x1101134000ce0000,0xef00000001000f4c,0x7007814600001878,0x800cfc5580000000,0x41803c0ab80,0x2040200000000000,0xcf19a00000002000,0x1e00f028d00003,0x0,0x1800000000000210,0x803d3a7404480301,0x6662ac00000007,0x14000000,0x100500033315600,0x14000a]) (cB [0x8541078000006009,0xccc778000000a20,0x2814c8089,0xda000406662ac000,0x200000023601e0,0xa00506d00030430,0x19b2000670000001,0x805a6998,0x2c00000001c0c778,0x746bbc0000000000,0x429600000180,0x2000000,0x800,0x1,0x10000000000,0x0,0x8000,0x0,0x4,0x0,0x0,0x0,0x80000000000000,0x0,0x3000000000])))) (bI j 94 (bI j 92 (cB [0x1000000000000000,0xc0c448000000000,0x4040200000000,0xc04004000,0x2000400,0x400,0x383512610000000,0xe580000,0x1000000,0x6a73bc0000000000,0x8409600101800,0x8000000,0x800000000000000,0x4000000002000,0x0,0x0,0x0,0x0,0x0,0x0,0x3800000020000000,0x12c00221c015460,0x80000000000000,0x0,0xf000030f1de00,0x8610f]) (bI j 93 (cB [0x4000000003818ab,0x100c008000000008,0x5040200001000,0x8000c00225000,0x2020180,0x100,0x3998ab0000000,0x8081400000,0x1400008,0x6663bc0000004000,0x3601e05800000,0x1070003030020000,0x8940000055900b04,0xc80782082000d800,0x4000000000028,0x0,0x60f6000006663bc0,0x80e00000023201,0x11ac4300080f001,0x23c401819ff00000,0x7800000000004082,0x883d04132000c0c7,0x1061e19c00000011,0x8441e820998,0x100200800000000,0x8002]) (cB [0x600000004200000,0x1,0x2,0x2000010000000000,0x8a0000010000000,0x4e20b4536ea24003,0x0,0x20000000800,0x2d0413200100c118,0x1188,0x100410000000000,0x0,0x100000000200000,0x1000008264002018,0x22,0x0,0xe878990000660040,0x188401,0x1200000000000,0x50401818ef00000,0x480000002400780e,0x3c278f932000c4,0x13,0x20000]))) (bI j 96 (bI j 95 (cB [0x200802000000000,0x300c118000000020,0x1200340702820,0x1000100000000000,0x0,0x800,0x4000000000000,0x500800,0x3e8f32820003c008,0x1000,0x2000000,0x0,0x100000000000000,0xa3b8401800,0xc00000000000002,0x0,0x0,0x0,0x0,0x0,0x5800000000000008,0x3c07028a10ccc5,0x2400608c00000050,0xb001a9ba363,0x18677cc830f3fe00,0x20c]) (cB [0x301b33006800000,0x1000000000000001,0x188300011002,0x88010000000000,0x4080,0x620c03644008000,0xc40b819ff0000000,0x100708223,0x38c111e2408a9e80,0x10000083,0x400000000000,0x800002000000,0x1c00000000008800,0x142708227cc008ad,0x800000002,0x2000022,0xef8eef1001804400,0x42501,0x12009500010034,0x63c401879ff00000,0x700789e,0x80254c1440080000,0x486667fc00000004,0x142aecf5,0x104478807033fe00,0x200b])) (bI j 97 (cB [0xe588223c60151370,0x100010,0x8000000000c,0x0,0x2200000000000400,0x100800444880202,0x1000000201,0x0,0x2000000200000800,0x2a34580000000002,0x840962099f900,0x88000000200000,0x1000000000000800,0x31878827bc400061,0x201c0cdd80000004,0x100402001112,0x80100000000,0x22200000000401,0x101028010448804,0x0,0xf800000000000000,0xc03c4f11e200cccf,0x1000000000000106,0x806010008080,0x17f4788003022200,0x11900b]) (cB [0x4400000000,0x6c00ff8000000010,0x300000002,0x1000060614ffc000,0x7000000000000984,0xf208000c0300,0x2000000000,0x2000000,0x20000200,0x0,0x0,0x0,0x0,0x100002,0x800000000000008,0x40000000000,0x8000,0xa7fe00000400000,0x4c208000f83,0x400,0x2000000000000,0x0,0x80000000000000,0x8000000000410000]))))) (bI j 105 (bI j 101 (bI j 99 (cB [0x0,0x1000000000000000,0x40000000000,0x1000060000000000,0x7000000008020000,0xc000000f830a,0x100000000040003,0x400,0x2000000000000,0xe007100000000000,0xc0001c00000010,0x20030200a0,0x520040000e00,0x40000,0x8000000000000,0x100003402000,0x0,0x80000,0x0,0x8000000000,0x20000,0x0,0x60060400000100,0x800042001c080000,0x80000020000000,0x20002c]) (bI j 100 (cB [0x780400004100000,0xc01c00000003000,0x40040003c0200032,0x1000060000000010,0x2000000,0x30000,0xc1801810000001,0x200028000780080,0x3c820000c1829d10,0x9540000000000001,0x9e000001e0,0x40a0000000,0x400010004c00,0x0,0x0,0x0,0x0,0x40000002000008,0x4f208000f02,0x10000000000,0x80016000]) (cB [0x182080000000000,0x0,0x800000000,0x1000000c14e00010,0x700008000a020980,0x1904f2380003023a,0x180182dff0040007,0x62600000,0x3c82003000c020c0,0x6010000000000000,0x8002641010000,0x0,0x0,0x8000001000004,0x20000000000,0x1000000000000000,0x10000,0x8,0x80,0x70000040000000,0x0,0x20,0x60019c01000000,0x80400000000,0x83018ce00,0x2000040210]))) (bI j 103 (bI j 102 (cB [0x0,0x0,0x0,0x0,0x40000000000,0x0,0x0,0x0,0x4000000c20c06000,0x80001000,0x2000000000,0x85000880000,0x200004000200,0x20000000000000,0x2,0x10000000000,0x0,0x100,0x40002000000081,0x0,0x0,0x0,0x1020100000000000,0x4000080026010100,0x30000000000,0x10]) (cB [0x800000000000000,0x0,0x0,0x0,0x4000,0x0,0x4000000000,0x800000,0xc00000001c00110,0x1008,0x8008000000000,0x0,0x14000000,0x8000000000000,0x14000000000000,0x10400000000,0x0,0x3000000000000000,0x59003018000001,0x800000200,0xf800000000000000,0x313000003c20c16f,0x800000,0x4000000000000000])) (bI j 104 (cB [0x200000,0x10000000,0x0,0x0,0x8300000008020000,0xc00000f08305,0x7000000000020000,0x20000000,0x3800000021c002e0,0x40000000c0010000,0x8000000000,0x0,0x0,0x400000000000000,0x204000000000020,0x3800003,0x0,0x1000000000,0x0,0x60418041800000,0x1080000007804,0x100000003c000000,0x0,0x1104,0x200]) (cB [0x0,0x2000000000000,0x300,0x600e0b6e8000,0x9e0,0x4000000000300,0x6000000000000200,0x0,0x30000000014160c0,0x10051,0x0,0x8003001358300000,0x2000419c4f03,0x800000000000080,0xcc0ff80000020,0x42503803d98,0x106003bc0,0x31de00000000040,0x40210000000083,0x41800ef00000,0x420000000])))) (bI j 109 (bI j 107 (bI j 106 (cB [0x0,0x0,0x0,0x1080008c000,0x20000000804260,0x4001300000000000,0x10000000,0x2000000000,0x0,0x0,0x0,0x0,0x100000000000000,0x8000000042000,0x2,0x0,0x6010000100600040,0x8042,0x0,0x4b800ef00000,0x20101000,0x90880000060c812,0x10,0x0,0x641020080c000000,0x250a02]) (cB [0x1800000043800ef,0x1c00338000000001,0x80c0000002,0x8200000400000000,0x0,0x2000000000000,0x0,0x800000,0x21c00008,0x48,0x0,0x20000,0x0,0x0,0x80000000,0x4c00000,0x0,0x0,0x0,0x43800ab00000,0x900000,0x0,0x106603bc00000000,0x1032406030000,0x0,0x200])) (bI j 108 (cB [0x182480004018001,0x8c9,0x0,0x13e007fc000,0x3fe00000000001e0,0xf00000008700,0x1000000000000,0x2080,0x3c10510021c00008,0x0,0x0,0x0,0xff00000000000000,0xc80781c00004d981,0x260c04480000000,0x146403c1fc00,0x100000000,0x33fe00000083000,0x620f410080003,0x278001819ff00000,0xf800000023106208,0x8730821103c0c01f,0x211,0x800000010000,0x4384f00003300200,0x4720f]) (cB [0x800000000000,0x5c00ff8000002000,0x11188380011001,0x1a0640904000,0x88c79c4,0x800000202,0x1e00010000000,0x32b507f2381,0x3d0e020000cccff8,0x6007fc00000307c8,0x183c01e08e8e000,0x8000f02004000000,0xb001c020,0x0,0x0,0x80000000,0x40000000ae007fc0,0x227fe00000000001,0x14a200000503,0x4005018034000000,0x7900,0x100000000000010,0x800000000000000,0x0,0x4000040000]))) (bI j 111 (bI j 110 (cB [0x2000020,0x0,0x0,0x0,0x4000000000000000,0x30000,0x2000000002,0x100000000000,0x28800003d0c89ff8,0x10000005,0x200000000000000,0x0,0x0,0x0,0x800000000020000,0x0,0x10000000,0x80000000,0x0,0x2000000000000,0x500,0x0,0xe8644d0000000000,0x800400014000001,0x4000000000,0x100]) (cB [0x10000018000000,0x2c00e40000000000,0x8000380000001,0x200000101,0x800,0x0,0x21000000000000,0x10000700000,0x0,0x600d000000040000,0x1e40100148,0x700000000009,0x40000020,0x80000000,0x1000000000020000,0x200000000000,0x6000000096005880,0x28200090000001,0xb000000002,0x200000000049,0x0,0x28800000808000])) (bI j 112 (cB [0x2000000000080000,0x0,0x0,0x600504000,0x8000080160,0x0,0x0,0x20000208000000,0x2c80000090800000,0x600d000000000000,0x40001e40000148,0x50e226c40808,0x4f20,0x27800000782550,0x0,0x4000010000000,0xe400001e04008000,0x9,0x0,0x0,0x0,0x53f882001408b9a,0xa865400000100085,0x800428014100200]) (cB [0x874007b0001861ff,0x7c00ff8000000420,0x3c0000001,0x96007fc000,0x3fe00000080001e0,0x1400fe208000570c,0x1819ff0000000,0x500780c04,0x3f8e220000c3cff8,0x6007fc0000000780,0x3c01f028ee000,0x8000f02004000000,0x30004081,0x0,0x8000000000000,0x204000,0x108ee0006000040])))))))) 103 (i / 1 % 16)

def zo := zc zcj zcr zmi (fun i => zt zcr (cutPick zcG (zmd i))) 1805 zkP zdS zma zvJ zpa
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ztB : ze zcj zcr zmi (zt zcr zcG) zmC (zD 1805 zkP zdS zma 0) zdd 12 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zpu : tB 0 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zro : tB 24 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zwK : tB 48 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem znq : tB 72 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zqt : tB 96 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zvB : tB 120 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ztq : tB 144 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zxA : tB 168 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zwM : tB 192 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zpG : tB 216 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zsp : tB 240 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zuX : tB 264 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ztu : tB 288 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zmD : tB 312 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zmV : tB 336 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zsX : tB 360 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ztm : tB 384 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zsS : tB 408 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zwo : tB 432 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zqd : tB 456 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zuW : tB 480 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zsc : tB 504 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zvd : tB 528 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem znt : tB 552 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zqb : tB 576 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zoE : tB 600 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ztG : tB 624 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zoz : tB 648 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zuc : tB 672 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zoD : tB 696 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zwh : tB 720 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zwT : tB 744 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zoo : tB 768 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zte : tB 792 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zut : tB 816 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zqa : tB 840 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zxW : tB 864 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zrS : tB 888 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ztT : tB 912 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zxn : tB 936 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zoS : tB 960 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zqi : tB 984 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zwY : tB 1008 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ztL : tB 1032 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zvh : tB 1056 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zpn : tB 1080 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zwb : tB 1104 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zvl : tB 1128 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ztd : tB 1152 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zvn : tB 1176 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zpD : tB 1200 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zvO : tB 1224 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zts : tB 1248 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zxI : tB 1272 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zpM : tB 1296 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zox : tB 1320 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zvI : tB 1344 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zta : tB 1368 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zqc : tB 1392 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zoV : tB 1416 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zrX : tB 1440 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zsK : tB 1464 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zrA : tB 1488 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zsQ : tB 1512 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zxo : tB 1536 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zqK : tB 1560 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zql : tB 1584 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zmt : tB 1608 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zsR : tB 1632 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zvj : tB 1656 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ztf : tB 1680 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ztW : tB 1704 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zxV : tB 1728 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zmE : tB 1752 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zrl : tB 1776 24 zo = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zpQ : tB 1800 5 zo = true := by decide +kernel
theorem zoM : tB 0 48 zo = true := tM (start := 0) (left := 24) (right := 24) (check := zo) zpu zro
theorem zsC : tB 48 48 zo = true := tM (start := 48) (left := 24) (right := 24) (check := zo) zwK znq
theorem zvi : tB 0 96 zo = true := tM (start := 0) (left := 48) (right := 48) (check := zo) zoM zsC
theorem zwR : tB 96 48 zo = true := tM (start := 96) (left := 24) (right := 24) (check := zo) zqt zvB
theorem zrC : tB 168 48 zo = true := tM (start := 168) (left := 24) (right := 24) (check := zo) zxA zwM
theorem zpr : tB 144 72 zo = true := tM (start := 144) (left := 24) (right := 48) (check := zo) ztq zrC
theorem zxz : tB 96 120 zo = true := tM (start := 96) (left := 48) (right := 72) (check := zo) zwR zpr
theorem zqf : tB 0 216 zo = true := tM (start := 0) (left := 96) (right := 120) (check := zo) zvi zxz
theorem zve : tB 216 48 zo = true := tM (start := 216) (left := 24) (right := 24) (check := zo) zpG zsp
theorem zuS : tB 288 48 zo = true := tM (start := 288) (left := 24) (right := 24) (check := zo) ztu zmD
theorem zmH : tB 264 72 zo = true := tM (start := 264) (left := 24) (right := 48) (check := zo) zuX zuS
theorem zsd : tB 216 120 zo = true := tM (start := 216) (left := 48) (right := 72) (check := zo) zve zmH
theorem zmK : tB 336 48 zo = true := tM (start := 336) (left := 24) (right := 24) (check := zo) zmV zsX
theorem zsD : tB 408 48 zo = true := tM (start := 408) (left := 24) (right := 24) (check := zo) zsS zwo
theorem znu : tB 384 72 zo = true := tM (start := 384) (left := 24) (right := 48) (check := zo) ztm zsD
theorem zsr : tB 336 120 zo = true := tM (start := 336) (left := 48) (right := 72) (check := zo) zmK znu
theorem znb : tB 216 240 zo = true := tM (start := 216) (left := 120) (right := 120) (check := zo) zsd zsr
theorem zog : tB 0 456 zo = true := tM (start := 0) (left := 216) (right := 240) (check := zo) zqf znb
theorem zoP : tB 456 48 zo = true := tM (start := 456) (left := 24) (right := 24) (check := zo) zqd zuW
theorem zxP : tB 504 48 zo = true := tM (start := 504) (left := 24) (right := 24) (check := zo) zsc zvd
theorem zpZ : tB 456 96 zo = true := tM (start := 456) (left := 48) (right := 48) (check := zo) zoP zxP
theorem zrI : tB 552 48 zo = true := tM (start := 552) (left := 24) (right := 24) (check := zo) znt zqb
theorem zrp : tB 624 48 zo = true := tM (start := 624) (left := 24) (right := 24) (check := zo) ztG zoz
theorem zuq : tB 600 72 zo = true := tM (start := 600) (left := 24) (right := 48) (check := zo) zoE zrp
theorem znJ : tB 552 120 zo = true := tM (start := 552) (left := 48) (right := 72) (check := zo) zrI zuq
theorem ztJ : tB 456 216 zo = true := tM (start := 456) (left := 96) (right := 120) (check := zo) zpZ znJ
theorem ztQ : tB 672 48 zo = true := tM (start := 672) (left := 24) (right := 24) (check := zo) zuc zoD
theorem zqo : tB 744 48 zo = true := tM (start := 744) (left := 24) (right := 24) (check := zo) zwT zoo
theorem zqC : tB 720 72 zo = true := tM (start := 720) (left := 24) (right := 48) (check := zo) zwh zqo
theorem zwr : tB 672 120 zo = true := tM (start := 672) (left := 48) (right := 72) (check := zo) ztQ zqC
theorem zrf : tB 792 48 zo = true := tM (start := 792) (left := 24) (right := 24) (check := zo) zte zut
theorem zxM : tB 864 48 zo = true := tM (start := 864) (left := 24) (right := 24) (check := zo) zxW zrS
theorem zmz : tB 840 72 zo = true := tM (start := 840) (left := 24) (right := 48) (check := zo) zqa zxM
theorem zry : tB 792 120 zo = true := tM (start := 792) (left := 48) (right := 72) (check := zo) zrf zmz
theorem zmy : tB 672 240 zo = true := tM (start := 672) (left := 120) (right := 120) (check := zo) zwr zry
theorem zuK : tB 456 456 zo = true := tM (start := 456) (left := 216) (right := 240) (check := zo) ztJ zmy
theorem ztK : tB 0 912 zo = true := tM (start := 0) (left := 456) (right := 456) (check := zo) zog zuK
theorem zpT : tB 912 48 zo = true := tM (start := 912) (left := 24) (right := 24) (check := zo) ztT zxn
theorem zsj : tB 960 48 zo = true := tM (start := 960) (left := 24) (right := 24) (check := zo) zoS zqi
theorem zxu : tB 912 96 zo = true := tM (start := 912) (left := 48) (right := 48) (check := zo) zpT zsj
theorem zwV : tB 1008 48 zo = true := tM (start := 1008) (left := 24) (right := 24) (check := zo) zwY ztL
theorem zrK : tB 1080 48 zo = true := tM (start := 1080) (left := 24) (right := 24) (check := zo) zpn zwb
theorem zuY : tB 1056 72 zo = true := tM (start := 1056) (left := 24) (right := 48) (check := zo) zvh zrK
theorem zvb : tB 1008 120 zo = true := tM (start := 1008) (left := 48) (right := 72) (check := zo) zwV zuY
theorem zqq : tB 912 216 zo = true := tM (start := 912) (left := 96) (right := 120) (check := zo) zxu zvb
theorem zxC : tB 1128 48 zo = true := tM (start := 1128) (left := 24) (right := 24) (check := zo) zvl ztd
theorem zna : tB 1200 48 zo = true := tM (start := 1200) (left := 24) (right := 24) (check := zo) zpD zvO
theorem zou : tB 1176 72 zo = true := tM (start := 1176) (left := 24) (right := 48) (check := zo) zvn zna
theorem zrF : tB 1128 120 zo = true := tM (start := 1128) (left := 48) (right := 72) (check := zo) zxC zou
theorem zph : tB 1248 48 zo = true := tM (start := 1248) (left := 24) (right := 24) (check := zo) zts zxI
theorem ztr : tB 1320 48 zo = true := tM (start := 1320) (left := 24) (right := 24) (check := zo) zox zvI
theorem znj : tB 1296 72 zo = true := tM (start := 1296) (left := 24) (right := 48) (check := zo) zpM ztr
theorem zrk : tB 1248 120 zo = true := tM (start := 1248) (left := 48) (right := 72) (check := zo) zph znj
theorem zrH : tB 1128 240 zo = true := tM (start := 1128) (left := 120) (right := 120) (check := zo) zrF zrk
theorem zvN : tB 912 456 zo = true := tM (start := 912) (left := 216) (right := 240) (check := zo) zqq zrH
theorem zvV : tB 1368 48 zo = true := tM (start := 1368) (left := 24) (right := 24) (check := zo) zta zqc
theorem zsa : tB 1416 48 zo = true := tM (start := 1416) (left := 24) (right := 24) (check := zo) zoV zrX
theorem zwZ : tB 1368 96 zo = true := tM (start := 1368) (left := 48) (right := 48) (check := zo) zvV zsa
theorem zsw : tB 1464 48 zo = true := tM (start := 1464) (left := 24) (right := 24) (check := zo) zsK zrA
theorem znW : tB 1536 48 zo = true := tM (start := 1536) (left := 24) (right := 24) (check := zo) zxo zqK
theorem ztn : tB 1512 72 zo = true := tM (start := 1512) (left := 24) (right := 48) (check := zo) zsQ znW
theorem zot : tB 1464 120 zo = true := tM (start := 1464) (left := 48) (right := 72) (check := zo) zsw ztn
theorem zok : tB 1368 216 zo = true := tM (start := 1368) (left := 96) (right := 120) (check := zo) zwZ zot
theorem zqL : tB 1584 48 zo = true := tM (start := 1584) (left := 24) (right := 24) (check := zo) zql zmt
theorem znY : tB 1656 48 zo = true := tM (start := 1656) (left := 24) (right := 24) (check := zo) zvj ztf
theorem znw : tB 1632 72 zo = true := tM (start := 1632) (left := 24) (right := 48) (check := zo) zsR znY
theorem zqR : tB 1584 120 zo = true := tM (start := 1584) (left := 48) (right := 72) (check := zo) zqL znw
theorem zuB : tB 1704 48 zo = true := tM (start := 1704) (left := 24) (right := 24) (check := zo) ztW zxV
theorem zoO : tB 1776 29 zo = true := tM (start := 1776) (left := 24) (right := 5) (check := zo) zrl zpQ
theorem ztv : tB 1752 53 zo = true := tM (start := 1752) (left := 24) (right := 29) (check := zo) zmE zoO
theorem zuP : tB 1704 101 zo = true := tM (start := 1704) (left := 48) (right := 53) (check := zo) zuB ztv
theorem zxL : tB 1584 221 zo = true := tM (start := 1584) (left := 120) (right := 101) (check := zo) zqR zuP
theorem zso : tB 1368 437 zo = true := tM (start := 1368) (left := 216) (right := 221) (check := zo) zok zxL
theorem ztH : tB 912 893 zo = true := tM (start := 912) (left := 456) (right := 437) (check := zo) zvN zso
theorem znf : tB 0 1805 zo = true := tM (start := 0) (left := 912) (right := 893) (check := zo) ztK ztH
theorem zoU : tB 0 1805 zo = true := znf
theorem zrM : Known zcG := (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) zlZ) zss) zra) zjp) zdG) znK) zqx) zfk) zuh) zgv) zdV) zwx) zsg) zlV) zft) zjG) zjK) zbG) zcA) zcd) zeH) zoQ) zbU) zpH) zji) zeE) zlX) zex) zfb) zbK) zif) zvH) zgV) zqY) zcu) znP) zuy) zxO) zkT) zpt) zcU) zpf) zqj) zly) zww) zsM) zwQ) zbN) zsv) zsu) zrb) ztV) zqh) zwI) zqM) zcS) zxr) zrG) zvv) zcE) ztD) zsn) zxK) zvg) zdg) zwH) ztA) zbT) zvr) zuH) zsk) zcM) zmY) zoZ) zxJ) zcL) zrW) ztZ) zsh) zxh) zde) zjN) zdF) zcp) zpA) zpy) zpe) zpC) zmO) zuE) zcX) zcV) zob) zgt) zsJ) zpO) ztO) zrg) zmv) zcZ) zvK) zcJ) zmM)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zuQ : Lower zcj zdd zcr 13 := by
  apply lowerDag zmd _ _ _ _ zua _ _ _ zrM _ ztB zoU
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold pW; decide +kernel
  · exact cK (by decide +kernel)
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [zcG,List.mem_cons,List.not_mem_nil,or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
end PEqualNP.Outside.L_meta_46994

open PEqualNP.Outside.L_meta_46994 in
theorem PEqualNP.Outside.L_meta_46994 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4294901482 * 2 ^ 32 + 4276808904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4294901482 * 2 ^ 32 + 4276808904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  intro t h
  let raw : List (BitVec 64) := [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]
  let goal : BitVec 64 := 0xfffefeeafeeaecc8
  have root : Lower (fM 64) (raw.map BitVec.toNat) goal.toNat 13 :=
    hcsLowerEq (by decide +kernel) (by decide +kernel) (by decide +kernel) zuQ
  have size : 13 ≤ t :=
    hcsLower (n := 6) raw goal 13 _ (by decide +kernel) (by decide +kernel) root t h
  let circuit : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or,[0,1]⟩,⟨.or,[0,2]⟩,⟨.or,[1,4]⟩,⟨.and,[6,3]⟩,⟨.or,[6,3]⟩,⟨.and,[4,5]⟩,⟨.or,[9,11]⟩,⟨.and,[2,12]⟩,⟨.or,[7,12]⟩,⟨.and,[10,14]⟩,⟨.or,[8,5]⟩,⟨.and,[15,16]⟩,⟨.or,[13,17]⟩],18⟩
  refine ⟨circuit,?_,?_,by decide +kernel⟩
  · intro gate member
    simp only [circuit,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · exact Nat.le_trans (by decide +kernel : circuit.size ≤ 13) size

