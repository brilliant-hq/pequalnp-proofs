import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_47823

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

theorem zl {select inverse : Fin rows → Fin rows} {mask goal : Nat} {move : (List (List (Nat × Nat) × List (Nat × Nat)))}
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

def zbk (m : (List (List (Nat × Nat) × List (Nat × Nat)))) (ws : List Nat) : List Nat :=
  List.rec [] (fun w _ next => insertWord (mixMove m w) next) ws

theorem zby {m : (List (List (Nat × Nat) × List (Nat × Nat)))} {ws : List Nat} {select : Fin rows → Fin rows}
    (agree : ∀ w ∈ ws,mixMove m w = relabel select w) :
    (zbk m ws).toFinset = ws.toFinset.image (relabel select) := by
  induction ws with
  | nil => simp [zbk]
  | cons w ws ih =>
    change (insertWord (mixMove m w) (zbk m ws)).toFinset = _
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

def zq {α : Type} (word : Nat) (cont : Nat → α) : α :=
  Nat.rec (cont 0) (fun k _ => cont (k + 1)) word

theorem zU {α : Type} (word : Nat) (cont : Nat → α) :
    zq word cont = cont word := by cases word <;> rfl

def zab (words : List Nat) (cont : List Nat → Bool) : Bool :=
  (List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k [])
    (fun w _ next k => zq w (fun v => next (fun rest => k (v :: rest)))) words) cont

theorem zaw (words : List Nat) (cont : List Nat → Bool) :
    zab words cont = cont words := by
  induction words generalizing cont with
  | nil => rfl
  | cons w ws ih =>
    change zq w (fun v => zab ws (fun rest => cont (v :: rest))) = _
    rw [zU,ih]

def zb (target : Nat) (state : (Nat × List Nat × List (Nat × Nat × Nat))) (bound : (Nat × List Nat × Nat × Nat)) : Bool :=
  let (mask,stock,lower,goal) := bound
  let (fuel,ws,history) := state
  (target &&& mask) == goal && goal != 0 && goal != mask &&
    zq (fuel - flatCount mask ws) (fun remaining =>
      if Nat.blt remaining lower then
        zab (recipeStart mask stock ws) (fun start =>
          if Nat.blt (start.length + remaining) lower then
            zab (recipeClosure mask stock history start) (fun needed =>
              if Nat.blt (needed.length + remaining) lower then
                zab (replayRecipes mask needed history.reverse stock) (fun replay =>
                  decide (replay.length + remaining < lower) &&
                    ws.all (fun w => availableB mask (replay ++ stock) (w &&& mask)))
              else false)
          else false)
      else false)

theorem zn (target : Nat) (state : (Nat × List Nat × List (Nat × Nat × Nat))) (bound : (Nat × List Nat × Nat × Nat)) :
    zb target state bound = boundCloses target state bound := by
  obtain ⟨fuel,ws,history⟩ := state
  obtain ⟨mask,stock,lower,goal⟩ := bound
  simp [zb,boundCloses,zaw,zU,Nat.blt_eq]

def zt (target : Nat) (bounds : List (Nat × List Nat × Nat × Nat)) (state : (Nat × List Nat × List (Nat × Nat × Nat))) : Bool :=
  List.rec false (fun bound _ later => zb target state bound || later) bounds

theorem zbw (target : Nat) (bounds : List (Nat × List Nat × Nat × Nat)) (state : (Nat × List Nat × List (Nat × Nat × Nat))) :
    zt target bounds state = knownCloses target bounds state := by
  induction bounds with
  | nil => rfl
  | cons bound bounds ih =>
    change (zb target state bound || zt target bounds state) =
      (boundCloses target state bound || knownCloses target bounds state)
    rw [zn,ih]

def za (witnesses : List (Nat × Nat × Nat)) (ws : List Nat) : Bool :=
  witnesses.all (fun entry => ws.contains (witnessWord entry))

def zw (mask : Nat) (stock : List Nat) (fuel : Nat) (forest : (Nat → Nat × Nat))
    (i : Nat) : Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
    (fun _ previous j =>
      let (parent,token) := forest j
      if parent == 0 then
        if token < 2 ^ stock.length then some (rootState stock fuel token) else none
      else (previous (parent - 1)).bind (childState mask token)) (fuel + 1)) i

def zz (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
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
               | some m => saved.2.1 == zbk m state.2.1

def zF (directed : Bool) (ws : List Nat) : Nat → Nat → Bool :=
  List.rec
    (fun p n => Nat.beq p 0 || Nat.beq n 0)
    (fun w _ rest p n =>
      Nat.beq p 0 || Nat.beq n 0 ||
      zq (p &&& w) (fun up =>
        zq (n &&& w) (fun down =>
          rest up down &&
            zq (p ^^^ up) (fun offP =>
              zq (if directed then n else n ^^^ down) (rest offP))))) ws

theorem zbu {v w : Nat} {i : Nat} (bit : (v ^^^ (v &&& w)).testBit i = true) :
    v.testBit i = true ∧ w.testBit i = false := by
  rw [Nat.testBit_xor,Nat.testBit_and] at bit
  cases hv : v.testBit i <;> cases hw : w.testBit i <;> simp [hv,hw] at bit ⊢

theorem zG {directed : Bool} {ws : List Nat} {positive negative : Nat}
    (fail : zF directed ws positive negative = false) :
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
      zq (positive &&& w) (fun up =>
        zq (negative &&& w) (fun down =>
          zF directed ws up down &&
            zq (positive ^^^ up) (fun offP =>
              zq (if directed then negative else negative ^^^ down)
                (zF directed ws offP))))) = false at fail
    simp only [zU,Bool.or_eq_false_iff,Bool.and_eq_false_iff] at fail
    rcases fail.2 with on | off
    · obtain ⟨p,n,hp,hn,agree⟩ := ih on
      rw [Nat.testBit_and,Bool.and_eq_true] at hp hn
      refine ⟨p,n,hp.1,hn.1,?_⟩
      intro a ha
      rcases List.mem_cons.mp ha with rfl | tail
      · simp [hp.2,hn.2]
      · exact agree _ tail
    · obtain ⟨p,n,hp,hn,agree⟩ := ih off
      have hp' := zbu hp
      cases mode : directed
      · have hn' : negative.testBit n = true ∧ w.testBit n = false := by
          apply zbu
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

theorem zbp {mask goal : Nat} {ws : List Nat} {k t : Nat} {directed : Bool}
    (goalMask : Masked mask goal) (live : LiveWord mask goal k t ws.toFinset)
    (noNot : directed = true → t = 0) :
    zF directed ws goal (mask ^^^ goal) = true := by
  by_contra fail
  have openPair : zF directed ws goal (mask ^^^ goal) = false := by
    cases h : zF directed ws goal (mask ^^^ goal) <;> simp_all
  obtain ⟨p,n,hp,hn,agree⟩ := zG openPair
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

def zak (tags : List (Nat × Nat)) (use : List (Nat × Nat) → Bool) : Bool :=
  (List.rec (motive := fun _ => (List (Nat × Nat) → Bool) → Bool) (fun k => k [])
    (fun tag _ next k =>
      zq tag.1 (fun up => zq tag.2 (fun down =>
        next (fun tail => k ((up,down)::tail))))) tags) use

theorem zao (tags : List (Nat × Nat)) (use : List (Nat × Nat) → Bool) :
    zak tags use = use tags := by
  induction tags generalizing use with
  | nil => rfl
  | cons tag rest ih =>
    obtain ⟨a,b⟩ := tag
    change zq a (fun up => zq b (fun down =>
      zak rest (fun tail => use ((up,down)::tail)))) = _
    simp only [zU,ih]

def zC (directed : Bool) (full : Nat) (tag : (Nat × Nat)) : Nat :=
  if directed then tag.1 &&& (tag.2 ^^^ full) else tag.1 ^^^ tag.2

def zj (acc : (Nat × Nat × Nat)) (column : Nat) : (Nat × Nat × Nat) :=
  (acc.1 ||| column,acc.2.1 ||| (acc.1 &&& column),acc.2.2 ||| (acc.2.1 &&& column))

def zi (directed : Bool) (full : Nat) (tags : List (Nat × Nat))
    (use : (Nat × Nat × Nat) → Bool) : Bool :=
  (List.rec (motive := fun _ => ((Nat × Nat × Nat) → Bool) → Bool) (fun k => k (0,0,0))
    (fun tag _ more k =>
      zq (zC directed full tag) (fun column =>
        more (fun acc =>
          zq (acc.1 ||| column) (fun once =>
            zq (acc.2.1 ||| (acc.1 &&& column)) (fun twice =>
              zq (acc.2.2 ||| (acc.2.1 &&& column)) (fun thrice => k (once,twice,thrice)))))))
    tags) use

theorem zf (directed : Bool) (full : Nat) (tags : List (Nat × Nat))
    (use : (Nat × Nat × Nat) → Bool) : zi directed full tags use =
    use (tags.foldr (fun tag acc => zj acc (zC directed full tag)) (0,0,0)) := by
  induction tags generalizing use with
  | nil => rfl
  | cons tag tags ih =>
    change zq (zC directed full tag) (fun column =>
      zi directed full tags (fun acc =>
        zq (acc.1 ||| column) (fun once =>
          zq (acc.2.1 ||| (acc.1 &&& column)) (fun twice =>
            zq (acc.2.2 ||| (acc.2.1 &&& column)) (fun thrice => use (once,twice,thrice)))))) = _
    simp only [zU,ih]
    rfl

def zba (value : Nat) : Nat :=
  (Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ offset => offset)
    (fun i next w offset =>
      let shift := 1 <<< i
      zq (w >>> shift) (fun upper =>
        if Nat.beq upper 0 then next w offset else next upper (offset+shift))) 8) value 0

def zam (sample : (Nat × Nat)) (full : Nat) (normal tight : (Nat × Nat × Nat))
    (x y out : (Nat × Nat)) (directed : Bool) (op keep : Nat) : List Nat :=
  let counts := if directed then tight else normal
  let dx := if keep.testBit 0 then 0 else zC directed full x
  let dy := if op == 2 || keep.testBit 1 then 0 else zC directed full y
  let rest := counts.2.2 ||| (counts.2.1 ^^^ (counts.2.1 &&& dx &&& dy)) |||
    (counts.1 ^^^ (counts.1 &&& (dx ||| dy)))
  zq ((rest ||| zC directed full out) ^^^ full) (fun missing =>
    if Nat.beq missing 0 then [] else [uP sample.1 18 (zba missing)])

def zaY (mask goal : Nat) (directed : Bool) (ws : List Nat) (pairs : List Nat) : Bool :=
  pairs.any fun code =>
    let p := code &&& 511
    let n := code >>> 9
    goal.testBit p && mask.testBit n && !goal.testBit n &&
      ws.all (fun w => if directed then !(w.testBit p) || w.testBit n
                       else w.testBit p == w.testBit n)

theorem zB {mask goal : Nat} {ws : List Nat} {pairs : List Nat} {k t : Nat} {directed : Bool}
    (masked : Masked mask goal) (live : LiveWord mask goal k t ws.toFinset)
    (noNot : directed = true → t = 0) : zaY mask goal directed ws pairs = false := by
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

def zaW (mask goal : Nat) (chart : Option ({ rows : List Nat // rows.length = 24 }))
    (cut : ((Nat × List Nat × List (Nat × Nat × Nat)) → Bool)) (state : (Nat × List Nat × List (Nat × Nat × Nat))) : Bool :=
  let (fuel,ws,_) := state
  ws.length > fuel + 1 ||
    (!ws.contains goal &&
      (fuel == 0 ||
        (if ws.length == fuel + 1 then !zF true ws goal (mask ^^^ goal)
         else !zF false ws goal (mask ^^^ goal)) ||
        (if ws.length == fuel + 1 then
           chart.any (fun c => !PackedRect.rectOK1 (ws.map (chartWord c)))
         else false) || cut state))

def zL (n op keep : Nat) : Nat :=
  (n - (if keep.testBit 0 then 0 else 1) -
    (if op == 2 || keep.testBit 1 then 0 else 1)) + 1

def zap (n fuel token : Nat) : Bool :=
  zL n (token / 4 % 3) (token % 4) > (fuel-1) + 1

def zbr (ws : List Nat) (op keep x y : Nat) : List Nat :=
  keepWord (op == 2 || keep.testBit 1) y (keepWord (keep.testBit 0) x ws)

def zI (mask op x y : Nat) : Nat :=
  if Nat.beq op 0 then x &&& y else if Nat.beq op 1 then x ||| y else mask ^^^ x

def zo (mask : Nat) (state : (Nat × List Nat × List (Nat × Nat × Nat))) (a b op keep x y out : Nat) : Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  let (fuel,ws,history) := state
  if fuel == 0 || b ≥ ws.length || (if op == 2 then a != b || keep ≥ 2 else a ≥ b) then none
  else if out == 0 || out == mask || ws.contains out then none
  else
    some (fuel-1,insertWord out (zbr ws op keep x y),(out,x,y) :: history)

theorem zaz {mask a b op keep : Nat} {state : (Nat × List Nat × List (Nat × Nat × Nat))}
    (hb : b < 64) (hop : op < 3) (hk : keep < 4) :
    let x := state.2.1.getD a 0
    let y := state.2.1.getD b 0
    zo mask state a b op keep x y (zI mask op x y) =
      childState mask (gateToken a b op keep) state := by
  obtain ⟨fuel,ws,history⟩ := state
  obtain ⟨keepEq,opEq,aEq,bEq⟩ := gateTokenFields (a := a) hb hop hk
  simp only [childState,keepEq,opEq,aEq,bEq]
  rfl

def zD (stock : List Nat) (positive negative width : Nat) : List (Nat × (Nat × Nat)) :=
  (List.rec (motive := fun _ => Nat → List (Nat × (Nat × Nat))) (fun _ => [])
    (fun w _ next i => (w,uP positive width i,uP negative width i) :: next (i+1)) stock) 0

def zbn (bank : List (Nat × (Nat × Nat))) (token : Nat) : List (Nat × (Nat × Nat)) :=
  (List.rec (motive := fun _ => Nat → List (Nat × (Nat × Nat))) (fun _ => [])
    (fun tag _ next k =>
      if Nat.beq (k &&& 1) 0 then next (k >>> 1) else tag :: next (k >>> 1)) bank) token

def zax (keep : Bool) (w : Nat) (bank : List (Nat × (Nat × Nat))) : List (Nat × (Nat × Nat)) :=
  if keep then bank
  else List.rec [] (fun tag tail next => if Nat.beq tag.1 w then tail else tag :: next) bank

def zaZ (tag : (Nat × (Nat × Nat))) (bank : List (Nat × (Nat × Nat))) : List (Nat × (Nat × Nat)) :=
  List.rec [tag] (fun old tail next => if Nat.ble tag.1 old.1 then tag :: old :: tail else old :: next) bank

def zA (mask full token : Nat) (bank : List (Nat × (Nat × Nat))) : List (Nat × (Nat × Nat)) :=
  let keep := token % 4
  let op := token / 4 % 3
  let x := bank.getD (token / (4*3*64)) (0,0,0)
  let y := bank.getD (token / (4*3) % 64) (0,0,0)
  let tag := (zI mask op x.1 y.1,zI full op x.2.1 y.2.1,zI full op x.2.2 y.2.2)
  zaZ tag (zax (op == 2 || keep.testBit 1) y.1 (zax (keep.testBit 0) x.1 bank))

def zr (mask width : Nat) (root : List (Nat × (Nat × Nat))) (fuel : Nat) (forest : (Nat → Nat × Nat))
    (i : Nat) : List (Nat × Nat) :=
  let tags := (Nat.rec (motive := fun _ => Nat → List (Nat × (Nat × Nat))) (fun _ => [])
    (fun _ previous j =>
      let (parent,token) := forest j
      if Nat.beq parent 0 then zbn root token
      else zA mask (fM width) token (previous (parent-1))) (fuel+1)) i
  List.rec [] (fun tag _ rest => tag.2 :: rest) tags

def zbe (ws : List Nat) : Nat :=
  List.rec 0 (fun w _ tail => (w &&& fM 64) ||| (tail <<< 64)) ws

def zbd (n : Nat) : Nat :=
  Nat.rec 0 (fun _ more => 1 ||| (more <<< 64)) n

def zbf (a b : Nat) (left right : Bool) : Nat :=
  (if left then 0 else 1 <<< (64*a)) ||| (if right then 0 else 1 <<< (64*b))

def zbo (mask goal packed marks erased out : Nat) (directed : Bool) (pairs : List Nat) : Bool :=
  pairs.any fun code =>
    zq code (fun code =>
      zq (code &&& 511) (fun p =>
        zq (code >>> 9) (fun n =>
          let up := (packed >>> p) &&& marks
          let down := (packed >>> n) &&& marks
          let contrast := if directed then up &&& (down ^^^ marks) else up ^^^ down
          let gateOK := if directed then !out.testBit p || out.testBit n else out.testBit p == out.testBit n
          goal.testBit p && mask.testBit n && !goal.testBit n && Nat.blt p 64 && Nat.blt n 64 &&
            gateOK && Nat.beq (contrast &&& (marks ^^^ erased)) 0)))

theorem zbA {ws : List Nat} {i row : Nat} (inside : i < ws.length) (width : row < 64) :
    (zbe ws).testBit (64*i+row) = (ws.getD i 0).testBit row := by
  induction ws generalizing i with
  | nil => simp at inside
  | cons w ws ih =>
    change ((w &&& fM 64) ||| (zbe ws <<< 64)).testBit (64*i+row) = _
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

theorem zbx {length i : Nat} (inside : i < length) :
    (zbd length).testBit (64*i) = true := by
  induction length generalizing i with
  | zero => omega
  | succ length ih =>
    change (1 ||| (zbd length <<< 64)).testBit (64*i) = true
    rw [Nat.testBit_or,Nat.testBit_shiftLeft]
    cases i with
    | zero => simp
    | succ i =>
      have hi : i < length := by omega
      have crossed : 64 ≤ 64*i.succ := by omega
      have offset : 64*i.succ-64 = 64*i := by omega
      simp [crossed,offset,ih hi]

def ze (mask goal : Nat) (chart : Option ({ rows : List Nat // rows.length = 24 })) (cut : ((Nat × List Nat × List (Nat × Nat × Nat)) → Bool))
    (reference : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool) (state : (Nat × List Nat × List (Nat × Nat × Nat))) (sample : (Nat × Nat)) (tags : List (Nat × Nat)) : Bool :=
  let n := state.2.1.length
  (n ≤ 64) && !state.2.1.contains goal &&
  zq (zbe state.2.1) (fun packed =>
    zq (zbd n) (fun marks =>
      zak tags (fun tags =>
    zq (fM sample.2) (fun full =>
      zi false full tags (fun normal =>
        zi true full tags (fun tight =>
          let visit := fun a b op retains =>
            zq (state.2.1.getD a 0) (fun x =>
              zq (state.2.1.getD b 0) (fun y =>
                zq (zI mask op x y) (fun out =>
                  let xs := tags.getD a (0,0)
                  let ys := tags.getD b (0,0)
                  zq (zI full op xs.1 ys.1) (fun up =>
                    zq (zI full op xs.2 ys.2) (fun down =>
                      tB 0 retains (fun keep =>
                        let token := gateToken a b op keep
                        if zap n state.1 token then true else
                          let directed := zL n op keep == (state.1-1)+1
                          let pairs := zam sample full normal tight xs ys (up,down) directed op keep
                          let erased := zbf a b (keep.testBit 0) (op == 2 || keep.testBit 1)
                          if zbo mask goal packed marks erased out directed pairs then true
                          else match zo mask state a b op keep x y out with
                          | none => true
                          | some (fuel,ws,history) => zab ws (fun forced =>
                            let child := (fuel,forced,history)
                            reference token child || zaW mask goal chart cut child)))))))
          tB 0 n (fun a =>
            visit a a 2 2 && tB (a+1) (n-(a+1)) (fun b =>
              tB 0 2 (fun op => visit a b op 4)))))))))

def zZ (mask : Nat) (ws : List Nat) : Bool :=
  (ws.dedup.length == ws.length) && ws.all (fun w => w &&& mask == w)

theorem zM {mask : Nat} {ws : List Nat} (ok : zZ mask ws = true) :
    ws.Nodup ∧ ∀ w ∈ ws,Masked mask w := by
  simp only [zZ,Bool.and_eq_true,beq_iff_eq,List.all_eq_true] at ok
  exact ⟨List.nodup_iff_length_dedup_eq.mpr ok.1,ok.2⟩

def zc (mask goal : Nat) (chart : Option ({ rows : List Nat // rows.length = 24 })) (cut : Nat → ((Nat × List Nat × List (Nat × Nat × Nat)) → Bool))
    (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (moves : Array (List (List (Nat × Nat) × List (Nat × Nat)))) (links : (Nat → Nat → Option (Nat × Nat)))
    (sample : (Nat × Nat)) (tags : Nat → List (Nat × Nat)) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some (fuel,ws,history) => zab ws (fun forced =>
      zZ mask forced && ze mask goal chart (cut i)
        (zz count states moves links (i+1)) (fuel,forced,history) sample (tags i))

def zd (mask goal : Nat) (chart : Option ({ rows : List Nat // rows.length = 24 })) (cut : ((Nat × List Nat × List (Nat × Nat × Nat)) → Bool))
    (witnesses : List (Nat × Nat × Nat)) (reference : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool) (stock : List Nat)
    (fuel : Nat) : Bool :=
  tB 0 (2^stock.length) fun token =>
    let state := rootState stock fuel token
    !za witnesses state.2.1 || zaW mask goal chart cut state || reference token state

theorem zbs {mask goal : Nat} {chart : Option ({ rows : List Nat // rows.length = 24 })}
    {cut : ((Nat × List Nat × List (Nat × Nat × Nat)) → Bool)} {state : (Nat × List Nat × List (Nat × Nat × Nat))}
    (masked : Masked mask goal) (chartOK : ∀ c,chart = some c → ChartOK goal c)
    (viable : WordViable mask goal state) (noCut : cut state = false) :
    zaW mask goal chart cut state = false := by
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
    simp [zaW,fit,hm]
  by_cases tight : ws.length = fuel + 1
  · have ht : t = 0 := by omega
    subst t
    have dir := zbp (directed := true) masked live (fun _ => rfl)
    have noChart : chart.any (fun c => !PackedRect.rectOK1 (ws.map (chartWord c))) = false := by
      cases opt : chart with
      | none => rfl
      | some c =>
        have vt : WordViable mask goal (fuel,ws,[]) := viable
        have ok := tightChart (chartOK c opt) tight vt
        simp [ok]
    simp [zaW,fit,hz,tight,dir,noCut,noChart]
  · have sep := zbp (directed := false) masked live (by simp)
    simp [zaW,fit,hz,tight,sep,noCut]

theorem zaL (w : Nat) (ws : List Nat) :
    (insertWord w ws).length = ws.length + 1 := by
  induction ws with
  | nil => rfl
  | cons a ws ih =>
    change (if w ≤ a then w :: a :: ws else a :: insertWord w ws).length = _
    split <;> simp [ih]

theorem zay (keep : Bool) (w : Nat) (ws : List Nat) :
    ws.length - (if keep then 0 else 1) ≤ (keepWord keep w ws).length := by
  cases keep
  · exact List.le_length_erase
  · simp [keepWord]

theorem zQ {mask token : Nat} {state child : (Nat × List Nat × List (Nat × Nat × Nat))}
    (eval : childState mask token state = some child)
    (wide : zap state.2.1.length state.1 token = true) :
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
  rw [zaL]
  have h1 := zay a x ws
  have h2 := zay b y (keepWord a x ws)
  have h : ws.length - (if a then 0 else 1) - (if b then 0 else 1) + 1 > fuel - 1 + 1 :=
    of_decide_eq_true wide
  dsimp only [rest]
  omega

theorem zbj {ws : List Nat} {x w : Nat} {keep : Bool}
    (nd : ws.Nodup) (h : w ∈ keepWord keep x ws) : w ∈ ws ∧ (keep = true ∨ w ≠ x) := by
  cases keep
  · simpa [keepWord,nd.mem_erase_iff,and_comm] using h
  · simpa [keepWord] using h

theorem zbz {ws : List Nat} (nd : ws.Nodup) (keep : Bool) (x : Nat) :
    (keepWord keep x ws).Nodup := by
  cases keep
  · exact nd.erase x
  · exact nd

theorem zbb {mask goal out : Nat} {ws : List Nat} {directed : Bool}
    {pairs : List Nat} {a b : Nat} {left right : Bool}
    (nd : ws.Nodup)
    (checked : zbo mask goal (zbe ws) (zbd ws.length)
      (zbf a b left right) out directed pairs = true) :
    zaY mask goal directed
      (out :: keepWord right (ws.getD b 0) (keepWord left (ws.getD a 0) ws)) pairs = true := by
  obtain ⟨code,mem,verdict⟩ := List.any_eq_true.mp checked
  apply List.any_eq_true.mpr
  refine ⟨code,mem,?_⟩
  simp only [zU,Bool.and_eq_true,Nat.blt_eq] at verdict
  obtain ⟨⟨⟨⟨⟨⟨hp,hn⟩,neg⟩,wp⟩,wn⟩,output⟩,closure⟩ := verdict
  refine Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨
    Bool.and_eq_true_iff.mpr ⟨hp,hn⟩,neg⟩,List.all_eq_true.mpr ?_⟩
  intro w hw
  rcases List.mem_cons.mp hw with rfl | later
  · exact output
  have rightMem := zbj (zbz nd left (ws.getD a 0)) later
  have leftMem := zbj nd rightMem.1
  obtain ⟨i,inside,eq⟩ := List.mem_iff_getElem.mp leftMem.1
  have atIndex : ws.getD i 0 = w := by
    simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem inside] using eq
  have omitted : (zbf a b left right).testBit (64*i) = false := by
    have cleared (j : Nat) (keep : Bool) (h : keep = true ∨ w ≠ ws.getD j 0) :
        (if keep then 0 else 1 <<< (64*j)).testBit (64*i) = false := by
      rcases h with yes | diff
      · simp [yes]
      · have ne : i ≠ j := fun same => diff (same ▸ atIndex).symm
        cases keep <;> simp [Nat.shiftLeft_eq,Nat.testBit_two_pow,show 64*j ≠ 64*i by omega]
    simp [zbf,Nat.testBit_or,cleared a left leftMem.2,cleared b right rightMem.2]
  let p := code &&& 511
  let n := code >>> 9
  let marks := zbd ws.length
  let signal := zbe ws
  have mark : marks.testBit (64*i) = true := zbx inside
  have test {j : Nat} (within : j < 64) :
      ((signal >>> j) &&& marks).testBit (64*i) = w.testBit j := by
    rw [Nat.testBit_and,Nat.testBit_shiftRight,mark,Bool.and_true,
      Nat.add_comm j,zbA inside within,atIndex]
  have h := congrArg (fun word => Nat.testBit word (64*i)) (Nat.beq_eq.mp closure)
  simp only [Nat.zero_testBit] at h
  change (((if directed then (signal >>> p &&& marks) &&& ((signal >>> n &&& marks) ^^^ marks)
      else (signal >>> p &&& marks) ^^^ (signal >>> n &&& marks)) &&&
    (marks ^^^ zbf a b left right)).testBit (64*i)) = false at h
  have pt := test (j := p) wp
  have nt := test (j := n) wn
  cases directed <;> cases px : w.testBit p <;> cases nx : w.testBit n <;>
    simp [px,nx,pt,nt,Nat.testBit_and,Nat.testBit_xor,mark,omitted,p,n] at h ⊢

theorem zaP {mask goal a b op keep out : Nat} {state child : (Nat × List Nat × List (Nat × Nat × Nat))}
    (masked : Masked mask goal) (viable : WordViable mask goal child)
    (parent : state.2.1.Nodup) (eval : zo mask state a b op keep
      (state.2.1.getD a 0) (state.2.1.getD b 0) out = some child) (pairs : List Nat) :
    zbo mask goal (zbe state.2.1) (zbd state.2.1.length)
      (zbf a b (keep.testBit 0) (op == 2 || keep.testBit 1)) out
      (zL state.2.1.length op keep == (state.1-1)+1) pairs = false := by
  obtain ⟨fuel,ws,history⟩ := state
  let x := ws.getD a 0
  let y := ws.getD b 0
  apply Bool.eq_false_iff.mpr
  intro closed
  have closed := zbb parent closed
  let bad : Bool := fuel == 0 || b ≥ ws.length || (if op == 2 then a != b || keep ≥ 2 else a ≥ b)
  let stale : Bool := out == 0 || out == mask || ws.contains out
  let bank := zbr ws op keep x y
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
  rw [List.toFinset_card_of_nodup nd,zaL] at size
  have same : (out::bank).toFinset = (insertWord out bank).toFinset := by
    ext w
    simp only [List.mem_toFinset,List.mem_cons,insertWordMem]
  have openBank := zB (pairs := pairs)
    (directed := zL ws.length op keep == (fuel-1)+1) masked (show LiveWord mask goal k t (out::bank).toFinset by rwa [same])
  have available : (zL ws.length op keep == (fuel-1)+1) = true → t = 0 := by
    intro directed
    have exactBudget := beq_iff_eq.mp directed
    have first := zay (keep.testBit 0) x ws
    have second := zay (op == 2 || keep.testBit 1) y (keepWord (keep.testBit 0) x ws)
    change zL ws.length op keep = (fuel-1)+1 at exactBudget
    unfold zL at exactBudget
    dsimp only [bank,zbr] at size
    omega
  have refuses := openBank available
  exact Bool.noConfusion (closed.symm.trans refuses)

theorem zk {mask goal : Nat} {chart : Option ({ rows : List Nat // rows.length = 24 })}
    {cut : ((Nat × List Nat × List (Nat × Nat × Nat)) → Bool)} {ref : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool} {state child : (Nat × List Nat × List (Nat × Nat × Nat))} {sample : (Nat × Nat)} {tags : List (Nat × Nat)} {a b op keep : Nat}
    (checked : ze mask goal chart cut ref state sample tags = true)
    (ha : a < state.2.1.length)
    (legal : (a = b ∧ op = 2 ∧ keep < 2) ∨ (a < b ∧ b < state.2.1.length ∧ op < 2 ∧ keep < 4))
    (eval : childState mask (gateToken a b op keep) state = some child)
    (masked : Masked mask goal) (viable : WordViable mask goal child) (nd : state.2.1.Nodup)
    (openChild : zaW mask goal chart cut child = false) :
    ref (gateToken a b op keep) child = true := by
  have narrow : zap state.2.1.length state.1 (gateToken a b op keep) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have tooMany := zQ eval h
    obtain ⟨f,w,path⟩ := child
    simp [zaW,tooMany] at openChild
  simp only [ze,zao,zU,zf,
    Bool.and_eq_true,decide_eq_true_eq] at checked
  have width := checked.1.1
  have atA := treeBlock_at checked.2 (i := a) (Nat.zero_le _) (by simpa using ha)
  rcases Bool.and_eq_true_iff.mp atA with ⟨unary,binary⟩
  rcases legal with ⟨rfl,rfl,hk⟩ | ⟨ab,hb,hop,hk⟩
  · have atKeep := treeBlock_at unary (i := keep) (Nat.zero_le _) (by simpa using hk)
    have fields := zaz (mask := mask) (state := state) (a := a) (b := a) (op := 2)
      (keep := keep) (by omega) (by decide) (by omega)
    have direct := fields.trans eval
    have early := zaP masked viable nd direct
    rcases child with ⟨fuel,ws,history⟩
    simpa only [narrow,Bool.false_eq_true,ite_false,fields,eval,zaw,early,openChild,Bool.or_false] using atKeep
  · have atB := treeBlock_at binary (i := b) (by omega) (by omega)
    have atOp := treeBlock_at atB (i := op) (Nat.zero_le _) (by simpa using hop)
    have atKeep := treeBlock_at atOp (i := keep) (Nat.zero_le _) (by simpa using hk)
    have fields := zaz (mask := mask) (state := state) (a := a) (b := b) (op := op)
      (keep := keep) (by omega) (by omega) hk
    have direct := fields.trans eval
    have early := zaP masked viable nd direct
    rcases child with ⟨fuel,ws,history⟩
    simpa only [narrow,Bool.false_eq_true,ite_false,fields,eval,zaw,early,openChild,Bool.or_false] using atKeep

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

def zaa (cert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin width → Fin width) × (Fin width → Fin width)))) : Array (List (List (Nat × Nat) × List (Nat × Nat))) := (cert.map Prod.fst).toArray

def zg {width : Nat} (mask goal : Nat) (entry : ((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin width → Fin width) × (Fin width → Fin width))) : Prop :=
  let (move,select,inverse) := entry
  (∀ i,inverse (select i) = i) ∧ (∀ i,select (inverse i) = i) ∧
    (mask &&& fM width = mask) ∧ (goal &&& mask = goal) ∧
    (∀ i : Fin width,mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = 2 ^ (inverse i).val) ∧
    mixMove move mask = mask ∧ mixMove move goal = goal

def zbv {width : Nat} (mask goal : Nat) (entry : ((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin width → Fin width) × (Fin width → Fin width))) : Bool :=
  let (move,select,inverse) := entry
  decide ((∀ i,inverse (select i) = i) ∧ (∀ i,select (inverse i) = i) ∧
    (mask &&& fM width = mask) ∧ (goal &&& mask = goal) ∧
    (∀ i : Fin width,mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = 2 ^ (inverse i).val) ∧
    mixMove move mask = mask ∧ mixMove move goal = goal)

theorem zbi {width : Nat} {mask goal : Nat} {entry : ((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin width → Fin width) × (Fin width → Fin width))}
    (ok : zbv mask goal entry = true) : zg mask goal entry := by
  rcases entry with ⟨move,select,inverse⟩
  unfold zg
  exact of_decide_eq_true ok

theorem zah {width : Nat} {mask goal : Nat} {cert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin width → Fin width) × (Fin width → Fin width)))}
    (ok : cert.all (zbv mask goal) = true) :
    dM mask goal width (zaa cert) := by
  intro i m get
  simp only [zaa,List.getElem?_toArray,List.getElem?_map] at get
  cases e : cert[i]? with
  | none => simp [e] at get
  | some entry =>
    have eq : entry.1 = m := by simpa [e] using get
    rcases entry with ⟨move,select,inverse⟩
    obtain ⟨left,right,bm,gm,basis,mm,mg⟩ :=
      zbi (List.all_eq_true.mp ok _ (List.mem_of_getElem? e))
    subst m
    exact ⟨select,zl left right bm gm basis mm mg⟩

theorem zbt {mask goal : Nat} {width count : Nat} {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {moves : Array (List (List (Nat × Nat) × List (Nat × Nat)))} {links : (Nat → Nat → Option (Nat × Nat))} {parent token : Nat} {state : (Nat × List Nat × List (Nat × Nat × Nat))}
    (bounds : Masked (fM width) mask)
    (valid : dM mask goal width moves)
    (masked : ∀ w ∈ state.2.1,Masked mask w)
    (ok : zz count states moves links parent token state = true)
    {k t : Nat} (live : LiveWord mask goal k t state.2.1.toFinset) :
    ∃ i saved,i < count ∧ states i = some saved ∧ saved.1 = state.1 ∧
      LiveWord mask goal k t saved.2.1.toFinset := by
  unfold zz at ok
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
          have same : saved.2.1 = zbk m state.2.1 := beq_iff_eq.mp last
          rw [same,zby (fun w hw => agree w (masked w hw))]
          exact liveMaskedImage auto bounds live (fun w hw => masked _ (List.mem_toFinset.mp hw))

theorem zwW {mask goal : Nat} {width count : Nat}
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
    simp only [zc,stateEq,zaw,Bool.and_eq_true] at checked
    obtain ⟨nd,masked⟩ := zM checked.1
    have ok := checked.2
    have viable : WordViable mask goal s := ⟨nd,k,t,sFuel ▸ kBound,live⟩
    have scanned := ok
    simp only [ze,Bool.and_eq_true,decide_eq_true_eq] at scanned
    have wide := scanned.1.1
    have absent := scanned.1.2
    rcases wordProgress wide viable with hit | ⟨child,possible,cv⟩
    · simpa [hit] using absent
    obtain ⟨a,b,op,keep,ha,legal,eval⟩ := possible
    have r := zk ok ha legal eval goalMask cv nd (zbs goalMask chartOK cv (cutSound i _ cv))
    have ⟨less,cm⟩ := childStateData eval masked
    have below : child.1 < cap := sFuel ▸ less
    obtain ⟨_,k',t',fits,clive⟩ := cv
    obtain ⟨j,dest,bound,restore,fuelEq,tail⟩ :=
      zbt maskBounds autos cm r clive
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
    (rootCheck : zd mask goal chart (zt goal bounds) witnesses
      (zz count states moves links 0)
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
    rw [zbw]
    exact knownClosesSound known submasks h
  have openRoot := zbs goalMask chartOK v (cutOpen _ v)
  have allowed : za witnesses state.2.1 = true := by
    apply List.all_eq_true.mpr
    intro entry mem
    apply List.contains_iff_mem.mpr
    rw [← List.mem_toFinset,eq']
    exact essentialRequired (List.all_eq_true.mp essential entry mem) sub live
  have checked := treeBlock_at rootCheck (Nat.zero_le token) (by simpa using tokenBound)
  change (!za witnesses state.2.1 || zaW mask goal chart (zt goal bounds) state ||
    zz count states moves links 0 token state) = true at checked
  simp only [allowed,openRoot,Bool.not_true,Bool.false_or] at checked
  have slim (i : Nat) (s) (h : WordViable mask goal s) : zt goal (cutPick bounds (choices i)) s = false := by
    rw [zbw]
    exact knownClosesSound (fun b hb => known b (cutPickMem _ _ hb)) (fun b hb => submasks b (cutPickMem _ _ hb)) h
  have finish := zwW maskBounds goalMask chartOK slim autos nodeCheck
  have fits : k ≤ fuel := by omega
  have still : LiveWord mask goal k t state.2.1.toFinset := by rwa [eq']
  have stateMask : ∀ w ∈ state.2.1,Masked mask w := by
    intro w hw
    exact stockMasked _ ((rootWordSublist stock token).subset hw)
  obtain ⟨i,s,hi,restore,cap,plan⟩ := zbt maskBounds autos stateMask checked still
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

def zy (mask : Nat) (move : (List (List (Nat × Nat) × List (Nat × Nat)))) (word : Nat) : Nat :=
  mixMove move (word &&& mask)

def zu (mask : Nat) (move : (List (List (Nat × Nat) × List (Nat × Nat)))) : Nat → Nat → Bool :=
  Nat.rec (fun _ => true) (fun i next occupied =>
    if mask.testBit i then
      zq (mixMove move (2^i)) (fun col =>
        Nat.beq (col &&& occupied) 0 && zq (occupied ||| col) next)
    else next occupied)

theorem zbc (mask : Nat) (move : (List (List (Nat × Nat) × List (Nat × Nat)))) : BitLinear (zy mask move) := by
  apply bitLinearComp (mixMoveLinear move)
  simpa using bitLinearRight mask 0

theorem zW (mask : Nat) (move : (List (List (Nat × Nat) × List (Nat × Nat)))) (i : Nat) :
    zy mask move (2 ^ i) = if mask.testBit i then mixMove move (2^i) else 0 := by
  have select : 2 ^ i &&& mask = if mask.testBit i then 2^i else 0 := by
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases same : i = j
    · subst j
      simp only [Nat.testBit_and,Nat.testBit_two_pow,decide_true,Bool.true_and]
      cases mask.testBit i <;> simp
    · cases h : mask.testBit i <;> simp [Nat.testBit_and,Nat.testBit_two_pow,same,h]
  rw [zy,select]
  split
  · rfl
  · apply Nat.eq_of_testBit_eq
    intro j
    apply Bool.eq_iff_iff.mpr
    rw [mixMoveLinear]
    simp

theorem zat {mask : Nat} {move : (List (List (Nat × Nat) × List (Nat × Nat)))} {n : Nat} {occupied : Nat}
    (ok : zu mask move n occupied = true) :
    (∀ j < n,∀ b,(zy mask move (2^j)).testBit b = true → occupied.testBit b = false) ∧
    (∀ j < n,∀ k < n,∀ b,(zy mask move (2^j)).testBit b = true →
      (zy mask move (2^k)).testBit b = true → j = k) := by
  induction n generalizing occupied with
  | zero => simp
  | succ n ih =>
    let col := mixMove move (2^n)
    change (if mask.testBit n then zq col (fun w =>
      Nat.beq (w &&& occupied) 0 && zq (occupied ||| w) (zu mask move n))
      else zu mask move n occupied) = true at ok
    cases active : mask.testBit n
    · simp [active,zU] at ok
      obtain ⟨existing,unique⟩ := ih ok
      have dead : zy mask move (2^n) = 0 := by simp [zW,active]
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
    · simp only [active,ite_true,zU,Bool.and_eq_true] at ok
      have disjoint := Nat.beq_eq.mp ok.1
      obtain ⟨existing,unique⟩ := ih ok.2
      have colEq : zy mask move (2^n) = col := by simp [zW,active,col]
      have old {j b : Nat} (hj : j < n) (h : (zy mask move (2^j)).testBit b = true) :
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

theorem zJ {mask : Nat} {move : (List (List (Nat × Nat) × List (Nat × Nat)))} {width : Nat}
    (bounded : Masked (fM width) mask) (checked : zu mask move width 0 = true) :
    (∀ a b,zy mask move (a &&& b) = zy mask move a &&& zy mask move b) ∧
    (∀ a b,zy mask move (a ||| b) = zy mask move a ||| zy mask move b) ∧
    (∀ a b,zy mask move (a ^^^ b) = zy mask move a ^^^ zy mask move b) := by
  let f := zy mask move
  have lin := zbc mask move
  have uniq {j k i : Nat} (hj : (f (2^j)).testBit i = true) (hk : (f (2^k)).testBit i = true) : j = k := by
    have within {m : Nat} (a : (f (2^m)).testBit i = true) : m < width := by
      by_contra! big
      have eq := congrArg (fun w => Nat.testBit w m) bounded
      have zero : mask.testBit m = false := by
        simpa [Masked,fM,Nat.testBit_and,Nat.testBit_two_pow_sub_one,show ¬m < width by omega] using eq.symm
      simp [f,zW,zero] at a
    exact (zat checked).2 j (within hj) k (within hk) i hj hk
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

def zP (width mask goal oldMask oldGoal : Nat) (stock old : List Nat) (move : (List (List (Nat × Nat) × List (Nat × Nat)))) : Bool :=
  Nat.beq (mask &&& fM width) mask && zu mask move width 0 &&
    Nat.beq (zy mask move mask) oldMask && Nat.beq (zy mask move goal) oldGoal &&
    stock.all (fun w => availableB oldMask old (zy mask move w))

theorem zp {width mask goal oldMask oldGoal : Nat} {stock old : List Nat} {min : Nat}
    (move : (List (List (Nat × Nat) × List (Nat × Nat)))) (origin : Lower oldMask old oldGoal min)
    (ok : zP width mask goal oldMask oldGoal stock old move = true) :
    Lower mask stock goal min := by
  simp only [zP,Bool.and_eq_true,Nat.beq_eq] at ok
  obtain ⟨⟨⟨⟨bounded,unique⟩,masks⟩,goals⟩,supply⟩ := ok
  obtain ⟨andG,orG,xorG⟩ := zJ bounded unique
  have zero : zy mask move 0 = 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    apply Bool.eq_iff_iff.mpr
    rw [zbc]
    simp
  apply lowerMap (zy mask move) zero masks (fun w => by rw [xorG,masks]) andG orG (uC supply)
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

def gZ : Nat := 0xfee8e8a8ec888888
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
                     (zI mask op x y,x,y) :: prev (p-1)) (fuel+1)) i
def zT : Nat := (cB [0x741a1d0703c1a0f,0x4180f0e0781c1e0e,0xc1f0687c181e0607,0xe07074380f0e07c1,0x607c1a1])
def zaB : Nat := 0xefbcdf73becf
def zaF : Nat := 0x182824124205
def zN : Nat := 0xf000f000
abbrev zad : Nat := gZ &&& zN
abbrev zE : List Nat := [0xa000a000,0xc000c000,0xf0000000]
def zY : Nat × List Nat × Nat × Nat := (zN,zE,4,zad)
def zav : List (Nat × List Nat × Nat × Nat) := []
def zaJ : Option ({rows : List Nat // rows.length = 24}) := some ⟨[15,29,30,15,29,30,15,29,30,15,29,30,13,14,28,13,14,28,13,14,28,13,14,28],rfl⟩
def zaC := uW zE [7694,269837,539149]
def zaG (i : Nat) : Nat := uP 0x9 2 i
def zaT (i : Nat) : Nat := uP 0x7 15 i
def zv (i : Nat) : Nat := uP 0xe 14 i
def zaH := pageLinks zaG zaT 1 13 1 2
def zbg (i : Nat) : Nat × Nat :=
  let e := zv i
  (e &&& 1,e >>> 1)
def zV : Nat × Nat := (zT,16)
def zag := zr zN 16 (zD zE zaB zaF 16) 3 zbg
def zaK := zw zN zE 3 zbg
def zaq : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def zaE := zaa zaq
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zaM : dM zN zad 64 zaE := zah (by decide +kernel)
def zaN (i : Nat) : Nat :=
  let j := i / 16
  uP 0x0 1 (i % 16)
def zal := zc zN zad zaJ (fun i => zt zad (cutPick zav (zaN i))) 1 zaK zaE zaH zV zag
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zaX : zd zN zad zaJ (zt zad zav) zaC (zz 1 zaK zaE zaH 0) zE 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zaV : tB 0 1 zal = true := by decide +kernel
theorem zaU : tB 0 1 zal = true := zaV
theorem zaS : Known zav := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zx : Lower zN zE zad 4 := by
  apply lowerDag zaN _ _ _ _ zaM _ _ _ zaS _ zaX zaU
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold pW; decide +kernel
  · exact cK (by decide +kernel)
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [zav,List.mem_cons,List.not_mem_nil,or_false]
    intro b h
    exact False.elim h
def st02 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xa5a5a5a5a5a5a5a5,0),(0xa0a0a0a0a0a0a0a,3)],[(0x5050505050505050,3)])
def st15 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xcccccccc33333333,0),(0xcccccccc,30)],[(0x3333333300000000,30)])
def st14 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xcccc3333cccc3333,0),(0xcccc0000cccc,14)],[(0x3333000033330000,14)])
def pm0 : List (List (Nat × Nat) × List (Nat × Nat)) := [st02,st15,st14]
def zct : Nat := 0x2200220022002200
abbrev zhI : Nat := gZ &&& zct
abbrev zcA : List Nat := [0x2000200020002000,0x2200000022000000,0x2200220000000000]
def zxy : Nat × List Nat × Nat × Nat := (zct,zcA,4,zhI)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zcM : Lower zct zcA zhI 4 := zp (width := 64) pm0 zx (by decide +kernel)
def pm1 : List (List (Nat × Nat) × List (Nat × Nat)) := [st15,st14]
def zek : Nat := 0x3000300030003000
abbrev zlE : Nat := gZ &&& zek
abbrev zjp : List Nat := [0x2000200020002000,0x3000000030000000,0x3000300000000000]
def zfN : Nat × List Nat × Nat × Nat := (zek,zjp,4,zlE)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zeS : Lower zek zjp zlE 4 := zp (width := 64) pm1 zx (by decide +kernel)
def st12 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xc3c3c3c3c3c3c3c3,0),(0xc0c0c0c0c0c0c0c,2)],[(0x3030303030303030,2)])
def st23 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xf00ff00ff00ff00f,0),(0xf000f000f000f0,4)],[(0xf000f000f000f00,4)])
def st34 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xff0000ffff0000ff,0),(0xff000000ff00,8)],[(0xff000000ff0000,8)])
def pm2 : List (List (Nat × Nat) × List (Nat × Nat)) := [st15,st12,st23,st34]
def zfY : Nat := 0x3300000033000000
abbrev zks : Nat := gZ &&& zfY
abbrev zlq : List Nat := [0x2200000022000000,0x3000000030000000,0x3300000000000000]
def zgU : Nat × List Nat × Nat × Nat := (zfY,zlq,4,zks)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zlV : Lower zfY zlq zks 4 := zp (width := 64) pm2 zx (by decide +kernel)
def pm3 : List (List (Nat × Nat) × List (Nat × Nat)) := [st15,st12,st23]
def zet : Nat := 0x3300330000000000
abbrev zjX : Nat := gZ &&& zet
abbrev zmg : List Nat := [0x2200220000000000,0x3000300000000000,0x3300000000000000]
def zqy : Nat × List Nat × Nat × Nat := (zet,zmg,4,zjX)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ztv : Lower zet zmg zjX 4 := zp (width := 64) pm3 zx (by decide +kernel)
def st45 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xffff00000000ffff,0),(0xffff0000,16)],[(0xffff00000000,16)])
def pm4 : List (List (Nat × Nat) × List (Nat × Nat)) := [st45]
def st24 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xf0f00f0ff0f00f0f,0),(0xf0f00000f0f0,12)],[(0xf0f00000f0f0000,12)])
def pm5 : List (List (Nat × Nat) × List (Nat × Nat)) := [st24]
def st25 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xf0f0f0f00f0f0f0f,0),(0xf0f0f0f0,28)],[(0xf0f0f0f00000000,28)])
def pm6 : List (List (Nat × Nat) × List (Nat × Nat)) := [st24,st25]
def pm7 : List (List (Nat × Nat) × List (Nat × Nat)) := [st02]
def pm8 : List (List (Nat × Nat) × List (Nat × Nat)) := [st02,st45]
def st04 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xaaaa5555aaaa5555,0),(0xaaaa0000aaaa,15)],[(0x5555000055550000,15)])
def pm9 : List (List (Nat × Nat) × List (Nat × Nat)) := [st02,st04]
def st05 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xaaaaaaaa55555555,0),(0xaaaaaaaa,31)],[(0x5555555500000000,31)])
def pm10 : List (List (Nat × Nat) × List (Nat × Nat)) := [st02,st04,st05]
def pm11 : List (List (Nat × Nat) × List (Nat × Nat)) := [st04,st02]
def pm12 : List (List (Nat × Nat) × List (Nat × Nat)) := [st04,st02,st25]
def pm13 : List (List (Nat × Nat) × List (Nat × Nat)) := [st04,st25]
def zqB : Nat := (cB [0x8b4381d0c8741a1d,0x43239160b4522d06,0x83c0e0f07039148e,0xd06074121d1c0f05,0x40b4182d048b4301,0xf050390c0e412391,0x1a3d140f0303c060,0x3d148f4383d0c8f4,0x14874101d1c0f458,0x8b4102d1c074581d,0x410391c0b4382d0c,0x3c160e43839068e,0xd148f0323c068f01,0x40f4303d060f4123,0xf018390c0b4501d1,0x103d048])
def zrW : Nat := (cB [0x1fdfc3ffff1ff1ff,0x1ff1f7fe1ffff1ff,0xfff1ff1dfff0ffff,0xf7fff87])
def znu : Nat := (cB [0x16a078888b0490db,0x12d18845c88a9093,0x1241b602444e8992,0xc44477])
def zbH : Nat := 0x3300330033003300
abbrev zcj : Nat := gZ &&& zbH
abbrev zbL : List Nat := [0x2200220022002200,0x3000300030003000,0x3300000033000000,0x3300330000000000]
def zjG : Nat × List Nat × Nat × Nat := (zbH,zbL,7,zcj)
def zda : List (Nat × List Nat × Nat × Nat) := [zxy,zfN,zgU,zqy]
def zir : Option ({rows : List Nat // rows.length = 24}) := some ⟨[29,45,57,60,29,45,57,60,29,45,57,60,13,25,28,41,44,56,13,25,28,41,44,56],rfl⟩
def zwv := uW zbL [14876,277017,539149,809485]
def ztb (i : Nat) : Nat := uP 0x4c242e4702cc3401 9 i
def zvq (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 1 (cB [0xb0600f020080000f,0x1b42314360272601,0x6276262096327863,0x4620043147292ca6,0x18332083263492c2]) 0xa6245863248626) 20 (i % 16)
def zsb (i : Nat) : Nat := uP (cB [0x7918a200410078,0x31251934]) 16 i
def zlG := pageLinks ztb zvq 4 13 3 5
def zkm (i : Nat) : Nat × Nat :=
  let e := zsb i
  (e &&& 7,e >>> 3)
def zta : Nat × Nat := (zqB,55)
def zwq := zr zbH 55 (zD zbL zrW znu 55) 6 zkm
def zgS := zw zbH zbL 6 zkm
def zmW : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm4,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,3,5,4] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,3,5,4] 0 i.val))),(pm5,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,4,3,2,5] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,4,3,2,5] 0 i.val))),(pm6,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,5,3,2,4] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,4,3,5,2] 0 i.val))),(pm7,(fun i : Fin 64 => Fin.ofNat 64 (pA [2,1,0,3,4,5] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [2,1,0,3,4,5] 0 i.val))),(pm8,(fun i : Fin 64 => Fin.ofNat 64 (pA [2,1,0,3,5,4] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [2,1,0,3,5,4] 0 i.val))),(pm9,(fun i : Fin 64 => Fin.ofNat 64 (pA [4,1,0,3,2,5] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [2,1,4,3,0,5] 0 i.val))),(pm10,(fun i : Fin 64 => Fin.ofNat 64 (pA [5,1,0,3,2,4] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [2,1,4,3,5,0] 0 i.val))),(pm11,(fun i : Fin 64 => Fin.ofNat 64 (pA [2,1,4,3,0,5] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [4,1,0,3,2,5] 0 i.val))),(pm12,(fun i : Fin 64 => Fin.ofNat 64 (pA [2,1,5,3,0,4] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [4,1,0,3,5,2] 0 i.val))),(pm13,(fun i : Fin 64 => Fin.ofNat 64 (pA [4,1,5,3,0,2] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [4,1,5,3,0,2] 0 i.val)))]
def zeK := zaa zmW
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zvN : dM zbH zcj 64 zeK := zah (by decide +kernel)
def zhZ (i : Nat) : Nat :=
  let j := i / 16
  uP 0x101f 4 (i % 16)
def zih := zc zbH zcj zir (fun i => zt zcj (cutPick zda (zhZ i))) 6 zgS zeK zlG zta zwq
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zpa : zd zbH zcj zir (zt zcj zda) zwv (zz 6 zgS zeK zlG 0) zbL 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zwS : tB 0 6 zih = true := by decide +kernel
theorem zpp : tB 0 6 zih = true := zwS
theorem zpF : Known zda := (eK (eK (eK (eK (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) ztv) zlV) zeS) zcM)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zbP : Lower zbH zbL zcj 7 := by
  apply lowerDag zhZ _ _ _ _ zvN _ _ _ zpF _ zpa zpp
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
def zeE : Nat := 0x3333333333333333
abbrev zlW : Nat := gZ &&& zeE
abbrev zej : List Nat := [0x2222222222222222,0x3030303030303030,0x3300330033003300,0x3333000033330000,0x3333333300000000]
def zjb : Nat × List Nat × Nat × Nat := (zeE,zej,8,zlW)
def zoJ := uW zej [14876,277017,539157,801293,1067525]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zfs : Lower zeE zej zlW 8 := by
  apply eL (witnesses := zoJ) (cut := zbH)
  · unfold pW; decide +kernel
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold pW; decide +kernel
  · exact uC (old := zbL) (by decide +kernel)
  · exact zbP
  · decide +kernel
def st01 : List (Nat × Nat) × List (Nat × Nat) := ([( 0x9999999999999999,0),(0x2222222222222222,1)],[(0x4444444444444444,1)])
def pm14 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01,st23,st45]
def zdA : Nat := 0x5555555555555555
abbrev zlF : Nat := gZ &&& zdA
abbrev zhn : List Nat := [0x4444444444444444,0x5050505050505050,0x5500550055005500,0x5555000055550000,0x5555555500000000]
def zeG : Nat × List Nat × Nat × Nat := (zdA,zhn,8,zlF)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zel : Lower zdA zhn zlF 8 := zp (width := 64) pm14 zfs (by decide +kernel)
def pm15 : List (List (Nat × Nat) × List (Nat × Nat)) := [st25]
def pm16 : List (List (Nat × Nat) × List (Nat × Nat)) := [st02,st05]
def pm17 : List (List (Nat × Nat) × List (Nat × Nat)) := [st05,st02]
def ztD : Nat := (cB [0x8940a250e074321d,0x70390c8e4482510,0x1d02874703c0e0f,0x9100940825008943,0x20f0303c108e4303,0x74703d0e0f4323d1,0x251c074081d008,0x3c100e43839008e4,0x28f4403c0c8f008,0x74483d108f4303d,0x4322512074421d00,0xa39000e470250e09,0xc028f0003c120e40,0xf4083d008f4423,0xf008390c094401d1,0x3d008])
def zvr : Nat := (cB [0xcfdf8fff8ffcfe7f,0xf1f8f7f8fff8ff9f,0xe3ff3f9dff8fffbf,0xf7ff8ff])
def zpx : Nat := (cB [0x4b20e452a2248a2d,0x5178c896524a2509,0x12542b0200704927,0xc926c9])
def zbS : Nat := 0x3300003333000033
abbrev zcc : Nat := gZ &&& zbS
abbrev zcr : List Nat := [0x2200002222000022,0x3000003030000030,0x3300000033000000,0x3300003300000000]
def zjB : Nat × List Nat × Nat × Nat := (zbS,zcr,7,zcc)
def zcY : List (Nat × List Nat × Nat × Nat) := [zgU]
def ziz : Option ({rows : List Nat // rows.length = 24}) := some ⟨[29,37,57,60,29,37,57,60,29,37,57,60,5,25,28,33,36,56,5,25,28,33,36,56],rfl⟩
def zwx := uW zcr [14876,277017,539141,805381]
def zpu (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 1 (cB [0x4028050088c18001,0xd85b0360644a15,0x802e8dd03817]) 0x9c730622421) 11 (i % 16)
def zvM (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 1 (cB [0x820024040100000f,0xc400361a01305007,0xa823142d01592809,0xb85193a80c6d1062,0x638189c48c411a32,0x6149]) (bI j 2 (cB [0x1988008628c892d,0x82464c0c31c22496,0x9663249313058cc,0xa312040c901c63,0x8071890180181863,0xf31]) (cB [0x48c68200180e00c,0xc52642262529199,0x8866200318a050c9,0x18d25]))) 21 (i % 16)
def zvQ (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 1 (cB [0x862820040401e0,0xc638600784012131,0x48a19318648718c1,0xe00984c60c19918c,0x31838c48]) 0xc401312c40361) 18 (i % 16)
def zjT := pageLinks zpu zvM 5 13 5 6
def zkd (i : Nat) : Nat × Nat :=
  let e := zvQ i
  (e &&& 31,e >>> 5)
def zwU : Nat × Nat := (ztD,55)
def zpi := zr zbS 55 (zD zcr zvr zpx 55) 6 zkd
def ziR := zw zbS zcr 6 zkd
def zuN : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm15,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,5,3,4,2] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,5,3,4,2] 0 i.val))),(pm7,(fun i : Fin 64 => Fin.ofNat 64 (pA [2,1,0,3,4,5] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [2,1,0,3,4,5] 0 i.val))),(pm16,(fun i : Fin 64 => Fin.ofNat 64 (pA [5,1,0,3,4,2] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [2,1,5,3,4,0] 0 i.val))),(pm17,(fun i : Fin 64 => Fin.ofNat 64 (pA [2,1,5,3,4,0] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [5,1,0,3,4,2] 0 i.val)))]
def zen := zaa zuN
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zrZ : dM zbS zcc 64 zen := zah (by decide +kernel)
def zhB (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 1 0x3 0x5) 1 (i % 16)
def zlR := zc zbS zcc ziz (fun i => zt zcc (cutPick zcY (zhB i))) 19 ziR zen zjT zwU zpi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ztx : zd zbS zcc ziz (zt zcc zcY) zwx (zz 19 ziR zen zjT 0) zcr 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zxr : tB 0 19 zlR = true := by decide +kernel
theorem zua : tB 0 19 zlR = true := zxr
theorem zrd : Known zcY := (eK (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) zlV)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zed : Lower zbS zcr zcc 7 := by
  apply lowerDag zhB _ _ _ _ zrZ _ _ _ zrd _ ztx zua
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold pW; decide +kernel
  · exact cK (by decide +kernel)
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [zcY,List.mem_cons,List.not_mem_nil,or_false]
    intro b h
    rcases h with rfl <;> decide +kernel
def pm18 : List (List (Nat × Nat) × List (Nat × Nat)) := [st34]
def zeU : Nat := 0x3333000033330000
abbrev zlZ : Nat := gZ &&& zeU
abbrev zgX : List Nat := [0x2222000022220000,0x3030000030300000,0x3300000033000000,0x3333000000000000]
def zkc : Nat × List Nat × Nat × Nat := (zeU,zgX,7,zlZ)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ziX : Lower zeU zgX zlZ 7 := zp (width := 64) pm18 zbP (by decide +kernel)
def zcP : Nat := 0x5050505005050505
abbrev zgt : Nat := gZ &&& zcP
abbrev zfV : List Nat := [0x4040404004040404,0x5050505000000000,0x5000500005000500,0x5050000005050000]
def ziP : Nat × List Nat × Nat × Nat := (zcP,zfV,7,zgt)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zfO : Lower zcP zfV zgt 7 := zp (width := 64) pm14 zed (by decide +kernel)
def pm19 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01,st23]
def zfo : Nat := 0x5050505050505050
abbrev zik : Nat := gZ &&& zfo
abbrev zhQ : List Nat := [0x4040404040404040,0x5000500050005000,0x5050000050500000,0x5050505000000000]
def zcN : Nat × List Nat × Nat × Nat := (zfo,zhQ,7,zik)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zcQ : Lower zfo zhQ zik 7 := zp (width := 64) pm19 zbP (by decide +kernel)
def st35 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xff00ff0000ff00ff,0),(0xff00ff00,24)],[(0xff00ff00000000,24)])
def pm20 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01,st34,st35]
def zdC : Nat := 0x5555555500000000
abbrev zjD : Nat := gZ &&& zdC
abbrev zmf : List Nat := [0x4444444400000000,0x5050505000000000,0x5500550000000000,0x5555000000000000]
def zdB : Nat × List Nat × Nat × Nat := (zdC,zmf,7,zjD)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zdo : Lower zdC zmf zjD 7 := zp (width := 64) pm20 zbP (by decide +kernel)
def zeM : Nat := 0xf0f0f0f0
abbrev zkV : Nat := gZ &&& zeM
abbrev zeI : List Nat := [0xa0a0a0a0,0xc0c0c0c0,0xf000f000,0xf0f00000]
def zdJ : Nat × List Nat × Nat × Nat := (zeM,zeI,5,zkV)
def zrC := uW zeI [3590,265733,539157,801293]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zbE : Lower zeM zeI zkV 5 := by
  apply eL (witnesses := zrC) (cut := zN)
  · unfold pW; decide +kernel
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold pW; decide +kernel
  · exact uC (old := zE) (by decide +kernel)
  · exact zx
  · decide +kernel
def pm21 : List (List (Nat × Nat) × List (Nat × Nat)) := [st02,st15]
def zeq : Nat := 0x2222222222222222
abbrev zmj : Nat := gZ &&& zeq
abbrev ziQ : List Nat := [0x2020202020202020,0x2200220022002200,0x2222000022220000,0x2222222200000000]
def zfx : Nat × List Nat × Nat × Nat := (zeq,ziQ,5,zmj)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zeW : Lower zeq ziQ zmj 5 := zp (width := 64) pm21 zbE (by decide +kernel)
def st13 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xcc33cc33cc33cc33,0),(0xcc00cc00cc00cc,6)],[(0x3300330033003300,6)])
def pm22 : List (List (Nat × Nat) × List (Nat × Nat)) := [st05,st12,st13,st01,st14]
def zdj : Nat := 0x4444444444444444
abbrev zmh : Nat := gZ &&& zdj
abbrev zlI : List Nat := [0x4040404040404040,0x4400440044004400,0x4444000044440000,0x4444444400000000]
def zcV : Nat × List Nat × Nat × Nat := (zdj,zlI,5,zmh)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zdc : Lower zdj zlI zmh 5 := zp (width := 64) pm22 zbE (by decide +kernel)
def pm23 : List (List (Nat × Nat) × List (Nat × Nat)) := [st25,st34]
def pm24 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01,st23,st25,st24]
def pm25 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01,st24,st23,st35]
def zuK : Nat := (cB [0x874301a09068141a,0x8381d0c8742a1d06,0xa250e0782c1e0707,0xd068b44825108940,0x30b81c2e160b4522,0xd42a35160b8542e1,0x4c360b0d86835188,0x390c8e46836190d8,0x150e87039188e452,0xf0383c1c0e8643a,0x8041a1c0f0683c16,0xc1a080681c1a0406,0xa15068381a0c8682,0x48740a1d1c068641,0x74281d08874181d0,0x181e050780c1e0c0,0x250c078281e09078,0xa8941a250209402,0x945225130944025,0x40a2d1a094622516,0x82d108b4182d048b,0xe050b80c2e140b44,0x40b8482e110b8182,0xd42835088d40a351,0xc36180d44835108,0x36110d82836090d8,0x88e41239180d848])
def zuZ : Nat := (cB [0xf03f00007870fc78,0x878f0387c0fc0fff,0x3f03f0000fc0ffc3,0xffff003c07fffff8,0xf80fe3ff3fffffff,0xc003ffc00fffffff,0xffffffffff003ff,0xfffffc00fffc0000,0xfffffffff000003f])
def zuM : Nat := (cB [0xd00b080038306c38,0x83870183c02c02d4,0xb00b00202c06541,0xe555151c05dbb7d8,0xd80de2ed1555556a,0x4002698c49a6b9ae,0x8e38de376ef00376,0xf76ed800a6980030,0x38e38e3f0000e03b])
def zbQ : Nat := 0x7777777777777777
abbrev zcb : Nat := gZ &&& zbQ
abbrev zcq : List Nat := [0x2222222222222222,0x4444444444444444,0x7070707070707070,0x7700770077007700,0x7777000077770000,0x7777777700000000]
def zxv : Nat × List Nat × Nat × Nat := (zbQ,zcq,11,zcb)
def zdf : List (Nat × List Nat × Nat × Nat) := [zjb,zeG,zjB,zjG,zkc,ziP,zcN,zdB,zfx,zcV]
def zgM : Option ({rows : List Nat // rows.length = 24}) := some ⟨[26,29,37,46,54,57,60,26,29,37,46,54,13,14,21,22,25,28,38,41,42,44,49,50],rfl⟩
def zmT := uW zcq [14876,275480,539161,799762,1061898,1329669]
def ztq (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 2 (bI j 1 (cB [0x281140081005e001,0x7462c71600a84540,0x2808484202101004,0x2501]) (cB [0x5802b09580ac04a6,0xc8a6212d21680b02,0xce107003709b80,0x430a])) (bI j 3 (cB [0x9204902215100880,0x34a9a04922481240,0x1818c0c605d3292d,0x6323]) (bI j 4 (cB [0xce767033819c0ce0,0xc02e006e13701b80,0xc89d0ae617113881,0x7b03]) (cB [0x2c08c54602300f71,0xa493309904b0e581,0x15e0af0568a])))) 13 (i % 16)
def znS (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 5 (bI j 2 (bI j 1 (cB [0x380440100400003f,0x18a03401381c0240,0x330a4c4e0e188201,0x70e24b03f31f9526,0x9c61c25293f8fd26,0x471e88d4b0fe]) (cB [0x2a4cc03496004008,0x496008c3820d8700,0x2703062a040c5006,0x60b24b08f19981e3,0x949612cc3806126,0x22587005a4cc])) (bI j 3 (cB [0x698f80d319014c38,0x18a11cf440398704,0x3e034c40088cf810,0x80abd101461f0246,0x931002663c04d87,0x254c66071884]) (bI j 4 (cB [0x58c500a49602ec38,0x19e82833104464a0,0x1e06cc400ca4b094,0x60ea4b20331042c3,0x9d61c04c93f08526,0xa1e885330fc]) (cB [0xf3d102061f83cc38,0x4a504492c07de890,0x50291e9412312823,0xc11a4f82749604b2,0x17315140f4409187,0x8798710224b2])))) (bI j 8 (bI j 6 (cB [0x518829e7a204ac3f,0x31f85c63e0b4c421,0x4a8c8c9717192832,0x7533d123361f0669,0x2b01f24d2500f1e9,0xb1295158128]) (bI j 7 (cB [0x3c942a77a2458c3e,0x4a506064a0bcc409,0x3e0b0c4091c94031,0xc1aa4fc344960626,0x3a7a4d48f440d987,0xe1e901ba4d0]) (cB [0xc31203b320072640,0x32006063c0e52601,0x480e92a81f19083d,0x51da4c03b324474c,0x4018ec0a31486002,0x108c40208c7c]))) (bI j 9 (cB [0x298ce2e319088621,0x49918a63fab8c7c2,0x3f88587059a4f833,0x350bd113362488ec,0xc301f0860326cde9,0x818c410c8c78]) (bI j 10 (cB [0x130e0b449f068932,0x7a4d44f444d18931,0x55119e945ab129b4,0xa2418d03031836b2,0x3131e492636124c6,0xac4c902318f6]) (cB [0x324c83149818c649,0x62a16c9480d92792,0x544d9ea9a3315531,0x5b98f03731236d2,0x4a32436ef484dd29,0x25c950]))))) 23 (i % 16)
def zuG (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 2 (bI j 1 (cB [0x2004020040101f80,0x64998261c044960,0x60918a0800881496,0x8a884998961c0a49,0x1938861c0d3190d1]) (cB [0x331f1019f1018a10,0x87a21061f1061e1,0x6194998861c17496,0x10013101b0098149,0x7a21f61c1e4961d3])) (bI j 3 (cB [0x2496224999d61f9e,0x9d92822625224a52,0x3817a21d4962749f,0xa52b01f2b3102a31,0x3102f31f2a310aa4]) (bI j 4 (cB [0xa31faa4a52f3252f,0x3449fb4496344a52,0x397a43749a3761f,0xa5aa3203b7a4b432,0x31f813213d3203d7]) (cB [0x33104018fc018ec0,0x46319c0310c00194,0xac831a4861fc07a5,0x92a4a3244a31])))) 20 (i % 16)
def zhL := pageLinks ztq znS 5 13 7 6
def zjy (i : Nat) : Nat × Nat :=
  let e := zuG i
  (e &&& 127,e >>> 7)
def zth : Nat × Nat := (zuK,96)
def ztr := zr zbQ 96 (zD zcq zuZ zuM 96) 10 zjy
def zjZ := zw zbQ zcq 10 zjy
def zmQ : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm18,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,4,3,5] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,4,3,5] 0 i.val))),(pm15,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,5,3,4,2] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,5,3,4,2] 0 i.val))),(pm23,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,5,4,3,2] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,5,4,3,2] 0 i.val))),(pm14,(fun i : Fin 64 => Fin.ofNat 64 (pA [1,0,3,2,5,4] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [1,0,3,2,5,4] 0 i.val))),(pm24,(fun i : Fin 64 => Fin.ofNat 64 (pA [1,0,4,2,5,3] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [1,0,3,5,2,4] 0 i.val))),(pm25,(fun i : Fin 64 => Fin.ofNat 64 (pA [1,0,3,5,2,4] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [1,0,4,2,5,3] 0 i.val)))]
def zfq := zaa zmQ
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zmu : dM zbQ zcb 64 zfq := zah (by decide +kernel)
def zjS (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 2 (bI j 1 (cB [0x836cc936cdb36cdb,0xdb0200030ddb3680,0x36c01001]) (cB [0xb021040101800008,0xdb36ddb021da30cd,0x4936c])) (bI j 3 (cB [0xb020040000836c00,0x6f36cdb000f,0x7b120]) (bI j 4 (cB [0x203e81008300,0xd800008000000000,0x36c00000]) (cB [0x16060002fb106db,0x40100ff36c4])))) 10 (i % 16)
def zbF := zc zbQ zcb zgM (fun i => zt zcb (cutPick zdf (zjS i))) 76 zjZ zfq zhL zth ztr
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zna : zd zbQ zcb zgM (zt zcb zdf) zmT (zz 76 zjZ zfq zhL 0) zcq 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zxA : tB 0 24 zbF = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ztk : tB 24 24 zbF = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zwk : tB 48 24 zbF = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zms : tB 72 4 zbF = true := by decide +kernel
theorem zum : tB 0 48 zbF = true := tM (start := 0) (left := 24) (right := 24) (check := zbF) zxA ztk
theorem zqI : tB 48 28 zbF = true := tM (start := 48) (left := 24) (right := 4) (check := zbF) zwk zms
theorem zor : tB 0 76 zbF = true := tM (start := 0) (left := 48) (right := 28) (check := zbF) zum zqI
theorem znN : tB 0 76 zbF = true := zor
theorem zwV : Known zdf := (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) zdc) zeW) zdo) zcQ) zfO) ziX) zbP) zed) zel) zfs)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zoV : Lower zbQ zcq zcb 11 := by
  apply lowerDag zjS _ _ _ _ zmu _ _ _ zwV _ zna znN
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold pW; decide +kernel
  · exact cK (by decide +kernel)
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [zdf,List.mem_cons,List.not_mem_nil,or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def zee : Nat := 0xf0000000f000
abbrev zkf : Nat := gZ &&& zee
abbrev ziY : List Nat := [0xa0000000a000,0xc0000000c000,0xf00000000000]
def zhP : Nat × List Nat × Nat × Nat := (zee,ziY,4,zkf)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zid : Lower zee ziY zkf 4 := zp (width := 64) pm4 zx (by decide +kernel)
def pm26 : List (List (Nat × Nat) × List (Nat × Nat)) := [st05,st01,st14]
def zeh : Nat := 0x5000500050005000
abbrev zij : Nat := gZ &&& zeh
abbrev zjn : List Nat := [0x4000400040004000,0x5000000050000000,0x5000500000000000]
def zxG : Nat × List Nat × Nat × Nat := (zeh,zjn,4,zij)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zqS : Lower zeh zjn zij 4 := zp (width := 64) pm26 zx (by decide +kernel)
def pm27 : List (List (Nat × Nat) × List (Nat × Nat)) := [st14]
def pm28 : List (List (Nat × Nat) × List (Nat × Nat)) := [st14,st15]
def pm29 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01]
def pm30 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01,st45]
def pm31 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01,st04]
def pm32 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01,st04,st05]
def pm33 : List (List (Nat × Nat) × List (Nat × Nat)) := [st04,st01]
def pm34 : List (List (Nat × Nat) × List (Nat × Nat)) := [st04,st01,st15]
def pm35 : List (List (Nat × Nat) × List (Nat × Nat)) := [st04,st15]
def zsU : Nat := (cB [0x741a1d0703c1a0f,0x41a2d0e0781c1e0e,0x83c160b81c2e160b,0xe06074180f160f03,0xe07c1c1f0687c181,0xbc1a2f060b8182d0,0x1a3d060f0582f070,0x3e070f8583d0e0f4,0x1603c380f160f838,0x781a1e160741c1d,0x8382d070b4181f16,0xa3c060bc382e068b,0xf060f8183d070f01,0x60fc383f070fc1a3,0xf81c3d0e0bc581f1,0x183f068])
def zwG : Nat := (cB [0x99dfd273c777b0cf,0xfb0f37f1ce7c3de9,0xff81f81dff07cfe0,0xf7ffc07])
def zvI : Nat := (cB [0x8920448401108045,0x810a084410841080,0x8801500240501480,0xc00154])
def zbK : Nat := 0xf000f000f000f000
abbrev zci : Nat := gZ &&& zbK
abbrev zcm : List Nat := [0xa000a000a000a000,0xc000c000c000c000,0xf0000000f0000000,0xf000f00000000000]
def zhG : Nat × List Nat × Nat × Nat := (zbK,zcm,7,zci)
def zcU : List (Nat × List Nat × Nat × Nat) := [zY,zhP,zfN,zxG]
def zhk : Option ({rows : List Nat // rows.length = 24}) := some ⟨[15,29,30,45,46,60,15,29,30,45,46,60,13,14,28,44,13,14,28,44,13,14,28,44],rfl⟩
def zrD := uW zcm [7694,269837,539149,809485]
def zog (i : Nat) : Nat := uP 0x4c242e4702cc3401 9 i
def zvA (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 1 (cB [0xf06013020080000f,0x1f423143602b2601,0x62b626209632b863,0x4620043147292ca6,0x180360802a3492c2]) 0xa01c583364832a) 20 (i % 16)
def zmq (i : Nat) : Nat := uP (cB [0x9918a200410078,0xe50154]) 16 i
def zka := pageLinks zog zvA 4 13 3 5
def zgm (i : Nat) : Nat × Nat :=
  let e := zmq i
  (e &&& 7,e >>> 3)
def zmn : Nat × Nat := (zsU,55)
def zpO := zr zbK 55 (zD zcm zwG zvI 55) 6 zgm
def zie := zw zbK zcm 6 zgm
def zob : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm4,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,3,5,4] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,3,5,4] 0 i.val))),(pm27,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,4,2,3,1,5] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,4,2,3,1,5] 0 i.val))),(pm28,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,5,2,3,1,4] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,4,2,3,5,1] 0 i.val))),(pm29,(fun i : Fin 64 => Fin.ofNat 64 (pA [1,0,2,3,4,5] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [1,0,2,3,4,5] 0 i.val))),(pm30,(fun i : Fin 64 => Fin.ofNat 64 (pA [1,0,2,3,5,4] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [1,0,2,3,5,4] 0 i.val))),(pm31,(fun i : Fin 64 => Fin.ofNat 64 (pA [4,0,2,3,1,5] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [1,4,2,3,0,5] 0 i.val))),(pm32,(fun i : Fin 64 => Fin.ofNat 64 (pA [5,0,2,3,1,4] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [1,4,2,3,5,0] 0 i.val))),(pm33,(fun i : Fin 64 => Fin.ofNat 64 (pA [1,4,2,3,0,5] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [4,0,2,3,1,5] 0 i.val))),(pm34,(fun i : Fin 64 => Fin.ofNat 64 (pA [1,5,2,3,0,4] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [4,0,2,3,5,1] 0 i.val))),(pm35,(fun i : Fin 64 => Fin.ofNat 64 (pA [4,5,2,3,0,1] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [4,5,2,3,0,1] 0 i.val)))]
def zdv := zaa zob
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zvB : dM zbK zci 64 zdv := zah (by decide +kernel)
def zia (i : Nat) : Nat :=
  let j := i / 16
  uP 0x401f 4 (i % 16)
def zjw := zc zbK zci zhk (fun i => zt zci (cutPick zcU (zia i))) 6 zie zdv zka zmn zpO
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zpe : zd zbK zci zhk (zt zci zcU) zrD (zz 6 zie zdv zka 0) zcm 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zuP : tB 0 6 zjw = true := by decide +kernel
theorem zsE : tB 0 6 zjw = true := zuP
theorem zte : Known zcU := (eK (eK (eK (eK (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) zqS) zeS) zid) zx)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zcu : Lower zbK zcm zci 7 := by
  apply lowerDag zia _ _ _ _ zvB _ _ _ zte _ zpe zsE
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold pW; decide +kernel
  · exact cK (by decide +kernel)
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [zcU,List.mem_cons,List.not_mem_nil,or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel
def zdu : Nat := 0xf0f00000f0f00000
abbrev zkp : Nat := gZ &&& zdu
abbrev zlY : List Nat := [0xa0a00000a0a00000,0xc0c00000c0c00000,0xf0000000f0000000,0xf0f0000000000000]
def zgY : Nat × List Nat × Nat × Nat := (zdu,zlY,7,zkp)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zjN : Lower zdu zlY zkp 7 := zp (width := 64) pm18 zcu (by decide +kernel)
def pm36 : List (List (Nat × Nat) × List (Nat × Nat)) := [st04]
def pm37 : List (List (Nat × Nat) × List (Nat × Nat)) := [st04,st05]
def zxc : Nat := (cB [0x8e41c2e070781c0f,0x8120f1c0e452390c,0x2e0c87c1c1f0c07,0x9048e4522f070bc5,0xc0f81c3e140e4303,0x78520f0c83c100f1,0x121f1c078321e040,0x2e148b8102e0c07c,0x40e4502f048bc70,0x8fc1c3f140f8303e,0xc300f1c0fc523f0c,0x1f14078121e1403,0xe048b8701f1487c1,0xc0bc322f040bc302,0xfc523e0c8f8103e1,0x700f140fc303f048,0x2f0c8b8501f14878,0x40fc123e070e430])
def zvp : Nat := (cB [0xb5e39cfce31cfb79,0xdfffffff7fff1fc7,0xe6fc1f3f83e3e3ba,0xf8ffe03ffc03fc3c])
def zvD : Nat := (cB [0x4a39291829583258,0x2000000400010907,0x194b506912ca42a8,0x7921ab258929430])
def zbX : Nat := 0xc300c300c300c300
abbrev zch : Nat := gZ &&& zbX
abbrev zcs : List Nat := [0x8200820082008200,0xc000c000c000c000,0xc3000000c3000000,0xc300c30000000000]
def zil : Nat × List Nat × Nat × Nat := (zbX,zcs,6,zch)
def zde : List (Nat × List Nat × Nat × Nat) := []
def zhv : Option ({rows : List Nat // rows.length = 24}) := some ⟨[15,30,46,57,15,30,46,57,15,30,46,57,14,25,41,56,14,25,41,56,14,25,41,56],rfl⟩
def zuI := uW zcs [7694,269833,539662,809998]
def zxC (i : Nat) : Nat := uP 0xa28301 6 i
def zoK (i : Nat) : Nat := uP (cB [0x31010c504010000f,0x1292c5]) 17 i
def zqp (i : Nat) : Nat := uP 0x3144010803c 15 i
def zgO := pageLinks zxC zoK 3 13 2 4
def zgz (i : Nat) : Nat × Nat :=
  let e := zqp i
  (e &&& 3,e >>> 2)
def zrG : Nat × Nat := (zxc,64)
def zsQ := zr zbX 64 (zD zcs zvp zvD 64) 5 zgz
def zlQ := zw zbX zcs 5 zgz
def ztR : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm36,(fun i : Fin 64 => Fin.ofNat 64 (pA [4,1,2,3,0,5] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [4,1,2,3,0,5] 0 i.val))),(pm37,(fun i : Fin 64 => Fin.ofNat 64 (pA [5,1,2,3,0,4] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [4,1,2,3,5,0] 0 i.val)))]
def zfP := zaa ztR
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ztl : dM zbX zch 64 zfP := zah (by decide +kernel)
def zhc (i : Nat) : Nat :=
  let j := i / 16
  uP 0x0 1 (i % 16)
def zmi := zc zbX zch zhv (fun i => zt zch (cutPick zde (zhc i))) 3 zlQ zfP zgO zrG zsQ
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zqQ : zd zbX zch zhv (zt zch zde) zuI (zz 3 zlQ zfP zgO 0) zcs 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zuJ : tB 0 3 zmi = true := by decide +kernel
theorem ztF : tB 0 3 zmi = true := zuJ
theorem zuQ : Known zde := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zbJ : Lower zbX zcs zch 6 := by
  apply lowerDag zhc _ _ _ _ ztl _ _ _ zuQ _ zqQ ztF
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold pW; decide +kernel
  · exact cK (by decide +kernel)
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [zde,List.mem_cons,List.not_mem_nil,or_false]
    intro b h
    exact False.elim h
def zeD : Nat := 0xa050a050a050a050
abbrev zgh : Nat := gZ &&& zeD
abbrev ziA : List Nat := [0xa000a000a000a000,0x8040804080408040,0xa0500000a0500000,0xa050a05000000000]
def zlc : Nat × List Nat × Nat × Nat := (zeD,ziA,6,zgh)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zjt : Lower zeD ziA zgh 6 := zp (width := 64) pm19 zbJ (by decide +kernel)
def pm38 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01,st23,st24]
def zdN : Nat := 0xa0a05050a0a05050
abbrev zgR : Nat := gZ &&& zdN
abbrev zkM : List Nat := [0xa0a00000a0a00000,0x8080404080804040,0xa0005000a0005000,0xa0a0505000000000]
def ziD : Nat × List Nat × Nat × Nat := (zdN,zkM,6,zgR)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zkg : Lower zdN zkM zgR 6 := zp (width := 64) pm38 zbJ (by decide +kernel)
def pm39 : List (List (Nat × Nat) × List (Nat × Nat)) := [st23,st24,st25]
def zfv : Nat := 0xc0c0c0c030303030
abbrev zje : Nat := gZ &&& zfv
abbrev zjV : List Nat := [0x8080808020202020,0xc0c0c0c000000000,0xc000c00030003000,0xc0c0000030300000]
def zhN : Nat × List Nat × Nat × Nat := (zfv,zjV,6,zje)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zgG : Lower zfv zjV zje 6 := zp (width := 64) pm39 zbJ (by decide +kernel)
def zdH : Nat := 0xff00ff00
abbrev zic : Nat := gZ &&& zdH
abbrev zfW : List Nat := [0xaa00aa00,0xcc00cc00,0xf000f000,0xff000000]
def zdm : Nat × List Nat × Nat × Nat := (zdH,zfW,5,zic)
def zpC := uW zfW [5642,267785,539161,799754]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zbI : Lower zdH zfW zic 5 := by
  apply eL (witnesses := zpC) (cut := zN)
  · unfold pW; decide +kernel
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold pW; decide +kernel
  · exact uC (old := zE) (by decide +kernel)
  · exact zx
  · decide +kernel
def zfK : Nat := 0xf0f00000f0f0
abbrev zln : Nat := gZ &&& zfK
abbrev zjH : List Nat := [0xa0a00000a0a0,0xc0c00000c0c0,0xf0000000f000,0xf0f000000000]
def zdG : Nat × List Nat × Nat × Nat := (zfK,zjH,5,zln)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zeH : Lower zfK zjH zln 5 := zp (width := 64) pm14 zbI (by decide +kernel)
def zev : Nat := 0xf000f000f000f0
abbrev zii : Nat := gZ &&& zev
abbrev zhb : List Nat := [0xa000a000a000a0,0xc000c000c000c0,0xf0000000f00000,0xf000f000000000]
def zjv : Nat × List Nat × Nat × Nat := (zev,zhb,5,zii)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zhg : Lower zev zhb zii 5 := zp (width := 64) pm24 zbI (by decide +kernel)
def pm40 : List (List (Nat × Nat) × List (Nat × Nat)) := [st15]
def zeN : Nat := 0x3030303030303030
abbrev zlP : Nat := gZ &&& zeN
abbrev zgs : List Nat := [0x2020202020202020,0x3000300030003000,0x3030000030300000,0x3030303000000000]
def zku : Nat × List Nat × Nat × Nat := (zeN,zgs,5,zlP)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zlN : Lower zeN zgs zlP 5 := zp (width := 64) pm40 zbE (by decide +kernel)
def zeX : Nat := 0xaa00aa00aa00aa00
abbrev zhl : Nat := gZ &&& zeX
abbrev zei : List Nat := [0x8800880088008800,0xa000a000a000a000,0xaa000000aa000000,0xaa00aa0000000000]
def zgC : Nat × List Nat × Nat × Nat := (zeX,zei,5,zhl)
def zxa := uW zei [5641,277017,539149,809485]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zcd : Lower zeX zei zhl 5 := by
  apply eL (witnesses := zxa) (cut := zct)
  · unfold pW; decide +kernel
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold pW; decide +kernel
  · exact uC (old := zcA) (by decide +kernel)
  · exact zcM
  · decide +kernel
def zfn : Nat := 0xc0c0c0c0c0c0c0c0
abbrev zjC : Nat := gZ &&& zfn
abbrev zlr : List Nat := [0x8080808080808080,0xc000c000c000c000,0xc0c00000c0c00000,0xc0c0c0c000000000]
def zcF : Nat × List Nat × Nat × Nat := (zfn,zlr,5,zjC)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zcG : Lower zfn zlr zjC 5 := zp (width := 64) pm19 zcd (by decide +kernel)
def pm41 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01,st02,st34,st35]
def zeL : Nat := 0xf0f0f0f000000000
abbrev zkw : Nat := gZ &&& zeL
abbrev zhM : List Nat := [0xa0a0a0a000000000,0xc0c0c0c000000000,0xf000f00000000000,0xf0f0000000000000]
def zky : Nat × List Nat × Nat × Nat := (zeL,zhM,5,zkw)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zgk : Lower zeL zhM zkw 5 := zp (width := 64) pm41 zcd (by decide +kernel)
def zfc : Nat := 0xf0f00000
abbrev zkQ : Nat := gZ &&& zfc
abbrev zkh : List Nat := [0xa0a00000,0xc0c00000,0xf0000000]
def zxu : Nat × List Nat × Nat × Nat := (zfc,zkh,4,zkQ)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zoZ : Lower zfc zkh zkQ 4 := zp (width := 64) pm18 zx (by decide +kernel)
def pm42 : List (List (Nat × Nat) × List (Nat × Nat)) := [st35,st34]
def zfm : Nat := 0xf0000000f00000
abbrev zlg : Nat := gZ &&& zfm
abbrev zli : List Nat := [0xa0000000a00000,0xc0000000c00000,0xf0000000000000]
def znA : Nat × List Nat × Nat × Nat := (zfm,zli,4,zlg)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zwD : Lower zfm zli zlg 4 := zp (width := 64) pm42 zx (by decide +kernel)
def pm43 : List (List (Nat × Nat) × List (Nat × Nat)) := [st15,st13,st34]
def zfu : Nat := 0x3030000030300000
abbrev zig : Nat := gZ &&& zfu
abbrev zgq : List Nat := [0x2020000020200000,0x3000000030000000,0x3030000000000000]
def zpm : Nat × List Nat × Nat × Nat := (zfu,zgq,4,zig)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zpf : Lower zfu zgq zig 4 := zp (width := 64) pm43 zx (by decide +kernel)
def zeY : Nat := 0x4040404040404040
abbrev zld : Nat := gZ &&& zeY
abbrev zlz : List Nat := [0x4000400040004000,0x4040000040400000,0x4040404000000000]
def ziq : Nat × List Nat × Nat × Nat := (zeY,zlz,4,zld)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zlJ : Lower zeY zlz zld 4 := zp (width := 64) pm22 zx (by decide +kernel)
def pm44 : List (List (Nat × Nat) × List (Nat × Nat)) := [st05,st01,st13]
def zew : Nat := 0x5050505000000000
abbrev zgj : Nat := gZ &&& zew
abbrev zkx : List Nat := [0x4040404000000000,0x5000500000000000,0x5050000000000000]
def zxB : Nat × List Nat × Nat × Nat := (zew,zkx,4,zgj)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zrX : Lower zew zkx zgj 4 := zp (width := 64) pm44 zx (by decide +kernel)
def pm45 : List (List (Nat × Nat) × List (Nat × Nat)) := [st15,st34]
def zvg : Nat := (cB [0x3c1a0f0301c0a07,0x41a1d0b05c2a1707,0xc1e07078381d0a87,0x7120940a250e0782,0x70b8582d068b44c2,0xd42a35160b84c2e0,0x6836130d82c361a0,0x71a0f0583c0e0f0,0xa81c1c070681c08,0x3c0a0f1301c2c07,0xc0c170285c180f03,0x81d060740a1d0a05,0xf0a078181e030782,0xb07c2a1f0707c1a1,0x941a2502094381f0,0x6825160944c250a8,0x2d1209c0c270289c,0x30b8482d060b40a,0xbc1a2f120b8182e,0x40a35160bc4c2f07,0x836030d848350a0d,0x70b0dc2a37120d82,0xa0f0183c1a0dc4c3,0xf42a3d068f4483c0,0x1c3e1a0f4583d0e0,0x3e130f8383e0b0f8,0xa01c18071a0f858])
def zpZ : Nat := (cB [0x7fffc7fff031f1ff,0xf1ce4e3fc0f8f1fc,0xff00fe3f8e07f8ff,0xf007ff1c0e0f8fcc,0xff00ff03fff003f,0x3fffffc00007ffe0,0xfff800000ffff000,0x3fffffff])
def zwT : Nat := (cB [0x12314124a01090d5,0x40c6462a00181044,0xb0062188442884b,0x2094d210660b8b4c,0x8b700db05569002d,0xa6b2b48001272481,0x49c000020dad6000,0x38c4c932])
def zbB : Nat := 0xf0f0f0f0f0f0f0f0
abbrev zcl : Nat := gZ &&& zbB
abbrev zbD : List Nat := [0xa0a0a0a0a0a0a0a0,0xc0c0c0c0c0c0c0c0,0xf000f000f000f000,0xf0f00000f0f00000,0xf0f0f0f000000000]
def zub : Nat × List Nat × Nat × Nat := (zbB,zbD,10,zcl)
def zcW : List (Nat × List Nat × Nat × Nat) := [zcN,zhG,zgY,zlc,ziD,zhN,zdJ,zdG,zjv,zku,zcF,zky,zY,zxu,zhP,znA,zfN,zpm,ziq,zxB]
def zkP : Option ({rows : List Nat // rows.length = 24}) := some ⟨[7,29,30,37,46,54,60,7,29,30,37,46,13,14,21,22,28,38,44,52,13,14,21,22],rfl⟩
def zux := uW zbD [3590,265733,539157,801293,1067525]
def zni (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 7 (bI j 3 (bI j 1 (cB [0x79008b40180001,0xa00140026104c,0x5460a80140828005,0xc0018003000]) (bI j 2 (cB [0xdc01b803700607,0xfc21ba037006e,0x88510c2218040188,0x129225004908]) (cB [0x617a82f005548a62,0x1e003c007800e4,0xf801e083c007800f,0x1f063e007c00]))) (bI j 5 (bI j 4 (cB [0x120403f887f00fe0,0xc421044108820102,0x200228c45008a010,0x248048089001]) (cB [0xf264049989301241,0x402a425480a80932,0x5832b005600aa115,0x2bc45780af01])) (bI j 6 (cB [0x2ec05c88b141620,0xa02f505e80bb1176,0x8c231806284c5018,0x32406404c801]) (cB [0xe34006800d001927,0xb37c26f80de09a0,0xfc13ae67580eb01c,0x40008000ff09])))) (bI j 10 (bI j 8 (cB [0x410682010402004,0x804300839507020e,0x220444086150c021,0x44e288891102]) (bI j 9 (cB [0x4b0295852b02487,0x4bc296892d025a,0x7204dc4991530126,0x4e469c813902]) (cB [0x4f449e813d02781,0x814fca9f813f027e,0x9845208a401451a8,0x588ea8c5500a]))) (bI j 12 (bI j 11 (cB [0x15b40b6816d02d24,0x205c02b7856e0ada,0xfe45d54b9897112e,0x60c8c1818302]) (cB [0x6206c38587030e0,0x363c2c5918b0316,0x6616a92ca59930b2,0x6f02da9db40b])) (bI j 13 (cB [0x27080df11bd0b7a0,0x9674d2e3b1c41b84,0xf207dc4fb81f22bb,0x7fc2fe0df91b]) 0x4003)))) 15 (i % 16)
def zoA (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 16 (bI j 8 (bI j 4 (bI j 2 (bI j 1 (cB [0x1004c0100400001f,0x18a88631488806e1,0x335f864e3f0c6c6a,0xe629880b919b93a3,0xc54964fc63331cc4,0x90d871bf24cd]) (cB [0x58c540218a4d4c39,0x199a1e32703c6360,0x27078c400d8cdc15,0x68f24b20f3198406,0xb61cc04c38c3d26,0x10c400180de])) (bI j 3 (cB [0x224b00831980e627,0x61c812c384212668,0x2c01987002a4b00a,0x40618990661c00c9,0xe49601a63e430c6,0x829e888730e0]) (cB [0x90cf811199020314,0x61c026932030c400,0x26058629043d1014,0x69881121990243,0x1a61c03492c060c8,0x5cc8106bd11]))) (bI j 6 (bI j 5 (cB [0xca4b01931002e314,0x3100303300652808,0x3d4712580e98f41c,0x20218801931823a9,0x1a319a28627038c4,0x7d2580e18dc]) (cB [0x730e60461c628933,0x18a40ac380152590,0x3104c64a088c6407,0xd0898f8213102263,0x77a2626c3e84d27,0xa064e118c52])) (bI j 7 (cB [0x50d082919fa50333,0x3138626260b8c401,0x3e4ccc669898c833,0x81b99083631f86a6,0x3f49f87a9330e925,0x4fd87e9d30e0]) (cB [0x21898427a2882f44,0x49604a63e490c641,0x3009de889330e026,0x816989c2c3100563,0x2f61c05e92c4b125,0x90628183d11])))) (bI j 12 (bI j 10 (bI j 9 (cB [0x28c50344a5064f44,0x49f0689320ac6801,0x2c0e4c781c188134,0x41318813949e2709,0x384a105e92c0b0c8,0xf1e881db0e0]) (cB [0xa02d1a707c028,0x49906092c09cc402,0x440f18709924f832,0x623004c44004a78f,0x4b019a9002712003,0x86282700dc])) (bI j 11 (cB [0xb189c50310482337,0x499aa092c17cc662,0x4419d87231b0e15f,0x824b0e0477a208af,0x4c61c09892c129e8,0xc62826bd11]) (cB [0x60ccd4919389ec38,0x496478637010c402,0x3915187029a4cc51,0x82930e0054960aac,0x718a0a4c3801925,0x160c402b8c74]))) (bI j 14 (bI j 13 (cB [0xea4f85b3210b263e,0x18e0bcf4457587c2,0x405712602e18c05a,0x300c740818a0b86,0x5d4990b2632184c4,0x189e88a9b0e0]) (cB [0x3004c64007c8a009,0x19c9402791c03e3,0x2711c63e228c574a,0x80498814a1998943,0x5461c0bc93315125,0x194018328c71])) (bI j 15 (cB [0x480c8690130d001e,0x31009e34113467ab,0x3d1552591399040a,0x4b130f55561c0c49,0x6c0190d80261ac02,0x1b80843680f9]) (cB [0x10d0c2318e816314,0x31f2de6321bcc4d2,0x331e52583a990872,0xebcb0e07c49f8f69,0x7d7a2ccef445f187,0x9a5e89343d10]))))) (bI j 24 (bI j 20 (bI j 18 (bI j 17 (cB [0x899087018e818314,0x18e81a314989e883,0x3d1d8c403a3d1073,0xbba4f5764960ee6,0x2631481c6201e187,0x1e98703b2508]) (cB [0xc2530744a44aaf44,0x98fe01103c0103,0x148fc08614007c87,0x4470cf8891991103,0x6f31012834324868,0x2592644a990c])) (bI j 19 (cB [0xfbd109b61f934c38,0x18a4800429f1e8b2,0x3820526440188070,0xd303d108561f908c,0x8601a10603420987,0x20cc484124f0]) (cB [0x88022617a2020314,0x1a01180112280200,0x3822c6292cbd108d,0x2478040120044b4c,0x7118a12031424402,0x4c01049a4b0]))) (bI j 22 (bI j 21 (cB [0xc30f897314102011,0x8cb8c38975e884,0x14264669c100d482,0x84999088418e8283,0x8501a90a011d4de8,0x2612784e0cd3]) (cB [0xf004415004132624,0x2185201f2980264,0x3223864c540c5229,0x25519007231031c3,0xb4321d666422ccc8,0x2dd2665aa4b0])) (bI j 23 (cB [0x98c52727a236ac38,0x49614662027c6803,0x4469187052a4cca4,0xe509880a018a4e6f,0xa032034292c288c4,0x288698509900]) (cB [0x499001618a14e64c,0x40cac3805c6285,0x1429c0264f804418,0x657189cab3101523,0xb1499b5692c2c4c6,0x646285930e1])))) (bI j 28 (bI j 26 (bI j 25 (cB [0x6b0e0ac49614231d,0x49f15e31c2880225,0x202c1264d830f8b0,0x8d6b0e0ad4960ca6,0xab4a014831d06862,0x2b18805b30e0]) (cB [0x71930b819414a011,0x88360082bc6805,0x140dc0831500d42a,0xca8c9c9518d8ea3,0xb31991663312a866,0x2e8c405a0cce])) (bI j 27 (cB [0x98f69531997a627,0x499b7492c30cc7e6,0x3870d27ee0a4f795,0xa0e0c50c47a24eac,0x381a0c583350b063,0x2acc603b1880]) (cB [0xe3d127661c17692c,0x895a93c2b12605,0x3c2f863d1681042d,0x460252abe32095c3,0xb019e17e34070189,0x30803a0e8020]))) (bI j 30 (bI j 29 (cB [0x88cf2777a20ee314,0x49616463c3012645,0x1f078628de30e0bc,0x22818823a19b8743,0xb5319b346271e4c4,0x3192585d18dc]) (cB [0xcb0e65061c734933,0x31b87662b07cc413,0x331e925a28a4b23b,0x328b0e0bb49b96c9,0x3d0098400089e987,0x32803e640074])) (bI j 31 (cB [0xd8c545618a47a043,0x18f99831d2246323,0x3f6586624b0c94cd,0xc679880bd1a196e3,0xcd321d98642a24c7,0xe5987d4b24fa]) (bI j 32 (cB [0xf004a7b7a2cacf44,0x4960ae3148f80841,0x4e32c63b2bbd10c9,0x8cb8cc09718c5966,0xbe1a719601d96de8,0x2fc680671938]) (cB [0xc3d1058310042314,0x12]))))))) 23 (i % 16)
def ztC (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 6 (bI j 3 (bI j 1 (cB [0x8c50080100201f00,0x52580a6200301b81,0x66330331381b0e01,0xc18a8130e40d8700,0x124b030c7c186260,0x18d8]) (bI j 2 (cB [0xcf8406642031410,0x866604c381049908,0x2640163200b8c505,0xc19b8124b058c403,0xf988008c7a386201,0x4960]) (cB [0x804c04c404262702,0xc7c486262418a11,0x6327237a21224b09,0xb198158d088c67e4,0x798808cc4e566202,0x4961]))) (bI j 4 (cB [0xbd10c8c4c46f442f,0xcc7c4694a3431391,0x620383211198fc8,0xb61c1da4b08cc787,0x180a0f926646f443,0x49f9]) (bI j 5 (cB [0xbd148de884602840,0x1e888a0094418a00,0x201b447a223804d1,0xc019a23d11258709,0x780dd11e889892c4,0x61c2]) (cB [0xb0e149258a262044,0x1872a2c3851499a8,0xe6205718eab989d1,0xc3212b8c7168c7ca,0x23d115d27cae6305,0x319a])))) (bI j 9 (bI j 7 (cB [0x3d1180c40c031d60,0x638ca00f6461c22,0x1e6861ca2004d9,0xb009358c540404cd,0x58109ac07cd60266,0x3133]) (bI j 8 (cB [0x98f9acc84e031d70,0x8c84d6f447318eb9,0x6c387631ebb1881d,0xb499b5b0e1e9258d,0xf8c6c05e8ad693f6,0x8b]) (cB [0xb0fa092650062080,0x987f00c388001a41,0xe3147f009bf80d21,0xa18a45804228664f,0x78cf9fc681140118,0x84]))) (bI j 11 (bI j 10 (cB [0x8d09fc0231e31490,0xcc86fe3437f49649,0x2c3e973144ba4c9f,0xc61fbfb0e1fc6693,0xf804678666023349,0x1a04]) (cB [0x989e80c4140314a0,0x92673e92c9f3104f,0x23149e32653804e7,0xc31055990278c815,0x7989ead8715892ca,0x18e5])) (bI j 12 (cB [0x30e2acc675693eaf,0x92593c6439e320cf,0x2328b8499cf30e2d,0xb4965d9882e866e0,0xf8c7af8c4f74f44b,0x1a05]) (cB [0x7708c7b7494abe,0x8c4002f44ba31fdd,0x201dc831380a4b31,0x818ee5807f212599,0x4193b3863f9031dc,0x3106]))))) 21 (i % 16)
def ziO := pageLinks zni zoA 5 13 8 6
def zjU (i : Nat) : Nat × Nat :=
  let e := ztC i
  (e &&& 255,e >>> 8)
def zqk : Nat × Nat := (zvg,96)
def ztw := zr zbB 96 (zD zbD zpZ zwT 96) 9 zjU
def ziy := zw zbB zbD 9 zjU
def zxe : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm18,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,4,3,5] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,4,3,5] 0 i.val))),(pm40,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,5,2,3,4,1] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,5,2,3,4,1] 0 i.val))),(pm45,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,5,2,4,3,1] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,5,2,4,3,1] 0 i.val)))]
def zdy := zaa zxe
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zmp : dM zbB zcl 64 zdy := zah (by decide +kernel)
def zkj (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 6 (bI j 3 (bI j 1 (cB [0x400070000700007,0x10000,0x10000000002000,0xc00070000000,0x8000700000000000]) (bI j 2 (cB [0x4000058000100000,0xc0007000004000,0x4000100000000,0xc00070000000,0x100007000000]) (cB [0x70040700002c0007,0x8060,0x4010000000000000,0x1001034418044300,0xc3f000020]))) (bI j 4 (cB [0x200000089c700000,0x103447000000000,0xd010400200d87004,0x500708,0x54000018005830]) (bI j 5 (cB [0x7808608084700048,0x700000006270000,0x5040700000702,0x404270000000,0x30227000000]) (cB [0x110007,0x700000000010000,0x2000000200000006,0x60000000,0x60700002000040])))) (bI j 9 (bI j 7 (cB [0x7000000000000000,0x0,0x607000,0x89a7703e70060700,0x20207b0be7434675]) (bI j 8 (cB [0x302270000000000,0x40627004000000,0x70004000000000,0x620306860000015,0x8c70030700e400]) (cB [0x4000400000,0x0,0xac7081ef00001000,0x20600,0x23420234780a060]))) (bI j 11 (bI j 10 (cB [0x80a870000000000,0x500202001000000,0x40506207,0x402a00700,0x40007c0187002470]) (cB [0x0,0x100000000000000,0x60033e700000000,0x10010044703,0x200002000000])) (bI j 12 (cB [0x7400200000000000,0x11007000007060,0xc0700006001c2000,0x1500700,0x20000200d860]) (cB [0x2000010818700000,0x70000740da70000,0xe4700087000,0x447000020000300,0x3cf00002001864]))))) 20 (i % 16)
def zbh := zc zbB zcl zkP (fun i => zt zcl (cutPick zcW (zkj i))) 208 ziy zdy ziO zqk ztw
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zwR : zd zbB zcl zkP (zt zcl zcW) zux (zz 208 ziy zdy ziO 0) zbD 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zwf : tB 0 24 zbh = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zsm : tB 24 24 zbh = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zot : tB 48 24 zbh = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zuH : tB 72 24 zbh = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zoL : tB 96 24 zbh = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zpV : tB 120 24 zbh = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zvS : tB 144 24 zbh = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zvc : tB 168 24 zbh = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zwZ : tB 192 16 zbh = true := by decide +kernel
theorem zvX : tB 0 48 zbh = true := tM (start := 0) (left := 24) (right := 24) (check := zbh) zwf zsm
theorem zom : tB 48 48 zbh = true := tM (start := 48) (left := 24) (right := 24) (check := zbh) zot zuH
theorem zny : tB 0 96 zbh = true := tM (start := 0) (left := 48) (right := 48) (check := zbh) zvX zom
theorem zsY : tB 96 48 zbh = true := tM (start := 96) (left := 24) (right := 24) (check := zbh) zoL zpV
theorem zpv : tB 168 40 zbh = true := tM (start := 168) (left := 24) (right := 16) (check := zbh) zvc zwZ
theorem zvU : tB 144 64 zbh = true := tM (start := 144) (left := 24) (right := 40) (check := zbh) zvS zpv
theorem zuh : tB 96 112 zbh = true := tM (start := 96) (left := 48) (right := 64) (check := zbh) zsY zvU
theorem zpS : tB 0 208 zbh = true := tM (start := 0) (left := 96) (right := 112) (check := zbh) zny zuh
theorem zqT : tB 0 208 zbh = true := zpS
theorem zuL : Known zcW := (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) zrX) zlJ) zpf) zeS) zwD) zid) zoZ) zx) zgk) zcG) zlN) zhg) zeH) zbE) zgG) zkg) zjt) zjN) zcu) zcQ)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zbG : Lower zbB zbD zcl 10 := by
  apply lowerDag zkj _ _ _ _ zmp _ _ _ zuL _ zwR zqT
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold pW; decide +kernel
  · exact cK (by decide +kernel)
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [zcW,List.mem_cons,List.not_mem_nil,or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def zdi : Nat := 0xf0f0f0f0ffffffff
abbrev zlM : Nat := gZ &&& zdi
abbrev zfh : List Nat := [0xa0a0a0a0aaaaaaaa,0xc0c0c0c0cccccccc,0xf0f0f0f0f0f0f0f0,0xf000f000ff00ff00,0xf0f00000ffff0000,0xf0f0f0f000000000]
def zsc : Nat × List Nat × Nat × Nat := (zdi,zfh,11,zlM)
def zmm := uW zfh [1538,263681,539161,799762,1061898,1329669]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zcR : Lower zdi zfh zlM 11 := by
  apply eL (witnesses := zmm) (cut := zbB)
  · unfold pW; decide +kernel
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold pW; decide +kernel
  · exact uC (old := zbD) (by decide +kernel)
  · exact zbG
  · decide +kernel
def zfj : Nat := 0xf0f0fffff0f0ffff
abbrev zgn : Nat := gZ &&& zfj
abbrev zez : List Nat := [0xa0a0aaaaa0a0aaaa,0xc0c0ccccc0c0cccc,0xf0f0f0f0f0f0f0f0,0xf000ff00f000ff00,0xf0f00000f0f00000,0xf0f0ffff00000000]
def zuV : Nat × List Nat × Nat × Nat := (zfj,zez,11,zgn)
def zmv := uW zez [1538,263681,543265,801301,1063437,1329669]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zbV : Lower zfj zez zgn 11 := by
  apply eL (witnesses := zmv) (cut := zbB)
  · unfold pW; decide +kernel
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold pW; decide +kernel
  · exact uC (old := zbD) (by decide +kernel)
  · exact zbG
  · decide +kernel
def zdK : Nat := 0xf0fff0fff0fff0ff
abbrev zhf : Nat := gZ &&& zdK
abbrev zhe : List Nat := [0xa0aaa0aaa0aaa0aa,0xc0ccc0ccc0ccc0cc,0xf0f0f0f0f0f0f0f0,0xf000f000f000f000,0xf0ff0000f0ff0000,0xf0fff0ff00000000]
def zuq : Nat × List Nat × Nat × Nat := (zdK,zhe,11,zhf)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zxx : Lower zdK zhe zhf 11 := zp (width := 64) pm18 zbV (by decide +kernel)
def zgc : Nat := 0xf3f3f3f3f3f3f3f3
abbrev zkr : Nat := gZ &&& zgc
abbrev zfS : List Nat := [0xa2a2a2a2a2a2a2a2,0xc0c0c0c0c0c0c0c0,0xf0f0f0f0f0f0f0f0,0xf300f300f300f300,0xf3f30000f3f30000,0xf3f3f3f300000000]
def zuY : Nat × List Nat × Nat × Nat := (zgc,zfS,11,zkr)
def zpq := uW zfS [3590,265733,539161,801301,1063437,1329669]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zcI : Lower zgc zfS zkr 11 := by
  apply eL (witnesses := zpq) (cut := zbB)
  · unfold pW; decide +kernel
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold pW; decide +kernel
  · exact uC (old := zbD) (by decide +kernel)
  · exact zbG
  · decide +kernel
def zfa : Nat := 0xf5f5f5f5f5f5f5f5
abbrev ziv : Nat := gZ &&& zfa
abbrev zdp : List Nat := [0xa0a0a0a0a0a0a0a0,0xc4c4c4c4c4c4c4c4,0xf0f0f0f0f0f0f0f0,0xf500f500f500f500,0xf5f50000f5f50000,0xf5f5f5f500000000]
def zud : Nat × List Nat × Nat × Nat := (zfa,zdp,11,ziv)
def zmJ := uW zdp [3590,265733,547882,799762,1061898,1329669]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zcH : Lower zfa zdp ziv 11 := by
  apply eL (witnesses := zmJ) (cut := zbB)
  · unfold pW; decide +kernel
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold pW; decide +kernel
  · exact uC (old := zbD) (by decide +kernel)
  · exact zbG
  · decide +kernel
def zfC : Nat := 0xfafafafafafafafa
abbrev zgL : Nat := gZ &&& zfC
abbrev zdk : List Nat := [0xaaaaaaaaaaaaaaaa,0xc8c8c8c8c8c8c8c8,0xf0f0f0f0f0f0f0f0,0xfa00fa00fa00fa00,0xfafa0000fafa0000,0xfafafafa00000000]
def ztU : Nat × List Nat × Nat × Nat := (zfC,zdk,11,zgL)
def zop := uW zdk [3590,263681,539161,801301,1063437,1329669]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zcL : Lower zfC zdk zgL 11 := by
  apply eL (witnesses := zop) (cut := zbB)
  · unfold pW; decide +kernel
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold pW; decide +kernel
  · exact uC (old := zbD) (by decide +kernel)
  · exact zbG
  · decide +kernel
def zeO : Nat := 0xfcfcfcfcfcfcfcfc
abbrev zgQ : Nat := gZ &&& zeO
abbrev zfA : List Nat := [0xa8a8a8a8a8a8a8a8,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfc00fc00fc00fc00,0xfcfc0000fcfc0000,0xfcfcfcfc00000000]
def zmZ : Nat × List Nat × Nat × Nat := (zeO,zfA,11,zgQ)
def zwj := uW zfA [1538,265733,547882,799762,1061898,1329669]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zdb : Lower zeO zfA zgQ 11 := by
  apply eL (witnesses := zwj) (cut := zbB)
  · unfold pW; decide +kernel
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold pW; decide +kernel
  · exact uC (old := zbD) (by decide +kernel)
  · exact zbG
  · decide +kernel
def zef : Nat := 0xff00ff00ffffffff
abbrev zgZ : Nat := gZ &&& zef
abbrev zlS : List Nat := [0xaa00aa00aaaaaaaa,0xcc00cc00cccccccc,0xf000f000f0f0f0f0,0xff00ff00ff00ff00,0xff000000ffff0000,0xff00ff0000000000]
def zxJ : Nat × List Nat × Nat × Nat := (zef,zlS,11,zgZ)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem znV : Lower zef zlS zgZ 11 := zp (width := 64) pm14 zbV (by decide +kernel)
def zfQ : Nat := 0xff00ffffff00ffff
abbrev zmk : Nat := gZ &&& zfQ
abbrev zlA : List Nat := [0xaa00aaaaaa00aaaa,0xcc00cccccc00cccc,0xf000f0f0f000f0f0,0xff00ff00ff00ff00,0xff000000ff000000,0xff00ffff00000000]
def zqH : Nat × List Nat × Nat × Nat := (zfQ,zlA,11,zmk)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zpA : Lower zfQ zlA zmk 11 := zp (width := 64) pm14 zcR (by decide +kernel)
def zdE : Nat := 0xff0fff0fff0fff0f
abbrev zhT : Nat := gZ &&& zdE
abbrev zlD : List Nat := [0xaa0aaa0aaa0aaa0a,0xcc0ccc0ccc0ccc0c,0xf000f000f000f000,0xff00ff00ff00ff00,0xff0f0000ff0f0000,0xff0fff0f00000000]
def zwE : Nat × List Nat × Nat × Nat := (zdE,zlD,11,zhT)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zsF : Lower zdE zlD zhT 11 := zp (width := 64) pm25 zbV (by decide +kernel)
def zeT : Nat := 0xff33ff33ff33ff33
abbrev zmc : Nat := gZ &&& zeT
abbrev zkN : List Nat := [0xaa22aa22aa22aa22,0xcc00cc00cc00cc00,0xf030f030f030f030,0xff00ff00ff00ff00,0xff330000ff330000,0xff33ff3300000000]
def zuO : Nat × List Nat × Nat × Nat := (zeT,zkN,11,zmc)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem znx : Lower zeT zkN zmc 11 := zp (width := 64) pm14 zcH (by decide +kernel)
def zfM : Nat := 0xff55ff55ff55ff55
abbrev zlO : Nat := gZ &&& zfM
abbrev zhV : List Nat := [0xaa00aa00aa00aa00,0xcc44cc44cc44cc44,0xf050f050f050f050,0xff00ff00ff00ff00,0xff550000ff550000,0xff55ff5500000000]
def zxd : Nat × List Nat × Nat × Nat := (zfM,zhV,11,zlO)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zvC : Lower zfM zhV zlO 11 := zp (width := 64) pm14 zcI (by decide +kernel)
def zdF : Nat := 0xffaaffaaffaaffaa
abbrev zhm : Nat := gZ &&& zdF
abbrev zhA : List Nat := [0xaaaaaaaaaaaaaaaa,0xcc88cc88cc88cc88,0xf0a0f0a0f0a0f0a0,0xff00ff00ff00ff00,0xffaa0000ffaa0000,0xffaaffaa00000000]
def zrM : Nat × List Nat × Nat × Nat := (zdF,zhA,11,zhm)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem znc : Lower zdF zhA zhm 11 := zp (width := 64) pm14 zdb (by decide +kernel)
def zdh : Nat := 0xffccffccffccffcc
abbrev zkY : Nat := gZ &&& zdh
abbrev zgJ : List Nat := [0xaa88aa88aa88aa88,0xcccccccccccccccc,0xf0c0f0c0f0c0f0c0,0xff00ff00ff00ff00,0xffcc0000ffcc0000,0xffccffcc00000000]
def zwm : Nat × List Nat × Nat × Nat := (zdh,zgJ,11,zkY)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zsN : Lower zdh zgJ zkY 11 := zp (width := 64) pm14 zcL (by decide +kernel)
def zdR : Nat := 0xfff0fff0fff0fff0
abbrev zkU : Nat := gZ &&& zdR
abbrev zey : List Nat := [0xaaa0aaa0aaa0aaa0,0xccc0ccc0ccc0ccc0,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xfff00000fff00000,0xfff0fff000000000]
def zue : Nat × List Nat × Nat × Nat := (zdR,zey,11,zkU)
def zpQ := uW zey [3590,265733,539161,801301,1061898,1329669]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zcS : Lower zdR zey zkU 11 := by
  apply eL (witnesses := zpQ) (cut := zbB)
  · unfold pW; decide +kernel
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold pW; decide +kernel
  · exact uC (old := zbD) (by decide +kernel)
  · exact zbG
  · decide +kernel
def zfb : Nat := 0xffff0000ffffffff
abbrev zlp : Nat := gZ &&& zfb
abbrev zkn : List Nat := [0xaaaa0000aaaaaaaa,0xcccc0000cccccccc,0xf0f00000f0f0f0f0,0xff000000ff00ff00,0xffff0000ffff0000,0xffff000000000000]
def zof : Nat × List Nat × Nat × Nat := (zfb,zkn,11,zlp)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zpH : Lower zfb zkn zlp 11 := zp (width := 64) pm24 zbV (by decide +kernel)
def zdl : Nat := 0xffff00ffffff00ff
abbrev zkZ : Nat := gZ &&& zdl
abbrev zkT : List Nat := [0xaaaa00aaaaaa00aa,0xcccc00cccccc00cc,0xf0f000f0f0f000f0,0xff000000ff000000,0xffff0000ffff0000,0xffff00ff00000000]
def zpR : Nat × List Nat × Nat × Nat := (zdl,zkT,11,zkZ)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zod : Lower zdl zkT zkZ 11 := zp (width := 64) pm24 zcR (by decide +kernel)
def pm46 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01,st24,st35]
def zfd : Nat := 0xffff0f0fffff0f0f
abbrev zjE : Nat := gZ &&& zfd
abbrev zlk : List Nat := [0xaaaa0a0aaaaa0a0a,0xcccc0c0ccccc0c0c,0xf0f00000f0f00000,0xff000f00ff000f00,0xffff0000ffff0000,0xffff0f0f00000000]
def zsw : Nat × List Nat × Nat × Nat := (zfd,zlk,11,zjE)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem znR : Lower zfd zlk zjE 11 := zp (width := 64) pm46 zbV (by decide +kernel)
def zeQ : Nat := 0xffff3333ffff3333
abbrev zjY : Nat := gZ &&& zeQ
abbrev zhd : List Nat := [0xaaaa2222aaaa2222,0xcccc0000cccc0000,0xf0f03030f0f03030,0xff003300ff003300,0xffff0000ffff0000,0xffff333300000000]
def zpP : Nat × List Nat × Nat × Nat := (zeQ,zhd,11,zjY)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zwL : Lower zeQ zhd zjY 11 := zp (width := 64) pm24 zcH (by decide +kernel)
def zdY : Nat := 0xffff5555ffff5555
abbrev ziE : Nat := gZ &&& zdY
abbrev zgB : List Nat := [0xaaaa0000aaaa0000,0xcccc4444cccc4444,0xf0f05050f0f05050,0xff005500ff005500,0xffff0000ffff0000,0xffff555500000000]
def zrB : Nat × List Nat × Nat × Nat := (zdY,zgB,11,ziE)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zsR : Lower zdY zgB ziE 11 := zp (width := 64) pm24 zcI (by decide +kernel)
def zga : Nat := 0xffffaaaaffffaaaa
abbrev zip : Nat := gZ &&& zga
abbrev ziS : List Nat := [0xaaaaaaaaaaaaaaaa,0xcccc8888cccc8888,0xf0f0a0a0f0f0a0a0,0xff00aa00ff00aa00,0xffff0000ffff0000,0xffffaaaa00000000]
def ztd : Nat × List Nat × Nat × Nat := (zga,ziS,11,zip)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zpg : Lower zga ziS zip 11 := zp (width := 64) pm24 zdb (by decide +kernel)
def zgd : Nat := 0xffffccccffffcccc
abbrev zkS : Nat := gZ &&& zgd
abbrev zle : List Nat := [0xaaaa8888aaaa8888,0xcccccccccccccccc,0xf0f0c0c0f0f0c0c0,0xff00cc00ff00cc00,0xffff0000ffff0000,0xffffcccc00000000]
def zrT : Nat × List Nat × Nat × Nat := (zgd,zle,11,zkS)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem znC : Lower zgd zle zkS 11 := zp (width := 64) pm24 zcL (by decide +kernel)
def zem : Nat := 0xfffff0f0fffff0f0
abbrev zgT : Nat := gZ &&& zem
abbrev zhw : List Nat := [0xaaaaa0a0aaaaa0a0,0xccccc0c0ccccc0c0,0xf0f0f0f0f0f0f0f0,0xff00f000ff00f000,0xffff0000ffff0000,0xfffff0f000000000]
def znk : Nat × List Nat × Nat × Nat := (zem,zhw,11,zgT)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zqb : Lower zem zhw zgT 11 := zp (width := 64) pm18 zcS (by decide +kernel)
def zcE : Nat := 0xff00ff00ff00ff00
abbrev zgu : Nat := gZ &&& zcE
abbrev zea : List Nat := [0xaa00aa00aa00aa00,0xcc00cc00cc00cc00,0xf000f000f000f000,0xff000000ff000000,0xff00ff0000000000]
def zoc : Nat × List Nat × Nat × Nat := (zcE,zea,10,zgu)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zhW : Lower zcE zea zgu 10 := zp (width := 64) pm14 zbG (by decide +kernel)
def zfG : Nat := 0xffffff00ffffff00
abbrev zkz : Nat := gZ &&& zfG
abbrev zdM : List Nat := [0xaaaaaa00aaaaaa00,0xcccccc00cccccc00,0xf0f0f000f0f0f000,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffff0000000000]
def zrr : Nat × List Nat × Nat × Nat := (zfG,zdM,11,zkz)
def zmN := uW zdM [5642,267785,539161,799762,1061898,1333773]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zjP : Lower zfG zdM zkz 11 := by
  apply eL (witnesses := zmN) (cut := zcE)
  · unfold pW; decide +kernel
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold pW; decide +kernel
  · exact uC (old := zea) (by decide +kernel)
  · exact zhW
  · decide +kernel
def zfr : Nat := 0xffffffff0000ffff
abbrev zha : Nat := gZ &&& zfr
abbrev zlx : List Nat := [0xaaaaaaaa0000aaaa,0xcccccccc0000cccc,0xf0f0f0f00000f0f0,0xff00ff000000ff00,0xffff000000000000,0xffffffff00000000]
def zrf : Nat × List Nat × Nat × Nat := (zfr,zlx,11,zha)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zqr : Lower zfr zlx zha 11 := zp (width := 64) pm15 zbV (by decide +kernel)
def zfR : Nat := 0xffffffff00ff00ff
abbrev zif : Nat := gZ &&& zfR
abbrev zgg : List Nat := [0xaaaaaaaa00aa00aa,0xcccccccc00cc00cc,0xf0f0f0f000f000f0,0xff00ff0000000000,0xffff000000ff0000,0xffffffff00000000]
def zoO : Nat × List Nat × Nat × Nat := (zfR,zgg,11,zif)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zpX : Lower zfR zgg zif 11 := zp (width := 64) pm23 zbV (by decide +kernel)
def zge : Nat := 0xffffffff0f0f0f0f
abbrev zjk : Nat := gZ &&& zge
abbrev zis : List Nat := [0xaaaaaaaa0a0a0a0a,0xcccccccc0c0c0c0c,0xf0f0f0f000000000,0xff00ff000f000f00,0xffff00000f0f0000,0xffffffff00000000]
def zrL : Nat × List Nat × Nat × Nat := (zge,zis,11,zjk)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zsq : Lower zge zis zjk 11 := zp (width := 64) pm15 zcR (by decide +kernel)
def zfw : Nat := 0xffffffff33333333
abbrev zjK : Nat := gZ &&& zfw
abbrev zkG : List Nat := [0xaaaaaaaa22222222,0xcccccccc00000000,0xf0f0f0f030303030,0xff00ff0033003300,0xffff000033330000,0xffffffff00000000]
def zvF : Nat × List Nat × Nat × Nat := (zfw,zkG,11,zjK)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zwB : Lower zfw zkG zjK 11 := zp (width := 64) pm15 zcI (by decide +kernel)
def zdD : Nat := 0xffffffff55555555
abbrev zkR : Nat := gZ &&& zdD
abbrev zhX : List Nat := [0xaaaaaaaa00000000,0xcccccccc44444444,0xf0f0f0f050505050,0xff00ff0055005500,0xffff000055550000,0xffffffff00000000]
def zpw : Nat × List Nat × Nat × Nat := (zdD,zhX,11,zkR)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zoD : Lower zdD zhX zkR 11 := zp (width := 64) pm15 zcH (by decide +kernel)
def zeu : Nat := 0xffffffffaaaaaaaa
abbrev zkD : Nat := gZ &&& zeu
abbrev zhD : List Nat := [0xaaaaaaaaaaaaaaaa,0xcccccccc88888888,0xf0f0f0f0a0a0a0a0,0xff00ff00aa00aa00,0xffff0000aaaa0000,0xffffffff00000000]
def zvv : Nat × List Nat × Nat × Nat := (zeu,zhD,11,zkD)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ztg : Lower zeu zhD zkD 11 := zp (width := 64) pm15 zcL (by decide +kernel)
def zeg : Nat := 0xffffffffcccccccc
abbrev zjf : Nat := gZ &&& zeg
abbrev zhr : List Nat := [0xaaaaaaaa88888888,0xcccccccccccccccc,0xf0f0f0f0c0c0c0c0,0xff00ff00cc00cc00,0xffff0000cccc0000,0xffffffff00000000]
def zxi : Nat × List Nat × Nat × Nat := (zeg,zhr,11,zjf)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zqg : Lower zeg zhr zjf 11 := zp (width := 64) pm15 zdb (by decide +kernel)
def zdr : Nat := 0xfffffffff0f0f0f0
abbrev zgp : Nat := gZ &&& zdr
abbrev zkL : List Nat := [0xaaaaaaaaa0a0a0a0,0xccccccccc0c0c0c0,0xf0f0f0f0f0f0f0f0,0xff00ff00f000f000,0xffff0000f0f00000,0xffffffff00000000]
def zpM : Nat × List Nat × Nat × Nat := (zdr,zkL,11,zgp)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zwy : Lower zdr zkL zgp 11 := zp (width := 64) pm14 zjP (by decide +kernel)
def zgb : Nat := 0xffffffffff00ff00
abbrev ziG : Nat := gZ &&& zgb
abbrev zkW : List Nat := [0xaaaaaaaaaa00aa00,0xcccccccccc00cc00,0xf0f0f0f0f000f000,0xff00ff00ff00ff00,0xffff0000ff000000,0xffffffff00000000]
def zmE : Nat × List Nat × Nat × Nat := (zgb,zkW,11,ziG)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zqD : Lower zgb zkW ziG 11 := zp (width := 64) pm15 zcS (by decide +kernel)
def zfF : Nat := 0xffffffffffff0000
abbrev zlK : Nat := gZ &&& zfF
abbrev zjL : List Nat := [0xaaaaaaaaaaaa0000,0xcccccccccccc0000,0xf0f0f0f0f0f00000,0xff00ff00ff000000,0xffff0000ffff0000,0xffffffff00000000]
def zmI : Nat × List Nat × Nat × Nat := (zfF,zjL,11,zlK)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zxE : Lower zfF zjL zlK 11 := zp (width := 64) pm23 zcS (by decide +kernel)
def zfD : Nat := 0xffff0000ffff0000
abbrev zhY : Nat := gZ &&& zfD
abbrev zlw : List Nat := [0xaaaa0000aaaa0000,0xcccc0000cccc0000,0xf0f00000f0f00000,0xff000000ff000000,0xffff000000000000]
def zrH : Nat × List Nat × Nat × Nat := (zfD,zlw,10,zhY)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zmw : Lower zfD zlw zhY 10 := zp (width := 64) pm24 zbG (by decide +kernel)
def zdO : Nat := 0xffffffff00000000
abbrev zhO : Nat := gZ &&& zdO
abbrev zkJ : List Nat := [0xaaaaaaaa00000000,0xcccccccc00000000,0xf0f0f0f000000000,0xff00ff0000000000,0xffff000000000000]
def zut : Nat × List Nat × Nat × Nat := (zdO,zkJ,10,zhO)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem znb : Lower zdO zkJ zhO 10 := zp (width := 64) pm15 zbG (by decide +kernel)
def zfH : Nat := 0xffffffff
abbrev zkK : Nat := gZ &&& zfH
abbrev zfE : List Nat := [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000]
def zfp : Nat × List Nat × Nat × Nat := (zfH,zfE,6,zkK)
def zsJ := uW zfE [1538,263681,539161,799762,1061898]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zcw : Lower zfH zfE zkK 6 := by
  apply eL (witnesses := zsJ) (cut := zN)
  · unfold pW; decide +kernel
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold pW; decide +kernel
  · exact uC (old := zE) (by decide +kernel)
  · exact zx
  · decide +kernel
def zex : Nat := 0xffff0000
abbrev zgi : Nat := gZ &&& zex
abbrev zlf : List Nat := [0xaaaa0000,0xcccc0000,0xf0f00000,0xff000000]
def zfX : Nat × List Nat × Nat × Nat := (zex,zlf,5,zgi)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zdQ : Lower zex zlf zgi 5 := zp (width := 64) pm18 zbI (by decide +kernel)
def zpt : Nat := (cB [0x1c0a070100c0203,0xc1a0f0502c120b03,0xa170904c22130703,0xa09068141a0b05c2,0xa8741a1d0c86c301,0x781c1e0e074321d0,0x4c2e070b8381e0b0,0x360b0d8582e150b8,0x150e86836190d84c,0xf0383c1c0e8643a,0xc00031c0f0683c16,0x4030480c0c030280,0x71100c24030880c1,0x681c08070101c020,0x1c2c070a81c1c070,0x100b0102c020b130,0xb0c82c1c0b0682c,0x483c0c0f0283c54,0x4c02130603c140f,0xc2c130a84c201301,0xc170285c64130c84,0xa0a05c24170885c0,0x80681c1a04068041,0x68381a0c8682c1a0,0x121b1c068641a150,0x1b0906c221b0506c,0x6074121d0287430])
def znv : Nat := (cB [0xffffffc0000f8fff,0xfff0ffffff003fff,0x1fffffffffffffc3,0xe03fc03c7fff0ccc,0x87fff0f0e0003e03,0xffffc003ffc0003f,0x3ff87fff00,0xff800000fffffffc,0x3f])
def zwP : Nat := (cB [0xaa4a4a8000078555,0xbbb03aaa65080aa4,0xa65554954b4b501,0x663f019c5dfb0ccc,0x86ddd0f0a0152662,0xd3b980839f06062e,0x8181837686eef00,0xf70000001cde39f0,0xe001001020203b])
def zbN : Nat := 0x55555555ffffffff
abbrev zce : Nat := gZ &&& zbN
abbrev zcy : List Nat := [0xaaaaaaaa,0x44444444cccccccc,0x50505050f0f0f0f0,0x55005500ff00ff00,0x55550000ffff0000,0x5555555500000000]
def zrx : Nat × List Nat × Nat × Nat := (zbN,zcy,10,zce)
def zcO : List (Nat × List Nat × Nat × Nat) := [zeG,zcN,zdB,zfp,zdm,zfX,zcV]
def zkB : Option ({rows : List Nat // rows.length = 24}) := some ⟨[3,26,29,46,54,60,3,26,29,46,54,60,13,14,21,22,25,28,38,42,44,50,52,56],rfl⟩
def zol := uW zcy [1538,263681,539161,799762,1061898,1334286]
def znK (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 2 (bI j 1 (cB [0xb01512a03600e001,0x26640c81722c2580,0x440790e89c13]) (cB [0x48290502a0113220,0xc0171295520a41,0x620c41883016])) (bI j 3 (cB [0xd83a1740e8194311,0x4120a38bf87e0ed1,0x9e73c252ca09]) (cB [0xe8da3b2351691520,0x178a]))) 11 (i % 16)
def zvE (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 3 (bI j 1 (cB [0x71a315023140003f,0x37a03332e32b2032,0x9334a92d4092cae3,0xac39c0c38629374e,0x692c843370432bc]) (bI j 2 (cB [0x8149370c9330a92d,0x4008c388ac3986c3,0x63c12c3c106300ec,0x93018f480e93016,0x9c63e1c632129301]) (cB [0xe223149ef441ec38,0x3e28c381c6202433,0x630260102cf442ac,0xcc483ac3e36c3c30,0x34c38326203ef443]))) (bI j 4 (cB [0x74231f3493c38c38,0x331e621066204433,0xc3946c38be637ac6,0x86310a6200892c48,0xc314c8f444cc3e2]) (bI j 5 (cB [0xcaa33d2a33124325,0x4458c404cc385092,0xc3c5493052c40ccf,0xc6305a3310e31456,0x1031460c3c5292c5]) (cB [0xc123145492c5e620,0x3c6433d143145692,0xc3c6af4858930666,0xc93068620163145a,0x60930183145e9305])))) 20 (i % 16)
def zxt (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 2 (bI j 1 (cB [0x432b08628080fc0,0x330925a130e04496,0x9878418c086200e9,0xa0bd20b31e169370,0x61c1c6323862]) (cB [0x2633e4462888c9c1,0x444587c8b0e11008,0x4c40c98c1819582f,0xcc30e1c61e30c386,0x7a230c486187])) (bI j 3 (cB [0x423378463f0a4b01,0x3e9925a0b0e6161c,0x98814a4b2849982c,0x36b102861e54930a,0x3105e630b466]) (cB [0x6433dc926e0b0f2d,0x1e9191883431e]))) 19 (i % 16)
def zjh := pageLinks znK zvE 4 13 6 5
def zlU (i : Nat) : Nat × Nat :=
  let e := zxt i
  (e &&& 63,e >>> 6)
def zsp : Nat × Nat := (zpt,96)
def ztI := zr zbN 96 (zD zcy znv zwP 96) 9 zlU
def zhx := zw zbN zcy 9 zlU
def zqu : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm18,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,4,3,5] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,4,3,5] 0 i.val)))]
def zeA := zaa zqu
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zwX : dM zbN zce 64 zeA := zah (by decide +kernel)
def zhu (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 2 (bI j 1 (cB [0xe02387,0x3b8000000]) (cB [0x55ae011000018077,0x43ec000ae000])) (bI j 3 (cB [0xee03b800e00017,0x5401700000]) 0x1d806a01b8b)) 7 (i % 16)
def zbM := zc zbN zce zkB (fun i => zt zce (cutPick zcO (zhu i))) 54 zhx zeA zjh zsp ztI
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zpY : zd zbN zce zkB (zt zce zcO) zol (zz 54 zhx zeA zjh 0) zcy 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zrY : tB 0 24 zbM = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ztf : tB 24 24 zbM = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zva : tB 48 6 zbM = true := by decide +kernel
theorem zsZ : tB 24 30 zbM = true := tM (start := 24) (left := 24) (right := 6) (check := zbM) ztf zva
theorem zuu : tB 0 54 zbM = true := tM (start := 0) (left := 24) (right := 30) (check := zbM) zrY zsZ
theorem zui : tB 0 54 zbM = true := zuu
theorem zuS : Known zcO := (eK (eK (eK (eK (eK (eK (eK (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) zdc) zdQ) zbI) zcw) zdo) zcQ) zel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zdd : Lower zbN zcy zce 10 := by
  apply lowerDag zhu _ _ _ _ zwX _ _ _ zuS _ zpY zui
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold pW; decide +kernel
  · exact cK (by decide +kernel)
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [zcO,List.mem_cons,List.not_mem_nil,or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def zdS : Nat := 0x3333ffff3333ffff
abbrev zib : Nat := gZ &&& zdS
abbrev zjj : List Nat := [0x2222aaaa2222aaaa,0xcccc0000cccc,0x3030f0f03030f0f0,0x3300ff003300ff00,0x3333000033330000,0x3333ffff00000000]
def zmX : Nat × List Nat × Nat × Nat := (zdS,zjj,10,zib)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zmL : Lower zdS zjj zib 10 := zp (width := 64) pm14 zdd (by decide +kernel)
def zeb : Nat := 0x33ff33ff33ff33ff
abbrev zho : Nat := gZ &&& zeb
abbrev zhF : List Nat := [0x22aa22aa22aa22aa,0xcc00cc00cc00cc,0x30f030f030f030f0,0x3300330033003300,0x33ff000033ff0000,0x33ff33ff00000000]
def zra : Nat × List Nat × Nat × Nat := (zeb,zhF,10,zho)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zpy : Lower zeb zhF zho 10 := zp (width := 64) pm24 zdd (by decide +kernel)
def zdP : Nat := 0x5f5f5f5f5f5f5f5f
abbrev zgw : Nat := gZ &&& zdP
abbrev ziU : List Nat := [0xa0a0a0a0a0a0a0a,0x4c4c4c4c4c4c4c4c,0x5050505050505050,0x5f005f005f005f00,0x5f5f00005f5f0000,0x5f5f5f5f00000000]
def zuT : Nat × List Nat × Nat × Nat := (zdP,ziU,10,zgw)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ztW : Lower zdP ziU zgw 10 := zp (width := 64) pm15 zdd (by decide +kernel)
def zfy : Nat := 0xaaaaaaaaaaaaaaaa
abbrev zio : Nat := gZ &&& zfy
abbrev zeJ : List Nat := [0x8888888888888888,0xa0a0a0a0a0a0a0a0,0xaa00aa00aa00aa00,0xaaaa0000aaaa0000,0xaaaaaaaa00000000]
def ziV : Nat × List Nat × Nat × Nat := (zfy,zeJ,6,zio)
def zsf := uW zeJ [1537,277017,539157,801293,1067525]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zfZ : Lower zfy zeJ zio 6 := by
  apply eL (witnesses := zsf) (cut := zct)
  · unfold pW; decide +kernel
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold pW; decide +kernel
  · exact uC (old := zcA) (by decide +kernel)
  · exact zcM
  · decide +kernel
def zdg : Nat := 0xcccccccccccccccc
abbrev zlB : Nat := gZ &&& zdg
abbrev zjd : List Nat := [0x8888888888888888,0xc0c0c0c0c0c0c0c0,0xcc00cc00cc00cc00,0xcccc0000cccc0000,0xcccccccc00000000]
def zlH : Nat × List Nat × Nat × Nat := (zdg,zjd,6,zlB)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zgl : Lower zdg zjd zlB 6 := zp (width := 64) pm14 zfZ (by decide +kernel)
def zdq : Nat := 0xaaaa0000aaaa0000
abbrev zlv : Nat := gZ &&& zdq
abbrev zkb : List Nat := [0x8888000088880000,0xa0a00000a0a00000,0xaa000000aa000000,0xaaaa000000000000]
def zly : Nat × List Nat × Nat × Nat := (zdq,zkb,5,zlv)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zix : Lower zdq zkb zlv 5 := zp (width := 64) pm18 zcd (by decide +kernel)
def zfI : Nat := 0xcccccccc00000000
abbrev zgH : Nat := gZ &&& zfI
abbrev ziZ : List Nat := [0x8888888800000000,0xc0c0c0c000000000,0xcc00cc0000000000,0xcccc000000000000]
def ziB : Nat × List Nat × Nat × Nat := (zfI,ziZ,5,zgH)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zkX : Lower zfI ziZ zgH 5 := zp (width := 64) pm20 zcd (by decide +kernel)
def zuo : Nat := (cB [0x1c0a070100c0203,0xc1a0f0502c120b03,0xa170904c22130703,0xb09068141a0b05c2,0xc8742a1d06874321,0x8c42230b0781c1e0,0x4c27108940a25110,0x2d068b4542b148ac,0x150b84c2e070b852,0x8d42a35190cc6233,0x46436130d82c3618,0x43a188e452390c8e,0x30300c0a03190e85,0x900c22030500c120,0x1c02071100c42030,0x2a070701c1a07010,0xb0082c4c070b01c,0xc82c1c0b0682c04,0x3c0a0f1502c520b,0xc02130503c120f03,0x2130b04c2a130104,0x70285c64131884c3,0x106824170885c0c1,0x68321a0b0681c1a0,0x141b0486c641a150,0x1d02874241b0886c,0x50780c1e0887412])
def zsT : Nat := (cB [0xfffff38f1ff3cfff,0xe73c7fff3f81ffff,0xc7fffffffffffc73,0x7f0007cf9cf8ccc,0xfe0ff0f0f801e03c,0xfffe003ff8000f80,0xfff000fff00,0xfff00000ffffffc0,0xfff])
def zsV : Nat := (cB [0xa955538d1ad3c555,0xe52c3aaa3a90ad55,0xc56f52aa56aaac72,0x67c03034694d8ccc,0xbe06d0f0480c630c,0x91b40433e0c0c580,0x83030adf000b6f00,0xd7b0000026599f00,0x601803040c0f6b])
def zbR : Nat := 0xeeeeeeeeeeeeeeee
abbrev zcg : Nat := gZ &&& zbR
abbrev zcx : List Nat := [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xe0e0e0e0e0e0e0e0,0xee00ee00ee00ee00,0xeeee0000eeee0000,0xeeeeeeee00000000]
def zvd : Nat × List Nat × Nat × Nat := (zbR,zcx,10,zcg)
def zcT : List (Nat × List Nat × Nat × Nat) := [ziV,zlH,zfx,zcV,zgC,zly,zcF,ziB]
def zkE : Option ({rows : List Nat // rows.length = 24}) := some ⟨[3,26,29,37,46,54,57,3,26,29,37,46,13,14,21,22,25,38,41,42,49,50,13,14],rfl⟩
def ztL := uW zcx [1538,263681,539161,799762,1061898,1329669]
def ztV (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 4 (bI j 2 (bI j 1 (cB [0x41d802c3c0358001,0xc021803f107e00ec,0x1002182430086010,0x248045108809]) (cB [0x127004c089219240,0x340064109ea938,0xc8039006e10d031a,0x39827204e401])) (bI j 3 (cB [0x3c00750ce809d00,0x4040808100f049e0,0xc14084810102020,0x428284050802]) (cB [0x847008e011c02188,0x444c8099012c1a38,0x8c051809d193a026,0x5180a3014602]))) (bI j 6 (bI j 5 (cB [0x5402a8014e0a8c4,0x405506a9055202a4,0xd005904ad155a02b,0x5ac0b501680a]) (cB [0x66b00d601ac03541,0x806e04dc01b80358,0x7c16f80de05bc037,0x7300e019c003])) (bI j 7 (cB [0x779aef01de03989,0x827e0cfc01f803f0,0x6c2822f040208040,0x8f011d063a04]) (cB [0x7930125064a04787,0x25a0c98])))) 15 (i % 16)
def zvt (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 9 (bI j 4 (bI j 2 (bI j 1 (cB [0x800240100400003f,0x7c2800e05001a0,0x270fc03e1c806c33,0xe6300cc4901588c0,0x3f021a7203f32406,0x84062b008c51]) (cB [0xc8c9e4918fc8c31b,0x19bd723338fc6571,0x20d24687a30cfebf,0x631189c5f31089c6,0xe631b9c4633198c5,0x1ccc863518fc])) (bI j 3 (cB [0x524ce5f496c9c92c,0x4a1ac493f9cd26f3,0x3fb7d8736730e166,0xaa73d11e6621bc4c,0x318a00400857de8,0x20c42029880]) (cB [0x518fc89319812627,0x49981a92c030c860,0x3f23587084a4fc0f,0x843d15057a2312c,0x8461c40892c010c4,0x10c40823d12]))) (bI j 6 (bI j 5 (cB [0x3bd108661c00c92c,0x31001663c02d2980,0x440398700324b204,0x9a4b01118c20cf,0x127a202462044e4a,0x54010091891]) (cB [0x80a42000f83001d,0x21a3004128406a1,0x21090c40088c5120,0xe5498cc293138506,0x2f49605c6430a8c7,0x4a527e1924cc])) (bI j 7 (cB [0x23d11a961f95ec38,0x49602c6204a1e8a9,0x40459e884bb0e017,0x80e98801c0210320,0x1f7a213cc3807925,0x6cc400d0c50]) (bI j 8 (cB [0xd0d011a61c13692c,0x31023804c06c6800,0x12489e8811b0e022,0xa110ca41618a04a0,0x1231023e34128866,0x2998701324b0]) (cB [0x6a5302b00e04ef44,0x31e05801c0b06801,0x2905c6281800482d,0x88f0d04a319a83c3,0x267a2062c3809925,0x8d00681a00a1]))))) (bI j 14 (bI j 11 (bI j 10 (cB [0xba4b134026568040,0x92856ef448dd8701,0x442d58701aa4b137,0x11a8cd03800806cf,0x3a49626c34cad468,0xf18701da528]) (cB [0xf4940bc7a207ac3f,0x4a50849481006481,0x2c105e8822c94044,0x823a4b0413180869,0x4a19828f250121e8,0x134c62261880])) (bI j 12 (cB [0x598814c92829ac4a,0x409663052de882,0x3714405627804c02,0xa028c50520219a20,0x2f18d04831904c62,0x11c64e1b8c6e]) (bI j 13 (cB [0x60cdcc719989832b,0x31028a3434f867e6,0x3faf0c671e189e0d,0x62aa4b4534966906,0x5a49f8b293715926,0x34d8702da50c]) (cB [0xdb10cda61f9aac39,0x3120bcf45175e886,0x26098c4a03188050,0x82a30e20649644c6,0x586200ae328951e8,0x1718902c24c0])))) (bI j 16 (bI j 15 (cB [0x898982731280e620,0x7a24a8c388392591,0x250a0632040c52d4,0x47024f8604990743,0xd57a24aac3818529,0x24010af4942]) (cB [0x48c522900705200d,0x3250c863e18cc410,0x381952943024b264,0x16d3d126561f4c0c,0x6961f0cec3c56a4a,0x9a589533b120])) (bI j 17 (cB [0x430e15b9285b6f44,0x6814008571e883,0x490ec04b1900382a,0xc358c720f18a2760,0xbd19fc7a3331b063,0x990c64369882]) (bI j 18 (cB [0x2a4c8614965c863e,0x61c0de94c39527c3,0x4459589238b0fe56,0x8b0c941e57a4dacf,0x6e4a65aec3895d25,0xb401a058020]) (cB [0x824f6584960dc620,0x31a1e0c3db618703,0x3c0b801a06002072,0x3a2526594960de6,0x703241e8c49b6587])))))) 23 (i % 16)
def zpK (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 4 (bI j 2 (bI j 1 (cB [0x2004020040101f80,0x6310023100418a0,0x382310827a206496,0x21824a60b31f8231,0x4998261c0e496023]) (cB [0x13101218c1100481,0x1600415006814961,0x1900e9549616310,0x21193101a18a1a02,0x7a21949619310190])) (bI j 3 (cB [0x2310220149500f95,0x25009253101561c2,0x395310957a225496,0xa02c00e2b31f9531,0x49615321954a62b1]) (cB [0x14999561c3000930,0x3549635014340078,0xd8100838496347a2,0x1c3a4a53a4963a00,0xf819283a61fba6]))) (bI j 6 (bI j 5 (cB [0x34a4407a24119240,0x81928404a5404964,0x5817a24749647013,0x104a3104b1984a01,0x9cf31001318ca3]) (cB [0xf021cf015cf31250,0xcf496cf61c544964,0xbcf6205719457499,0x245c4a1cf49fcf49,0x310817a2cf7a24f6])) (bI j 7 (cB [0x3313814a56049960,0x814a56331f633106,0xf6761c6861e67315,0x8f6b18e6b31f8161,0x4a66b4a66e3106b1]) (cB [0x131a7261feb49ef0,0x4a4f43218])))) 20 (i % 16)
def zlC := pageLinks ztV zvt 6 13 7 7
def zki (i : Nat) : Nat × Nat :=
  let e := zpK i
  (e &&& 127,e >>> 7)
def zmt : Nat × Nat := (zuo,96)
def zrh := zr zbR 96 (zD zcx zsT zsV 96) 9 zki
def zgo := zw zbR zcx 9 zki
def zru : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm18,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,4,3,5] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,4,3,5] 0 i.val))),(pm15,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,5,3,4,2] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,5,3,4,2] 0 i.val))),(pm23,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,5,4,3,2] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,5,4,3,2] 0 i.val))),(pm14,(fun i : Fin 64 => Fin.ofNat 64 (pA [1,0,3,2,5,4] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [1,0,3,2,5,4] 0 i.val))),(pm24,(fun i : Fin 64 => Fin.ofNat 64 (pA [1,0,4,2,5,3] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [1,0,3,5,2,4] 0 i.val))),(pm25,(fun i : Fin 64 => Fin.ofNat 64 (pA [1,0,3,5,2,4] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [1,0,4,2,5,3] 0 i.val)))]
def zdw := zaa zru
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zsS : dM zbR zcg 64 zdw := zah (by decide +kernel)
def zkt (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 4 (bI j 2 (bI j 1 (cB [0x410007f33d00,0x1800110000080000]) (cB [0x73d0000373d,0x404])) (bI j 3 (cB [0x100001400,0x1100000000000100]) (cB [0x4cfc100000,0x750000008100ff00]))) (bI j 6 (bI j 5 (cB [0x1f800000750075,0x40000000353500]) (cB [0x50000000,0xff00c00040000000])) (bI j 7 (cB [0x505f908300ff4000,0x4a000440caff0000]) 0xff000000))) 8 (i % 16)
def zbC := zc zbR zcg zkE (fun i => zt zcg (cutPick zcT (zkt i))) 117 zgo zdw zlC zmt zrh
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zqU : zd zbR zcg zkE (zt zcg zcT) ztL (zz 117 zgo zdw zlC 0) zcx 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zos : tB 0 24 zbC = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zro : tB 24 24 zbC = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zsd : tB 48 24 zbC = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zoU : tB 72 24 zbC = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem znG : tB 96 21 zbC = true := by decide +kernel
theorem zuU : tB 0 48 zbC = true := tM (start := 0) (left := 24) (right := 24) (check := zbC) zos zro
theorem zrR : tB 72 45 zbC = true := tM (start := 72) (left := 24) (right := 21) (check := zbC) zoU znG
theorem znt : tB 48 69 zbC = true := tM (start := 48) (left := 24) (right := 45) (check := zbC) zsd zrR
theorem zqV : tB 0 117 zbC = true := tM (start := 0) (left := 48) (right := 69) (check := zbC) zuU znt
theorem zuj : tB 0 117 zbC = true := zqV
theorem zml : Known zcT := (eK (eK (eK (eK (eK (eK (eK (eK (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) zkX) zcG) zix) zcd) zdc) zeW) zgl) zfZ)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zqf : Lower zbR zcx zcg 10 := by
  apply lowerDag zkt _ _ _ _ zsS _ _ _ zml _ zqU zuj
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold pW; decide +kernel
  · exact cK (by decide +kernel)
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [zcT,List.mem_cons,List.not_mem_nil,or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def zes : Nat := 0xc3c30000c3c30000
abbrev zgI : Nat := gZ &&& zes
abbrev zhi : List Nat := [0x8282000082820000,0xc0c00000c0c00000,0xc3000000c3000000,0xc3c3000000000000]
def zsG : Nat × List Nat × Nat × Nat := (zes,zhi,6,zgI)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem znI : Lower zes zhi zgI 6 := zp (width := 64) pm18 zbJ (by decide +kernel)
def pm47 : List (List (Nat × Nat) × List (Nat × Nat)) := [st34,st35]
def zeZ : Nat := 0xc3c3c3c300000000
abbrev zhR : Nat := gZ &&& zeZ
abbrev zht : List Nat := [0x8282828200000000,0xc0c0c0c000000000,0xc300c30000000000,0xc3c3000000000000]
def zlb : Nat × List Nat × Nat × Nat := (zeZ,zht,6,zhR)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zji : Lower zeZ zht zhR 6 := zp (width := 64) pm47 zbJ (by decide +kernel)
def zgN : Nat := 0x2211221122112211
abbrev ztH : Nat := gZ &&& zgN
abbrev zkv : List Nat := [0x2200220022002200,0x2010201020102010,0x2211000022110000,0x2211221100000000]
def zxj := uW zkv [14868,277017,539149,809485]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zow : Lower zgN zkv ztH 5 := by
  apply eL (witnesses := zxj) (cut := zct)
  · unfold pW; decide +kernel
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold pW; decide +kernel
  · exact uC (old := zcA) (by decide +kernel)
  · exact zcM
  · decide +kernel
def zfT : Nat := 0x4141414141414141
abbrev zlj : Nat := gZ &&& zfT
abbrev zlo : List Nat := [0x4040404040404040,0x4100410041004100,0x4141000041410000,0x4141414100000000]
def znL : Nat × List Nat × Nat × Nat := (zfT,zlo,5,zlj)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zrc : Lower zfT zlo zlj 5 := zp (width := 64) pm19 zow (by decide +kernel)
def zpl : Nat := (cB [0x782c170703c0c07,0x81c2e1309c2c1e07,0x239130d82c36130b,0x71c0e46239148e43,0x301c2c070701c020,0x5c0c170483c0c0f1,0x1c1f0c0780c1e088,0x270309c321f0b07c,0x70bc502e030b842,0xd80c36148bc4c2f,0x46237130dc2c3718,0x2390c0e42239048e,0xe070f86039140e44,0x1c703e130f82c3,0x3c42070881c12070,0x320f0b03c100f008,0x170085c520f1303c,0x1305c32170805c1c,0x878201e040786217,0xc0c1f1c0784c1e0c,0x2270c07c221f0487,0x71009c2c270709c0,0xb0b8102e1889c522,0xbc702e148b8402e0,0x502f108bc122f030,0x36100d82036070d8,0x88dc0c371c0d862])
def zoY : Nat := (cB [0xfffe1ff39f3ffc27,0xffffc3ffc1e0ffc1,0xffffffffffffe07f,0x7e1ff83e7cc3cda,0x7f03f1c01ff03fe,0xfe0003fff801fffc,0x1fffff8003fe0,0xfffffc00])
def zvO : Nat := (cB [0x4d3c05c214285c00,0xab5783ff90c8c589,0x422218509280e035,0x55452a82c588ac4a,0x6a1351423594aaa,0xb412932d61895358,0x86119c6b50023aa0,0x399ce031])
def zbT : Nat := 0xc3c3c3c3c3c3c3c3
abbrev zck : Nat := gZ &&& zbT
abbrev zcp : List Nat := [0x8282828282828282,0xc0c0c0c0c0c0c0c0,0xc300c300c300c300,0xc3c30000c3c30000,0xc3c3c3c300000000]
def zoo : Nat × List Nat × Nat × Nat := (zbT,zcp,9,zck)
def zcZ : List (Nat × List Nat × Nat × Nat) := [zil,zsG,zlb,znL,zcF,ziq]
def zkH : Option ({rows : List Nat // rows.length = 24}) := some ⟨[7,30,46,54,57,7,30,46,54,57,7,30,14,22,25,38,41,49,56,14,22,25,38,41],rfl⟩
def zwo := uW zcp [3590,265729,539670,801806,1072142]
def zqs (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 2 (bI j 1 (cB [0x40340026d032001,0xc64c04c046346046,0x6005e15835805804]) (cB [0x2780780780723609,0x38278208207c378,0xa20a209669609609])) (bI j 3 (cB [0xb80b61b60b60a2a,0x80d80d23b8db80b8,0xf01f00f00f00d8cd]) 0xf20)) 12 (i % 16)
def zqh (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 4 (bI j 2 (bI j 1 (cB [0x120090080200001f,0xa806c1e01306003c,0x3146a80cd2a0270,0x8c9c3e31b0e0c543,0x627131881be3334f,0x3518cc54]) (cB [0xccc389524cd4c92c,0x100cd0402701006d,0xa327028c6c063146,0x189c0c620628ccd0,0x9334324b09063304,0x6330e210])) (bI j 3 (cB [0x88c384224b008620,0x3b0e00e92c021881,0x403e4500c8140262,0xbd1116c3805a4b19,0xf4446b0e01a92c65,0x700419a]) (cB [0x2063009989820624,0x998f9a063c4998c9,0x8f444a30e02892c6,0x30e02492c089881a,0xc386924f12493029,0xbb0fc2c]))) (bI j 6 (bI j 5 (cB [0x32620018c50acf44,0xca4b0b66330d989c,0x86206cb0e2369334,0x9898b4c380d24b00,0x92c6e98f93a6320e,0x4f30e03c]) (cB [0x40011028021bcf44,0x10cf844332108c50,0x893e1224c83a6203,0x8040caf4412b0e0c,0x31b058c540c31411,0xa0c7c1a])) (bI j 7 (cB [0x326206b0ccd2c327,0x298cd4a6270f1884,0xec3814a4cc4e92c7,0x30e03492c039880c,0x3f1580741000814,0xd8c51ae]) (cB [0x48331120c9444319,0x724f85a63e161881,0xec3c74bd115cc3e1,0x5])))) 22 (i % 16)
def zrF (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 1 (cB [0x401b080100807c0,0x200863611880418a,0x80120989c24960e6,0x86803c1496140262,0x9820103925]) (bI j 2 (cB [0x2092c44c40898910,0x38580360a4b10313,0x8c40c8c50161facc,0xce8c541313b292c6,0x18d8292c74c4]) (cB [0x4633280629000460,0x2005871024ca0008,0x52673b0e284964e6,0xd59882b00ed66270,0x61e5e93eacc7]))) 19 (i % 16)
def zit := pageLinks zqs zqh 5 13 6 6
def ziT (i : Nat) : Nat × Nat :=
  let e := zrF i
  (e &&& 63,e >>> 6)
def zwI : Nat × Nat := (zpl,96)
def zvG := zr zbT 96 (zD zcp zoY zvO 96) 8 ziT
def zlL := zw zbT zcp 8 ziT
def zrn : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm4,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,3,5,4] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,3,5,4] 0 i.val))),(pm18,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,4,3,5] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,4,3,5] 0 i.val))),(pm47,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,5,3,4] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,4,5,3] 0 i.val))),(pm42,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,4,5,3] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,5,3,4] 0 i.val)))]
def zfe := zaa zrn
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zpT : dM zbT zck 64 zfe := zah (by decide +kernel)
def zke (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 1 (cB [0xbc1001000040bc7,0xfc01bf00]) (bI j 2 (cB [0x77000fc1000030,0xbc003f04]) (cB [0xf080047002004010,0xc600101]))) 6 (i % 16)
def zcz := zc zbT zck zkH (fun i => zt zck (cutPick zcZ (zke i))) 48 zlL zfe zit zwI zvG
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zsD : zd zbT zck zkH (zt zck zcZ) zwo (zz 48 zlL zfe zit 0) zcp 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zvT : tB 0 24 zcz = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zoE : tB 24 24 zcz = true := by decide +kernel
theorem zox : tB 0 48 zcz = true := tM (start := 0) (left := 24) (right := 24) (check := zcz) zvT zoE
theorem zxg : tB 0 48 zcz = true := zox
theorem ztn : Known zcZ := (eK (eK (eK (eK (eK (eK (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) zlJ) zcG) zrc) zji) znI) zbJ)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zcD : Lower zbT zcp zck 9 := by
  apply lowerDag zke _ _ _ _ zpT _ _ _ ztn _ zsD zxg
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold pW; decide +kernel
  · exact cK (by decide +kernel)
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [zcZ,List.mem_cons,List.not_mem_nil,or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def zft : Nat := 0xaa55aa55aa55aa55
abbrev zjo : Nat := gZ &&& zft
abbrev zgP : List Nat := [0xaa00aa00aa00aa00,0x8844884488448844,0xa050a050a050a050,0xaa550000aa550000,0xaa55aa5500000000]
def zvx : Nat × List Nat × Nat × Nat := (zft,zgP,9,zjo)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zwi : Lower zft zgP zjo 9 := zp (width := 64) pm19 zcD (by decide +kernel)
def zeR : Nat := 0xaaaa5555aaaa5555
abbrev ziw : Nat := gZ &&& zeR
abbrev zgv : List Nat := [0xaaaa0000aaaa0000,0x8888444488884444,0xa0a05050a0a05050,0xaa005500aa005500,0xaaaa555500000000]
def zqA : Nat × List Nat × Nat × Nat := (zeR,zgv,9,ziw)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zus : Lower zeR zgv ziw 9 := zp (width := 64) pm38 zcD (by decide +kernel)
def zeF : Nat := 0xcccccccc33333333
abbrev zhp : Nat := gZ &&& zeF
abbrev zlu : List Nat := [0x8888888822222222,0xcccccccc00000000,0xc0c0c0c030303030,0xcc00cc0033003300,0xcccc000033330000]
def zrO : Nat × List Nat × Nat × Nat := (zeF,zlu,9,zhp)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zpD : Lower zeF zlu zhp 9 := zp (width := 64) pm39 zcD (by decide +kernel)
def zec : Nat := 0xffff0000ffff
abbrev zjq : Nat := gZ &&& zec
abbrev zlm : List Nat := [0xaaaa0000aaaa,0xcccc0000cccc,0xf0f00000f0f0,0xff000000ff00,0xffff00000000]
def zlT : Nat × List Nat × Nat × Nat := (zec,zlm,6,zjq)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zkA : Lower zec zlm zjq 6 := zp (width := 64) pm14 zcw (by decide +kernel)
def zur : Nat := (cB [0x1c0a070100c0203,0x4321d0c86c301a03,0xa030000c381e0e07,0x70101c02070300c0,0xe068321a01068080,0x78301d02874301b0,0x381f0c87c301e030,0x1a0001c32030200c,0x106c021b0306800,0x78081d00874381b,0xc0a1f0c878081e01,0x2070c00c301f0307,0xb02068021a0e01c3,0x740c1b0286c001,0x7c0a1e000780c1d0,0x38030207c041f008,0x1d0206c0a1a0c01c,0x1f0087804])
def zrS : Nat := (cB [0xdbe7cfc7cf9c7eef,0x37fcfffcfff3ff9f,0x1cbf837f827e1c73,0xf9ffe3ffe3ff03e])
def zrJ : Nat := (cB [0x2430946244891465,0x822804450105405,0x3656a3548ca9363,0x6001e420bae03e])
def zbU : Nat := 0xff0000ff
abbrev zbY : Nat := gZ &&& zbU
abbrev zco : List Nat := [0xaa0000aa,0xcc0000cc,0xf00000f0,0xff000000]
def zpW : Nat × List Nat × Nat × Nat := (zbU,zco,5,zbY)
def zcC : List (Nat × List Nat × Nat × Nat) := []
def zll : Option ({rows : List Nat // rows.length = 24}) := some ⟨[3,26,29,3,26,29,3,26,29,3,26,29,5,6,25,28,5,6,25,28,5,6,25,28],rfl⟩
def zrU := uW zco [1538,263681,539161,799746]
def zqj (i : Nat) : Nat := uP 0x9 2 i
def zwe (i : Nat) : Nat := uP 0xf 15 i
def zmU (i : Nat) : Nat := uP 0x1e 14 i
def zgr := pageLinks zqj zwe 1 13 1 2
def zja (i : Nat) : Nat × Nat :=
  let e := zmU i
  (e &&& 1,e >>> 1)
def ztG : Nat × Nat := (zur,63)
def zno := zr zbU 63 (zD zco zrS zrJ 63) 4 zja
def zjx := zw zbU zco 4 zja
def zrm : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def zfg := zaa zrm
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zwQ : dM zbU zbY 64 zfg := zah (by decide +kernel)
def zhz (i : Nat) : Nat :=
  let j := i / 16
  uP 0x0 1 (i % 16)
def zls := zc zbU zbY zll (fun i => zt zbY (cutPick zcC (zhz i))) 1 zjx zfg zgr ztG zno
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zrg : zd zbU zbY zll (zt zbY zcC) zrU (zz 1 zjx zfg zgr 0) zco 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zxo : tB 0 1 zls = true := by decide +kernel
theorem znM : tB 0 1 zls = true := zxo
theorem zsW : Known zcC := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zqP : Lower zbU zco zbY 5 := by
  apply lowerDag zhz _ _ _ _ zwQ _ _ _ zsW _ zrg znM
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold pW; decide +kernel
  · exact cK (by decide +kernel)
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [zcC,List.mem_cons,List.not_mem_nil,or_false]
    intro b h
    exact False.elim h
def pm48 : List (List (Nat × Nat) × List (Nat × Nat)) := [st23,st45]
def zeB : Nat := 0xff000000ff00
abbrev zjQ : Nat := gZ &&& zeB
abbrev zim : List Nat := [0xaa000000aa00,0xcc000000cc00,0xf0000000f000,0xff0000000000]
def ziH : Nat × List Nat × Nat × Nat := (zeB,zim,5,zjQ)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ziC : Lower zeB zim zjQ 5 := zp (width := 64) pm48 zbE (by decide +kernel)
def zdX : Nat := 0xffff00000000
abbrev zhK : Nat := gZ &&& zdX
abbrev zma : List Nat := [0xaaaa00000000,0xcccc00000000,0xf0f000000000,0xff0000000000]
def ziL : Nat × List Nat × Nat × Nat := (zdX,zma,5,zhK)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zjc : Lower zdX zma zhK 5 := zp (width := 64) pm25 zbI (by decide +kernel)
def znZ : Nat := (cB [0x1c0a070100c0203,0xc1a0f0502c120b03,0xa170904c22130703,0xa09068141a0b05c2,0xa8741a1d0c86c301,0x781c1e0e074321d0,0x44231088c381e0b0,0x2712094422502894,0x68b4542b148ac4c,0xb81c2e160b4522d,0xc0003160b8542e13,0x4030480c0c030280,0x31080c24030880c1,0x201c04070081c440,0x1c2a070701c1a070,0x40b0082c4c070b0,0xb0702c1a0b0402c,0x283c540b1482c32,0x3c140f0483c0c0f,0xc20130104c021306,0xa170c84c2c130a84,0x70905c22170305c0,0x7068101a01068281,0x68321a0b068201a0,0x141b0486c541a0e0,0x1d0c06c241b0886c,0x8874181d048740a])
def zsa : Nat := (cB [0xffffffc3ff8f8fff,0x71f0ffffff807fff,0xffffffffffffffc,0x807f803f9e7f0ccc,0xe07ff0f0f0007c0f,0xffff800fff80003f,0x7fff00,0xff800000fffffff0,0x3f])
def zrk : Nat := (cB [0xb494aa81a6878555,0x51303aaab2901692,0x54aa9254969551c,0x8c7e01ae9a7b0ccc,0xe05dd0f0502a4d89,0x69f3020e7e0c0637,0x10301800006eef00,0x7d8000008e3c73c0,0x4000006040603b])
def zbW : Nat := 0xffffffffffff
abbrev zbZ : Nat := gZ &&& zbW
abbrev zcv : List Nat := [0xaaaaaaaaaaaa,0xcccccccccccc,0xf0f0f0f0f0f0,0xff00ff00ff00,0xffff0000,0xffff00000000]
def znr : Nat × List Nat × Nat × Nat := (zbW,zcv,9,zbZ)
def zcB : List (Nat × List Nat × Nat × Nat) := [zfp,zlT,zdJ,zpW,zdm,zfX,zdG,ziH,ziL]
def zlX : Option ({rows : List Nat // rows.length = 24}) := some ⟨[3,26,29,37,46,3,26,29,37,46,3,26,13,14,21,22,25,28,38,41,42,44,13,14],rfl⟩
def zwz := uW zcv [1538,263681,539161,799762,1061898,1329669]
def zsK (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 2 (bI j 1 (cB [0x3a03a0289033001,0xc03a13a03a03a03a,0x3e03e03e03e03c13]) (cB [0x4404214204203e2,0x6056056056044944,0x5a05815805615605])) (bI j 3 (cB [0x35c05a15a05a05a0,0xe36836236206205c,0x8438407e37837426]) 0x9029008a3)) 12 (i % 16)
def znP (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 2 (bI j 1 (cB [0xf1a009020080003f,0x272401b1e0131c00,0x31b403152a314280,0xc627486204432742,0x529315092c4e63d4]) (cB [0x45cc4256c4154c38,0x3d066200431462f4,0xc380c9310a92c086,0x8f4414c4210c410e,0x206241693c1263c1])) (bI j 3 (cB [0x43142694822630,0x313092c2e63d2c62,0xc4236c4134c38329,0xc93c3863c3ef443a,0x2c6200631446c3c3]) (bI j 4 (cB [0x426025080084a92c,0x2c306200a3142e31,0x631326200c3144a9,0x8343140e00846,0x120085863c363141]) (cB [0x4140085a62038314,0x14160085e93c3a31,0x620183146092c3c3,0x3e])))) 20 (i % 16)
def zuA (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 2 (bI j 1 (cB [0x431408010080fc0,0x3109258118f42310,0x8c784b104261c049,0x20bd10249e16c420,0x98200f0401]) (cB [0x2601b04c60818910,0x20586280809c14a4,0x9262b24b1631eac6,0x4b18f1c620acc385,0x7a22c93c7988])) (bI j 3 (cB [0x463270463608c541,0x270525929880161e,0x52620a4b0131e826,0x1698f2c62082c380,0x49e5ec4204c4]) 0x1e880a4b30)) 19 (i % 16)
def zme := pageLinks zsK znP 5 13 6 6
def zgA (i : Nat) : Nat × Nat :=
  let e := zuA i
  (e &&& 63,e >>> 6)
def ztE : Nat × Nat := (znZ,96)
def zqW := zr zbW 96 (zD zcv zsa zrk 96) 8 zgA
def zju := zw zbW zcv 8 zgA
def zoy : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def zdx := zaa zoy
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem znW : dM zbW zbZ 64 zdx := zah (by decide +kernel)
def zjs (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 2 (bI j 1 (cB [0x337,0x0,0x1cd]) 0x200000000000) (bI j 3 (cB [0x9400045000000000,0x40082713a4a6911b,0x28d]) 0x6a00)) 9 (i % 16)
def zbO := zc zbW zbZ zlX (fun i => zt zbZ (cutPick zcB (zjs i))) 50 zju zdx zme ztE zqW
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zxs : zd zbW zbZ zlX (zt zbZ zcB) zwz (zz 50 zju zdx zme 0) zcv 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem znh : tB 0 24 zbO = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zwC : tB 24 24 zbO = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zse : tB 48 2 zbO = true := by decide +kernel
theorem zxH : tB 24 26 zbO = true := tM (start := 24) (left := 24) (right := 2) (check := zbO) zwC zse
theorem zsv : tB 0 50 zbO = true := tM (start := 0) (left := 24) (right := 26) (check := zbO) znh zxH
theorem zmV : tB 0 50 zbO = true := zsv
theorem zqv : Known zcB := (eK (eK (eK (eK (eK (eK (eK (eK (eK (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) zjc) ziC) zeH) zdQ) zbI) zqP) zbE) zkA) zcw)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zcJ : Lower zbW zcv zbZ 9 := by
  apply lowerDag zjs _ _ _ _ znW _ _ _ zqv _ zxs zmV
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold pW; decide +kernel
  · exact cK (by decide +kernel)
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [zcB,List.mem_cons,List.not_mem_nil,or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def zdL : Nat := 0xff00ffffffffff
abbrev zjg : Nat := gZ &&& zdL
abbrev zgW : List Nat := [0xaa00aaaaaaaaaa,0xcc00cccccccccc,0xf000f0f0f0f0f0,0xff00ff00,0xff0000ffff0000,0xff00ff00000000]
def zwc : Nat × List Nat × Nat × Nat := (zdL,zgW,9,zjg)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zws : Lower zdL zgW zjg 9 := zp (width := 64) pm18 zcJ (by decide +kernel)
def zaj : Nat := 0xf0fffff0f0fffff
abbrev zaf : Nat := gZ &&& zaj
abbrev zan : List Nat := [0xa0aaaaa0a0aaaaa,0xc0ccccc0c0ccccc,0xf0f00000f0f0,0xf00ff000f00ff00,0xf0f00000f0f0000,0xf0fffff00000000]
def zas : Nat × List Nat × Nat × Nat := (zaj,zan,9,zaf)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zac : Lower zaj zan zaf 9 := zp (width := 64) pm15 zcJ (by decide +kernel)
def zaQ : Nat := 0xfff0fff0fff0fff
abbrev zaA : Nat := gZ &&& zaQ
abbrev zX : List Nat := [0xaaa0aaa0aaa0aaa,0xccc0ccc0ccc0ccc,0xf000f000f000f0,0xf000f000f000f00,0xfff00000fff0000,0xfff0fff00000000]
def zau : Nat × List Nat × Nat × Nat := (zaQ,zX,9,zaA)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zbl : Lower zaQ zX zaA 9 := zp (width := 64) pm23 zcJ (by decide +kernel)
def zR : Nat := 0x33333333ffffffff
abbrev zbq : Nat := gZ &&& zR
abbrev zaR : List Nat := [0x22222222aaaaaaaa,0xcccccccc,0x30303030f0f0f0f0,0x33003300ff00ff00,0x33330000ffff0000,0x3333333300000000]
def zO : Nat × List Nat × Nat × Nat := (zR,zaR,9,zbq)
def zaO := uW zaR [1538,263681,539161,799762,1061898,1329669]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zH : Lower zR zaR zbq 9 := by
  apply eL (witnesses := zaO) (cut := zbH)
  · unfold pW; decide +kernel
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold pW; decide +kernel
  · exact uC (old := zbL) (by decide +kernel)
  · exact zbP
  · decide +kernel
def zS : Nat := 0x3f3f3f3f3f3f3f3f
abbrev zae : Nat := gZ &&& zS
abbrev zaI : List Nat := [0x2a2a2a2a2a2a2a2a,0xc0c0c0c0c0c0c0c,0x3030303030303030,0x3f003f003f003f00,0x3f3f00003f3f0000,0x3f3f3f3f00000000]
def zbm : Nat × List Nat × Nat × Nat := (zS,zaI,9,zae)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zai : Lower zS zaI zae 9 := zp (width := 64) pm15 zH (by decide +kernel)
def zaD : Nat := 0x5555ffff5555ffff
abbrev zK : Nat := gZ &&& zaD
abbrev zhH : List Nat := [0xaaaa0000aaaa,0x4444cccc4444cccc,0x5050f0f05050f0f0,0x5500ff005500ff00,0x5555000055550000,0x5555ffff00000000]
def zar : Nat × List Nat × Nat × Nat := (zaD,zhH,9,zK)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zcf : Lower zaD zhH zK 9 := zp (width := 64) pm14 zH (by decide +kernel)
def zfz : Nat := 0x55ff55ff55ff55ff
abbrev zmd : Nat := gZ &&& zfz
abbrev ziu : List Nat := [0xaa00aa00aa00aa,0x44cc44cc44cc44cc,0x50f050f050f050f0,0x5500550055005500,0x55ff000055ff0000,0x55ff55ff00000000]
def zph : Nat × List Nat × Nat × Nat := (zfz,ziu,9,zmd)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zng : Lower zfz ziu zmd 9 := zp (width := 64) pm24 zH (by decide +kernel)
def zfJ : Nat := 0xbbbbbbbbbbbbbbbb
abbrev zjI : Nat := gZ &&& zfJ
abbrev zfB : List Nat := [0xaaaaaaaaaaaaaaaa,0x8888888888888888,0xb0b0b0b0b0b0b0b0,0xbb00bb00bb00bb00,0xbbbb0000bbbb0000,0xbbbbbbbb00000000]
def zrE : Nat × List Nat × Nat × Nat := (zfJ,zfB,9,zjI)
def zpI := uW zfB [14876,263681,539161,801301,1063437,1329669]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zjm : Lower zfJ zfB zjI 9 := by
  apply eL (witnesses := zpI) (cut := zbH)
  · unfold pW; decide +kernel
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold pW; decide +kernel
  · exact uC (old := zbL) (by decide +kernel)
  · exact zbP
  · decide +kernel
def zdt : Nat := 0xdddddddddddddddd
abbrev zko : Nat := gZ &&& zdt
abbrev zgD : List Nat := [0x8888888888888888,0xcccccccccccccccc,0xd0d0d0d0d0d0d0d0,0xdd00dd00dd00dd00,0xdddd0000dddd0000,0xdddddddd00000000]
def zwr : Nat × List Nat × Nat × Nat := (zdt,zgD,9,zko)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zgy : Lower zdt zgD zko 9 := zp (width := 64) pm14 zjm (by decide +kernel)
def zeC : Nat := 0xf00ff00ff00ff00f
abbrev zjJ : Nat := gZ &&& zeC
abbrev zdU : List Nat := [0xa00aa00aa00aa00a,0xc00cc00cc00cc00c,0xf000f000f000f000,0xf00f0000f00f0000,0xf00ff00f00000000]
def zpE : Nat × List Nat × Nat × Nat := (zeC,zdU,8,zjJ)
def zuc := uW zdU [1538,263681,539153,801293,1071629]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zoW : Lower zeC zdU zjJ 8 := by
  apply eL (witnesses := zuc) (cut := zbK)
  · unfold pW; decide +kernel
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold pW; decide +kernel
  · exact uC (old := zcm) (by decide +kernel)
  · exact zcu
  · decide +kernel
def zdW : Nat := 0xf0f0f0f00f0f0f0f
abbrev zhy : Nat := gZ &&& zdW
abbrev zer : List Nat := [0xa0a0a0a00a0a0a0a,0xc0c0c0c00c0c0c0c,0xf0f0f0f000000000,0xf000f0000f000f00,0xf0f000000f0f0000]
def zry : Nat × List Nat × Nat × Nat := (zdW,zer,8,zhy)
def zwF := uW zer [1538,263681,543233,799762,1061898]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ziF : Lower zdW zer zhy 8 := by
  apply eL (witnesses := zwF) (cut := zcP)
  · unfold pW; decide +kernel
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold pW; decide +kernel
  · exact uC (old := zfV) (by decide +kernel)
  · exact zfO
  · decide +kernel
def zdn : Nat := 0xff0000ffff0000ff
abbrev zlh : Nat := gZ &&& zdn
abbrev zgE : List Nat := [0xaa0000aaaa0000aa,0xcc0000cccc0000cc,0xf00000f0f00000f0,0xff000000ff000000,0xff0000ff00000000]
def zwM : Nat × List Nat × Nat × Nat := (zdn,zgE,8,zlh)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zsB : Lower zdn zgE zlh 8 := zp (width := 64) pm14 ziF (by decide +kernel)
def pm49 : List (List (Nat × Nat) × List (Nat × Nat)) := [st24,st23,st35]
def zfL : Nat := 0xff00ff0000000000
abbrev zkO : Nat := gZ &&& zfL
abbrev zgF : List Nat := [0xaa00aa0000000000,0xcc00cc0000000000,0xf000f00000000000,0xff00000000000000]
def ztm : Nat × List Nat × Nat × Nat := (zfL,zgF,7,zkO)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zuB : Lower zfL zgF zkO 7 := zp (width := 64) pm49 zcu (by decide +kernel)
def pm50 : List (List (Nat × Nat) × List (Nat × Nat)) := [st24,st35]
def zff : Nat := 0xffff000000000000
abbrev ziI : Nat := gZ &&& zff
abbrev ziJ : List Nat := [0xaaaa000000000000,0xcccc000000000000,0xf0f0000000000000,0xff00000000000000]
def zsr : Nat × List Nat × Nat × Nat := (zff,ziJ,7,ziI)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zwb : Lower zff ziJ ziI 7 := zp (width := 64) pm50 zcu (by decide +kernel)
def pm51 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01,st24]
def zds : Nat := 0xaa005500aa005500
abbrev zhC : Nat := gZ &&& zds
abbrev zin : List Nat := [0xaa000000aa000000,0x8800440088004400,0xa0005000a0005000,0xaa00550000000000]
def zqF : Nat × List Nat × Nat × Nat := (zds,zin,6,zhC)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zvo : Lower zds zin zhC 6 := zp (width := 64) pm51 zbJ (by decide +kernel)
def pm52 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01,st24,st23]
def zgf : Nat := 0xaa550000aa550000
abbrev zkC : Nat := gZ &&& zgf
abbrev ziM : List Nat := [0xaa000000aa000000,0x8844000088440000,0xa0500000a0500000,0xaa55000000000000]
def zmR : Nat × List Nat × Nat × Nat := (zgf,ziM,6,zkC)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zvm : Lower zgf ziM zkC 6 := zp (width := 64) pm52 zbJ (by decide +kernel)
def zdZ : Nat := 0xcc00cc0033003300
abbrev zjA : Nat := gZ &&& zdZ
abbrev zhh : List Nat := [0x8800880022002200,0xcc00cc0000000000,0xc000c00030003000,0xcc00000033000000]
def zpN : Nat × List Nat × Nat × Nat := (zdZ,zhh,6,zjA)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zqM : Lower zdZ zhh zjA 6 := zp (width := 64) pm6 zbJ (by decide +kernel)
def zdT : Nat := 0xff00ff00ff00ff
abbrev zjF : Nat := gZ &&& zdT
abbrev zjR : List Nat := [0xaa00aa00aa00aa,0xcc00cc00cc00cc,0xf000f000f000f0,0xff000000ff0000,0xff00ff00000000]
def zrb : Nat × List Nat × Nat × Nat := (zdT,zjR,6,zjF)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zri : Lower zdT zjR zjF 6 := zp (width := 64) pm24 zcw (by decide +kernel)
def zfk : Nat := 0xf0f0f0f0f0f0f0f
abbrev zjz : Nat := gZ &&& zfk
abbrev zgx : List Nat := [0xa0a0a0a0a0a0a0a,0xc0c0c0c0c0c0c0c,0xf000f000f000f00,0xf0f00000f0f0000,0xf0f0f0f00000000]
def zmo : Nat × List Nat × Nat × Nat := (zfk,zgx,6,zjz)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zvV : Lower zfk zgx zjz 6 := zp (width := 64) pm15 zcw (by decide +kernel)
def pm53 : List (List (Nat × Nat) × List (Nat × Nat)) := [st23,st25,st24]
def zfl : Nat := 0xff000000ff0000
abbrev zhj : Nat := gZ &&& zfl
abbrev zhU : List Nat := [0xaa000000aa0000,0xcc000000cc0000,0xf0000000f00000,0xff000000000000]
def zqc : Nat × List Nat × Nat × Nat := (zfl,zhU,5,zhj)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem znX : Lower zfl zhU zhj 5 := zp (width := 64) pm53 zbE (by decide +kernel)
def zeo : Nat := 0xff00ff00000000
abbrev zmb : Nat := gZ &&& zeo
abbrev zkF : List Nat := [0xaa00aa00000000,0xcc00cc00000000,0xf000f000000000,0xff000000000000]
def zwl : Nat × List Nat × Nat × Nat := (zeo,zkF,5,zmb)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zvW : Lower zeo zkF zmb 5 := zp (width := 64) pm46 zbI (by decide +kernel)
def zfi : Nat := 0xf000f000f000f00
abbrev zkk : Nat := gZ &&& zfi
abbrev zjM : List Nat := [0xa000a000a000a00,0xc000c000c000c00,0xf0000000f000000,0xf000f0000000000]
def zrp : Nat × List Nat × Nat × Nat := (zfi,zjM,5,zkk)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zsA : Lower zfi zjM zkk 5 := zp (width := 64) pm15 zbI (by decide +kernel)
def zeV : Nat := 0xf0f00000f0f0000
abbrev ziN : Nat := gZ &&& zeV
abbrev zhs : List Nat := [0xa0a00000a0a0000,0xc0c00000c0c0000,0xf0000000f000000,0xf0f000000000000]
def zqG : Nat × List Nat × Nat × Nat := (zeV,zhs,5,ziN)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zwO : Lower zeV zhs ziN 5 := zp (width := 64) pm23 zbI (by decide +kernel)
def zeP : Nat := 0xf0f0f0f00000000
abbrev zjO : Nat := gZ &&& zeP
abbrev zgK : List Nat := [0xa0a0a0a00000000,0xc0c0c0c00000000,0xf000f0000000000,0xf0f000000000000]
def zpr : Nat × List Nat × Nat × Nat := (zeP,zgK,5,zjO)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zoR : Lower zeP zgK zjO 5 := zp (width := 64) pm15 zbE (by decide +kernel)
def pm54 : List (List (Nat × Nat) × List (Nat × Nat)) := [st15,st12]
def zfU : Nat := 0x3333333300000000
abbrev zkl : Nat := gZ &&& zfU
abbrev zhS : List Nat := [0x2222222200000000,0x3030303000000000,0x3300330000000000,0x3333000000000000]
def zrj : Nat × List Nat × Nat × Nat := (zfU,zhS,5,zkl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem znE : Lower zfU zhS zkl 5 := zp (width := 64) pm54 zbE (by decide +kernel)
def pm55 : List (List (Nat × Nat) × List (Nat × Nat)) := [st05,st01,st23,st14]
def zdz : Nat := 0x5500550055005500
abbrev zhJ : Nat := gZ &&& zdz
abbrev ziK : List Nat := [0x4400440044004400,0x5000500050005000,0x5500000055000000,0x5500550000000000]
def zoS : Nat × List Nat × Nat × Nat := (zdz,ziK,5,zhJ)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zxz : Lower zdz ziK zhJ 5 := zp (width := 64) pm55 zbE (by decide +kernel)
def pm56 : List (List (Nat × Nat) × List (Nat × Nat)) := [st05,st01,st23,st12,st24]
def zep : Nat := 0x5555000055550000
abbrev ziW : Nat := gZ &&& zep
abbrev zjl : List Nat := [0x4444000044440000,0x5050000050500000,0x5500000055000000,0x5555000000000000]
def zug : Nat × List Nat × Nat × Nat := (zep,zjl,5,ziW)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zoq : Lower zep zjl ziW 5 := zp (width := 64) pm56 zbE (by decide +kernel)
def st03 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xaa55aa55aa55aa55,0),(0xaa00aa00aa00aa,7)],[(0x5500550055005500,7)])
def pm57 : List (List (Nat × Nat) × List (Nat × Nat)) := [st02,st04,st03]
def zdI : Nat := 0xff000000ff000000
abbrev zlt : Nat := gZ &&& zdI
abbrev zkq : List Nat := [0xaa000000aa000000,0xcc000000cc000000,0xf0000000f0000000,0xff00000000000000]
def zql : Nat × List Nat × Nat × Nat := (zdI,zkq,5,zlt)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zwA : Lower zdI zkq zlt 5 := zp (width := 64) pm57 zcd (by decide +kernel)
def zmF : Nat := (cB [0x1c0a070100c0203,0xc1a0f0502c120b03,0xa170904c22130703,0xa09068141a0b05c2,0xa8741a1d0c86c301,0x781c1e0e074321d0,0x44231088c381e0b0,0x2712094422502894,0x68b4542b148ac4c,0xb81c2e160b4522d,0xc6233160b8542e13,0x835188d42a35190c,0x6190d84c360b0d86,0x88e452390c8e4683,0xe8643a150e870391,0x683c160f0383c1c0,0x30280c00031c0f0,0x880c14030480c0c,0x81c44031080c2403,0xc1a070201c040700,0xc070b01c2a070701,0xb0402c040b0082c4,0x482c320b0702c1a0,0x3c0c0f0283c540b1,0x2130603c140f048,0x130a84c20130104c,0x1904c62130c84c2c])
def zxf : Nat := (cB [0xfc0787c3ff8f8fff,0x71f0ffffffffffff,0xfffffffffc3878fc,0x3c07f3f9e7f0ccc,0xe07ff0f000f807f8,0xfff80003ff803f,0x3ffffc0007fff00,0xff800000ff000000,0x3ffffff])
def zoz : Nat := (cB [0xa8038341a6878555,0x51303aaa692b494a,0x925496955018389c,0x19c05d2e9a7b0ccc,0xe05dd0f01898c7e0,0x20e7e0c062ed8037,0x8376efc0006eef00,0x7d800000fc010301,0xc006040603bf76fb])
def zca : Nat := 0xffffffffffffffff
abbrev zcn : Nat := gZ &&& zca
abbrev zcK : List Nat := [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]
def zcX : List (Nat × List Nat × Nat × Nat) := [zxv,zsc,zuV,zuq,zuY,zud,ztU,zmZ,zxJ,zqH,zwE,zuO,zxd,zrM,zwm,zue,zof,zpR,zsw,zpP,zrB,ztd,zrT,znk,zrr,zrf,zoO,zrL,zvF,zpw,zvv,zxi,zpM,zmE,zmI,zub,zoc,zrH,zut,zmX,zra,zrx,zuT,zvd,zvx,zqA,zoo,zrO,znr,zwc,zas,zau,zO,zbm,zar,zph,zrE,zwr,zjb,zeG,zpE,zry,zwM,zjB,zjG,zkc,ziP,zcN,zdB,zhG,zgY,ztm,zsr,zlc,ziD,zqF,zmR,zhN,zil,zlb,zpN,zfp,zlT,zrb,zmo,ziV,zlH,zdJ,zdm,zfX,zdG,ziH,ziL,zjv,zqc,zwl,zrp,zqG,zpr,zfx,zku,zrj,zcV,zoS,zug,zgC,zly,zcF,ziB,zky,zql]
def zhq : Option ({rows : List Nat // rows.length = 24}) := some ⟨[3,26,29,37,46,54,57,60,3,26,29,37,13,14,21,22,25,28,38,41,42,44,49,50],rfl⟩
def zuy := uW zcK [1538,263681,539161,799762,1061898,1329669]
def zvy (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 78 (bI j 39 (bI j 19 (bI j 9 (bI j 4 (bI j 2 (bI j 1 (cB [0x840185c002b80001,0x3140062000c40017,0x900011820208a0,0x4101280024040480,0x268004c0409]) (cB [0x800500409a181340,0x5a080a2481440028,0xb808170002e000,0x238174402e8005d0,0x3400068000c])) (bI j 3 (cB [0x68000d0001a00,0x79000f0081a10034,0xfa001f4003c880,0xe081fc003e8407d0,0x4004080000f]) (cB [0x8808a2c110102086,0x990013200264004a,0x14e10288504c920,0x6002a42054800a90,0x56800ab0815]))) (bI j 6 (bI j 5 (cB [0xb20815a282b40,0xb40c168002d0005a,0x4172182dc205b800,0x61030c005e8c0bc0,0x6a0a0c53c18]) (cB [0xdc001b8003643,0xe0001c000370406e,0x41c4003802070000,0x6003985071860e20,0x76800eb081d])) (bI j 7 (cB [0xef041de003b42,0x1fa183c0d078,0x4200004000080001,0xa104140082801001,0x838a1070020]) (bI j 8 (cB [0x11600226184307,0x160422c00458008b,0x23600460308b821,0xa0046c208d8011b0,0x930611d2423]) (cB [0x1a1290c252004a40,0x3908272004e40096,0xc278104ec109d801,0xa5051400a28013e1,0xb11614f4c28]))))) (bI j 14 (bI j 11 (bI j 10 (cB [0x6170002e0005b43,0x73082e6005cc00b8,0x2ea105d400ba801,0xa005f400bb8c1770,0xbe8017d002f]) (cB [0x8018700306205f46,0x8b0830e2061c00c3,0x431e0063420c6801,0x20864010c80018f0,0xc91c1920032])) (bI j 12 (cB [0x801a118342006801,0xa70434e0069c00d3,0xc352006a010d4001,0xa486c050d8001a91,0xdf061be0036]) (bI j 13 (cB [0x841c100382007040,0xc5103861070c00e0,0x43960072c00e4841,0xa0873010e6001cb0,0xe9061ce1039]) (cB [0x801d60c3ac007541,0xdc143b60876420ec,0xc3c46078410f0801,0xa007d400fa801ee1,0xfa881f5003e])))) (bI j 16 (bI j 15 (cB [0x921fa143f2087e40,0x9004100882000ff,0x4414088280104822,0x60083071060020b0,0x110002133442]) (cB [0x8022300446008803,0x24004460888c0111,0x4454088a02112082,0x40890021200022b5,0x121942430048])) (bI j 17 (cB [0x2a24d2c49a009340,0x7a004ee189b4a12c,0x4f4089e8013d002,0x8a20813d9a27b0,0x148802910052]) (bI j 18 (cB [0x29a0053400a449,0xa00053430a68014d,0x56e20aa0f150102,0xa40af4015d842bb0,0x162842c50057]) (cB [0x42c70458e00b1c0,0xe3005c600b299164,0x5da00b8ca171802,0xc20bb49176802ed0,0x18b842fa745e])))))) (bI j 29 (bI j 24 (bI j 21 (bI j 20 (cB [0x803241463258c640,0x291065200ca40194,0x65a08cb40196803,0x410cbc31970232e0,0x19a003340066]) (cB [0x883410067e10cd0b,0x450068a00d1401a0,0x69008d1431a2803,0xa00d3011a4863490,0x1a70034d0469])) (bI j 22 (cB [0x364006c020d392,0x66046cc00d9021b2,0x46dc50d9c71b3803,0xa00df401be803781,0x1be8037d006f]) (bI j 23 (cB [0x8037d086fa00df40,0x9700700b8dfc11bf,0x72e20e5c01cb803,0x610e6c01cd8039b0,0x1d01a39d0c73]) (cB [0x83c40076490eb45,0xc80079000f2001e2,0x7b008f5431e41a3,0x400f6411ec803d90,0x1ef823da147b])))) (bI j 26 (bI j 25 (cB [0x923e0047c000f800,0xef007de00fa851f0,0x7de08fbc01f7803,0x200fc401f8023f00,0x1f9083f1047e]) (cB [0xe3fe307ec40fd80,0x160082c010445205,0x82c09058020b004,0x629060320b824170,0x210804200483])) (bI j 27 (cB [0x242400846090842,0x261884c010941212,0x858510b00216004,0x4010e8021d004361,0x21d0043a0087]) (bI j 28 (cB [0x243b0c876010e81,0x500089c110fcf21f,0x8a0391400228004,0x115c122b804570,0x22e82458148b]) (cB [0xc472288c6791785,0x870090621208123e,0x91aa921c6243804,0x8012900251044a20,0x255804a41c94]))))) (bI j 34 (bI j 31 (bI j 30 (cB [0x864ab00956012ac0,0xb900972012b8b255,0x972012e4025c804,0x6012ec025c844b90,0x260804bb1897]) (cB [0x4d410992593048,0xdb289b019360026c,0x4a00093d8a272a24,0xe014181283005011,0x2838250700a0])) (bI j 32 (cB [0x650d04a1a014205,0x1110a22014440287,0xa462945cc28a845,0x4014a80294045280,0x2950252a00a5]) (bI j 33 (cB [0x8653204a64014ac7,0x4008a70414d82299,0xa8a0150832a1005,0xe0153c02a6845452,0x2a98054f10a9]) (cB [0x256600aaa8954c2,0x6820ace0959c02b3,0xae2015c012b8005,0x4095c802b8825710,0x2b99857300ae])))) (bI j 36 (bI j 35 (cB [0x58304b06015fc4,0x8504b0a0161012c2,0xb0c3961802c3005,0x60166132c88e58d1,0x2d5825ab00b5]) (cB [0x805b604b6c016b0a,0xbf2cb70396dc12db,0xbda8174da2e5125,0xc017f412fe805fd0,0x2ff005fe00bf])) (bI j 37 (cB [0x61000c1a197f8f,0x1900c32018409308,0x4c3201864030c806,0x679868130d006190,0x3150462a00c3]) (bI j 38 (cB [0x8063100c58298b00,0x3100c62018c40318,0xcc6c198d803188a6,0x8019300326006394,0x3268064c04c9]) (cB [0x66400c9cb19341,0x6600cc8119900332,0x8cd4019a80333086,0x2419c403360a66a0,0x33ca267900ce]))))))) (bI j 58 (bI j 48 (bI j 43 (bI j 41 (bI j 40 (cB [0x68a08d1401a280,0x8c00d1801a300346,0x4d3601a6813461c6,0xa01a70134e0069b0,0x3508069d10d3]) (cB [0x386b210d4289a840,0xd500daa01b48335b,0xdac41b58036a826,0xc01ba063710c6de1,0x379006ee10dd])) (bI j 42 (cB [0x206fa00df401bc88,0x3444e2af9c28b37d,0xe9201d1443a2807,0xc01d2453a4807490,0x3a71e74e00e9]) (cB [0x8275e0cebc01d741,0x6204ec401d8803b0,0x8ec871d8c13b1807,0x201de403ba0a7720,0x3bdaa77908ef]))) (bI j 45 (bI j 44 (cB [0x479000f2001e400,0xa70cf2a91e4833c8,0x4f5409ea803d5007,0xa01f2833e4047ab7,0x3e8007cd0cf9]) (cB [0x827d108fa201f401,0xd954fae11f5033e9,0x8fdc01fb803f7007,0x60204c04060e7ee7,0x409828130102])) (bI j 46 (cB [0x8081425028020500,0x210504202074440e,0xd04c0a08c3411028,0xc020b80417008271,0x41d0c82e3105]) (bI j 47 (cB [0x84009080021000,0x49010843a1080421,0x1092021240424808,0x8021300424868490,0x4260484c0109]) (cB [0x808560d09c421380,0x5b290b212164042c,0x10ca021940432808,0x6021946432808650,0x4358e86b010d]))))) (bI j 53 (bI j 50 (bI j 49 (cB [0x8087f210fe021c8d,0x870110e0221c0443,0x111a0222c2443888,0xc0a23804468288d0,0x4480888f0511]) (cB [0x68980112e0a2503,0x9d051361226c044c,0x11460a28c044f0a8,0x2022c404560a8a42,0x458848b10116])) (bI j 51 (cB [0x8e8b40d1660a2cc0,0xbf0117c0a2f8045b,0x51800a300045f828,0xe4a3085461008c10,0x469008d00918]) (bI j 52 (cB [0x48d2111a4023480,0xe6091b26a360146b,0x11d63a3a42474028,0x60a3ec047d028f22,0x47e028fc011f]) (cB [0x68fe011fc023f41,0x45920412404147f,0x125e024a0748d1c9,0xe024bc04978092f0,0x49a8092f1925])))) (bI j 55 (bI j 54 (cB [0x89370d26a124d40,0x3e0927c024f8049d,0x12802250004a0009,0x3a51144a2009440,0x4af8095f012b]) (cB [0x8095f012be0257c0,0x67012be4257c04af,0x52ce0259c04b3809,0x25c004b8009672,0x4b800970012e])) (bI j 56 (cB [0x97a012e0525c00,0x7a1d2f4025e804bd,0x53022260404c0809,0x23261834c3009850,0x4cf0c98f3d31]) (bI j 57 (cB [0x9a401348026900,0xac013484269004d2,0xd358026b004d6009,0x6026cc04d9809ac1,0x4d9929b30136]) (cB [0x9bc01378026f00,0xbf013781a6f004de,0x93960270894df869,0x80277c54e89c9cb1,0x4f2069e4013c])))))) (bI j 68 (bI j 63 (bI j 60 (bI j 59 (cB [0x49ee313d22a79c2,0x20d3fe1a7f034fd,0x941492820250286a,0x202878350f00a1c0,0x51106a210544]) (cB [0x8aa292944a228940,0x4901492028e11519,0x149842930052486a,0x2960052c00a541,0x52d80a580d4b])) (bI j 61 (cB [0x88a662d4bc4296c3,0x75014ea029d40538,0x14ee2a9dc053a84a,0x8029f0053e00a7c0,0x53e08a7c014f]) (bI j 62 (cB [0x2a83155001aa000,0x8a155120aa240544,0x152802a5005478aa,0xa0aa50154a00a940,0x54d84a961552]) (cB [0xaa60154812a747,0xa71554e02a981553,0x156602ac425560aa,0x812ad0055982ab30,0x55b00ab60156])))) (bI j 65 (bI j 64 (cB [0x82aba0557012ad82,0xbf8d5781aaf0055d,0x55e412bc415711ea,0x62be4f57a88af40,0x58c00b141161]) (cB [0xcb180163002c600,0x1e0163c02c78058c,0x164402c78458f00b,0xc32c94159106b220,0x59700b2c0964])) (bI j 66 (cB [0xb310565c1acb80,0x33056640acc80599,0x56720acd0559a00b,0x20acfc259d88b3a0,0x5a5a4b422568]) (bI j 67 (cB [0xb72016d442d74d,0x73016e602dc815b9,0x16e802dd005b982b,0x2de005ba08b740,0x5bf00b78196f]) (cB [0x82b7e0d6fc02df80,0x8c0170a3ae0835c0,0x972042e4005c608b,0x812e6c15cd02b980,0x5cf88b9e0573]))))) (bI j 73 (bI j 70 (bI j 69 (cB [0x2ba40174802e8c1,0xb50976a02e9505d2,0x576e02edc05db80b,0x27aee875dc04bb70,0x5ed08bd02978]) (cB [0x88bdf017bc0af780,0xf6017e422f8cf5ef,0x17ec1afd805fb00b,0x40afe805fc82bf90,0x5fd84bfb017f])) (bI j 71 (cB [0x88c00257fa1aff40,0xe0181a0b0340604,0xd8308b038a60700c,0xe030c8561804c291,0x61c00c370586]) (bI j 72 (cB [0xc39158700b0e00,0x420987e1b0f8161f,0x189a03130162210c,0xa43134062680c4d0,0x62a82c550189]) (cB [0xc5c098ac331580,0x64018bc33178062f,0x18ca5b194063202c,0x60b1c0363800c700,0x63a00c74018e])))) (bI j 75 (bI j 74 (cB [0x2c82018ea6b1d01,0x8f1190c4b20c3641,0x1964032bc3649b8c,0xc032f8065d08cb22,0x65f06cbe0197]) (cB [0x2cc4419821b3040,0xd6019aa0b354066a,0x99ac03358066b00c,0x20b364066c02cd60,0x67100cda219b])) (bI j 76 (cB [0xce3159c40b3880,0xf7019ee033a0f674,0x99ee133dc067b80c,0xe133ecc67d80cf90,0x68c06d093da0]) (bI j 77 (cB [0xacd1b19a360346c0,0x7109a8d5b4dcf690,0x5ae8035cc16b980d,0xe335e466bc80d741,0x6c280d8501af]) (cB [0x8ad8729b0e036142,0x9601b2c0365806c8,0x1b50036a006cb24d,0x36a006d400da80,0x6d602da811b5])))))))) (bI j 117 (bI j 97 (bI j 87 (bI j 82 (bI j 80 (bI j 79 (cB [0xdb609b5a4b6b40,0xc009b80036e086dc,0x1bb41370986e100d,0xc0377806ee04ddc0,0x6f0b4dde0dbb]) (cB [0xae0401c060b7ec8,0xa01c120b8240702,0xdc160382c070502e,0x81b838670700e0b0,0x70b80e1701c2])) (bI j 81 (cB [0x2e1c01c341385c3,0x4105c647b875570e,0x1c8a1b914072106e,0x803930072408e480,0x72600e4c01c9]) (cB [0xe510dca00b9304,0x6405cc803951072a,0x9cca13994073280e,0x8039b0073486e670,0x73780e6c0dcd]))) (bI j 84 (bI j 83 (cB [0xe7e01cf61b9bcc,0x8301d001b9f8273f,0x1d0c33a18074186e,0x803a30074600e8c0,0x74780e8c0dd1]) (cB [0x82e9549d202ba3c1,0xa90dd5203aa01753,0x1d5813ab0075600e,0x41bac8075900eae1,0x75a80eb501d6])) (bI j 85 (cB [0xcebb25d7603ad46,0xcb15d940bb280762,0xddc213b84076822e,0xe0bb9c077302ee30,0x77404ee801dc]) (bI j 86 (cB [0x18eed0ddd613ba81,0xfd2ddf80bbf00778,0x1e3c23c5c77841ee,0x423c90e79104f220,0x79b00f3601e6]) (cB [0x2f3601e6c03cd80,0x3801e6e0bcdc079b,0x5e7c53ce8479c04f,0x683d24a7a480f480,0x7b382f6311ea]))))) (bI j 92 (bI j 89 (bI j 88 (cB [0x84f7329ee40bda0a,0x8239f020bdfc27be,0x1f2213e4017c800f,0x203e5c27c988f930,0x7cc80f9901f3]) (cB [0x84fa27df3833e643,0xcc01f921bf0c67e0,0x5f980bf3007e600f,0xc23f3887e700fcd0,0x7ed04fda01fa])) (bI j 90 (cB [0x80fde05fba0bf701,0xe751fce03f7c87ef,0xdffc03ff807fd86f,0x204004080080ffe0,0x801010010600]) (bI j 91 (cB [0x9d0050200a040083,0x131a0260404c0802,0x2052440a4080ca10,0x6240cc0818850310,0x81c030370606]) (cB [0x50541209c340e55,0x5b3e0b604168182c,0x210a041fc68352b0,0xa042140842810850,0x842990850210])))) (bI j 94 (bI j 93 (cB [0x1096021222c2440,0x9a0212c24258084b,0xa1340c268084d010,0x204284084e8909b0,0x856010a12e14]) (cB [0x830b01615c142b02,0xb80216c142d8085a,0x2174142e0285c010,0x2143001860010bc1,0x868810c33a18])) (bI j 95 (cB [0x10d1061a2043440,0xd4021a8043482869,0xe1ac04358086a050,0x60436c086c850d60,0x872010db261b]) (bI j 96 (cB [0x30e6021cc043902,0xf00a1e00439c9873,0xa210043cd5879030,0xc0c4380887011081,0x8878110f0221]) (cB [0x811130221e2443c0,0x1c022380444c9889,0x623c0c478088e051,0x448088900111f0,0x894811280625])))))) (bI j 107 (bI j 102 (bI j 99 (bI j 98 (cB [0x811310a262044a48,0x34362660c4cc0899,0xa2866450c08a0851,0xe0c55428aa8114f1,0x8ae2d158122a]) (cB [0x1173062e6045c81,0x76022e8145d008ba,0x22ee0c5d818bb011,0xc61828bc1d1780,0x8ca171892e31])) (bI j 100 (cB [0x811b30235a3467ce,0xb40e3660c6cc08d9,0x6370046e008db831,0x40470808dc931b80,0x8e1031c20238]) (bI j 101 (cB [0x51c4023880470c1,0xcb0238e2471818e2,0x63a44c74028e58b1,0xa1477018ee011db0,0x8f0031df063b]) (cB [0x871e8063c62c7842,0xfd0a3e84c7b088f4,0xa3fe047fc08ff811,0x2048040900811ff0,0x900852010240])))) (bI j 104 (bI j 103 (cB [0x1208024082480c1,0x193e4108c8200904,0x64500c8a00914012,0xc0c8b80917012291,0x9178922f0245]) (cB [0x32330e466048cc0,0x371e46e048dc091b,0xe47e048fc091f032,0x1c92009230523f1,0x9258124b0249])) (bI j 105 (cB [0x9b24d0249a0492c2,0x5c0a4b60c9681926,0x64bc0c978092f012,0xc5c99029320125f1,0x939812710a4c]) (bI j 106 (cB [0x87277024ee049cc4,0x7b024f6049e8193b,0x650604a08193d8f2,0x224a240944032831,0x9488128d1251]) (cB [0x92912652204a440,0xa5025480ca78694d,0x257604ae03952a72,0x804aec195d812bb0,0x960012bc1257]))))) (bI j 112 (bI j 109 (bI j 108 (cB [0x52c3065801cb000,0xc70258e04b181962,0x659204b240963852,0x41cb480967092c91,0x96b012d5065a]) (cB [0xb2e0325c004b58a,0xf21a5e404bc41976,0x661614c0c897c172,0xa2cc5019890530d1,0x9989731a5e62])) (bI j 110 (cB [0x133d0e67a04cf01,0x410a68204d0019a0,0x269c04d3419a1953,0xc24d3809a70134e0,0x9a9073520269]) (bI j 111 (cB [0x8135b0a6ac2cd541,0x601a6be0cd7429ae,0x26ce04d9819b3013,0x814dd009b9833673,0x9bb03376026e]) (cB [0x9737b026f214ddc2,0x880671004e1829bd,0x271604e2429c4813,0x624e4819c78738b1,0x9cc033970672])))) (bI j 114 (bI j 113 (cB [0x153a2227420ce648,0xb90a77204ed059d5,0x678244ef059dd833,0x404f7c39ed0b3c94,0x9f2213e20a7c]) (cB [0x813fd0a7fa04fd09,0xff027fe04ffc09ff,0x280a0500c29ff893,0x80d0300a028f4050,0xa070540d0681])) (bI j 115 (cB [0xf4100a820050400,0x1906832050640a09,0xa836050681a0d014,0xa4d0740a0e8141b0,0xa13054260283]) (bI j 116 (cB [0x8142a06854050a02,0x3802870050acda15,0x28744d0e02a1c014,0xe2511c0a23814431,0xa2b0144b2e88]) (cB [0x25456028ac051580,0x69028d2051a01a2b,0x28d6051ac0a34854,0x2d1b4ba358546b0,0xa3f0147d068f]))))))) (bI j 136 (bI j 126 (bI j 121 (bI j 119 (bI j 118 (cB [0x548002900051f82,0x870290a152083a40,0x29261522c8a43894,0xc052541a4a814950,0xa4c014960a92]) (cB [0x8349a06930152600,0xa90a9482d2708a4d,0x695e052bc0a55894,0x4052f45a5a134af1,0xa61014c20298])) (bI j 120 (cB [0x834c60e98c053084,0xd1029a2053287a64,0x29c24d3450a68814,0x80d3b00a75054ea0,0xa76874ed029d]) (cB [0x814f7029ee053c07,0xfa069ee1d3dc0a7b,0x29f82d3ec1a7d814,0x62d4042a80815010,0xa840f50802a0]))) (bI j 123 (bI j 122 (cB [0x151002a200543c1,0x121aa24054402a88,0x2a6a654911a8c195,0xc155388aa48b5412,0xaad2d5580aaa]) (cB [0x957602aea0d5c05,0x7a02af4055e80abb,0x2b101d5ecdabd035,0x8156300ac58358b0,0xac78958e06b1])) (bI j 124 (cB [0x815930ab260564c0,0xa806b327d6544aca,0x2b52056a40ad4815,0x4056a41ad4815a90,0xad58f5aa06b5]) (bI j 125 (cB [0x815b50ab6a056c83,0xb70eb6e056dc0adb,0x2b76056ec0add035,0x157200adf935bb1,0xae5075ca02b9]) (cB [0x1d5cd0eb9a057340,0xde06bbc057780ae8,0x6bc41d7880aef875,0xc157d80afb015e54,0xafc075f802be]))))) (bI j 131 (bI j 128 (bI j 127 (cB [0x815fb12bf6057ec0,0xa02c08357fc5aff,0x2c22258287b05016,0x8058586b0a836150,0xb0e1761c02c3]) (cB [0x9b62e3ec561d89c4,0x541aca4159288b1e,0xecca659709b2d056,0x5a408b42196714,0xb4c9769806d3])) (bI j 129 (cB [0x836a616d4815a900,0xaf0ed581dab00b55,0x6d7e15afc0b591b6,0x405b202b610d6c10,0xb65016ca02d9]) (bI j 130 (cB [0x8f6d102da00db286,0xda02db20db601b68,0x6dd275b6ceb6d036,0x635be03b7c016f70,0xb82017010edf]) (cB [0x370716e0e05c103,0x162ee2815c347b86,0x2e5215ca01b908f7,0x605cc42b958d72b0,0xb999573302e6])))) (bI j 133 (bI j 132 (cB [0x2b73e12e7c05cf41,0x5c02eb60dd5c4ba1,0x2ed415d70ebae017,0x805db00bb60176c0,0xbb68376c06ed]) (cB [0x777202edc25db80,0x760eeec05dd41bb9,0x2ef41dde80bbc837,0x5e400bbea777d0,0xbc88179006f2])) (bI j 134 (cB [0x8179302f240de441,0x970af2e05e4c4bc9,0xaf5405ea80bcca37,0x805ecc1bd60f7aa0,0xbda077b402f6]) (bI j 135 (cB [0x37c11ef782dedc5,0xc91af9205f240be4,0x6fc84df3d5be7817,0x225fb83bf7017ed0,0xbfb877f50afe]) (cB [0x9b80a36ff485fe80,0x5843086ae091fc0b,0x70e4061c80c34158,0x8161cc1c39818720,0xc3b03876030e])))))) (bI j 146 (bI j 141 (bI j 138 (bI j 137 (cB [0x8787b030f2161dc2,0x93070fcae1f80c3d,0x71280e2500c4a018,0xc0e2580c4b018950,0xc4b878970312]) (cB [0x898a5031345e2680,0xac07158062a43c52,0xb15c2e2b41c56818,0x2062d44c5a818b30,0xc5d0b8b90717])) (bI j 139 (cB [0x98c013180062fc1,0xd00f1923e3201c62,0xb1cc2e3551c69858,0xa1e3b40c76818eb0,0xc788f8f0071d]) (bI j 140 (cB [0x818f8071f0063e00,0x503206163e4ac7c,0xb2101e4182c82839,0x4064441c888190b1,0xc89a19120722]) (cB [0x1923072460648c0,0x2483248064900c92,0x7294065280ca20d9,0xa065740cad8594a4,0xcb08b95d132b])))) (bI j 143 (bI j 142 (cB [0x19700b2cc565980,0x82033020e5c8fcb9,0x33160e6089cc1019,0xa066301cc60198c0,0xcc68398d0331]) (cB [0x9b98f0331c0e6380,0xab033540e670ecc7,0xf3561e6ac0cd5819,0x2066dd2cda859ae1,0xcf2b79c97339])) (bI j 144 (cB [0x3a1203424068012,0x13034260684c0d09,0x34260e84c0d0981a,0x1e8504d0a01a140,0xd0e01a1b0743]) (bI j 145 (cB [0x85a1d034380e8700,0x200343e0e87c0d0e,0x344a168901d1009a,0x2069040d1d8da275,0xd2607a412f48]) (cB [0x8da530349e2693c0,0x5b034b2169640d29,0x34c21e9783d2d87a,0x20e9a01d3209a640,0xd3f8da6a574d]))))) (bI j 151 (bI j 148 (bI j 147 (cB [0x81a8d0351616a146,0x8f2751e06a342d46,0x753226a640d4c03a,0x206a7cad4f03a9d0,0xd5489aa90355]) (cB [0x5ab80355a5eab40,0xbe3357816ae82d5c,0x35960eb2c0d6503a,0xa0eb340d6603acc0,0xd6e85ace3f59])) (bI j 149 (cB [0x93ae0975c006b7c1,0x1d0761e76c381d82,0x365416c78cd8f01b,0xa06cb01d9601b2c0,0xd9683b2d0365]) (bI j 150 (cB [0x1b310765c1ecb80,0x52036828ecc8fd99,0xb6a42ed480da901b,0xcbed741dae81b571,0xdbc85b75136b]) (cB [0x83b7c0f6f60edec0,0xa4037364ee01bdbf,0x375406e945dd203b,0x406eb8cdd701baa1,0xddf05bba1377])))) (bI j 153 (bI j 152 (cB [0x8bbcb0b7940ef00a,0xe80f7cc16f494de6,0x37deeefac4df581b,0xc2f0580e080dc0c1,0xe0e07c1b0782]) (cB [0x83c23038460707c4,0x530787ea7091be11,0x38aa0f1540e2a03c,0x6071681e2b09c560,0xe2f01c5b0f8b])) (bI j 154 (cB [0x81c650b8ca071787,0x69078d20719c2e33,0x78f0071a8ee3501c,0x4271e41e3c81c780,0xe4307c7e238f]) (bI j 155 (cB [0x1c890f912072240,0x93179183f2300e46,0x3950272943e4c1bc,0xc073741e6c0bcacb,0xe6f81cde079b]) (cB [0x87cf11b9c67737c4,0xfc039f4173e80e7b,0x3a1e6f408de7e0dc]))))))))) 19 (i % 16)
set_option maxRecDepth 16000 in
def zsi (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 233 (bI j 116 (bI j 58 (bI j 29 (bI j 14 (bI j 7 (bI j 3 (bI j 1 (cB [0x90002008000003f,0xa01b09dc01305920,0xe120330e120270b6,0x580023144b6a03f2,0x3278e1231b859231,0x1233fab6a3338b6a,0xff26270f2e620ce]) (bI j 2 (cB [0x2c10e663f2ff2633,0x293f90e69338f2e9,0xff2c3faf2ec384ff,0xf00040094f2ef446,0x1b006c013000a00,0x1a033011a027009a,0x204314409a03f21]) (cB [0x2702ec31b025a315,0xc33f232233303223,0x3cc627038062042e,0xc046e63f23cc6330,0x93f0528933052492,0xccc3f2524c3843cc,0x66204380f4463]))) (bI j 5 (bI j 4 (cB [0x26000c0080008621,0xe333401a04a001a0,0x20620201e33f001,0xf0038933002892c0,0xc38004694b203893,0x38c4b0062c3f005e,0x6038f4b205ef4440]) (cB [0x4a000e3264029250,0x894b001492c400e3,0x1094a4015250001,0x401264a00132500,0x3540010330001725,0x2292c001d2504010,0x4023250002694b00])) (bI j 6 (cB [0x4a00143140025250,0xac38002292c401c3,0x34c4b0030c3f002,0x2034f4b202af440,0x250002cf44003725,0x166200032334002f,0x2ef440024c3800]) (cB [0x4a003a92c202f250,0xc56003e956003c9,0x452500042f4a004,0x60018008403555c0,0x2a004c028004802,0x5462800266200052,0x5a92c005862a00])))) (bI j 10 (bI j 8 (cB [0x3e203e94a003e93e,0xcf442040c4a0040c,0x5d2504040f55005,0x2004a62860412552,0xc38204e93e004e93,0x56c382050f440050,0x4a0182056f4400]) (bI j 9 (cB [0x3800569340050334,0xcc4b2044c3f002ac,0x44f4b0060f44005,0x2cf44402b2506,0x360064034402d25,0x3c931003092c0068,0x2042949004293d00]) (cB [0x56403cc56006ac38,0x155c60432564042f,0x666310032620403,0x440332504066c4a0,0x333007c315006e31,0x80632207e33f007e,0x90c38208063e00]))) (bI j 12 (bI j 11 (cB [0x322090f440094c3f,0x6c38207063e00706,0x76f44007ac3f007,0xe0074f440072c3e2,0x63c0078f44207493,0x7031420726480072,0x8863e008262000]) (cB [0x3e008ef44008ac3e,0x23140086f440084c,0x8cc380084620007,0x8692c00746200,0xf44208e93e007662,0x7a314007892c0092,0x96632008863000])) (bI j 13 (cB [0x38208a648008a63c,0xc948008c93c0098c,0x9c032001a01a208,0xb604a209c03e0,0x63300de62100c662,0xf664b20ee63f00ee,0x104c3f00fac3800]) (cB [0x4b20faf440112c4b,0xe62001192502112f,0xaef4400a6c3e009,0xe00b525000b2f4b0,0x25000a2f4400a0c3,0xa8c3800a062000a5,0xad25000aaf4a00]))))) (bI j 21 (bI j 17 (bI j 15 (cB [0x4800b125000a292c,0xcf4a00a492c00aac,0xb800800b125000a,0xf00bec3800ba6200,0xc3820bef4400c2c3,0xbc92c20bcf4400bc,0xc403400c0f4400]) (bI j 16 (cB [0x3f00ce03300c8025,0xe33200d004b20ce0,0xba34a209e33e009,0xb00d8c3f00d2c380,0xf4b20d2f4400dac4,0xcac3800dd25020da,0xcd25020caf4400]) (cB [0x4a20a263e00ca331,0x725000d4f4400bc6,0xa034800a033c00d,0xa00a463e00cc3312,0x25000d6f4420a464,0xe603e00e003020d7,0xe805620e604a00]))) (bI j 19 (bI j 18 (cB [0x5c20eb25000eaf44,0x2f4400e2c3800ed5,0xe233c00e525020e,0xf0f4a00e433c0,0xf4400f555c00f325,0xae33e20f925000f8,0xd292c00be34a20]) (cB [0x4b20f293f00ea92d,0xf4b00fcf4400f89,0xc064a0103250010,0xa00ff25000d4c380,0x25000d6c3820b064,0xa603c010603200ff,0xc205620a604800])) (bI j 20 (cB [0x3d010863500d8620,0xac3820f064900f06,0x10ef56010cc56010,0xc011155c210f2560,0x4820a834800a833,0xac35400ac34820aa,0xda62020b204a20]) (cB [0x4a0116c380114635,0x1250010ef4a010cc,0xb433e001c326210,0xd00dc92c20b434a0,0x94b00f493f00ec92,0x10f4b0102f4420f4,0x11c01e210325001])))) (bI j 25 (bI j 23 (bI j 22 (cB [0x3e009c026014001f,0xe31b409c04a01480,0x15c620015633f001,0xf018a62701786210,0x92c418a64b019a63,0xda94b01c493f01b0,0x202f4401f2c3e01]) (cB [0x1441b125041c4f4b,0xa6260124620011e3,0x12a64a013063e012,0xb013a93f013492c4,0xf4b013ef44013c94,0x2092c4135250413a,0x41212500122f4401])) (bI j 24 (cB [0x500128f44012692c,0xf250012cf4441272,0x133250013292c012,0xe012692c01206204,0xf44412e94a013293,0x2262001392500136,0x12c932012892c01]) (cB [0x500136c38412c94a,0x4f4a0142c3841372,0x14355c0147250014,0xb014e92c014a6204,0x92c414f250015294,0x4c92c414d250014c,0x154028015125001]))) (bI j 27 (bI j 26 (cB [0x27015af440158f48,0x3f80c8031015e0,0x9e326415e04ba0d,0xc409e34a014a33e0,0x94b016a93f016292,0x76f440172c3e016e,0x4163250416af4b01]) (cB [0x3e80ca331016001c,0x4c3e40a464a014c6,0x1692500166f44016,0x60170328016cf480,0x92c40a034a00a032,0x74c38016c93d0164,0x4165250416cf4a01])) (bI j 28 (cB [0x4a00a263280cc33d,0x72500166c3840a26,0x17c03c017a032416,0x8417a056018204a0,0xf4a0184c38011e32,0x8555c01892500186,0x180f44017ec3841]) (cB [0x34017e33c417f250,0x2634018034801206,0x192f4a018c01c012,0x4019955c01972500,0x6400191250018ef4,0x90328018e3280194,0x1a6c38019c01c01])))))) (bI j 43 (bI j 36 (bI j 32 (bI j 30 (cB [0x2c41a755c01aaf48,0xf25001a2c3c019e9,0x1a092c01a0c3c419,0x841a0f4401a4c380,0x32801a8f48019e32,0xac94201a201c01a0,0x1aef4401a8c3801]) (bI j 31 (cB [0x2a01a432841a9250,0xe33e014232b01343,0x16292c40b434a014,0xb01a693f018492d0,0xf4401b2c3e419894,0xc325001c0f4b01bc,0x16492c40ac34a01]) (cB [0x3801a893d01b4935,0xb25001b8f4a01b6c,0xb064a013663601b,0x801bf2500166c384,0x64a013863601b8c4,0xbaf4a0168c380150,0x13a01e01bf25001]))) (bI j 34 (bI j 33 (cB [0x29016a62040b2056,0xc95601c892c01c66,0x1d6f4801d0c5601c,0x801caf4841c155c0,0xc4001d2f4801cef4,0x6c62040aa04a01d4,0x1ce94a01ca92c01]) (cB [0x5001d8f4401d2c4a,0xc026013c01e41b92,0x1e402a01de02801d,0x9016e620015204a0,0x94a01e892c01e662,0xecf4a01d0c4a01cc,0x41d125501f125001])) (bI j 35 (cB [0x4401e093e0170314,0xe94001ea03c01e2f,0x1d2c4801ce94801e,0x801d493c41d32540,0x1f01e233441d4f4,0xa604a00a60260144,0x172620015833d40]) (cB [0x3301926270186621,0x863701f663501f46,0x19264b01aa63d01f,0xd01fa93301b292c4,0xc3801ec94b01d693,0xfac4b0200c3901fc,0x41b325041d6f4a41])))) (bI j 39 (bI j 37 (cB [0x4841b525001b492c,0x833201fe01901ac6,0x15a63d40a834a00a,0x801ae93d017492c0,0xf4a01d8c3d01b6c3,0x3e32a41b725041d8,0xae332014632b01]) (bI j 38 (cB [0x2d017692c40ae34a,0x694b019693301889,0x1f0c4b01bcc38419,0xf800600941bd2500,0x27815c01b020600,0x5c03fa0c603380c6,0xc631b0006315c1]) (cB [0x3f215c333015c327,0xe627021462040c63,0x24663f222e633022,0xf8246933821492c0,0xc3fa214c38422e93,0x892c4214f44622e,0x220e93f020e93302]))) (bI j 41 (bI j 40 (cB [0x3f8208c38021094b,0x8f44420ec4b8210c,0x209250620ef4ba20,0x220af44020ac384,0x31b0212028020d25,0xd233380d23270208,0x162627c17633fa0]) (cB [0x2c40dc63f2162633,0x893f021e93302169,0x228c3f2216c38022,0x3020a627022cf442,0x933c16663fa0d663,0x18c3840d693f2166,0x8218f44021cc3f02])) (bI j 42 (cB [0x2580bc325021af44,0x463d0164631014c6,0x22294a022092c216,0x2224f4a0224c4a0,0x625c0a2325022725,0x2293e022a92c40a4,0x221cf440224c3e02]) (cB [0x3f80d4633020c627,0x893f0168933a0d46,0x226c3f8218c38216,0x9020e00fa218f440,0x4ba0da03f809e01,0x6a33f009e319c16a,0x23062040da34b21]))))) (bI j 50 (bI j 46 (bI j 44 (cB [0x4a823464a023463e,0x8f448238c3e02389,0x2292500244f4ba22,0x48232c3e023294a4,0x94a422b250a22af4,0xa001942232500236,0x232620c16c04980]) (bI j 45 (cB [0x3e023a92c023663e,0x2f49a224f44023cc,0x240f48023e934024,0x802429540240c480,0x19021000f8242c4,0x4a01f024801b814a,0x80d8033817202502]) (cB [0x19c172049a0d803f,0xe333024c31b00ba3,0x24e620216e33f016,0x3823463202526210,0x63fa23463e025463,0x3893e02389322254,0x256c3f821ec3822]))) (bI j 48 (bI j 47 (cB [0x49a21ef444238c49,0x3e02500326238f,0x1743498174325225,0x8223a93e023a932c,0xf44423ac498220c3,0x58634623af49a220,0xa236648823663c02]) (cB [0x48023c93c0236930,0xcf544236c54223c9,0x23e624623d254423,0x8423e948223e63c0,0x26025c00f623ef4,0x7e03202780270260,0x426004a227e03e02])) (bI j 49 (cB [0x190008315427804b,0xc31f006e31d00203,0x17833300de327007,0x640de34b217833f0,0x63e0294632029062,0x9e92c429064a2294,0x22b093f02b093302]) (cB [0x3f02dcc3802c894b,0xcf4442b0c4b02e0c,0x29f25062b0f4b22d,0x5425f55c025ec384,0x33f017a33300e032,0x6294a40e834b217a,0x270c3f026ac3802])))) (bI j 54 (bI j 52 (bI j 51 (cB [0x4b226af440274c4b,0x492c02772502274f,0x268c490266c38026,0x12268f492266f440,0xf440266c4a00e263,0x72034026f250026c,0xe4631026895402]) (cB [0x56226f250026ef44,0x3e027d55c027ac,0x17c33100e6327028,0xc40e634b218233f0,0x94b028a93f028492,0x8af4b028ef44028c,0x28292c428525042])) (bI j 53 (cB [0x31028233e4283250,0x92500286f44017e6,0x286c38018063d028,0xc029325042872500,0x250029a94b029692,0x9c62802992504297,0x284332025e31b02]) (cB [0x4b427634a228433e,0x46330022625427c3,0xec64b218463f018,0xa229693e02969324,0xc3f02a0c38429294,0xa0f4402aac4b02a6,0x2af25022aaf4b22]))) (bI j 56 (bI j 55 (cB [0x44426e64a228663e,0x233002a525002a2f,0x2ac93402a8934028,0x1228864a028863e0,0xc4a0298c3e002493,0xa525002a4f442298,0x4274056228a04a22]) (cB [0x4a02bc92c02b2628,0x2c5602c095602be9,0x2c725002c4f4a02c,0xe02b464a42ab55c0,0xf4402b894a02b693,0x6805442ad25002ba,0x2ba93402b462842])) (bI j 57 (cB [0x3002cc02a02ca026,0xc03e027a03102620,0x262054228c04a028,0x60026319427a0554,0x62a02d062802ce62,0x9a64a029a63e02d6,0x2c093e02d892c22]) (cB [0x4a02c2c3e22c094a,0x2f5502daf4422c2c,0x2c325522db25042c,0x822d293e02d29326,0x33022d4f4402d4c3,0x6633c42643540264,0x2d4934426635402]))))))) (bI j 87 (bI j 72 (bI j 65 (bI j 61 (bI j 59 (cB [0x4a228e33e026a332,0xa6330076629426a3,0xea64b218863f00e,0xb22c6c3f02a0c384,0xf4b02def4402dac4,0x6c63e42a125062c6,0x78935426c64a02]) (bI j 60 (cB [0x2642a325002a2f44,0x2032028003002700,0x7a31d427005602e,0x42186349018633d0,0x92c02e863602e463,0xc493d02be93102a6,0x2eac3822c494902]) (cB [0x5642c4f5642bec56,0x862042a755c62c52,0x2e6c4a02e663102a,0x3001a00d42a92504,0x4b218a03f018a03,0xf834a02ee31440f6,0x2fac38029062002]))) (bI j 63 (bI j 62 (cB [0x44031cc4b0304c3f,0x1250231cf4b22faf,0x2f404a02f000e032,0xa02f325002f72500,0x34b219633f02f231,0xf4b02fcf4440f8,0x2ff250030325003]) (cB [0x49019203d02ff250,0xe336030633421920,0x314c560310c38030,0xc23192560318f560,0x3d0194025031b55,0xac4a0308c382194,0x31201c030d25003])) (bI j 64 (cB [0x38030c6400316334,0x8f4a0314c4a031ec,0x1c3192301250031,0x219834b019833f0,0xf44029292c02f662,0x3250031af4b0302,0xee027007e01f23]) (cB [0x2040ee04b219a03f,0x893f032492c02946,0x366c3e035094b033,0x4338f4b037ef440,0x34b21a633f432525,0x26c3e029692c40f4,0x334f4b0330f4403])))) (bI j 68 (bI j 66 (cB [0x3621a833d0337250,0xcf4a032ac3803289,0x333250032f250032,0xa0298c38032cc480,0x92c0333250032ef4,0x46c56033e956033a,0x433555c034af4803]) (bI j 67 (cB [0x480340328033cf48,0x23280342c3c0344f,0x34c6420348f48034,0xa034494a033c92c0,0x250034ef440348c4,0x5a32a0352328432d,0x35c629029a62003]) (cB [0x4a033e94a035e92c,0x52500362f4a0346c,0x29c3144347255036,0x4035693e035492c0,0x948036001c0358f4,0x492540348c480344,0xf0027035863443]))) (bI j 70 (bI j 69 (cB [0x3d036e0370368033,0x63640f004b21aa0,0x376933032692c037,0x8036294b034a93d0,0xc4b037cc39037ac3,0x27250434af4a4376,0x36c028036a01c43]) (cB [0x3d032862021ac03d,0x4c38037292c034c6,0x329250434cf4a037,0x821ae33d03786284,0xf4a034ec3d032ac3,0x72940432b250434e,0x40f234b00f233303])) (bI j 71 (cB [0x500364c4b0330c38,0x327002831b43312,0x11833f21b033301b,0x7029e62102146204,0x63f2324633032462,0x90933038292c4320,0x2382c3803c093f03]) (cB [0x2703caf4423c0c3f,0x263f21bc633002a6,0x2a092d021692c410,0x8430293f23309330,0xf440388c3f0384c3,0xfe93f002c933038e,0x2a2c390218c3840]))))) (bI j 79 (bI j 75 (bI j 73 (cB [0x440386f4442fec3f,0xc92c60b0631021af,0x38cc38038a935021,0x821be93f002e9330,0xc3f02a4c398218c3,0x3031b0386f442332,0x392327014e32500]) (bI j 74 (cB [0x4b21b233d01b2331,0x6621021e62041103,0x39a629039462702a,0xd032663103a462b0,0x92c431a64b232663,0xb494a03b292d03a6,0x3bac4a03b894b03]) (cB [0x1c03bf25023baf4a,0x4325039893403960,0x1b433d039c33101b,0xa039ec3802a86202,0x62403a325003a0c4,0x2864803286300398,0x3aa02a03a801a23]))) (bI j 77 (bI j 76 (cB [0x3d01b663103ac04a,0xa931022092c21b66,0x3aec4a232a93d032,0x3b125023aef4a0,0x33103b6629022262,0x2462021b833d40ac,0x3ae92c232c63d02]) (cB [0x3d015063103bcc38,0x692c21ba64901ba6,0x32e93d03a2935022,0xb03b0c38232e9490,0x33f40b4325003431,0xaa621022862021c0,0x233463f03c262902])) (bI j 78 (cB [0x3e03b493e03c892c,0x43312388f4403bac,0x3c6c3e02ac62003c,0xe022a92c238af440,0x627238cf4403bcc3,0xc263f01c26330036,0x2ae92d022c92c21]) (cB [0x38233693f0336933,0xef4403bec3f038ec,0x9c019003800f238,0x4411204b21c403f0,0x31d02b0315022e31,0x1c34b233833f03ce,0x40863e03ee62043])))) (bI j 83 (bI j 81 (bI j 80 (cB [0x3e042094a041264a,0xcf4b046af440456c,0x3d002543c1250046,0x4411404b21c603f0,0x93e03d264a02b231,0xeaf4403e494a03de,0x43c325003ecf4b03]) (cB [0x2002b431443c5250,0xaf4403d693e03d46,0x3d8f4803dcf4903d,0xa02b631403d89480,0xf4a03e092c03d664,0xd864843c725003e2,0x3e692c02b831403])) (bI j 82 (cB [0x4a02ba62003e8f44,0xb25003e8c4a03da9,0x3e294803dc654638,0xb21c833f003a31b0,0x6210230620411634,0x1e64b233a63f02bc,0x3fec3e03f094a43]) (cB [0x500406f4b0404f44,0x292c023262043c92,0x3faf4403f4c3e03f,0x803f693403fcf490,0x33d03f8c4803f8f4,0x3c63d823262021ca,0x400c3803f494a23]))) (bI j 85 (bI j 84 (cB [0x4843bd2500402f4a,0xac4aa22a92c03f89,0x3fc954638d25003f,0xb003c00f0402c480,0x3150234314410c04,0x1434b040a31d02be,0x43b5250040e94a43]) (cB [0x1443b7250040c64a,0x92c040c31d02363,0x1cc03f003e00f041,0xd02c031582343142,0xc3e233e33f041431,0x1693e041ef44041a,0x21ce03d0418f4404])) (bI j 86 (cB [0x38234433d8236314,0x8629a222620041cc,0x422027004000f041,0x5023831421d003f0,0x32703d231d02c231,0x4633f042832b0424,0x40e63e03f062023]) (cB [0x3f043692d042a92c,0x2f44043cc3e04389,0x4266340454f49045,0x42c03104263240,0x92c03d4629023a62,0x2ec3e041093e03f2,0x434f490432f4404])))))) (bI j 101 (bI j 94 (bI j 90 (bI j 88 (cB [0x480430c480430f48,0xc31421d203d043af,0x3f4620234833d023,0x5043e934042e92c0,0x93d0446936044293,0x4ec49044ac38043a,0x21d40310450f4804]) (bI j 89 (cB [0x2c03f6620023e314,0x8f480444f4804409,0x240314044cf48044,0x5043092c03f86200,0xc380448936044493,0x2462063f8f44044c,0x3fa92c03da629a2]) (cB [0x1d02423140432c38,0xc62063dc34103dc3,0x450c48043492c03f,0x9004200f63fcf440,0x3d045803300a601,0x38314410e04b21d6,0x45a33302c431582]))) (bI j 92 (bI j 91 (cB [0x4b234a33d045c337,0xa64a03fe62043183,0x45ec38043c94a041,0xa0466c4b0464c390,0x34843bb2500468f4,0xa83250460031234c,0x823a62021d833d00]) (cB [0x4a040092c234e63d,0x2f4a044ac4a041c9,0x44cc4843af250046,0xd00aa019044e9540,0x620824231460aa03,0x62c3804509480402,0x4431b6402f4404])) (bI j 93 (cB [0x20610034b00ae325,0xa62902c6621a2286,0x40492c630064b03e,0x452c4a041e94a0,0x3d00b2019638925,0xec31d024431460b2,0x40662063ec34103]) (cB [0x440468c480454954,0x6019004600f6406f,0x1da033047001b00b,0x5024631421da03f0,0x31b02f831902c831,0xb231f049831d047e,0x235033f035033304])))) (bI j 97 (bI j 95 (cB [0x3204dc62104c0620,0x263e04ec63304126,0x42093224ec63f241,0xf0500c38242093e0,0xf444420c490504c3,0x720086420f492500,0x47401e004801a04]) (bI j 96 (cB [0x2021dc04a01dc03e,0x892c0476629024c6,0x47a94a047a93e047,0x42422c4a0422c3e2,0x2504422f55047cf4,0x4a0186423255247d,0x480314004800d00]) (cB [0x29048662802ce620,0x92c048e62a048c6,0x49294a049293e049,0x42424c4a0424c3e2,0x2504424f550496f4,0x8203064252552497,0x484628448205404]))) (bI j 99 (bI j 98 (cB [0x320484314004a00d,0x892c242663e04266,0x426c49048ac38048,0x86426f49248af444,0xd048a934049462,0xe6033049a0250054,0x2d031421e603f01]) (cB [0x2c235c33f035c333,0xa93304a0932049c9,0x4aa93f24a093e04a,0x404b0c3f04acc382,0xf44049ec3824acf4,0xa292c02d2314249e,0x4a6c3e04a493e04])) (bI j 100 (cB [0x20005631904a8f44,0x8c3e049ec3802d46,0x4a493004aef4424a,0xd24a694804a693c0,0x310476019005800,0x8631802d631404b4,0x48e31a048c31904]) (cB [0x4a04b863e04b6620,0x894a042893e24b86,0x4bcc3e04bac38242,0x504bef4424bcc4a0,0x25524bf2504428f5,0x8a62404886246429,0x4c400f04c200e04]))))) (bI j 108 (bI j 104 (bI j 102 (cB [0x3204c801f04c601b,0xc03e04d203304cc0,0x5a31b24d203f24c,0x21e833f01e83330,0x63302d8621024e62,0x2a932235e63f035e,0x4d4c38242a93e04]) (bI j 103 (cB [0x44442ac4904d8c3f,0xa930642af4924d4f,0x4ce03e44ca95404c,0x4025062001ea3310,0xf54042cc3c04d0f4,0x2092c24d033e442c,0x4d6f442432c3e82]) (cB [0x3404ce0306432f49,0xe93c041093004da0,0x410c54242e948042,0xe642f254442ef544,0x1e04e001a04de00,0xe604a04e603e04e2,0x252620047832524]))) (bI j 106 (bI j 105 (cB [0x3e04b66290490625,0x6c3e24e894a04e89,0x4eaf442436c4a043,0x524eb2504436f550,0x65404e4630643725,0x7a02501dc01944e4,0x4ee31d025431404]) (cB [0x2004b83290492325,0x892c04f264a04f06,0x438c4a04f694a04e,0x504ff25004faf4a2,0x31c0494318643925,0xfc94004f8f4804f4,0x243ac4804f894804])) (bI j 107 (cB [0x25005c31b643b254,0x33f047c32700be3,0x2da621821e62021f,0xb04ac62904966270,0x92c236463f04be62,0x1e93e04ea92d04d4,0x2452c3e24fe93f24]) (cB [0x316452f490502f44,0xe935822692c00c06,0xc201904d6c3804a,0x901ec03d01520310,0x31d025631421ec04,0x6233d050633504b0,0x4d8620236234903])))) (bI j 112 (bI j 110 (bI j 109 (cB [0x34050c63204f2631,0x6636051463505106,0x4fa63d041a63c051,0x24fa649241a6480,0x93c051a932040e93,0x1ec38243c948043c,0x451ac55440ec5405]) (cB [0x3c643d254443cf54,0xaf54050a93c05086,0x1ee025050e31c450,0x4025831421ee03d0,0x948243e63c043e62,0x3ef480512c38443e,0x244093c044093064])) (bI j 111 (cB [0x306440f484440c48,0x293024fc64804fc6,0x442c542442948044,0x51862464432544,0x9542446648044663,0x472544446c544518,0x51cc54051893464]) (cB [0x24644f254444ef54,0xc93c052202805200,0x44ac3c241c948041,0x4444af54244ac480,0x31f005e31b644b25,0x233300fa3270090,0x821462040fa33f22]))) (bI j 114 (bI j 113 (cB [0x3302fa62702dc621,0x292c42fa63f237e6,0x50093f246a933038,0x4646ac3f0526c380,0x62b00606274382f4,0xfc63f00fc6330092,0x2de92d822c92c40]) (cB [0x3842fc93f02fc933,0x4f440502c3f0384c,0x94013006200f438,0x70148025010401b0,0x31053602b052a02,0x404b21f203d01f2,0x2e0315824631441])) (bI j 115 (cB [0x29053c327030431b,0x6331055c32b05503,0x30434b236633d036,0x7040862503906204,0x63d0456631056862,0x7292c050464b2456,0x440894a058a92d05]) (cB [0x4a4456c4a456894b,0xc00843912506456f,0x106026052e01e052,0x5824862041060560,0x649036863d053063,0x32931039292c2368,0x2458949045893d05])))))))) (bI j 174 (bI j 145 (bI j 130 (bI j 123 (bI j 119 (bI j 117 (cB [0x564532c560534c38,0x355c64592564458f,0x36c348036c33c439,0x4236a648036a63c2,0x3310538325824a31,0x3a92c236e349036e,0x538035053e01005]) (bI j 118 (cB [0x3421f404901f403d,0x492c054863605426,0x45a93d054a931039,0x6054ec38245a9490,0x256445af56454ac5,0x4092c439555c645b,0x544c38039862005]) (cB [0x28054601c4399250,0x801b054031c054c6,0x55203101f6025010,0x4410804b21f603d0,0x631039a62002e431,0x664b05586330554,0x4554c4a055ac3805]))) (bI j 121 (bI j 120 (cB [0x2c439b2504558c4b,0x6314439d250039c9,0x50864a055662002e,0xc43a1250050a94a0,0x25439f250039e92,0x5e03d01f80310530,0x2e831421f804905]) (cB [0x3005483260542324,0x4620237034803703,0x45c631056062503a,0xc245c649056263d0,0xc564560956056492,0x62f560566f44445c,0x43a555c645d25645])) (bI j 122 (cB [0x3023726480372630,0x4648037463c05446,0x5320310106019237,0x421fa04901fa03d0,0x331056a31d825431,0x7633d0560335054a,0x56c620237634903]) (cB [0x38051a956050c656,0x6f560570c56056ec,0x3b955c6467256446,0x8037833c054c3304,0xe051c954237834,0x7a013057600f0574,0x58201e057e01b05])))) (bI j 126 (bI j 124 (cB [0x270586026058401f,0x804b458604a05880,0x9831f006a31b458,0xd01fc331010a3270,0x620410a34b21fc33,0x1062702ea621824e,0x237a63d037a63103]) (bI j 125 (cB [0x3103a692c431064b,0xe94b245e93d045e9,0x45ef4a445ec4a051,0x3a892c43a72506,0x63c057831c43a925,0x7800c21fe64801fe,0x257c648057c63c05]) (cB [0x5003aa92c0580328,0x4a058001843ab2,0x3ad2508250620052,0xe2460c480460c3c4,0x26058e01e058c00,0x3433145900560590,0x20033d053a33505]))) (bI j 128 (bI j 127 (cB [0x3182526202200349,0xc63d0564635054e6,0x3b292c237c649037,0x9046493d056e9310,0xf56456ec56246494,0xb355c64652564464,0x5a201e059401b43]) (cB [0x3305fe03205ba026,0x203f25fe03e06720,0x68a31e45ba04a267,0x20780326077031f0,0x34a27ca33e07ca33,0xea621825a6204780,0x83c63307f662707])) (bI j 129 (cB [0x2c47f664b283c63f,0x93f08d093308989,0x984c38092c94b28d,0x448d0c4b0988c3f0,0x25068d0f4b2984f4,0x9833e05960084899,0x59a92c259834a05]) (cB [0x5005a0f4b059cf44,0xc314059f250259d2,0x5a43338596315800,0xe05a663225a433f0,0xc3f05aec3825a663,0xe31425aef4405b2,0x5aac3e05a863e80]))))) (bI j 137 (bI j 133 (bI j 131 (cB [0x20801031405acf44,0xc93e801462080126,0x1692c05b0f4425a,0x405b603605b40348,0x63c05a8630801831,0xb8c3825aa64805aa,0x827e62005bc04a05]) (bI j 132 (cB [0x3f05d463305c8621,0xc3805dc64b25d46,0x5f6c4b05eac3f05e,0x25f6f4b25e0f440,0x1105be00805fd25,0xc2c38828062005c0,0x25c2f4405c6c3f05]) (cB [0x3005c4f44828292c,0xc04a05cc03e05ca0,0x5d0f4405ce05625c,0xa05d355c25d12500,0x55c05d925005d6f4,0xdf25005def4405db,0x828492c05c234a25]))) (bI j 135 (bI j 134 (cB [0x4b25d893f05d092d,0x6f4b05e2f4405de9,0x5c464a05e925005e,0x805e52508288c380,0x5605e52508286c3,0xec635828c62005c6,0x25d664905d663d05]) (cB [0x5605f0c5605eec38,0x555c25f325605f2f,0x5f8635828a62005f,0xa05f0c4a05fac380,0x92c25e725005f2f4,0xda93f05d292d828e,0x5e8f4425da94b05])) (bI j 136 (cB [0x1f25e925005f4f4b,0x2621826062006003,0x61c63f060c627060,0xf063292c460c64b0,0xc3e065894b064493,0x44f4b0670f440668,0x604032463325046]) (cB [0x56a5ce04a85ca03c,0x8f4a0606c3846040,0x60755c060b250060,0x614f4a060e01c4,0xf44061b55c061925,0x1664006132500610,0x612328061032806])))) (bI j 141 (bI j 139 (bI j 138 (cB [0x480628c38061e01c,0x92c462955c062cf,0x6212500624c3c062,0x8062292c0622c3c4,0x3284622f440626c3,0x22328062af480620,0x62e942062401c06]) (cB [0x500630f44062ac38,0xa92c0626328462b2,0x62893f060692d826,0x40634c3e461a94b0,0x2500640f4b063cf4,0x36935826692c0643,0x638f4a062a93d06])) (bI j 140 (cB [0x50826ec38063b250,0xcc380638c48063f2,0x63f250063af4a826,0xc064662982746200,0xc56064c956064892,0x4155c0656f480650,0x64ef48064af4846]) (cB [0x200654c400652f48,0xe94a064a92c82686,0x6392500652c4a064,0x98270620065a0284,0x94a066092c065e62,0x62f4a0650c4a064c,0x4651255066725006]))) (bI j 143 (bI j 142 (cB [0x40065cf448272314,0x2c48064e94806649,0x65493c4653254065,0x65c3344654f480,0x6270608621826262,0x6c637066a6350614,0x461464b062c63d06]) (cB [0x4b065693d063492c,0x6f4a066ec3806629,0x63692c4635250465,0xc062e64846372500,0x92c063093d826492,0x18933060a92d8276,0x63cc38461894b06])) (bI j 144 (cB [0x2a463d2500666c4b,0x8326067804a06740,0x68262a067c34a059,0x684f4a827892c0,0x1c0677250068925,0x80f44067ef48067a,0x827a92c067e34806]) (cB [0x3606806480686f44,0x2033827cc3806763,0x68c314268203f068,0x306aa32706a43150,0x34b26b033f06b033,0xfa63206b662646aa,0x46b664a26fa63e06])))))) (bI j 159 (bI j 152 (bI j 148 (bI j 146 (cB [0x3f0742933073492c,0x2c38075094b27429,0x742c4b0766c3f076,0x6742f4b2762f444,0x632068e626473525,0x8e64aa68e63e868e,0x6a0933069a92c46]) (bI j 147 (cB [0x3806a294b26a093f,0xc4b86a2c3f869ac,0x6a0f4ba69af4446a,0x2069064a469b2506,0x94a269293e069293,0x96f440696c380694,0x8696932069925026]) (cB [0x38469894aa69693e,0xf250269cf44069cc,0x69263c0692630069,0x4069463006906248,0x95606a6932469465,0xa955c06a8c3846a6,0x6af55c06ac95646]))) (bI j 150 (bI j 149 (cB [0x3846b295606b2932,0xe31446b555c06b4c,0x6b233306a6315068,0x46ac34b26b233f0,0x63306c462106b862,0xc864a26c663f06c6,0x6d293206d064b06]) (cB [0x3806e094a26d293e,0x6c4b06f0c3f06eac,0x6f6f4b26eaf4406f,0x206ba04a06f92502,0x94a26bc93e06bc93,0xc0f4406c0c3806be,0x69031406c325026])) (bI j 151 (cB [0x3e06cc93206ca620,0xcc4906cec3826cc9,0x6ccf4926cef4446c,0xa06bc62006923146,0x93e06d492c06cc64,0xdac3e06d894a06d6,0x6df25006dcf4406]) (cB [0x2006e232a0694314,0x893206e492c06be6,0x6e6c3826d893e06d,0x926e6f4406e8c490,0x92c069662026e8f4,0xdcc3e06ce94a06c0,0x6ecf4406e6c4a26])))) (bI j 155 (bI j 153 (cB [0x3006f263406ef250,0xa94806da93c06d69,0x6cc65406f4c4826d,0x6e895406d89304,0xc3e06c292c069862,0xeef4426dec4a06de,0x868e31426ef25006]) (bI j 154 (cB [0x3e070662706fc620,0x664b071063f07086,0x71c931071292c470,0xe072c94b072893f0,0xf44471cc4a072ec3,0x132504728f4b0732,0x70093106fe92c47]) (cB [0x444700c4a0702c3e,0x31446ff2500704f,0x70c92c070a620869,0xa270e93d070e9310,0x250670ef4a470ec4,0xfe92c8696620470d,0x714c3e070c93e06]))) (bI j 157 (bI j 156 (cB [0x500718f440716c4a,0x6208692314071b2,0x71e92c070e63e070,0xa072294a072093e0,0x2500726f440724c4,0x2093c270e6484717,0x72293c072af4807]) (cB [0x144724f540724c3c,0x492c070262086943,0x72a93d0720931071,0xa4720c4a0730c380,0x6204715250472af4,0x18c38070492c8698,0x4726f4a0726c3d07])) (bI j 158 (cB [0x21069a6204719250,0x463f06b463306a86,0x71293246ae64b26b,0x846f894a271293e0,0xc4b073cc3f0736c3,0x3ef4b2736f44073e,0x69c92c074125027]) (cB [0x4446eec4a2718c3e,0xc930073b2500738f,0x714948071493c070,0xc46de954071693c2,0xc4a071ac3e069e92,0x3b250073af44271a,0x6d263006a031427]))))) (bI j 166 (bI j 162 (bI j 160 (cB [0x56272864a071c63c,0x694a074492c46f66,0x74ac560748956074,0xc074f250074cf4a0,0x93c06d4930473f55,0x2063c06d6630071e,0x6d8630272064807]) (bI j 161 (cB [0x3046d8654072263c,0x8654072463c06cc6,0x70e63c06da63046e,0x806dc93c272a6480,0x32806a2314072694,0xc8624075632a0752,0x6e0630075a62606]) (cB [0x54272c64a072c63e,0x893e075c92c46e06,0x74ac3e274894a074,0x50760f44274ac4a0,0x2552761250474af5,0x54f440754c38674b,0x6e2324075831827]))) (bI j 164 (bI j 163 (cB [0x24075832846e2354,0x495406e4930075e0,0x6ce930075463446e,0x46e695406e693c0,0x93e06ea932869a62,0x36c3846ea94a2732,0x760c4b274ec3f07]) (cB [0x50674ef4b0764f44,0xcc3e869e92c47372,0x738f4446ecc4a06e,0x4076803647392500,0x63006f062686a231,0x2e63c076a6320708,0x46f0656272e64807])) (bI j 165 (cB [0x3d0746931073c92c,0xcc38274c949074c9,0x74cf564746c56076,0x4473d55c674d2564,0x948073093c076e02,0x4a060003e2730,0x77293e86a462026]) (cB [0x4b077af44277294a,0x6620277b250077ef,0x776f4a077494a86a,0xa86a892c07792500,0x93c077d2502778c4,0x7695407769480774,0x8294620078231e27])))) (bI j 170 (bI j 168 (bI j 167 (cB [0x3f07aa63307a2621,0xec3f07bac3827aa6,0x78431427baf4407b,0x278a33f078a3330,0x6330790632078c62,0x9a63f279063e079a,0x7a0c3f079cc3827]) (cB [0x3e0786632279cf44,0x8f440788c3827866,0x78ef44078ec38278,0xe079262007863142,0xf440796c3e079463,0x8e92c07886200798,0x79ef44279893e07])) (bI j 169 (cB [0x48079663c0794630,0x493e078462827966,0x7a8f4427a494a07a,0x407a662827a92500,0x32a07ac31c078893,0xb6f4a07a492c078a,0x7a631407b925007]) (cB [0x3e07b063e07ae620,0x231c07b4f4407b2c,0x79c62a07b462807b,0xf07a892d829692c0,0x93607bcf4427b893,0xa031e8298c38079e,0x7c433607c033407]))) (bI j 172 (bI j 171 (cB [0x4907b663d829a620,0xc31407c6c3827b66,0x7c801c07c2c38829,0x1829062007cc31e0,0xf4407e463f07e062,0xd462007ce31407e8,0x7dc63f07d863e07]) (cB [0x4407d063e07def44,0x31407d6f4407d2f,0x7d262007da62007d,0x7ce62807d692c0,0x31c07d293407e325,0x9292c07de62a07e6,0x859a01907e292d82])) (bI j 173 (cB [0x32059601e000c01c,0x804a85c803e86020,0x59a325c602056a5c,0x2859632a800c3280,0x34a060233e05c833,0x8c62845c83562602,0x6a462a86a462906]) (cB [0x4a07e063e07a2632,0x93247a265627e06,0x7a294a87a293e87e,0xf07ecc38c7e0956a,0xc5727f2c4b07f2c3,0xf4f4b87ecf4407f4,0xa7ed25047f2f5787]))))))) (bI j 203 (bI j 188 (bI j 181 (bI j 177 (bI j 175 (cB [0x2847ed55c67f3257,0x34a85d033e00143,0x60663ec60a356a5d,0x445d2656260664a0,0xc3e06a8936069a93,0xe2c56a7a8c4a87a8,0x27ef25007eef44c7]) (bI j 176 (cB [0x34069cc4007f155c,0x628069ec4000166,0x60803c001801c06a,0xe06a2628c6080608,0x56260c04a060c03,0x1a31e07f831c45dc,0x82062006aa32a08]) (cB [0x4487e092c082a656,0x8f570834f4b082ef,0x839257282f250083,0x87ce314083b55c2,0x63e07fa63202f062,0xc64b080464a27fa,0x814c3f080ec3808]))) (bI j 179 (bI j 178 (cB [0x4b280ef440816c4b,0xc63e08192502816f,0x800f4407fec3e07f,0x87d031408032500,0xc490808c38080662,0xaf492808f44080a,0x80894a280093e28]) (cB [0x3008132500810f44,0xe64807fe63c07fc6,0x7d2620080a65427f,0xa080293e02f292c8,0x2500812f44280294,0x1f55c081c9562813,0x826056082200c08])) (bI j 180 (cB [0x180825250082955c,0x834a082c31c08243,0x80e62845de356261,0x4083355c08312500,0x480812934081093,0x1431c26140540614,0x616030083664008]) (cB [0x4a081631c2616048,0x8628261a356061a3,0x6ae636081e62a081,0x87e2c38082892c0,0x2a283355c083325,0x1c04a05d403205a4,0x83e31c45d405626])))) (bI j 184 (bI j 182 (cB [0x3206b032a086e31d,0xa35627e434a07aa3,0x870c3887a292c47a,0xa087cc570878c4b0,0x25708972500886f4,0x84314487155c4879,0x852627084062687]) (bI j 183 (cB [0x4b484064a085463e,0x293f085a92c48526,0x868c3e086694b086,0x4862f4b086cf440,0x6208786314485b25,0x4693e084464a0842,0x84cc3e084a94a08]) (cB [0x3c0851250084ef44,0x692c084893c0848c,0x858f4a085893d085,0xe878862048572504,0xc3e485094a085693,0x61250085ef44085c,0x858648084663008]))) (bI j 186 (bI j 185 (cB [0x2408486300864f48,0xa654084a63008446,0x84c64a084c626484,0x8086493d085c92c4,0x2504864f4a086ac3,0x4e94a084e932485d,0x485f250085ec3848]) (cB [0x2845da356262834a,0x8c3806b4636085a6,0x8752500872f4a87a,0x8262a348087755c0,0x934085e934085c62,0x7b254086231c0860,0x87e056086431c08])) (bI j 187 (cB [0x560882634086631c,0x54088125408852,0x88804205d6032088,0xc45d6056262c0480,0x33e07b6332086831,0xb63560890342088a,0x872c38089294247]) (cB [0x440884c57087ac49,0x355c487b2560894f,0x88e328088c31c487,0x82630348262e0480,0x35605d833e086a62,0xb863e086c62845d8,0x874f4447b865607]))))) (bI j 195 (bI j 191 (bI j 189 (cB [0x3e0632332487555c,0x462a45fc34a26323,0x7ec92d82dc92c073,0xb287093f08709330,0xc3f089ac38483a94,0x9af4408c2c4b08a6,0x8cf25028c2f4b28]) (bI j 190 (cB [0x3645e864a263c63e,0xec3982a0c3807369,0x832c4b2874c3f07e,0x8a0f4b089cf444,0xc4245e494a08a525,0x9f25082a4f440738,0x263e94a08a294008]) (cB [0x5082a2f44073ac42,0x4348063433c089f2,0x73c62a45f4356263,0xc08ae63608a86340,0x93d08b093582da92,0xb4c3828729490872,0x8bcf5608b8c5608]))) (bI j 193 (bI j 192 (cB [0x2008c155c28bd256,0xac4a03a8c3882d46,0x63633008ad25008a,0x8263634808b233c0,0x34808ba63408b601,0x3a64808be6402638,0x8ac940263a65406]) (cB [0x34073e62a264034a,0x8935c2c692c08c46,0x8b8c4a08ccc3808c,0x28a125008bcf4a0,0xc3e08be93ec2ba62,0xca33c28a2f4408c6,0x264264a064263e08])) (bI j 194 (cB [0x3982dec380740936,0x6c4b0876c3f07f0c,0x8c0f4b08a4f44287,0x6264404a28a52500,0x328074231e45f605,0xf262182b062008d2,0x287864b08ec62907]) (cB [0x4a08f892c4838657,0xc56090895609009,0x9292500920f4a091,0x448c355c092b2570,0x94a08d493e82b231,0xe8f4408e2c3e08d6,0x48c525008eaf4b08])))) (bI j 199 (bI j 197 (bI j 196 (cB [0x1448c725082b8314,0xac3e08d892c82b63,0x8e0f4908def4408d,0x408dcc4808dcf480,0xc3808da94a82b431,0xbf25008e6f4a08e4,0xa2ac62008dc94848]) (cB [0x5468a325008dec4a,0xe03008e6c4808e09,0x5f8056264604a08e,0x608f2c4a08f09564,0x55c08f725008f4c5,0x4834a48cb25048c9,0x74462a45fa35626])) (bI j 198 (cB [0x4a08fac5682bc92c,0xd55c08ff25008fcf,0x5f0056264a34848c,0x902328074631e4,0x55c0906c5682c062,0xbb250090494a48b9,0x74831e264c04a48]) (cB [0x4a82be620090a328,0xe048090f250090cf,0x74a31e265004a264,0x982c462009123360,0x94a08fa92c08f062,0x16f4a0914c380906,0x91f255091d25009]))) (bI j 201 (bI j 200 (cB [0x540918c402652048,0xaf54265403c091b2,0x5f20562656048091,0x208e2328074c31e4,0x64982c2620092234,0xc95608fc92c287a,0x924f440916c5609]) (cB [0x3448bd55c0927256,0x634c08e632808e46,0x5e6356091ac5468e,0xc08e8634074e62a6,0xc3808f6935a2aa92,0x1cf56090ec5608fe,0x8ea32868a155c09])) (bI j 202 (cB [0x54091ec6068ea34c,0xe02605bc0240926f,0x65804a065803e092,0xa0932328075031e2,0x62182e0620094232,0x52627082a62507f4,0x96262b095a62909]) (cB [0x2c287c64b087c63f,0x893e097092d09669,0x90894a097293f090,0xa0910c3e297294b2,0xf4b0976f442910c4,0x772504910f55097a,0x5c0328691125529])))))) (bI j 218 (bI j 210 (bI j 206 (bI j 204 (cB [0x26093062982e2620,0x292c82e431405c00,0x93493e093493204c,0x40940c3f093cc382,0x93e82e6314293cf4,0x3af440938c3e0936,0x293ac3e82a862009]) (bI j 205 (cB [0x3c0936930093ef44,0x18293894809389,0x94431d82e831405c,0xe094a62009483310,0x93e294c64a094c63,0xdec38291294a0912,0x294ec4a094ec3e04]) (cB [0x504912f550950f44,0x6324691325529512,0x95431c0946628094,0xc095632809589340,0x3e095c030095631,0x5231c265e04a065e,0x295ec4a095ec3e07]))) (bI j 208 (bI j 207 (cB [0x2829612500960f44,0x403c093002407546,0x944328075631c096,0xc096800c09586240,0x3e096a01d00b801,0x6033e296c04a096c,0x75c62a266034a06]) (cB [0x4a0914c3e82ea92c,0x4f55096ef442914c,0x915255296f250491,0x8094a634047201c6,0x330094c334097432,0x6062a266634a05c2,0x950636093c63407])) (bI j 209 (cB [0x38096093582a692c,0xcf4a290ec4a096ec,0x91d2550979250291,0x4093e94005c463c6,0x54066204805c602,0x7c34009403282662,0x982940088464909]) (cB [0x3c290c954090c948,0x6c540916c480906c,0x9172604906f60291,0xc097e63c69175604,0x304980f54098093,0x1893026640480664,0x4918c54291894809])))) (bI j 214 (bI j 212 (bI j 211 (cB [0x2a059c3276919254,0x33e05e033205ae3,0x5e034a268833f267,0x2077a62b076262a4,0x64a27e863e07ba63,0xec92d829e92c47ba,0x289693f082e93387]) (cB [0x3f089ac38482e94b,0x6f440976c4b2928c,0x89b2506928f4b098,0xe05b0636059e6334,0x93645e264a05e263,0xbc93e077c9370764,0x82aec3847bc94a07])) (bI j 213 (cB [0x4b0830c3f87f0c39,0x8f4b089cf444830c,0x5a001b489d250097,0x105ea02605b201e0,0x33098a032067803,0x6803c0992036098e,0x2668048068403d06]) (cB [0x1e45ea0562684049,0xe326077e31f07663,0x9a2334099633207b,0x709ac33609aa3350,0x62047be35609b833,0x3462787f462182c8,0x9c063509ba63308]))) (bI j 216 (bI j 215 (cB [0x49088663d09c6637,0x692c483465728866,0x9ca933090093108a,0x72920949092093d0,0xc3909cec38097a95,0xcac574900c5609da,0x69212564920f5649]) (cB [0x3582ca62048a755c,0x8012099001c098c6,0x99432582cc314076,0xe288834908883310,0x63182ce620099831,0x8a649088a63d099e,0x99a33009a0c3828])) (bI j 217 (cB [0x30288e348088e33c,0xc648088c63c099c6,0x99a328099c31c288,0x82d031405b40120,0x63309a463108a862,0x74c38097c64b09a8,0x49a8c4b49a4c4a05]) (cB [0x2082d231448a9250,0x94a097e64a09a66,0x5b601248ab250098,0x982d631409ae03d0,0x349089033109b032,0xb262508ae6202890,0x9b463d092263109]))))) (bI j 225 (bI j 221 (bI j 219 (cB [0x5609b692c2922649,0xcf444922c5649b29,0x92325649b4f56058,0xc099404048af55c6,0x940099e33c09bc31,0xec026099c63009be,0x9c203c066a03005]) (bI j 220 (cB [0x2c45ec056266a048,0x4f5609c493d08b09,0x8b292c48b155c49c,0xc098c03048b32500,0x5409c8048066c03,0xbe63009b0334266c,0x2892654089263c09]) (cB [0xc09b234009cc328,0x401d09d201909d00,0x9d805609d803209d,0xc05ee33205b832a4,0x348068633d066e33,0xee3562686349266e,0x7c6632076c62a45]))) (bI j 223 (bI j 222 (cB [0x3d82d892c47c6656,0x4c38289494908949,0x924c490924c3d08b,0xc69252564924f562,0x25008b692c48b555,0xd664809d663c48b7,0x9a063c052c01c29]) (cB [0x9068a00809b6640,0xe03309de02707700,0x9de04b29fe03f09f,0x78770315868a3144,0x33f89de33389fe32,0x6626c9fe34ba9de,0xaa0663e8a066320a])) (bI j 224 (cB [0x330aac92c4a0664a,0x294b2ad893f0ad89,0xb02c3f8aacc380b0,0xbaaacf444ad8c4b8,0x6204aad2506ad8f4,0xe064b09e063f86b0,0x29e494a09e493e29]) (cB [0x5009f6f4b09f2f44,0x262009e201c29f32,0x9e894a09e692c86b,0x809f125009ecf4a0,0x92c09ee04009ea02,0xf525029f0c4a86b4,0x9fa34009f804009])))) (bI j 229 (bI j 227 (bI j 226 (cB [0x4809e893c09fc342,0xe63029ec95409ec9,0x9ee64809ea63c09e,0xa0094a86aa6202,0x92c86ac6200a0525,0xb600886ae92c0a02,0x877231586fa31406]) (cB [0x4ba9e433f89e4333,0x6210a08620ca003,0xa2263f0a226330a2,0x20a3a64b0a2664a2,0x94a2a3e93e0a3e93,0x8cc3f0a82c380a62,0x2a82f440aa4c4b0a])) (bI j 228 (cB [0x4a0aab2502aa4f4b,0xc62006b83140a0a0,0x9e663f89e663386f,0xe0a0c932ca0264ba,0xc380a1094a2a0c93,0x1cc4b0a1ac3f0a14,0x2a1cf4b2a14f440a]) (cB [0x1406ba3140a1f250,0x6200a0e32906bc3,0xa1232906be314870,0xc06c062087026200,0x2500a16f4486fe92,0x492c06c26200a19,0x2a192500a18f4487]))) (bI j 231 (bI j 230 (cB [0x1d06c600806c4314,0x800887063140a240,0x7083140a2801f06c,0xf0a2a31e87743158,0x33f89e83330a2e31,0x329320a30620a9e8,0xa34c382a3293e0a]) (cB [0x444a32c490a38c3f,0xc6206a32f492a34f,0x70a62006ca3140a2,0x4870e31406cc0088,0xf44870c62006ce31,0x3c01d06d00080a36,0x6d200887103140a])) (bI j 232 (cB [0x20871c3140a40029,0x692c0a3264a0a0c6,0xa4c94a0a4893e0a4,0xb0a5af440a50c3e0,0x6200a612500a5ef4,0x452500a4294a0a0e,0x871e62006d43140a]) (cB [0x140a4a02806d6008,0xe02806d800887223,0x6da00887203140a4,0x887243140a520370,0x2500a56f4a0a54c3,0x1662006dc3140a59,0xa56c480a5d250a7]))))))))) (bI j 349 (bI j 291 (bI j 262 (bI j 247 (bI j 240 (bI j 236 (bI j 234 (cB [0x200a4433506de314,0xd2500a58f4a87266,0xa6402906e00080a5,0x5872e3140a6602b0,0x32b0a6a32a877631,0xec33f89ec3330a6e,0xa7092c0a10620a9]) (bI j 235 (cB [0x382a4c93e0a4c932,0xec490a78c3f0a72c,0xa7ef492a72f440a7,0x80a683280a126202,0x92c0a6801d06e200,0x3062006e43140a6c,0x871462006e631487]) (cB [0x540a76f490a74f44,0xd2540a7cf540a7ac,0x72a31406e80082a7,0xa0a7ac4a0a80c388,0x3142a772500a7cf4,0x1492c871262006ea,0x2a5ac3e0a3494a0a]))) (bI j 238 (bI j 237 (cB [0x4b0a84f440a72c4a,0xc6200a8b2500a88f,0xa16c38871a92c06e,0xa74f4a0a36c4a0,0x6200a76c540a8725,0x18c38871892c06ee,0xa872502a5cf4a0a]) (cB [0x370a8e03506f0008,0xa620872c3140a900,0xa386560a926340a1,0xc0a989320a489300,0x9562a509480a5093,0x9ec560a9cc380a78,0x2aa12560aa0f560a])) (bI j 239 (cB [0x540a5293c0aa355c,0x4c4806f20082a529,0x6f40080a972500a9,0x80a54c3c0a9a0280,0x9480a7a9542a54c4,0x969400a7c9542a56,0x2a58c540a58c480a]) (cB [0x140aa603506f6008,0x26540a1c62087283,0xa5e94a0a4c9304a3,0xa0aa8c380a7e9542,0x2500aa0f4a0a9ec4,0xf83140a80c542a89,0x8778621873262006])))) (bI j 243 (bI j 241 (cB [0x2ca9f064b89f063f,0xc4a0a60c3e0a1e9,0xaa2f4b0a8af442a6,0x7343142a8b2500,0x633877a621876262,0x464ba9f263f89f2,0xaa8293e8a82932ca]) (bI j 242 (cB [0x3f0aaec384aaa94a,0xef440ad0c4b0ab6c,0xad72502ad0f4b2aa,0xe873692c07366200,0xf444a8ac4aaa8ac3,0xb12500ab4f4b0ab0,0x873ac38073892c8a]) (cB [0x480ab32504a86f4a,0xc3146a5cc54ea5cc,0xac03350ab8334073,0x87606200ac23360,0x9488a7293c8a3493,0xc4c384aa2956aa72,0xaccf560ac8c560a]))) (bI j 245 (bI j 244 (cB [0x140acf55c2acd256,0xcc380aba33287543,0xac60300abf2500ab,0x4aa769480aca3340,0xc3c0abe6404a5895,0x74c548a74c488a36,0xad2335073e314aa]) (cB [0x4aca5a93cc74e620,0x4c384a60954aa889,0xaccf4a0ac8c4a0ad,0x4a449542ab52500,0x92d876492c074062,0xf494b89f493f877c,0xaa84c4a8a84c3ea9])) (bI j 246 (cB [0x500acef4b8ab0f44,0xa0290742008aab12,0xada32987423140ad,0xa8a3e63c0a3e6308,0x92c4aa4656aaa464,0xe29560ae294a0ade,0x8aeaf4a0aeac568a]) (cB [0x5c0b01257aad1250,0x66560a406244ad15,0xad355c0adcc564aa,0x7443140a426244,0x93c0a46930874462,0xa8956aaa894a8a46,0x8ae0f4a0ae0c564a]))))) (bI j 254 (bI j 250 (bI j 248 (cB [0x544ad555caad5250,0x402807460084a809,0xae632887483140ae,0x88a4c63c0a486300,0xc564a9e656aa4c64,0x4a3184ac955c0ae8,0x8a4e3304acb2500a]) (bI j 249 (cB [0x84a7a654aa4e33c,0xc336874c314074a0,0xa326300aee3370ae,0x4aaa064a8a5063c0,0x94a0ae092c4a7e65,0xf4f4a0af0c380ae8,0xaff255aacd2500a]) (cB [0x3c0af20248a52648,0xc654aa7c6488a549,0xafd2540af6c404a7,0xc0afa6320af86300,0xf54ea566548a5663,0x5e63c0a5e6300afc,0x6a5e660ea5e6548a]))) (bI j 252 (bI j 251 (cB [0x88afef540afec60,0x602b0b0402907500,0x77e31587663140b0,0x90b163280b123278,0x32b0b2a32a0b2632,0xf634b89f633f0b44,0xb4a6260a26624a9]) (cB [0x4a8a8c63e0a62630,0xc92c4a62654aa8c6,0xae293e0b5492d0b4,0xbaae294a0b5893f8,0xc4a0aeac3e2b5894,0x5ef4b8ab6f442aea,0xaab72504aeaf550b])) (bI j 253 (cB [0x540a646246aeb255,0xc33c0b083284a646,0xa666300b0e6240b0,0x84a666600b1063c0,0x3540b0a3240a6831,0x146340b0a3284a68,0xb1802607520080b]) (cB [0x3f0b1e9330b1c92c,0xc3f8ab8c382b1e9,0xb1a932aab8f440b2,0x48abac382b1a93e0,0xf448abcc38aabaf4,0x220340b1a030aabc,0x89fa33e0b246300b])))) (bI j 258 (bI j 256 (bI j 255 (cB [0x4a8a8e63ea9fa34a,0x8c4a0b28c3eaa8e6,0xac12508ac0f442b2,0x20b0801d0756008a,0x3240b323180b2c03,0x6a3540b363320a6a,0xb3a63e0b386204a]) (cB [0x4a0aec93e2b3a64a,0xc3f0b3ec382aec9,0xac2f442b40c4b0b4,0x4aecf550b42f4b8,0x94a6aed255aac325,0x2f2550b30c4a0b2e,0xb0a01107580084b])) (bI j 257 (cB [0x240b3c01c0b3492c,0xc6540a6c6300b346,0x9fc34a0b143244a6,0xb46624a9fc3568,0x6568a9064a0a6e63,0xeec4a4a6e660aa90,0xb48f4a2aeec560a]) (cB [0x614aef2612b48f56,0x1d075a0086aef5,0x76a3140b0e0290b1,0x90b463290b323288,0x3e0b500240b4e01,0x5c3142b5204a0b52,0xa70930876c62007]))) (bI j 260 (bI j 259 (cB [0x54aa9c94a8a9c93e,0xc4a0af0c3e4a709,0xaf0f558ac4f442af,0x46af1255aac52504,0x932876e620075e31,0xc6c382af293e0af2,0xaac6f444af2c498a]) (cB [0x340b560186af2f49,0xc3280b5a0280b386,0xa986480b3a3340b5,0x8a9a33c0b3c01c8,0x3288b420428b2004,0x386240b4232a0b20,0x8a3863c0a786300a])) (bI j 261 (cB [0x60aa786548a78648,0x69410b609404a786,0xae89488b669420b6,0x80ae8c3caae89548,0xf602af4c540af4c4,0xf55604af52604ae8,0xb6463e0b6263c6a]) (cB [0x542af69480af6930,0x89306af72544af6c,0xaf8c482af893c0af,0x40afa9306af8f484,0x1e0b686486afb25,0xde31f07803140b6c,0x883c621832262009])))))) (bI j 276 (bI j 269 (bI j 265 (bI j 263 (cB [0x4b2c5c63f0c5c633,0xcc380cc894a0ca66,0xe04c4b0d9ac3f0d8,0x2e04f4b2d8cf440,0x31407820080e1125,0x6e333886e315883e,0xb7a34b2b6e33f0b]) (bI j 264 (cB [0x320b946210b7c620,0xa63e0bba6330b9a6,0xbda64a2bba63f2b9,0x80bee94a0be664b0,0xc4b0c3cc3f0c30c3,0x54f4b2c30f440c54,0x78a0080c5b2502c]) (cB [0x560b7292c0b70011,0x955c0b76c560b749,0xb7e03e0b7e0320b7,0xf0b72633078c3142,0xc380b8094a2b7263,0x90c4b0b8ec3f0b88,0x2b90f4b2b88f440b]))) (bI j 267 (bI j 266 (cB [0x380b8292c0b93250,0x4f440b86c490b84c,0x78e6202b86f492b8,0xb8af440b84c4a0,0xf440b869540b8d25,0x9693e2b8d2500b8c,0xb98f442b9694a0b]) (cB [0x1f07900082b99250,0xe62088403140b9c0,0xba294a0ba063e0b9,0x40bb0c4a0baec3e0,0x2500bb6f4b0bb2f4,0x4262007923140bb9,0x8844314079400888])) (bI j 268 (cB [0x480ba492c884c314,0xcf490baaf440ba8c,0x8483140ba6c480ba,0x407960080ba692c8,0x9488846314884a31,0x5062007983140ba8,0xbb52500baac4a88]) (cB [0x50884e6200bac954,0x1d079a0080bb52,0xbbc62088523140b7,0xc0bc06560bbe64a0,0x9560bc294a0b9692,0xd2f4a0bccc560bc6,0xbd72500bd4f560b])))) (bI j 272 (bI j 270 (cB [0x4a0bc4f480bd955c,0xef4a0bcaf540bc8f,0xbc49480bd0f540bc,0x40bcec560bc89560,0x3140bd0c540bca95,0x7433f0b743338854,0xbdec380bdc6202b]) (bI j 271 (cB [0x440be4c490be2c3f,0x66202be4f492bdef,0x8583140be0f44885,0xe2bc064a0bc063e8,0xf442bc694a0bc693,0xecf550beaf4b0be8,0x2bed2552be92500b]) (cB [0x482bc89540bc8948,0x32788683140bca9,0xb763330bf232a0bf,0x70b806202b7633f0,0x6320c0062a0bfe62,0xa263e0bcc6330ba2,0xc0692c2bcc63f2b]))) (bI j 274 (bI j 273 (cB [0x3f0c129330c1092d,0xec3f0c16c382c129,0xc16f440c2ac490c1,0x80bf46202c2af492,0xc490bf8c3f0bf6c3,0xfcf492bf6f440bfc,0xc02c380bfb2542b]) (cB [0x492c02f440c04c49,0xa6200c080192c04f,0xba49320b8292c886,0x90c0ac382ba493e0,0xf492c0af440c0cc4,0xa693c0c0e6342c0c,0xc140280bf46340b])) (bI j 275 (cB [0x2c0bf6636885c620,0xa93e0c029360b849,0xc18f440c0ac382ba,0xa0c1c6400c1af490,0x63d0c203360bf832,0x229352bce6490bce,0xc28f540c26c540c]) (cB [0x540c24c542c29254,0x43140c249352c252,0xc2c3340bfc32a886,0xc0c0462a0b866200,0x64a0bd063d0ba863,0x2ec380c0c92c2bac,0xc28f4a0c26c4a0c]))))) (bI j 283 (bI j 279 (bI j 277 (cB [0x440c0e6202c1b250,0xa620079c3142c1cf,0xb9892d0b8892c885,0xa2bd693f2bb293e0,0xc4a0be894b0bde94,0x36f4b0c32f440c16,0x79e6200c3b2500c]) (bI j 278 (cB [0x4a0b8ac38886092c,0x52500c18f4a0be0c,0xc1ac540c386400c3,0x8885e92c0c1c9480,0x2502bb4c4a0b8cc3,0x3e03507a00080c35,0x88663140c420370c]) (cB [0x200c483360c46334,0xe6310ba06300b8e6,0xbae63c0c4a6340bb,0x92bae6480bd263d0,0x6570be26562bd264,0x4cc380c1e9560bea,0xc50f560c4ec560c]))) (bI j 281 (bI j 280 (cB [0x3c0c5355c2c51256,0x40290c443340c406,0xc269540c206560c4,0x488623140c289540,0x6310b906200c5633,0xd463d0bb063c0bc0,0xbe46542bb664a0b]) (cB [0x380c2a9540bec655,0xf4a0c4ec4a0c58c,0xc2c6482c372500c5,0xc2ec542c38f440,0x64b0b7863f886c62,0xb893e0b9292c2b78,0x2bb894a0bd893f0b])) (bI j 282 (cB [0x4b0c3af442bd894b,0xe01c2c3b2500c52f,0x7aa3140b6e02a0c5,0xc09e032b8b6e31d0,0xf4a0c90c5687aa92,0xa52570ca12508c90,0x7ac0088ca155c0c]) (cB [0x2087ac31409e2013,0x863e0c666210c606,0xc6864a0c6a63f0c6,0xe0c7494a8c6a64b8,0xf4b0c88f448c74c3,0xae3148c892500c8c,0xc6294a87ae62007])))) (bI j 287 (bI j 285 (bI j 284 (cB [0x500c64f448c62c3e,0xc95607b00088c652,0xc732560c70c560c6,0xa0c6e9540c6f2540,0x62087b23140c7602,0x7063f0c7862b0c62,0xc7cc3e0c7a92c0c]) (cB [0x480c84f490c82f44,0x66410c806410c7ef,0xc80c3c0c7ec480c8,0xa0c6492c07b43140,0x6410c8b2500c82c4,0x726550c726490c8e,0x8c84c480c849548c])) (bI j 286 (cB [0x1c8c86c3c0c86954,0x23360b7602a0c740,0x7b692c0c946360c9,0xc98f4a0c96c388,0x100c9f2550c9d25,0x7c01c0c7a3280c76,0xc7e01c0c9b2540c]) (cB [0x540c8401c0c82328,0x86200c883280c9af,0xc9cf568b7862907b,0xc0c8a6340ca355c0,0xf540c9ec600c8c01,0xb801e0ca801c8c9e,0xcba6200b7a02a0c]))) (bI j 289 (bI j 288 (cB [0x4b0cbcf44c7e492c,0x63142cbd2500cc0f,0xcae6320caa620c7e,0xf2cae63e0cb06330,0xc3f0cb2c382cb063,0xacc382cb2f440cb6,0xcac92c2cacf440c]) (cB [0x500cb23280cb4f44,0x601c0cb46340cbf2,0xcc46400cc20400cb,0xa0bee01e0cc66420,0x62183666200cca32,0x462b0cf26278886,0x2c9063f0c906330d])) (bI j 290 (cB [0x330d3292d0d1892c,0x2c382d3893f0d389,0xd82c490d4cc3f0d4,0x42d82f492d42f440,0x3198892315837031,0x923330cce3270ccc,0xcd06202c9233f0c]) (cB [0x3f0cd89330cd292c,0x2c3f0cdcc382cd89,0xcdcf440ceac490ce,0x83726202ceaf492,0xc490cd4c38837462,0xd6f492cd4f440cd6,0x83286200cda9542c]))))))) (bI j 320 (bI j 305 (bI j 298 (bI j 294 (bI j 292 (cB [0x490cdef440cd4c38,0x8f540ce4c540ce0f,0xce60342ce92540ce,0xc0cec335834c3140,0xc4a0cf0c380cd692,0xe12500ce8f4a0ce4,0xcf401c0cee93c2c]) (bI j 293 (cB [0x340cf831c0bf002a,0xe934888a92c0ccc3,0x88c3140d029350cf,0x888e3140cf63288,0x1c0cfc6490cfa62,0xf201c0d0092c0cf6,0xcfe62488906200b]) (cB [0x380d0692c0d02625,0xac4a0d0ac3e0d08c,0xd12f4b0d10f442d0,0x52d112500d16f550,0x9300bf43282d1725,0xef4a0d0c0340d00,0xbf801c0bf63280d]))) (bI j 296 (bI j 295 (cB [0x602d0ec540d0ec48,0xc01c2d155600d152,0xd1a0270d152560bf,0xd837a92c0c0632a0,0x93f0c96933889492,0x24c3f0d1ec382c96,0x2d1ef440d2cc490d]) (cB [0x340d1c01c2d2cf49,0xac380c0a6360c086,0xd22f490d20f44832,0x40d2af540d26c540,0x32a0d283342d2b25,0x2e935834e92c0c0c,0xd26c4a0d30c380d])) (bI j 297 (cB [0x282d232500d2af4a,0x32a0d340260c0e3,0x37c92c0cd06340c1,0xe0d360100d069358,0x6200d3a3280c1201,0x140120d406298376,0xd3c92c83783140c]) (cB [0x360c1632a0d3e949,0x292d832692c0cdc6,0xc9c93f0d10937887,0x90d44f440d1ec382,0x9420c186360d46f4,0x20f44832ec380cde,0xce06360c1a32a0d])))) (bI j 301 (bI j 299 (cB [0x380d48941832c92c,0xc3280d4af440d22c,0xce232a0c1e01e0c1,0xb888462183626200,0x6350d4e6330d1262,0x9863d0d5a6370d56,0xd2492c2c986490c]) (bI j 300 (cB [0x380d649370d60935,0x2c540d70c390d6cc,0xd7ef540d78c550d7,0xc0d5001c2d7f2540,0xf540d546340d5231,0x5cf600c2001c0d58,0x2d5d5600d5f2600d]) (cB [0x540d62c540c2201e,0x6c600c2401e2d632,0xd680340d6b5600d6,0xe2d6f2540d6ef540,0x32a0d740340c2601,0x2692c83446200ce4,0x83423140ce601e0d]))) (bI j 303 (bI j 302 (cB [0x340d76c380d28620,0x69410d7c6350d7a0,0xc2801e0d686290d6,0xb83486200ce832a0,0x6490d5c6370d1462,0x629350d2a92c2c9a,0xd80f440d6ec380d]) (cB [0x200cea32a0c2a01e,0x662b887a621834a6,0xc9e64b0d846350d1,0xa0d8ac380d2c92c2,0x2500d7ef4a0d72c4,0xec32a0c2c01c2d47,0xd86f4a0d2e92c0c])) (bI j 304 (cB [0x2a0d880402d49250,0xc92c0cf06360c2e3,0xd80f4a0d30c38833,0xc3032a2d4b2500,0x92c09f262b07ba62,0xa093f887092d8324,0xd42c4a0cbc94b2c]) (cB [0x500d92f4b0d8ef44,0xc92c0c326360d992,0x336c3809f493707b,0xa0cbec4b8876c398,0x9420d912500d44f4,0x3632a8332f440c34,0xd94941833492c0c]))))) (bI j 312 (bI j 308 (bI j 306 (cB [0x280d96f440d46c54,0xaf540d48c540c383,0x330c380c3a6360d4,0x2ca2c4b8874c398,0x340c3c01e0d9125,0xbe3140dac0360d9c,0xdb833509f631f07]) (bI j 307 (cB [0x2183506200dbc337,0xa6350dc0633887c6,0xc9063d0dd26370dc,0x60cc0657ac906498,0xc390de4c380d4c95,0xf8c570df2c560dee,0x2dff2560dfef560d]) (cB [0x1307c00080e0355c,0x2315835231409f80,0xc4a3350d9e333888,0xa0da2c380cc234b0,0x2500da8c4b0da6c4,0xc23140da00100dab,0xda5250835462007]))) (bI j 310 (bI j 309 (cB [0x4483586208356314,0xa31407c40080da4f,0xc943310dae325835,0x60db0956ac943498,0x2560db4f560db2c5,0xa00100db755c2db3,0x9fa31e0c3e01e0d]) (cB [0x1e0dbaf44835c620,0xe63509fc31e0c420,0xdc201c0c4401c0db,0xdc631c0dae0400,0x3340d4ec620dc894,0xa00340d509560dc4,0xdc401c0d529560d])) (bI j 311 (cB [0x3c0c4a0400c4601c,0xef560d569560dcc9,0xd589540dd155c0dc,0xa0dbe3350c4801c0,0x63c0dc86300dd434,0xd8948ac926548c92,0xd5a9620ddc94a0d]) (cB [0x620de12620ddef62,0xaf560dd69482ddf5,0xdd63482ddb2560dd,0xc0d5c9600dda9480,0x100d5e9600de204,0x4c32a0de80560de6,0x835e92c07c66200c])))) (bI j 316 (bI j 314 (bI j 313 (cB [0x56ac969498c9693d,0xb2560deaf560d6cc,0x7c83140ded55c2de,0x20d6ec5483606200,0x1e0d70c620df006,0x3e6200df40340c4e,0x83403140d7295483]) (cB [0x480df6c380d74648,0x400dfa0340d769,0xd789600dfc6350db,0xe0d7c9600d7a6540,0x6200db20360c5001,0x9e6490dde6378346,0xdeac380d7e954ac])) (bI j 315 (cB [0x2a0d80c540e00f44,0x63420daa3400c523,0xdd0941836492c0db,0x4ac9c9558c9c9490,0x6200c5401e0decf4,0x663588786218338,0xd829542ca464b0e]) (cB [0x4a0df2c4a0e0ec38,0x601c2d932500dfef,0xd849540e0893c0c5,0x2d952500e0af4a0,0x6480d869540e0c04,0x3a92c0c5832a0d88,0xe00f4a0d8ac5483]))) (bI j 318 (bI j 317 (cB [0x2c0c5a32a2d97250,0x93f889692d837e9,0xd98f44aca094b8ca,0x82d992500e02f4b0,0x1f0e1c01e0e1400,0xca3140ea603e0e98,0x82ec62009fe31f07]) (cB [0x3f0eac62787f6621,0x692c4eac64baca66,0xeee94b0ed493f0ec,0x4ed4f4b0f2cf440,0x6200e1603e4ec725,0xba63f882062182ee,0xe1801e0e1af44ac])) (bI j 319 (cB [0x2c882662182f4620,0xc008882892d82f69,0xe1e62087f831407c,0x70e346260e2e6210,0x63f0e5863e0e4462,0x4464b4e3464a0e66,0xe7a93f0e7092c4e]) (cB [0x4b0e96f440e8494b,0x3e4e712504e7af,0x2f062007d43140e2,0xb0e2893f0e2292c8,0xf4b0e2cf440e2a94,0x24f444e232504e28,0x7d66200e272500e])))))) (bI j 334 (bI j 327 (bI j 323 (bI j 321 (cB [0x500e24c3882f292c,0x32500e3094a4e252,0xe3662087fa3140e3,0x40e3a94a0e3864a0,0x2500e40f4b0e3cf4,0xfe31487fc3140e43,0xe3f250880262087]) (bI j 322 (cB [0x4a0e3f2508800620,0xa94a0e486560e466,0xe52c560e4e9560e4,0x60e5755c0e552500,0x94a0e50c540e4cc5,0xd80080e509540e4c,0x88043140e5a01f07]) (cB [0x3d0e5e92c0e5c620,0x2f4a0e6494b0e629,0x7da3144e5f2504e6,0x880862088066200,0x8880a3140e6125,0x68620880c31407dc,0x4e466560e466320e]))) (bI j 325 (bI j 324 (cB [0x560e4a9320e3092c,0xcc490e6ac384e4a9,0xe6d2560e6ec570e6,0xe4c93c4e6b55c4,0x92c880e6204e4c96,0x6a93f0e5e93e0e22,0x4e5694b4e4294a0e]) (cB [0x500e76f4b0e72f44,0x4c38881292c0e792,0xe752504e3ec4a0e2,0xa0e26c38881092c0,0x3140e752500e60c4,0x286200e7c3288816,0xe626480e466250e])) (bI j 326 (cB [0x2c4e406560e6c649,0x2c560e809560e7e9,0x8143144e7755c0e8,0xe8a32a0e863288,0x6250e386240e2a62,0x3a6300e8c6280e48,0xe6464a0e526310e]) (cB [0x554e3a6540e6e64b,0x94a0e9292c4e526,0xe952500e82c4a0e8,0xc0e88f444e832550,0x6340e90f440e8e93,0xde3140e909340e88,0xe2c92c881862007])))) (bI j 330 (bI j 328 (cB [0x330e3c9320e3292d,0x494b4e3c94a0e549,0xe94c4b0e72c384e5,0xc881a6204e732500,0x94b0e9e94a0e9a92,0x9d2500ea52500ea2,0xea092c881c6200e]) (bI j 329 (cB [0x1e0e9cc38881e92c,0xa62182f86200ea80,0xeaa620882c314882,0x70ec12500eae01c0,0x6208ec155c0ec525,0xb663f0eb463e0eb0,0x8eb664b8eb464a0e]) (cB [0x500ebef4b0ebaf44,0x32500eb2f448ebb2,0xeb292c0eb89568eb,0xc0eba3280ebd2500,0x1c0ebc6340ec355,0xfa92c0e7032a0ebe,0xacbc93f882e92d82]))) (bI j 332 (bI j 331 (cB [0x4b0ec8f44cec094b,0x26360ed32500eccf,0x832c398302c380e7,0x20ecb2504ec2c4b8,0x32a82fef440e7494,0xce941830092c0e76,0xe786360ed0f440e]) (cB [0x4b8830c3982fcc38,0xa01e0ecb250acbec,0x838621831c6200e7,0xc4ec46570ed66298,0xc560ee29560ede92,0x7c01c4ecd55c0ee6,0xedac3c0ed89560e])) (bI j 333 (cB [0x2a4ecf55c0edcc56,0xc56831e92c0e7e3,0xe8001e4ed155c0ee,0x483146200ee40280,0x360e8201e831631,0xd862983186200ee8,0xee092c0eea6370e]) (cB [0x280e8401e0eecc38,0x46200efe02a0ef00,0xf086278834621830,0xb0f1862b0f106290,0x92d0f1c92cacc064,0x2694b0ee294a0f24,0xf2b2500ee6c4a0f]))))) (bI j 341 (bI j 337 (bI j 335 (cB [0x1583063144ee7255,0xc3290ef232788363,0xef492cacc433f0e8,0x40efa93f0ef893e0,0xf4483086200efcf4,0xc620830a3140ef6,0xef6c380e9063583]) (bI j 336 (cB [0x4a0f00319830e314,0x4c4a0ee894a0f026,0xee92550f072500f0,0x40f000340f0a01c4,0x1c0f0c3280f0e93,0x8c0340e8601c0f0c,0xf14c4a0f12c3c0e]) (cB [0x400e883280f17250,0xe6240e8a01c0e903,0xf1af480eeac560f0,0xa0f1e0104eeb5610,0x92c0e9232a0f2004,0x232500eecc4a8310,0x83126204eed2550f]))) (bI j 339 (bI j 338 (cB [0x2a0f020340f28028,0x63360efc3340e943,0xf16935831a92c0f0,0xa0e1a3140f22c380,0x6200ea432b0e9632,0x2092c0a0462b07e8,0xec0933883a92d83]) (cB [0x4b0ec8c384ec094b,0x3144ec92500f2ac,0xaac31f0898315038,0xf2ec63330ec63270,0x62185246204e1033,0x8c6338d8c6278984,0xf3092ccf2c63fad])) (bI j 340 (cB [0x380fe493f0f3c933,0xf442fe4c3f2f30c,0x89a62103826200ff,0xf2ec86330aae62b0,0x92d838292c4d9863,0xc893fad98933889a,0xf36c3f0f32c38ce]) (cB [0x2d038492c8f32f44,0x93f0ab0937089c9,0x8a4c39838ec384d9,0x80f34f44cecac3f8,0xc43089ec390386c3,0x9ef458386f440ab2,0x8a0621038862088])))) (bI j 345 (bI j 343 (bI j 342 (cB [0x2c0f386350ab462b,0x893588a092d83889,0x8a26200f3ac388f3,0x8038c92c838a92c0,0x3150390314838cc3,0x3e3270ab631f08a6,0xf6832b0f4e3290f]) (cB [0x2185006204e0234b,0x46290f7c62789766,0xd426310fa462b0f9,0xccf2a64bad4263d8,0x94a0fc892d0fb292,0xdcc4a0fd694b0fce,0xfe32502fdcf4a0f])) (bI j 344 (cB [0x2c0f446340f4032a,0xd55c0f4a93584969,0xf4231e0f423340f4,0xf46c38848a6200,0x3140f489400f4925,0xc031f0ab831e08a8,0x896062184ac6200a]) (cB [0x4b0f586370f50633,0xc390f5cc38cf166,0xf64c4b0f62c4a0f6,0x80f5201c0f672500,0xc480f549400aba32,0x5af540f546300f56,0x3a86200f566300f]))) (bI j 347 (bI j 346 (cB [0x50849e92c0abc62a,0x862008aa3140f5f2,0xabe62a08ac620c4a,0x40f5ef4484ae92c0,0x3240ac231e08ae31,0x6a62584be6200f44,0x8d106310f6e6290f]) (cB [0x560f7092cad10649,0x6f440f74c560f729,0xf752560f78f560f7,0xf6c01c0f7b55c2,0x1c0f486300f4663,0x8231c03943140f7e,0xf6a3350f8831d0f])) (bI j 348 (cB [0x80f9355c0f8a934,0x12500f6c02903960,0xf872500f846200f8,0xf8cc3803983140,0x280f8e0280f9125,0x866280f803284f80,0x39a3140f90c400f]) (cB [0x4b0f9633308b0315,0x8c38893c6204dd03,0xfa0c4b0f9cc4a0f9,0x39e6200fa32500,0x33503a03140f9b25,0xa2620c93a6200f9e,0xf9af44893e92c03])))))))) (bI j 407 (bI j 378 (bI j 363 (bI j 356 (bI j 352 (bI j 350 (cB [0x290f4a32503a4314,0xa62489506200f6e3,0xcdc6488cdc6300f8,0x60fa89560fa692ca,0xf560facf440faac5,0xb155c2fab2560fae,0xf8c930ace06480f]) (bI j 351 (cB [0x30acd49488cd493c,0xe9548cde93c0f909,0xfb60270fb401bacd,0xb0fbc04a0fb802a0,0x62103a66200fc004,0xec64b0ac462b08b4,0x896e92d84d492c4d]) (cB [0x4bad1e93d8d1e931,0x2f4a0fc2c4acf229,0x3aa3140fc72502fc,0xfbe01e0fbb2500,0x620c4d092c03ac62,0x3292c0fc463503ae,0xfba336ad2293dc4]))) (bI j 354 (bI j 353 (cB [0x3d84d6c3803b092c,0xa056ad20c498d20c,0xf7063503b26200fc,0xc0fa693584ea92c0,0x31503b43140fcd55,0xd03290ac831f08b8,0xc90e621c41e6200f]) (cB [0x1e08ba3140fd4629,0x2c38c4186200aca3,0x3b831403b63140fd,0xf723350fd83290,0x6350fda629c4fe62,0xbc31503ba3140fa8,0xf7432b0acc31f08])) (bI j 355 (cB [0x21c4526200fde335,0x663d0faa62bc91c6,0xfe0c380fc292cad4,0xdc3da62008be3140,0x6200fc492cad4863,0x4a93dc3fa92c03bc,0x8c062103be620ad]) (cB [0x350f4c6330ace62b,0x292c0f7a6370f666,0xf92933897892d850,0xd0fb09370fa29350,0xc38ad449498d4493,0xc03140fccc390fc6,0xad031f08c231503])))) (bI j 359 (bI j 357 (cB [0x202ecc33f0fe6329,0xa629c928621c46a6,0xfee92cad9263f0fe,0x40fdcc3e0fce93e0,0x31f08c43142f36f4,0xf6621c3ea6200ad2,0xfde93ead9463fc8]) (bI j 358 (cB [0x142f38f440fe8c3e,0x2314c3e862008c63,0xece33f08c831503c,0x40fecc3ec8e86202,0x62003c6314af38f4,0xcc62103c8620c8de,0x2ed063f0ad462b08]) (cB [0x3fc8fe92dc40492c,0xaf440fe0c3ead969,0x8ce62103ca6202f3,0xf0ed26330ad662b0,0x92d852692c2ed263,0x8e93f8d8e9338986,0xfe2c3f8f32c38ad]))) (bI j 361 (bI j 360 (cB [0x903cc008af32f44,0x401d0ad801308d00,0xe0404b2ed403f0ff,0xd88d031583cc3144,0x34bae0433f8ff431,0x4a63e102e620ced4,0x106494a904a64a10]) (cB [0x4bafe4f449064c3e,0x20084fe525010e4f,0x3ce3140ada01308d,0xbae0633f88ec3158,0x94a0ff693eced634,0xeaf44100cc3e0ffc,0x4fe72501024f4baf])) (bI j 362 (cB [0x1583e431408d4008,0x833d0ff832988f43,0xffa92ccedc34bae0,0x883e66204fe92500,0x3140adc01308d600,0xfe32b88f231583de,0xceda349ae0a33f0f]) (cB [0x441002c3e100092c,0x8314100af49afecf,0x8da00883e062008d,0x8ad8633d83d63140,0xf481008f481004c3,0xd831408dc0081006,0x8e00081006c3883]))))) (bI j 370 (bI j 366 (bI j 364 (cB [0x81008c4883e2314,0x31583d231408e20,0x10337100e33388f,0xaced834bad8433d1,0xc391014c38100294,0x1ef4a101cc4b101a,0xacec3484fdf25010]) (bI j 365 (cB [0x14acee33c101293c,0xe63d83d462008e43,0x16f4a1004c4aad2,0x810183404fc52501,0x4008e60081006c4,0x894883dc3141020,0x1022f441016c3810]) (cB [0x4008ea008101892c,0x834183ec31410260,0x1ec48100a954102,0x81020930102cf441,0x3141022f48102a94,0xde31f08f831503ee,0x4e0e34b2ede33f0a]))) (bI j 368 (bI j 367 (cB [0x3f88f862183ee620,0x94acede64bae0e6,0xfeef449030c3e103,0x44fef2501046f4ba,0x31f08fa31503f031,0xe033f103232b0ae0,0x83fe6204d8a3492e]) (cB [0x3f103462b88fc621,0x8c3e103692cae006,0x42f49afe0f44103,0x903f26204cf03541,0x314840092c4d3064,0xf46204d8034903f4,0x103a934ad8063d83])) (bI j 369 (cB [0x2003f6314103ef48,0x8314103c92c83f66,0x40f4483f862003f,0x1840262003fc3141,0xf44103ec48f02264,0x63141040f481044,0x8406620702c34104]) (cB [0x481042954f02c641,0x4c541048f449042c,0x4080089044f48104,0xd0ae201309000090,0x3144df204b104c01,0x5431d89083158412,0x105c94acee234b10])))) (bI j 374 (bI j 372 (bI j 371 (cB [0x1209020084fcf250,0xe92c84143140ae40,0x5294b105094a104,0x84fd32504fd12501,0x88416314090400,0xa3140ae6011040a,0x105a92c105664a89]) (cB [0x20040c0084fd5250,0x6009040e00810586,0x5e02b0ae8013090,0x5841a3144d720491,0x32b105631d890c31,0xe4054106292c1060,0x4d2634904103144c])) (bI j 373 (cB [0x81058629841c620,0xa013091000904200,0x6e02b10660270ae,0x44d820492ee603f1,0x31d8920315845631,0x9432b108a327900c,0x1030620adfe33f10]) (cB [0x2d10ac92c105c63e,0xec3e10c293f10c09,0xe2f49afdcf4410c,0x106c01e106801c1,0x314900e629845a62,0xea0540912008106a,0x901031d845c3144c]))) (bI j 376 (bI j 375 (cB [0x2010763331070329,0x892c105e64a10326,0x7cc4a107ac38107,0x5afab2501080f4a1,0x2551072f4a108525,0x7ef484cd63541075,0x10723294ce805410]) (cB [0x291083254107ec48,0x2f54108634d10743,0x4240081088f54108,0x41090634108c0110,0x110426008108e33,0x28008109292c108e,0xaee0130aec01104])) (bI j 377 (cB [0x4b10960331070029,0x23144d160552eea0,0x346201090324892,0xa109892c106064a1,0xc4a109ec38109a94,0xa6f4a10a4c4b10a0,0x10ab255af7525010]) (cB [0x481092630109cf48,0xc948107202910a2f,0xa925410a2c48109,0xf10a8f5410740291,0x3110b001b10ae00,0x14315042a31410b2,0x2eec33f0af031f09])))))) (bI j 392 (bI j 385 (bI j 381 (bI j 379 (cB [0x21845e6204d2c349,0xa63f901462989246,0x6293e103692cade,0x9afc2f4410b4c3e1,0x92c042c62010bef4,0x2a349042e3148460,0xad6e63d844a6204d]) (bI j 380 (cB [0x4810bac4910b6c38,0x31410b8f4810bcf,0xb8c38844c620043,0x9846262004343141,0xc48f016641901662,0x78335043631410bc,0x901a629846462010]) (cB [0x2904380081098635,0xc31d846631410c40,0x9a33510c8329901,0x810c6f4810caf481,0x31410c6029043a00,0xccc42109c335844e,0x43c00890baf4410]))) (bI j 383 (bI j 382 (cB [0x2b0af40130916009,0xe04990a603710800,0x916315843c3144d7,0xd908033710a632b8,0x92c1038620ad7e33,0xd893510d093410b4,0x10dc93790d893610]) (cB [0x4990b4c3810ca93d,0xe00810e0f4890cac,0xaf60130918009043,0x5843e31410d20270,0x62090d2327891831,0xd401e10d692c103a,0x8440620044031410])) (bI j 384 (cB [0x490442008103c92c,0xaf4884463144d620,0x448314044400810d,0x490ccc5410cc9488,0x9045000810df25,0x8202b0afc013091a,0x845031490a803710]) (cB [0x3710a832b891a315,0xc92c103e62090823,0xda93610da93510b,0x490bcc3810de9379,0x90454008703ef4,0x8402b0afe013091e,0x8926315846831410])))) (bI j 388 (bI j 386 (cB [0x4110aa32b901e31d,0xe92c1042620f01e3,0x42f4410e0c4810b,0x3092a009046c0087,0x41102401d0b0001,0x2a315846c3147024,0xf024341902431d89]) (bI j 387 (cB [0x4810e29541046620,0xe0087046f4490e2c,0xb02013092c009046,0xf114e01d10e801b0,0x330cc8025118a01,0xc80492eee03f0eee,0x898831585283144c]) (cB [0x1d11da31b8ea6319,0xa333128231f123a3,0x2c6620ad9a33f8d9,0x3904a63212f06211,0x63fb04a63e130663,0x6493e10649323306,0x1352c3f8f3cc3830]))) (bI j 390 (bI j 389 (cB [0x49af3cf445064c49,0x801e10ea01c7064f,0x12e32a1120328110,0x589ba621853c6201,0x62b1136629113062,0xc064b8dc063f113a,0x114293e113c92cad]) (cB [0x4a1066c3e314294a,0x8f4b8f7cf443066c,0xf7d2505066f55114,0x510ec3147067255a,0x31f0a2a31910f631,0xf833f10f83330b36,0x10fe63210fc62030])) (bI j 391 (cB [0x3e106893230fe63e,0x4c3f8f82c3830689,0xf82f445068c49110,0x10ee01d7068f49a,0x63e10f263210f062,0x6a93e106a93230f2,0x506ac498f84c3830]) (cB [0x1c706af49af84f44,0x3280a2c62410f43,0xf062010faf4a8da,0x810f2314110001c1,0x33d110262010f400,0x663430fa34910fa,0x110a32489bc31411]))))) (bI j 399 (bI j 395 (bI j 393 (cB [0x3e0b3632a110e325,0x620adc634a8dc63,0xa2e6251112624111,0xc311464a111463e0,0x94a111893e111692,0x6cc4a106cc3e3118,0x111cf4b8f88f4430]) (bI j 394 (cB [0x55af89250506cf55,0xc624110c620706d2,0x11a028899c314110,0xad523548d523481,0x3158542314111e94,0xc8333112232789be,0x112492cadc833f8d]) (cB [0x38312893f1128933,0xaf44112ac3f8f8ac,0x5446201126010af8,0x4af8cf448f8cc388,0xc388f8e92c854631,0x48314112c034af8e,0x110a028111201c85]))) (bI j 397 (bI j 396 (cB [0x2c113231c110e02a,0x4620899a314899e9,0x138c4a1138c3e113,0xcaf6b2508f6af443,0x2605be0100b3601,0x1632a10fc328113e,0x1140010854e92c11]) (cB [0x28111801e10fe01c,0x10854a62011443,0x54c314111a012110,0xc110231c114692c8,0x40111c01e110401,0x4e649112a328114a,0x114c940ad4e6558d])) (bI j 398 (cB [0x498d54331112c01c,0xe01e110601cad543,0xb040130932008111,0x789c031585503140,0x333115832b115032,0x5c92cadca33f8dca,0x1166932116292d11]) (cB [0x3f316693e1172933,0xcc3f8f94c3831729,0x152634af94f44117,0x43156c4a1156c3e1,0x930af972508f96f4,0x52324315493c1154,0x315ac48115ac3c11])))) (bI j 403 (bI j 401 (bI j 400 (cB [0x12115e0111154324,0xa62004c231405be0,0x160c3f8f98c38855,0x81164010af98f441,0x3158554314093400,0xcc331116832989c4,0x116c92cadce33f8d]) (cB [0x441170c3e116e93e,0xef44116a93caf9cf,0x9360088556620af9,0x4093800885083140,0x314ad5833d850a31,0x7494a11563318558,0x117af4a1176c4a11])) (bI j 402 (cB [0x481178f48afa1250,0xe03409400081178c,0x5063141180036117,0x98d5633d11823358,0x930116092cad5634,0x869341174931116e,0x117a93d117093c11]) (cB [0x38317a9493170948,0x2008118493c1188c,0x1200180b06013094,0x40cca024112e01a1,0x315855c3144cca05,0x9031b118c31989c6,0x119c331119231d11]))) (bI j 405 (bI j 404 (cB [0x4b8dd233f11a0333,0xe63e11a6620add23,0x1ae64a11c263f11a,0xa106e93e31c264b3,0xc3e11c4c38306e94,0xc6c4a11d2c3f11c6,0x8fa4f4431d2c4b31]) (cB [0x50506ef5511d6f4b,0xc024706f255afa52,0x18ec3e4ccc0540cc,0x8f4af44318ec4a1,0x110944008af4b25,0x9432489b03140b08,0xadbe34b8dbe33f11])) (bI j 406 (cB [0x3e307064a107063e,0x8c3e319694a11969,0xf6ef443198c4a119,0x5070f55119af4b8,0x87071255af6f25,0x726480b0a0110946,0x5073260307265410]) (cB [0x1109480087073560,0x46280b0c01d0b100,0x122024119e92c119,0xa4cce0600cce0301,0xc561076c4a8dd464,0xa2f5611a2f4a3076,0x7077561507726131]))))))) (bI j 436 (bI j 421 (bI j 414 (bI j 410 (bI j 408 (cB [0x1011a4c3c8dd6648,0xa31411a801e11640,0xcd03540cd0324094,0xe119e63185646204,0xc3e307894a107893,0xa6f4431acc4a11ac,0xafa72505078f558f]) (bI j 409 (cB [0x811aa6307079255,0x31d8560314094c0,0x1b664a11b462011b,0xa11bcc4a11bac381,0x930afa925011c0f4,0xbef4811b831c11b2,0x4de31411bec4811]) (cB [0x540cd23301124324,0xa93e85666204cd23,0x7ac3e31ba94a11b,0x58facf44307ac4a1,0x255afad250507af5,0x62314094e008707b,0x119631d118e31985]))) (bI j 412 (bI j 411 (cB [0x208dd833d11c8335,0xc94a31bc64a11ac6,0x1cec4a11ccc38307,0x5afaf25011d0f4a1,0x64811cac48707d25,0x7f254307e94831be,0xcd8024112801870]) (cB [0x4911a233d4cd8060,0x4c6011d49308ddc3,0x1a43314cda05451d,0xce2024112a0181,0x31d4ce206011d804,0xb663c8d5a349119a,0x31c065411c064811])) (bI j 413 (cB [0x541080948105e93c,0xc4811cec3c30809,0x5ef6031d0c5411d,0x8708156050812605,0x110952009047e00,0x1201f120801311dc,0x118c02911300250b]) (cB [0x3f0cf2031119002b,0x20552f0804b0f080,0x996620120c3144cf,0xa122462912126288,0x92c122a62b122862,0x2e94a122e93e122c,0x308ac4a108ac3e32])))) (bI j 417 (bI j 415 (cB [0x551234f4b8f3ef44,0xb255af3f250508af,0x1320240954008708,0x44cf80540cf80301,0x32911de328899831,0xf662011f432a11f0,0xa28625111262411]) (bI j 416 (cB [0x3e11f86310cf4630,0x465431fc64a11fc6,0x1fe92c51f86554cf,0xe320094a120093e1,0xf44308cc4a108cc3,0x8cf551204f4b8f40,0x708d255af4125050]) (cB [0x1411e00260956008,0x43190cf631811e23,0xcf634811e832611e,0xe108e63251e43494,0x93311ea92c308e63,0x42c3831ec93f11ec,0x508ec4911eec3f8f]))) (bI j 419 (bI j 418 (cB [0x48708ef49af42f44,0x432411f263011e66,0xcfa3540cfa330113,0x44cfc05411e26284,0x33411fa95411e433,0xee328120232811e6,0x120a634120694011]) (cB [0x14520e054120e030,0x2314121062804803,0x57892c0484314048,0x1095800904860088,0x19120a01311de01,0xe03312140270cfe,0x4cfe0492f0e03f0f])) (bI j 420 (cB [0x3e10906321210314,0xc933121a92c30906,0xf44c38321c93f121,0x45090c491220c3f8,0x1c7090f49af44f4,0x1694a11e031c11e8,0x3218c4a1218c3e12]) (cB [0x1d04883145217255,0x3490d0032511ea3,0x9293285786204d0,0x98f46c38309293e1,0xf49af46f445092c4,0x1803111ec0117092,0x11ee011121ef4a12]))))) (bI j 428 (bI j 424 (bI j 422 (cB [0x49121e93d1222334,0x11048c008321e9,0xd020250b1401d11f,0x81226c384d020550,0x31411f4011048e00,0xa092c11fe31d0490,0x1200011049200889]) (bI j 423 (cB [0x1104940081230628,0x4011123292c12020,0x2206281236340120,0x1122231c12389401,0x90498008120601,0x260130b16011095a,0x124a02b123c0270b]) (cB [0x142f1003f0f10033,0x833389aa31589a23,0x25692cadb833f8db,0x31260932125c92d1,0x93f326093e126a93,0x7ac3f8f4ec38326a,0xb1831caf4ef4412]))) (bI j 426 (bI j 425 (cB [0x4a1246c3e123e334,0x12508f50f443246c,0x2449321240930af5,0x8324493e324093c1,0x92caf54f448f54c3,0x1a31caf56c381242,0x123e02412483340b]) (cB [0x3c324c94a124c93e,0xc481254c3e1250c,0xf58f443254c4a325,0x4124ec48af592508,0xc38324e93e124002,0x42330af5af441252,0x1258032124402412])) (bI j 427 (cB [0x1d049c314325803e,0xa63385746200b1c3,0xf5cc38adba63f8db,0xeaf5cf44125ac3f8,0xf44325ec4a125ec3,0xa0008af612508f60,0xb28013095e00904]) (cB [0x3f0f12031126202b,0x492c89a43142f140,0x268c3e126693e126,0x4a2314af62f441,0x31404a400889a662,0x8031404a6008897e,0xb1e01104aa00889])))) (bI j 432 (bI j 430 (bI j 429 (cB [0x351246031126c029,0xe92c89a8314124c0,0x25ec38127094a126,0x1278f4a1274c4a1,0x281248024af6525,0x76c481276f481272,0xb2001104b000812]) (cB [0x34897c314127c035,0xa92c91d8336917e3,0x2709311266930125,0xd126893c91869341,0x9493268948127893,0x220101280c383278,0xb24010127e93c0b])) (bI j 431 (cB [0x11096200904b2008,0x60190b440130b2a0,0x19201d113a01b113,0xf12840330d040251,0x552f1804b0f1803,0xb831589ac3144d04,0x1224319121231889]) (cB [0x3f122a31b122831a,0x8620adbc34b8dbc3,0x2a263f128e63e128,0xe32a264b328e64a1,0xc38309494a109493,0xb2c3f12a8c3e12a6,0x32b2c4b32a8c4a12]))) (bI j 434 (bI j 433 (cB [0x5512b8f4b8f68f44,0x5255af692505094f,0xb2c31c0b3601c709,0x61096c4a12146240,0xf561286f4a3096c5,0x9756150972613286,0x128a012121862470]) (cB [0x250b3831d04b6314,0x66204d063550d063,0x9894a109893e89b,0x4328cc4a128cc3e3,0x2505098f558f70f4,0x403307099255af71,0xb3a01104b800811])) (bI j 435 (cB [0x2089b2314129001d,0xa94a129664a12946,0x29cc4a129ac38309,0x5af7325012a0f4a1,0x9300b3c010709b25,0x9ef48129801c1292,0x129ec48309c94812]) (cB [0x1412a401d709d254,0x83310b3e31d04ba3,0x58c6204d083550d0,0xe1226625121a6248,0xc3e329a94a129a93,0x76f44309ec4a109e,0xaf77250509ef558f])))))) (bI j 451 (bI j 443 (bI j 439 (bI j 437 (cB [0x1304bc008709f255,0x801d11380190b480,0x2aa0350d0a025119,0x44d0a0550f1a03d1,0x64a128c62089b431,0xacc3830a094a329c,0x12b0f4a12aec4a12]) (bI j 438 (cB [0x2570a1255af79250,0xe6484d0e0550d0e0,0xa325430a2948329,0xd12b40350b400117,0x956121c318128603,0x1e31812b725630a4,0x119a01d0b4201112]) (cB [0x184d120610d12025,0x663c918034012203,0x2a064812ba642129,0xe106093c32a06541,0x95410a694812c293,0xb0c4812aec3c30a6,0x32b0c5412b6c4912]))) (bI j 441 (bI j 440 (cB [0x615060f6032b6c55,0x756050a726052c2f,0x2bcc6012bc63070a,0x432c156012c0f605,0x63032bf25412bec5,0xc526012bc94012be,0x12be94032c556012]) (cB [0x1312ce01212c800f,0xa01f12d601b12d20,0x2e403312de03212d,0x432e403f32de03e1,0x31f096631504c031,0x1c3330d183250b4c,0x4d183492f1c33f0f])) (bI j 442 (cB [0x3389ce6218572620,0xc932ade463f8de46,0xfb2c3830ac93e10a,0x450acc4912e6c3f8,0x2a70acf49afb2f4,0x7e92c12cc31c12ca,0x30aec4a10aec3e85]) (cB [0x5050aef558fb6f44,0x62070af255afb72,0x58262000b8008858,0x412d0c3f8fb8c388,0x31412cc00cafb8f4,0x8492c12d4626096a,0x4c662012d801e85])))) (bI j 447 (bI j 445 (bI j 444 (cB [0x550d1a6310b4e629,0xc3e89d292c4d1a6,0xfb4f4430b0c4a10b,0x5afb525050b0f558,0x62004c831470b125,0xdc95412dc93089d4,0x89d692c04ca31452]) (cB [0x1412e203e12e001e,0x231f096c31504cc3,0x5866202f2033f0b5,0x4ade863f89d86218,0x314afbef44afbcf4,0xd2620852062004ce,0x10b2c3c858892c04])) (bI j 446 (cB [0x12afc125050b2f54,0x803412e203012d00,0xd2432504d831412e,0x4d2435592803350,0x63d9188635851e62,0x62930ad6c6498d6c,0x10b493c12ea93210]) (cB [0x5412eec3830b4948,0x4f5452eac555062c,0x4da00870b525450b,0x412ecc5485223140,0xc3c70bb25450baf5,0xb6f5430b6c4810b6,0x12f201270b725450]))) (bI j 449 (bI j 448 (cB [0x3e12f801e12f401a,0xc31432fc04a12fc0,0xb5431f097031504d,0x111a6329113c3250,0x34b0f2433f0d3233,0x8a6204d323552f24,0x122c62589da62185]) (cB [0x4b8dee63f1288629,0xe94a12fe93eadee6,0xc0c4a10c0c3e32f,0x51304f4b8fc8f443,0x255afc925050c0f5,0x64028047200870c1,0x128a629858e62011])) (bI j 450 (cB [0x1d04e031412f6012,0x4331113e3250b563,0x4e20084d343550d3,0x852c31411a80290,0x852fa65412fa63,0x9062004e631404e4,0x4e8314afcb25085]) (cB [0x29856e6201300329,0xc0088d7064913026,0xb58013097200904e,0x5132a01f130801d0,0x2b11ae029114202,0x2604b0d3803111c2,0x85683144d380552f]))))) (bI j 458 (bI j 454 (bI j 452 (cB [0x1f132e31d89ca315,0xe329122e32513363,0xdf834b12a232b128,0xc133a64a1338620a,0xc4a134894a12fe92,0xd7250134cf4a30c2,0x97400870c3255af]) (bI j 453 (cB [0x2411440180b5a012,0xa3144d3a0540d3a0,0x2a431f129031d856,0xadfc34b130a3331,0x932131064a130062,0x1ac3830c494a1314,0x5314c55131cc4a13]) (cB [0x55afdb250131ef4a,0xe628130cc3c70c52,0xd3e0541312f48130,0x4130c331131631d4,0x324130e3241318c5,0x3c3540d3c3301146,0x1320640ad7c3494d]))) (bI j 456 (bI j 455 (cB [0x4813126481322642,0x72541326c4230c69,0x325254132464870c,0xd532925413289485,0x1104ee008132c31,0x4002511b001d0b5c,0x89cc3144d400550d]) (cB [0x4a13026201230318,0x2c3830c894a13306,0xfd92501334c4a133,0xd123262470c9255a,0x32904f0314132c01,0x94629856c62011b4,0x133c01c04f200812])) (bI j 457 (cB [0x1411b6029134001d,0x631d134231c850c3,0x50e0081296329134,0x8133e92c12980118,0x92c11b801104f400,0x1001d04f60081344,0x8570314331002913]) (cB [0x483330329133031d,0x201d04f8008134af,0x51c3143312029131,0xd04fa00892ecf448,0x4311c0029131e01,0xa0329851a31492c2,0x134e940ad7834912])))) (bI j 462 (bI j 460 (bI j 459 (cB [0x48134a9481350942,0xb25492eaf4430cac,0x32001d04fc00870c,0x5132201d85183141,0x25430cc94892bc03,0x7a009050400870cd,0x114801b0b5e01309]) (cB [0x2511d601f117c01d,0xa03592340330d4c0,0xd4c05592b8037927,0xb897a31585043144,0x31f127a31d123431,0x7c335914833312b8,0x8d4c33d91d633791])) (bI j 461 (cB [0x2112e6620ad4c349,0xa632133a63113046,0x3606341354633933,0x7936e636136e6351,0x63d905c63c137063,0x4c649b05c648134c,0x934c932105c93033]) (cB [0x3830ce94810ce93c,0xcc549304c3992e6c,0xcef54d34cc55505,0xd135601c70cf2545,0x31d935631c135a01,0x58334135e940935a,0x135801c135c64013]))) (bI j 464 (bI j 463 (cB [0x1d935831c135c01d,0x20090510008935c3,0x3620330b60013098,0x5851031411860351,0x3359362333898231,0xd063c10d06249186,0x136cc3850d094830]) (cB [0x3d136401e70d0f48,0x294810d293013686,0xd325450d2c5430d,0x410d4930136663c7,0x254136601c70d525,0x126200512314136b,0x30d693c10d693085])) (bI j 465 (cB [0x870d6f4850d6c48,0xc0190b6601305140,0xd600550d60025114,0x123831985163144,0x930334e648134e63,0xd8c5430d894810d8,0xd6402570d925450]) (cB [0x3d12ba31d92ba035,0x63c135e6308d643,0x3509303350654135,0x30dc95410dc93c9,0x56050dcf60d350c6,0x70dd])))))))))) 28 (i % 16)
def zoN (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 78 (bI j 39 (bI j 19 (bI j 9 (bI j 4 (bI j 2 (bI j 1 (cB [0x400801000203f000,0x4621003310001802,0x3003802001801e00,0x1e4a001094a00819,0x4b007928005a4b00,0x3494003804c00c9,0x1998]) (cB [0x49258022620006,0xa92c0064a5808c94,0x800b3d1005987002,0x54668032c3f01592,0x3300692800ab12c0,0xea52807525803a9,0x4ab0])) (bI j 3 (cB [0x75e9403ac5601d,0xa0260244a5803494,0x901380a0090c5004,0x90054048c3802749,0x2a02461c01598a00,0x33d100912580486,0x61c0]) (cB [0xc987e00cf44030,0x403603231881980d,0xa01b804c00987006,0xe587c07263203818,0x4403c61c01c3d100,0x1b8c540dd87e070f,0x1998]))) (bI j 6 (bI j 5 (cB [0x8108c40082632037,0x263e0417a202130f,0x2020b0e011987c08,0xdde88092c380377a,0x3804b319025b0fc0,0x2780c8138036004c,0x3100]) (cB [0x141e880a0c3e050,0x8c3805461f027c94,0x2027c940151e940a,0x3de9609f2500587a,0x805c02502749401,0x2e30e0178c400b80,0x61c0])) (bI j 7 (cB [0x18987e0b8f44060,0xa02506431002700d,0x983249401958700c,0xa98700c804b06401,0x3f0649280353d101,0x2749401918960c8c,0x3108]) (bI j 8 (cB [0x1c58700e2030070,0x5607001f038494,0x982755701c1e880e,0xe24a00f0f4a07831,0x4407c32582755701,0x3fbd101f987009cf,0x9280]) (cB [0xc13a4a00fcf4b07e,0x6635083019041b0f,0xb041b15820d87010,0x2989609d55c0837a,0x5004e61c04518d42,0x47807823804e0052,0x18a0]))))) (bI j 14 (bI j 11 (bI j 10 (cB [0x23de8812092c090,0xef44093496049988,0x804b3d10258c4c11,0x3d25813263e08f92,0x5009b7a204da4b02,0x47a52c23d27e11f2,0x7a20]) (cB [0x828587014201f08e,0xa03e08e928050bd2,0x6052a4b0298c4014,0xa929614b2500a849,0x480ac19f84700a02,0x579880239e8815af,0x138])) (bI j 12 (cB [0x82c925815e01c0b0,0xf2500b27a205930f,0x5857bd202d927e15,0xe987c15e3280b84a,0x2108e7a2057b0e02,0x5f80f02f406417a6,0x61c0]) (bI j 13 (cB [0x2f409417af440bf,0xd2500bd7a505eb0e,0x20638070318c4e11,0x29e9418d2500c77a,0x5c0c692806319003,0x678070338c7e11d5,0x4960]) (cB [0x34987819ec3c0d0,0xcf480d461c06730e,0x206b2508359e9019,0x6987c1b292c08e7a,0x4a0da61c06d24d43,0x6fbd103664a01b4f,0x9280])))) (bI j 16 (bI j 15 (cB [0xc23a4a01b2f4b0d9,0xa92c0e3314871a4f,0x4073a55838de901c,0xa9e901d2c560e37a,0x440ec7a4071b1003,0x7700983b929611cf,0x140]) (cB [0x83b9e881e093e0f0,0xa92c0ee31487700a,0x7bbd283b80781e,0xe987c11d2500ee4a,0x370fa31a87d18cc3,0x7fb0e03e92661f46,0xc8])) (bI j 17 (cB [0x9e8811cc390fa,0xa92c1040078818c5,0x9882494041587020,0xc05021294b10449,0x3810c49608598804,0x85b0fc431e8821ac,0x4998]) (bI j 18 (cB [0x844129422092c110,0xa93f10b928088312,0x3881bd1042d25822,0x6129423262011831,0x4a1184a508d98f84,0x8fb0f847525823a9,0x49a0]) (cB [0xc461e9223af4811f,0x801b12431f881bd2,0x920c6c49003e24,0x90c4224803212831,0x3412c61f89218cc4,0x97803c4b862a0046,0x61c0])))))) (bI j 29 (bI j 24 (bI j 21 (bI j 20 (cB [0x4c929426202612e,0x2c4913261c09924b,0x809b3d104d987026,0xc4068272c3f13192,0x2712e928098b12c4,0x9755704f58ac27a0,0x190]) (cB [0x50125828203e140,0x12501437a20a1a4b,0x20a0252c50127e28,0xba4a029262612e7a,0x5014c4960a598c84,0x9718a05392962972,0x4960])) (bI j 22 (cB [0x545e882a2c38150,0x93415461f8a8494,0x80a824d05598962a,0x68c502b293312e92,0x4a15a49f0ad19285,0xaca4b0565e882b49,0x4a50]) (bI j 23 (cB [0x85658ac2b2956159,0xa94b12e9280acbd2,0x30b280a859404c2c,0xa52642d262816531,0x2c1653150b2b0e05,0xb7b0e04b9e882ca9,0x7a20]) (cB [0x5c40642e2c3f12e,0x26361713188b998d,0xa0bb8c6c0098702e,0xe24a02f200e17818,0x4a1779280bc01285,0xbfbd105f98702ee3,0x9280])))) (bI j 26 (bI j 25 (cB [0xc5de4a02fcf4b17e,0x8c3818419a0c1b0f,0xb0c1c94061189430,0xc038312c3818319,0x5618319a0c5b1586,0xc7b12c5deab8306f,0x61c0]) (cB [0x64864e005250177,0x893619461f0c9a4b,0x80ca3d2865187032,0x4e4a0332f4419392,0x3f1929280c9bd2c6,0xcebd2067925833a9,0x4ab0])) (bI j 27 (cB [0x6818783423281a0,0xaf481a462b0cebd2,0x20d31908699e9033,0xa865035294b1927a,0x441aa49f0d524b06,0xd498a46a4654352f,0x4960]) (bI j 28 (cB [0x6a5e9435201c1b0,0xa0331b461f0c9494,0xb8da00a06d403836,0xe52583726361b401,0x281bc4998da30e06,0xc930e46d18703686,0x7a20]) (cB [0x709258382620002,0xac3f1c27a20e1b0e,0x20e130e071526a38,0x2464e3929331c17a,0x341cb00e0e5989c7,0xe70cc4738c523929,0x61c0]))))) (bI j 34 (bI j 31 (bI j 30 (cB [0xc7264a039cc4a1ce,0x801a1d44960e498a,0x50ea01287500543a,0x2525a3932501d462,0x4b1c93148eda5287,0xe4b0e07798943929,0x9280]) (cB [0x4788c523c293f1c1,0x292c1e161f0f10cc,0xe8f3989c009e8838,0xa8c943d00251e818,0x481ec49f0f518807,0xf43d247a9e883d4f,0x49f0])) (bI j 32 (cB [0x87a1e943e092c1f0,0xf441f34960f9a52,0xf3bd2c7a1e883d,0xe52583f294a1f831,0x481fb49a0fdb0f87,0xfc3d247e5e883f2f,0x61f0]) (bI j 33 (cB [0x7e1e94400c38200,0xa63e1e77a58fc3d1,0x5102992881863a40,0x28c943ce92c2084a,0x4420b49f1058c748,0x530e083987c414f,0x7a21]) (cB [0xc84404e42294a1e7,0x232b21131a1098c9,0xf10b00c485925842,0x59e8842cf4821861,0x3f211496908bd248,0xfb0f8845e9043a9,0x49a1])))) (bI j 36 (bI j 35 (cB [0x88926a43e92c220,0xef4822449b10fbd2,0x490fbd2089987043,0x45e88422f4821f62,0x3322c61f0f3bd248,0x160cdc8b06664580,0x61c1]) (cB [0x48b1e94460031230,0xef4a22c62591630e,0xf8013d2c79de883c,0xe401047201b23831,0x2c23931491c80788,0x1c3d108e527c4729,0x18d9])) (bI j 37 (cB [0x904060482314240,0x892c24431412018a,0x512018a490187048,0x2927c48092c24031,0x1d2387a212018a09,0x27a4b093404a49a3,0x61c1]) (bI j 38 (cB [0x89452584a293224d,0xaf4425161f128a4f,0x212bb0e093526649,0x6863e470c3f24d7a,0x3e25a31012d00c49,0x2d30f89698704b46,0x7a21]) (cB [0xc98401c4c2620238,0xa01f26100d930803,0xf13380c89852604c,0x840664c2f4426701,0x3f2617a2135b0e09,0x3798848e00684dac,0x71]))))))) (bI j 58 (bI j 48 (bI j 43 (bI j 41 (bI j 40 (cB [0x9c803c4de01a26f,0xe93e26f01f13798c,0xe93b98cc8e1e884d,0xe8c944ee62027718,0x4827c4a513b8c709,0x3ba5009f9e944eef,0x9281]) (cB [0xc8e1e88502c38238,0x863c28419a941b0f,0xe14398c8a0d27850,0xd87051263428318,0x2428c31b14198d4a,0x41b150a392645066,0x61c1])) (bI j 42 (cB [0x8050520024290,0xa93300261c149a4b,0xf14b0020a5804e52,0x5926252c63529600,0x2529c01594ab0e0a,0x4f8c9ca552585383,0x81]) (cB [0xa88c6853e92c2a0,0xe63629f00e151b0e,0xc14f98a0a9926253,0xa406255232929561,0x332a931015598c4a,0x578caca558705526,0x1e9]))) (bI j 45 (bI j 44 (cB [0xabcc7a55e6252af,0xa6272957a2157a4b,0xc15a9880ad463a56,0xe925852ac562b561,0x1c2bc00795d0038a,0x5d18f0af80265743,0xd9]) (cB [0xcae803c5743282c0,0xa0272ba01315d007,0xf1630038b1925a52,0x280120020262c600,0x3e2cb004165806cb,0x67bd10b2d2585963,0x9281])) (bI j 46 (cB [0xcb4803c594f4b2cb,0x863e2d43191690cc,0xc1693d10b5187c5a,0x6987e5a4f442d861,0x382da01b16d00d0b,0x6f8128b7804c594c,0x41]) (bI j 47 (cB [0xb898705be0112df,0xa6212de61f96fbd1,0xb17280f8b940605c,0x7aab85caf442e502,0x502eb7a517598ccb,0x77992cb7aab85d72,0x7a21]) (cB [0xbc9e885e2c382de,0xd2502f17a5978c94,0xc17b18d4bd987e5b,0xd9eac5ecc562f661,0x352fc62596f5570b,0x654940b798705f86,0x191]))))) (bI j 53 (bI j 50 (bI j 49 (cB [0x8c08c4260031f300,0x4f4a30261c18100c,0xe183989cc024a060,0x1e4a0610f4430800,0x50307320185bd28c,0x8798fcc02ab860f2,0xe1]) (cB [0xc4187862292c310,0xac3830f61c189b0f,0x118bbd20c3de9062,0x69258600f443174a,0x4a31b49a98db0f8c,0x8fbd10c6a4a0636f,0x9281])) (bI j 51 (cB [0xcc024a0634f4b31a,0xa92c323314991a4f,0x4193a558c8de9064,0xa9e90652c563237a,0x4b3007a4191b100c,0x96bd10cb805065a9,0x3149]) (bI j 52 (cB [0xcc9e9465a92c32d,0xac3e300928196a50,0xc19a98dccd4c6a66,0xe8066594f4430061,0x4a33a92819d80a8c,0x9f8d28ce803867a0,0x7a41]) (cB [0x8ce8c54674f44340,0x525033a7a21a1bd2,0x31a38c50d1863c59,0x2126469064a34831,0x5034861c1a42528d,0xa730e0d3925868f2,0x9281])))) (bI j 55 (bI j 54 (cB [0x4d1929668e933347,0xcc383534991a98c5,0xe1ab2558d5864e68,0x652646b2333346aa,0x2035c3131a330e0d,0xaea4c8d740946ba6,0x4a51]) (cB [0x4d724a06bac3835d,0xa64a35c3199ae188,0xc1b2a4c8d94c406c,0xa92646b864b35c61,0x4a36a49f1b524b0d,0xb53d10da987c6d49,0x9281])) (bI j 56 (cB [0xdc46546e294a35c,0x8c4937161c1b8a4b,0x81bb3d10dd98706b,0xe8c686f2c3f35c92,0x5035c6259ae3120d,0xbf9880df8c6468d2,0x4961]) (bI j 57 (cB [0xdfd87c6fe93137f,0xa63e37e3139bf3d1,0x89c2a4b0e14c4070,0x292586fc63f37e49,0x4438a6251c530f8e,0xc7a4c4dfa4a0714f,0x4961]) (cB [0x8e3d29471e93e38f,0xa93f37e7a21c7b12,0xf1bf252cdf9e9072,0x19e886fcc3839861,0x4439c61c1cda4b0d,0xcdb0fce6e4a0738f,0x6259])))))) (bI j 68 (bI j 63 (bI j 60 (bI j 59 (cB [0xe8926668d25039b,0x49563a24a51d124b,0x81d13d28e898ac74,0xa865075294b34692,0x183ac1951d4b0e0e,0xd7a4b0ea4c4c7523,0x121]) (cB [0xec987068cf443a9,0x80363b461f9a33d1,0x21dbb0e0ed0c6476,0xe927c77231f2ca01,0x503ba7a51dd2528e,0xdcc940ef9e887732,0x7a59])) (bI j 61 (cB [0xf0863c7823262ca,0x4c383c33191e18c5,0xc1e39880f0866678,0x24c407926323c261,0x443c961f1e498f8f,0xe7b0e0f08c66784f,0x7a21]) (bI j 62 (cB [0x8f48c42782c3f3c2,0x2f443d23141e9a4f,0x1eb8c70f58c6678,0x5d87c7ae63e3d731,0x503d67a51eb3d10f,0xe0bd10f798707832,0x61f9]) (cB [0x8f818707c23343e0,0x401c3e461c1f00cd,0xa1f38c78f9866459,0x9de887d063e3e818,0x3e3e77a21f59880f,0xf398fcf9cc407da6,0x7a21])))) (bI j 65 (bI j 64 (cB [0xcf9a4a07e26213e6,0x4f443e618e1f998f,0x21fbb0e0fd8c4259,0xd987e7ed55c3f77a,0x1c3fc313965315cf,0xff18f8ff8c647fa3,0x61f1]) (cB [0x8ff64a07fcf443fe,0x6c38403310201992,0xc1fe992cff589280,0xf64a0810f4440861,0x503fd6259feb0fcf,0x7255903863c7f92,0xaae2])) (bI j 66 (cB [0x10480188226203fc,0x955c41102b208c94,0x21fe0c71058cac7f,0xf2ab88312504187a,0x573fc32020dbd2cf,0xf98ccb2aab87f8f,0x18e2]) (bI j 67 (cB [0x9084c40842626420,0x2c3c42449f210992,0x2210b0f908529484,0x80c4e8412504217a,0x3d42b49621598f90,0x1730f90b92588409,0x7a22]) (cB [0x10c927e84125042e,0xac3e4204a5a103d2,0xea0fbd1108187086,0xe5e94872c3841f18,0x4b41faae21cc9410,0x1fb15d07e4a887ac,0x2b2]))))) (bI j 73 (bI j 70 (bI j 69 (cB [0x90fcc6887f254440,0x80424447a520fc95,0x42230c7111867c88,0x1128488834244419,0x2c2ca92820fbd111,0x27bd1113987089a9,0x9282]) (cB [0x11392808a2f4b44e,0xa63445461fa26c94,0xb22a49411558948a,0x506788b293545431,0x5645400c22db0e11,0x2fbd59150c688bac,0x3202])) (bI j 71 (cB [0x118989689b55c454,0xa93546261f23198d,0x8226b0e11886788c,0xa86508d29332ca92,0x2c46c4a523524f91,0x363d211b987c8d89,0x7a22]) (bI j 72 (cB [0x11c987c8d4f4946c,0x4f4446a7a523930e,0x823b98a51a5e968d,0xdd8948ee95647701,0x2c46992823bb1591,0x3ebd291f58ac8fa9,0x9282]) (cB [0x920865090294a469,0xa95646962b240a52,0x8242bd2921465090,0x2466c912c5646992,0x4048c7a5244b0e12,0x44c9412264a8918c,0x92aa])))) (bI j 75 (bI j 74 (cB [0x1244684922f4a469,0x325046992b248bd1,0x324ba52cb2a4ae8d,0x6865092e62949801,0x3e49b49f24da4c92,0x4fb0e1269e88936c,0x7a22]) (cB [0x528865492ec3f49a,0x43314a21922518c7,0xf25118f9288c4094,0xa8c4e92ef444a261,0x344aa1942558c712,0x5700c12b8c5292e9,0x61f2])) (bI j 76 (cB [0x12c8c5692ef444ae,0x800c4b449624b80f,0x225a00f92d003a96,0xe927e92e92d4977a,0x504bc7a224b8ca12,0x5f8d012f9e9692f2,0x31e2]) (bI j 77 (cB [0xb2928097c93c4bf,0xac3f2ca7a2261b0e,0x9a6298d531806498,0x2806c98a01c4c801,0x1e4cc1992628c953,0x6618c133466099a3,0x318a]) (cB [0x534866898ac384cc,0xa6334d231026998c,0xea6b8cd931466a98,0x5cc4a9ae3294d701,0x374c549626b98f53,0x6f0c71378c6698a3,0x4a02])))))))) (bI j 117 (bI j 97 (bI j 87 (bI j 82 (bI j 80 (bI j 79 (cB [0x53840789c26354c5,0xa0484e431ba62a4f,0xc2628ca139926698,0xa00329d000c4e861,0x324e831e27580753,0x77804c00587298a0,0x13a]) (cB [0x93c00389e263f4f0,0xa94a4f3496279a4f,0x27bbd293cc0509e,0xe9e889e12504f302,0x404fc7a5a7849413,0x778d093f06809f80,0x19a])) (bI j 81 (cB [0x1401258a0294a500,0xa620504313277c94,0x4a83a4c9414094a0,0x14652a1294a50519,0x5050b7a2285b0e14,0x82b12d41587ea0b2,0x9282]) (cB [0x5448c66a08621504,0x801f514325282007,0xfa8a188145863ca2,0x51264a2862051418,0x3f5147a228db0e14,0x820075478c96a08c,0x4992]))) (bI j 84 (bI j 83 (cB [0x1485294a42029520,0xa93e520496290494,0x4293a529480050a4,0xa406ea52c3e52001,0x505297a5294b0e14,0x9049414b9e88a412,0x7a5a]) (cB [0x54c9294a09250520,0x4328534015a9900a,0x5a9924b14d8654a6,0xe9870a6492c53219,0x3f5327a4a9d3d114,0x993d514f58a8a7ac,0x624a])) (bI j 85 (cB [0x1509870a08c38540,0x4f4b5429282a1bd1,0xaaa3b0fd4124a0a8,0x28c68a8e03754701,0x325479282a531215,0xa3b0e151c050a9a9,0x62b2]) (bI j 86 (cB [0xd412ab8a8ef56547,0x8c3855301aaa9b12,0xc2aba4b13be4a0a0,0x624a0ab2f4455861,0x3455c61faabbd2d5,0xaeb0e1574664aba3,0x9282]) (cB [0x157066cab833555c,0xac5655c0182b1b0e,0xe2ae3d59570668ac,0xa466aad2c4b557aa,0x334ef9282abb0e15,0xb6b1595b8052ada9,0x4962]))))) (bI j 92 (bI j 89 (bI j 88 (cB [0x15c9294adac56570,0xac565721942b900a,0xbabb0cd95d98acad,0xd8048af2c3857619,0x3057c6202bdbd295,0xbb49515ecc64af86,0x92aa]) (cB [0x56092969df25756d,0xa328584015ac100a,0x22c20cf1610648b0,0x2864eb0463c58431,0x2658c1942c118d16,0xc624b1631264b1a0,0x499a])) (bI j 90 (cB [0x1648068b22c3f58c,0x4c3e594194ac118c,0x52cb80c9658654b0,0x68630b2cc4a5974a,0x205961992cb24b16,0xcb0071678c7cb2c6,0x61c2]) (bI j 91 (cB [0xd609e96b2cc3f596,0x4f4a5a33122d18ca,0xcad3a4b1608c4cb0,0x807cb4e0245a700,0x3f58200c2d5a4b56,0xc10ca16b4050b5a9,0x7a5a]) (cB [0x96c4c78b629405b0,0x26485b44a0ad818f,0x9adb80796d803600,0xe1258b700115b819,0x5c5b862b2dc25596,0xdf98816dc696b6f5,0x192])))) (bI j 94 (bI j 93 (cB [0x1705258b8294a5bf,0xac385bf624ae0b0e,0xfadfc941715e88b8,0xde4a0b7ec4b5bf61,0x445cb49f2e598856,0xe7007d738c64b6ef,0x3102]) (cB [0x1749294b9c63e5ce,0x4c485d26242e9a4b,0xf2e73d25749e88ba,0x69e88b9cc4a5ce61,0x505ce7a5ae749417,0xef1881778c66b6f2,0x3252])) (bI j 95 (cB [0x1789294bbc6565de,0x8f4a5e44ab2ef3d2,0x52f3b159779ea8bc,0x79e94bbcf545e77a,0x5c5de9282ef3d597,0xf718817b8c94b6f5,0x61c2]) (bI j 96 (cB [0x57b987ebdcf445f0,0x8f445f4325adbb12,0x52dbbd557d1e96be,0xe8654bf03275f84a,0x3f5fa61c2fd18817,0xfc31257ea4a8bfac,0x313a]) (cB [0x5805870c0262a5f8,0x80196044962fc312,0xa303b125811870c0,0x29266bf092d5f831,0x4460c61c2fc00a18,0xfc1901839e92c18f,0x61fa])))))) (bI j 107 (bI j 102 (bI j 99 (bI j 98 (cB [0x184926ac20336610,0xf5461062a308315,0xc30b0cd1859892bf,0x69e88c32c385b761,0x4061c7a5b0cc9418,0xfb0fd6de4a0c326,0x1ab]) (cB [0x188806ec3e63c620,0xe33661f19a30f8cd,0xb30fb0e187cc68c3,0xdeab8c3ef5661f62,0x3862b19a315b12d6,0x1798cd6da4a0b6ec,0xe3])) (bI j 100 (cB [0x18c5294c62620630,0x63e630310b183d1,0xa31ba5598d8c7ec6,0xc24acc6cc5663692,0x2b63b01531da5298,0x1fb0f98ed258c766,0x7a43]) (bI j 101 (cB [0x58ede88c76641640,0xaf44630320b21bd2,0xb23bd2d8c24a0c8,0x2466cc92c5662f32,0x4a64961c32498d99,0x24c9419264a8c9af,0x92ab]) (cB [0xd8beab8ca325062f,0xa01c654325adb495,0x932ab0e1958c40ca,0x69870caa63365531,0x1e65461fb2abd119,0x2fbd11950c40ca80,0x9283])))) (bI j 104 (bI j 103 (cB [0x1984080cc2f4b654,0xa94a5b6321330990,0x3b330c65998654cc,0xa9258ccc62066619,0x33666624b3530e19,0x37b0e19992a8cda9,0x7a23]) (cB [0x19c987ecccf4966f,0xcf5467201a339b15,0xe33b8cd59d9892cc,0xe8c4eccac3867649,0x1c67a19433d80719,0x3d19259f4c40cfa3,0x49a3])) (bI j 105 (cB [0xd99526acf492c680,0x6c3868349634198a,0x534300d1a1987cd0,0x29e96d06f446837a,0x2c6657aab41c981a,0x468071a3804ed1a9,0x61c3]) (bI j 106 (cB [0xda35e92d20f44690,0x633469462a349b0f,0xab4bb125a35ea8d2,0x6925accac3869749,0x3366500834d8099a,0x4f24b1a78650d3a9,0x4a4b]) (cB [0x1a89870cca62969d,0x89416a47a4b513d1,0x9b53b0fd995e88d4,0xa0638d5001c6a831,0x546ac31ab5398d1a,0x573d81ab8c6ed4ef,0x9303]))))) (bI j 112 (bI j 109 (bI j 108 (cB [0xda9d8a8d629356a7,0x60346b4630359a4d,0xa35bb0e1a9eac0d6,0xe98a8d4ec396a77a,0x556a761c35d80d1a,0x5398d5af4068d7ac,0x7aa3]) (cB [0x5b09892ccaf446c0,0x40406c47a536198d,0x2363b0e16d9870d8,0x29e96d8f2506c87a,0x506c77a23652505b,0x6780d1b3987eb6d2,0x199b])) (bI j 110 (cB [0x1b49870d9e0106d0,0xec4b6cf625367c94,0x2b6b80d9b3a4a0d9,0x5d8acdae9566d719,0x356ceaae36bbd59b,0x6f8cddb39e88dba3,0x31ab]) (bI j 111 (cB [0x1b88038dc26336ce,0xc9406e118e3708cd,0xb37324f1b98c6ad9,0xa8c6ed9d55c6e67a,0x486ea4a43758d29b,0x752529ba9eacdda9,0x7b13]) (cB [0x1b38098de32626ea,0x60566f3008379b0e,0xcb675571bcdeacde,0xe98acd9c0626f861,0x576ce61c37d80d1b,0x6718d5bf4068dfac,0x7ab3])))) (bI j 114 (bI j 113 (cB [0xd6daab8d9cf44700,0x893c70431ab81b12,0xc3818101c19e94e0,0x2804e0032505b661,0x1e70c01f3858021c,0x878079c29e88e160,0x3103]) (cB [0x1c49258e2003e710,0x93f7109283893d1,0xb87bd11c41296e2,0x3e4a0e3094a71831,0x4a71b31038d9899c,0x8fbd11c6d294e366,0x9283])) (bI j 115 (cB [0xdc3e4a0e36f4b71b,0x6656723325391989,0xb391b159c99294e4,0x8d8ace46c547284a,0x3e70faae391c941c,0x969881cb403ee5a6,0x4963]) (bI j 116 (cB [0xdcb527ae5b250730,0x862073431fb87a52,0xbb9a3125cd1870e6,0xe9e88e7292c70f62,0x507397a5b9cc941c,0x9f0ca1cf927ee1f2,0x4963]) (cB [0xdc3d8ace7c95673e,0x6f447441943a1a52,0xe3a398a1d0c654e8,0xd258e86f4474749,0x1f70a7a2387c941d,0xa6c941d39258e9a0,0x4a53]))))))) (bI j 136 (bI j 126 (bI j 121 (bI j 119 (bI j 118 (cB [0x1d35296e9a92c750,0xa01e75401f385494,0xe3ab989dc28c40ea,0x61e88eb262075800,0x5675c31fbac18f9d,0xac4941d79e88eb09,0x7a5b]) (cB [0xdd5eab8ec3250757,0xaf44764496385495,0xbb3bd2dd924a0ec,0x2a4a0ec8f447674a,0x5676c314bb5a4fdc,0xb5b159db1878ed89,0x4963])) (bI j 120 (cB [0x1dc92aced6c56770,0x803677462b3b580a,0x5b8530e1dd0c6eee,0xe464eef20287784a,0x3e7797a23bda4b1d,0xbc3d11de527eef29,0x153]) (cB [0x9e00c94f00319780,0xa6277789283c0312,0xa3c28ca1e18038f0,0x25878f1262977849,0x2b7789283c4b129e,0xc7a4b1de1e90f1a6,0x83]))) (bI j 123 (bI j 122 (cB [0x5de24a0f1e04a78f,0x287944a5bbc24b,0xbd11c2a4a0ef,0x69870f3292c79831,0x3579c61fbccbd11e,0xcfa4cde61870f386,0x193b]) (cB [0x1e80668f4232a7a0,0x12507a361c3d198d,0x4bcfd571e8126af4,0xa4038f526337a819,0x377a86243d5a501e,0xd7b0e1ea1ea8f5a6,0x9283])) (bI j 124 (cB [0xdea1894f50c397a8,0xa32b79f9283d4312,0x4bda8071ed8c4af6,0xd52acf6a92c7b531,0x567b57a23dab159e,0xdf989de7eab8f6af,0xe3]) (bI j 125 (cB [0x1f08638f7f2507c0,0xe31d7bf9283e1188,0x43e3b0e1f19268f7,0x7eab8f7f2507c601,0x387cb199be598a5e,0xe7b129f2e4a0f9ac,0x19ab]) (cB [0xde7e4a0f96c4b7cb,0x69567d34963e998a,0xb3e9bd11f4d8acfa,0x69258f3f55c7d37a,0x2a7da013bed006df,0xef8129f6a4a0fba0,0xf3]))))) (bI j 131 (bI j 128 (bI j 127 (cB [0x5f89894fb404b7da,0xa92d79f9283ed18d,0x53cfd571f940acfc,0xa1870fd23297e84a,0x297ec4a5bcf98a5f,0xf7b129e7cc52fd83,0x19ab]) (cB [0xde624a0f3ec387ef,0x6c3e7f4194bf9a4f,0x63f9b0f9fd8c52fe,0xe8c4e002f4479849,0x297fc49f3fd8075f,0xffa529fed258ff83,0x195b])) (bI j 129 (cB [0x200987cffe92c7ff,0xef488027a4401b0e,0x9c03b0f9fede92ff,0x1d27901233780719,0x4080c7a5405b0e20,0x3b12e01d87300e3,0x7a54]) (bI j 130 (cB [0xdfede89020040810,0xa341813020409bd2,0x3fd3d1204d29102,0x6465703294a81831,0x3e81949640c98ae0,0xea4b207926903ac,0x7a44]) (cB [0x2089e93032f44820,0x4f448247a5c0c3d1,0x64138076098c7cff,0x9929704e94a82749,0x2082c3254158c760,0x17a52a0992590566,0x15c])))) (bI j 133 (bI j 132 (cB [0x9fe925905e32b82f,0xa01c834013c19a52,0x5c19807a0d062906,0xe5e9507232983801,0x2c838199c1c49560,0x1fb12a0e18710709,0x7a44]) (cB [0x60e24a9082f4a838,0x6f548441a6c21c95,0xa423804611864f06,0xcd25909263484619,0x2c84b019c258cae0,0x25bd221392950969,0x61c4])) (bI j 134 (cB [0xe12de910a2c4a84b,0x72548547a5425b12,0x7c2ba4b20ce4ab09,0x5c0630ae01b85700,0x4885c61c42db0fa1,0x2bbd2216d8930b6f,0x7a4c]) (bI j 135 (cB [0x618927f06692d833,0x43298627a443180a,0xf419b10a199e910c,0xa804f0d293486861,0x35868496434807a1,0x37a4de1a1e910da9,0x92a4]) (cB [0xdfe9e93066f48868,0xa01b87431f800bd2,0xec3b8c521d80390e,0xe8c650ee62087700,0x3387618ac3b0c721,0x3b18821d9e950fa3,0x3194])))))) (bI j 146 (bI j 141 (bI j 138 (bI j 137 (cB [0xe1d8c4110201c880,0xa01e87531a441b0f,0x2c42988221864910,0x14c4910a62088519,0x3e88549644298fa2,0x47bd2e21405111a9,0x4a04]) (cB [0x224464f122328875,0x2933891008449a4b,0x543a80d225987f12,0x6863913262587519,0x3e89c314c3a98822,0x4fa4b21d4c570eac,0x134])) (bI j 139 (cB [0x228927d0ea0108a0,0xaf4b8754964518ca,0xec3a250229408114,0xa8c691523278a800,0x2b8a861f454a4c22,0x57a4b22a187915a3,0x8c]) (bI j 140 (cB [0x22c925b150c3f8af,0xa3298b4499454004,0xf45a24b22d127916,0xe9267150c3e8b449,0x488bc62545d252a2,0x5fb0fe2a1e95174f,0x1a4]) (cB [0x230866b17e0368bf,0x8c388bf49a45fa4f,0xf4638c6631803f0e,0x2863b18c31b8c661,0x3e8ca49f4650c923,0x678cc6319e97194c,0x4964])))) (bI j 143 (bI j 142 (cB [0x2349e951a23338c6,0xa01e8d431046330f,0xf46330fa350c611a,0x612611b231d8d831,0x1c8dc32546c18823,0x6fb12a3618711b03,0x7a44]) (cB [0x2318c7f18cf4a8d8,0xa3358e461f46330e,0x547230e23918911c,0xa987f18cf4a8e462,0x408ec7a5c6324c23,0x7780463b86370e80,0x1944])) (bI j 144 (cB [0x63c06291e00268f0,0x3268f03244798c6,0xfc7824ce3c12591e,0xbcc611f23298ef61,0x318ef3104778caa3,0x7798fa3bd2a91fa6,0x4964]) (bI j 145 (cB [0xe3bc65120293e8ef,0xa0138ee4a0481bd2,0x84838c523b8c6920,0x28c511dc62890701,0x3e90b4a5485809e4,0x87a4ce429259214c,0x7a54]) (cB [0x63b8669222c3f90a,0xc62a8ee61c48998a,0xf47724b23b8c571d,0xb925923262891849,0x4091b1a048dbd2e3,0x8f809e47863b0e89,0x19a4]))))) (bI j 151 (bI j 148 (bI j 147 (cB [0xa481259242930920,0xc33492461f48fa4c,0x4493a4fa49805723,0x99871252c3c92662,0x3292c49648f30fa4,0x97a4b647987f2580,0x61f4]) (cB [0x24c405726293291e,0xcc3e93149f498a4b,0x649b00a64d926723,0xd805127294a93649,0x4a9367a449db12a4,0x9f80d64f987f23cf,0x49e4])) (bI j 149 (cB [0xe50863f0e8c3893e,0xa6209427a54a180c,0xf4a130fa51402528,0x2126129201d94831,0x1c94c3254a418825,0xa7b12a5218712900,0x7a44]) (bI j 150 (cB [0x6548c7f284f4a948,0xac3e94261c4a1007,0x54aab0e255406b2a,0x6987f284f4a95562,0x4b94292b4ad00d65,0xaf98c2578c852baf,0x62a4]) (cB [0x258927d2baf6095e,0xa00f96431043a498,0x94b20c725940552c,0xa80272c8c3f96800,0x1e96c00dcb2189a5,0xb224c25b803f2c80,0x194])))) (bI j 153 (bI j 152 (cB [0xe59007d2e001e970,0x803497461fcb200c,0xc4ba31525d92652e,0xe40252f262187461,0x1e9790094bd806a5,0xbc80fa5e4c612fa0,0x49f4]) (cB [0xe5e4c53300329980,0xa01d984319c3a3d2,0x44c3b0f261866730,0x15e9131264a98531,0x5498b18ecc5a4ca6,0xc2b12a61587130ac,0x7a54])) (bI j 154 (cB [0x2648c85320640990,0x89489946214c8192,0xecc20c7665803f30,0x6187133064a99818,0x2098418fcc2312a6,0xcf8072678c953086,0x4964]) (bI j 155 (cB [0x268863933c01d99e,0xa94a98418eccf24b,0x4d3bd2a611e9134,0xa987f0e89429a74a,0x349ac00e4d598ce6,0xd599026b803b3563,0x4a04]) (cB [0xa6c80673626349aa,0xa63d9b231e4d9807,0xacd530e26c64a936,0x6379aa31]))))))))) 25 (i % 16)
def zjr := pageLinks zvy zsi 6 13 12 7
def zgV (i : Nat) : Nat × Nat :=
  let e := zoN i
  (e &&& 4095,e >>> 12)
def znT : Nat × Nat := (zmF,96)
def zuw := zr zca 96 (zD zcK zxf zoz 96) 12 zgV
def znB (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 11 (bI j 5 (bI j 2 (bI j 1 (cB [0xffffffff,0xffff0000ffff,0xffffffffffff,0xf0f0f00ffffff,0x33333300333333,0x3f3f3f003f3f3f,0x55555500555555,0x55555555555555,0x5f5f5f005f5f5f,0x5f5f5f5f5f5f5f,0xaaaaaa00aaaaaa,0xcccccc00cccccc,0xeeeeee00eeeeee,0xf0f0f000000000,0xf0f0f000f0f0f0,0xff00ff00ff00ff]) (cB [0xff00ffffffffff,0xffffff00000000,0xffffff00ffffff,0x1ff01ff11ff11ff,0x300030033003300,0x303030333333333,0x30f030f33ff33ff,0x333033333333333,0x3330333ffffffff,0x333333303333333,0x333333333333333,0x333ffff0333ffff,0x3ff03ff33ff33ff,0x505050555555555,0x50f050f55ff55ff,0x555055555555555])) (bI j 3 (cB [0x5550555ffffffff,0x555555505555555,0x555555555555555,0x555ffff0555ffff,0x5ff05ff55ff55ff,0xa0a0a0aaaaaaaaa,0xc0c0c0ccccccccc,0xe0e0e0eeeeeeeee,0xf000000ff000000,0xf000f00ff00ff00,0xf0f0000ffff0000,0xf0f0f0f0f0f0f0f,0xf0f0f0fffffffff,0xf0fffff0f0fffff,0xf3f3f3f0f3f3f3f,0xf5f5f5f0f5f5f5f]) (bI j 4 (cB [0xfff0fff0fff0fff,0xfff0fffffffffff,0xfffffff0fffffff,0x1111111111111111,0x1111ffff1111ffff,0x1133000011330000,0x1133113311331133,0x1133333311333333,0x1133ffff1133ffff,0x1155555511555555,0x11ff11ff11ff11ff,0x11ffffff11ffffff,0x1300130013001300,0x1313131313131313,0x1313131333333333,0x131313135f5f5f5f]) (cB [0x13131313ffffffff,0x135f135f135f135f,0x13ff13ff13ff13ff,0x1515151515151515,0x1515151555555555,0x15151515ffffffff,0x153f153f153f153f,0x1f1f1f1f00000000,0x1f1f1f1f1f1f1f1f,0x1f1f1f1fffffffff,0x1f3f1f3f1f3f1f3f,0x1f5f1f5f1f5f1f5f,0x2233223322332233,0x22ff22ff22ff22ff,0x3030303000000000,0x3030303030303030])))) (bI j 8 (bI j 6 (cB [0x30303030f0f0f0f0,0x3300000033000000,0x3300330033003300,0x3333000033330000,0x3333333300000000,0x3333333333333333,0x33333333ffffffff,0x3f3f3f3f00000000,0x3f3f3f3f3f3f3f3f,0x3f3f3f3fffffffff,0x4040404000000000,0x4040404040404040,0x4444444444444444,0x5000000050000000,0x5000500000000000,0x5000500050005000]) (bI j 7 (cB [0x5050505000000000,0x5050505050505050,0x5444544454445444,0x5454545444444444,0x5500000055000000,0x5500550055005500,0x5500ff005500ff00,0x5544444455444444,0x5544554444444444,0x5555000055550000,0x5555555555555555,0x55ff000055ff0000,0x55ff55ff55ff55ff,0x55ffffff55ffffff,0x7530753075307530,0x8c8c8c8ccccccccc]) (cB [0xa0a0a0a000000000,0xa0a0a0a0a0a0a0a0,0xa0ffffffa0ffffff,0xa5a5a5a555555555,0xa8a8a8a888888888,0xaa000000aa000000,0xaa00aa00aa00aa00,0xaa00ff00aa00ff00,0xaa888888aa888888,0xaaa0a0a0aa000000,0xaaaaaaaaaaaaaaaa,0xaaffffffaaaaaaaa,0xaaffffffaaffffff,0xacacacaccccccccc,0xacacacacecececec,0xaeaeaeaeeeeeeeee]))) (bI j 9 (cB [0xaf0faf0fffffffff,0xafafafafffffffff,0xb0b0b0b0b0b0b0b0,0xbbbbbbbbbbbbbbbb,0xc0c0c0c000000000,0xc0c0c0c0c0c0c0c0,0xc0c0c0c0f0f0f0f0,0xc0ffffffc0ffffff,0xc888c88888888888,0xc8c0c8c088008800,0xc8c8c8c888888888,0xcacacacaaaaaaaaa,0xcc000000cc000000,0xcc00cc00cc00cc00,0xcc333333cc333333,0xcc808080cc808080]) (bI j 10 (cB [0xcc888888cc888888,0xccc0c0c0cc000000,0xcccc0000cccc0000,0xcccccccc00000000,0xcccccccccccccccc,0xccffffffccffffff,0xcecececeeeeeeeee,0xcf0f0f0fcf0f0f0f,0xcf0fcf0fffffffff,0xcf8f8f8fcf8f8f8f,0xcfcccfccffccffcc,0xcfcfcfcfffffffff,0xd0c0d0c0d0c0d0c0,0xd5c0d5c0d5c0d5c0,0xdcdcdcdccccccccc,0xdd000000dd000000]) (cB [0xdd00cc00dd00cc00,0xdd00dd00dd00dd00,0xdd555555dd555555,0xddcc0000ddcc0000,0xddcc5500ddcc5500,0xddccccccddcccccc,0xddccddccddccddcc,0xdddddddddddddddd,0xddffccccddffcccc,0xe000e000e000e000,0xe0a0e0a000000000,0xe0a0e0a0e0a0e0a0,0xe0c00000e0c00000,0xe0c0e0c000000000,0xe0c0e0c0e0c0e0c0,0xe0e0e0e000000000]))))) (bI j 16 (bI j 13 (bI j 12 (cB [0xe0e0e0e0a0a0a0a0,0xe0e0e0e0e0e0e0e0,0xe8e8e8e888888888,0xea000000ea000000,0xea00ea00aa00aa00,0xea00ea00ea00ea00,0xeaaaeaaaeaaaeaaa,0xeac00000eac00000,0xeac0eac000000000,0xeac0eac0aa00aa00,0xeac0eac0eac0eac0,0xeaeaeaea00000000,0xeaeaeaeaaaaaaaaa,0xeaeaeaeaeaeaeaea,0xec000000ec000000,0xec00ec0000000000]) (cB [0xec00ec00a000a000,0xec00ec00cc00cc00,0xec00ec00ec00ec00,0xeca00000eca00000,0xeca0a0a0eca0a0a0,0xeca0eca000000000,0xeca0eca0eca0eca0,0xeca8a8a8eca8a8a8,0xecec0000ecec0000,0xecececec00000000,0xececececa0a0a0a0,0xececececcccccccc,0xecececececececec,0xee000000ee000000,0xee00cc00ee00cc00,0xee00ee00ee00ee00])) (bI j 14 (cB [0xeea0a0a0eea0a0a0,0xeeaa0000eeaa0000,0xeeaaaaaaeeaaaaaa,0xeeaaeeaaeeaaeeaa,0xeecc0000eecc0000,0xeeccaa00eeccaa00,0xeecccccceecccccc,0xeecceecc00000000,0xeecceecceecceecc,0xeee0e0e0ee000000,0xeeecececeecccccc,0xeeee0000eeee0000,0xeeeeaaaaeeeeaaaa,0xeeeeeeee00000000,0xeeeeeeeeeeeeeeee,0xf000000000000000]) (bI j 15 (cB [0xf0000000f0000000,0xf000f00000000000,0xf000f000a000a000,0xf000f000f000f000,0xf0404040f0404040,0xf0a0a0a000000000,0xf0a0a0a0f0a0a0a0,0xf0a0f0a0a0a0a0a0,0xf0c0c0c000000000,0xf0c0c0c0f0c0c0c0,0xf0c0f0c0c0c0c0c0,0xf0f0000000000000,0xf0f00000f0f00000,0xf0f0f0f000000000,0xf0f0f0f0f0f0f0f0,0xf0ffffff00ffffff]) (cB [0xf1f1f1f111111111,0xf3f3f3f333333333,0xf400f40044004400,0xf4f4f4f444444444,0xf5f0000055000000,0xf5f0f0f055000000,0xf5f0f5f055005500,0xf8a8f8a888888888,0xf8c8f8c888888888,0xfa000000aa000000,0xfa00fa0000000000,0xfa00fa00aa00aa00,0xfa88c888fa88c888,0xfaaa0000aaaa0000,0xfaaa0000faaa0000,0xfaaaaaaa00000000])))) (bI j 19 (bI j 17 (cB [0xfaaaaaaaaaaaaaaa,0xfaaaaaaafaaaaaaa,0xfaaac888c888c888,0xfaaafaaa00000000,0xfaaafaaaaaaaaaaa,0xfaaafaaafaaafaaa,0xfac8c8c8aa888888,0xfac8fac888888888,0xfaf00000aa000000,0xfaf0aa00aa00aa00,0xfaf0faf0aa00aa00,0xfafa0000aaaa0000,0xfafaaaaaaaaaaaaa,0xfafafafaaaaaaaaa,0xfc000000cc000000,0xfc00cc00fc00cc00]) (bI j 18 (cB [0xfc00fc00cc00cc00,0xfca0fca0eca0eca0,0xfca8a8a8cc888888,0xfccc0000cccc0000,0xfccc0000fccc0000,0xfccccccccccccccc,0xfcccccccfccccccc,0xfcccfccc00000000,0xfcccfccccccccccc,0xfcccfcccfcccfccc,0xfcecfcececececec,0xfcf00000cc000000,0xfcf0cc00cc00cc00,0xfcf0f0f0cc000000,0xfcf0fcf0cc00cc00,0xfcf0fcf0eca0eca0]) (cB [0xfcfc0000cccc0000,0xfcfccccc00000000,0xfcfccccccccccccc,0xfcfcccccfcfccccc,0xfcfcfcfccccccccc,0xfcfcfcfcecececec,0xfe00fe00ee00ee00,0xfeaaaaaaeeaaaaaa,0xfeaafeaaeeaaeeaa,0xfecc0000eecc0000,0xfeccfecceecceecc,0xfeeeccccfeeecccc,0xfeeefeeecccccccc,0xfefc0000eecc0000,0xfefcfefceecceecc,0xfefe0000eeee0000]))) (bI j 20 (cB [0xfefefefeeeeeeeee,0xff00000000000000,0xff000000ff000000,0xff00cc00cc00cc00,0xff00ff0000000000,0xff00ff00ff00ff00,0xff0f0f0fffffffff,0xff303030ff303030,0xff444444ff444444,0xff505050ff000000,0xff555555ff555555,0xffa0a0a000000000,0xffa0a0a0a0a0a0a0,0xffa0a0a0ff000000,0xffa0a0a0ffa0a0a0,0xffaa0000aaaa0000]) (bI j 21 (cB [0xffaaaaaa00000000,0xffaaaaaaaaaaaaaa,0xffaaaaaaffaaaaaa,0xffaafaaaffaaaaaa,0xffaaffaaaaaaaaaa,0xffc0c0c000000000,0xffc0c0c0c0c0c0c0,0xffc0c0c0ff000000,0xffc0c0c0ffc0c0c0,0xffcc0000cccc0000,0xffcccccc00000000,0xffcccccccccccccc,0xffccccccff000000,0xffccccccffcccccc,0xffccffcccccccccc,0xffe0e0e000000000]) (cB [0xffe0e0e0ffe0e0e0,0xffeca0a0ececa0a0,0xffecececa0a0a0a0,0xffecececffececec,0xffeeeeee00000000,0xffeeeeeeaaaaaaaa,0xffeeeeeeffeeeeee,0xfff0f0f0ff000000,0xfffafafaffaaaaaa,0xffff000000000000,0xffff0000ffff0000,0xffffaaaaaaaaaaaa,0xffffcccccccccccc,0xffffeca0eca0eca0,0xffffffff00000000])))))) 64 (i % 16)
set_option maxRecDepth 16000 in
def zjW (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 78 (bI j 39 (bI j 19 (bI j 9 (bI j 4 (bI j 2 (bI j 1 (cB [0x3fc,0x1afeb,0x1affa,0x3595bd9,0x3595bf9,0x35977ea,0x421afe9,0x419afe8,0xee419afa7,0x8335805e7,0x84358b3a8,0x1086b16005a7,0xee421afe8,0x35973e9,0x6b2e005e8,0x6b33177e9]) (cB [0x6b2e95bc9,0xd65d2b0b388,0x1acba561600587,0x1dc6b2e95bc8,0x6b2e8b3a9,0xd65d1604328,0x1acba2c0800a27,0x1acba2c0800527,0x2666b2e8b3a8,0x139358b3a7,0x26a6b2e8b3a8,0xd65d16005a8,0xe435977e9,0x6b2e8c7e8,0xe135977e8,0xe235977e8])) (bI j 3 (cB [0x1dce435977a8,0x266e43597768,0x1c86b2e80ae8,0xee35977e9,0xee3596fe8,0x1253596fc7,0x7a1afe8,0x799afe7,0xf43584367,0xf4771afe8,0x12535977c8,0x24a6b2e84347,0x24aee35977c8,0x6b2e8b7e8,0x1dc6b2e84368,0x6b2e84369]) (cB [0xd65d0800a68,0x13335977e9,0x9c9afe8,0x729afe7,0x139999afe8,0x6b2e84fe8,0x541afea,0xa83595bc9,0xa23595bc8,0x266a23595b47,0x1446b2b00ac7,0x1506b2b04348,0x2a0d6560800a47,0x266a83595bc8,0xa83595be9,0xa8471afe9]))) (bI j 6 (bI j 5 (cB [0x511afe9,0x3593be8,0x1333593b67,0x6b2700ae7,0x501afe8,0x133511af68,0xa23584f67,0xa23580ae8,0xa83584369,0x1506b0800a68,0x133541afe9,0x133501afe8,0xa83584fe8,0x3598bea,0x35983e9,0x6b3015bc8]) (cB [0x2666b3015b47,0xd6602b00ac7,0xd6602b005c7,0x1333598368,0x6b3004f67,0x2b5333598267,0x2666b3000567,0x6b3000ae8,0xd66001004e7,0x15a35983e8,0x6b30005e8,0x35987e9,0x411afe8,0x6b3095bc8,0xd6612b04347,0x6b3084368])) (bI j 7 (cB [0xd6610800a67,0x13335987e8,0x9d1afe7,0x6b3115bc9,0xd6622b14388,0x1acc4562804307,0x1acc4562800587,0xd6622b14fc8,0xd6622b157c8,0xd6622b04348,0x1acc4560800a47,0x1acc4560800547,0x2666b3115bc8,0x26a6b3115bc8,0xd6622b005c8,0x6b3115be9]) (bI j 8 (cB [0x6b31143a8,0xd6622804327,0xd66228005a7,0x6b3114fe8,0x6b31157e8,0xd6622b04368,0xd6622b005e8,0x8e3598be9,0x2668e3598b68,0x11c6b3100ae8,0x11c6b31005e8,0x943598be9,0x1286b3104368,0x6b3104369,0xd6620800a68,0x1acc4100100467]) (cB [0x2b46b3104368,0xd6620800568,0x1333598be9,0x1333597be8,0x14e3598be8,0x6b3104fe8,0x1323598be8,0x26b333598b68,0x2666b31005e8,0x1353598be9,0x14f3598be8,0x6b31047e8,0x6b31005e9,0x3599bea,0x539afe9,0xa73595bc8]))))) (bI j 14 (bI j 11 (bI j 10 (cB [0x14e6b2b0b387,0x14e6b2b00ac7,0x35937e8,0x6b268b3a7,0x6b2680ae7,0x4e9afe8,0x9d3580ae7,0x9d35805e7,0x521afe8,0xa4358b3a7,0xa7358b3a8,0x14e6b1600aa7,0x14e6b16005a7,0xed539afe8,0xee539afe8,0xa73580ae8]) (cB [0xa73599be9,0x14e6b330b3a8,0x266a73599b68,0x14e6b3300ae8,0x35997e9,0x6b3295bc8,0xd6652b0b387,0x6b328b3a8,0xd66516005a7,0xee35997e8,0x7b1afe7,0x6b3519be9,0x2666b3519a68,0xd66a3304e67,0x6b3315bc9,0xd6662b143c8])) (bI j 12 (cB [0x6f3595bc7,0xd6662b0b388,0x4ccd6662b0b307,0x1accc561600a87,0x1accc561600587,0x1da6b3315bc8,0x4cdda6b3315a47,0x1dc6b3315bc8,0xf73595bc7,0x2666b3315b48,0xd6662b04f47,0xd6662b00ac8,0x6b3315be9,0x6b33143e8,0x6b3314f68,0xd666298b327]) (bI j 13 (cB [0xd6662980a67,0x6b33153e8,0xd6662b0b3a8,0x2666b3315b68,0xd6662b00ae8,0x863599be9,0x4f1afe8,0x9e3580ae7,0x9e35805e7,0x266863599b68,0x1493599b67,0x10c6b3300ae8,0x10c6b33005e8,0x933599be9,0x529afe8,0xa5358b3a7]) (cB [0x266a5358b226,0x133529ae67,0xa53584e66,0x1266b330b3a8,0x4cd266b330b227,0x266933599a68,0x53a66933599a47,0x1266b3304e67,0x6b330b3a9,0x2666b330b328,0x29c6b330b327,0xd6661604f27,0x56a666b330b227,0x4ccd6661600527,0xd6661600aa8,0x1accc2c01004a7])))) (bI j 16 (bI j 15 (cB [0x2b46b330b3a8,0xd66616005a8,0xed3599be9,0x1243599be8,0x6b330bbe8,0x2666b330ba67,0xec3599be8,0x266ec3599a67,0x1dced3599ba8,0x4cddced3599a27,0x2b0ed3599a26,0x266ed3599a68,0x1da6b3304e67,0xee3599be9,0xee3597fe8,0x7b9afe8]) (cB [0x7a9afe7,0xf73580ae7,0xf7771afe8,0x1253599be8,0x6b330b7e8,0x6b330ab67,0x266ee3599b68,0x1583599b67,0x1dc6b3300ae8,0x1333599b69,0x2668d3599b68,0x14e3599b68,0x29d333599b68,0x266e13599b68,0x6b3304f68,0x660981f67])) (bI j 17 (cB [0x2666b3304f68,0x6b3300ae9,0x3595bca,0x6b2b0d3c9,0xd6561a0b388,0x1acac341604307,0x1acac341600587,0x1c86b2b0d3c8,0x1dc6b2b0d3c8,0xf13595bc7,0x6b2b0b389,0xd6561604308,0x1acac2c0800a07,0x3595858100100406,0x568d6561604307,0x2666b2b0b388]) (bI j 18 (cB [0xd6561604f87,0x2646b2b0b387,0x4d6666b2b0b307,0x4ccd6561600587,0x26a6b2b0b388,0xd6561604787,0xd6561600588,0xe43595bc9,0x6b2b0c7c8,0x1dc6b2b0c787,0xe13595bc8,0x1dce13595b87,0x1dce43595b88,0x1c86b2b0b787,0x4cddce43595b07,0x2b0e43595b06]) (cB [0xad4cddce43595806,0x569dce43595987,0x2b4e43595bc8,0xee3595bc9,0x1dc6b2b13fc8,0x1e4ee3595bc8,0x1dc6b3095bc8,0x6b2b0b7c8,0x6b2b0abc7,0x1dc6b2b0b7c8,0x1dce23595bc8,0x266ee3595bc8,0x1583595bc7,0x3595bea,0x6b2b0d3e9,0xd6561a0b3a8])))))) (bI j 29 (bI j 24 (bI j 21 (bI j 20 (cB [0x35943e9,0xee35943a8,0x6b280b7a7,0x1dc6b2804327,0x26aee35941a7,0x6b2804368,0xd6500800a67,0xd6500800567,0x13335943e8,0x9c1afe7,0x13535943e8,0x6b28005e8,0x6b2b143e9,0x1dc6b2b143a8,0xd65628005e8,0x3594fe9]) (cB [0x3594be8,0x6b290b3a7,0x6b298b3a8,0xd6531600aa7,0xd65316005a7,0xed3594fe8,0xee3594fe8,0x6b2980ae8,0x863595bc9,0x10c6b2b005c8,0x8e3595bc9,0x11c6b2b0b388,0x238d6561600587,0x1dc8e3595bc8,0x11f3595bc7,0x6b2b0b3a9])) (bI j 22 (cB [0xd6561604328,0x1acac2c0800a27,0x1acac2c0800527,0x2666b2b0b3a8,0x29c6b2b0b387,0x26a6b2b0b3a8,0x29e6b2b0b387,0xd65616005a8,0xe43595be9,0x11a3595bc8,0x234ee3595b87,0x1153595bc7,0x1183595bc7,0x2346b2b00ac7,0x6b2b0c7e8,0xe13595be8]) (bI j 23 (cB [0xe23595be8,0x1dce43595ba8,0x266e43595b68,0x1c86b2b00ae8,0xee3595be9,0xee3593fe8,0xf2771afe8,0x1dc853595bc8,0x1253595bc8,0x1113595bc7,0x24a6b2b04347,0x24aee3595bc8,0x6b2b0b7e8,0x1dc6b2b04368,0x6b2b04369,0xd6560800a68]) (cB [0x1333595be9,0x1333594be8,0x14e3595bc8,0xea3595bc7,0x29d333595bc8,0x6b2b04fe8,0x431afea,0x35967e9,0x35913e8,0x6b22005e7,0x35963e8,0x6b2c805e8,0x429afe9,0x863584369,0x10c6b0800a68,0x218d6100100467])))) (bI j 26 (bI j 25 (cB [0x2b4863584368,0x10c6b0800568,0x133431afe9,0xa49afe8,0x3581be7,0xa31afe7,0x14935805e7,0x149999afe8,0x863584fe8,0x441afe7,0x132431afe8,0xa39afe7,0x26b33431af68,0x2668635805e8,0x135431afe9,0x8635847e8]) (cB [0x8635805e9,0x471afea,0x8e358b3a9,0x2668e358b328,0x53a668e358b307,0x11c6b1604f27,0x56a668e358b227,0x4cd1c6b1600527,0x11c6b1600aa8,0x238d62c01004a7,0x2b48e358b3a8,0x11c6b16005a8,0xed471afe9,0x8e358bbe8,0x2668e358ba67,0xec471afe8])) (bI j 27 (cB [0x8e9afe7,0x1338e9ae66,0x266ec471ae67,0x1dced471afa8,0x4cddced471ae27,0x266ed471ae68,0x53a66ed471ae47,0x1da8e3584e67,0xee471afe9,0x8f9afe8,0x3585fe7,0x8e1afe7,0x11f3580ae7,0x11f771afe8,0x125471afe8,0x8e358b7e8]) (bI j 28 (cB [0x4c9afe7,0x266ee471af68,0x1dc8e3580ae8,0x133471af69,0x2668e3599768,0x133509af67,0x266a6471af47,0x27733471af68,0x29d33471af48,0x29c8e3584f47,0x2668e3581747,0x266e1471af68,0x26717471af47,0x8e3584f68,0x2668e3584f68,0x8e3580ae9]) (cB [0x358b3aa,0x6b1604329,0xd62c0800a28,0x1ac58100100427,0x2b46b1604328,0x2ba6b1604327,0xd62c0800f27,0xd62c0800528,0x133358b3a9,0x2666b328b3a8,0x2668d358b3a8,0x1334c1afa7,0x29c8d358b387,0x14e358b3a8,0x6b340b3a7,0x6b16017a7]))))) (bI j 34 (bI j 31 (bI j 30 (cB [0x14b358b3a7,0x29c6b16005a7,0x29d33358b3a8,0x6b1604fa8,0x6b1601fa7,0x96358b3a7,0x6b1604ba7,0x26a6b1604f27,0xd62c09805a7,0x2666b1604fa8,0x132358b3a8,0x14c358b3a7,0x26732358b3a8,0x26b33358b328,0x2666b1604727,0x2666b16005a8]) (cB [0x135358b3a9,0x14f358b3a8,0x6b348b3a7,0x14a358b3a7,0x6b16047a8,0x6b16005a9,0x721afea,0x8d1afe9,0x3598fe8,0x11a771afa8,0x11a358b7a7,0x115771afa7,0x2b515771aca6,0x234ee3580aa7,0x2b51a771ada7,0x8a9afe8])) (bI j 32 (cB [0x35873e7,0x15a8a9aee7,0x8c1afe8,0x35867e7,0x1183580ae7,0x11a3580ae8,0x15a8d1afe8,0x358c7e9,0xee358c7a8,0x6b188b7a7,0x266ee358c727,0x158358c726,0x56a66ee358c426,0x1dc6b1880aa7,0x2b4ee358c5a7,0x133358c768]) (bI j 33 (cB [0x6b1884f67,0x2b533358c667,0x6b1880ae8,0x15a358c7e8,0x709afe9,0x8b9afe8,0x117771afa7,0xee709afa8,0xe1358b7a7,0x711afe9,0x8c9afe8,0x8a1afe7,0x1193580ae7,0x133711af68,0xe23584f67,0xe23580ae8]) (cB [0xee721afa9,0x1dce435987a8,0x1dce4429afa8,0x24ae4429af87,0x24aee721afa8,0xe4358b7a8,0x1c86b168ab27,0x266e4358b727,0x56a66e4358b426,0x1c86b1680aa7,0x2b4e4358b5a7,0x1dce4358b7a8,0x1dcec721afa8,0x4cddcec721ae27,0x266ee721af28,0x158721af27])))) (bI j 36 (bI j 35 (cB [0xe43581326,0x2b0ee721af27,0x56ab0ee721ac26,0x2b133721af27,0x56ab133721ac26,0x1dce43584f27,0x569dce43584c26,0x4ce64ee721ad27,0x56a66ee721ac27,0x1dce43580aa8,0x2b4ee721ada8,0x133721af69,0x266e43599768,0x266e4469af68,0x29d33721af68,0xe43584f68]) (cB [0x1c86b0983f27,0x2b4e43584e67,0x266e43584f68,0x26732721af68,0x2b533721ae68,0xe43580ae9,0x15a721afe9,0x771afea,0xee35987e9,0xee411afe8,0xee4f9afe8,0x12535987e8,0x6b308b7e8,0xe235987e8,0x1dc6b3084368,0xee429afe9])) (bI j 37 (cB [0xee3596be8,0xee35947a7,0x1253596bc7,0x125429afc8,0x853585bc7,0x24a853584347,0x125429afe8,0x24aee429afc8,0x85358b7e8,0xe2429afe8,0x119429afc7,0x1dc853584368,0x929afe9,0x35993e8,0x3585be8,0x6b0b04367]) (bI j 38 (cB [0x889afe8,0x35877e7,0x879afe7,0x133889af67,0x1113580ae7,0x125889afe8,0x1253584368,0x24a6b0800a67,0x133929afe8,0x125771afe9,0xee35993e8,0x125358b7e8,0x125711afe8,0xee3585be8,0x111771afe8,0x24aee3584368]) (cB [0x358b7e9,0x3587be8,0x6b1687be8,0x6b1689fe8,0x9c358b7e8,0x87358b7a7,0x358abe8,0x358a7e7,0x6b1500ae7,0x6b168abe8,0x6b1684368,0xd62d0800a67,0x133358b7e8,0x9b9afe7,0xee358b7e9,0xee3587be8]))))))) (bI j 58 (bI j 48 (bI j 43 (bI j 41 (bI j 40 (cB [0xee3589fe8,0xee4e1afe8,0xee439afa7,0xee358abe8,0xe2358b7e8,0x1dc6b1684368,0xee711afe9,0x119771afe8,0xee358cbe8,0xee701afe8,0x116771afc7,0xec711afe8,0x266ec711ae67,0x266ee711af68,0x158711af67,0x1dce23580ae8]) (cB [0xee3584369,0x1dc6b0800a68,0x133771afe9,0x14e771afe8,0x749afe7,0xee751afa7,0x133701afe8,0x1338b1afc7,0xac1afe8,0x35813e7,0x158771afe8,0x158999afe8,0x158709afa7,0x266ee709afa8,0x264ee709ada7,0xee3584fe8])) (bI j 42 (cB [0x3583be7,0x781afe7,0x358436a,0x6b0800a69,0x999afea,0x13335997e9,0x1333e9afe8,0x133531afe8,0x14e35997e8,0xe135997e8,0x6b3284fe8,0x13b999afe9,0x13b469afe8,0x13b3584fe8,0x133469afe9,0x99a8fe8]) (cB [0x5184fe7,0x14e469afc8,0x8d35817c7,0x479afc6,0x29d33469afc8,0xe1469afe8,0x117469afc7,0x8d3584fe8,0xa71afe9,0x359a3e8,0x751afe8,0x358bfe7,0x14e751afe8,0x35817e8,0x14e999afe9,0x133359a3e8]))) (bI j 45 (bI j 44 (cB [0x14e709afe8,0x133751afe8,0x14e3584fe8,0x13335817e8,0x133709afe9,0x1338b9afe8,0x133358cfe8,0xe13584fe8,0x132709afe8,0x3584fe9,0x3581fe8,0x6b0981fe8,0x3701fe7,0x6e3584fe8,0x6b3384f67,0x6b09833e8]) (cB [0x9635833c7,0x4b1afe8,0x963584fe8,0x3583fe8,0x6b0983fe8,0x1333584fe9,0x1333581fe8,0x1334b1afe8,0x1333583fe8,0x1affb,0x35977fa,0x421aff9,0x33177f9,0x6b2e95bd9,0x6b2e84379,0xd65d0800a78])) (bI j 46 (cB [0x13335977f9,0x2a3fa,0x5423bf9,0x28bf9,0x283f8,0x99a8b78,0x5100af8,0x5404379,0xa80800a78,0x99aa3f9,0xa1aa3e8,0x14399aa3e8,0x5404ff8,0x18bfa,0x187f9,0x20bf8]) (bI j 47 (cB [0x87187e8,0x3084378,0x610800a77,0x99987f8,0x3115bf9,0x31143b8,0x3114ff8,0x31157f8,0x622b04378,0x622b005f8,0x4718bf9,0x1334718b78,0x8e3100af8,0x8e31005f8,0x4a18bf9,0x943104378]) (cB [0x3104379,0x620800a78,0xc4100100477,0x15a3104378,0x620800578,0x9998bf9,0xa718bf8,0x3104ff8,0x9918bf8,0x1359998b78,0x13331005f8,0x9a98bf9,0xa798bf8,0x31047f8,0x31005f9,0x19bfa]))))) (bI j 53 (bI j 50 (bI j 49 (cB [0x6f99bf9,0x3315bf9,0x33143f8,0x662b0b3b8,0x1333315b78,0x662b00af8,0x4319bf9,0x27bf8,0x4f00af7,0x4f005f7,0x1334319b78,0xa499b77,0x863300af8,0x8633005f8,0x4999bf9,0x297f8]) (cB [0x528b3b7,0x133528b236,0x99a9677,0x5284e76,0x93330b3b8,0x26693330b237,0x1334999a78,0x29d334999a57,0x933304e77,0x330b3b9,0x133330b338,0x14e330b337,0x2b533330b237,0x266661600537,0x661600ab8,0xcc2c01004b7])) (bI j 51 (cB [0x15a330b3b8,0x6616005b8,0x7699bf9,0x9219bf8,0x330bbf8,0x133330ba77,0x7619bf8,0x1337619a77,0xee7699bb8,0x266ee7699a37,0x1587699a36,0x1337699a78,0x7719bf9,0x3dff8,0x7b80af7,0x9299bf8]) (bI j 52 (cB [0x330b7f8,0x1337719b78,0xac19b77,0xee3300af8,0x9999b79,0xa719b78,0x14e9999b78,0x3304f78,0x3300af9,0x3599bfa,0x539aff9,0xa73580af8,0x35997f9,0xa19afe8,0x3519bf9,0x1333519a78]) (cB [0x6a3304e77,0xdf3599be9,0x1333599b79,0x6b3304f78,0x6b3300af9,0x6f9afea,0xdf3595bc9,0xb23595bc8,0xb03595bc7,0x1c8b23595b87,0x1dcb23595b87,0x1646b2b04347,0x1646b2b005c7,0x1be6b2b0b388,0x37cd6561604307,0x37cd6561600587])))) (bI j 55 (bI j 54 (cB [0x1c8df3595bc8,0x1dcdf3595bc8,0xdf3595be9,0xb23595be8,0x1be6b2b0b3a8,0xdf431afe9,0xde431afe8,0x1be8635805e8,0xdf471afe9,0xb2471afe8,0x1be8e358b3a8,0x591afe9,0x35927e8,0x35923e7,0xe435927a7,0xee35927a7]) (cB [0x6b2484367,0x6b24805e7,0xb235927e8,0xb2551afe8,0x581afe8,0x3592be7,0xe4581afa7,0xb03584367,0xb2581afe8,0xe4591afa8,0xb2358c7a7,0xe1591afa7,0xe2591afa7,0x266e4591af27,0x1c8b23580aa7,0x1c8b235805a7])) (bI j 56 (cB [0xee591afa8,0x24aee591af87,0xb2358b7a7,0x1dcb23584327,0x26aee591ada7,0xb23584368,0x1646b0800a67,0x1646b0800567,0x133591afe8,0xa89afe7,0xa81ade6,0x135591afe8,0xb235805e8,0x681afe9,0x358efe8,0x6b1d8b3a7]) (bI j 57 (cB [0xe4358ef67,0x133358ef67,0x6b1d80ae7,0xd0551afe8,0x671afe8,0x358f3e7,0xce358b3a7,0xe4671af67,0xd0671afe8,0xd0358b3a8,0x266d0358b327,0x26ad0358b327,0x1a06b1600aa7,0x1a06b16005a7,0xe4681af68,0xd0358c767]) (cB [0xe1681af67,0xe2681af67,0x1dce4681af27,0x1c8d03580a67,0xed681afe8,0x266ed681ae67,0xee681afe8,0x133681af68,0xd03584f67,0xd03580ae8,0xdf358b3a9,0x1be6b1604328,0x37cd62c0800a27,0x37cd62c0800527,0x266df358b3a8,0x26adf358b3a8])))))) (bI j 68 (bI j 63 (bI j 60 (bI j 59 (cB [0x1be6b16005a8,0xe46f9afe9,0xdf358c7e8,0xe16f9afe8,0xe26f9afe8,0x1dce46f9afa8,0x266e46f9af68,0x1c8df3580ae8,0xee6f9afe9,0x1256f9afc8,0x24adf3584347,0x24aee6f9afc8,0x125581afc7,0xee581afe8,0xdf358b7e8,0x358a3e7]) (cB [0x1dcdf3584368,0xdf3584369,0x1be6b0800a68,0x1336f9afe9,0x13b99b7fe8,0x133671afe8,0xdf3584fe8,0x35837e7,0x6f9affa,0x681aff9,0x671aff8,0x133681af78,0xd03580af8,0xdf3584379,0x1be6b0800a78,0x1336f9aff9])) (bI j 61 (cB [0x391afea,0x669afe9,0xcd3595bc8,0xc33595bc7,0x19a6b2b04347,0xcd471afe8,0x358fbe8,0x6b1f04367,0x619afe8,0x3590fe7,0x5f9afe7,0x133619af67,0xc33580ae7,0xcd619afe8,0xcd3584368,0x19a6b0800a67]) (bI j 62 (cB [0x133669afe8,0x723595be9,0x11c723595bc8,0xc73595bc7,0xe46b2b04368,0x8e391afe9,0x639afe8,0x3590be7,0x621afe7,0x133639af67,0xc73580ae7,0x2668e391af68,0x11c723580ae8,0x723584369,0xe46b0800a68,0x133391afe9]) (cB [0x9f9afe8,0x35827e7,0x13f999afe8,0x723584fe8,0x399afe7,0x3b9afea,0x6c9afe9,0xd93595bc8,0xd53595bc7,0x1b26b2b00ac7,0x358dfe8,0x6b1b80ae7,0x6a9afe8,0x358e7e7,0xd96a9afe8,0xd93580ae8])))) (bI j 65 (bI j 64 (cB [0x773595be9,0xee6b2b00ae8,0x933b9afe9,0x6b1afe8,0x773580ae9,0x3595bfa,0x6b2b0b3b9,0xd6561604338,0xd65616005b8,0xe43595bf9,0xee3595bf9,0x431affa,0x5f1afe9,0x5b1afe8,0x5a1afe7,0x1335b1af67]) (cB [0xb63580ae7,0xb635805e7,0x5e1afe8,0x3591be7,0xbc3584367,0x1355e1ade7,0xbe5e1afe8,0xbe3584368,0x17c6b0800a67,0x17c6b0800567,0x1335f1afe8,0x1355f1afe8,0xbe35805e8,0xbe431afe9,0xbc431afe8,0x17c8635805e8])) (bI j 66 (cB [0x35967f9,0x113f8,0x22005f7,0x35963f8,0x6b2c805f8,0x429aff9,0x5e9afe8,0x863584379,0x10c6b0800a78,0x10c6b0800578,0x133431aff9,0xa49aff8,0x135431aff9,0x8635805f9,0x471affa,0x6a1afe9]) (bI j 67 (cB [0x561afe8,0x35933e7,0x559afe7,0xed561afa7,0x266ed561ae26,0xee561afa7,0x133561af67,0xac3580ae7,0xac35805e7,0xd4561afe8,0x691afe8,0xd2358b3a7,0xed691aee7,0xd4358b3a8,0x266d4358b327,0x1a86b1600aa7]) (cB [0x1a86b16005a7,0xed6a1afe8,0x266ed6a1ae67,0xee6a1afe8,0x1336a1af68,0xd43584f67,0xd43580ae8,0x6a1aff9,0x8e358b3b9,0x2668e358b338,0x11c6b1600ab8,0x11c6b16005b8,0xed471aff9,0x266ed471ae78,0xee471aff9,0xee471abf8]))))) (bI j 73 (bI j 70 (bI j 69 (cB [0x266ee471aa77,0x8f9aff8,0x266ee471af78,0x133471af79,0x13b99a3b78,0x2668e3b1af68,0x133679af67,0x266d7471af47,0x28733471af68,0x29d33471af58,0x8e3584f78,0x8e3580af9,0x358b3ba,0x6b1604339,0xd62c0800a38,0x1ac58100100437]) (cB [0x2b46b1604338,0x2b86b1604327,0xd62c0800538,0x133358b3b9,0x143358b3a8,0x141358b3a7,0x2866b16005a7,0x28733358b3a8,0x14e358b3b8,0x340b3b7,0x6b1604fb8,0x1601fb7,0x132358b3b8,0x142358b3a7,0x26b33358b338,0x28b33358b327])) (bI j 71 (cB [0x2666b16005b8,0x135358b3b9,0x145358b3a8,0x140358b3a7,0x14f358b3b8,0x348b3b7,0x6b16047b8,0x6b16005b9,0x721affa,0x831afe9,0x7f9afe8,0x821afe8,0x35887e7,0x133821af67,0x2b533821ac66,0x1043580ae7]) (bI j 72 (cB [0x15a821ade7,0x133831af68,0x1063584f67,0x2b533831ae67,0x1063580ae8,0x15a831afe8,0x8d1aff9,0x18ff8,0x11a771afb8,0x8a9aff8,0x8c1aff8,0x11a3580af8,0x358c7f9,0xee358c7b8,0x133358c778,0x6b1880af8]) (cB [0x709aff9,0x811afe8,0x801afe7,0xee709afb8,0x711aff9,0x829afe8,0x133711af78,0xe23580af8,0xee721afb9,0x21cee721afa8,0xe4358b7b8,0x266ee721af38,0x158721af37,0x56a66ee721ac37,0x1dce43580ab8,0x2b4ee721adb8])))) (bI j 75 (bI j 74 (cB [0x133721af79,0x28733721af68,0xe43584f78,0x2b533721ae78,0xe43580af9,0x15a721aff9,0x771affa,0x77187f9,0x92987f8,0x871afe9,0x7e1afe8,0x7d1afe7,0x1337e1af67,0xfc3580ae7,0x10e3584368,0x21c6b0800a67]) (cB [0x133871afe8,0x10e771afe9,0x125871afe8,0x125459afc7,0xee459afe8,0x10e358b7e8,0x10e711afe8,0xfc771afe8,0x21cee3584368,0xee429aff9,0xee5e9afe8,0x1255e9afc7,0x125429afd8,0x929aff9,0x193f8,0x889aff8])) (bI j 76 (cB [0x1253584378,0x125771aff9,0x77193f8,0x358b7f9,0x7bf8,0x82358b7e8,0x358abf8,0x6b1684378,0xee358b7f9,0xee711aff9,0x105771afe8,0xee3584379,0x1dc6b0800a78,0x133771aff9,0x143771afe8,0x731afe7]) (bI j 77 (cB [0xee739afa7,0xac1aff8,0x358437a,0x6b0800a79,0x999affa,0x99997f9,0xa7197f8,0x13335997f9,0x143999afe8,0x9dccff9,0x9da37f8,0x1333b1afe9,0x1336b9afe8,0xd7469afc7,0x671afe7,0x8d3b1afe8]) (cB [0x763584fe8,0xa19afe9,0x739afe8,0x358c3e7,0x143739afe8,0xa19aff9,0x143999afe9,0x13335997e8,0x14ea19afe8,0x143709afe8,0x133739afe8,0x1433584fe8,0x143999aff9,0x133469aff9,0x133699afe8,0x14e469afd8])))))))) (bI j 117 (bI j 97 (bI j 87 (bI j 82 (bI j 80 (bI j 79 (cB [0xa71aff9,0x1a3f8,0x751aff8,0x14e999aff9,0x999a3f8,0x133709aff9,0x133811afe8,0x3584ff9,0x1ff8,0x6b0982fe8,0x7d3584fe8,0x783584f67,0x3583ff8,0x1333584ff9,0x37ffb,0x6f9cbfa]) (cB [0xdf471cbf9,0x6fb1ff8,0x681cbf9,0x390eff8,0x671cbf8,0x347f7,0x133681cb78,0x9fb4377,0xd03900af8,0xdf3904379,0x1be720800a78,0x1336f9cbf9,0x9fb7ff8,0x1436f9cbe8,0x287336f9cbe8,0x6f9dffa])) (bI j 81 (cB [0x6e1dff9,0x3b8d7f8,0xdf3b80af9,0x2cbfa,0x127f9,0x123f8,0x72127b8,0x83127b7,0x77127b8,0x87127b7,0x2484378,0x490800a77,0x490800577,0x99927f8,0x9a927f8,0x24805f8]) (cB [0x59127f9,0x592abf9,0x5bacbf8,0x2c3f9,0x5eac3f8,0x662c3d8,0x580ffd7,0x662c3f8,0x12bf8,0x722c3b8,0x5804378,0xb00800a77,0x99ac3f8,0x592c3f9,0x5eacbf8,0x722cbb9]))) (bI j 84 (bI j 83 (cB [0x832cbb8,0x822cbb7,0x10659005b7,0x590c7b8,0x70acbb8,0x812cba7,0x712cbb8,0x82acba7,0x133722cb38,0x28733722cb37,0xe45904f37,0x2b533722ca37,0x266e45900537,0xe45900ab8,0x1c8b201004b7,0x15a722cbb8]) (cB [0xe459005b8,0x772cbb9,0x872cbb8,0x10e772cbb8,0x125872cb97,0x125772cb98,0xee5905b97,0x125772cbb8,0x590b7b8,0xee5904338,0x1dcb20800a37,0x2b4ee5904137,0x133772cbb8,0x132772c9b7,0x26b33772c937,0x135772c9b8])) (bI j 85 (cB [0xee59045b7,0x5904379,0xb20800a78,0x164100100477,0x15a5904378,0xb20800578,0x99acbf9,0xa1acbf8,0x14399acbf8,0x547f8,0x541f7,0xa8805f7,0x13370acbb8,0x133812cba7,0x5904ff8,0x992cbf8]) (bI j 86 (cB [0x13599acb78,0x13359005f8,0x9aacbf9,0xa2acbf8,0x59047f8,0x59005f9,0x6f8b3ba,0xdf1604339,0x1be2c0800a38,0x37c58100100437,0x2b4df1604338,0x1336f8b3b9,0x1436f8b3a8,0x286df488b387,0xdf1601fa7,0x286df16005a7]) (cB [0x1436f8b3b8,0x287336f8b3a8,0xdf1604fb8,0x16037b7,0x1326f8b3b8,0x1426f8b3a7,0x26b336f8b338,0x266df16005b8,0x1356f8b3b9,0x1456f8b3b8,0xdf16047b8,0xdf16005b9,0x7237ffa,0x8337ff9,0x8237ff8,0x6f8c7f9]))))) (bI j 92 (bI j 89 (bI j 88 (cB [0xee6f8c7b8,0x70b7ff9,0x8137fe8,0x8bb7fd8,0xee70b7fb8,0xee7237fb9,0x24aee7237f98,0x24aee7237fb8,0xe46f8b7b8,0x720a3b7,0x266ee7237f38,0x1587237f37,0x7236b36,0x1587236b36,0x56a66ee7237c37,0x2b4ee7237db8]) (cB [0x15a7237ff9,0x7737ffa,0x8737ff9,0x10e7737ff9,0x1258737fd8,0x92af7d7,0xee6fa2fd8,0x872c3f8,0x772f7f8,0xee6fa17f9,0x1256fa17d8,0x92b7fd9,0x1256f9d7c8,0x1116f9d7c7,0x6f85bd8,0x12588b7fd8])) (bI j 90 (cB [0x13392b7fd8,0x14392b7fc7,0x89b7fc6,0x92b7ff9,0x88b7ff8,0x1257737fd9,0x24aee6f9d7c8,0x495dced6f9d787,0x242ee6f9d7c7,0x92ac3d8,0x5805bd7,0x12577333d8,0x1256f8b7d8,0x1257137fd8,0x12582b7fc7,0xee6f85bd8]) (bI j 91 (cB [0x24b117737fd8,0x267257737fd8,0x1257737ff9,0x92ac3f8,0x1117737ff8,0x772c3f9,0x6f8b7f9,0xdf1689fd8,0xa3f8,0x6f8abf8,0xee6f8b7f9,0xee6f89fd8,0xee7137ff9,0x1057737fe8,0x1197737fd8,0x1337737ff9]) (cB [0xac37ff8,0x36bf7,0xac36bf7,0x1587737ff8,0x7736bf7,0x1cbfb,0x337fa,0x66a3bf9,0x6a337f8,0x470fbf8,0x6523bf8,0xee66a3bb8,0xcd47005f8,0x66a53f9,0xfbf9,0xf7f8])))) (bI j 94 (bI j 93 (cB [0x770fbb8,0x1f0b7b7,0xee1f04337,0x135770f9b7,0x1f04378,0x3e0800a77,0x3e0800577,0x998fbf8,0x9a8fbf8,0x1f005f8,0x668fbf9,0x618fbf8,0xcd1f04378,0x30ff9,0x6a30ff8,0x10ff8]) (cB [0x2fff8,0x7730fb8,0x618b7b7,0x135618b536,0x1357730d37,0xee6180ab7,0x15a7730db7,0x99b0f78,0x9ab0f78,0x6180af8,0xc301004f7,0xad30ff8,0x61805f8,0x66b0ff9,0x6690ff8,0x66afff8])) (bI j 95 (cB [0x66b03f8,0x64b0ff8,0x13364b0e77,0x6530ff8,0x1336530f77,0x1356530d77,0xee66b0fb8,0x266ee66b0f37,0x26aee66b0d37,0x13366b0f78,0x13566b0f78,0xcd6180af8,0xcd61805f8,0x32bf9,0x107f8,0x6504378]) (bI j 96 (cB [0xca0800a77,0x99b2bf8,0x9ab29f8,0x66b2bf9,0xcd6504378,0x13366b2bf8,0x13566b29f8,0x77337b9,0xee66a17b8,0x1257733798,0x125668b797,0x24aee6684317,0x267257733797,0x56a67257733496,0x26b257733597,0xee66ac3b8]) (cB [0x933bbb8,0x1267704337,0x135933b9b7,0x668b7b8,0xcd1689f97,0xcd1684337,0x135668b5b7,0x14f668b596,0xee668b7b8,0xee71337b8,0x10577337a7,0xee6684338,0x1dccd0800a37,0x2b4ee6684137,0x2baee6684116,0x13377337b8])))))) (bI j 107 (bI j 102 (bI j 99 (bI j 98 (cB [0x29d337733797,0x15877337b7,0x2b1357733536,0x13277335b7,0x26b337733537,0x13577335b8,0x14f7733597,0xee66845b7,0x6684379,0xcd0800a78,0x19a100100477,0x15a6684378,0x15d6684357,0xcd0800578,0x99b37f9,0xa1b37f8]) (cB [0x323f7,0x14399b37f8,0x14ea1b37d7,0xa7337d8,0x14e99b37d8,0x553f8,0x6684ff8,0x99337f8,0x13599b3778,0x13366805f8,0x9ab37f9,0xa7b37d8,0x66847f8,0x66805f9,0x471cbfa,0x31ff9])) (bI j 100 (cB [0x10bf8,0x7710bb7,0x2100af7,0x6390bf8,0x313f8,0x63b13f8,0x63313f7,0x15a63310f6,0xee63b13b7,0x15a63b12f7,0x7731fb8,0x10e7731fa7,0x1207731fb7,0x638b7b7,0x1337731f37,0x2b5337731c36]) (bI j 101 (cB [0x2bd337731c35,0xee6380ab7,0x15a7731db7,0x15e7731db6,0x6380af8,0xc701004f7,0xad31ff8,0xaf31ff7,0xee471cbb9,0x21cee471cba8,0x11f771cbb8,0x8e390b7b8,0x266ee471cb38,0x56a66ee471c837,0x1dc8e3900ab8,0x2b4ee471c9b8]) (cB [0x8e3900af9,0x11c7201004f8,0x15a471cbf9,0x4a1cbfa,0x32ff9,0x103f8,0x2004377,0x307f8,0x65b07f8,0x6584378,0xcb0800a77,0x99b2ff8,0x65a53f9,0x3915ff9,0x943904379,0x128720800a78])))) (bI j 104 (bI j 103 (cB [0x1334a1cbf9,0x9fa53f8,0xa69cbf8,0x14d999cbf8,0x771cbba,0x10e771cba9,0x10e429cba8,0x21cee459cba8,0x10e390b7a8,0xee3907ba8,0x1dc720f04327,0x26aee39079a7,0x21cfc771cba8,0x21cfb771c9a7,0x21cee3904328,0x439dc720800a27]) (cB [0x56a1cee3904127,0x2670e771cba8,0x2650e771c9a7,0x13d873b9a6,0x4d6670e771c927,0x26b0e771c9a8,0x29f0e771c9a7,0x108771c9a6,0x21cee39045a7,0xee429cbb9,0x772c7b8,0x92ac797,0xee5e9cba8,0xee39117a7,0x1dcbd5e1c9a7,0x125429cb98])) (bI j 105 (cB [0x853905b97,0x125429cbb8,0x125771cbb9,0x125390b7b8,0xee3905bb8,0x111771cbb8,0x893bbb7,0x26711771cb37,0x24aee3904338,0x26725771cbb8,0x4d66725771c937,0x26b25771c9b8,0x390b7b9,0x721689fb8,0x3f8b7b7,0x721684338]) (bI j 106 (cB [0xe42d0800a37,0x2b4721684137,0x133390b7b8,0x132390b5b7,0x9e8b5b6,0x26b33390b537,0x135390b5b8,0x14f390b5b7,0x7216845b7,0xee390b7b9,0xee3909fb8,0x771ffb7,0xee711cbb9,0x105771cba8,0xee39083a7,0x20b04771c9a7]) (cB [0x119771cbb8,0xee3904339,0x1dc720800a38,0x2b4ee3904138,0x2baee3904137,0x1dc720800d37,0x133771cbb9,0x266ee469cbb8,0x13377317b7,0x266ee699cba7,0x1338f1cbb7,0x14e771cbb8,0x14b771c9b7,0x29d33771cbb8,0x53a6b33771c937,0x29733771c9b7]))))) (bI j 112 (bI j 109 (bI j 108 (cB [0x158771cbb8,0x2b135771c937,0x2b133771cbb8,0x2b132771c9b7,0x1589ebb9b6,0x56ab133771c8b7,0xee3904fb8,0x26aee3904d37,0x266ee3904fb8,0x132771c9b8,0x9ebb9b7,0x77029b6,0x26732771c9b8,0x13d99bb9b7,0x29933771c9b7,0x26b33771c938]) (cB [0x266ee3904537,0x135771c9b9,0x14f771c9b8,0x14a771c9b7,0xa93b9b6,0xee39045b8,0x390437a,0x720800a79,0xe4100100478,0x15a3904379,0x15d3904378,0x720800f78,0x720800579,0x999cbfa,0x4fff9,0x9fa43f8])) (bI j 110 (cB [0x9fb4fe7,0x27f8,0x4805f7,0x4f3f8,0x9fcf3f8,0x9f805f8,0x9fccff9,0x9fa37f8,0x9fccbf8,0x13f9accf78,0x9e4cff8,0x13f99805f8,0xa19cbf9,0x3901ff8,0x143999cbf9,0x14ea19cbf8]) (bI j 111 (cB [0x133469cbf9,0x99b17f8,0xa7317d7,0x133699cbe8,0x14e469cbd8,0xa71cbf9,0x751cbb8,0xa59cbf8,0x14e39005f8,0x14e999cbf9,0x29d333c9cbe8,0x266ea3c9cba7,0x133751cbb8,0x26b33751cb37,0x29d33751cbb8,0x29d35999cb78]) (cB [0x14b999cbf8,0xa9ccff7,0x3904ff9,0x1cff8,0x3904bf8,0x1353904f78,0x7209805f8,0x1333904ff9,0x1333904bf8,0x991cbf9,0x4f7f8,0x2bf7,0x133991cbf9,0x9eccff8,0x14c999cbf8,0x135999cb79])))) (bI j 114 (bI j 113 (cB [0x1333904778,0x13339005f9,0x9a9cbfa,0xa79cbf9,0x759cbb8,0xa51cbf8,0x54bf7,0x39047f9,0x39005fa,0x1dffb,0x1b7fa,0x1b3f9,0x2a7f8,0x3680af9,0x367fa,0xdff9]) (cB [0xdbf8,0x1b8b3b8,0x371600ab7,0x3716005b7,0x768dff8,0x770dff8,0x1b80af8,0x6c8dff9,0x6a8dff8,0xd91b80af8,0x2bff9,0x12ff8,0x2bbf8,0x772bfb8,0x5780af8,0xaf01004f7])) (bI j 115 (cB [0xad2bff8,0x57805f8,0x6cabff9,0x6cab7f8,0x6cabbf8,0x6aabff8,0xee6aabfb7,0x6c2bff8,0xee6c2bdb7,0xee6cabfb8,0xd95780af8,0xd957805f8,0x357f9,0x6eb57f8,0xe7f8,0x6a8b3b8]) (bI j 116 (cB [0xd516005b7,0x76b56f8,0x77357f8,0x6cb57f9,0x6c8e7f8,0xd96a8b3b8,0xed6cb56f8,0xee6cb57f8,0x6c8b3b9,0xd91600ab8,0x1b22c01004b7,0x15a6c8b3b8,0xd916005b8,0x76b67f9,0x92367d8,0x6c8bbf8]) (cB [0x76367f8,0xee76b67b8,0x77367f9,0x92b67d8,0x1256c80ad7,0x12577367d8,0x4bff8,0x4baf7,0x9780af7,0x6c8b7f8,0xee6c80af8,0x6c80af9,0x6c9dffa,0x3b8dff9,0x771b80af8,0x6a9dff9]))))))) (bI j 136 (bI j 126 (bI j 121 (bI j 119 (bI j 118 (cB [0x3b8e7f8,0xd96a9dff9,0xd93b80af9,0x1dbfa,0x35ff9,0xe3f8,0x431dffa,0x2eff9,0x11ff8,0x2380af7,0x2e3f8,0x5dae3f8,0x5cae3f7,0x5d80af8,0xbb01004f7,0xad2eff8]) (cB [0x863b80af9,0x10c7701004f8,0x15a431dff9,0x3b8b3ba,0x771600ab9,0xee2c01004b8,0x15a3b8b3b9,0x15d3b8b3b8,0x771600fb8,0x7716005b9,0x769dffa,0x921dff9,0x124771dfb8,0x881df78,0x911dff8,0x3b8bbf9])) (bI j 120 (cB [0xee3b8bbb8,0x761dff9,0x42bf8,0xee769dfb9,0x10b773b7b8,0x24aee769dfb8,0xed3b8b7b8,0x771dffa,0x42ff9,0x85a2bf8,0x7ff8,0xf80af7,0x427f8,0x85c27f8,0x8580af8,0x85bbbf9]) (cB [0x85a17f8,0x85bb3f8,0x84bbbf8,0x10b7700af8,0xee429dff9,0x772ebf8,0x92aebd7,0x125429dfd8,0x929dff9,0x889df78,0x909dff8,0x1253b80af8,0x125771dff9,0x111771df78,0x3b8b7f9,0x207f8]))) (bI j 123 (bI j 122 (cB [0x3b8aff8,0x771680af8,0xee3b8b7f9,0xee761dff9,0x853bbf8,0xee3b80af9,0x3b80afa,0xb3bb,0x160433a,0x2c0800a39,0x58100100438,0x15a1604339,0x15c1604338,0x2c0800f38,0x998b3ba,0x1333b0b3b9]) (cB [0x1336b8b3b8,0x1436b8b3a7,0x1433b0b3a8,0x761601fa7,0x2867616005a7,0x14e3b0b3b8,0x2667616005b8,0xa18b3b9,0x143488b3b8,0xa1a6bb7,0x157488b397,0x155488b196,0x157a18b3b8,0x155a18b1b7,0x1601fb8,0x2c03805b7])) (bI j 124 (cB [0x1431601fb8,0xa08b3b8,0x143a08b3b8,0x14316005b8,0x143998b3b9,0x143468b3b8,0xa1a63b7,0x14ea18b3b8,0x1431604fb8,0x143990b3b8,0x28735998b338,0x1331601fb8,0x141998b3b8,0x2873316005b8,0x133468b3b9,0x99a63b8]) (bI j 125 (cB [0x1334c005b7,0x133698b3a8,0x1331d0b3a7,0x266d316005a7,0x133698b3b8,0x14e468b398,0x8d1601797,0x478b396,0x29c8d1600597,0x2668d16005b8,0xa70b3b9,0x14e3c8b3b8,0x16017b8,0x2c02805b7,0xa58b3b8,0xab0b3b7]) (cB [0x14ea58b3b8,0x14e16005b8,0x14e998b3b9,0x14e1604fb8,0x14e990b3b8,0x29d35998b338,0x13316017b8,0x14b998b3b8,0x29d3316005b8,0x1604fb9,0x2c0982fb8,0x2c09833b8,0x4b0b3b8,0x9616005b7,0x1604bb8,0x3e0b3b7]))))) (bI j 131 (bI j 128 (bI j 127 (cB [0x2c0984bb8,0x1351604f38,0x1451604f37,0x2c09805b8,0x1331604fb9,0x1331604bb8,0x2662c09805b8,0x990b3b9,0xa10b3b8,0x16023b7,0xa60b3b8,0x133990b3b9,0x142998b3b8,0x14c998b3b8,0x135998b339,0x145998b338]) (cB [0x1331604738,0x13316005b9,0x9a8b3ba,0xa28b3b9,0xa00b3b8,0xa78b3b9,0xa50b3b8,0x16047b9,0x16005ba,0x393fb,0x41bfa,0x3fff9,0x4b3f8,0x93f8,0x413f9,0x96c13f8])) (bI j 129 (cB [0x87f8,0x99c1378,0x8204f77,0x15a8204c76,0x15a99c1077,0xad411f8,0x99c1b79,0x1338323778,0x14e99c1b78,0x99bf777,0x8304f78,0x15a8304e77,0x15c8304e66,0x1338304f78,0x1339941b78,0x15a99c1a78]) (bI j 130 (cB [0x15c99c1a67,0x1338300e77,0xad41bf9,0xae41be8,0xaec1bf8,0x40ff7,0x8300ff8,0xc7fa,0x770c7b9,0x10e770c7b8,0x125770c7b8,0x188b7b8,0x133770c738,0xac0c737,0x1881336,0x2b533770c437]) (cB [0x266ee1880c36,0x15a770c5b8,0xee1880db7,0xad0c7f9,0x1880ff8,0x387fa,0x40bf9,0x8bf8,0x403f8,0x81403f8,0x45ff9,0x8bbbbb8,0x8b8b7b7,0x6bf8,0x77387b9,0x10e77387b8])))) (bI j 133 (bI j 132 (cB [0x12577387b8,0x708b7b8,0x77393ba,0xee721c7b9,0xee7233398,0xee720ff97,0xee72333b8,0x10e77393b9,0x12587393b8,0x267258739337,0x2b52587391b7,0x21cee7222fb8,0x10e720b7b8,0xee7207bb8,0x10c77393b8,0x2670c7739237]) (cB [0x2670e7739338,0x56a670e7739037,0x2b50e77391b8,0x2bb0e77391b7,0x2690e7739136,0xee72217b9,0xee722f7b8,0x125722f797,0x1257221798,0xe44285b97,0x12577393b9,0x24aee721d7b8,0x125720b7b8,0x12576393b8,0x267257639237,0xee7205bb8])) (bI j 134 (cB [0x12177393b8,0x267217739237,0x24b2177393b8,0x267257739338,0x56a67257739037,0x2b52577391b8,0x720b7b9,0xe41689bb8,0xe41689fb8,0xe4168ab38,0x133720b738,0xe41684f37,0x2b4e41684c36,0x26732720b537,0x2b533720b437,0x15a720b5b8]) (bI j 135 (cB [0xee720b7b9,0xee76393b9,0x10d77393b8,0x2670d7739237,0x12377393b8,0x266ee7639238,0x2b1337639237,0x1337739339,0xac39338,0x158721eb37,0x1587236f36,0x7201337,0x1587739338,0x2b5587739037,0x2b1337739338,0x56ab1337739037]) (cB [0x2b5337739038,0x15a77391b9,0xad393fa,0x3bbfb,0x771c7fa,0x77333d9,0x770ffd8,0x790ffd7,0x1f8b7d7,0x710ffd7,0x828ffc6,0xee660ffd8,0xee6630bd8,0x266ee6630b57,0x660b7d8,0x71333d8])))))) (bI j 146 (bI j 141 (bI j 138 (bI j 137 (cB [0x82b33c7,0x66083c6,0x13377333d8,0xac333d7,0x77333f9,0x66217d8,0x428ffd7,0x66217f8,0x770fff8,0x2c3f8,0x7730bf8,0x660b7f8,0x71333f8,0x82b33e7,0x13377333f8,0xac333f7]) (cB [0x871c7e9,0x10e459c7e8,0x3887be8,0x1d3e7,0x10e7e1c7e8,0x133871c7e8,0x9f43be7,0x10e771c7e9,0x429c7f9,0x5e9c7e8,0x38917e7,0x929c7f9,0x889c7f8,0x125771c7f9,0x388b7f9,0x3889ff8])) (bI j 139 (cB [0x1fbf7,0x711c7f9,0x829c7e8,0x38883e7,0x133771c7f9,0x9f3bbf8,0xac1c7f8,0x43bfa,0x8722ff9,0x98a2fd8,0x93a2f57,0x7e22ff8,0x98c3bf9,0x93c3b78,0x7bf9,0x4107be8]) (bI j 140 (cB [0x9987bf8,0x8707bf9,0x8720be8,0x3f3f9,0x4aff8,0x4aaf7,0x97f8,0x3ebf8,0x99bf378,0x873f3f9,0x873ebf8,0x863f3f8,0x133863f277,0x133873f378,0x99c3bf9,0xa1c3be8]) (cB [0x14399c3be8,0xa743bf8,0x41ff7,0x567f8,0x8704ff8,0x873bbfa,0x87217f9,0x7e217f8,0x10e77217f9,0x92c3bf9,0x92a2fd8,0x92bf3f8,0x88c3bf8,0x13392c3bf8,0x7722ff9,0x458b7f8])))) (bI j 143 (bI j 142 (cB [0x10e7722ff9,0xfc7722ff8,0xee71a2fb7,0x870b7f9,0x87273f8,0x233f7,0x7e0b7f8,0x8738bf9,0x8cc3bf8,0x3e7f7,0x870cbf8,0x87383f8,0x8b43bd7,0x7107bf8,0x8638bf8,0x1338638a77]) (cB [0x1338738b78,0x10e7738bf9,0x7707bf9,0x7e3bbf9,0x95bbbf8,0x953baf7,0x77097f8,0x7d3bbf8,0x1337e3bb78,0x10e7e3bbf9,0x10e7738fb8,0x133873bbf9,0x143873bbe8,0x77217fa,0x772f7f9,0x92af7d8])) (bI j 144 (cB [0x1255e9d7c7,0x92917d7,0x1255eac797,0x1255e2c596,0x92acfd7,0x5e85bd7,0x12588af7d7,0x13392af7d7,0x92af7f8,0x2cff7,0x125772f7d8,0x77117f8,0xee5eac7b8,0xee5e2c5b7,0x772d7f8,0x5e8b7f8]) (bI j 145 (cB [0x712f7f8,0x8caf7d7,0x133772f7f8,0xac2f7f7,0xee5ea17f9,0x1255ea17d8,0x7716bf9,0x77147b8,0x9296bd8,0x92a17d9,0x125429d7d8,0x24aed429d797,0x111429d7d7,0x4285bd8,0x12588a17d8,0x2672588a1757]) (cB [0x13392a17d8,0xa4497d7,0x92a17f9,0x4285bf8,0x12577217d9,0x12577217f9,0x428b7f9,0x71217f9,0x8ca17d8,0x42863d7,0x13377217f9,0xa43bbf8,0xac217f8,0x497fa,0x929d7f9,0x989d7e8]))))) (bI j 151 (bI j 148 (bI j 147 (cB [0x939d767,0x3a85366,0x939d7e7,0x889d7f8,0x949d7e7,0x98c97f9,0x98c47f8,0x98446f7,0x93c9778,0x9285377,0x93c97f8,0x5bf9,0x57f8,0x9985bf8,0x9285bf9,0x8885bf8]) (cB [0x447f9,0x94c47f8,0x77f8,0x43ff8,0x99c4778,0x92c47f9,0x94c97f8,0x92877f8,0x92c3ff8,0x94497e7,0x90c47f8,0x13390c4677,0x13392c4778,0x99c97f9,0xa1c97f8,0x44ff7])) (bI j 149 (cB [0x9284ff8,0x92bbbfa,0x125771d7f9,0x111771d7f8,0x928b7f9,0x92a0bf8,0x888b7f8,0x92b8bf9,0x92c17f8,0x3e3f7,0x928cbf8,0x92b83f8,0x92c07e7,0x7105bf8,0x90b8bf8,0x13390b8a77]) (bI j 150 (cB [0x13392b8b78,0x1257738bf9,0x12582bbbf8,0x7705bf9,0x88bbbf9,0x94bbbf8,0x77077f8,0x87bbbf8,0x13388bbb78,0x12588bbbf9,0x12992bbbf8,0x2672588bbb78,0x13392bbbf9,0x15899c97f8,0x15892b87b7,0x2b13592b8536]) (cB [0x2b13599c9577,0x2672577387b8,0x4d667257738537,0xb7fa,0x1689bf9,0x4b8b7f8,0x4109be8,0x20bf9,0x99a0bf8,0x410b7f9,0x380b7f8,0x1689ff9,0x400b7f8,0x4e0b7f9,0x438b7b8,0xabf9])))) (bI j 153 (bI j 152 (cB [0x26ff8,0xa7f8,0x168abf9,0x998b7f9,0x4dff8,0x133708b7b8,0x132708b5b7,0x1684ff8,0x770b7fa,0x7720bf9,0x7709ff9,0x77203f8,0x77273f9,0x7721fb8,0x770abf9,0x710b7f9]) (cB [0x828b7f8,0x8c8b7f8,0x133770b7f9,0x7738bfa,0x82bbbf9,0x10577227f8,0xee74227b7,0x11b7722796,0x82bb3f8,0x13382bb277,0x105773a3b8,0x11b82bbbb7,0x104773a1b7,0x77083f8,0x7f3bbf8,0x13382bbb78])) (bI j 154 (cB [0xac41777,0x15899c1777,0x2b13382bb636,0x14499bbb77,0x28933773b636,0x1057738bf9,0x11982bbbf8,0x8cbbbf9,0x8cbb3f8,0x77063f8,0x8a3bbf8,0x1197738bf9,0x770cbf9,0x77383f9,0x80bbbe8,0x7708fe7]) (bI j 155 (cB [0x80bbbf8,0x8b3bbd8,0x7706fd7,0x8b3bbf8,0x7638bf9,0x1337638a78,0x1337738b79,0xac38b78,0x15899b8b78,0x99bbbfa,0x13377383f9,0x13380bbbe8,0xac407e7,0x13380bbbf8,0xac407f7,0xac383f8]) (cB [0x563f9,0xac1ebf8,0xac36ff7,0x36bf6,0x491ebf7,0x15a491e8f6,0x13f8,0xac3bbf9,0x15899bbbf9]))))))))) 64 (i % 16)
def zve (i : Nat) := materialize [122,148,238,309,346,350] 9 511 6 (zjW i >>> 4)
def zla (i : Nat) := (zve i).map znB
def zhE (i : Nat) : Option (Nat × List Nat × List (Nat × Nat × Nat)) := some (zjW i &&& 15,zla i,shortHist zca 12 zla zgV i)
def zns : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm18,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,4,3,5] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,2,4,3,5] 0 i.val))),(pm15,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,5,3,4,2] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,5,3,4,2] 0 i.val))),(pm23,(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,5,4,3,2] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [0,1,5,4,3,2] 0 i.val))),(pm14,(fun i : Fin 64 => Fin.ofNat 64 (pA [1,0,3,2,5,4] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [1,0,3,2,5,4] 0 i.val))),(pm24,(fun i : Fin 64 => Fin.ofNat 64 (pA [1,0,4,2,5,3] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [1,0,3,5,2,4] 0 i.val))),(pm25,(fun i : Fin 64 => Fin.ofNat 64 (pA [1,0,3,5,2,4] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [1,0,4,2,5,3] 0 i.val))),(pm46,(fun i : Fin 64 => Fin.ofNat 64 (pA [1,0,4,5,2,3] 0 i.val)),(fun i : Fin 64 => Fin.ofNat 64 (pA [1,0,4,5,2,3] 0 i.val)))]
def zdV := zaa zns
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zuk : dM zca zcn 64 zdV := zah (by decide +kernel)
set_option maxRecDepth 16000 in
def zkI (i : Nat) : Nat :=
  let j := i / 16
  uP (bI j 78 (bI j 39 (bI j 19 (bI j 9 (bI j 4 (bI j 2 (bI j 1 (cB [0x7fc1e0e0c1,0x6850800000000000,0x3fd0e8,0x1c0e4edfc0000000,0x21e,0x10f1e0f2f7fe000,0x1000000000000000,0x878f07878f,0xc6c5880000000000,0xc028000ffd8e,0xfec76362c4000000,0x6c140027,0x5810101008086200,0x800000001600,0x80000,0x0,0x0,0x6204020200400000,0xc00002,0x0,0x20000000000000,0x100000000000,0x4ea6a38804000000,0x5821800ffd,0x720201010440000,0xc1080,0x11202814f032,0x80000400032]) (cB [0x50009ff31989831,0x40880000000001b,0x1820004c40804,0x0,0x0,0x20000024000,0xf008000000000082,0x8050001feb95c5c5,0x4040880000000000,0x8000004c080,0x0,0x0,0x0,0x0,0x180000002,0x101000000000000,0x0,0x4000000000000000,0x20000000,0x390201010220,0x8190000000000000,0x2908000198140a0,0x0,0x8400000,0x200000000000000,0x100000000000000,0x20000000000,0x8000000000])) (bI j 3 (cB [0x14000400,0x4000000000020,0xc00001,0x0,0x800000040,0x39160121366000,0x20080000000101a2,0x0,0x100000000000,0x0,0xe02000004c000000,0x20200001,0x1,0x0,0x0,0x90000000000,0x0,0x1200000000400000,0x1000000000008000,0x0,0x20000000000000,0x0,0x8000009000000000,0x28000000,0x400000480200,0x40,0xa0001fb69b45f72,0x40000000032]) (cB [0x3010080811,0x50a800000000001,0x868000d80904,0x828043000010,0x800004300001e,0x10,0x0,0x2020,0x10000000000000,0x8000c0000,0xfe87434284020000,0x60200001,0x10fe6331306200,0x900000000003610,0x19000a0810040218,0x100000008000000,0x0,0x0,0x0,0x1020402000420,0x300,0x0,0x100000000000,0x50000000,0x2002c16162c40040,0x6c1000,0x800032048243052,0x34]))) (bI j 6 (bI j 5 (cB [0x80a007fa5d2d8a9,0x3c04800800000019,0xc804504080201,0x400000,0x0,0x0,0x5000000000000000,0x8000508b00200000,0x1040080080000001,0xc84050010000,0x80000020000,0x0,0x1400600804b41200,0xa900000000003000,0x190800007da4d22f,0x108000000000,0xc0000001810,0x2c08840489400000,0x1000000006c28000,0x4020,0x2000000000000001,0x40000000000,0x4ea6a70000800000,0x40400003fd,0x65fe974953800000,0x20000000202000,0x800303008040082]) (cB [0x20000,0x0,0x0,0x0,0x0,0x225000040080000,0x1000000010000,0x2000,0x0,0x8000000000000,0x80000000000,0x0,0x32700804048200,0x0,0x0,0x0,0x800000080000,0x5601008010400000,0x6,0x2070fd53a3a3c00,0x1e00010004000101,0xc00103848a0010,0x80b0860800200,0x2001c241,0x40,0x0,0x2050b1400203c2,0x40000000000])) (bI j 7 (cB [0x0,0x100000000000000,0x18000000,0x808000000000,0x0,0x10fe733938e2000,0x1000000000010080,0x80c000000000000c,0x80080000000,0x0,0x4000000,0x0,0x10000000000000,0x200,0x800000800000000,0x202308008000000,0x200040c04,0x0,0x0,0x0,0x2000000000000000,0x80000100000000,0x0,0x4000008000,0x2120201011840000,0x1000,0x18001011309899e2,0x1000000010]) (bI j 8 (cB [0x8004000000000d1,0x800800000000,0x0,0x40000000,0x0,0x100000000000000,0x2000,0x4000008000000000,0x4000080000000,0x402000400000,0x200000000,0x20100020,0x330180c19d000,0x100000001018,0x100000200,0x40008000000,0x40000008000,0x4000000002000000,0x2000000,0x8200390300a0bc40,0x20010000000101,0x80010000000000,0x66b17f4800000000,0x48400003ed,0xe0201013840000,0x240000]) (cB [0x200000000000,0x270800000000008,0x48000002c0402,0x28101b900000000,0x24200042e,0x400000,0x0,0x8000000000002020,0x10000000020000,0x400000000000,0x8000001,0x10000040,0x20000006000000,0x0,0x800001000000002,0x282f10000000000,0x4840108ac04,0x0,0x80002000000,0x40000000000000,0x5e30000000001000,0x8080000785fd5d,0x2e97854000000000,0xc040008bfd,0x21fe8743e2800000,0x20000000640000,0x102100805102,0x1000000000]))))) (bI j 14 (bI j 11 (bI j 10 (cB [0x0,0x0,0x0,0x20100a2040000000,0x3204,0x10,0x0,0x0,0x2125800000000000,0x40402000c040,0x4000,0x0,0x0,0x400000000000000,0x8052030025822,0x8000000,0x0,0x620100a00400000,0x2,0x0,0x0,0x0,0x0,0x20000200000,0x2000002080000,0x120000000000000,0x106100005102]) (cB [0x107880407880,0x400000800200000,0x8000000,0x800000000000,0x400,0x200000001000012,0x4000000000000000,0x8080018ffa2d2f0a,0x100280080020001,0x2000c18010,0x0,0x0,0x31700400400a00,0x0,0x0,0x30000000000,0x80001,0x0,0x0,0x3600ce4e4180,0x2000010000000300,0x180800018000222,0x100000800000,0x0,0x61fcd66ae0e40000,0x20000000641000,0x100000000000])) (bI j 12 (cB [0x0,0x1804800000000000,0x200040c0201,0x800000000000,0x0,0x0,0x0,0x0,0x0,0x2000000800000,0x0,0x100000000,0x20000800021400,0x0,0x0,0x511008000000000,0x8000600001000,0x8000002400,0x0,0x8001060080464120,0x8990000000000000,0x10c001910944a7,0x800000,0x4000,0x4000001a0040400,0x120000000042000,0x2]) (bI j 13 (cB [0x1,0x0,0x1000004000000,0x100000200000,0x1000240,0x20000140000000,0x8000000002080,0x40009000000400,0x33a0c00000000000,0x840000cc060,0xe000009060004000,0x2000000004000001,0x0,0x0,0x0,0x100000000000000,0xc000,0x80000000,0x0,0x200000008000,0x4000000000000000,0x10000000,0x3053906000000000,0x840000d80,0x1e00028c8000040,0x20000000040000]) (cB [0x0,0x100000000000000,0x800a00000000001,0x40000,0x0,0x10000000400000,0x0,0x20,0x1110000000000000,0x800800000c0000,0x80000004000,0x0,0x0,0x5f00000000000000,0x80800117ead5674,0x311008000000000,0x40400009400,0x80000000,0x0,0x400000,0x0,0x1000000000000000,0x10000000000000,0x0,0x4e01009c8240000])))) (bI j 16 (bI j 15 (cB [0x100000000000,0x3804800000000100,0xac0201,0x1809c8300000000,0x120201046e,0x200000000000020,0x80000,0x410000000000,0x0,0x0,0x400000000,0x40,0x40002,0x1000000000000,0x4000000000060400,0x0,0x200000000000,0x0,0x0,0x310000440080,0x100000000900,0x400000000000000,0x201b8d5000000000,0x4840008ac5,0x40000000080400,0x0,0x80000f010004214,0x18000000000]) (cB [0x0,0x0,0x0,0x280000000,0x0,0x200000008000000,0xa008000400000000,0x10000400000,0x800000000,0x100000,0x80008000000,0x40,0x40000,0xa00000000000000,0x1000040001,0x6911500000000000,0x80c040008b6d0,0x808001020000,0x20000,0x4000240000444000,0x2000090000000020,0x20,0x10002000000000,0x40000000,0x400000888000000,0x100000000000100])) (bI j 17 (cB [0x20200,0xf956840000001000,0xc040008bdd317,0xcc66260c42000000,0x1f,0x10fee37170e2000,0x1009000000036000,0x8084020204,0x0,0x0,0x0,0x0,0x10000000408000,0x4200000000004000,0x4000800400000,0x0,0x0,0x1f8e470733c00000,0x0,0xf8783dc78e0,0x10000000000000,0x0,0x0,0x0,0x0,0x0,0x1800007004181c0a]) (bI j 18 (cB [0x200,0x0,0x0,0xc00000000000,0x0,0x400000,0x3000000000000000,0xc0000580801010,0x0,0x0,0xe71c747734000000,0x1,0x1000fe6b34307200,0x900000000001218,0x2000000500040204,0x0,0x0,0xe00800000400000,0x30154,0x140000000,0x5010000000000000,0x80000502c000,0x2000000000000000]) (cB [0x0,0x20,0x10000000000000,0x0,0x800004000,0xfc63333266000,0x2000000000010180,0x0,0x100000000200,0x500000000000040,0x8000000,0x20000000,0x2004005002024600,0x900000000000,0x0,0x10000000000,0x4,0x40800000,0x0,0x20000000004040,0x2020000000000000,0x8020,0x8ec6c58800000000,0x18200043fd,0x200341a1a3440000,0x1000000000c3000,0x1000100000000002])))))) (bI j 29 (bI j 24 (bI j 21 (bI j 20 (cB [0xc00487fa9d4d4b1,0x49800000000008,0x40020205400,0x200000000040000,0x0,0x10000000000,0x0,0x0,0x2024880000000008,0x400240c040,0x0,0x0,0x0,0x400000000000000,0x4000000406,0x0,0x0,0x0,0x20000010,0x9090100809260,0xc910000000000001,0xb0c000808984c4,0x4000008004800000,0x21000004,0x400200,0x1000,0x180192ff4ba5b152,0x2]) (cB [0xc00c93002004005,0x4000000001,0x0,0x100920240000000,0x2002246,0x0,0x0,0x0,0x0,0x80002000000,0x8000000,0x4000300,0x192600804901200,0x3100000000000010,0x30c2001ff399c9c,0x202088008000000,0x1860000e404,0x7fcd66a60e400000,0x200000000830000,0x330080410120,0x41,0x0,0x2000005000000000,0x800,0x0,0x0,0x80010fd72b8b9be,0x16])) (bI j 22 (cB [0x81890484891,0x9,0x0,0x0,0x0,0x10000101400000,0x6080,0x2020,0x0,0x2004080000,0x0,0x0,0x10912090912200,0x9900000000001000,0x290c084918944a48,0x20020c8008000000,0x100100200c40,0x20000000000400,0x0,0x0,0x0,0x0,0x0,0x0,0x400000000000000,0x800001,0x800810000000000,0x8000000000]) (bI j 23 (cB [0x400410000000000,0x200004000000000,0x20004200,0x2800200000000,0x41000040,0x820000000000000,0x3000000000000080,0x80c004848b04949b,0x100480000000,0x2000000,0x20000008000000,0x100000,0x400,0x1300000000000008,0x2004848084040,0x48000000,0x0,0x0,0x0,0x18000000000240,0x820000000000000,0x410400080000,0x41004000000,0x20020004,0x21f6d369bee40000,0x41000,0x106120909122,0x2]) (cB [0xc0008b092484a95,0x100000800000003,0x0,0x200282a040200000,0x4080000c,0x12,0x0,0x2020,0x4050000400000000,0x180000040000,0xfea75350c4020000,0x20308007,0x4003ff53a9a86200,0x3000100000000608,0x304203808402020,0x2000,0x0,0x1204004044c00000,0x200080000c204c0,0x400390000808220,0x1310000000000060,0x30c1001fe39d1d,0x66b179c800000000,0x8610007ed,0xe0201010440000,0x42000])))) (bI j 26 (bI j 25 (cB [0x8000000000,0x208800000000100,0x8400006c0402,0x281018540000000,0x4308006e,0xf000040c2a002,0x400002180,0x0,0x0,0x0,0x80800000000,0x0,0x4040000,0x0,0x200180000002,0x0,0x0,0x2000000000000000,0x0,0x0,0x0,0x18000030,0x100000000000,0xc00,0x7602014144c0000,0x20000002042000,0x44000000000000]) (cB [0xc2001f85fd5d533,0x4c54800000000008,0x60000ffd2e9,0xab558717c0000000,0x20300007f,0x250000c0002000,0x4080,0x0,0x1000000000000000,0x0,0x0,0x400000000,0x4000000,0x900000000000000,0x20800013804020a,0x0,0x0,0x2000000000000000,0x40000000,0x3b0080410120,0xa0d0000000000001,0x42080001b806020,0x800000,0x200800,0x0,0x0,0x10000000000])) (bI j 27 (cB [0x0,0x0,0x0,0x0,0x0,0xc080000000,0x80000,0x0,0x1000280000000004,0x21000000c4000,0x10004000,0x0,0x0,0xab00000000008000,0xc0001d8a40309,0x4858008000000,0x1000000400003c04,0x0,0x0,0x40000080,0x0,0x0,0x5000000000,0x0,0x20000000,0x0,0x20008000014]) (bI j 28 (cB [0x0,0x1800000000000,0x800001,0x100000280000000,0x40,0x2db41a40542000,0x4080,0x2000,0x1000000000000000,0x0,0x0,0x0,0x4040000,0x100800000100000,0x16800020a,0x40000000,0x0,0x0,0x0,0x400080,0x40000000000800,0x0,0x10100800000000,0x1020000800,0x400000808000000,0x0,0x180002f74c5f355a,0x4]) (cB [0x7ea954545f,0x55ab800000000008,0x40000003e562b,0x2bea6a54c0000000,0x20000001e,0x2000,0x3000000000000000,0x80000f80803010,0x0,0x0,0x0,0x0,0xf6a4af54aa00,0x5f00000000001000,0x8080000feaa5456,0x1000000000000,0x40000000000,0x800080000000,0x2000000,0x4000,0x0,0x0,0x10500800000000,0x18100001c4]))))) (bI j 34 (bI j 31 (bI j 30 (cB [0x0,0x100000000000000,0x1,0x808000000000,0x0,0x110040c0c02000,0x8,0x0,0x0,0x0,0x0,0x0,0x2000000,0x0,0x2,0x101000000000000,0x0,0x3e02000000c00000,0x20044,0x0,0x2000000000000000,0x2000,0x7038000800000000,0xb40,0x0,0x0,0x100001f0040a0e0a]) (cB [0x802017ca955555f,0x480800000000088,0x400100002c0620,0x0,0x0,0x0,0x1000000000000000,0x83080c01010,0xaaaae80000000008,0x40000003caba,0xfe974942a4000000,0xa0202005,0xff43a0297200,0x1900000000005204,0x2800003018402008,0x2048408002000,0x100100002850,0x20000000000000,0x0,0x40000000,0x0,0x2000,0x0,0x4,0x0,0x100000000800000,0x1002407005b0040a])) (bI j 32 (cB [0x0,0x0,0x100,0x2c004040c0000000,0x8000002004016,0x0,0x0,0x0,0x20c80000000000,0x100100001c400,0x200000,0x80000400,0x108aff4ba4a95201,0xb00000000005000,0x2000084450a40005,0x2000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1002500004081a,0x40]) (bI j 33 (cB [0x8,0x0,0x0,0x100018240000000,0x800001148,0x2000000000000000,0x9000000000000001,0x8080510ffa25654a,0x4040880000000000,0x100401c400,0x200000000020001,0x0,0x800e15400000200,0x10,0x20000,0xe8aa548000000000,0x4040188be56,0x1604100204400000,0x1000080000008000,0x40000000000,0x0,0x0,0x18000800000000,0x108b40,0x400000000,0x0,0x100422f000020402]) (cB [0x8080076ad505503,0x280000000000028,0x200,0x100014000000000,0x0,0x8000000000,0x2000000000000000,0xc00040,0x8180000000000,0x4000008560,0x0,0x0,0x0,0x0,0x2000000000000000,0x0,0x2,0x0,0x8000000,0x100000080008040,0x5000000000000000,0x4000,0x100000000000,0x0,0x182a00810240000,0x0,0xc100040406])))) (bI j 36 (bI j 35 (cB [0x0,0x100000000000000,0x0,0x0,0x0,0x4000,0x0,0x0,0x0,0x0,0x0,0x80000000,0x400,0x100000000000000,0x2000000000000000,0x3808000000001,0x400003857,0xc00004100c00000,0x48020000,0x1002db41a4015a0,0xc0000000000500,0x20,0x1010006000000000,0x4000000000,0x808200000,0x0,0x2100004041a]) (cB [0x0,0x0,0x10000000000000,0x808200000000,0x20000,0x40014000,0x9000000000000000,0x1c80200020,0x7a95680000000012,0x14040400bdd31,0xe0100c042c000000,0x480202407,0xfd43a3a34600,0xa200000000001010,0x808000078a00101,0x10008000000,0x60000010000,0x4000004800000,0x200000001000010,0x240,0x20000000000000,0x20000000,0x80000000200,0x40000000,0x80000,0x200000,0x100003f140020346,0x1000000010])) (bI j 37 (cB [0x400000000002,0x1800000000000,0x0,0x80000000,0x80000000000,0x9040000146000,0x2000000000000000,0x0,0x100000000200,0x0,0x248000000,0x0,0x400,0x200000000000000,0x104000000000,0x800000000000,0x0,0x0,0x0,0x40,0xb30000000000000,0x80200007e29d0d,0x8101009804000000,0x100004000038240,0x21206101004c3040,0x100000000002001]) (bI j 38 (cB [0x800105804025809,0x0,0x0,0x80000100000000,0x2001000,0x40000000,0x0,0x0,0x200000000000000,0x0,0x602100004c000000,0x80001,0x8,0x0,0x2,0x2020598040000000,0x40400003c14,0x4000004800000,0x3000000,0x208000000000240,0x0,0x0,0x4000001000000000,0x20000000,0x40100000280000,0x0,0x24]) (cB [0x400427ea9d1d1a3,0x1051000000000008,0x200801c245410,0x800000883040000,0x200000000,0x20000024000,0x2000000004000000,0x0,0x100000000200,0x0,0x603008042c000000,0x200045,0x1,0x0,0x0,0x810000000000,0x2,0x842b00402ac00000,0x8000000000010010,0x40,0x3020000000000000,0x10,0x0,0x0,0x8c2a004068c0000,0x200000,0x1000000040000044,0x400000]))))))) (bI j 58 (bI j 48 (bI j 43 (bI j 41 (bI j 40 (cB [0x10400010000012,0x1000000000000,0x820000000,0xc0000000,0x1000,0x4000008000204000,0x2000000000000001,0x200000000010,0x100000000000,0x40,0xe28004168c000000,0x20200005,0x2000022400,0x200000000000000,0xa000000000000001,0x10000000000,0x400000000,0x800000,0x0,0x202000,0x1000000000000000,0x10,0x18001000000000,0x0,0x4080000,0x0,0x204]) (cB [0x800007ca4d32fab,0x80d7800000000009,0x8400003c5300,0x288040e9c0000000,0x4200403e,0x40404000,0x8000000000000,0x40000000000,0x0,0x2000040,0x800000000,0x200000,0x40000,0x8700000000000000,0xc000078880203,0x40002000,0x0,0x2008080800000,0x0,0x100404040,0x2020000000000000,0x0,0x5000100000000000,0x0,0x80000080000,0x0,0x400040c])) (bI j 42 (cB [0x0,0x0,0x0,0x69348bea40000000,0x1f,0xf34e5a5b5a000,0x5000000000000000,0x80000ffa2d0d2a,0x1010200000000000,0x4000400007c010,0x800004000,0x2000010000,0x40006,0x100000100200,0x202,0x20000000000,0x400000000,0x80000000,0x80000001000,0xf0400424420,0x2040080000030301,0x800000002020,0x10100000000000,0x100c00002000000,0x3e0080808140000,0x20000000042000,0x100000f000040402,0x32]) (cB [0x200,0x100800000000000,0x580001,0x0,0x0,0x0,0x0,0x20,0x200000000000,0x400000000010,0x8000000000000,0x0,0x1000400040800,0xa100800000000000,0x30200007fa092da,0x405208040000000,0x1000000000081820,0xe0201012c400400,0x80000020000,0x0,0x2800000000000000,0x20,0x50540800000000,0x1840064184,0x1e200082a040200,0x1000000000c2000,0x600000000400,0x8000000002]))) (bI j 45 (bI j 44 (cB [0x20200,0x100000000000000,0x600040000,0x808000000000,0x20,0x101400010,0xd000000000000080,0x8080000f80200020,0x10200000000000,0x3000000000000,0x810000000,0x180000000,0x800000000040800,0x600000000000000,0x20000,0x6969528000000000,0x20007fd1,0xc10048490000000,0x200080000004002,0x404000,0x2000000000000000,0x0,0x100000000000,0x0,0x8000000,0x0,0x30000040400]) (cB [0x0,0x102800000000000,0x1802060d80101,0x8000200010,0xc0000000,0x80701004051a000,0x4000000400000104,0x2020,0x1010280000000000,0x84000024010,0x80800000000,0x800000200000,0x1000000040018,0x400800000000100,0xc0000000202,0xf878708000000000,0xc0400003ff0,0x7ffc7e3e3c400000,0x6034002,0x1300e07070e20,0x8190000000000361,0x1908000890140a7,0x81c1c38840000200,0xd860004c03,0x2241c0e0e1c40000,0x800000000642000,0x100000000002])) (bI j 46 (cB [0x800098000202201,0x7870864000200000,0xc0500073ff0f8,0x904860a40000000,0x6830003e4,0x410ff8bc5f192000,0x5000000100032111,0x8000518b00200000,0x10c0080080004001,0x4000c80450010001,0xc010096824000002,0x64022800,0x1cfbc9e43fd200,0x2100000000003214,0x1800000e30200000,0x1819128000000000,0x22000d8500075811,0xc00000000400000,0x200000006018000,0x4000,0x2000000001800000,0x840000000000,0x4f272708008000c0,0x404101e3fe,0xf1fb278787040000,0x20000800202040,0x1020789100020380,0x1006000008]) (bI j 47 (cB [0x48880000c0,0x80e0800803220000,0x40408162c4000,0x80,0x0,0x600000000400000,0x1800000000000000,0x804203c08984c4cf,0x7880080000000,0x8000000002200000,0x3800,0x4000020,0x10000000000000,0x8000000004000800,0x4200800000000,0x400001000000,0x210040000,0x660301833a400200,0x20000000200080b,0x4200000400000,0x80000000000000,0x80000010000000,0x4000000000,0x4000000800,0xf7206014178c0000,0x200000002000c0,0x20000000000004,0x10]) (cB [0x8202c7dcce61fe9,0x270800000000008,0x10061c0402,0x0,0x0,0x400000000000000,0x1000000000010000,0x202c58080404e,0x2137200000000000,0x404101e5c051,0x80800000000,0x400020200000,0x60000000040000,0x200000020001000,0x400001000000000,0x180000000000000,0x180000,0x80000000,0x200000c,0x407eb0100a0bc40,0x100,0x80800000000000,0x100,0x40000100000,0xf1e0ff97978c0000,0x202080,0x100032ff8bc5e192]))))) (bI j 53 (bI j 50 (bI j 49 (cB [0x191044227049,0x3c4c840800000018,0x82000c884a25,0x40000,0x200,0x120000008000004,0x40000000080,0x104000100000a000,0x200000400008000,0x2000480000,0x603019d064000200,0x24000066,0xf00000483200,0xc000200,0x0,0x0,0x0,0x6000008000000000,0x0,0x4000,0x4000000000000000,0x10000000,0x200000000000,0x800,0x66c01829c8340000,0x8000040000,0xf000144402,0x240002]) (cB [0x0,0x0,0x0,0x888000000000,0x4800050000400,0x0,0x0,0x800000020,0x10000000000000,0x0,0x8c800000000,0x800004000046,0x4000000,0x0,0x0,0xb33a1f8000000000,0x404000cbf66,0x4a00098c80400000,0x8000000000004,0x4000,0x0,0x1000000000000000,0x10000000000000,0x0,0x64e01009c8240000])) (bI j 51 (cB [0x100000000000,0x3804800000000100,0xcac0201,0x1809c8300000000,0x120000076e,0x200000000000000,0x80000,0x410000000000,0x0,0x0,0x400000000,0x40,0x40002,0x1000000000000,0x4000000000060400,0x0,0x200000000000,0x0,0x0,0x2310000460080,0x18a0000400000900,0x908001b5884037,0x4001085200000000,0x2200000200013c0,0x400,0x0,0x1000200000008000,0x800000]) (bI j 52 (cB [0x10000400000a,0x10000000a0000,0x40008800001,0x8000000000,0x0,0x200008000214000,0x1000000000000000,0x800116dc0e232c,0x1190004000008000,0x84000090001,0x80800020000,0x40,0x22000044640000,0xcd00014010200001,0x800197bc61ff2,0xf978748400000000,0xc040008bff2,0x4381c0e38400400,0x200000006020002,0x1000000040020,0x650000000000000,0x18080018b062303,0x11920000800200,0xc04800c182,0x6c019c9c8300040,0x20000000602000,0x80030000646400,0x1000400030]) (cB [0x200,0x3824800000000000,0xc00000c882211,0x180c8c1842040010,0x602200048,0x442000112,0x9000000000000018,0x8080001306432726,0x8787084000000001,0xc0000043ff0f,0xfdc6e2e1c4000000,0x200000006c000021,0x5888101008086201,0x1000,0x0,0x2000000000000,0x0,0x2000000000000,0x0,0x0,0x0,0x0,0x101000800000000,0x4042])))) (bI j 55 (bI j 54 (cB [0x8080000000000,0x1000000000000,0x20004000000,0x341a1a3440000000,0xc1000200,0x881000000120010,0x1000000000000000,0x0,0x2122880000000000,0x1868004c4241,0x20000000000000,0x1,0x0,0x4900000000000000,0x20c000990442228,0x40000000000,0x400,0x0,0x0,0x5810ff53a9a9620,0x4910000000000100,0x8000c0c0808040,0x0,0x0,0x0,0x0,0x800000000000]) (cB [0x0,0x0,0x0,0x0,0x200,0x800000,0x1000000000000000,0x8081302488001018,0x0,0x0,0x1000000000,0x0,0x4000000000000,0x0,0x4000080000,0x2008000000000,0x40000200800,0x0,0x0,0x1000000000000,0x0,0x480000000,0x0,0x0,0x10000000,0x0,0x800])) (bI j 56 (cB [0xc4048a8000021,0x8,0x0,0x200000000000000,0x0,0x800010000000000,0x0,0x0,0x2025c80000000008,0x40012000c040,0x0,0x0,0x0,0x0,0xc0000000002,0x101000000000000,0x40000,0x0,0x0,0x40000000000000,0x4b30000000001000,0x8002c004808040,0x2e96c54800000000,0xc80050cbfd,0x6040100920241000,0x800000000040228]) (bI j 57 (cB [0x0,0x0,0x0,0x0,0x0,0x10000,0x5000000000000000,0x84510b00200000,0x2000000080,0x0,0x1,0x0,0x1000,0x0,0x8000000000200,0x12e048000000000,0x1088c02,0x8000000000,0x0,0x80000000,0x0,0x0,0x0,0x0,0x4020000000240000,0x100000000000000]) (cB [0x80000000000,0x4000000000,0x4000000,0x200000,0x0,0x10000,0x0,0x400000000000,0x4,0x2000000000000,0x8000000,0x2800,0x1422400004100208,0x4800000200200,0x200,0x12d048000002000,0x5089802,0x1fba5d1d17c00000,0x2000002,0x1030804000020,0x0,0x0,0x0,0x0,0x2000000008000000,0x2000,0x4100000000000])))))) (bI j 68 (bI j 63 (bI j 60 (bI j 59 (cB [0x84800202001,0x1024800000000000,0x40404048c2211,0x200000,0x800000200,0x8100000000000000,0x8000000000100,0x80208000000000,0x20000400000000,0x40000020,0x80020000000,0x2000,0x1010000000000000,0xe300000000000000,0x80c000848e02121,0x8040000000,0x652400,0x8000000000002000,0x30,0x400000000040,0x20000000000000,0x0,0x1000000000,0x1000,0x2000000000080000,0x1000]) (cB [0x80000000002,0x17f4800000000000,0xc8000043ef279,0x1000001041000000,0x20c,0x11608440448a000,0xc8000400006100,0x20,0x10000000000180,0x40000000000000,0x800000000,0x800000000020,0x0,0xe100000000000000,0x180800087fe1f0f0,0x193c348008000000,0xc04050c8832,0x2000080800010000,0x200021004,0x2220004400000,0x400000000000,0x111000003,0x181830800000000,0xc040004083,0x2000000000041000,0x0,0x1000300000404402,0xc0000400000])) (bI j 61 (cB [0x800067fa9d4d4a1,0x6858800000000010,0x80500023fd0e8,0x2410100c40200000,0x400000102,0x0,0x0,0x0,0x0,0x0,0x22010100c4000000,0x40080210,0x1,0x900000000000000,0x1008020118040248,0x0,0x0,0x800001000000,0x1,0x400000,0x0,0x0,0x2000000000000,0x0,0x1062010000c40000,0x400800]) (bI j 62 (cB [0x200,0x2658804000000000,0x8060007044c26,0x40200000,0x0,0x0,0x1000000000000000,0x40004000000000,0x3061480000000000,0x8040003cc060,0xe0000030a4000000,0x40000015,0x0,0x400000000000000,0x0,0x0,0x1000,0x0,0x0,0xc00000,0x10000000000000,0x0,0x66b17d4800000000,0x80400033ed,0x18e0201010840000,0x400000,0x10000d7014080c4a,0x8000000020]) (cB [0x400107800020625,0x4000000010,0x0,0x18000000000,0x0,0x80000080c00000,0x0,0x0,0x9685480000000000,0xc0440033fd2e,0xfe87436284000000,0x64280001,0x210080310201,0x3011,0x0,0x0,0x0,0x420100620400000,0x100000000602a030,0x0,0x2050000000000000,0x18080500b002480,0x0,0x0,0x10000000000,0x0,0x1400006100003102,0x30])))) (bI j 65 (bI j 64 (cB [0xc800e10944a5899,0x804000000019,0x24000000000,0x182848340000000,0x6420001ac,0x1f000142402000,0xd000000000032100,0x80880067ba62fd2a,0xc7c7880000000001,0xd8600043ff8f,0x23c1e1e3c4024000,0x20300020,0x10000000000200,0x100000000001200,0x800000800000000,0x8000000000,0x486002e8000,0x8028000028c02400,0x1200000006030012,0x84003ffd3e9e8e20,0x710000000000101,0x80d20007fe1f0f,0x2010804860000200,0x8041088c0,0x0,0x0,0x40000]) (cB [0x0,0x0,0x0,0x28004044c0000000,0x20004c092,0x0,0x0,0x0,0x8000000000000,0x0,0x100000000000000,0x0,0x4000308040006200,0x200,0x0,0x0,0x0,0x80000000,0x80000020000,0x40000000000000,0x310000000001001,0x20004800202,0x101018800000000,0x18610003c2,0x100000000000000,0x0,0x40000000000000])) (bI j 66 (cB [0x420018868343471,0x101880080000000b,0x100180101c042010,0x0,0x0,0x40080000000000,0x1000000444000100,0x2000000000000,0x898b880000000000,0x5860800e4381,0x20c0c0c0c4000000,0xc1440e1,0x400130d06868e200,0x100000000001210,0x8200000000000,0x8000000000,0x410000000,0x6000080880400000,0x200000000020804,0x4444000,0x10000004000001,0x800820130000000,0x41a1a38800800000,0x4041000e43,0x7ff97cae3a40000,0x20000000603000,0x1a0002ffc3e171c2,0x80000400030]) (bI j 67 (cB [0x24051808040421,0x8,0x0,0x404000000000,0x80,0x80000000,0x0,0x4000,0x0,0x40,0x100000000000,0x0,0x0,0x0,0x0,0x200000000000,0x0,0x2c00840081400000,0x801148,0x0,0x40000000000000,0x0,0x180c00800000000,0x8c2,0x8000000000]) (cB [0x0,0x0,0x20040200000000,0x0,0x1000000000,0x4000,0x1000000400000100,0x2040001200030080,0x4000020100,0x1,0xc100806904000000,0x8000004,0x220c06070c200,0x6908100040003010,0x808000198643238,0x1100000000000000,0x8000,0x4000000000400000,0x20000,0x200000000020,0x10000000000001,0x400800258000000,0x800000,0x20000010800,0xc00904000ac0040,0x20000000602000]))))) (bI j 73 (bI j 70 (bI j 69 (cB [0x0,0x0,0x40000000000,0x800000800000010,0x40,0x240c06400c2000,0x81000100004080,0x2020,0x1000000400000100,0x0,0x80000020000,0x0,0x0,0x0,0x2000000202,0x1000000000000000,0x0,0x4000088000002000,0x0,0x260c86474d20,0x47f0800000000041,0x80800007ee9747,0x63b5dbb800000000,0x40400003e7,0xe180c0c1840000,0x200000]) (cB [0x800220000000000,0x0,0x0,0x180c0c1840000000,0x200000016,0x2170c4686cca000,0x1000008000010100,0x8040018384002120,0x0,0x0,0x0,0x0,0x60000000240000,0x0,0xa000800002222,0x0,0x0,0x80880000000,0x9000000021004,0x0,0x0,0x800120000000,0x0,0x0,0x4000008c00000000,0x0,0x400000])) (bI j 71 (cB [0x800100000202200,0x98b1800000000000,0x44040109ac3418,0x108044040000000,0x2001000616,0x0,0x0,0xa0008000000000,0x0,0x0,0x0,0x200000048,0xf2eeeaeafa00,0xe900000000001010,0x280808157fe5f270,0xf82a748000000000,0x1406000c3ff0,0x2e00840081400400,0x120000000000004c,0x2320b4400202060,0x10000000100,0x0,0x8000000000000,0x0,0x400000000]) (bI j 72 (cB [0x10000,0x204800000000000,0x14020008140010,0x8000000040000,0x0,0x0,0x9000000000040000,0x40018384000062,0x2,0x1004008000000,0x6381c0d1e4000000,0xa0280020,0x50308040103201,0x8100004001000,0x80a000000a00000,0x800000000000000,0x40420100000,0x8008000000000000,0x88002020000,0x4001000000000000,0x4690800000000001,0x280008551864323,0x0,0x4000002001,0x4000008000000000,0x800000,0x280000000000,0x40]) (cB [0x80514b862303061,0x810804000000008,0x400800c1c3008,0x40000,0x0,0x80054000000000,0x1000000000010100,0x8080313586031306,0x8081080400000000,0x400801c2c101,0x8c0000204000,0x40,0x24000000000010,0x108000000000010,0x2808080450ec3035,0x2010000001000,0x6,0x9000000000000,0x2020001,0x404000000,0x100,0x200,0x0,0x10000000000,0x1000900010000000,0x202000,0x10000c0000000000,0x40])))) (bI j 75 (bI j 74 (cB [0x811286032006d,0x104000000080028,0x10000001,0x8800000000000,0x100000000000400,0x600000000000000,0x9000000000040000,0x8080815386432326,0x2,0x1004009b00000,0xfb87c7c78c000000,0x60200009,0x207cf10002030400,0x1200000624001000,0x100000000000,0xf878718000000000,0x1000040600043f54,0x5601008402430400,0x1200000000000004,0x0,0x0,0x20,0x0,0x0,0x2162a080028c0000,0x800040000201000,0x10000004]) (cB [0x800000008000202,0x1051800000200000,0x40400043c5410,0x200000480040001,0x8000100000200,0x4000,0x3000000000000000,0x4001000000000000,0x100000000000,0x100040,0x20000008000000,0x0,0x1400200000000400,0x200000000000000,0x80000,0x118000010000,0x1000c0408000010,0x800400,0x8007000000,0x40,0x220000000000300,0x180010000020000,0x4383839800000000,0x4050004243,0xe1204080804c0200,0x1820000000200000,0x1100200000002000,0x10])) (bI j 76 (cB [0xa00080000000001,0x19820000000000,0xc050004001000,0x400000480000000,0x8000300000000,0x8491d06263c6000,0x2400000000030180,0xc09003848a82020a,0x106080020000,0x200000000000,0x8000000001,0x200000220040,0x4004000004400,0x2204000000003000,0x1808000200280000,0x912000000200,0x1000c0400090010,0x40800000,0x8006000000,0x4b1c86263d60,0x220000020000321,0x180800020020000,0x101111800000000,0xc040089001,0x80000,0x8000002000,0x800000020200]) (bI j 77 (cB [0x8000000,0x1101800000000000,0x4040000000411,0x793c8ffa40000010,0x60200001f,0xf3ce7a7bda000,0x5000000000030100,0x8080010ffe2f0f2e,0x110200000000001,0x6000000000c7c011,0x808020000a0,0x0,0x20000044440000,0x10,0x212,0x1119108000000000,0xc0520033c10,0x808081202000,0x200000000,0xcf00400040a0,0x2000080000000301,0x10800000000000,0x1000002000000000,0x40000000,0x0,0x0,0x100000000400000a]) (cB [0x100000000200,0x7970c00000000000,0xc06000c3ff069,0x201010840040010,0x20008140e,0x2,0x0,0x4,0x9193080000000000,0xc06000c18300,0xe10008c904004001,0x20000000042000e1,0x40018,0x10,0x100003800000212,0x2000,0x0,0x200010180000000,0x0,0x806000000024000,0x2000000000000000,0x800300000003,0x1101102800000000,0x60000040000400,0xc000004048000040,0x20000000])))))))) (bI j 117 (bI j 97 (bI j 87 (bI j 82 (bI j 80 (bI j 79 (cB [0xa000830e0323ae1,0x520804000600003,0x4182004,0x800240009,0xc000002000100,0x100000444400010,0x8000000000140,0x800030000000020,0x110200000020000,0x6000404000a00001,0x404810000000,0xc0,0x802160c46464ca00,0x4080800048000010,0x1001830401212,0x809000008003200,0xc000020000000,0x80000000,0x80000000000,0x4000,0x4000000,0x800040000000,0x111100000000300,0x60000042000000,0x21ff078383060000,0x0,0x10001cff93c9c9c2,0x8000000020]) (cB [0x1,0x800000000000,0x0,0x3019f0a40000000,0x80000040200818e,0x800000,0x4000000000400000,0x4800004040,0x1000000000001,0x0,0xc000180004000000,0x80000040000040,0x4000,0x0,0x10000004,0x1202308000000000,0x80400070c24,0x0,0x0,0x187000480c020,0x200000000000200,0x80000000,0x0,0x8018400,0x0,0x800000040000,0x11001cff8bc5e192,0x32])) (bI j 81 (cB [0x8050630067a120d,0x18,0x400000000001,0x11008c1240000000,0x60200038c,0x800ff93c9c9e2000,0x1000000000010001,0x8002c4c7fc9e4e4f,0x80c108070010000,0x1c024000,0x4000001020400019,0x1804400000000120,0x0,0x2200000000000000,0x8000c4c40880000,0x10003001000,0x0,0x60201003e400000,0x40400000000903,0x0,0x0,0x0,0x20300000000000,0x80100000000000,0x200000000018,0x4004002000008,0x581890000809e6,0x800000000]) (cB [0x1000c78080404f0,0x260080700100000,0x22bc0201,0x10800030008,0x2,0x604fd93c3c382000,0x40010002,0x8000000000000000,0x4000000000000,0x900040000013c400,0x18,0x0,0x80012000012000,0x8000000000000000,0x130248880101,0x2800000031200,0x8800000000202840,0x9621004062400100,0x40400000000440,0x400000000000,0x2000000000000000,0x30003020080000,0x40080e0400303120,0x800000200213c4,0x20200000800018,0x0,0x1080fd82c0c812,0x200052]))) (bI j 84 (bI j 83 (cB [0x81840200409,0x40800000028,0x200000,0x0,0x0,0xb00000000810000,0xc00200040000,0x548300000000,0x40030000,0x8000000000018000,0x4000000000006001,0x800c00000000d21,0xa00000000000,0x800140060000000,0x100000020002204,0x4402001000,0x8000000000,0x0,0x0,0x0,0x20000000,0x0,0x300800000000,0x20180,0x10002010,0x0,0x2000000000800,0x2000000]) (cB [0x405000000401,0x3011800400000000,0x40006203f64b0,0x22080808c0000008,0x8000202000212,0x10000044182,0x2000000000010000,0x800000,0x100000000000,0x8000400000038040,0x1800,0x0,0x1880101000000400,0x2200060000000000,0x8000c4808880000,0x108003001000,0x40002202c46,0x2000000010080,0x10,0x0,0x2200000000002000,0xb000d400888202,0x300000,0x0,0x4000,0x10,0x8043010000244,0x100200000100])) (bI j 85 (cB [0x0,0xffc800000000000,0x48002003ee673,0x201013f40008000,0xe,0x0,0x0,0x100000000000,0x2027d80010100010,0x2002c040,0xe328909bd4000000,0xc0040002c203003,0x100000008120,0x60000002,0x100080000000000,0x1035a0001000000,0x100000000043c00,0xe00000020040000,0x8000000000,0x1080000404002,0x2000000000000000,0x80000202,0x100400000000,0x0,0x8100000,0x4008000030,0x2000000000000,0x100000040000]) (bI j 86 (cB [0x6000000030000,0x100000202000000,0x600000000,0x2201417c80020000,0x40040020000180d6,0x1000000080200,0x2000000200100000,0x200000000000,0x2f2f980000002008,0x40006003c1ff,0xfb259190fc002000,0x20000021,0x10f998cd366e00,0x100000000001200,0x838400000,0x0,0x0,0x0,0x42,0x117084484c0a0,0x11000080000061,0x10038b000000,0x0,0x0,0xc000000000000000,0x0,0x610000000000]) (cB [0x100388000000000,0x100000000000000,0x400000,0x8000001200,0x900000002000200,0x0,0x0,0x108000000000,0x8002480000,0x1840000,0xc0000000004,0x80000000000800,0x10000000040000,0x300000000000000,0x20b58482121,0x8800000000,0x800c8000,0x0,0x8200020000002,0x10f26ecaca7a0,0xc90000000000100,0x2900080d7fc5e26,0x101234800000000,0x1400800c8c2,0x6100000000002040,0x800000000,0x10ba3088444892,0x40]))))) (bI j 92 (bI j 89 (bI j 88 (cB [0x0,0x1020800080100020,0x2865c2110,0x1000000000000030,0x8000000400e2e,0x987080000000002,0x208000800000040,0x400000a00000,0x128090009010000,0x8000400040628661,0x10001000800000,0x4400000000008,0x1000000000000000,0x1000,0x80000040000,0x10000,0x0,0x0,0xa0000000000200,0x4040,0x0,0x0,0x101000000000,0x0,0x0,0x140000800024,0x12000000000000,0x2000040]) (cB [0x9080000000000,0xf0e1800000000020,0xc0200053f60f0,0x32080838c0000000,0x8000202440212,0x100010000004182,0x2000000000030000,0x4080002000800000,0x100000000000,0xc00000000000,0x8000000,0x10000020,0x4001000000400,0x200000000003000,0x1800000800000000,0x10000000000,0x900000000040000,0x8000000000800000,0x30,0x40194fc93c1c1840,0x820000008000100,0x80000084800000,0x400,0x0,0x2120000000080000,0x100000000000003,0x1800000000000])) (bI j 90 (cB [0xca0800000200,0x0,0x0,0x0,0x0,0x1949090c0c1a6000,0x8000800000040,0xc8100000000,0x4100000008000,0x1000c0400053c000,0x208000000,0x0,0x0,0x0,0x0,0x410000000000,0x89000c0000002400,0x800001,0x800000000,0x1000000001040,0x20000000000000,0x100a0000000,0x120,0x90000000001000,0x800000000000000,0x0,0x800000000000004]) (bI j 91 (cB [0x0,0x1000000000000,0x0,0x2490008000,0x200000280,0x40000000124000,0x2,0x0,0x80c100012000000,0x9000c0009813c400,0x232084870c000018,0x800060100129,0x10000000000480,0xc200000024000000,0x3100a30c80000,0xc00,0x8400000000040000,0x2000000800080,0x48000000002,0x8000000000048,0x1820000000140000,0x2080080000,0xc1000000120,0x90000000000804,0x800000004080000,0x800000003,0x2103100404504,0x36]) (cB [0x81888222282,0x0,0x0,0x200808080000000,0x0,0x4000,0x2400200000000000,0x0,0x27250a0000000000,0x400033fe4f,0xff078382c4000000,0x200001,0x3310884907200,0x2100000000000408,0x8,0x0,0x20000000000000,0x1001000040000000,0x0,0x201080400000,0x40,0x0,0x820a099800000000,0x9820000e44,0x31ff078382c48000,0x4100010000002002,0x1183008048010,0x8180008400])))) (bI j 94 (bI j 93 (cB [0x800044080000023,0x100090408010,0x4000,0x2000000000000000,0x0,0x0,0x1000000800000000,0x8c188040403,0x800000,0x0,0x0,0x0,0x80840000,0x80000080040000,0x8000008000800040,0x2020198000004000,0x80000062448,0x22010102c400048,0x1000100000010001,0x80004,0x4000,0x40000000,0x2f17454800000000,0x40000844100bfe,0x0,0x2000002000,0x1040a3008049050,0x180180000]) (cB [0x4104b802000004,0x20000000100c0000,0x8844000284210,0x100000010004800,0x0,0x8000000000,0x0,0x1000000000420000,0x20004048009,0x20,0x200,0x200300400000000,0x402500044104200,0x10090000210,0x9000000048042000,0x125048000404800,0x41009c02,0x20,0x0,0x20000000000000,0x90b0001001802000,0x100080015804024,0x2212454800090000,0x400000c4,0x40000100000000,0x0,0x90004000008])) (bI j 95 (cB [0x20000000000,0x100800000000000,0x80001,0x808040000000,0x0,0xb008000200000,0x0,0x400000000,0x8000000000000,0x20,0x210090000000000,0x400400000000000,0x10004000000,0x0,0x40000,0x100108001004000,0x2000000000000040,0x1000000000000,0x100000000000,0x80000,0x0,0x4,0x8f0f0d1800000000,0x100080409813fe,0x922400404888000,0xc080040004e,0x2204b128020206,0x2000020]) (bI j 96 (cB [0x4000000000,0x100000000000000,0x180200000,0x4008000181,0x80800400002016,0x49122828346000,0x200000000020000,0x408000000,0x10000000000000,0x20400,0x400000000,0x1000000000000,0xed92c0c04200,0x20000000002010,0x300004180800101,0x10000000000,0x800080500203044,0x880000,0x0,0x40,0x0,0x0,0x200000000,0x0,0x90000,0x0,0x800110020200,0x600200000]) (cB [0x800404080000022,0x1300090000010,0x0,0x80000000,0x2000000000000,0x80100000046000,0x400000000020100,0x1000000,0x0,0x400,0x0,0x200000000,0x0,0x200000000000000,0x800000,0x80802000000080,0x800080400208040,0x20000040000100,0x80040000000000,0xa1080000420,0x201,0x80000,0x0,0x4000080000000000,0x0,0x0,0x1000008100404442,0x200720000006])))))) (bI j 107 (bI j 102 (bI j 99 (bI j 98 (cB [0x200,0x100000000000000,0x1,0x10010000,0x0,0x0,0x980000000,0x20000,0x9180001008000,0x4880000108001,0x4000000400000802,0x1000240080000,0x0,0xb900000010000000,0x10800007dc4e21f,0x188000000000,0x1c40,0x0,0x0,0x20000000000000,0x120002000,0x20000000,0x8200019800000000,0x80000002c0,0x3e3098188d40000,0x110000c2000,0x800100000000041]) (cB [0x30,0x0,0x800000000000,0x4,0x0,0x87100444440000,0x208000800000040,0x4000020220,0x121500000000c000,0x441c400,0x800820002,0x300800000002,0x200000000000100,0x10000009c000000,0x20040802300,0x1000000120800,0x0,0xd62018504cc80048,0x100024000080,0x40004b0000002400,0x8001200,0x800000810000000,0xff0f0d98000000a0,0x80400003c1,0x1fff379ab2a48000,0x3000,0x180000ff83c15952])) (bI j 100 (cB [0x57800000c28,0x10400,0x0,0x0,0x0,0x0,0x4000000000000000,0x2000105b80200020,0x200001004000,0x98000,0x0,0x0,0x0,0x0,0x100000000,0x0,0x0,0x1c20480208000000,0x44000004030000,0x8,0x0,0x0,0x100000,0x200,0x182008000000000,0x4800000000000,0x0,0x200]) (bI j 101 (cB [0x0,0x0,0x200000,0x400080000000,0x100400000000c,0x0,0x9000000000000000,0x20000007800000e2,0x200000,0x0,0xe000000000000000,0x180400000401,0x0,0x100000000000000,0x100c0005f08d2208,0x1000000,0x2,0x402000000900000,0x0,0x180000008,0x0,0x120c00056088220,0x4010000000120000,0x80000002800,0x300000000000,0x0,0xa6010020004,0x200]) (cB [0x7380c060e29,0x800000000002,0x0,0x40000000,0x40000001fe,0xbfeb3cbcb46000,0x3000000000020182,0xc00007f59e0e0a,0x1110000000001,0x3080008023c0c0,0x0,0x0,0xab00804000400,0x8018002201,0x10000000,0x118000000000,0x88000003c0c,0x4,0x0,0x90200004000,0x232000001800000,0x130410007818000,0xc028291900000000,0x9820802e40,0x13606014148c0000,0x440000,0x2])))) (bI j 104 (bI j 103 (cB [0x5f810050601,0x11,0x800000000,0x1818008000001,0x4000000000100,0x40400400,0x1000200000000000,0x8000476c960600,0x301180000000001,0x800000000023b44b,0x200040409000000,0x2c00400000000011,0x600,0x200000000002000,0x1000000400880101,0x11000b000000,0x80400023854,0x100400,0x0,0x40,0x0,0x1000000,0x1000000000,0x0,0x11823000048c0000,0x4000000000000]) (cB [0x2,0x100000000000000,0x0,0x90000000,0x0,0x0,0x0,0x0,0x8120000000000,0x208000,0x800,0x0,0x0,0x0,0x0,0x80808000000000,0x80008060002e044,0x1022000000800180,0xc0040004030301,0x80100000044,0x2006002000201,0x40000044088000,0x300100,0x0,0x0,0x0,0x1000088010000004,0x600200020])) (bI j 105 (cB [0x8000000,0x1100000000000,0x20000400,0x250100088000000,0x400040200031c,0x10000004c00,0x2000000000000000,0x800000,0x10000000000,0x8060,0x0,0x1,0x0,0x200000000000000,0x80000,0x1010001000000,0x4,0x100080,0x20000000,0x100000048,0x1030002000001000,0x1008000476c9616,0xc000000000300100,0x0,0x2000000000000,0x0,0x1000082118000006,0x20]) (bI j 106 (cB [0x8000000,0x0,0x80000000000000,0x200008080000000,0x100,0x0,0x0,0x0,0x0,0x4000000000000,0x4020000008000000,0x400000240000018,0x0,0x10010,0x0,0x80810000000000,0x800080400021844,0x6000000000180,0x200002000000000,0x1000000000,0x5020010000000000,0x900800075088010,0x4000281000200100,0x80000000002284,0x4000010,0x0,0x204]) (cB [0x400018000100,0xf81800000100000,0x80400023a6631,0x2380000040008000,0x40200011c,0xc6010060006000,0x220000,0x80000000000000,0x10,0x0,0xdb29818804000000,0xc00400040200013,0x400040000,0x0,0x2,0x1000000000000,0x0,0x80000000,0x0,0x800100404000,0x2000002000001,0x0,0x10100100000000,0x40000000]))))) (bI j 112 (bI j 109 (bI j 108 (cB [0x800003088222202,0x80200300000010,0x40000000000400,0x200808090000000,0xc000000000000000,0x0,0x0,0x0,0x800000000000000,0x8000000000040,0x28000808001000,0x40000000000000,0x0,0x10000,0x0,0x10000000000,0x80000831804,0xc00000000802000,0x100004080000,0x0,0x2020000000000000,0x40000000,0x1000100000020000,0x0,0x8000001,0x800004000000,0x84010440000,0x200000120]) (cB [0x0,0x3081800000000000,0x480401031804b0,0x340004000008000,0x1000240200010c,0x80000000000010,0x0,0x4000000000,0x8100000000000,0x4800004308060,0xf733987ea4000000,0x200019,0xcf39e3a3b5a00,0x2300000000000010,0x1000000478080404,0x382918000000000,0x880000037c04,0x0,0x40000040020001,0x20800000000000,0xeab0000000000000,0x100800047a3ae71,0x5727352800000000,0x400037fe,0x1ff038b9a940000,0x3000,0x2000000b,0x800000000000])) (bI j 110 (cB [0x0,0x312000000000000,0x200083c0003,0x21,0x0,0x124f080020204000,0x40020002,0x400001010,0x1031280000000000,0x80200003c000,0xe000889890800000,0x300001,0x400000900,0x0,0x0,0x181000000000000,0x2,0x10000040c0000000,0x0,0xc000,0x6610000000000000,0x100c000e3848061,0x10000000000,0x100000000000,0x3001001058800000,0x442000,0x0,0x2]) (bI j 111 (cB [0x40002040605,0x312000020000001,0x800002000002,0x1000,0x0,0x80000080c00000,0x40000002000,0x4040,0x3175080000000000,0x18400071c441,0xc000000080020002,0x1000c00000000138,0x4000000000001,0x20000020000000,0x8000400000606,0x1313001004000000,0x18400061c00,0x8080200000,0x0,0x4000,0x2000000000000000,0x300000c3000202,0x400000000,0x0,0x808000000,0x0,0x1000000000020400]) (cB [0x0,0x0,0x0,0x289898940000000,0x10000020005ae,0x2097004040448010,0x20000400000,0x2000800000,0x2800000001000000,0x4000000000000,0x101800000000,0x40000000000010,0x800000c0c0000,0x80000008000200,0x0,0x202118000000000,0x80000837c04,0x1e02010108802000,0x100004010000,0x0,0x6000000000000000,0x64002040,0x1020300000020000,0x200,0x8000001,0x800004000000,0x10000ed11c4e0042,0x40000120])))) (bI j 114 (bI j 113 (cB [0x2000000040000,0x9393800000000000,0x80400027c0512,0x72797968c0000000,0x24020081df,0x18b01a881b42000,0x8000800120100,0x4c500000000,0x420010001,0x200000,0x0,0x10,0x52eb0180a0a4600,0xa300000000012000,0x10080004783fe5e5,0xf168648000000000,0x440033fe2,0x9ff178b432400000,0x6022001,0x8a01ff87e1a58a0,0x800000800010301,0x180200c03080285,0x30fe966800000400,0xc0440033de,0x1ff078363040000,0x42000,0x110190ff83c1b182,0x800002]) (cB [0xc83002401204,0xc40804014400800,0x40040440c4020,0x200,0x0,0x0,0x0,0x40000040000,0x4100000040004,0x2000400,0xc201006205000002,0x20320,0x210080b10200,0x30800080000009,0x4000,0x8,0x40000000,0x1ff2793534400000,0x40002420901,0x488830100829200,0x180000c002040100,0x80011425880010,0x4000000000002020,0x800048402222c4,0x10e0201012440010,0x8080000200080])) (bI j 115 (cB [0x1000000000000,0x249800200000100,0x40012022c0402,0x2211152440020000,0x240000106,0x80000000000200,0x0,0x2000000000,0x2000200000000000,0x4000,0x0,0x0,0x101000000400,0x200000000000000,0x80000,0x4000,0x2000000000000004,0x20000000,0x0,0x1000,0x2c50000000000000,0x1084500ffc3e8d,0x80800000000040,0x40000000,0x2c009a048100000,0x501000000114,0x82017004d8240a,0x8000010]) (bI j 116 (cB [0x0,0x802000000000000,0x240000000c0000,0x8000080000822,0x501000000014000,0x6104d0a50a800,0x2100,0x200040000,0x0,0x2,0x10000000,0x1000000000000,0x0,0x3f00000000000000,0x90800007ec9645c,0xc008800000000,0x40000001c40,0x0,0x0,0x20000000000000,0x8011000080002000,0x80000005800401,0x1200d42800000000,0x2000240002025c4,0x10e0000040000000,0x4000010001200800,0x810000000000,0x80080]) (cB [0x1000000000000,0x440000,0x200000102,0x20184660c8000900,0x1080024300009e,0x184b000002000800,0x800010040,0xc2000000000,0x100000000000,0x1000000006100000,0x6021014208000000,0x1100020000021,0xb00000200000,0x200000088001000,0x820080010,0x10000000000,0x900000200200000,0x900000,0x80800000000000,0xf7843fb58a0,0x8c10000000000021,0x190880007fc1e0d,0x200c40804000000,0xc8640643c4,0x40200,0x1000,0x118a01f004d0240a,0x30]))))))) (bI j 136 (bI j 126 (bI j 121 (bI j 119 (bI j 118 (cB [0xa000020000,0x800000000000,0x100020,0x2000862040000000,0x60220001e,0xcff85a5a18a000,0x1000000000030108,0x90a00c87fc0dad8c,0xc0c4080000040001,0xc05206418400,0xff379b5164000000,0x2432800b,0xff83c1a8b200,0x1804000000001218,0x100a00078000014,0x28,0x0,0x2e00880481000000,0x4010002401040,0x40000000000,0x0,0x0,0xa0c800000000,0x10000048000003c0,0x0,0x0,0x2000000000000,0x200]) (cB [0x2380c061419,0x800000000009,0x0,0x40000000,0x40000000a0,0x4fd9acca87e000,0xb000000000010110,0x80880027ace9b563,0x1080480000000000,0x40000003c020,0xe0300c442c000000,0x42000000b,0x0,0x10004000020001,0x810000000000,0xb3aa9e8000000000,0x40440003c9b,0xbff1d8b4b3400000,0x12022101,0x1001471080ca03a0,0x80008000901,0x80020080000,0x4100080000,0x24002400000d140,0x800000000000204,0x800000000000000,0x108cd700c0c241a,0x90])) (bI j 120 (cB [0x80020000000000,0x884800000000000,0x40000817c0201,0x100844200200000,0x1000020100001e,0xce11c0e2002080,0x2000000000090110,0xa04000,0x20000000000,0x4000000000,0x8000001000000,0x18,0xcfd8bc7a39600,0xcb00000000001211,0x80c00007ec9e0d1,0x18200000000,0x4,0x1e23000462810000,0x100202030000,0x0,0x1040000000000000,0x8004020f802201,0x4000001000000440,0x100,0x1e22000462c0000,0x203000,0x180000f110402314,0x400000000010]) (cB [0x8000002,0x1000000000000,0x400,0x8000080000000,0x2014008,0x10000004000,0x3000000000000000,0x6000001000,0x100000000000,0xe00000000000,0x8000000,0x60000000,0xc000000000400,0x1b00000000000000,0x8088008580c4250,0x40004000,0x24000400000c2400,0x2020,0x8000000002001000,0x1000000000000000,0x120000800000001,0x880061000000,0x1200000000,0x4000,0x1962300c462d0000,0x800203201,0x228cb110022304,0x4000018]))) (bI j 123 (bI j 122 (cB [0x40000000020000,0x1000002000000,0x4003000000,0x200000080000100,0x800000200180,0xc0000020004800,0x2000000000000000,0x8000000000001000,0x188c780000000001,0x48440033c430,0xef187f4b34000000,0x220019,0xfd92c8c87e00,0x3700000000000000,0x7ccc669b,0xcccc998000000000,0x3c67,0x1fcc66260c400000,0x0,0x205f198cf366e0,0x10000000002000,0x1000400087802130,0x5018000800000000,0x514c0,0x3fb299198fc0000,0x200000,0x4f004484c0a,0x48000010]) (cB [0x200,0x100000024000001,0x0,0x1098040001200,0x90000020000000c,0x400000,0x1000000,0x20,0x1010000000000000,0x0,0x800000120,0x0,0x10fd908cec7e00,0x100000000001008,0x1000100000,0x0,0x0,0x0,0x0,0x0,0x2000000000000000,0x800020,0x0,0x0,0x60e1004849040000,0x20000000400])) (bI j 124 (cB [0x100000000000,0x8081800000000000,0x8403c3400,0x1000000000000040,0x0,0x10f000042402000,0x5000000000000080,0x9000008784006360,0x400000,0x800010,0x0,0x0,0x10000004240000,0x1200,0x401000000012,0x0,0x0,0x100c080000000,0x8000000000000,0x404000,0x3000000000000001,0x4000010,0x900000000000,0x0,0x3e0089898140000,0x900000040000,0x1f0004c4c00,0x48000002]) (bI j 125 (cB [0x200,0x1302800000000000,0x8000083c0013,0x8000001200,0x0,0x400000,0x0,0x10000030320,0x1010080000400000,0x58000,0x0,0x0,0x0,0x0,0x0,0x1000000000000,0x0,0x1fb2099b8fc00000,0xc20002,0x404022,0xa811000000000000,0x302008838802a2,0x80004000,0x0,0x9e26004040c0000,0x20000000000,0x101000000000]) (cB [0x80020200,0x1500800000000000,0x18400043c0011,0x20098b8140000000,0x1000002c000021e,0x10000040400000,0x48000000000,0x2020,0x1810000000000000,0x0,0x202800000000,0x100000,0x600800000040000,0x0,0x202,0x33331f8000000000,0x400087f65,0x40480000002,0x200000000,0x300000404000,0x2010000080000000,0x3004089b802222,0x80000000,0x0,0x9e2000c0c0c0000,0x42]))))) (bI j 131 (bI j 128 (bI j 127 (cB [0x2010300,0x8180800024000000,0xa40513,0x8000000001000,0x0,0x2190004e4e02000,0x5000000000000100,0x9000000480226260,0x818000002400000,0x18000010,0x80800000000,0x0,0x205f19ccccc7e00,0x2100000000000000,0x1000878201010,0x0,0x0,0x1e06020204400000,0x8002,0x5f0144c4c0e2,0x2000000480000000,0x2101,0x1000100000004000,0x20000c0000000000,0x5b3399c04dc0001,0x800002000008,0x80000d008480202,0x100]) (cB [0x211680e250101,0xb39e800020000000,0x40000007c9b32,0x3259594fc0000000,0x20000080df,0x10f91ac8ea7e000,0x5000000000110080,0xf80230020,0x2369f88000400000,0x408400043e26b,0xf029300814400000,0x10000000010081,0x526f99acaca7e00,0x3d00000000010000,0x79376565,0xf130648000000000,0x10000402bfe2,0x1ff078113a400000,0xa010002,0x201ff87e0859a0,0x800800000800100,0x410000a83880384,0x1180106104000400,0x80200000000985c0,0x1ff8785072c0000,0x800200046,0x0,0x40040])) (bI j 129 (cB [0x11905a6001010a,0x8000000002020020,0x800342010,0x400020000100,0x0,0x20000000,0x0,0x880001020,0x808040000022010,0x100800000005c000,0xb703801324000001,0xa0100001,0x20000440001810,0x800000000000000,0x2002,0x400040000000000,0x0,0x200080182000000,0x8010000,0x10,0x400,0x0,0x100104000000000,0x800000000000,0x4000008000280000,0x0,0x800019004000c10,0x400240]) (bI j 130 (cB [0x4800000000,0x800000120,0x0,0x1008414a80000001,0x80048010042be,0x60f000000000000,0x1000000240000,0x8000000000,0x0,0x0,0x0,0x80400000088,0x10aaff8bc4c99200,0xb00000000004000,0x2000084476c56265,0x10000001000,0x100000000000,0x1000100800000,0x40000000000,0x10882108000a140,0x1060004000000400,0x8006080200,0x100101000280180,0x10000400304,0x0,0x0,0x10000000000004,0x500000000]) (cB [0x0,0x8205000000000020,0x423180200,0x10000,0x800000000,0x2aff008060a14000,0x1,0x100000000000,0x3326480000000002,0x2827fe13,0xff01d9d3a4000000,0x2000800020040021,0x30708020205000,0x200100044000002,0x108078600101,0x200,0x2020,0x1ff01b9b36400000,0x1000100000408022,0x40080e1000000004,0x2080000000000,0x80000,0x4040c000000000,0x2000000100641c4,0x11db299990248200,0x4000000010,0x14000004])))) (bI j 133 (bI j 132 (cB [0x40000a000002,0x1000000100000,0x202184500,0xb358194040000000,0x80002011d,0xca118020a06000,0x2000402200010000,0x8000044508c00040,0x20000020110000,0x20,0x250001000000000,0x800400020000100,0x18a11840480400,0x240000020001200,0x9000000100c0000,0x2000000000,0x0,0x0,0x8000000,0x100000000,0x20000000000000,0xc000,0x2000200000001000,0x10000000001,0x100010000000,0x14,0x2000000000000]) (cB [0x8000002,0x1200000000000,0x10000000000400,0x200000080000000,0x840000000,0x0,0x0,0x0,0x828080000000000,0x8000080000268460,0x210001000001008,0x4400004002000,0x800000000,0x200000200000000,0x1000004500c0004,0x2011000,0x2,0x1d13181100800000,0x40002400203,0x200000c,0x24000000000000,0xc000,0x280000000000,0x0,0x8000000,0x0,0x8000804])) (bI j 134 (cB [0x6000400,0x1,0x800000000000,0x10000000,0x8000000000000000,0x804000,0x400400000000000,0x0,0x100000100002,0x1400000000040,0xdb3585940c000008,0x800400080002011,0x4000800000400,0x0,0x2000000000140000,0x818000000000,0x8000000004000844,0x182208c042800100,0x80000000000000,0x0,0x4000000000000,0x200000000000000,0x1000000000,0x0,0x80000,0x8040004800000,0xc6008000004,0x402000240]) (bI j 135 (cB [0x804308c010502,0x8281800201100009,0x3784602,0x100410000000088,0x44001000020000,0x20000000,0x2200080000,0x40001400040,0x30000000000000,0x8000000008060440,0x808000008,0x0,0x1000c990c4081200,0xb00050000004000,0x2000080064c86206,0x81002000000000,0x40,0x20000000000000,0x0,0xc1044200040,0x6024000000000002,0x6088220,0x10201200200100,0x800000000000000,0x808090010,0x20,0x40004,0x40]) (cB [0x900000000060b,0xb201800005000120,0x900004831800b0,0xf178d872c0000080,0x48000241fe,0x4fd83c3c386000,0x3000000000000000,0x80800027ec9e1e1c,0x706100000002000,0x100040400203f64f,0xe020000008000000,0x20000301,0x1000000400,0x200000000000000,0x0,0x0,0x0,0x0,0x0,0x19001000001040,0xa0000000040000,0x80000000004000,0x1000100020,0x0,0x2802200406080000,0xc4880200000,0x80b000020200,0x4240010])))))) (bI j 146 (bI j 141 (bI j 138 (bI j 137 (cB [0x5800000000,0x2120000,0x0,0x2200008080000000,0xc0c4800200000000,0x110040404000,0x3000606000000000,0x8080048789840409,0x80c0a0000002000,0x90004000000e4400,0x18,0x0,0x12000012000,0x8200000000000000,0x400c800800000,0x80c10000000000,0x8900040009812440,0x401000002800001,0x8000000000080,0x209001200001248,0x40000,0x2410000000,0x0,0x0,0x2000000080000,0x800000000000,0x100000000]) (cB [0x27e89e0e0c3,0x200000000000,0x0,0x800000880000000,0x92,0x49000000000800,0x0,0x0,0x10000000000000,0x0,0x800000000,0x0,0x4f11000010400,0x8140000624000000,0x8000003c8800101,0x80808000031200,0x8000000000012400,0x4040000001,0x0,0x9490108282260,0x1000080000000101,0x401000010,0x8089000000000,0x10000000000000,0x8022004060d0000,0xc4800200000,0x20200,0x4000])) (bI j 139 (cB [0x20000000000,0x8080800000000000,0x4000001ac0000,0x404000200109,0x84800000000096,0x20000000,0x2000000000000000,0x8000002008801030,0x18100030312000,0x9000400000000440,0x2200c0c09001818,0xc0c000000000000,0x10fd13c1c1c600,0xc300000000003008,0x18000001c8882828,0x10008002000,0x10000c0000042404,0x1200000000030400,0x8200080006000000,0x20000010021,0xc20410000000000,0x180000084888202,0x4100061060800200,0x10000c000008244,0xe1faa783838c3040,0x20008000600400,0x9140000144,0xc1000400030]) (bI j 140 (cB [0x100000202200,0x1071400000200000,0xc000000245410,0x22000020c3040010,0xc0000600000012,0x2fd0bc5e196002,0x40000100010000,0x18588040388,0x100000400044000,0x200000000002c000,0x601008c028020002,0x100202000000045,0x21f00440400800,0x98000000,0x11f8002200,0x1118650000000800,0xc000000ac46,0x2000000810400,0x80000000000,0x20000404000,0x2000000000000000,0x20,0x4010001000000200,0x100000000000000,0x23e228808a980000,0x9000603000,0x70f110000105,0x1000400000]) (cB [0x300000000200,0x101000000040000,0x4000401,0x0,0x0,0x10f110044584000,0x2001000400000020,0x80010000800020,0x7071c000000c000,0xc0000043f44f,0x222084868d000000,0x2000800060100027,0x200000020000,0x200000000000000,0x80000,0xb030592000001200,0xc0600042404,0x1200080020900000,0x6c10002,0x8,0xa0000009000100,0x1000000000c000,0x4000101000000280,0x4800000000,0x7e200a0220c0000,0x80000000006c1040,0x800800000000006])))) (bI j 143 (bI j 142 (cB [0x8000003,0x1200800000008,0x0,0x10000000,0x0,0x149110424344000,0x2401000440030100,0x800000,0x0,0x0,0x408000000,0x200000022800,0x16b11042434400,0x1200000000003200,0x100000800180000,0x8000000000,0x0,0x2000000800000,0x2000000000000000,0x100000040,0x20000004000000,0x8000,0x0,0x0,0x80000400000400,0x0,0x40000]) (cB [0x8030002,0x81000000000000,0x400,0x2a08082890000009,0x800602400e1e,0x402f108c46114802,0x2400140000030001,0xc8100000000,0x100000000000,0x0,0x4010000428000000,0x20000,0xa20000000000400,0x200000000000800,0x18000a1010000200,0x10012000000000,0x804,0x3000000900000,0x0,0x104044048,0x24000000000320,0x300000000,0x4f0f0e1800000120,0x10000020800ff6,0x21e28080828c0000,0x8800601000,0x9000404104,0x30])) (bI j 144 (cB [0x101002,0x1000000000000,0x0,0x200000000000000,0x0,0x4000,0x2000000000000000,0x0,0x100000000000,0x0,0xc00000,0x0,0x400,0x9200020000000000,0xb04000800000000,0x9800000000,0x10000,0x800000,0x48000000000,0x1000400000440,0x200000000000001,0x100000000008000,0x4000001000000000,0x0,0x42000000080000,0x800000100028,0x20140000000004,0x240000]) (bI j 145 (cB [0x2000000000000,0x320000,0x5000000000000000,0x80000000,0x4800000000000000,0x0,0x3000000000000000,0x0,0x100080012000,0x9000000000000000,0xe20004060c000000,0x200048000c104107,0x1808910000002600,0x8200100005000608,0x300100048000000,0xf070618000001220,0x8003f24,0x40400d00000,0x0,0x0,0x0,0x0,0x4000001000000000,0x1000000000240,0x100000290000,0x4000000000000,0x4]) (cB [0x202,0x101000303120000,0x5000000000000000,0x2105064c0018180,0x2c1000272,0x104000,0x2000000004000000,0x780000008,0x4920000312000,0x0,0x22004060c000000,0xc480020004106,0x5b10002030200,0x8000100424000200,0x100000058800101,0x21200,0x0,0x6020000080800000,0xc0c48000410000,0x8000001000404040,0x2024006062400020,0x88020,0x4f07069800303000,0x400043f2,0x1202141420c0000,0x100010000200001,0x109010000004,0x800010]))))) (bI j 151 (bI j 148 (bI j 147 (cB [0x84800000000,0x400008,0x0,0x0,0x0,0x802000202002000,0x10000,0x8000010000,0x306100000000000,0x400000424043,0x20000008020002,0x200000000000,0x0,0x8200000000000000,0x800000848084000,0x40004800,0x0,0x400001000000000,0x20000000000,0x40090fcb3c1c1a60,0xa0080008000000,0x80085804026,0x2021000040404c4,0x220000000000000,0x1206101024a0000,0x100010000200001,0x8000,0x100000]) (cB [0x80107e45e2e8cb,0x80001,0x0,0x100920280000004,0x1003000000201416,0xa1f004000008000,0x80000008,0x9000010680022080,0x1244500000048000,0x40000002c062,0x4000010000020000,0x20,0x200000800000,0x400000000000000,0x4000020000,0x0,0x0,0x400008080000000,0x0,0x404000,0x0,0x800020,0x530316b000000400,0x2200058400047c2,0x2000000000020000,0x0,0xa00020202020])) (bI j 149 (cB [0x8000000200,0x7069c000000c0000,0x40000043f24f0,0x40420d0000000,0x80,0x200000800,0x2400000000000000,0x8041048480841419,0x920000002000,0x400000,0x10000428000000,0x200000000004,0x16b01082822400,0x1000,0x800000800000000,0x8008000000000,0x0,0x0,0x400000,0x8000000000000,0x0,0x0,0x0,0x800000000,0x80000400000000,0x0,0x40000]) (bI j 150 (cB [0x30000,0x89000000000000,0x0,0x4090000009,0x2000000000,0x90f030808124000,0xa4080000000000c0,0x1008000780462488,0x100000000000,0x5000000408000,0x4000000408000000,0x2804,0x2a0000400000c00,0x240000000000000,0x10002208,0x20452000000000,0x802,0x100000,0x20000000,0x40,0x2924000000000000,0xb0000003800202,0x101200000000,0x800000000,0x280000000000]) (cB [0x0,0x100000000000001,0x500,0x100000000000000,0x0,0x84fd93c3c386000,0x3000000000000080,0x800000648a81111a,0x120400002000,0x9000000002000000,0x2020000009000000,0xc000030000009,0x207cfd93c3c38600,0x100644003000,0x103,0x80c10000000600,0x89000c0000072444,0x4000004800401,0x8000000400,0x391301213260,0x24010000440000,0x40000000000000,0x40080c1200000020,0x1891004000004244,0x1002200000080200,0xc4800000030,0x10022fd9bc5c396,0x2100000])))) (bI j 153 (bI j 152 (cB [0x200085808406882,0x1003004000444000,0x20087c0510,0x2300c86280000022,0x4040000200000056,0x85f11442470c800,0x2c000000c0010080,0x1042788801038,0x10000000002000,0x8000000000000010,0x8000000,0x0,0x200000402060c00,0xc340000000000000,0x80000007ec9e1e1,0x80c12000030200,0x99000e0200073c44,0x7e26020224c00001,0x200000000c10410,0x1400000000048,0x1820000004000080,0x104a7888010,0x4000001800003120,0x1890000000622004,0x5e2300886280100,0x8004040000000228,0x4062110020b04,0x4240012]) (cB [0x2020000000102,0x890000001200a0,0x820000800,0x20040c080000000,0xc0c4800240000000,0x406f983c2cb86800,0x2000000040000000,0x804000878a02015a,0x8000200b,0x0,0x0,0x0,0x0,0x0,0xa000000000000001,0x800000003200,0x1900500000000000,0x22000048000000,0x0,0x0,0x1020000000000000,0x0,0x91000000000,0x40000001,0x80000000080000,0x100014,0x800000100400204,0x404000140])) (bI j 154 (cB [0x80200102,0x2020000a0,0x0,0x20010000,0x0,0x0,0x800000000000000,0x0,0x8100000000000,0x9005000010000400,0x40000000000000,0x200000000,0x10f120801b2400,0x800004000210,0x4000000001,0x810000000000,0x200600000,0x800800001800000,0x40,0x40000200002248,0x5820000002400000,0xa00002537880010,0x282c1000002120,0x900000000817c4,0x1e2001416080000,0xc800000000,0x4]) (bI j 155 (cB [0x2,0x82c1000000320004,0x203c4002,0x80000009,0x0,0x800120000124000,0x0,0x3f88001018,0x80c000000012000,0x90000000000e4400,0xa2008c020c000000,0x808080000002805,0xd11040030400,0x240040400000000,0xa0000080101,0x70f1e38002000000,0x48000817f61,0x2008080800000,0x480000000003c0,0x1e0000100404040,0x2020002400000000,0xf000008020,0x120000,0x0,0x8,0x4000000000000,0x1e000010040404,0x240000000]) (cB [0xc00007ec8e2e3c7,0x91c1a00000000000,0x40000003c4411,0x2000002010000000,0x0,0x0,0x1000000000000000,0x0,0x80000000000,0x0,0xe2288c8e18000000,0x1800000300001,0xf11044470e00,0x240000600000018,0x900000000080202]))))))))) 111 (i / 1 % 16)

def zm := zc zca zcn zhq (fun i => zt zcn (cutPick zcX (zkI i))) 2489 zhE zdV zjr znT zuw
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zqw : zd zca zcn zhq (zt zcn zcX) zuy (zz 2489 zhE zdV zjr 0) zcK 12 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zup : tB 0 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ztZ : tB 24 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zuX : tB 48 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem znl : tB 72 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zqm : tB 96 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zsP : tB 120 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zvn : tB 144 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zti : tB 168 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zqE : tB 192 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem znQ : tB 216 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zwN : tB 240 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zrP : tB 264 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zrq : tB 288 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zsy : tB 312 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zsh : tB 336 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zts : tB 360 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zoh : tB 384 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zmG : tB 408 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ztB : tB 432 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zqO : tB 456 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zto : tB 480 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zmK : tB 504 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zqn : tB 528 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zpj : tB 552 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zoG : tB 576 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zwY : tB 600 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zuz : tB 624 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem znq : tB 648 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zrA : tB 672 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zxb : tB 696 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zqY : tB 720 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zso : tB 744 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zwa : tB 768 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zty : tB 792 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zun : tB 816 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zxp : tB 840 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem znO : tB 864 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zvf : tB 888 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zqo : tB 912 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zqJ : tB 936 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zss : tB 960 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zpb : tB 984 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem znU : tB 1008 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zsX : tB 1032 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zmC : tB 1056 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zps : tB 1080 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zpz : tB 1104 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zmA : tB 1128 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zsH : tB 1152 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zqR : tB 1176 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem znF : tB 1200 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zrI : tB 1224 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem znp : tB 1248 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ztX : tB 1272 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zst : tB 1296 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zwp : tB 1320 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zvu : tB 1344 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zuR : tB 1368 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zvi : tB 1392 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zqx : tB 1416 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zok : tB 1440 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zqZ : tB 1464 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ztA : tB 1488 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zmP : tB 1512 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zoj : tB 1536 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zmD : tB 1560 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zne : tB 1584 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zoX : tB 1608 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zsI : tB 1632 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ztp : tB 1656 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zrQ : tB 1680 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zrN : tB 1704 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zwt : tB 1728 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zsj : tB 1752 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ztK : tB 1776 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zvl : tB 1800 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zxh : tB 1824 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zpB : tB 1848 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zmM : tB 1872 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zxI : tB 1896 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zpk : tB 1920 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zoQ : tB 1944 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zoT : tB 1968 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zvR : tB 1992 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zqe : tB 2016 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zoH : tB 2040 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zsu : tB 2064 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zvh : tB 2088 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zmO : tB 2112 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zuW : tB 2136 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zwh : tB 2160 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ztM : tB 2184 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zrV : tB 2208 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ztu : tB 2232 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ztS : tB 2256 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ztT : tB 2280 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem znj : tB 2304 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem znf : tB 2328 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem znJ : tB 2352 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zsk : tB 2376 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ztz : tB 2400 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem znY : tB 2424 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zmS : tB 2448 24 zm = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zov : tB 2472 17 zm = true := by decide +kernel
theorem zrt : tB 24 48 zm = true := tM (start := 24) (left := 24) (right := 24) (check := zm) ztZ zuX
theorem zxF : tB 0 72 zm = true := tM (start := 0) (left := 24) (right := 48) (check := zm) zup zrt
theorem zuD : tB 96 48 zm = true := tM (start := 96) (left := 24) (right := 24) (check := zm) zqm zsP
theorem zrs : tB 72 72 zm = true := tM (start := 72) (left := 24) (right := 48) (check := zm) znl zuD
theorem zxq : tB 0 144 zm = true := tM (start := 0) (left := 72) (right := 72) (check := zm) zxF zrs
theorem zxw : tB 168 48 zm = true := tM (start := 168) (left := 24) (right := 24) (check := zm) zti zqE
theorem zrw : tB 144 72 zm = true := tM (start := 144) (left := 24) (right := 48) (check := zm) zvn zxw
theorem zsO : tB 216 48 zm = true := tM (start := 216) (left := 24) (right := 24) (check := zm) znQ zwN
theorem zoi : tB 264 48 zm = true := tM (start := 264) (left := 24) (right := 24) (check := zm) zrP zrq
theorem zvb : tB 216 96 zm = true := tM (start := 216) (left := 48) (right := 48) (check := zm) zsO zoi
theorem zqL : tB 144 168 zm = true := tM (start := 144) (left := 72) (right := 96) (check := zm) zrw zvb
theorem zwJ : tB 0 312 zm = true := tM (start := 0) (left := 144) (right := 168) (check := zm) zxq zqL
theorem zsn : tB 336 48 zm = true := tM (start := 336) (left := 24) (right := 24) (check := zm) zsh zts
theorem zrv : tB 312 72 zm = true := tM (start := 312) (left := 24) (right := 48) (check := zm) zsy zsn
theorem zsl : tB 408 48 zm = true := tM (start := 408) (left := 24) (right := 24) (check := zm) zmG ztB
theorem znn : tB 384 72 zm = true := tM (start := 384) (left := 24) (right := 48) (check := zm) zoh zsl
theorem zvK : tB 312 144 zm = true := tM (start := 312) (left := 72) (right := 72) (check := zm) zrv znn
theorem zoB : tB 480 48 zm = true := tM (start := 480) (left := 24) (right := 24) (check := zm) zto zmK
theorem zuF : tB 456 72 zm = true := tM (start := 456) (left := 24) (right := 48) (check := zm) zqO zoB
theorem zwd : tB 528 48 zm = true := tM (start := 528) (left := 24) (right := 24) (check := zm) zqn zpj
theorem zsL : tB 576 48 zm = true := tM (start := 576) (left := 24) (right := 24) (check := zm) zoG zwY
theorem ztJ : tB 528 96 zm = true := tM (start := 528) (left := 48) (right := 48) (check := zm) zwd zsL
theorem znH : tB 456 168 zm = true := tM (start := 456) (left := 72) (right := 96) (check := zm) zuF ztJ
theorem zqz : tB 312 312 zm = true := tM (start := 312) (left := 144) (right := 168) (check := zm) zvK znH
theorem zmz : tB 0 624 zm = true := tM (start := 0) (left := 312) (right := 312) (check := zm) zwJ zqz
theorem zpn : tB 648 48 zm = true := tM (start := 648) (left := 24) (right := 24) (check := zm) znq zrA
theorem ztO : tB 624 72 zm = true := tM (start := 624) (left := 24) (right := 48) (check := zm) zuz zpn
theorem zqK : tB 720 48 zm = true := tM (start := 720) (left := 24) (right := 24) (check := zm) zqY zso
theorem zoe : tB 696 72 zm = true := tM (start := 696) (left := 24) (right := 48) (check := zm) zxb zqK
theorem zqd : tB 624 144 zm = true := tM (start := 624) (left := 72) (right := 72) (check := zm) ztO zoe
theorem ztQ : tB 792 48 zm = true := tM (start := 792) (left := 24) (right := 24) (check := zm) zty zun
theorem zrl : tB 768 72 zm = true := tM (start := 768) (left := 24) (right := 48) (check := zm) zwa ztQ
theorem znm : tB 840 48 zm = true := tM (start := 840) (left := 24) (right := 24) (check := zm) zxp znO
theorem zre : tB 888 48 zm = true := tM (start := 888) (left := 24) (right := 24) (check := zm) zvf zqo
theorem zqX : tB 840 96 zm = true := tM (start := 840) (left := 48) (right := 48) (check := zm) znm zre
theorem zsx : tB 768 168 zm = true := tM (start := 768) (left := 72) (right := 96) (check := zm) zrl zqX
theorem ztY : tB 624 312 zm = true := tM (start := 624) (left := 144) (right := 168) (check := zm) zqd zsx
theorem zvk : tB 960 48 zm = true := tM (start := 960) (left := 24) (right := 24) (check := zm) zss zpb
theorem zoP : tB 936 72 zm = true := tM (start := 936) (left := 24) (right := 48) (check := zm) zqJ zvk
theorem zon : tB 1032 48 zm = true := tM (start := 1032) (left := 24) (right := 24) (check := zm) zsX zmC
theorem zvH : tB 1008 72 zm = true := tM (start := 1008) (left := 24) (right := 48) (check := zm) znU zon
theorem zsM : tB 936 144 zm = true := tM (start := 936) (left := 72) (right := 72) (check := zm) zoP zvH
theorem zvj : tB 1104 48 zm = true := tM (start := 1104) (left := 24) (right := 24) (check := zm) zpz zmA
theorem zwu : tB 1080 72 zm = true := tM (start := 1080) (left := 24) (right := 48) (check := zm) zps zvj
theorem zqq : tB 1152 48 zm = true := tM (start := 1152) (left := 24) (right := 24) (check := zm) zsH zqR
theorem zxm : tB 1200 48 zm = true := tM (start := 1200) (left := 24) (right := 24) (check := zm) znF zrI
theorem zvY : tB 1152 96 zm = true := tM (start := 1152) (left := 48) (right := 48) (check := zm) zqq zxm
theorem zwK : tB 1080 168 zm = true := tM (start := 1080) (left := 72) (right := 96) (check := zm) zwu zvY
theorem zpU : tB 936 312 zm = true := tM (start := 936) (left := 144) (right := 168) (check := zm) zsM zwK
theorem zvz : tB 624 624 zm = true := tM (start := 624) (left := 312) (right := 312) (check := zm) ztY zpU
theorem zpJ : tB 0 1248 zm = true := tM (start := 0) (left := 624) (right := 624) (check := zm) zmz zvz
theorem ztj : tB 1272 48 zm = true := tM (start := 1272) (left := 24) (right := 24) (check := zm) ztX zst
theorem zoM : tB 1248 72 zm = true := tM (start := 1248) (left := 24) (right := 48) (check := zm) znp ztj
theorem zoC : tB 1344 48 zm = true := tM (start := 1344) (left := 24) (right := 24) (check := zm) zvu zuR
theorem zmx : tB 1320 72 zm = true := tM (start := 1320) (left := 24) (right := 48) (check := zm) zwp zoC
theorem zoF : tB 1248 144 zm = true := tM (start := 1248) (left := 72) (right := 72) (check := zm) zoM zmx
theorem zww : tB 1416 48 zm = true := tM (start := 1416) (left := 24) (right := 24) (check := zm) zqx zok
theorem zuv : tB 1392 72 zm = true := tM (start := 1392) (left := 24) (right := 48) (check := zm) zvi zww
theorem zou : tB 1464 48 zm = true := tM (start := 1464) (left := 24) (right := 24) (check := zm) zqZ ztA
theorem zqN : tB 1512 48 zm = true := tM (start := 1512) (left := 24) (right := 24) (check := zm) zmP zoj
theorem zxn : tB 1464 96 zm = true := tM (start := 1464) (left := 48) (right := 48) (check := zm) zou zqN
theorem zoa : tB 1392 168 zm = true := tM (start := 1392) (left := 72) (right := 96) (check := zm) zuv zxn
theorem zuC : tB 1248 312 zm = true := tM (start := 1248) (left := 144) (right := 168) (check := zm) zoF zoa
theorem zqa : tB 1584 48 zm = true := tM (start := 1584) (left := 24) (right := 24) (check := zm) zne zoX
theorem zwn : tB 1560 72 zm = true := tM (start := 1560) (left := 24) (right := 48) (check := zm) zmD zqa
theorem znz : tB 1656 48 zm = true := tM (start := 1656) (left := 24) (right := 24) (check := zm) ztp zrQ
theorem zqt : tB 1632 72 zm = true := tM (start := 1632) (left := 24) (right := 48) (check := zm) zsI znz
theorem zmB : tB 1560 144 zm = true := tM (start := 1560) (left := 72) (right := 72) (check := zm) zwn zqt
theorem zvL : tB 1728 48 zm = true := tM (start := 1728) (left := 24) (right := 24) (check := zm) zwt zsj
theorem ztt : tB 1704 72 zm = true := tM (start := 1704) (left := 24) (right := 48) (check := zm) zrN zvL
theorem zpc : tB 1776 48 zm = true := tM (start := 1776) (left := 24) (right := 24) (check := zm) ztK zvl
theorem ztP : tB 1824 48 zm = true := tM (start := 1824) (left := 24) (right := 24) (check := zm) zxh zpB
theorem ztc : tB 1776 96 zm = true := tM (start := 1776) (left := 48) (right := 48) (check := zm) zpc ztP
theorem zsz : tB 1704 168 zm = true := tM (start := 1704) (left := 72) (right := 96) (check := zm) ztt ztc
theorem zvP : tB 1560 312 zm = true := tM (start := 1560) (left := 144) (right := 168) (check := zm) zmB zsz
theorem zpo : tB 1248 624 zm = true := tM (start := 1248) (left := 312) (right := 312) (check := zm) zuC zvP
theorem zmr : tB 1896 48 zm = true := tM (start := 1896) (left := 24) (right := 24) (check := zm) zxI zpk
theorem ztN : tB 1872 72 zm = true := tM (start := 1872) (left := 24) (right := 48) (check := zm) zmM zmr
theorem zmY : tB 1968 48 zm = true := tM (start := 1968) (left := 24) (right := 24) (check := zm) zoT zvR
theorem znw : tB 1944 72 zm = true := tM (start := 1944) (left := 24) (right := 48) (check := zm) zoQ zmY
theorem zmy : tB 1872 144 zm = true := tM (start := 1872) (left := 72) (right := 72) (check := zm) ztN znw
theorem zpd : tB 2040 48 zm = true := tM (start := 2040) (left := 24) (right := 24) (check := zm) zoH zsu
theorem znD : tB 2016 72 zm = true := tM (start := 2016) (left := 24) (right := 48) (check := zm) zqe zpd
theorem zsg : tB 2088 48 zm = true := tM (start := 2088) (left := 24) (right := 24) (check := zm) zvh zmO
theorem zuE : tB 2136 48 zm = true := tM (start := 2136) (left := 24) (right := 24) (check := zm) zuW zwh
theorem zuf : tB 2088 96 zm = true := tM (start := 2088) (left := 48) (right := 48) (check := zm) zsg zuE
theorem zvw : tB 2016 168 zm = true := tM (start := 2016) (left := 72) (right := 96) (check := zm) znD zuf
theorem zsC : tB 1872 312 zm = true := tM (start := 1872) (left := 144) (right := 168) (check := zm) zmy zvw
theorem zmH : tB 2208 48 zm = true := tM (start := 2208) (left := 24) (right := 24) (check := zm) zrV ztu
theorem zxD : tB 2184 72 zm = true := tM (start := 2184) (left := 24) (right := 48) (check := zm) ztM zmH
theorem zxk : tB 2280 48 zm = true := tM (start := 2280) (left := 24) (right := 24) (check := zm) ztT znj
theorem zvJ : tB 2256 72 zm = true := tM (start := 2256) (left := 24) (right := 48) (check := zm) ztS zxk
theorem zpL : tB 2184 144 zm = true := tM (start := 2184) (left := 72) (right := 72) (check := zm) zxD zvJ
theorem znd : tB 2352 48 zm = true := tM (start := 2352) (left := 24) (right := 24) (check := zm) znJ zsk
theorem zqi : tB 2328 72 zm = true := tM (start := 2328) (left := 24) (right := 48) (check := zm) znf znd
theorem zvs : tB 2400 48 zm = true := tM (start := 2400) (left := 24) (right := 24) (check := zm) ztz znY
theorem zqC : tB 2448 41 zm = true := tM (start := 2448) (left := 24) (right := 17) (check := zm) zmS zov
theorem zoI : tB 2400 89 zm = true := tM (start := 2400) (left := 48) (right := 41) (check := zm) zvs zqC
theorem zrz : tB 2328 161 zm = true := tM (start := 2328) (left := 72) (right := 89) (check := zm) zqi zoI
theorem zwH : tB 2184 305 zm = true := tM (start := 2184) (left := 144) (right := 161) (check := zm) zpL zrz
theorem zul : tB 1872 617 zm = true := tM (start := 1872) (left := 312) (right := 305) (check := zm) zsC zwH
theorem zpG : tB 1248 1241 zm = true := tM (start := 1248) (left := 624) (right := 617) (check := zm) zpo zul
theorem zxl : tB 0 2489 zm = true := tM (start := 0) (left := 1248) (right := 1241) (check := zm) zpJ zpG
theorem zrK : tB 0 2489 zm = true := zxl
theorem zvZ : Known zcX := (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (eK (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) zwA) zgk) zkX) zcG) zix) zcd) zoq) zxz) zdc) znE) zlN) zeW) zoR) zwO) zsA) zvW) znX) zhg) zjc) ziC) zeH) zdQ) zbI) zbE) zgl) zfZ) zvV) zri) zkA) zcw) zqM) zji) zbJ) zgG) zvm) zvo) zkg) zjt) zwb) zuB) zjN) zcu) zdo) zcQ) zfO) ziX) zbP) zed) zsB) ziF) zoW) zel) zfs) zgy) zjm) zng) zcf) zai) zH) zbl) zac) zws) zcJ) zpD) zcD) zus) zwi) zqf) ztW) zdd) zpy) zmL) znb) zmw) zhW) zbG) zxE) zqD) zwy) zqg) ztg) zoD) zwB) zsq) zpX) zqr) zjP) zqb) znC) zpg) zsR) zwL) znR) zod) zpH) zcS) zsN) znc) zvC) znx) zsF) zpA) znV) zdb) zcL) zcH) zcI) zxx) zbV) zcR) zoV)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zwg : Lower zca zcK zcn 13 := by
  apply lowerDag zkI _ _ _ _ zuk _ _ _ zvZ _ zqw zrK
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold pW; decide +kernel
  · exact cK (by decide +kernel)
  · exact sM (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [zcX,List.mem_cons,List.not_mem_nil,or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
end PEqualNP.Outside.L_meta_47823

open PEqualNP.Outside.L_meta_47823 in
theorem PEqualNP.Outside.L_meta_47823 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676776 * 2 ^ 32 + 3968370824) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676776 * 2 ^ 32 + 3968370824) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  intro t h
  let raw : List (BitVec 64) := [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]
  let goal : BitVec 64 := 0xfee8e8a8ec888888
  have root : Lower (fM 64) (raw.map BitVec.toNat) goal.toNat 13 :=
    hcsLowerEq (by decide +kernel) (by decide +kernel) (by decide +kernel) zwg
  have size : 13 ≤ t :=
    hcsLower (n := 6) raw goal 13 _ (by decide +kernel) (by decide +kernel) root t h
  let circuit : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.and,[0,1]⟩,⟨.or,[6,2]⟩,⟨.and,[0,5]⟩,⟨.or,[8,1]⟩,⟨.and,[3,4]⟩,⟨.and,[9,10]⟩,⟨.or,[9,10]⟩,⟨.and,[7,12]⟩,⟨.or,[3,4]⟩,⟨.and,[14,5]⟩,⟨.or,[0,15]⟩,⟨.and,[13,16]⟩,⟨.or,[11,17]⟩],18⟩
  refine ⟨circuit,?_,?_,by decide +kernel⟩
  · intro gate member
    simp only [circuit,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · exact Nat.le_trans (by decide +kernel : circuit.size ≤ 13) size

