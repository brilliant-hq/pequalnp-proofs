import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_4043_5
    (projection : ∀ (C : Circuit) (p : Fin 26 → Option (Fin 25)), Monotone2 C →
      ∃ D : Circuit, Monotone2 D ∧ D.size = C.size ∧ ∀ y : Fin 25 → Bool,
        D.eval (List.ofFn y) = C.eval (List.ofFn fun i => (p i).elim false y))
    (constantCase : ∀ (v : Bool) (D : Circuit), Monotone2 D →
      (∀ x : Fin 25 → Bool, D.eval (List.ofFn x ++ [v]) = true ↔ ∃ (p : Fin 12) (l : Fin 13), (p.succ = l ∨ p.succ = l+1 ∨ p.succ = l+3 ∨ p.succ = l+9) ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 12 l) = true) → 57 ≤ D.size)
    (pairCase : ∀ (both : Bool) (a b : Fin 26) (D : Circuit),
      26 * min a.val b.val + max a.val b.val ∈ ([0, 1, 2, 12, 13, 14, 16, 25, 324, 325, 328, 337, 351, 352, 363, 675] : List ℕ) → Monotone2 D →
      (∀ x : Fin 25 → Bool, let u := List.ofFn x
        D.eval (u ++ [if both then u.getD a.val false && u.getD b.val false
          else u.getD a.val false || u.getD b.val false]) = true ↔ ∃ (p : Fin 12) (l : Fin 13), (p.succ = l ∨ p.succ = l+1 ∨ p.succ = l+3 ∨ p.succ = l+9) ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 12 l) = true) → 57 ≤ D.size) :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (26 : ℕ)), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x4 : Fin (26 : ℕ) → Bool), x4 x2 = Bool.false → (x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ x4 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x7) = Bool.true)) → (58 : ℕ) ≤ x1.size := by
  have fixed : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (25 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (12 : ℕ)) (x5 : Fin (13 : ℕ)), (x4.succ = x5 ∨ x4.succ = x5 + (1 : Fin ((12 : ℕ) + (1 : ℕ))) ∨ x4.succ = x5 + (3 : Fin ((12 : ℕ) + (1 : ℕ))) ∨ x4.succ = x5 + (9 : Fin ((12 : ℕ) + (1 : ℕ)))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (12 : ℕ) x5) = Bool.true) → (58 : ℕ) ≤ x1.size := by
    let incident (p : Fin 12) (l : Fin 13) : Prop :=
      p.succ = l ∨ p.succ = l+1 ∨ p.succ = l+3 ∨ p.succ = l+9
    let good (x : Fin 25 → Bool) : Prop := ∃ p l, incident p l ∧
      x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 12 l) = true
    let E (a b : Fin 25) : Prop := a.val < 12 ∧ 12 ≤ b.val ∧
      (a.val + 14 - (b.val - 12)) % 13 ∈ ([0,1,3,9] : List ℕ)
    have edgeSpec : ∀ a b : Fin 25, E a b ↔ ∃ p l, incident p l ∧
        a = Fin.castAdd 13 p ∧ b = Fin.natAdd 12 l := by decide +kernel
    have asEdges (x : Fin 25 → Bool) : good x ↔
        ∃ a b, E a b ∧ x a = true ∧ x b = true := by
      constructor
      · rintro ⟨p,l,e,hp,hl⟩
        exact ⟨_,_,(edgeSpec _ _).mpr ⟨p,l,e,rfl,rfl⟩,hp,hl⟩
      · rintro ⟨a,b,e,ha,hb⟩
        obtain ⟨p,l,incidence,rfl,rfl⟩ := (edgeSpec a b).mp e
        exact ⟨p,l,incidence,ha,hb⟩
    let gen (k : Fin 4) (i : Fin 25) : Fin 25 :=
      Fin.ofNat 25 ((([[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24], [2, 11, 8, 3, 4, 10, 6, 1, 0, 5, 9, 7, 12, 15, 21, 20, 16, 14, 23, 18, 13, 17, 22, 19, 24], [1, 9, 11, 3, 4, 2, 6, 10, 7, 0, 8, 5, 24, 13, 21, 15, 16, 14, 19, 23, 20, 17, 12, 18, 22], [3, 1, 4, 0, 2, 5, 8, 11, 6, 9, 10, 7, 16, 13, 14, 17, 12, 15, 18, 21, 23, 19, 22, 20, 24]] : List (List ℕ)).getD k.val []).getD i.val 0)
    have onto : ∀ k i, ∃ j, gen k j = i := by decide +kernel
    have preserves : ∀ k a b, E (gen k a) (gen k b) ↔ E a b := by decide +kernel
    have acts (k : Fin 4) (x : Fin 25 → Bool) : good (fun i => x (gen k i)) ↔ good x := by
      refine (asEdges (fun i => x (gen k i))).trans (Iff.trans ?_ (asEdges x).symm)
      constructor
      · rintro ⟨a,b,e,ha,hb⟩
        exact ⟨gen k a,gen k b,(preserves k a b).mpr e,ha,hb⟩
      · rintro ⟨a,b,e,ha,hb⟩
        obtain ⟨u,rfl⟩ := onto k a
        obtain ⟨v,rfl⟩ := onto k b
        exact ⟨u,v,(preserves k u v).mp e,ha,hb⟩
    let extend (f : Fin 25 → Fin 25) (i : Fin 26) : Fin 26 :=
      if h : i.val < 25 then (f ⟨i.val,h⟩).castSucc else Fin.last 25
    have comp (f g : Fin 25 → Fin 25) (i : Fin 26) :
        extend (fun w => f (g w)) i = extend f (extend g i) := by
      by_cases h : i.val < 25
      · simp [extend,h,Fin.val_castSucc]
      · simp [extend,h,Fin.val_last]
    let representative (a b : Fin 26) : Prop :=
      26 * min a.val b.val + max a.val b.val ∈ ([0, 1, 2, 12, 13, 14, 16, 25, 324, 325, 328, 337, 351, 352, 363, 675] : List ℕ)
    let guide (a b : Fin 26) : Fin 4 :=
      Fin.ofNat 4 ((([0, 8, 28, 238, 999, 2919, 14310, 44923, 93853, 694762, 2800251, 12040539, 16613340, 14391784, 300587480, 1840184155, 14439529432, 67572989807, 92742850294, 750272556927, 1603732871031, 7066758904154, 42462926842555, 270342354007467, 820917159242410, 815422369283032] : List ℕ).getD (max a.val b.val) 0) / 4 ^ (min a.val b.val))
    let rank (a b : Fin 26) : ℕ :=
      ((([0, 0, 32, 0, 608, 0, 5138, 0, 202069, 0, 3425109, 0, 37954356, 0, 877864244, 0, 4652806721, 0, 91621762081, 0, 2345911268964, 0, 75201694151203, 0, 73810124673584, 0, 91346496329248, 0, 1483680198759776, 80, 641179867034163, 562, 72641624085024, 4945, 1204039710876996, 209985, 1220819812635988, 3486803, 1498931833038132, 54735699, 372052419093863, 340862003, 1216422086980133, 17821876818, 653196933735731, 90802754385, 918458393192035, 2423490159172, 920588464240164, 39810929861730, 72641624085024, 37469616804432] : List ℕ).getD (2 * max a.val b.val + min a.val b.val / 13) 0) /
        16 ^ (min a.val b.val % 13)) % 16
    have descend : ∀ a b, representative a b ∨
        rank (extend (gen (guide a b)) a) (extend (gen (guide a b)) b) < rank a b := by
      decide +kernel
    have normalize : ∀ a b, ∃ f : Fin 25 → Fin 25,
        (∀ x, good (fun i => x (f i)) ↔ good x) ∧ representative (extend f a) (extend f b) := by
      have byRank (d : ℕ) : ∀ a b, rank a b = d → ∃ f : Fin 25 → Fin 25,
          (∀ x, good (fun i => x (f i)) ↔ good x) ∧ representative (extend f a) (extend f b) := by
        induction d using Nat.strong_induction_on with
        | _ d ih =>
          intro a b distance
          rcases descend a b with done | closer
          · have identical (i : Fin 26) : extend id i = i := by
              apply Fin.ext
              by_cases h : i.val < 25
              · simp [extend,h]
              · simp [extend,h]
                omega
            exact ⟨id,fun _ => Iff.rfl,by simpa only [identical] using done⟩
          · let g := gen (guide a b)
            obtain ⟨f,aut,canonical⟩ := ih _ (distance ▸ closer) (extend g a) (extend g b) rfl
            refine ⟨fun i => f (g i), fun x => (acts (guide a b) (fun i => x (f i))).trans (aut x), ?_⟩
            rw [comp f g a, comp f g b]
            exact canonical
      exact fun a b => byRank _ a b rfl
    let select (x : Fin 25 → Bool) (a : Fin 26) := (List.ofFn x).getD a.val false
    let address (w : ℕ) : Fin 26 :=
      if h : w < 25 then (⟨w,h⟩ : Fin 25).castSucc else Fin.last 25
    have lookup (x : Fin 25 → Bool) (i : ℕ) :
        (List.ofFn x).getD i false = if h : i < 25 then x ⟨i,h⟩ else false := by
      by_cases h : i < 25
      · rw [dif_pos h, List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using h), List.getElem_ofFn]
      · rw [dif_neg h, List.getD_eq_default _ _ (by simp; omega)]
    have addressRead (x : Fin 25 → Bool) (w : ℕ) :
        (List.ofFn x).getD w false = select x (address w) := by
      by_cases h : w < 25 <;> simp [select,address,h,lookup]
    have selectExt (f : Fin 25 → Fin 25) (x : Fin 25 → Bool) (a : Fin 26) :
        select x (extend f a) = select (fun i => x (f i)) a := by
      simp only [select,lookup]
      by_cases h : a.val < 25 <;> simp [extend,h]
    let combine (both : Bool) (a b : Bool) := if both then a && b else a || b
    let wire (f : Fin 25 → Fin 25) (w : ℕ) : ℕ := if h : w < 25 then (f ⟨w,h⟩).val else w
    let renGate (f : Fin 25 → Fin 25) (g : Gate) : Gate := ⟨g.op, g.inputs.map (wire f)⟩
    let rename (f : Fin 25 → Fin 25) (D : Circuit) : Circuit :=
      ⟨D.gates.map (renGate f), wire f D.output⟩
    let step (u : List Bool) (g : Gate) := u ++ [g.op.eval (g.inputs.map fun i => u.getD i false)]
    have readSnoc (u : List Bool) (b : Bool) (w : ℕ) :
        (u ++ [b]).getD w false = if w = u.length then b else u.getD w false := by
      by_cases same : w = u.length
      · subst w
        simp [List.getD_eq_getElem?_getD]
      · rw [ite_eq_right same]
        by_cases before : w < u.length
        · exact List.getD_append _ _ _ _ before
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
    have above (f : Fin 25 → Fin 25) (w m : ℕ) (hl : 25 ≤ m) : wire f w = m ↔ w = m := by
      by_cases h : w < 25
      · have less : wire f w < 25 := by simpa only [wire,dif_pos h] using (f ⟨w,h⟩).isLt
        omega
      · simp [wire,h]
    have sim (f : Fin 25 → Fin 25) (gs : List Gate) (u v : List Bool)
        (huv : u.length = v.length) (hl : 25 ≤ u.length)
        (agree : ∀ w, u.getD (wire f w) false = v.getD w false) :
        ∀ w, ((gs.map (renGate f)).foldl step u).getD (wire f w) false =
          (gs.foldl step v).getD w false := by
      induction gs generalizing u v with
      | nil => exact agree
      | cons g gs ih =>
        apply ih (step u (renGate f g)) (step v g) (by simp [step,huv]) (by simp [step]; omega)
        intro w
        have nextVal : (renGate f g).op.eval ((renGate f g).inputs.map fun i => u.getD i false) =
            g.op.eval (g.inputs.map fun i => v.getD i false) := by
          simp only [renGate,List.map_map,Function.comp_def,agree]
        simp only [step,readSnoc,nextVal,huv,above f w v.length (huv ▸ hl),agree]
    have asInput (f : Fin 25 → Fin 25) (x : Fin 25 → Bool) (w : ℕ) :
        (List.ofFn x).getD (wire f w) false = (List.ofFn fun i => x (f i)).getD w false := by
      simp only [lookup]
      by_cases h : w < 25 <;> simp [wire,h]
    have simTail (f : Fin 25 → Fin 25) (D : Circuit) (x : Fin 25 → Bool) (extra : Bool) :
        (rename f D).eval (List.ofFn x ++ [extra]) =
          D.eval (List.ofFn (fun i => x (f i)) ++ [extra]) := by
      apply sim f D.gates _ _ (by simp) (by simp) _ D.output
      intro w
      simp only [readSnoc,List.length_ofFn,above f w 25 (Nat.le_refl _),asInput]
    have monoRename (f : Fin 25 → Fin 25) (D : Circuit) (h : Monotone2 D) :
        Monotone2 (rename f D) := by
      intro g hg
      change g ∈ D.gates.map (renGate f) at hg
      obtain ⟨old,mem,rfl⟩ := List.mem_map.mp hg
      simpa only [renGate,List.length_map] using h old mem
    have renameSize (f : Fin 25 → Fin 25) (D : Circuit) : (rename f D).size = D.size := by
      simp [rename,Circuit.size]
    intro C hm correct
    have hc (x : Fin 25 → Bool) : C.eval (List.ofFn x) = true ↔ good x := correct x
    cases gates : C.gates with
    | nil =>
      let pair (p : Fin 12) (l : Fin 13) (i : Fin 25) :=
        decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 12 l)
      have avoiding : ∀ w : Fin 26, ∃ p l, incident p l ∧ select (pair p l) w = false := by
        decide +kernel
      obtain ⟨p,l,e,off⟩ := avoiding (address C.output)
      have hit := (hc (pair p l)).mpr ⟨p,l,e,by simp [pair],by simp [pair]⟩
      have out : C.eval (List.ofFn (pair p l)) = (List.ofFn (pair p l)).getD C.output false := by
        simp only [Circuit.eval,Circuit.wires,gates,List.foldl_nil]
      rw [out,addressRead,off] at hit
      contradiction
    | cons g gs =>
      let D : Circuit := ⟨gs,C.output⟩
      have gm := hm g (by simp [gates])
      have dm : Monotone2 D := by
        intro h hh
        apply hm h
        rw [gates]
        exact List.mem_cons_of_mem _ hh
      have sz : C.size = D.size+1 := by simp [D,Circuit.size,gates]
      have valid (x : Fin 25 → Bool) :
          D.eval (List.ofFn x ++ [g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false)]) = true ↔ good x := by
        simpa only [D,Circuit.eval,Circuit.wires,gates,List.foldl_cons] using hc x
      have ops : g.op = .and ∨ g.op = .or := by
        simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using gm.1
      obtain ⟨both,op⟩ : ∃ both : Bool, g.op = (if both then GateOp.and else GateOp.or) := by
        rcases ops with hand | hor
        · exact ⟨true,hand⟩
        · exact ⟨false,hor⟩
      have pairBound (a b : Fin 26) (gateValue : ∀ x : Fin 25 → Bool,
          g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) =
            combine both (select x a) (select x b)) : 57 ≤ D.size := by
        obtain ⟨f,aut,rep⟩ := normalize a b
        have transformed (x : Fin 25 → Bool) :
            (rename f D).eval (List.ofFn x ++ [combine both (select x (extend f a)) (select x (extend f b))]) =
              true ↔ good x := by
          rw [selectExt,selectExt,simTail]
          rw [← gateValue (fun i => x (f i))]
          exact (valid (fun i => x (f i))).trans (aut x)
        have h := pairCase both (extend f a) (extend f b) (rename f D) rep (monoRename f D dm) transformed
        rwa [renameSize] at h
      have residual : 57 ≤ D.size := by
        cases inputs : g.inputs with
        | nil =>
          apply constantCase (g.op.eval []) D dm
          intro x
          simpa only [inputs,List.map_nil] using valid x
        | cons a ws =>
          cases rest : ws with
          | nil =>
            apply pairBound (address a) (address a)
            intro x
            rw [inputs,rest,op]
            simp only [List.map_cons,List.map_nil,addressRead]
            cases both <;> simp [GateOp.eval,combine]
          | cons b more =>
            cases tail : more with
            | nil =>
              apply pairBound (address a) (address b)
              intro x
              rw [inputs,rest,tail,op]
              simp only [List.map_cons,List.map_nil,addressRead]
              cases both <;> simp [GateOp.eval,combine]
            | cons c endList =>
              have h := gm.2
              simp [inputs,rest,tail] at h
      omega
  intro C v mono computes
  let left (i : Fin 13) : Option (Fin 25) := Fin.cases none (fun j : Fin 12 => some (Fin.castAdd 13 j)) i
  let right (i : Fin 13) : Option (Fin 25) := some (Fin.natAdd 12 i)
  let adj (a b : Fin 13) := a = b ∨ a = b+1 ∨ a = b+3 ∨ a = b+9
  let shift (z : Fin 26) : Fin 13 := Fin.ofNat 13 z.val
  let f (z : Fin 26) (a b : Fin 13) : Fin 13 × Fin 13 :=
    if z.val < 13 then (a-shift z,b-shift z) else (shift z-b,shift z-a)
  let inv (z : Fin 26) (a b : Fin 13) : Fin 13 × Fin 13 :=
    if z.val < 13 then (a+shift z,b+shift z) else (shift z-b,shift z-a)
  let p (z i : Fin 26) : Option (Fin 25) := Fin.addCases (motive := fun _ => Option (Fin 25))
    (fun a : Fin 13 => if z.val < 13 then left (a-shift z) else right (shift z-a))
    (fun b : Fin 13 => if z.val < 13 then right (b-shift z) else left (shift z-b)) i
  have removed : ∀ z, p z z = none := by decide +kernel
  have back : ∀ z a b, f z (inv z a b).1 (inv z a b).2 = (a,b) := by decide +kernel
  have preserves : ∀ z a b, adj a b ↔ adj (f z a b).1 (f z a b).2 := by decide +kernel
  have ends : ∀ z a b,
      (p z (Fin.castAdd 13 a) = left (f z a b).1 ∧ p z (Fin.natAdd 13 b) = right (f z a b).2) ∨
      (p z (Fin.castAdd 13 a) = right (f z a b).2 ∧ p z (Fin.natAdd 13 b) = left (f z a b).1) := by
    decide +kernel
  obtain ⟨D,hd,size,ev⟩ := projection C (p v) mono
  rw [← size]
  apply fixed D hd
  intro y
  let read (a : Option (Fin 25)) := a.elim false y
  have off : read (p v v) = false := by rw [removed]; rfl
  rw [ev,computes _ off]
  have signal (a b : Fin 13) :
      (read (p v (Fin.castAdd 13 a)) = true ∧ read (p v (Fin.natAdd 13 b)) = true) ↔
      (read (left (f v a b).1) = true ∧ read (right (f v a b).2) = true) := by
    rcases ends v a b with ⟨h,j⟩ | ⟨h,j⟩
    · rw [h,j]
    · rw [h,j,and_comm]
  constructor
  · rintro ⟨a,b,ha,hab⟩
    have edge := (preserves v a b).mp ha
    have values := (signal a b).mp hab
    obtain ⟨u,w,h⟩ : ∃ u w, f v a b = (u,w) := ⟨_,_,rfl⟩
    rw [h] at edge values
    change adj u w at edge
    change read (left u) = true ∧ read (right w) = true at values
    revert edge values
    refine Fin.cases ?_ (fun i => ?_) u
    · intro _ vals; exact False.elim (Bool.noConfusion vals.1)
    · intro edge vals; exact ⟨i,w,edge,vals.1,vals.2⟩
  · rintro ⟨i,w,edge,hi,hw⟩
    let a := (inv v i.succ w).1
    let b := (inv v i.succ w).2
    have h : f v a b = (i.succ,w) := back v i.succ w
    refine ⟨a,b,(preserves v a b).mpr ?_,(signal a b).mpr ?_⟩
    · rw [h]; exact edge
    · rw [h]; exact ⟨hi,hw⟩
