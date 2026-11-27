import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1063

theorem independentEvalSurjective {ι X : Type*} [Fintype ι] [AddCommGroup X] [Module (ZMod 2) X]
    (a : ι → X →ₗ[ZMod 2] ZMod 2) (ha : LinearIndependent (ZMod 2) a) :
    Function.Surjective (LinearMap.pi a) := by
  let L := LinearMap.ltoFun (ZMod 2) X (ZMod 2) (ZMod 2)
  have hi : Function.Injective L := fun _ _ h => LinearMap.ext (congrFun h)
  have hli : LinearIndependent (ZMod 2) (fun i x => a i x) :=
    (L.linearIndependent_iff_of_injOn hi.injOn).2 ha
  have h := span_flip_eq_top_iff_linearIndependent.mpr hli
  change Submodule.span (ZMod 2) (Set.range (LinearMap.pi a)) = ⊤ at h
  have incl : Submodule.span (ZMod 2) (Set.range (LinearMap.pi a)) ≤ LinearMap.range (LinearMap.pi a) :=
    Submodule.span_le.mpr (fun _ m => m)
  rw [h] at incl
  exact LinearMap.range_eq_top.mp (top_unique incl)

private noncomputable def preimageProduct {X Y : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup Y] [Module (ZMod 2) Y]
    (f : X →ₗ[ZMod 2] Y) (hf : Function.Surjective f) (P : Y → Prop) :
    {x : X // P (f x)} ≃ {y : Y // P y} × LinearMap.ker f := by
  let g := Function.surjInv hf
  have right (y : Y) : f (g y) = y := Function.rightInverse_surjInv hf y
  refine { toFun := fun x =>
             (⟨f x, x.property⟩, ⟨x.val - g (f x), by change f _ = 0; simp [map_sub, right]⟩)
           invFun := fun y =>
             ⟨(y.2 : X) + g y.1, by
               have hz : f y.2 = 0 := y.2.property
               simpa only [map_add, hz, right, zero_add] using y.1.property⟩
           left_inv := ?_
           right_inv := ?_ }
  · intro x
    apply Subtype.ext
    exact sub_add_cancel _ _
  · rintro ⟨⟨y, hy⟩, ⟨x, hx⟩⟩
    change f x = 0 at hx
    apply Prod.ext
    · apply Subtype.ext
      change f (x+g y) = y
      simp [map_add, hx, right]
    · apply Subtype.ext
      change x + g y - g (f (x+g y)) = x
      simp [map_add, hx, right]

theorem preimageCount {X Y : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup Y] [Module (ZMod 2) Y] [Finite X] [Finite Y]
    (f : X →ₗ[ZMod 2] Y) (hf : Function.Surjective f) (P : Y → Prop) :
    Nat.card {x : X // P (f x)} = Nat.card {y : Y // P y} * Nat.card (LinearMap.ker f) :=
  (Nat.card_congr (preimageProduct f hf P)).trans (Nat.card_prod _ _)

theorem uniformPushforward {X Y : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup Y] [Module (ZMod 2) Y] [Finite X] [Finite Y]
    (f : X →ₗ[ZMod 2] Y) (hf : Function.Surjective f) (P : Y → Prop) :
    Nat.card {x : X // P (f x)} * Nat.card Y = Nat.card {y : Y // P y} * Nat.card X := by
  have total := preimageCount f hf (fun _ => True)
  simp only [Nat.card_subtype_true] at total
  rw [preimageCount f hf P, total]
  ring

def coordinateExtra {ι : Type*} (c : Option (Finset ι)) (z : (ι → ZMod 2) × ZMod 2) : ZMod 2 :=
  match c with
  | none => z.2
  | some T => ∑ i ∈ T, z.1 i

theorem extraCoordinates {ι X : Type*} [Fintype ι] [AddCommGroup X] [Module (ZMod 2) X]
    (a : ι → X →ₗ[ZMod 2] ZMod 2) (ha : LinearIndependent (ZMod 2) a) (u : X →ₗ[ZMod 2] ZMod 2) :
    ∃ (L : (X × ZMod 2) →ₗ[ZMod 2] ((ι → ZMod 2) × ZMod 2)) (c : Option (Finset ι)),
      Function.Surjective L ∧ (∀ x i, (L x).1 i = a i x.1) ∧
        ∀ x, u x.1 = coordinateExtra c (L x) := by
  classical
  by_cases dep : u ∈ Submodule.span (ZMod 2) (Set.range a)
  · obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp dep
    let T := Finset.univ.filter (fun i => w i = 1)
    let L : X × ZMod 2 →ₗ[ZMod 2] (ι → ZMod 2) × ZMod 2 := (LinearMap.pi a).prodMap LinearMap.id
    refine ⟨L, some T, ?_, fun _ _ => rfl, ?_⟩
    · rintro ⟨y,t⟩
      obtain ⟨x, hx⟩ := independentEvalSurjective a ha y
      exact ⟨(x,t), Prod.ext hx rfl⟩
    · rintro ⟨x,t⟩
      change u x = ∑ i ∈ T, a i x
      rw [← hw, LinearMap.sum_apply, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      have h01 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
      rcases h01 (w i) with h | h <;> simp [h]
  · let fam : Option ι → X →ₗ[ZMod 2] ZMod 2 := fun j => Option.casesOn' j u a
    let L : X × ZMod 2 →ₗ[ZMod 2] (ι → ZMod 2) × ZMod 2 :=
      ((LinearMap.pi a).prod u).comp (LinearMap.fst (ZMod 2) X (ZMod 2))
    refine ⟨L, none, ?_, fun _ _ => rfl, fun _ => rfl⟩
    rintro ⟨y,t⟩
    let target : Option ι → ZMod 2 := fun j => Option.casesOn' j t y
    obtain ⟨x, hx⟩ := independentEvalSurjective fam (ha.option dep) target
    refine ⟨(x,0), Prod.ext (funext fun i => ?_) ?_⟩
    · exact congrFun hx (some i)
    · exact congrFun hx none

end PEqualNP.Outside.L_lib_1063

namespace PEqualNP.Outside.L_lib_1063

theorem matchingTargetCards (I : Type*) [Fintype I] :
    Nat.card {v : (I → ZMod 2) × (I → ZMod 2) // ∀ i, v.1 i * v.2 i = 0} =
      3 ^ Fintype.card I ∧
    Nat.card ((I → ZMod 2) × (I → ZMod 2)) = 4 ^ Fintype.card I := by
  let A := {p : ZMod 2 × ZMod 2 // p.1 * p.2 = 0}
  let good := {v : (I → ZMod 2) × (I → ZMod 2) // ∀ i, v.1 i * v.2 i = 0}
  let e : good ≃ (I → A) :=
    { toFun := fun z i => ⟨(z.val.1 i, z.val.2 i), z.property i⟩
      invFun := fun f => ⟨(fun i => (f i).val.1, fun i => (f i).val.2), fun i => (f i).property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have three : Nat.card A = 3 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have two : Nat.card (ZMod 2) = 2 := by simp [Nat.card_eq_fintype_card, ZMod.card]
  constructor
  · rw [Nat.card_congr e, Nat.card_fun, three, Nat.card_eq_fintype_card (α := I)]
  · rw [Nat.card_prod, Nat.card_fun, two, ← mul_pow, Nat.card_eq_fintype_card (α := I)]
    norm_num

theorem pureMatchingConditions {I X Y : Type*} [DecidableEq I] (indices : Finset I)
    [AddCommGroup X] [Module (ZMod 2) X] [AddCommGroup Y] [Module (ZMod 2) Y]
    (a : I → X →ₗ[ZMod 2] ZMod 2) (b : I → Y →ₗ[ZMod 2] ZMod 2)
    (pure : ∀ i, a i = 0 ∨ b i = 0 ∨ ∃ s ∈ indices, a i = a s ∧ b i = b s)
    (x : X) (y : Y) :
    (∀ i, a i x * b i y = 0) ↔ ∀ s : indices, a s.val x * b s.val y = 0 := by
  constructor
  · exact fun h s => h s.val
  · intro h i
    rcases pure i with h0 | h0 | ⟨j, hj, ha, hb⟩
    · simp [h0]
    · simp [h0]
    · simpa only [ha, hb] using h ⟨j,hj⟩

end PEqualNP.Outside.L_lib_1063

namespace PEqualNP.Outside.L_lib_1063

theorem matchingCard {I X Y : Type*} [Fintype I]
    [AddCommGroup X] [Module (ZMod 2) X] [AddCommGroup Y] [Module (ZMod 2) Y]
    [Finite X] [Finite Y] (a : I → X →ₗ[ZMod 2] ZMod 2) (b : I → Y →ₗ[ZMod 2] ZMod 2)
    (ha : LinearIndependent (ZMod 2) a) (hb : LinearIndependent (ZMod 2) b) :
    4 ^ Fintype.card I * Nat.card {w : X × Y // ∀ i, a i w.1 * b i w.2 = 0} =
      3 ^ Fintype.card I * (Nat.card X * Nat.card Y) := by
  let L := (LinearMap.pi a).prodMap (LinearMap.pi b)
  let P (v : (I → ZMod 2) × (I → ZMod 2)) : Prop := ∀ i, v.1 i * v.2 i = 0
  have onto : Function.Surjective L := by
    rintro ⟨u,v⟩
    obtain ⟨x,hx⟩ := independentEvalSurjective a ha u
    obtain ⟨y,hy⟩ := independentEvalSurjective b hb v
    exact ⟨(x,y), Prod.ext hx hy⟩
  have counts := uniformPushforward L onto P
  obtain ⟨target, all⟩ := matchingTargetCards I
  change Nat.card {w : X × Y // ∀ i, a i w.1 * b i w.2 = 0} *
      Nat.card ((I → ZMod 2) × (I → ZMod 2)) =
    Nat.card {v : (I → ZMod 2) × (I → ZMod 2) // ∀ i, v.1 i * v.2 i = 0} *
      Nat.card (X × Y) at counts
  rw [all, target, Nat.card_prod] at counts
  simpa only [mul_comm (4 ^ Fintype.card I)] using counts

theorem pureCount {m X Y : Type*} [DecidableEq m]
    [AddCommGroup X] [Module (ZMod 2) X] [AddCommGroup Y] [Module (ZMod 2) Y]
    [Finite X] [Finite Y]
    (a : m → X →ₗ[ZMod 2] ZMod 2) (b : m → Y →ₗ[ZMod 2] ZMod 2) (S : Finset m)
    (ha : LinearIndependent (ZMod 2) (fun i : S => a i.val))
    (hb : LinearIndependent (ZMod 2) (fun i : S => b i.val))
    (pure : ∀ i, a i = 0 ∨ b i = 0 ∨ ∃ s ∈ S, a i = a s ∧ b i = b s) :
    4 ^ S.card * Nat.card {w : X × Y // ∀ i, a i w.1 * b i w.2 = 0} =
      3 ^ S.card * (Nat.card X * Nat.card Y) := by
  let e := Equiv.subtypeEquivRight (fun w : X × Y => pureMatchingConditions S a b pure w.1 w.2)
  rw [Nat.card_congr e]
  simpa using matchingCard (fun i : S => a i.val) (fun i : S => b i.val) ha hb

end PEqualNP.Outside.L_lib_1063

namespace PEqualNP.Outside.L_lib_1063

open scoped Classical

abbrev PairState := {p : ZMod 2 × ZMod 2 // p.1 * p.2 = 0}
abbrev Site (S : Type*) := S ⊕ Bool

def Alphabet {S : Type*} : Site S → Type
  | .inl _ => PairState
  | .inr _ => ZMod 2

instance {S : Type*} (s : Site S) : Fintype (Alphabet s) := by
  cases s with
  | inl _ => exact inferInstanceAs (Fintype PairState)
  | inr _ => exact inferInstanceAs (Fintype (ZMod 2))

abbrev Config (S : Type*) := (s : Site S) → Alphabet s

def leftSite {S : Type*} : Option S → Site S
  | none => .inr false
  | some s => .inl s

def rightSite {S : Type*} : Option S → Site S
  | none => .inr true
  | some s => .inl s

def leftAt {S : Type*} (w : Config S) : Option S → ZMod 2
  | none => w (.inr false)
  | some s => (w (.inl s)).val.1

def rightAt {S : Type*} (w : Config S) : Option S → ZMod 2
  | none => w (.inr true)
  | some s => (w (.inl s)).val.2

def bitValue {S : Type*} (c : Option (Finset S)) (v : Option S → ZMod 2) : ZMod 2 :=
  match c with
  | none => v none
  | some T => ∑ s ∈ T, v (some s)

def extraL {S : Type*} (c : Option (Finset S)) (w : Config S) := bitValue c (leftAt w)
def extraR {S : Type*} (c : Option (Finset S)) (w : Config S) := bitValue c (rightAt w)

def selects {S : Type*} : Option (Finset S) → Option S → Prop
  | none, none => True
  | some T, some i => i ∈ T
  | _, _ => False

lemma nineFiberCount {Ω K : Type*} [Fintype K] [DecidableEq K] (A G : Finset Ω) (p : Ω → K)
    (sub : G ⊆ A) (cap : ∀ k, (A.filter (fun x => p x = k)).card ≤ 9)
    (escape : ∀ x ∈ A, ∃ y ∈ A, p y = p x ∧ y ∉ G) : 9 * G.card ≤ 8 * A.card := by
  classical
  have partition (B : Finset Ω) :
      B.card = ∑ k, (B.filter (fun x => p x = k)).card :=
    Finset.card_eq_sum_card_fiberwise (t := Finset.univ) (f := p) (fun _ _ => Finset.mem_univ _)
  rw [partition G, partition A, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  have incl : G.filter (fun x => p x = k) ⊆ A.filter (fun x => p x = k) :=
    fun x hx => Finset.mem_filter.mpr ⟨sub (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩
  by_cases hn : (A.filter (fun x => p x = k)).Nonempty
  · obtain ⟨x,hx⟩ := hn
    obtain ⟨y,hy,he,hnG⟩ := escape x (Finset.mem_filter.mp hx).1
    have hy' : y ∈ A.filter (fun w => p w = k) :=
      Finset.mem_filter.mpr ⟨hy, he.trans (Finset.mem_filter.mp hx).2⟩
    have strict : G.filter (fun x => p x = k) ⊂ A.filter (fun x => p x = k) :=
      ⟨incl, fun back => hnG (Finset.mem_filter.mp (back hy')).1⟩
    have hlt := Finset.card_lt_card strict
    have hcap := cap k
    omega
  · have hzero := Finset.not_nonempty_iff_eq_empty.mp hn
    have hle := Finset.card_le_card incl
    rw [hzero, Finset.card_empty] at hle ⊢
    omega

lemma nineProductCount {I : Type*} [Fintype I] [DecidableEq I] {α : I → Type*} [∀ i, Fintype (α i)]
    (i j : I) (G : Finset ((k : I) → α k))
    (hi : Fintype.card (α i) ≤ 3) (hj : Fintype.card (α j) ≤ 3)
    (escape : ∀ x : (k : I) → α k, ∃ y ∉ G, ∀ k, k ≠ i → k ≠ j → y k = x k) :
    9 * G.card ≤ 8 * Fintype.card ((k : I) → α k) := by
  classical
  let O := {k : I // k ≠ i ∧ k ≠ j}
  let p (x : (k : I) → α k) := fun k : O => x k.val
  have cap (v : (k : O) → α k.val) :
      (Finset.univ.filter (fun x => p x = v)).card ≤ 9 := by
    let D := Finset.univ.filter (fun x => p x = v)
    let f (x : D) : α i × α j := (x.val i, x.val j)
    have inj : Function.Injective f := by
      intro x y h
      apply Subtype.ext
      funext k
      by_cases hki : k = i
      · subst k; exact congrArg Prod.fst h
      by_cases hkj : k = j
      · subst k; exact congrArg Prod.snd h
      have hx : p x.val = v := (Finset.mem_filter.mp x.prop).2
      have hy : p y.val = v := (Finset.mem_filter.mp y.prop).2
      exact congrFun (hx.trans hy.symm) ⟨k,hki,hkj⟩
    have h := Fintype.card_le_of_injective f inj
    rw [Fintype.card_coe, Fintype.card_prod] at h
    exact h.trans ((Nat.mul_le_mul hi hj).trans_eq (by decide))
  have h := nineFiberCount Finset.univ G p (Finset.subset_univ _) cap (by
    intro x _
    obtain ⟨y,hy,hs⟩ := escape x
    exact ⟨y, Finset.mem_univ _, funext (fun k => hs k.val k.prop.1 k.prop.2), hy⟩)
  simpa using h

lemma chooseBit {S : Type*} (c : Option (Finset S)) (i : Option S) (hi : selects c i)
    (f : Option S → ZMod 2) : ∃ u : ZMod 2,
      bitValue c (fun q => if q = i then u else f q) = 1 := by
  classical
  cases c with
  | none => cases i <;> simp_all [selects, bitValue]
  | some T =>
    cases i with
    | none => cases hi
    | some i =>
      change i ∈ T at hi
      refine ⟨1 - ∑ q ∈ T.erase i, f (some q), ?_⟩
      simp only [bitValue]
      rw [← Finset.add_sum_erase _ _ hi]
      have hsum : (∑ q ∈ T.erase i, if (some q : Option S) = some i then
          1 - ∑ q ∈ T.erase i, f (some q) else f (some q)) = ∑ q ∈ T.erase i, f (some q) := by
        apply Finset.sum_congr rfl
        intro k hk
        simp [(Finset.mem_erase.mp hk).1]
      rw [hsum, if_pos rfl]
      exact sub_add_cancel (1 : ZMod 2) _

def setPivots {S : Type*} [DecidableEq S] (w : Config S) (i j : Option S)
    (u v : ZMod 2) : Config S
  | .inl s =>
    if i = some s then ⟨(u,0), mul_zero _⟩
    else if j = some s then ⟨(0,v), zero_mul _⟩ else w (.inl s)
  | .inr false => if i = none then u else w (.inr false)
  | .inr true => if j = none then v else w (.inr true)

lemma pivotBits {S : Type*} [DecidableEq S] (w : Config S) (i j : Option S)
    (hij : leftSite i ≠ rightSite j) (u v : ZMod 2) :
    leftAt (setPivots w i j u v) =
      (fun q => if q = i then u else leftAt (setPivots w i j 0 0) q) ∧
    rightAt (setPivots w i j u v) =
      (fun q => if q = j then v else rightAt (setPivots w i j 0 0) q) := by
  constructor <;> funext q <;> by_cases h₁ : q = i <;> by_cases h₂ : q = j <;>
    cases q <;> cases i <;> cases j <;>
    simp_all [leftSite, rightSite, leftAt, rightAt, setPivots, eq_comm] <;> rfl

lemma pivotOutside {S : Type*} [DecidableEq S] (w : Config S) (i j : Option S)
    (u v : ZMod 2) (k : Site S) (hi : k ≠ leftSite i) (hj : k ≠ rightSite j) :
    setPivots w i j u v k = w k := by
  cases k with
  | inl s => cases i <;> cases j <;> simp_all [leftSite, rightSite, setPivots, eq_comm]
  | inr b => cases b <;> cases i <;> cases j <;> simp_all [leftSite, rightSite, setPivots]

lemma nine_good_configs {S : Type*} [Fintype S] (A B : Option (Finset S)) (i j : Option S)
    (hi : selects A i) (hj : selects B j) (hij : leftSite i ≠ rightSite j) :
    9 * Nat.card {w : Config S // extraL A w * extraR B w = 0} ≤ 8 * Nat.card (Config S) := by
  classical
  let G := Finset.univ.filter (fun w : Config S => extraL A w * extraR B w = 0)
  have bound (s : Site S) : Fintype.card (Alphabet s) ≤ 3 := by
    cases s with
    | inl _ => change Fintype.card PairState ≤ 3; decide
    | inr _ => change Fintype.card (ZMod 2) ≤ 3; decide
  have h := nineProductCount (leftSite i) (rightSite j) G (bound _) (bound _) (by
    intro w
    obtain ⟨u,hu⟩ := chooseBit A i hi (leftAt (setPivots w i j 0 0))
    obtain ⟨v,hv⟩ := chooseBit B j hj (rightAt (setPivots w i j 0 0))
    obtain ⟨hl,hr⟩ := pivotBits w i j hij u v
    refine ⟨setPivots w i j u v, ?_, pivotOutside w i j u v⟩
    simp [G, extraL, extraR, hl, hr, hu, hv])
  have hc : Nat.card {w : Config S // extraL A w * extraR B w = 0} = G.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hc]
  simpa only [← Nat.card_eq_fintype_card] using h

end PEqualNP.Outside.L_lib_1063

namespace PEqualNP.Outside.L_lib_1063

private abbrev Side (I : Type*) := (I → ZMod 2) × ZMod 2

private def matched {I : Type*} (w : Side I × Side I) : Prop :=
  ∀ s, w.1.1 s * w.2.1 s = 0

private def configEquiv (I : Type*) : {w : Side I × Side I // matched w} ≃ Config I where
  toFun w
    | .inl s => ⟨(w.val.1.1 s, w.val.2.1 s), w.property s⟩
    | .inr false => w.val.1.2
    | .inr true => w.val.2.2
  invFun w := ⟨((fun s => (w (.inl s)).val.1, w (.inr false)),
                (fun s => (w (.inl s)).val.2, w (.inr true))), fun s => (w (.inl s)).property⟩
  left_inv _ := rfl
  right_inv w := by
    funext s
    rcases s with s | b
    · rfl
    · cases b <;> rfl

private theorem modelGap {I : Type*} [Fintype I] (A B : Option (Finset I)) (i j : Option I)
    (hi : selects A i) (hj : selects B j) (hne : leftSite i ≠ rightSite j) :
    9 * Nat.card {w : Side I × Side I // matched w ∧ coordinateExtra A w.1 * coordinateExtra B w.2 = 0}
      ≤ 8 * Nat.card {w : Side I × Side I // matched w} := by
  let q (w : Side I × Side I) := coordinateExtra A w.1 * coordinateExtra B w.2 = 0
  let e := configEquiv I
  have eqs (w : {w : Side I × Side I // matched w}) :
      q w.val ↔ extraL A (e w) * extraR B (e w) = 0 := by
    cases A <;> cases B <;> rfl
  let keep (w : Config I) := extraL A w * extraR B w = 0
  let eqGood := (Equiv.subtypeSubtypeEquivSubtypeInter matched q).symm.trans
    (e.subtypeEquiv (q := keep) eqs)
  calc
    _ = 9 * Nat.card {w : Config I // keep w} := congrArg (9 * ·) (Nat.card_congr eqGood)
    _ ≤ 8 * Nat.card (Config I) := nine_good_configs A B i j hi hj hne
    _ = _ := congrArg (8 * ·) (Nat.card_congr e).symm

private theorem dummyCount {X Y : Type*} (P : X × Y → Prop) :
    Nat.card {z : (X × ZMod 2) × (Y × ZMod 2) // P (z.1.1, z.2.1)} =
      Nat.card {w : X × Y // P w} * 4 := by
  let e : {z : (X × ZMod 2) × (Y × ZMod 2) // P (z.1.1, z.2.1)} ≃
      {w : X × Y // P w} × (ZMod 2 × ZMod 2) :=
    { toFun := fun z => (⟨(z.val.1.1, z.val.2.1), z.property⟩, (z.val.1.2, z.val.2.2))
      invFun := fun z => ⟨((z.1.val.1,z.2.1), (z.1.val.2,z.2.2)), z.1.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hf : Nat.card (ZMod 2 × ZMod 2) = 4 := by rw [Nat.card_eq_fintype_card]; decide
  rw [Nat.card_congr e, Nat.card_prod, hf]

private theorem transferGap {I X Y : Type*} [Fintype I]
    [AddCommGroup X] [Module (ZMod 2) X] [AddCommGroup Y] [Module (ZMod 2) Y]
    [Finite X] [Finite Y] (a : I → X →ₗ[ZMod 2] ZMod 2) (b : I → Y →ₗ[ZMod 2] ZMod 2)
    (u : X →ₗ[ZMod 2] ZMod 2) (v : Y →ₗ[ZMod 2] ZMod 2)
    (L : X × ZMod 2 →ₗ[ZMod 2] Side I) (R : Y × ZMod 2 →ₗ[ZMod 2] Side I)
    (A B : Option (Finset I)) (hL : Function.Surjective L) (hR : Function.Surjective R)
    (al : ∀ x i, (L x).1 i = a i x.1) (br : ∀ y i, (R y).1 i = b i y.1)
    (hu : ∀ x, u x.1 = coordinateExtra A (L x)) (hv : ∀ y, v y.1 = coordinateExtra B (R y))
    (i j : Option I) (hi : selects A i) (hj : selects B j) (hne : leftSite i ≠ rightSite j) :
    9 * Nat.card {w : X × Y // (∀ k, a k w.1 * b k w.2 = 0) ∧ u w.1 * v w.2 = 0}
      ≤ 8 * Nat.card {w : X × Y // ∀ k, a k w.1 * b k w.2 = 0} := by
  let f := L.prodMap R
  have onto : Function.Surjective f := by
    rintro ⟨x,y⟩
    obtain ⟨x',hx⟩ := hL x
    obtain ⟨y',hy⟩ := hR y
    exact ⟨(x',y'), Prod.ext hx hy⟩
  let Q (w : Side I × Side I) := matched w ∧ coordinateExtra A w.1 * coordinateExtra B w.2 = 0
  let P (w : X × Y) := ∀ k, a k w.1 * b k w.2 = 0
  have key (z : (X × ZMod 2) × (Y × ZMod 2)) : matched (f z) ↔ P (z.1.1, z.2.1) := by
    change (∀ k, (L z.1).1 k * (R z.2).1 k = 0) ↔ _
    simp only [al, br, P]
  have keys (z : (X × ZMod 2) × (Y × ZMod 2)) :
      Q (f z) ↔ P (z.1.1, z.2.1) ∧ u z.1.1 * v z.2.1 = 0 := by
    change (matched (f z) ∧ coordinateExtra A (L z.1) * coordinateExtra B (R z.2) = 0) ↔ _
    rw [key, ← hu, ← hv]
  have all := preimageCount f onto matched
  have keep := preimageCount f onto Q
  rw [Nat.card_congr (Equiv.subtypeEquivRight key), dummyCount P] at all
  rw [Nat.card_congr (Equiv.subtypeEquivRight keys),
      dummyCount (fun w => P w ∧ u w.1 * v w.2 = 0)] at keep
  have bound := Nat.mul_le_mul_right (Nat.card (LinearMap.ker f)) (modelGap A B i j hi hj hne)
  rw [Nat.mul_assoc, Nat.mul_assoc 8, ← all, ← keep] at bound
  change 9 * Nat.card {w : X × Y // P w ∧ u w.1 * v w.2 = 0} ≤ 8 * Nat.card {w : X × Y // P w}
  omega

end PEqualNP.Outside.L_lib_1063

namespace PEqualNP.Outside.L_lib_1063

private theorem hasSelectedSite {I X : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    (u : X →ₗ[ZMod 2] ZMod 2) (L : X × ZMod 2 →ₗ[ZMod 2] ((I → ZMod 2) × ZMod 2))
    (c : Option (Finset I)) (rep : ∀ x, u x.1 = coordinateExtra c (L x)) (nonzero : u ≠ 0) :
    ∃ i, selects c i := by
  classical
  cases c with
  | none => exact ⟨none, trivial⟩
  | some T =>
    by_cases ht : T.Nonempty
    · obtain ⟨i,hi⟩ := ht
      exact ⟨some i,hi⟩
    · obtain rfl := Finset.not_nonempty_iff_eq_empty.mp ht
      exact (nonzero (LinearMap.ext (fun x => by
        simpa [coordinateExtra] using rep (x,0)))).elim

private theorem sharedSite {I : Type*} {i j : Option I} (eq : leftSite i = rightSite j) :
    ∃ s, i = some s ∧ j = some s := by
  cases i <;> cases j <;> simp_all [leftSite, rightSite]

private theorem singletonCode {I : Type*} [DecidableEq I]
    (c : Option (Finset I)) (s : I) (hs : selects c (some s))
    (unique : ∀ i, selects c i → i = some s) : c = some {s} := by
  cases c with
  | none => cases hs
  | some T =>
    congr 1
    ext j
    rw [Finset.mem_singleton]
    exact ⟨fun h => Option.some.inj (unique (some j) h), fun h => h.symm ▸ hs⟩

theorem choosePivots {I X Y : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup Y] [Module (ZMod 2) Y]
    (a : I → X →ₗ[ZMod 2] ZMod 2) (b : I → Y →ₗ[ZMod 2] ZMod 2)
    (u : X →ₗ[ZMod 2] ZMod 2) (v : Y →ₗ[ZMod 2] ZMod 2)
    (L : X × ZMod 2 →ₗ[ZMod 2] ((I → ZMod 2) × ZMod 2))
    (R : Y × ZMod 2 →ₗ[ZMod 2] ((I → ZMod 2) × ZMod 2))
    (A B : Option (Finset I))
    (al : ∀ x i, (L x).1 i = a i x.1) (br : ∀ y i, (R y).1 i = b i y.1)
    (hu : ∀ x, u x.1 = coordinateExtra A (L x)) (hv : ∀ y, v y.1 = coordinateExtra B (R y))
    (un : u ≠ 0) (vn : v ≠ 0) (different : ∀ s, ¬ (u = a s ∧ v = b s)) :
    ∃ i j, selects A i ∧ selects B j ∧ leftSite i ≠ rightSite j := by
  classical
  obtain ⟨i,hi⟩ := hasSelectedSite u L A hu un
  obtain ⟨j,hj⟩ := hasSelectedSite v R B hv vn
  by_contra no
  have same (i j : Option I) (hi : selects A i) (hj : selects B j) : leftSite i = rightSite j :=
    by_contra (fun ne => no ⟨i,j,hi,hj,ne⟩)
  obtain ⟨s,rfl,rfl⟩ := sharedSite (same i j hi hj)
  have codeA := singletonCode A s hi (fun i hi => by
    obtain ⟨t,hit,ht⟩ := sharedSite (same i (some s) hi hj)
    exact hit.trans (congrArg some (Option.some.inj ht).symm))
  have codeB := singletonCode B s hj (fun j hj => by
    obtain ⟨t,ht,hjt⟩ := sharedSite (same (some s) j hi hj)
    exact hjt.trans (congrArg some (Option.some.inj ht).symm))
  apply different s
  constructor
  · exact LinearMap.ext (fun x => by simpa [codeA, coordinateExtra, al] using hu (x,0))
  · exact LinearMap.ext (fun x => by simpa [codeB, coordinateExtra, br] using hv (x,0))

end PEqualNP.Outside.L_lib_1063

namespace PEqualNP.Outside.L_lib_1063

private theorem incompleteMatchingBound {m X Y : Type*} [DecidableEq m]
    [AddCommGroup X] [Module (ZMod 2) X] [AddCommGroup Y] [Module (ZMod 2) Y]
    [Finite X] [Finite Y]
    (a : m → X →ₗ[ZMod 2] ZMod 2) (b : m → Y →ₗ[ZMod 2] ZMod 2) (S : Finset m)
    (ha : LinearIndependent (ZMod 2) (fun i : S => a i.val))
    (hb : LinearIndependent (ZMod 2) (fun i : S => b i.val))
    (np : ¬ ∀ i, a i = 0 ∨ b i = 0 ∨ ∃ s ∈ S, a i = a s ∧ b i = b s) :
    9 * 4^S.card * Nat.card {w : X × Y // ∀ i, a i w.1 * b i w.2 = 0} ≤
      8 * 3^S.card * (Nat.card X * Nat.card Y) := by
  classical
  obtain ⟨t, ht⟩ := Classical.not_forall.mp np
  have un : a t ≠ 0 := fun h => ht (Or.inl h)
  have vn : b t ≠ 0 := fun h => ht (Or.inr (Or.inl h))
  have diff (s : S) : ¬ (a t = a s.val ∧ b t = b s.val) :=
    fun h => ht (Or.inr (Or.inr ⟨s.val, s.property, h⟩))
  let α := fun s : S => a s.val
  let β := fun s : S => b s.val
  obtain ⟨L,A,hL,al,hu⟩ := extraCoordinates α ha (a t)
  obtain ⟨R,B,hR,br,hv⟩ := extraCoordinates β hb (b t)
  obtain ⟨i,j,hi,hj,hne⟩ := choosePivots α β (a t) (b t) L R A B al br hu hv un vn diff
  have gap := transferGap α β (a t) (b t) L R A B hL hR al br hu hv i j hi hj hne
  let P (w : X × Y) := ∀ s, α s w.1 * β s w.2 = 0
  let All (w : X × Y) := ∀ k, a k w.1 * b k w.2 = 0
  have inc (w : X × Y) (hw : All w) : P w ∧ a t w.1 * b t w.2 = 0 :=
    ⟨fun s => hw s.val, hw t⟩
  have sub : Nat.card {w // All w} ≤ Nat.card {w // P w ∧ a t w.1 * b t w.2 = 0} :=
    Nat.card_le_card_of_injective (fun w => ⟨w.val, inc w.val w.property⟩)
      (fun _ _ e => Subtype.ext (congrArg (fun z : {w // P w ∧ a t w.1 * b t w.2 = 0} => z.val) e))
  have scaled := Nat.mul_le_mul_left (4^S.card) ((Nat.mul_le_mul_left 9 sub).trans gap)
  have exactCount : 4^S.card * Nat.card {w // P w} = 3^S.card * (Nat.card X * Nat.card Y) := by
    simpa [P, α, β] using matchingCard α β ha hb
  calc
    9 * 4^S.card * Nat.card {w // All w} = 4^S.card * (9 * Nat.card {w // All w}) := by ring
    _ ≤ 4^S.card * (8 * Nat.card {w // P w}) := scaled
    _ = 8 * (4^S.card * Nat.card {w // P w}) := by ring
    _ = 8 * 3^S.card * (Nat.card X * Nat.card Y) := by rw [exactCount]; ring

end PEqualNP.Outside.L_lib_1063

open PEqualNP.Outside.L_lib_1063 in
theorem PEqualNP.Outside.L_lib_1063 : (∀ l r m : ℕ,
  let F := ZMod 2
  let X := Fin l → F
  let Y := Fin r → F
  ∀ (a : Fin m → X →ₗ[F] F) (b : Fin m → Y →ₗ[F] F) (S : Finset (Fin m)),
    LinearIndependent F (fun i : S => a i.val) → LinearIndependent F (fun i : S => b i.val) →
    let pure := ∀ i, a i = 0 ∨ b i = 0 ∨ ∃ s ∈ S, a i = a s ∧ b i = b s
    let hits := Nat.card {w : X × Y // ∀ i, a i w.1 * b i w.2 = 0}
    let allPairs := Nat.card X * Nat.card Y
    (4^S.card*hits = 3^S.card*allPairs ↔ pure) ∧
      (¬ pure → 9*4^S.card*hits ≤ 8*3^S.card*allPairs)) := by
  intro l r m
  dsimp only
  intro a b S ha hb
  have gap := incompleteMatchingBound a b S ha hb
  refine ⟨⟨?_, pureCount a b S ha hb⟩, gap⟩
  intro eq
  by_contra h
  have bound := gap h
  rw [Nat.mul_assoc, eq, Nat.mul_assoc 8] at bound
  have pos : 0 < 3 ^ S.card * (Nat.card (Fin l → ZMod 2) * Nat.card (Fin r → ZMod 2)) :=
    Nat.mul_pos (by positivity) (Nat.mul_pos Nat.card_pos Nat.card_pos)
  omega
