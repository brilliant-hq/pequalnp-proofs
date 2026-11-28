import PEqualNP.Defs
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.LinearMap
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.ZMod.Basic

open scoped BigOperators

namespace PEqualNP.Outside.L_meta_33652

section Linear

variable {K : Type} [Field K]
variable {S U V Y : Type}
variable [AddCommGroup S] [Module K S] [FiniteDimensional K S]
variable [AddCommGroup U] [Module K U] [FiniteDimensional K U]
variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y]

theorem left_section (f : U →ₗ[K] V) (hf : Function.Injective f) :
    ∃ s : V →ₗ[K] U, ∀ x, s (f x) = x := by
  obtain ⟨s,hs⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hf)
  exact ⟨s,fun x => LinearMap.congr_fun hs x⟩

theorem right_section (f : U →ₗ[K] V) (hf : Function.Surjective f) :
    ∃ s : V →ₗ[K] U, ∀ y, f (s y) = y := by
  obtain ⟨s,hs⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hf)
  exact ⟨s,fun y => LinearMap.congr_fun hs y⟩

theorem onto_of_dim (h : Module.finrank K V ≤ Module.finrank K U) :
    ∃ f : U →ₗ[K] V, Function.Surjective f := by
  obtain ⟨j,hj⟩ := (finrank_le_iff_exists_linearMap (R := K)).mp h
  obtain ⟨f,hf⟩ := left_section j hj
  exact ⟨f,fun v => ⟨j v,hf v⟩⟩

theorem injective_lift (f : V →ₗ[K] Y) (g : U →ₗ[K] Y)
    (hf : Function.Surjective f) (bound : Module.finrank K g.ker ≤ Module.finrank K f.ker) :
    ∃ lift : U →ₗ[K] V, Function.Injective lift ∧ ∀ u, f (lift u) = g u := by
  obtain ⟨s,hs⟩ := right_section f hf
  obtain ⟨p,hp⟩ := left_section g.ker.subtype Subtype.val_injective
  obtain ⟨j,hj⟩ := (finrank_le_iff_exists_linearMap (R := K)).mp bound
  let lift := s.comp g + f.ker.subtype.comp (j.comp p)
  have eq (u : U) : f (lift u) = g u := by
    change f (s (g u) + (j (p u)).val) = g u
    rw [map_add,hs,LinearMap.mem_ker.mp (j (p u)).property,add_zero]
  refine ⟨lift,?_ ,eq⟩
  apply (LinearMap.ker_eq_bot).mp
  rw [Submodule.eq_bot_iff]
  intro u hu
  have zero := LinearMap.mem_ker.mp hu
  have gzero : g u = 0 := by rw [← eq,zero,map_zero]
  let z : g.ker := ⟨u,LinearMap.mem_ker.mpr gzero⟩
  have pz : p u = z := hp z
  change s (g u) + (j (p u)).val = 0 at zero
  rw [gzero,map_zero,zero_add,pz] at zero
  have zj : j z = 0 := Subtype.ext zero
  have zz : z = 0 := hj (by simpa using zj)
  exact congrArg Subtype.val zz

theorem quotient_zero (P : Submodule K V) (x : V) : P.mkQ x = 0 ↔ x ∈ P := by
  rw [← LinearMap.mem_ker,Submodule.ker_mkQ]

theorem map_on_quotient (f : V →ₗ[K] Y) (P : Submodule K V) (Q : Submodule K Y)
    (hf : ∀ x ∈ P, f x ∈ Q) :
    ∃ g : V ⧸ P →ₗ[K] Y ⧸ Q, ∀ x, g (P.mkQ x) = Q.mkQ (f x) := by
  let g := P.liftQ (Q.mkQ.comp f) (by
    intro x hx
    exact LinearMap.mem_ker.mpr ((quotient_zero _ _).mpr (hf x hx)))
  exact ⟨g,fun x => rfl⟩

theorem extend_onto (i : S →ₗ[K] V) (f : S →ₗ[K] Y)
    (hi : Function.Injective i)
    (bound : Module.finrank K S + Module.finrank K Y ≤ Module.finrank K V + Module.finrank K f.range) :
    ∃ g : V →ₗ[K] Y, Function.Surjective g ∧ ∀ x, g (i x) = f x := by
  obtain ⟨p,hp⟩ := left_section i hi
  let q := f.range.mkQ
  let J := f.range
  have pSurj : Function.Surjective p := fun x => ⟨i x,hp x⟩
  have rp : Module.finrank K p.range = Module.finrank K S := by
    rw [LinearMap.range_eq_top.mpr pSurj,finrank_top]
  have pk : Module.finrank K S + Module.finrank K p.ker = Module.finrank K V := by
    simpa only [rp] using p.finrank_range_add_finrank_ker
  have yq : Module.finrank K (Y ⧸ J)+Module.finrank K f.range = Module.finrank K Y :=
    J.finrank_quotient_add_finrank
  have space : Module.finrank K (Y ⧸ J) ≤ Module.finrank K p.ker := by omega
  obtain ⟨h,hh⟩ := onto_of_dim (K := K) space
  obtain ⟨s,hs⟩ := right_section q J.mkQ_surjective
  let rem := LinearMap.id - i.comp p
  have hrem (x : V) : rem x ∈ p.ker := by
    apply LinearMap.mem_ker.mpr
    change p (x-i (p x)) = 0
    rw [map_sub,hp,sub_self]
  let T : V →ₗ[K] p.ker := rem.codRestrict p.ker hrem
  let g := f.comp p + s.comp (h.comp T)
  have iT (x : S) : T (i x) = 0 := by
    apply Subtype.ext
    change i x-i (p (i x)) = 0
    rw [hp,sub_self]
  have bound_g (x : S) : g (i x) = f x := by
    change f (p (i x)) + s (h (T (i x))) = f x
    rw [hp,iT,map_zero,map_zero,add_zero]
  refine ⟨g,?_ ,bound_g⟩
  intro y
  obtain ⟨v,hv⟩ := hh (q y)
  have p0 := LinearMap.mem_ker.mp v.property
  have same : T v.val = v := by
    apply Subtype.ext
    change v.val - i (p v.val) = v.val
    simp [p0]
  have gV : g v.val = s (q y) := by
    change f (p v.val) + s (h (T v.val)) = _
    simp [p0,same,hv]
  have mem : y-s (q y) ∈ J := by
    apply (quotient_zero _ _).mp
    change q (y-s (q y)) = 0
    rw [map_sub,hs,sub_self]
  obtain ⟨x,hx⟩ := mem
  refine ⟨i x+v.val,?_⟩
  rw [map_add,bound_g,gV,hx,sub_add_cancel]


end Linear

section Relative

variable {K : Type} [Field K]
variable {S U V Y : Type}
variable [AddCommGroup S] [Module K S] [FiniteDimensional K S]
variable [AddCommGroup U] [Module K U] [FiniteDimensional K U]
variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y]

theorem quotient_range_dim (A : S →ₗ[K] Y) (B : U →ₗ[K] Y) :
    Module.finrank K (A.range.mkQ.comp B).range + Module.finrank K A.range =
      Module.finrank K (A.coprod B).range := by
  let M := A.coprod B
  let R := A.range
  have le : R ≤ M.range := by
    intro y hy
    obtain ⟨x,hx⟩ := hy
    exact ⟨(x,0),by simpa [M,LinearMap.coprod_apply] using hx⟩
  let q := R.mkQ.comp M.range.subtype
  have range_eq : q.range = (R.mkQ.comp B).range := by
    ext y
    constructor
    · rintro ⟨z,rfl⟩
      obtain ⟨⟨s,u⟩,h⟩ := z.property
      have hA : R.mkQ (A s) = 0 := (quotient_zero _ _).mpr ⟨s,rfl⟩
      refine ⟨u,?_⟩
      change R.mkQ (B u) = R.mkQ z.val
      rw [← h]
      change R.mkQ (B u) = R.mkQ (A s+B u)
      rw [map_add,hA,zero_add]
    · rintro ⟨u,rfl⟩
      refine ⟨⟨B u,⟨(0,u),by simp [M,LinearMap.coprod_apply]⟩⟩,rfl⟩
  let into : R →ₗ[K] q.ker :=
    (Submodule.inclusion le).codRestrict _ (fun x =>
      LinearMap.mem_ker.mpr ((quotient_zero _ _).mpr x.property))
  have injective : Function.Injective into := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : q.ker => z.val.val) h)
  have surj : Function.Surjective into := by
    intro x
    have h : x.val.val ∈ R := (quotient_zero _ _).mp (LinearMap.mem_ker.mp x.property)
    exact ⟨⟨x.val.val,h⟩,Subtype.ext (Subtype.ext rfl)⟩
  have dim_ker := (LinearEquiv.ofBijective into ⟨injective,surj⟩).finrank_eq
  have dims := q.finrank_range_add_finrank_ker
  rw [range_eq,← dim_ker] at dims
  exact dims

theorem relative_lift (i : S →ₗ[K] V) (f : V →ₗ[K] Y) (B : U →ₗ[K] Y)
    (hi : Function.Injective i) (hf : Function.Surjective f)
    (bound : Module.finrank K S + Module.finrank K U + Module.finrank K Y ≤
      Module.finrank K V + Module.finrank K ((f.comp i).coprod B).range) :
    ∃ e : (S × U) →ₗ[K] V, Function.Injective e ∧
      (∀ s, e (s,0) = i s) ∧ ∀ s u, f (e (s,u)) = f (i s)+B u := by
  let A := f.comp i
  let T := i.range
  let R := A.range
  let g := R.mkQ.comp B
  obtain ⟨F,hF⟩ := map_on_quotient f T R (by
    rintro x ⟨s,rfl⟩
    exact ⟨s,rfl⟩)
  have Fsurj : Function.Surjective F := by
    intro y
    obtain ⟨z,rfl⟩ := R.mkQ_surjective y
    obtain ⟨x,rfl⟩ := hf z
    exact ⟨T.mkQ x,hF x⟩
  have Fdim : Module.finrank K F.range = Module.finrank K (Y ⧸ R) := by
    rw [LinearMap.range_eq_top.mpr Fsurj,finrank_top]
  have Fker := F.finrank_range_add_finrank_ker
  rw [Fdim] at Fker
  have gker := g.finrank_range_add_finrank_ker
  have qdim := quotient_range_dim A B
  change Module.finrank K g.range + Module.finrank K R = Module.finrank K (A.coprod B).range at qdim
  have Tdim := LinearMap.finrank_range_of_inj hi
  change Module.finrank K T = Module.finrank K S at Tdim
  have Td := T.finrank_quotient_add_finrank
  have Rd := R.finrank_quotient_add_finrank
  change Module.finrank K S + Module.finrank K U + Module.finrank K Y ≤ Module.finrank K V + Module.finrank K (A.coprod B).range at bound
  have enough : Module.finrank K g.ker ≤ Module.finrank K F.ker := by omega
  obtain ⟨l,hl,lifts⟩ := injective_lift F g Fsurj enough
  obtain ⟨p,hp⟩ := right_section T.mkQ T.mkQ_surjective
  obtain ⟨s,hs⟩ := right_section A.rangeRestrict A.surjective_rangeRestrict
  let diff := f.comp (p.comp l) - B
  have inR (u : U) : diff u ∈ R := by
    apply (quotient_zero _ _).mp
    change R.mkQ (f (p (l u))-B u) = 0
    rw [map_sub,← hF,hp,lifts]
    exact sub_self (R.mkQ (B u))
  let L := p.comp l - i.comp (s.comp (diff.codRestrict R inR))
  have fixed_f (u : U) : f (L u) = B u := by
    let r : R := ⟨diff u,inR u⟩
    have e := congrArg Subtype.val (hs r)
    change f (i (s r)) = f (p (l u))-B u at e
    change f (p (l u)-i (s r)) = B u
    rw [map_sub,e,sub_sub_cancel]
  have fixed_q (u : U) : T.mkQ (L u) = l u := by
    let r : R := ⟨diff u,inR u⟩
    have kill : T.mkQ (i (s r)) = 0 := (quotient_zero _ _).mpr ⟨_,rfl⟩
    change T.mkQ (p (l u)-i (s r)) = l u
    rw [map_sub,hp,kill,sub_zero]
  let e := i.coprod L
  have es (x : S) : e (x,0) = i x := by simp [e,LinearMap.coprod_apply]
  have ef (x : S) (y : U) : f (e (x,y)) = f (i x)+B y := by
    change f (i x+L y) = _
    rw [map_add,fixed_f]
  refine ⟨e,?_ ,es,ef⟩
  apply (LinearMap.ker_eq_bot).mp
  rw [Submodule.eq_bot_iff]
  rintro ⟨x,y⟩ h
  have zero := LinearMap.mem_ker.mp h
  change i x+L y = 0 at zero
  have image := congrArg T.mkQ zero
  have kill : T.mkQ (i x) = 0 := (quotient_zero _ _).mpr ⟨x,rfl⟩
  rw [map_add,kill,zero_add,fixed_q,map_zero] at image
  have yy : y = 0 := hl (by simpa using image)
  have xx : x = 0 := hi (by simpa [yy] using zero)
  simp [xx,yy]

end Relative

section Pad

variable {K : Type} [Field K] {n m : ℕ}
variable {U V : Type} [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]

abbrev RowSpace (K : Type) (m : ℕ) := Fin m → K

def zeroOutside (J : Finset (Fin m)) : RowSpace K m →ₗ[K] RowSpace K m :=
  LinearMap.pi fun y => if y ∈ J then LinearMap.proj y else 0

def readColumns (J : Finset (Fin m)) : RowSpace K m →ₗ[K] (J → K) :=
  LinearMap.pi fun y => LinearMap.proj y.val

def padColumns (J : Finset (Fin m)) : (J → K) →ₗ[K] RowSpace K m :=
  LinearMap.pi fun y => if h : y ∈ J then LinearMap.proj ⟨y,h⟩ else 0

theorem zeroOutside_apply (J : Finset (Fin m)) (z : RowSpace K m) (y : Fin m) :
    zeroOutside J z y = if y ∈ J then z y else 0 := by
  unfold zeroOutside
  rw [LinearMap.pi_apply]
  split <;> rfl

theorem zeroOutside_comp (I J : Finset (Fin m)) (h : I ⊆ J) :
    (zeroOutside I : RowSpace K m →ₗ[K] _).comp (zeroOutside J) = zeroOutside I := by
  apply LinearMap.ext
  intro z
  funext y
  simp only [LinearMap.comp_apply,zeroOutside_apply]
  by_cases hy : y ∈ I
  · simp [hy, h hy]
  · simp [hy]

theorem read_pad (J : Finset (Fin m)) (z : J → K) : readColumns J (padColumns J z) = z := by
  funext y
  change (padColumns J z) y.val = z y
  simp [padColumns, y.property]

theorem pad_injective (J : Finset (Fin m)) : Function.Injective (padColumns (K := K) J) :=
  Function.LeftInverse.injective (read_pad J)

theorem pad_read (J : Finset (Fin m)) (z : RowSpace K m) :
    padColumns J (readColumns J z) = zeroOutside J z := by
  funext y
  simp only [padColumns,LinearMap.pi_apply,zeroOutside_apply]
  split <;> rfl

def rowSpan (M : Matrix (Fin n) (Fin m) K) (I : Finset (Fin n)) : Submodule K (RowSpace K m) :=
  Submodule.span K (Set.range (fun x : I => M x.val))

def maskedSpan (M : Matrix (Fin n) (Fin m) K) (I : Finset (Fin n)) (J : Finset (Fin m)) :
    Submodule K (RowSpace K m) :=
  (rowSpan M I).map (zeroOutside J)

noncomputable def blockRank (M : Matrix (Fin n) (Fin m) K) (I : Finset (Fin n)) (J : Finset (Fin m)) : ℕ :=
  Matrix.rank (M.submatrix (fun x : I => x.val) (fun y : J => y.val))

theorem mem_maskedSpan (M : Matrix (Fin n) (Fin m) K) (I : Finset (Fin n))
    (J : Finset (Fin m)) {x : Fin n} (hx : x ∈ I) :
    zeroOutside J (M x) ∈ maskedSpan M I J := by
  exact ⟨M x,Submodule.subset_span ⟨⟨x,hx⟩,rfl⟩,rfl⟩

theorem rowSpan_map (M : Matrix (Fin n) (Fin m) K) (I : Finset (Fin n))
    (J : Finset (Fin m)) :
    maskedSpan M I J = Submodule.span K (Set.range (fun x : I => zeroOutside J (M x.val))) := by
  rw [maskedSpan,rowSpan,Submodule.map_span,← Set.range_comp]
  rfl

theorem span_dimension (S : Submodule K U) (f : U →ₗ[K] V) (hf : Function.Injective f) :
    Module.finrank K (S.map f) = Module.finrank K S := by
  let g : S →ₗ[K] S.map f := (f.comp S.subtype).codRestrict _ (fun x => ⟨x.val,x.property,rfl⟩)
  have gi : Function.Injective g := by
    intro x y h
    exact Subtype.ext (hf (congrArg Subtype.val h))
  have gs : Function.Surjective g := by
    rintro ⟨v,hv⟩
    obtain ⟨u,hu,rfl⟩ := hv
    exact ⟨⟨u,hu⟩,rfl⟩
  exact (LinearEquiv.ofBijective g ⟨gi,gs⟩).finrank_eq.symm

theorem maskedSpan_rank (M : Matrix (Fin n) (Fin m) K) (I : Finset (Fin n)) (J : Finset (Fin m)) :
    Module.finrank K (maskedSpan M I J) = blockRank M I J := by
  let M' := M.submatrix (fun x : I => x.val) (fun y : J => y.val)
  have image : maskedSpan M I J = ((Submodule.span K (Set.range M'.row)).map (padColumns J)) := by
    rw [rowSpan_map,Submodule.map_span]
    apply congrArg (Submodule.span K)
    ext z
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨M'.row x,⟨x,rfl⟩,pad_read J (M x.val)⟩
    · rintro ⟨v,⟨x,rfl⟩,rfl⟩
      exact ⟨x,(pad_read J (M x.val)).symm⟩
  rw [image,span_dimension _ _ (pad_injective J),blockRank,Matrix.rank_eq_finrank_span_row]

theorem univ_blockRank (M : Matrix (Fin n) (Fin m) K) (I : Finset (Fin n)) :
    Module.finrank K (rowSpan M I) = blockRank M I Finset.univ := by
  rw [← maskedSpan_rank]
  unfold maskedSpan
  symm
  apply span_dimension
  intro x y he
  funext j
  have eq := congrFun he j
  simpa only [zeroOutside_apply,Finset.mem_univ,ite_true] using eq

theorem total_rank (M : Matrix (Fin n) (Fin m) K) :
    Matrix.rank M = Module.finrank K (rowSpan M Finset.univ) := by
  have seteq : Set.range M.row = Set.range (fun x : (Finset.univ : Finset (Fin n)) => M x.val) := by
    ext z
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨⟨i,Finset.mem_univ _⟩,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨i.val,rfl⟩
  rw [Matrix.rank_eq_finrank_span_row,rowSpan,seteq]

theorem mask_mono (M : Matrix (Fin n) (Fin m) K) {I I' : Finset (Fin n)}
    (h : I ⊆ I') (J : Finset (Fin m)) :
    maskedSpan M I J ≤ maskedSpan M I' J := by
  rw [rowSpan_map,rowSpan_map]
  apply Submodule.span_mono
  rintro _ ⟨x,rfl⟩
  exact ⟨⟨x.val,h x.property⟩,rfl⟩

theorem mask_span_further (M : Matrix (Fin n) (Fin m) K) (I : Finset (Fin n))
    {J J' : Finset (Fin m)} (h : J ⊆ J') :
    (maskedSpan M I J').map (zeroOutside J) = maskedSpan M I J := by
  rw [maskedSpan,← Submodule.map_comp,zeroOutside_comp J J' h,maskedSpan]

theorem mask_eq_if (M N : Matrix (Fin n) (Fin m) K) (I : Finset (Fin n))
    (J : Finset (Fin m)) (agree : ∀ x ∈ I, ∀ y ∈ J, M x y = N x y) :
    maskedSpan M I J = maskedSpan N I J := by
  rw [rowSpan_map,rowSpan_map]
  congr 1
  apply congrArg Set.range
  funext x y
  simp only [zeroOutside_apply]
  split
  · exact agree x.val x.property y (by assumption)
  · rfl

theorem rank_codRestrict (f : U →ₗ[K] V) (T : Submodule K V)
    (h : ∀ x, f x ∈ T) :
    Module.finrank K (f.codRestrict T h).range = Module.finrank K f.range := by
  let L := f.codRestrict T h
  have comp : T.subtype.comp L = f := rfl
  have image : L.range.map T.subtype = f.range := by
    rw [← LinearMap.range_comp,comp]
  exact (span_dimension L.range T.subtype Subtype.val_injective).symm.trans
    (congrArg (fun (s : Submodule K V) => Module.finrank K s) image)

end Pad

section AttachBag

variable {K : Type} [Field K]
variable {S H V W : Type}
variable [AddCommGroup S] [Module K S] [FiniteDimensional K S]
variable [AddCommGroup H] [Module K H] [FiniteDimensional K H]
variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable [AddCommGroup W] [Module K W] [FiniteDimensional K W]

theorem extend_embedding {U : Type} [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (i : S →ₗ[K] V) (hi : Function.Injective i)
    (bound : Module.finrank K S + Module.finrank K U ≤ Module.finrank K V) :
    ∃ e : (S×U) →ₗ[K] V, Function.Injective e ∧ ∀ s, e (s,0) = i s := by
  obtain ⟨p,hp⟩ := left_section i hi
  have surj : Function.Surjective p := fun s => ⟨i s,hp s⟩
  have dims := p.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr surj,finrank_top] at dims
  have enough : Module.finrank K U ≤ Module.finrank K p.ker := by omega
  obtain ⟨j,hj⟩ := (finrank_le_iff_exists_linearMap (R := K)).mp enough
  let e := i.coprod (p.ker.subtype.comp j)
  have known (s : S) : e (s,0) = i s := by simp [e,LinearMap.coprod_apply]
  refine ⟨e,?_ ,known⟩
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  rintro ⟨s,u⟩ h
  have z := LinearMap.mem_ker.mp h
  change i s+(j u).val=0 at z
  have first := congrArg p z
  rw [map_add,hp,LinearMap.mem_ker.mp (j u).property,add_zero,map_zero] at first
  rw [first,map_zero,zero_add] at z
  have second : u=0 := hj (by simpa using (Subtype.ext z : j u = 0))
  simp [first,second]

theorem attach_bag {I : Type} [DecidableEq I]
    (U : I → Submodule K W) (current members : Finset I)
    (embed : S →ₗ[K] V) (inj : Function.Injective embed)
    (base : ∀ i, S →ₗ[K] U i)
    (before : ∀ i, V →ₗ[K] U i)
    (before_base : ∀ i s, before i (embed s) = base i s)
    (before_onto : ∀ i ∈ current, Function.Surjective (before i))
    (observe : S →ₗ[K] H)
    (project : ∀ i ∈ members, H →ₗ[K] U i)
    (consistent : ∀ i (hi : i ∈ members) s, project i hi (observe s) = base i s)
    (small : (members ∩ current).card ≤ 1)
    (budget : ∀ i (hi : i ∈ members),
      Module.finrank K S + Module.finrank K H + Module.finrank K (U i) ≤
        Module.finrank K V + Module.finrank K observe.range +
          Module.finrank K (project i hi).range) :
    ∃ after : ∀ i, V →ₗ[K] U i,
      (∀ i ∈ current, after i = before i) ∧
      (∀ i s, after i (embed s) = base i s) ∧
      (∀ i ∈ current ∪ members, Function.Surjective (after i)) ∧
      ∀ x : H, ∃ z : V, ∀ i (hi : i ∈ members), after i z = project i hi x := by
  classical
  by_cases empty : members = ∅
  · subst members
    exact ⟨before,fun _ _ => rfl,before_base,by simpa using before_onto,
      fun _ => ⟨0,by simp⟩⟩
  let R := observe.range
  let T := H ⧸ R
  obtain ⟨s,hs⟩ := right_section R.mkQ R.mkQ_surjective
  let J : (S×T) →ₗ[K] H := observe.coprod s
  have J_surj : Function.Surjective J := by
    intro x
    let t := R.mkQ x
    have mem : x-s t ∈ R := by
      apply (quotient_zero _ _).mp
      rw [map_sub,hs,sub_self]
    obtain ⟨a,ha⟩ := mem
    refine ⟨(a,t),?_⟩
    change observe a+s t=x
    rw [ha,sub_add_cancel]
  have J_base (x : S) : J (x,0) = observe x := by simp [J,LinearMap.coprod_apply]
  have Jdim := R.finrank_quotient_add_finrank
  have ranges (i : I) (hi : i ∈ members) : ((project i hi).comp J).range = (project i hi).range := by
    ext y
    constructor
    · rintro ⟨z,rfl⟩
      exact ⟨J z,rfl⟩
    · rintro ⟨z,rfl⟩
      obtain ⟨x,rfl⟩ := J_surj z
      exact ⟨x,rfl⟩
  have space (i : I) (hi : i ∈ members) :
      Module.finrank K S + Module.finrank K T + Module.finrank K (U i) ≤
        Module.finrank K V + Module.finrank K (project i hi).range := by
    have h := budget i hi
    change Module.finrank K T + Module.finrank K observe.range = Module.finrank K H at Jdim
    omega
  have lifts :
      ∃ L : (S×T) →ₗ[K] V, Function.Injective L ∧
        (∀ x, L (x,0) = embed x) ∧
        ∀ i (hi : i ∈ members), i ∈ current → ∀ z, before i (L z) = project i hi (J z) := by
    by_cases any : (members ∩ current).Nonempty
    · obtain ⟨i,hi⟩ := any
      have hm := (Finset.mem_inter.mp hi).1
      have ho := (Finset.mem_inter.mp hi).2
      let B := (project i hm).comp s
      have Smap : ((before i).comp embed).coprod B = (project i hm).comp J := by
        apply LinearMap.ext
        rintro ⟨x,t⟩
        change before i (embed x)+project i hm (s t)=project i hm (observe x+s t)
        rw [map_add,before_base,consistent]
      have enough : Module.finrank K S + Module.finrank K T + Module.finrank K (U i) ≤
          Module.finrank K V + Module.finrank K (((before i).comp embed).coprod B).range := by
        rw [Smap,ranges]
        exact space i hm
      obtain ⟨L,hL,baseL,liftL⟩ := relative_lift embed (before i) B inj (before_onto i ho) enough
      refine ⟨L,hL,baseL,?_⟩
      intro j hj hjo z
      have eq : j=i := Finset.card_le_one.mp small j (Finset.mem_inter.mpr ⟨hj,hjo⟩) i hi
      subst j
      rcases z with ⟨x,t⟩
      rw [liftL]
      exact LinearMap.congr_fun Smap (x,t)
    · obtain ⟨i,hi⟩ := Finset.nonempty_iff_ne_empty.mpr empty
      have bound := space i hi
      have rank_le := (project i hi).range.finrank_le
      have enough : Module.finrank K S + Module.finrank K T ≤ Module.finrank K V := by omega
      obtain ⟨L,hL,baseL⟩ := extend_embedding embed inj enough
      exact ⟨L,hL,baseL,fun i hm ho => (any ⟨i,Finset.mem_inter.mpr ⟨hm,ho⟩⟩).elim⟩
  obtain ⟨L,hL,baseL,liftL⟩ := lifts
  have new (i : I) (hi : i ∈ members) :
      ∃ f : V →ₗ[K] U i, Function.Surjective f ∧
        ∀ z, f (L z) = project i hi (J z) := by
    apply extend_onto L ((project i hi).comp J) hL
    rw [ranges,Module.finrank_prod]
    exact space i hi
  let after (i : I) : V →ₗ[K] U i :=
    if h : i ∈ members ∧ i ∉ current then Classical.choose (new i h.1) else before i
  have unchanged (i : I) (hi : i ∈ current) : after i = before i := by simp [after,hi]
  have match_bag (i : I) (hi : i ∈ members) (z : S×T) :
      after i (L z) = project i hi (J z) := by
    by_cases old : i ∈ current
    · rw [unchanged i old]
      exact liftL i hi old z
    · have h : i ∈ members ∧ i ∉ current := ⟨hi,old⟩
      simp only [after,dite_eq_left h]
      exact (Classical.choose_spec (new i hi)).2 z
  refine ⟨after,unchanged,?_ ,?_ ,?_⟩
  · intro i x
    by_cases hi : i ∈ members
    · rw [← baseL x, match_bag i hi, J_base, consistent]
    · simpa [after,hi] using before_base i x
  · intro i hi
    by_cases old : i ∈ current
    · rw [unchanged i old]
      exact before_onto i old
    · have hm := (Finset.mem_union.mp hi).resolve_left old
      have h : i ∈ members ∧ i ∉ current := ⟨hm,old⟩
      simp only [after,dite_eq_left h]
      exact (Classical.choose_spec (new i hm)).1
  · intro x
    obtain ⟨z,eq⟩ := J_surj x
    exact ⟨L z, fun i hi => (match_bag i hi z).trans (congrArg (project i hi) eq)⟩

end AttachBag

section Assemble

variable {K : Type} [Field K]
variable {S V W : Type}
variable [AddCommGroup S] [Module K S] [FiniteDimensional K S]
variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable [AddCommGroup W] [Module K W] [FiniteDimensional K W]
variable {a b : ℕ}

def pastGroups (bags : Fin a → Finset (Fin b)) (w : ℕ) : Finset (Fin b) :=
  ((Finset.univ.filter fun i : Fin a => i.val < w).biUnion bags)

theorem pastGroups_step (bags : Fin a → Finset (Fin b)) (w : ℕ) (hw : w < a) :
    pastGroups bags (w+1) = pastGroups bags w ∪ bags ⟨w,hw⟩ := by
  ext v
  simp only [pastGroups,Finset.mem_biUnion,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union]
  constructor
  · rintro ⟨i,hi,hv⟩
    by_cases hh : i.val < w
    · exact Or.inl ⟨i,hh,hv⟩
    · have eq : i = ⟨w,hw⟩ := Fin.ext (show i.val = w by omega)
      exact Or.inr (eq ▸ hv)
  · rintro (⟨i,hi,hv⟩ | hv)
    · exact ⟨i,by omega,hv⟩
    · exact ⟨⟨w,hw⟩,Nat.lt_succ_self _,hv⟩

theorem forest_maps (bags : Fin a → Finset (Fin b))
    (forest : ∀ i : Fin a, (bags i ∩ pastGroups bags i.val).card ≤ 1)
    (U : Fin b → Submodule K W) (H : Fin a → Submodule K W)
    (embed : S →ₗ[K] V) (inj : Function.Injective embed)
    (base : ∀ v, S →ₗ[K] U v) (observe : ∀ i, S →ₗ[K] H i)
    (project : ∀ i v, v ∈ bags i → H i →ₗ[K] U v)
    (consistent : ∀ i v (hv : v ∈ bags i) x, project i v hv (observe i x) = base v x)
    (budget : ∀ i v (hv : v ∈ bags i),
      Module.finrank K S + Module.finrank K (H i) + Module.finrank K (U v) ≤
        Module.finrank K V + Module.finrank K (observe i).range +
          Module.finrank K (project i v hv).range) :
    ∃ maps : ∀ v, V →ₗ[K] U v,
      (∀ v x, maps v (embed x) = base v x) ∧
      ∀ i (h : H i), ∃ x : V, ∀ v (hv : v ∈ bags i), maps v x = project i v hv h := by
  obtain ⟨left,hleft⟩ := left_section embed inj
  have accumulated (w : ℕ) (hw : w ≤ a) :
      ∃ maps : ∀ v, V →ₗ[K] U v,
        (∀ v x, maps v (embed x) = base v x) ∧
        (∀ v ∈ pastGroups bags w, Function.Surjective (maps v)) ∧
        ∀ i : Fin a, i.val < w → ∀ h : H i,
          ∃ x : V, ∀ v (hv : v ∈ bags i), maps v x = project i v hv h := by
    induction w with
    | zero =>
      exact ⟨fun v => (base v).comp left,
        fun v x => congrArg (base v) (hleft x),by simp [pastGroups],by simp⟩
    | succ w ih =>
      have lt : w < a := by omega
      let i : Fin a := ⟨w,lt⟩
      obtain ⟨before,hbase,honto,hcover⟩ := ih (by omega)
      obtain ⟨after,keep,abase,aonto,cover⟩ := attach_bag U (pastGroups bags w) (bags i)
        embed inj base before hbase honto (observe i) (project i) (consistent i) (forest i) (budget i)
      refine ⟨after,abase,?_,?_⟩
      · rw [pastGroups_step bags w lt]
        exact aonto
      · intro j hj t
        by_cases eq : j = i
        · subst j
          exact cover t
        · have earlier : j.val < w := by
            by_contra! no
            have same : j.val = w := by omega
            exact eq (Fin.ext same)
          obtain ⟨z,hz⟩ := hcover j earlier t
          refine ⟨z,fun v hv => ?_⟩
          have entered : v ∈ pastGroups bags w := by
            apply Finset.mem_biUnion.mpr
            exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,earlier⟩,hv⟩
          rw [keep v entered]
          exact hz v hv
  obtain ⟨maps,hbase,honto,hcover⟩ := accumulated a le_rfl
  exact ⟨maps,hbase,fun i => hcover i i.isLt⟩

end Assemble

section MatrixForest

variable {K : Type} [Field K] {n m a b : ℕ}

def shared (row : Fin n → Option (Fin a)) : Finset (Fin n) :=
  Finset.univ.filter (fun x => row x = none)

def panelRows (row : Fin n → Option (Fin a)) (i : Fin a) : Finset (Fin n) :=
  shared row ∪ Finset.univ.filter (fun x => row x = some i)

def panelColumns (col : Fin m → Fin b) (bag : Finset (Fin b)) : Finset (Fin m) :=
  Finset.univ.filter (fun y => col y ∈ bag)

def groupColumns (col : Fin m → Fin b) (v : Fin b) : Finset (Fin m) :=
  Finset.univ.filter (fun y => col y = v)

theorem group_le_panel (col : Fin m → Fin b) (bag : Finset (Fin b))
    {v : Fin b} (hv : v ∈ bag) : groupColumns col v ⊆ panelColumns col bag := by
  intro y hy
  have eq := (Finset.mem_filter.mp hy).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rwa [eq]⟩

theorem range_on_submodule {V Y : Type} [AddCommGroup V] [Module K V] [AddCommGroup Y]
    [Module K Y] (f : V →ₗ[K] Y) (S : Submodule K V) :
    (f.comp S.subtype).range = S.map f := by
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨x.val,x.property,rfl⟩
  · rintro ⟨x,hx,rfl⟩
    exact ⟨⟨x,hx⟩,rfl⟩

theorem forest_complete (r : ℕ)
    (row : Fin n → Option (Fin a)) (col : Fin m → Fin b) (bags : Fin a → Finset (Fin b))
    (forest : ∀ i, (bags i ∩ pastGroups bags i.val).card ≤ 1)
    (A : Matrix (Fin n) (Fin m) K) (B : Fin a → Matrix (Fin n) (Fin m) K)
    (same : ∀ i x, x ∈ shared row → ∀ y, B i x y = A x y)
    (U : Fin b → Submodule K (RowSpace K m))
    (baseBound : blockRank A (shared row) Finset.univ ≤ r)
    (baseObserved : ∀ v x, x ∈ shared row → zeroOutside (groupColumns col v) (A x) ∈ U v)
    (panelObserved : ∀ i v, v ∈ bags i → ∀ x, x ∈ panelRows row i →
       zeroOutside (groupColumns col v) (B i x) ∈ U v)
    (localBound : ∀ i v, v ∈ bags i →
      blockRank A (shared row) Finset.univ +
      blockRank (B i) (panelRows row i) (panelColumns col (bags i)) +
      Module.finrank K (U v) ≤
      r + blockRank A (shared row) (panelColumns col (bags i)) +
      blockRank (B i) (panelRows row i) (groupColumns col v)) :
    ∃ G : Matrix (Fin n) (Fin m) K, Matrix.rank G ≤ r ∧
      (∀ x, row x = none → ∀ y, G x y = A x y) ∧
      ∀ i x, row x = some i → ∀ y ∈ panelColumns col (bags i), G x y = B i x y := by
  classical
  let V := Fin r → K
  let R := shared row
  let S := rowSpan A R
  let H (i : Fin a) := maskedSpan (B i) (panelRows row i) (panelColumns col (bags i))
  have Vdim : Module.finrank K V = r := by
    simp [V,Module.finrank_pi_fintype]
  have Sdim : Module.finrank K S = blockRank A R Finset.univ := univ_blockRank A R
  have Ssmall : Module.finrank K S ≤ Module.finrank K V := by rw [Vdim,Sdim]; exact baseBound
  obtain ⟨embed,hinj⟩ := (finrank_le_iff_exists_linearMap (R := K)).mp Ssmall
  have baseMem (v : Fin b) (s : S) : zeroOutside (groupColumns col v) s.val ∈ U v := by
    have span : S ≤ (U v).comap (zeroOutside (groupColumns col v)) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨x,rfl⟩
      exact baseObserved v x.val x.property
    exact span s.property
  let base (v : Fin b) :=
    ((zeroOutside (groupColumns col v)).comp S.subtype).codRestrict (U v) (baseMem v)
  have obsMem (i : Fin a) (s : S) : zeroOutside (panelColumns col (bags i)) s.val ∈ H i := by
    have sub : maskedSpan A R (panelColumns col (bags i)) ≤ H i := by
      rw [← mask_eq_if (B i) A R (panelColumns col (bags i)) (fun x hx y _ => same i x hx y)]
      exact mask_mono (B i) (by exact Finset.subset_union_left) (panelColumns col (bags i))
    exact sub (Submodule.mem_map_of_mem s.property)
  let observe (i : Fin a) :=
    ((zeroOutside (panelColumns col (bags i))).comp S.subtype).codRestrict (H i) (obsMem i)
  have groupMem (i : Fin a) (v : Fin b) (hv : v ∈ bags i) (h : H i) :
      zeroOutside (groupColumns col v) h.val ∈ U v := by
    have sub : (H i).map (zeroOutside (groupColumns col v)) ≤ U v := by
      change (maskedSpan (B i) (panelRows row i) (panelColumns col (bags i))).map _ ≤ _
      rw [mask_span_further _ _ (group_le_panel col (bags i) hv),rowSpan_map]
      apply Submodule.span_le.mpr
      rintro _ ⟨x,rfl⟩
      exact panelObserved i v hv x.val x.property
    exact sub (Submodule.mem_map_of_mem h.property)
  let project (i : Fin a) (v : Fin b) (hv : v ∈ bags i) :=
    ((zeroOutside (groupColumns col v)).comp (H i).subtype).codRestrict (U v) (groupMem i v hv)
  have cons (i : Fin a) (v : Fin b) (hv : v ∈ bags i) (s : S) :
      project i v hv (observe i s) = base v s := by
    apply Subtype.ext
    exact LinearMap.congr_fun
      (zeroOutside_comp (K := K) (groupColumns col v) (panelColumns col (bags i))
        (group_le_panel col (bags i) hv)) s.val
  have obsDim (i : Fin a) :
      Module.finrank K (observe i).range = blockRank A R (panelColumns col (bags i)) := by
    calc
      _ = Module.finrank K ((zeroOutside (panelColumns col (bags i))).comp S.subtype).range :=
        rank_codRestrict _ _ (fun s => obsMem i s)
      _ = _ := by
        rw [range_on_submodule]
        exact maskedSpan_rank A R _
  have projDim (i : Fin a) (v : Fin b) (hv : v ∈ bags i) :
      Module.finrank K (project i v hv).range =
        blockRank (B i) (panelRows row i) (groupColumns col v) := by
    calc
      _ = Module.finrank K ((zeroOutside (groupColumns col v)).comp (H i).subtype).range :=
        rank_codRestrict _ _ (fun z => groupMem i v hv z)
      _ = _ := by
        rw [range_on_submodule]
        dsimp only [H]
        rw [mask_span_further _ _ (group_le_panel col (bags i) hv),maskedSpan_rank]
  have budget (i : Fin a) (v : Fin b) (hv : v ∈ bags i) :
      Module.finrank K S + Module.finrank K (H i) + Module.finrank K (U v) ≤
        Module.finrank K V + Module.finrank K (observe i).range +
          Module.finrank K (project i v hv).range := by
    rw [Sdim,Vdim,obsDim i,projDim i v hv]
    dsimp only [H]
    rw [maskedSpan_rank]
    exact localBound i v hv
  obtain ⟨maps,mapsBase,mapsPanel⟩ := forest_maps bags forest U H embed hinj base observe project cons budget
  let read : V →ₗ[K] RowSpace K m :=
    LinearMap.pi fun y => (LinearMap.proj y).comp ((U (col y)).subtype.comp (maps (col y)))
  have read_eval (z : V) (y : Fin m) : read z y = (maps (col y) z).val y := rfl
  have chooseRow (x : Fin n) : ∃ z : V,
      (row x = none → ∀ y, read z y = A x y) ∧
      (∀ i, row x = some i → ∀ y ∈ panelColumns col (bags i), read z y = B i x y) := by
    cases hx : row x with
    | none =>
      have hr : x ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩
      let s : S := ⟨A x,Submodule.subset_span ⟨⟨x,hr⟩,rfl⟩⟩
      refine ⟨embed s,?_ ,by simp⟩
      intro _ y
      rw [read_eval,mapsBase]
      change zeroOutside (groupColumns col (col y)) (A x) y = _
      simp [zeroOutside_apply,groupColumns]
    | some i =>
      have hr : x ∈ panelRows row i := Finset.mem_union.mpr
        (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩))
      let h : H i := ⟨zeroOutside (panelColumns col (bags i)) (B i x),mem_maskedSpan _ _ _ hr⟩
      obtain ⟨z,hz⟩ := mapsPanel i h
      refine ⟨z,by simp,?_⟩
      intro j eq y hy
      have ij : i = j := Option.some.inj eq
      subst j
      rw [read_eval,hz (col y) (Finset.mem_filter.mp hy).2]
      change zeroOutside (groupColumns col (col y))
        (zeroOutside (panelColumns col (bags i)) (B i x)) y = _
      simp [zeroOutside_apply,groupColumns,hy]
  let G : Matrix (Fin n) (Fin m) K := fun x => read (Classical.choose (chooseRow x))
  refine ⟨G,?_ ,fun x => (Classical.choose_spec (chooseRow x)).1,
    fun i x => (Classical.choose_spec (chooseRow x)).2 i⟩
  rw [total_rank,← Vdim]
  have h : rowSpan G Finset.univ ≤ read.range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x,rfl⟩
    exact ⟨Classical.choose (chooseRow x.val),rfl⟩
  exact (Submodule.finrank_mono h).trans read.finrank_range_le

end MatrixForest

open PEqualNP.CircuitLowerBounds

abbrev BitField := ZMod 2

def bitValue (b : Bool) : BitField := (b.toNat : BitField)

def bitOf (x : BitField) : Bool := decide (x ≠ 0)

theorem bitValue_of (x : BitField) : bitValue (bitOf x) = x := by fin_cases x <;> rfl

theorem bitOf_value (b : Bool) : bitOf (bitValue b) = b := by cases b <;> rfl

theorem bitValue_injective : Function.Injective bitValue := fun x y e => by
  simpa only [bitOf_value] using congrArg bitOf e

theorem two_bit : (2 : BitField) = 0 := by decide +kernel

theorem bit_add_self (x : BitField) : x+x=0 := by linear_combination x*two_bit

theorem bit_xor (x y : Bool) : bitValue (xor x y) = bitValue x+bitValue y := by
  cases x <;> cases y <;> decide +kernel

theorem bit_and (x y : Bool) : bitValue (x && y) = bitValue x*bitValue y := by
  cases x <;> cases y <;> decide +kernel

def nonlinear (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
    xor (xor (g.op.eval [false,false]) (g.op.eval [false,true]))
      (xor (g.op.eval [true,false]) (g.op.eval [true,true]))

def depthAppend (ds : List ℕ) (g : Gate) : List ℕ :=
  ds ++ [(g.inputs.map (fun h => ds.getD h 0)).foldr max 0+(nonlinear g).toNat]

def depth (w : ℕ) (C : Circuit) : ℕ :=
  ((C.gates.foldl depthAppend (List.replicate w 0)).getD C.output 0)

theorem unary_value (T : Bool → Bool) (x : Bool) :
    bitValue (T x) = bitValue (T false)+(bitValue (T false)+bitValue (T true))*bitValue x := by
  cases x <;> simp [bitValue,add_assoc,← add_assoc,bit_add_self]

def binaryCoefficient (T : Bool → Bool → Bool) : BitField :=
  (bitValue (T false false)+bitValue (T false true))+
    (bitValue (T true false)+bitValue (T true true))

theorem binary_value (T : Bool → Bool → Bool) (x y : Bool) :
    bitValue (T x y) = bitValue (T false false)+
      (bitValue (T true false)+bitValue (T false false))*bitValue x+
      (bitValue (T false true)+bitValue (T false false))*bitValue y+
      binaryCoefficient T*(bitValue x*bitValue y) := by
  cases x <;> cases y <;>
    cases e00 : T false false <;> cases e01 : T false true <;>
    cases e10 : T true false <;> cases e11 : T true true <;>
    simp only [binaryCoefficient,e00,e01,e10,e11] <;> decide +kernel

theorem binary_nonlinear (op : GateOp) (i j : ℕ) :
    bitValue (nonlinear ⟨op,[i,j]⟩) =
      binaryCoefficient (fun x y => op.eval [x,y]) := by
  simp [nonlinear,binaryCoefficient,bit_xor,add_assoc]

section Anchored

variable {n m : ℕ}

abbrev Table (n m : ℕ) := Fin n → Fin m → BitField

def anchor (u : Fin n) (q : Fin m) (A : Table n m) : Table n m :=
  fun x y => A x y+A x q+A u y+A u q

def bitTable (P : Fin n → Fin m → Bool) : Table n m := fun x y => bitValue (P x y)

theorem anchor_add (u : Fin n) (q : Fin m) (A B : Table n m) :
    anchor u q (A+B) = anchor u q A + anchor u q B := by
  funext x y
  simp only [anchor,Pi.add_apply]
  ring

theorem anchor_scale (u : Fin n) (q : Fin m) (c : BitField) (A : Table n m) :
    anchor u q (c • A) = c • anchor u q A := by
  funext x y
  simp only [anchor,Pi.smul_apply,smul_eq_mul]
  ring

theorem anchor_const (u : Fin n) (q : Fin m) (c : BitField) :
    anchor u q (fun _ _ => c) = 0 := by
  funext x y
  change c+c+c+c=0
  linear_combination 2*bit_add_self c

theorem anchor_left (u : Fin n) (q : Fin m) (f : Fin n → BitField) :
    anchor u q (fun x _ => f x) = 0 := by
  funext x y
  change f x+f x+f u+f u=0
  linear_combination bit_add_self (f x)+bit_add_self (f u)

theorem anchor_right (u : Fin n) (q : Fin m) (f : Fin m → BitField) :
    anchor u q (fun _ y => f y) = 0 := by
  funext x y
  change f y+f q+f y+f q=0
  linear_combination bit_add_self (f y)+bit_add_self (f q)

def colEffect (u : Fin n) (q : Fin m) (A : Table n m) : Fin m → BitField :=
  fun y => A u y+A u q

theorem anchor_zero_separates (u : Fin n) (q : Fin m) (A : Table n m)
    (zero : anchor u q A = 0) (x : Fin n) (y : Fin m) :
    A x y = A x q+colEffect u q A y := by
  have h := congrFun (congrFun zero x) y
  change A x y+A x q+A u y+A u q=0 at h
  unfold colEffect
  linear_combination h-bit_add_self (A x q)-bit_add_self (A u y)-bit_add_self (A u q)

theorem anchor_product (u : Fin n) (q : Fin m) (A B : Table n m)
    (ha : anchor u q A = 0) (hb : anchor u q B = 0) (x : Fin n) :
    anchor u q (fun i j => A i j*B i j) x =
      (A x q+A u q) • colEffect u q B + (B x q+B u q) • colEffect u q A := by
  funext y
  simp only [anchor,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  rw [anchor_zero_separates u q A ha x y,anchor_zero_separates u q B hb x y,
    anchor_zero_separates u q A ha u y,anchor_zero_separates u q B hb u y]
  linear_combination bit_add_self (A x q*B x q)+bit_add_self (A u q*B u q)+
    bit_add_self (colEffect u q A y*colEffect u q B y)

end Anchored

section Necessity

variable {K : Type} [Field K]
variable {V Y : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable [AddCommGroup Y] [Module K Y]

theorem rank_descent (f : V →ₗ[K] Y) {J L : Submodule K V} (inc : J ≤ L) :
    Module.finrank K J + Module.finrank K (L.map f) ≤
      Module.finrank K L + Module.finrank K (J.map f) := by
  let g := f.comp J.subtype
  let h := f.comp L.subtype
  let k : g.ker →ₗ[K] h.ker :=
    ((Submodule.inclusion inc).comp g.ker.subtype).codRestrict h.ker
      (fun x => LinearMap.mem_ker.mpr (LinearMap.mem_ker.mp x.property))
  have inj : Function.Injective k := by
    intro x y same
    exact Subtype.ext (Subtype.ext (congrArg (fun z : h.ker => z.val.val) same))
  have dim := LinearMap.finrank_le_finrank_of_injective inj
  have left := g.finrank_range_add_finrank_ker
  have right := h.finrank_range_add_finrank_ker
  change Module.finrank K (f.comp J.subtype).range + Module.finrank K g.ker = Module.finrank K J at left
  change Module.finrank K (f.comp L.subtype).range + Module.finrank K h.ker = Module.finrank K L at right
  rw [range_on_submodule] at left right
  omega

variable {n m a b : ℕ}

theorem rowSpan_le_rows (M : Matrix (Fin n) (Fin m) K) {I I' : Finset (Fin n)} (h : I ⊆ I') :
    rowSpan M I ≤ rowSpan M I' := by
  apply Submodule.span_mono
  rintro _ ⟨x,rfl⟩
  exact ⟨⟨x.val,h x.property⟩,rfl⟩

theorem rowSpan_eq_rows (M M' : Matrix (Fin n) (Fin m) K) (I : Finset (Fin n))
    (h : ∀ x ∈ I, ∀ y, M x y=M' x y) :
    rowSpan M I = rowSpan M' I := by
  unfold rowSpan
  apply congrArg (Submodule.span K)
  apply congrArg Set.range
  funext x y
  exact h x.val x.property y

theorem completion_necessary (r : ℕ)
    (row : Fin n → Option (Fin a)) (col : Fin m → Fin b) (bags : Fin a → Finset (Fin b))
    (A : Matrix (Fin n) (Fin m) K) (B : Fin a → Matrix (Fin n) (Fin m) K)
    (G : Matrix (Fin n) (Fin m) K) (budget : Matrix.rank G ≤ r)
    (shared_eq : ∀ x ∈ shared row, ∀ y, G x y=A x y)
    (panel_eq : ∀ i x, x ∈ panelRows row i → ∀ y ∈ panelColumns col (bags i), G x y=B i x y) :
    blockRank A (shared row) Finset.univ ≤ r ∧ ∃ U : Fin b → Submodule K (RowSpace K m),
      (∀ v, Module.finrank K (U v) ≤ r ∧
        ∀ x ∈ shared row, zeroOutside (groupColumns col v) (A x) ∈ U v) ∧
      ∀ i v, v ∈ bags i →
        (∀ x ∈ panelRows row i, zeroOutside (groupColumns col v) (B i x) ∈ U v) ∧
        blockRank A (shared row) Finset.univ +
        blockRank (B i) (panelRows row i) (panelColumns col (bags i)) +
        Module.finrank K (U v) ≤
        r + blockRank A (shared row) (panelColumns col (bags i)) +
        blockRank (B i) (panelRows row i) (groupColumns col v) := by
  let R := shared row
  let S := rowSpan A R
  let P := rowSpan G Finset.univ
  let U (v : Fin b) := maskedSpan G Finset.univ (groupColumns col v)
  have total : Module.finrank K P ≤ r := (total_rank G) ▸ budget
  have Sdim := univ_blockRank A R
  have Se : rowSpan G R = S := rowSpan_eq_rows G A R shared_eq
  have hSP : S ≤ P := by
    rw [← Se]
    exact rowSpan_le_rows G (Finset.subset_univ _)
  refine ⟨by rw [← Sdim]; exact (Submodule.finrank_mono hSP).trans total,U,?_ ,?_⟩
  · intro v
    refine ⟨?_ ,?_⟩
    · have h := (zeroOutside (groupColumns col v) |>.comp P.subtype).finrank_range_le
      rw [range_on_submodule] at h
      exact h.trans total
    · intro x hx
      have eq : G x = A x := funext (shared_eq x hx)
      rw [← eq]
      exact mem_maskedSpan G Finset.univ _ (Finset.mem_univ x)
  · intro i v hv
    let I := panelRows row i
    let J := panelColumns col (bags i)
    let C := groupColumns col v
    have cJ : C ⊆ J := group_le_panel col (bags i) hv
    have col_eq : maskedSpan G I C = maskedSpan (B i) I C :=
      mask_eq_if G (B i) I C (fun x hx y hy => panel_eq i x hx y (cJ hy))
    have bg : maskedSpan G I J = maskedSpan (B i) I J := mask_eq_if G (B i) I J (panel_eq i)
    refine ⟨fun x hx => ?_,?_⟩
    · have member := mem_maskedSpan (B i) I C hx
      rw [← col_eq] at member
      exact mask_mono G (Finset.subset_univ _) C member
    · have first := rank_descent (zeroOutside J) hSP
      have whole : maskedSpan G I J ≤ maskedSpan G Finset.univ J :=
        mask_mono G (Finset.subset_univ _) J
      have second := rank_descent (zeroOutside C) whole
      rw [mask_span_further _ _ cJ,mask_span_further _ _ cJ,bg,col_eq] at second
      change Module.finrank K S + Module.finrank K (maskedSpan G Finset.univ J) ≤
        Module.finrank K P + Module.finrank K (maskedSpan A R J) at first
      rw [Sdim,maskedSpan_rank A R J] at first
      rw [maskedSpan_rank (B i) I J,maskedSpan_rank (B i) I C] at second
      change blockRank A R Finset.univ + blockRank (B i) I J + Module.finrank K (U v) ≤
        r + blockRank A R J + blockRank (B i) I C
      have second' : blockRank (B i) I J + Module.finrank K (U v) ≤
          Module.finrank K (maskedSpan G Finset.univ J) + blockRank (B i) I C := second
      omega

end Necessity

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

section WireLower

variable {n m : ℕ}

abbrev BoolGrid (n m : ℕ) := Fin n → Fin m → Bool

def inputTables (n m : ℕ) : List (BoolGrid n m) :=
  (List.ofFn (fun (i x : Fin n) (_ : Fin m) => decide (i=x))) ++
    List.ofFn (fun (j : Fin m) (_ : Fin n) (y : Fin m) => decide (j=y))

def falseTable : BoolGrid n m := fun _ _ => false

def gridGate (w : List (BoolGrid n m)) (g : Gate) : BoolGrid n m :=
  fun x y => g.op.eval (g.inputs.map (fun i => w.getD i falseTable x y))

def appendGrid (w : List (BoolGrid n m)) (g : Gate) : List (BoolGrid n m) :=
  w ++ [gridGate w g]

theorem getD_map_grid {A B : Type} (f : A → B) (l : List A) (i : ℕ) (a : A) :
    (l.map f).getD i (f a) = f (l.getD i a) := by
  rw [List.getD_eq_getElem?_getD,List.getD_eq_getElem?_getD,List.getElem?_map]
  cases l[i]? <;> rfl

theorem getD_append_single {A : Type} (l : List A) (g d : A) (i : ℕ) :
    (l++[g]).getD i d = if i = l.length then g else l.getD i d := by
  by_cases smaller : i < l.length
  · have ne : i ≠ l.length := by omega
    simp [ne,List.getD_eq_getElem?_getD,List.getElem?_append_left smaller]
  · simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right (by omega : l.length ≤ i)]
    by_cases equal : i=l.length
    · simp [equal]
    · have h : 1 ≤ i-l.length := by omega
      simp [equal,List.getElem?_eq_none (by omega : l.length ≤ i),
        List.getElem?_eq_none (by simpa using h : [g].length ≤ i-l.length)]

theorem grid_wires (gs : List Gate) (init : List (BoolGrid n m)) (x : Fin n) (y : Fin m) :
    (gs.foldl appendGrid init).map (fun f => f x y) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))])
        (init.map (fun f => f x y)) := by
  induction gs generalizing init with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons,ih,appendGrid,List.map_append,List.map_singleton]
    congr 2
    unfold gridGate
    apply congrArg (fun l => [g.op.eval l])
    apply List.map_congr_left
    intro i _
    exact (getD_map_grid (fun f : BoolGrid n m => f x y) init i falseTable).symm

theorem inputTables_eval (x : Fin n) (y : Fin m) :
    (inputTables n m).map (fun f => f x y) = oneEach x y := by
  simp [inputTables,oneEach,List.map_ofFn,Function.comp_def]

theorem inputTables_length (n m : ℕ) : (inputTables n m).length = n+m := by
  simp [inputTables]

theorem input_anchor (u : Fin n) (q : Fin m) (i : ℕ) :
    anchor u q (bitTable ((inputTables n m).getD i falseTable)) = 0 := by
  let w := inputTables n m
  change anchor u q (bitTable (w.getD i falseTable)) = 0
  by_cases h : i < w.length
  · have hm : w.getD i falseTable ∈ w := by
      simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h,Option.getD_some]
      exact List.getElem_mem _
    rcases List.mem_append.mp hm with left|right
    · obtain ⟨j,hj⟩ := List.mem_ofFn.mp left
      rw [← hj]
      exact anchor_left u q _
    · obtain ⟨j,hj⟩ := List.mem_ofFn.mp right
      rw [← hj]
      exact anchor_right u q _
  · have eq : w.getD i falseTable = falseTable := by
      simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega : w.length ≤ i)]
    rw [eq]
    exact anchor_const u q (bitValue false)

theorem gate_input_shapes (ins : List ℕ) (h : ins.length ≤ 2) :
    ins = [] ∨ (∃ a, ins=[a]) ∨ (∃ a b, ins=[a,b]) := by
  rcases ins with _|⟨a,ins⟩
  · exact Or.inl rfl
  rcases ins with _|⟨b,ins⟩
  · exact Or.inr (Or.inl ⟨a,rfl⟩)
  rcases ins with _|⟨c,ins⟩
  · exact Or.inr (Or.inr ⟨a,b,rfl⟩)
  · simp at h

noncomputable def updateForms (u : Fin n) (q : Fin m) (w : List (BoolGrid n m))
    (g : Gate) (S : Finset (Fin m → BitField)) : Finset (Fin m → BitField) := by
  classical
  exact if nonlinear g then
    insert (colEffect u q (bitTable (w.getD (g.inputs.getD 0 0) falseTable)))
      (insert (colEffect u q (bitTable (w.getD (g.inputs.getD 1 0) falseTable))) S)
    else S

theorem forms_subset (u : Fin n) (q : Fin m) (w : List (BoolGrid n m)) (g : Gate)
    (S : Finset (Fin m → BitField)) : S ⊆ updateForms u q w g S := by
  classical
  unfold updateForms
  split
  · intro i hi
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hi)
  · exact Finset.Subset.refl _

theorem forms_budget (u : Fin n) (q : Fin m) (w : List (BoolGrid n m)) (g : Gate)
    (S : Finset (Fin m → BitField)) :
    (updateForms u q w g S).card ≤ S.card + 2*(nonlinear g).toNat := by
  classical
  cases hb : nonlinear g
  · simp [updateForms,hb]
  · simp only [updateForms,hb,Bool.toNat_true,ite_true,Nat.mul_one]
    exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right (Finset.card_insert_le _ _) 1)

set_option maxHeartbeats 4000000 in
theorem gate_invariant (u : Fin n) (q : Fin m) (w : List (BoolGrid n m)) (ds : List ℕ)
    (S : Finset (Fin m → BitField)) (g : Gate) (shape : g.inputs.length ≤ 2)
    (affine : ∀ i, ds.getD i 0=0 → anchor u q (bitTable (w.getD i falseTable))=0)
    (rank : ∀ i, ds.getD i 0≤1 → ∀ x, anchor u q (bitTable (w.getD i falseTable)) x ∈
      Submodule.span BitField (S : Set (Fin m → BitField))) :
    let d := (g.inputs.map (fun h => ds.getD h 0)).foldr max 0+(nonlinear g).toNat
    (d=0 → anchor u q (bitTable (gridGate w g))=0) ∧
    (d≤1 → ∀ x, anchor u q (bitTable (gridGate w g)) x ∈
      Submodule.span BitField (updateForms u q w g S : Set (Fin m → BitField))) := by
  classical
  let H := Submodule.span BitField (updateForms u q w g S : Set (Fin m → BitField))
  have old (i : ℕ) (h : ds.getD i 0 ≤ 1) (x : Fin n) :
      anchor u q (bitTable (w.getD i falseTable)) x ∈ H :=
    Submodule.span_mono (forms_subset u q w g S) (rank i h x)
  rcases g with ⟨op,ins⟩
  change ins.length ≤ 2 at shape
  rcases gate_input_shapes ins shape with rfl | ⟨a,rfl⟩ | ⟨a,b,rfl⟩
  · have zero : anchor u q (bitTable (gridGate w ⟨op,[]⟩)) = 0 := anchor_const u q (bitValue (op.eval []))
    exact ⟨fun _ => zero,fun _ x => by rw [zero]; exact Submodule.zero_mem _⟩
  · let A := bitTable (w.getD a falseTable)
    let c := bitValue (op.eval [false])
    let l := c+bitValue (op.eval [true])
    have spec : bitTable (gridGate w ⟨op,[a]⟩) = (fun _ _ => c)+l • A := by
      funext x y
      exact unary_value (fun b => op.eval [b]) (w.getD a falseTable x y)
    have equation : anchor u q (bitTable (gridGate w ⟨op,[a]⟩)) = l • anchor u q A := by
      rw [spec,anchor_add,anchor_const,zero_add,anchor_scale]
    have d : (([a].map (fun h => ds.getD h 0)).foldr max 0+
      (nonlinear ⟨op,[a]⟩).toNat) = ds.getD a 0 := by simp [nonlinear]
    dsimp only
    rw [d,equation]
    exact ⟨fun h => by rw [affine a h]; simp,fun h x => H.smul_mem l (old a h x)⟩
  · let A := bitTable (w.getD a falseTable)
    let B := bitTable (w.getD b falseTable)
    let T := fun x y => op.eval [x,y]
    let c := bitValue (T false false)
    let l := bitValue (T true false)+c
    let r := bitValue (T false true)+c
    let g : Gate := ⟨op,[a,b]⟩
    let n := nonlinear g
    have coeff : binaryCoefficient T = bitValue n := (binary_nonlinear op a b).symm
    have spec : bitTable (gridGate w g) =
        (fun _ _ => c)+l • A+r • B+bitValue n • (fun x y => A x y*B x y) := by
      funext x y
      change bitValue (T (w.getD a falseTable x y) (w.getD b falseTable x y)) =
        c + l * A x y + r * B x y + bitValue n * (A x y*B x y)
      rw [← coeff]
      exact binary_value T _ _
    have equation : anchor u q (bitTable (gridGate w g)) =
        l • anchor u q A + r • anchor u q B +
          bitValue n • anchor u q (fun x y => A x y*B x y) := by
      rw [spec,anchor_add,anchor_add,anchor_add,anchor_const,zero_add,
        anchor_scale,anchor_scale,anchor_scale]
    let d := max (ds.getD a 0) (ds.getD b 0)+n.toNat
    have deq : (([a,b].map (fun h => ds.getD h 0)).foldr max 0+
      (nonlinear g).toNat) = d := by simp [d,n]
    dsimp only
    rw [deq]
    change (d=0 → anchor u q (bitTable (gridGate w g))=0) ∧
      (d≤1 → ∀ x, anchor u q (bitTable (gridGate w g)) x ∈ H)
    have la : ds.getD a 0 ≤ d := (le_max_left _ _).trans (Nat.le_add_right _ _)
    have lb : ds.getD b 0 ≤ d := (le_max_right _ _).trans (Nat.le_add_right _ _)
    have ln : n.toNat ≤ d := Nat.le_add_left _ _
    constructor
    · intro hz
      have za : ds.getD a 0=0 := by omega
      have zb : ds.getD b 0=0 := by omega
      have zn : n=false := by
        cases hn : n
        · rfl
        · have hn' : n.toNat=1 := by simp [hn]
          omega
      rw [equation,affine a za,affine b zb,zn]
      simp [bitValue]
    · intro hx x
      by_cases paid : n
      · have pn : n = true := paid
        have nd : n.toNat=1 := by simp [pn]
        have za : ds.getD a 0=0 := by dsimp [d] at hx; omega
        have zb : ds.getD b 0=0 := by dsimp [d] at hx; omega
        have memA : colEffect u q A ∈ H := by
          apply Submodule.subset_span
          change colEffect u q A ∈ updateForms u q w g S
          have hb : nonlinear g = true := pn
          simp [updateForms,hb,A,g]
        have memB : colEffect u q B ∈ H := by
          apply Submodule.subset_span
          change colEffect u q B ∈ updateForms u q w g S
          have hb : nonlinear g = true := pn
          simp [updateForms,hb,B,g]
        rw [equation,affine a za,affine b zb]
        simp only [smul_zero,add_zero,zero_add,Pi.smul_apply]
        rw [anchor_product u q A B (affine a za) (affine b zb)]
        exact H.smul_mem _ (H.add_mem (H.smul_mem _ memB) (H.smul_mem _ memA))
      · have pn : n = false := Bool.eq_false_iff.mpr paid
        rw [equation,pn]
        simp only [Pi.add_apply,Pi.smul_apply]
        have b0 : bitValue false=0 := rfl
        rw [b0,zero_smul,add_zero]
        exact H.add_mem (H.smul_mem _ (old a (la.trans hx) x))
          (H.smul_mem _ (old b (lb.trans hx) x))

theorem grid_depth_invariant (u : Fin n) (q : Fin m) (gs : List Gate)
    (legal : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    let W := gs.foldl appendGrid (inputTables n m)
    let D := gs.foldl depthAppend (List.replicate (n+m) 0)
    W.length=D.length ∧ ∃ S : Finset (Fin m → BitField), S.card ≤ 2*(gs.countP nonlinear) ∧
      (∀ i, D.getD i 0=0 → anchor u q (bitTable (W.getD i falseTable))=0) ∧
      (∀ i, D.getD i 0≤1 → ∀ x, anchor u q (bitTable (W.getD i falseTable)) x ∈
        Submodule.span BitField (S : Set (Fin m → BitField))) := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨by simp [inputTables_length],∅,by simp,fun i _ => input_anchor u q i,?_⟩
    intro i _ x
    rw [List.foldl_nil,input_anchor]
    exact Submodule.zero_mem _
  | append_singleton gs g ih =>
    let W := gs.foldl appendGrid (inputTables n m)
    let D := gs.foldl depthAppend (List.replicate (n+m) 0)
    obtain ⟨length,S,size,aff,low⟩ := ih (fun a ha => legal a (by simp [ha]))
    let S' := updateForms u q W g S
    let d := (g.inputs.map (fun h => D.getD h 0)).foldr max 0+(nonlinear g).toNat
    obtain ⟨new0,new1⟩ := gate_invariant u q W D S g (legal g (by simp)) aff low
    have len : W.length=D.length := length
    simpa only [List.foldl_append,List.foldl_cons,List.foldl_nil,appendGrid,depthAppend] using
      (show (W++[gridGate W g]).length=(D++[d]).length ∧
          ∃ R : Finset (Fin m → BitField), R.card ≤ 2*((gs++[g]).countP nonlinear) ∧
          (∀ i, (D++[d]).getD i 0=0 → anchor u q (bitTable ((W++[gridGate W g]).getD i falseTable))=0) ∧
          (∀ i, (D++[d]).getD i 0≤1 → ∀ x,
            anchor u q (bitTable ((W++[gridGate W g]).getD i falseTable)) x ∈
              Submodule.span BitField (R : Set (Fin m → BitField))) from by
        refine ⟨by simp [len],S',?_ ,?_ ,?_⟩
        · have step : S'.card ≤ S.card+2*(nonlinear g).toNat := forms_budget u q W g S
          have size' : S.card ≤ 2*(gs.countP nonlinear) := size
          rw [List.countP_append]
          cases hn : nonlinear g <;> simp only [List.countP_cons,List.countP_nil,hn,Bool.toNat_false,
            Bool.toNat_true,ite_true,ite_false] at step ⊢ <;> omega
        · intro i h
          rw [getD_append_single] at h ⊢
          by_cases hi : i = W.length
          · have hd : i=D.length := hi.trans len
            rw [ite_eq_left hd] at h
            rw [ite_eq_left hi]
            exact new0 h
          · have hd : i ≠ D.length := by simpa [len] using hi
            simp only [hi,hd,ite_true,ite_false] at h ⊢
            exact aff i h
        · intro i h x
          rw [getD_append_single] at h ⊢
          by_cases hi : i = W.length
          · have hd : i=D.length := hi.trans len
            rw [ite_eq_left hd] at h
            rw [ite_eq_left hi]
            exact new1 h x
          · have hd : i ≠ D.length := by simpa [len] using hi
            simp only [hi,hd,ite_true,ite_false] at h ⊢
            exact Submodule.span_mono (forms_subset u q W g S) (low i h x))

theorem representation_rank (u : Fin n) (q : Fin m) (P : BoolGrid n m) (C : Circuit)
    (legal : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (represented : Represents P C) (level : depth (n+m) C ≤ 1) :
    Matrix.rank (anchor u q (bitTable P)) ≤ 2*(C.gates.countP nonlinear) := by
  classical
  let W := C.gates.foldl appendGrid (inputTables n m)
  have evaluation : W.getD C.output falseTable=P := by
    funext x y
    have mapped := grid_wires C.gates (inputTables n m) x y
    rw [inputTables_eval] at mapped
    rw [← getD_map_grid (fun f : BoolGrid n m => f x y),mapped]
    exact represented x y
  obtain ⟨_,S,size,_,rank⟩ := grid_depth_invariant u q C.gates legal
  have rows : ∀ x, anchor u q (bitTable P) x ∈ Submodule.span BitField (S : Set (Fin m → BitField)) := by
    intro x
    rw [← evaluation]
    exact rank C.output level x
  let M : Matrix (Fin n) (Fin m) BitField := anchor u q (bitTable P)
  change Matrix.rank M ≤ _
  rw [total_rank]
  have sub : rowSpan (K := BitField) (anchor u q (bitTable P)) Finset.univ ≤
      Submodule.span BitField (S : Set (Fin m → BitField)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x,rfl⟩
    exact rows x.val
  exact (Submodule.finrank_mono sub).trans
    ((finrank_span_finset_le_card (R := BitField) S).trans size)

end WireLower

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

section UpperPlan

variable {n m : ℕ}

abbrev Plan (n m : ℕ) :=
  {gs : List Gate // ReadsBack (n+m) ⟨gs,0⟩ ∧ ∀ g ∈ gs, g.inputs.length ≤ 2}

def emptyPlan (n m : ℕ) : Plan n m := ⟨[],by simp [ReadsBack],by simp⟩

def tables (P : Plan n m) : List (BoolGrid n m) :=
  P.val.foldl appendGrid (inputTables n m)

def levels (P : Plan n m) : List ℕ :=
  P.val.foldl depthAppend (List.replicate (n+m) 0)

def realizes (P : Plan n m) (d : ℕ) (f : BoolGrid n m) : Prop :=
  ∃ i, i < n+m+P.val.length ∧ (tables P).getD i falseTable = f ∧ (levels P).getD i 0 ≤ d

def advances (P Q : Plan n m) (c : ℕ) : Prop :=
  (∃ rest, Q.val = P.val++rest) ∧ Q.val.countP nonlinear ≤ P.val.countP nonlinear+c

theorem advances_self (P : Plan n m) : advances P P 0 :=
  ⟨⟨[],by simp⟩,by simp⟩

theorem advances_chain {P Q R : Plan n m} {a b : ℕ} (h : advances P Q a) (j : advances Q R b) :
    advances P R (a+b) := by
  obtain ⟨⟨s,hs⟩,hb⟩ := h
  obtain ⟨⟨t,ht⟩,hc⟩ := j
  exact ⟨⟨s++t,by rw [ht,hs,List.append_assoc]⟩,by omega⟩

theorem snoc_fold_length {A : Type} (f : List A → Gate → A) (gs : List Gate) (l : List A) :
    (gs.foldl (fun l g => l++[f l g]) l).length = l.length+gs.length := by
  induction gs generalizing l with
  | nil => simp
  | cons g gs ih => simp [ih]; omega

theorem table_length (P : Plan n m) : (tables P).length = n+m+P.val.length := by
  unfold tables appendGrid
  rw [snoc_fold_length,inputTables_length]

theorem levels_length (P : Plan n m) : (levels P).length = n+m+P.val.length := by
  unfold levels depthAppend
  rw [snoc_fold_length,List.length_replicate]

theorem snoc_fold_getD {A : Type} (f : List A → Gate → A) (gs : List Gate)
    (l : List A) (i : ℕ) (h : i < l.length) (d : A) :
    (gs.foldl (fun l g => l++[f l g]) l).getD i d = l.getD i d := by
  induction gs generalizing l with
  | nil => rfl
  | cons g rest ih =>
    rw [List.foldl_cons,ih _ (by simp; omega),getD_append_single,ite_eq_right (by omega)]

theorem realizes_more {P Q : Plan n m} {c d : ℕ} {f : BoolGrid n m} (h : realizes P d f)
    (e : advances P Q c) : realizes Q d f := by
  obtain ⟨i,hi,hf,hd⟩ := h
  obtain ⟨s,hs⟩ := e.1
  refine ⟨i,by rw [hs,List.length_append]; omega,?_ ,?_⟩
  · unfold tables
    rw [hs,List.foldl_append]
    change (s.foldl (fun l g => l++[gridGate l g]) (tables P)).getD i falseTable = f
    rw [snoc_fold_getD _ _ _ _ (by rwa [table_length])]
    exact hf
  · unfold levels
    rw [hs,List.foldl_append]
    change (s.foldl (fun l g => l++[
      (g.inputs.map (fun j => l.getD j 0)).foldr max 0+(nonlinear g).toNat]) (levels P)).getD i 0 ≤ d
    rw [snoc_fold_getD _ _ _ _ (by rwa [levels_length])]
    exact hd

theorem realize_weaken {P : Plan n m} {a b : ℕ} {f : BoolGrid n m}
    (h : realizes P a f) (hb : a≤b) : realizes P b f := by
  obtain ⟨i,hi,hf,hd⟩ := h
  exact ⟨i,hi,hf,hd.trans hb⟩

def plan_add (P : Plan n m) (g : Gate) (small : g.inputs.length ≤ 2)
    (prior : ∀ i ∈ g.inputs, i < n+m+P.val.length) : Plan n m := by
  refine ⟨P.val++[g],?_ ,?_⟩
  · intro j hj i hi
    change i ∈ ((P.val++[g]).getD j ⟨.or,[]⟩).inputs at hi
    rw [getD_append_single] at hi
    by_cases h : j=P.val.length
    · subst j
      simp at hi
      exact prior i hi
    · have prev : j<P.val.length := by
        change j<(P.val++[g]).length at hj
        simp at hj
        omega
      simp only [h,ite_false] at hi
      exact P.property.1 j prev i hi
  · intro x hx
    rcases List.mem_append.mp hx with old|new
    · exact P.property.2 x old
    · have eq : x=g := by simpa using new
      simpa [eq] using small

theorem append_plan (P : Plan n m) (g : Gate) (small : g.inputs.length ≤ 2)
    (prior : ∀ i ∈ g.inputs, i < n+m+P.val.length) :
    ∃ Q : Plan n m, advances P Q (nonlinear g).toNat ∧
      realizes Q ((g.inputs.map (fun i => (levels P).getD i 0)).foldr max 0+(nonlinear g).toNat)
        (gridGate (tables P) g) := by
  let Q := plan_add P g small prior
  have hQ : Q.val = P.val++[g] := rfl
  have ht : tables Q = tables P++[gridGate (tables P) g] := by
    simp [tables,hQ,List.foldl_append,appendGrid]
  have hd : levels Q = levels P++[(g.inputs.map (fun i => (levels P).getD i 0)).foldr max 0+
      (nonlinear g).toNat] := by
    simp [levels,hQ,List.foldl_append,depthAppend]
  refine ⟨Q,⟨⟨[g],hQ⟩,?_⟩,n+m+P.val.length,?_ ,?_ ,?_⟩
  · rw [hQ,List.countP_append]
    cases hg : nonlinear g <;> simp [hg]
  · simp [hQ]
  · rw [ht,getD_append_single,table_length,ite_eq_left rfl]
  · rw [hd,getD_append_single,levels_length,ite_eq_left rfl]

theorem constant_grid (P : Plan n m) (b : Bool) :
    ∃ Q, advances P Q 0 ∧ realizes Q 0 (fun _ _ => b) := by
  cases b
  · obtain ⟨Q,e,o⟩ := append_plan P ⟨.or,[]⟩ (by simp) (by simp)
    exact ⟨Q,e,o⟩
  · obtain ⟨Q,e,o⟩ := append_plan P ⟨.and,[]⟩ (by simp) (by simp)
    exact ⟨Q,e,o⟩

theorem not_grid (P : Plan n m) {d : ℕ} {f : BoolGrid n m} (hf : realizes P d f) :
    ∃ Q, advances P Q 0 ∧ realizes Q d (fun x y => !(f x y)) := by
  obtain ⟨i,hi,eval,level⟩ := hf
  obtain ⟨Q,e,out⟩ := append_plan P ⟨.not,[i]⟩ (by simp) (by simpa using hi)
  refine ⟨Q,by simpa [nonlinear] using e,?_⟩
  apply realize_weaken _ level
  have eq : gridGate (tables P) ⟨.not,[i]⟩ = (fun x y => !(f x y)) := by
    funext x y
    change (!((tables P).getD i falseTable x y)) = (!(f x y))
    rw [eval]
  simpa [nonlinear,eq] using out

theorem and_grid (P : Plan n m) {f g : BoolGrid n m} (hf : realizes P 0 f) (hg : realizes P 0 g) :
    ∃ Q, advances P Q 1 ∧ realizes Q 1 (fun x y => f x y && g x y) := by
  obtain ⟨i,hi,fi,di⟩ := hf
  obtain ⟨j,hj,fj,dj⟩ := hg
  have refs : ∀ l ∈ [i,j], l<n+m+P.val.length := by simp_all
  have dz1 : (levels P).getD i 0 =0 := by omega
  have dz2 : (levels P).getD j 0 =0 := by omega
  obtain ⟨Q,e,out⟩ := append_plan P ⟨.and,[i,j]⟩ (by simp) refs
  have eq : gridGate (tables P) ⟨.and,[i,j]⟩ = (fun x y => f x y && g x y) := by
    funext x y
    simp [gridGate,GateOp.eval,-List.getD_eq_getElem?_getD,fi,fj]
  exact ⟨Q,by simpa [nonlinear,GateOp.eval] using e,
    by simpa [nonlinear,GateOp.eval,eq,-List.getD_eq_getElem?_getD,dz1,dz2] using out⟩

theorem xor_grid (P : Plan n m) {d : ℕ} {f g : BoolGrid n m}
    (hf : realizes P d f) (hg : realizes P d g) :
    ∃ Q, advances P Q 0 ∧ realizes Q d (fun x y => xor (f x y) (g x y)) := by
  obtain ⟨i,hi,fi,di⟩ := hf
  obtain ⟨j,hj,fj,dj⟩ := hg
  have refs : ∀ l ∈ [i,j], l<n+m+P.val.length := by simp_all
  obtain ⟨Q,e,out⟩ := append_plan P ⟨.mod 2,[i,j]⟩ (by simp) refs
  have ev : nonlinear ⟨.mod 2,[i,j]⟩ = false := rfl
  have e0 : advances P Q 0 := by simpa [ev] using e
  have grade : (([i,j].map (fun l => (levels P).getD l 0)).foldr max 0)+
      (nonlinear ⟨.mod 2,[i,j]⟩).toNat ≤ d := by
    simp [ev,-List.getD_eq_getElem?_getD,di,dj]
  obtain ⟨R,er,neq⟩ := not_grid Q (realize_weaken out grade)
  have eq : (fun x y => !(gridGate (tables P) ⟨.mod 2,[i,j]⟩ x y)) =
      (fun x y => xor (f x y) (g x y)) := by
    funext x y
    simp only [gridGate,List.map_cons,List.map_nil,fi,fj]
    cases f x y <;> cases g x y <;> rfl
  exact ⟨R,by simpa using advances_chain e0 er,eq ▸ neq⟩

theorem build_grid_set {I : Type} (P : Plan n m) (cost d : ℕ) (s : Finset I)
    (f : I → BoolGrid n m)
    (each : ∀ i ∈ s, ∀ (Q : Plan n m) c, advances P Q c →
      ∃ R, advances Q R cost ∧ realizes R d (f i)) :
    ∃ Q, advances P Q (s.card*cost) ∧ ∀ i ∈ s, realizes Q d (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨P,by simpa using advances_self P,by simp⟩
  | @insert i s hi ih =>
    obtain ⟨Q,hQ,done⟩ := ih (fun j hj => each j (Finset.mem_insert_of_mem hj))
    obtain ⟨R,hR,new⟩ := each i (Finset.mem_insert_self _ _) Q _ hQ
    refine ⟨R,by simpa [Finset.card_insert_of_notMem hi,Nat.add_mul] using advances_chain hQ hR,?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl|old
    · exact new
    · exact realizes_more (done j old) hR

theorem xor_grid_sum {I : Type} (P : Plan n m) (d : ℕ) (s : Finset I)
    (f : I → BoolGrid n m) (all : ∀ i ∈ s, realizes P d (f i)) :
    ∃ Q, advances P Q 0 ∧ realizes Q d (fun x y => bitOf (∑ i ∈ s, bitValue (f i x y))) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨Q,e,z⟩ := constant_grid P false
    refine ⟨Q,e,?_⟩
    simpa [bitOf] using realize_weaken z (Nat.zero_le d)
  | @insert i s hi ih =>
    obtain ⟨Q,e,prev⟩ := ih (fun j hj => all j (Finset.mem_insert_of_mem hj))
    have current := realizes_more (all i (Finset.mem_insert_self _ _)) e
    obtain ⟨R,j,combo⟩ := xor_grid Q current prev
    have eq : (fun x y => xor (f i x y) (bitOf (∑ a ∈ s, bitValue (f a x y)))) =
        (fun x y => bitOf (∑ a ∈ insert i s, bitValue (f a x y))) := by
      funext x y
      apply bitValue_injective
      simp [bit_xor,bitValue_of,Finset.sum_insert hi]
    exact ⟨R,by simpa using advances_chain e j,eq ▸ combo⟩

end UpperPlan

open PEqualNP.CircuitLowerBounds PEqualNP.Represents PEqualNP.MetaComplexity.NestedCover

section WireUpper

variable {n m t : ℕ}

theorem realizes_initial (P : Plan n m) (i : ℕ) (hi : i<n+m) (f : BoolGrid n m)
    (eq : (inputTables n m).getD i falseTable=f) : realizes P 0 f := by
  refine ⟨i,by omega,?_ ,?_⟩
  · unfold tables appendGrid
    rw [snoc_fold_getD gridGate _ _ _ (by rwa [inputTables_length])]
    exact eq
  · unfold levels depthAppend
    have h : i < (List.replicate (n+m) 0).length := by simpa using hi
    rw [snoc_fold_getD _ _ _ _ h]
    simp [List.getD_eq_getElem?_getD]

theorem realizes_left_input (P : Plan n m) (i : Fin n) :
    realizes P 0 (fun x (_ : Fin m) => decide (i = x)) := by
  apply realizes_initial P i.val (by have := i.isLt; omega)
  unfold inputTables
  rw [List.getD_eq_getElem?_getD,List.getElem?_append_left (by simpa using i.isLt)]
  simp only [List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some]

theorem realizes_right_input (P : Plan n m) (j : Fin m) :
    realizes P 0 (fun (_ : Fin n) y => decide (j = y)) := by
  apply realizes_initial P (n+j.val) (by have := j.isLt; omega)
  unfold inputTables
  rw [List.getD_eq_getElem?_getD,List.getElem?_append_right (by simp)]
  simp only [List.length_ofFn,Nat.add_sub_cancel_left,List.getElem?_ofFn,
    dite_eq_left j.isLt,Option.getD_some]

theorem indicator_sum {I : Type} [Fintype I] [DecidableEq I] (p : I → BitField) (x : I) :
    (∑ i ∈ Finset.univ.filter (fun i => p i=1), bitValue (decide (i=x))) = p x := by
  have term (i : I) : bitValue (decide (i=x)) = if i=x then 1 else 0 := by
    by_cases h : i=x <;> simp [h,bitValue]
  simp_rw [term]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  generalize p x = v
  fin_cases v <;> rfl

theorem affine_grid (P : Plan n m) (a : Fin n → BitField) (b : Fin m → BitField) :
    ∃ Q, advances P Q 0 ∧ realizes Q 0 (fun x y => bitOf (a x+b y)) := by
  let L := Finset.univ.filter (fun i : Fin n => a i=1)
  let R := Finset.univ.filter (fun j : Fin m => b j=1)
  obtain ⟨Q,e,left⟩ := xor_grid_sum P 0 L
    (fun i x _ => decide (i=x)) (fun i _ => realizes_left_input P i)
  obtain ⟨U,h,right⟩ := xor_grid_sum Q 0 R
    (fun j _ y => decide (j=y)) (fun j _ => realizes_right_input Q j)
  obtain ⟨V,v,result⟩ := xor_grid U (realizes_more left h) right
  refine ⟨V,by simpa using advances_chain (advances_chain e h) v,?_⟩
  have eq : (fun x y => xor (bitOf (∑ i ∈ L, bitValue (decide (i=x))))
      (bitOf (∑ j ∈ R, bitValue (decide (j=y))))) = (fun x y => bitOf (a x+b y)) := by
    funext x y
    apply bitValue_injective
    rw [bit_xor,bitValue_of,bitValue_of,bitValue_of,indicator_sum a x,indicator_sum b y]
  exact eq ▸ result

theorem row_rank_factor (M : Matrix (Fin n) (Fin m) BitField) (bound : Matrix.rank M ≤ 2*t) :
    ∃ (A : Fin t → Fin 2 → Fin n → BitField) (B : Fin t → Fin 2 → Fin m → BitField),
      ∀ x y, M x y = ∑ j : Fin t, (A j 0 x*B j 0 y+A j 1 x*B j 1 y) := by
  classical
  let H := rowSpan M Finset.univ
  let V := (Fin t × Fin 2) → BitField
  have vd : Module.finrank BitField V=2*t := by
    simp [V,Module.finrank_pi_fintype,Nat.mul_comm]
  have hd : Module.finrank BitField H ≤ Module.finrank BitField V := by
    exact (total_rank M).symm ▸ vd.symm ▸ bound
  obtain ⟨j,hj⟩ := (finrank_le_iff_exists_linearMap (R := BitField)).mp hd
  obtain ⟨l,hl⟩ := left_section j hj
  let recover : V →ₗ[BitField] (Fin m → BitField) := H.subtype.comp l
  let r (x : Fin n) : H := ⟨M x,Submodule.subset_span ⟨⟨x,Finset.mem_univ _⟩,rfl⟩⟩
  let k (p : Fin t × Fin 2) : V := Pi.single p 1
  refine ⟨fun a b x => j (r x) (a,b),fun a b y => recover (k (a,b)) y,?_⟩
  intro x y
  have basis (z : V) : (∑ p : Fin t × Fin 2, z p • k p)=z := by
    funext i
    change ((∑ p : Fin t × Fin 2, z p • k p) : (Fin t × Fin 2) → BitField) i = z i
    rw [Finset.sum_apply]
    change (∑ p : Fin t × Fin 2, z p * k p i) = z i
    simp [k,Pi.single_apply,mul_ite]
  have expanded : (∑ p : Fin t × Fin 2, j (r x) p • recover (k p))=M x := by
    simp_rw [← map_smul]
    rw [← map_sum,basis]
    change (l (j (r x))).val = M x
    rw [hl]
  have formula := congrFun expanded y
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at formula
  rw [Fintype.sum_prod_type] at formula
  simp_rw [Fin.sum_univ_two] at formula
  exact formula.symm

theorem represent_from_rank (u : Fin n) (q : Fin m) (P : BoolGrid n m)
    (bound : Matrix.rank (anchor u q (bitTable P)) ≤ 2*t) :
    ∃ C : Circuit,
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ ReadsBack (n+m) C ∧ Represents P C ∧
      depth (n+m) C ≤ 1 ∧ C.gates.countP nonlinear ≤ t := by
  classical
  let M : Matrix (Fin n) (Fin m) BitField := anchor u q (bitTable P)
  obtain ⟨A,B,h⟩ := row_rank_factor M (t := t) bound
  let f (j : Fin t) (x : Fin n) (y : Fin m) :=
    bitOf (A j 0 x+B j 1 y) && bitOf (A j 1 x+B j 0 y)
  let P0 := emptyPlan n m
  obtain ⟨Q,e,acts⟩ := build_grid_set P0 1 1 Finset.univ f (by
    intro j _ Q _ _
    obtain ⟨R,hR,left⟩ := affine_grid Q (A j 0) (B j 1)
    obtain ⟨V,hV,right⟩ := affine_grid R (A j 1) (B j 0)
    obtain ⟨X,hX,act⟩ := and_grid V (realizes_more left hV) right
    exact ⟨X,by simpa using advances_chain (advances_chain hR hV) hX,act⟩)
  obtain ⟨R,rR,main⟩ := xor_grid_sum Q 1 Finset.univ f (fun i hi => acts i hi)
  let a (x : Fin n) := bitValue (P x q) + (∑ i : Fin t, A i 0 x * A i 1 x)
  let b (y : Fin m) := bitValue (P u y) + bitValue (P u q) + (∑ i : Fin t, B i 0 y * B i 1 y)
  obtain ⟨D,dD,correction⟩ := affine_grid R a b
  obtain ⟨E,eE,both⟩ := xor_grid D (realizes_more main dD) (realize_weaken correction (by decide))
  have eq : (fun x y => xor (bitOf (∑ i : Fin t, bitValue (f i x y))) (bitOf (a x+b y)))=P := by
    funext x y
    apply bitValue_injective
    rw [bit_xor,bitValue_of,bitValue_of]
    have each (i : Fin t) : bitValue (f i x y) =
        (A i 0 x*B i 0 y+A i 1 x*B i 1 y)+(A i 0 x*A i 1 x+B i 0 y*B i 1 y) := by
      simp only [f,bit_and,bitValue_of]
      ring
    simp_rw [each,Finset.sum_add_distrib]
    -- Preserve the grouped cross terms while rewriting them to the anchored row.
    have hcross : (∑ i : Fin t, A i 0 x*B i 0 y) + (∑ i : Fin t, A i 1 x*B i 1 y) = M x y := by
      rw [← Finset.sum_add_distrib,← h x y]
    rw [hcross]
    dsimp only [M,anchor,bitTable,a,b]
    linear_combination bit_add_self (bitValue (P x q))+bit_add_self (bitValue (P u y))+
      bit_add_self (bitValue (P u q))+bit_add_self (∑ i : Fin t, A i 0 x*A i 1 x)+
      bit_add_self (∑ i : Fin t, B i 0 y*B i 1 y)
  have eval : realizes E 1 P := eq ▸ both
  obtain ⟨j,_,hj,lev⟩ := eval
  let C : Circuit := ⟨E.val,j⟩
  have cost := (advances_chain (advances_chain (advances_chain e rR) dD) eE).2
  have actual : E.val.countP nonlinear≤t := by simpa [P0,emptyPlan] using cost
  refine ⟨C,E.property.2,E.property.1,?_ ,lev,actual⟩
  intro x y
  have eq := grid_wires E.val (inputTables n m) x y
  rw [inputTables_eval] at eq
  have verdict := congrArg (fun f : BoolGrid n m => f x y) hj
  change (C.wires (oneEach x y)).getD j false = P x y
  unfold Circuit.wires
  rw [← eq]
  change ((tables E).map (fun f => f x y)).getD j ((fun f : BoolGrid n m => f x y) falseTable) = _
  rw [getD_map_grid]
  exact verdict

end WireUpper

open PEqualNP.CircuitLowerBounds PEqualNP.Represents PEqualNP.MetaComplexity.NestedCover

section Weighted

variable {n m a b : ℕ}

def cells (row : Fin n → Option (Fin a)) (col : Fin m → Fin b) (bags : Fin a → Finset (Fin b))
    (q : Fin m) (i : Fin a) : Finset (Fin n × Fin m) :=
  Finset.univ.filter (fun z => row z.1=some i ∧ col z.2 ∈ bags i ∧ z.2≠q)

def corrected (A : Matrix (Fin n) (Fin m) BitField) (F : Finset (Fin n × Fin m)) :
    Matrix (Fin n) (Fin m) BitField :=
  fun x y => A x y + if (x,y) ∈ F then 1 else 0

theorem bit_value_delta (x y : Bool) :
    bitValue x = bitValue y + if x ≠ y then 1 else 0 := by
  cases x <;> cases y <;> decide +kernel

theorem bit_diff_iff (x y : Bool) (p : Prop) [Decidable p]
    (h : bitValue x = bitValue y + if p then 1 else 0) : x ≠ y ↔ p := by
  by_cases hp : p
  · rw [if_pos hp] at h
    refine ⟨fun _ => hp,fun _ eq => ?_⟩
    rw [eq] at h
    have bad : (1:BitField) = 0 := by linear_combination -h
    exact one_ne_zero bad
  · rw [if_neg hp,add_zero] at h
    exact ⟨fun bad => (bad (bitValue_injective h)).elim,fun no => (hp no).elim⟩

theorem anchor_at_row (u : Fin n) (q : Fin m) (T : Table n m) (y : Fin m) :
    anchor u q T u y=0 := by
  unfold anchor
  linear_combination bit_add_self (T u y)+bit_add_self (T u q)

theorem anchor_at_col (u : Fin n) (q : Fin m) (T : Table n m) (x : Fin n) :
    anchor u q T x q=0 := by
  unfold anchor
  linear_combination bit_add_self (T x q)+bit_add_self (T u q)

theorem mask_total_rank (M : Matrix (Fin n) (Fin m) BitField) (J : Finset (Fin m)) :
    Matrix.rank (fun x => zeroOutside J (M x)) ≤ Matrix.rank M := by
  let H : Matrix (Fin n) (Fin m) BitField := fun x => zeroOutside J (M x)
  change Matrix.rank H ≤ Matrix.rank M
  rw [total_rank H,total_rank M]
  have eq : rowSpan H Finset.univ = maskedSpan M Finset.univ J := by
    rw [rowSpan_map,rowSpan]
  rw [eq]
  have h := (zeroOutside J |>.comp (rowSpan M Finset.univ).subtype).finrank_range_le
  rw [range_on_submodule] at h
  exact h

theorem weighted_forward
    (t : ℕ) (T : BoolGrid n m) (row : Fin n → Option (Fin a)) (col : Fin m → Fin b)
    (bags : Fin a → Finset (Fin b)) (u : Fin n) (q : Fin m) (hu : row u=none)
    (w : Fin n × Fin m → ℕ) (e : Fin a → ℕ)
    (P : BoolGrid n m) (C : Circuit)
    (legal : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (rep : Represents P C)
    (level : depth (n+m) C≤1) (cost : C.gates.countP nonlinear≤t)
    (sharedValid : ∀ x y, row x=none → P x y=T x y)
    (anchorValid : ∀ x, P x q = T x q)
    (errors : ∀ i, ((cells row col bags q i).filter (fun z => P z.1 z.2≠T z.1 z.2)).sum w ≤ e i) :
    let A : Matrix (Fin n) (Fin m) BitField := anchor u q (bitTable T)
    let R := shared row
    blockRank A R Finset.univ ≤ 2*t ∧ ∃ U : Fin b → Submodule BitField (RowSpace BitField m),
      (∀ v, Module.finrank BitField (U v) ≤ 2*t ∧
        ∀ x ∈ R, zeroOutside (groupColumns col v) (A x) ∈ U v) ∧
      ∀ i, ∃ F : Finset (Fin n × Fin m), F ⊆ cells row col bags q i ∧ F.sum w≤e i ∧
        ∀ v ∈ bags i,
          (∀ x ∈ panelRows row i, zeroOutside (groupColumns col v) (corrected A F x) ∈ U v) ∧
          blockRank A R Finset.univ +
          blockRank (corrected A F) (panelRows row i) (panelColumns col (bags i)) +
          Module.finrank BitField (U v) ≤
          2*t + blockRank A R (panelColumns col (bags i)) +
          blockRank (corrected A F) (panelRows row i) (groupColumns col v) := by
  classical
  let A : Matrix (Fin n) (Fin m) BitField := anchor u q (bitTable T)
  let G : Matrix (Fin n) (Fin m) BitField := anchor u q (bitTable P)
  let F (i : Fin a) := (cells row col bags q i).filter (fun z => P z.1 z.2≠T z.1 z.2)
  have low : Matrix.rank G ≤ 2*t := (representation_rank u q P C legal rep level).trans
    (Nat.mul_le_mul_left 2 cost)
  have delta (x : Fin n) (y : Fin m) :
      G x y = A x y + if P x y ≠ T x y then 1 else 0 := by
    dsimp only [G,A,anchor,bitTable]
    rw [anchorValid,sharedValid u y hu,sharedValid u q hu,
      bit_value_delta (P x y) (T x y)]
    ring
  have onShared : ∀ x ∈ shared row, ∀ y, G x y=A x y := by
    intro x hx y
    rw [delta,sharedValid x y (Finset.mem_filter.mp hx).2]
    simp
  have onPanel (i : Fin a) : ∀ x ∈ panelRows row i, ∀ y ∈ panelColumns col (bags i),
      G x y=corrected A (F i) x y := by
    intro x hx y hy
    have mark : (x,y) ∈ F i ↔ P x y ≠ T x y := by
      constructor
      · exact fun h => (Finset.mem_filter.mp h).2
      · intro h
        rcases Finset.mem_union.mp hx with hs|hp
        · exact (h (sharedValid x y (Finset.mem_filter.mp hs).2)).elim
        · have hr : row x=some i := (Finset.mem_filter.mp hp).2
          have hc : col y∈bags i := (Finset.mem_filter.mp hy).2
          have hq : y≠q := fun eq => h (eq ▸ anchorValid x)
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr,hc,hq⟩,h⟩
    rw [corrected,delta]
    simp only [mark]
  obtain ⟨base,U,hU,panels⟩ := completion_necessary (2*t) row col bags A
    (fun i => corrected A (F i)) G low onShared onPanel
  exact ⟨base,U,hU,fun i => ⟨F i,Finset.filter_subset _ _,errors i,fun v hv => panels i v hv⟩⟩

end Weighted

open PEqualNP.CircuitLowerBounds PEqualNP.Represents PEqualNP.MetaComplexity.NestedCover

section WeightedReverse

variable {n m a b : ℕ}

theorem weighted_reverse
    (t : ℕ) (T : BoolGrid n m) (row : Fin n → Option (Fin a)) (col : Fin m → Fin b)
    (bags : Fin a → Finset (Fin b)) (u : Fin n) (q : Fin m) (hu : row u=none)
    (w : Fin n × Fin m → ℕ) (e : Fin a → ℕ)
    (forest : ∀ i, (bags i ∩ pastGroups bags i.val).card ≤ 1) :
    let A : Matrix (Fin n) (Fin m) BitField := anchor u q (bitTable T)
    let R := shared row
    (blockRank A R Finset.univ ≤ 2*t ∧ ∃ U : Fin b → Submodule BitField (RowSpace BitField m),
      (∀ v, Module.finrank BitField (U v) ≤ 2*t ∧
        ∀ x ∈ R, zeroOutside (groupColumns col v) (A x) ∈ U v) ∧
      ∀ i, ∃ F : Finset (Fin n × Fin m), F ⊆ cells row col bags q i ∧ F.sum w≤e i ∧
        ∀ v ∈ bags i,
          (∀ x ∈ panelRows row i, zeroOutside (groupColumns col v) (corrected A F x) ∈ U v) ∧
          blockRank A R Finset.univ +
          blockRank (corrected A F) (panelRows row i) (panelColumns col (bags i)) +
          Module.finrank BitField (U v) ≤
          2*t + blockRank A R (panelColumns col (bags i)) +
          blockRank (corrected A F) (panelRows row i) (groupColumns col v)) →
    ∃ (P : BoolGrid n m) (C : Circuit),
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ ReadsBack (n+m) C ∧ Represents P C ∧
      depth (n+m) C≤1 ∧ C.gates.countP nonlinear≤t ∧
      (∀ x y, row x = none → P x y=T x y) ∧ (∀ x, P x q=T x q) ∧
      ∀ i, ((cells row col bags q i).filter (fun z => P z.1 z.2≠T z.1 z.2)).sum w≤e i := by
  classical
  let A : Matrix (Fin n) (Fin m) BitField := anchor u q (bitTable T)
  let R := shared row
  dsimp only
  intro valid
  obtain ⟨base,U,hU,panels⟩ := valid
  choose F hsub hcost hlocal using panels
  let B (i : Fin a) := corrected A (F i)
  have same (i : Fin a) (x : Fin n) (hx : x∈R) (y : Fin m) : B i x y=A x y := by
    have h : (x,y) ∉ F i := by
      intro bad
      have rowi := (Finset.mem_filter.mp (hsub i bad)).2.1
      have sharedx := (Finset.mem_filter.mp hx).2
      simp [sharedx] at rowi
    simp [B,corrected,h]
  obtain ⟨G,rankG,agreeShared,agreePanel⟩ := forest_complete (2*t) row col bags forest A B same U
    base (fun v => (hU v).2) (fun i v hv => (hlocal i v hv).1)
    (fun i v hv => (hlocal i v hv).2)
  let J := Finset.univ.erase q
  let G' : Matrix (Fin n) (Fin m) BitField := fun x => zeroOutside J (G x)
  have gq (x : Fin n) : G' x q=0 := by simp [G',J,zeroOutside_apply]
  have gkeep (x : Fin n) (y : Fin m) (hy : y≠q) : G' x y=G x y := by
    simp [G',J,zeroOutside_apply,hy]
  have sharedEq (x : Fin n) (hx : row x=none) (y : Fin m) : G' x y=A x y := by
    by_cases hy : y=q
    · subst y
      exact (gq x).trans (anchor_at_col u q (bitTable T) x).symm
    · exact (gkeep x y hy).trans (agreeShared x hx y)
  have gu (y : Fin m) : G' u y=0 :=
    (sharedEq u hu y).trans (anchor_at_row u q (bitTable T) y)
  let P (x : Fin n) (y : Fin m) :=
    bitOf (G' x y + bitValue (T x q) + bitValue (T u y) + bitValue (T u q))
  have pval (x : Fin n) (y : Fin m) :
      bitValue (P x y)=G' x y+bitValue (T x q)+bitValue (T u y)+bitValue (T u q) := bitValue_of _
  have pShared (x : Fin n) (y : Fin m) (hx : row x=none) : P x y=T x y := by
    apply bitValue_injective
    rw [pval,sharedEq x hx y]
    change (bitValue (T x y)+bitValue (T x q)+bitValue (T u y)+bitValue (T u q))+
      bitValue (T x q)+bitValue (T u y)+bitValue (T u q)=bitValue (T x y)
    linear_combination bit_add_self (bitValue (T x q)) +
      bit_add_self (bitValue (T u y)) + bit_add_self (bitValue (T u q))
  have pq (x : Fin n) : P x q=T x q := by
    apply bitValue_injective
    rw [pval,gq,zero_add]
    linear_combination bit_add_self (bitValue (T u q))
  have pAnchor : anchor u q (bitTable P)=G' := by
    funext x y
    simp only [anchor,bitTable,pval,gq,gu,zero_add]
    linear_combination bit_add_self (bitValue (T x q))+
      bit_add_self (bitValue (T u y))+4*bit_add_self (bitValue (T u q))
  have pRank : Matrix.rank (anchor u q (bitTable P))≤2*t :=
    pAnchor.symm ▸ (mask_total_rank G J).trans rankG
  obtain ⟨C,legal,back,rep,lev,cnt⟩ := represent_from_rank u q P (t := t) pRank
  refine ⟨P,C,legal,back,rep,lev,cnt,pShared,pq,?_⟩
  intro i
  have flips : (cells row col bags q i).filter (fun z => P z.1 z.2≠T z.1 z.2) = F i := by
    ext z
    rcases z with ⟨x,y⟩
    by_cases marked : (x,y)∈cells row col bags q i
    · obtain ⟨_,hx,hy,hq⟩ := Finset.mem_filter.mp marked
      have column : y∈panelColumns col (bags i) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hy⟩
      have panelMatch : G' x y = B i x y := (gkeep x y hq).trans (agreePanel i x hx y column)
      have dx : bitValue (P x y) = bitValue (T x y)+if (x,y)∈F i then 1 else 0 := by
        rw [pval,panelMatch]
        change
          ((bitValue (T x y)+bitValue (T x q)+bitValue (T u y)+bitValue (T u q))+
            (if (x,y)∈F i then 1 else 0))+
            bitValue (T x q)+bitValue (T u y)+bitValue (T u q) = _
        linear_combination bit_add_self (bitValue (T x q))+
          bit_add_self (bitValue (T u y))+bit_add_self (bitValue (T u q))
      simpa only [Finset.mem_filter,marked,true_and] using bit_diff_iff (P x y) (T x y) _ dx
    · have none : (x,y)∉F i := fun h => marked (hsub i h)
      simp [Finset.mem_filter,marked,none]
  rw [flips]
  exact hcost i

end WeightedReverse

end PEqualNP.Outside.L_meta_33652

theorem PEqualNP.Outside.L_meta_33652 :
  let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
    xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
        (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
let depth := fun (w : ℕ) (Q : PEqualNP.CircuitLowerBounds.Circuit) =>
  (Q.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun h => ds.getD h 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate w 0)).getD Q.output 0
∀ (n m a b t : ℕ) (T : Fin n → Fin m → Bool)
  (row : Fin n → Option (Fin a)) (col : Fin m → Fin b) (bags : Fin a → Finset (Fin b))
  (u : Fin n) (q : Fin m) (_ : row u = none) (w : Fin n × Fin m → ℕ) (e : Fin a → ℕ),
  (∀ i : Fin a, ((bags i) ∩ ((Finset.univ.filter (fun j : Fin a => j < i)).biUnion bags)).card ≤ 1) →
  let R := (Finset.univ : Finset (Fin n)).filter (fun x => row x = none)
  let rows := fun i : Fin a => R ∪ Finset.univ.filter (fun x => row x = some i)
  let cols := fun i : Fin a => (Finset.univ : Finset (Fin m)).filter (fun y => col y ∈ bags i)
  let group := fun v : Fin b => (Finset.univ : Finset (Fin m)).filter (fun y => col y = v)
  let cells := fun i : Fin a => (Finset.univ : Finset (Fin n × Fin m)).filter
    (fun z => row z.1 = some i ∧ col z.2 ∈ bags i ∧ z.2 ≠ q)
  let entry := fun x y => ((T x y).toNat : ZMod 2)
  let A : Matrix (Fin n) (Fin m) (ZMod 2) := fun x y => entry x y + entry x q + entry u y + entry u q
  let rk := fun (B : Matrix (Fin n) (Fin m) (ZMod 2)) (I : Finset (Fin n)) (J : Finset (Fin m)) =>
    Matrix.rank (B.submatrix (fun x : I => x.val) (fun y : J => y.val))
  let base := rk A R Finset.univ
  ((∃ (P : Fin n → Fin m → Bool) (Q : PEqualNP.CircuitLowerBounds.Circuit),
    (∀ g ∈ Q.gates, g.inputs.length ≤ 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+m) Q ∧
    PEqualNP.Represents.Represents P Q ∧ depth (n+m) Q ≤ 1 ∧ Q.gates.countP nonlinear ≤ t ∧
    (∀ x y, row x = none → P x y = T x y) ∧ (∀ x, P x q = T x q) ∧
    ∀ i, (((cells i).filter (fun z => P z.1 z.2 ≠ T z.1 z.2)).sum w) ≤ e i) ↔
    base ≤ 2*t ∧ ∃ U : Fin b → Submodule (ZMod 2) (Fin m → ZMod 2),
      (∀ v, Module.finrank (ZMod 2) (U v) ≤ 2*t ∧
        ∀ x ∈ R, (fun y => if col y = v then A x y else 0) ∈ U v) ∧
      ∀ i : Fin a, ∃ F : Finset (Fin n × Fin m), F ⊆ cells i ∧ F.sum w ≤ e i ∧
        let B : Matrix (Fin n) (Fin m) (ZMod 2) := fun x y => A x y + (if (x,y) ∈ F then 1 else 0)
        ∀ v ∈ bags i, (∀ x ∈ rows i, (fun y => if col y = v then B x y else 0) ∈ U v) ∧
          base + rk B (rows i) (cols i) + Module.finrank (ZMod 2) (U v) ≤
            2*t + rk A R (cols i) + rk B (rows i) (group v)) := by
  classical
  dsimp only
  intro n m a b t T row col bags u q hu w e forest
  have forest' : ∀ i, (bags i ∩ PEqualNP.Outside.L_meta_33652.pastGroups bags i.val).card ≤ 1 := forest
  have showGroup (v : Fin b) (z : Fin m → ZMod 2) :
      PEqualNP.Outside.L_meta_33652.zeroOutside
        (PEqualNP.Outside.L_meta_33652.groupColumns col v) z =
      (fun y => if col y = v then z y else 0) := by
    funext y
    simp [PEqualNP.Outside.L_meta_33652.zeroOutside_apply,
      PEqualNP.Outside.L_meta_33652.groupColumns]
  constructor
  · rintro ⟨P,C,legal,_,rep,lev,cost,sharedGood,anchorGood,weightGood⟩
    obtain ⟨base,U,hU,bagsGood⟩ :=
      PEqualNP.Outside.L_meta_33652.weighted_forward
        t T row col bags u q hu w e P C legal rep lev cost sharedGood anchorGood weightGood
    refine ⟨base,U,?_ ,?_⟩
    · intro v
      refine ⟨(hU v).1,?_⟩
      intro x hx
      have h := (hU v).2 x hx
      rw [showGroup] at h
      exact h
    · intro i
      obtain ⟨F,sub,cap,hF⟩ := bagsGood i
      refine ⟨F,sub,cap,?_⟩
      intro v hv
      refine ⟨?_ ,(hF v hv).2⟩
      intro x hx
      have h := (hF v hv).1 x hx
      rw [showGroup] at h
      exact h
  · rintro ⟨base,U,hU,bagsGood⟩
    apply PEqualNP.Outside.L_meta_33652.weighted_reverse t T row col bags u q hu w e forest'
    refine ⟨base,U,?_ ,?_⟩
    · intro v
      refine ⟨(hU v).1,?_⟩
      intro x hx
      rw [showGroup]
      exact (hU v).2 x hx
    · intro i
      obtain ⟨F,sub,cap,hF⟩ := bagsGood i
      refine ⟨F,sub,cap,?_⟩
      intro v hv
      refine ⟨?_ ,(hF v hv).2⟩
      intro x hx
      rw [showGroup]
      exact (hF v hv).1 x hx
