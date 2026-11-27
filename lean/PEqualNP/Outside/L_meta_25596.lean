import PEqualNP.Outside.L_meta_25594

open PEqualNP.Outside.L_meta_25594_aux

namespace PEqualNP.Outside.L_meta_25596_aux

private theorem diffComm {k : ℕ} (f : Word94 k → Bool) (u v : Word94 k) :
    boolDiff94 (boolDiff94 f u) v = boolDiff94 (boolDiff94 f v) u := by
  funext x
  have commute : add94 (add94 x v) u = add94 (add94 x u) v := by
    funext i
    change xor (xor (x i) (v i)) (u i) = xor (xor (x i) (u i)) (v i)
    cases x i <;> cases u i <;> cases v i <;> rfl
  simp only [boolDiff94, commute]
  generalize f x = a
  generalize f (add94 x u) = b
  generalize f (add94 x v) = c
  generalize f (add94 (add94 x u) v) = e
  cases a <;> cases b <;> cases c <;> cases e <;> rfl

private theorem sliceZero {k : ℕ} (f : Word94 k → Bool) (base shift u v w : Word94 k)
    (pinned : Finset (Fin k)) (sign : Bool)
    (hconst : ∀ z, (∀ q ∈ pinned, z q = base q) → boolDiff94 f shift z = sign)
    (hu : ∀ q ∈ pinned, u q = false) (hv : ∀ q ∈ pinned, v q = false)
    (hw : ∀ q ∈ pinned, w q = false) :
    boolDiff94 (boolDiff94 (boolDiff94 (boolDiff94 f u) v) w) shift base = false := by
  rw [diffComm (boolDiff94 (boolDiff94 f u) v) w shift,
      diffComm (boolDiff94 f u) v shift, diffComm f u shift]
  let slice (z : Word94 k) := ∀ q ∈ pinned, z q = base q
  have annihilate (g : Word94 k → Bool) (c : Bool) (h : Word94 k)
      (hh : ∀ q ∈ pinned, h q = false) (hg : ∀ z, slice z → g z = c) :
      ∀ z, slice z → boolDiff94 g h z = false := by
    intro z hz
    have hs : slice (add94 z h) := by
      intro q hq
      simp [add94, hh q hq, hz q hq]
    unfold boolDiff94
    rw [hg z hz, hg _ hs]
    cases c <;> rfl
  exact annihilate _ false w hw (annihilate _ false v hv (annihilate _ sign u hu hconst))
    base (fun _ _ => rfl)

private theorem unitFree {k : ℕ} {pinned : Finset (Fin k)} {p : Fin k} (hp : p ∉ pinned) :
    ∀ q ∈ pinned, dir94 p q = false := by
  intro q hq
  have hne : q ≠ p := fun h => hp (h ▸ hq)
  simp [dir94, hne]

private theorem relative {k d : ℕ} (hk : 0 < k) (j t : Fin k) (r s a : ℕ)
    (hj : at94 hk d j r = t) (ha : r + s = a ∨ r + s = a + k) :
    idx94 hk (t.val + s) = at94 hk d j a := by
  rw [← hj]
  change idx94 hk ((idx94 hk (anch94 d j + r)).val + s) = idx94 hk (anch94 d j + a)
  rw [idx_shift94, Nat.add_assoc]
  rcases ha with h | h
  · rw [h]
  · rw [h, ← Nat.add_assoc, idx_wrap94]

end PEqualNP.Outside.L_meta_25596_aux

open PEqualNP.Outside.L_meta_25596_aux in
theorem PEqualNP.Outside.L_meta_25596 :
∀ (k d : ℕ) (hk : 0 < k), 0 < d → 4 * d + 4 < k →
  let W := Fin k → Bool
  let idx := fun (n : ℕ) => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
  let add := fun (x y : W) (i : Fin k) => xor (x i) (y i)
  let step := fun (x : W) (i : Fin k) =>
    xor (x i) (!(x (idx (i.val + 1))) && x (idx (i.val + 2)))
  let mix := fun (x : W) (i : Fin k) =>
    xor (xor (x i) (x (idx (i.val + d)))) (x (idx (i.val + k - d)))
  ∀ (feedback : W → W), (∀ x y, feedback (add x y) = add (feedback x) (feedback y)) →
  ∀ (offset base shift : W) (pinned : Finset (Fin k)) (sign : Bool),
    let observed := fun (z : W) =>
      (List.ofFn (step (mix (add (step z) (add (feedback z) offset))))).foldl xor false
    (∀ q ∈ pinned, shift q = false) →
    (∀ z : W, (∀ q ∈ pinned, z q = base q) →
      xor (observed z) (observed (add z shift)) = sign) →
    ∀ t : Fin k, shift t = true →
      (idx (t.val + k - 1) ∈ pinned ∨ idx (t.val + 2*d) ∈ pinned ∨
        idx (t.val + 2*d + 1) ∈ pinned) ∧
      (idx (t.val + 1) ∈ pinned ∨ idx (t.val + k - 2*d) ∈ pinned ∨
        idx (t.val + k - (2*d + 1)) ∈ pinned) := by
  intro k d hk hd hw W idx add step mix fb hf ofs base shift pinned sign observed _ hconst t ht
  let arc := at94 hk d
  have constraint (j p : Fin k) (hlo : arc j 0 ∉ pinned) (hhi : arc j (2*d+2) ∉ pinned)
      (hp : p ∉ pinned) :
      bit94 (dir94 p (arc j 1)) * bit94 (shift (arc j (2*d+1))) +
        bit94 (shift (arc j 1)) * bit94 (dir94 p (arc j (2*d+1))) = 0 := by
    let lo := dir94 (arc j 0)
    let hi := dir94 (arc j (2*d+2))
    let u := dir94 p
    let det := bit94 (u (arc j 1)) * bit94 (shift (arc j (2*d+1))) +
      bit94 (shift (arc j 1)) * bit94 (u (arc j (2*d+1)))
    have hval := maskedFour94 (output94 hk d fb ofs) (fun _ => true) j lo hi u shift base det
      (fun i => select94 hk d hd hw fb hf ofs j u shift base i)
    have hbit : bit94 (boolDiff94 (boolDiff94 (boolDiff94 (boolDiff94 observed lo) hi) u)
        shift base) = det := by
      change bit94 (boolDiff94 (boolDiff94 (boolDiff94 (boolDiff94 observed lo) hi) u)
        shift base) = bit94 true * det at hval
      rwa [show bit94 true = 1 by rfl, one_mul] at hval
    rw [sliceZero observed base shift lo hi u pinned sign hconst
      (unitFree hlo) (unitFree hhi) (unitFree hp)] at hbit
    exact hbit.symm
  have chooseArc (r : ℕ) (hr : k-d+2+r ≤ 2*k) : ∃ j, arc j r = t := by
    let a := t.val + 2*k - (k-d+2+r)
    refine ⟨idx94 hk a, ?_⟩
    change idx94 hk ((idx94 hk a).val + (k-d+2) + r) = t
    rw [Nat.add_assoc, idx_shift94, show a + (k-d+2+r) = t.val+k+k by dsimp [a]; omega,
      idx_wrap94, idx_wrap94]
    exact Fin.ext (Nat.mod_eq_of_lt t.isLt)
  have interior (j : Fin k) : arc j 1 ≠ arc j (2*d+1) := by
    intro h
    have he := (offEq94 hk d j (by omega : 1 < k) (by omega : 2*d+1 < k)).mp h
    omega
  constructor
  · obtain ⟨j, hj⟩ := chooseArc 1 (by omega)
    have el : idx (t.val+k-1) = arc j 0 := by
      rw [show t.val+k-1 = t.val+(k-1) by omega]
      exact relative hk j t 1 (k-1) 0 hj (Or.inr (by omega))
    have ep : idx (t.val+2*d) = arc j (2*d+1) :=
      relative hk j t 1 (2*d) (2*d+1) hj (Or.inl (by omega))
    have eh : idx (t.val+2*d+1) = arc j (2*d+2) := by
      rw [Nat.add_assoc]
      exact relative hk j t 1 (2*d+1) (2*d+2) hj (Or.inl (by omega))
    rw [el, ep, eh]
    by_contra h
    push Not at h
    have bad := constraint j _ h.1 h.2.2 h.2.1
    have hot : shift (arc j 1) = true := hj ▸ ht
    simp [dir94, interior j, hot, bit94] at bad
  · obtain ⟨j, hj⟩ := chooseArc (2*d+1) (by omega)
    have eh : idx (t.val+1) = arc j (2*d+2) :=
      relative hk j t (2*d+1) 1 (2*d+2) hj (Or.inl (by omega))
    have ep : idx (t.val+k-2*d) = arc j 1 := by
      rw [show t.val+k-2*d = t.val+(k-2*d) by omega]
      exact relative hk j t (2*d+1) (k-2*d) 1 hj (Or.inr (by omega))
    have el : idx (t.val+k-(2*d+1)) = arc j 0 := by
      rw [show t.val+k-(2*d+1) = t.val+(k-(2*d+1)) by omega]
      exact relative hk j t (2*d+1) (k-(2*d+1)) 0 hj (Or.inr (by omega))
    rw [eh, ep, el]
    by_contra h
    push Not at h
    have bad := constraint j _ h.2.2 h.1 h.2.1
    have hot : shift (arc j (2*d+1)) = true := hj ▸ ht
    simp [dir94, (interior j).symm, hot, bit94] at bad
