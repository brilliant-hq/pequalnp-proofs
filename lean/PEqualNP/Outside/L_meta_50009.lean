import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_50009

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def sig5 (b0 b1 b2 b3 b4 : Bool) : Nat :=
  (if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) +
  (if b3 then 8 else 0) + (if b4 then 16 else 0)

theorem sig5_lt (b0 b1 b2 b3 b4 : Bool) : sig5 b0 b1 b2 b3 b4 < 32 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> decide

def bit5 (v k : Nat) : Bool := (v / 2 ^ k) % 2 == 1

def not5 (a : Nat) : Nat := 31 - a

def and5 (a b : Nat) : Nat :=
  sig5 (bit5 a 0 && bit5 b 0) (bit5 a 1 && bit5 b 1) (bit5 a 2 && bit5 b 2)
    (bit5 a 3 && bit5 b 3) (bit5 a 4 && bit5 b 4)

def or5 (a b : Nat) : Nat :=
  sig5 (bit5 a 0 || bit5 b 0) (bit5 a 1 || bit5 b 1) (bit5 a 2 || bit5 b 2)
    (bit5 a 3 || bit5 b 3) (bit5 a 4 || bit5 b 4)

theorem bit5_sig5_0 (b0 b1 b2 b3 b4 : Bool) : bit5 (sig5 b0 b1 b2 b3 b4) 0 = b0 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> decide

theorem bit5_sig5_1 (b0 b1 b2 b3 b4 : Bool) : bit5 (sig5 b0 b1 b2 b3 b4) 1 = b1 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> decide

theorem bit5_sig5_2 (b0 b1 b2 b3 b4 : Bool) : bit5 (sig5 b0 b1 b2 b3 b4) 2 = b2 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> decide

theorem bit5_sig5_3 (b0 b1 b2 b3 b4 : Bool) : bit5 (sig5 b0 b1 b2 b3 b4) 3 = b3 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> decide

theorem bit5_sig5_4 (b0 b1 b2 b3 b4 : Bool) : bit5 (sig5 b0 b1 b2 b3 b4) 4 = b4 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> decide

theorem sig5_not (b0 b1 b2 b3 b4 : Bool) :
    sig5 (!b0) (!b1) (!b2) (!b3) (!b4) = not5 (sig5 b0 b1 b2 b3 b4) := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> decide

theorem sig5_and (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Bool) :
    sig5 (a0 && b0) (a1 && b1) (a2 && b2) (a3 && b3) (a4 && b4) =
      and5 (sig5 a0 a1 a2 a3 a4) (sig5 b0 b1 b2 b3 b4) := by
  unfold and5
  rw [bit5_sig5_0, bit5_sig5_1, bit5_sig5_2, bit5_sig5_3, bit5_sig5_4]
  rw [bit5_sig5_0, bit5_sig5_1, bit5_sig5_2, bit5_sig5_3, bit5_sig5_4]

theorem sig5_or (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Bool) :
    sig5 (a0 || b0) (a1 || b1) (a2 || b2) (a3 || b3) (a4 || b4) =
      or5 (sig5 a0 a1 a2 a3 a4) (sig5 b0 b1 b2 b3 b4) := by
  unfold or5
  rw [bit5_sig5_0, bit5_sig5_1, bit5_sig5_2, bit5_sig5_3, bit5_sig5_4]
  rw [bit5_sig5_0, bit5_sig5_1, bit5_sig5_2, bit5_sig5_3, bit5_sig5_4]

theorem and5_self (a : Nat) (ha : a < 32) : and5 a a = a := by
  have : ∀ x < 32, and5 x x = x := by decide
  exact this a ha

theorem or5_self (a : Nat) (ha : a < 32) : or5 a a = a := by
  have : ∀ x < 32, or5 x x = x := by decide
  exact this a ha

def hasBit (m k : Nat) : Bool := (m / 2 ^ k) % 2 == 1

def setBit (m k : Nat) : Nat := if hasBit m k then m else m + 2 ^ k

theorem hasBit_setBit_self (m k : Nat) : hasBit (setBit m k) k = true := by
  unfold setBit
  cases h : hasBit m k
  · simp only [Bool.false_eq_true, ite_false]
    unfold hasBit at h ⊢
    have hpos : 0 < 2 ^ k := Nat.pow_pos (by decide)
    rw [Nat.add_div_right _ hpos]
    have hmod : (m / 2 ^ k) % 2 < 2 := Nat.mod_lt _ (by decide)
    have hneq : (m / 2 ^ k) % 2 ≠ 1 := by
      intro eq1; rw [eq1] at h; exact Bool.noConfusion h
    rw [beq_iff_eq]
    omega
  · simp [h]

theorem hasBit_setBit_ne (m k j : Nat) (hjk : j ≠ k) : hasBit (setBit m k) j = hasBit m j := by
  unfold setBit
  cases hk : hasBit m k
  · simp only [Bool.false_eq_true, ite_false]
    rcases Nat.lt_trichotomy j k with hjk' | rfl | hkj
    · unfold hasBit
      have hk_eq : k = j + (k - j) := by omega
      have hpos : 0 < 2 ^ j := Nat.pow_pos (by decide)
      have hpow1 : 2 ^ k = 2 ^ (k - j) * 2 ^ j := by
        calc 2 ^ k = 2 ^ (j + (k - j)) := by rw [← hk_eq]
          _ = 2 ^ j * 2 ^ (k - j) := Nat.pow_add 2 j (k - j)
          _ = 2 ^ (k - j) * 2 ^ j := Nat.mul_comm _ _
      rw [hpow1, Nat.add_mul_div_right _ _ hpos]
      have hd : k - j = (k - j - 1) + 1 := by omega
      have hpow2 : 2 ^ (k - j) = 2 ^ (k - j - 1) * 2 := by
        conv_lhs => rw [hd, Nat.pow_succ]
      rw [hpow2, Nat.add_mul_mod_self_right]
    · exact False.elim (hjk rfl)
    · unfold hasBit at hk ⊢
      have hposk : 0 < 2 ^ k := Nat.pow_pos (by decide)
      have hposk1 : 0 < 2 ^ (k + 1) := Nat.pow_pos (by decide)
      have hdiv2k : (m / 2 ^ k) % 2 = 0 := by
        have hmod : (m / 2 ^ k) % 2 < 2 := Nat.mod_lt _ (by decide)
        have hneq : (m / 2 ^ k) % 2 ≠ 1 := by
          intro eq1; rw [eq1] at hk; exact Bool.noConfusion hk
        omega
      have hm_decomp : m = 2 ^ (k + 1) * (m / 2 ^ (k + 1)) + m % 2 ^ (k + 1) :=
        (Nat.div_add_mod m (2 ^ (k + 1))).symm
      have hpow : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ 2 k
      have hdiv : m / 2 ^ k = 2 * (m / 2 ^ (k + 1)) + (m % 2 ^ (k + 1)) / 2 ^ k := by
        conv_lhs => rw [hm_decomp, hpow, Nat.mul_assoc]
        rw [Nat.mul_add_div hposk, ← hpow]
      have hm_lt : m % 2 ^ (k + 1) < 2 * 2 ^ k := by
        rw [Nat.mul_comm, ← hpow]; exact Nat.mod_lt _ hposk1
      have hq_lt : (m % 2 ^ (k + 1)) / 2 ^ k < 2 :=
        (Nat.div_lt_iff_lt_mul hposk).mpr hm_lt
      have hmod0 : ((m % 2 ^ (k + 1)) / 2 ^ k) % 2 = 0 := by
        have h1 := hdiv2k; rw [hdiv, Nat.mul_add_mod] at h1; exact h1
      have hq0 : (m % 2 ^ (k + 1)) / 2 ^ k = 0 := by
        cases hq : (m % 2 ^ (k + 1)) / 2 ^ k with
        | zero => rfl
        | succ n =>
          have hn : n = 0 := by have hlt : n + 1 < 2 := hq ▸ hq_lt; omega
          subst hn
          rw [hq] at hmod0
          contradiction
      have hr_lt : m % 2 ^ (k + 1) < 2 ^ k := (Nat.div_eq_zero_iff_lt hposk).mp hq0
      have hadd_div : (m + 2 ^ k) / 2 ^ (k + 1) = m / 2 ^ (k + 1) := by
        conv_lhs => rw [hm_decomp, Nat.add_assoc]
        rw [Nat.mul_add_div hposk1]
        have hlt2 : m % 2 ^ (k + 1) + 2 ^ k < 2 ^ (k + 1) := by
          conv_rhs => rw [hpow]
          omega
        rw [Nat.div_eq_of_lt hlt2, Nat.add_zero]
      have hj_eq : j = (k + 1) + (j - k - 1) := by omega
      have hj_pow : 2 ^ j = 2 ^ (k + 1) * 2 ^ (j - k - 1) := by
        conv_lhs => rw [hj_eq, Nat.pow_add]
      rw [hj_pow, ← Nat.div_div_eq_div_mul, hadd_div, Nat.div_div_eq_div_mul]
  · simp

theorem hasBit_setBit_of (m k j : Nat) (h : hasBit m j = true) : hasBit (setBit m k) j = true := by
  by_cases hjk : j = k
  · subst hjk; exact hasBit_setBit_self m j
  · rw [hasBit_setBit_ne m k j hjk]; exact h

theorem hasBit_setBit_imp {m k j : Nat} (h : hasBit (setBit m k) j = true) : hasBit m j = true ∨ j = k := by
  by_cases hjk : j = k
  · exact Or.inr hjk
  · rw [hasBit_setBit_ne m k j hjk] at h; exact Or.inl h

theorem setBit_idem {m k : Nat} (h : hasBit m k = true) : setBit m k = m := by
  simp [setBit, h]

def elemsAux (m : Nat) : Nat → List Nat
  | 0 => []
  | k + 1 => if hasBit m k then k :: elemsAux m k else elemsAux m k

theorem elemsAux_lt (m k x : Nat) (hx : x ∈ elemsAux m k) : x < k := by
  induction k with
  | zero => cases hx
  | succ k ih =>
    unfold elemsAux at hx
    split at hx
    · rcases List.mem_cons.mp hx with rfl | hmem
      · omega
      · have := ih hmem; omega
    · have := ih hx; omega

theorem mem_elemsAux (m k v : Nat) (hv : v < k) : v ∈ elemsAux m k ↔ hasBit m v = true := by
  induction k with
  | zero => omega
  | succ k ih =>
    unfold elemsAux
    by_cases hvk : v = k
    · subst hvk
      cases hm : hasBit m v
      · simp only [Bool.false_eq_true, ite_false]
        exact ⟨fun hmem => absurd (elemsAux_lt m v v hmem) (Nat.lt_irrefl v), fun h => False.elim h⟩
      · simp
    · have hv' : v < k := by omega
      split
      · simp [List.mem_cons, hvk, ih hv']
      · exact ih hv'

def hash64 (x : Nat) : Nat := ((x * 2654435761) / 65536) % 64

def bucketMem (tbl : List (List Nat)) (x : Nat) : Bool :=
  (tbl.getD (hash64 x) []).elem x

def L1B : List (List Nat) := [
  [3506536449],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [3506503683],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [3506503689],
  [3506503809],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  []
]

def L2B : List (List Nat) := [
  [],
  [],
  [3506503693],
  [3506503873],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [3506503691],
  [3506503811],
  [],
  [],
  [3540058115, 4043374595],
  [],
  [],
  [],
  [],
  [3506503825, 3506540545],
  [],
  [],
  [],
  [],
  [3506503817],
  [],
  [],
  [3640721417],
  [3514892417],
  [],
  [],
  [],
  [],
  [],
  [],
  [3507027977],
  [3506552833],
  [],
  [3506536451],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [3506634755],
  [3506536705],
  [],
  [3506536457],
  [3506536577],
  [],
  []
]

def L3B : List (List Nat) := [
  [],
  [],
  [3573612557, 3640721421, 4043374605],
  [3510698177, 3514892481, 3540058305],
  [3507060745],
  [],
  [3506765837],
  [3507032073],
  [3506556929],
  [],
  [3506540547, 3507027981],
  [3506503827],
  [],
  [],
  [],
  [3506683905],
  [3506503819],
  [3506667523],
  [],
  [3540058123, 3640721419, 4043374603],
  [3514892419, 3540058243, 4043374723],
  [3506540801],
  [],
  [3506540553, 4076929027],
  [3506503833, 3506540673],
  [],
  [3506536461],
  [3507027979, 3640721433],
  [3506536641, 3506552835, 3514892433, 3640721553],
  [],
  [],
  [3514892673],
  [],
  [3514892425, 3640721545],
  [],
  [],
  [3507064833, 3707830281],
  [3506651139, 3519086721],
  [3506553089],
  [],
  [],
  [3506536707, 3506552841, 3507028105],
  [3506552961],
  [3506536459],
  [3506536579, 3507552401, 3641245705],
  [],
  [],
  [3540090883, 4043407363],
  [3507290121],
  [3506503695],
  [3506503875],
  [],
  [],
  [3506536593, 3506634763, 3515940993, 3540058179, 4043374599],
  [3506536713, 3506634883],
  [3506536833],
  [],
  [3506536585, 3540189187, 4043505667],
  [3514925313],
  [3506503889],
  [3640754185],
  [3514925185],
  [],
  [3506503821, 3506503881]
]

def L4B : List (List Nat) := [
  [3506655235],
  [3506548739, 3506557185, 3507032329, 3507060873],
  [3515943041, 3707830285, 4110483469, 4177592333],
  [3506765965, 3519086785, 3544252609, 3548446913, 4043374755, 4076929217],
  [3506538761, 3506540803, 3506556937, 3507032201, 3641278473],
  [3506557057, 3507585169],
  [3506540555, 3506552845, 3573874701, 3640983565, 4043636749],
  [3506503835, 3506540675, 3507028109, 3507028169, 3641249801],
  [3506553025, 3506684161, 3507322889],
  [3506536463],
  [3515973889, 3540094979, 3574136845, 3640721435, 3640756233, 3641245709, 4043411459, 4043898893],
  [3506536643, 3506667779, 3506683913, 3507294217, 3507552465, 3514892435, 3540058259, 3640721555, 4043374739],
  [3506684033],
  [3506667531, 3514892675, 3515973761, 4043407367],
  [3506667651, 3507290125, 3540090947],
  [3540238337, 4043554817],
  [3506540689, 3507081217, 3514892427, 3540058251, 3640721547, 4043374731],
  [3506540809, 3540221955, 4043538435],
  [3506540929, 3507064835],
  [3506536657, 3506634767, 3511746753, 3515941057, 3674275851, 3707830283, 3707830313, 4076929035, 4177592331],
  [3506536717, 3506540681, 3506634947, 3519086723, 3548446851, 4051763331, 4076929155],
  [3506536897, 3506553091, 3514929409],
  [3514892689],
  [3506536589, 3506552843, 3540189251, 3640758281, 4043505671],
  [3506536649, 3507028107, 3514892441, 3514929281, 3519087233, 3640721561],
  [3506552963],
  [3514892681, 3573645325, 3640754189, 4043407373],
  [3507552403, 3540582411, 3641245707, 3707830297, 4043898891],
  [3510730945, 3514925249, 3519086737, 3540091073, 3540107267, 3649110161, 3707830417, 4043423747],
  [3506503885, 3506537219, 3507065089],
  [3506798605],
  [3506651395, 3507064841, 3507290123, 3519086977],
  [3507028121, 3507064961],
  [3506552977, 3506651147, 3519086729, 3649110153, 3707830409],
  [3506553097, 3506651267, 3507060749],
  [3506553217, 3540091395, 3641245721],
  [3506536595, 3515940995, 3641282561],
  [3506536715, 3506552969, 3507032077, 3540205571, 4043522051],
  [3506536835, 3507298313, 3514941697, 4043415555],
  [],
  [3506536587, 3507326977, 3507552409],
  [3514925315, 3515416713, 3540091139, 3640770569, 3641245833, 4043407619],
  [3506503891, 3506688001, 3514941569],
  [3540090891, 3640754187, 3641770009, 4043407371],
  [3506671619, 3514925187, 3515941009, 3540091011, 3641770129, 3708354569, 4043407491],
  [3506503823, 3506634899, 3507290249, 3540058195],
  [3506503883],
  [3506536849, 3515941249, 4076961795],
  [3574398985, 3641507849],
  [3506536601, 3507077129, 3515941001, 3540058127, 3540058187, 3573612559, 3573612589, 3640721423, 4043374607],
  [3506634891, 3510698179, 3514892483, 3540058307, 4043374727, 4043374787],
  [3506536841, 3507060747],
  [3640754201],
  [3506540557, 3506765839, 3514925201, 3520135297, 3540189195, 3544252483, 3640754321, 3640852491, 4043505675, 4076929031, 4076929091, 4110483463],
  [3506503837, 3507032075, 3514925321, 3515023491, 3540189315, 3640754441, 4043505795],
  [3506503897, 3506540737, 3506556931, 3510698689, 3514925441],
  [],
  [3507027983, 3514925193, 3640721437, 3640754313, 4043636743, 4077060099],
  [3507554449, 3519119617],
  [3506503859, 3510698193, 3514892497, 3540058321, 3640721617],
  [3506774029, 3707863049],
  [3507159051, 3514892737, 3519119489],
  [3506683907, 3507061001],
  [3510698185, 3514892429, 3514892489, 3540058313, 3573612685, 3640721549, 3640721609, 4043374733]
]

def initMask : Nat := 3506503681

def noBoth (m : Nat) : Bool := !(hasBit m 18 && hasBit m 20)

def has031 (m : Nat) : Bool := hasBit m 0 && hasBit m 31

def stepOk (nextTbl : List (List Nat)) (m : Nat) : Bool :=
  noBoth m && has031 m &&
  let es := elemsAux m 32
  es.all fun a =>
    (let na := not5 a
     (hasBit m na || bucketMem nextTbl (setBit m na))) &&
    es.all fun b =>
      let aa := and5 a b
      let oo := or5 a b
      (hasBit m aa || bucketMem nextTbl (setBit m aa)) &&
      (hasBit m oo || bucketMem nextTbl (setBit m oo))

def checkL0 : Bool := stepOk L1B initMask
def checkL1 : Bool := L1B.all fun b => b.all (stepOk L2B)
def checkL2 : Bool := L2B.all fun b => b.all (stepOk L3B)
def checkL3 : Bool := L3B.all fun b => b.all (stepOk L4B)

def checkL4 : Bool := L4B.all fun b => b.all fun m =>
  noBoth m && has031 m &&
  (if hasBit m 18 then
     let es := elemsAux m 32
     es.all fun a =>
       (not5 a != 20) &&
       es.all fun x => (and5 a x != 20) && (or5 a x != 20)
   else true) &&
  (if hasBit m 20 then
     let es := elemsAux m 32
     es.all fun a =>
       (not5 a != 18) &&
       es.all fun x => (and5 a x != 18) && (or5 a x != 18)
   else true)

theorem ok0 : checkL0 = true := by decide
theorem ok1 : checkL1 = true := by decide
theorem ok2 : checkL2 = true := by decide
theorem ok3 : checkL3 = true := by decide
theorem ok4 : checkL4 = true := by decide

theorem mem_of_elem_eq_true {l : List Nat} {x : Nat} (h : l.elem x = true) : x ∈ l := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
    by_cases hxy : x = y
    · subst hxy; exact List.mem_cons_self
    · have hb : (x == y) = false := beq_false_of_ne hxy
      simp only [List.elem_cons, hb] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem bucketMem_all {tbl : List (List Nat)} {p : Nat → Bool}
    (hp : tbl.all (fun b => b.all p) = true) {m : Nat} (hm : bucketMem tbl m = true) :
    p m = true := by
  unfold bucketMem at hm
  have h1 : (tbl.getD (hash64 m) []).all p = true := by
    rw [List.all_eq_true] at hp
    cases hg : tbl[hash64 m]? with
    | none => simp [List.getD, hg]
    | some b =>
      have hb : b ∈ tbl := List.mem_of_getElem? hg
      simpa [List.getD, hg] using hp b hb
  rw [List.all_eq_true] at h1
  exact h1 m (mem_of_elem_eq_true hm)

def InLayer : Nat → Nat → Bool
  | 0, m => m == initMask
  | 1, m => bucketMem L1B m
  | 2, m => bucketMem L2B m
  | 3, m => bucketMem L3B m
  | 4, m => bucketMem L4B m
  | _, _ => false

theorem stepOk_sound {tbl : List (List Nat)} {m v : Nat} (hs : stepOk tbl m = true)
    (hv : (∃ a, a < 32 ∧ hasBit m a = true ∧ v = not5 a) ∨
      (∃ a b, a < 32 ∧ b < 32 ∧ hasBit m a = true ∧ hasBit m b = true ∧ (v = and5 a b ∨ v = or5 a b))) :
    hasBit m v = true ∨ bucketMem tbl (setBit m v) = true := by
  unfold stepOk at hs
  simp only [Bool.and_eq_true] at hs
  have hall := hs.2
  rw [List.all_eq_true] at hall
  rcases hv with ⟨a, ha32, hma, rfl⟩ | ⟨a, b, ha32, hb32, hma, hmb, rfl | rfl⟩
  · have ha_mem : a ∈ elemsAux m 32 := (mem_elemsAux m 32 a ha32).mpr hma
    have hres := hall a ha_mem
    simp only [Bool.and_eq_true, Bool.or_eq_true] at hres
    exact hres.1
  · have ha_mem : a ∈ elemsAux m 32 := (mem_elemsAux m 32 a ha32).mpr hma
    have hb_mem : b ∈ elemsAux m 32 := (mem_elemsAux m 32 b hb32).mpr hmb
    have hres := hall a ha_mem
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at hres
    exact (hres.2 b hb_mem).1
  · have ha_mem : a ∈ elemsAux m 32 := (mem_elemsAux m 32 a ha32).mpr hma
    have hb_mem : b ∈ elemsAux m 32 := (mem_elemsAux m 32 b hb32).mpr hmb
    have hres := hall a ha_mem
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at hres
    exact (hres.2 b hb_mem).2

theorem inLayer_props (k m : Nat) (hm : InLayer k m = true) : noBoth m = true ∧ has031 m = true := by
  rcases k with _ | _ | _ | _ | _ | k
  · simp [InLayer] at hm; subst hm; decide
  · have hs := bucketMem_all ok1 hm
    unfold stepOk at hs; simp only [Bool.and_eq_true] at hs; exact hs.1
  · have hs := bucketMem_all ok2 hm
    unfold stepOk at hs; simp only [Bool.and_eq_true] at hs; exact hs.1
  · have hs := bucketMem_all ok3 hm
    unfold stepOk at hs; simp only [Bool.and_eq_true] at hs; exact hs.1
  · have hs := bucketMem_all ok4 hm
    simp only [Bool.and_eq_true] at hs; exact hs.1.1
  · simp [InLayer] at hm

theorem inLayer_step {j m v : Nat} (hj : j < 4) (hm : InLayer j m = true)
    (hv : (∃ a, a < 32 ∧ hasBit m a = true ∧ v = not5 a) ∨
      (∃ a b, a < 32 ∧ b < 32 ∧ hasBit m a = true ∧ hasBit m b = true ∧ (v = and5 a b ∨ v = or5 a b))) :
    InLayer j (setBit m v) = true ∨ InLayer (j + 1) (setBit m v) = true := by
  have hs : stepOk (match j with | 0 => L1B | 1 => L2B | 2 => L3B | _ => L4B) m = true := by
    rcases j with _ | _ | _ | _ | j
    · simp [InLayer] at hm; subst hm; exact ok0
    · exact bucketMem_all ok1 hm
    · exact bucketMem_all ok2 hm
    · exact bucketMem_all ok3 hm
    · omega
  rcases stepOk_sound hs hv with hmem | hnext
  · left; rw [setBit_idem hmem]; exact hm
  · right
    rcases j with _ | _ | _ | _ | j
    · exact hnext
    · exact hnext
    · exact hnext
    · exact hnext
    · omega

theorem inLayer4_step {m v : Nat} (hm : InLayer 4 m = true)
    (hv : (∃ a, a < 32 ∧ hasBit m a = true ∧ v = not5 a) ∨
      (∃ a b, a < 32 ∧ b < 32 ∧ hasBit m a = true ∧ hasBit m b = true ∧ (v = and5 a b ∨ v = or5 a b))) :
    noBoth (setBit m v) = true := by
  have hc := bucketMem_all ok4 hm
  simp only [Bool.and_eq_true] at hc
  rcases hc with ⟨⟨⟨hnb, _⟩, h18⟩, h20⟩
  by_contra hbad
  have hnbF : noBoth (setBit m v) = false := by cases h : noBoth (setBit m v) <;> simp_all
  unfold noBoth at hnbF
  simp only [Bool.not_eq_false', Bool.and_eq_true] at hnbF
  rcases hasBit_setBit_imp hnbF.1 with hm18 | rfl
  · rcases hasBit_setBit_imp hnbF.2 with hm20 | hv20
    · have h1820 : ¬ (hasBit m 18 = true ∧ hasBit m 20 = true) := by
        intro ⟨h1, h2⟩; simp [noBoth, h1, h2] at hnb
      exact h1820 ⟨hm18, hm20⟩
    · subst hv20
      simp only [hm18, ↓reduceIte, List.all_eq_true, Bool.and_eq_true, bne_iff_ne] at h18
      rcases hv with ⟨a, ha32, hma, hveq⟩ | ⟨a, b, ha32, hb32, hma, hmb, hveq | hveq⟩
      · have ha_mem : a ∈ elemsAux m 32 := (mem_elemsAux m 32 a ha32).mpr hma
        exact (h18 a ha_mem).1 hveq.symm
      · have ha_mem : a ∈ elemsAux m 32 := (mem_elemsAux m 32 a ha32).mpr hma
        have hb_mem : b ∈ elemsAux m 32 := (mem_elemsAux m 32 b hb32).mpr hmb
        exact ((h18 a ha_mem).2 b hb_mem).1 hveq.symm
      · have ha_mem : a ∈ elemsAux m 32 := (mem_elemsAux m 32 a ha32).mpr hma
        have hb_mem : b ∈ elemsAux m 32 := (mem_elemsAux m 32 b hb32).mpr hmb
        exact ((h18 a ha_mem).2 b hb_mem).2 hveq.symm
  · rcases hasBit_setBit_imp hnbF.2 with hm20 | h1820
    · simp only [hm20, ↓reduceIte, List.all_eq_true, Bool.and_eq_true, bne_iff_ne] at h20
      rcases hv with ⟨a, ha32, hma, hveq⟩ | ⟨a, b, ha32, hb32, hma, hmb, hveq | hveq⟩
      · have ha_mem : a ∈ elemsAux m 32 := (mem_elemsAux m 32 a ha32).mpr hma
        exact (h20 a ha_mem).1 hveq.symm
      · have ha_mem : a ∈ elemsAux m 32 := (mem_elemsAux m 32 a ha32).mpr hma
        have hb_mem : b ∈ elemsAux m 32 := (mem_elemsAux m 32 b hb32).mpr hmb
        exact ((h20 a ha_mem).2 b hb_mem).1 hveq.symm
      · have ha_mem : a ∈ elemsAux m 32 := (mem_elemsAux m 32 a ha32).mpr hma
        have hb_mem : b ∈ elemsAux m 32 := (mem_elemsAux m 32 b hb32).mpr hmb
        exact ((h20 a ha_mem).2 b hb_mem).2 hveq.symm
    · omega

def ValidAt : Nat → Nat → Prop
  | 0, m => InLayer 0 m = true
  | 1, m => ∃ j ≤ 1, InLayer j m = true
  | 2, m => ∃ j ≤ 2, InLayer j m = true
  | 3, m => ∃ j ≤ 3, InLayer j m = true
  | 4, m => ∃ j ≤ 4, InLayer j m = true
  | _, m => noBoth m = true

theorem validAt_noBoth (k m : Nat) (hk : k ≤ 5) (hv : ValidAt k m) : noBoth m = true := by
  rcases k with _ | _ | _ | _ | _ | _ | k
  · exact (inLayer_props 0 m hv).1
  · obtain ⟨j, _, hj⟩ := hv; exact (inLayer_props j m hj).1
  · obtain ⟨j, _, hj⟩ := hv; exact (inLayer_props j m hj).1
  · obtain ⟨j, _, hj⟩ := hv; exact (inLayer_props j m hj).1
  · obtain ⟨j, _, hj⟩ := hv; exact (inLayer_props j m hj).1
  · exact hv
  · omega

theorem validAt_has031 (k m : Nat) (hk : k ≤ 4) (hv : ValidAt k m) : has031 m = true := by
  rcases k with _ | _ | _ | _ | _ | k
  · exact (inLayer_props 0 m hv).2
  · obtain ⟨j, _, hj⟩ := hv; exact (inLayer_props j m hj).2
  · obtain ⟨j, _, hj⟩ := hv; exact (inLayer_props j m hj).2
  · obtain ⟨j, _, hj⟩ := hv; exact (inLayer_props j m hj).2
  · obtain ⟨j, _, hj⟩ := hv; exact (inLayer_props j m hj).2
  · omega

theorem validAt_step (k m v : Nat) (hk : k < 5) (hm : ValidAt k m)
    (hv : (∃ a, a < 32 ∧ hasBit m a = true ∧ v = not5 a) ∨
      (∃ a b, a < 32 ∧ b < 32 ∧ hasBit m a = true ∧ hasBit m b = true ∧ (v = and5 a b ∨ v = or5 a b))) :
    ValidAt (k + 1) (setBit m v) := by
  rcases k with _ | _ | _ | _ | _ | k
  · rcases inLayer_step (by omega) hm hv with h | h
    · exact ⟨0, by omega, h⟩
    · exact ⟨1, by omega, h⟩
  · obtain ⟨j, hj1, hj⟩ := hm
    rcases inLayer_step (by omega) hj hv with h | h
    · exact ⟨j, by omega, h⟩
    · exact ⟨j + 1, by omega, h⟩
  · obtain ⟨j, hj2, hj⟩ := hm
    rcases inLayer_step (by omega) hj hv with h | h
    · exact ⟨j, by omega, h⟩
    · exact ⟨j + 1, by omega, h⟩
  · obtain ⟨j, hj3, hj⟩ := hm
    rcases inLayer_step (by omega) hj hv with h | h
    · exact ⟨j, by omega, h⟩
    · exact ⟨j + 1, by omega, h⟩
  · obtain ⟨j, hj4, hj⟩ := hm
    by_cases hjlt : j < 4
    · rcases inLayer_step hjlt hj hv with h | h
      · exact (inLayer_props j _ h).1
      · exact (inLayer_props (j + 1) _ h).1
    · have hj4eq : j = 4 := by omega
      subst hj4eq
      exact inLayer4_step hj hv
  · omega

def xsAt (t : Nat) : List Bool :=
  (List.ofFn (fun i : Fin 4 => decide (i.val < t))) ++ [false, true]

def stepWires (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Covers (m : Nat) (w0 w1 w2 w3 w4 : List Bool) : Prop :=
  ∀ i : Nat, hasBit m (sig5 (w0.getD i false) (w1.getD i false) (w2.getD i false) (w3.getD i false) (w4.getD i false)) = true

theorem covers_init : Covers initMask (xsAt 0) (xsAt 1) (xsAt 2) (xsAt 3) (xsAt 4) := by
  intro i
  rcases i with _ | _ | _ | _ | _ | _ | i
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [xsAt, initMask, hasBit, sig5]

theorem gate_sig_reach (m : Nat) (hm031 : has031 m = true) (w0 w1 w2 w3 w4 : List Bool)
    (hcov : Covers m w0 w1 w2 w3 w4) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    let v := sig5
      (g.op.eval (g.inputs.map fun i => w0.getD i false))
      (g.op.eval (g.inputs.map fun i => w1.getD i false))
      (g.op.eval (g.inputs.map fun i => w2.getD i false))
      (g.op.eval (g.inputs.map fun i => w3.getD i false))
      (g.op.eval (g.inputs.map fun i => w4.getD i false))
    (∃ a, a < 32 ∧ hasBit m a = true ∧ v = not5 a) ∨
      (∃ a b, a < 32 ∧ b < 32 ∧ hasBit m a = true ∧ hasBit m b = true ∧ (v = and5 a b ∨ v = or5 a b)) := by
  dsimp only
  unfold has031 at hm031
  simp only [Bool.and_eq_true] at hm031
  obtain ⟨hm0, hm31⟩ := hm031
  obtain ⟨hop, hlen⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases g with ⟨op, ins⟩
  dsimp only at hop hlen ⊢
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ins'⟩⟩
  · rcases hop with rfl | rfl | rfl
    · right; refine ⟨31, 31, by omega, by omega, hm31, hm31, Or.inl ?_⟩
      simp [GateOp.eval, sig5, and5, bit5]
    · right; refine ⟨0, 0, by omega, by omega, hm0, hm0, Or.inr ?_⟩
      simp [GateOp.eval, sig5, or5, bit5]
    · left; refine ⟨0, by omega, hm0, ?_⟩
      simp [GateOp.eval, sig5, not5]
  · let a := sig5 (w0.getD i false) (w1.getD i false) (w2.getD i false) (w3.getD i false) (w4.getD i false)
    have ha32 : a < 32 := sig5_lt _ _ _ _ _
    have hma : hasBit m a = true := hcov i
    rcases hop with rfl | rfl | rfl
    · right; refine ⟨a, a, ha32, ha32, hma, hma, Or.inl ?_⟩
      simpa [GateOp.eval, a] using (and5_self a ha32).symm
    · right; refine ⟨a, a, ha32, ha32, hma, hma, Or.inr ?_⟩
      simpa [GateOp.eval, a] using (or5_self a ha32).symm
    · left; refine ⟨a, ha32, hma, ?_⟩
      simpa [GateOp.eval, a] using sig5_not _ _ _ _ _
  · let a := sig5 (w0.getD i false) (w1.getD i false) (w2.getD i false) (w3.getD i false) (w4.getD i false)
    let b := sig5 (w0.getD j false) (w1.getD j false) (w2.getD j false) (w3.getD j false) (w4.getD j false)
    have ha32 : a < 32 := sig5_lt _ _ _ _ _
    have hb32 : b < 32 := sig5_lt _ _ _ _ _
    have hma : hasBit m a = true := hcov i
    have hmb : hasBit m b = true := hcov j
    rcases hop with rfl | rfl | rfl
    · right; refine ⟨a, b, ha32, hb32, hma, hmb, Or.inl ?_⟩
      simpa [GateOp.eval, a, b] using sig5_and _ _ _ _ _ _ _ _ _ _
    · right; refine ⟨a, b, ha32, hb32, hma, hmb, Or.inr ?_⟩
      simpa [GateOp.eval, a, b] using sig5_or _ _ _ _ _ _ _ _ _ _
    · left; refine ⟨a, ha32, hma, ?_⟩
      simpa [GateOp.eval, a] using sig5_not _ _ _ _ _
  · simp at hlen

theorem getD_stepWires (w : List Bool) (g : Gate) (L : Nat) (hL : w.length = L) (i : Nat) :
    (stepWires w g).getD i false =
      if i < L then w.getD i false
      else if i = L then g.op.eval (g.inputs.map fun idx => w.getD idx false)
      else false := by
  unfold stepWires
  rw [List.getD_eq_getElem?_getD]
  split_ifs with hlt heq
  · have hlt' : i < w.length := hL ▸ hlt
    rw [List.getElem?_append_left hlt']
    rw [List.getD_eq_getElem?_getD]
  · subst heq; subst hL
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  · have hge : w.length + 1 ≤ i := by omega
    have hlen : (w ++ [g.op.eval (g.inputs.map fun idx => w.getD idx false)]).length ≤ i := by
      simp [hge]
    rw [List.getElem?_eq_none hlen]
    rfl

theorem covers_step (m : Nat) (hm031 : has031 m = true) (w0 w1 w2 w3 w4 : List Bool)
    (L : Nat) (hl0 : w0.length = L) (hl1 : w1.length = L) (hl2 : w2.length = L)
    (hl3 : w3.length = L) (hl4 : w4.length = L)
    (hcov : Covers m w0 w1 w2 w3 w4) (g : Gate) :
    let v := sig5
      (g.op.eval (g.inputs.map fun idx => w0.getD idx false))
      (g.op.eval (g.inputs.map fun idx => w1.getD idx false))
      (g.op.eval (g.inputs.map fun idx => w2.getD idx false))
      (g.op.eval (g.inputs.map fun idx => w3.getD idx false))
      (g.op.eval (g.inputs.map fun idx => w4.getD idx false))
    Covers (setBit m v) (stepWires w0 g) (stepWires w1 g) (stepWires w2 g) (stepWires w3 g) (stepWires w4 g) := by
  intro v i
  rw [getD_stepWires w0 g L hl0 i, getD_stepWires w1 g L hl1 i,
      getD_stepWires w2 g L hl2 i, getD_stepWires w3 g L hl3 i,
      getD_stepWires w4 g L hl4 i]
  split_ifs with hlt heq
  · exact hasBit_setBit_of m v _ (hcov i)
  · exact hasBit_setBit_self m v
  · unfold has031 at hm031
    simp only [Bool.and_eq_true] at hm031
    simpa [sig5] using hasBit_setBit_of m v 0 hm031.1

theorem fold_reach (gs : List Gate) (k m L : Nat) (hk : k + gs.length ≤ 5)
    (hvalid : ValidAt k m)
    (w0 w1 w2 w3 w4 : List Bool)
    (hl0 : w0.length = L) (hl1 : w1.length = L) (hl2 : w2.length = L)
    (hl3 : w3.length = L) (hl4 : w4.length = L)
    (hcov : Covers m w0 w1 w2 w3 w4)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∃ m', ValidAt (k + gs.length) m' ∧
      Covers m' (gs.foldl stepWires w0) (gs.foldl stepWires w1) (gs.foldl stepWires w2)
        (gs.foldl stepWires w3) (gs.foldl stepWires w4) := by
  induction gs generalizing k m L w0 w1 w2 w3 w4 with
  | nil => exact ⟨m, hvalid, hcov⟩
  | cons g gs ih =>
    simp only [List.length_cons] at hk
    have hk4 : k ≤ 4 := by omega
    have hm031 : has031 m = true := validAt_has031 k m hk4 hvalid
    have hg := hfan g List.mem_cons_self
    have hreach := gate_sig_reach m hm031 w0 w1 w2 w3 w4 hcov g hg
    let v := sig5
      (g.op.eval (g.inputs.map fun idx => w0.getD idx false))
      (g.op.eval (g.inputs.map fun idx => w1.getD idx false))
      (g.op.eval (g.inputs.map fun idx => w2.getD idx false))
      (g.op.eval (g.inputs.map fun idx => w3.getD idx false))
      (g.op.eval (g.inputs.map fun idx => w4.getD idx false))
    have hvalid' : ValidAt (k + 1) (setBit m v) := validAt_step k m v (by omega) hvalid hreach
    have hcov' : Covers (setBit m v) (stepWires w0 g) (stepWires w1 g) (stepWires w2 g)
        (stepWires w3 g) (stepWires w4 g) :=
      covers_step m hm031 w0 w1 w2 w3 w4 L hl0 hl1 hl2 hl3 hl4 hcov g
    have hsl0 : (stepWires w0 g).length = L + 1 := by simp [stepWires, hl0]
    have hsl1 : (stepWires w1 g).length = L + 1 := by simp [stepWires, hl1]
    have hsl2 : (stepWires w2 g).length = L + 1 := by simp [stepWires, hl2]
    have hsl3 : (stepWires w3 g).length = L + 1 := by simp [stepWires, hl3]
    have hsl4 : (stepWires w4 g).length = L + 1 := by simp [stepWires, hl4]
    have hfan' : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg')
    obtain ⟨m', hm'⟩ := ih (k + 1) (setBit m v) (L + 1) (by omega) hvalid'
      (stepWires w0 g) (stepWires w1 g) (stepWires w2 g) (stepWires w3 g) (stepWires w4 g)
      hsl0 hsl1 hsl2 hsl3 hsl4 hcov' hfan'
    have heq : k + 1 + gs.length = k + (gs.length + 1) := by omega
    refine ⟨m', ?_, hm'.2⟩
    simp only [List.length_cons]
    rw [← heq]
    exact hm'.1

theorem validAt_init : ValidAt 0 initMask := by simp [ValidAt, InLayer]

theorem wires_eq_foldl (D : Circuit) (xs : List Bool) :
    D.wires xs = D.gates.foldl stepWires xs := rfl

end PEqualNP.Outside.L_meta_50009

theorem PEqualNP.Outside.L_meta_50009 : (¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (6+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 6 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
  ∀ t : Fin 5,
    let xs := (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (4 : Nat).testBit t.val ∧
    w.getD q.val false = (18 : Nat).testBit t.val ∧
    w.getD r.val false = (20 : Nat).testBit t.val)) := by
  rintro ⟨D, p, q, r, hfan, _, _, hsize, hvals⟩
  have hl0 : (PEqualNP.Outside.L_meta_50009.xsAt 0).length = 6 := by decide
  have hl1 : (PEqualNP.Outside.L_meta_50009.xsAt 1).length = 6 := by decide
  have hl2 : (PEqualNP.Outside.L_meta_50009.xsAt 2).length = 6 := by decide
  have hl3 : (PEqualNP.Outside.L_meta_50009.xsAt 3).length = 6 := by decide
  have hl4 : (PEqualNP.Outside.L_meta_50009.xsAt 4).length = 6 := by decide
  have hlen : D.gates.length ≤ 5 := hsize
  obtain ⟨m', hvalid', hcov'⟩ := PEqualNP.Outside.L_meta_50009.fold_reach
    D.gates 0 PEqualNP.Outside.L_meta_50009.initMask 6 (by simpa using hlen)
    PEqualNP.Outside.L_meta_50009.validAt_init
    (PEqualNP.Outside.L_meta_50009.xsAt 0)
    (PEqualNP.Outside.L_meta_50009.xsAt 1)
    (PEqualNP.Outside.L_meta_50009.xsAt 2)
    (PEqualNP.Outside.L_meta_50009.xsAt 3)
    (PEqualNP.Outside.L_meta_50009.xsAt 4)
    hl0 hl1 hl2 hl3 hl4
    PEqualNP.Outside.L_meta_50009.covers_init
    hfan
  have hnb : PEqualNP.Outside.L_meta_50009.noBoth m' = true :=
    PEqualNP.Outside.L_meta_50009.validAt_noBoth D.gates.length m' hlen (by simpa using hvalid')
  have hq0 := (hvals 0).2.1
  have hq1 := (hvals 1).2.1
  have hq2 := (hvals 2).2.1
  have hq3 := (hvals 3).2.1
  have hq4 := (hvals 4).2.1
  have hr0 := (hvals 0).2.2
  have hr1 := (hvals 1).2.2
  have hr2 := (hvals 2).2.2
  have hr3 := (hvals 3).2.2
  have hr4 := (hvals 4).2.2
  have hm18 : PEqualNP.Outside.L_meta_50009.hasBit m' 18 = true := by
    have hcovq := hcov' q.val
    have hq0' : (D.wires (PEqualNP.Outside.L_meta_50009.xsAt 0)).getD q.val false = false := by
      have h : (D.wires (PEqualNP.Outside.L_meta_50009.xsAt 0)).getD q.val false = (18 : Nat).testBit 0 := by
        simpa [PEqualNP.Outside.L_meta_50009.xsAt] using hq0
      rw [h]; decide
    have hq1' : (D.wires (PEqualNP.Outside.L_meta_50009.xsAt 1)).getD q.val false = true := by
      have h : (D.wires (PEqualNP.Outside.L_meta_50009.xsAt 1)).getD q.val false = (18 : Nat).testBit 1 := by
        simpa [PEqualNP.Outside.L_meta_50009.xsAt] using hq1
      rw [h]; decide
    have hq2' : (D.wires (PEqualNP.Outside.L_meta_50009.xsAt 2)).getD q.val false = false := by
      have h : (D.wires (PEqualNP.Outside.L_meta_50009.xsAt 2)).getD q.val false = (18 : Nat).testBit 2 := by
        simpa [PEqualNP.Outside.L_meta_50009.xsAt] using hq2
      rw [h]; decide
    have hq3' : (D.wires (PEqualNP.Outside.L_meta_50009.xsAt 3)).getD q.val false = false := by
      have h : (D.wires (PEqualNP.Outside.L_meta_50009.xsAt 3)).getD q.val false = (18 : Nat).testBit 3 := by
        simpa [PEqualNP.Outside.L_meta_50009.xsAt] using hq3
      rw [h]; decide
    have hq4' : (D.wires (PEqualNP.Outside.L_meta_50009.xsAt 4)).getD q.val false = true := by
      have h : (D.wires (PEqualNP.Outside.L_meta_50009.xsAt 4)).getD q.val false = (18 : Nat).testBit 4 := by
        simpa [PEqualNP.Outside.L_meta_50009.xsAt] using hq4
      rw [h]; decide
    simp only [PEqualNP.Outside.L_meta_50009.wires_eq_foldl] at hq0' hq1' hq2' hq3' hq4'
    rw [hq0', hq1', hq2', hq3', hq4'] at hcovq
    simpa [PEqualNP.Outside.L_meta_50009.sig5] using hcovq
  have hm20 : PEqualNP.Outside.L_meta_50009.hasBit m' 20 = true := by
    have hcovr := hcov' r.val
    have hr0' : (D.wires (PEqualNP.Outside.L_meta_50009.xsAt 0)).getD r.val false = false := by
      have h : (D.wires (PEqualNP.Outside.L_meta_50009.xsAt 0)).getD r.val false = (20 : Nat).testBit 0 := by
        simpa [PEqualNP.Outside.L_meta_50009.xsAt] using hr0
      rw [h]; decide
    have hr1' : (D.wires (PEqualNP.Outside.L_meta_50009.xsAt 1)).getD r.val false = false := by
      have h : (D.wires (PEqualNP.Outside.L_meta_50009.xsAt 1)).getD r.val false = (20 : Nat).testBit 1 := by
        simpa [PEqualNP.Outside.L_meta_50009.xsAt] using hr1
      rw [h]; decide
    have hr2' : (D.wires (PEqualNP.Outside.L_meta_50009.xsAt 2)).getD r.val false = true := by
      have h : (D.wires (PEqualNP.Outside.L_meta_50009.xsAt 2)).getD r.val false = (20 : Nat).testBit 2 := by
        simpa [PEqualNP.Outside.L_meta_50009.xsAt] using hr2
      rw [h]; decide
    have hr3' : (D.wires (PEqualNP.Outside.L_meta_50009.xsAt 3)).getD r.val false = false := by
      have h : (D.wires (PEqualNP.Outside.L_meta_50009.xsAt 3)).getD r.val false = (20 : Nat).testBit 3 := by
        simpa [PEqualNP.Outside.L_meta_50009.xsAt] using hr3
      rw [h]; decide
    have hr4' : (D.wires (PEqualNP.Outside.L_meta_50009.xsAt 4)).getD r.val false = true := by
      have h : (D.wires (PEqualNP.Outside.L_meta_50009.xsAt 4)).getD r.val false = (20 : Nat).testBit 4 := by
        simpa [PEqualNP.Outside.L_meta_50009.xsAt] using hr4
      rw [h]; decide
    simp only [PEqualNP.Outside.L_meta_50009.wires_eq_foldl] at hr0' hr1' hr2' hr3' hr4'
    rw [hr0', hr1', hr2', hr3', hr4'] at hcovr
    simpa [PEqualNP.Outside.L_meta_50009.sig5] using hcovr
  simp [PEqualNP.Outside.L_meta_50009.noBoth, hm18, hm20] at hnb
