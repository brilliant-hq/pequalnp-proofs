import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_52558_aux
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
def mask256:Nat:=2 ^ 256 - 1
def negD (d w:Nat):Nat:=(w^^^mask256)&&&d
def andD (d a b:Nat):Nat:=(a&&&b)&&&d
def orD (d a b:Nat):Nat:=(a|||b)&&&d
def opD (d:Nat) (op:Nat) (a b:Nat):Nat :=
  if op==0 then andD d a b
  else if op==1 then orD d a b
  else if op==2 then andD d a (negD d b)
  else andD d (negD d a) b
def allowedB (u:Bool) (op:Nat):Bool :=
  decide (op < 2)||(u&&decide (op < 4))
def flipOp (op:Nat):Nat :=
  if op==2 then 3 else if op==3 then 2 else op
def nrmD (u:Bool) (d w:Nat):Nat :=
  if u&&w.testBit 0 then negD d w else w&&&d
def kept {α : Type} (b:Bool) (x : α) (xs:List α):List α :=
  if b then x :: xs else xs
def RunD (u:Bool) (d y:Nat) (t : ℕ) (ws:List Nat) : Prop :=
  ∀ P : ℕ → List Nat → Prop,P 0 [y] →
    (∀ {s xs zs},List.Perm xs zs → P s xs → P s zs) →
    (∀ {s a b r} (op:Nat) (ka kb:Bool),
      allowedB u op = true →
      opD d op a b ≠ 0 →
      opD d op a b ≠ d →
      opD d op a b ∉ (a :: b :: r) →
      P s (opD d op a b :: kept ka a (kept kb b r)) →
      P (s + 1) (a :: b :: r)) → P t ws
section
variable {u:Bool} {d y:Nat}
theorem Run.done : RunD u d y 0 [y]:=fun _ dn _ _=>dn
theorem Run.perm {s xs zs} (p : List.Perm xs zs) (h : RunD u d y s xs) :
    RunD u d y s zs:=fun P dn q b=>q p (h P dn q b)
theorem Run.two {s a b r} (op:Nat) (ka kb:Bool)
    (hop : allowedB u op = true)
    (h0 : opD d op a b ≠ 0) (hd : opD d op a b ≠ d) (hm : opD d op a b ∉ (a :: b :: r))
    (h : RunD u d y s (opD d op a b :: kept ka a (kept kb b r))) :
    RunD u d y (s + 1) (a :: b :: r):=fun P dn q v=>v op ka kb hop h0 hd hm (h P dn q v)
theorem Run.fold {P : ∀ t ws,RunD u d y t ws → Prop}
    (done : P 0 [y] Run.done)
    (perm : ∀ {s xs zs} (hp : List.Perm xs zs) (h : RunD u d y s xs),
      P s xs h → P s zs (Run.perm hp h))
    (two : ∀ {s a b r} (op:Nat) (ka kb:Bool)
      (hop : allowedB u op = true)
      (h0 : opD d op a b ≠ 0) (hd : opD d op a b ≠ d) (hm : opD d op a b ∉ (a :: b :: r))
      (h : RunD u d y s (opD d op a b :: kept ka a (kept kb b r))),
      P _ _ h → P _ _ (Run.two op ka kb hop h0 hd hm h))
    {t ws} (h : RunD u d y t ws) : P t ws h:=by
  have hex:=h (fun s xs=>∃ h' : RunD u d y s xs,P s xs h')
    ⟨Run.done,done⟩
    (fun hp ⟨h',ih⟩=>⟨Run.perm hp h',perm hp h' ih⟩)
    (fun op ka kb hop h0 hd hm ⟨h',ih⟩=>⟨Run.two op ka kb hop h0 hd hm h',two op ka kb hop h0 hd hm h' ih⟩)
  exact hex.elim fun _ hp=>hp
end
theorem allowed_cases {u:Bool} {op:Nat} (h : allowedB u op = true) :
    op = 0 ∨ op = 1 ∨ (u = true ∧ op = 2) ∨ (u = true ∧ op = 3):=by
  simp only [allowedB,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at h
  rcases h with h | ⟨hu,h⟩
  · omega
  · have : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3:=by omega
    rcases this with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl ⟨hu,rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hu,rfl⟩))
theorem opD_comm {u:Bool} (d:Nat) {op:Nat} (hop : allowedB u op = true) (a b:Nat) :
    opD d op a b = opD d (flipOp op) b a:=by
  rcases allowed_cases hop with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;>
    simp [opD,flipOp,andD,orD,Nat.and_comm,Nat.or_comm]
theorem flipOp_allowed {u:Bool} {op:Nat} (hop : allowedB u op = true) :
    allowedB u (flipOp op) = true:=by
  rcases allowed_cases hop with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [allowedB,flipOp]
theorem kept_map {α β : Type} (e : α → β) (b:Bool) (x : α) (xs:List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e):=by cases b <;> simp [kept]
theorem mem_kept {α : Type} (b:Bool) (x a : α) (xs:List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs:=by cases b <;> simp [kept]
theorem nodup_kept {α : Type} (b:Bool) (x : α) (xs:List α) (h : xs.Nodup) (hx : x ∉ xs) :
    (kept b x xs).Nodup:=by
  cases b
  · simpa [kept] using h
  · simpa [kept] using And.intro hx h
theorem keep_perm {α : Type} {xs ys:List α} (p : xs.Perm ys) (b:Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys):=by cases b <;> simpa [kept] using p
theorem run_len {u d y s xs} (h : RunD u d y s xs) :
    xs.length ≤ s + 1:=by
  induction h using Run.fold with
  | done=>simp
  | perm hp _ ih=>rwa [← hp.length_eq]
  | two _ ka kb _ _ _ _ _ ih=>cases ka <;> cases kb <;> simp_all [kept] <;> omega
theorem zero_done {u d y t ws} (h : RunD u d y t ws) :
    t = 0 → ws = [y]:=by
  induction h using Run.fold with
  | done=>simp
  | perm p _ ih=>intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | two=>simp
def IsConst (d w:Nat) : Prop:=(w&&&d) = 0 ∨ (w&&&d) = d
def isConstB (d w:Nat):Bool:=(w&&&d==0)||(w&&&d==d)
theorem isConstB_iff (d w:Nat) : isConstB d w = true ↔ IsConst d w:=by
  simp [isConstB,IsConst]
def Avail (u:Bool) (d:Nat) (bank:List Nat) (w:Nat) : Prop :=
  IsConst d w ∨ (∃ v ∈ bank,(v&&&d) = (w&&&d)) ∨ (u = true ∧ ∃ v ∈ bank,(v&&&d) = negD d w)
def availB (u:Bool) (d:Nat) (bank:List Nat) (w:Nat):Bool :=
  let m:=w&&&d
  m==0||m==d||bank.any (fun v=>(v&&&d)==m) ||
    (u&&bank.any (fun v=>(v&&&d)==negD d w))
theorem availB_iff (u:Bool) (d:Nat) (bank:List Nat) (w:Nat) :
    availB u d bank w = true ↔ Avail u d bank w:=by
  simp [availB,Avail,IsConst,or_assoc]
def NatReach (u:Bool) (d:Nat) (roots:List Nat):Nat → List Nat → Prop
  | 0,bank=>bank = roots
  | p + 1,bank =>
    ∃ b a c op,allowedB u op = true ∧ bank = opD d op a c :: b ∧
      NatReach u d roots p b ∧ Avail u d b a ∧ Avail u d b c
def Lower (u:Bool) (d:Nat) (roots:List Nat) (T:Nat) (L:Nat) : Prop :=
  ∀ p bank,NatReach u d roots p bank → Avail u d bank T → L ≤ p
theorem mask256_bit (i:Nat) : mask256.testBit i = decide (i < 256):=by
  rw [mask256,Nat.testBit_two_pow_sub_one]
theorem opD_and_sub {d d1:Nat} (hd : d&&&mask256 = d) (hsub : d&&&d1 = d) (op a b:Nat) :
    opD d1 op a b&&&d = opD d op a b:=by
  apply Nat.eq_of_testBit_eq; intro i
  have h1:=congrArg (fun v=>v.testBit i) hd
  have h2:=congrArg (fun v=>v.testBit i) hsub
  unfold opD
  split_ifs <;> simp only [andD,orD,negD,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor] at * <;>
    cases hi : d.testBit i <;> simp_all
theorem negD_invol {d:Nat} (hd : d&&&mask256 = d) (a:Nat) :
    negD d (negD d a) = a&&&d:=by
  apply Nat.eq_of_testBit_eq; intro i
  have h1:=congrArg (fun v=>v.testBit i) hd
  simp only [negD,Nat.testBit_and,Nat.testBit_xor] at *
  cases hi : d.testBit i <;> cases ha : a.testBit i <;> simp_all
theorem negD_mask (d a:Nat) : negD d (a&&&d) = negD d a:=by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [negD,Nat.testBit_and,Nat.testBit_xor]
  cases d.testBit i <;> simp
theorem andD_mask (d a b:Nat) : andD d (a&&&d) (b&&&d) = andD d a b:=by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [andD,Nat.testBit_and]
  cases d.testBit i <;> simp
theorem orD_mask (d a b:Nat) : orD d (a&&&d) (b&&&d) = orD d a b:=by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [orD,Nat.testBit_and,Nat.testBit_or]
  cases d.testBit i <;> simp
theorem opD_mask_self (d op a b:Nat) : opD d op a b&&&d = opD d op a b:=by
  apply Nat.eq_of_testBit_eq; intro i
  unfold opD; split_ifs <;> simp only [andD,orD,negD,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor] <;>
    cases d.testBit i <;> simp
theorem negD_const {d:Nat} (hd : d&&&mask256 = d) {a:Nat} (hc : IsConst d a) :
    IsConst d (negD d a):=by
  rcases hc with h0 | h1
  · right; apply Nat.eq_of_testBit_eq; intro i
    have h0i:=congrArg (fun v=>v.testBit i) h0
    have hdi:=congrArg (fun v=>v.testBit i) hd
    simp only [negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit] at *
    cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
  · left; apply Nat.eq_of_testBit_eq; intro i
    have h1i:=congrArg (fun v=>v.testBit i) h1
    have hdi:=congrArg (fun v=>v.testBit i) hd
    simp only [negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit] at *
    cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
theorem avail_cons {u:Bool} {d:Nat} {bank:List Nat} (z w:Nat) (h : Avail u d bank w) :
    Avail u d (z :: bank) w:=by
  rcases h with hc | ⟨v,hv,he⟩ | ⟨hu,v,hv,he⟩
  · exact Or.inl hc
  · exact Or.inr (Or.inl ⟨v,List.mem_cons_of_mem _ hv,he⟩)
  · exact Or.inr (Or.inr ⟨hu,v,List.mem_cons_of_mem _ hv,he⟩)
theorem avail_of_eq {u:Bool} {d:Nat} {bank:List Nat} {v w:Nat}
    (he : v&&&d = w&&&d) (h : Avail u d bank v) : Avail u d bank w:=by
  rcases h with (h0 | h1) | ⟨x,hx,hxe⟩ | ⟨hu,x,hx,hxe⟩
  · exact Or.inl (Or.inl (he.symm.trans h0))
  · exact Or.inl (Or.inr (he.symm.trans h1))
  · exact Or.inr (Or.inl ⟨x,hx,hxe.trans he⟩)
  · exact Or.inr (Or.inr ⟨hu,x,hx,hxe.trans (by rw [← negD_mask,he,negD_mask])⟩)
theorem avail_neg {d:Nat} (hd : d&&&mask256 = d) {bank:List Nat} {w:Nat}
    (h : Avail true d bank w) : Avail true d bank (negD d w):=by
  rcases h with hc | ⟨v,hv,he⟩ | ⟨_,v,hv,he⟩
  · exact Or.inl (negD_const hd hc)
  · refine Or.inr (Or.inr ⟨rfl,v,hv,?_⟩)
    rw [negD_invol hd,he]
  · refine Or.inr (Or.inl ⟨v,hv,?_⟩)
    rw [he]; simp [negD,Nat.and_assoc,Nat.and_self]
theorem opD_const_left {u:Bool} {d:Nat} (hd : d&&&mask256 = d) {op:Nat}
    (hop : allowedB u op = true) {a b:Nat} (hc : IsConst d a) :
    (opD d op a b&&&d = 0) ∨ (opD d op a b&&&d = d) ∨
      (opD d op a b&&&d = b&&&d) ∨ (u = true ∧ opD d op a b&&&d = negD d b):=by
  rcases allowed_cases hop with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · rcases hc with h0 | h1
    · left; apply Nat.eq_of_testBit_eq; intro i
      have h0i:=congrArg (fun v=>v.testBit i) h0
      simp only [opD,andD,Nat.testBit_and,Nat.zero_testBit,beq_self_eq_true,ite_true] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
    · right; right; left; apply Nat.eq_of_testBit_eq; intro i
      have h1i:=congrArg (fun v=>v.testBit i) h1
      simp only [opD,andD,Nat.testBit_and,beq_self_eq_true,ite_true] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
  · rcases hc with h0 | h1
    · right; right; left; apply Nat.eq_of_testBit_eq; intro i
      have h0i:=congrArg (fun v=>v.testBit i) h0
      simp only [opD,orD,Nat.testBit_and,Nat.testBit_or,Nat.zero_testBit,beq_self_eq_true,ite_true,ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
    · right; left; apply Nat.eq_of_testBit_eq; intro i
      have h1i:=congrArg (fun v=>v.testBit i) h1
      simp only [opD,orD,Nat.testBit_and,Nat.testBit_or,beq_self_eq_true,ite_true,ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
  · rcases hc with h0 | h1
    · left; apply Nat.eq_of_testBit_eq; intro i
      have h0i:=congrArg (fun v=>v.testBit i) h0
      simp only [opD,andD,negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit,beq_self_eq_true,ite_true,ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
    · right; right; right; refine ⟨hu,?_⟩
      apply Nat.eq_of_testBit_eq; intro i
      have h1i:=congrArg (fun v=>v.testBit i) h1
      have hdi:=congrArg (fun v=>v.testBit i) hd
      simp only [opD,andD,negD,Nat.testBit_and,Nat.testBit_xor,beq_self_eq_true,ite_true,ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
  · rcases hc with h0 | h1
    · right; right; left; apply Nat.eq_of_testBit_eq; intro i
      have h0i:=congrArg (fun v=>v.testBit i) h0
      have hdi:=congrArg (fun v=>v.testBit i) hd
      simp only [opD,andD,negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit,beq_self_eq_true,ite_true,ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
    · left; apply Nat.eq_of_testBit_eq; intro i
      have h1i:=congrArg (fun v=>v.testBit i) h1
      have hdi:=congrArg (fun v=>v.testBit i) hd
      simp only [opD,andD,negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit,beq_self_eq_true,ite_true,ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
theorem countP_kept_ge {α : Type} (p : α → Bool) (b:Bool) (a : α) (xs:List α) :
    xs.countP p ≤ (kept b a xs).countP p:=by
  cases b
  · simp [kept]
  · simp [kept,List.countP_cons]
theorem contraction {u:Bool} {d d1 T:Nat} (hd : d&&&mask256 = d) (hsub : d&&&d1 = d)
    (hnc : ¬ IsConst d T) {s ws} (h : RunD u d1 T s ws) {roots p bank}
    (hp:NatReach u d roots p bank) (hs : ∀ w ∈ ws,Avail u d bank w) :
    ∃ q next,NatReach u d roots q next ∧ Avail u d next T ∧
      q + ws.countP (isConstB d) ≤ p + s:=by
  induction h using Run.fold generalizing p bank with
  | done =>
    have hfalse : isConstB d T = false:=by
      cases hc : isConstB d T with
      | false=>rfl
      | true=>exact absurd ((isConstB_iff d T).1 hc) hnc
    exact ⟨p,bank,hp,hs T (by simp),by simp [hfalse]⟩
  | perm eq _ ih =>
    obtain ⟨q,next,hq,ht,hle⟩:=ih hp (fun w hw=>hs w (eq.mem_iff.1 hw))
    rw [eq.countP_eq] at hle
    exact ⟨q,next,hq,ht,hle⟩
  | @two s a b r op ka kb hop _ _ _ _ ih =>
    have ha:=hs a List.mem_cons_self
    have hb:=hs b (List.mem_cons_of_mem _ List.mem_cons_self)
    set z1:=opD d1 op a b
    set z0:=opD d op a b
    have hz_eq : z1&&&d = z0&&&d:=by
      rw [opD_and_sub hd hsub,opD_mask_self]
    by_cases hcab : IsConst d a ∨ IsConst d b
    · have hz_av : Avail u d bank z1:=by
        apply avail_of_eq hz_eq.symm
        rcases hcab with hca | hcb
        · rcases opD_const_left hd hop hca with h0 | h1 | he | ⟨rfl,hn⟩
          · exact Or.inl (Or.inl h0)
          · exact Or.inl (Or.inr h1)
          · exact avail_of_eq he.symm hb
          · exact avail_of_eq (by rw [hn]; simp [negD,Nat.and_assoc,Nat.and_self]) (avail_neg hd hb)
        · dsimp only [z0]; rw [opD_comm d hop a b]
          rcases opD_const_left hd (flipOp_allowed hop) hcb with h0 | h1 | he | ⟨rfl,hn⟩
          · exact Or.inl (Or.inl h0)
          · exact Or.inl (Or.inr h1)
          · exact avail_of_eq he.symm ha
          · exact avail_of_eq (by rw [hn]; simp [negD,Nat.and_assoc,Nat.and_self]) (avail_neg hd ha)
      have hs' : ∀ w ∈ z1 :: kept ka a (kept kb b r),Avail u d bank w:=by
        intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact hz_av
        · rw [mem_kept,mem_kept] at hw
          rcases hw with ⟨_,rfl⟩ | ⟨_,rfl⟩ | hw
          · exact ha
          · exact hb
          · exact hs w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw))
      obtain ⟨q,next,hq,ht,hle⟩:=ih hp hs'
      have hkr : r.countP (isConstB d) ≤ (kept ka a (kept kb b r)).countP (isConstB d) :=
        le_trans (countP_kept_ge _ kb b r) (countP_kept_ge _ ka a _)
      have hcost : (if isConstB d a = true then 1 else 0) + (if isConstB d b = true then 1 else 0)
          ≤ 1 + (if isConstB d z1 = true then 1 else 0):=by
        rcases hcab with hca | hcb
        · have ha1 : isConstB d a = true:=(isConstB_iff _ _).2 hca
          rcases opD_const_left hd hop hca with h0 | h1 | he | ⟨_,hn⟩
          · have hz1 : isConstB d z1 = true:=(isConstB_iff _ _).2 (Or.inl (hz_eq.trans h0))
            simp [ha1,hz1]; split <;> omega
          · have hz1 : isConstB d z1 = true:=(isConstB_iff _ _).2 (Or.inr (hz_eq.trans h1))
            simp [ha1,hz1]; split <;> omega
          · have hzb : isConstB d z1 = isConstB d b:=by simp only [isConstB,hz_eq.trans he]
            simp [ha1,hzb]
          · have hzb : isConstB d z1 = isConstB d b:=by
              apply Bool.eq_iff_iff.2; rw [isConstB_iff,isConstB_iff]
              have hnm : negD d b&&&d = negD d b:=by simp [negD,Nat.and_assoc,Nat.and_self]
              constructor
              · intro hz; have hnb : IsConst d (negD d b):=by
                  rcases hz with h0 | h1
                  · exact Or.inl (hnm.trans (hn.symm.trans (hz_eq.symm.trans h0)))
                  · exact Or.inr (hnm.trans (hn.symm.trans (hz_eq.symm.trans h1)))
                have h2:=negD_const hd hnb
                rw [negD_invol hd] at h2
                rcases h2 with e | e <;> [exact Or.inl (by simpa [Nat.and_assoc,Nat.and_self] using e); exact Or.inr (by simpa [Nat.and_assoc,Nat.and_self] using e)]
              · intro hb'; have hnb:=negD_const hd hb'
                rcases hnb with h0 | h1
                · exact Or.inl (hz_eq.trans (hn.trans (hnm.symm.trans h0)))
                · exact Or.inr (hz_eq.trans (hn.trans (hnm.symm.trans h1)))
            simp [ha1,hzb]
        · have hb1 : isConstB d b = true:=(isConstB_iff _ _).2 hcb
          have hz_eq' : z1&&&d = opD d (flipOp op) b a&&&d:=by rw [hz_eq]; dsimp only [z0]; rw [opD_comm d hop a b]
          rcases opD_const_left hd (flipOp_allowed hop) hcb with h0 | h1 | he | ⟨_,hn⟩
          · have hz1 : isConstB d z1 = true:=(isConstB_iff _ _).2 (Or.inl (hz_eq'.trans h0))
            simp [hb1,hz1]; split <;> omega
          · have hz1 : isConstB d z1 = true:=(isConstB_iff _ _).2 (Or.inr (hz_eq'.trans h1))
            simp [hb1,hz1]; split <;> omega
          · have hza : isConstB d z1 = isConstB d a:=by simp only [isConstB,hz_eq'.trans he]
            simp [hb1,hza]
          · have hza : isConstB d z1 = isConstB d a:=by
              apply Bool.eq_iff_iff.2; rw [isConstB_iff,isConstB_iff]
              have hnm : negD d a&&&d = negD d a:=by simp [negD,Nat.and_assoc,Nat.and_self]
              constructor
              · intro hz; have hna : IsConst d (negD d a):=by
                  rcases hz with h0 | h1
                  · exact Or.inl (hnm.trans (hn.symm.trans (hz_eq'.symm.trans h0)))
                  · exact Or.inr (hnm.trans (hn.symm.trans (hz_eq'.symm.trans h1)))
                have h2:=negD_const hd hna
                rw [negD_invol hd] at h2
                rcases h2 with e | e <;> [exact Or.inl (by simpa [Nat.and_assoc,Nat.and_self] using e); exact Or.inr (by simpa [Nat.and_assoc,Nat.and_self] using e)]
              · intro ha'; have hna:=negD_const hd ha'
                rcases hna with h0 | h1
                · exact Or.inl (hz_eq'.trans (hn.trans (hnm.symm.trans h0)))
                · exact Or.inr (hz_eq'.trans (hn.trans (hnm.symm.trans h1)))
            simp [hb1,hza]
      simp only [List.countP_cons] at hle ⊢
      exact ⟨q,next,hq,ht,by omega⟩
    · have hna : isConstB d a = false:=by
        cases h : isConstB d a with | false=>rfl | true=>exact absurd (Or.inl ((isConstB_iff _ _).1 h)) hcab
      have hnb : isConstB d b = false:=by
        cases h : isConstB d b with | false=>rfl | true=>exact absurd (Or.inr ((isConstB_iff _ _).1 h)) hcab
      have hreach':NatReach u d roots (p + 1) (z0 :: bank):=⟨bank,a,b,op,hop,rfl,hp,ha,hb⟩
      have hz_av : Avail u d (z0 :: bank) z1:=Or.inr (Or.inl ⟨z0,List.mem_cons_self,hz_eq.symm⟩)
      have hs' : ∀ w ∈ z1 :: kept ka a (kept kb b r),Avail u d (z0 :: bank) w:=by
        intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact hz_av
        · rw [mem_kept,mem_kept] at hw
          rcases hw with ⟨_,rfl⟩ | ⟨_,rfl⟩ | hw
          · exact avail_cons _ _ ha
          · exact avail_cons _ _ hb
          · exact avail_cons _ _ (hs w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw)))
      obtain ⟨q,next,hq,ht,hle⟩:=ih hreach' hs'
      have hkr : r.countP (isConstB d) ≤ (kept ka a (kept kb b r)).countP (isConstB d) :=
        le_trans (countP_kept_ge _ kb b r) (countP_kept_ge _ ka a _)
      simp only [List.countP_cons,hna,hnb,Bool.false_eq_true,ite_false] at hle ⊢
      exact ⟨q,next,hq,ht,by omega⟩
theorem nrmD_mask (u:Bool) (d w:Nat) : nrmD u d w&&&d = nrmD u d w:=by
  unfold nrmD; split <;> simp [negD,Nat.and_assoc,Nat.and_self]
theorem nrmD_of_bit0_false (u:Bool) (d w:Nat) (hw : w.testBit 0 = false) :
    nrmD u d w = w&&&d:=by
  simp [nrmD,hw]
theorem nrmD_and_d {d:Nat} (hd0 : d.testBit 0 = true) (u:Bool) (w:Nat) :
    nrmD u d (w&&&d) = nrmD u d w:=by
  unfold nrmD
  rw [Nat.testBit_and,hd0,Bool.and_true,negD_mask,Nat.and_assoc,Nat.and_self]
theorem nrmD_neg {d:Nat} (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true) (w:Nat) :
    nrmD true d (negD d w) = nrmD true d w:=by
  have hm0 : mask256.testBit 0 = true:=by decide
  unfold nrmD
  have hnb : (negD d w).testBit 0 = !w.testBit 0:=by
    simp only [negD,Nat.testBit_and,Nat.testBit_xor,hd0,hm0,Bool.and_true,Bool.xor_true]
  rw [hnb]
  cases hw : w.testBit 0
  · simp [negD_invol hd]
  · simp [negD,Nat.and_assoc,Nat.and_self]
theorem nrmD_const_iff {d:Nat} (hd : d&&&mask256 = d) (u:Bool) (w:Nat) :
    (nrmD u d w ≠ 0 ∧ nrmD u d w ≠ d) ↔ ¬ IsConst d w:=by
  unfold nrmD
  have hnm : negD d w&&&d = negD d w:=by simp [negD,Nat.and_assoc,Nat.and_self]
  split
  · constructor
    · rintro ⟨h0,h1⟩ hc
      rcases negD_const hd hc with hn0 | hn1
      · exact h0 (hnm.symm.trans hn0)
      · exact h1 (hnm.symm.trans hn1)
    · intro hnc; refine ⟨fun h0=>?_,fun h1=>?_⟩
      · have:=negD_const hd (a:=negD d w) (Or.inl (hnm.trans h0))
        rw [negD_invol hd] at this
        exact hnc (by rcases this with e | e <;> [exact Or.inl (by simpa [Nat.and_assoc,Nat.and_self] using e); exact Or.inr (by simpa [Nat.and_assoc,Nat.and_self] using e)])
      · have:=negD_const hd (a:=negD d w) (Or.inr (hnm.trans h1))
        rw [negD_invol hd] at this
        exact hnc (by rcases this with e | e <;> [exact Or.inl (by simpa [Nat.and_assoc,Nat.and_self] using e); exact Or.inr (by simpa [Nat.and_assoc,Nat.and_self] using e)])
  · simp [IsConst,not_or]
theorem opD_bit {d:Nat} (hd : d&&&mask256 = d) (op a b i:Nat) (hdi : d.testBit i = true) :
    (opD d op a b).testBit i =
      if op==0 then a.testBit i&&b.testBit i
      else if op==1 then a.testBit i||b.testBit i
      else if op==2 then a.testBit i&&!(b.testBit i)
      else !(a.testBit i)&&b.testBit i:=by
  have hmi : mask256.testBit i = true:=by
    have:=congrArg (fun v=>v.testBit i) hd; simp [Nat.testBit_and,hdi] at this; exact this
  unfold opD; split_ifs <;>
    simp only [andD,orD,negD,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,hdi,hmi,Bool.and_true,Bool.xor_true]
theorem nrmD_bit {d:Nat} (hd : d&&&mask256 = d) (w i:Nat) (hdi : d.testBit i = true) :
    (nrmD true d w).testBit i = if w.testBit 0 then !(w.testBit i) else w.testBit i:=by
  have hmi : mask256.testBit i = true:=by
    have:=congrArg (fun v=>v.testBit i) hd; simp [Nat.testBit_and,hdi] at this; exact this
  unfold nrmD
  cases hw0 : w.testBit 0 <;>
    simp only [hw0,Bool.true_and,Bool.and_false,Bool.false_eq_true,ite_true,ite_false,
      negD,Nat.testBit_and,Nat.testBit_xor,hdi,hmi,Bool.and_true,Bool.xor_true]
theorem nrmD_opD {d:Nat} (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    (u:Bool) (op:Nat) (hop : allowedB u op = true) (a b:Nat) :
    ∃ op',allowedB u op' = true ∧
      nrmD u d (opD d op a b) = opD d op' (nrmD u d a) (nrmD u d b):=by
  cases u with
  | false =>
    rcases allowed_cases hop with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
    · exact ⟨0,rfl,by
        apply Nat.eq_of_testBit_eq; intro i
        simp only [nrmD,opD,andD,Bool.false_and,Bool.false_eq_true,ite_false,beq_self_eq_true,ite_true,Nat.testBit_and]
        cases d.testBit i <;> cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨1,rfl,by
        apply Nat.eq_of_testBit_eq; intro i
        simp only [nrmD,opD,orD,Bool.false_and,Bool.false_eq_true,ite_false]
        simp only [show (1==0) = false from rfl,show (1==1) = true from rfl,Bool.false_eq_true,ite_false,ite_true,Nat.testBit_and,Nat.testBit_or]
        cases d.testBit i <;> cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · contradiction
    · contradiction
  | true =>
    have h4 : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3:=by
      rcases allowed_cases hop with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp
    have hbit : ∀ (e:Nat),
        (∀ i,d.testBit i = true →
          (nrmD true d (opD d op a b)).testBit i =
          (opD d e (nrmD true d a) (nrmD true d b)).testBit i) →
        nrmD true d (opD d op a b) = opD d e (nrmD true d a) (nrmD true d b):=by
      intro e h; apply Nat.eq_of_testBit_eq; intro i
      by_cases hdi : d.testBit i = true
      · exact h i hdi
      · have hf : d.testBit i = false:=Bool.eq_false_iff.2 hdi
        have h1:=congrArg (fun v=>v.testBit i) (nrmD_mask true d (opD d op a b))
        have h2:=congrArg (fun v=>v.testBit i) (opD_mask_self d e (nrmD true d a) (nrmD true d b))
        simp only [Nat.testBit_and,hf,Bool.and_false] at h1 h2; exact h1.symm.trans h2
    rcases h4 with rfl | rfl | rfl | rfl <;>
      cases ha0 : a.testBit 0 <;> cases hb0 : b.testBit 0
    · exact ⟨0,by decide,hbit 0 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨2,by decide,hbit 2 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨3,by decide,hbit 3 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨1,by decide,hbit 1 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨1,by decide,hbit 1 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨3,by decide,hbit 3 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨2,by decide,hbit 2 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨0,by decide,hbit 0 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨2,by decide,hbit 2 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨0,by decide,hbit 0 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨1,by decide,hbit 1 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨3,by decide,hbit 3 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨3,by decide,hbit 3 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨1,by decide,hbit 1 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨0,by decide,hbit 0 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨2,by decide,hbit 2 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
theorem avail_nrm_mem {u:Bool} {d:Nat} (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    {b:List Nat} {w:Nat} (h : Avail u d b w) (hnc : ¬ IsConst d w) :
    nrmD u d w ∈ b.map (nrmD u d):=by
  rcases h with hc | ⟨v,hv,he⟩ | ⟨rfl,v,hv,he⟩
  · exact absurd hc hnc
  · refine List.mem_map.2 ⟨v,hv,?_⟩
    rw [← nrmD_and_d hd0,he,nrmD_and_d hd0]
  · refine List.mem_map.2 ⟨v,hv,?_⟩
    rw [← nrmD_and_d hd0,he,nrmD_neg hd hd0]
theorem perm_erase_two {α : Type} [DecidableEq α] {rest:List α} {a' c' : α}
    (hnd : rest.Nodup) (hne : a' ≠ c') :
    rest.Perm (kept (decide (a' ∈ rest)) a' (kept (decide (c' ∈ rest)) c' ((rest.erase a').erase c'))):=by
  refine (List.perm_ext_iff_of_nodup hnd (nodup_kept _ a' _ (nodup_kept _ c' _ ((hnd.erase a').erase c')
    ((hnd.erase a').not_mem_erase)) (by
      rw [mem_kept]; rintro (⟨_,h⟩ | h)
      · exact hne h
      · exact hnd.not_mem_erase (List.mem_of_mem_erase h)))).2 ?_
  intro x
  rw [mem_kept,mem_kept,(hnd.erase a').mem_erase_iff,hnd.mem_erase_iff]
  by_cases hxa : x = a' <;> by_cases hxc : x = c' <;> by_cases hxr : x ∈ rest <;> simp_all
theorem pull_two {u:Bool} {d Y k ws} (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    (hnd : ws.Nodup) (hprop : ∀ w ∈ ws,w ≠ 0 ∧ w ≠ d) (h : RunD u d Y k ws)
    {b:List Nat} {a c:Nat} (op:Nat) (hop : allowedB u op = true)
    (ha : Avail u d b a) (hc : Avail u d b c)
    (hsub : ∀ w ∈ ws,w ∈ nrmD u d (opD d op a c) :: b.map (nrmD u d)) :
    ∃ k' ws',k' ≤ k + 1 ∧ ws'.Nodup ∧ (∀ w ∈ ws',w ≠ 0 ∧ w ≠ d) ∧
      (∀ w ∈ ws',w ∈ b.map (nrmD u d)) ∧ RunD u d Y k' ws':=by
  set z:=nrmD u d (opD d op a c)
  by_cases hzm : z ∈ ws
  · by_cases hzb : z ∈ b.map (nrmD u d)
    · exact ⟨k,ws,by omega,hnd,hprop,fun w hw=>by
        rcases List.mem_cons.1 (hsub w hw) with rfl | hm
        · exact hzb
        · exact hm,h⟩
    · have hzp:=hprop z hzm
      obtain ⟨op',hop',hez⟩:=nrmD_opD hd hd0 u op hop a c
      have ha_nc : ¬ IsConst d a:=by
        intro hca
        have hznc : ¬ IsConst d (opD d op a c):=(nrmD_const_iff hd u _).1 hzp
        rcases opD_const_left hd hop hca with e0 | e1 | ec | ⟨rfl,en⟩
        · exact hznc (Or.inl e0)
        · exact hznc (Or.inr e1)
        · have hcn : ¬ IsConst d c:=fun hcc=>hznc (by rcases hcc with e | e <;> [exact Or.inl (ec.trans e); exact Or.inr (ec.trans e)])
          have hz_eq : z = nrmD u d c:=by dsimp only [z]; rw [← nrmD_and_d hd0 u (opD d op a c),ec,nrmD_and_d hd0]
          exact hzb (hz_eq ▸ avail_nrm_mem hd hd0 hc hcn)
        · have hcn : ¬ IsConst d c:=fun hcc=>hznc (by
            rcases negD_const hd hcc with e | e
            · exact Or.inl (en.trans (by simpa [negD,Nat.and_assoc,Nat.and_self] using e))
            · exact Or.inr (en.trans (by simpa [negD,Nat.and_assoc,Nat.and_self] using e)))
          have hz_eq : z = nrmD true d c:=by dsimp only [z]; rw [← nrmD_and_d hd0 true (opD d op a c),en,nrmD_neg hd hd0]
          exact hzb (hz_eq ▸ avail_nrm_mem hd hd0 hc hcn)
      have hc_nc : ¬ IsConst d c:=by
        intro hcc
        have hznc : ¬ IsConst d (opD d op a c):=(nrmD_const_iff hd u _).1 hzp
        have hcm : opD d op a c = opD d (flipOp op) c a:=opD_comm d hop a c
        rcases opD_const_left hd (flipOp_allowed hop) hcc with e0 | e1 | ea | ⟨rfl,en⟩
        · exact hznc (Or.inl (hcm.symm ▸ e0))
        · exact hznc (Or.inr (hcm.symm ▸ e1))
        · have hz_eq : z = nrmD u d a:=by
            dsimp only [z]; rw [← nrmD_and_d hd0 u (opD d op a c),hcm,ea,nrmD_and_d hd0]
          exact hzb (hz_eq ▸ avail_nrm_mem hd hd0 ha ha_nc)
        · have hz_eq : z = nrmD true d a:=by
            dsimp only [z]; rw [← nrmD_and_d hd0 true (opD d op a c),hcm,en,nrmD_neg hd hd0]
          exact hzb (hz_eq ▸ avail_nrm_mem hd hd0 ha ha_nc)
      set a':=nrmD u d a
      set c':=nrmD u d c
      have ha'_mem : a' ∈ b.map (nrmD u d):=avail_nrm_mem hd hd0 ha ha_nc
      have hc'_mem : c' ∈ b.map (nrmD u d):=avail_nrm_mem hd hd0 hc hc_nc
      have ha'_prop : a' ≠ 0 ∧ a' ≠ d:=(nrmD_const_iff hd u a).2 ha_nc
      have hc'_prop : c' ≠ 0 ∧ c' ≠ d:=(nrmD_const_iff hd u c).2 hc_nc
      have hne_ac : a' ≠ c':=by
        intro heq
        have hz_eq : opD d op' a' a' = a' ∨ opD d op' a' a' = 0:=by
          rcases allowed_cases hop' with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
          · left; apply Nat.eq_of_testBit_eq; intro i
            have hm:=congrArg (fun v=>v.testBit i) (nrmD_mask u d a)
            change (a'&&&d).testBit i = a'.testBit i at hm
            simp only [opD,andD,Nat.testBit_and] at hm ⊢
            cases hd' : d.testBit i <;> cases ha' : a'.testBit i <;> simp_all
          · left; apply Nat.eq_of_testBit_eq; intro i
            have hm:=congrArg (fun v=>v.testBit i) (nrmD_mask u d a)
            change (a'&&&d).testBit i = a'.testBit i at hm
            simp only [opD,orD,Nat.testBit_and,Nat.testBit_or] at hm ⊢
            cases hd' : d.testBit i <;> cases ha' : a'.testBit i <;> simp_all
          · right; apply Nat.eq_of_testBit_eq; intro i
            have hdi:=congrArg (fun v=>v.testBit i) hd
            simp only [opD,andD,negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit] at hdi ⊢
            cases hd' : d.testBit i <;> cases ha' : a'.testBit i <;> simp_all
          · right; apply Nat.eq_of_testBit_eq; intro i
            have hdi:=congrArg (fun v=>v.testBit i) hd
            simp only [opD,andD,negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit] at hdi ⊢
            cases hd' : d.testBit i <;> cases ha' : a'.testBit i <;> simp_all
        have hez' : z = opD d op' a' a':=by
          have : z = opD d op' a' c':=hez
          rw [← heq] at this; exact this
        rcases hz_eq with e | e
        · exact hzb ((hez'.trans e).symm ▸ ha'_mem)
        · exact hzp.1 (hez'.trans e)
      set rest:=ws.erase z
      have hrest_nd : rest.Nodup:=hnd.erase z
      have hrest_sub : ∀ w ∈ rest,w ∈ b.map (nrmD u d):=by
        intro w hw
        have ⟨hne,hm⟩:=hnd.mem_erase_iff.1 hw
        rcases List.mem_cons.1 (hsub w hm) with rfl | hmb
        · exact absurd rfl hne
        · exact hmb
      have hrest_prop : ∀ w ∈ rest,w ≠ 0 ∧ w ≠ d:=fun w hw=>hprop w (List.mem_of_mem_erase hw)
      have hp1 : ws.Perm (z :: rest):=List.perm_cons_erase hzm
      have h1 : RunD u d Y k (opD d op' a' c' :: rest):=by
        rw [← hez]; exact Run.perm hp1 h
      set ka:=decide (a' ∈ rest)
      set kb:=decide (c' ∈ rest)
      set tail:=(rest.erase a').erase c'
      have htail_nd : tail.Nodup:=(hrest_nd.erase a').erase c'
      have hna_tail : a' ∉ tail:=by
        intro hm; exact hrest_nd.not_mem_erase (List.mem_of_mem_erase hm)
      have hnc_tail : c' ∉ tail:=(hrest_nd.erase a').not_mem_erase
      have hna_mid : a' ∉ kept kb c' tail:=by
        rw [mem_kept]; rintro (⟨_,h⟩ | h)
        · exact hne_ac h
        · exact hna_tail h
      have hrest_perm : rest.Perm (kept ka a' (kept kb c' tail)) :=
        perm_erase_two hrest_nd hne_ac
      have h2:=Run.perm (hrest_perm.cons _) h1
      have hne0 : opD d op' a' c' ≠ 0:=fun h0=>hzp.1 (hez.trans h0)
      have hned : opD d op' a' c' ≠ d:=fun h1=>hzp.2 (hez.trans h1)
      have hnm : opD d op' a' c' ∉ (a' :: c' :: tail):=by
        rw [← hez,List.mem_cons,List.mem_cons]; rintro (e | e | hm)
        · exact hzb (by simpa [z,e] using ha'_mem)
        · exact hzb (by simpa [z,e] using hc'_mem)
        · exact hnd.not_mem_erase (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
      have h3 : RunD u d Y (k + 1) (a' :: c' :: tail):=Run.two op' ka kb hop' hne0 hned hnm h2
      have hnd3 : (a' :: c' :: tail).Nodup :=
        List.nodup_cons.2 ⟨by simp [hne_ac,hna_tail],List.nodup_cons.2 ⟨hnc_tail,htail_nd⟩⟩
      refine ⟨k + 1,a' :: c' :: tail,le_rfl,hnd3,?_,?_,h3⟩
      · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact ha'_prop
        · rcases List.mem_cons.1 hw with rfl | hw
          · exact hc'_prop
          · exact hrest_prop w (List.mem_of_mem_erase (List.mem_of_mem_erase hw))
      · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact ha'_mem
        · rcases List.mem_cons.1 hw with rfl | hw
          · exact hc'_mem
          · exact hrest_sub w (List.mem_of_mem_erase (List.mem_of_mem_erase hw))
  · exact ⟨k,ws,by omega,hnd,hprop,fun w hw=>by
      rcases List.mem_cons.1 (hsub w hw) with rfl | hm
      · exact absurd hw hzm
      · exact hm,h⟩
theorem reach_to_run_aux {u:Bool} {d:Nat} {roots:List Nat} {p bank}
    (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    (hr:NatReach u d roots p bank) :
    ∀ {Y k ws},ws.Nodup → (∀ w ∈ ws,w ≠ 0 ∧ w ≠ d) →
      (∀ w ∈ ws,w ∈ bank.map (nrmD u d)) → RunD u d Y k ws →
      ∃ k' ws',k' ≤ p + k ∧ ws'.Nodup ∧ (∀ w ∈ ws',w ≠ 0 ∧ w ≠ d) ∧
        (∀ w ∈ ws',w ∈ roots.map (nrmD u d)) ∧ RunD u d Y k' ws':=by
  induction p generalizing bank with
  | zero =>
    intro Y k ws hnd hprop hsub hrun
    subst hr
    exact ⟨k,ws,by omega,hnd,hprop,hsub,hrun⟩
  | succ p ih =>
    intro Y k ws hnd hprop hsub hrun
    obtain ⟨b,a,c,op,hop,rfl,hrb,ha,hc⟩:=hr
    have hsub' : ∀ w ∈ ws,w ∈ nrmD u d (opD d op a c) :: b.map (nrmD u d):=by
      intro w hw; simpa [List.map_cons] using hsub w hw
    obtain ⟨k1,ws1,hk1,hnd1,hprop1,hsub1,hrun1⟩:=pull_two hd hd0 hnd hprop hrun op hop ha hc hsub'
    obtain ⟨k2,ws2,hk2,hnd2,hprop2,hsub2,hrun2⟩:=ih hrb hnd1 hprop1 hsub1 hrun1
    exact ⟨k2,ws2,by omega,hnd2,hprop2,hsub2,hrun2⟩
theorem reach_to_run {u:Bool} {d:Nat} {roots:List Nat} {T:Nat} {p bank}
    (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    (hT0 : T.testBit 0 = false) (hR0 : roots.all (fun r=>!r.testBit 0) = true)
    (hnc : ¬ IsConst d T) (hr:NatReach u d roots p bank) (ha : Avail u d bank T) :
    ∃ s ws,s ≤ p ∧ ws.Nodup ∧ (∀ w ∈ ws,w ∈ roots.map (·&&&d)) ∧ RunD u d (T&&&d) s ws:=by
  have hTmem : T&&&d ∈ bank.map (nrmD u d):=by
    have:=avail_nrm_mem hd hd0 ha hnc
    rwa [nrmD_of_bit0_false u d T hT0] at this
  have hprop : ∀ w ∈ [T&&&d],w ≠ 0 ∧ w ≠ d:=by
    intro w hw; rw [List.mem_singleton.1 hw]
    exact ⟨fun e=>hnc (Or.inl e),fun e=>hnc (Or.inr e)⟩
  have hsub : ∀ w ∈ [T&&&d],w ∈ bank.map (nrmD u d):=by
    intro w hw; rw [List.mem_singleton.1 hw]; exact hTmem
  obtain ⟨s,ws,hs,hnd,_,hsub',hrun⟩:=reach_to_run_aux hd hd0 hr (List.nodup_singleton _) hprop hsub Run.done
  have hrmap : roots.map (nrmD u d) = roots.map (·&&&d):=by
    apply List.map_congr_left
    intro r hr_m
    have h0:=List.all_eq_true.1 hR0 r hr_m
    simp only [Bool.not_eq_true'] at h0
    exact nrmD_of_bit0_false u d r h0
  rw [hrmap] at hsub'
  exact ⟨s,ws,by omega,hnd,hsub',hrun⟩
theorem runD_bits {u d y s ws} (hd : d&&&mask256 = d) (h : RunD u d y s ws) (i j:Nat)
    (hi : d.testBit i = true) (hj : d.testBit j = true)
    (hw : ∀ w ∈ ws,w.testBit i = w.testBit j) : y.testBit i = y.testBit j:=by
  have hmi : mask256.testBit i = true:=by
    have:=congrArg (fun v=>v.testBit i) hd; simp [Nat.testBit_and,hi] at this; exact this
  have hmj : mask256.testBit j = true:=by
    have:=congrArg (fun v=>v.testBit j) hd; simp [Nat.testBit_and,hj] at this; exact this
  induction h using Run.fold with
  | done=>exact hw _ (by simp)
  | perm hp _ ih=>exact ih (fun w h=>hw w (hp.mem_iff.1 h))
  | two op ka kb hop _ _ _ _ ih =>
    apply ih; have ha:=hw _ List.mem_cons_self; have hb:=hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hm
    rcases List.mem_cons.1 hm with rfl | hr
    · rcases allowed_cases hop with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;>
        simp [opD,andD,orD,negD,ha,hb,hi,hj,hmi,hmj]
    · rw [mem_kept,mem_kept] at hr
      rcases hr with ⟨_,rfl⟩ | ⟨_,rfl⟩ | hr
      · exact ha
      · exact hb
      · exact hw _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))
theorem runD_bits_le_mono {d y s ws} (h : RunD false d y s ws) (i j:Nat)
    (hi : d.testBit i = true) (hj : d.testBit j = true)
    (hw : ∀ w ∈ ws,w.testBit i ≤ w.testBit j) : y.testBit i ≤ y.testBit j:=by
  induction h using Run.fold with
  | done=>exact hw _ (by simp)
  | perm hp _ ih=>exact ih (fun w h=>hw w (hp.mem_iff.1 h))
  | two op ka kb hop _ _ _ _ ih =>
    apply ih; have ha:=hw _ List.mem_cons_self; have hb:=hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hm
    rcases List.mem_cons.1 hm with rfl | hr
    · rcases allowed_cases hop with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
      · simp only [opD,andD,beq_self_eq_true,ite_true,Nat.testBit_and,hi,hj,Bool.and_true]; grind
      · simp only [opD,orD,beq_self_eq_true,ite_true,ite_false,Nat.testBit_and,Nat.testBit_or,hi,hj,Bool.and_true]; grind
      · contradiction
      · contradiction
    · rw [mem_kept,mem_kept] at hr
      rcases hr with ⟨_,rfl⟩ | ⟨_,rfl⟩ | hr
      · exact ha
      · exact hb
      · exact hw _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))
theorem lower_base {u:Bool} {d:Nat} {roots:List Nat} {T:Nat} (h : availB u d roots T = false) :
    Lower u d roots T 1:=by
  intro p bank hr ha
  cases p with
  | zero =>
    dsimp only [NatReach] at hr; rw [hr] at ha
    have ht:=(availB_iff u d roots T).2 ha
    rw [h] at ht; contradiction
  | succ p=>omega
def moveBits (tag d w:Nat):Nat :=
  ((w&&&tag) <<< d)|||((w >>> d)&&&tag) |||
    (w^^^((w&&&tag)|||(w&&&(tag <<< d))))
theorem moved (tag d i w:Nat) (h : (tag&&&(tag <<< d)) = 0) :
    (moveBits tag d w).testBit i =
      (if tag.testBit i then w.testBit (d + i)
       else if (tag <<< d).testBit i then w.testBit (i - d) else w.testBit i):=by
  have ht:=congrArg (fun v:Nat=>v.testBit i) h
  simp only [Nat.testBit_and,Nat.zero_testBit] at ht
  simp only [moveBits,Nat.testBit_or,Nat.testBit_shiftLeft,Nat.testBit_and,
    Nat.testBit_shiftRight,Nat.testBit_xor] at *
  by_cases hi : d ≤ i <;> simp [hi] at * <;> grind
theorem move_hom (tag d:Nat) (h : (tag&&&(tag <<< d)) = 0) (a b:Nat) :
    moveBits tag d (a&&&b) = (moveBits tag d a&&&moveBits tag d b) ∧
    moveBits tag d (a|||b) = (moveBits tag d a|||moveBits tag d b) ∧
    moveBits tag d (a^^^b) = (moveBits tag d a^^^moveBits tag d b):=by
  refine ⟨?_,?_,?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
    simp only [Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,moved tag d i _ h] <;>
    split_ifs <;> simp
theorem move_zero (tag d:Nat) (h : (tag&&&(tag <<< d)) = 0) : moveBits tag d 0 = 0:=by
  apply Nat.eq_of_testBit_eq; intro i; rw [moved tag d i 0 h]; split_ifs <;> simp
def applyMoves (ms:List (Nat × Nat)) (w:Nat):Nat :=
  ms.foldl (fun acc p=>moveBits p.1 p.2 acc) w
def moveOK256 (p:Nat × Nat):Bool :=
  (p.1&&&(p.1 <<< p.2)==0)&&(moveBits p.1 p.2 mask256==mask256)
theorem applyMoves_hom (ms:List (Nat × Nat)) (hok : ms.all moveOK256 = true) :
    (∀ a b,applyMoves ms (a&&&b) = applyMoves ms a&&&applyMoves ms b) ∧
    (∀ a b,applyMoves ms (a|||b) = applyMoves ms a|||applyMoves ms b) ∧
    (∀ a b,applyMoves ms (a^^^b) = applyMoves ms a^^^applyMoves ms b) ∧
    applyMoves ms 0 = 0 ∧ applyMoves ms mask256 = mask256:=by
  induction ms with
  | nil=>exact ⟨fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl,rfl,rfl⟩
  | cons p ps ih =>
    simp only [List.all_cons,Bool.and_eq_true,moveOK256,beq_iff_eq] at hok
    obtain ⟨⟨hz,hm⟩,hps⟩:=hok
    obtain ⟨hand,hor,hxor,h0,h256⟩:=ih hps
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro a b; simp only [applyMoves,List.foldl_cons,(move_hom p.1 p.2 hz a b).1]; exact hand _ _
    · intro a b; simp only [applyMoves,List.foldl_cons,(move_hom p.1 p.2 hz a b).2.1]; exact hor _ _
    · intro a b; simp only [applyMoves,List.foldl_cons,(move_hom p.1 p.2 hz a b).2.2]; exact hxor _ _
    · simp only [applyMoves,List.foldl_cons,move_zero p.1 p.2 hz]; exact h0
    · simp only [applyMoves,List.foldl_cons,hm]; exact h256
theorem move_invol (tag d w:Nat) (h : (tag&&&(tag <<< d)) = 0) :
    moveBits tag d (moveBits tag d w) = w:=by
  apply Nat.eq_of_testBit_eq; intro i
  have ht:=congrArg (fun v:Nat=>v.testBit i) h
  simp only [Nat.testBit_and,Nat.zero_testBit] at ht
  rw [moved tag d i _ h]
  by_cases h1 : tag.testBit i = true
  · simp only [h1,ite_true,moved tag d (d + i) w h]
    have h2 : tag.testBit (d + i) = false:=by
      have htd:=congrArg (fun v:Nat=>v.testBit (d + i)) h
      simp only [Nat.testBit_and,Nat.testBit_shiftLeft,Nat.zero_testBit] at htd
      have hge : d ≤ d + i:=Nat.le_add_right d i
      have hsub : d + i - d = i:=Nat.add_sub_cancel_left d i
      simp [hge,hsub,h1] at htd; exact htd
    have h3 : (tag <<< d).testBit (d + i) = true:=by
      simp [Nat.testBit_shiftLeft,Nat.le_add_right,Nat.add_sub_cancel_left,h1]
    simp [h2,h3,Nat.add_sub_cancel_left]
  · simp only [h1,ite_false]
    by_cases h2 : (tag <<< d).testBit i = true
    · simp only [h2,ite_true,moved tag d (i - d) w h]
      rw [Nat.testBit_shiftLeft] at h2
      simp only [Bool.and_eq_true,decide_eq_true_eq] at h2
      simp [h2.2,Nat.add_sub_of_le h2.1]
    · simp [h1,h2,moved tag d i w h]
theorem applyMoves_inj (ms:List (Nat × Nat)) (hok : ms.all moveOK256 = true) :
    Function.Injective (applyMoves ms):=by
  induction ms with
  | nil=>intro a b h; exact h
  | cons p ps ih =>
    simp only [List.all_cons,Bool.and_eq_true,moveOK256,beq_iff_eq] at hok
    intro a b h
    simp only [applyMoves,List.foldl_cons] at h
    have h1:=ih hok.2 h
    have:=congrArg (moveBits p.1 p.2) h1
    rwa [move_invol p.1 p.2 a hok.1.1,move_invol p.1 p.2 b hok.1.1] at this
theorem applyMoves_opD (ms:List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    {d1 d2:Nat} (hd : applyMoves ms d2 = d1) (op a b:Nat) :
    applyMoves ms (opD d2 op a b) = opD d1 op (applyMoves ms a) (applyMoves ms b):=by
  obtain ⟨hand,hor,hxor,_,h256⟩:=applyMoves_hom ms hok
  unfold opD; split_ifs <;> simp only [andD,orD,negD,hand,hor,hxor,h256,hd]
theorem applyMoves_runD {u d Y s} (ms:List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    (hd : applyMoves ms d = d) (hY : applyMoves ms Y = Y) {ws} (h : RunD u d Y s ws) :
    RunD u d Y s (ws.map (applyMoves ms)):=by
  obtain ⟨_,_,_,h0,_⟩:=applyMoves_hom ms hok
  have hinj:=applyMoves_inj ms hok
  rw [← hY]
  induction h using Run.fold with
  | done=>exact Run.done
  | perm hp _ ih=>exact Run.perm (hp.map _) ih
  | @two s a b r op ka kb hop hne0 hned hnm _ ih =>
    have eop:=applyMoves_opD ms hok hd op a b
    have e1 : (opD d op a b :: kept ka a (kept kb b r)).map (applyMoves ms) =
        opD d op (applyMoves ms a) (applyMoves ms b) ::
          kept ka (applyMoves ms a) (kept kb (applyMoves ms b) (r.map (applyMoves ms))):=by
      simp [kept_map,eop]
    rw [e1] at ih
    refine Run.two op ka kb hop ?_ ?_ ?_ ih
    · intro e; rw [← eop] at e; exact hne0 (hinj (e.trans h0.symm))
    · intro e; rw [← eop] at e; exact hned (hinj (e.trans hd.symm))
    · rw [← eop,← List.map_cons,← List.map_cons,List.mem_map]; rintro ⟨x,hx,he⟩; exact hnm (hinj he ▸ hx)
theorem reach_map_moves {u:Bool} (ms:List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    {d1 d2:Nat} (hd1 : d1&&&mask256 = d1) (hd : applyMoves ms d2 = d1)
    {roots1 roots2:List Nat} (hroots : ∀ r ∈ roots2,Avail u d1 roots1 (applyMoves ms r)) :
    ∀ {p bank},NatReach u d2 roots2 p bank →
      ∃ bank',NatReach u d1 roots1 p bank' ∧ ∀ v ∈ bank,Avail u d1 bank' (applyMoves ms v):=by
  obtain ⟨hand,_,hxor,h0,h256⟩:=applyMoves_hom ms hok
  have hav : ∀ {b b' w},(∀ v ∈ b,Avail u d1 b' (applyMoves ms v)) →
      Avail u d2 b w → Avail u d1 b' (applyMoves ms w):=by
    intro b b' w hbb hw
    rcases hw with (hz | h1) | ⟨v,hv,he⟩ | ⟨rfl,v,hv,he⟩
    · exact Or.inl (Or.inl (by rw [← hd,← hand,hz,h0]))
    · exact Or.inl (Or.inr (by rw [← hd,← hand,h1]))
    · have hve : applyMoves ms v&&&d1 = applyMoves ms w&&&d1:=by rw [← hd,← hand,← hand,he]
      exact avail_of_eq hve (hbb v hv)
    · have hve : applyMoves ms v&&&d1 = negD d1 (applyMoves ms w)&&&d1:=by
        rw [← hd,← hand,he]; simp only [negD,hand,hxor,h256,hd,Nat.and_assoc,Nat.and_self]
      have hneg:=avail_neg hd1 (avail_of_eq hve (hbb v hv))
      exact avail_of_eq (by rw [negD_invol hd1,Nat.and_assoc,Nat.and_self]) hneg
  intro p
  induction p with
  | zero =>
    intro bank hr; subst hr
    exact ⟨roots1,rfl,hroots⟩
  | succ p ih =>
    intro bank hr
    obtain ⟨b,a,c,op,hop,rfl,hrb,ha,hc⟩:=hr
    obtain ⟨b',hrb',hbb⟩:=ih hrb
    have ha':=hav hbb ha; have hc':=hav hbb hc
    refine ⟨opD d1 op (applyMoves ms a) (applyMoves ms c) :: b',
      ⟨b',applyMoves ms a,applyMoves ms c,op,hop,rfl,hrb',ha',hc'⟩,?_⟩
    intro v hv; rcases List.mem_cons.1 hv with rfl | hv
    · exact Or.inr (Or.inl ⟨opD d1 op (applyMoves ms a) (applyMoves ms c),List.mem_cons_self,by
        rw [applyMoves_opD ms hok hd]⟩)
    · exact avail_cons _ _ (hbb v hv)
theorem lower_iso {u:Bool} {d1 d2 T1 T2 L:Nat} {roots1 roots2:List Nat}
    (ms:List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    (hd1 : d1&&&mask256 = d1) (hd : applyMoves ms d2 = d1) (hT : applyMoves ms T2 = T1)
    (hroots : roots2.all (fun r=>availB u d1 roots1 (applyMoves ms r)) = true)
    (h1 : Lower u d1 roots1 T1 L) : Lower u d2 roots2 T2 L:=by
  obtain ⟨hand,_,hxor,h0,h256⟩:=applyMoves_hom ms hok
  have hr : ∀ r ∈ roots2,Avail u d1 roots1 (applyMoves ms r):=fun r hr =>
    (availB_iff u _ _ _).1 (List.all_eq_true.1 hroots r hr)
  intro p bank hreach ha
  obtain ⟨bank',hrb',hbb⟩:=reach_map_moves ms hok hd1 hd hr hreach
  apply h1 p bank' hrb'
  rcases ha with (hz | ho) | ⟨v,hv,he⟩ | ⟨rfl,v,hv,he⟩
  · exact Or.inl (Or.inl (by rw [← hT,← hd,← hand,hz,h0]))
  · exact Or.inl (Or.inr (by rw [← hT,← hd,← hand,ho]))
  · have hve : applyMoves ms v&&&d1 = T1&&&d1:=by rw [← hT,← hd,← hand,← hand,he]
    exact avail_of_eq hve (hbb v hv)
  · have hve : applyMoves ms v&&&d1 = negD d1 T1&&&d1:=by
      rw [← hT,← hd,← hand,he]; simp only [negD,hand,hxor,h256,hd,Nat.and_assoc,Nat.and_self]
    have hneg:=avail_neg hd1 (avail_of_eq hve (hbb v hv))
    exact avail_of_eq (by rw [negD_invol hd1,Nat.and_assoc,Nat.and_self]) hneg
def pairOK (d T:Nat) (p:Nat × Nat):Bool :=
  d.testBit p.1&&d.testBit p.2&&(T.testBit p.1 != T.testBit p.2)
def essOK (d T:Nat) (roots:List Nat) (a:Nat) (p:Nat × Nat):Bool :=
  pairOK d T p&&roots.all (fun v=>(v==a)||(v.testBit p.1==v.testBit p.2))
theorem countP_ge_sublist (p:Nat → Bool) {xs ys:List Nat}
    (hnd : xs.Nodup) (hsub : ∀ a ∈ xs,a ∈ ys) (hall : ∀ a ∈ xs,p a = true) :
    xs.length ≤ ys.countP p:=by
  induction xs generalizing ys with
  | nil=>simp
  | cons a xs ih =>
    have ⟨hna,hnd'⟩:=List.nodup_cons.1 hnd
    have ham : a ∈ ys:=hsub a List.mem_cons_self
    have hperm : ys.Perm (a :: ys.erase a):=List.perm_cons_erase ham
    rw [hperm.countP_eq,List.countP_cons,hall a List.mem_cons_self]
    have ih':=ih hnd' (fun x hx=>by
      have hne : x ≠ a:=fun e=>hna (e ▸ hx)
      exact (List.mem_erase_of_ne hne).2 (hsub x (List.mem_cons_of_mem _ hx)))
      (fun x hx=>hall x (List.mem_cons_of_mem _ hx))
    simp only [ite_true,List.length_cons]
    omega
theorem lower_slice {u:Bool} {d dSub T TSub L:Nat} {roots rootsSub:List Nat}
    (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    (hT0 : T.testBit 0 = false) (hR0 : roots.all (fun r=>!r.testBit 0) = true)
    (hdSub : dSub&&&mask256 = dSub) (hsub : dSub&&&d = dSub)
    (hT : T&&&dSub = TSub&&&dSub)
    (hnc : isConstB d T = false) (hncSub : isConstB dSub TSub = false)
    (hcov : roots.all (availB u dSub rootsSub) = true)
    (singles:List (Nat × Nat × Nat))
    (hs_nd : (singles.map Prod.fst).Nodup)
    (hs_ok : singles.all (fun e=>isConstB dSub e.1&&essOK d (T&&&d) (roots.map (·&&&d)) e.1 e.2) = true)
    (hprior : Lower u dSub rootsSub TSub L) :
    Lower u d roots T (L + singles.length):=by
  have hnc' : ¬ IsConst d T:=fun h=>by rw [(isConstB_iff _ _).2 h] at hnc; contradiction
  have hncSub' : ¬ IsConst dSub (T&&&d):=by
    intro h
    have e : (T&&&d)&&&dSub = TSub&&&dSub:=by
      rw [Nat.and_assoc,Nat.and_comm d dSub,hsub,hT]
    rcases h with h0 | h1
    · exact absurd ((isConstB_iff _ _).2 (Or.inl (e.symm.trans h0))) (by simp [hncSub])
    · exact absurd ((isConstB_iff _ _).2 (Or.inr (e.symm.trans h1))) (by simp [hncSub])
  intro p bank hr ha
  obtain ⟨s,ws,hs_le,hnd,hws_sub,hrun⟩:=reach_to_run hd hd0 hT0 hR0 hnc' hr ha
  have hws_av : ∀ w ∈ ws,Avail u dSub rootsSub w:=by
    intro w hw
    obtain ⟨r,hr_m,rfl⟩:=List.mem_map.1 (hws_sub w hw)
    have hav:=(availB_iff u _ _ _).1 (List.all_eq_true.1 hcov r hr_m)
    exact avail_of_eq (by rw [Nat.and_assoc,Nat.and_comm d dSub,hsub]) hav
  obtain ⟨q,next,hq,ht,hle⟩:=contraction hdSub hsub hncSub' hrun (p:=0) (bank:=rootsSub) rfl hws_av
  have hTSub_av : Avail u dSub next TSub:=avail_of_eq (by
    rw [Nat.and_assoc,Nat.and_comm d dSub,hsub,hT]) ht
  have hL : L ≤ q:=hprior q next hq hTSub_av
  have hsin_mem : ∀ a ∈ singles.map Prod.fst,a ∈ ws:=by
    intro a ha
    obtain ⟨⟨a',r1,r2⟩,hm,rfl⟩:=List.mem_map.1 ha
    have hok:=List.all_eq_true.1 hs_ok (a',r1,r2) hm
    simp only [Bool.and_eq_true,essOK,pairOK,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at hok
    obtain ⟨_,⟨⟨hr1,hr2⟩,hdiff⟩,hiso⟩:=hok
    by_contra hnot
    apply hdiff
    apply runD_bits hd hrun r1 r2 hr1 hr2
    intro w hw
    rcases hiso w (hws_sub w hw) with rfl | heq
    · exact absurd hw hnot
    · exact heq
  have hsin_const : ∀ a ∈ singles.map Prod.fst,isConstB dSub a = true:=by
    intro a ha
    obtain ⟨⟨a',r1,r2⟩,hm,rfl⟩:=List.mem_map.1 ha
    have hok:=List.all_eq_true.1 hs_ok _ hm
    simp only [Bool.and_eq_true] at hok
    exact hok.1
  have hcnt:=countP_ge_sublist (isConstB dSub) hs_nd hsin_mem hsin_const
  simp only [List.length_map] at hcnt
  omega
theorem lower_ess_count {u:Bool} {d T:Nat} {roots:List Nat}
    (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    (hT0 : T.testBit 0 = false) (hR0 : roots.all (fun r=>!r.testBit 0) = true)
    (hnc : isConstB d T = false)
    (singles:List (Nat × Nat × Nat))
    (hs_nd : (singles.map Prod.fst).Nodup)
    (hs_ok : singles.all (fun e=>essOK d (T&&&d) (roots.map (·&&&d)) e.1 e.2) = true) :
    Lower u d roots T (singles.length - 1):=by
  have hnc' : ¬ IsConst d T:=fun h=>by rw [(isConstB_iff _ _).2 h] at hnc; contradiction
  intro p bank hr ha
  obtain ⟨s,ws,hs_le,_,hws_sub,hrun⟩:=reach_to_run hd hd0 hT0 hR0 hnc' hr ha
  have hsin_mem : ∀ a ∈ singles.map Prod.fst,a ∈ ws:=by
    intro a ha
    obtain ⟨⟨a',r1,r2⟩,hm,rfl⟩:=List.mem_map.1 ha
    have hok:=List.all_eq_true.1 hs_ok (a',r1,r2) hm
    simp only [essOK,pairOK,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at hok
    obtain ⟨⟨⟨hr1,hr2⟩,hdiff⟩,hiso⟩:=hok
    by_contra hnot
    apply hdiff
    apply runD_bits hd hrun r1 r2 hr1 hr2
    intro w hw
    rcases hiso w (hws_sub w hw) with rfl | heq
    · exact absurd hw hnot
    · exact heq
  have hcnt:=countP_ge_sublist (fun _=>true) hs_nd hsin_mem (fun _ _=>rfl)
  simp only [List.length_map,List.countP_true] at hcnt
  have hlen:=run_len hrun
  omega
theorem negD_eq_xor {d:Nat} (hd : d&&&mask256 = d) (w:Nat) :
    d^^^(w&&&d) = negD d w:=by
  apply Nat.eq_of_testBit_eq; intro i
  have hdi:=congrArg (fun v=>v.testBit i) hd
  simp only [negD,Nat.testBit_and,Nat.testBit_xor] at hdi ⊢
  cases hd' : d.testBit i <;> cases hw' : w.testBit i <;> simp_all
def availM (d:Nat) (bank:List Nat) (w:Nat):Bool :=
  let m:=w&&&d
  if m==0||m==d then true else
  let nm:=d^^^m
  bank.any (fun v=>v==m||v==nm)
theorem avail_of_availM {d:Nat} (hd : d&&&mask256 = d)
    {bank pool:List Nat} (hsup : ∀ v ∈ pool,Avail true d bank v ∧ v&&&d = v) {w:Nat}
    (hb : availM d pool w = true) : Avail true d bank w:=by
  unfold availM at hb; dsimp only at hb
  split at hb
  · rename_i hc
    simp only [Bool.or_eq_true,beq_iff_eq] at hc
    exact Or.inl hc
  · rw [List.any_eq_true] at hb
    obtain ⟨v,hv,he⟩:=hb
    simp only [Bool.or_eq_true,beq_iff_eq] at he
    obtain ⟨hav,hvm⟩:=hsup v hv
    rcases he with rfl | hnm
    · exact avail_of_eq hvm hav
    · have hneg:=avail_neg hd hav
      have he1 : negD d v&&&d = w&&&d:=by
        rw [← negD_mask,hvm,hnm,negD_eq_xor hd,negD_invol hd,Nat.and_assoc,Nat.and_self]
      exact avail_of_eq he1 hneg
def stepOp (d:Nat) (st:Nat × List Nat) (g:Nat × Nat × Nat):Nat × List Nat :=
  if allowedB true g.1 then
    let om:=opD d g.1 g.2.1 g.2.2
    if availM d st.2 om then st
    else if availM d st.2 g.2.1&&availM d st.2 g.2.2 then (st.1 + 1,om :: st.2)
    else st
  else st
def runOps (d:Nat) (st:Nat × List Nat) (ops:List (Nat × Nat × Nat)):Nat × List Nat :=
  ops.foldl (stepOp d) st
theorem getD_mem {xs:List Nat} {i:Nat} (hi : i < xs.length) : xs.getD i 0 ∈ xs:=by
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]
  exact List.getElem_mem hi
theorem stepOp_sound {d:Nat} (hd : d&&&mask256 = d) {roots bank:List Nat}
    (st:Nat × List Nat) (g:Nat × Nat × Nat)
    (hr:NatReach true d roots st.1 bank) (hsup : ∀ v ∈ st.2,Avail true d bank v ∧ v&&&d = v) :
    ∃ bank',NatReach true d roots (stepOp d st g).1 bank' ∧ ∀ v ∈ (stepOp d st g).2,Avail true d bank' v ∧ v&&&d = v:=by
  unfold stepOp; dsimp only
  split
  · rename_i hop
    split
    · exact ⟨bank,hr,hsup⟩
    · split
      · rename_i hab
        simp only [Bool.and_eq_true] at hab
        have ha:=avail_of_availM hd hsup hab.1
        have hb:=avail_of_availM hd hsup hab.2
        refine ⟨opD d g.1 g.2.1 g.2.2 :: bank,⟨bank,g.2.1,g.2.2,g.1,hop,rfl,hr,ha,hb⟩,?_⟩
        intro v hv
        rcases List.mem_cons.1 hv with rfl | hv
        · exact ⟨Or.inr (Or.inl ⟨_,List.mem_cons_self,rfl⟩),opD_mask_self d g.1 g.2.1 g.2.2⟩
        · exact ⟨avail_cons _ _ (hsup v hv).1,(hsup v hv).2⟩
      · exact ⟨bank,hr,hsup⟩
  · exact ⟨bank,hr,hsup⟩
theorem runOps_sound {d:Nat} (hd : d&&&mask256 = d) {roots:List Nat}
    (ops:List (Nat × Nat × Nat)) :
    ∀ (st:Nat × List Nat) (bank:List Nat),
      NatReach true d roots st.1 bank → (∀ v ∈ st.2,Avail true d bank v ∧ v&&&d = v) →
      ∃ bank',NatReach true d roots (runOps d st ops).1 bank' ∧ ∀ v ∈ (runOps d st ops).2,Avail true d bank' v ∧ v&&&d = v:=by
  induction ops with
  | nil=>intro st bank hr hsup; exact ⟨bank,hr,hsup⟩
  | cons g ops ih =>
    intro st bank hr hsup
    obtain ⟨bank1,hr1,hsup1⟩:=stepOp_sound hd st g hr hsup
    exact ih (stepOp d st g) bank1 hr1 hsup1
def checkPool (dSub LSub s:Nat) (st:Nat × List Nat) (ws:List Nat):Bool :=
  decide (s + st.1 < LSub + ws.countP (isConstB dSub))&&ws.all (availM dSub st.2)
def checkPoolG (dSub LSub s:Nat) (st:Nat × List Nat) (g:Nat × Nat × Nat) (ws:List Nat):Bool :=
  let c:=ws.countP (isConstB dSub)
  if decide (s + st.1 < LSub + c) then
    let st':=stepOp dSub st g
    decide (s + st'.1 < LSub + c)&&ws.all (availM dSub st'.2)
  else false
theorem checkPool_sound {d dSub T TSub LSub s:Nat} {rootsSub ws:List Nat}
    (hdSub : dSub&&&mask256 = dSub) (hsub : dSub&&&d = dSub)
    (hT : T&&&dSub = TSub&&&dSub) (hncSub : isConstB dSub TSub = false)
    (hprior : Lower true dSub rootsSub TSub LSub)
    (st:Nat × List Nat) (bank:List Nat)
    (hrb:NatReach true dSub rootsSub st.1 bank) (hsb : ∀ v ∈ st.2,Avail true dSub bank v ∧ v&&&dSub = v)
    (hchk : checkPool dSub LSub s st ws = true) :
    ¬ RunD true d (T&&&d) s ws:=by
  intro hrun
  simp only [checkPool,Bool.and_eq_true,decide_eq_true_eq] at hchk
  obtain ⟨hineq,hall⟩:=hchk
  have hws_av : ∀ w ∈ ws,Avail true dSub bank w:=fun w hw =>
    avail_of_availM hdSub hsb (List.all_eq_true.1 hall w hw)
  have hnc' : ¬ IsConst dSub (T&&&d):=by
    intro h; have e : (T&&&d)&&&dSub = TSub&&&dSub:=by rw [Nat.and_assoc,Nat.and_comm d dSub,hsub,hT]
    rcases h with h0 | h1
    · exact absurd ((isConstB_iff _ _).2 (Or.inl (e.symm.trans h0))) (by simp [hncSub])
    · exact absurd ((isConstB_iff _ _).2 (Or.inr (e.symm.trans h1))) (by simp [hncSub])
  obtain ⟨q,next,hq,ht,hle⟩:=contraction hdSub hsub hnc' hrun hrb hws_av
  have hL:=hprior q next hq (avail_of_eq (by rw [Nat.and_assoc,Nat.and_comm d dSub,hsub,hT]) ht)
  omega
def subValidB (d dSub T TSub:Nat):Bool :=
  (dSub&&&mask256==dSub)&&(dSub&&&d==dSub)&&(T&&&dSub==TSub&&&dSub)&&!(isConstB dSub TSub)
theorem cpcs {d dSub T TSub LSub s:Nat} {rootsSub ws:List Nat}
    (hv : subValidB d dSub T TSub = true)
    (hprior : Lower true dSub rootsSub TSub LSub)
    (ops:List (Nat × Nat × Nat)) (g:Nat × Nat × Nat)
    (hchk : checkPoolG dSub LSub s (runOps dSub (0,rootsSub.map (·&&&dSub)) ops) g ws = true) :
    ¬ RunD true d (T&&&d) s ws:=by
  unfold checkPoolG at hchk; dsimp only at hchk
  split at hchk
  · simp only [subValidB,Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true'] at hv
    have hsup0 : ∀ v ∈ rootsSub.map (·&&&dSub),Avail true dSub rootsSub v ∧ v&&&dSub = v:=by
      intro v hv'; obtain ⟨r,hr,rfl⟩:=List.mem_map.1 hv'
      exact ⟨Or.inr (Or.inl ⟨r,hr,by rw [Nat.and_assoc,Nat.and_self]⟩),by rw [Nat.and_assoc,Nat.and_self]⟩
    obtain ⟨bank1,hr1,hsup1⟩:=runOps_sound hv.1.1.1 ops (0,rootsSub.map (·&&&dSub)) rootsSub rfl hsup0
    obtain ⟨bank2,hr2,hsup2⟩:=stepOp_sound hv.1.1.1 _ g hr1 hsup1
    exact checkPool_sound hv.1.1.1 hv.1.1.2 hv.1.2 hv.2 hprior _ bank2 hr2 hsup2 hchk
  · contradiction
theorem checkRootSub_sound {d dSub T TSub LSub s:Nat} {rootsSub ws:List Nat}
    (hv : subValidB d dSub T TSub = true)
    (hprior : Lower true dSub rootsSub TSub LSub)
    (hchk : checkPool dSub LSub s (0,rootsSub.map (·&&&dSub)) ws = true) :
    ¬ RunD true d (T&&&d) s ws:=by
  simp only [subValidB,Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true'] at hv
  have hsup0 : ∀ v ∈ rootsSub.map (·&&&dSub),Avail true dSub rootsSub v ∧ v&&&dSub = v:=by
    intro v hv'; obtain ⟨r,hr,rfl⟩:=List.mem_map.1 hv'
    exact ⟨Or.inr (Or.inl ⟨r,hr,by rw [Nat.and_assoc,Nat.and_self]⟩),by rw [Nat.and_assoc,Nat.and_self]⟩
  exact checkPool_sound hv.1.1.1 hv.1.1.2 hv.1.2 hv.2 hprior (0,rootsSub.map (·&&&dSub)) rootsSub rfl hsup0 hchk
def coversP (u:Bool) (pairs:List (Nat × Nat)) (ws:List Nat):Bool :=
  if !u then
    pairs.all (fun p=>ws.any (fun w=>!w.testBit p.1&&w.testBit p.2))
  else
    pairs.all (fun p=>ws.any (fun w=>w.testBit p.1 != w.testBit p.2))
theorem coversP_ok {u:Bool} {d T s:Nat} (hd : d&&&mask256 = d)
    (pairs:List (Nat × Nat))
    (hpairs : pairs.all (fun p=>d.testBit p.1&&d.testBit p.2&&!(T&&&d).testBit p.1&&(T&&&d).testBit p.2) = true)
    {ws:List Nat} (h : RunD u d (T&&&d) s ws) : coversP u pairs ws = true:=by
  cases u with
  | false =>
    simp only [coversP,Bool.not_false,ite_true,List.all_eq_true,List.any_eq_true]
    intro ⟨u1,v1⟩ hm
    have hp:=List.all_eq_true.1 hpairs (u1,v1) hm
    simp only [Bool.and_eq_true,Bool.not_eq_true'] at hp
    by_contra! hall
    have hle:=runD_bits_le_mono h v1 u1 hp.1.1.2 hp.1.1.1 (fun w hw=>by
      have hbad:=hall w hw
      cases hu : w.testBit u1 <;> cases hv : w.testBit v1 <;> simp_all)
    rw [hp.1.2,hp.2] at hle; contradiction
  | true =>
    simp only [coversP,Bool.not_true,Bool.false_eq_true,ite_false,List.all_eq_true,List.any_eq_true,bne_iff_ne]
    intro ⟨u1,v1⟩ hm
    have hp:=List.all_eq_true.1 hpairs (u1,v1) hm
    simp only [Bool.and_eq_true,Bool.not_eq_true'] at hp
    by_contra! hall
    have heq:=runD_bits hd h u1 v1 hp.1.1.1 hp.1.1.2 hall
    rw [hp.1.2,hp.2] at heq; contradiction
def unorientedCov (pairs:List (Nat × Nat)) (ws:List Nat):Bool :=
  pairs.all (fun p=>ws.any (fun w=>w.testBit p.1 != w.testBit p.2))
theorem unorientedCov_ok {u:Bool} {d T s:Nat} (hd : d&&&mask256 = d)
    (pairs:List (Nat × Nat))
    (hpairs : pairs.all (fun p=>d.testBit p.1&&d.testBit p.2&&((T&&&d).testBit p.1 != (T&&&d).testBit p.2)) = true)
    {ws:List Nat} (h : RunD u d (T&&&d) s ws) : unorientedCov pairs ws = true:=by
  simp only [unorientedCov,List.all_eq_true,List.any_eq_true,bne_iff_ne]
  intro ⟨u1,v1⟩ hm
  have hp:=List.all_eq_true.1 hpairs (u1,v1) hm
  simp only [Bool.and_eq_true,bne_iff_ne] at hp
  by_contra! hall
  have heq:=runD_bits hd h u1 v1 hp.1.1 hp.1.2 hall
  exact hp.2 heq
def maskP (m:Nat):Nat:=2 ^ m - 1
def projBit (rs:List Nat) (w:Nat):Nat :=
  rs.foldr (fun r acc=>(acc <<< 1)|||(if w.testBit r then 1 else 0)) 0
theorem projBit_testBit (rs:List Nat) (w:Nat) (i:Nat) :
    (projBit rs w).testBit i = if h : i < rs.length then w.testBit rs[i] else false:=by
  induction rs generalizing i with
  | nil=>simp [projBit]
  | cons r rs ih =>
    cases i with
    | zero =>
      simp only [projBit,List.foldr_cons,Nat.testBit_or,Nat.testBit_shiftLeft,
        Nat.not_le.2 Nat.zero_lt_one,decide_false,Bool.false_and,Bool.false_or,
        List.length_cons,Nat.zero_lt_succ,dite_true,List.getElem_cons_zero]
      cases w.testBit r <;> simp
    | succ i =>
      simp only [projBit,List.foldr_cons,Nat.testBit_or,Nat.testBit_shiftLeft,
        Nat.succ_le_succ (Nat.zero_le i),decide_true,Bool.true_and,Nat.add_sub_cancel,
        List.length_cons,Nat.succ_lt_succ_iff,List.getElem_cons_succ]
      have h1 : (if w.testBit r = true then 1 else 0).testBit (i + 1) = false:=by
        cases w.testBit r <;> simp [Nat.testBit_succ]
      rw [h1,Bool.or_false]; exact ih i
def opP (mp op:Nat) (pa pb:Nat):Nat :=
  if op==0 then pa&&&pb
  else if op==1 then pa|||pb
  else if op==2 then pa&&&(pb^^^mp)
  else (pa^^^mp)&&&pb
theorem projBit_opD {dm:Nat} (hd : dm&&&mask256 = dm) {rs:List Nat}
    (hrs : ∀ r ∈ rs,dm.testBit r = true) (op a b:Nat) :
    projBit rs (opD dm op a b) = opP (maskP rs.length) op (projBit rs a) (projBit rs b):=by
  apply Nat.eq_of_testBit_eq; intro i
  by_cases hi : i < rs.length
  · have hdr:=hrs rs[i] (List.getElem_mem hi)
    have hmr : mask256.testBit rs[i] = true:=by
      have:=congrArg (fun v=>v.testBit rs[i]) hd; simp [Nat.testBit_and,hdr] at this; exact this
    unfold opD opP
    split_ifs <;>
      simp only [projBit_testBit,hi,dite_true,andD,orD,negD,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,
        maskP,Nat.testBit_two_pow_sub_one,decide_true,hdr,hmr,Bool.and_true,Bool.xor_true] <;>
      (cases a.testBit rs[i] <;> cases b.testBit rs[i] <;> rfl)
  · unfold opD opP
    split_ifs <;>
      simp only [projBit_testBit,hi,dite_false,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,
        maskP,Nat.testBit_two_pow_sub_one,decide_false,Bool.false_and,Bool.and_false,Bool.false_or,Bool.xor_false]
theorem foldl_or_testBit {α : Type} (g : α → Nat) (xs:List α) (acc i:Nat) :
    (xs.foldl (fun a x=>a|||g x) acc).testBit i = (acc.testBit i||xs.any (fun x=>(g x).testBit i)):=by
  induction xs generalizing acc with
  | nil=>simp
  | cons x xs ih =>
    simp only [List.foldl_cons,ih,Nat.testBit_or,List.any_cons,Bool.or_assoc]
def colB (mp:Nat) (oriented:Bool) (p:Nat × Nat):Nat :=
  if oriented then (p.1^^^mp)&&&p.2 else p.1^^^p.2
def coversD (u:Bool) (mp:Nat) (dws:List (Nat × Nat × Nat)):Bool :=
  dws.foldl (fun acc d=>acc|||colB mp (!u) d.2) 0==mp
theorem coversD_eq (u:Bool) (pairs:List (Nat × Nat)) (ws:List Nat) :
    coversD u (maskP pairs.length) (ws.map (fun w=>(w,projBit (pairs.map Prod.fst) w,projBit (pairs.map Prod.snd) w))) =
      coversP u pairs ws:=by
  set r1s:=pairs.map Prod.fst
  set r2s:=pairs.map Prod.snd
  set mp:=maskP pairs.length
  have hr1 : r1s.length = pairs.length:=List.length_map _
  have hr2 : r2s.length = pairs.length:=List.length_map _
  unfold coversD coversP
  cases u with
  | false =>
    simp only [Bool.not_false,colB,ite_true]
    apply Bool.eq_iff_iff.2; rw [beq_iff_eq,List.all_eq_true]
    constructor
    · intro heq pr hpr
      obtain ⟨i,hi,rfl⟩:=List.mem_iff_getElem.1 hpr
      have hb:=congrArg (fun v=>v.testBit i) heq
      rw [foldl_or_testBit,Nat.zero_testBit,Bool.false_or,List.any_map] at hb
      simp only [mp,maskP,Nat.testBit_two_pow_sub_one,hi,decide_true] at hb
      obtain ⟨w,hw,hwt⟩:=List.any_eq_true.1 hb
      simp only [Function.comp_def,Nat.testBit_and,Nat.testBit_xor,projBit_testBit,hr1,hr2,hi,dite_true,
        Nat.testBit_two_pow_sub_one,decide_true,Bool.xor_true] at hwt
      exact List.any_eq_true.2 ⟨w,hw,by simpa [r1s,r2s] using hwt⟩
    · intro hall
      apply Nat.eq_of_testBit_eq; intro i
      rw [foldl_or_testBit,Nat.zero_testBit,Bool.false_or,List.any_map]
      simp only [mp,maskP,Nat.testBit_two_pow_sub_one]
      by_cases hi : i < pairs.length
      · simp only [hi,decide_true]
        obtain ⟨w,hw,hwt⟩:=List.any_eq_true.1 (hall pairs[i] (List.getElem_mem hi))
        exact List.any_eq_true.2 ⟨w,hw,by
          simp only [Function.comp_def,Nat.testBit_and,Nat.testBit_xor,projBit_testBit,hr1,hr2,hi,dite_true,
            Nat.testBit_two_pow_sub_one,decide_true,Bool.xor_true,r1s,r2s,List.getElem_map]
          exact hwt⟩
      · simp only [hi,decide_false,List.any_eq_false]
        intro w _
        simp only [Function.comp_def,Nat.testBit_and,Nat.testBit_xor,projBit_testBit,hr1,hr2,hi,dite_false,
          Nat.testBit_two_pow_sub_one,decide_false,Bool.xor_false,Bool.and_false,not_false_eq_true,Bool.false_eq_true]
  | true =>
    simp only [Bool.not_true,colB,Bool.false_eq_true,ite_false]
    apply Bool.eq_iff_iff.2; rw [beq_iff_eq,List.all_eq_true]
    constructor
    · intro heq pr hpr
      obtain ⟨i,hi,rfl⟩:=List.mem_iff_getElem.1 hpr
      have hb:=congrArg (fun v=>v.testBit i) heq
      rw [foldl_or_testBit,Nat.zero_testBit,Bool.false_or,List.any_map] at hb
      simp only [mp,maskP,Nat.testBit_two_pow_sub_one,hi,decide_true] at hb
      obtain ⟨w,hw,hwt⟩:=List.any_eq_true.1 hb
      simp only [Function.comp_def,Nat.testBit_xor,projBit_testBit,hr1,hr2,hi,dite_true] at hwt
      exact List.any_eq_true.2 ⟨w,hw,by simpa [r1s,r2s,bne] using hwt⟩
    · intro hall
      apply Nat.eq_of_testBit_eq; intro i
      rw [foldl_or_testBit,Nat.zero_testBit,Bool.false_or,List.any_map]
      simp only [mp,maskP,Nat.testBit_two_pow_sub_one]
      by_cases hi : i < pairs.length
      · simp only [hi,decide_true]
        obtain ⟨w,hw,hwt⟩:=List.any_eq_true.1 (hall pairs[i] (List.getElem_mem hi))
        exact List.any_eq_true.2 ⟨w,hw,by
          simp only [Function.comp_def,Nat.testBit_xor,projBit_testBit,hr1,hr2,hi,dite_true,r1s,r2s,List.getElem_map]
          simpa [bne] using hwt⟩
      · simp only [hi,decide_false,List.any_eq_false]
        intro w _
        simp only [Function.comp_def,Nat.testBit_xor,projBit_testBit,hr1,hr2,hi,dite_false,
          Bool.xor_false,Bool.false_eq_true,not_false_eq_true]
theorem erase_map_inj {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (f : α → β) (hinj : Function.Injective f) (xs:List α) (a : α) :
    (xs.map f).erase (f a) = (xs.erase a).map f:=by
  induction xs with
  | nil=>rfl
  | cons x xs ih =>
    simp only [List.map_cons,List.erase_cons]
    by_cases h : x = a
    · subst h; simp
    · have hf : (f x==f a) = false:=beq_false_of_ne (fun e=>h (hinj e))
      have hx : (x==a) = false:=beq_false_of_ne h
      simp [hf,hx,ih]
def opsOf (u:Bool):List Nat:=if u then [0,1,2,3] else [0,1]
theorem mem_opsOf {u:Bool} {op:Nat} (hop : allowedB u op = true) : op ∈ opsOf u:=by
  rcases allowed_cases hop with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> decide
  · cases u <;> decide
  · decide
  · decide
def nextD (u:Bool) (dm:Nat) (slack:Nat) (ws:List Nat) (f : (Nat × Nat × Nat) → List Nat → Bool):Bool :=
  ws.any fun a =>
    let ra:=ws.erase a
    ra.any fun b =>
      a ≤ b&&(let r:=ra.erase b
        (opsOf u).any fun op =>
          let w:=opD dm op a b
          let g:=(op,a,b)
          w != 0&&w != dm&&!(ws.contains w) &&
            (f g (w :: r)||(slack ≥ 1&&(f g (w :: a :: r)||f g (w :: b :: r))) ||
              (slack ≥ 2&&f g (w :: a :: b :: r))))
theorem nextD_two_sorted {u:Bool} {dm y a b rest} {op:Nat} {ka kb:Bool} {s ws}
    (hop : allowedB u op = true) (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h0 : opD dm op a b ≠ 0) (hd : opD dm op a b ≠ dm) (hnm : opD dm op a b ∉ (a :: b :: rest))
    (h : RunD u dm y s (opD dm op a b :: kept ka a (kept kb b rest)))
    (f : (Nat × Nat × Nat) → List Nat → Bool) (hf : ∀ g ys,RunD u dm y s ys → f g ys = true) :
    nextD u dm (s + 2 - ws.length) ws f = true:=by
  have ha:=p.mem_iff.1 List.mem_cons_self
  have pp:=(p.trans (List.perm_cons_erase ha)).cons_inv
  have hb:=pp.mem_iff.1 List.mem_cons_self
  have pr:=(pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh:=run_len h; have hl:=p.length_eq; simp only [List.length_cons] at hl hh
  have hnc : ws.contains (opD dm op a b) = false:=by
    cases h : ws.contains (opD dm op a b) with
    | false=>rfl
    | true=>exact absurd (p.mem_iff.2 (by simpa using h)) hnm
  have h0b : (opD dm op a b != 0) = true:=bne_iff_ne.2 h0
  have hdb : (opD dm op a b != dm) = true:=bne_iff_ne.2 hd
  apply List.any_eq_true.2 ⟨a,ha,?_⟩
  apply List.any_eq_true.2 ⟨b,hb,?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab,?_⟩
  apply List.any_eq_true.2 ⟨op,mem_opsOf hop,?_⟩
  simp only [h0b,hdb,hnc,Bool.not_false,Bool.true_and]
  have ht:=hf (op,a,b) _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht,Bool.true_or,Bool.or_true,Bool.and_true] <;>
    first | (simp [show 2 ≤ s + 2 - ws.length by omega]) | (simp [show 1 ≤ s + 2 - ws.length by omega])
theorem nextD_two {u:Bool} {dm y a b rest} {op:Nat} {ka kb:Bool} {s ws}
    (hop : allowedB u op = true) (p : (a :: b :: rest).Perm ws)
    (h0 : opD dm op a b ≠ 0) (hd : opD dm op a b ≠ dm) (hnm : opD dm op a b ∉ (a :: b :: rest))
    (h : RunD u dm y s (opD dm op a b :: kept ka a (kept kb b rest)))
    (f : (Nat × Nat × Nat) → List Nat → Bool) (hf : ∀ g ys,RunD u dm y s ys → f g ys = true) :
    nextD u dm (s + 2 - ws.length) ws f = true:=by
  rcases le_total a b with hab | hba
  · exact nextD_two_sorted hop hab p h0 hd hnm h f hf
  · have he : opD dm op a b = opD dm (flipOp op) b a:=opD_comm dm hop a b
    have hnm' : opD dm (flipOp op) b a ∉ (b :: a :: rest):=by
      rw [← he]; intro hm; exact hnm ((List.Perm.swap _ _ _).mem_iff.1 hm)
    apply nextD_two_sorted (op:=flipOp op) (ka:=kb) (kb:=ka) (flipOp_allowed hop) hba
      ((List.Perm.swap _ _ _).trans p) (he ▸ h0) (he ▸ hd) hnm' _ f hf
    rw [he] at h; apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]; exact List.Perm.swap _ _ _
theorem nextD_complete {u:Bool} {dm y t ws} (h : RunD u dm y t ws) :
    ∀ s,t = s + 1 → ∀ zs,ws.Perm zs → ∀ f : (Nat × Nat × Nat) → List Nat → Bool,
      (∀ g ys,RunD u dm y s ys → f g ys = true) →
      nextD u dm (s + 2 - zs.length) zs f = true:=by
  induction h using Run.fold with
  | done=>simp
  | perm p _ ih=>intro s he zs q; exact ih s he zs (p.trans q)
  | two op ka kb hop h0 hd hnm h _=>intro s he zs p f hf; cases he; exact nextD_two hop p h0 hd hnm h f hf
def span (f:Nat → Bool):Nat → Nat → Bool
  | 0,_=>true
  | n + 1,i=>f i&&span f n (i + 1)
theorem span_ok {f n o} (h : span f n o = true) : ∀ i,o ≤ i → i < o + n → f i = true:=by
  induction n generalizing o with
  | zero=>omega
  | succ n ih =>
    simp only [span,Bool.and_eq_true] at h; intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)
theorem range_split {P:Nat → Prop} {lo mid hi:Nat}
    (h1 : ∀ i,lo ≤ i → i < mid → P i) (h2 : ∀ i,mid ≤ i → i < hi → P i) :
    ∀ i,lo ≤ i → i < hi → P i:=fun i hlo hhi =>
  if h : i < mid then h1 i hlo h else h2 i (Nat.le_of_not_lt h) hhi
def fld (T w i:Nat):Nat :=
  (T >>> (w * i))&&&(if w==6 then 63 else if w==11 then 2047 else if w==13 then 8191 else if w==14 then 16383 else if w==19 then 524287 else if w==20 then 1048575 else if w==32 then 4294967295 else if w==52 then 4503599627370495 else if w==256 then mask256 else 2 ^ w - 1)
def bsr (read:Nat → Nat) (h:Nat):Nat → Nat → Nat → Nat
  | 0,lo,_=>lo
  | f + 1,lo,hi =>
    if lo + 1 < hi then
      (if read ((lo + hi) / 2) ≤ h then bsr read h f ((lo + hi) / 2) hi
       else bsr read h f lo ((lo + hi) / 2))
    else lo
def hw256 (seed w:Nat):Nat :=
  let r:=(w^^^seed) % 1048573
  (r * r + r) % 1048573
def hz (seed:Nat):List Nat → Nat
  | []=>0
  | w :: t=>hw256 seed w + hz seed t
def hk (seed:Nat) (zs:List Nat):Nat:=hz seed zs&&&1048575
def found (S:Nat → Nat → List Nat) (N:Nat → Nat) (idx:Nat → List Nat → Nat)
    (s:Nat) (zs:List Nat):Bool :=
  decide (idx s zs < N s)&&zs.isPerm (S s (idx s zs))
def foundH (S:Nat → Nat → List Nat) (N:Nat → Nat) (htAt:Nat → Nat → Nat)
    (idxH:Nat → Nat → Nat) (s h:Nat) (zs:List Nat):Bool :=
  let i:=idxH s h
  decide (i < N s)&&(htAt s i==h)&&zs.isPerm (S s i)
def nextD_decor (u:Bool) (dm mp:Nat) (slack:Nat) (dws:List (Nat × Nat × Nat))
    (f : (Nat × Nat × Nat) → List (Nat × Nat × Nat) → Bool):Bool :=
  dws.any fun da =>
    let a:=da.1
    let ra:=dws.erase da
    ra.any fun db =>
      let b:=db.1
      a ≤ b&&(let r:=ra.erase db
        (opsOf u).any fun op =>
          let w:=opD dm op a b
          let g:=(op,a,b)
          w != 0&&w != dm&&!(dws.any (fun x=>x.1==w)) &&
            let dw:=(w,opP mp op da.2.1 db.2.1,opP mp op da.2.2 db.2.2)
            (f g (dw :: r)||(slack ≥ 1&&(f g (dw :: da :: r)||f g (dw :: db :: r))) ||
              (slack ≥ 2&&f g (dw :: da :: db :: r))))
theorem nextD_decor_gen (u:Bool) (dm mp:Nat) (dec:Nat → Nat × Nat × Nat)
    (hfst : ∀ w,(dec w).1 = w)
    (hop : ∀ op a b,(opD dm op a b,opP mp op (dec a).2.1 (dec b).2.1,opP mp op (dec a).2.2 (dec b).2.2) = dec (opD dm op a b))
    (slack:Nat) (ws:List Nat) (g : (Nat × Nat × Nat) → List (Nat × Nat × Nat) → Bool) :
    nextD_decor u dm mp slack (ws.map dec) g = nextD u dm slack ws (fun opab zs=>g opab (zs.map dec)):=by
  have hinj : Function.Injective dec:=fun x y h=>by rw [← hfst x,← hfst y,h]
  have herase : ∀ (l:List Nat) x,(l.map dec).erase (dec x) = (l.erase x).map dec :=
    fun l x=>erase_map_inj dec hinj l x
  have hcont : ∀ (l:List Nat) w,(l.map dec).any (fun x=>x.1==w) = l.contains w:=by
    intro l w; apply Bool.eq_iff_iff.2; simp [hfst]
  unfold nextD_decor nextD
  simp only [List.any_map,Function.comp_def,hfst,herase,hcont,hop,List.map_cons]
theorem nextD_decor_eq (u:Bool) {dm:Nat} (hd : dm&&&mask256 = dm)
    (pairs:List (Nat × Nat))
    (hr1 : ∀ r ∈ pairs.map Prod.fst,dm.testBit r = true)
    (hr2 : ∀ r ∈ pairs.map Prod.snd,dm.testBit r = true)
    (slack:Nat) (ws:List Nat) (g : (Nat × Nat × Nat) → List (Nat × Nat × Nat) → Bool) :
    let dec:=fun w=>(w,projBit (pairs.map Prod.fst) w,projBit (pairs.map Prod.snd) w)
    nextD_decor u dm (maskP pairs.length) slack (ws.map dec) g =
      nextD u dm slack ws (fun opab zs=>g opab (zs.map dec)):=by
  intro dec
  apply nextD_decor_gen
  · intro w; rfl
  · intro op a b
    simp only [dec,projBit_opD hd hr1,projBit_opD hd hr2,List.length_map]
def addC (x:Nat) (c:Nat × Nat × Nat):Nat × Nat × Nat :=
  (c.1|||x,c.2.1|||(c.1&&&x),c.2.2|||(c.2.1&&&x))
def cov3 (mp:Nat) (d:Bool) (dws:List (Nat × Nat × Nat)):Nat × Nat × Nat :=
  dws.foldl (fun c dw=>addC (colB mp d dw.2) c) (0,0,0)
def takeOne (c:Nat × Nat × Nat) (x:Nat):Nat:=(c.1^^^x)|||c.2.1
def takeTwo (c:Nat × Nat × Nat) (x y:Nat):Nat :=
  (c.1^^^(x|||y))|||(c.2.1&&&(x^^^y))|||c.2.2
theorem cov3_bit (mp:Nat) (d:Bool) (dws:List (Nat × Nat × Nat)) (i:Nat) :
    let k:=dws.countP (fun dw=>(colB mp d dw.2).testBit i)
    (cov3 mp d dws).1.testBit i = decide (1 ≤ k) ∧
    (cov3 mp d dws).2.1.testBit i = decide (2 ≤ k) ∧
    (cov3 mp d dws).2.2.testBit i = decide (3 ≤ k):=by
  have hgen : ∀ (xs:List (Nat × Nat × Nat)) (c:Nat × Nat × Nat) (k0:Nat),
      (c.1.testBit i = decide (1 ≤ k0) ∧ c.2.1.testBit i = decide (2 ≤ k0) ∧ c.2.2.testBit i = decide (3 ≤ k0)) →
      let k:=k0 + xs.countP (fun dw=>(colB mp d dw.2).testBit i)
      (xs.foldl (fun acc dw=>addC (colB mp d dw.2) acc) c).1.testBit i = decide (1 ≤ k) ∧
      (xs.foldl (fun acc dw=>addC (colB mp d dw.2) acc) c).2.1.testBit i = decide (2 ≤ k) ∧
      (xs.foldl (fun acc dw=>addC (colB mp d dw.2) acc) c).2.2.testBit i = decide (3 ≤ k):=by
    intro xs
    induction xs with
    | nil=>intro c k0 ⟨h1,h2,h3⟩; simp [h1,h2,h3]
    | cons dw xs ih =>
      intro c k0 ⟨h1,h2,h3⟩
      simp only [List.foldl_cons,List.countP_cons]
      have hc : (addC (colB mp d dw.2) c).1.testBit i =
            decide (1 ≤ k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) ∧
          (addC (colB mp d dw.2) c).2.1.testBit i =
            decide (2 ≤ k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) ∧
          (addC (colB mp d dw.2) c).2.2.testBit i =
            decide (3 ≤ k0 + (if (colB mp d dw.2).testBit i then 1 else 0)):=by
        simp only [addC,Nat.testBit_or,Nat.testBit_and,h1,h2,h3]
        cases hb : (colB mp d dw.2).testBit i <;>
          rcases k0 with _ | _ | _ | k0 <;>
          simp [hb,Nat.le_add_left]
      have ih':=ih (addC (colB mp d dw.2) c) (k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) hc
      cases hb : (colB mp d dw.2).testBit i <;> simp only [hb,↓reduceIte,Bool.false_eq_true,Nat.add_zero] at ih' ⊢
      · exact ih'
      · simpa only [Nat.add_assoc,Nat.add_comm 1] using ih'
  simpa only [cov3,Nat.zero_testBit,Nat.zero_add] using hgen dws (0,0,0) 0 (by simp)
theorem cov3_perm (mp:Nat) (d:Bool) {xs ys:List (Nat × Nat × Nat)} (p : xs.Perm ys) :
    cov3 mp d xs = cov3 mp d ys:=by
  have heq : ∀ i,(cov3 mp d xs).1.testBit i = (cov3 mp d ys).1.testBit i ∧
      (cov3 mp d xs).2.1.testBit i = (cov3 mp d ys).2.1.testBit i ∧
      (cov3 mp d xs).2.2.testBit i = (cov3 mp d ys).2.2.testBit i:=by
    intro i
    obtain ⟨a1,a2,a3⟩:=cov3_bit mp d xs i
    obtain ⟨b1,b2,b3⟩:=cov3_bit mp d ys i
    rw [p.countP_eq] at a1 a2 a3
    exact ⟨a1.trans b1.symm,a2.trans b2.symm,a3.trans b3.symm⟩
  apply Prod.ext
  · exact Nat.eq_of_testBit_eq (fun i=>(heq i).1)
  · apply Prod.ext
    · exact Nat.eq_of_testBit_eq (fun i=>(heq i).2.1)
    · exact Nat.eq_of_testBit_eq (fun i=>(heq i).2.2)
theorem takeOne_eq (mp:Nat) (d:Bool) (a:Nat × Nat × Nat) (rest:List (Nat × Nat × Nat)) :
    takeOne (cov3 mp d (a :: rest)) (colB mp d a.2) = (cov3 mp d rest).1:=by
  apply Nat.eq_of_testBit_eq; intro i
  obtain ⟨h1,h2,_⟩:=cov3_bit mp d (a :: rest) i
  obtain ⟨r1,_,_⟩:=cov3_bit mp d rest i
  simp only [takeOne,Nat.testBit_or,Nat.testBit_xor,h1,h2,r1,List.countP_cons]
  set k:=rest.countP (fun dw=>(colB mp d dw.2).testBit i)
  cases ha : (colB mp d a.2).testBit i <;> simp only [ha,Bool.false_eq_true,↓reduceIte] <;>
    rcases k with _ | _ | _ | k
  · decide
  · decide
  · decide
  · simp only [show 1 ≤ k + 3 by omega,show 2 ≤ k + 3 by omega,decide_true,Bool.xor_false,Bool.or_true]
  · decide
  · decide
  · decide
  · simp only [show 1 ≤ k + 3 + 1 by omega,show 2 ≤ k + 3 + 1 by omega,show 1 ≤ k + 3 by omega,
      decide_true,Bool.xor_true,Bool.or_true,Bool.or_false]
theorem takeTwo_eq (mp:Nat) (d:Bool) (a b:Nat × Nat × Nat) (rest:List (Nat × Nat × Nat)) :
    takeTwo (cov3 mp d (a :: b :: rest)) (colB mp d a.2) (colB mp d b.2) = (cov3 mp d rest).1:=by
  apply Nat.eq_of_testBit_eq; intro i
  obtain ⟨h1,h2,h3⟩:=cov3_bit mp d (a :: b :: rest) i
  obtain ⟨r1,_,_⟩:=cov3_bit mp d rest i
  simp only [takeTwo,Nat.testBit_or,Nat.testBit_and,Nat.testBit_xor,h1,h2,h3,r1,List.countP_cons]
  set k:=rest.countP (fun dw=>(colB mp d dw.2).testBit i)
  cases ha : (colB mp d a.2).testBit i <;> cases hb : (colB mp d b.2).testBit i <;>
    simp only [ha,hb,Bool.false_eq_true,↓reduceIte] <;>
    rcases k with _ | _ | _ | k <;>
    (first | decide | simp only [
      show 1 ≤ k + 3 by omega,show 2 ≤ k + 3 by omega,show 3 ≤ k + 3 by omega,
      show 1 ≤ k + 3 + 1 by omega,show 2 ≤ k + 3 + 1 by omega,show 3 ≤ k + 3 + 1 by omega,
      show 1 ≤ k + 3 + 1 + 1 by omega,show 2 ≤ k + 3 + 1 + 1 by omega,show 3 ≤ k + 3 + 1 + 1 by omega,
      decide_true,Bool.xor_true,Bool.xor_false,Bool.or_true,Bool.or_false,Bool.and_true,Bool.and_false])
theorem cov3_coversD (u:Bool) (mp:Nat) (dw:Nat × Nat × Nat) (rest:List (Nat × Nat × Nat)) :
    ((cov3 mp (!u) rest).1|||colB mp (!u) dw.2==mp) = coversD u mp (dw :: rest):=by
  have e : ((cov3 mp (!u) rest).1|||colB mp (!u) dw.2) =
      (dw :: rest).foldl (fun acc x=>acc|||colB mp (!u) x.2) 0:=by
    apply Nat.eq_of_testBit_eq; intro i
    obtain ⟨h1,_,_⟩:=cov3_bit mp (!u) rest i
    rw [foldl_or_testBit,Nat.zero_testBit,Bool.false_or,Nat.testBit_or,h1,List.any_cons]
    have hp : decide (1 ≤ rest.countP (fun dw=>(colB mp (!u) dw.2).testBit i)) =
        rest.any (fun x=>(colB mp (!u) x.2).testBit i):=by
      rw [Bool.eq_iff_iff,decide_eq_true_eq,Nat.succ_le_iff,List.countP_pos_iff,List.any_eq_true]
    rw [hp,Bool.or_comm]
  unfold coversD; exact congrArg (·==mp) e
def nextD_cov (u:Bool) (dm mp slack:Nat) (dws:List (Nat × Nat × Nat))
    (f : (Nat × Nat × Nat) → List (Nat × Nat × Nat) → Bool):Bool :=
  let ori:=!u
  let cov:=cov3 mp ori dws
  dws.any fun da =>
    let a:=da.1
    let ca:=colB mp ori da.2
    let ra:=dws.erase da
    ra.any fun db =>
      let b:=db.1
      a ≤ b &&
        (let cb:=colB mp ori db.2
         let base0:=takeTwo cov ca cb
         let base1a:=takeOne cov cb
         let base1b:=takeOne cov ca
         let r:=ra.erase db
         (opsOf u).any fun op =>
           let pz:=(opP mp op da.2.1 db.2.1,opP mp op da.2.2 db.2.2)
           let cz:=colB mp ori pz
           let ok0:=(base0|||cz)==mp
           let ok1a:=slack ≥ 1&&((base1a|||cz)==mp)
           let ok1b:=slack ≥ 1&&((base1b|||cz)==mp)
           let ok2:=slack ≥ 2&&((cov.1|||cz)==mp)
           (ok0||ok1a||ok1b||ok2) &&
           (let w:=opD dm op a b
            let g:=(op,a,b)
            w != 0&&w != dm&&!(dws.any (fun x=>x.1==w)) &&
              let dw:=(w,pz)
              ((ok0&&f g (dw :: r))||(ok1a&&f g (dw :: da :: r)) ||
               (ok1b&&f g (dw :: db :: r))||(ok2&&f g (dw :: da :: db :: r)))))
theorem nextD_cov_eq (u:Bool) (dm mp slack:Nat) (dws:List (Nat × Nat × Nat))
    (g : (Nat × Nat × Nat) → List (Nat × Nat × Nat) → Bool) :
    nextD_cov u dm mp slack dws g =
      nextD_decor u dm mp slack dws (fun opab dzs=>coversD u mp dzs&&g opab dzs):=by
  unfold nextD_cov nextD_decor
  dsimp only
  apply Bool.eq_iff_iff.2; simp only [List.any_eq_true,Bool.or_eq_true,Bool.and_eq_true]
  constructor
  · rintro ⟨da,hda,db,hdb,hab,op,hop,_,⟨⟨hw0,hwdm⟩,hnw⟩,hfx⟩
    refine ⟨da,hda,db,hdb,hab,op,hop,⟨⟨hw0,hwdm⟩,hnw⟩,?_⟩
    set pz:=(opP mp op da.2.1 db.2.1,opP mp op da.2.2 db.2.2)
    set dw:=(opD dm op da.1 db.1,pz)
    set ra:=dws.erase da
    set r:=ra.erase db
    have hp : dws.Perm (da :: db :: r):=(List.perm_cons_erase hda).trans (List.Perm.cons _ (List.perm_cons_erase hdb))
    have hc2:=cov3_perm mp (!u) hp
    have hca:=cov3_perm mp (!u) (hp.trans (List.Perm.swap _ _ _))
    have hcov0 : (takeTwo (cov3 mp (!u) dws) (colB mp (!u) da.2) (colB mp (!u) db.2)|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: r):=by rw [hc2,takeTwo_eq]; exact cov3_coversD u mp dw r
    have hcov1a : (takeOne (cov3 mp (!u) dws) (colB mp (!u) db.2)|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: da :: r):=by rw [hca,takeOne_eq]; exact cov3_coversD u mp dw (da :: r)
    have hcov1b : (takeOne (cov3 mp (!u) dws) (colB mp (!u) da.2)|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: db :: r):=by rw [hc2,takeOne_eq]; exact cov3_coversD u mp dw (db :: r)
    have hcov2 : ((cov3 mp (!u) dws).1|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: da :: db :: r):=by rw [hc2]; exact cov3_coversD u mp dw (da :: db :: r)
    rcases hfx with ((⟨hu0,hf0⟩ | ⟨⟨hsl1,hu1a⟩,hf1a⟩) | ⟨⟨hsl1,hu1b⟩,hf1b⟩) | ⟨⟨hsl2,hu2⟩,hf2⟩
    · left; left; exact ⟨hcov0 ▸ hu0,hf0⟩
    · left; right; exact ⟨hsl1,Or.inl ⟨hcov1a ▸ hu1a,hf1a⟩⟩
    · left; right; exact ⟨hsl1,Or.inr ⟨hcov1b ▸ hu1b,hf1b⟩⟩
    · right; exact ⟨hsl2,hcov2 ▸ hu2,hf2⟩
  · rintro ⟨da,hda,db,hdb,hab,op,hop,⟨⟨hw0,hwdm⟩,hnw⟩,hfx⟩
    refine ⟨da,hda,db,hdb,hab,op,hop,?_⟩
    set pz:=(opP mp op da.2.1 db.2.1,opP mp op da.2.2 db.2.2)
    set dw:=(opD dm op da.1 db.1,pz)
    set ra:=dws.erase da
    set r:=ra.erase db
    have hp : dws.Perm (da :: db :: r):=(List.perm_cons_erase hda).trans (List.Perm.cons _ (List.perm_cons_erase hdb))
    have hc2:=cov3_perm mp (!u) hp
    have hca:=cov3_perm mp (!u) (hp.trans (List.Perm.swap _ _ _))
    have hcov0 : (takeTwo (cov3 mp (!u) dws) (colB mp (!u) da.2) (colB mp (!u) db.2)|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: r):=by rw [hc2,takeTwo_eq]; exact cov3_coversD u mp dw r
    have hcov1a : (takeOne (cov3 mp (!u) dws) (colB mp (!u) db.2)|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: da :: r):=by rw [hca,takeOne_eq]; exact cov3_coversD u mp dw (da :: r)
    have hcov1b : (takeOne (cov3 mp (!u) dws) (colB mp (!u) da.2)|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: db :: r):=by rw [hc2,takeOne_eq]; exact cov3_coversD u mp dw (db :: r)
    have hcov2 : ((cov3 mp (!u) dws).1|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: da :: db :: r):=by rw [hc2]; exact cov3_coversD u mp dw (da :: db :: r)
    rcases hfx with (⟨hc0,hg0⟩ | ⟨hsl1,⟨hc1a,hg1a⟩ | ⟨hc1b,hg1b⟩⟩) | ⟨hsl2,hc2',hg2⟩
    · have u0 : (takeTwo (cov3 mp (!u) dws) (colB mp (!u) da.2) (colB mp (!u) db.2)|||colB mp (!u) pz==mp) = true:=hcov0.symm ▸ hc0
      exact ⟨Or.inl (Or.inl (Or.inl u0)),⟨⟨hw0,hwdm⟩,hnw⟩,Or.inl (Or.inl (Or.inl ⟨u0,hg0⟩))⟩
    · have u1a : (takeOne (cov3 mp (!u) dws) (colB mp (!u) db.2)|||colB mp (!u) pz==mp) = true:=hcov1a.symm ▸ hc1a
      exact ⟨Or.inl (Or.inl (Or.inr ⟨hsl1,u1a⟩)),⟨⟨hw0,hwdm⟩,hnw⟩,Or.inl (Or.inl (Or.inr ⟨⟨hsl1,u1a⟩,hg1a⟩))⟩
    · have u1b : (takeOne (cov3 mp (!u) dws) (colB mp (!u) da.2)|||colB mp (!u) pz==mp) = true:=hcov1b.symm ▸ hc1b
      exact ⟨Or.inl (Or.inr ⟨hsl1,u1b⟩),⟨⟨hw0,hwdm⟩,hnw⟩,Or.inl (Or.inr ⟨⟨hsl1,u1b⟩,hg1b⟩)⟩
    · have u2 : ((cov3 mp (!u) dws).1|||colB mp (!u) pz==mp) = true:=hcov2.symm ▸ hc2'
      exact ⟨Or.inr ⟨hsl2,u2⟩,⟨⟨hw0,hwdm⟩,hnw⟩,Or.inr ⟨⟨hsl2,u2⟩,hg2⟩⟩
def mkWire (dictB:Nat → Nat → Nat) (ndict dw dmask i:Nat):Nat :=
  if i < ndict then (dictB (i / 256) (i / 16 % 16) >>> (dw * (i % 16)))&&&dmask else 0
def addP (pm i d L:Nat) (rs:List Nat) (ops:List (Nat × Nat × Nat)):List (Nat × Nat × (Nat × List Nat)) :=
  if pm.testBit i then [(d,L,runOps d (0,rs.map (·&&&d)) ops)] else []
theorem mem_addP {pm i d L rs ops e} (h : e ∈ addP pm i d L rs ops) :
    pm.testBit i = true ∧ e = (d,L,runOps d (0,rs.map (·&&&d)) ops):=by
  unfold addP at h; split at h
  · rename_i ht; exact ⟨ht,List.mem_singleton.1 h⟩
  · simp at h
def isoOK (ms:List (Nat × Nat)) (d1 d2 T1 T2:Nat) (r1 r2:List Nat):Bool :=
  ms.all moveOK256&&(d1&&&mask256==d1)&&(applyMoves ms d2==d1) &&
    (applyMoves ms T2==T1)&&r2.all (fun r=>availB true d1 r1 (applyMoves ms r))
theorem lower_iso_b {d1 d2 T1 T2 L:Nat} {r1 r2:List Nat}
    (ms:List (Nat × Nat)) (h : isoOK ms d1 d2 T1 T2 r1 r2 = true)
    (h1 : Lower true d1 r1 T1 L) : Lower true d2 r2 T2 L:=by
  simp only [isoOK,Bool.and_eq_true,beq_iff_eq] at h
  exact lower_iso ms h.1.1.1.1 h.1.1.1.2 h.1.1.2 h.1.2 h.2 h1
def sliceOK (d dSub T TSub:Nat) (r rSub:List Nat) (singles:List (Nat × Nat × Nat)):Bool :=
  (d&&&mask256==d)&&d.testBit 0&&!(T.testBit 0)&&r.all (fun x=>!x.testBit 0) &&
    (dSub&&&mask256==dSub)&&(dSub&&&d==dSub)&&(T&&&dSub==TSub&&&dSub) &&
    !(isConstB d T)&&!(isConstB dSub TSub)&&r.all (availB true dSub rSub) &&
    decide (singles.map Prod.fst).Nodup &&
    singles.all (fun e=>isConstB dSub e.1&&essOK d (T&&&d) (r.map (·&&&d)) e.1 e.2)
theorem lower_slice_b {d dSub T TSub L:Nat} {r rSub:List Nat}
    (singles:List (Nat × Nat × Nat))
    (h : sliceOK d dSub T TSub r rSub singles = true)
    (hprior : Lower true dSub rSub TSub L) : Lower true d r T (L + singles.length):=by
  simp only [sliceOK,Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true',decide_eq_true_eq] at h
  exact lower_slice h.1.1.1.1.1.1.1.1.1.1.1 h.1.1.1.1.1.1.1.1.1.1.2 h.1.1.1.1.1.1.1.1.1.2
    h.1.1.1.1.1.1.1.1.2 h.1.1.1.1.1.1.1.2 h.1.1.1.1.1.1.2 h.1.1.1.1.1.2 h.1.1.1.1.2
    h.1.1.1.2 h.1.1.2 singles h.1.2 h.2 hprior
def essOKB (d T:Nat) (r:List Nat) (singles:List (Nat × Nat × Nat)):Bool :=
  (d&&&mask256==d)&&d.testBit 0&&!(T.testBit 0)&&r.all (fun x=>!x.testBit 0) &&
    !(isConstB d T)&&decide (singles.map Prod.fst).Nodup &&
    singles.all (fun e=>essOK d (T&&&d) (r.map (·&&&d)) e.1 e.2)
theorem lower_ess_b {d T:Nat} {r:List Nat}
    (singles:List (Nat × Nat × Nat)) (h : essOKB d T r singles = true) :
    Lower true d r T (singles.length - 1):=by
  simp only [essOKB,Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true',decide_eq_true_eq] at h
  exact lower_ess_count h.1.1.1.1.1.1 h.1.1.1.1.1.2 h.1.1.1.1.2 h.1.1.1.2 h.1.1.2 singles h.1.2 h.2
def mkReadSt (wireAt:Nat → Nat) (stPool:Nat → Nat) (idw:Nat):Nat → Nat → List Nat
  | 0,_=>[]
  | n + 1,p=>wireAt (fld (stPool (p / 128)) idw (p % 128)) :: mkReadSt wireAt stPool idw n (p + 1)
def mkSS (wireAt:Nat → Nat) (stPool:Nat → Nat) (stOffB:Nat → Nat → Nat) (idw offw s j:Nat):List Nat :=
  let v:=fld (stOffB s (j / 64)) offw (j % 64)
  mkReadSt wireAt stPool idw (v&&&15) (v >>> 4)
def mkReadOps (wireAt:Nat → Nat) (opPool:Nat → Nat) (opw idw idm:Nat):Nat → Nat → List (Nat × Nat × Nat)
  | 0,_=>[]
  | n + 1,p =>
    let code:=fld (opPool (p / 64)) opw (p % 64)
    (code&&&3,wireAt ((code >>> 2)&&&idm),wireAt ((code >>> (2 + idw))&&&idm)) ::
      mkReadOps wireAt opPool opw idw idm n (p + 1)
def mkPO (wireAt:Nat → Nat) (opPool:Nat → Nat) (opOffB:Nat → Nat → Nat) (opw idw idm ooffw s j:Nat):List (Nat × Nat × Nat) :=
  let v:=fld (opOffB s (j / 64)) ooffw (j % 64)
  mkReadOps wireAt opPool opw idw idm (v&&&15) (v >>> 4)
def bar (dm Y:Nat) (mp:Nat)
    (SD:Nat → Nat → List (Nat × Nat × Nat)) (S:Nat → Nat → List Nat)
    (N:Nat → Nat) (htAt idxH:Nat → Nat → Nat)
    (ori:List Nat → List Nat) (seed:Nat)
    (mkCut:Nat → Nat → (Nat × Nat × Nat) → List Nat → Bool):Nat → Nat → Bool
  | 0,i=>!(S 0 i==[Y])
  | s + 1,i =>
    let dws:=SD (s + 1) i
    !(nextD_cov true dm mp (s + 2 - dws.length) dws fun g dzs =>
        let zs:=dzs.map Prod.fst
        !(mkCut (s + 1) i g zs) &&
        (let cz:=ori zs
         let h:=hk seed cz
         !(foundH S N htAt idxH s h cz)))
def barP (dm Y:Nat) (mp:Nat)
    (SD:Nat → Nat → List (Nat × Nat × Nat)) (S:Nat → Nat → List Nat)
    (N:Nat → Nat) (htAt idxH:Nat → Nat → Nat)
    (ori:List Nat → List Nat) (seed:Nat)
    (mkPools:Nat → Nat → List (Nat × Nat × (Nat × List Nat))):Nat → Nat → Bool
  | 0,i=>!(S 0 i==[Y])
  | s + 1,i =>
    let dws:=SD (s + 1) i
    match mkPools (s + 1) i with
    | [] =>
      !(nextD_cov true dm mp (s + 2 - dws.length) dws fun _ dzs =>
          let zs:=dzs.map Prod.fst
          let cz:=ori zs; let h:=hk seed cz; !(foundH S N htAt idxH s h cz))
    | p :: ps =>
      !(nextD_cov true dm mp (s + 2 - dws.length) dws fun g dzs =>
          let zs:=dzs.map Prod.fst
          !((p :: ps).any fun e=>checkPoolG e.1 e.2.1 s e.2.2 g zs) &&
          (let cz:=ori zs; let h:=hk seed cz; !(foundH S N htAt idxH s h cz)))
theorem lower_of_search {u:Bool} {d T L:Nat} {roots:List Nat} {pairs:List (Nat × Nat)}
    (hinit : (d&&&mask256==d)&&d.testBit 0&&!(T.testBit 0)&&roots.all (fun r=>!r.testBit 0) &&
             !(isConstB d T)&&decide ((roots.map (·&&&d)).Nodup) &&
             pairs.all (fun p=>d.testBit p.1&&d.testBit p.2&&((T&&&d).testBit p.1 != (T&&&d).testBit p.2)) = true)
    (hpf : ∀ zs ∈ (roots.map (·&&&d)).sublists,zs ≠ roots.map (·&&&d) → unorientedCov pairs zs = false)
    (hno : ∀ s ≤ L - 1,RunD u d (T&&&d) s (roots.map (·&&&d)) → False) :
    Lower u d roots T L:=by
  simp only [Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true',decide_eq_true_eq] at hinit
  obtain ⟨⟨⟨⟨⟨⟨hd,hd0⟩,hT0⟩,hR0⟩,hncb⟩,hnd_xs'⟩,hpairs⟩:=hinit
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst d T:=fun h=>by rw [(isConstB_iff _ _).2 h] at hncb; contradiction
  obtain ⟨s,ws,hs_le,hnd,hws_sub,hrun⟩:=reach_to_run hd hd0 hT0 hR0 hnc hr ha
  have hperm_sub : ∃ zs,zs.Sublist (roots.map (·&&&d)) ∧ ws.Perm zs:=by
    refine ⟨(roots.map (·&&&d)).filter (fun x=>decide (x ∈ ws)),List.filter_sublist,?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ hnd_xs')).2 ?_
    intro x; simp only [List.mem_filter,decide_eq_true_eq]
    exact ⟨fun hx=>⟨hws_sub x hx,hx⟩,fun h=>h.2⟩
  obtain ⟨zs,hsub,hpz⟩:=hperm_sub
  have hrun':=Run.perm hpz hrun
  by_cases heq : zs = roots.map (·&&&d)
  · subst heq; exact hno s (by omega) hrun'
  · have hcov:=unorientedCov_ok hd pairs hpairs hrun'
    rw [hpf zs (List.mem_sublists.2 hsub) heq] at hcov; contradiction
theorem barP_eq (dm Y mp:Nat) (SD S N htAt idxH ori seed mkPools s i) :
    barP dm Y mp SD S N htAt idxH ori seed mkPools s i =
      bar dm Y mp SD S N htAt idxH ori seed
        (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s' - 1) e.2.2 g zs) s i:=by
  cases s with
  | zero=>rfl
  | succ s =>
    unfold barP bar; dsimp only
    cases mkPools (s + 1) i with
    | nil=>simp
    | cons p ps=>rfl
theorem bar_all {dm T:Nat} {pairs:List (Nat × Nat)} {r1s r2s mp SD S N htAt idxH ori seed mkCut cap}
    (hd : dm&&&mask256 = dm)
    (hr1_eq : r1s = pairs.map Prod.fst) (hr2_eq : r2s = pairs.map Prod.snd) (hmp_eq : mp = maskP pairs.length)
    (hSD : ∀ s j,SD s j = (S s j).map (fun w=>(w,projBit r1s w,projBit r2s w)))
    (hpairs : pairs.all (fun p=>dm.testBit p.1&&dm.testBit p.2&&!(T&&&dm).testBit p.1&&(T&&&dm).testBit p.2) = true)
    (hr : ∀ {v ys},RunD true dm (T&&&dm) v ys → RunD true dm (T&&&dm) v (ori ys))
    (hcut : ∀ {s i g ys},mkCut (s + 1) i g ys = true → ¬ RunD true dm (T&&&dm) s ys)
    (hc : ∀ s ≤ cap,∀ i < N s,bar dm (T&&&dm) mp SD S N htAt idxH ori seed mkCut s i = true) :
    ∀ s ≤ cap,∀ i < N s,¬ RunD true dm (T&&&dm) s (S s i):=by
  subst hr1_eq hr2_eq hmp_eq
  have hr1 : ∀ r ∈ pairs.map Prod.fst,dm.testBit r = true:=by
    intro r hr'; obtain ⟨p,hp,rfl⟩:=List.mem_map.1 hr'
    have h:=List.all_eq_true.1 hpairs p hp; simp only [Bool.and_eq_true] at h; exact h.1.1.1
  have hr2 : ∀ r ∈ pairs.map Prod.snd,dm.testBit r = true:=by
    intro r hr'; obtain ⟨p,hp,rfl⟩:=List.mem_map.1 hr'
    have h:=List.all_eq_true.1 hpairs p hp; simp only [Bool.and_eq_true] at h; exact h.1.1.2
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    have hb:=hc s hs i hi
    cases s with
    | zero=>simp [bar,zero_done hh rfl] at hb
    | succ s =>
      by_contra! hn
      let F (g:Nat × Nat × Nat) (zs:List Nat) :=
        coversP true pairs zs&&!(mkCut (s + 1) i g zs) &&
        (let cz:=ori zs
         let h:=hk seed cz
         !(foundH S N htAt idxH s h cz))
      have hF (g zs) (hz : RunD true dm (T&&&dm) s zs) : F g zs = true:=by
        have hcz:=hr hz
        have hcutf : mkCut (s + 1) i g zs = false:=by
          cases h : mkCut (s + 1) i g zs with
          | false=>rfl
          | true=>exact absurd hz (hcut h)
        simp only [F,coversP_ok hd pairs hpairs hz,hcutf,Bool.not_false,Bool.true_and,foundH]
        simp only [Bool.not_eq_true',Bool.and_eq_false_imp,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq]
        rintro ⟨hj,_⟩
        by_contra! hp
        have p:=List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
        exact ih s (by omega) (by omega) _ hj (Run.perm p hcz)
      have hN:=nextD_complete hh s rfl _ (List.Perm.refl _) F hF
      dsimp only [bar] at hb
      rw [hSD,List.length_map,nextD_cov_eq,nextD_decor_eq true hd pairs hr1 hr2] at hb
      have hFeq : (fun g zs=>coversD true (maskP pairs.length) (zs.map (fun w=>(w,projBit (pairs.map Prod.fst) w,projBit (pairs.map Prod.snd) w))) &&
          (let zs':=(zs.map (fun w=>(w,projBit (pairs.map Prod.fst) w,projBit (pairs.map Prod.snd) w))).map Prod.fst
           !(mkCut (s + 1) i g zs') &&
           (let cz:=ori zs'
            let h:=hk seed cz
            !(foundH S N htAt idxH s h cz)))) = F:=by
        funext g zs
        have hfst : (zs.map (fun w=>(w,projBit (pairs.map Prod.fst) w,projBit (pairs.map Prod.snd) w))).map Prod.fst = zs:=by
          simp [List.map_map,Function.comp_def]
        rw [coversD_eq,hfst]
        simp only [F,Bool.and_assoc]
      rw [hFeq,hN] at hb
      contradiction
def pickMin (seed:Nat) (orig:List Nat):List (List (Nat × Nat)) → List Nat → Nat → List Nat
  | [],best,_=>best
  | ms :: rest,best,bestH =>
    let img:=orig.map (applyMoves ms)
    let h:=hk seed img
    if h < bestH then pickMin seed orig rest img h else pickMin seed orig rest best bestH
theorem pickMin_runD {u:Bool} {dm Y v} (seed:Nat) (orig:List Nat) (h0 : RunD u dm Y v orig) :
    ∀ (syms:List (List (Nat × Nat))) (best:List Nat) (bestH:Nat),
      syms.all (fun ms=>ms.all moveOK256&&(applyMoves ms dm==dm)&&(applyMoves ms Y==Y)) = true →
      RunD u dm Y v best →
      RunD u dm Y v (pickMin seed orig syms best bestH)
  | [],_,_,_,hb=>hb
  | ms :: rest,best,bestH,hok,hb=>by
    simp only [List.all_cons,Bool.and_eq_true,beq_iff_eq] at hok
    unfold pickMin; dsimp only; split
    · exact pickMin_runD seed orig h0 rest _ _ hok.2 (applyMoves_runD ms hok.1.1.1 hok.1.1.2 hok.1.2 h0)
    · exact pickMin_runD seed orig h0 rest best bestH hok.2 hb
def gvN (w:List Nat) (g : Gate):Nat :=
  match g.op with
  | .and=>g.inputs.foldr (fun i acc=>andD mask256 (w.getD i 0) acc) mask256
  | .or =>g.inputs.foldr (fun i acc=>orD mask256 (w.getD i 0) acc) 0
  | .not=>match g.inputs with | []=>mask256 | i :: _=>negD mask256 (w.getD i 0)
  | _=>0
def execN (gs:List Gate) (w:List Nat):List Nat :=
  gs.foldl (fun l g=>l ++ [gvN l g]) w
theorem gvN_bit (w:List Nat) (g : Gate) (r:Nat) (hr : r < 256)
    (hop : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (gvN w g).testBit r = g.op.eval (g.inputs.map fun i=>(w.map (·.testBit r)).getD i false):=by
  have hm : mask256.testBit r = true:=by simp [mask256_bit,hr]
  have hgd : ∀ i,(w.map (·.testBit r)).getD i false = (w.getD i 0).testBit r:=by
    intro i; simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
    cases w[i]? with | none=>simp | some v=>rfl
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop
  rcases hop with h | h | h
  · simp only [gvN,GateOp.eval,h]
    induction g.inputs with
    | nil=>simp [hm]
    | cons i l ih =>
      rw [List.foldr_cons,List.map_cons,List.all_cons,id_eq,andD,Nat.testBit_and,Nat.testBit_and,hm,Bool.and_true,hgd,ih]
  · simp only [gvN,GateOp.eval,h]
    induction g.inputs with
    | nil=>simp
    | cons i l ih =>
      rw [List.foldr_cons,List.map_cons,List.any_cons,id_eq,orD,Nat.testBit_and,Nat.testBit_or,hm,Bool.and_true,hgd,ih]
  · simp only [gvN,GateOp.eval,h]
    cases g.inputs with
    | nil=>simp [hm]
    | cons i l=>simp only [List.map_cons,List.headD_cons,negD,Nat.testBit_and,Nat.testBit_xor,hm,Bool.and_true,Bool.xor_true,hgd]
theorem execN_bit (gs:List Gate) (w:List Nat) (r:Nat) (hr : r < 256)
    (hfan : ∀ g ∈ gs,g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execN gs w).map (·.testBit r) =
      gs.foldl (fun l g=>l ++ [g.op.eval (g.inputs.map fun i=>l.getD i false)]) (w.map (·.testBit r)):=by
  induction gs generalizing w with
  | nil=>rfl
  | cons g gs ih =>
    simp only [execN,List.foldl_cons] at ih ⊢
    rw [ih _ (fun g' hg'=>hfan g' (List.mem_cons_of_mem _ hg'))]
    simp [gvN_bit w g r hr (hfan g List.mem_cons_self)]
def isNotGate (g : Gate):Bool:=match g.op with | .not=>true | _=>false
theorem execN_reach (u:Bool) (gs:List Gate) (roots:List Nat)
    (hfan : ∀ g ∈ gs,g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hmono : u = false → ∀ g ∈ gs,isNotGate g = false) :
    ∀ (p:Nat) (w bank:List Nat),NatReach u mask256 roots p bank →
      (∀ v ∈ w,Avail u mask256 bank v) →
      ∃ p' bank',p' ≤ p + gs.countP (fun g=>!isNotGate g) ∧ NatReach u mask256 roots p' bank' ∧
        ∀ v ∈ execN gs w,Avail u mask256 bank' v:=by
  have hm256 : mask256&&&mask256 = mask256:=Nat.and_self _
  induction gs with
  | nil=>intro p w bank hr hsup; exact ⟨p,bank,by simp,hr,hsup⟩
  | cons g gs ih =>
    intro p w bank hr hsup
    have hav_gd : ∀ i,Avail u mask256 bank (w.getD i 0):=by
      intro i; by_cases hi : i < w.length
      · exact hsup _ (getD_mem hi)
      · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
    have hstep : ∃ p1 bank1,p1 ≤ p + (if !isNotGate g then 1 else 0) ∧ NatReach u mask256 roots p1 bank1 ∧
        (∀ v ∈ w ++ [gvN w g],Avail u mask256 bank1 v):=by
      have hg:=hfan g List.mem_cons_self
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
      obtain ⟨hop,hlen⟩:=hg
      have hand_m : ∀ a,andD mask256 a mask256&&&mask256 = a&&&mask256:=fun a=>by
        simp [andD,Nat.and_assoc,Nat.and_self]
      have hor_0 : ∀ a,orD mask256 a 0&&&mask256 = a&&&mask256:=fun a=>by
        simp [orD,Nat.and_assoc,Nat.and_self]
      have lift_w : ∀ z,(∀ v ∈ w,Avail u mask256 (z :: bank) v):=fun z v hv=>avail_cons z v (hsup v hv)
      rcases hop with h | h | h
      · have hn : (!isNotGate g) = true:=by simp [isNotGate,h]
        rw [hn]; simp only [ite_true]
        rcases hgi : g.inputs with _ | ⟨i,_ | ⟨j,_ | ⟨k,l⟩⟩⟩
        · exact ⟨p,bank,by omega,hr,fun v hv=>by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inr (by simp [gvN,h,hgi]))⟩
        · exact ⟨p,bank,by omega,hr,fun v hv=>by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; simp only [gvN,h,hgi,List.foldr_cons,List.foldr_nil]
              exact avail_of_eq (hand_m _).symm (hav_gd i)⟩
        · refine ⟨p + 1,opD mask256 0 (w.getD i 0) (w.getD j 0) :: bank,le_rfl,
            ⟨bank,_,_,0,by simp [allowedB],rfl,hr,hav_gd i,hav_gd j⟩,fun v hv=>?_⟩
          rcases List.mem_append.1 hv with hv | hv; · exact lift_w _ v hv
          · rw [List.mem_singleton.1 hv]; simp only [gvN,h,hgi,List.foldr_cons,List.foldr_nil]
            exact Or.inr (Or.inl ⟨_,List.mem_cons_self,by simp [opD,andD,Nat.and_assoc,Nat.and_self]⟩)
        · rw [hgi] at hlen; simp at hlen
      · have hn : (!isNotGate g) = true:=by simp [isNotGate,h]
        rw [hn]; simp only [ite_true]
        rcases hgi : g.inputs with _ | ⟨i,_ | ⟨j,_ | ⟨k,l⟩⟩⟩
        · exact ⟨p,bank,by omega,hr,fun v hv=>by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inl (by simp [gvN,h,hgi]))⟩
        · exact ⟨p,bank,by omega,hr,fun v hv=>by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; simp only [gvN,h,hgi,List.foldr_cons,List.foldr_nil]
              exact avail_of_eq (hor_0 _).symm (hav_gd i)⟩
        · refine ⟨p + 1,opD mask256 1 (w.getD i 0) (w.getD j 0) :: bank,le_rfl,
            ⟨bank,_,_,1,by simp [allowedB],rfl,hr,hav_gd i,hav_gd j⟩,fun v hv=>?_⟩
          rcases List.mem_append.1 hv with hv | hv; · exact lift_w _ v hv
          · rw [List.mem_singleton.1 hv]; simp only [gvN,h,hgi,List.foldr_cons,List.foldr_nil]
            exact Or.inr (Or.inl ⟨_,List.mem_cons_self,by apply Nat.eq_of_testBit_eq; intro r; simp [opD,orD]; cases mask256.testBit r <;> simp⟩)
        · rw [hgi] at hlen; simp at hlen
      · cases u with
        | false =>
          have hbad:=hmono rfl g List.mem_cons_self
          simp [isNotGate,h] at hbad
        | true =>
          have hn : (!isNotGate g) = false:=by simp [isNotGate,h]
          rw [hn]; simp only [Bool.false_eq_true,ite_false,Nat.add_zero]
          rcases hgi : g.inputs with _ | ⟨i,l⟩
          · exact ⟨p,bank,le_rfl,hr,fun v hv=>by
              rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
              · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inr (by simp [gvN,h,hgi]))⟩
          · exact ⟨p,bank,le_rfl,hr,fun v hv=>by
              rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
              · rw [List.mem_singleton.1 hv]; simp only [gvN,h,hgi]
                exact avail_neg hm256 (hav_gd i)⟩
    obtain ⟨p1,bank1,hp1,hr1,hsup1⟩:=hstep
    obtain ⟨p2,bank2,hp2,hr2,hsup2⟩:=ih (fun g' hg'=>hfan g' (List.mem_cons_of_mem _ hg'))
      (fun hu g' hg'=>hmono hu g' (List.mem_cons_of_mem _ hg')) p1 _ bank1 hr1 hsup1
    rw [List.countP_cons]
    cases hb : !isNotGate g <;> simp only [hb,ite_true,Bool.false_eq_true,ite_false] at hp1 ⊢ <;>
      exact ⟨p2,bank2,by omega,hr2,hsup2⟩
def xs256:List Nat :=
  [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
   0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,
   0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
   0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,
   0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,
   0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,
   0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,
   0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]
def pt8 (r:Nat) : Fin 8 → Bool:=fun i=>r.testBit i.val
theorem xs256_bits : ∀ r : Fin 256,xs256.map (·.testBit r.val) = List.ofFn (pt8 r.val):=by
  decide +kernel
theorem countP_not_lt {gs:List Gate} {g : Gate} (hg : g ∈ gs) (hn : isNotGate g = true) :
    gs.countP (fun x=>!isNotGate x) + 1 ≤ gs.length:=by
  induction gs with
  | nil=>simp at hg
  | cons x xs ih =>
    rw [List.countP_cons,List.length_cons]
    rcases List.mem_cons.1 hg with rfl | hxs
    · simp only [hn,Bool.not_true,Bool.false_eq_true,ite_false]
      have:=List.countP_le_length (p:=fun y=>!isNotGate y) (l:=xs); omega
    · have:=ih hxs; cases hb : !isNotGate x <;> simp only [hb,ite_true,Bool.false_eq_true,ite_false] <;> omega
-- [PNP-PREFIX-END]
def dom_41 : Nat := 0x30300000303
def goal_41 : Nat := 0xffaaffaaaa00aa00ffaaffaaaa00aa00ffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_41 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_43 : Nat := 0xf0f00000f0f
def goal_43 : Nat := 0xffaaffaaee00ee00ffaaffaaee00ee00ffaaffaaee00ee00ffaaffaaee00ee00
def roots_43 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_45 : Nat := 0x333300003333
def goal_45 : Nat := 0xfffafffaaa00aa00fffafffaaa00aa00fffafffaaa00aa00fffafffaaa00aa00
def roots_45 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_46 : Nat := 0x555500005555
def goal_46 : Nat := 0xfff0fff0cc00cc00fff0fff0cc00cc00fff0fff0cc00cc00fff0fff0cc00cc00
def roots_46 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_47 : Nat := 0xffff0000ffff
def goal_47 : Nat := 0xfffafffaee00ee00fffafffaee00ee00fffafffaee00ee00fffafffaee00ee00
def roots_47 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_51 : Nat := 0xf000f000f000f
def goal_51 : Nat := 0xeeeeaaaaeeee0000eeeeaaaaeeee0000eeeeaaaaeeee0000eeeeaaaaeeee0000
def roots_51 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_53 : Nat := 0x33003300330033
def goal_53 : Nat := 0xfafafafaaaaa0000fafafafaaaaa0000fafafafaaaaa0000fafafafaaaaa0000
def roots_53 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xfefefafaeeee0000fefefafaeeee0000fefefafaeeee0000fefefafaeeee0000
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_57 : Nat := 0x303030303030303
def goal_57 : Nat := 0xffaaffaaaaaaaa00ffaaffaaaaaaaa00ffaaffaaaaaaaa00ffaaffaaaaaaaa00
def roots_57 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_58 : Nat := 0x505050505050505
def goal_58 : Nat := 0xffccff00cccccc00ffccff00cccccc00ffccff00cccccc00ffccff00cccccc00
def roots_58 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xffeeffaaeeeeee00ffeeffaaeeeeee00ffeeffaaeeeeee00ffeeffaaeeeeee00
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xfffafffaaaaaaa00fffafffaaaaaaa00fffafffaaaaaaa00fffafffaaaaaaa00
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_62 : Nat := 0x5555555555555555
def goal_62 : Nat := 0xfffcfff0cccccc00fffcfff0cccccc00fffcfff0cccccc00fffcfff0cccccc00
def roots_62 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfffefffaeeeeee00fffefffaeeeeee00fffefffaeeeeee00fffefffaeeeeee00
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_79 : Nat := 0xffff000000000000ffff
def goal_79 : Nat := 0xfefafefafefafefaee00ee00ee00ee00fefafefafefafefaee00ee00ee00ee00
def roots_79 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_81 : Nat := 0x300030000000000030003
def goal_81 : Nat := 0xffffaaaaffffaaaaaaaa0000aaaa0000ffffaaaaffffaaaaaaaa0000aaaa0000
def roots_81 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_86 : Nat := 0x5500550000000000550055
def goal_86 : Nat := 0xfffff0f0fffff0f0cccc0000cccc0000fffff0f0fffff0f0cccc0000cccc0000
def roots_86 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_87 : Nat := 0xff00ff0000000000ff00ff
def goal_87 : Nat := 0xfffffafafffffafaeeee0000eeee0000fffffafafffffafaeeee0000eeee0000
def roots_87 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_89 : Nat := 0x30303030000000003030303
def goal_89 : Nat := 0xffffaaaaffffaaaaaaaaaa00aaaaaa00ffffaaaaffffaaaaaaaaaa00aaaaaa00
def roots_89 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_90 : Nat := 0x50505050000000005050505
def goal_90 : Nat := 0xffffcc00ffffcc00cccccc00cccccc00ffffcc00ffffcc00cccccc00cccccc00
def roots_90 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_94 : Nat := 0x555555550000000055555555
def goal_94 : Nat := 0xfffffcf0fffffcf0cccccc00cccccc00fffffcf0fffffcf0cccccc00cccccc00
def roots_94 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_95 : Nat := 0xffffffff00000000ffffffff
def goal_95 : Nat := 0xfffffefafffffefaeeeeee00eeeeee00fffffefafffffefaeeeeee00eeeeee00
def roots_95 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_105 : Nat := 0x303000003030000030300000303
def goal_105 : Nat := 0xffaaffaaaaaaaaaaffaaffaaaa00aa00ffaaffaaaaaaaaaaffaaffaaaa00aa00
def roots_105 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_108 : Nat := 0x1111000011110000111100001111
def goal_108 : Nat := 0xfff0fff0f0f0f0f0fff0fff000000000fff0fff0f0f0f0f0fff0fff000000000
def roots_108 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_110 : Nat := 0x5555000055550000555500005555
def goal_110 : Nat := 0xfff0fff0fcf0fcf0fff0fff0cc00cc00fff0fff0fcf0fcf0fff0fff0cc00cc00
def roots_110 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xfffafffafefafefafffafffaee00ee00fffafffafefafefafffafffaee00ee00
def roots_111 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_113 : Nat := 0x30003000300030003000300030003
def goal_113 : Nat := 0xffffaaaaffffaaaaaaaaaaaaaaaa0000ffffaaaaffffaaaaaaaaaaaaaaaa0000
def roots_113 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_116 : Nat := 0x110011001100110011001100110011
def goal_116 : Nat := 0xfffff0f0fffff0f0f0f0f0f000000000fffff0f0fffff0f0f0f0f0f000000000
def roots_116 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xfffff0f0fffff0f0fcfcf0f0cccc0000fffff0f0fffff0f0fcfcf0f0cccc0000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xfffffafafffffafafefefafaeeee0000fffffafafffffafafefefafaeeee0000
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_121 : Nat := 0x3030303030303030303030303030303
def goal_121 : Nat := 0xffffffaaffffaaaaffaaffaaaaaaaa00ffffffaaffffaaaaffaaffaaaaaaaa00
def roots_121 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_122 : Nat := 0x5050505050505050505050505050505
def goal_122 : Nat := 0xffffff00ffffcc00ffccff00cccccc00ffffff00ffffcc00ffccff00cccccc00
def roots_122 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffffffaaffffeeaaffeeffaaeeeeee00ffffffaaffffeeaaffeeffaaeeeeee00
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_124 : Nat := 0x11111111111111111111111111111111
def goal_124 : Nat := 0xfffffff0fffff0f0fff0fff000000000fffffff0fffff0f0fff0fff000000000
def roots_124 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xfffffffafffffafafffafffaaaaaaa00fffffffafffffafafffafffaaaaaaa00
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_126 : Nat := 0x55555555555555555555555555555555
def goal_126 : Nat := 0xfffffff0fffffcf0fffcfff0cccccc00fffffff0fffffcf0fffcfff0cccccc00
def roots_126 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xfffffffafffffefafffefffaeeeeee00fffffffafffffefafffefffaeeeeee00
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_137 : Nat := 0x30300000000000000000000000000000303
def goal_137 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_137 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_138 : Nat := 0x50500000000000000000000000000000505
def goal_138 : Nat := 0xffccffccffccffccffccffccffccffcccc00cc00cc00cc00cc00cc00cc00cc00
def roots_138 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_139 : Nat := 0xf0f00000000000000000000000000000f0f
def goal_139 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffeeee00ee00ee00ee00ee00ee00ee00ee00
def roots_139 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_142 : Nat := 0x555500000000000000000000000000005555
def goal_142 : Nat := 0xfffcfffcfffcfffcfffcfffcfffcfffccc00cc00cc00cc00cc00cc00cc00cc00
def roots_142 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_143 : Nat := 0xffff0000000000000000000000000000ffff
def goal_143 : Nat := 0xfffefffefffefffefffefffefffefffeee00ee00ee00ee00ee00ee00ee00ee00
def roots_143 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_146 : Nat := 0x5000500000000000000000000000000050005
def goal_146 : Nat := 0xffffccccffffccccffffccccffffcccccccc0000cccc0000cccc0000cccc0000
def roots_146 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_147 : Nat := 0xf000f000000000000000000000000000f000f
def goal_147 : Nat := 0xffffeeeeffffeeeeffffeeeeffffeeeeeeee0000eeee0000eeee0000eeee0000
def roots_147 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_149 : Nat := 0x33003300000000000000000000000000330033
def goal_149 : Nat := 0xfffffafafffffafafffffafafffffafaaaaa0000aaaa0000aaaa0000aaaa0000
def roots_149 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_150 : Nat := 0x55005500000000000000000000000000550055
def goal_150 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfccccc0000cccc0000cccc0000cccc0000
def roots_150 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_151 : Nat := 0xff00ff00000000000000000000000000ff00ff
def goal_151 : Nat := 0xfffffefefffffefefffffefefffffefeeeee0000eeee0000eeee0000eeee0000
def roots_151 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_153 : Nat := 0x303030300000000000000000000000003030303
def goal_153 : Nat := 0xffffffaaffffffaaffffffaaffffffaaaaaaaa00aaaaaa00aaaaaa00aaaaaa00
def roots_153 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_154 : Nat := 0x505050500000000000000000000000005050505
def goal_154 : Nat := 0xffffffccffffffccffffffccffffffcccccccc00cccccc00cccccc00cccccc00
def roots_154 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def goal_155 : Nat := 0xffffffeeffffffeeffffffeeffffffeeeeeeee00eeeeee00eeeeee00eeeeee00
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_157 : Nat := 0x3333333300000000000000000000000033333333
def goal_157 : Nat := 0xfffffffafffffffafffffffafffffffaaaaaaa00aaaaaa00aaaaaa00aaaaaa00
def roots_157 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_158 : Nat := 0x5555555500000000000000000000000055555555
def goal_158 : Nat := 0xfffffffcfffffffcfffffffcfffffffccccccc00cccccc00cccccc00cccccc00
def roots_158 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_159 : Nat := 0xffffffff000000000000000000000000ffffffff
def goal_159 : Nat := 0xfffffffefffffffefffffffefffffffeeeeeee00eeeeee00eeeeee00eeeeee00
def roots_159 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_161 : Nat := 0x30000000300000000000000000000000300000003
def goal_161 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaa00000000aaaaaaaa00000000
def roots_161 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_163 : Nat := 0xf0000000f00000000000000000000000f0000000f
def goal_163 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeeeaaaaaaaa00000000aaaaaaaa00000000
def roots_163 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_166 : Nat := 0x550000005500000000000000000000005500000055
def goal_166 : Nat := 0xfffffffffcfcfcfcfffffffffcfcfcfcf0f0f0f000000000f0f0f0f000000000
def roots_166 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_167 : Nat := 0xff000000ff0000000000000000000000ff000000ff
def goal_167 : Nat := 0xfffffffffefefefefffffffffefefefefafafafa00000000fafafafa00000000
def roots_167 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_168 : Nat := 0x1010000010100000000000000000000010100000101
def goal_168 : Nat := 0xffffffffff00ff00ffffffffff00ff00ff00ff0000000000ff00ff0000000000
def roots_168 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_169 : Nat := 0x3030000030300000000000000000000030300000303
def goal_169 : Nat := 0xffffffffffaaffaaffffffffffaaffaaffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_169 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_170 : Nat := 0x5050000050500000000000000000000050500000505
def goal_170 : Nat := 0xffffffffffccffccffffffffffccffccff00ff00cc00cc00ff00ff00cc00cc00
def roots_170 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_171 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
def goal_171 : Nat := 0xffffffffffeeffeeffffffffffeeffeeffaaffaaee00ee00ffaaffaaee00ee00
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_172 : Nat := 0x11110000111100000000000000000000111100001111
def goal_172 : Nat := 0xfffffffffff0fff0fffffffffff0fff0fff0fff000000000fff0fff000000000
def roots_172 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_173 : Nat := 0x33330000333300000000000000000000333300003333
def goal_173 : Nat := 0xfffffffffffafffafffffffffffafffafffafffaaa00aa00fffafffaaa00aa00
def roots_173 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_174 : Nat := 0x55550000555500000000000000000000555500005555
def goal_174 : Nat := 0xfffffffffffcfffcfffffffffffcfffcfff0fff0cc00cc00fff0fff0cc00cc00
def roots_174 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_175 : Nat := 0xffff0000ffff00000000000000000000ffff0000ffff
def goal_175 : Nat := 0xfffffffffffefffefffffffffffefffefffafffaee00ee00fffafffaee00ee00
def roots_175 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_177 : Nat := 0x300030003000300000000000000000003000300030003
def goal_177 : Nat := 0xffffffffffffaaaaffffffffffffaaaaaaaaaaaaaaaa0000aaaaaaaaaaaa0000
def roots_177 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_178 : Nat := 0x500050005000500000000000000000005000500050005
def goal_178 : Nat := 0xffffffffffffccccffffffffffffcccccccc0000cccc0000cccc0000cccc0000
def roots_178 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_179 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f
def goal_179 : Nat := 0xffffffffffffeeeeffffffffffffeeeeeeeeaaaaeeee0000eeeeaaaaeeee0000
def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_180 : Nat := 0x1100110011001100000000000000000011001100110011
def goal_180 : Nat := 0xfffffffffffff0f0fffffffffffff0f0f0f0f0f000000000f0f0f0f000000000
def roots_180 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_182 : Nat := 0x5500550055005500000000000000000055005500550055
def goal_182 : Nat := 0xfffffffffffffcfcfffffffffffffcfcfcfcf0f0cccc0000fcfcf0f0cccc0000
def roots_182 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_183 : Nat := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
def goal_183 : Nat := 0xfffffffffffffefefffffffffffffefefefefafaeeee0000fefefafaeeee0000
def roots_183 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_184 : Nat := 0x10101010101010100000000000000000101010101010101
def goal_184 : Nat := 0xffffffffffffff00ffffffffffffff00ff00ff0000000000ff00ff0000000000
def roots_184 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_185 : Nat := 0x30303030303030300000000000000000303030303030303
def goal_185 : Nat := 0xffffffffffffffaaffffffffffffffaaffaaffaaaaaaaa00ffaaffaaaaaaaa00
def roots_185 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_186 : Nat := 0x50505050505050500000000000000000505050505050505
def goal_186 : Nat := 0xffffffffffffffccffffffffffffffccffccff00cccccc00ffccff00cccccc00
def roots_186 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffffffffffeeffffffffffffffeeffeeffaaeeeeee00ffeeffaaeeeeee00
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_188 : Nat := 0x111111111111111100000000000000001111111111111111
def goal_188 : Nat := 0xfffffffffffffff0fffffffffffffff0fff0fff000000000fff0fff000000000
def roots_188 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_189 : Nat := 0x333333333333333300000000000000003333333333333333
def goal_189 : Nat := 0xfffffffffffffffafffffffffffffffafffafffaaaaaaa00fffafffaaaaaaa00
def roots_189 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_190 : Nat := 0x555555555555555500000000000000005555555555555555
def goal_190 : Nat := 0xfffffffffffffffcfffffffffffffffcfffcfff0cccccc00fffcfff0cccccc00
def roots_190 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xfffffffffffffffefffffffffffffffefffefffaeeeeee00fffefffaeeeeee00
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_198 : Nat := 0x55000000000000005500000000000000550000000000000055
def goal_198 : Nat := 0xfffffffffffffffffcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f00000000000000000
def roots_198 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_199 : Nat := 0xff00000000000000ff00000000000000ff00000000000000ff
def goal_199 : Nat := 0xfffffffffffffffffefefefefefefefefafafafafafafafa0000000000000000
def roots_199 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_201 : Nat := 0x303000000000000030300000000000003030000000000000303
def goal_201 : Nat := 0xffffffffffffffffffaaffaaffaaffaaaaaaaaaaaaaaaaaaaa00aa00aa00aa00
def roots_201 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_206 : Nat := 0x5555000000000000555500000000000055550000000000005555
def goal_206 : Nat := 0xfffffffffffffffffffcfffcfffcfffcfcf0fcf0fcf0fcf0cc00cc00cc00cc00
def roots_206 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_207 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def goal_207 : Nat := 0xfffffffffffffffffffefffefffefffefefafefafefafefaee00ee00ee00ee00
def roots_207 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_209 : Nat := 0x30003000000000003000300000000000300030000000000030003
def goal_209 : Nat := 0xffffffffffffffffffffaaaaffffaaaaffffaaaaffffaaaaaaaa0000aaaa0000
def roots_209 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_210 : Nat := 0x50005000000000005000500000000000500050000000000050005
def goal_210 : Nat := 0xffffffffffffffffffffccccffffccccffff0000ffff0000cccc0000cccc0000
def roots_210 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffffffffffffffffffeeeeffffeeeeffffaaaaffffaaaaeeee0000eeee0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_212 : Nat := 0x110011000000000011001100000000001100110000000000110011
def goal_212 : Nat := 0xfffffffffffffffffffff0f0fffff0f0fffff0f0fffff0f00000000000000000
def roots_212 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_213 : Nat := 0x330033000000000033003300000000003300330000000000330033
def goal_213 : Nat := 0xfffffffffffffffffffffafafffffafafffffafafffffafaaaaa0000aaaa0000
def roots_213 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xfffffffffffffffffffffcfcfffffcfcfffff0f0fffff0f0cccc0000cccc0000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xfffffffffffffffffffffefefffffefefffffafafffffafaeeee0000eeee0000
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_216 : Nat := 0x1010101000000000101010100000000010101010000000001010101
def goal_216 : Nat := 0xffffffffffffffffffffff00ffffff00ffff0000ffff00000000000000000000
def roots_216 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_217 : Nat := 0x3030303000000000303030300000000030303030000000003030303
def goal_217 : Nat := 0xffffffffffffffffffffffaaffffffaaffffaaaaffffaaaaaaaaaa00aaaaaa00
def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def goal_218 : Nat := 0xffffffffffffffffffffffccffffffccffffcc00ffffcc00cccccc00cccccc00
def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffffffffffffffffffffeeffffffeeffffeeaaffffeeaaeeeeee00eeeeee00
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_220 : Nat := 0x11111111000000001111111100000000111111110000000011111111
def goal_220 : Nat := 0xfffffffffffffffffffffff0fffffff0fffff0f0fffff0f00000000000000000
def roots_220 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def goal_221 : Nat := 0xfffffffffffffffffffffffafffffffafffffafafffffafaaaaaaa00aaaaaa00
def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xfffffffffffffffffffffffcfffffffcfffffcf0fffffcf0cccccc00cccccc00
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffffffffffffffffffefffffffefffffefafffffefaeeeeee00eeeeee00
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_225 : Nat := 0x300000003000000030000000300000003000000030000000300000003
def goal_225 : Nat := 0xffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000
def roots_225 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_228 : Nat := 0x1100000011000000110000001100000011000000110000001100000011
def goal_228 : Nat := 0xfffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000
def roots_228 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def goal_230 : Nat := 0xfffffffffffffffffffffffffcfcfcfcf0f0f0f0f0f0f0f0f0f0f0f000000000
def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def goal_231 : Nat := 0xfffffffffffffffffffffffffefefefefafafafafafafafafafafafa00000000
def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_232 : Nat := 0x10100000101000001010000010100000101000001010000010100000101
def goal_232 : Nat := 0xffffffffffffffffffffffffff00ff00ff00ff0000000000ff00ff0000000000
def roots_232 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffffffffffffffffffaaffaaffaaffaaaaaaaaaaffaaffaaaa00aa00
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffffffffffffffffffccffccff00ff00cc00cc00ff00ff00cc00cc00
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffffffffffffffffffeeffeeffaaffaaeeaaeeaaffaaffaaee00ee00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_236 : Nat := 0x111100001111000011110000111100001111000011110000111100001111
def goal_236 : Nat := 0xfffffffffffffffffffffffffff0fff0fff0fff0f0f0f0f0fff0fff000000000
def roots_236 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xfffffffffffffffffffffffffffafffafffafffafafafafafffafffaaa00aa00
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_238 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def goal_238 : Nat := 0xfffffffffffffffffffffffffffcfffcfff0fff0fcf0fcf0fff0fff0cc00cc00
def roots_238 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffffffffffffffffffefffefffafffafefafefafffafffaee00ee00
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_240 : Nat := 0x1000100010001000100010001000100010001000100010001000100010001
def goal_240 : Nat := 0xffffffffffffffffffffffffffff0000ffff0000ffff00000000000000000000
def roots_240 : List Nat := [xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_241 : Nat := 0x3000300030003000300030003000300030003000300030003000300030003
def goal_241 : Nat := 0xffffffffffffffffffffffffffffaaaaffffaaaaffffaaaaaaaaaaaaaaaa0000
def roots_241 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def goal_242 : Nat := 0xffffffffffffffffffffffffffffccccffff0000ffff0000cccc0000cccc0000
def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffffffffffffffffffffeeeeffffaaaaffffaaaaeeeeaaaaeeee0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_244 : Nat := 0x11001100110011001100110011001100110011001100110011001100110011
def goal_244 : Nat := 0xfffffffffffffffffffffffffffff0f0fffff0f0fffff0f0f0f0f0f000000000
def roots_244 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_245 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
def goal_245 : Nat := 0xfffffffffffffffffffffffffffffafafffffafafffffafafafafafaaaaa0000
def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffffffffffffffffffffffcfcfffff0f0fffff0f0fcfcf0f0cccc0000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffffffffffffffffffefefffffafafffffafafefefafaeeee0000
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_248 : Nat := 0x101010101010101010101010101010101010101010101010101010101010101
def goal_248 : Nat := 0xffffffffffffffffffffffffffffff00ffffff00ffff0000ff00ff0000000000
def roots_248 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffffffffffffffffffaaffffffaaffffaaaaffaaffaaaaaaaa00
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffffffffffffffffffccffffff00ffffcc00ffccff00cccccc00
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffffffffffffffffffeeffffffaaffffeeaaffeeffaaeeeeee00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_252 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
def goal_252 : Nat := 0xfffffffffffffffffffffffffffffff0fffffff0fffff0f0fff0fff000000000
def roots_252 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffffffffffffffffffafffffffafffffafafffafffaaaaaaa00
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffffffffffffffffffcfffffff0fffffcf0fffcfff0cccccc00
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffffffffffffffffffefffffffafffffefafffefffaeeeeee00
def roots_255 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

namespace S_41
def pG:List (Nat×Nat):=[(1,9),(1,33),(8,9),(8,40),(32,33),(32,40)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3f
def xsM:=roots_41.map (·&&&dom_41)
def gM:=goal_41&&&dom_41
def NN:Nat→Nat
|2=>1
|3=>1
|_=>0
def HT:Nat→Nat→Nat
|2,0=>0xc64ca
|3,0=>0xc64ca
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x30300000000c0000000c020200000202
|_,_=>0
def sP:Nat→Nat
|0=>0x924
|_=>0
def sO:Nat→Nat→Nat
|2,0=>3
|3,0=>0x33
|_,_=>0
def wAt:=mkWire dB 3 42 0x3ffffffffff
def SS:=mkSS wAt sP sO 2 7
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def mkPools (_ _:Nat):List (Nat×Nat×(Nat×List Nat)):=[]
def mkCut (_ _:Nat) (_:Nat×Nat×Nat) (_:List Nat):Bool:=false
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_41 gM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_41 gM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_41==dom_41)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_41 gM v ys):RunD true dom_41 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_41 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s:Nat) (hs:s≤3):∀ i<NN s,bar dom_41 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 2 2=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤3) (h:RunD true dom_41 gM s xsM):False:=by
  have hmin:2≤s:=by have hl:=run_len h;change 3≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_41 roots_41 goal_41 4:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_41
theorem lowS_41:Lower true dom_41 roots_41 goal_41 4:=S_41.noCircuit
def isoMvS_81:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_81:Lower true dom_81 roots_81 goal_81 4:=lower_iso_b isoMvS_81 (by decide +kernel) lowS_41
def isoMvS_137:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_137:Lower true dom_137 roots_137 goal_137 4:=lower_iso_b isoMvS_137 (by decide +kernel) lowS_41
def isoMvS_138:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_138:Lower true dom_138 roots_138 goal_138 4:=lower_iso_b isoMvS_138 (by decide +kernel) lowS_41
def isoMvS_146:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_146:Lower true dom_146 roots_146 goal_146 4:=lower_iso_b isoMvS_146 (by decide +kernel) lowS_41
def isoMvS_161:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_161:Lower true dom_161 roots_161 goal_161 4:=lower_iso_b isoMvS_161 (by decide +kernel) lowS_41
def isoMvS_168:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_168:Lower true dom_168 roots_168 goal_168 4:=lower_iso_b isoMvS_168 (by decide +kernel) lowS_41
theorem lowS_43:Lower true dom_43 roots_43 goal_43 5:=lower_slice_b [(0xc0c00000c0c,8,10)] (by decide +kernel) lowS_41
namespace S_46
def pG:List (Nat×Nat):=[(2,10),(4,36),(6,14),(6,38),(8,10),(8,40),(12,14),(12,44),(32,36),(32,40),(34,38),(34,42)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfff
def xsM:=roots_46.map (·&&&dom_46)
def gM:=goal_46&&&dom_46
def NN:Nat→Nat
|3=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x98604
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaaaa0000000154000001540282800002828444400004444
|_,_=>0
def sP:Nat→Nat
|0=>0xe4
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|_,_=>0
def wAt:=mkWire dB 4 47 0x7fffffffffff
def SS:=mkSS wAt sP sO 2 7
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def mkPools (_ _:Nat):List (Nat×Nat×(Nat×List Nat)):=[]
def mkCut (_ _:Nat) (_:Nat×Nat×Nat) (_:List Nat):Bool:=false
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_46 gM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_46 gM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_46==dom_46)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_46 gM v ys):RunD true dom_46 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_46 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s:Nat) (hs:s≤3):∀ i<NN s,bar dom_46 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 1 3=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤3) (h:RunD true dom_46 gM s xsM):False:=by
  have hmin:3≤s:=by have hl:=run_len h;change 4≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_46 roots_46 goal_46 4:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_46
theorem lowS_46:Lower true dom_46 roots_46 goal_46 4:=S_46.noCircuit
theorem lowS_139:Lower true dom_139 roots_139 goal_139 5:=lower_slice_b [(0xa0a00000000000000000000000000000a0a,8,9)] (by decide +kernel) lowS_138
namespace S_169
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,129),(8,9),(8,40),(8,136),(32,33),(32,40),(32,160),(128,129),(128,136),(128,160)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfff
def xsM:=roots_169.map (·&&&dom_169)
def gM:=goal_169&&&dom_169
def NN:Nat→Nat
|3=>3
|4=>8
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x3e545373b004d20
|4,0=>0x99e4571e8868f5652c1a50e882ab292893b11cc9
|5,0=>0x532f32aeff22bc0
|6,0=>0x532f3
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xc0800000000000000000000000000000c0b030000030300000000000000000000030000000300c0c00000c0c000000000000000000000c0800000c0800000000000000000000000000000003020000030200c0000000800000000000000000000000c0000000b030000030000000000000000000000030300000300c0800000c08000000000000000000000c0800000c0b030000020200000000000000000000030300000202c0c00000c0c000000000000000000000c0c00000003030000030300000000000000000000020200000202c0c00000000000000000000000000000c0c00000001010000010100000000000000000000010100000100c0c00000000000000000000000000000c0800000003000000030000000000000000000000030000000300808000008080000000000000000000008080000080b030000030300000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x52105210526105e210521f0a5e10a82105d2105c210521b085260a5910872652403210
|_=>0
def sO:Nat→Nat→Nat
|3,0=>0x21022004
|4,0=>0x5eaa952aa0536a5948a8c5
|5,0=>0xf91cab45
|6,0=>0x424
|_,_=>0
def wAt:=mkWire dB 16 170 0x3ffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x14815240915495514052149550405
|_=>0
def oO:Nat→Nat→Nat
|3,0=>0x20000
|4,0=>0x82620000004222
|5,0=>0xb1a1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0xfb9630
|_=>0
def pmB:Nat→Nat→Nat
|3,0=>0x40
|4,0=>0x98011
|5,0=>0x12d
|6,0=>5
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 4 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_168 4 roots_168 ops++addP pm 1 dom_137 4 roots_137 ops++addP pm 2 dom_41 4 roots_41 ops++addP pm 3 dom_161 4 roots_161 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_169 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_161 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_168 4 s (0,roots_168.map (·&&&dom_168)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_169 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_168 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff00000000ffffffff00000000,96)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xff00ff00ff00ff00ff00ff00ff00ff00,120)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff00ff00ff00ff00ff00,120)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_169==dom_169)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_169 gM v ys):RunD true dom_169 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_169 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 3 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 8 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_169 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 4 3=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_169 gM s xsM):False:=by
  have hmin:3≤s:=by have hl:=run_len h;change 4≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_169 roots_169 goal_169 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_169
theorem lowS_169:Lower true dom_169 roots_169 goal_169 7:=S_169.noCircuit
def isoMvS_45:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_45:Lower true dom_45 roots_45 goal_45 5:=lower_iso_b isoMvS_45 (by decide +kernel) lowS_43
def isoMvS_51:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_51:Lower true dom_51 roots_51 goal_51 4:=lower_iso_b isoMvS_51 (by decide +kernel) lowS_46
def isoMvS_53:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_53:Lower true dom_53 roots_53 goal_53 4:=lower_iso_b isoMvS_53 (by decide +kernel) lowS_46
def isoMvS_57:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_57:Lower true dom_57 roots_57 goal_57 5:=lower_iso_b isoMvS_57 (by decide +kernel) lowS_43
def isoMvS_58:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_58:Lower true dom_58 roots_58 goal_58 4:=lower_iso_b isoMvS_58 (by decide +kernel) lowS_46
def isoMvS_86:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_86:Lower true dom_86 roots_86 goal_86 4:=lower_iso_b isoMvS_86 (by decide +kernel) lowS_46
def isoMvS_89:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_89:Lower true dom_89 roots_89 goal_89 5:=lower_iso_b isoMvS_89 (by decide +kernel) lowS_43
def isoMvS_90:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_90:Lower true dom_90 roots_90 goal_90 4:=lower_iso_b isoMvS_90 (by decide +kernel) lowS_46
def isoMvS_105:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_105:Lower true dom_105 roots_105 goal_105 5:=lower_iso_b isoMvS_105 (by decide +kernel) lowS_43
def isoMvS_108:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]
theorem lowS_108:Lower true dom_108 roots_108 goal_108 4:=lower_iso_b isoMvS_108 (by decide +kernel) lowS_46
def isoMvS_113:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_113:Lower true dom_113 roots_113 goal_113 5:=lower_iso_b isoMvS_113 (by decide +kernel) lowS_43
def isoMvS_116:List (Nat×Nat):=[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]
theorem lowS_116:Lower true dom_116 roots_116 goal_116 4:=lower_iso_b isoMvS_116 (by decide +kernel) lowS_46
def isoMvS_142:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_142:Lower true dom_142 roots_142 goal_142 5:=lower_iso_b isoMvS_142 (by decide +kernel) lowS_43
def isoMvS_147:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_147:Lower true dom_147 roots_147 goal_147 5:=lower_iso_b isoMvS_147 (by decide +kernel) lowS_139
def isoMvS_149:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_149:Lower true dom_149 roots_149 goal_149 5:=lower_iso_b isoMvS_149 (by decide +kernel) lowS_43
def isoMvS_150:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_150:Lower true dom_150 roots_150 goal_150 5:=lower_iso_b isoMvS_150 (by decide +kernel) lowS_43
def isoMvS_153:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_153:Lower true dom_153 roots_153 goal_153 5:=lower_iso_b isoMvS_153 (by decide +kernel) lowS_139
def isoMvS_154:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_154:Lower true dom_154 roots_154 goal_154 5:=lower_iso_b isoMvS_154 (by decide +kernel) lowS_139
def isoMvS_163:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_163:Lower true dom_163 roots_163 goal_163 5:=lower_iso_b isoMvS_163 (by decide +kernel) lowS_43
def isoMvS_166:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_166:Lower true dom_166 roots_166 goal_166 5:=lower_iso_b isoMvS_166 (by decide +kernel) lowS_43
def isoMvS_170:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_170:Lower true dom_170 roots_170 goal_170 5:=lower_iso_b isoMvS_170 (by decide +kernel) lowS_139
def isoMvS_172:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_172:Lower true dom_172 roots_172 goal_172 5:=lower_iso_b isoMvS_172 (by decide +kernel) lowS_139
def isoMvS_177:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_177:Lower true dom_177 roots_177 goal_177 5:=lower_iso_b isoMvS_177 (by decide +kernel) lowS_139
def isoMvS_178:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_178:Lower true dom_178 roots_178 goal_178 5:=lower_iso_b isoMvS_178 (by decide +kernel) lowS_43
def isoMvS_180:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_180:Lower true dom_180 roots_180 goal_180 5:=lower_iso_b isoMvS_180 (by decide +kernel) lowS_43
def isoMvS_184:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_184:Lower true dom_184 roots_184 goal_184 5:=lower_iso_b isoMvS_184 (by decide +kernel) lowS_43
def isoMvS_198:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_198:Lower true dom_198 roots_198 goal_198 5:=lower_iso_b isoMvS_198 (by decide +kernel) lowS_43
def isoMvS_201:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_201:Lower true dom_201 roots_201 goal_201 5:=lower_iso_b isoMvS_201 (by decide +kernel) lowS_139
def isoMvS_209:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_209:Lower true dom_209 roots_209 goal_209 7:=lower_iso_b isoMvS_209 (by decide +kernel) lowS_169
def isoMvS_210:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_210:Lower true dom_210 roots_210 goal_210 5:=lower_iso_b isoMvS_210 (by decide +kernel) lowS_139
def isoMvS_212:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_212:Lower true dom_212 roots_212 goal_212 5:=lower_iso_b isoMvS_212 (by decide +kernel) lowS_139
def isoMvS_216:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_216:Lower true dom_216 roots_216 goal_216 5:=lower_iso_b isoMvS_216 (by decide +kernel) lowS_43
def isoMvS_225:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_225:Lower true dom_225 roots_225 goal_225 5:=lower_iso_b isoMvS_225 (by decide +kernel) lowS_139
def isoMvS_228:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_228:Lower true dom_228 roots_228 goal_228 5:=lower_iso_b isoMvS_228 (by decide +kernel) lowS_139
def isoMvS_232:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_232:Lower true dom_232 roots_232 goal_232 5:=lower_iso_b isoMvS_232 (by decide +kernel) lowS_43
def isoMvS_240:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_240:Lower true dom_240 roots_240 goal_240 5:=lower_iso_b isoMvS_240 (by decide +kernel) lowS_43
theorem lowS_47:Lower true dom_47 roots_47 goal_47 6:=lower_slice_b [(0xcccc0000cccc,8,10)] (by decide +kernel) lowS_45
theorem lowS_55:Lower true dom_55 roots_55 goal_55 5:=lower_slice_b [(0xcc00cc00cc00cc,16,18)] (by decide +kernel) lowS_53
theorem lowS_59:Lower true dom_59 roots_59 goal_59 6:=lower_slice_b [(0xc0c0c0c0c0c0c0c,8,10)] (by decide +kernel) lowS_57
namespace S_121
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(8,9),(8,40),(16,17),(16,80),(24,25),(24,56),(24,88),(32,33),(32,40),(48,49),(48,56),(48,112),(64,65),(64,80),(72,73),(72,88),(72,104),(96,97),(96,104),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_121.map (·&&&dom_121)
def gM:=goal_121&&&dom_121
def NN:Nat→Nat
|3=>1
|4=>4
|5=>10
|6=>4
|7=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x12653
|4,0=>0x193c809d0f00d1e00823
|5,0=>0x847868153d776ac652813a7791d8e41d19f138bf0a88d05b9d
|6,0=>0xb9efe6f9be33df731529
|7,0=>0xb9efe
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xc0c0000080800000c0c00000808030003000200020003000300020002c0c0c000c0c0c000c0c0c000c0c0c02020200020202000202020002020200c0c0c0c080808080c0c0c0c080008030203020302030203020302030203028080808080808080800080008000800000303000003030000000200000002c0c00000c0c00000c0c00000c0c000202020202020202020202020202020200000000c0c0c08000000000c0c0c0b030303030303030000000000000000c0c0c0c000000000c0c0c0c00000003030202030302020303020203030000c000c000c000c000c000c000c000c03030303030303030202020202020202
|0,1=>0x202000002020000020200000202c0c0c0c0c0c0c0c0c000c000c000c03030303030303030302030203020302c0c0c0c0c0c0c0c0c0c0c0c00000001010101010101010101010100000000000000000000808000000000000080b030303020202020303030302020202000000008080808000000000808080b030000030302020303000003030202
|_,_=>0
def sP:Nat→Nat
|0=>0xce1310670989519c262486709883384d824867338833d82625467080c3384d420ce134c92384d120e0709883384cf20ce6710670998459c2620cea4906132087098a418820
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|4,0=>0x26a3944a845
|5,0=>0x26b47682ced9ab2f652c8d8f2986
|6,0=>0xcab7dacb536
|7,0=>0x6a5
|_,_=>0
def wAt:=mkWire dB 25 122 0x3ffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x19130d31f90730db9931130f698
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x42312100000011000001
|6,0=>0x817161
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 8
def pmP:Nat→Nat
|0=>0x3ff77d5b30a185080
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x2430051006
|6,0=>0x7a98
|7,0=>0xa
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 6 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_113 5 roots_113 ops++addP pm 1 dom_41 4 roots_41 ops++addP pm 2 dom_89 5 roots_89 ops++addP pm 3 dom_81 4 roots_81 ops++addP pm 4 dom_105 5 roots_105 ops++addP pm 5 dom_57 5 roots_57 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_121 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_57 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_113 5 s (0,roots_113.map (·&&&dom_113)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_121 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_113 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_121==dom_121)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_121 gM v ys):RunD true dom_121 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_121 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 4 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
theorem checked (s:Nat) (hs:s≤7):∀ i<NN s,bar dom_121 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
  · exact z7 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 4 4=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤7) (h:RunD true dom_121 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_121 roots_121 goal_121 8:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_121
theorem lowS_121:Lower true dom_121 roots_121 goal_121 8:=S_121.noCircuit
theorem lowS_143:Lower true dom_143 roots_143 goal_143 6:=lower_slice_b [(0xaaaa0000000000000000000000000000aaaa,8,9)] (by decide +kernel) lowS_142
theorem lowS_155:Lower true dom_155 roots_155 goal_155 6:=lower_slice_b [(0xa0a0a0a0000000000000000000000000a0a0a0a,8,9)] (by decide +kernel) lowS_154
theorem lowS_171:Lower true dom_171 roots_171 goal_171 8:=lower_slice_b [(0xc0c00000c0c000000000000000000000c0c00000c0c,8,10)] (by decide +kernel) lowS_169
namespace S_174
def pG:List (Nat×Nat):=[(2,10),(2,130),(4,36),(4,132),(6,14),(6,38),(6,134),(8,10),(8,40),(8,136),(12,14),(12,44),(12,140),(32,36),(32,40),(32,160),(34,38),(34,42),(34,162),(128,130),(128,132),(128,136),(128,160)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffff
def xsM:=roots_174.map (·&&&dom_174)
def gM:=goal_174&&&dom_174
def NN:Nat→Nat
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x97ff8
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x55550000000000000000000000000000555500000000aa000000aa0000000000000000000000aa000000aa0141400001414000000000000000000001414000014142222000022220000000000000000000022220000222255550000555500000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x4688
|_=>0
def sO:Nat→Nat→Nat
|6,0=>5
|_,_=>0
def wAt:=mkWire dB 5 175 0x7fffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 7
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def pmP:Nat→Nat
|0=>0xf0
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 1 (j%128);fld (pmP (k/32)) 4 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_172 5 roots_172 ops++addP pm 1 dom_170 5 roots_170 ops++addP pm 2 dom_166 5 roots_166 ops++addP pm 3 dom_142 5 roots_142 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_174 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_172 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_166 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_142 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_172 5 s (0,roots_172.map (·&&&dom_172)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_174 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_172 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_174==dom_174)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_174 gM v ys):RunD true dom_174 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_174 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_174 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 3 4=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_174 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_174 roots_174 goal_174 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_174
theorem lowS_174:Lower true dom_174 roots_174 goal_174 7:=S_174.noCircuit
def isoMvS_61:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_61:Lower true dom_61 roots_61 goal_61 6:=lower_iso_b isoMvS_61 (by decide +kernel) lowS_47
def isoMvS_62:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_62:Lower true dom_62 roots_62 goal_62 5:=lower_iso_b isoMvS_62 (by decide +kernel) lowS_55
def isoMvS_79:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_79:Lower true dom_79 roots_79 goal_79 5:=lower_iso_b isoMvS_79 (by decide +kernel) lowS_55
def isoMvS_87:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_87:Lower true dom_87 roots_87 goal_87 6:=lower_iso_b isoMvS_87 (by decide +kernel) lowS_47
def isoMvS_94:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_94:Lower true dom_94 roots_94 goal_94 5:=lower_iso_b isoMvS_94 (by decide +kernel) lowS_55
def isoMvS_110:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_110:Lower true dom_110 roots_110 goal_110 5:=lower_iso_b isoMvS_110 (by decide +kernel) lowS_55
def isoMvS_118:List (Nat×Nat):=[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_118:Lower true dom_118 roots_118 goal_118 5:=lower_iso_b isoMvS_118 (by decide +kernel) lowS_55
def isoMvS_122:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_122:Lower true dom_122 roots_122 goal_122 5:=lower_iso_b isoMvS_122 (by decide +kernel) lowS_55
def isoMvS_124:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_124:Lower true dom_124 roots_124 goal_124 5:=lower_iso_b isoMvS_124 (by decide +kernel) lowS_55
def isoMvS_151:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_151:Lower true dom_151 roots_151 goal_151 6:=lower_iso_b isoMvS_151 (by decide +kernel) lowS_143
def isoMvS_157:List (Nat×Nat):=[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_157:Lower true dom_157 roots_157 goal_157 6:=lower_iso_b isoMvS_157 (by decide +kernel) lowS_143
def isoMvS_158:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_158:Lower true dom_158 roots_158 goal_158 6:=lower_iso_b isoMvS_158 (by decide +kernel) lowS_143
def isoMvS_167:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_167:Lower true dom_167 roots_167 goal_167 6:=lower_iso_b isoMvS_167 (by decide +kernel) lowS_143
def isoMvS_173:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_173:Lower true dom_173 roots_173 goal_173 8:=lower_iso_b isoMvS_173 (by decide +kernel) lowS_171
def isoMvS_179:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_179:Lower true dom_179 roots_179 goal_179 7:=lower_iso_b isoMvS_179 (by decide +kernel) lowS_174
def isoMvS_182:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_182:Lower true dom_182 roots_182 goal_182 8:=lower_iso_b isoMvS_182 (by decide +kernel) lowS_121
def isoMvS_185:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_185:Lower true dom_185 roots_185 goal_185 8:=lower_iso_b isoMvS_185 (by decide +kernel) lowS_171
def isoMvS_186:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_186:Lower true dom_186 roots_186 goal_186 7:=lower_iso_b isoMvS_186 (by decide +kernel) lowS_174
def isoMvS_188:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_188:Lower true dom_188 roots_188 goal_188 6:=lower_iso_b isoMvS_188 (by decide +kernel) lowS_143
def isoMvS_199:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_199:Lower true dom_199 roots_199 goal_199 6:=lower_iso_b isoMvS_199 (by decide +kernel) lowS_143
def isoMvS_206:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_206:Lower true dom_206 roots_206 goal_206 8:=lower_iso_b isoMvS_206 (by decide +kernel) lowS_121
def isoMvS_211:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_211:Lower true dom_211 roots_211 goal_211 8:=lower_iso_b isoMvS_211 (by decide +kernel) lowS_171
def isoMvS_213:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_213:Lower true dom_213 roots_213 goal_213 8:=lower_iso_b isoMvS_213 (by decide +kernel) lowS_171
def isoMvS_214:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_214:Lower true dom_214 roots_214 goal_214 7:=lower_iso_b isoMvS_214 (by decide +kernel) lowS_174
def isoMvS_217:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_217:Lower true dom_217 roots_217 goal_217 8:=lower_iso_b isoMvS_217 (by decide +kernel) lowS_171
def isoMvS_218:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_218:Lower true dom_218 roots_218 goal_218 7:=lower_iso_b isoMvS_218 (by decide +kernel) lowS_174
def isoMvS_220:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_220:Lower true dom_220 roots_220 goal_220 6:=lower_iso_b isoMvS_220 (by decide +kernel) lowS_143
def isoMvS_230:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_230:Lower true dom_230 roots_230 goal_230 6:=lower_iso_b isoMvS_230 (by decide +kernel) lowS_143
def isoMvS_233:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_233:Lower true dom_233 roots_233 goal_233 8:=lower_iso_b isoMvS_233 (by decide +kernel) lowS_171
def isoMvS_234:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_234:Lower true dom_234 roots_234 goal_234 6:=lower_iso_b isoMvS_234 (by decide +kernel) lowS_143
def isoMvS_236:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]
theorem lowS_236:Lower true dom_236 roots_236 goal_236 7:=lower_iso_b isoMvS_236 (by decide +kernel) lowS_174
def isoMvS_241:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_241:Lower true dom_241 roots_241 goal_241 8:=lower_iso_b isoMvS_241 (by decide +kernel) lowS_171
def isoMvS_242:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_242:Lower true dom_242 roots_242 goal_242 6:=lower_iso_b isoMvS_242 (by decide +kernel) lowS_143
def isoMvS_244:List (Nat×Nat):=[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]
theorem lowS_244:Lower true dom_244 roots_244 goal_244 7:=lower_iso_b isoMvS_244 (by decide +kernel) lowS_174
def isoMvS_248:List (Nat×Nat):=[(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_248:Lower true dom_248 roots_248 goal_248 8:=lower_iso_b isoMvS_248 (by decide +kernel) lowS_121
theorem lowS_63:Lower true dom_63 roots_63 goal_63 7:=lower_slice_b [(0xcccccccccccccccc,8,10)] (by decide +kernel) lowS_61
theorem lowS_123:Lower true dom_123 roots_123 goal_123 9:=lower_slice_b [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,8,10)] (by decide +kernel) lowS_121
namespace S_126
def pG:List (Nat×Nat):=[(2,10),(2,18),(4,36),(4,68),(6,14),(6,22),(6,38),(6,70),(8,10),(8,40),(12,14),(12,44),(12,76),(16,18),(16,80),(20,22),(20,52),(20,84),(24,26),(24,56),(24,88),(28,30),(28,60),(28,92),(32,36),(32,40),(34,38),(34,42),(34,50),(48,50),(48,52),(48,56),(48,112),(64,68),(64,80),(66,70),(66,74),(66,82),(72,74),(72,76),(72,88),(72,104),(96,100),(96,104),(96,112),(98,102),(98,106),(98,114)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffffff
def xsM:=roots_126.map (·&&&dom_126)
def gM:=goal_126&&&dom_126
def NN:Nat→Nat
|5=>1
|6=>3
|7=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0xe4f1
|6,0=>0xac125464f400935
|7,0=>0x464f4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x55555555555555555500550055005500aaaaaaaa88888888aaaaaaaa8888888954015401540154015401540154015402aaaaaaa800000002aaaaaaa8000000055550000555500005555000055550000a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a11111111111111111111111111111111002a802a80220022002a802a8022002255555555555555550000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x54632054863205463207546320543210
|_=>0
def sO:Nat→Nat→Nat
|5,0=>6
|6,0=>0x13735867
|7,0=>0x1a6
|_,_=>0
def wAt:=mkWire dB 9 127 0x7fffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def pmP:Nat→Nat
|0=>0xfff004003000
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x21
|7,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 2 (j%128);fld (pmP (k/32)) 12 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_124 5 roots_124 ops++addP pm 1 dom_116 4 roots_116 ops++addP pm 2 dom_118 5 roots_118 ops++addP pm 3 dom_62 5 roots_62 ops++addP pm 4 dom_122 5 roots_122 ops++addP pm 5 dom_58 4 roots_58 ops++addP pm 6 dom_110 5 roots_110 ops++addP pm 7 dom_46 4 roots_46 ops++addP pm 8 dom_94 5 roots_94 ops++addP pm 9 dom_108 4 roots_108 ops++addP pm 10 dom_90 4 roots_90 ops++addP pm 11 dom_86 4 roots_86 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_126 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_46 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_108 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_86 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_124 5 s (0,roots_124.map (·&&&dom_124)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_126 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_124 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_126==dom_126)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_126 gM v ys):RunD true dom_126 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_126 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 3 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
theorem checked (s:Nat) (hs:s≤7):∀ i<NN s,bar dom_126 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
  · exact z7 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 3 5=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤7) (h:RunD true dom_126 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_126 roots_126 goal_126 8:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_126
theorem lowS_126:Lower true dom_126 roots_126 goal_126 8:=S_126.noCircuit
theorem lowS_159:Lower true dom_159 roots_159 goal_159 7:=lower_slice_b [(0xaaaaaaaa000000000000000000000000aaaaaaaa,8,9)] (by decide +kernel) lowS_158
theorem lowS_175:Lower true dom_175 roots_175 goal_175 9:=lower_slice_b [(0xcccc0000cccc00000000000000000000cccc0000cccc,8,10)] (by decide +kernel) lowS_173
theorem lowS_183:Lower true dom_183 roots_183 goal_183 9:=lower_slice_b [(0xaa00aa00aa00aa000000000000000000aa00aa00aa00aa,16,17)] (by decide +kernel) lowS_182
namespace S_187
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,129),(2,10),(2,18),(2,130),(3,11),(3,19),(3,35),(3,131),(8,9),(8,10),(8,40),(8,136),(16,17),(16,18),(16,144),(24,25),(24,26),(24,56),(24,152),(32,33),(32,40),(32,160),(34,35),(34,42),(34,50),(34,162),(48,49),(48,50),(48,56),(48,176),(128,129),(128,130),(128,136),(128,144),(128,160)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffff
def xsM:=roots_187.map (·&&&dom_187)
def gM:=goal_187&&&dom_187
def NN:Nat→Nat
|4=>21
|5=>61
|6=>70
|7=>45
|8=>10
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xed40ae3b8dada3aaab72a629c8ffc77ee96794f6710926ccf26c7c35dd2a5cbe3310e125c0c1865d116570eeef0e13407c0e061f7
|5,0=>0xedb17e7cc5daf40d84b2c831ec1f35b66d5b5698b4254ac711a850ba3ff2a34799a33599f4481d5e7dea47a7a976db36bb336a94b6a5af6995767e33631865d94158343551da5354f4888e47d9346be044985448b03e0763b89b3b2fb3935b38ec62703625d6724e10237b322577208d72036a1f32819f081993b17b8a12d8c10dfa0f8aa0a92c090560886307f0f065f502e7c0223701e63
|6,0=>0xe98aedd446d236ed1ce1c9474c83c3c65bdbac4cb9976b53fcb1f73b0f49b049aae7e4ad9229d50f916698c9da8c3408088b7bf6c6e7fb6ca926840c6785562d45628a75fa8f5e67a5d6865b3ed5a26c58cc757a3d562dc54f50538374fd894edeb48f094520843d5a425534130f412593d6bc362ee3589832f053281130d102f6eb2f5ca2d8b82d08a220df17c1a15c77146370f9130edf50b8b90b7fb09edb09a3408c6d03c490263e01aad00d24
|7,0=>0xf7978e5ea9e0bc4d1175c8cddbf963bf55cbec1db9c35b5207a45e98ab5583f1b8091e73c07718e96fec86b82664c2b6264b5e3f65a8394f67f4b534472d04641f3b98836ede32fc73082829e1a22f9a215e71e35a1c80e1929716d81150ba12b81103a60adbb0a0f0099a60671900f2b
|8,0=>0xea54be5ea9d5146c352dbb648824c96a88826f6b18d9f139c6
|9,0=>0x3dbb0
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0a0f0f0f0a00000000000000000f000f000f000f00f000f0f0f000f0f00000000000000000f000f0a0f000f0af0f0f0f0f0f0f0f00000000000000000000000000000000f0f0f000f0f0f0000000000000000000e0e0e000e0e0e00a0a0a0a0a0a0a0a00000000000000000a0a0a0a0a0a0a0af0f0f0f0f0f0f0f00000000000000000f000f000f000f00f0f0f000f0f0f0000000000000000000f0f0f000f0f0f00f000f0f0f000f0f00000000000000000f000f000f000f00f0f0f0f0f0f0f0f00000000000000000f0f0f000f0f0f00c0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0c0cf0f0f0f0f0f0f0a00000000000000000a0a0a0a0a0a0a0af0f0f0f0000000000000000000000000f0f0f0f00000000f0f0f0e0f0f0f0e00000000000000000f0f00000f0f0000f000f000f000f0000000000000000000f000f000f000f00e0e0e0e0e0e0e0e00000000000000000e0e0e0e0e0e0e0ef0f0f0f0f0f0f0f00000000000000000a0a0a0a0a0a0a0a
|0,1=>0xf0f0f0f0f0e0f0e00000000000000000f0f0f0f00000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f00000000f0f0f0f0f0f0f0a00000000000000000f0f0f0f00000000f0f0f0f0f0f0f0c00000000000000000c0c0c0c0c0c0c0c00000000000000000000000000000000f0f0f0a0f0f0f0af0f0f0f0f0f0f0f00000000000000000e0e0e0e0e0e0e0e10101010101010100000000000000000101010001010100f0a0f0f0f0a0f0f00000000000000000f0a0f0a0f0a0f0af0f0f0a0f0f0f0a00000000000000000f0f0f0a0f0f0f0ae0e0e0e0e0e0e0e00000000000000000e0e0e000e0e0e0050505050505050500000000000000000504050405040504f0f00000f0f000000000000000000000f0f00000f0f0000f0a0f0a0f0a0f0a00000000000000000f0a0f0a0f0a0f0af0f0f0f0f0f0f0f00000000000000000f0a0f0a0f0a0f0a00000000f0f0f0f0000000000000000000000000f0a0f0af0f0f0f0f0f0e0e00000000000000000f0f00000f0f0000
|0,2=>0xf0f00000f0f000000000000000000000e0e00000e0ef000f0f0f000f0f00000000000000000f000f0e0f000f0e00000000000000000000000000000000f0e0f0e0f0e0f0e0000f0f00000f0f000000000000000000000f0f00000e0e00f000f000000000000000000000000000f000f0000000000000000f0f0f0f0000000000000000000000000f0f0f00f0b0f0b0f0b0f0b00000000000000000f0a0f0a0f0a0f0a10101010101010100000000000000000000000000000000f0f0f0f0e0e0e0e00000000000000000f0f0f0f0e0e0e0e5050505050505050000000000000000050505000505050010101010101010100000000000000000100010001000100f0e0f0e0f0e0f0e00000000000000000f0e0f0e0f0e0f0ef0e0f0e0f0e0f0e00000000000000000000000000000000a0a0a0f0a0a0a0f00000000000000000a0a0a0a0a0a0a0a00f000f000f000f0000000000000000000f000f000f0000f0f0f0f0e0e0e0e00000000000000000a0a0a0a0a0a0a0a
|0,3=>0xf0f0f0f0f0f0f0f00000000000000000f0e0f0e0f0e0f0ea0b0a0b0a0b0a0b00000000000000000a0a0a0a0a0a0a0aa0a0a0a0f0f0f0f00000000000000000a0a0a0a0e0e0e0ef0f0f0f0f0f0f0000000000000000000000000000000000f0f0f0f0000000f00000000000000000f0f0f0f00000000000000f0000000f00000000000000000000000000000000f0f0f0f0e0e0e0e0000000000000000000000000000000000f000f000f000f0000000000000000000f000f000e000e0000e0e00000f0f000000000000000000000e0e00000e0e00000000000000000000000000000000f0f0f0f0e0e0e0ef010f010f010f0100000000000000000f000f000f000f00a0a0a0a0b0b0b0b00000000000000000a0a0a0a0a0a0a0a00f000f0000000f0000000000000000000f000f00000000000000f0000000f00000000000000000000000f00000000f000f0f0f000f0f00000000000000000f000f0f0f000f0050505050000000000000000000000000505050500000000
|0,4=>0xa0f0a0f0a0f0a0f00000000000000000a0a0a0a0a0a0a0af0f0f0f0a0a0a0a00000000000000000f0f0f0f0a0a0a0a00000000f0f0f0f00000000000000000000000000000000f000f000f0f0f0f00000000000000000f000f000f000f0050505050505050500000000000000000500050005000500f0f0f0f0f0f0f0f0000000000000000000f000f00000000f0f0f0a0f0f0f0a0000000000000000000000000000000000f000f000f000f00000000000000000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f000f00101010101010101000000000000000001010101000000005050505050505050000000000000000050505050000000030303030303030300000000000000000303030003030300f0f0f0e0f0f0f0e00000000000000000c0c0c0c0c0c0c0c0000e0f00000e0f000000000000000000000e0e00000e0e3030303030303030000000000000000030303020303030200000000f0f0f0f0000000000000000000000000f0e0f0e
|0,5=>0x5050505000000000000000000000000000000005050505050505050000000000000000000000000000000000100010001000100000000000000000000000000000000f0f0f0f0f0f0f0000000000000000000f0f0f0f0f0f0f00e0f0e0f0e0f0e0f00000000000000000e0e0e0e0e0e0e0e000000f0000000f00000000000000000000000a0000000a00000000101010100000000000000000000000000000000f0f0f000f0f0f0f00000000000000000f0f0f000f0f0f00f0f0f0f0f000f0000000000000000000f0f0f0f0f000f00f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f00f0f0f0e0f0f0f0e00000000000000000f0f0f0e0f0f0f0e00000000f0f0f0f0000000000000000000000000e0e0e0ef0f0f0f0a0a0a0a00000000000000000a0a0a0a0a0a0a0af0f0f0f000000000000000000000000000000000000000000000000f0f0f0f00000000000000000f0f0f0f0000000000f000f000f000f0000000000000000000f000f00000000
|0,6=>0x50005000500050000000000000000000000000000000000000000f0f0f0f0000000000000000000000000a0a0a0aa0a0a0a0f0f0f0f00000000000000000a0a0a0a0a0a0a0a00000000f000f0000000000000000000f000f000f000f00f0f0f0f000f000f00000000000000000f0f0f0f0000000000000000000000000000000000000000f0f0f0f00000000f0f0f0f0c0c0c0c00000000000000000c0c0c0c0c0c0c0cf0f0f0f0f0f0f0f00000000000000000f0f0f0f0a0a0a0aa0a0a0a0f0f0f0f00000000000000000000000000000000f0f0f0f0f000f0000000000000000000f000f000f000f00f0f0f0f0f0f0f0f00000000000000000505050500000000
|_,_=>0
def sP:Nat→Nat
|0=>0x12080a21a10486168468914185911a10488022c684124cb0d3c50101407ca0a022cf09041829d122830b081c11c1610d8914042030468584124cc8d0824c011a10b822c342090254689240488d0840101001048f0c002091c04684140460b08245060a10488020020704182840608080
|1=>0xc0022e040458d08516820200202022d60d0850101008c209266808d0840101163448616ad50d0851482023421426280a808241161634209041828d08249011a1048f0c2c6a73c50101001048e0c2c684124c3261a104811694684282808b4610a020254684122030016509020244684
|2=>0x28080bd1a104ad022c69e120830b78ec48616ac68412280801a10a241468584122808008249811ae82140404039085008b7034202022db8d08252010034214040500d6c10a02020021426d408d082451a022c2140405a0d082490a02342090c2d98d0825886163420202c178d081c493
|3=>0x163421404045c61a10a24040400d3c10a020c02294240830b2234202022d78d0824106442c684124c5c41a10482862c6840e0830b7810101170868412085c11a10b89141801d120830b1a5010117006842e1c1011a104bf022c684122808b5010482166468428080be1a10a02342d184
|4=>0x28080cf1b38f14041a28d082660616342090c2e58d76104820c2c694041800b2234214260808d50104930234207124c30b1a10a02020240428b4101163421414080801a104861728684282810100104920c2c6842808d016034209041858d929cf14040458d085011a022e4470824506
|5=>0x141858d08244061634f14041a984122830b9a1048a022c684280808b1ae4f04122830b3d44a020c2c209046808b1a10a3f040458d082430b5635d0428080c51a10a0a04045a83c104861740684282830ba035b04280808b1a104a4022c684120830b4c34209261800d082490a0c2c684
|6=>0xb60458d0824906002c6d73c50506163420904185da1a10a02022c6d9a2501061678a0202c0684b0241061636b9e282830bac104820c2c684120808b1ae8255120808b1a10389042e20d4e10a02020069404185911a10a24046858d081c4820c005c7085030ba03421404045d41a78209
|7=>0x850101163641e0850106172021414083001634214040580d0853086163421404185e01a78214140830b1a10a0a041800b08505020c2e684280830b1b7c214140808b1a78214140830b08505020c2ef04284c50600342142628300085c4820c00684280808b1b76e040e0830b1a10a02
|8=>0x41b40b1a9c214040458d08509020c0058d0824106163669e08241061634214ce1858d08241011634f1404185ab1b98214041858d085010617146e5280830b9a10a02c82c6e308501061634214041a78b1a10a020c2c6e2085010116354473c10a020c2c684124c30b1b5c214141858d
|9=>0x850106163640428281061636b84280830b1a10a020c2c6d2085010616c069e0850106171469e0850106163421404185cb1a10a13141858d081c4820c2c68428481061634209141858dae78a020c2c6842e24106163638428281061634f1404185d208501061637504280830bd234214
|10=>0x8501061634214041858d9a78214041858d08509820c2c684120830b1a13294041858d
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x6450bea16942aa8505096a119420a83c506ea0c9416a8285046a07940ca814501ea029402a8005
|5,0=>0x1cf6392c70d8deb1b76362c6ad8d2b19f6332c64d8c6b1876302c5ed8bab16f62d2c58d8aeb15852a4c5318a331406274c4d189731286244c47188b31106214c41187f30f861e4c3b187330e061b4c35186730c86184c2f185ba8b16156c29584fb0996126c235843b08160f6c1d5837b0696
|6,0=>0x6eaedb9db3bb6076b6ad559a73b486682ece9d99bb2c764aec7d98c3b117614ec0dd7e3af665e2abad972b2de75b0cb49965bac4757aeadd9583aa97544ea6dd4ab28e7510ca05d3db27474dcc9a1930ba5a74a6e939523ba416474e8cdd16b2276442c869d09ba0c740ae7f9cfbb9f073d2e789cee31d57
|6,1=>0x1cf3b986722ee29dc1bb7c7
|7,0=>0x4d5899cf31de603cb97964f2b1a52bc9e792d1241a44bc8278f6f1d1e36446578bcf161a29344b7888f0f5e1bb4316854f08de0e3c15781b101da003bf977e4efaa1f233de67aeef3e1e43bc17774eecddd63ba57
|8,0=>0x28dbd147a1af41da803cf979e4f3ade723cdd7
|9,0=>0x5226
|_,_=>0
def wAt:=mkWire dB 107 188 0xfffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 15
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 8 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x2809082f02350c2d2e34122d2809080508350c2d2809043516350c2d3c2f08350435345302350c2d123628091635483502090c2d4834483704352809023504350c2d123628090c2d4e3416352809280904c93c270835123516352809483428090236021c123528092635280908350805002748340c2d26351236280926350027
|1=>0x28093c2f08350c2d02360c2d3c0b083528098e0b082904354e370805020928090c2d0e2f123528091635042d2809280904350c2d172104363c2f0835053528090836142f0435280908e91236084a000902360c2d0c2d042d2809042d12352809043616350c2d48370209163504350c2d28095635080b0c2d163504352635042d
|2=>0x8350c2d1335280908360435080908353c2508352809123628090c2d120528090e1b123528091635084a142d043502350c2d1635123528093c093c0b0835086a023504350835280904e912362809174908340835043528090836043528090c2d4e3408050c2d0435083528093d4b08340835280902350c2d340902350c2d1236
|3=>0x8360d4908343c2d0835172104366036082f02360c2d0835042d28090809043504360c2d0436083516350435082f0c2d054908346035082f0435083516350435043508369c36082d04350c2d04350835163604351635042d0435042d163504351635082512352809032104360c2d280900091635080908353d4b08340835082f
|4=>0x8360835042d280908370436043508090834082f3c2f083509350836142f0435042d043512352809142d04350435280908090835122d280908290435083408352636042d080216351735083608050c2d000916352809083608352809054b08340c2d2809080b0835092104363c2f08350837
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x18800000001200000000020000000000000000
|5,0=>0x14880000000001318000000000128800048200000008883e60000e186c40000000c900000000000c080000000000a98000246000000000022210100000001e2000061800014400004101c400000002900000000410000000000000
|6,0=>0x631b108000000609af8d766b835a9ac8d604ad3560aa4d4e4a43509a7c93869934b1a4cd2068d3451a1cd0868133f91f0cf447733a19c88de66c334999c8c866222f9970cb445822b114cca064d3259120c8a64231f98f0c7263721b08d080003221810bc45862a2
|6,1=>0x1a66d036788001986c93
|7,0=>0x12d29594a4a4e5252919484a3e51d28d9464a2e5152899444a1e50d2859424a0e50528194049fe4fd27d93e49ee4f527a0bc89e04ee27613a89d04e627213889c04de26e13689b04d62
|8,0=>0x27033719b0cd46683331990cc466032f1
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 13
def pmP:Nat→Nat
|0=>0x2400008800014200049100104000400000f5c003c5000e5c00206000810001c50006440012800042000100000300000a000027800088000200000400000a00002000005000010000020000050000100000200000400000
|1=>0x2050c0809702020008040020064061ff010f7c039d500e6540395100c4000300100a67c0299500877c021d70087540219300840401b95004e1001297004a100119700440400c00002e5400b1c00266c0099700260000915
|2=>0xa067c200880802002000a04a744100c1040300100810401041000102e5140b91502e4000b10002a7540a99702a6540a99302a6440a91502a4000a8450286640a19702864c0a1910284000a00002644c0899702264c08882
|3=>0xc100208a01822065c8199520660081397204e108099c2026008019710471c401d71001002a993
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x60000200001800000000
|5,0=>0x14000000e000000a00400002c8801e1400012000003400a800c00780000028500001800200b00180c00020000020000000
|6,0=>0x10a5c20169b567c0005db2b4c083f6d7b84c859682e5b65d2980daab8e8778f88454f75d5830a513d418c80b22e6d241d95fe654eca5e4d100123c08e0b
|7,0=>0x409ca165bd0e2662a51d16b857f3d1a3058c39f0a760c88a6a36a66a3399a64ce8d4f54c44cea25
|8,0=>0x28502ebe7326f22746
|9,0=>0x13
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 7 (j%128);fld (pmP (k/32)) 22 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_185 8 roots_185 ops++addP pm 1 dom_154 5 roots_154 ops++addP pm 2 dom_146 4 roots_146 ops++addP pm 3 dom_184 5 roots_184 ops++addP pm 4 dom_171 8 roots_171 ops++addP pm 5 dom_177 5 roots_177 ops++addP pm 6 dom_163 5 roots_163 ops++addP pm 7 dom_186 7 roots_186 ops++addP pm 8 dom_179 7 roots_179 ops++addP pm 9 dom_178 5 roots_178 ops++addP pm 10 dom_57 5 roots_57 ops++addP pm 11 dom_59 6 roots_59 ops++addP pm 12 dom_51 4 roots_51 ops++addP pm 13 dom_147 5 roots_147 ops++addP pm 14 dom_169 7 roots_169 ops++addP pm 15 dom_155 6 roots_155 ops++addP pm 16 dom_43 5 roots_43 ops++addP pm 17 dom_153 5 roots_153 ops++addP pm 18 dom_170 5 roots_170 ops++addP pm 19 dom_58 4 roots_58 ops++addP pm 20 dom_161 4 roots_161 ops++addP pm 21 dom_168 4 roots_168 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_187 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_146 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_184 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_177 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_178 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_169 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_153 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_161 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_168 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_185 8 s (0,roots_185.map (·&&&dom_185)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_187 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_185 h
def symsG:List (List (Nat×Nat)):=[[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_187==dom_187)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_187 gM v ys):RunD true dom_187 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_187 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 21 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 21 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 61 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 61 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 70 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 70 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 45 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 45 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 10 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_187 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
  · exact z7 i (Nat.zero_le i) hi
  · exact z8 i (Nat.zero_le i) hi
  · exact z9 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 5 5=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_187 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_187 roots_187 goal_187 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_187
theorem lowS_187:Lower true dom_187 roots_187 goal_187 10:=S_187.noCircuit
namespace S_249
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(1,129),(8,9),(8,40),(8,136),(16,17),(16,80),(16,144),(24,25),(24,56),(24,88),(24,152),(32,33),(32,40),(32,160),(48,49),(48,56),(48,112),(48,176),(64,65),(64,80),(64,192),(72,73),(72,88),(72,104),(72,200),(96,97),(96,104),(96,112),(96,224),(128,129),(128,136),(128,144),(128,160),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffff
def xsM:=roots_249.map (·&&&dom_249)
def gM:=goal_249&&&dom_249
def NN:Nat→Nat
|4=>7
|5=>40
|6=>155
|7=>121
|8=>28
|9=>5
|10=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x5c7d842d87200721a9210e34f0d8e70567b
|5,0=>0x966fd5f1cc5bd504f0e9437d8429b53f12e3c98f35c07322753071b2ca8024584236a4212b71fbdc1e5071d2461cd1b1c8d11ac651a4ff18ef5150be14f35139a21332711dfe10cc80cc85099f408cad07512071ce06e4b069b503db00349702ed9018eb
|6,0=>0x3e87e3db7c3cb093c5113b6473809b3712c3632935dc334dcc34a103366632e853232931a503159c301092ffde2f9402f9212f4532ed4f2e13d2d1712cd012cc5d2ae212a51c2981727a72279b527452271cc26a20268102662f24b07249a92459123f7823cf223c8723b1d239012368b23439231b12269d2236121cd82153e2135a209e4203002016e1ed481e1111dd9f1dc441d9351cb471c3641abd219cab18fe918ef5189e4173741729e16ce716a0d15ee5154f81495314905145a31446c143c3141e1136ea13022120b51105f10c7e10a7b0ebe20eb010ea3e0e9b00e1fe0e07d0df5d0dc030cd6c0c5f50c3da0b2670b21e0a2920a1ac0a0dd09e3a09a08099f408e5c08de208a640800707a1d073b40716f06a3e0540904ac403fa7035160348a033550316602ea402a8802a66028e301ec7015220112900e7b004a8
|6,1=>0xa65a7909898f8627dfc97cc01684b86604d621805dc945d1b45c7c25a20d562ed55bad529985276a4e4294d8374bcf148e0f462ef4512842adb415a24152e4112d3f2a8
|7,0=>0x887c0803627c18d7ab3c7577074b6e6c8dd6275f604ef5b1f9590e85849657d5e57bfc56e995374552e1d500454e4144ce194c1324adcf49de2494dd457d142f39414da3ec793a00038f9b364b735ca8357bc326ab31aee30f8f30d2d300202fc3f2e1292db232dac22d2812d0272b6862b39b2a9262a57429e422906e279b5272b9268c02613025aee25a282427823d5a23a8522cec213d12110a20daf1ecdc1e27e1dbfa1dbb41d8cd1ce581c3d31bf911b7da1b738199e6197f4195ef17c4515de4156e7140a41405d13ff2139ec100520f9ca0f5150f1920e2550e16d0df9a0cb3c0c9490c9340c6510bde00aa370a6710a070097dd0918208e2f088e2086e8079590747d06efc06193058d2050a304c1a0475b04091039e70388a02b79023420221b0205901ec701eb600f84
|8,0=>0x7623e58fc15758b3fd703dbf532ba93166f30a2d2ac3527c4d26f04265cc243e120bc41f3e31cc211834c170b415f5513aa812876119a9112fc102d10e9b70c192070a10394d
|9,0=>0xf254a854c2516ab2ccf8092d1
|10,0=>0x854c2
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xc0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0c0c000000000000000303030303030303030303030303030303030303020202020303030302020202c0c0c0c0c0c0c0c08080808080808080c0c0c0c0c0c0c0c080808080808080b03030300000000030303030000000003030303000000000303030300000000c0c0c0c0c0c0c0c0c0c0c0c000000000c0c0c0c0c0c0c0c0c0c0c0c0000000303030303030303030303030303030300000000000000000000000000000000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c000000000c0c0c0c0000000303030303030303030303030303000003030202030302020303020203030000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c030303030303030303030303030303030303030303030303020202020202020280808080808080808080808080808080808080808080808080808080808080b03030302020202030303030202020203030303020202020303030302020202c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c000303030303030303030303030300030003020302030203020302030203000300c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0808080808080808080808080808080b03030303030303030303030303030303030303030303030000000000000000
|0,1=>0xc0c0000000000000c0c000000000000080800000000000008080000000000000003030303030303030000000000000000030302020303020200c000c000c000c000c000c000c000c000c000c000c0008000c000c000c000b03030303030303030003000300030003030303030303030300030003000300c0c0c0c0c0c0c0c0c0c0c000c0c0c000c0c08080c0c08080c0c08000c0c080302030203020302030203020302030203020302030203020302030203020302c0c0c000c0c0c000c0c0c000c0c0c000c0c0c000c0c0c000c0c0c000c0c0c0303030303030300030303030303030003030303020202000303030302020200c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c080c080c080c080c080c080c080c0b03030303030303030303030303030303030000030300000303000003030000c0c0c0c0c0c0c0c0c0c0c0c0c0c00000c0c0c0c0c0c0c0c080808080808000303030303030000030303030303000002020202020200000202020202020000c0c0c0c0c0c00000c0c0c0c0c0c00000c0c0c0c0c0c00000c0c0c0c0c0c000303030303030303030303030303030303030202030302020303020203030202c0c0c0c0c0c0c000c0c0c0c0c0c0c000c080c080c080c000c080c080c080c0303030303030303030303030000000002020202020202020202020200000000
|0,2=>0xc0c00000c0c0000000000000c0c00000c0c00000c0c00000000000008080003030000030300000303000003030000020200000202000002020000020200c000c0000000c000c000c0000000c000c000c00000008000c000c00000008000000010101010000000001010101000002020000020200000202000002020000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c0000080b0203020302030203020302030203020302000003020000030200000302000000000000c000c0c000000000c000c0c000000000c000c08000000000c000c0b03030300000303030303030000030303030303000002020303030300000202c0c00000c0c0c0c0c0c00000c0c0c0c0c0c00000c0c08080c0c00000c0c0808000003000000030000000300000003010100020101000201010002010100020000000000000000c0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c080b03030003030300030303000303030002020200020202000202020002020200c0c0c0c0c0c0c0c0c0c0c000c0c0c000c0c0c0c0c0c0c0c080808000808080303030303030303030003000300030002020202020202020200020002000200c0c0c0c0c0c0c0c0c0c0c0c0c000c000c0c0c0c080808080c0c0c0c0800080303020203030202030302020303020203030202030302020303020203030202
|0,3=>0xc0c00000c0c00000c0c00000c0c00000c0800000c0800000c0800000c08000000000000000303030303030303000000000000000003030303020202020000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000808000008080000000303030300000000030303030000000003030303000000000202020200000000000000000000000000000000c0c0c0c0c0c0c0c0c0c0c0c08080809010101010101010101010101010101010101010101010101010101000000000000c0c00000c0c0000000c0000000c00000c0c00000c0c00000008000000080003030000030300000303000003030000030300000202000003030000020240404040404040404040404040404040404040404040000040404040404000000000003030303000000000303030300000000030302020000000003030202c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c000c000c000c000c000c000c000c000000000000000000030003000300030000000000000000000200020002000200000000c0c0c0c000000000c0c0c0c000000000c080c08000000000c080c08000303000003030000000000000303000003030000030300000000000003020000000000000000c0c0c0c0c0c0c0c00000000000000000c0c0c080c0c0c0800000003030303000000000303030300000000030303020000000003030302
|0,4=>0xc000c000c000c000c000c000c000c000c000c00080008000c000c0008000800000000000000030303030303030300000000000000000302030203020302c000c0c0c000c0c0c000c0c0c000c0c0c000c080c000c080c000c080c000c0b03030303030303030203020302030203030303030303030302030203020302c0c0c0c0c0c0c0c0c0c0c0c080808080c0c0c0c0c0c0c0c0c0c0c0c0808080800000000000000000000000000000003030303030302020303030303030202c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c08080c0c0c0c0c0c080803000300030003000300030003000300020002000200020002000200020002000000c0000000c0000000c0000000c000000080000000800000008000000080000000000000003030303030303030000000000000000020202020202020200000000000000000000c0c00000c0c0000000000000000000008080000080800000000000000000000000000000000000000030303030000000002020202c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0808080b03030303030303000000000303030303030303030303030000000002020202c0c0c0c080808080c0c0c0c080808080c0c0000080800000c0c00000808000003000300030003000300030003000300030002000300020003000200030002
|0,5=>0xc0c0c080c0c0c080c0c0c080c0c0c080c0c0c080c0c0c080c0c0c080c0c0c080000000000000000000000000000000303030203030302030303020303030200000000c0c0c0c0000000008080808000000000c0c0c0c000000000808080b03030303030303030303030303030303030302030303020303030203030302c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c080c080c080c080000000000000000030003000300030000000000000000000300030002000200000000c0c0c0c000000000c0c0c0c0000000008080808000000000808080901010101010101010101010101010101010100010101000101010001010100000000000000000000000000000000000000c0800000c0800000c0800000c0b03000003030000030300000303000003030302030303020303030203030302c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c000c0c0c000c0c0c000c0c0c0303030303030303000300030003000303030303030303030002000200020002c0c0c0c0c0c08080c0c0c0c0c0c08080c0c0c0c0c0c08080c0c0c0c0c0c080b0303030303030303030303030303030303030303030000030303030303000000c000c000c000c000c000c000c000c000c000c000c000c000c000c0008000b03030303030303030303030303030303030303030303030303030300000000
|0,6=>0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c04040400040404000404040004040403030303000000000303030303030303030303030000000003030303030302020000000000000000c0c0c0c0808080800000000000000000c0c0c0c0808080b03030303030303030303030303030303030303030303030300030003000300c0c0c0c0c0c0c0c000c000c000c000c0c0c0c0c0c0c0c0c000c000c0008000800000000000000030300000303030300000000000000000303000003030202c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c000000000c0c0c0c0000000008080808000302000003020000030200000302000003020000030200000302000003020000000000c000c00000000000c000c000000000008000800000000000800080000000300030000000000030303030000000003000300000000000302030200400040004000400040004000400040004000000040000000400000004000301030103010301030103010301030103010300030103000301030003010300000000000000000000000000c0c0c0c0000000000000000000000000808080803000300030003000300030003000300030003000300030000000000000000000000000000000000c000c000c000c0000000000000000000c0008000c000800000000000000000000000000000003030303030303030302030203020302
|0,7=>0xc0c0c000c0c0c000c0c0c000c0c0c0101010101010000010101010101000001010101010100000101010101010000000000004040404000000000404040400000000040404040000000000000001010101010101010101010101010101010100000101000001010000010100000000000000000000000000000000000000c0008000c0008000c0008000c00080000000000000000000000000000000303030303030303020202020202020200c000c000c000c000c000c000c000c000c0000000c0000000c0000000c000101010001010100010101000101010001010100010101000101010001010100404040404040404040404040404040404040404040404040400040004000400000000000000000303030303030303000000000000000003030303000000008080808080808080c0c0c0c0c0c0c0c08080808080808080c0c0c0c080808080000000303020200000000030302020000000003030202000000000303020240404040404040404040404040404040400040004000400040004000400040000000000000000000000000000000001010101010101010101010100000000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0404040404040404040404040000000000000000000000000000000000000001010100010101000101010001010100
|0,8=>0x4040404040404040404040404040404040404040404040400000000000000000000000303030300000000030303030000000003030303000000000000000000000000000000000000000000000000c0c08080c0c08080c0c08080c0c080800000000000000000000000000000003030303020202020303030302020202c0c00000c0c00000c0c00000c0c00000c0c0c0c0c0c08080c0c0c0c0c0c080800000000000000000000000000000001010101010100000101010101010000
|_,_=>0
def sP:Nat→Nat
|0=>0x807050f0a200701290f0a282707050f0a0903070d01100c0705260f0a0403071000250c0307050a0c0302010500180317050f0a0c2017240f0a0c121a240f0a0c200701230a21031a0f0a092007011f0f0c1e03051d0a0e03070510000c1b1a060a181617050f0416070115091211050f0e08070d0a09080706050403020100
|1=>0x3070507053d330f0a3b0307053c0f3b0c03073a0f0c1a05390f0a0c0737380f0a030737360f0a09080701050f04091e0307010c03350d013409200701140f0c1607010515200705290f0a070533320f0a0c2011010f0a31030705300a0c08070d0a090701052f0f0c12052d0f0a0c0307012c0f0c07052b0f0a0c192a010f0e
|2=>0x7100f0a0c03171c06050a4b0c030701004a090c0307050f03171c05330f0a0c03070d100a49030705360f0a0c200701470f0a0c031a3501460f0c121e0705450a0c030201050f0a040c07013d0f0a430c0307050f0a0c1c07053d000a04030701420f0a134107050f0a0b0c070d053d0a0c05403f0f0a09031101050f3b3e0c
|3=>0x3f0f0e270307050f0a0c030701580f0a4b040c03070100040307051f0f0a0c561607050f0a0c551e0307050a12030705330f0a490c0705380f0a0c03070546540a4a520c0307050f250c0307050a0c030d05510f0a500307053c0f0a0c03054f380f0a0c034e1c35050a0c204d07050f0a0c03070d01220a0c034c35010f0403
|4=>0x19033505330f0a0c03601c35050f0c2707051f0f0a0c200701380f0a0c0307010522000c5e200307010f0e0c0307370f0a0450030701000f0b0903070d010c0307015d000c200705470f0a0c31190307050a500c03070d010004030705420f0a0c5b07053d0f0a0c03054f5a0f0a13090705380f0a0c07052f0f0a0c16070105
|5=>0x64050f0a040c1607012e0f0409030706010f130c03051d0f0a0c55031a580f0a0c033505540f0a430c03073a0f0a0c031a35012e0f0c192007580f0a0e030705630f0a0c07052b0f0a0903070105100f03070546330f0a0c31031a07050a0c03070d01620e0c1e0307050a0c0706052b0f0a0c1e030705610a0c033505400f0a
|6=>0x28030705590f0a0b0307053c0f0a4b0b090307010f090c0305510f0a04030701360f0a0403054f670f0a0c0807050f0a4a0c160307050f0c19161701050f0c03171c0d010a03070546660f0a0e0307053c0f0a0c200705380f0a0e0c03073a0f0a3e500c0307050a0c121e07052e0a03350548330f0a0c0705422f0f0a0c031a
|7=>0x3054f0f0a13200705360f0a0c5f5e0307010f0c1e031a07010a0e3e0b0307050a4b0c03070d01000c19034d050f0a0c55031a35010f0c033501680f0c032a07010f0c031a01340f0a03170705300f0a0c030705630f0a4b0307053c0f0a0c1e160705450a0c1e030705590a52040307010f4b0c03073a0f0a0c5e031707050f
|8=>0x90c0307013a0f0c034d05470f0a3e0b0c0307050a520c03051d0f0a0403070159000f0c03056b4f0f0a0c031a05340f0a0903070105630f520c030701370f0c6a030701050a090c030705690f0c03350105340f13040307370f0a0c1c0706053d0a0c1203051d0f0a04030705360f0a130c2707050f0a0c03171c0105003e0c
|9=>0x470f0a430c0305510f0a6e0c1e0307050a040903073a0f0a0c034c1c070100530c201607010f25520c0307050a0c03070605100a0c034c6c07010f0c030105510f0a04090307370f0a500c0305510f0a530c1e0307050a0c1e1607052e0a6d090307010f0c070d052b0f0a0c031a6c1c010f55030705330f0a0c03070563000a
|10=>0xf0a0c030701740f0a0c55031a050f0a0c030705690f0a0c122007052e0f0a0e040b0307050f0a0c031c05730f0a430c0307050f0a0c1e030701050a0c030701051f0f0a0c031705240f0a0c080701050f0a0c035b6007050f0c03070105710f0c16031a01480f3b0c03070d05000c030701056f0f4b3b090307050f0c120705
|11=>0x370f0a0c0307015d0f0a0c0307056f0f0a0c030705100f0a43040c0307050f0a4b0c030706050f0a0317350705330f0a0c07053d0f0a0e030705590f0a0c5f550307050f0a0c034c1c35050f0a0c030705770f0a4b040c0307010f0a0c0706053d0f0a0c03171c35050f0a750c0307050f0a0c03070105420f0a0e0c03070605
|12=>0x500c03070105000f0c03070605590f0a03350705330f0a5313090307050f0a0c20030701480f0a49530c0307050f0a0c0307057b0f0a0c031c0705340f0a0b0c03077a050a130e030701050f0a0c200705790f0a0c03070105220f0a0c031a07053f0f0a520c120307050f0a0e090c03054f0f0a520c201607050f0a0c030705
|13=>0x50f040c0307050f7d0a04090307010f0c03070105800f0a0c55203507050f0a0c03070554480f0a0b0c03070605000a0c030701050f620c16030705360f0a0c031a0706010f0a0c031c070601050a0c7f031a050f0a0c270307050f0a0c1607057e0f0a0c0307050f7d0a13040307010f0a0b09030701050f0c036407050f0a
|14=>0x480f0a0c031a01480f0a4b040c030705000a130c8307050f0a430c03070d050f0a520c030701050f530c0307010f0a0c030705630f0a0c03070105360f0a0c03174e07050f0a0c034c35050f0a0c030705591f0f0a0903070105590f0c5c120307050f0a0c5f190307010f0a4b0c030705000a810c0307050f0a090c03070601
|15=>0x7050f0a0c0307010559000f040c030701000f0c031a05480f0a130c030705370f0a0c03070d05620a0c1607052e0f0a0c5e200307050f0a0c034e07050f0a0c070d053d0f0a0c0307053c0f0a0b0903070d050a0c0307055d000a0c5c033507050f0a0317070105330f0a500c03070d05000a0c5f200335050f0a0c03070605
|16=>0x50f0a0c030701050f84130c160701050f0c033507057b0f0a0c0307010548000f0c030705720f0a53130c0307010f0a0c5c030701050f0a520e0c0307050f0a0c5f5e0307050f0a0c191207050f0a4b0c03070d05000a0c03070d01480f0a0c033505680f0a0c032a07050f0a52040307050f0a4b0b090307050f0a3b040c03
|17=>0xa52090c0307050f0a0c030705740f0a0c031c35050f0a0e040c0307050f0a4b0c0307050f0a0e0c0307050f0a0c0307050f850a0c27030701050f0a0c035b1707050f0a0c03601c07050f0a0c190317050f0a0e03070105590f0a530c201607050f0a0c035b1c07050f0a0c03070546590f0a0c031a6c1c050f0a0c5c550307
|18=>0x50f0a0c03070105460f0a0c030705790f0a0c5f190307050f0a0c12030701050f0a0c030705780f0a530c200307050f0a13040307050f0a0c12160307050f0a090c030701050f0b0c030705000a0c031a07010f0a130c030701050f0a0c0307055d0f0a0c030705590f0a0c830307050f0a4b040c0307050f0a0c7f0307050f
|19=>0xc0307050f0a0c030701050f0a0c0307050f0a0c030705000f0a0c031a07050f0a0b0c0307050f0a0c036c07050f0a040c030705000f0a0c036c1c07050f0a04090307
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x1e50195014500f500a500550005
|5,0=>0x109610360fd60f760f160eb60e560df60d960d360cd60c760c160bb60b560af60a960a3609e50986092608c60866081507b6075606f60696063605e50586052604c60466040603a6035502f602960236
|6,0=>0x2bd72b762b072a972a2729c6295728e7287728072797272726b7264725d7256724f72487242623c6235722e7227722072197212720b720561fe71f771f071e971e271db71d471cd71c671bf71b871b261ab71a4719d7196718f71887182617c6175716f61687161715b6154714d7146713f71387131712a7123711c7116610f7
|6,1=>0x4797472746b7464745d7456744f74487441743a7433742c7425741e741774107409740273fb73f473ed73e673df73d873d173ca73c463be63b773b073a973a2739b7394738e6387738073797372736b7364735d7356735063497342733b7334732d7326731f73187311730a730372fc72f572ee72e772e072d972d272cb72c47
|6,2=>0x535752e7527752075197512750b750474fd74f674ef74e874e174da74d374cc74c574be74b774b074a974a2749c6495748e748774807
|7,0=>0x714870d770676fe86f686f066e886e086d886d086c976c186b986b186aa76a3769c7695768e76877680767886708669766186598651864a7642863b7633862c7624861c8614860c860485fd75f675ef75e875e085d885d085ca65c375bb85b385ac75a4859d7595858e7586857e857775707569756185598552754b7544753c8
|7,1=>0x8c488bc88b488ad78a5889d8895888d8885887d8876786f7867885f88587850884888408838883178298821881a7813780c780487fc87f487ed77e677de87d777d077c887c177ba77b377ac77a5779d8795878d8785877d8776776e8767775f87587751774a7742873a8733772b8724771c8
|8,0=>0x994798c8984897d7975896e7966895e8957794f8948794089397932792b7923891c7915790e790688ff78f788f078e978e188da78d378cc7
|9,0=>0x9b679b069a979a2799b7
|10,0=>0x9bd6
|_,_=>0
def wAt:=mkWire dB 134 250 0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 1000003 zs)
def oP:Nat→Nat
|0=>0x30a43c511301014290f0540c410b010303d0a054a01f2e0c414291a1601c0d030a40c410b01014290b0103c290c054303d050a43091010746404030741429190100c15050a41c151901014290f2440c151901028150c2247004070541c3d050a428150b01014290f0a41c151c0101429030a464040a0541c511301014290c0a40c410f0542c04050a430290b0102815
|1=>0xa0543c110c055242b0e03414250c0a43c1d170cc041d050a42c040f0543c310a0544833120c4040d050a5200f0107c1429070a41c15010fc14291e03c483f010341429071042c040c0f414290c054180f010f428150944434270c0a43c15030681c3d050043c29010cc10580c0340c290c054180f0f0c434290f0541c511301014290c0a43029120fc040d0a0541429
|2=>0xe07c0431050a424150c0a5080f590f40433050a40c5e01074142959034142912074040d0f0a4103d0c054384f0c034102903574685b030a41c15170cc041d050a5240f041640c290c0543cd14607c043f050a44c29530ac0c314307c24350c0a50c330c0043c29053541c291c0103c150f07414290a054683d070541c290b01030150c0f4142907014043d050a43c29
|3=>0xa1a4001f050a43c290f054483f0103414294303c1831010f41429120fc040d050a5701f1703414d5070a40c1d170cc14d5070a470150f0740d655903c0433050a4380f010c414290f0a470040f07414295f0ac1c81030540c250c0a430010f0a430150f05430290a05414290d0cc3c290f0541cba1203c28810f5c95415190a42815000c43c150f0a4180f010f41429
|4=>0x30a43015030a4041d050a41c050f0541429430cc383d010c414294903c24810c0a4383d010c50c3f090f430291203c483f0103414291707c5c33350541c29590f40433050a41d951a1680c290c054040f010f414290c0a43015074994815130a55417350341c290c0043c29050741c290103c1429190a40c1d0c595643f010cc14290b01014290f0c430295c0fc5c0d
|5=>0x70341429350341429070a41c151a03c1429070a41c15050a46858030a41c151c0181c3d050a4317217034041d050a43035060cc3429031e8483f051640c29130a430150c03414290b0a4303d5c0ac5c0d0107430b90c018040f050a50c33500542c290c0f42c150c0f4281507438383d0509448330103428154f0cc381f040a43015031042c040c0f41429490ac1059
|6=>0xb0a4303d0f0a404330e07c0431050a45c730f0742869460cc043f050a548170309430290f2780d65010cc1429440a434270c0a43c1507468043f050a44c29030c41c3d0603c043d050a41d26120c41429490cc380d040a47c0d13018300d050a43c290107414290a2040c155f0ac1c81030541c15120fc040d0a054383f0509430290d0c414290f0a43c15074746406
|7=>0x40f43015030140d220107c14294307c10010f0a43015120fc040d050a54017090f430291c0543c1d0a0548031050a40c2903054043d0b010303d050a414291c0547029070f50c1f0e0f404315205c0c250c0a4483f1203c5815030a4103f0a05430150c0a50c0f090d43029050a470290f074311a060fc14010f0a540170f0943029074746406030741429430fd4015
|8=>0x10f414290f07414d5070a415d90f09830290f5940433050a43005010f41429050a4308203054d40d070a41c155d0a430360f054480f200a40c150c0f410290c0543c1d053581c29040043c290c054483f010341429035980433050a4640403074041d050a40c410b010303d050a530294c0ac1c350a7242c070f0c40c290107d2c2b0c0d43c15700a46407030752c2b
|9=>0xa0d8303d0f0540c31010c414291607c0c29030547004070f414291703c6829070545831051640c290e07c24150c0a45831030a40c155205c240d0c0a430360f0542815780a46417070342c040f0c414290e0f410290c05434310d0a43c15170cc14d5070a4180f010f41429010c40433050a46415190a41c0d070a47015070f5b017070043c29050a4103d0c054180f
|10=>0x30c40cd5070a40c150107c142905004303d0f0a41429070083c29120cc1459030a41c15010f428150f074043d050a41c15190ac1c0d590340433050a44c170c0340c29040083c290c05430150c0341429050a43c310c0a41df1051680c290a05430010f0a40433050a45c33053541c291305430290c0340c150107c1429530a4100d0c05480d7070a40c151c0181429
|11=>0xc43c290f0541c29072040c150107c142905074041f050a4103d0f0a43015200ac0c15030c424350f0543029050a40c250c0a414290403430150b0183c31050a44833010341429170fc041d050a4683d070a41c15010cc14290c0a40433050a4481d0103414290a05464150703434310f0a43c1503824102b0c0543029010f41429040083c29050a430290c0544c07
|12=>0x30a434310f0a43c150f054041f050a4680f070a41c151a1600c290705414310309430290c0a42c150f0c52c2b0f04430150f0a40433050a414290f0a430151707c6829070554817130a40c310007c3c290f054480f051640c295f0ac1c81030545c3f0107414290603c34290f0541833010f414290c0f43c150c0a434330f0a43c151703414d5070a45c33010741429
|13=>0xc054103d0c0540431050a414020f0a40d65010cc1429170f4041d050a5302b1c0541c3d1a0a41c15070356431010cc1429200c40c2903055b0151c0a43006010fc14290507470290f0755415071640c29000cc3c29050a40c29030c414292035c0c150f0a4041f050a42c070f0c41429130540c310a054481d0103414290903424150c0a57c2b072040c15051641c0d
|14=>0x14290f0a41c150c0f41c010f0a43c290c0547029070f430290c054043f050a41c5a030a4641507034040d050a464170703430810305430150c0341459030a43029050a4303d0f0a41c150a0540c31050a430360f0540433050a4802b03054103d0c054642b070340c250c0a48033030541c3d070a41029
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0xe302cc00001d0034000c000
|5,0=>0x4540000000000000000000000000000105040100003c4000000000000000dd40000d0c00000003130b8c0000000000000029500000000914213078c1a405541410000113
|6,0=>0x419000040900003fccfb43e0cf443c4ced43a50e7238d0e033710d9335c8d43344ccd4328cc7330d0000300cbd32ec8b742d0cb222c08ad32a8ca640000a3327d09b4260c000254c923000090200008c42210844204c7d41e507541c506d41a8c66418905e4169056414905111350494
|6,1=>0x718dc246f900006f09b936d8db336c0dac46a11a5368c99f4670d99365519230001902634d894618d8245f917a45d917245bcd6b40001683591000058115e256cd57454d1503534d4a351914244f913b34e0c0004d113134bc92c34a11244484d1e34709184454d123000110243110a2
|6,2=>0x213483d20c3824e072810e0137f8dfa47d91f337c0ded37a500007951e14778ddb3000000075d1d34740dcd30001c94
|7,0=>0xb3cecc3b24ec63b10ac13afcabc3ae8ab73ad0eb13ab8eab3aa0ea53a88e9f3a70e993a58e933a44a8e3a2ce883a14e823a00a7d39e8e7739d0e7139b8e6b39a0e653988e5f3970e593958e533940e4d3928e473910e4138f8e3b38e0e3538c8e2f38b0e293898e233880e1d3868e173
|7,1=>0x3763dccf703db4f6a3d9cf652d88f5f3d70f593d58f542d44f4e3d2cf483d14f423cfcf3c3ce4f363cccf303cb4f2a3c9cf243c84f1e3c6cf183c54f123c3cf0c3c24f063c0cf003bf4efa3be0af53bc8eef3bb0ee93b98ee33b80edd3b68ed82b54ed23
|8,0=>0xebcbad2eacba92e9cba52e8cba12e7cb9d2e6cb992e5cb952e4cb912e3cb8d2e2cb892e1cb852e0cb812dfcb7d2decb792
|9,0=>0x3b410003b31ec87b11
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 14
def pmP:Nat→Nat
|0=>0x258000910002400008d000220000820002040008000015000048000104000400000e000028000094000210000800001600005400014000048000100000380000800001c000060000140000400000c0000200000400000
|1=>0xc2c00212000820002010006fc001bd0006ec001b1000624001880004bc001290004800011f000464001180004580011200044400109000420001060004100010300040400100000294000a3000284000a000026400098
|2=>0x1167c04499010d7c04319010978042590106fc040480100000232f008ca4021bf00801c020010066fc018bf0060a4014bf005020011bf004080009bf0022a400801002000005bf00105c0041400102000401000efc0038b
|3=>0x10001c3212f0c8484303270906fc203bf080ee420381080cbc2021b0807fc2010108010420022080080200120426bc108af040cbc101bf0400f410021020664055bf01527c054990152600548e01522405419014020045bf
|4=>0x210234840052046fc8109f2016fc8031f200c78801bf20001c800011426fc508af142224508271400a4500011116fc4440611027c440971046fc411bb1046044110b10428c4108310406c410031012fc401bf1004044008b
|5=>0x4406fd101bd4406e5100a5440285100144400451000d408efd02329408c25019bf4062bd018a9406225018294026fd002084006fd001064002010001830425cc0491301224c00012807fca00592106e48411c21045484095
|6=>0x800009400af
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x4020004020400
|5,0=>0xf0000000000000000191400180000000036000400003c02000000004500000302042613470002
|6,0=>0x96031900010c0143901919160133040111700018ae2b0b66287d7c3515220001aa0092010184194d18ab816910723e0003010101b9740f0108a00f52000134010b0020000199022226271208054b303d01a68e8c0126a800c10a0f377102016101100004059e01000101000a002d5b4e2f64191d5f035231ba1e1b062b574f19
|6,1=>0x281e01010143014329291a4258b2000d2c014800006aa90173001b
|7,0=>0xbc0e5c7a86b12a1da4079c6f263146b05324b6bf6331773b94625e219c40919a6b553ba33b8f8dac78a7b5173f62af7f94b33bbb2e5d0f802ab5674ca0018b017d0c9f9a23a2a1563b6e9850836ca84479b03409ad2660876d32342589933b8d5446971c7839882c5a3b65a37682a01fc07e59b8857b3bbd49
|8,0=>0xa59da58b3a6cb7be54b451be829b414a593bad685495ad758a688b98
|9,0=>0x3b38984146
|10,0=>0x3b
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 22 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_248 8 roots_248 ops++addP pm 1 dom_209 7 roots_209 ops++addP pm 2 dom_169 7 roots_169 ops++addP pm 3 dom_121 8 roots_121 ops++addP pm 4 dom_185 8 roots_185 ops++addP pm 5 dom_233 8 roots_233 ops++addP pm 6 dom_177 5 roots_177 ops++addP pm 7 dom_217 8 roots_217 ops++addP pm 8 dom_241 8 roots_241 ops++addP pm 9 dom_240 5 roots_240 ops++addP pm 10 dom_153 5 roots_153 ops++addP pm 11 dom_201 5 roots_201 ops++addP pm 12 dom_216 5 roots_216 ops++addP pm 13 dom_225 5 roots_225 ops++addP pm 14 dom_184 5 roots_184 ops++addP pm 15 dom_137 4 roots_137 ops++addP pm 16 dom_105 5 roots_105 ops++addP pm 17 dom_113 5 roots_113 ops++addP pm 18 dom_89 5 roots_89 ops++addP pm 19 dom_57 5 roots_57 ops++addP pm 20 dom_232 5 roots_232 ops++addP pm 21 dom_161 4 roots_161 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_249 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_209 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_169 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_177 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_240 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_153 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_201 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_216 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_225 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_184 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_161 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_248 8 s (0,roots_248.map (·&&&dom_248)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_249 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_248 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_249==dom_249)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 1000003 zs symsG zs (hk 1000003 zs)
theorem ori_ok {v ys} (h:RunD true dom_249 gM v ys):RunD true dom_249 gM v (ori ys):=pickMin_runD 1000003 ys h symsG ys (hk 1000003 ys) symsG_ok h
def Z (s:Nat):=barP dom_249 gM mpG SD SS NN hAt idxH ori 1000003 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 7 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 40 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 40 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 155 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 27 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 155 → Z 6 i = true := (range_split z6_0 z6_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 121 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 121 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 28 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 28 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 5 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s:Nat) (hs:s≤10):∀ i<NN s,bar dom_249 gM mpG SD SS NN hAt idxH ori 1000003 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
  · exact z7 i (Nat.zero_le i) hi
  · exact z8 i (Nat.zero_le i) hi
  · exact z9 i (Nat.zero_le i) hi
  · exact z10 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 6 5=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤10) (h:RunD true dom_249 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_249 roots_249 goal_249 11:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_249
theorem lowS_249:Lower true dom_249 roots_249 goal_249 11:=S_249.noCircuit
def isoMvS_95:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_95:Lower true dom_95 roots_95 goal_95 7:=lower_iso_b isoMvS_95 (by decide +kernel) lowS_63
def isoMvS_111:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_111:Lower true dom_111 roots_111 goal_111 7:=lower_iso_b isoMvS_111 (by decide +kernel) lowS_63
def isoMvS_119:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_119:Lower true dom_119 roots_119 goal_119 7:=lower_iso_b isoMvS_119 (by decide +kernel) lowS_63
def isoMvS_125:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_125:Lower true dom_125 roots_125 goal_125 9:=lower_iso_b isoMvS_125 (by decide +kernel) lowS_123
def isoMvS_189:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_189:Lower true dom_189 roots_189 goal_189 9:=lower_iso_b isoMvS_189 (by decide +kernel) lowS_175
def isoMvS_190:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_190:Lower true dom_190 roots_190 goal_190 9:=lower_iso_b isoMvS_190 (by decide +kernel) lowS_183
def isoMvS_207:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_207:Lower true dom_207 roots_207 goal_207 9:=lower_iso_b isoMvS_207 (by decide +kernel) lowS_183
def isoMvS_215:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_215:Lower true dom_215 roots_215 goal_215 9:=lower_iso_b isoMvS_215 (by decide +kernel) lowS_175
def isoMvS_219:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_219:Lower true dom_219 roots_219 goal_219 10:=lower_iso_b isoMvS_219 (by decide +kernel) lowS_187
def isoMvS_221:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_221:Lower true dom_221 roots_221 goal_221 9:=lower_iso_b isoMvS_221 (by decide +kernel) lowS_175
def isoMvS_222:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_222:Lower true dom_222 roots_222 goal_222 9:=lower_iso_b isoMvS_222 (by decide +kernel) lowS_183
def isoMvS_231:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_231:Lower true dom_231 roots_231 goal_231 7:=lower_iso_b isoMvS_231 (by decide +kernel) lowS_159
def isoMvS_235:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_235:Lower true dom_235 roots_235 goal_235 9:=lower_iso_b isoMvS_235 (by decide +kernel) lowS_175
def isoMvS_237:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_237:Lower true dom_237 roots_237 goal_237 10:=lower_iso_b isoMvS_237 (by decide +kernel) lowS_187
def isoMvS_238:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_238:Lower true dom_238 roots_238 goal_238 9:=lower_iso_b isoMvS_238 (by decide +kernel) lowS_183
def isoMvS_243:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_243:Lower true dom_243 roots_243 goal_243 9:=lower_iso_b isoMvS_243 (by decide +kernel) lowS_175
def isoMvS_245:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_245:Lower true dom_245 roots_245 goal_245 10:=lower_iso_b isoMvS_245 (by decide +kernel) lowS_187
def isoMvS_246:List (Nat×Nat):=[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_246:Lower true dom_246 roots_246 goal_246 9:=lower_iso_b isoMvS_246 (by decide +kernel) lowS_183
def isoMvS_250:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_250:Lower true dom_250 roots_250 goal_250 9:=lower_iso_b isoMvS_250 (by decide +kernel) lowS_183
def isoMvS_252:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_252:Lower true dom_252 roots_252 goal_252 9:=lower_iso_b isoMvS_252 (by decide +kernel) lowS_183
theorem lowS_127:Lower true dom_127 roots_127 goal_127 10:=lower_slice_b [(0xcccccccccccccccccccccccccccccccc,8,10)] (by decide +kernel) lowS_125
theorem lowS_191:Lower true dom_191 roots_191 goal_191 11:=lower_slice_b [(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,32,36)] (by decide +kernel) lowS_187
theorem lowS_251:Lower true dom_251 roots_251 goal_251 12:=lower_slice_b [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,8,10)] (by decide +kernel) lowS_249
namespace S_254
def pG:List (Nat×Nat):=[(2,10),(2,18),(2,130),(4,36),(4,68),(4,132),(6,14),(6,22),(6,38),(6,70),(6,134),(8,10),(8,40),(8,136),(12,14),(12,44),(12,76),(12,140),(16,18),(16,80),(16,144),(20,22),(20,52),(20,84),(20,148),(24,26),(24,56),(24,88),(24,152),(28,30),(28,60),(28,92),(28,156),(32,36),(32,40),(32,160),(34,38),(34,42),(34,50),(34,162),(48,50),(48,52),(48,56),(48,112),(48,176),(64,68),(64,80),(64,192),(66,70),(66,74),(66,82),(66,194),(72,74),(72,76),(72,88),(72,104),(72,200),(96,100),(96,104),(96,112),(96,224),(98,102),(98,106),(98,114),(98,226),(128,130),(128,132),(128,136),(128,144),(128,160),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffffffffffffffff
def xsM:=roots_254.map (·&&&dom_254)
def gM:=goal_254&&&dom_254
def NN:Nat→Nat
|5=>4
|6=>51
|7=>246
|8=>232
|9=>47
|10=>5
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0x2085017898139590d1bd
|6,0=>0x8e7b85dc575d83455f72507f24f9354cb53442d844266408f83fc513d66934d46343b32d5ec2b2f5254e71d2471b4c91b2171ad40192ed1905b18db01734c1636c1511a14af8122231219711efa10a92108bb0fde70f7290eae70dc580cd780bb220b39f0a0f70980b0938008eed0817306ef804b8b02ea801cc00156d00fa0
|7,0=>0x1a8cb1a84619c96195251946d189b61802c17eab17c7617b8d178dc16e1016b4e165361634e15c9015b3014976148a214800142e913f3513f0a13d7313a52129e511d3511d1d1197c1164a1149c1149a10a92109211091a100c40fcd80fca00f8ef0f79d0f5320e64e0e5180e4300e37d0dcec0d92a0d5590d4d70d3ee0cd530ccfe0c9b80c9a80c9810c9130c4110c2570bcae0b6310b41d0b1280ad720ab8a0a97609d3309cf909baf09b12091ee08d7d08d1e088d90835707f9d07ab4077a707248071d40708806f4906c4e068b406891066a6060930606005cdf05905058e70568e0567a0555e05282051ee04ebd04e5304c3704ba204a8e048af046fc045d30410c0401f03b90039e9039c80397d03979037ff0353c0342102ff002e7002e3702e1602dab02ce502b98028470202001ebf0179c0169b011f700621000ce
|7,1=>0xabe8e92bfe8aad484c0681aaf721f07077a6de1e6c4a36bed968e8a653cb624a95972455dbb52a25518344eed54eae84b131470d04527044eb943c4843413429cd41be041532408f740334400c03f8413f3c43cdfa3c3113b1693b0153986537c213796f376ec376873740236aba3642c36187360d93572834d4d34be934add33c14334ff3220531ca731c7630fa9306f830412300a32fca72fa7e2f9892f8d22f6c42f16c2ee2b2ea842e4882d67d2cfa02c2482b2f52b0c52a8a72a69829e4f28b44288272849a27bcd273cb2699d2690b25cbc254e725367251f22514f24b0d24a5423fbf235bc233fd2193c21395200ec1fc4c1f96a1f4871f2841f22e1eee01eec91e1681d8791d8051d3e61cabc1bedf1bed81bd131bce31b7891b6cd1b27d1af261acdd
|8,0=>0x1e1f21d7371d43c1cdd21cdc91c5981c36b1bedf1bc681b92c1b5a71b4a51b4421b3f21abcc1aaf81a9011a77c1a4d81a43b19a1a199ce1929e18f5d18bbd184bb1841917fc717a7e174e91718b170a2165191631315f301535d14483142e9120b411fad11bf0116791121910cde106150fd600f57a0efbf0eec50ed010eb690e0b10dd550d8c30d7310d5ef0cf3a0ccf80cc410c9fb0c11f0c0d70c0560bf210bd5c0bbce0b95d0b7970b2c20ae4d0aba90a9600a80e0a6810a49e0a4010a3270a08509e3c09590094f608ed508df508944087c3086cb080b6077a70770b075ec074c2073650727b0724a06e0a06df606b7e0656c064e60644b063b90627705e3305cb605c9c05a5d05a030585205777054cd0445b03e4003b90039e902df002b98026d702271020e1019ab0198f017bd0141d012f500ea3005a0004b90028d
|8,1=>0xc0cecb9cfeaaff0a364fa32379bf9f8aad46d3a8681c6642126212a5c87359d6157ce2571c456ea656bcf55d5455ba2552da5519f52cf4525c151329505e84ebc64e5b54b1314a98e487c3471994527044e1243bbd43ac6438734334e423884101f4084b4078f3d0903c3113c0df3ae563a2893a128391c538f0036f59369cb3697135b903570435305348743465a32b8232b7b31ca731a053173c31645309cb300a42f6202f0e62f0052e69e2e4d12e13c2d9e52cc2d2cb052c9ca2c81d2c3232b5672a93f2a87528e5628d7928b4426f8025f3424abf2446f2384e234c72276e220c221c0b219da217b020824207462013e200ec1f6c51f3321f1de1eab71e8af1e293
|9,0=>0x9e7448147b64b8f5b1cb512b2500544dee349db73f8373edc53c3ab36f59324d730a152e8212dd962c5312752623d5a23b1320ef41f3011d1f81c12a1a9501a4ba1a2d117d4f172e915e8815b03147e71431f13428109440ee070ed650b3000a68e099df0886a0673d0551504cad04c90022e2007f8
|10,0=>0xba90f4ae32371a00a6d404bea
|11,0=>0xba90f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa888888888888888888888888888888880000000000004444000000000000444400015554000155540001111000011112aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa800000002aaaaaaa80000000555555555544554455555555554455445500550055005500550055005500550088888888888888888888888888888888888888888888888888888888888888881414141414141414141414141414141414141414141414141414141400000002aaaaaaa800000002aaaaaaa800000002aaaaaaa800000002aaaaaaa800000005555555555555555555555555555555555550000555500005555000055550000aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa000000040400000404000004040000040444444400444444004444440044444402aaaaaaaaaa82aa82aaaaaaaaaa82aa82aaaaaaa800000002aaaaaaa800000005555000055550000555500005555000055550000555500005555000055550000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00aa00aa00aa00aa00aa00aa00aa0141414141414141414141414141414141414141414141414141414141414141408888888888888888888888888888888888888800888888008888880088888805555555555555555000000000000000055555555555555550000000000000000
|0,1=>0xaaaaaaaaaaaaaaaaaaaaaaaa88888888000000000000000000000000000000015555555555555555555555551111111155555555555555555555555511111112aaaaaaaaaaaaaaaaaaaaaaa800000002aaaaaaaaaaaaaaaaaaaaaaa800000005555555555555555555555555555444455550000555500005555000055550000000000aa000000aa000000aa000000aaaaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa15555555511111111555555551111111000000000000000000000000000000002aaaaaaaa22222222aaaaaaaa22222222aaaaaaaa22222222aaaaaaaa22222225555555555555555555555555555555555555555555555555555555500000000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a15555540155555401555554015555540155555401555554015555540155555402aaaa8282aaaa8282aaaa8282aaaa8282aaaa8282aaaa8282aaaa8282aaaa828000000000000000055555555555555550000000000000000555550505555505000000000000000002222222222222222000000008888888822222222888888895555555555555555555555555555555400000000000000000000000000000002aa82aa82aa82aa82aa82aa82aa82aa82aa82aa82aa82aa82aa82aa82aa82aa85555555455555554555555545555555444444444444444444444444444444444
|0,2=>0x222222220000000022222222000000002222222288888888888888880000000044444444000000004444444555555555555555551111111111111112aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa828282828282828282828282828282800000000000000005555555555555555000000000000000055550000555500000000000000000000aaaaaaaaaaaaaaaa0000000000000000a0a0a0a0a0a0a0a15555554155555541555555415555554000000000000000000000000000000002aaaaaa82aaaaaa82aaaaaa82aaaaaa82aaaaaa82aaaaaa82aaaaaa82aaaaaa85555555555555555555555505555555055555555555555550000000000000000aaaaaaaaaaaaaaaa888888888888888800000000000000000000000000000000444444444444444444444444444444444444444044444440444444404444444000000002aaaaaaa800000002aaaaaaa800000002aaaaaa8000000002aaaaaa85555555555555555555500005555000055555555555555555555000055550000aaaaaaaaaaaaaaaaaaaa8888aaaa8888aaaaaaaaaaaaaaaaaaaa8888aaaa88895555555555555555555555555555555555555555555555540000000000000002aaaaaaaa22222222aaaaaaaa22222222aaaaaaaa222222200000000000000000055005500550055005500550055005500550055000000000055005500000000
|0,3=>0x222222220000000022222222000000002222222200000000000000000000000155555554000000015555555400000001554155400000000155415542aaaaaaaaaaaaaaaaaaaaaaa8000000022222222222222222222222200000000000000000000000051515151515151510000000000000000515151505151515000000000000000000000000000000000aaaaaaaaaaaaaaaaaaaaaaaa888888884444444444444444444444444444444444444444444444444444444400000002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa2222222222222225555550055555500555555005555550000000000000000000000000000000000aaaaaaaaaaaaaa00aaaaaaaaaaaaaa00aaaaaaaa00000000aaaaaaaa0000000155555555555555555555555555555555554155415541554155415541554155422222222222222222aaaaaaaaaaaaaaaa2222222222222222aaaaaaaa2222222555555555555555511111111111111115555555555555555111111110000000000000000000000000000000000000000aaaaaaaa88888888aaaaaaaa888888895555555555555555555555555555555555555555111111115555555511111112aaaaaaaaaaaaaaaa2222222222222222aaaaaaaaaaaaaaaa2222222222222225555555555555550555555555555555055555555000000005555555500000000
|0,4=>0x222222222222222222222222222222222200220022002200220022002200220155554141555541415555414155554141540140015401400154014001540140000000000000000002aaaaaaaaaaaaaaa80000000000000002222222222222222111111111111111111111111111111111111111111111111000000000000000000aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00880088141414141414141414141414141414141414140014141400141414001414140002a802a802a802a802a802a802a802a802a8028002a8028002a8028002a802800550055000000550055005500000055005500550000005500550055000000440000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa00008888000088880000001400000014000000140000001555555541555555415555554155555542aaaaaaaaaaaaaaaaa2a2a2a2a2a2a2a282828282828282828282828282828281111110111111101111111011111110111111100111111001111110011111100888888888888888888888888aaaaaaaa888888888888888888888888888888880000000000000000000000015555555400000000000000000000000000000002aaaaaaaaaaaaaaaa22222222aaaaaaaaaaaaaaaaaaaaaaaa2222222222222220000000000000000111111111111111100000000000000001111111100000000
|0,5=>0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000aaaa00000001555400015554000155540001555400000000000000000000000000000002aaaaaaaaaaaaaaaa8282828282828282aaaaaaaaaaaaaaaa828282828282828555555555555555555555555555555550000555000005550000055500000555000000a0a00000a0a00000a0a00000a0a000000000000000000000000000000014141555541415555414155554141555541414141414141414141414141414140000000000000000000000000000000000000000000000002aaaaaaaa222222255555555555555550000000000000000555555555555555555555555444444440a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a000a000a000a000a000a000a000a015554141555541415555414155554141555541401555414015554140155541402aaaa2222aaaa2222aaaa2222aaaa2222aaaa2222aaaa2222aaaa2222aaaa2225555555555555555555555551111111155555555555555555555555500000000222222222222222222222222222222220000000000000000000000000000000014141414141414141414141404040404141414141414141414141414000000000000002800000028000000280000002a82828282828282828282828282828280055005500550055005500550055005500440044004400440044004400440044
|0,6=>0xaaaaa0a0aaaaa0a00000000000000000aaaaa0a0aaaaa0a15555555555555555555554015555540155555555555555540000000000000002aaaaaaa88888888aaaaaaaa88888888aaaaaaaa800000002aaaaaaa800000005550555055505550555055505550555000000000000000000000000000000000aaaaaaaa00aa00aaaaaaaaaa00aa00aaaaaaaaaa00880088aaaaaaaa008800880000015400000154000001540000015400000000000000000000000000000002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa802aaaaa802aaaaa802aaaaa805555555555555555555555555555555555445544554455445544554455445544aaaaaa22aaaaaa22aaaaaa22aaaaaa22aaaaaa00aaaaaa00aaaaaa00aaaaaa000000015400000154000001540000015400000140000001400000014000000142a802aaaaa802aaaaa802aaaaa802aaaaa802aa82a802aa82a802aa82a802aa800000000000000005555555555555555000000000000000055555555444444440000000000000000aaaaa0aaaaaaa0aa0000000000000000aaaaa0a0aaaaa0a15554015555540155555401555554015555540001555400015554000155540002aaaaaaaaa802a802aaaaaaaaa802a802aaaaaaaaa802a802aaaaaaaaa802a800000000055555555000000005555555500000000555555550000000000000000
|0,7=>0xaa00aa0088008800aa00aa0088008800aa00aa0088008800aa00aa008800880000000000000000000000015555555400000000000000000000000111111112aaaa8282aaaa8282aaaa8282aaaa828000000000000000000000000000000005555555555555555555550505555505055555555555555550000000000000000aaaaaaaaaaaaaaaaaaaaa0a0aaaaa0a0aaaaaaaaaaaaaaaaaaaaa0a0aaaaa0a00000000000000000000000000000000000000001555555540000000111111112aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa800000002aaaaaaa8000000022222222000055550000555500005555000055550000505000005050000050500000505022222222222222222222222222222222222222220000000022222222000000000000000155555554000000015555555400000001111111100000000111111112aaaaaaaaaaaaaaaaaaaaaaaa22222222aaaaaaaaaaaaaaa80000000000000005555555555555555555555555555555555555555555555555050505050505050aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88000155540001555400015554000155540001540000015400000154000001540222aa22aa22aa22aa22aa22aa22aa22aa22222222222222222222222222222220055005500550055005500550055005500550055004400440055005500440044
|0,8=>0xaaaaaaaa000000008888888800000000aaaaaaaa00000000888888880000000000000000000000000000000155555541555555415555554155555542aaaaaa82aaaaaa82aaaaaa82aaaaaa82aaa80002aaa80002aaa80002aaa800055545554555455545554555455545554444444444444444444444444444444440000aaaa0000aaaa0000aaaa0000aaaa000088880000888800008888000088880404040404040404040404040404040404040400040404000404040004040402aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa82828282aaaaaaaa82828281111111111111111111111111111111111110000111100001111000011110000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa8888aaaa888955555555555555544444444444444445555555555555555400000000000000000000000000000000888888888888888800000000000000000000000000000000055005500550055005500550055005500000000000000000000000000000000aaaaa0aaaaaaa0aaaaaaa0aaaaaaa0aaaaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a155555555555555555555555555555555555555555401540155555555540154002828282828282828282828280000000028282828282828282828282800000000505050505050505050505050505050500000000000000000000000000000000
|0,9=>0xaaa00000aaa00000aaa00000aaa155555555414141415555555541414141555555554141414155555555414141400000000088888888000000008888888800000000000000000000000000000000000000000000000555555555555555500000000000000000000000000000000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0aaaaaaa0aaaaaaa0aaaaaaa15401541554015415540154155401541554015401540154015401540154015402aaaaa82aaaaaa82aaaaaa82aaaaaa82aaaaaa802aaaaa802aaaaa802aaaaa8055550005555500055555000555550005555500005555000055550000555500000000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa000088880044004400440044004400440044004400440044000000000044004400000002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa222222205050505050505050505050505050505050505050505050505050505040404040000000000000000aaaaaaaaaaaaaaaa0000000000000000aaaaaaaa000000000014001400140014001400140014001400000000000000000000000000000002a82aa82aa82aa82aa82aa82aa82aa82aa802a802a802a802a802a802a802a805555555555555555444444444444444455555555000000004444444400000000
|0,10=>0xaaaaaaaa00000000aaaaaaaaaaaaaaaaaaaaaaaa00000000aaaaaaaa0000000155415541554155415541554155415541554000015540000155400001554000000000000002a802a80000000002a802a800000000022002200000000002200220000000000000000000000001111111100000000000000000000000000000000aaaaaaaaaaaaaaaa0000000022222222aaaaaaaaaaaaaaaa00000000000000000154015401540154015401540154015401400140014001400140014001400142aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa82828282828282828282828280000000505550555055505550555055505550555050505050505050505050505050505000000000aaaaaaaa000000002222222200000000aaaaaaaa00000000000000011111111111111111111111115555555511111110000000011111111000000002aaa802aaaaa802aaaaa802aaaaa802aaaaa80282aaa80282aaa80282aaa80280000555500005555000055550000555500005550000055500000555000005550000a000a000a000a000a000a000a000a000a0000000a0000000a0000000a000000015554000155540001111000011110000155540001555400011110000111100000000000000000282828282828282800000000000000002828282800000005555555555555555555555555544554455005500550055005500550055005500
|0,11=>0xaaaa000aaaaa000aaaaa000aaaaa000aaa000000aa000000aa000000aa0000000000000000000000000000000000000155555555555555555555555400000002aaa8888aaaa8888aaaa8888aaaa8888aaaa80002aaa80002aaa80002aaa80001111110011111100111111001111110011111100111111001111110011111100000000aa000000aa000000aa000000aaaa00aa00aa00aa00aa00aa00aa00aa014141555541415555414155554141555541415541414155414141554141415542aaaaaaaaaaaaaaa802a802a802a802aaaaaaaaaaaaaaaaa802a802a802200220000000055555555000000005555555500000000505050500000000050505050aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0a0aaaaa0a00000000014141414000000001414141400000000141414140000000000000002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa802a802a80220022002a802a80220022000000000000000055555555555555550000000000000000555555505555555000a000aa00a000aa00a000aa00a000aa00a000a000a000a000a000a000a000a1555555555555555555555555555555555555555555115511555555555511551002a802a802a802a802a802a802a802a802a8000002a8000002a8000002a80005555000055550000555555555555555555550000555500005555000055550000
|0,12=>0xaaa00000aaa00000aaa00000aaa00000aaa00000aaa00000aaa00000aaa1414141414141414155555555555555554141414141414141414141414141414000028280000282800002aaa80002aaa8000282800002828000028280000282855555555555555555555555500000000000000000000000000000000000000000a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a000000000000000155541415555414155554141555541415555400015554000155540001555400000000000000000002aaa8282aaaa828280000000000000002aaa80002aaa800055555550555555505555555055555550505050505050505050505050505050500a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a000000000a0a0a0a000000015555555555555554141414141414141555555555555555541414141400000002aaaaaaaaaaaaaaaaaaaaaaaa222222222222222222222222222222222222222555555551111111155555555111111115555555511111111555555550000000000000000aaaaaaaa00000000aaaaaaaa0000000000000000000000000000000155555555555555555555555541414141555555555555555555555555414141400000888800008888000088880000888800008800000088000000880000008805555555555555555000000005555555555555555555555550000000044444444
|0,13=>0xa0a0a0a0aaaaaaaaa0a0a0a0aaaaaaaaa0a0a0a0aaa0aaa0a0a0a0a0aaa0aaa0000000015555555400000001555555540000000154015400000000015401540222222222aaaaaaaa22222222aaaaaaaa2222222222222222222222222222222000000000000000044444444555555550000000000000000444444444444444400000000aaa0aaa000000000aaa0aaa000000000aaa0aaa000000000aaa0aaa000001400000014000000140000001401540154015401540154015401540154000000000000000002aaaaaaaaaaaaaaa80000000000000002aaaa2222aaaa2225555555555555555554455445544554455005500550055005500550055005500aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa8888aaaa8888aaaa8888aaaa88895554000155540001555555555555555555540001555400015555414155554142aaaaaaaaaaaaaaaaaaa8282aaaa8282aaaaaaaaaaaaaaaaaaaa80002aaa800055555555555555550505050505050505555555555555555500000000000000000000aaaa0000aaaa00000a0a00000a0a0000aaaa0000aaaa000000000000000154015555540155555401555554015555540154015401540154015401540154022222222222222222aaaaaaaaaaaaaaaa2222222222222222aaaa2222aaaa2225555555555445544555555555544554455555555554455445555555555445544
|0,14=>0xaaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa1555400015554000155540001555400015555554155555541555555415555554000000000000000000002aaa80002aaa800000000000000000002222000022225555555544444444000000000000000055555555444444445555555544444444aaaaaaaa0a0a0a0aaaaaaaaa0a0a0a0aaaaaaaaa00000000aaaaaaaa0000000014141414141414141414141414141414141400001414000014140000141400000000000000000000888888888888888800000000000000008888000088880005555555500000000555555550000000055505550000000005550555000000000aaaaaaaa00aa00aaaaaaaaaa00aa00aaaaaaaaaa00000000aaaaaaaa000000015555555541554155555555554155415555555555414141415555555541414142aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa82828285555555505050505555555550505050555555555050505055555555500000000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0aaa0aaaaaaaaaaa0aaa00000141400001414000000000000000155555555555555540000000000000002aaaaaaaaaaaaaaa80000000000000002aaaa8282aaaa82800000000000000005555550055555500555555005555550050505000505050005050500050505000
|0,15=>0xaaaaa0a0aaaaa0a0aaaaaaaaaaaaaaaaaaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a154155415541554155415541554155415541554015415540154155401541554008888000088880000888888888888888888880000888800008888000088880000000000000000000000000000000000055555050555550505555505055555050aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa88aaaaaa88aaaaaa88aaaaaa8955555555555555540001555400015555555555555555555400000000000000000088008800880088008800880088008800000000000000000000000000000005555001155550011555500115555001155550000555500005555000055550000a0a0a0a0a0a0a0a0aaaaaaaaaaaaaaaaa0a0a0a0a0a0a0a0aaaaaaaaa0a0a0a141414155414141554141415541414155414141414141414141414141414141400002aaa80002aaa80002aaa80002aaa80002aaa80002aaa800000000000000050505555505055555050555550505555505055555050555550505050505050500022002200220022002200220022002200220000002200000022000000220000000000000000000000015554000155540000000000000000000000000000000282828282828282828282aaaa8282aaaa82828282828282828282828282828280000000000000000000011110000111100000000000000000000000000000000
|1,0=>0x1400000014000000140000001400000000000000000000000000000002aaaaaaa82828282aaaaaaaa82828282aaaaaaaa828002802aaaaaaa828002805500550055115511550055005511551100000000000000000000000000000000aaaaaaaa00000000aaaaaaaa22222222000000000000000000000000000000014141414141414141414141415555555541414141414141414141414141414142aaaaaaaa22aa22aaaaaaaaaa22aa22aaaaaaaaaa22222222aaaaaaaa22222220505050005050500050505000505050005050500050505000505050005050500
|_,_=>0
def sP:Nat→Nat
|0=>0x48100e021703c00090201c5a0b140242a2c038ac16120485c08070102c50090201c160a1109c0807010984a00090244608038081e220e8100e020788424190200c040f100003a090e01c040f00024081b0180816000c034080c0102c00090b05428110584812040380826000902408110180820000481c040f070001a040602c1400048200e02030000a04018080200
|1=>0x110424320e8100e02200483c090e01c040f000600807010c47e120201c04011f0002430020440e2d05800640403808623d0902408071e0080212048700e020588876090201c043a0002452040180820000481018021c83c0037020d80602058006a090201c0434090c83a040380862121805408030102c00090a8200e02080002804038081625090240807010bc0012
|2=>0x382ca4000902408071694416000c83408030114000090b020040f278001208089381600090240e022691c9812048a408071682c50090202c144b0004832180201c620a090740807010c47e1204810164a2480024090102c90470004812460201c040b000640807010e47a120200c040b1f0007018048100e45058881204038088800090100e020589400120c8740807
|3=>0x201c0439058481263310100e0205848c2190200c040f0004812160201c5a0b000a83a040382c14003004812160a8d8060b0004812552f8200e0207800120403974b40b1102408070102cb8000902452040396816000902408070103c6800090242804038b4040b11160120403808162209024aa07010e48e0009024ac040880c1600090244604038081e22090741204
|4=>0x1c8002409021cc040f3900012040102ce022000481204011c4167000048126f0201c5a2b05848120803808166e0c9b40807010c400120485428040881c1612028100e2d05800c20d0200c040f05800d6090200c040f0580032180201c040b00048126902044040b0004864090201c160a0004812162a9a0040f0004812670201c040100048121602194040b00048c809
|5=>0x201c0431079f824090a8100e020800024090201c040f0008424300201c040b000481204038b4167c049ec08071682c44120682408070102cf2000201c040b3c0f80012190100e023b9d80012048100e02058883e18048100e31058282433048100e021888824090201c0431059d424090b020222d0580024640c02408070102c24090a97c0e74058002419068100e02
|6=>0x448100e02058f800120f02408070103c001f048100e02058d080120485c0e02059980012048580e0207a2000120481c040b2388800122a0240807010c41612320741a0403808161204a0cc604038081612410240802059c00012049a4aa070103c00120c0100e021882cc012048100e0b4088900320481006020588000090201c040b1d000240d0201c040f3f8002409
|7=>0x380816900902408070103d1e22090251c150201c5a0b000242a04039d0560b090242a8d038081600090240807010c4443f0902408030123000092f8100e5d1682c44090b020040b2780024090201c044d26048125503808728b000481a0403808167e00048120403808028a00048c20d02008165700064120403808624d090242e0403974162204810e602079c00012
|8=>0xa81c040b0004812690b810220b0004812294c01c040b00048641d0201c0431090240e020782d2e00090243807010c41600090251c160401c040b000240802079c12c000907412040382d28000902408021883ce000090242c08038081e88000c812043980c040009065260403808162209024520448808160009024108d03808160009024d2550401c040f000601204
|9=>0x201c160a5084812550401c043907800321d0201c043a000483a0902280040b0004812150401ce80b0004812171201c040b11048320403808627600048129b0201c040b000482e0403808163e00048126903938040b000493c0d0201c5a0b1100076090201c040b0027412170a0100e0205a701216020b4165700048129b020081649000483a0d0201c040b480481299
|10=>0x1882cfc120485c080701098001204810044f2800024090a8900e2d05888120803808168b110006409021cc0450000481a040380816a60004864090201c04400004812a50380816660004812160880816a400048120803938040b00048120403808623d09034080705a040080048100e2d05a8c00120481c040f5122c0012049541007010c44418048100e5d1682c3a09
|11=>0x4810040b1014000124f2bc08071682c000d04810060205940009e0c0100e0b0500024090a8215c07058002409148200e2d058002419048100602280002409118200e020588864040102ce0ad000483a04038081621090240807010c416ab0906012040382c14000902408110595d540009024080705aa400800485808115402c0012068100e02058014e12048100e02
|12=>0x580012930201c160a11048125f040100e021883c12150201c5a0b000a808070102c4a00090241007010c41e8b0002568040881c040b090242a040382d6600090242804038081649092c812040102ce0000907812040382d28000902428040380816b1090242c030102d100009024deb00380816121d8240807010c416222a02408070102c00121902408020592c0012
|13=>0x5828001d048100e310582824640e82408070102c24090aa6022070580024090200816b93800024190e8100e022180024093d8200e020588824090201c04440004912040881c16b800048c2320200c040f0580012140201ce802058483c0902280040b0004830040382c14005b04812160401c040b000a81a090380816970004812040102d6a70000492a3b048100e02
|14=>0x182d5400090242c035d00816000902408035f808160009060120403808623a0902452070102d48000902408070102cfc0009024d20701004e400090c83a930201c040b092f8120403808620f090257a07012f00012048100e021882c441f0481006bb0102c00090201c5a0b2500024323207408070102c24090b01d7402058002419498100e0207800240d048100e2d
|15=>0x198740807010c424090201c040100049121d0201c040b110492a090201c1694000481a0902044062d0580012294701006020580076090201c040b1100012160400816570004812552f8200e021884984090201c5a0b1102428080201c040b4e060120403808620f092781a041b00c0e0b0025412040380816000f8242c07010058200090c808070102d8000090242a04
|16=>0x91ac1204018081600090ec12040380816005602408076402c0012048100e2d05b180012048501004038081612410640803038081e000485c0807010ac1622048901007010c41e120f02408070131400120c0240807010c49812048582a11058002492190643a04038086212190240807010d0001204854083605aa80012620240807010e400120200c0e02058f800c3
|17=>0x90242e14038081678090251c04038081600090242e04038081600150601a040380816000d0242e080380816001c25412040382c1400090601204038b4160a000251c170201c040b000242c070102d4800090242e110382cf0000902408111682c92000902408071682c14000907812040382c1400090c83a04038081622092783004038b416220018408030102c7c00
|18=>0x3481022020580024d0048100e020780024090201c040b2e00024091481006020580024090b15406020580024090201c040b66800240d0201c040b003301204038081e00260483a090201c040b3f00024090200c040b001b0a86d048100e020580024094d8100e2d0102c0012048100e2d0588800cb0481192070102c0012048100e021882c00120f8242a65038081600
|19=>0x14d04090200c0e020782c00096b0100e020580024092a810d0070103c00120481058070102c4412048100eba0102ce4000927808071682d700009025aa040380816000902408730180816006182408030102d9e00090242a041b00c0e0b0004812040380816006984830090201c0439058002409021cda402058002409688100e020580024190c0100e02058002409
|20=>0x38081622000493c0d0201c5a0b00025b2040380816000902408d80102c0012048200811038b416000902408070102c74000902408030103c1650003081204038b416000918412041b00c040b00048128e0b0100e020580024090201c04310580024ac32034120403808160009025ae040380862000903412041b01c5a02058003009498100e020584812690201c040b
|21=>0xe8100e2d058002409348100e020593c0012048100e2d0102dc212048100e2d013801600093101204038081622000483a0d498100e0205848120403b7c040b6f00024090201c040b6e00024040380816db00049863204810e607010002432048100e02059c0001204adc100403808160009074120403808620b0910812043281c040b0004812046d0081600090242a08
|22=>0x90242e140201c5a0205848120408b48040b00048121602044040b0004924092a8100e021c83c0012048100e0205ba40012020d9d0071680816000903408070102d020009024aa08038081e000939812040380816000902408030380816b80004812690201c040f05801ca090201ce8020580024e4048100e020580024e34102408070102c0012048100e0205b88249e
|23=>0x102c001204a6c08070102c00124f03408030380816000c02526040380816220918412043400c040b000481204038b4040b1f000241d758100e020580024090201c040b5480024090b35c0e020782c00120e82408070102d0c12048106c0205aa800120c86008070102c4400090240811018081600618242a040382dd40009024480403808162240024aa04038086222
|24=>0x4102408070103c160009024080778808160009064120403808a000090643a04038081e000902408070102c00127807412040380872310584812ee0201c040b0004812160a8441600091843204018081600093901204038081622000481a090201c04310588824090201c040b1a00024090201c040b768002409023480e020782c00090b8100e2d0102c009c760240807
|25=>0x91841a040102c40000906012040382c14000902408070102cea00090241004038081600260241004038081e0b1100012160200c040b2b80024090201c040b000842409020440e0205a900012048a42a04038b416000902526040380816004002408070102cf0004e0601a090201c5a020580012040380816f300048301d048100e021882c2419068100e02058800012
|26=>0x201c16aa00048120403bd0040b0004808367401c040b00048a8090201c040b00048121502044060b0004812080201c040b4f80024090201c040b5500186090201c0443058002418048100e02059dc0012048100e0205b8424090b01c040b4400024091485810070102c001204a0c2a0403808160009024d25503808160009024080c0102c00120485408071682d5400
|27=>0x493ce70201c040b00048120403808720f05800bc090201ce80b0032c240903808620b238002409148100e02058002492048100e2d0102d62000902408070102c7c0009024aa0403808e2000906412043401c04000902408072e80816fa09025f004038081600093dc1204038081600090641204038089a0009024081103aa01600090242c0403bd8040b000493c09
|28=>0x907412930201c040b090741a040380816220902410047f01c040b000486409498100e02058002409438100e020580024090201c040b7e8002409120100e021c82c24323202408070102c001204859f8070102c0012049a42c070102ce4000939430090201c040b000483c32048100e020580024092a8200e0205888001204bec0803038081600090242c08038081e0b
|29=>0x4812170201c040b0004812171201c5a02058002461068100e2d0102c00120488c08070103c00125902408070103c160009405ce090201c040b0004812fc0200c0e0205800240d0481022071682c00090200c040b8000024097f8100e020580024090201c040b3f00024610200c040b6f00024091481022030102c0012048100e02059e800124f03408070102c4400
|30=>0x9024d204038b4040b000492a32048100e020580024094d81022070102c00120485c08070102c44000902408070102c00a709024080781008160009024be0403808620b110490489048100e020580024090201c0401000493caf0201c040b0004866090201c04310004812080201c040b518002409040100e020595c00124482408070102c44000902408110180816de
|31=>0x20440e0b000481204038081e0b001802409348580807010040012048100e020782c006a0481006020594000120482008073a00816220027812040181c5a0b000483a090201c040b6a0483a0d0201c043105848120403b201600090240807010c41e002f0242a04038b416220002408070102c00128182428080201c040b0902408110382d7000090652604038081600
|32=>0x102c00128302408070102c0012154141204038081600090251c0403808160009024087303808ec000902408680102ca0000938c1a090201c040b000481204038081600094110409020d80e0205800241e0e82408070103c0012410c81204038081600090242c170401c040b00048129b148100e020580024096b8100e021883c00120c0240807010c41622092241a09
|33=>0x38b4040b000481a090200c0e02058013c09020440e0b0004812080201c040b0014c12550201c040b00049380d04a4c08070102c0012048100e0205a2c0012048100e0205800c0120495408030380816000902408070102dbc00090242a040380816000921012040380816cf000483c090201c040b00049581e048100e0205800241f0f0ec1204038081600090240807
|34=>0x401c040b0004812040380816000909c12040380816220032c2461048102202058002489048100e2d0102c00120485408110382c00120489008070103c16000902408070103c16004234012040380816000902408070102c004c0902408070103c16220004812240201c040b00048a6090201c040b00049f209020440e02058002492048100e02058880060090341204
|35=>0x902408070102c0012210240891038081600091841a040380816000902408076700816000902410040380816880004812160200c040b0004812170201c040b00048120403808168100048301d048100e020580024090201cb402058002489048100e020580024091481022070102c00127382408070102c0012048580807168081600090242e04038b4040b000481255
|36=>0x2408070102c0012048100e0205800249e048100e020580024090b0100e020580024090201c040f0580024090201c040b00048a61e048100e020580024090b0100e020580024530e83408070102c00125f02408070102c0012068240811038081600
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x930031800cc0006
|6,0=>0x5d1c2dae16670afb8561c2a2e14a70a1b84f1c26ae12e7093b8481c232e1127085b8411c1fae0f67077b83a1c1c2e0da7069b8331c18cc0bf705c382c5c154e0a3704e38255c11ce0877040381e5c0e6c06c7032b8179c0aee0507024b8109c076e0347016b8099c03ee0187
|7,0=>0x1b440d8206b1035081a440d0206710330819440c820632e3118184c0c0605f302f18174c0b89c5b8c2d4816640b12057902b57156c0a96053b02958146c0a1604fb027671374099a04bd02586128409220484c23a8119408aa0445021a81094082a040501fa80f9407aa03c501da80e94072a0386e1bb80d9c06ae0347019b80c9c062e0307017b8
|7,1=>0x2af4155a0a9d0546829f414da0a5d05277290394620a2105097281393ea09e504ea82714136a09a504ca8261412ea096504aa82514126a0925048a8241411ea08e5046a8231b916e08a7044b8221c10ee0867042b8211c106e0827040b8201c0fee07e703eb81f1c0f6e07a703cd61e2c0ef6076ce3ae81d340e7a072ee38f81c438e0206f103708
|7,2=>0x3a9c1d2e0e87073b839a39cb20e4ae71d838ac1c360e0b06fd837ac1bb60dcb06dd836ac1b360d8ce6be835b41aba0d4d069e834b41a3a0d0d067e833b419ba0ccd065f732bc193e0c8f063f831bc18be0c4f061f830c398420c11060082fc417c5cbd305e182ecc17460b9305c272dd416cdcb5705a382cdc1651cb19058482be415d20adae5667
|7,3=>0x11ff08f78477c239e11bf08d78467c231e117f08b78457c229e113f08978447c221e10ff08778437c21a1d0c10858842842122108108388418420a210410818840842022100107f973f939faa0fc507da83e941f2a0f8507ba83d9b9eae0f47079b83c9c1e2e0f07077b83b9c1dae0ec7075b8
|8,0=>0x588c2c225602eaf985784aba215bf2ad6956742b16557b0ab58556c2a9255372a92954542a0dd4f52a737535c2991d4b72a538525c290e14752a3195144a87e542f0a0e9503427fa13eb29ed84f24a77213a729cb84e1c26ee136709aa94d1426665323098984c0c25e612e3096984b0c256612a3094a74a1424e65264e92994904a462122109079
|8,1=>0x694c34825a2f2d0f86843b3fe59ef0cef8673c337e19ad2ccd9662c32f259672cab8651c326a59250c8996404b1de58df0c67862fc315e189d2c46861fbb0de185d2c25960ec3056181b0c0495fe42fd217d90be395ed4af4657930bc185dc4aec217510b9f95cbc2e3e170f0b7f85bb4adba16cb2b5c95aa42d2e56870b3b8599c2caa56450b199
|8,2=>0x7a14bce65e64ef2a879143c665e212f07977f4bbda1ddb2ee4976e43b4e5d952ec1975cc3ac61d530ea1874cc3a425d110e7f973bc39be1ccd2e5d972ac39361c8b0e3c971a438ae5c452e1997084b81e5bfd2df686f6cb7961bbb0dd496e5cb70e1b770db386d5c368e1b370d9386c5c360a5af50d7286b54358a1ab50d5196a4c35061a712d317
|8,3=>0x84acc2326107307b8839c41ae20c7105b8829c412a6085103998184c09e603d301598064c00e5ff52ff197f44bf821fb10fcf97e34befa1f6d0faf77d3c3e7e1f2f0f8f87c3c3dfe1eed2f6d97b24bd6e5ea70f4b8
|9,0=>0x4886243132108904447fe63ef11ef88f3c477e23ad31ce88e3446fa236b31ad88d2c46726329118b98c14c5ea22e5116998b0c456262a11147989fc44de225f1126988ecc45622193103987d4c3ca21d510e2886ccc342619110c0885bcc2be214d309e8
|10,0=>0x12497920c48e6246312298
|11,0=>0x12507
|_,_=>0
def wAt:=mkWire dB 263 255 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 9 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x202d2a00b0e94d0584a0482d0c00b0e84900025058011c8671884904801058010109d1884805801110250004921801059090e84a048011883605835048490c88a04889000490003d038690c848058250584901809048e10b0480381103849198490c84b0582503849048a9148480a81d000a90a849148480a81d1202d020010207d0f048058490e82d038690c8480582506801048490b8030a8490381101011
|1=>0x101d02009049b1088480101d010490382503849048490584904941058490e9090e84a000250b1a90b04a038110c00b05835048490781d058493301d0b0b60201d010490780119003078250584914848010490b0090c00b0e8490100d0384904001020490202d058490004901001011790204a038550116d0a84a010110005e168110104900049001650c88b0482d000491c81307801058492b811038492a801
|2=>0x482d05849058a9148480a81d110640482d0004905849048a9148480b0090381101049001f50a84802009010492e81101001000493d049188370002d048490f048000490e82d000250c00b0e84900025058010c84b0482d0007d0f048188250201d02049000ca06801048491101101089000490003d0584901813058490581d038491901f05835048490a803000b6000e10b0480201d020490c84a0b8030a849
|3=>0x110110100100049020490182f078031102f0780105849078770002505849048493482f01811038490100e0384903825048491884904009020490100100049038ca0782505849048b51b0271681d010492000118836048492481304009020490402f0204905849438132a8890581104a19002151884a0682d048490aa11020090384a038ca03835048490200d038490104a000490e80b0002505835048490c81f
|4=>0x4849022690396d0a84a03821010210204908811022490884a0101d0c84900025058250002d4a8130e83d048010207d0f04818825058010b0090201d1901f07825012560f0490e82d1901f07825058490201d05822078250584903a490884a088110101d08820038090202d0401d058490204900035188340002d048490a81d01011000b6000b50104914820020490a81d00049059b103849088480101d01049
|5=>0x3809018540101102049038490e83c058490002d04801048490104a0e80b000250404703809010490204907813188130002d000490204911025010490100100049050030c00b0e84902049078010202d058490e849000250387d0f0480e82d0108900049020b5010490c8490427d088230380902049048da16811010490a80c0200d020090384901049000490484916811010494d81f148490a81d0002518834
|6=>0x4a71010250004a3401f0182d03849048490c00b110250004901011088200204902045038090383e03849058492a8010004905811020491901f05849048010c8880582500049002b10f04a188250e9090e84a000251b01f088490e80b000250884a048d23b801048491c87718849000254d82f1681101049010110004901049020490203e05849000490782505849188360583504849021990b0b60201d08849
|7=>0x494c82f0b2010381104ae1168270104907825058495b8033a01101089000490c00b06801148480201d020494a813188350002d3f849058254a84b0f049000250c00b0c003110250004904001020491484801049010110002d078134d80314849088110396a0a84a039c11901f078250582203849022710004a0a8030200918825058010eab10f04a048014a81f190010782505849038360383e0484901049
|8=>0x400906801048490180903849020063482f0b04939009038490e849048014d8131484908811348133482f0204905835048490e84b000250214d0584a0b02f03811000490f04805801018e30b0480384903821020490682d0484939009348130b04900036058490c00b068010104904849010620e84900025058014a8030f0490e82d048010884a0101d001c11901f07825058490e84a00025020492e81101001
|9=>0x48491102500049048da01809038490494105849148b4010490a81d010110031d048495b8032f809000210480d0384916811010490584911025000490884a0201d0101d020090c84900025058250002d048da018090484a0c84b00025058250002d06809048494a80b0f0490c8010482d0484903849010490b009038114a84b0c8890582500049020490180b04001020492e8250104901001000490a0480b803
|10=>0x67013012710004a0e84804801048491102f05849000490e83e0584903849088480101d001b50494d0584a0b0b503811010490108a000490104965003022010104a0f0481882505801039e10b8130a8490005e020b6168110a849148480a81d0c848058250680104849040090b0480201d020490c00b0c02d110250004911025000494d84b0b81d168114d813148490b0090201d168110104906801048490682d
|11=>0x680106803048490401d020490584a01825038490584915811000b601049058110383d058490004900022020490200e03849048b60104902351002010104a0484a0581d038490384908813038090100d010110384902352002010104a0588911025000490382d039790204a058b100022020490e84904801058250b049038090201d398250382d0584967849088130101d038490b00903811058110381103849
|12=>0x5b0d0484a0484a0882703809078250382d058491901f07825058490b80104009020490e84a0002d04801039e1020b601049039f70a848010110200902049000490104901025048496b80305821020490389d188480002d0380902049010490c02f11025000490781f03849058492e8250000901049018090481d038491484b0b0090201d0f04a18825190030682d048490580105821020491681d0104904849
|13=>0xb803168110104903979038090204a0884a038090201d058110780105849058b200022020491b0241681d01049048490e80b048010584905811020497380904a110384a048b601049038490401d0584902049000b50104904b2d0108a000490480d03849001f70a84801011048010480901049018110580e038490b80016811010490b0b40381101049049310588a000490480106803048490480e0384900376
|14=>0x49058010004904849001dd0682f048490022e0203e0584903979058490204a020b50004a010490ca730482d0004a148490b0090201d0384901025048490c00311025000490182d0481d038491b0271681d010490480104a010104a408490e80b000250201d0203d058490014d048010584a038b61681d01049048890582500049038490101d0484a0b80b0a849010110104a02001000490002d0202d00049
|15=>0x2049000490204900049058490201d0100e038490c88805825000491b0130884903809010490a81d0101106803048490104a020b60004a0104906801010490484905ac603822020490e8490002d048010482d0383604849038350484905849013c91204a020010781f0482d058490584904801058251184a1202d02001188490002d04801778110884b038090201d0101d020090482d0481d0384904b2d0108a
|16=>0x482d05849012490884a0101d011a90b04a0201d1681f0480901049013d50208a000491b0241681d010490e94d048010584a038490101d0200908823038090484a1681f01049059090e84a00025068010682f048490b80016811010490402f0201d020490b0090201d020490aa11020090384a0200d0202d03849038690c84805825010111681f010490681f048490c00b1102500049000690c848058251102f
|17=>0x22710004a0780102001058491900307825058490a84b0201d01011348130b04911025000490c8490c801058250004905811020492a80d0202d0384903811058490204904a11010250384a07801058490204a0132d0108a000491c813188490002d0884a088110101d0382202049010491b0271681d010490202d05a110384a0781d0482d0584900009001790204a023e53984a0581d0124d000360484907803
|18=>0x49048490101d0480e038490a96d0a84a010111681100011010490481d0104904849188110580105849340250383d058497382d04a110384a0a84b010110101d01049048490b00b038110384958009022710004a0e83e04801058490480e0384903849088110101d188370002d048490102500049048490c0030e849048010480100049048497501d0400b020490583500036048496b80105821020495802f
|19=>0x58010480104849010e10b0480201d05801058490204a0101100049010494784a18827058010b80304009020490101d048b601049068030482d0484903821020490104919001078250584914849088110101d04009020490004904a1a0014d0584a011090e84a000250580102089000490681d01035048493482f018110384904a71010250004a0c84b058250002d088220380902049020490180b0384901035
|20=>0x201d0495d0180b038491484b0b0090201d078270382d058490383e0383d058494481d01035048493f84a0c81f058250100d0480d03849058490e82d048010681d0682d04849040090201d02049148490b0090201d0781105801058490580111025000490680903809048490488a05849000493482f0b0490201d058490b04a0201d0383e038490584911009020490004904809010490384904801002010104a
|21=>0x58010108a00049038250101d048b5010490101d0200902001058490384a058493082d038251102f000490004905849000110584a3984a0581d0884a0101d0488a00049048490104903849048490101d04809020490584a0202d0004a06803048490203e058490488a000490202d038490480e03849020090384a088130101d0e82d000250f0480e82d000250f04b0e82d000251484a0b0090201d148480b009
|22=>0x10250201d058490584a0e82d000250201d0584a04801048490e84b000250101d048490e84a0002503a010104a0382504849012710004a05822020490201d0384916811010490e80b000250e84900025011790204a048b501049088110101d04a110384a03811010491681101049058110204918848
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x6ea0cd000000000000000000002e50000000015202730000090c0000000000000000000000000007d40d2800002e604d0000000000000000000000001e8000000000d20000000004a0000008a00100000000
|7,0=>0x1ba6368c6b98d431a2633c86618c9318e4000061a0c1200002fc85f08bb316e82cd057a0ab414e800000000a3413e827484d1898212a6248c48108c411260000439083410421f903d207640e841c4c37186b30d24000032a0623000018442f185c20b441590292000009c800002520464086610481f903c3
|7,1=>0x312861c8000184330265fc8bda17742e685bd0b6916a32cc858ccafa15d22b465608ab115512a28538ca52147300005148000142327e64f0c9c9935426284b8c952128224c448cc90191e2238400008c211622248439000010c22126418c82890141fa83ec87c90f721e683c0c7620eb11ce8390c7020000
|7,2=>0x8b8d16122a244c888cd101a1e24384864d0b9213441e882d1049205440647fd0fe19f933ee47cd00001f123dc67accf491e633c487808ee980003b64760ceb100003a6600000001d1239a872c8e419c4438266f50dca1b6336666c48d719aa435046910d0999e333846688cc899633266640c00018d3
|7,3=>0x1501a9d30000a68d4b2292451c8a309449a8540000a0c940900004fe49f493d1a78200009d1139126f34da49ac935080004d0499113020000000000012e9a594000095c929a250349c49291241246248488fcd1e923b200008e0c000000046c400011a12313
|8,0=>0x6b46d609aa9b52369e6d30da49b4636866d0499f1b3b36706cd4d991b2f36586ca4d931b2336406c74d8d1b1736286c44d871b0b36124c18d819b0035fa6be8d7b9af435e26bb8d7612ea25ce6b90d709ade35b66b60d6a9ad2359e6b30d649ac635866b00d5e9aba356e6ad49591aaf35586aa4d531aa33
|8,1=>0x8307054e091c0f38187024e03940438026ff8dfd9bf837ea6fc8df79bec37d26f98df19be037ba6f68deb9bd437a26f38de59bc8378a6f08ddf9bbc37726ed8dd99bb0375a6ea8dd39ba437426e78dcd9b98372a6e48dc79b8c37126e18dc19b8036fa6de8dbb9b7436e26db8db59b6836ca6d88daf9b5d2
|8,2=>0x9a67340e669cca398e7310e609cbe397672e0e5a9cb2395e72b0e549ca729487284e4f1c9b39325258e499c90391a7228e439c84390271f8e3d9c7838ea71cca38946e38d671a0e329c6238be7170e2c9c5638a67140e269c4a388e7110e209c3e387670e0e1a9c32385e70b0e149c2728487084e0f1c1b3
|8,3=>0xa965520ea29d423a7e74f0e9c9d363a6674c0e969d2a3a4e7490e909d1e3a367460e8a9d123a1e7430e849d063a067400e7e9cfa39ee73d0e789cee39d673a0e729ce239be7370e6c9cd63
|9,0=>0x16a4ad395a52b465684acf959d2b365664acb95952b265644ac7958d2b165624ac395852b065604abf957d2af655e4abb95752ae655c4ab7956d2ad655a4ab395652ac65584aaf955d2ab65564aab95552aa65544aa7954d2
|10,0=>0xb5c36b46d60dab1
|_,_=>0
def PO:=mkPO wAt oP oO 20 9 511 15
def pmP:Nat→Nat
|0=>0x4000000000048000000000868000000010900000000210000000004180000000081000000000a0000000001160000000020c00000000410000000008100000000100000000001200000000020800000000400000000004800000000084000000001000000000010000000000180000000002c00000000050000000000900000000010000000000180000000002800000000040000000000600000000008000000000080000000000
|1=>0x300000000003eec00000007d780000000f9500000001e5e00000003c4000000006f780000000ca000000001900000000030ac000000061000000000c00000000011000000000208000000004000000000062400000000900000000010800000000208000000004020000000080000000000e3c00000001c6800000003840000000064800000000c800000000183000000003040000000050600000000880000000010580000000202
|2=>0x1009020000020104000000402000000008032400000100048000001820880000020400000000403ae00000080310000000c008000000104100000002002800000029f5e00000053eac00000082100000000c209000000184000000003001c000000479780000008eaf0000001100000000020e3c0000004084800000047ac0000000875c000000106b800000018008000000300000000005f5e000000080040000000fd780000001ba6
|3=>0x64008120000c80100000018007d780003000409000060000820000c000004000100a284000020104a0000040008000000800010000009000208000101042000002001f5e000040010a000008002048000100000100001800e7e00002003ebc00004006100000080009000000701f0a00000e03c1400001c060080000200c9100000203f5e0000040020000000407df80000080faf00000101f5600000203e90000004079f80000080f27
|4=>0x14401e9a000280000000004900386800092004090001040000000020021cbc00040025978000800400100010001f5e00020001c1800040001058000800000000008060658000100c00a8000200a785000040143080000802075c00010023c3c000200408580004004fae00008009e5e00010003ebc00020007c500004000f2f00008001e5600010002cbc00020000100000400000f0000800001a00010000024000200000400004000000
|5=>0x10202004000200001080002808034680043000f2f00084400c1000104003ebc00204007ca80040200faf00080001f4e00100003e140020000450000400008000008000004000070000000000d00079680018000b2f000280100000004800102000088002000001030068500020401f5e0004001100400080010400001000180200020001f5e00040003e1400060047978000c00870d000180101160003002002400060005978000c00000f
|6=>0x80100054001000083ebc020000a6d780400010faf00800009f5e0100000400802000007d780400000c800080000154c010000016b00100030400002000208a200400000004007000012a000c00082140010400000000202020f58004040412a000808080040010100072000200060154004000c00a0008001801000100014f2f00200021f5e00400041cb0008000800100100000f2f0020000080000400000a080070000597800c0000faf
|7=>0x200400001004004043cbc080080821401001010420020020008500400200208008000007d781000000fa402000001e5e04000003480080000065001000000c20020000012000400000208008000003d60100000002001001001b5e02000422c1c04000844018080010380101000205e5e0200040200c0400000c1100800001803010000000440180200208803000006978050002002c00a00021b5e012000038bc020100021400400800faf
|8=>0x50002110040a000023c9c140000004182050000f850408000180208040022e9c100048079782000280f0f04000401f5e08000803044100008140102000100faf04000201e5e08000403c9c10000806d7820001004100400001770e0800002ce1410000007d78140200072f0280002044805000003cbc0a0000000001180000f2f02104001e5e04200043ebc08400083d681080000eaf02100000d4e0420000002008210003d701003010028
|9=>0x20000000c40400000002088000000010100000000001020808075c20410100e30408200859708004004f0a10008001f5e20010003eac40000180100800003000810000009f5e20000000200300010070206000200c0008084000f1a10040c0003420080807d78400a000f6f08014000f9a1002000100020040000000400220000908001101e1e10000803cb42000100386840000044c9080000088001000000204014004007d78280010a104
|10=>0x400000c1e5e80000106e9900000107d7a0000020fab40000009f5e8000001001900000007d7a0000000f8f4000000174c8000000002c88000407d211000080f2f2200010180044000202080880004021011000000f2f22000001e4e440000032808400010c1110800020b0620800001e5e410000036bc82000000001020080092d2040004260040800082e9c81000006d790040000c0020000101e5c40000003ebc80000006d790000000822
|11=>0x200000007d7a2800000b874102000050e820001808a9040001015320800000faf41000001d5e8004000a00d0008000757a000800000440010000006800100400a9000200800520004000fae40008001e5e8001000000100004805d120000800faf
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x200c00000000007020000000000000b000003802000040000000000000000643c00100340000000000000068000013000400e00030b80000
|7,0=>0x541dc0002068c46e8d610bc03204981dda01038c404b21207c68ca0034c000d0183c60184b00428139481c046c1580066313482400132c83528c1748accc3f0a83598afa64a8a200008ac5a0202808047000d88af230004d000d0b0e1ca3304001362907008020d008c83731010001a6f400d1c47f568141e1f910005c01001d8568179ba0800017801ce0325acc2607
|7,1=>0x1b3d000340c22121581a2ea48ac1a0010325fe2b000dc1a3108b688800b43d12a008480056a4000084cbe0980c56459d0c40acd000ac00005a0000a0d001749e011781c740d100ac0e5404020621a0086030c33f15400d00681c5601049085600548341a003a80000310c04c082c009615c851704c250e4f280020d784ca78980087c0147
|8,0=>0x93d45be6a1cb60f2871edc1d4b54b8e2a6466ba48dc83921e87ab1508f492f7aa27ecc1745a9e38e61e8ed9f65943ed188a8b562168480d22bd1ea02dde51f373f11f116db84d734b1afc77398d8f46b5648acd4ef14ea71aa82850eda8c789dc47088564ee014e0082a24fd482e4f94b9858566e4b04bdf0f6ac8756d194318256f7aac61b333b781d815a2e5b4dc4a
|8,1=>0x98a9463d1eaf07725974087a72511c67e288aa0da3672f8f17a5a675911c3e8d5187b4186264b62513cfab23d761d0c6474d3d688c5695169a78879ed542b82989c03d5dd489acb9c224da50759b9dc21a197a6a238ec40d048b55b898337d3e54d26ab8f590b0818b98d5f7f56e9e316b0f49c3b
|9,0=>0x294cb379bc187aba3eb71de65a12226cde63d50a664a5450876b83b8ea06796cb2d969208f6095c6e9ce112186949575d8bae284f7
|10,0=>0x36621847a3d
|11,0=>0x3b
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 43 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_252 9 roots_252 ops++addP pm 1 dom_190 9 roots_190 ops++addP pm 2 dom_248 8 roots_248 ops++addP pm 3 dom_222 9 roots_222 ops++addP pm 4 dom_228 5 roots_228 ops++addP pm 5 dom_250 9 roots_250 ops++addP pm 6 dom_212 5 roots_212 ops++addP pm 7 dom_126 8 roots_126 ops++addP pm 8 dom_206 8 roots_206 ops++addP pm 9 dom_182 8 roots_182 ops++addP pm 10 dom_246 9 roots_246 ops++addP pm 11 dom_238 9 roots_238 ops++addP pm 12 dom_174 7 roots_174 ops++addP pm 13 dom_172 5 roots_172 ops++addP pm 14 dom_94 5 roots_94 ops++addP pm 15 dom_188 6 roots_188 ops++addP pm 16 dom_90 4 roots_90 ops++addP pm 17 dom_58 4 roots_58 ops++addP pm 18 dom_186 7 roots_186 ops++addP pm 19 dom_230 6 roots_230 ops++addP pm 20 dom_108 4 roots_108 ops++addP pm 21 dom_116 4 roots_116 ops++addP pm 22 dom_166 5 roots_166 ops++addP pm 23 dom_110 5 roots_110 ops++addP pm 24 dom_86 4 roots_86 ops++addP pm 25 dom_214 7 roots_214 ops++addP pm 26 dom_158 6 roots_158 ops++addP pm 27 dom_220 6 roots_220 ops++addP pm 28 dom_124 5 roots_124 ops++addP pm 29 dom_240 5 roots_240 ops++addP pm 30 dom_118 5 roots_118 ops++addP pm 31 dom_210 5 roots_210 ops++addP pm 32 dom_218 7 roots_218 ops++addP pm 33 dom_170 5 roots_170 ops++addP pm 34 dom_122 5 roots_122 ops++addP pm 35 dom_46 4 roots_46 ops++addP pm 36 dom_242 6 roots_242 ops++addP pm 37 dom_236 7 roots_236 ops++addP pm 38 dom_244 7 roots_244 ops++addP pm 39 dom_154 5 roots_154 ops++addP pm 40 dom_234 6 roots_234 ops++addP pm 41 dom_62 5 roots_62 ops++addP pm 42 dom_180 5 roots_180 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_254 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_228 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_212 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_238 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_174 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_172 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_188 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_108 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_166 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_240 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_46 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_180 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_252 9 s (0,roots_252.map (·&&&dom_252)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_254 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_252 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_254==dom_254)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_254 gM v ys):RunD true dom_254 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_254 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 4 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 51 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 51 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 246 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 118 128 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 246 → Z 7 i = true := (range_split z7_0 z7_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 232 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 104 128 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 232 → Z 8 i = true := (range_split z8_0 z8_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 47 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 47 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 5 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_254 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
  · exact z7 i (Nat.zero_le i) hi
  · exact z8 i (Nat.zero_le i) hi
  · exact z9 i (Nat.zero_le i) hi
  · exact z10 i (Nat.zero_le i) hi
  · exact z11 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 6 6=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤11) (h:RunD true dom_254 gM s xsM):False:=by
  have hmin:6≤s:=by have hl:=run_len h;change 7≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_254 roots_254 goal_254 12:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_254
theorem lowS_254:Lower true dom_254 roots_254 goal_254 12:=S_254.noCircuit
def isoMvS_223:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_223:Lower true dom_223 roots_223 goal_223 11:=lower_iso_b isoMvS_223 (by decide +kernel) lowS_191
def isoMvS_239:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_239:Lower true dom_239 roots_239 goal_239 11:=lower_iso_b isoMvS_239 (by decide +kernel) lowS_191
def isoMvS_247:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_247:Lower true dom_247 roots_247 goal_247 11:=lower_iso_b isoMvS_247 (by decide +kernel) lowS_191
def isoMvS_253:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_253:Lower true dom_253 roots_253 goal_253 12:=lower_iso_b isoMvS_253 (by decide +kernel) lowS_251
namespace S_255
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(1,129),(2,10),(2,18),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(4,36),(4,68),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(6,14),(6,22),(6,38),(6,70),(6,134),(7,15),(7,23),(7,39),(7,71),(7,135),(8,9),(8,10),(8,40),(8,136),(12,13),(12,14),(12,44),(12,76),(12,140),(16,17),(16,18),(16,80),(16,144),(20,21),(20,22),(20,52),(20,84),(20,148),(24,25),(24,26),(24,56),(24,88),(24,152),(28,29),(28,30),(28,60),(28,92),(28,156),(32,33),(32,36),(32,40),(32,160),(34,35),(34,38),(34,42),(34,50),(34,162),(48,49),(48,50),(48,52),(48,56),(48,112),(48,176),(64,65),(64,68),(64,80),(64,192),(66,67),(66,70),(66,74),(66,82),(66,194),(72,73),(72,74),(72,76),(72,88),(72,104),(72,200),(96,97),(96,100),(96,104),(96,112),(96,224),(98,99),(98,102),(98,106),(98,114),(98,226),(128,129),(128,130),(128,132),(128,136),(128,144),(128,160),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffffffffffffffffffff
def xsM:=roots_255.map (·&&&dom_255)
def gM:=goal_255&&&dom_255
def NN:Nat→Nat
|5=>2
|6=>14
|7=>159
|8=>685
|9=>733
|10=>262
|11=>46
|12=>5
|13=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0x89efd1ff9a
|6,0=>0x84c0373e916b7dc56697212a11c9f91a02717fea16d270f0d90f0720a9690214602101
|7,0=>0x6117e60ead605695fbf85e0535dcbd5c3c15a2bb59f6559f1559a55594ab58ea358b80576a8575eb566975578a552a85260f513a950d4a4e2d54d80e4a889491eb47bbe4770b46ec146a20455ba41efe409d13fa9b3fa8d3de7e3c4ca3a83338f8c38d363771c3740136d983691c3628c3607335c26358693519a34cf4347f0346f82f8492eb5a2e7b42e6b92d2e12ad802acd4286cc23c19223122227c22224216a42151b2112120db320cce2086a2046d200f01d55d1d36a1c9f91b7731b34d1aca71a94e1a4aa199f418e6a17fea1719c16d27141ad13e8e1319d125c7117e310dd610bb61007e0f9070f7860f3050f2a60c6930c3db0b8990b3990b1040981a0919108fc008ea608c73084c5083fd075360740706def068710603905de6058d1056760439f03f8502ffc02dfa02abc01c7401c52015c400fb70080300507
|7,1=>0xff804e0e4ed1412c0817b5a53b11f9af4ebaeca79b86b88d498899383a3d7ce037be847be3a7b0797856477754762be74fe772a2d7194270b746e15e6bd8a694746657a6475d640796328262f8b
|8,0=>0x1076a10447102f4100a00f7f90f7070f4230ee770eb230e94d0e7880e59e0e40e0e1e90e08a0e0470dc990dbc70d6d80d65c0d5110d3420d2f40cf540cf130cb940caaa0c8310c5b80c3ba0c2830c1910c0b90beee0ba710b8c80b8990b1a30b19a0b1040ad530ab780ab1f0a90b0a3a20a3320a2990a1c50a03b09fb209a1509738096e20930d091c709141089c0087d4087670820907d990771007568074c20736d073390726f06fb206f420685b067f4066f2066470647c063310612605fc405e5805de605bb505a750590e057c9056a10526a050c60505c04fb904eee04bee04bb404ac0048e104435041f103f3703e8003c7c034ec030a802c0502ab1028b4027cb0272902662022010215f01f0501e6a01bb001b4d01ae0018ad01769016c801699014a000e5b00c6200b1800ab200a5700a0f005ec00316002bf0012e
|8,1=>0x21a1a2170321656212a52108920e2420c1b20c1920b2d201af1febe1fbd71fa8e1f9f21f99e1f6961f6301f1cd1f1af1f15d1edb21ecd21e7ad1e7311e5f51e3011e20e1e1861d8d01d5dc1d2681ce6d1cc5b1c7531c60b1c6071c2ad1c1c71bad21ba491b2571af971ae5b1ac741ab491a9f41a97d1a06419a0a19942198be1970219246190bd190a918d9118a45187ed1876f1870e1863e183b6183a91839717e0e17abd175c11748b172721719c16fdf16fbe16bf716bbf16ba316ac21698b1688e167691674a1622715f9d15ee815d4e156981523b14ed514d9914d5414c29147f514610143fe1415613e2c13d6b13d6113b651399113944138ac1389d134761334012ecd12e5f12c2012beb12b2f12b00126a9125f41257f1249f122e91215a11f2211d6911c11117471156b1108a10fe410dd610dbf10dbd10bb610aa4
|8,2=>0x33ecf33c1a33b5d338bb332d732f8132b8332ac6328f2326983212f31fe831e8031ca831ca531b9731b3331703315553121130bc830b97308a7303ca303ac30372301c92fb392fb312fa332f9a32f98a2f8fd2f7af2ea942ea862e4b72e0602df972de252dd582dd282dc172db582d49c2cd0c2cbf42cb252cb132ca372c6532c3ba2c29d2be6c2be442be002bc582bad12b8582b7de2b6f02b6d52b5d12b1ac2b0982b0492ab922a9c62a6292a5542a51f2a17b2a15329e1329d6229c7e29c4629b3f29710296ef296a32961f295772923d2906828eb028ea128bcd2872d28374276e226af82681d2674d265ff2618425e2625c5b25b4b257c2257ac2563d25358252032510a24a7f24a79247632428e2422f241e024135240a123ea323e9d23c9a238a623406232bd22df022d9922701226552254a225062231221c9121aef
|8,3=>0x5225e51f0751e8d51cbc5129750ffa50d5250b3b509c9506e15055b504234fda14fc764fbc94f81e4f6c94f6ab4efe24edec4eb384e8954e43e4e0534d92f4d3214d0094c3804ba224b3e74b08b4a9d24a9c74a6464a44c4a3314991c4925b48f6a47ed047c7d466b7465bc464754607045f0345efe45a2945a0a4584a457d9455ba451794507d44ffe44f7f44b4e44753444aa443b6442214402943ee942d1642cd84295b4291a424ce423654216f41bc841b7b41a2840cea407c14076d4025a3fbf03fbef3fa9b3fa5a3f6ed3f5bc3e6a43de373dbea3d0a83cf323c8ba3c7d23bc9c3b7b63b3f93b32c3b1223af5b3ab843aaf13aa843a8163a2f13a2e339ff339cc0395053909c38e3138c16387373870b38210380a13795a37401372ce3729b36e82366c935c4b359b1358b834d2034b5734a6034a083452e343e334398
|8,4=>0x8a7a28a70189b7688fd98871f86400863c785f0e857978485c84303826a381df5812c280ea580712806627ff377fa027f8247f2ec7ee8b7ecba7c9587c8d57c7b17b15a7b0797ab587a2bf7a1a179ed779da17990f794c978c3a779c4774c07623475e4275d8d75c8a75b00752a374fe774fce7483e744917437c71b646f0286ec9d6eaeb6e9916e15f6e15e6d31a6d1de6d06b6cbd06b59469b0c69ada6920c68dbb6896b67fef66db266976668976687c66306658cd657c3654d2650b364ae0647ec63f8a63dd0639b7636126313f6282f619a26146b60f485f8885f6ff5eb2f5e9485e7735e05e5dcf55da115d8515d7925d1a95c5d05c3c15c15d5b8be5b4bd5adf15acc25a3745a1515a116599fe59666595df58f9b587b8583355719756f90568e05571d5569054a7a54a72549f054597540075393e538ee532de527b0
|8,5=>0xff2e9eaa93dae83d5165d0afbc869dc29cbc0893b9bd8b6de4b6197b512fb502cb4c39b1752b1393aeb3aacf58acd4eac493ac3f2ab7f6ab6baa9b9fa38c0a3147a25c9a09b9a0598a05029f86f9e21a9cb8d9c9f79c2d19abfb96ffb95c3295a889349e919db8ceb88bf478ba218b298
|9,0=>0xb4060b27b0b1a30b19a0b1690ae240ae1a0ab460aa940aa7e0aa650a9690a6510a3eb0a1c509fc309eb909a85096490960e095f309533094e4093da093b60917608c9708ace087ee087e7087db085c90851a084b8081c80801307872077dd076ee0736d072df071950712b0706606fc806e5c06d8306c8106a360687c0674e066ae064a5061aa0616705fdf05e1c05d3105c2605b5705aa205944058f00578c05686056260527504cb404b4704ac004843048240473004546044bb03ec603dee03ba303ae403a140388d0387303800036610364503306030b202eb0029fb02943027fc02586025280244602299020f8020660203901b6101a8c019d101970017f8016140132101135010890100100f9600f7900f4a00f2100ed100ea600ca400c6200c0900a03009dc008cc008650056e00541002d000279000e2000c40006c
|9,1=>0x1b9eb1b9e11b20f1b0321aacc1a8161a4741a1db19e0d19d6c19aea199b1198db1942f192f2191da18c281897d1881f1860c185bd183801814c180bb17f3f17c5d1789c17728172521707216f3016dfa16c7816765166941667e1610b160cc15fbe15eee15e9015898153a4152941510a150e514c291429b1429a141561409713f2d13e8c13e4113dfe13d62135e8133eb132ae132a913225130f312e8912b31126761255d1231012268121d4120f511fb511c61116a910dd110b2e109e9109e810775106541031f101d8100e60feaf0fdc30fcdd0fc2b0f7f80f3740f35d0ef260edd20ecdb0ebc70e9cc0e8ca0e5d70e59e0e4570e3890e3440e2870de2b0dd9b0dcba0dc8a0dc0a0dc080dbc70d9160d5570cf770ce220cc490c9ff0c85e0c6820c5510c5490c4c30c4930c3fb0c13f0bf9a0bd880b64f0b5410b4fa0b4c5
|9,2=>0x2fd9f2fc952fbfc2fad32f7242eb9a2e8b92e7982e6292e24b2e1d22e1c02db7d2db582d9c92cf6c2cb9b2cb252c8e52c8c92c7662c1052baf32baad2b86b2b7de2b66f2b2102ac742a51f2a4372a3ed2a05e29f8a29de229d3a29c7929b3f29a8f299882962e291d428e65283cd281e1280c527e9f2731a270f326f5e26a522698e2680025e57259c525668254fe254b12517624a53249a32494a2470f243a224204241352404023a7523867236f52352e23527233d8232f3232bd2317322e3f227482243d21e65216ed216e2212de2119b20e76209de209cf205fb201af2019c201391fc3a1fb3c1f9ae1f99e1f4951f2501f1ed1f0dc1f0b31efc01e8401e1181deb01dd511d9341d8d01d5f61d57d1d5381d4a11d3bb1cfd61cec91ce6d1cd991cb5e1c9531c92c1c8091c8031c4981c4701c4551c30c1c09c1bf911bdf4
|9,3=>0x4a44c4a3c04a37a4a19149bbf49bae496c04919e48e5748d6c4885a4834647ccb4783d46cf846cce46be64654145bc5453ca44a6a44a6443afd4317f427ce4261f424f8424f24229e41f3b417e5415f54105940de84050a401573fd0e3fb963fb233fa273f9793f5173f4eb3eb3b3e4393e4093d69c3d5bf3d0373cd773c8f03c8e73c7163c4ca3c13b3bf713bb5e3b6173b58b3b1bd3ab423a6203a4e33a07a39f93399a3390ba3882937fbf37e1a37db937b80379aa378c8374ab3712f36da436c6e36bf536be036752366773608d35fda35d173594a350d334d34349d83497c348ba346373407833b7633640330d032f4832e4932cb432aff32a8f3252f32336321ab321383212a320dd31fe831d7b31c8b31c8931bec31b0b31b04319ca314e53144a3141a313a4313933137a31298310f530cf630ad4306f23064430119
|9,4=>0x75b00752a37413b73bd473567734ce71c79714b57134a70d616f0286eb736e8a66d9d66d89c6d4686d06b6c9f66c9ed6b9186b5ac6acc86a3d269cea69019681ef6658965aef64fc164e6264ae0641fb63f0e6320362f81629a2628ee620fc61b8b616f760f356085c603ad600745feaf5fe695fc695f1015ecd35dcf55d5565d48e5d2a75d29b5cd7d5bc8b5ba7d5b3f55b18f5b0615ae9d5adae5ac595a7305a2b25a1165a02d59d0059a9759a515954f5951858e7c58acf58655585cd583355816b57eef5736956c6b56c1f56b1b566915608655c9a55c09557aa552b4551ba54c01549f05413d53d3053d1d5393e533f052e1950cdd4ffaf4fdce4fdc04fcf54f8bd4f6994f5fc4efe24ec264eb384e8954e8754df8a4dbfc4dbdd4dbb44d8b04d3214c3804c1df4bc8e4bb824bae84b2424b2344b14d4a9de4a9024a84f
|9,5=>0xff2e9e5be9e21e7d72b7d5151cd5cac9eb6c869dc636fc29cbbe44cb92f2b4252b1accaffe8aeb8dae122ad509ab856aa6a0a894ba511ea50efa3f56a0e51a0582a057d9fb4e9e5ac9df7c9c2059bf6f9b2989abcc9a47d9a02699c309971d993939845397bfb97aad96c799625095c3294a49949e391c2b8f5758d5788d4168be028a0d289880893cf8927788ffa88fed88d3b88acf883c28762686ac3861df8524f84fd88457f83a5e82688823bf810ff80655803f67fe747f88b7f1567f1277cb177c5f37b71a7b4057a43278fee787d3783f277ef677c657794d772c07658a7624d75e0475d58
|10,0=>0x2a432298b2289a227828269e3269e026713262fb2625c25df4257a024e202482824040237c12318422bf62153d210f020bfd206be204e2201e01fb831f7201f0b31eb421e9961e8cb1d3231d28d1ce6d1cd651cc0e1c9001c8091c6c01c2181b9c81b0a81a3a21a13e1938818f681841617de8179f817873176f616cdf16bcd1626116209159931576615732153c5153a414ecc14de914a4c148b3147fd14360142bc1422d13f8613e8613c3f137091348312fa512e3c12dfb12d8a12c8212b4e1216b114a610abc10a05101d10fa420ee520e94e0e82a0e5970e5320d85b0d6130d40d0d3310d2210cfdd0cf040cd9f0cbfc0c0d30bd840b9010b2c10a4ae0a1c50a0d50992f098c6096490940e091e809039086b9085a407d660687e067ac05f46054f9054a40519504b9f04ab103fb903af902f8b027f801c4101a8c0006f
|10,1=>0xbf9e4bb0c7b7b97b5f55b3f10b3cbeafc5ca8145a50ef9ddf49c9ec988689781894dcf923c39194e905bb8f5758b0d288ffa84e9184dff833d37e7737c5f37bbf27708c76d08765ce7412673de67390d6d6596d4186a6fd69ce6693d466529662ca644cd63bd36345f61de060dd35f7995d6e95d3f65ca165b7d55923f590c358b38585e1557aa5514d5461552e7c5242c52140517be50aa84fdc04f18a4f0ab4ea514e5644e0c34c1484b56a4a41b496214951b493844796347752476fe46d67460e745cdd456af4516e4504c44822433ef420324186b413e8404c73f1cf3eab83e3d23d95a3cecf3aa583a68f39e353981338fe138f10389c6388b1384b6379493776e372f136e30369f23667b35b14359d2354fd325ff3193931409308b52fc152e7ce2e1ac2db2d2d6372d0922bedb2bafb2af692ae042a9a82a9222a7d6
|10,2=>0xe21e7dcb47d78b6d6810caa05c3cda
|11,0=>0xfbad9e593ee18e8bfc46981ce9110b8f5758d79a8d62c89bd07d5fa7926e707655dbe95b6d05780d533c44a26048ebc46e364469e417bd39f3034ee731f8d2dfe320bfd209991b65b19d0a19629194cd1877017a23161b61473f129ea129d41278e11cad111c90a65c0a152098c609711060a9
|12,0=>0x9915892675416072573e1bd90
|13,0=>0x4d71c
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00fffffffafffffffafffffffafffffffafafafafafafafafafafafafafafafafaccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccffffffaaffffffaaffffffaaffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000ffffffff00000000ffffffff00000000fffafffa00000000fffafffaffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000fffffffffffffffffffffffffffffffafafafafafafafafafafafafafafafafaffffffffffffffffffffffffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00fffffffffffffffffffffffffafafafafafafafafafafafafafafafafafafafaffffffffffffffffffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000eeee0000eeeeffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000
|0,1=>0x1111115511111155111111551111111111111155111111551111115511111100ffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccccc1111111111111111111111111111111111111155111111551111115511111100ffffffffffffffffffffffffffffffffffffff00ffffff00ffffff0000000000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffffffffffffffff00000000ffffff00ffffff00ffffff0000000000ffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffffffffffffffffffffffffffffffffffffeeeeeeeeeeeeeeeeffffffeeffffffeeffffffeeffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee000000000000000000000000000000000000fafa0000fafa0000fafa0000fafaffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
|0,2=>0x3333333333333333333333333333333333333300333333003333330033333300000000000000000000000000000000003333330033333300333333003333330000ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff000000ff000000003333000033330000333300003333000033000000330000003300000033000000000000000000ffffffffffffffff0000000000000000ffffff00ffffff000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffffffffffffffffffffffffffffffffffffffffffffffff00ff00ff00ff0033333333333333333333333333333333333333333333330033333333333333003333333333333333333300003333333333333333333333333333000033333300ffffffffffffffffffffffffffffffffffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000011111111111111111111111111111111111111111111111111111111111111000505050505050505050505050505050505050505050505050505050505050500
|0,3=>0xffffffff00000000ffffffff00000000ffffff0000000000ffffff000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffffffffff000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f00ffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffffff0000000000000000000000000000000000ffffffffffffffffffffffffffffff00ffffffffffffffffffffffffffffff000f0f0f0f0f0f0f0f000f000f000f000f0f0f0f0f0f0f0f0f000f000f000f0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fffffff00f0f0f0f0f0f0f0f0f0f0f0f030303030f0f0f0f0f0f0f0f0f0f0f0f0303030033003300330033003333333333333333330033003300330033333333333333000f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f000000ffff0000ffff0000ffff000000000000ffff0000ffff0000ffff00000000ff00ffffff00ffffff00ffffff00ff00ff00ffffff00ffffff00ffffff00ff0000000000000000000000000000000000ffffff00ffffff00ffffff00ffffff0000330033003300330033003300330033003300000033000000330000003300000000ffff0000ffff0000ffff0000ffff0000ff000000ff000000ff000000ff00
|0,4=>0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000000000ffffffff00000000ffffffff00000000ffffffff00000000ffffff00ffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ff00ffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffff000f0f0f0f0f0f0f0f0f0f0f0f000f000f0f0f0f0f0f0f0f0f0f0f0f0f000f00003333000033333333333300003333333333330000333333003333000033333300ffffffff00000000ffffffffffffffffffffffff00000000ffffffff00000000000000000000000000000000ffffffff00000000000000000000000000000000ffffffffffff0000ffffffffffffffffffffffffffff0000ffffffffffff0000ffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffffffffffffffffff00ffffff00ffffffffffffffffffffff00ffffff003333000033333333333300003333333333330000333333333333000033333300cccccccccccccccccccccccc00000000ccccccffccccccffccccccff0000000000000000333333330000000033333333000000003333330000000000333333003300330033003300333333333333333333003300330033003333330033333300
|0,5=>0xf0f0f0f0f0f0f0f000f000f000f000f0f0f0f0f0f0f0f0f000f000f0000000000000f0f00000f0f0000000f0000000f00000f0f00000f0f0000000f00000000ffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff000000000000000000000000ffff0000ffff00000000000000000000ffff00000000ffffffffffffffffffffffffff00ff00ffffffffffffffffffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff003333333333333333333333003333333333333333333333333333330033333300ffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffff00ffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000ffffffff00000000ffffff0000000000ffffffff00000000ffffff000f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f0000000000000000000000000f0f0f0f00000f0f00000000000000000f0f0f0f00000000ffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000ffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00ff005555555555555555555555555555555555555555555555555555555555555500
|0,6=>0xffffffffffffffff0000000000000000ffffffffffff0000ffffffffffffff00ffffffffffffff00ffffffffffffff00ffffffffffffff0000000000ffffffff00000000ffffffff00000000ff00ff0000000000ff00ff0000000000ffffffff00000000ffffffff00ff00ffffffffff00ff00ffff00ff00000000000f0f0f0f000000000f0f0f0f000f000f0f0f0f0f000f000f0f000f003333333333333333333333333333333333333333333333333333333333333300fffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ffffffffffffffffffffffffffffff00ffffffff00000000ffffffff00000000000000000000000000000f0f00000f0f000000000000000000000f0f00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffff00ffffff00333333333333333333333333333333333333333333333333333333003333330000ff000000ff00ff00ff000000ff00ff00ff000000ff000000ff000000ff00000000000000000000000000000000000000fa00fa00fa00fa00fa00fa00fa00faffffff00ffffff00ffffff0000000000ffffff00ffffff00ffffff000000000000ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff00000000ffffffffffffff00ffffffffffffff00ffffffffffffff00ffffffff00000000
|0,7=>0xccccccffccccccffccccccffccccccccccccccffccccccffccccccffcccccccc00000000000000003333333333333333000000000000000033333300333333000000000000000000ffffffffffffffff0000000000000000ffffffff0000000000000000ffffffff00000000ffffffff00000000ffffffff0000000000000000ffffffffffffffff00000000ffffffffffffffffffffffff00000000ff00ff000000000000000000ffffffffffffffff0000ffff0000ffffffffffffffff00000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fffffff0000000000ff00ff0000000000ffffffff00000000ff00ff0000000000ffffff0000000000000000000000000000000000ffffffffffffffffffffffff00000000000000000000ffff000000000000ffff000000000000ffff000000000000ff0000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0000000000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000000000000000ffffff0000000000ffffff0000000000ffffff0000000000ffffff000000000000000000ffffff00ffffff000000000000000000ffffff00ffffff00000000000000000000000000ffffffff000000000000000000000000ffffff00ffff0000ffff0000ffff0000ffffffffffff0000ffff0000ff000000ff00ff00
|0,8=>0x3333333333333333333333333333333333333333330033003333333333333300ffffffffffffffffffffffffffffff00ffff0000ffff0000ffff0000ffff00000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff000000ff00000000ff000000ff000000ff000000ff00000000000000000000000000000000ffffffffffffffffffffffff000000ffffffffffffffffffffffffff00000000ffffffffffffffffffffffffffffff00ffffffffffffffff0000000000000000f0f0f0f0f0f0f0f0f0f0f0f0fffffff0f0f0f0f0f0f0f0f0f0f0f0f0fffffff000000000000000000000000000000000ffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000ffffff0000000000ffffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00ff0000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ffffffff0000ff00ffffffff000000000000ff00ff0000000000ff00ff00000000ffffff0000000000ffffff000000000000000000ffff0f0fffff0f0f0000000000000000ffff0f0fffff0000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffffffff000000ffffffffff000000ffffffffff00000000ffffffff00000000
|0,9=>0xffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000000000ff00ff00ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000ff00ffff00000000ff00ffff00000000ff00ffff00000000ff00ff00ffffffffffffffffffffffffccccccccccccccffccccccffccccccffcccccccc000f000f000f000f000f000f000f000f000f000f000f000f000f000f00000000ffffffffffffffffffffffff00000000000000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0fffffff0f0f0f0f0f0f0f0f0f0f0f0f0fffffff0033333300333333003333330033333333333333003333330033333300333333005555555555555555555555551111111155555555555555555555555511111100000000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f000000000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff00ffffff00ffffff00ffffff0000000000ffffff00ffffff00ffffff00ffffff000000000000000000ffffffffffffffff0000000000000000ffffffffffffff00
|0,10=>0xffffff00000000000000000000000000ffffff000000ffff0000ffff0000ffff0000000000000000000000000000000000000000aaaaffffaaaaffffaaaaffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa000000000000000000000000000000000000000000000000ffffffffffffff00ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffff00ffff0000ffffffffffff0000ffffffffffff0000ffff0000ffff0000ffff000000000000ffffffff00000000ffffffff00000000000000000000000000000000ffffff00ffffffffffffff00ffffffffffffff00ffffff00ffffff00ffffff00ffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000000000000000000000000000ffffffff000000000000000000000000ffff0000ffffffffffffffffffffff00ffffff0000000000000000000000000000000000ffffffffffffffffffffffccffffffcccccccccccccccccccccccccccccccccc0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000ffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff000000000f0f0f0f0f000f0f0f0f0f0f0f000f0f0f0f0f0f0f000f0f0f0f0f0f0f000f00ffffffffffffffffffffffffffff000000000000000000000000000000000000
|0,11=>0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff0000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ff00ffffffffffffffff0000ffff0000ffffffffffffffffffff0000ff000000ff00ff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff00ff00000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0000000000000000ff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ffffffffffffff00ffffffffffffffffffffffffffffffffffffffffffffff00ffffffffffffff0000000000ffffffff00000000ffffffff00000000ffff000000000000ffff0000ff00ff00ffffffffff00ff00ffffffffff00ff00ffffff00ff00ff00ffffff00ffffff00ffffffffffffff00ffffffffffffff00ffffffffffffff00ffffff003333330033333333333333003333333333333300333333333333330033333300ff00ff00ff00ff00ff00ff00ffffffffff00ff00ff00ff00ff00ff00ff00ff0000000000ffffffff00000000ffffffff00000000ffffffff00000000ff00ff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff000000000000000000ff00ffffff00ffffff00ffffff00ffffff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffffffff00ffffff00ffffffffffffffffffffff00ff00ff00ff00
|0,12=>0xff00ff00ff00ffffff00ff00ff00ffffff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff0000000000000000003300330000000000330033000000000033000000000000003300000000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000000000ffffff00ffffff00ffffff00ffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff000000ff000000ff000000ff00000000000000ff000000ff000000ff00000000000000ff000000ff000000ff00000000ffffffffffffffffffffffffffffffffffff00ffffff00ffffff00ffffff000000000000000000000000000000000000000000000000000000000000ffffff00ff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ffffff00ffffff000000000000000000ffffffffffffffff0000000000000000ffff0000ffff00000000ffff0000ffff0000ffff0000ffff00000000000000000000000000000000ffffffffffffffffffffffffff00ffffffffffffffffffffffffffffff00ff000f0f0f0f0f0f0f0f0f0f0f0f0f000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f00ffffffffffffffff3333333333333333ffffffffffffffff3333330033333300ffffffffff00ff00ffffffffffffffffffffffffff00ff00ffffffffffffff00
|0,13=>0xff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000ffffffff00ff00ffffffffff00ff00ffffffffff00000000ffffffff000000000000ffff0000ffff0000ffff000000ff0000ffff0000ffff0000ffff00000000ffffffffffffffffffffffff000000ff00000000000000000000000000000000ffffffffffffffffffffffff000000ffffffffff00000000ffffffff00000000ff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ff00ff00ffffffffffffffffffff00ffffff00ffffffffffffffffffffff00ffffff0000ffffffffffffffffffff0000ffffffffffffffffffffffffffff0000ffffff00ffff0000ffffffffffff0000ffffffffffff0000ffffff00ffff0000ffffff00ffffffff00000000ffffffff0000ffffffffffff00000000ffffffff00000000ffffffffffffffffffffffff00ff00ffffffffffffffffffffffffff0000000000000000000000000000000000ff00ff000000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f000f000f0f0f0f0f0f0f0f0f0f0f0f0f00000000ffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff0000ffffffffffffffffffffffffff00ff00ffff0000ffff0000ffff0000ff00000000000000000000ff00000000000000ff00000000000000000000000000000000
|0,14=>0xffffffff000000000000000000000000ff00ff00ffffffffffffffff000000ff000000ffffffffffffffffff000000ff0000000000000000000000000000ffff0000ffff00000000000000000000ff000000ff00000000000000000000000000000000ff00000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff00ffffff00ff00ff00ff00ff00ff00ff00ff000f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000ff00ff00ff00ff00ff00ff000000ff00ff00ff00ff00ff00ff00ff00000000ff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ff000000ffff0000ffff000000ff000000ff0000ffff0000ffff000000ff000000000000000000000000ffffffffffffffff0000000000000000ff00ff00ff00ff00ffffffffffffffffffffffff00ff00ffffffffffffffffffffffffff00ff0000ffffffff00000000ffffffffffffffffffffffff00000000ffffffffffff0000ffffffffffffffff000000ff000000ff00000000000000000000000000000000ffff00ffffff00ffffff00ffffff00ffffff00ffffff0000ffff00ffffff0000ffffffffffffffffff00ff00ffffffffffffffffffffffffff00ff00ff00ff003333333333333300333333333333333333333333333333003333333333333300
|0,15=>0xffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffff000000000000000000ffffff00ffffff0000000000000000000000000000000000ccccccccccccccccffffffccffffffcccccccccccccccccccccccccccccccccc3333330033333333333333003333333333333300333333003333330033333300ffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff000000000000000000ff00000000000000ff00000000000000ff0000000000000000ffffffff000000ffffffffff000000ffffffffff000000ffffffffff0000000000ff00ff0000000000ff00ff00ff00ff00ff00ff0000000000ff00ff00ff000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000ffffffffffffff00ffffffffffffffffffffffffffffff00ffffffffffffff000000000000000000ffffffffffffffff0000000000000000000000000000000000000000ffffff0000000000ffffffff00000000ffffff0000000000ffffff00ffff0000ffff0000ffffffffffffffffffff0000ffff0000ffffff00ffffff0000000000ffff000000000000ffffffff00000000ffff000000000000ffffff00ffffffffffffffff000000ff000000ffffffffffffffffff00000000000000000000000033333333000000003333333300000000333333330000000033333300
|1,0=>0xffffffff0000ffffffffffff000000ffffffffff0000ffffffffffff000000000f0f0f0f00000f0f0f0f0f0f0000000f0f0f0f0f00000f0f0f0f0f0f00000000000000000000000000000000000000000000ffff0000ffff0000ffff0000ff00ffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000ff00000000000000000000ff00ff00ff00ff000000000000000000ff00ff00ff0000ffffffffffffffffffffffff0000ffffffffffffffffffffffffffff00000000ffffffffffffffff0000ffff0000ffffffffffffffffffff0000000000000000ffffffffffffffffffffff00ffffffffffffffffffffffffffffff00ffffff00ffffffffffffffff00000000ffffffffffffffffffffffff0000000000000000000000ff000000ff000000ff000000ffffffff00ffffff00ffffff00ffffff000000003300000033000000330000003333333300333333003333330033333300ff00ff00ff00ff00ff00ff00ffffffffff00ff00ff00ff00ff00ff00ffffff00ffffff00ffffff00ffffff00ffffff0000000000000000000000000000000000ffffffffffffff00ffffffffffffff00ffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffffffffffffffff00ff00ffffffffff00ff00ffff0000ffff0000ffff0000ffff00ffffff0000ffff0000ffff0000ffff0000
|1,1=>0xffffffffffffffffffffffffffffff00ffffff00ffffff00ffffff00ffffff00ffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000000000000000000000ff000000ff00000000000000000000000000000000ffffffff00000000ffffffff000000ffffffffff00000000ffffffff00000000ff00ff00ff0fff0fff00ff00ff0fff0fff00ff00ff0fff0fff00ff00ff00ff003333333333003300333333333333333333333333330033003333333333333300ffffffffffffffffffffffffffffffff000000000000000000000000ffffff00ff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ff00ff00ff00ffffffffffffffffffffffffff00ff00ffffff00ffffff00ffffff00ff00ff000000ff0f0000ff0f0000ff0f0000ff0f0000ff0f0000ff0f0000ff0f0000ff00ffffffff00000000ffffffffffffff00ffffffff00000000ffffffffffffff00ffff0000ffff0000ffff0000ffffffff00000000000000000000000000000000ffffff00ffffff00ffffffffffffffffffffff00ffffff00ffffffffffffff0033333300333333003333333333333333333333003333330033333333333333000000ffff0000ffff000000ff000000ff0000ffff0000ffff0000000000000000ffffffffffffffff00ff00ff00ff00ffffffffffffffffff0000000000000000
|1,2=>0xffffff00ffffffff0000000000000000ffffff00ffffff00ffffffff33333333ffffffff33333333ffffffff33333300ffffffff33333300ffffffffffffffffffffff00ffffff00ffffffffffffffff000000000000000000000000ff0fff0f00000000ff0fff0f00000000ff0fff0f00000000ff00ff00ffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff000000000000ffff0000ffff0000ffff0000ffff0000ffff000000000000ffff0000000000ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff000000ff00000000ffffffffffffffffffffffffffffffffff00ffffff00ffffff00ffffff00ff00ffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff000000000000ffff0000ffff000000000000ffff0000ffff0000ffff000000000000ff00ffffffffffffffffffffffff00000000ff00ff00ff00ff00ff00ff0000000000ffffff00ffffff00ffffffffffffffffffffff00ffffff00ffffff00ffffff00ff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00ffffffff33333300ffffffff33333333ffffffff33333300ffffffff333333003333330033333300333333333333333333333300333333003333330033333300ffffffffffffffffff00ffffff00ffffffffffffffffffffff00ffffff00ff00
|1,3=>0xff00ff000000ff00ff00ff000000ff00ff00ff0000000000ff00ff00000000ffffffff0000ffffffffffff0000ffffffffffff00000000ffffffff000000000f0f0f0f0f0f0f0f000f000f0000000f0f0f0f0f0f0f0f0f000f000f00000000ffffffffffffffffffffffffffffffff00000000ff00ff0000000000ffffff00000000ff000000ff000000ff000000ff000000ff00000000000000ff00000000fffffffffffffffffffffff0fffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000ffff00000000000000000000000000000000ffffffffffffffff000000000000ffffffffffffffffffff0000000000000000fffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ffffffffffffffffffffffffffff00ffffffffffffffffffffffffffffff0000ffff00ffffff00ffffff00ffffff00ffffff0000ffff0000ffff0000ffff00000f0f0f0f0f0f0f0f0f0f0f0f0f0f000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000ccccccccccccccccccccccccccccccccccccccffccccccffccccccffcccccccc000000000000000000000000ffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000ff000000ff000000ff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffffffffff00
|1,4=>0xff00ff00ff00ff00ff00ff00ff00ff00ff00ffffff00ffffff00ffffff00ff0000000000ffffff00000000000000000000000000ffffff0000000000ffffff00ffffffffffffffffffffffffffffffffffffffff00000000ffffffffffffff00ff00ff00ff33ff33ff00ff00ff33ff33ff00ff00ff33ff00ff00ff00ff33ff00ffffffffffffffff0000000000000000ffffffffffffff00ffffffffffffff000033003300330033003300330033003300330033003300000033003300330000ffffffffffffffff0000000000ff00ffffffffffffffffff00000000000000000000000000000000ffff0000ffffffff0000000000000000ffff0000ffffff00ffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffffff00ffff0000ffff0000ffff0000ffffffffffff0000ffff0000ffff0000ffff0000000000000000000000000000000000000000000000000000ffffff00ffffff000000000000ff00ff0000000000ff00ff0000000000ff00000000000000ff0000ffffffffffffffffffffffffffffffff0000000000000000ffffff00ffffff0000000000ffffffff00000000ffffffff000000000000000000000000ffffff00000000000f0f0f0f00000000000f000f000000000f0f0f0f0000000000000000ffffffffffffffff00ff00ff000000ffffffffffffffffff00ff00ff00000000
|1,5=>0xffffffffffffffff0000000000000000ffffffffffffffff00000000ffffff00000000000000000000000000ffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ffffff00ff00ff00ffffff00ff00ff00ffffff00ff00ff00ff00ffffffff00000000ffffffff33333333ffffffff00000000ffffffff33333300ffffff00ffffff00ffffff00ffffffffffffff00ffffff00ffffff00ffffff00ffffffffffff00ffffffffffffff00ffffffffffffff0000ffffffffffff00000000000000000000000000000000000000ff00ff00ff00ff00ff00ff00000000ffffffffffffffff0000000000000000ffffffffffffffffffffff00ffffff00ffffffffffffffffffffffff00000000ffffffffffffffffffffffffffffff000000000000000000ffffffff0000ffff0000000000000000ffffffff00000000ff00ff00ff00ff00ff00ff00ffffffffff000000ff000000ff000000ffff0000ffff00ffffff00ffffff00ffffff0000ffff00ffffff00ffffff00ffffff0000ffffffccffffffccffffffccffffffccccccccccccccccccccccccccccccccccffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff000000000000000000000000000000ff000000ffff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000000000ffff0000ffff0000ffff00000000
|1,6=>0xffff0f0fffff0f0fffff000fffff000fffff0f0fffff0f0fffff000fffff0000ffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f000000ffff0000ffff0000ffff0000ff000000ffff0000ffff0000ffff0000ff00000000ff000000ff000000ff000000ffff00ff00ff00ff00ff00ff00ff00ff0000000000ffff00ff00000000ffff00ff00000000ffff000000000000ffff00000000000000000000ffff00ffffff00ff0000000000000000ffff00ffffff00000f0f0f0f0f0f0f0f0f0f000f0f0f000f0f0f0f0f0f0f0f0f0f0f000f0f0f00000000000000000000000000000000ffff0000000000000000000000000000ff00ffffffffffffffff000000000000ffffffffffffffffffff000000000000ff0000ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff00ff00ff00ff00ff00000f0f0f0f0f0f0f0f0f0f0f0f0000000f0f0f0f0f0f0f0f0f0f0f0f0f00000000ffffffffffffffffff00ff00ff00ffffffffffffffffffffff00ff00ff00ff00ffffffffffffffffffffffaaffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000f0f00000f0f00000f0f0000000f00000f0f00000f0f00000f0f000000000000000000000000000000ff000000ff0000000000000000000000ff0000000000000000ffffffff0000000000ff00ff00000000ffffffff0000000000000000
|1,7=>0xffff0000ffff000000000000ffff0000ffff0000ffff0000000000000000ff00ff00ff00ff00ff00ff00ffffffff00000000000000000000000000000000ffffffffffffffffff00ff00ffffffffffffffffffffffff00000000000000000000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff0000ffffff00ffffff00ffffff00ffffff00ffffff0000000000ffffff00000000000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f0000000000ffffffffffffffffffffffff33333333ffffffffffffffffffffffff33333300ffffffffffffff00ffffffffffffff0000000000000000000000000000000000ffffffffffffffaaffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffffffffff00ffffff00ffffffff00000000ffffff0000000000ffffffffffffffffffffffff00000000000000ff000000ff000000ff0000000000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0000ffffff00ffffff00ffffff00ffffff00000000000000000000000000ffffff000000000f0000000f0000000f0000000f0000000f0000000f0000000f00000000ffffffffffffffffffffffffffffffff00000000ffffff0000000000ffffff00ffffffff00000000ffffffff0000ffffffffffff00000000ffffffff0000ff00
|1,8=>0xffffffff000000ffffffffff000000ff00000000000000000000000000000000ffffffffffffffffffffffff000000ffffffffffffffffff000000000000000000ff00ff00ff00ff00ff00ff0000000000000000000000000000000000000000ffff00ffffff00ffffff00ffffff0000ffff0000ffff0000ffff0000ffff0000ffffffffff00ffffffffffffff00ffffffffffffff00ffffffffffffff00ff0000000000000000ff0000000000000000ffffffffffffffff0000000000000000fffffff0fffffff0fffffff0fffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000ffff0000ffff0000ffff0000ffff000000ff000000ff000000ff000000000000ff000000ffff0000ff000000ffff0000ff000000ff000000ff000000ff00ff00ff00ffffffffff00ff00ffffffffff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffffff0000ff000000ffffffffffffffffffff0000ff000000ff00ffff0000ffff0000ffffffffffffffffffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffffffffffffffffffff0000ffff0000ffffffffffff0000ffffffffffff0000ffffffffffffffffffffffffffff0000ffffffffffffff00ffffffffffffffffffffffff0000ffffffffffffffffffffffffffff0000ff00ffff0000ffff0000ffff0000ffff0000ffffffffffffffffffffffffffff0000
|1,9=>0xffff0000ffff0000ffff0000ffffffffffff0000ffff0000000000000000000000ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff0000000000000000ffffffff00ff00ffffffffff000000ffffffffff00ff00ffffffffff00000000ff00ff00ff00ff00ff00ff0000000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffffffffccccccccccccccccccccccccccccccccccccffffffffffffffff00000000ffffff00ffffffffffffffff00000000ffffff000000000000000000ffffffff000000ff0000000000000000000000000000000000ffffff00ffffff00ffffff00ff00ff0000ffff0000ffff0000ffff0000000000000000ffffff0000000000ffffff0000000000000000000000000000000000aaaaaaaaffffffaaaaaaaaaaffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa000000000000ffff000000000000ffff000000000000ff00000000000000ff0000000000000000000000000000000000ffffffffffffffffffffff00ffffff00ffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffff000000ff000000ff000000ffff0000ffff0000ff000000ff000000ff000000ff00ffffffff00ff00ffffffffff00ff00ffffffffff00ff0000ffffffff00ff00000000000000000000ffffffff00ff00ff0000000000000000ffffffff00ff0000
|1,10=>0xffffffffff00ff00ffffffffff00ffffffffffffff00ff00ffffffffff00ff00000000000000000000000000ffffffffffffffff00000000ffffffff00000000ffffffff00000000000000ff00000000ffffffff00000000ffffffff00000000ff00ffffff00ffffff00ffffff00ffffff00ffffff00ff00ff00ffffff00ff0000000000000000000000000000000000ffffffffffffffffffffffffff00ff00ffffffff00000000ffffff0000000000ffffffffffffffffffffff00ffffff00ffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00000000ffffff00ffffff000000000000000000ffffff00ffffff00ffffff00ffffff00ffffffffffffff00ffffffff00000000ffffffffffffff00ffffffffffffff00ffffffffffffffffffffffffff00ff00000000000000000000000000000000000000000000ff00ff00000000000000ff0000000000ff00ff0000000000000000ffffffffffff00ffffffffffffff00ffffff0000ffff0000ffff0000ffff00000000ff000000ff000000ff00000000000000ffff0000ffff0000ffff00000000ffffffffffffffffffffffff00000000ffff0000ffff0000ffff00000000000000000000000000000000000000ff00ff00000000000000000000000000ff000000ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff0000000000000000
|1,11=>0xff000000ff000000ffffffffff000000000000000000000000000000000000000000ff00ff0000000000ff00ff00000000000000000000000000000000ffffffffffffffccffffffffffffffcccccccccccccccccccccccccccccccccc00ff00ff00ff00ff00ff00ffffffffff00ff00ff00ff00ff00ff00ff00000000ff00ff00ff00ff00ff00ff0000000000ff00ffffff00ffffff00ffff00000000ffff0000ffff0000ffff0000ffffffffffff0000ffff0000ffff0000ffffff00000000000000ffff000000000000ffff00000000000000000000000000000000000000000000000000ff00ff00ff00ff00000000000000000000000000000000ffffffffffff0000ffffffffffff00ffffffffffffff0000ffffffffffff000000000000ffff000000000000ffffffff00000000ffff000000000000ffff0000ffffffffffffffffffff00ffffff00ffffff0000ffff0000ffff0000ffff000000000000ffffffff00000000ff00ffff00000000ffffffff00000000ff00ff00f0f0f0f0fffffff0f0f0f0f0fffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000000000000000000ffffffffffffffffffffffff0000000000000000ffffffffffffffff000000ff000000ffffff0000ffff0000000000000000000000000000000000000000ffff0000ffff00000000000000000000000000000000
|1,12=>0xffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000ffff00000000ffff0000ffff0000ffff0000ffff0000ffff0000ff000000ffff0000ff00ffffffffff00ff00ffffffffffffffffffffffffff00ff00ffffffffff00ff000000000000000000ffff00ffffff00ff0000000000000000ffff0000ffff000000000000ffffffff000000000000ffff00000000ffffffff0000000000000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff0000ffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff000000ff00ff0000000000ff00ff00ff00ff00ff00ff0000000000ff00ff00000000ffff00ffffff0000ffff00ffffff00ffffff00ffffff0000ffff00ffffff0000000000000000000000000000ffffff00ffffff00ffffff00ffffff00ffffff000000000000000000ffff0000ffffffff0000000000000000ffff0000ffff0000ff00ff00ff00ff00ffffff00ffffffffff00ff00ff00ff00ffffff00ffffff00ffff0000ffff00ffffff0000ffff00ffffff0000ffff0000ffff0000ffff00000000000000000000ffff0000ffff00ff0000000000000000ffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ffff00000000000000000000000000000000
|1,13=>0xff000000ff000000ff000000ff000000ff000000ff0000000000000000ffffffff00000000ffffffff00ff00ffffffffff00000000ffffffff00000000000000000000ffff000000000000ffff000000000000ffff00000000000000000000ffff000000ff0000ffff000000ff0000ffff000000000000ffff0000000000000000000000000000000000000000ffffffffffffffffffffffffffff0000ffffffff00000000ffffffffffffffffffffffff00000000ffffffffff00ff00ffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffff0000ffffffffffffffffffffffffcccccccccccccccccccccccccccccccccccccccc
|_,_=>0
def sP:Nat→Nat
|0=>0x305c240f0204430250305c361212064220c0c00036230c83030220b8141e04108800c170283c08110f8182e0504810221e0c0180a0f020443a060b86c38190883030170283c0808038182e0507810220c08000361a0c84418180b8141e0401854040002824080d0a04c0c12078102207080180a09020440e100303c1c0d0602c1406028240808038180a04018080200
|1=>0x305c0a0f020604c3d0305c781207810220c080180a2407810220c0801824050783818181c8180a0f020e018180305c0a0f020605e370305c52120781022181b05c241a07864220c0c05c0a28048cc220c0c0000a240203030350305c240f19838220c0c0000a32088605e31180180a24088605c2d160180a2b0204418181505c5212140244e11060600a0f020604c22
|2=>0x305c780507838220c080181e11060609c4d0305c984b0204418180305c0a281383030350305c52050781022181b05c0a0f02030304a0305c520f0c83822182485c0a1a07864220c0c05c8c2914064220c0c05c0a4404810181811000520504810220c08018240f0204430430305c1e040890830410305c360504810221820000081106060543f0305c0a0408830303e
|3=>0x28844181803014500c0c17cbc060b974340f02044181800014120406060445c000141e04089405e060b8141e040883020000283c08110c1640c170d8683211060602e5807810220c0c15c2e0f088303056268182e0504838220c0c15400050481018182a14c00290903c0811060400c050e03c3211060602e1207944220c0c0180a4407838221e0c0180a0f02030a04f
|4=>0x21a418180305c1e0c0c088ac6d0305c1e0406060d86b0305c0a0f02060d44f0305c361207044302f168188a0507810d20c0c018b66807838220c0c0180a0902030302233800b412078382218328188a0f0204430490305c240f070443049320180a0f07034180b3181836291406418181105c361c0c84418180b814121908830306100180240f0704418180316c240f
|5=>0x204430403c05c0a2b0784418182705c36240c84418183885c367712064220c0c05c52281384418183b05c36290203030753a05c52090704418183980024720704418181a05c240f0c838220c0c1c40a283804418180005c0a2804810221e0c018de0502030304f1505c361211864220c0c05cdc0507810d20c0c0001e0c0c0f4ac6d0305c740507810d20c0c0000a0f
|6=>0x2044fe180305c0a0f0204418100305c0a240c844307e1605c0a2304864220c0c000740504810220c0c000741207944220c0c018780507810d20c0c00036230203030220305cee7d078101818111f024280704418183b018741204810220c0c000520f0204430493d85c362912064220c0c05cf40514010220c0c05c0a0f0203030790305c0a0f0202018100305c520f
|7=>0x120683211060602e5b0282408110606114290903c1c89060600c0504810221e0c0191005020441818150190e0507810220c0c0180a2304838220c0c0180a24088605c31160180a0f02044a0210305c240f070102218128181e110606108830305c0a820203030221505c36451406418181105c520f0204430490005d020507810220c08018740507810220c08001000f
|8=>0x88303092268182e1b228903211060602e0507810221501058001b14a443211060602e88480141e04088303005078102218478182e1b1189c220c0c0182e3c04810220c0c0fc0005220240811060400c0507810220c280182e0514238081106060000507810302f110182e051903c18182f8182e0515810221817a342e12078382218189040c1b458a03211060602e1b
|9=>0xb8141e0408940d4060b814500c0c260e8060b814120e4483030060b81412040883030061d8481e04018080c0508830304e490182e050781018184b0182e050781022184a8182e121403c0869060600c5b0283c1c110f0600c051409c18182a0182e05078102218350182e05078102294178182e1b1482408110c0bc007d0781018181124cf805078103026278182e04
|10=>0x510141e040606142060b8481e04088313e062e8a424280c84418180b814882b0781022183285c0a0f02060d49b0305cba291409c220c0c05d3c0507810220c080180a4407810220c0800036290c84418184e85c24720484418184e05c367719064220c0c05c24720704418181a0141e040c0bd36060b83c220c0c15934060b86c52230c84418180b8481e0408a643006
|11=>0x7864080c0c088f81714814e40f5a04418180b848500f07044181859818520504810220c0c2c852051403d6011060602e05078101818112bc0c170283c0811062b400ab0283c081106060001702aa01e0408860b2060b8a40a0f0204430650005c0a0f02030304f0305c0a28048441818270182e1b228a0080c0c0880c17028240811520600c3a2d8481e0e088303006
|12=>0x3014501106060ac065185c0a0902044302f180000c0507810220c280000c17028ac12040883030bd0b814560f0204430260305c520f5e0101818032ec2e120283c08110c0d80c172e83c08110c09970060b848880f07044181836818ba12142dc220c0c0182e055b03c08110c2d40c17029981e040606136060b86c0a320c84418180005c360514044302f188182e12
|13=>0x60602e05140ac1e11060613817618141e040606184060b81450090883030560305c3628020441818268182e801403c220c0c2700c17028241e04088604c00031140a2804864220c0c0000a0f0204430c1179f82e052203c0811061400c17600141e040883030000b8141e0408830304e0305c0a44140244e11060600012078102218178fc0c17028a01211060617e00
|14=>0x7838220c0c0a80c0569010220c0c0a80c170283da2040883030001d0141ecf0883030060b86c24280883030ce0305c0a0f070441818270182e0507838221817b340c17028241e1902030302200114240f070441818033300a2804810220c0c01996052203c08110c0bc0017028a190040883030060b8141e041c03030060b9741e040883030780305c3629120641c11
|15=>0xc0180a0f7081022182c8182e0512044302f188c00c17370141e0408861c0060b9140a0f0222418180305c36de0204418186e8182e05078641c110c1240c1714b6c1e040883030060b8481eda0203030220305c5205078641c0c0c0882e1202b641e0e0883030060283c08110c0940c1714b581e190204418180b8141e0406061a6060b9740a2804864220c0c000b412
|16=>0x204418180305c7605078102218178fc0c17028681e190883030172d8141e04060609e060baf81e04060607a6d0305c0a2b5383c08110c0bc2e1b028a16011060600c172e8a450190883030175c83c220c0c2fc7e060bb901e0408830303f0305c0a0f02044302f0305c0ae2078101818110182e450283c0811060600c3b5f0141e11060609c060b848340f07010220c
|17=>0xc0187605538101818279d00c172e8141e19070441818000141e04088606c060b8e80a0f020441818000ec240f02030302249819763a0283c0811060611417028a1d0110606054060b8141e0e0883030e70305c3612020441818738182e280784418184e0fc0c17028241e040606136060b814500913b98220c0c0008a05078101818499d40a0f02030304a0305c0a0f
|18=>0x20441818490182e2907810220c0c2180017228141e040605844065f0141e1106060ac060b8a40a0f0204418187705c5205078641c0c0c0f42e290903d8a0e020441818028ac12040883030ed000e80a0f02030309b0305c0a0f0204418184e8182e051403dd611060600c174f0141e04060609e060b814640f088605e2d030141e0406061d4e90305d020507810220c
|19=>0xc194fc1702b64081106061ce060b814380f0c84418180b86c0a280c84418187885cba050781018181c8182e1207944220c0c0193c05020441818150182e1b458a00811060600c170d89034040883030060b848500f02044181603014500f08830304e0305c0a0f0704418184e8182e1b09010220c0c2740c170d8a448280c84418180b8141e0408860caf00305cba05
|20=>0xd8a4fa0408830302a0b9682424078382218178180a0f07030303d033dc2e6e07810220c0c3d00c17028a056040883030a30ba400aa707810220c0c05c36f3020441818790182e051403c221817a140c17028a01204089fc30060b974520f13810220c0c05c5205078641818112602e050783822a40c01852051403c320c0c0882e0504810220c0c15400050789c0811
|21=>0x883030060b8141e040883030ff0305c0a0902045fa180301412040883030760305c0a280786422187e0182e6e0283c081106060003b2d848480f070441818031a00a0f070441818031140a820781018181105c0ad8078102218128182e122583c0811060600c17028901e110c0bd7e060b9b9f20f0204418180305cb60f02030303d598182e051203c220c0c3e00c17
|22=>0x90a0220c0c1580c178103c4e0e0883030063b8141e0406060447500014340f0204418180005cb605078382218178182f010283c08110c1940c171d0141e040887830060b97452280204418180005d745d1483c0811060602e1b148918a04088303017370141e040606136060b814500f0883030560305c0a0f020448418178182e450283c320c0c08938170d8a60004
|23=>0x305d440519010220c0c0182e3a028a012040883030000283c320406061d5090b9300a280204418180305c361214064220c0c0002e050781022182c8182e5a0929c1e0e088303006028920c0f020443105031140a2804838220c0c0193c05078102218178182e05630241e04088608000148141f040c84418180b814880f02044306a0305c52056303c08110c1002e1b
|24=>0x2030310e0305d205b0283c0811060602e050483c08110606218060283c080c0c08924060b9300a280704418180305c0a52048102218178001e11060617e3f0305c362948810220c0c0182e2907810220c0c1ce0e17028c81204088605e30031140ad207864220c0c05c0a0f0883030e95e8182f010283c0811061400c17228141e0408830310b0b8141e0e060619c5f
|25=>0x28902218178b40c170283c320e088604c060ba79200507810220c0c05c3645020303022150182e6f07810220c0c0fc0c17029f41e04060609e000b86c8a090c810220c0c05c0a0408830302a430182e3c2d8481e0e0883030060d91448040883030060b814500f0204431120305c242807810227f0c0182e450283c080c0c08926750d9141e190883030560bc3c0a0f
|26=>0xb8141e2702030309b0305d10450283c0811060600c1b6a83c080c0c34c0c178a8a412040883030060b9740a2802030304f0305cde05078101818278002e4507864220c0c270f8170283c081106061d2060b814500f0204418100305c9805078441818308182e450283c080c0c0880c175f014560f0204418180b9b80a0f020443c180305c36090204418182b8182e1b
|27=>0xc26c0c17148481e0408830311903220ba0507810220c0c0190205078101818110182e1b3e82408110606000051203c2218178b85a06720a58c0f0204418180b974b44507838220c0c019100507810220c0c0182e050781018181ea480c170283e301106060c2060b814560f0204418182685c0b1707838220c0c0182e120288c1e190883030170283c080c0c08a2c06
|28=>0xb84a3e0f8f0441818030a4247204810220c0c05c751c07810220c0c0182e580283c08110606000170903e36040606044060b8141e043483030060b8141e04018302c00442040a0f020441818031141e1106060acb30305c0a090781022188d0182e6f02810220c0c0a800171d2200a0f02044181800014500408860ca065185c0a4480010220c0c0182e051203c080c
|29=>0xc0bc60060b8a4242407864220c0c05cba0f020441818388182e5807810220c0c1c40c170d89008110c0bd70060b86c8a281384418180305c240f8f044181803014cc0f02030304f0305cba291583c0811060602f220283c08110c4840c17148141f200204418180b8148809020441818030ed7c0f0204418181f8182e450283c080c0c0f40c170283c080c0c2fc7206
|30=>0x305c0a0f900441818948182e3c0283c08110606114170283c08110105800810283c080c0c0f40c172e81446040883030060b960520f0204418180305c0a28078642218130182e05144a0220c0c49c0c171d0141e040883031070b81412040883031260305cba050781018181e8182e0504810220c0c27400060282408110c0b858062d8481e0e088303000028a03211
|31=>0x6060e21702890560f0c84418180b9ba380f0204418180305d02050203030223a0182e051583c320e0883030a95c8141e11060609c060b9dc0a2407864220c0c05c520f020303022960182e051401018182a0194617028a01e1106061d2060b8141e04088605e7e0005c52050781018183a9d02e5d028101818111d00c171e014120e020441818000141e0406060bee7
|32=>0x7b1408110c0980c1702998560f02044302f0b8a40a7204838220c0c05c8a0f0c84418182b1f02e05844bc1e04088303017980a41e040883030060b8481e0e0204418182b8180ab69783c0811060602e1b2283c320408830301702b140811060605417808141e0408860d4060b814880f02044302f3f05e5c05078102218608182e29028240811060625a051203c3211
|33=>0xb849ae0f0c838220c0c01852050483c08110c1002e1b1483c081106060f617028a0121106060ac00030141e0e0204666180305c0a28020303022150182e45990141e040606044060294808110606124000b9300a0f0203030350305c0a0f02044302f988182e05078101818112340c1714814480f0c84418180baf80a0f0204430650305c24051583c320e088303005
|34=>0x883030060b96c1e0408830304d0305c8a0f5e0101818032ec2e5b0283c08110606270170d8a450040883031070baf80a5204810220c0c0000a28078126e0c0c0017c0507810220c280182e291403c4e1106060da17091c8081106060681702bec1e040606044060b814483202044302f1801852050781018189a0182e880283c0811060600cd0458141e04088303006
|35=>0xb8a40a0f0204418184505c8a05078102218130182e3c0903c1c040883030000288c1e040606044060b8481e330704418180305c0a0f0701018182a0182e0507af01818111580c170283c08110606278060b8e80a0f02030304f0305c522407864220c0c0fc2e051403e4011060600c17090a01c110606170060283c093a06060003c0283c08110f0600c178a8a41e0e
|36=>0x606054060b8e80a0408830302a0305c78120204418181a0002e2904810220c0c1cc00290283c080c0c26c0c1714848120f13810220c0c01450270883030760305c8a0507864080c0c0882e12078641c11060607e060283c080c0c0f51a060b8145004088605e340305c0a0f02030313d0305c0a09070441818398000c290283c081106060003b028a01233088303006
|37=>0x781023330c0182e29090a0120408830300051014500e0883030060b9b80a0f0204431210305c0a0f0204430493d8182e052203c1c11060600c3b0903c080c0c17c0d410bc040a0f088604cbf0305c0a2807810220c280182e1b028901219088303000028a008110c0bd1a060b9140a0f0c83818181105c360902044302f208182e29091c81e0e088303017370480811
|38=>0x305c0b45020441818150182e3a0283c08110c0bc0c170d8481204088605e060b974521214038220c0c0180a24190441818168c00cde0283c080c0c4d00c170903c1c1106062880644014880902044181803174de2914010220c0c05c362912064220c0c05c0a0902030304f3a0182e5d078102218130fc0c17090a01e0e08830307b030481e040883031420305c0a28
|39=>0xc1a80c17028a04e110606068000b815040f0203030220005c52d7a403c0811060602e051201022181781946172e8148809020441818000168e0f0204418180305cba291203c08110606000050483c081106061940602824081106060ec00030f00a0902030304f0305c520507810221e0c0182e81028101818278a80c171d0168c040883030060b814120f020443036
|40=>0x704418182a8182e1b1488c0811060600c170282408110c0bc580003168240f0704418180328c740504810220c0c000743c0903c1c11060600d4b028241e040883030060283c1c110c09a94060b8e9200507810220c0c05c0a24078382218170c40c450283c320c0c08930172e8a41e190704418180b8e80a0f020441818a485c791c07810220c0c0182e05078380811
|41=>0x1785c0a0f07544220c0c018360902044302f1f8182e051583c0811060619217028901f4f0883030060b8481e04089fc30060b814a40f02030303d0005d000f020441818648182e2907810220c0c5380c172d8141e11060609c060bd341e040883031420305c240f070102218179040c05120102218328c00c17029101e510883030060b814500fa6044302f0305c0a09
|42=>0x283c08110606000123903c1c1106060da0602948080c0c088e8000b8141e04088605f500305c0a4415810220c0c2342e0507810220c080182e0514554220c0c0182e0512044302f188b00c17095501e040883030000b8145609020441818180000a280883030850328c2e050789c1c11a98600c6e078102218178fc0c17028a0121106062a4060b8145652048102218
|43=>0x59016900f0204418185985c0a2808830309c0028c2e0507ba00811060600c172e8145011060619c060b8a40a0f1381022181785d10052203c1c11060600c051403c2218135280c171403c220c0c564da060b814560f1381022181785d100507810220c0c0000d570903c0811060600c1702d581204088303000440141e0408830300646014480408830302a0305d1029
|44=>0x883020060bc280a0f0203030ea0305e020507830303d2b0182f4d0283c0811060600c177b0141e040883030060b86c520f0c81018181105c3629142d0220c0c0182f5c0283c08110c0bc0c17ab8141e040883030060b814500f0204430950305c0b1f07810220c0c0182e050781018182f9780c17ad014081106061ba060b8a41e040606044753e05c0a090c8441818
|45=>0x1483c08110c0bc82060b8141f5e02044181800454240f070441818030a41e04060607a063e05c3612220a01c11060600c880283c0811060600cec2d048a40907044181803014500f088604cbf0305c36121209c0811060600c0514044302f168c00c17090141e0408860ca060b86c2428070441818000180a2407810220c0c3280c6e0283eba11060600c172d8141e04
|46=>0x35802e5d028a0220c0c1380c170903c080c0c0880ccc0b86c8a040883030920305c980f0204418183b0182e0507810220c0c4640c17028901e110c0c482060b8141eda0204430b50305c0a28078441818a90182e1b228241c040883030061e014080c0c13ce8060b814120406060a8060b8a4240f020441818af85c240f070102218178fc0c450784418182b1b40c17
|47=>0x3303c220c0c1380c17444040a0f020441818030a40a0fb2010220c0c05c3609020441818268182e0504810220cb18193c0507810220c0c0182f152283c0811060600c17028c81e040606044060b8141e0406061a7620305cb6050483c1c110606000050789c1c110602c0d130283c0811060600c171e0141e040883031490b8a4240f02044302f0305c240f02030305f
|48=>0x5d7205078102218350182e52078441818429b40c17148141e040883031670b9140a0f02030309b0305e020f088303056598182e290283c08110c0bc0c170299856040883030a30b8a40a0907810221817800b60f0704418181f8182e1204810220c0c5980c17028a01e0406062ca060b8141e0408830a0060b8141e04088605e710305c242807810220c0c0187605
|49=>0x6062d606028a01e190606044000bc040a0f0606044980305c36d507810220c0c0182e05140101818110194617600141e040886080060b9140a0f020441818033711605078101818b28182e90028241e0408830300014816d40f0204418180b86e48040883030f40305c0ae2078101818b48182e050783818181e9580c170912c1e0e020441818030141e04380441818
|50=>0x28ac1e040883031310b86c8a0f02030303d0305cfa0f0203030223e05d72050784430265f8182e05120c808110c0bc58064f0141e0408830a0060b9741e040883030570305c0a0f13db0220c0c018367719010220c0c0182e1b3e810220c0c0a800170903c1c11060619c06b006c24090c838220c0c018741204810220c0c0182e1b2283c080c0c088ea170903c1c11
|51=>0xc2540c17028a0560408830308d0b86c52280c84418180ba30740507810220c080182e1b148a0220c0c1580c17970141e0408860fc060b8141e040883031310305c740504838220c0c0182e051203c220c0c3380c170283d8a040886234060b8a41e040606044755d85c0a0f02044306a0305c36290204418184e8182e0e088303034398182e3a028240811060600c17
|52=>0x1483c081106060ec060b814480f08830304e0305c240f0204418183c0182e3cb803c0811060600c1702824080c0c15000062d8a4240f07044181800016de0f02030305f0305c741207838220c0c0182e05b703c080c0c0f40c17148141e043483030060b814500f06060be060b8481e0e08830316d0305c0a0f0203030224c0182ebe0283c080c0c0f40c170283c0811
|53=>0x60600c1723814120f0204418183c0008c05078102218908182e05078101818115c80c17148481e0e0883030af03014cc04088605e8d0305c0a289783c3211060602e05078101a140305c0a0f0203030753a0002e1b22824080c0c0880006028a0560f0c844302f0b8481e040883031711f8180a09020441818030ed3c05078102218350182e1b2283c3204060604417
|54=>0x19838220c0c0002e450283c08110c0bc0c170282408110c0bd1a060b9141e04060607ab30305c0a4407810220c0c00076450283c080c0c13ee817029101e0408830308a0b9140a0f020e018180305c367714038220c0c0182f701483c0811060600c1702824081106062e6060b9740a0f0204430400305c980512010220c0c0182ebe0283c18181ea600c170283c0889
|55=>0x280182e77028ac1e04088303017028a01204088303127030141e270204418500305d10052203c081106060009e0283c0811060600c3b3403c0811060600c17028241e04088604c067a83c081106060d8060b8481e040883030c90005d0205078102218178182f2e0283c1c110c0c40c172c0141e04088605e060b8e80a0f0204418500305c0a0f0204532180305c0a0f
|56=>0x283c080c0c260e8060b8141e0408830315f0005e6405078101818110180a0f07044302f170b40c9e440141e040883030061484850090c84418180b86c52e80204418180305e6c05078101818698182e291583c0811060607e172d0481e0e08830308d03014480f020443105030481e0408832ee06028901e04088605f050306c8a7d04810220c0c0000a2407810220c
|57=>0x203030220337c0b06078102218828180a2307864220c0c0002e050e03c0811060600c17028681e040883030060b814500e0883030760305c0a24088605e2d180182e051403c080c0c26c0c17028a0220c0c1840ca30b86cc4190883030170d8a4320408830302a0b8141e040883030ca03230362919064220c0c05c0a0f020303022bd0182f790283c08110c0bc0c17
|58=>0x20441818152740c170ddec0811060600c172d8141e040883031070b974120f0204418181f8182e05143cc1c11060600c17090141e040883030e70305cb6290283c1c110606000170d8a41e190704418180b81450aa0c84418180305c2405078102218178182e05078102218200182e1b148258a040883030170283c0811060600c17761dcfa0f0204418183e06c240f
|59=>0x60619c850305c0a0f020443065000182e052250c1e040883030171e0a40a0f0c838220c0c05c0a0907810220c0c49c0c121403c220c0c2700c172d03c1c110606166060b8145004088303006bf85c520507810220c0c5f42e6e02c901e040883030060b8f0520504b140811060602e0507810220c0c5f00c170283c080c0c088ac000305c0a0f02030304f0305c0a0f
|60=>0x305d3c052203c0811060600c170d8a41e040883030f70b814880f0204430650305c8a05a283c0811060600c170283c080c0c3aa12060b8141204088303006590141eeb0204418180305c0a2807ac0220c0c0182e5a228481e1106060ac060b81448281583c3211060602e0507810220c0c5c40c174f0141e040883030000305c0a2407838220c0c5100c17028a01e11
|61=>0xb81550aa0781022187e0182e3c0283c081106061de060b8480a0f0204418184e8182e055383c080c0c13c0c17370145009020441818033d40a28390241c11060600c1714814482807864220c0c05c78290283c081106061ee17028241e040883030b30001902450283c080c0c13c0c17029981e0408830306d0305c3605120641c11060600c17028241e04088605e7e
|62=>0x60600ccc0b9748a05020441818150182e812e8141e04060609e060b814cc28078102218178182f80028240811060600c17028a01e11060619c060ba2c0a2807810220c0c0182e0507810220c0c1380c170283c1c11a98600c05120681e040883030060b9140a520789c0811060602eb90903c08110606170060baf824050784418182b0182ebe2283c0811060616606
|63=>0xb815e60f020441818790182e812281408110606054060b8a41e040883030b30305d440507810220c0c1840c17028a012190883030000b8a40a0f0c81018181105d72050784418185f8182e1b228240811060600c17c08a40a0f0204418180305c0a24140102218178b00c171d1b80a0f0204418180005dc8050483c081106060000504810220c0c2f40c170903c0811
|64=>0x1203c08110c0bc0c1702a9c1e0408830304e0305cba0514064220c0c0182e0504810220c058180a0f0203030d30305f060514010220c0c0182e0507810220c0c215ce060b8a40a0f070441818578182e29093881e040883030060b8a40a7d07810220c0c0a82e0553810220c0c0a80c17c10141e040883030060b8f08a0504810220c0c0182f5a6a8141e04088303006
|65=>0x903c1c11060610a062d8141e040883030060bbb00a0f13810220c0c2480c1714814480f62810220c0c05d726f0283c0811060600c17409740a0408830302a0305c0a2819038220c0c0c00c46028a308040883030060b8a40b0007810220c0c0182e3c148141e040883031100b814500f0c84418187885d7c2907810220c0c1b40c1702890640f02044302f0305e0205
|66=>0x7810220c0c019be0507810181811019ee170283c08110606314170901450040883030065185c0a0f020441818738182e3a0283c0811060600c17680141e04088605e060ba04780504810220c0c0182e4c0283c0811060611a060b8a40a0f0262418180305c0a0f0204418182b0182e0507810220c0c54b10060b8141e0406060a8000305c0a0f020441818c28182e1b
|67=>0x305c0a0f020441818430000c1709014500f0c84418180005c3645020441818950182e051203c08110c0bc0d03090141ec507010220c0c018361219010220c0c0182e0507838220c0c1580c170283c0811060600c171d8141e04088605e3f0305c3629078380811060600017c58141e040883030065185c0a09070441818398182e12028a01e1106060ac060b86c8a12
|68=>0x60600c1702a9c1e04088605e060b8a40a9107810220c0c0182e12029481e0e0883030850306c8a0f020303022000182e1b0289050190883030060b8480a0f0203030ce2f8182e056903c081106060ac060b8f0de0507810220c0c05e02055383c0811060600c1702e300811060600c1702a9c1e040883030560305c0a660789c08e608830301702a9c1204088303073
|69=>0x32817c050784418182b0182f930283c0811060600c1702890120408830308d0305c0a0f02044280b0305c0a0f070441818033302e1b1483c0811060600c176a01412040883031920305f200507810220c0c0182e0507810220c0c6380c17228141e190204418185185c0a2804810220c0c3240c170283c0811060613a060b9b80a0f6784418180305cb41207b140811
|70=>0x20303022150182e120781018181101976171483c320408830307c0be2c0a0f8c010220c0c0182e45090141e04060604493031140a09078640811060602e5d0283c4e040883030060b9140a2407810220c0c0182e050783808110606054060b9682452078441818428182e0507810220c0c3b80c170283c08110606310060b8141e190883031870305c0a09020441818
|71=>0x5f0141e0408830302a0305c0a44140240811060600017028241e0408830307b0305c0a0f0204419960305cb0051203c0811060600c17229dc0a7d07810220c0c0480a0f020303022498182e050483c081106060ae060b8a4500f070441818368182eb95f0141e040883030060ba040a0f13810220c0c0182e6f148481e040883030171483c0811060632a060b9140a0f
|72=>0xc0bc5a060b9740a4414010220c0c0182e0507838080c0c08800060bc040a24078441818168182e0507810181867214be060b810220c0c4a970060b83c220c0c214da060b8141e040883031980305c78059a810220c0c0182e5d028a008110606000060b914240507810181811019beba2e8141e040883030060ba040a2407810220c0c0182e050789c0811060600097
|73=>0xb86c8a0f0204418180305cb60507810220c0c0182e3b2e8480a0f0203030220305c52120483c1c04088303006028a01e1106060ac060b814fa0907810220c0c0021405078101818754240c170283c081106061fe060b8141e040883030060be640a0f020441818868182e6e028a01211060605a060b814640f0701022181781902120283c1c04088303006028901e11
|74=>0x88303000028901e04088605e730305c0a66220ac1e040883030170903c0811060600ca02403c08110606138060b8141e04060619c5f0305c0b082203c0811060600c17028a01c11060600ca30ba7a020507810220c0c0182e81090141e040606044060b814cc2b07810220c0c0002e5a0283d8a0e0883030060ba04b41207810220c0c0182e3a029101204088303006
|75=>0x283c080c0c0f40c1709016b00f0204418180305d86290283c0811060600c175c86c24280204418180305c0a2407810221817ae00c1722814500f1384418180305c379c07810220c0c0182e5b0283c0811060629217148481e0e088303085030141e0408e6c30060b8a40a6607810220c0c0002eb92e8a41e040883030060b814480f02044302f3f0182e6f028241e04
|76=>0x182e290283c4e0408830308d0bae4500f0204418181f8182e050781018181124c0c17ce8141e040883030060b96c520507ac4220c0c0182e052583c0811060600c17028241e0408830310b0305cfa0f0204418183e05c0aaa0781022187e0182e450283c080c0c0890a060b9140a0f02030302249818ba0504810220c0c4a800060d8481e2707010220c0c0188a12
|77=>0x60607a000305cdc05220240811060600c17c1015e60f0204418180305daa0507810220c0c0182e0507810220c0c4a40c172e8a408110606254060b81450040883030340305d18290283c08110606340172d8a40a0f0204418188485c8a12028a01e0e0883030060283c081106060699f0b86c522404810220c0c0182e5d148481e040883030066f9b80a09020441818
|78=>0x940380811060600c17370141e040883030f10305c0a5204810220c0c2fc0c170283c081106061d2060b9140a0f0203030223a85c0b1707810220c0c0182eb9028901e190883030060b8a40a0f020441818d08182e050781018181126000060b8a40a0f020441818490182ee402b181e040883030060b9140a0f0203030220305c0a28078101818110000c175f0141e04
|79=>0xc0980c170283c08110606346060b8141e190883030300005c2405390240811060600c17090a01e0408830303f0305d100507810220c0c0182e1b2d9141e040883030060b8141e190204418189585cba05078101818110182e051903c1c11060605a065f0141e040883030060b814480902044302f180182e0507838220c0c01b401714814120f0203030220305c0a0f
|80=>0x1483c0811060610a060b8a41e270204418183685c52051403c0811060620e175f0154e0f0204418180305c0a0f020441818036942e051403c08113f8600c172e814560f0204418180305d4405ab03c081106060001702890e4040883030300305c0ba4020441818398182e5b0283d6811060600c170903c1c04088303034032040a0f0203030220305c0a240483c0811
|81=>0x305c0b1f1403c0811060600c17370481e040883030000305c240f8f0441818030144828078102218178182e1202bec1e040606044060b8e80a0f0204418180305d183a148141e040883030000bae40a0907810220c0c019ea4507810220c0c2140c7c0b9300a0f020441818000182e0507810220c0c1d80c17228141e04060607a060b8141e0e020441818938182e5d
|82=>0x78101818110182e3a029101e0e0883030060b814480f0204418183d8182e050483c0811060619c060b974520907810220c0c0000a662203c08110c1940c172d8a4240f070441818030a40a0f0cac4220c0c05c0a0f020441818033e82e6e091101e040883030060b814cc0f020443065000182e1207810220c0c01b4c122903c081106060da060b8145004088303150
|83=>0xb8a40b4507810220c0c0002e05120ac1e190883030174416c0a0f0204418180305cb4052902408110606000170283c080c0c08868060bea40a0f13838220c0c0182e5d090141e04088604c060b8141e0e0204430650305c5205078640811060614c1702b601e0e0204418180305c0a0f0204419770305f4e0507810220c0c0182e120282408110606054060b96c8a05
|84=>0x483c321106060009e5f0141e040883030060b9b80a09020441818033d452051203c3211060602e05bb03c0811060600c17408141e04060609e000305c0a5204838081106060001b2283c3204088303017028240811060625a061483c08110606254000be2d440507810220c0c0182ed5148141e0406061a6060b86c0a4414010220c0c0002e3c0283c4e04088303000
|85=>0x148481e040883030bf0305c360512038220c0c0b40c171d0141e040883030060bbb22a2907810220c0c0182e057d83c080c0c0880c17148481e270204418180005c0a2407864220c0c0fc0c17370141e0e0883030000305d160507810220c0c0182e1b028905004088605e060beac0a0907810220c0c0182e05d503c0811060600c170d8a450040883030060ba300a24
|86=>0x7838220c0c0182e5b2283c0811060600c7c0b8a4240f0c838220c0c17424280204418185c0182e12029481e0e020441818006b41e040883030060b8141e0408860926d0305c520514010220c0c0a80c1709014120f13810220c0c01a140507810220c0c3a40c17028c8081106060600602890500f0883030bf0305c240f19810220c0c0182e051403f5811060600c17
|87=>0x7b8a4247207810220c0c05c0a0907810220c0c1380c17028901e0e088605e310305c0a2b07810220c0c1b40c170283c08110606114060b8145004088303006d885f5e0507810220c0c0182e290283c0811060618e060b84b5c0f020441818031745212078640811060602e450283c0811060615e060bafa02050781018181e8182e3c148481e0e020441818030480a72
|88=>0x204430260305c8a053e83c08110606054170283c081106060ac0003310ba05140441818168182e051583c4e040883030000b9141e040883030b30305c36280204418181f8182e5a091481e040883030000ba780a2807810220c0c0182e900283c1c040883030060b9740a280883030bf0305c8a0507864080c0c0882e051403c08110c1940c17090141e0e088303006
|89=>0x883030000283c09b3060600c1714814500f02044302f0305c0a44120ac1e04088303017808141e040883030065185c0a0f020441818930182e05120ac1e040883030000b814e4040883030340b9dc1e0408830306d0305c52051183c0811060600c17028a0560f02044302f0305c520507810220c0c003646e0283e4611060600c172d8481e110606138060b9740a0f
|90=>0x60600c170283c080c0c08854000305c3605120a0220c0c0b40c17228a40a0f0c838220c0c05c361207810220c0c3380c170283c08110606368060b8141e330704418180305c240507af0080c0c0880c171481451460204418180305c78290903c0811060600017148141e040606044740305c0a289783c0811060600c1714814480f0204418180005c8a050483c3204
|91=>0xc810220c0c1f02e0515824081106061da060b8a4240f07010220c0c0000a28da810220c0c0182e5a029481e0e0883030000b8a40a7207838220c0c05cba05078641c11060600c171d0141e040883030060b8ec0a4404810220c0c0002f0a0283c32040883031090ba045205078640811060602e0522010220c0c00146172e814480f020441818000188a1207b680811
|92=>0xc4ae541702824081106060aa060b81451350c84418180305c240f020441818648182e050783808110606262060bae40a24078102218178182e0514010220c0c6d80c1702998560f07010220c0c05c1e04088303159368182e46149201e040883030060b8a40a2804810220c0c0000a52078101818110002ede07810220c0c0d00c175c9b80a0f0883030bf0305c8a0f
|93=>0x9014480f02044302f0305c0a0f020303022498000c1b14810220c0c0b40c17028241e0408830310d0305c0a0f0cb3c220c0c0182ebe8083c08110606166060b9b80a0f02044302f0305c52051403c4e110606000170d8141204088605e060b86c0a090c810220c0c0002e3c0283c0811060620e17029101e040883031610305f6e0507810220c0c0182e2907810220c
|94=>0x204418180b86cb62907810220c0c0002e1202b481e040883030060bc040a5204810220c0c0182e2902ee81e040883030060b814480f02046a61803014cc0f020441818268182e053302408110606060060b8160c0f02044181803014480f13810220c0c01952126b83c0811060600c1737024081106060e6060baf80a6607810220c0c0182e1b09010220c0c0a80c17
|95=>0x390243211060602e4c0283c1c040883030060b81448280784418184e0182e0507eec0811060600c170283c08113f8600c179b3780a0f0204418180305c8a0507810220c0c2480c170d81450270883030000305d72051203c220c0c0b40c170d8481e190204418180005c8a050483c1c040883030060d8481e040883030560305cb6050784418182b0182e45148141ec5
|96=>0x60600c1702c7c1e040883030060baf80a0907810220c0c0182e29bd83c0811060600c170283c1c04088605e06548f2021207810220c0c0182e051403dc211060600c171e0141eeb0204418180305c0a4407838220c0c0002e6e028a00811060600ca30b8a41e040606044063e05cb60507810220c0c0a80c170283dd0040883030060b8141e040883031bc0305c0a28
|97=>0x808901e0408830303f0305c240507810220c0c57c0c17148481e049b8303006850141e0406061d4060b814e5b50204418180305e9a0507810220c0c0182ef60283c0811060600c171d2200a0f0204418180305c74be0283c0811060600c171e0141e0408830304e0305c0a24078641c11060600017090141e0e02044302f030e8242807810220c0c0182f570283c0811
|98=>0x330a01e0408860ca060bc040a280789c220c0c0182e0507810220c0c4640c172d0481e27070441818030141e0408ef430060b8141e04088082c060b814500f0883031520305c0a28190241c11060600c290283c0811060600c177606c0a0f0c838220c0c0002e121403c0811060600c97029101f860883030060ba048a0507810220c0c0182e0507838220c0c1540c17
|99=>0x883030000305e260507810220c0c0182e05842a01e040883030060b814120408830302a00018b6050483c0811060600005120ac120f0c84418180b8141f28020441818938182e0507838220c0c01b2e29090c81e040883030060b968242407838220c0c0180a241903c1c04088605e06028a1c4040883030060bc081e040883030060b86c8a0f13810220c0c0182e05
|100=>0x305c24050483c320e08830300602998120f02044302f0305c0a0f13838220c0c1cc0c174f0141e040883030060b8141ec5020441818368182e3c0282408110606000052903c081106062921702b601e040883030060b9bc0a2407810220c0c0182ee40283c08110606000170903c081106060ac063e05c0a2407810220c05818b60507810220c0c0182f390d9145004
|101=>0xc0182e3b148141e04088605e060bc040a0907810220c0c0000c050483c081106060ac000306d7c1207810220c0c0182e450283c0811060618e060b9140a0f138101818110182e051403dcc1106060001722814500408830302a0305c0a28078126e0c0c0182e77028c81e040883030060b86c8a12078101818110182e290283c080c0c34c0c172ec041e040883030b8
|102=>0x8830306d0305cb4450903c080c0c0880c175c814cc0f0204418180305c520507810220c0c5242e290283c0811060613a060b814483207838220c0c0b40c45090141e0e02030302203016100f70810220c0c0182e5d028241e04088604c060b8f0ba2904810220c0c0182e0533010220c0c01946172d048a40f070441818030141e040883031670305c520507810220c
|103=>0xb914240f07010220c0c018f85d148481e0e0204418180306c52320204418180305c78be0283c0811060600c17028a01e040883030ca0305c0a28078102218608bc0c170283c0811060600c176e06c8a040883030340305c36d507810220c0c0182e05630241e0408830300002824081106062cc060b8141e270204418183b0182e29090a012040883030060b9141e04
|104=>0xb8141e040883030060befc0a0f020441818490000c170283c08110606262060bc041e040883030b30305c52d7078380811060600c171483c080c0c0880cbb0b8a4fa0f0204418183e05c52051583c1c040883030171d01412040883030060b86cc4040883030060b9740a280704418180305c5205140241c11060600c170204418181a1cc0c17378141e04088303000
|105=>0x883030f40305c0a7255010220c0c0182f13c18141e040883030060b8141e04aa84418180305c3612078641c11060600c6e028241c11060600c170283c080c0c08930060baf80a0f02030303d0305c52121403c1c11060600c1702890500f0204430650305c0a0f0204418180305f8088148141e040883030060b86c0a280c84418180305d1805330ad4e0f020441818
|106=>0xb8141e0e0204430260305c24051403c08110c0980c170d8a41eb40204418180305c0a0f1384418182b0182e3a0283c0811060600c170283c08110606138005185cba0507810220c0c3380c175f0481e040883030b30305c8a0507864220c0c1580017028a23011060600ca30b8e80a4407810220c0c0002e290283c0811060627017148481f1e08830300602e101e04
|107=>0x7810220c0c0000c1702890640f02044302f0306c52280704418180305cb41207810220c0c0a80c1780814a40f0883030850305c0a248303c0811060600c0507b1408110c0bc0c17028a01f1e0883030060b968240f0883030560305c0bc307810220c0c0182e120283c320e088303000458a40a0f0204418180305c0a0fe0810220c0c0182e1b028a05604088303006
|108=>0xc0bc0c170283c081106062e6060b814480f0204418180305c8a0507810220c0c2740c1702f181e040883030060b8a4240f02044181603014880f070441818368182e050789dcc1106061ee1702f141e040883030060b9140a3207810220c0c0182e450283c081106060ac060ba78740507810220c0c0182e0507810220c0c2fc00060b8141e330204418180005c0a23
|109=>0x1229c0811060600c17228141e040606044930305d3c050789c0811060600c17409bc520507810220c0c05c8a7d07810220c0c1f02e29091f41e040883030340b8a40a280789c220c0c05c0a2807810220c0b0182f010283c0811060611a060ba0452053e83c0811060602e051403c0811060600c17659a01e040883030060b8166a040883030730305c0a32078380811
|110=>0xb8141e040883030af0305c8fc80283c0811060600c1722814500f0204418180305c0a0f02045fa180305eae290283c0811060600c17028ac1e0408830303f0305c0a0f07044302f168182e29028901e04088605e060b8a5000f0204418180305c520507ba00811060600c1709014640f0c84418180305d3c051203c0811060600c172d814480f0704418180305c3605
|111=>0x120a008110c0bc60060b814380f0204418180305c0a32078102218178182e050d03c0811060600c171d014480f0204418180305c0a9107810220c0c0182e1b14810220c0c49c0c170903d6e040883030060b86cfa0f0204418180005c360519064220c0c0182e053903c1c11060600ca922815f60f0203030220305c3605920a00811060600c1702c7c1f1e088303006
|112=>0x305c0a241403c3211060600c1714b781e040883030060b9b80a2807810220c0c0000c17028a01e040883030060bb8c0a28390240811060600c170283c081106062e2060b8480a0f0c810220c0c0002e0507810220c0c0182eec028a01e0408830309d0305c0a28078102218178182e121203c1c0408830303f03014482808830302d180182e1b148a03211060602e05
|113=>0x60600dcb0b81412040883030730305cb40507ac4220c0c0182e051403dcc11060600c170d8141e0e020441818000182e051403c220c0c2700c175f0141e27020441818000182e0507810220c0c1700c17720141e040883030060b8a40a0f020441818578182e051203c1c040883030000305c520f07010220c0c1b40c170d8141e040883031100305c0a0fe50441818
|114=>0x2a9c1e190204418180005c0a0907810220c0c1b40c175c8480a2807810220c0c0182e12028a012040883030060b8141e190704418180005cba05290240811060600c170d914240f0204418180305c0a0f0204418180305ef005078102218178182e0507810220c0c4ac0c17028901ec50204418180305c0a3207810220c0c0182e0507810220c0c1580c170283c0811
|115=>0x14814480907810220c0c0182e05540a01e040883030060b814482807810220c0c0000c170d8166a040883030060b8141e0e088303006818a40a0f020441818778182e05120ac120f0204418180305c0a0fe6010220c0c0182e6f090141e040883030060b8144828020441818180182eb90283c1c040883030060b8a4247d07810220c0c05c8a050789c0811060600c17
|116=>0xc05c8a290283c08110606054060b8a40a0f0204418160305f9a0507810220c0c0182e1207810220c0c2e00c172e8480a0f07010220c0c0180a283903c1c11060600c17228480a0f0203030220305c0af307811cc11060600c172d114240f0204418180305c360519010220c0c0182e6e0283c0811060600c17681142405078380811060600c05078670c11060600c17
|117=>0xb8141eda020441818031f02e051403c32110606000173b8141e040883030062386c8a0f0204418180305c0a0f0204418185e8182e0507810220c0c7380c17028a00811060600ca30b914ee120283c0811060600c17c00141e040883030060b9dc240507810220c0c018b40507b140811060600c172d0481e0e08830300614814fa0f0204418180b8141e1907398220c
|118=>0x398182e290283c0811e80600c1702998880f0204418180305c0a28538240811060600c17029981e040883030000305c0a2804838220c0c0182e056b83c1c040883030060b86c0a09020441818168182e6f0283c0811060600c175c814500f0204418180305c780507810220c0c0182edf029c81e040883030060bb8c78450283c0811060600c17148179e04088303006
|119=>0x283c0811060600c1702f441e040883030060b8141e040883031920305c24051403c1c11060600c17228141e040606044060b8141e0e0204418181f8182e0507810220c0c01b4017228481e040883030063e05daa0507810220c0c0182e051403c0811060600c1723974521207810220c0c0182e050789c0811060611a060b8141ec50204418180005c0a0f070441818
|120=>0x2903c1c040883030060bf4c0a0f0204418180305c0a2807810220c0c41c0c1702910500f0204418180005fa40507810220c0c0182e45148141e040883030060b81412040883030300305c52051403c0811060600c17460a40a0f0204418180028c2e050789c081106060da060ba000a2807810220c0c0182ebe0283c0811060600c1702a9c1e0e0204418180305c8a77
|121=>0x305c0a0907810220c0c2700c170283c0811060600dd50b8141e0408830312a000182e4507810220c0c018f8170903c1c0408830306d03014500f0204418181f8182e5d1483c0811060600c170283c081106063a8060b8a40a0f0204418180025c0a0f8c010220c0c0000c171d014880f0204418180305e140507810220c0c4240c1702890500f02044302f0305e0205
|122=>0xb9742405078640811060600c170283c4e11060600cf70b8480a0f0c838220c0c0197c050789c1c040883030060b814e40f0204418180305d526e029101e040883030060b8141e19070441818032a4dc0507810220c0c0000c17090141e27020441818000182e1b0282408110606000060b9b80a0f0204418180305d180507810220c0c0182ee302d141e04088303000
|123=>0xc0182e5a9f03c0811060600c17028241e04088605e060b814480f020441818000182e05190241e040883030060b8480a0f020441818150182e050786408110606000a30b8a40a0f020441818168182e05078cc0811060600c170283d60b10204418180305c0af3078380811060600c172d03c1c1106060da060b9140a0f0204418182b0000c170d814500e088303006
|124=>0x883030060b9740a240483c0811060600c171e0a40a0f0204418180005c0a2804810220c0c0000c5a0903c08110606000060b9140a0f020441818033dc2e5b0283c220c0c2700c17808141e11060610a060b86c52040883030340305cb4052903c0811060600017090141e0e02044181800018ba05078640811060600c172d017080f0204418180305eb40507810220c
|125=>0x60600c17149dc0a0f0204418180005d0245090141e040883030060b914ee0507810220c0c0000c0507810220c0c3240c17eb0141e040883030060b9bc0a0907810220c0c0182e5a0283c1c110606000060b86c0a0f02398220c0c0182e053e8241e040883030060b9680a0907b140811060600c17028a01e270883030000305c0a66078380811060600c1714cf81e04
|126=>0x283c32040883030000b814480f0204418180340c0a0f0204418180305e720507810220c0c1540c173701450090204418180305e02051203c0811060600c17148141e040883031070bc040a0f13810220c0c0182e052203c081106060001702b5c1e040883030060b816480f91810220c0c0182e05078380811060600ca30ba000a0f0204418180305f22050483c0811
|127=>0x305c0a240483c3211060600c175c814482807810220c0c0182e290283f9411060600c178103c0811060600c1780814a40f0204418180305c74051403c0811060600c1702f081e040883030060bc080a0f0204418180305d025d0283c0811060600c17028a064090204418180316c240f0204418180305d02450283c0811060600c175c814480f07010220c0c0182e1b
|128=>0xc0182e8c0283dc3860204418180305c360514010220c0c0182ef50283c0811060610c060b9740a0f020441818168182e052903c0811060600c17df0a40a0f020441818003dc2e053103c0811060600c170283c0811060600c177f0480a52078380811060600c1714814640f0204418180305c367d07810220c0c0182e051403c0811a98600c17228141e04088303034
|129=>0x60600cf51d0141e040883030060b8141e190204418180305f720507810220c0c1ecda060b9740a0f020441818000182e290283c08110606000c43701412040883030060b814480907810220c0c019ea053329c1e040883030060b9dc0a0f07010220c0c0182e051403c0811060600c178e8f0520507810220c0c0182edf1481450090204418180305c0a2807864220c
|130=>0x30a40a09078380811060600c1702d0ce40f0204418180305c0a0f02044180b0305cb41207838220c0c0182e0507810220c0c019641702ea01e040883030060b8141e2702398220c0c0002e051203c0811060600c170283c0811060600d110b9140a0f0204418182b0182e1b148a00811060600c17028a2860f0204418180305c0a0f024dc18180305cb4050483c0811
|131=>0xba5c3605220a00811060600c170d81450190883030060ba880a0f0204418180328c2e0507810220c0c1cc0c17460a40a241403c0811060600c170d8a41e0e0204418180305c0a0f0262418180305c0a0f0204418180001998172e814120f020441818033d40a0f0204418180375c2e3a14814500f0204418180305c8a051403c0811060600c17229dc0a0f020441818
|132=>0x7810220c0c0182e1b0283c0811060600c176f8141e040883031090305c0a0f0204418180305f72120283c1c040883030060b814507207810220c0c0182e12029f41e040883030060b8141e190204418180005c0a3207810220c0c0182f010283c0811060600c1702cd41e040883030060b814500f02044302f0305c24052903c1c04088303006028a01e04088303006
|133=>0x305c360507810220c0c0000c170283c4e040883030000305c0a0907810220c0c019ea1b028a00811060600c17228a40a0f0204418180305c0a0f02044181800019461709014500f0204418180305c0a0f0204418185c0182e051403c0811060600c1754814a40f0204418180305dbe0507810220c0c1cc0c170283c0811060600c17df01450090204418180305c0a7d
|134=>0x60600c170294812040883030060b8154e0907810220c0c0182e29028a01e040883030060b8480a0907810220c0c0182e051203c1c040883030060b9b80a2807810220c0c0182e5b0283c0811060600c17148141e040883030060ba5c0a0f020441818428182e050483c1c040883030060b814120f0204418185c0182e0507810220c0c0182e472d0141e04088303000
|135=>0x305c0a5207810220c0c0182e1b0283c0811060600c170283c0811060600c1754814500f0204418180305c0a0f07010220c0c0182e1b0283c32040883030060b9680a5207810220c0c0182e05140c81e040883030060b8141e040883031100305c520507810220c0c0182e47090141e0e02044181803014480f0204418180305c0a0f0204418180305e06050789c0811
|136=>0xa0f020441818
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x3300006
|6,0=>0x33b8060700b2e0149c025b80447007ae00d9c017b802870042e0069c009b800c7
|7,0=>0x4c50096a01294024a80485008ea01194022a804450086a0109b820b80407007ee00f9c01eb803c70076e00ea381cc8038ae06f600dac01ad8034b0067600cac018e7030d005fa00bb4016e802cd0057a00ab4014e8028d004fa009b4012e8024d0047a008b4010e8020d003fa007b400ee801cd0037a006b400ce8018d002fa005b400ae8014d0027a004b4008e8010d001fa003b4006e8
|7,1=>0x8c3011660228c044980883010e60218c042980843010660208c04098080300fe601f8c03e9807c4e0f6a01e9403ca8078500eea01d9403aa8074500e6a01c94038a8070500dea01b94036a806c500d6a01a94034a8068500cea01994032a8064500c6a01894030a8060500bea0179402ea805c500b6a0169402ca8058500aea0159402aa8054500a6a01494028a80505009ea01394026a8
|7,2=>0x155a02a74054680a7d014da02974052680a3ee145e0287c0507809ff013de0277c04e7809bf013658268c04c980983012e60258c04a980943012660248c048980903011e60238c04698
|8,0=>0xf1701e0a43bcc877090ed101d7e43ab4874d90e8921cee43994872990e4121c5e4387c070690dfb21bd24375c86e290db321b424363c86be90d6b21ab24351c869a90d2321a22433fc867690cdb21992432dc865290c9321902431bc862e90c4b218724309c860a90c03217e242f7c85e690bbd0175642e6485c570b79216ce42d5485a280b332164242c4b858090aef215c1c2b3c855e9
|8,1=>0x1381226de44d7c09a69133b2265244c5c8982912f3225c244b44095f912ad2253644a24893b91265224a64490489179121f0241a447ec88f4911d72238e046d488d191191222fe445b488ad911492226e44494888a81105021e6443848868810bf2215a4426c884491079020ce44154882281033220424403c87fe90feb21fb243f1c87da90fa321f2243dfc87b690f5b21e9243ce407939
|8,2=>0x17eb22fb245f1c8bda917a322f2605e048bb79175d22e9645ce48b939171522e0645bc48b70816cf22d7a45aac8b4c9168722cea4598c8b289163f22c5a4586c8b04915f722bca4575b8ae2915b322b424563c8abf8156d22ab6455248a9b9152522a26454048a77914dd22996452e48a539149522906451c48a2f9144d22876450b38a0d9140b027f244f9c89eb813c52276644e9389c99
|8,3=>0x1c65238a6471048e1791c1d2381646fe48df391bd52378646ecc0dd091b8f236fa46dac8dac91b472366a46c8c8d8891aff235da46b6c8d6491ab72354a46a4c8d4091a6f234ba4692c8d1c91a272342a4680c8cf8919df2339a466ec8cd4919972330a465cc8cb09194f2327a464ac8c8c91907231ea4638c8c68918bf2315a462740c468187b230d24615c8c2291833230424603c8bfe9
|8,4=>0x20cd24176482a4904b92085240e64818490288203f2405a4806c900581ff923fce47f548fe191fb123f3e47e348fbd91f6923eae47d148f9991f2123e1e47bf48f7591ed923d95c7ae48f5391e9523d06479c48f2f91e4d23c76478a48f0c81e0903bee477948ee991dc123b5e476748ec771d7d23ad6475648ea391d3523a46474448e7f91cef039ba4732c8e5c91ca72392e072238e3b9
|8,5=>0x253f24a5a4946c9284924f7249ca4934c9261824b12493e49234923d92469248ae49114921a824232482248ffc91f6923db2479248edc91d2923932470248dbc91ae9234b2467248ca4118d72309245ee48b949169922c12455e48a7491468227b244d248964112392235244464884490ff921ed243b64872490db921a5243264860490b79215d24296484e490939211524206483c4906f9
|8,6=>0x29b72534e0a65494c192971252be4a534949d929292522e4a4149479928e12519e4a2f494568289b251124a1dc943292853250824a0bc940e9280b24ff249f9c93ea927c324f6249e7c93c69277b24ed249d5c93a29273324e4249c3c937e926eb24db249b1c935a926a324d2249a0413379265d24c9a098ec93149261724c0a497cc92f0925cf24b7a496ac92cc9258724aea4958c92a89
|8,7=>0x2e2525c264b80496f792ddf05b9e0b6f496d592d9925b0e4b5d496b192d5125a7e4b4b4968d92d09259ee4b394966992cc12595e4b274964592c79258ce4b154962192c312583e4b03495ff72bed257b64af2495db92ba5257264ae0495b792b5d256964ace4959482b172560a4abcc957092acf2557a4aaac954d82a8b054f24a99c952a92a43254660a8849507929fd253da0a76c94e49
|8,8=>0x32972650a4c9d41931932512647e4c8b4990d93209263f20c79c98ea931c3263624c67c98c69317b262d24c55c98a293133262424c43c987e930eb261b24c31c985a930a3261224c1fc98369305b260924c0dc981383015260064bfc497ef92fcd25f764beb397cd92f8925eee4bd9497a992f4305e624bc7c978692efb25dd24bb5c976292eb325d424ba3c973e92e6b25cb24b91c971b8
|8,9=>0x370506de64db849b67936bd26d564da649b439367526cc64d9449b1f9362d26c364d8249afb935e526ba64d7049ad79359d26b164d5f39ab59355926a8e4d4d49a928351326a024d3bc9a6e934cb269724d2a41a4b93485268e64d1849a279343f0685a4d06c9a04933f9067ce4cf5499e1933b12673e4ce3499bd93369266ae4cd14999a83323266260cc049977932dd2659a0caec99549
|8,10=>0x1d0b93a07073ea4e7941ce9939c12735e4e6749cc593979272ce4e5639ca3939352724a0e44c9c80938ef271ba4e3341c5d938a92712e4e2149c39938612709e4e0fc1c187381f2701a4dfec9bf4937d726f8a4decc9bd09379106efe4ddbc1bae9374b26e724dc9c9b8a9
|9,0=>0x3ecf47d768faa49f4b93e8347ce24f98b9f27a3e3b47c4e8f84d1effa3deb47bae8f70d1ed893d9d47b128f5d51eb0a3d4d47a728f4951e88a3cfd479d28f35c9e6293cb14793e4f23c1e3e93c6b278ae8f10d1e1893c1d478128efd51df193bd12777a8eeac9dcc93b87276ea4ed8c9da7a3b3b476524ec551d8283af1475c20eb3c9d5da3aa92752a8ea051d3793a5d274964e8ec1d149
|9,1=>0x438b286f250d9ca1aa943414865a90c6ca183a42f3485c250b44215ea42ab2852e90a1c2139a425f4849a508eca113a421528406507c4a0eea41c94836a9068520c6a417b282ce9054d209fa412d28232904152078a40dd48196502f3a0568409b2810e901cd202fa404b480725009ca009a3fff47fd68ff5d1fe293fb147f3e4fe349fbd93f6927eaa8fd051f96a3f1b27e124fbdc9f71a
|9,2=>0x484f490769209d2409a480128fda91f6523e2a47b508f4291e3ca3bda476748ea691cfd2395a471928e0e51bcd2370946cf28d7691a9d2349a467f48cd69195d2321a463128c3e51834a2fe845eb28bb25171522da845a328b1e915f4a2b59455928a8a914c5228f9450d289f29139ca269a44bf489569125d2241a446f488ba51125221c844254882290ff521f4a43d54878650ec4a1cea
|9,3=>0x4d0f499f69339d2669a4cc12995e5326d264494c75498ca1314ca61fa4c2d298329301525f8a4bdd4979292ed525d0a4b8d496f652da4a5ab94b470966692c7d2585a4af9295ca92b45256084aaf2953a52a25253b94a634949e928ed2513a4a13493fe927b4a4eca49c5493629267ca4c694979492ce52554a4a19492f4923a52425247b948e34919e922ed2453a48970910e121d4a4319
|9,4=>0x51d54a38dd46cd28cfa518b4a2ee9458d28a7a513b4a2525445ca881a50ef4a1ba54325285aa50a32a122541f52834a50554a086540c4a80f9500d29ff293f9ca7ea94fc149f5a93e6ca7c3a4f7529ec653d44a79f94f2b49e3253c152778a4edd49d9293adca75294e9329cfe939ad272ba4e4349c5e93874a704a4df549bc29373526dd94da929b2e5360d26b894d5d49a92934dca691a
|9,5=>0x56970ad0a559c52b2ea56494ac72158952b09956012abda957652ae2a55b32ab42556352abca55654aaa6554fd2a95a55192aa0a953ccaa6fa54cd2a976552a4aa4aa54832a8e2551842a279543b4a84e9504d29ffa53eb4a7b254f1529d8a539f2a71694ddd29b2953514a67a94cb4298d953074a5e694b7d2965a52b74a54a54a45293f9526d2a4b65491d2919a52230a41e947f4a8f4a
|9,6=>0x5b5b2b68e96ccd2d9095b0d4b5f296b952d68a5abd4b55296a5cad4295a714b4ba969252d1aa5a214b41a967e52cf4859d54b382966b52ccd959874b2ee16594aca8a593d4b25656464ac83958f52b1c2963352c5d958a74b12a5620cac37a585b4b08e960d4ac11958112affe55fb4abeca57c54af6295e7cabc69577b2aece95d5c2ba1a572f4ae3695c1d2b79a56df4ad9e15aed2b53a
|9,7=>0x60172c00a57fccafefa5fcb4bf7257ea42fcaa5f814beda97d652fa2a5f314be3a97c2caf7ba5ee34bd9e97aed2f53a5e970bd06979bd2f2f85e4b4bc725789caf09a5e012bbda9776caee495db54bb465763d2ebe95d694baae5750d2e9895d1d4ba16573e4ae7395cd52b986572bd2e4da5c892b8ea9718cae27a5c3d2b85657064ae02a5bf32b7be96f34addd95ba74b72a56e052db6a
|9,8=>0x64c14c95e5926d3245864792c8ce5914d32209642d4c83a1902531faa63e32c79e98ef4b1d5963974c70698dcc31afa634d2c67298c9cb18b863034c5de98b6d3164962b72c54e18a5c3142962732c4be9892d311c962272c42698804b0f6a61d94c392186dcb0d2961932c302585b530aca61454c2629847cb085a60f92c1ce5834d3060960af2c13698224b03aa60632c09e980f4b014a
|9,9=>0x69872d2ea5a58534a6a693b2d24e9a44d347fa68ed2d1b29a31cb45a968a14d11e5a1f4b434a68572d08e1a0d4b410a68110cffe59fad33eba67c52cf6299e7533c4a67772ceca59d4cb3a09672f2ce3699c1d337a966e14cd9a99aecb353a66934ccfe999ad332ba66434cc625987cb306965f94cbce5974d32dfa65ab4cb2e9960d32b89655d4ca96594dd3291a65112c9fa993a5326aa
|9,10=>0x6e414dc5a9b8653702a6df14dbba9b72536daa6da32db1e9b5f4b6b596d574da869b4bd368f86d0d2d9f29b39cb66a96cc14d95e5b27c3645a6c792d8ce5b14d361fa6c2b4d82e9b014b5f8a6bdf2d79a5aee535d2a6b932d7025adbcb5ae96b4b2d6725ac95358996aff4d5da5ab653562a6ab32d5425aa35353ca6a654d4a29a8fcb515a6a192d4121a7d534f1969cf4d37a5a6acb4cc9
|9,11=>0x38309704d4e0765c09d3809a70030dfde9bf74b7e596fb92df4a9be4cb7c096f6f2deba5bd2cb79c96f254de229bbfcb775a6ed92dd8a9bad43750a6e8d4dcf65b99d372a9
|10,0=>0x75314ea421d43cba7e974e76e9aa5d30cba589749d4e9129d1d53a30a744d4e8765d09d3a09a74012e7d6dcf5d39e0b73af2e73e1ce2d39bab73632e69e9cced3993a73152e6029cbb5396ca72c36e55e9ca74b944a72754e4c65c94c39209722d4e4365c824b8fb971e52e3a65c704b8d5b71992e306dc5c4b8af9714b4e26adc4853886a70fd0e1d29c35cb860b70ad4e1329c21cb839a
|10,1=>0x79fd4f3d29e75cbce1a79b12f33e5e62d3cbc979672f2aa5e5053c96a79194f20a9e3bdbc6e978c94f16a9e28cbc47a787d2f0cede14d3c1fa782b4f0325e0153bf8a77df2ef9a5dee53bd3977934ef025ddb53bad977474ee669dc7d3b86976fb2edd25db553b60a76ad4ed365da1d3b39a76612ec9a9d8e53b12a76114ebfe5d7ad3aec975c72eb6a5d68cbac89757f2ead2dd55cbaa29
|10,2=>0x7edd2fd965fae4bf52a7e914fcfe5f9ad3f2c97e472fc669f87d3f0697df94fbca9f73dbedda7da92fb2e5f60d3eb7a7d5b4fa8e9f4c5be8ea7d094f9ee5f385be66a7cbb2f94e9f24d3e4097c6f2f8ba5f1253e1aa7c214f81a9efecbdf497bd72f7869eebd3dcda7b874f6e69ed84bda6a7b394f64e5ec45bd7f97ae96f5ae5eb14bd57b7a9b4f50e9e9d4bd30a7a4b6f46e9e88d3d089
|10,3=>0x83af50732e0e1541ba883615069aa0cecc192b8311505fe60ba5c16aa82c51056660a84c1479827b504d26095cc121a82313043aa083440fca81e7303a6a06fd40d5a81993030e605cd40afa814b5026ea0485c086a80f9501caa0345405f980ab5012ea020d40389805f30092e00d54011980112fffa9ffa53fe9b7fc12ff621fe753fc4a7f772feca5fd453f9f97f2d2fe329fc0dbf77a
|10,4=>0x21094c208a83fd507d2a0f5cc1e1a
|11,0=>0x21e3d43bda876750eaa61d0543979871d30e1661be4c373986d350d7ea1aad434ba868350ce26197543259863750c46a1844c2fea85e950baaa170cc2d89859d50b12a15d542b19854f50a76a14a4c28b98505309e66137d4266984bb3094ea124d423fa846d308b661124c21b9
|12,0=>0x43f5987d930f8e61ed4c3d19
|13,0=>0x43fe8
|_,_=>0
def wAt:=mkWire dB 472 256 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 9 19
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 11 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 4000012 zs)
def oP:Nat→Nat
|0=>0x28110785d1501b2283f22847028010305d0c0ed0305d1d05c2d83d2d019028110283d02019120a41405d028190203d020ed0285d1d05c1e011290150303d079210291d1485e0785d22847028010c0ed1d05c0785d140a50203d148bf12033020250785d0c0ed1d05c148a1030151405d0785d020d11483f02819020261785f078be020250785d02001028190785d0203d0305d0285d08859060590602d0882d
|1=>0x1783f078390205d432151404b090130203d030110785d14114078110305d0305d0785d070190205d148a1028190203d0785d1485f0c85d020190308a228471485d07839088ed1d05c140a5078111485d1d0480285d0205d2d019028110785d2908a02801330330285d29039078190205d0882d22847020191485d3105d148a00201902819078110283d118150205d141140203d0285d0285d1d0380205d2d019
|2=>0x290150303d0903d0285d030113301b330332205d29011078190c85d030111485d1485f0205d0285d078a6030151401b0203d1485d1103f1101322847028010305d1d05c0285d08859060590c25d1485c02819088ed1d05c0285d148a1030150305d1203302025060591485e228a00280100011078110283d07839032310201914890078390205d0281907815060ed0785d1d05c370192d03d020151785f020be
|3=>0x203d0289e070190205d0785d02819000a0078110305d032c5022311405e028190203d140a7228471485d028190305d0c2b91a05c1483f02819032b1370032d03d028110305d54019022a907aa50285e330330229d078010305d4084714a99048a7030150785d2e819028250785d22847030490285d0785d062952205c29011078190285d0205d2d83d2d019028115101151815078020305d0285d0c2811e05c
|4=>0x205d0785d14019000110305d12033120170703d0205d0285d0305d0781102176048150785d0003f028010305d12033048114f06307af92d001028110288a11011228471485d030155d03337811031760903d0285d2e8175c83302175048150785d021490283a07819022e12e8170903d0285d5b033141f10203d028020305d4f047330150789d070190205d0283d020be120331405d0203d030a21485e03015
|5=>0x205d0785d120330783922847000150785d0205d2d11609019020150285d140a607811030150305d12033140191405d0781107b296485d140a60301508b1d228a21485d0203d0281902b1a02315048150785d03011078390205d020a61405d0781114ac503015023110785e0305d2205d1401907811148131405e078115c8330305d2d025020150785d0785d0201907811028010305d030be178191203307839
|6=>0x148a2028190203d0337902b7d0205e0635e079b50283a0205d02b715785e148a20203d22847021f1030490205d228471485d0204a6c0336b8193683d0283a0205d1e05e1483d6a84714b512d85e14811030150305d048150785d0203d03011020150205d2283f030490285d079160795922813028010305d0305d2d8242d019020150785d37019023413705e2d03d02015428190203d0204a408131482503015
|7=>0x72847148b502819020260785d1d05c14abd148a2028190203d02019120a41405d028190203d5f0470289d0283a0205d030251201b12033020250785d032c5022311405e0d85d07815030150203d030112e8135c81702175048150785d120170202502b15030260785d120331438d3905e1401b0203d1d05c140a5078111485d408132283d22811028010305d0285d14890028190205d0783a020be078390205d
|8=>0x70a50481b0285d030150785d0305d078ae03092020250785d023b11d05e148a103015078114081140847031750903d0285d12013120331405f1405d0203d0793e53815030250785d0903d0305d0285d0205d5d03337811031760903d0285d1105f0288a22847030490285d2283f030490285d07b3a148131405d0203d4f047032e52d025020150203d0785d1381b000110305d1101b1105f22847030490285d
|9=>0x22811e05c290150303d140a92283f030490285d02bc5032311405e14890078390205d0281907815078110285d0c25d1485c028194f01314891030151405d0203d1411607811090190285d0205d030491405d0201902819078110283d330330789d070190205d5f03f228110903d030490285d1404b078110285d0c25d228471485c1485d028195f01314bbd070a7028190205d4e8192b03f228131485d5f047
|10=>0x120330703d0205d0285d138135f0470289d070190205d7b017373d5140150203d0305e03025032e62d025020150785d07b990701b0205d120331405d0204a0285d0785d06325140a603015070190205d1485d030150205d062952205c290110781922847030110203d1485d030150785d0305d220172901107819031960789d070190205d6703f6703d428190204a0285d3105d148a0030150203d030110285d
|11=>0x3015148bf12033078390205d228472d85e14811030150785d063f93905c1401b0203d2683f53811030250785d0201954033142a5078110285e0285d1481102819078390205d02a952205c07865020190205d7d81b0788922847028010305d6b8193683d0283a0205d021761203304815020250785d7d015370022d03d028110305d5f0175f0472d85d2d019028112c013028ad078390205d2281b1485d02015
|12=>0x1441d0203d032a50285e030250785d020150205d0285d830331240f1405c1405d0203d0205d0203d000150305d0785d14891120331405d028190203d630330305d0231503026048a7030150785d0631a02315030260785d070190205d02c0d1405c078112285f0308a028010305d148900281904811120330d85d078110305d028190781503015031760903d0285d0481103015030260785d228133b85d1485f
|13=>0x140a6028191101b1105f030490285d02c4507c420337d0205e4f01b1d05d2d83d2d019028118685d2d8272d019020150785d468150203d0789e070190205d0303d12033048110785d0305d5c8170217502176048150785d1485e028a21485e078111205f120331203f020250785d408672283d030490285d0785d0305d148a10203d8504702c25033110785e02a353303f120191405d07811030110305d84033
|14=>0x6a84702c410337d0205e40847031750903d0285d408474081b53815078010305d0c0ed1d05c148a1028190203d468150789e0701914c511a05e1483f0281903092808190703d0205d120335c8338083d028390205d4f01b2e86503011048150785d22847030490285d2281b4084707915028010305d1404b030490285d0285d0205d1483d0281904811030490785d0285d89833141f50304a0285d063250285d
|15=>0x28110003f33033000a10305d07bb11d05e2201529011078194f0473301512019078390205d148a2028190203d4f05f40811031750903d0285d3b85d1485f028190305d0304a0785d0283d0285d048131785f020250785d0281902b15030260785d030490205d07849020150285d0228a0228d51815078020305d2d8901481102819078390205d03011141140203d030490285d1485d1d05f140a50203d02819
|16=>0x30250785d0785d9203307c8d023d50305e0c8a9030111485d030150785d1d05c29011078195c8178083d020490285d228113b85d1485f0301507c790285d0225d1485c030151401b2201502c752205e2901107819022ed2284703049088ed1d05c370192d03d02015088590305d0c25d1485c030151d05f1e05d1e011290150303d138170200122813028010305d600332d31503026020151d05f2d83d2d019
|17=>0x203d03049029c5120a71405d028190203d5c8333705d140150203d030111a05d1483f02819140a507811030150795e030fd020250785d0795a0305d1785f078be12033020250785d0205d0305d2d019020150285d120331203f1405d1405d0203d0285d5c8a702175048150785d028ae028ad1201b078390205d120330785d02801000110305d078110283d0285d02495070a4028190205d408470229d53815
|18=>0x140190203d2283d0788a028010305d408132e811031750903d0285d048110785d1485f02af211011228471485d030155104751815078020305d4581314a311405e02819030be12033048110785d0305d1101b1103f228471485d02819078490788a030490285d0294907819024ad024ae034a90903f0285d030ed1d05c290150303d060590305d0c25d1485c030155f0472283d22811028010305d0784914114
|19=>0x305d26047468150789e070190205d12033120a61405d0203d142311405e0203d13815330330789d070190205d12019120331201b078390205d8401b1441d0203d032a50285e63815141170203d1485d03015028925b01b141f10203d0305d5381b4083f53815030250785d030be140191405d07811028bd1781912033078390205d0340d0785d1405c028190203d0785d1905d1405f0203d02c75028a12205e
|20=>0x1485c0203d028194f0635f03d0289d000110305d030150283a070190205d0285d078a6030151401b0203d228473b85d1485f028191203f1405f1405d078119b04714cd507b7d0205e14a752b03f228131485d028190283a030156303302315030260785d77819070a70205d078110785d22813028010305d064c51489302819078392283f228471485d0281922a5f228471485c1485d0281907afa2d00102811
|21=>0x30495c83307c05020490285d02949078190285d020d10205d1483f028190205d5104751815078020305d228130208922847030490285d12017020250785d023b9034ed090a30285d0203d028260785d0205d0285d0305d08a952205c29011078194f0171d05d2d83d2d01902811110170208922847030490285d034e51e05e1483d028190283d0311d1485e030150303d0785d2d001028110305d08a5d0305d
|22=>0x14891030151405d0283d020250785d120333303f120191405d0781122847028010305d12033020250785d1401b028190205d0285d078a52283f1485d03015028190305d0785d14017078114f04714115078111485d0785d0c85d0285d0301502019000110305d228473b85d1485f0301512017120331483f028191405da0047034fd024fa02b110785e1d05c140a507811030150785d1d0000305d140a507811
|23=>0x203d2d0260785d020150205d0285d1d05f2201529011078190781103015031760903d0285d1405d0201902819078110283d2783f02a9d030250785d5c8175c83302175048150785d0283a02d0e3905d0285d1401b0203d064c514893030151405d028190785d0203d0305d0285d0205d0203d078020305d6b833031b53683d0205d1d05c0205d290110781967047032155c8335c8138083d020490285d4f063
|24=>0x205d5383f12033030250785d0305d29011028250303d0785d0035d0305d3683d0283a0205d0481502025030150305d0785d9885d1489303015020250785d1386f020010305d408471e05d290150303d060ed1d05c140a50203d4083f40847031750903d0285d0791d140a51485e0203d028195d0333781103176048151203307815048110785d0285d078110205d07849030150285d1405f120131203f1405d
|25=>0x781122017290110303d1485d1203304811078020305d028110285d0205d0c86d030110305d078150785d0205d5cbd70305e2d025020150209a5c8338083d028390205d37019032e63705d2d03d020151785f020be12033078390205d22847028010305d048150785d2d83d033512d85e2d0190281102bb11d05e1e011290150303d4f0330299929039078191483f033ee1103d22847028010305d079b50283a
|26=>0x203d4e05d148130301512033020250785d072972205c07865020190205d12033020250785d140a61405d078110481102541048a6030150785d0285d063251a0131483f028195f0472d001028110305d148a31405e0203d141230291d1485e0203d14811408132283d1485d0301502d0da18173905d1401b0203d0703d0205d330330703f12019078390205d1d0380205d29011078192081117817120331405d
|27=>0x7af92d001028110305d02d610285d190191405f0203d0785d5101b02a8d078020305d1405d2283f030490285d140a50203d028190285d070170205d1401b0203d22847028010305d1203314827020250785d0c0ed1d05c2d83d2d019028110781104a730785d1481303015020be1783f078390205d4e03d14813030151201b0305d020250305d0204a070190205d0640d1405c078111401512033120171405d
|28=>0x2205e140190203d22847020191485d078110283d0211d1485e02819ad8331411d1485e028191d090148a1030151405d67047428190204a0285d07b796a83f0337902b7d0205e1101b22847228171485d03015140000305d0785d0203d03011078110003f14813078110204a0903d0285d1203307019078390205d2201529011078190209a5c833120151405d0203d0281912033030391201b078390205d4f05f
|29=>0x2001028190305d0205d029c90285d1401b0203d228175f047228111485d028190285d140190205d078110283d020150303d0785d0205d0285d5c8135c833120151405d0203d03039078390205d120331203f1405d3303314001078110305d0305d0205d9885d120a61405d028190203d023e9370022d03d028110305d2d83d2d0190281114ce51e05e1483d028195f0475f01380819028390205d37475028a1
|30=>0x2d85e148110301502819120330703d0205d0285d02b3a67047032150285d031750903d0285d2b01722847030490285d22811028010305d029d91386f07815000110305d020be028be078390205dac85d1483b030150205d0205d030490285d2783f1e05d290150303d0785d5104751815078020305d090a20203d0285d12033078390205d228131485d030150283a0205d1781712033020250785d13a5f1485c
|31=>0x48110305d1e013290150303d4584714a311405e028194f0632e86503011048150785d1d05c0285d148a103015408130229d53815030250785d4f05f032e58083d020490285d024e1034e51e05e1483d0281953811030250785d0c2952205c290110303d0785d095610285d190191405f0203d1485d6a84702c410337d0205e2d01902811030390205d0c40d1405c0203d145852204a140190203d0285d03351
|32=>0x30150003f22847028010305d62811030260785d4001902a311405e0203d032e62d025020150785d0334a2b03d228131485d0281907c8d023d50305e5f0135f04703405028390205d0289e000115c81902175048150785d0204a0285d0283a0205d035a11e03a1483d028190205d408112283d030490285d5f0175f01380819028390205d120331905d1405f0203d5383f3301b53811078010305d0301512033
|33=>0x78110785d120a61405d078115f04722811028010305d228470901b22817030490285d2e8135c83302175048150785d078be1405f1405d078114f0632e86503011048150785d070190740f1405c078110205d1485f670170205d032150204a0285d0785d0205d030110285d22015290110303d0308a22847030490283d0285d0205d7101707a150204a0285d228471101309019020490285d14b512d85e14811
|34=>0x3215078110204a0285d0285d0205d2d83f2d01902811228473b85d1485f0301514bbd070a7028190205dad8335a03d0211d1485e028191405e02019078110283d2d83d2d01902811021160283d078111485d028191781512033020250785d120a6142311405e028190203d370192d03d028111101b0288a228471485d028194f0332e86503011048150785d141160283d1485d028191483f0205d0281914017
|35=>0x1405d078114305d090a20203d0785d1d05c370192d03d020154f0332e86503011048150785d5f06f2d85d148110281907815408135381504811030250785d0285d6301762811030260785d02da11e03a29015078190205d510470785d02a8d078020305d0285d020a5030150305d0205d67047428190204a0285d2916907819028110285d0205d5f0470289d000110305d088ed1d05c140a50203d0281908b3a
|36=>0x785d5f0475f01722811028010305d1d05c0305d29011078190313e408472283d030490285d1d0000305d2901107819228a21485d0203d028190205d1485fb40151e03a1483d028190205d141df078111485f03015020f60289d000110305d08abd140a71485e02819030260285d148a202819120333303f12019078390205d142a5078110285e0602d0882d0c40d1405c0203d2284722847000150305d12033
|37=>0xc5e13705c2d03d0201517c0f120331405c1405d0203d078150785d2281b028010305d4f0633301512019078390205d048a61d05f22015290110781902dd922048290110303d0285d5c8330305e2d02502015ac9b51483b07017028190205d4e03f148130301502a9d1203304811030250785d12033065d5148cb028191405f0203d020d11483f0281909019120330703d0205d0285d3303f120330309102025
|38=>0x78020305d148a00201902819078110283d1405f0201902819078110283d148bd0281912033078390205d0788a1101322847028010305d430191404b0203d0305d0285d22a5f228471485c1485d02819120131785f12033078390205d4f05f2e86503011048150785d0285d030150785d0301102c410337d0205e1201b12017020250785d0285d1383f03039028110205d1254f1405d0640d1405c0203d0285d
|39=>0x289204815020250785d07b990303a078110205d6703f032150204a0285d020a5030150305d0205d020190205d0281907815030110203d07aa50285e120330703d0205d0285d6303362811030260785d0301503026078150785d1485f228172281b1485d028190283d228470304983033192311405e1405f0203d1411402019078110305d070190205d048131203f020250785d4f04714891030151405d02a8d
|40=>0x204a0285d330330229d078010305d3905d031c91401b0203d0205d0301502019a805d048a6030150785d0285d0203d14813030151381703039028110205d07c1e0203d032a50285e035f94e05e1481303015143d5140150203d0305e1483d0481b030150785d5396b07801028110305d2284722813028010305d40847031750903d0285d2283f030490285d07815090a00203d0285d0311d148111485e02819
|41=>0x78190205d030110283d078390205d1781b12033020250785d1d05d220152901107819028190283d000130305d330332205d29011078191400307811028010305d8504702c25033110785e14000078110785d0305d024e51e05e290150303d032c5022311405e078112281309019020150285d020191201b1405d078114305d190171405f0781107af92d001028110305d2d0920703d028110205d0321507811
|42=>0x640d1405c07811120a41405d028190203d0001502001078190305d2e817021750903d0285d0215902116030490285d5f01722811028010305d54033022a907aa50285e070a7028190205d2b03f02116030490285d4084753815030250785d0785d140150203d0305e0785d0205d1401b0203d02019030151405d0203d078a503015000130305d0785d0289e000110305d408472283d030490285d0283a29039
|43=>0x22847020191485d028190217502176048150785d030490785d0283d0285d148c1030150783a0205d078be120331405d078110305d2d03d020150305d02b15030260785d180190785d0783a0205d0295a02116030490285d078492283f030490285d40847031750903d0285d12033120191405d07811a803d048a6030150785d03215078110204a0285d14a311405e028190203d40813031750903d0285d0205d
|44=>0x785d0c40d1405c078116a84702c410337d0205e079f5078110304a0285d6703f428190204a0285d0205d148a2028190203d0301507a150204a0285d2281b2283f1485d030154083f53815030250785d0db99078150701b0205d0785d1483d1485d0301507b790337902b7d0205e02bce07b990701b0205d2283f2283d030490285d5f017228111485d028195101351815078020305d0305d0785d0203d03011
|45=>0x361d07e1a022a50285e0204a0205d0283d0285d5f03f0289d000110305d0481b03015020250785d02175031760903d0285d4083f031750903d0285d1405f0703f078110205d0203d02e1107bd50305e07b512d85e14811030150337d1483d030150205e03011032311405e07811149b5030150283a0205d1205f12033078390205d120330703d028390205d0220653815030250785d07811020190903d0285d
|46=>0x78155101151815078020305d0205d0785d14017078110203d02116030490285d078150205e030490285d0200222847028010305d035e33705c2d03d020150003f0203d0305d0285d6703f428190204a0285d3705e370192d03d02015120331905d1405f0203d078a5048a5030150785d468150789e070190205d08c0d1405c028190203d228133b85d1485f030154e05d14813030155104702a8d078020305d
|47=>0x305d4081b1e05d290150303d028392905d078190205d07e354e05c14813030152281300015078010305d1381b0789d070190205d048190785d14017078111404b0203d0305d0285d03011078110285d0305d030490784a0283d0285d120331405c1405d0203d030260785d0205d0285d0285d078151405f078110205d22813028010305d1d05c2d83d2d019028111203312017020250785d0205d0305d02819
|48=>0x28110205d078152d85e14811030156303f02315030260785d0364616815020260785d0363d3985e14017078110280107802030110305d0785d140a60203d028190795a22813028010305d023413705e2d03d02015020150285d030260785d1203304811030250785d1411f1485e0203d0205d0204a0303d0285d2284707815028010305d0283d030111405d0781167047032150204a0285d079592281302801
|49=>0x1485d028198c0150228d078020305d1105f22847030490285d02019000150305d0785d0c85d03011048150785d02801048110785d0305d0205d2283f030490285d028110204a0303d0285d034ed07a160204a0285da903f4e05d14813030150301107e1a022a50285e1e05c0306d078150785d0215922813028010305dca0152205f29011078193303f03091020250785d0602d0c40d1405c0203d1396b03039
|50=>0x28190305d2283f22811028010305d030a1078110785d0305d368190785d0283a0205d0c65d3985c1401707811028ad1201b078390205d0304a2285f030490285d1105f22847030490285d030fd12017020250785d0781107017028190205d034058083d020490285d2283d00011028010305d02819031760903d0285d18017030150783a0205d228472283f030490285d0288a22847030490285d2281702019
|51=>0x203d0785d120331205f078390205d0205d290490303d0285d0481312033020250785d0d85d14019078110283d22847000150305d0205d120130703d028390205d67047428190204a0285d0903f0285d048170785d0204a0285d0283a0205d1a37d0205e1483f028191483d0281907b7d0205e0903d0203d0305d0285d228470205e030490285d021bd031760903d0285d5381504811030250785d1485c02001
|52=>0x20490285d228472283d030490285d3301b0229d078010305d020150205d030260785d2e81907849020150285d22015290110303d0785d3b85d0283d1485f028191d05c2d83d2d01902811228470903d030490285d0285d030150205d0785d0781122813028010305d0304a0285d0305d0785d8504702c25033110785e2a85d220172901107819cd05e3981914017078112d8272d019020150785d1401504813
|53=>0x28010305d14b7f0283d030150205e033512d85e2d0190281109013028190285d0205d062811e05c290150303d1383d02001028190305d0281902175048150785d030be12033020250785d0305d03176048150785d12033140171405d0203d3301b2205d29011078191e05c0306d0283d0285d0291d1485e148130301567047428190204a0285d222a514019078110285e0205d0203d078020305d032e58083d
|54=>0x30490285dcf01502426033110785e1481103015023110785e5983d0289e000110305d2e86702825030110785d000170305d0304a0285d54033022a907aa50285e0901322847030490285d1105f22847030490285d0305d2e83f048150785d070190205d0283d0285d5f04702115030490285d0285d190191405f0203d14ac503015023110785e0283d090a10203d0285d0481712033020250785d0781100011
|55=>0x2d001028110305d0785d14015140190203d07b990701b0205d14b512d85e1481103015024ae034a90903f0285d078490784a030150285d1483f1405e03015078110241e0311d1485e028190331114811028190785e030490203d0205d0285d000d30305d1483f028190283d03015020250785d028190205e0903d0285d2d03d020150305d0785d028190789e070190205d028fd120171405d0203d1105f22847
|56=>0x120331203f020250785d3d813031b50283a0205d228470785d1485d03015070d10205d1483f0281903231140151405e0203d2e813028250303d0785d85013034f902b110785e1101b22847030490285d02689048a4030150785d0301112015020250785d2d826148110785d0208a22847028010305d5f03f228111485d0281902b1562811030260785d228473b85d1485f028192284707811028010305d5f047
|57=>0x305d1203f1401b1405d0781107e3d3985e14017078110211d148111485e028190205d0285d1483f02819228472283d030490285d5c83312015020250785d14cd70281907b7d0205e0783a0305d020190205d0785d1401b0203d0285d120171405d0203d1d05f2d83d2d0190281107815148111485d02819034a9030110903f0285d228470903d030490285d120131205f078390205d14bbd070a7028190205d
|58=>0x285d148a11405e028190203d0305d140a507811030150305e2d025020150785d0901322817030490285d468150789e000110305d1386f0283d070190205d5f04722811028010305d1a05d0205d1483f02819030150204a0903d0285d028190283a070190205d0311d1485e0781103015078012d001028110305d2d42602811033110785e06325140a60203d028190481503092020250785d5101b02a8d07802
|59=>0x31b50283a0205d0785d428190204a0285d02825030150305d0785d330332205d290110781914811028190285d0205d0301103015023110785e370022d03d028110305d0285d140190203d330330229d078010305d2d85c2d019020150285d070170303d0205d0285d14827028190203d0785d1425d1485c0203d02819140150203d0285d0285d0225d1485c03015120331905d1405f0203d078892284703049
|60=>0x2001078190305d02819000a2078110305d030111201b078390205d1d05f2d83d2d01902811020150303d0305d0785d228471483f1485d0301502bdd13813070190205d5c833021750903d0285d3303329039078190205d03011048a7030150785d291b50283a078190205d0c5e13705c2d03d0201502ea1143d70203d0305e2283f090190285d0785d22847148111485d028190205d22015290110781907839
|61=>0x2d85f2d01902811222a714019078110285e078151405e03015078110305d03011020250785d5f03d0289d000110305d2d03d0305e020150785d020250785d030150201922048290110303d0285d4084753815078010305d0205d078190785d0305d028010283d030110305d0785d0340d1405c0203d0305d028190903f0285d5101151815078020305d6a84714b7d030150205e0305d14019078110283d29015
|62=>0x1485d03015000110285d0305d0785d85013034f902b110785e0703f1205f078390205d5c813120151405d0203d1a0110285d1483f02819024ed090a30203d0285d02819021760903d0285d120130283d078390205d2d83d2d0190281157815148a203015078111103d22847030490285d02819000110285d0305d0201912017020250785d2d03d028110205d4001902a311405e0203d120330283d1405d0203d
|63=>0x2d03d02015390260785d1401b0203d2d6c12905e028110781914117078111485d028190925f1485c030150285d0903d0285d0301502019140a7078111485d028195f04780819028390205d078a5028190285d0205d0285d0205d1401b0203d22817148111485d028190205d0285d03015020190203d2e8170903d0285d078190305d0285d0205d02bfb3905c1401b0203d6b8333683d0283a0205d078112283f
|64=>0x28010305d04815048130203d0785d3301b0789d000110305d000150289e000110305d0283d120171405d0203d0285d02015078190305d14891030151405d0203d5c81b8083d028390205d0203d02176048150785d2284702801030110305d33033120191405d07811020020305d0285d0205d0285d030151401b0203d0220602a9d030250785d020be12033078390205d070171201b078390205d035e13705c
|65=>0x30110305d08e5d3985c140170781112033030151405d0203d1201b140191405d07811090110285d078020305d3d83f031b50283a0205d1201b048110785d0305d030a2078111483f028191485f030150283a0205d14114078111485d02819120331201b1405d078110025f0305d1485c028192d03d02811023d50305e148110285d14813030155c83302175048150785d0304a2283f030490285d0785e22813
|66=>0x301502019290110003f078190305d0305d04815020250785d021f122817030490285d2283f22847028010305d120130283d1405d0203d0205d020191485d028190283d032150204a0285d5801702425033110785e020d10205d1483f028191101122847030490285d0791d1485e0203d028191483d0285d028190305d1103f228471485d028195401b142a5078110285e02819048110785d0305d028010785d
|67=>0x28190205d079210291d1485e0301502819078110785d0305d0303d22847028010305d02b7d0205e1483f028195c8133705d2d03d020150001502802030110305d078ae03092020250785d028190305d0285d0205d07b8d3905e1401b0203d0205d02015078190305d030150205d1401b0203d0205d020190903d0285d1d05c2d83d2d0190281129011078190785d0305d0201902c25033110785e1e05d1483d
|68=>0xd85e0283d5f01780819028390205d12033140151405d0203d0203d02001028190305d0283d12033020250785d0785d0283d030110305d0311d1483d1485e030150dee1078150c85e0201903015034a90903f0285d22017290110303d0785d0201907a311405e0203d1a0130285d1483f028191489302819078390205d1203312015020250785d0781102e1207bd50305e1201b12019078390205d1483b07017
|69=>0x2116030490285d2d05d028110303d0785d07bbd070a7028190205d1405d0640d1405c0203d330170789d070190205d120191203f020250785d192311405e1405f0203d0703d0285e070190205d0285d3683d0283a0205d140150785d14017078111383d0289d000110305d0283d2283f030490285d120330703d0205d0285d1105f22847028010305d0283d02819020260785d2d8272d01902015026e503011
|70=>0x1485e1481303015020190785d1401b0203d468150789e070190205d14813030151405d0203d148b702819020260785d063254e03f14813030156a83d0337902b7d0205e5f03f22811028010305d000110305d078110283d0481312015020250785d0285d0283d030110305d1485d028190785d0205d0283d02116030490285d020a5228131485d028191485d02819030260785d148110305d02819078152b03d
|71=>0x20190703d0205d0305d120330703d0205d0285d0285d148a10301507811148c9028191405f0203d1425d1485c0203d0281914839028190785d0205d03015090a00203d0285d120330285e078390205d0306d020490283d0285d0241d0203d032a50285e1e05e290150303d078650205d030110305d028a10203d078020305d22847228171485d03015148112283f1485d03015020a92283f030490285d4e11d
|72=>0x785d1d05e140a50203d0283d0205d030110305d0285d1485c0781103015022a514019078110285e2283d3b85d1485f028190205d220172901107819028920703d028390205d03219090a20203d0285d08a5d0285d1485c0301585047034f902b110785e07b8d3905e1401b0203d091c90285d1401b0203d141210781102bd50305e1d05f2d83d2d019028112d85d2d83d2d01902811022061e05d290150303d
|73=>0x20250785d1a05d1483f028193985c0205d14017078110285d030151405f078110703d020150205d0285d120331205f078390205d9d83d090a30203d0285d02ded090a00203d0285d0200107815028010305d33033120191405d078110701503039078110205d5785d3981b14017078110285d03039028110205d065e13705c2d03d02015060590c25d1485c028194e05d0203d14813030151405f0205d0203d
|74=>0x205d14017078112e86503011048150785d0481b0785d0283a0205d290150303d0305d0785d036f92d05e0303d020156b8193683d0283a0205d0481103176048150785d02b150305d030260785d2281322817030490285d1405d0c40d1405c0203d1e05e1483d028190203d07815028010305d141f5078110304a0285d54019022a907aa50285e0785d07916028010305d2d019028110785d0305d1201b03011
|75=>0x205d1d05c140a50203d028190281912033078390205d020490285d0305d0785d0785d22813028010305d03405020490283d0285d228a21485d0203d028192284700011028010305d0203d0305d0701b0205d0203d2283f030490285d08a5d1485c0203d028191485f1405f0283d22847030490285d6a84714b7d030150205e2e81707849020490285d020190785d0205d0285d1203303091020250785d07019
|76=>0x305d02315030260785d0785d1e013290150303d070190205d02819078110785d0285d1485d030150283a0205d0281122847030490285d1201512019078390205d033512d85e14811030152b03f228131485d02819120131205f078390205d22847090190285d0205d7083d03619022a50285e5c83302175048150785d1483d048150785d0789d07802000110305d07819028110285d0205d03655180170783a
|77=>0x30151201b078390205d22015290110303d0785d148a002819078110283d0d85d0205d078110283d07811028190785d0205d14017078111483f028190305d031760903d0285d0205d22817030490285d0205d07849030150285d02819078151405f07811228111483d1485d030156485d140a60203d0281917819120331405d0203d5785e3981b14017078110283d1483f1485d030150283d02c410337d0205e
|78=>0x785d2d03d028110205d1101322847028010305d5f0470289d000110305d028190203d0205d0285d33033120191405d07811b305e1e013290150303d1d05f140a50203d028191405e02019078110283d3301b53811078010305d3105e148a0028190203d07afa2d001028110305d120a61405d028190203d5f01780819028390205d02819079b50283a0205d0288a228471485d02819228172281b1485d02819
|79=>0x285d0283d0211d1485e028195f0130289d000110305d14abd148a2028190203d0003f0305d1481303015032150204a0903d0285d5f01780819020490285d0201922813028010305d0228d0203d078020305d0305d2901107819034e51e05e1483d028190285d0225d1485c02819920170261107bd50305e07aa50285e1401b0203d0260d3e83d0304a0285d04a730785d14813030150283d0285d020190205d
|80=>0x28191411407811028010305d120331405f1405d0203d028190205d078110283d028112283f030490285d090110204a0303d0285d1240f1405c1405d0203d0481b12033020250785d0225d1485c0203d028190201502116030490285d02711032aa07aa50285e0285d0305d020190205d14a31030151405e0203de101b07ef92d05e02811078151201b1405d078115c8338083d028390205d5c833090a10203d
|81=>0x281902a952205c290110781907a311405e1401707811120331205f078390205d141df0203d1485f028191438d3905e1401b0203d0795a22813028010305d07f1d2401302bd50305e0285d0c25d1485c03015290110283a078190205d020021381b000110305d1425f1485c0203d028191485d028191405f0203d228133b85d1485f030151d05d2d83d2d019028110305d02176048150785d1a0110305d1483f
|82=>0x203d0281902a311405e0203d150112283f1485d030150285d020191405f0203d3301512019078390205d1481102819078390205d0781504811030250785d1105f22847030490285d5f03d0289d000110305d4081b2283d1485d030150901b22817030490285d0304a0285d1483f028190c85d030150203d030110203d0c25d1485c02819070150789e070190205d2281b2283d1485d030156485e140a60203d
|83=>0x28191a05d0283d1483f02819022e10285d048170785d2281b07815028010305d02019078151405f078110285e0205d1401b0203d0788922847028010305d143d5078150203d0305e8f03d0225d1485c03015140a71485e0203d02819e481553813078010305d1491d1485e0203d02819063f93905c1401b0203d148c9028191405f0203d1201b12017020250785d1203312013078390205d120331405d02819
|84=>0x301502b7d0205e14015078110305d3905e1401b0203d0785d1401b0203d3985d14017078110285d030110305d1d05e2d83d2d01902811228a31485d02819120331905d1405f0203d120170703d0205d0285d120131203f1405d0203d0201902819078110283d120331203f1405d0203d3105d148a0028190203d1405f120331405d0203d120a41405d028190203d148a1030151405d0203d1411f078111485e
|85=>0x285d3705c2d03d0201512033078390205d034a90903f0285d03026020250785d1440f1405c0203d22813028010305d02c26033110785e0785d140170781102015023110785e0203d0701b0205d078150305d0205d0203d14813030150289d000110305d3e83f0304a0285d02b15030260785d148a2028190203d0703d0205d0305d07017028190205d0283d0337d0205e0225f1485c03015030111405d07811
|86=>0x285d0205d03011022a50285e03015020250785d142a5078110285e0305d1405d078110283d07b7d0205e1405c078110205d070a7028190205d03092020250785d9a81b07b7d0205e031760903d0285d1203f1405d0203d8083d028390205d0901b030150285d00011028010305d07801030110305d0785d0283a0205d090a10203d0285d078110785d0285d0205d030110305d028250303d0785d030490283d
|87=>0x180190783a0205d8083f020490285d0203d078020305d2285f030490285d3b83d1485f028192285f030490285d02811030260785d028110285d0205d2281b1485d028190303a020190205d2283f1485d030150c25d1485c0281902c8d023d50305e0285d048170785d0903d0205d0285d0205d1401b0203d22847030490285d07b990701b0205d09019020150285d078151405f078113705e2d03d0201509019
|88=>0x281907849030150285d0789e070190205d0305d030260785d0205d14017078110625d1485c028192205d290110781907811030250785d0229d078010305d0205d0203d0785d079b50283a0205d02026078150785d031760903d0285d120151405d0203d1483d030150205e3905e1401b0203d1483d1485d0301507a5d1485c030153e011028020305d07811030110305d1485e1485f02819030490283d0285d
|89=>0x290150303d0203d032a50285e030a1078110305d730150701b0205d3b85d1485f028190785d0783a0205d1405e028190203d0003f028190305d0283a070190205d02a311405e0203d0289d000110305d2905d078190205d1485f1485d028193e03d028020305d07c8e023d50305e0203d0205d0285d22847030490285d02892078390205d0241e032a50285e22817030490285d02c410337d0205e078111485e
|90=>0x285e020190205d2d03d028110305d000110285d0305d0305d078150785d140151405e0203d3905e1401b0203d000a2078110305d0785d14813030153e03f028020305d0305d0903f0285d3e015028020305d070170205d0285d120171405d0203d03015048150785d07b7a02b7d0205e0305d1485c028190228d078020305d22015290110781902c25033110785e120331405d0203d0303d028390205d1e05f
|91=>0x785d0201507bd50305e07b7902b7d0205e0201502b110785e12033020250785d048110785d0305d1205f020250785d2283f030490285d07802030110305d02819020260785d1a0111483f02819032c5023110785e07b990701b0205d07017028110205d22813028010305d0205d078110283d07849020190285d13813000110305d0285d020190205d0289d070190205d0285e1401b0203d140191401507811
|92=>0x28010305d4e03f148130301502ee10c85e0201903176048150785d0305d028110205d078150701b0205d0785d0304a0285d03026020150785d00011078110305d29039078190205d0301502b110785e04815020250785d1483d028190305d078110785d0305d0305d020150285d00013028010305d022711481303015022150204a0285d0283d1483f0281902015078190305d0305d0285d0205d0301104815
|93=>0x31750903d0285d0785d1405f078112d019020150285d2283d030490285d02891078390205d0283d030110305d1405c1405d0203d1e05e290150303d220172901107819028a10203d0785d0703d028390205d0311d1485e0281903039028390205d07865030110305d3683d0283a0205d07c8d023d50305e0205d078020305d02a311405e0203d16815020260785d0305d1485f030152283d030490285d2285f
|94=>0x301103619022a50285e078150203d0305e190171405f0781104815020260785d2d05e0303d0201502002028190305d148a0028190203d3905c1401b0203d078190285d0205d028191405f0203d0304a0283d0285d0640d1405c0203d1483f1485d0301503011020250785d120151405d0203d0225f1485c0281902c0d1405c07811020490303d0285d148a1028190203d07ef92d05e0281102c0d1405c07811
|95=>0x203d0305e1381b000110305d1905d1405f0203d07c420337d0205e22813028010305d02819078110283d3905d1401b0203d08a5d1485c028190305e020150785d2d83d2d01902811020190d85e07815031b50283a0205d0305d0903d0285d0305d028190785e0206d078150785d0305e020250785d53811078010305d0205d1485f030152205e140190203d1483d030150205e028190203d0785d1405e0203d
|96=>0x120331405d0203d078190285d0205d1485c0203d0281914019078110283d02019078110283d51815078020305d1405e1401707811030151405d0203d0205d028190781508c0d1405c0203d2d002028110305d0305e048150785d0228e078020305d148a1028190203d1485d0203d028191485f1485d02819028190785d0205d3905d1401b0203d0c40d1405c0203d028110285d0205d000a0078110305d143d7
|97=>0x14015078112d019028111485c028190204a0285d0785d0205d048170785d1485e02819028110305d078150305d000110305d0305e0785d078110283d1485d02819078020305d0203d0285d048170785d078110285e0303d0205e14017078112d05e020150203d0785d0304a0285d0283d0205e033110785e0d85e078150285d0205d1401b0203d0304a0285d030110305d1405f0203d028390205d07b7d0205e
|98=>0x7819078150285e0203d0205d020190781502811078191405f0203d0337d0205e1485e028190285d0205d078390205d1405c0203d070190205d0303d0785d030250785d028190203d0285d0785d078390205d
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x2200010000000000000
|7,0=>0xc0a05b502c1814d4000000000290813cc092c0000022280fd40000000001cb00000066c0000016b00000000000000000000000000027600000000000000000000000000000000000000000000486021300e2800000308000000000000000000000009a800000000000000000000002420000007980000014a000000230000000000000
|7,1=>0x4a8800000000090500000000000000000000000000000008f1047082218000000000413000000000000003ea8000000000794000000000000000000000000000000000003a281c88000000000000000000e0406d300000000000000000000000000000006c1035881a480cc60000000001944000000000000000000000000000000000000000000
|7,2=>0x16840000000002cc400000b2105630000000000ab100000000014ca00000528827d8000000000000026940000000000000000012e6000000000000000000961
|8,0=>0xcfa8669432aa19050c5a86194306617e50be105e4c2e8a17130b6285a102c6a15f40ae18564c2aa815410a898538c292a144509fa800000000000009da04d94262a12e3096104a1000000000091a84794232a1163089204354210a0000081a8000020060fc407ba83c941dc80e950722838101b880d7506a18344c198a0c75061a02f9417660b65
|8,1=>0x13a989c144d6a2665130a898044b6a25741292893cc494a2455120a08fc847682365000000000462a22c5113a800000000223410fa086940000215500000848c0000211110718829040aa20050fda87d9400001f15000007b503d0a1e530f02876d43aca1d15000007350390a1c4400000701000001bd30dd186d9036481af30d6186ac434ca1a42
|8,2=>0xd310690834441a098cf1466ea3325196a8ca146488321300000c7500000318518a20c44c6202000000000c2d460e8303400000bfd05f682fa117b9800005e4a2ee4174a800005c8a2df516d28b59000002d1516628b1d458682c1215e28add4564a0000156a8aa8c54c82a2415010a788532a2945147a8a2d050ca28150000000004f8a2784
|8,3=>0x203a900d000003ff41fda0fd947e2a3ee31f4a8f98c7c2a3dd41eca0f514000000001e7a80000794a3c55000000000780a3bc400000ee10766a000000000eb9475663a741d1a0000000003a211cf20e65472c600001c8a8000071c638a41c320e0906fc837a400000dd906e2a36c500000d9d46c4a35d51ae08d64c6a8a00000000000006a080000
|8,4=>0x9c8a4df526f09369000004d55000013450998a4c752630930cc97ca4ba4000012d5496464ad5254a12950940a49b524ba12548000049052462121d4904a47e423ca91d148e2646e32352000008d04463522f2916cc8b064544227a91348890a443521f290f4487284354218a10b50852800002122908c483ca000020d990594822a40c5
|8,5=>0x2daa96c8cb5e65ab40000169d000005a252cf216654b2e459342c9080000b1c85895000016150b08258042bda95e48000057452b7a95a94000000002b39958d0abca5595000000000aa8a54f52a5a151d0a84a53d529c294d10a5ea52b4293a148d0000051e528e894614a2a65105286214210a06a4ff427d293d9000004f3327728000000004e95
|8,6=>0x354a9a914d40869d334ca1a514d1ea68d234429a110cfea67c333d899e48ce8a66f5337099a90ccaa660532da9960ccac46515326299210c8e2642531f998ed0c6ca63153162989d4c486620430e2185d4c24a60e4000000000c12a60452ffa80000bf4a5f642f8a97b14bd085e352f1097754bb285d452e8200000b9885c842e3117054b7a85ba3
|8,7=>0x3c719e2ccf0ca78243bea9de14ee6a76e500001da54ec8a76133af19d690eb0475353a729d2cce8e8742500001cf54e7467355000000000e62872d4394a1c914e3ea71a500001c5cc00007134387a1c30ce0ea7061380a9bf14deea6f2500001bb90dd666e6537199b7d000006da536aa9b450d9c66cb336491b114d7ea6bc335c99ad14d6266ae3
|8,8=>0x4322800010bea85e10000216550aa88523426aa121508e2843441fa20ed10706000041a220c11056a82830000208d50442821140ea20651028a8104405aa01d1004a7fe400001feccfee87f2500001fb90fd2a7e453efa9f70cfaea7d253e8880000f9a87cb23e329f054f7a87b853da21ec4cf5a87aa33d2a80000f42800003cea1e68cf2c87915
|8,9=>0x4a62a524d288a93f549d2a4d91262a92d4494a249c9244a91e40000000012348916448a88000000009123486aa428d20aa90414809a3f8d1f668f65478a800011d8a8e754712a37551b0a8d35467a2329518c88c1545e2a2dd516688af445528000114c88a3344f2a269112aa892300000000111aa8885442221fd50fc287b343ba21c950daa8694
|8,10=>0x4ebaa750d39ea9cb400000000139249c544e0a26f8d372a0000000026d1400009af54d52a6955340a99b54cb2a6490000098f34c5a26195302a97c54bbaa5c952daa00004b60800012d0800004b1aa57d12b4a95734a92a544400000000
|9,0=>0x56aa2b45159a8ac94562a2b05157a8ab9455aa2ac5155a8aa94552a2a88d53c8a9a454b22a49151c8a8a454322a0914fc8a7a453b229c914dc8a6a45332298914bc8a5a452b22949149c8a4a452322909147c8a3a451b228ccd45e8a2b4513a288d143e8a1b450ba284d141e8a0b45041a811140089fc44fc227d113e089ec44f42279113c089dc4
|9,1=>0x5e7a2f2d178e8bc345dfa2eed176e8bb345d7a2ead174e8ba345cfa2e6d172e8b9345c7a2e2d170e8b8435c022df116f0800005ba22dc116d88b6845b222d8116b88b5845aa22d4116988b4845a222d0116788b38459a22cc116588b28459222c8116388b18458a22c4116188b08458222c0115f88af8457a22bc115d88ae93572a2b8515ba8ad94
|9,2=>0x66723329198c8cc2465f232e9196c8cb24657232a9194c8ca2464f23269192c8c92464723229190c8c82463f231e918ec8c724637231a918cc8c62462f2316918ac8c52462723129188c8c42461f230e9186c8c324617230a9184c8c22460f23069182c8c133607a302d180e8c0345ffa2fed17ee8bf345f7a2fad17ce8be345efa2f6d17ae8bd34
|9,3=>0x6e7237291b8c8dc246df236e91b6c8db246d7236a91b4c8da246cf236691b2c8d9246c7236291b0c8d8246bf235e91aec8d7246b7235a91acc8d6246af235691aac8d5246a7235291a8c8d42469f234e91a6c8d324697234a91a4c8d22468f234691a2c8d124687234291a0c8d02467f233e919ec8cf24677233a919cc8ce2466f2336919ac8cd24
|9,4=>0x7659bb1d1d868ebf475da3add1d668eaf4755a3a9d1d468e9f474da3a5d1d268e8f4745a3a1d1d068e7f473da39dd1ce68e6f4735a399d1cc68e5f472e1b9611ca88e504726239211c888e40471e238e11c688e304716238a11c488e20470e238611c2a6e114706a38251c0a8e0146fea37e51bec6df246f7237a91bcc8de246ef237691bac8dd24
|9,5=>0x7e323f091f7c8fba47db23ec91f5c8faa47d323e891f3c8f9b37cba3e4d1f1e8f8b47c41be111f008f7d37bca3dd51ee28f6d47b4a3d951ec28f5d47aca3d551ea28f4d47a4a3d151e828f3d479ca3cd51e628f2d4794a3c951e428f1d478ca3c551e228f0d4784a3c151e028efd477ca3bd51de28eed4774a3b951dc46ede476d23b591da48ece4
|9,6=>0x86324309217c90ba485b242c9215c90aa485324289213c909a484b24249211c908a48432420920fc907a483b241c920dc906a48332418920bc905a482b24149209c904a482324109207c903a481b240c9205c902a481324089203c901a480b24049201c900a4803240091ffc8ffa47fb23fc91fdc8fea47f323f891fbc8fda47eb23f491f9c8fca4
|9,7=>0x8e0a46f5237291b548d8a46b5235291a548d0a46752332919548c8a46352312918548c0a45f522f2917548b8a45b522d2916548b0a457522b2915548a8a45352292914548a11c4f9227491364899244b922549126400004489223c911a488b24449221c910a48832440921fc90fa487b243c921dc90ea48732438921bc90da486b24349219c90ca4
|9,8=>0x95ea4ae5256a92b14956a4aa5254a92a1494ea4a65252c7292494724a29250c9282493f249ece4ee92734937a49ad24ce9263492fa496d24ae92534927a492d248e9243491fa48f0e47092344918248b12450922449102487124309214490824831241092044900247f123f091f448f8247b123d091e448f02477123b091d538e8a4735239291c54
|9,9=>0x9dc24ed1276093ac49d424e912740939c49cc24e512720938c49c424e112700937c49bc24dd126e0936c49b424d9126c0935c49ac24d5126a0934c49a424d112680933c499c24cd8a664932e499524c992644931e498d24c592624930e49859cc1d260692ff497da4bdd25e692ef4975a4b9d25c692df496da4b5d25aa52d14966a4b25258a92c14
|9,10=>0xa5ba52cd295e94ab4a53a528d293e949b4a4ba524d291e948b4a43a520d28fe947b4a3ba51cd28de946b4a33a518d28be945b4a2ba514d289e944b4a23a510d287e943b4a1ba50cd285e942b4a13a508d283e941b4a0ba504d281e940b4a03a500d27fe93fb49fba4fcd27de93eb49f3a4f8d27be93dc39ec24f5127a093cc49e424f11278093bc4
|9,11=>0x152a4a939d48d2a3e951b4a8ba544d2a1e950b4a83a540d29fe94fb4a7ba53cd29de94eb4a73a538d29be94db4a6ba534d299e94cb4a63a530d297e94bb4
|10,0=>0xaf59d7a0ebca75e23aef9d770ebb275d63ae99d740eb9a75ca3ae39d710eb8275be3add9d6e0eb6a75b23ad79d6b0eb5275a63ad19d680eb3a759a3acb9d650eb22758e3ac59d620eb0a75823abf9d5f0eaf275763ab99d5c0eada756a3ab39d590eac2755e3aad9d560eaaa75523aa79d530ea9275463aa19d500ea7a753a3a9b9d4d0ea62752e3
|10,1=>0xb559daa0ed4a76a23b4f9da70ed3276963b499da40ed1a768a3b439da10ed02767e3b3d9d9e0ecea76723b379d9b0ecd276663b319d980ecba765a3b2b9d950eca2764e3b259d920ec8a76423b1f9d8f0ec7276363b199d8c0ec5a762a3b139d890ec42761e3b0d9d860ec2a76123b079d830ec1276063b019d800ebfa75fa3afb9d7d0ebe275ee3
|10,2=>0xbb59dda0eeca77623baf9dd70eeb277563ba99dd40ee9a774a3ba39dd10ee82773e3b9d9dce0ee6a77323b979dcb0ee5277263b919dc80ee3a771a3b8b9dc50ee22770e3b859dc20ee0a77023b7f9dbf0edf276f63b799dbc0edda76ea3b739db90edc276de3b6d9db60edaa76d23b679db30ed9276c63b619db00ed7a76ba3b5b9dad0ed6276ae3
|10,3=>0xc159e0a0f04a78223c0f9e070f03278163c099e040f01a780a3c039e010f00277fe3bfd9dfe0efea77f23bf79dfb0efd277e63bf19df80efba77da3beb9df50efa277ce3be59df20ef8a77c23bdf9def0ef7277b63bd99dec0ef5a77aa3bd39de90ef42779e3bcd9de60ef2a77923bc79de30ef1277863bc19de00eefa777a3bbb9ddd0eee2776e3
|10,4=>0x307a783a3c1b9e0d0f062782e3
|11,0=>0x313458982c4b16250b12458902c4716230b11458882c4316210b10458802c3f161f0b0f458782c3b161d0b0e458702c37161b0b0d458682c3316190b0c458602c2f16170b0b458582c2b16150b0a458502c2716130b09458482c2316110b08458402
|12,0=>0x18a01c4f8e278713a389c1
|_,_=>0
def PO:=mkPO wAt oP oO 20 9 511 17
def pmP:Nat→Nat
|0=>0x201000000000020000000000001f100000000001c100000000001810000000000180000000000014d0000000000140000000000012000000000001100000000000101000000000010000000000000c80000000000081000000000008000000000000600000000000050000000000004900000000000420000000000041000000000004000000000000300000000000021000000000002000000000000110000000000010000000000000c00000000000090000000000008000000000000200000000000010000000000000
|1=>0x8c300000000008c0000000000088000000000008600000000000840000000000082000000000008100000000000808000000000080100000000008000000000000600000000000058100000000005400000000000480000000000044000000000004200000000000408000000000040000000000003f100000000003600000000000348000000000030000000000002d0000000000028000000000002500000000000244000000000024200000000002400000000000221000000000021000000000002080000000000202
|2=>0x10c8000000000108300000000010400000000001020000000000101800000000010100000000001009000000000100100000000010000000000000d200000000000c680000000000c000000000000bcb0000000000b800000000000b690000000000b400000000000b010000000000b000000000000ad00000000000a600000000000a480000000000a400000000000a000000000000991000000000098b0000000000981000000000095000000000009480000000000940000000000092000000000009100000000000908
|3=>0x1a500000000001a400000000001a180000000001980000000000188900000000018600000000001848000000000184000000000018000000000001648000000000161000000000014400000000001408000000000140000000000013e000000000013a1000000000136000000000013410000000001340000000000132400000000012c000000000012800000000001260000000000124800000000012440000000001240000000000122100000000012010000000001200000000000119100000000011600000000001100
|4=>0x9a0800000000099000000000009850000000000936000000000093000000000009100000000000904000000000090210000000008e080000000008d68000000000844000000000084200000000008344000000000830400000000081400000000008104000000000810000000000080000000000001fd10000000001fc10000000001c440000000001c000000000001bf10000000001bf00000000001be10000000001bd10000000001bc90000000001bc50000000001bc10000000001b990000000001b400000000001ac1
|5=>0x20a810000000020a800000000020a00000000002090000000000208d0000000002088000000000208700000000020800000000002061000000000204080000000020401000000002040000000000203c1000000002032100000000202d100000000202d000000000202910000000020200000000002018100000000201610000000020091000000002009000000000200610000000020051000000002004100000000200110000000020010000000002000100000000200000000000009be10000000009bcd0000000009bc5
|6=>0x21be90000000021be10000000021bd10000000021b680000000021ad80000000021a980000000021a480000000021a00000000002192000000000218480000000021840000000002180000000000213b900000000213a100000000213600000000021321000000002132000000000212d800000000212900000000021240000000002120000000000211ed000000002112000000000210d00000000021044000000002104000000000210000000000020ed00000000020e510000000020e000000000020b910000000020ac0
|7=>0x8100800000000810000000000080a110000000080a080000000080a0000000000808480000000080800000000008040000000000802820000000080208000000008008000000000800200000000080008000000008000000000000400100000000040000000000003fbc00000000029f850000000029be10000000029bc100000000299c10000000028c4100000000289cd000000002838100000000282610000000021ff10000000021fc10000000021ed80000000021e680000000021c480000000021c400000000021c00
|8=>0x1008c1000000010082000000001000c200000001000c000000001000820000000100040000000010000000000000a1fe100000000a1e4800000000a1bf900000000a1ad800000000a1a0800000000a164800000000a161000000000a13e100000000a120000000000a0c0000000000a0b6800000000a0a4000000000a044800000000a040000000000a022100000000a020800000000891000000000081ff10000000081fd90000000081fc10000000081bcd0000000081bc50000000081bc300000000813600000000081040
|9=>0x200240000000020020100000002002000000000200181000000020004100000002000400000000200020000000020001000000002000080000000200001000000020000000000001a0b8d0000000129be100000001299810000000128bc10000000121b9100000001219c1000000012188100000001213c10000000120a1100000001206d100000001200810000000101e400000000101bc10000000101a5000000001010400000000100a800000000100a400000000100a010000000100a0000000001009cb00000001008c2
|10=>0x201a890000000201a500000000201a4100000002019cb000000020184800000002018420000000201841000000020180000000002013cf00000002013c9000000020130400000002012e0000000020125000000002012480000000201230000000020122000000002012010000000201200000000020100800000002010000000000200a400000000200a0000000002009500000000200900000000020085000000002008410000000200840000000020083000000002008000000000200400000000020036000000002002c0
|11=>0x209bc50000000209bc30000000209bc10000000209b85000000020992400000002093040000000208bcb0000000208a4000000002083040000000201fcf0000000201fcd0000000201fcb0000000201fc90000000201fc10000000201beb0000000201be30000000201be10000000201bdd0000000201bd70000000201bd10000000201bcf0000000201bcd0000000201bcb0000000201bc90000000201bc50000000201bc30000000201bc10000000201bc00000000201b890000000201b830000000201b410000000201a90
|12=>0x28100000000002802200000000229fd30000000229fc10000000229be10000000229bcb0000000229bc50000000229bc30000000229bc100000002299c10000000228fc10000000221fe10000000221fd10000000221fcb0000000221f910000000221e480000000221bf90000000221be10000000221bd10000000221bc10000000221a500000000221a48000000022184800000002218400000000220fd300000002202d0000000022021000000002200000000000209e010000000209be50000000209be10000000209bd1
|13=>0x321bc90000000321bc50000000321bc30000000321bc10000000321b8100000003219c50000000309bc100000003091e10000000301fc10000000301be10000000301bd30000000301bd10000000301bcb0000000301bc30000000301bc100000003013e10000000300842000000030084100000003000c300000002a9bc100000002a1fc900000002a1fc100000002a1be100000002a1bc10000000281fc90000000281fc10000000281bd30000000281bc50000000281bc100000002819c9000000028184000000002813e1
|14=>0x21000c100000021000c000000020819d10000002080b810000002021bf10000002001ff10000002001fd10000002001bd90000002001bd50000002001bd10000002001bc100000020001b100000020001810000002000049000000100000c0000000c00000000000080010000000003a93c500000003a1be100000003a1bcd00000003a1bc10000000381fc10000000381bc100000003812440000000360bd10000000329fd10000000329be50000000329bc50000000329bc10000000321fc10000000321be10000000321bcb
|15=>0x10000c600000010000b090000010000a480000010000a400000010000a0900000100009090000010000908000001000080900000100004000000010000348000001000030900000100001000000010000080000001000003000000100000090000010000000000000c000be50000008207bc10000008203bc0000000802d9c1000000802b9c00000008012bcd0000008006bcd0000002321bc10000002308bc30000002281bd90000002221fd10000002221bd10000002201bd10000002201bc100000022019d10000002201844
|16=>0x10209f8f0000010201fcb0000010201fc90000010201fc50000010201bc90000010201bc100000102013a10000010200b080000010200b040000010200a690000010081ff100000100800600000010021bf10000010009be50000010008be100000100083a100000100081a50000010001f830000010001f810000010001e080000010001d080000010001be10000010001bc90000010001bc10000010001b830000010001a000000010001500000001000140000000100013a1000001000110800000100010280000010000d04
|17=>0x20001bc10000020001a5000000200019c100000200018ca00000200018c9000002000188900000200018800000020001840000002000141000000200012d00000020001270000002000123000000200011cd00000200010c1000002000108000000200010000000020000a9800000200009d10000020000210000002000020000000200000c90000020000089000002000008800000200000500000020000009000002000000100000200000000000014009be400000108001000000010229bc10000010221bc10000010209fc9
|18=>0x20281bcf0000020281bcb0000020281bc900000202819cb0000020221bc10000020221ad80000020201fd10000020201bd10000020201bcd0000020201bc90000020201bc50000020201bc10000020201a5000000202013cf0000020201230000002020061000000202000c800000202000880000020101bd300000201002c200000200a1be900000200a03c10000020081fd10000020081bc300000200818000000020080889000002008080000000200800000000020021ed80000020021ad800000200202000000020001bd1
|19=>0x300019e9000003000107000000300010300000030000a700000030000230000003000021000000300001b10000022301bd30000022301bd100000223009d10000022281bc10000022221fc10000022201bf10000022201bd90000022201bd30000022201bd10000022201bc10000022200bc10000022101bd30000022101bd100000221009d10000022080bd90000022001bd90000022001bc100000220019c100000220002100000020321bc10000020301bd30000020301bcf0000020301bc500000203018c200000202a1bc1
|20=>0x100001bc90000100001bc10000100001b890000100001a480000100000a40000010000080200001000008000000100000785000010000018100001000001080000080201bc10000080121bc10000080121b8100000800013d300000800013cb0000050601ac50000050001ac900000500000000000040601b080000040009ec90000040000100000004000004000000400000000000032001bf10000030201bf90000030201a700000030201a5000000302003f9000003008083000000300802300000030021a900000030001bf1
|21=>0x1100002480000102281bd90000102281bd10000102281bc90000102201bd90000102201bd100001003a19c10000100381bc700001003219c300001003002400000100281bd10000100281bcd0000100229bc10000100229b850000100221bc10000100221a4000001002210000000100201fe30000100201bcf0000100201bcd0000100201bcb0000100201bc90000100201bc30000100201bc10000100200e20000010010000000001000a10000000100081040000010008080c0000100029bc10000100028b850000100009be1
|22=>0x122281bc90000122081fd100001220819d10000120321bc10000120301bc30000120281bc90000120281bc100001202819c50000120221bc10000120201bcb0000120201bc900001202017d1000012020004000001200819c500001200802500000120001bc9000012000184000001200002c80000110229bc10000110201fe10000110201fc90000110201e600000110201e000000110201bc50000110201b8d0000110029f810000110001a080000110000e020000110000b080000110000a1000001100009040000110000820
|23=>0x20000812440002000080c000002000021a0000020000211e10002000001c8000020000010880002000000b600002000000a48000200000088800020000003400002000000300000200000020800020000001400002000000009000200000000800020000000010001000261b510001000020290000100000001000010000000000000e00201bc10000c08201bc10000c080013cb0000a08201bc10000808201bc100008080299c100004080013cb0000400121b8100001500002080000130081bf1000013000023000001223018ca
|24=>0x4000000a0d000400000090800040000002c000040000000010002120201bc900021200000490002020301bc50002020281bcd0002020201bcd00020201018ca0002020001bc1000202000188900020003a1bc10002000301bc500020002a1be50002000281fc10002000281bcd0002000281bc50002000201bcd0002000201bc1000200020008800020001a1bc500020001a12440002000181be10002000181bc10002000120340000200012030000020000a13c100020000a13600002000081be10002000081bc90002000081849
|25=>0x4000221bc10004000220ed20004000209fcb0004000209bc300040002098120004000201fc90004000201fc30004000201fc10004000201b8b0004000201b89000400020100000040000a14480004000089448000400008140000040000802c00004000029fc1000400002978900040000286410004000021bd10004000020e4100040000202c000040000082420004000001b830004000001b81000400000197800040000019100004000001900000400000180000040000017c100040000012c000040000010400004000001000
|26=>0x80000089cb00080000080400008000001feb0008000001fe90008000001fdb0008000001bcd00080000013e100080000011600008000000a90000800000090000080000008800008000000801000800000064000080000002530008000000248000800000024400080000001000008000000048000800000004000080000000000004110209bc30004110001f810004110001b080004100201fcb0004100009e030004010209fc90004010001fc90004010001fc1000401000110900040021084900004002028ed00004000229fc1
|27=>0x8000229bd30008000229bc10008000228fd10008000221fcb0008000221bed0008000221bc10008000209bc50008000201fd10008000201fcb0008000201fc10008000201bed0008000201bcd0008000201bc30008000201bc1000800020184200080002013cd0008000200fd10008000200bd30008000200bd1000800020020200080002000420008000121bd10008000081be100080000813c10008000080c600008000021bc10008000021960000800002182000080000213c1000800002112000080000091650008000008bc1
|28=>0x81000200400008100001bc100081000000000008022221bc10008022000dd10008020201fd90008020201fc100080200812100008020001e500008010281be9000801028024000080100001480008002201fd10008002080dd100080020202d30008002001fd10008002000fd10008000381bc10008000329bc10008000321bd10008000321bc10008000320a410008000301bd10008000301bc50008000301bc100080003013cd00080002a9bc500080002a1be100080002813e1000800028026000080002801e10008000229be1
|29=>0x80000000fa30080000000300008000000006000800000000400080000000000004000002136000400000001000040000000081004000000002000400000000000020000201bc10020000201ac10020000000bcd0020000000acd00200000000000010100001b4b001002008080000100200010c80010020000009001000020008000100000000800010000000048000a0003a1bc1000a0001a1bc1000a0000a13600009002241f510008122081fd10008100221bc10008100201bc90008100201bc30008100201a400008100020a40
|30=>0x80010201fe10080010201bed0080010201be50080010201be10080010201bc90080010201bc100800102013c100800102013a10080010021bd10080010001bf10080010001be50080010001be10080002000bf100800002a1bc10080000229bcd0080000221bc100800002091640080000201fc10080000201be90080000201be10080000201bd90080000200b0000800000202650080000001fe10080000001fa90080000001fa10080000001bf10080000001be10080000001bd10080000001bcd0080000001bc10080000001a01
|31=>0x1800020001bd1100000000088010000000000900400000001bd104000000001010200000201be1020000000002001a0010209be10180000001bcd010000000138d01000000000200088010081be100880100813a100880002a1be100880002813e10088000201be900880000a1be10088000081bed00880000813e100840102005080080110201fc90080110201f810080090201be10080032081e700080030001bd10080022001be1008001c209be1008001c201be10080010281bc10080010229be10080010209be50080010209be1
|32=>0x8000000001bc14000028101bd34000008201bc120100200018c020001202019412000020201bc1200002010000018000a2201bd118000a0101bd3
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x500400000000
|7,0=>0xc0000005700000000000000000000f000c04400000002000000000220000001e000000000000000000000003c0280000000000017135000000000000000000000800c0b8170000000200000000000000000000000000000000000f0363a0090000002320c0e98000ae0d8000000ee0000d00000e00000000000000000010000000000000000000000000000790f303c0000f00000000000000016000000000000000400026a0000880009200000000
|7,1=>0x170000000180000603a000000060000001d80000c3bc0000000002c0000000000017800000000001d1
|8,0=>0x72044f580c2860187201e00215d1206503c3d006878000000063b8090000000142001900002a00002c0008e0440d951a1001c9e4000fd0001700202e20a2a98e00100007800836000044003b106c3f82b81e0b800c0fb4c2763d9a88010a25304a00c1e23c83693527402c00b2016e8c00a00603c0883b90e0b00000000048a07d9200b54c15c000000c018c5a93512a0a008800064000082f43b01241d9ef0b0044108010160d948a830287b085a26
|8,1=>0x280d80013901600408935002a254c0110161f8000005e00001d0490000000083600002c2c3bb0004e80581403c000000061fc0041b0000b20001b21409202c05814000050008370001260201500c8041d800000000058000009e80580b03c4f9a89200fcfec1b00b0000780413039e4d451800000174058200000d8318a306c001490350ee0008a9bb3e8044000010020242b9f709a29c008000020781b00f05ced94984c4940458e1dc0000007580b
|8,2=>0x1802d768b800002ddda7f03c1241700b0060011414644a4e40401e0286100014c0762a40000018a0d9b03b3000000008170160c46bbb20284781683602207800014006124170d401602c4903a03018c00057028000003ad0000217901f00607800012000eac3195701015c00a8b0000042d0600160d9d604e516610000a40167a54501e03e1dc0813506a00052a6b7029107f057002d30451330220200f03603c15c0a00026428c9b0007ea574f5001
|8,3=>0xae0780a05703264411a37000198060352340785b0010024d40a0a40000441708a0000000580b06cc71df26a00015c0005703c4d41e919002160a62a100002c9a92651c079129641040449aa9a05ca4c038364604a80f0570021b94c81e0ae00403aec44e0781e93500d009a82843e40d9fe80107cedc7914300202c792230ae02c848110f00dc5a14203c7c49d036000000a50c60240002993864234d458015e207c058d915c0000f22c7f2290058ff
|8,4=>0xc84d40a037002078fa01e0280b80f9430000000a03b1460000001044e15d759f00a815c0f1560360003b80166a004af95006c5601b13d1005300581429e0003a9351c015c351350000001500101e99c0405706c05453011036000970063e023c249353e8d7c01bb906c02d760000283141201e00003001bbb0220d80f8141960791483800c4d40581a00002c008010480797281b00c0001b1375c80a01b14c6bc02da68360020000880006c1500a07b
|8,5=>0x41e4d5ff81e0000001701101602dc9000000750000150761610911c0023e4002890c6d4526ae623a800088001460009c8002b20d85993502801800000
|9,0=>0x6fa4b4b28861c4d3cf384c2f6d68418672de530b2bec5eced0b28365206c4ca8000943dc7ab434eeca824aa73443248d8be048419749656601dc263333f6a746ebca64a488fd30203097df78c143ec18ef27d66e4bdb804f404ea903aa008a8214a0115362c4850ac23a0d83ea9f4a0781212c25fa7e4f991280a2b5ae2d90a05fd3496539218518a3f0c4d5c4f2565bab00b13d76d059df1940588e8c6621a016795f8b2c4ca27ccf11834abbe01a0e
|9,1=>0x6765497c0a87a859dc131521a664d9908406d1c398cf482c15a1355102f38d01ac52a8bc643ae66c301151967b228985a6252eb8d8a36c728a08be16f12e35843ab21248fcb28876a49d8fb04754831c9609a3306e4b2aae0ba1b19107161a10569afe80c1ad089551f64a43e0336884a0203f67dcbd44d8fa1f02205c84a2faf04e49741a48fd1dae86e01dd5bb3a2ca0991b16f6dadadd82342f08312189c076d29ce96504e9194e077228b1932025
|9,2=>0x1064a0fe8491229b058bd26cccd09593578a820e40d829a5fc580362ca1fd2e0465a84592da0557037d292cd5e65dd6890c0968f542ba179abfc612d5048b39739e263e50570afb64e879273f239a5a116a3932c48c439af29a3b4d6ac329c9f05d0986ca6986f3bc13ac210b3562ceff034ac13a49b9c198e51e2ecb7ab930ae284187a336a313688707ee1962bbd0b6a94b28e87963340f3ba17ac74500796c4e605716531ccbd1a96a72a371df8ce
|9,3=>0x10e868eeaf95022160429608644c5794b0fc155f6a176ceafd578498000a11d2400f04c5cd85241a0a5ec35d06c6c4683a61f861c9fbea0005f951260578f4035aee6e6c68d818350eb1cb80ab194b3ce2aba294224cf9655b224c15ad20fc1bd0339179e259863cc2027f164a8d2b4580873b547c8c82d3100bcf4cd82512b6f55ccbf31ca7e04cb5b600bf1c79450381d1919114ace190983c7fc1c8b29d73721407610f292324ff98b7926a59729b
|9,4=>0x7f4378c424f2ca9443aa2b2cad9043b6324efdde884b50e764ce98a7ccca1b08e23b42f0a385f2caf1cbf95c4420b8c49b86b01a8b795123e1bd7b8c24088cdd21ca4325846a0d50ac10c369ba088ed00520b3043a87e3af48e20c7c2cb2cec5598b291cf01c058e365abe8b1b964700413295371847c7298011404c6c1d5752a54f73c34e0078d099756ac796b8bf0c6fe0bf9e110ccfd43148274984e3a7e4b06c8211db6dce7d8900b5b0d4de1144
|9,5=>0x1650169e0929df20e77ceaa6d2d8550b2bc62f23b8eb3893f2930d894941210d4aa660c64843517d17a440380da0d02401a1f51d2f01259ed0e47f8af1654dc6b8b62bd02c5f5f2ab626859422891278cc9f806845c399a735449a408d8b592cc738bb9660ec64c618e160882845b261640b081a7b436f809216d6565a0d536f
|10,0=>0x4aef6cb3ab32d46f0f22cb2faf75872e22fe789d021a2dcb7dc5be138094d0e30831a63956be15586f0e316531a5a85097f2d8d198096b4e8fa56d2d662e700da377670635661e37d6f7c8225d7b887589b7a4aa5e9ed3e06e6de9f11cb430f90e199a680aecbe9bc700e4dbc19b39236cdaae02e86f0c723c2ccce8f419332ec455a1b7682dfce6348440dd8b2a224909c0b7967738e2d6e1907cee9ccbb397acc58db1752cab7cc0b973c6798f1385
|10,1=>0x4de968ca3b56e8d2cb3be831ef50c52bd5d4e35392706146c8b38de42aaf9daba250068d83b3d590de16dad0382951652874eac492ca6f6f8aa1ba9d62d8ac13999c802f352f1867b45b1d22882d2601a2a70708824621a74c85951fb936d4f79d42da3686f58c997324f75a4bdd78265d9d388384acdb8b186368899f3eb4bade5bdbf46fcf21d19c4356dcd9e37e2d298d38a1b3485c5e21be37ee1c6899322ec3cd43033c6e95c739a6125d9c9965
|10,2=>0x1382b12d8b7924884
|11,0=>0x82b9e4e05a9ee18c2ca594d1aaa556a00cd1bc720da5ee17d3805a4b2b722e6c3d5488d7b859cc69692d8aa1341652ca65cb91672ca70ceb1973469c1bd169
|12,0=>0x29e11859441965
|13,0=>0x83
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 11 (j%128);fld (pmP (k/32)) 52 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_254 12 roots_254 ops++addP pm 1 dom_111 7 roots_111 ops++addP pm 2 dom_63 7 roots_63 ops++addP pm 3 dom_47 6 roots_47 ops++addP pm 4 dom_199 6 roots_199 ops++addP pm 5 dom_151 6 roots_151 ops++addP pm 6 dom_247 11 roots_247 ops++addP pm 7 dom_253 12 roots_253 ops++addP pm 8 dom_251 12 roots_251 ops++addP pm 9 dom_223 11 roots_223 ops++addP pm 10 dom_207 9 roots_207 ops++addP pm 11 dom_239 11 roots_239 ops++addP pm 12 dom_191 11 roots_191 ops++addP pm 13 dom_150 5 roots_150 ops++addP pm 14 dom_142 5 roots_142 ops++addP pm 15 dom_95 7 roots_95 ops++addP pm 16 dom_154 5 roots_154 ops++addP pm 17 dom_87 6 roots_87 ops++addP pm 18 dom_213 8 roots_213 ops++addP pm 19 dom_183 9 roots_183 ops++addP pm 20 dom_119 7 roots_119 ops++addP pm 21 dom_127 10 roots_127 ops++addP pm 22 dom_171 8 roots_171 ops++addP pm 23 dom_187 10 roots_187 ops++addP pm 24 dom_61 6 roots_61 ops++addP pm 25 dom_231 7 roots_231 ops++addP pm 26 dom_158 6 roots_158 ops++addP pm 27 dom_126 8 roots_126 ops++addP pm 28 dom_143 6 roots_143 ops++addP pm 29 dom_167 6 roots_167 ops++addP pm 30 dom_235 9 roots_235 ops++addP pm 31 dom_125 9 roots_125 ops++addP pm 32 dom_175 9 roots_175 ops++addP pm 33 dom_228 5 roots_228 ops++addP pm 34 dom_166 5 roots_166 ops++addP pm 35 dom_198 5 roots_198 ops++addP pm 36 dom_221 9 roots_221 ops++addP pm 37 dom_55 5 roots_55 ops++addP pm 38 dom_79 5 roots_79 ops++addP pm 39 dom_215 9 roots_215 ops++addP pm 40 dom_189 9 roots_189 ops++addP pm 41 dom_123 9 roots_123 ops++addP pm 42 dom_243 9 roots_243 ops++addP pm 43 dom_159 7 roots_159 ops++addP pm 44 dom_219 10 roots_219 ops++addP pm 45 dom_211 8 roots_211 ops++addP pm 46 dom_149 5 roots_149 ops++addP pm 47 dom_237 10 roots_237 ops++addP pm 48 dom_245 10 roots_245 ops++addP pm 49 dom_173 8 roots_173 ops++addP pm 50 dom_230 6 roots_230 ops++addP pm 51 dom_157 6 roots_157 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_255 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45|h46|h47|h48|h49|h50|h51
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_47 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_247 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_223 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_207 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_191 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_150 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_142 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_127 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_143 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_175 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_228 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_166 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_198 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_221 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_79 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_189 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h45;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h46;exact cpcs (by decide +kernel) lowS_149 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h47;exact cpcs (by decide +kernel) lowS_237 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h48;exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h49;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h50;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h51;exact cpcs (by decide +kernel) lowS_157 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_254 12 s (0,roots_254.map (·&&&dom_254)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_254 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_255==dom_255)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 4000012 zs symsG zs (hk 4000012 zs)
theorem ori_ok {v ys} (h:RunD true dom_255 gM v ys):RunD true dom_255 gM v (ori ys):=pickMin_runD 4000012 ys h symsG ys (hk 4000012 ys) symsG_ok h
def Z (s:Nat):=barP dom_255 gM mpG SD SS NN hAt idxH ori 4000012 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 2 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 14 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 14 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 159 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 31 128 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 159 → Z 7 i = true := (range_split z7_0 z7_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 256 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_256 : ∀ i, 256 ≤ i → i < 384 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 256 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_384 : ∀ i, 384 ≤ i → i < 512 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 384 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_512 : ∀ i, 512 ≤ i → i < 640 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 512 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_640 : ∀ i, 640 ≤ i → i < 685 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 45 640 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 685 → Z 8 i = true := (range_split (range_split z8_0 (range_split z8_128 z8_256)) (range_split z8_384 (range_split z8_512 z8_640)))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_0 : ∀ i, 0 ≤ i → i < 128 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_128 : ∀ i, 128 ≤ i → i < 256 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_256 : ∀ i, 256 ≤ i → i < 384 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 256 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_384 : ∀ i, 384 ≤ i → i < 512 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 384 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_512 : ∀ i, 512 ≤ i → i < 640 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 512 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_640 : ∀ i, 640 ≤ i → i < 733 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 93 640 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 733 → Z 9 i = true := (range_split (range_split z9_0 (range_split z9_128 z9_256)) (range_split z9_384 (range_split z9_512 z9_640)))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_0 : ∀ i, 0 ≤ i → i < 128 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_128 : ∀ i, 128 ≤ i → i < 256 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_256 : ∀ i, 256 ≤ i → i < 262 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 6 256 = true)
private theorem z10 : ∀ i, 0 ≤ i → i < 262 → Z 10 i = true := (range_split z10_0 (range_split z10_128 z10_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 46 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 46 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z12 : ∀ i, 0 ≤ i → i < 5 → Z 12 i = true := span_ok (by decide +kernel : span (Z 12) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z13 : ∀ i, 0 ≤ i → i < 1 → Z 13 i = true := span_ok (by decide +kernel : span (Z 13) 1 0 = true)
theorem checked (s:Nat) (hs:s≤13):∀ i<NN s,bar dom_255 gM mpG SD SS NN hAt idxH ori 4000012 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
  · exact z7 i (Nat.zero_le i) hi
  · exact z8 i (Nat.zero_le i) hi
  · exact z9 i (Nat.zero_le i) hi
  · exact z10 i (Nat.zero_le i) hi
  · exact z11 i (Nat.zero_le i) hi
  · exact z12 i (Nat.zero_le i) hi
  · exact z13 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 7 7=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤13) (h:RunD true dom_255 gM s xsM):False:=by
  have hmin:7≤s:=by have hl:=run_len h;change 8≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_255 roots_255 goal_255 14:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_255
theorem lowS_255:Lower true dom_255 roots_255 goal_255 14:=S_255.noCircuit
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
    (hhas : ∃ g ∈ gates, isNotGate g = true) : 15 ≤ gates.length := by
  obtain ⟨g, hg, hgn⟩ := hhas
  have hout : (execN gates xs256).getD o 0 &&& mask256 = goal_255 &&& mask256 := by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and, Nat.testBit_and, mask256_bit]
    by_cases hlt : r < 256
    · simp only [hlt, decide_true, Bool.and_true]
      have h1 := execN_bit gates xs256 r hlt (fun g' hg' => (hfan g' hg').1)
      have h2 := congrArg (fun l => l.getD o false) h1
      rw [xs256_bits ⟨r, hlt⟩] at h2
      have hgd : ((execN gates xs256).map (·.testBit r)).getD o false =
          ((execN gates xs256).getD o 0).testBit r := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN gates xs256)[o]? with | none => simp | some v => rfl
      rw [hgd] at h2
      exact h2.trans ((hev (pt8 r)).trans (goal_eq_f ⟨r, hlt⟩).symm)
    · simp [hlt]
  have hsup0 : ∀ v ∈ xs256, Avail true mask256 xs256 v := fun v hv => Or.inr (Or.inl ⟨v, hv, rfl⟩)
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach true gates xs256 hfan (fun h => Bool.noConfusion h) 0 xs256 xs256 rfl hsup0
  have hav_out : Avail true mask256 bank ((execN gates xs256).getD o 0) := by
    by_cases hi : o < (execN gates xs256).length
    · exact hsup _ (getD_mem hi)
    · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
  have hL := lowS_255 p bank hr (avail_of_eq hout hav_out)
  have hlt := countP_not_lt hg hgn
  omega

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [1, 0] }, { op := GateOp.or, inputs := [2, 0] }, { op := GateOp.or, inputs := [7, 3] }, { op := GateOp.or, inputs := [4, 9] }, { op := GateOp.or, inputs := [3, 6] }, { op := GateOp.or, inputs := [7, 6] }, { op := GateOp.or, inputs := [9, 10] }, { op := GateOp.or, inputs := [4, 10] }, { op := GateOp.and, inputs := [14, 5] }, { op := GateOp.and, inputs := [12, 7] }, { op := GateOp.and, inputs := [13, 11] }, { op := GateOp.and, inputs := [8, 15] }, { op := GateOp.or, inputs := [16, 17] }, { op := GateOp.or, inputs := [20, 18] }, { op := GateOp.or, inputs := [21, 19] }]

theorem wit_mono : ∀ g ∈ witGates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

def b2n (b : Bool) : Nat := if b then 1 else 0
theorem b2n_le (b : Bool) : b2n b ≤ 1 := by cases b <;> decide
theorem b2n_testBit0 (b : Bool) : (b2n b).testBit 0 = b := by cases b <;> rfl
theorem testBit0_b2n_add (b : Bool) (m : Nat) : (b2n b + 2 * m).testBit 0 = b := by
  cases b <;> simp [b2n, Nat.testBit_zero]
theorem testBit_succ_b2n_add (b : Bool) (m k : Nat) : (b2n b + 2 * m).testBit (k + 1) = m.testBit k := by
  cases b <;> simp [b2n, Nat.testBit_succ]
  have : (1 + 2 * m) / 2 = m := by omega
  rw [this]

def natOfBits8 (x : Fin 8 → Bool) : Nat :=
  b2n (x 0) + 2 * (b2n (x 1) + 2 * (b2n (x 2) + 2 * (b2n (x 3) + 2 * (b2n (x 4) + 2 * (b2n (x 5) + 2 * (b2n (x 6) + 2 * b2n (x 7)))))))

theorem natOfBits8_lt (x : Fin 8 → Bool) : natOfBits8 x < 256 := by
  have h0 := b2n_le (x 0); have h1 := b2n_le (x 1); have h2 := b2n_le (x 2); have h3 := b2n_le (x 3)
  have h4 := b2n_le (x 4); have h5 := b2n_le (x 5); have h6 := b2n_le (x 6); have h7 := b2n_le (x 7)
  unfold natOfBits8; omega

theorem pt8_natOfBits8 (x : Fin 8 → Bool) : pt8 (natOfBits8 x) = x := by
  funext i
  fin_cases i <;> simp only [pt8, natOfBits8, testBit0_b2n_add, testBit_succ_b2n_add, b2n_testBit0] <;> rfl

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 22⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
  have hwit : (execN witGates xs256).getD 22 0 &&& mask256 = goal_255 &&& mask256 := by decide +kernel
  intro x
  have hlt : natOfBits8 x < 256 := natOfBits8_lt x
  have hpt : pt8 (natOfBits8 x) = x := pt8_natOfBits8 x
  generalize hr : natOfBits8 x = r at hlt hpt
  have h1 := execN_bit witGates xs256 r hlt (fun g hg => by
    have hm := wit_mono g hg
    rcases hm.1 with h | h <;> simp [h])
  have h2 := congrArg (fun l => l.getD 22 false) h1
  rw [xs256_bits ⟨r, hlt⟩, hpt] at h2
  have hgd : ((execN witGates xs256).map (·.testBit r)).getD 22 false =
      ((execN witGates xs256).getD 22 0).testBit r := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases (execN witGates xs256)[22]? with | none => simp | some v => rfl
  rw [hgd] at h2
  have hbit : ((execN witGates xs256).getD 22 0).testBit r = goal_255.testBit r := by
    have hb := congrArg (fun v => v.testBit r) hwit
    simp only [Nat.testBit_and, mask256_bit, hlt, decide_true, Bool.and_true] at hb
    exact hb
  have hres := h2.symm.trans (hbit.trans (goal_eq_f ⟨r, hlt⟩))
  rw [hpt] at hres
  exact hres

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o hfan _h1not hev
  by_cases hhas : ∃ g ∈ gates, isNotGate g = true
  · have hfan' : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
      intro g hg
      obtain ⟨h1, h2⟩ := hfan g hg
      refine ⟨?_, h2⟩
      rcases h1 with h1 | h1 | h1 <;> simp [h1]
    have hlb : 15 ≤ gates.length := lb_with_not gates o hfan' hev hhas
    refine ⟨witGates, 22, wit_mono, ?_, wit_eval⟩
    have hlen : witGates.length = 15 := rfl
    omega
  · push Not at hhas
    refine ⟨gates, o, ?_, le_rfl, hev⟩
    intro g hg
    obtain ⟨h1, h2⟩ := hfan g hg
    refine ⟨?_, h2⟩
    rcases h1 with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exfalso; have := hhas g hg; simp [isNotGate, h1] at this

end PEqualNP.Outside.L_meta_52558_aux

theorem PEqualNP.Outside.L_meta_52558 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_52558_aux.main
