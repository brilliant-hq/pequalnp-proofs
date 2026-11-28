import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_51990_aux
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
def dom_27 : Nat := 0xf0f0f0f
def goal_27 : Nat := 0xeeaaee00eeaaee00eeaaee00eeaaee00eeaaee00eeaaee00eeaaee00eeaaee00
def roots_27 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_29 : Nat := 0x33333333
def goal_29 : Nat := 0xfafaaa00fafaaa00fafaaa00fafaaa00fafaaa00fafaaa00fafaaa00fafaaa00
def roots_29 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_31 : Nat := 0xffffffff
def goal_31 : Nat := 0xfefaee00fefaee00fefaee00fefaee00fefaee00fefaee00fefaee00fefaee00
def roots_31 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_41 : Nat := 0x30300000303
def goal_41 : Nat := 0xffaaffaaaa00aa00ffaaffaaaa00aa00ffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_41 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_42 : Nat := 0x50500000505
def goal_42 : Nat := 0xffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00
def roots_42 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_43 : Nat := 0xf0f00000f0f
def goal_43 : Nat := 0xffeeffeeee00ee00ffeeffeeee00ee00ffeeffeeee00ee00ffeeffeeee00ee00
def roots_43 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_46 : Nat := 0x555500005555
def goal_46 : Nat := 0xffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00
def roots_46 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_47 : Nat := 0xffff0000ffff
def goal_47 : Nat := 0xffeeffeeee00ee00ffeeffeeee00ee00ffeeffeeee00ee00ffeeffeeee00ee00
def roots_47 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_51 : Nat := 0xf000f000f000f
def goal_51 : Nat := 0xeeeeeeeeaaaa0000eeeeeeeeaaaa0000eeeeeeeeaaaa0000eeeeeeeeaaaa0000
def roots_51 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_53 : Nat := 0x33003300330033
def goal_53 : Nat := 0xfafaaaaafafa0000fafaaaaafafa0000fafaaaaafafa0000fafaaaaafafa0000
def roots_53 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xfefeeeeefafa0000fefeeeeefafa0000fefeeeeefafa0000fefeeeeefafa0000
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_57 : Nat := 0x303030303030303
def goal_57 : Nat := 0xffaaffaaaaaaaa00ffaaffaaaaaaaa00ffaaffaaaaaaaa00ffaaffaaaaaaaa00
def roots_57 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_58 : Nat := 0x505050505050505
def goal_58 : Nat := 0xffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00
def roots_58 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xffeeffeeeeaaee00ffeeffeeeeaaee00ffeeffeeeeaaee00ffeeffeeeeaaee00
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xfffaffaafafaaa00fffaffaafafaaa00fffaffaafafaaa00fffaffaafafaaa00
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_62 : Nat := 0x5555555555555555
def goal_62 : Nat := 0xfffcffccfcf0cc00fffcffccfcf0cc00fffcffccfcf0cc00fffcffccfcf0cc00
def roots_62 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfffeffeefefaee00fffeffeefefaee00fffeffeefefaee00fffeffeefefaee00
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_73 : Nat := 0x3030000000000000303
def goal_73 : Nat := 0xffaaffaaffaaffaaaa00aa00aa00aa00ffaaffaaffaaffaaaa00aa00aa00aa00
def roots_73 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_75 : Nat := 0xf0f0000000000000f0f
def goal_75 : Nat := 0xffaaffaaffaaffaaee00ee00ee00ee00ffaaffaaffaaffaaee00ee00ee00ee00
def roots_75 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_77 : Nat := 0x33330000000000003333
def goal_77 : Nat := 0xfffafffafffafffaaa00aa00aa00aa00fffafffafffafffaaa00aa00aa00aa00
def roots_77 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_78 : Nat := 0x55550000000000005555
def goal_78 : Nat := 0xfff0fff0fff0fff0cc00cc00cc00cc00fff0fff0fff0fff0cc00cc00cc00cc00
def roots_78 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_79 : Nat := 0xffff000000000000ffff
def goal_79 : Nat := 0xfffafffafffafffaee00ee00ee00ee00fffafffafffafffaee00ee00ee00ee00
def roots_79 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_81 : Nat := 0x300030000000000030003
def goal_81 : Nat := 0xffffaaaaffffaaaaaaaa0000aaaa0000ffffaaaaffffaaaaaaaa0000aaaa0000
def roots_81 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_84 : Nat := 0x1100110000000000110011
def goal_84 : Nat := 0xfffff0f0fffff0f0f0f00000f0f00000fffff0f0fffff0f0f0f00000f0f00000
def roots_84 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_85 : Nat := 0x3300330000000000330033
def goal_85 : Nat := 0xfffffafafffffafafafa0000fafa0000fffffafafffffafafafa0000fafa0000
def roots_85 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_89 : Nat := 0x30303030000000003030303
def goal_89 : Nat := 0xffffffaaffffffaaaaaaaa00aaaaaa00ffffffaaffffffaaaaaaaa00aaaaaa00
def roots_89 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_90 : Nat := 0x50505050000000005050505
def goal_90 : Nat := 0xffffff00ffffff00cc00cc00cc00cc00ffffff00ffffff00cc00cc00cc00cc00
def roots_90 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f
def goal_91 : Nat := 0xffffffaaffffffaaeeaaee00eeaaee00ffffffaaffffffaaeeaaee00eeaaee00
def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_92 : Nat := 0x111111110000000011111111
def goal_92 : Nat := 0xfffffff0fffffff0f0f00000f0f00000fffffff0fffffff0f0f00000f0f00000
def roots_92 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_93 : Nat := 0x333333330000000033333333
def goal_93 : Nat := 0xfffffffafffffffafafaaa00fafaaa00fffffffafffffffafafaaa00fafaaa00
def roots_93 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_94 : Nat := 0x555555550000000055555555
def goal_94 : Nat := 0xfffffff0fffffff0fcf0cc00fcf0cc00fffffff0fffffff0fcf0cc00fcf0cc00
def roots_94 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_95 : Nat := 0xffffffff00000000ffffffff
def goal_95 : Nat := 0xfffffffafffffffafefaee00fefaee00fffffffafffffffafefaee00fefaee00
def roots_95 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_97 : Nat := 0x3000000030000000300000003
def goal_97 : Nat := 0xffffffffaaaaaaaaaaaaaaaa00000000ffffffffaaaaaaaaaaaaaaaa00000000
def roots_97 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_99 : Nat := 0xf0000000f0000000f0000000f
def goal_99 : Nat := 0xffffffffaaaaaaaaeeeeeeee00000000ffffffffaaaaaaaaeeeeeeee00000000
def roots_99 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_101 : Nat := 0x33000000330000003300000033
def goal_101 : Nat := 0xfffffffffafafafaaaaaaaaa00000000fffffffffafafafaaaaaaaaa00000000
def roots_101 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_103 : Nat := 0xff000000ff000000ff000000ff
def goal_103 : Nat := 0xfffffffffafafafaeeeeeeee00000000fffffffffafafafaeeeeeeee00000000
def roots_103 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_104 : Nat := 0x101000001010000010100000101
def goal_104 : Nat := 0xffffffffff00ff00ff00ff0000000000ffffffffff00ff00ff00ff0000000000
def roots_104 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_105 : Nat := 0x303000003030000030300000303
def goal_105 : Nat := 0xffffffffffaaffaaffaaffaaaa00aa00ffffffffffaaffaaffaaffaaaa00aa00
def roots_105 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_106 : Nat := 0x505000005050000050500000505
def goal_106 : Nat := 0xffffffffff00ff00ffccffcccc00cc00ffffffffff00ff00ffccffcccc00cc00
def roots_106 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffffffffffaaffaaffeeffeeee00ee00ffffffffffaaffaaffeeffeeee00ee00
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_108 : Nat := 0x1111000011110000111100001111
def goal_108 : Nat := 0xfffffffffff0fff0ff00ff0000000000fffffffffff0fff0ff00ff0000000000
def roots_108 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_109 : Nat := 0x3333000033330000333300003333
def goal_109 : Nat := 0xfffffffffffafffaffaaffaaaa00aa00fffffffffffafffaffaaffaaaa00aa00
def roots_109 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_110 : Nat := 0x5555000055550000555500005555
def goal_110 : Nat := 0xfffffffffff0fff0ffccffcccc00cc00fffffffffff0fff0ffccffcccc00cc00
def roots_110 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xfffffffffffafffaffeeffeeee00ee00fffffffffffafffaffeeffeeee00ee00
def roots_111 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_113 : Nat := 0x30003000300030003000300030003
def goal_113 : Nat := 0xffffffffffffaaaaaaaaaaaaaaaa0000ffffffffffffaaaaaaaaaaaaaaaa0000
def roots_113 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_114 : Nat := 0x50005000500050005000500050005
def goal_114 : Nat := 0xffffffffffff0000cccccccc00000000ffffffffffff0000cccccccc00000000
def roots_114 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def goal_115 : Nat := 0xffffffffffffaaaaeeeeeeeeaaaa0000ffffffffffffaaaaeeeeeeeeaaaa0000
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_116 : Nat := 0x110011001100110011001100110011
def goal_116 : Nat := 0xfffffffffffff0f0f0f00000f0f00000fffffffffffff0f0f0f00000f0f00000
def roots_116 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_117 : Nat := 0x330033003300330033003300330033
def goal_117 : Nat := 0xfffffffffffffafafafaaaaafafa0000fffffffffffffafafafaaaaafafa0000
def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xfffffffffffff0f0fcfcccccf0f00000fffffffffffff0f0fcfcccccf0f00000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xfffffffffffffafafefeeeeefafa0000fffffffffffffafafefeeeeefafa0000
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_120 : Nat := 0x1010101010101010101010101010101
def goal_120 : Nat := 0xffffffffffffff00ff00ff0000000000ffffffffffffff00ff00ff0000000000
def roots_120 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_121 : Nat := 0x3030303030303030303030303030303
def goal_121 : Nat := 0xffffffffffffffaaffaaffaaaaaaaa00ffffffffffffffaaffaaffaaaaaaaa00
def roots_121 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_122 : Nat := 0x5050505050505050505050505050505
def goal_122 : Nat := 0xffffffffffffff00ffccffcccc00cc00ffffffffffffff00ffccffcccc00cc00
def roots_122 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffffffffffffffaaffeeffeeeeaaee00ffffffffffffffaaffeeffeeeeaaee00
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_124 : Nat := 0x11111111111111111111111111111111
def goal_124 : Nat := 0xfffffffffffffff0fff0ff00f0f00000fffffffffffffff0fff0ff00f0f00000
def roots_124 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xfffffffffffffffafffaffaafafaaa00fffffffffffffffafffaffaafafaaa00
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_126 : Nat := 0x55555555555555555555555555555555
def goal_126 : Nat := 0xfffffffffffffff0fffcffccfcf0cc00fffffffffffffff0fffcffccfcf0cc00
def roots_126 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xfffffffffffffffafffeffeefefaee00fffffffffffffffafffeffeefefaee00
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_139 : Nat := 0xf0f00000000000000000000000000000f0f
def goal_139 : Nat := 0xffccffccffccffccffccffccffccffccee00ee00ee00ee00ee00ee00ee00ee00
def roots_139 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_141 : Nat := 0x333300000000000000000000000000003333
def goal_141 : Nat := 0xfff0fff0fff0fff0fff0fff0fff0fff0aa00aa00aa00aa00aa00aa00aa00aa00
def roots_141 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_143 : Nat := 0xffff0000000000000000000000000000ffff
def goal_143 : Nat := 0xfffcfffcfffcfffcfffcfffcfffcfffcee00ee00ee00ee00ee00ee00ee00ee00
def roots_143 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_147 : Nat := 0xf000f000000000000000000000000000f000f
def goal_147 : Nat := 0xffffccccffffccccffffccccffffccccaaaa0000aaaa0000aaaa0000aaaa0000
def roots_147 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_149 : Nat := 0x33003300000000000000000000000000330033
def goal_149 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0fafa0000fafa0000fafa0000fafa0000
def roots_149 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_151 : Nat := 0xff00ff00000000000000000000000000ff00ff
def goal_151 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfcfafa0000fafa0000fafa0000fafa0000
def roots_151 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_154 : Nat := 0x505050500000000000000000000000005050505
def goal_154 : Nat := 0xffffffccffffffccffffffccffffffcccc00cc00cc00cc00cc00cc00cc00cc00
def roots_154 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def goal_155 : Nat := 0xffffffccffffffccffffffccffffffcceeaaee00eeaaee00eeaaee00eeaaee00
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_156 : Nat := 0x1111111100000000000000000000000011111111
def goal_156 : Nat := 0xfffffff0fffffff0fffffff0fffffff0f0f00000f0f00000f0f00000f0f00000
def roots_156 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_157 : Nat := 0x3333333300000000000000000000000033333333
def goal_157 : Nat := 0xfffffff0fffffff0fffffff0fffffff0fafaaa00fafaaa00fafaaa00fafaaa00
def roots_157 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_158 : Nat := 0x5555555500000000000000000000000055555555
def goal_158 : Nat := 0xfffffffcfffffffcfffffffcfffffffcfcf0cc00fcf0cc00fcf0cc00fcf0cc00
def roots_158 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_159 : Nat := 0xffffffff000000000000000000000000ffffffff
def goal_159 : Nat := 0xfffffffcfffffffcfffffffcfffffffcfefaee00fefaee00fefaee00fefaee00
def roots_159 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_163 : Nat := 0xf0000000f00000000000000000000000f0000000f
def goal_163 : Nat := 0xffffffffccccccccffffffffcccccccceeeeeeee00000000eeeeeeee00000000
def roots_163 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_165 : Nat := 0x330000003300000000000000000000003300000033
def goal_165 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0aaaaaaaa00000000aaaaaaaa00000000
def roots_165 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_168 : Nat := 0x1010000010100000000000000000000010100000101
def goal_168 : Nat := 0xffffffffff00ff00ffffffffff00ff00ff00ff0000000000ff00ff0000000000
def roots_168 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_169 : Nat := 0x3030000030300000000000000000000030300000303
def goal_169 : Nat := 0xffffffffff00ff00ffffffffff00ff00ffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_169 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_170 : Nat := 0x5050000050500000000000000000000050500000505
def goal_170 : Nat := 0xffffffffffccffccffffffffffccffccffccffcccc00cc00ffccffcccc00cc00
def roots_170 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_171 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
def goal_171 : Nat := 0xffffffffffccffccffffffffffccffccffeeffeeee00ee00ffeeffeeee00ee00
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_173 : Nat := 0x33330000333300000000000000000000333300003333
def goal_173 : Nat := 0xfffffffffff0fff0fffffffffff0fff0ffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_173 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_174 : Nat := 0x55550000555500000000000000000000555500005555
def goal_174 : Nat := 0xfffffffffffcfffcfffffffffffcfffcffccffcccc00cc00ffccffcccc00cc00
def roots_174 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_181 : Nat := 0x3300330033003300000000000000000033003300330033
def goal_181 : Nat := 0xfffffffffffff0f0fffffffffffff0f0fafaaaaafafa0000fafaaaaafafa0000
def roots_181 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_182 : Nat := 0x5500550055005500000000000000000055005500550055
def goal_182 : Nat := 0xfffffffffffffcfcfffffffffffffcfcfcfcccccf0f00000fcfcccccf0f00000
def roots_182 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_184 : Nat := 0x10101010101010100000000000000000101010101010101
def goal_184 : Nat := 0xffffffffffffff00ffffffffffffff00ff00ff0000000000ff00ff0000000000
def roots_184 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_185 : Nat := 0x30303030303030300000000000000000303030303030303
def goal_185 : Nat := 0xffffffffffffff00ffffffffffffff00ffaaffaaaaaaaa00ffaaffaaaaaaaa00
def roots_185 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_186 : Nat := 0x50505050505050500000000000000000505050505050505
def goal_186 : Nat := 0xffffffffffffffccffffffffffffffccffccffcccc00cc00ffccffcccc00cc00
def roots_186 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffffffffffccffffffffffffffccffeeffeeeeaaee00ffeeffeeeeaaee00
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_188 : Nat := 0x111111111111111100000000000000001111111111111111
def goal_188 : Nat := 0xfffffffffffffff0fffffffffffffff0fff0ff00f0f00000fff0ff00f0f00000
def roots_188 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_189 : Nat := 0x333333333333333300000000000000003333333333333333
def goal_189 : Nat := 0xfffffffffffffff0fffffffffffffff0fffaffaafafaaa00fffaffaafafaaa00
def roots_189 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_190 : Nat := 0x555555555555555500000000000000005555555555555555
def goal_190 : Nat := 0xfffffffffffffffcfffffffffffffffcfffcffccfcf0cc00fffcffccfcf0cc00
def roots_190 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_197 : Nat := 0x33000000000000003300000000000000330000000000000033
def goal_197 : Nat := 0xfafafafafafafafaf0f0f0f0f0f0f0f0fafafafafafafafa0000000000000000
def roots_197 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_198 : Nat := 0x55000000000000005500000000000000550000000000000055
def goal_198 : Nat := 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f00000000000000000
def roots_198 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_199 : Nat := 0xff00000000000000ff00000000000000ff00000000000000ff
def goal_199 : Nat := 0xfefefefefefefefefcfcfcfcfcfcfcfcfafafafafafafafa0000000000000000
def roots_199 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_201 : Nat := 0x303000000000000030300000000000003030000000000000303
def goal_201 : Nat := 0xffaaffaaffaaffaaff00ff00ff00ff00ffaaffaaffaaffaaaa00aa00aa00aa00
def roots_201 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_202 : Nat := 0x505000000000000050500000000000005050000000000000505
def goal_202 : Nat := 0xffccffccffccffccffccffccffccffccff00ff00ff00ff00cc00cc00cc00cc00
def roots_202 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffeeffeeffeeffeeffccffccffccffccffaaffaaffaaffaaee00ee00ee00ee00
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_205 : Nat := 0x3333000000000000333300000000000033330000000000003333
def goal_205 : Nat := 0xfffafffafffafffafff0fff0fff0fff0fffafffafffafffaaa00aa00aa00aa00
def roots_205 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_206 : Nat := 0x5555000000000000555500000000000055550000000000005555
def goal_206 : Nat := 0xfffcfffcfffcfffcfffcfffcfffcfffcfff0fff0fff0fff0cc00cc00cc00cc00
def roots_206 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_207 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def goal_207 : Nat := 0xfffefffefffefffefffcfffcfffcfffcfffafffafffafffaee00ee00ee00ee00
def roots_207 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_209 : Nat := 0x30003000000000003000300000000000300030000000000030003
def goal_209 : Nat := 0xffffaaaaffffaaaaffff0000ffff0000ffffaaaaffffaaaaaaaa0000aaaa0000
def roots_209 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_210 : Nat := 0x50005000000000005000500000000000500050000000000050005
def goal_210 : Nat := 0xffffccccffffccccffffccccffffccccffff0000ffff00000000000000000000
def roots_210 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffeeeeffffeeeeffffccccffffccccffffaaaaffffaaaaaaaa0000aaaa0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_212 : Nat := 0x110011000000000011001100000000001100110000000000110011
def goal_212 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0f0f00000f0f00000
def roots_212 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_213 : Nat := 0x330033000000000033003300000000003300330000000000330033
def goal_213 : Nat := 0xfffffafafffffafafffff0f0fffff0f0fffffafafffffafafafa0000fafa0000
def roots_213 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfcfffff0f0fffff0f0f0f00000f0f00000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xfffffefefffffefefffffcfcfffffcfcfffffafafffffafafafa0000fafa0000
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_217 : Nat := 0x3030303000000000303030300000000030303030000000003030303
def goal_217 : Nat := 0xffffffaaffffffaaffffff00ffffff00ffffffaaffffffaaaaaaaa00aaaaaa00
def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def goal_218 : Nat := 0xffffffccffffffccffffffccffffffccffffff00ffffff00cc00cc00cc00cc00
def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffffeeffffffeeffffffccffffffccffffffaaffffffaaeeaaee00eeaaee00
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_220 : Nat := 0x11111111000000001111111100000000111111110000000011111111
def goal_220 : Nat := 0xfffffff0fffffff0fffffff0fffffff0fffffff0fffffff0f0f00000f0f00000
def roots_220 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def goal_221 : Nat := 0xfffffffafffffffafffffff0fffffff0fffffffafffffffafafaaa00fafaaa00
def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xfffffffcfffffffcfffffffcfffffffcfffffff0fffffff0fcf0cc00fcf0cc00
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffefffffffefffffffcfffffffcfffffffafffffffafefaee00fefaee00
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_225 : Nat := 0x300000003000000030000000300000003000000030000000300000003
def goal_225 : Nat := 0xffffffffaaaaaaaaffffffff00000000ffffffffaaaaaaaaaaaaaaaa00000000
def roots_225 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_226 : Nat := 0x500000005000000050000000500000005000000050000000500000005
def goal_226 : Nat := 0xffffffffccccccccffffffffccccccccffffffff00000000cccccccc00000000
def roots_226 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def goal_227 : Nat := 0xffffffffeeeeeeeeffffffffccccccccffffffffaaaaaaaaeeeeeeee00000000
def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_229 : Nat := 0x3300000033000000330000003300000033000000330000003300000033
def goal_229 : Nat := 0xfffffffffafafafafffffffff0f0f0f0fffffffffafafafaaaaaaaaa00000000
def roots_229 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def goal_230 : Nat := 0xfffffffffcfcfcfcfffffffffcfcfcfcfffffffff0f0f0f0cccccccc00000000
def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_232 : Nat := 0x10100000101000001010000010100000101000001010000010100000101
def goal_232 : Nat := 0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ff00ff0000000000
def roots_232 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffaaffaaffffffffff00ff00ffffffffffaaffaaffaaffaaaa00aa00
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffccffccffffffffffccffccffffffffff00ff00ffccffcccc00cc00
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffeeffeeffffffffffccffccffffffffffaaffaaffeeffeeee00ee00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_236 : Nat := 0x111100001111000011110000111100001111000011110000111100001111
def goal_236 : Nat := 0xfffffffffff0fff0fffffffffff0fff0fffffffffff0fff0ff00ff0000000000
def roots_236 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xfffffffffffafffafffffffffff0fff0fffffffffffafffaffaaffaaaa00aa00
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_238 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def goal_238 : Nat := 0xfffffffffffcfffcfffffffffffcfffcfffffffffff0fff0ffccffcccc00cc00
def roots_238 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffefffefffffffffffcfffcfffffffffffafffaffeeffeeee00ee00
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_241 : Nat := 0x3000300030003000300030003000300030003000300030003000300030003
def goal_241 : Nat := 0xffffffffffffaaaaffffffffffff0000ffffffffffffaaaaaaaaaaaaaaaa0000
def roots_241 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def goal_242 : Nat := 0xffffffffffffccccffffffffffffccccffffffffffff0000cccccccc00000000
def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_244 : Nat := 0x11001100110011001100110011001100110011001100110011001100110011
def goal_244 : Nat := 0xfffffffffffff0f0fffffffffffff0f0fffffffffffff0f0f0f00000f0f00000
def roots_244 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_245 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
def goal_245 : Nat := 0xfffffffffffffafafffffffffffff0f0fffffffffffffafafafaaaaafafa0000
def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffffffcfcfffffffffffffcfcfffffffffffff0f0fcfcccccf0f00000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffefefffffffffffffcfcfffffffffffffafafefeeeeefafa0000
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_248 : Nat := 0x101010101010101010101010101010101010101010101010101010101010101
def goal_248 : Nat := 0xffffffffffffff00ffffffffffffff00ffffffffffffff00ff00ff0000000000
def roots_248 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffaaffffffffffffff00ffffffffffffffaaffaaffaaaaaaaa00
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffccffffffffffffffccffffffffffffff00ffccffcccc00cc00
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffeeffffffffffffffccffffffffffffffaaffeeffeeeeaaee00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_252 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
def goal_252 : Nat := 0xfffffffffffffff0fffffffffffffff0fffffffffffffff0fff0ff00f0f00000
def roots_252 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffafffffffffffffff0fffffffffffffffafffaffaafafaaa00
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffcfffffffffffffffcfffffffffffffff0fffcffccfcf0cc00
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffefffffffffffffffcfffffffffffffffafffeffeefefaee00
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
def isoMvS_42:List (Nat×Nat):=[(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_42:Lower true dom_42 roots_42 goal_42 4:=lower_iso_b isoMvS_42 (by decide +kernel) lowS_41
def isoMvS_73:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_73:Lower true dom_73 roots_73 goal_73 4:=lower_iso_b isoMvS_73 (by decide +kernel) lowS_41
def isoMvS_81:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_81:Lower true dom_81 roots_81 goal_81 4:=lower_iso_b isoMvS_81 (by decide +kernel) lowS_41
def isoMvS_84:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_84:Lower true dom_84 roots_84 goal_84 4:=lower_iso_b isoMvS_84 (by decide +kernel) lowS_41
def isoMvS_97:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_97:Lower true dom_97 roots_97 goal_97 4:=lower_iso_b isoMvS_97 (by decide +kernel) lowS_41
def isoMvS_104:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_104:Lower true dom_104 roots_104 goal_104 4:=lower_iso_b isoMvS_104 (by decide +kernel) lowS_41
def isoMvS_168:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_168:Lower true dom_168 roots_168 goal_168 4:=lower_iso_b isoMvS_168 (by decide +kernel) lowS_41
namespace S_27
def pG:List (Nat×Nat):=[(1,9),(1,17),(2,10),(3,11),(3,19),(8,9),(8,10),(16,17),(18,19),(18,26),(24,25),(24,26)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfff
def xsM:=roots_27.map (·&&&dom_27)
def gM:=goal_27&&&dom_27
def NN:Nat→Nat
|3=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x526b1
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0000f000f00c0c0c0ca0a0a0a
|_,_=>0
def sP:Nat→Nat
|0=>0xe4
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|_,_=>0
def wAt:=mkWire dB 4 28 0xfffffff
def SS:=mkSS wAt sP sO 2 7
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def mkPools (_ _:Nat):List (Nat×Nat×(Nat×List Nat)):=[]
def mkCut (_ _:Nat) (_:Nat×Nat×Nat) (_:List Nat):Bool:=false
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_27 gM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_27 gM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat×Nat)):=[[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_27==dom_27)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_27 gM v ys):RunD true dom_27 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_27 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s:Nat) (hs:s≤3):∀ i<NN s,bar dom_27 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 1 3=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤3) (h:RunD true dom_27 gM s xsM):False:=by
  have hmin:3≤s:=by have hl:=run_len h;change 4≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_27 roots_27 goal_27 4:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_27
theorem lowS_27:Lower true dom_27 roots_27 goal_27 4:=S_27.noCircuit
theorem lowS_43:Lower true dom_43 roots_43 goal_43 5:=lower_slice_b [(0xa0a00000a0a,8,9)] (by decide +kernel) lowS_42
theorem lowS_57:Lower true dom_57 roots_57 goal_57 5:=lower_slice_b [(0x303000003030000,1,17)] (by decide +kernel) lowS_41
namespace S_105
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(8,9),(8,40),(8,72),(32,33),(32,40),(32,96),(64,65),(64,72),(64,96)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfff
def xsM:=roots_105.map (·&&&dom_105)
def gM:=goal_105&&&dom_105
def NN:Nat→Nat
|3=>3
|4=>7
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0xa3c7b36bad0b047
|4,0=>0x5ef5a56d164b08941ad53e3192943b0e7df
|5,0=>0x8401343d8911e8a
|6,0=>0x84013
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xc0c0000080800000c0c0000080b03000003030000020200000202c0800000c0800000c0800000c0b03000003030000030300000202404000004000000040400000400030000000300000002000000020000000000000000c0c00000c0101000001010000010100000100c0c00000c0000000c0c00000c0303000003030000030300000000c0c00000c0c00000c0000000c0202000002020000020200000202c0c0000000000000c0c000000030000000300000003000000030080800000808000008080000080303000003030000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x3240324035240632407f240632e473d40c3240324b0324a093240328076543210
|_=>0
def sO:Nat→Nat→Nat
|3,0=>0x21022004
|4,0=>0xa952aa0536a5948a8c5
|5,0=>0xe51a2af5
|6,0=>0x3d4
|_,_=>0
def wAt:=mkWire dB 16 106 0x3ffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x204c1324d1404c1424c9204c1
|_=>0
def oO:Nat→Nat→Nat
|3,0=>0x200
|4,0=>0x62422200000000
|5,0=>0x9181
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0xf76530
|_=>0
def pmB:Nat→Nat→Nat
|3,0=>0x18
|4,0=>0x52000
|5,0=>0x12d
|6,0=>5
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 4 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_104 4 roots_104 ops++addP pm 1 dom_97 4 roots_97 ops++addP pm 2 dom_73 4 roots_73 ops++addP pm 3 dom_41 4 roots_41 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_105 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_104 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_97 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_41 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_104 4 s (0,roots_104.map (·&&&dom_104)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_105 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_104 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_105==dom_105)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_105 gM v ys):RunD true dom_105 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_105 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 3 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 7 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_105 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_105 gM s xsM):False:=by
  have hmin:3≤s:=by have hl:=run_len h;change 4≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_105 roots_105 goal_105 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_105
theorem lowS_105:Lower true dom_105 roots_105 goal_105 7:=S_105.noCircuit
def isoMvS_29:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_29:Lower true dom_29 roots_29 goal_29 4:=lower_iso_b isoMvS_29 (by decide +kernel) lowS_27
def isoMvS_51:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_51:Lower true dom_51 roots_51 goal_51 4:=lower_iso_b isoMvS_51 (by decide +kernel) lowS_27
def isoMvS_53:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_53:Lower true dom_53 roots_53 goal_53 4:=lower_iso_b isoMvS_53 (by decide +kernel) lowS_27
def isoMvS_75:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_75:Lower true dom_75 roots_75 goal_75 5:=lower_iso_b isoMvS_75 (by decide +kernel) lowS_57
def isoMvS_77:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_77:Lower true dom_77 roots_77 goal_77 5:=lower_iso_b isoMvS_77 (by decide +kernel) lowS_57
def isoMvS_78:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_78:Lower true dom_78 roots_78 goal_78 4:=lower_iso_b isoMvS_78 (by decide +kernel) lowS_27
def isoMvS_85:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_85:Lower true dom_85 roots_85 goal_85 5:=lower_iso_b isoMvS_85 (by decide +kernel) lowS_43
def isoMvS_89:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_89:Lower true dom_89 roots_89 goal_89 5:=lower_iso_b isoMvS_89 (by decide +kernel) lowS_43
def isoMvS_90:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_90:Lower true dom_90 roots_90 goal_90 4:=lower_iso_b isoMvS_90 (by decide +kernel) lowS_27
def isoMvS_92:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_92:Lower true dom_92 roots_92 goal_92 5:=lower_iso_b isoMvS_92 (by decide +kernel) lowS_57
def isoMvS_99:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_99:Lower true dom_99 roots_99 goal_99 5:=lower_iso_b isoMvS_99 (by decide +kernel) lowS_57
def isoMvS_101:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_101:Lower true dom_101 roots_101 goal_101 5:=lower_iso_b isoMvS_101 (by decide +kernel) lowS_57
def isoMvS_106:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_106:Lower true dom_106 roots_106 goal_106 5:=lower_iso_b isoMvS_106 (by decide +kernel) lowS_43
def isoMvS_108:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_108:Lower true dom_108 roots_108 goal_108 5:=lower_iso_b isoMvS_108 (by decide +kernel) lowS_57
def isoMvS_113:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_113:Lower true dom_113 roots_113 goal_113 5:=lower_iso_b isoMvS_113 (by decide +kernel) lowS_43
def isoMvS_114:List (Nat×Nat):=[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_114:Lower true dom_114 roots_114 goal_114 4:=lower_iso_b isoMvS_114 (by decide +kernel) lowS_27
def isoMvS_116:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_116:Lower true dom_116 roots_116 goal_116 5:=lower_iso_b isoMvS_116 (by decide +kernel) lowS_57
def isoMvS_120:List (Nat×Nat):=[(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_120:Lower true dom_120 roots_120 goal_120 5:=lower_iso_b isoMvS_120 (by decide +kernel) lowS_57
def isoMvS_139:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_139:Lower true dom_139 roots_139 goal_139 5:=lower_iso_b isoMvS_139 (by decide +kernel) lowS_57
def isoMvS_141:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_141:Lower true dom_141 roots_141 goal_141 4:=lower_iso_b isoMvS_141 (by decide +kernel) lowS_27
def isoMvS_147:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_147:Lower true dom_147 roots_147 goal_147 4:=lower_iso_b isoMvS_147 (by decide +kernel) lowS_27
def isoMvS_149:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_149:Lower true dom_149 roots_149 goal_149 5:=lower_iso_b isoMvS_149 (by decide +kernel) lowS_57
def isoMvS_154:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_154:Lower true dom_154 roots_154 goal_154 5:=lower_iso_b isoMvS_154 (by decide +kernel) lowS_57
def isoMvS_156:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_156:Lower true dom_156 roots_156 goal_156 5:=lower_iso_b isoMvS_156 (by decide +kernel) lowS_57
def isoMvS_163:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_163:Lower true dom_163 roots_163 goal_163 5:=lower_iso_b isoMvS_163 (by decide +kernel) lowS_57
def isoMvS_165:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_165:Lower true dom_165 roots_165 goal_165 4:=lower_iso_b isoMvS_165 (by decide +kernel) lowS_27
def isoMvS_169:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_169:Lower true dom_169 roots_169 goal_169 5:=lower_iso_b isoMvS_169 (by decide +kernel) lowS_43
def isoMvS_170:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_170:Lower true dom_170 roots_170 goal_170 7:=lower_iso_b isoMvS_170 (by decide +kernel) lowS_105
def isoMvS_184:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_184:Lower true dom_184 roots_184 goal_184 5:=lower_iso_b isoMvS_184 (by decide +kernel) lowS_57
def isoMvS_197:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_197:Lower true dom_197 roots_197 goal_197 4:=lower_iso_b isoMvS_197 (by decide +kernel) lowS_27
def isoMvS_198:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_198:Lower true dom_198 roots_198 goal_198 4:=lower_iso_b isoMvS_198 (by decide +kernel) lowS_27
def isoMvS_201:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_201:Lower true dom_201 roots_201 goal_201 5:=lower_iso_b isoMvS_201 (by decide +kernel) lowS_57
def isoMvS_202:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_202:Lower true dom_202 roots_202 goal_202 5:=lower_iso_b isoMvS_202 (by decide +kernel) lowS_57
def isoMvS_209:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_209:Lower true dom_209 roots_209 goal_209 5:=lower_iso_b isoMvS_209 (by decide +kernel) lowS_57
def isoMvS_210:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_210:Lower true dom_210 roots_210 goal_210 4:=lower_iso_b isoMvS_210 (by decide +kernel) lowS_27
def isoMvS_212:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_212:Lower true dom_212 roots_212 goal_212 5:=lower_iso_b isoMvS_212 (by decide +kernel) lowS_43
def isoMvS_225:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_225:Lower true dom_225 roots_225 goal_225 5:=lower_iso_b isoMvS_225 (by decide +kernel) lowS_57
def isoMvS_226:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_226:Lower true dom_226 roots_226 goal_226 5:=lower_iso_b isoMvS_226 (by decide +kernel) lowS_57
def isoMvS_232:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_232:Lower true dom_232 roots_232 goal_232 5:=lower_iso_b isoMvS_232 (by decide +kernel) lowS_43
theorem lowS_31:Lower true dom_31 roots_31 goal_31 5:=lower_slice_b [(0xcccccccc,8,10)] (by decide +kernel) lowS_29
def dzo_43_16:=0xf0f00000f0f0000
def gzo_43_16:=0xf0e00000e0a0000
def gsh_43_16:=0xf0e00000e0a
theorem lowS_zo_43_16_42:Lower true dzo_43_16 roots_43 gzo_43_16 5:=lower_iso_b (d1:=dom_43) (r1:=roots_43) (T1:=gsh_43_16) [(dom_43,16)] (by decide +kernel) (lower_slice_b (T:=gsh_43_16) [(0xa0a00000a0a,0,1)] (by decide +kernel) lowS_42)
namespace S_59
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(2,10),(2,34),(3,11),(3,19),(3,35),(8,9),(8,10),(8,40),(16,17),(18,19),(18,26),(18,50),(24,25),(24,26),(24,56),(32,33),(32,34),(32,40),(48,49),(48,50),(48,56)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_59.map (·&&&dom_59)
def gM:=goal_59&&&dom_59
def NN:Nat→Nat
|4=>1
|5=>1
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x116aa
|5,0=>0xa6f0
|6,0=>0x9abd7
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f0f000f00c0c0c0c0c0c0c0cf0f0f0f00000000f0f00000f0f0000f000f000f000f00a0a0a0a0a0a0a0a303030303000300
|_,_=>0
def sP:Nat→Nat
|0=>0x8d53a354c688
|_=>0
def sO:Nat→Nat→Nat
|4,0=>5
|5,0=>0x56
|6,0=>0xb5
|_,_=>0
def wAt:=mkWire dB 7 60 0xfffffffffffffff
def SS:=mkSS wAt sP sO 3 9
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x89
|_=>0
def oO:Nat→Nat→Nat
|5,0=>1
|_,_=>0
def PO:=mkPO wAt oP oO 8 3 7 5
def pmP:Nat→Nat
|0=>0x3f3c0
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>1
|6,0=>2
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 2 (j%128);fld (pmP (k/32)) 6 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_57 5 roots_57 ops++addP pm 1 dom_51 4 roots_51 ops++addP pm 2 dzo_43_16 5 roots_43 ops++addP pm 3 dom_43 5 roots_43 ops++addP pm 4 dom_42 4 roots_42 ops++addP pm 5 dom_27 4 roots_27 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_59 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_43_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_27 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_57 5 s (0,roots_57.map (·&&&dom_57)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_59 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_57 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_59==dom_59)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_59 gM v ys):RunD true dom_59 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_59 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_59 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 3 4=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_59 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_59 roots_59 goal_59 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_59
theorem lowS_59:Lower true dom_59 roots_59 goal_59 7:=S_59.noCircuit
def dzo_57_4:=0x3030303030303030
def gzo_57_4:=0x3030302030302000
def gsh_57_4:=0x303030203030200
theorem lowS_zo_57_4_41:Lower true dzo_57_4 roots_57 gzo_57_4 5:=lower_iso_b (d1:=dom_57) (r1:=roots_57) (T1:=gsh_57_4) [(dom_57,4)] (by decide +kernel) (lower_slice_b (T:=gsh_57_4) [(0x303000003030000,0,16)] (by decide +kernel) lowS_41)
namespace S_61
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(4,20),(5,13),(5,21),(5,37),(8,9),(8,40),(12,13),(12,28),(12,44),(16,17),(16,20),(24,25),(24,28),(24,56),(32,33),(32,40),(36,37),(36,44),(36,52),(48,49),(48,52),(48,56)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1ffffff
def xsM:=roots_61.map (·&&&dom_61)
def gM:=goal_61&&&dom_61
def NN:Nat→Nat
|4=>2
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xb6d8e19fc8
|5,0=>0xa5e019bec497d24
|6,0=>0xd596d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcccccccccc00cc00022002200220022cc88cc88cc88cc8b30033003300330000cc00cc0088008b333333300000000cccc0000cccc0003300330022002200c0c0c0c0c0c0c0c2222222222222222
|_,_=>0
def sP:Nat→Nat
|0=>0x436109436104361084376104310543210
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x15405
|5,0=>0x166418a6
|6,0=>0x1c5
|_,_=>0
def wAt:=mkWire dB 10 62 0x3fffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x182
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x20
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 5
def pmP:Nat→Nat
|0=>0xf9c40
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x19
|6,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 2 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_57 5 roots_57 ops++addP pm 1 dom_53 4 roots_53 ops++addP pm 2 dzo_57_4 5 roots_57 ops++addP pm 3 dom_41 4 roots_41 ops++addP pm 4 dom_29 4 roots_29 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_61 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_53 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_57_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_29 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_57 5 s (0,roots_57.map (·&&&dom_57)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_61 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_57 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_61==dom_61)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_61 gM v ys):RunD true dom_61 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_61 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_61 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 3 4=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_61 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_61 roots_61 goal_61 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_61
theorem lowS_61:Lower true dom_61 roots_61 goal_61 7:=S_61.noCircuit
theorem lowS_62:Lower true dom_62 roots_62 goal_62 6:=lower_slice_b [(0x5050505050505050,16,20),(0x5555000055550000,4,20)] (by decide +kernel) lowS_42
theorem lowS_79:Lower true dom_79 roots_79 goal_79 6:=lower_slice_b [(0xcccc000000000000cccc,8,10)] (by decide +kernel) lowS_77
namespace S_93
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(4,20),(4,68),(5,13),(5,21),(5,69),(8,9),(8,72),(12,13),(12,28),(12,76),(16,17),(16,20),(16,80),(24,25),(24,28),(24,88),(64,65),(64,68),(64,72),(64,80)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffff
def xsM:=roots_93.map (·&&&dom_93)
def gM:=goal_93&&&dom_93
def NN:Nat→Nat
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x4011c
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x333300000000000033330000cc00cc0000000000cc00cc030303030000000003030303088888888000000008888888b33333330000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x4688
|_=>0
def sO:Nat→Nat→Nat
|6,0=>5
|_,_=>0
def wAt:=mkWire dB 5 94 0x3fffffffffffffffffffffff
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
addP pm 0 dom_92 5 roots_92 ops++addP pm 1 dom_89 5 roots_89 ops++addP pm 2 dom_85 5 roots_85 ops++addP pm 3 dom_77 5 roots_77 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_93 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_92 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_77 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_92 5 s (0,roots_92.map (·&&&dom_92)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_93 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_92 h
def symsG:List (List (Nat×Nat)):=[[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_93==dom_93)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_93 gM v ys):RunD true dom_93 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_93 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_93 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_93 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_93 roots_93 goal_93 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_93
theorem lowS_93:Lower true dom_93 roots_93 goal_93 7:=S_93.noCircuit
theorem lowS_107:Lower true dom_107 roots_107 goal_107 8:=lower_slice_b [(0xc0c00000c0c00000c0c00000c0c,8,10)] (by decide +kernel) lowS_105
theorem lowS_109:Lower true dom_109 roots_109 goal_109 8:=lower_slice_b [(0x3030000030300000303000003030,64,68)] (by decide +kernel) lowS_105
namespace S_124
def pG:List (Nat×Nat):=[(4,20),(4,68),(8,40),(8,72),(12,28),(12,44),(12,76),(16,20),(16,80),(24,28),(24,56),(24,88),(32,40),(32,96),(36,44),(36,52),(36,100),(48,52),(48,56),(48,112),(64,68),(64,72),(64,80),(64,96)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_124.map (·&&&dom_124)
def gM:=goal_124&&&dom_124
def NN:Nat→Nat
|3=>1
|4=>4
|5=>10
|6=>4
|7=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x3281
|4,0=>0x4bcec2f7192359419d21
|5,0=>0x9a6f0951664bde8403c53d0471fa9e06f52067a90550901ab5
|6,0=>0x4243e1a9c2196d604f73
|7,0=>0x4f73
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x88888888808080808888888880808084444444444444444444444440000000220222022202220222002200220022000000000000000001110111011101110000000000808080800000000000000000000000440444040000000044004402222222222222200222222220000000101010101010101010101010101010100000000088888888000000008880888444444444444444400000000000000022220000222200002222000022220001111111110101010000000000000000088888888000000008888888800000004444444044444440444400004444000220022002200220022002200220022011111111111111111010101010101010
|0,1=>0x111111111111111111001100110011008888888888880000888888888888000040404040404040404040000040400000002222000022220000202000002021110111011101110111011101110111088808880888088800000000000000000404040404040404040004000400040000000002222222200000000000000011111111111111111111111110101010
|_,_=>0
def sP:Nat→Nat
|0=>0xca141865c0506b8ca1418650a0d11942830ca1b1861022a61942834c650a2467142834603285067b8a1418656850619581418650a0cb2850a324a1418a141cc32840418820
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|4,0=>0x26a3944a845
|5,0=>0x272c8684cf19b330654c918f3186
|6,0=>0xc8d79ac3535
|7,0=>0x6a5
|_,_=>0
def wAt:=mkWire dB 25 125 0x1fffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x9919519a282419a1879919941a
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x423100002111010000
|6,0=>0x81716100
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 8
def pmP:Nat→Nat
|0=>0xffbe625c9183080
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x450632100
|6,0=>0x8987
|7,0=>9
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 6 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_120 5 roots_120 ops++addP pm 1 dom_84 4 roots_84 ops++addP pm 2 dom_104 4 roots_104 ops++addP pm 3 dom_108 5 roots_108 ops++addP pm 4 dom_116 5 roots_116 ops++addP pm 5 dom_92 5 roots_92 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_124 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_120 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_104 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_108 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_92 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_120 5 s (0,roots_120.map (·&&&dom_120)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_124 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_120 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_124==dom_124)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_124 gM v ys):RunD true dom_124 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_124 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 4 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
theorem checked (s:Nat) (hs:s≤7):∀ i<NN s,bar dom_124 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤7) (h:RunD true dom_124 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_124 roots_124 goal_124 8:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_124
theorem lowS_124:Lower true dom_124 roots_124 goal_124 8:=S_124.noCircuit
theorem lowS_155:Lower true dom_155 roots_155 goal_155 6:=lower_slice_b [(0xa0a0a0a0000000000000000000000000a0a0a0a,8,9)] (by decide +kernel) lowS_154
theorem lowS_185:Lower true dom_185 roots_185 goal_185 6:=lower_slice_b [(0x20202020202020200000000000000000202020202020202,8,9)] (by decide +kernel) lowS_184
def isoMvS_55:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_55:Lower true dom_55 roots_55 goal_55 5:=lower_iso_b isoMvS_55 (by decide +kernel) lowS_31
def isoMvS_91:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_91:Lower true dom_91 roots_91 goal_91 7:=lower_iso_b isoMvS_91 (by decide +kernel) lowS_59
def isoMvS_94:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_94:Lower true dom_94 roots_94 goal_94 7:=lower_iso_b isoMvS_94 (by decide +kernel) lowS_61
def isoMvS_103:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_103:Lower true dom_103 roots_103 goal_103 6:=lower_iso_b isoMvS_103 (by decide +kernel) lowS_79
def isoMvS_110:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_110:Lower true dom_110 roots_110 goal_110 7:=lower_iso_b isoMvS_110 (by decide +kernel) lowS_59
def isoMvS_115:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_115:Lower true dom_115 roots_115 goal_115 7:=lower_iso_b isoMvS_115 (by decide +kernel) lowS_59
def isoMvS_117:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_117:Lower true dom_117 roots_117 goal_117 7:=lower_iso_b isoMvS_117 (by decide +kernel) lowS_93
def isoMvS_118:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_118:Lower true dom_118 roots_118 goal_118 7:=lower_iso_b isoMvS_118 (by decide +kernel) lowS_61
def isoMvS_121:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_121:Lower true dom_121 roots_121 goal_121 8:=lower_iso_b isoMvS_121 (by decide +kernel) lowS_107
def isoMvS_122:List (Nat×Nat):=[(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_122:Lower true dom_122 roots_122 goal_122 7:=lower_iso_b isoMvS_122 (by decide +kernel) lowS_59
def isoMvS_143:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_143:Lower true dom_143 roots_143 goal_143 6:=lower_iso_b isoMvS_143 (by decide +kernel) lowS_79
def isoMvS_151:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_151:Lower true dom_151 roots_151 goal_151 6:=lower_iso_b isoMvS_151 (by decide +kernel) lowS_79
def isoMvS_157:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_157:Lower true dom_157 roots_157 goal_157 6:=lower_iso_b isoMvS_157 (by decide +kernel) lowS_155
def isoMvS_158:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_158:Lower true dom_158 roots_158 goal_158 8:=lower_iso_b isoMvS_158 (by decide +kernel) lowS_124
def isoMvS_171:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_171:Lower true dom_171 roots_171 goal_171 8:=lower_iso_b isoMvS_171 (by decide +kernel) lowS_107
def isoMvS_173:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_173:Lower true dom_173 roots_173 goal_173 7:=lower_iso_b isoMvS_173 (by decide +kernel) lowS_59
def isoMvS_174:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_174:Lower true dom_174 roots_174 goal_174 8:=lower_iso_b isoMvS_174 (by decide +kernel) lowS_109
def isoMvS_181:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_181:Lower true dom_181 roots_181 goal_181 6:=lower_iso_b isoMvS_181 (by decide +kernel) lowS_155
def isoMvS_182:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_182:Lower true dom_182 roots_182 goal_182 8:=lower_iso_b isoMvS_182 (by decide +kernel) lowS_124
def isoMvS_186:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_186:Lower true dom_186 roots_186 goal_186 8:=lower_iso_b isoMvS_186 (by decide +kernel) lowS_109
def isoMvS_188:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_188:Lower true dom_188 roots_188 goal_188 8:=lower_iso_b isoMvS_188 (by decide +kernel) lowS_124
def isoMvS_199:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_199:Lower true dom_199 roots_199 goal_199 5:=lower_iso_b isoMvS_199 (by decide +kernel) lowS_31
def isoMvS_203:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_203:Lower true dom_203 roots_203 goal_203 8:=lower_iso_b isoMvS_203 (by decide +kernel) lowS_124
def isoMvS_205:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_205:Lower true dom_205 roots_205 goal_205 6:=lower_iso_b isoMvS_205 (by decide +kernel) lowS_155
def isoMvS_206:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_206:Lower true dom_206 roots_206 goal_206 6:=lower_iso_b isoMvS_206 (by decide +kernel) lowS_155
def isoMvS_211:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_211:Lower true dom_211 roots_211 goal_211 7:=lower_iso_b isoMvS_211 (by decide +kernel) lowS_61
def isoMvS_213:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_213:Lower true dom_213 roots_213 goal_213 7:=lower_iso_b isoMvS_213 (by decide +kernel) lowS_93
def isoMvS_214:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_214:Lower true dom_214 roots_214 goal_214 7:=lower_iso_b isoMvS_214 (by decide +kernel) lowS_59
def isoMvS_217:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_217:Lower true dom_217 roots_217 goal_217 6:=lower_iso_b isoMvS_217 (by decide +kernel) lowS_185
def isoMvS_218:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_218:Lower true dom_218 roots_218 goal_218 6:=lower_iso_b isoMvS_218 (by decide +kernel) lowS_155
def isoMvS_220:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_220:Lower true dom_220 roots_220 goal_220 6:=lower_iso_b isoMvS_220 (by decide +kernel) lowS_185
def isoMvS_227:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_227:Lower true dom_227 roots_227 goal_227 8:=lower_iso_b isoMvS_227 (by decide +kernel) lowS_124
def isoMvS_229:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_229:Lower true dom_229 roots_229 goal_229 6:=lower_iso_b isoMvS_229 (by decide +kernel) lowS_155
def isoMvS_230:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_230:Lower true dom_230 roots_230 goal_230 6:=lower_iso_b isoMvS_230 (by decide +kernel) lowS_155
def isoMvS_233:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_233:Lower true dom_233 roots_233 goal_233 8:=lower_iso_b isoMvS_233 (by decide +kernel) lowS_107
def isoMvS_234:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_234:Lower true dom_234 roots_234 goal_234 8:=lower_iso_b isoMvS_234 (by decide +kernel) lowS_107
def isoMvS_236:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_236:Lower true dom_236 roots_236 goal_236 6:=lower_iso_b isoMvS_236 (by decide +kernel) lowS_185
def isoMvS_241:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_241:Lower true dom_241 roots_241 goal_241 6:=lower_iso_b isoMvS_241 (by decide +kernel) lowS_185
def isoMvS_242:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_242:Lower true dom_242 roots_242 goal_242 6:=lower_iso_b isoMvS_242 (by decide +kernel) lowS_155
def isoMvS_244:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_244:Lower true dom_244 roots_244 goal_244 6:=lower_iso_b isoMvS_244 (by decide +kernel) lowS_185
def isoMvS_248:List (Nat×Nat):=[(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_248:Lower true dom_248 roots_248 goal_248 6:=lower_iso_b isoMvS_248 (by decide +kernel) lowS_185
theorem lowS_63:Lower true dom_63 roots_63 goal_63 8:=lower_slice_b [(0xcccccccccccccccc,8,10)] (by decide +kernel) lowS_61
def dzo_93_2:=0xcccccccc00000000cccccccc
def gzo_93_2:=0xccccccc800000000ccc8cc00
def gsh_93_2:=0x333333320000000033323300
theorem lowS_zo_93_2_85:Lower true dzo_93_2 roots_93 gzo_93_2 6:=lower_iso_b (d1:=dom_93) (r1:=roots_93) (T1:=gsh_93_2) [(dom_93,2)] (by decide +kernel) (lower_slice_b (T:=gsh_93_2) [(0x330033000000000033003300,0,8)] (by decide +kernel) lowS_85)
def dzo_85_2:=0xcc00cc0000000000cc00cc
def gzo_85_2:=0xcc00c80000000000c80000
def gsh_85_2:=0x3300320000000000320000
theorem lowS_zo_85_2_85:Lower true dzo_85_2 roots_85 gzo_85_2 5:=lower_iso_b (d1:=dom_85) (r1:=roots_85) (T1:=gsh_85_2) [(dom_85,2)] (by decide +kernel) (lower_slice_b (T:=gsh_85_2) [] (by decide +kernel) lowS_85)
namespace S_95
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(2,10),(3,11),(3,19),(3,67),(4,20),(4,68),(5,13),(5,21),(5,69),(6,14),(6,22),(6,70),(7,15),(7,23),(7,71),(8,9),(8,10),(8,72),(12,13),(12,14),(12,28),(12,76),(16,17),(16,20),(16,80),(18,19),(18,22),(18,26),(18,82),(24,25),(24,26),(24,28),(24,88),(64,65),(64,68),(64,72),(64,80),(66,67),(66,70),(66,74),(66,82)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_95.map (·&&&dom_95)
def gM:=goal_95&&&dom_95
def NN:Nat→Nat
|4=>3
|5=>10
|6=>17
|7=>7
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x44f983d51c01dec
|5,0=>0xdbd85d96cf84b6c814366b55a6667d616d2419c0339792fe2a
|6,0=>0xf8e2df4153d6302c9547c75f0c0be3af52e9323b700976f9fe6f78a654e262b886055f4fe621bd920c6f3
|7,0=>0xfddb0e1246da081bf2a14d1952bb092a996
|8,0=>0xc3264
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f000f000000000f0f00003300ffff0000000033003300ffffffff00000000ccccccccffffff0000000000000000003300330000000000330033000f0f0f0f000000000f0f0000ffffffff0000000000000000ffff000000000000ffff0000ffffffff00000000ff00ff00fffffff000000000f0f0f0f0aaaaaaaa00000000aaaaaaaaffffffff00000000ffff0000ff00ff0000000000ff00ff00f0f0f0f000000000f0f0f0f0cccccccc00000000ccccccccffffffaa00000000aaaaaaaa
|0,1=>0xff00000000000000000000000000000000ffffff00ffffffff000000003300330000ff00ff0000000000ff0000ff00ffff00000000ff00ff0000ff00ff0000000000000000ffff00ff00000000ffff0000ccccffff00000000ccccccccffffffff00000000ffffff000000ffff000000000000ff000000ffff0000000000000000ffffff0000000000ffffff000f0f0f0f000000000f0f0f00555555550000000055555500
|_,_=>0
def sP:Nat→Nat
|0=>0x104a962062b152440c455a6a818825491030954940c412d128188ab4ce48388254a0612c528188304a0e209588184af4a06609528188ae4a06d2a92418825620655a928188204a0e208083304a418820
|1=>0x40c412a5031156940c412a67240c412a503104a9c20e3104a940c4d2a488188254a0612a928188254f788188254c883104a940c45da503104ba4a323104a9220626953740c412a503
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0xa5055005
|5,0=>0x4563f63963362d62762161b61560f6
|6,0=>0xb96b27ab7a479e69779078978277b77566e76776075975274b7
|7,0=>0xe86e17da7d37cc7c66bf7
|8,0=>0xee6
|_,_=>0
def wAt:=mkWire dB 30 96 0xffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x18742640d1a61a50a542520b42592640d92740d40d4255a518720f4251cd4260a54254611a692440d0cd42618742541d1a520b42518742640d1a5
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x1e2709a26096250922408e2308a2208621080008802
|7,0=>0x261946418c62184601
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 10
def pmP:Nat→Nat
|0=>0xfffdbd7d594c483f3d382b1410090600
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x299659943c54b401a
|7,0=>0x8dceefd
|8,0=>7
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 8 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_94 7 roots_94 ops++addP pm 1 dzo_93_2 6 roots_93 ops++addP pm 2 dom_79 6 roots_79 ops++addP pm 3 dom_93 7 roots_93 ops++addP pm 4 dom_91 7 roots_91 ops++addP pm 5 dom_85 5 roots_85 ops++addP pm 6 dzo_85_2 5 roots_85 ops++addP pm 7 dom_31 5 roots_31 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_95 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_93_2_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_79 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_85_2_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_31 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_94 7 s (0,roots_94.map (·&&&dom_94)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_95 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_94 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_95 gM v ys):RunD true dom_95 gM v (ori ys):=h
def Z (s:Nat):=barP dom_95 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 17 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 17 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 7 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_95 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 4 5=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_95 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_95 roots_95 goal_95 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_95
theorem lowS_95:Lower true dom_95 roots_95 goal_95 9:=S_95.noCircuit
theorem lowS_111:Lower true dom_111 roots_111 goal_111 9:=lower_slice_b [(0xcccc0000cccc0000cccc0000cccc,8,10)] (by decide +kernel) lowS_109
def dzo_89_2:=0xc0c0c0c000000000c0c0c0c
def gzo_89_2:=0xc0c0c08000000000c080c00
def gsh_89_2:=0x30303020000000003020300
theorem lowS_zo_89_2_81:Lower true dzo_89_2 roots_89 gzo_89_2 5:=lower_iso_b (d1:=dom_89) (r1:=roots_89) (T1:=gsh_89_2) [(dom_89,2)] (by decide +kernel) (lower_slice_b (T:=gsh_89_2) [(0x30003000000000003000300,0,8)] (by decide +kernel) lowS_81)
def dzo_81_2:=0xc000c00000000000c000c
def gzo_81_2:=0xc00080000000000080000
def gsh_81_2:=0x300020000000000020000
theorem lowS_zo_81_2_81:Lower true dzo_81_2 roots_81 gzo_81_2 4:=lower_iso_b (d1:=dom_81) (r1:=roots_81) (T1:=gsh_81_2) [(dom_81,2)] (by decide +kernel) (lower_slice_b (T:=gsh_81_2) [] (by decide +kernel) lowS_81)
def dzo_42_16:=0x505000005050000
def gzo_42_16:=0x504000004000000
def gsh_42_16:=0x50400000400
theorem lowS_zo_42_16_42:Lower true dzo_42_16 roots_42 gzo_42_16 4:=lower_iso_b (d1:=dom_42) (r1:=roots_42) (T1:=gsh_42_16) [(dom_42,16)] (by decide +kernel) (lower_slice_b (T:=gsh_42_16) [] (by decide +kernel) lowS_42)
def dzo_121_2:=0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
def gzo_121_2:=0xc0c0c0c0c0c0c080c0c0c0c0c080c00
def gsh_121_2:=0x3030303030303020303030303020300
theorem lowS_zo_121_2_81:Lower true dzo_121_2 roots_121 gzo_121_2 6:=lower_iso_b (d1:=dom_121) (r1:=roots_121) (T1:=gsh_121_2) [(dom_121,2)] (by decide +kernel) (lower_slice_b (T:=gsh_121_2) [(0x3000300030003000300030003000300,0,8),(0x3030303000000000303030300000000,0,32)] (by decide +kernel) lowS_81)
def dzo_107_16:=0xf0f00000f0f00000f0f00000f0f0000
def gzo_107_16:=0xf0f00000f0f00000f0e00000e0a0000
def gsh_107_16:=0xf0f00000f0f00000f0e00000e0a
theorem lowS_zo_107_16_42:Lower true dzo_107_16 roots_107 gzo_107_16 6:=lower_iso_b (d1:=dom_107) (r1:=roots_107) (T1:=gsh_107_16) [(dom_107,16)] (by decide +kernel) (lower_slice_b (T:=gsh_107_16) [(0xa0a00000a0a00000a0a00000a0a,0,1),(0xf0f00000f0f0000000000000000,0,64)] (by decide +kernel) lowS_42)
def dzo_113_2:=0xc000c000c000c000c000c000c000c
def gzo_113_2:=0xc000c000c0008000c000c00080000
def gsh_113_2:=0x30003000300020003000300020000
theorem lowS_zo_113_2_81:Lower true dzo_113_2 roots_113 gzo_113_2 5:=lower_iso_b (d1:=dom_113) (r1:=roots_113) (T1:=gsh_113_2) [(dom_113,2)] (by decide +kernel) (lower_slice_b (T:=gsh_113_2) [(0x30003000000000003000300000000,0,32)] (by decide +kernel) lowS_81)
def dzo_106_16:=0x5050000050500000505000005050000
def gzo_106_16:=0x5050000050500000504000004000000
def gsh_106_16:=0x505000005050000050400000400
theorem lowS_zo_106_16_42:Lower true dzo_106_16 roots_106 gzo_106_16 5:=lower_iso_b (d1:=dom_106) (r1:=roots_106) (T1:=gsh_106_16) [(dom_106,16)] (by decide +kernel) (lower_slice_b (T:=gsh_106_16) [(0x505000005050000000000000000,0,64)] (by decide +kernel) lowS_42)
namespace S_123
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(2,10),(2,34),(3,11),(3,19),(3,35),(3,67),(8,9),(8,10),(8,40),(8,72),(16,17),(16,80),(18,19),(18,26),(18,50),(18,82),(24,25),(24,26),(24,56),(24,88),(32,33),(32,34),(32,40),(32,96),(48,49),(48,50),(48,56),(48,112),(64,65),(64,72),(64,80),(64,96),(66,67),(66,74),(66,82),(66,98)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_123.map (·&&&dom_123)
def gM:=goal_123&&&dom_123
def NN:Nat→Nat
|4=>3
|5=>12
|6=>20
|7=>13
|8=>3
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xe219c21e2d114b1
|5,0=>0x5b1e258fcd58e995838c56ce83a7983390d2d74c1d42312494117ce091b3
|6,0=>0x682be5e77543d25436d239f503833437db4274b61ddb31dd37174021667d107f50fa5b0d1770c09c0acad05d3a03dca024bd
|7,0=>0x52ca74f6444643a446b5424f32e1d02cd92224591fafa16fdc1489e0ca2c001c7
|8,0=>0x47c680e7a107721
|9,0=>0x62b5b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f0a0a0a0a0f0f0f0f0a0a0a0af0f0f0f0f0f0f0f0f000f000f000f0000000000f0f0f0f000000000f000f00f0f0f0f000000000f0f0f0f00000000f000f000f000f000f000f000f000f00a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a3030f0f03000f0f03030b0b03000b0af0f0f0f0f0f0f0f0000000000000000f0f0f0f0f000f000f0f0f0f0f000f00f0a0f0a0f0a0f0a0f0a0f0a00000000f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f0f0f0f0f00000000f0f00000f0f00000f0f00000f0f0000f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0af0f0f0f0a0a0a0a0f000f000a000a00c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
|0,1=>0xf0a0f0a000000000f0a0f0af0f0f0f0f0f0f0f000000000f0a0f0af0f0f0f0f0f00000f0f0f0f0f0f0000f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0cf0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a000000000000000000f000f000a000a5050505050505050500050005000500f0f0f0f0f0f0f000f0f0f0f0f0f0f0050505050505050505050505000000000000000000000000b0b0b0b0b0a0b0af0f0f0f0f0f0f0f0303030303000300f0f0f0f0f000f0f0f0f0f0f0f000f0a30303030300030003030303030003000000f0f00000f0f00000a0a00000a0af0f0f0f0f0a0f0a0f0f0f0f0f0a0f0af0f0f0f0f0f0f0f0e0e0e0e0e0e0e0e
|0,2=>0xe0e0e0e0e0e0e0ef0f0f0f0f0f0f0f0f0f0f0f0f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0a0f0ae0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e00f000f000f000f000f000f000a000af0f0f000f0f0f000f0f0f000f0f0f0000000000f0f0f00000000000f0f0f00
|_,_=>0
def sP:Nat→Nat
|0=>0x70a6cc0c22c02073c308020c0cb00a68810c0cb00a65810b00a2070cb00a5c84440ce00a3032d62883032c529550c2c028830b29348844c0ce0053c40cb40c0c638028f10308e00710308014c0c20053470c600a20c2ca2481c31801440c2040
|1=>0x70a20f1032c028860c2c02883032c02992073030802883cc84b00a20f30338b00594c0cb0052873c32c01483032c100a21d10e2c02a43032c02883032c529320c0cb29520430308e00a6cf3032e320c0cb00a88830200a8083032c029e21d10b
|2=>0x3032c02883032c014a20c0cb8ca2043032c02883032ca4c83cc0ce2c028810c0cb70a1cc0cb0052883032e628844c0c22c028894c0cb00a20c84b
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x2940aa005
|5,0=>0x283129888c3e61c30c985aa27610b06d82ac0f6
|6,0=>0x6a3b35d8cebf75cb2c9d56ea564f3a5dd20e8a641b9f94eee71635398dcbac567
|7,0=>0x12e6934481a31112685440ddfacf677833a5dc4edb7
|8,0=>0x505e76d347
|9,0=>0x1486
|_,_=>0
def wAt:=mkWire dB 39 124 0xfffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x2884b3120a4f3830a4b210cc4b21308471530b4a21288401e2cc53210078b3100a4f2130a5b2f10a4c2128b61330cb487d08cca2d3084331008453120a4c2930b4a2d38acb211c34b3120c442b2cc483108c4a2d1ca4c2d20a4a311404a2130844082ca4c2130b4829288440820c4a2d
|1=>0x2884029308401e2cc4c292c840213084c2d288632300a423128b442d20c432d0084a3120c61310cb4e2b2c84c2d28b432d28c48291c84c2d
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x2040000000000034c4a06300010818803
|6,0=>0x842fcde93a36e6d0d89ae3000acd41a534467cce91a3000608a9923
|7,0=>0x5b2b255caa9532a253ca694b29251ca29432
|8,0=>0x17c6f0dd1
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0xd2ef5840662c2010040a85c90426a48103f2c081b1604048201fef780b97240073de00298b000eed800676c002314000dcb0006e40002d2c0013160008400003200001400000886000440000204000100800030000014800006000001f8000080000000
|1=>0x6002926001696802c8b2426e5909262c405796200d8b
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0xc000000308500b044
|6,0=>0x20c2d058975121819b19728e00770a
|7,0=>0x1e3d56939a17e48a0963
|8,0=>0x19494
|9,0=>0xd
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 25 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_121 8 roots_121 ops++addP pm 1 dom_107 8 roots_107 ops++addP pm 2 dzo_89_2 5 roots_89 ops++addP pm 3 dom_91 7 roots_91 ops++addP pm 4 dom_120 5 roots_120 ops++addP pm 5 dom_57 5 roots_57 ops++addP pm 6 dzo_81_2 4 roots_81 ops++addP pm 7 dom_59 7 roots_59 ops++addP pm 8 dom_115 7 roots_115 ops++addP pm 9 dom_81 4 roots_81 ops++addP pm 10 dzo_42_16 4 roots_42 ops++addP pm 11 dom_122 7 roots_122 ops++addP pm 12 dzo_121_2 6 roots_121 ops++addP pm 13 dom_27 4 roots_27 ops++addP pm 14 dzo_107_16 6 roots_107 ops++addP pm 15 dom_75 5 roots_75 ops++addP pm 16 dom_105 7 roots_105 ops++addP pm 17 dzo_43_16 5 roots_43 ops++addP pm 18 dom_42 4 roots_42 ops++addP pm 19 dom_99 5 roots_99 ops++addP pm 20 dzo_113_2 5 roots_113 ops++addP pm 21 dom_51 4 roots_51 ops++addP pm 22 dzo_106_16 5 roots_106 ops++addP pm 23 dom_90 4 roots_90 ops++addP pm 24 dom_114 4 roots_114 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_123 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_89_2_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_120 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_81_2_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_42_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_121_2_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_107_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_43_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_zo_113_2_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_zo_106_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_114 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_121 8 s (0,roots_121.map (·&&&dom_121)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_123 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_121 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_123==dom_123)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_123 gM v ys):RunD true dom_123 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_123 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 12 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 20 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 20 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 13 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 13 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 3 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_123 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_123 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_123 roots_123 goal_123 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_123
theorem lowS_123:Lower true dom_123 roots_123 goal_123 10:=S_123.noCircuit
namespace S_125
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(4,20),(4,68),(5,13),(5,21),(5,37),(5,69),(8,9),(8,40),(8,72),(12,13),(12,28),(12,44),(12,76),(16,17),(16,20),(16,80),(24,25),(24,28),(24,56),(24,88),(32,33),(32,40),(32,96),(36,37),(36,44),(36,52),(36,100),(48,49),(48,52),(48,56),(48,112),(64,65),(64,68),(64,72),(64,80),(64,96)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_125.map (·&&&dom_125)
def gM:=goal_125&&&dom_125
def NN:Nat→Nat
|6=>1
|7=>5
|8=>2
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x28b9c
|7,0=>0xc19e396df88e6608c64e11e83
|8,0=>0x74b3a213f1
|9,0=>0x7f2e4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x3333333333333333333333333300330000cc00cc00cc00cc00cc00cc000000033003300330033003300330033003300cccccccc00000000cccccccc000000033333333333333330000000000000000cccccccccc00cc00cccccccccc00cc033333333333333333333333300000000cccc0000cccc0000cccc0000cccc00033333333333333333300330033003300c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c22222222222222222222222222222222
|_,_=>0
def sP:Nat→Nat
|0=>0x738106473810657381064732810a7381065438106a47381067381096543210
|_=>0
def sO:Nat→Nat→Nat
|6,0=>6
|7,0=>0x23771d5736067
|8,0=>0xc5ea7
|9,0=>0x386
|_,_=>0
def wAt:=mkWire dB 11 126 0x3fffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1d97861976559785d98752176523765e1865d9
|_=>0
def oO:Nat→Nat→Nat
|6,0=>3
|7,0=>0xb292725232
|8,0=>0xe1d1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0xfff32ff3f7f9fc7e00
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>1
|7,0=>0x3f72
|8,0=>0x14
|9,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 9 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_124 8 roots_124 ops++addP pm 1 dom_121 8 roots_121 ops++addP pm 2 dom_117 7 roots_117 ops++addP pm 3 dom_93 7 roots_93 ops++addP pm 4 dom_61 7 roots_61 ops++addP pm 5 dom_109 8 roots_109 ops++addP pm 6 dom_29 4 roots_29 ops++addP pm 7 dom_53 4 roots_53 ops++addP pm 8 dom_85 5 roots_85 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_125 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_29 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_53 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_85 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_124 8 s (0,roots_124.map (·&&&dom_124)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_125 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_124 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_125==dom_125)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_125 gM v ys):RunD true dom_125 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_125 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 5 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 2 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_125 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z6 i (Nat.zero_le i) hi
  · exact z7 i (Nat.zero_le i) hi
  · exact z8 i (Nat.zero_le i) hi
  · exact z9 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 5 5=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_125 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_125 roots_125 goal_125 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_125
theorem lowS_125:Lower true dom_125 roots_125 goal_125 10:=S_125.noCircuit
def dzo_84_2:=0x4400440000000000440044
def gzo_84_2:=0x4400400000000000400000
def gsh_84_2:=0x1100100000000000100000
theorem lowS_zo_84_2_84:Lower true dzo_84_2 roots_84 gzo_84_2 4:=lower_iso_b (d1:=dom_84) (r1:=roots_84) (T1:=gsh_84_2) [(dom_84,2)] (by decide +kernel) (lower_slice_b (T:=gsh_84_2) [] (by decide +kernel) lowS_84)
def dzo_58_4:=0x5050505050505050
def gzo_58_4:=0x5050504050504000
def gsh_58_4:=0x505050405050400
theorem lowS_zo_58_4_42:Lower true dzo_58_4 roots_58 gzo_58_4 5:=lower_iso_b (d1:=dom_58) (r1:=roots_58) (T1:=gsh_58_4) [(dom_58,4)] (by decide +kernel) (lower_slice_b (T:=gsh_58_4) [(0x505000005050000,0,16)] (by decide +kernel) lowS_42)
def dzo_46_16:=0x5555000055550000
def gzo_46_16:=0x5554000054500000
def gsh_46_16:=0x555400005450
theorem lowS_zo_46_16_42:Lower true dzo_46_16 roots_46 gzo_46_16 5:=lower_iso_b (d1:=dom_46) (r1:=roots_46) (T1:=gsh_46_16) [(dom_46,16)] (by decide +kernel) (lower_slice_b (T:=gsh_46_16) [(0x505000005050,0,4)] (by decide +kernel) lowS_42)
def dzo_116_2:=0x440044004400440044004400440044
def gzo_116_2:=0x440044004400400044004400400000
def gsh_116_2:=0x110011001100100011001100100000
theorem lowS_zo_116_2_84:Lower true dzo_116_2 roots_116 gzo_116_2 5:=lower_iso_b (d1:=dom_116) (r1:=roots_116) (T1:=gsh_116_2) [(dom_116,2)] (by decide +kernel) (lower_slice_b (T:=gsh_116_2) [(0x110011000000000011001100000000,0,32)] (by decide +kernel) lowS_84)
def dzo_110_16:=0x55550000555500005555000055550000
def gzo_110_16:=0x55550000555500005554000054500000
def gsh_110_16:=0x5555000055550000555400005450
theorem lowS_zo_110_16_42:Lower true dzo_110_16 roots_110 gzo_110_16 6:=lower_iso_b (d1:=dom_110) (r1:=roots_110) (T1:=gsh_110_16) [(dom_110,16)] (by decide +kernel) (lower_slice_b (T:=gsh_110_16) [(0x5050000050500000505000005050,0,4),(0x5555000055550000000000000000,0,64)] (by decide +kernel) lowS_42)
def dzo_124_2:=0x44444444444444444444444444444444
def gzo_124_2:=0x44444444444444404444444444404400
def gsh_124_2:=0x11111111111111101111111111101100
theorem lowS_zo_124_2_84:Lower true dzo_124_2 roots_124 gzo_124_2 6:=lower_iso_b (d1:=dom_124) (r1:=roots_124) (T1:=gsh_124_2) [(dom_124,2)] (by decide +kernel) (lower_slice_b (T:=gsh_124_2) [(0x11001100110011001100110011001100,0,8),(0x11111111000000001111111100000000,0,32)] (by decide +kernel) lowS_84)
def dzo_122_4:=0x50505050505050505050505050505050
def gzo_122_4:=0x50505050505050505050504050504000
def gsh_122_4:=0x5050505050505050505050405050400
theorem lowS_zo_122_4_42:Lower true dzo_122_4 roots_122 gzo_122_4 6:=lower_iso_b (d1:=dom_122) (r1:=roots_122) (T1:=gsh_122_4) [(dom_122,4)] (by decide +kernel) (lower_slice_b (T:=gsh_122_4) [(0x5050000050500000505000005050000,0,16),(0x5050505050505050000000000000000,0,64)] (by decide +kernel) lowS_42)
def dzo_92_2:=0x444444440000000044444444
def gzo_92_2:=0x444444400000000044404400
def gsh_92_2:=0x111111100000000011101100
theorem lowS_zo_92_2_84:Lower true dzo_92_2 roots_92 gzo_92_2 5:=lower_iso_b (d1:=dom_92) (r1:=roots_92) (T1:=gsh_92_2) [(dom_92,2)] (by decide +kernel) (lower_slice_b (T:=gsh_92_2) [(0x110011000000000011001100,0,8)] (by decide +kernel) lowS_84)
def dzo_106_4:=0x5050000050500000505000005050
def gzo_106_4:=0x5050000050500000504000004000
def gsh_106_4:=0x505000005050000050400000400
theorem lowS_zo_106_4_42:Lower true dzo_106_4 roots_106 gzo_106_4 5:=lower_iso_b (d1:=dom_106) (r1:=roots_106) (T1:=gsh_106_4) [(dom_106,4)] (by decide +kernel) (lower_slice_b (T:=gsh_106_4) [(0x505000005050000000000000000,0,64)] (by decide +kernel) lowS_42)
namespace S_126
def pG:List (Nat×Nat):=[(2,10),(2,34),(4,20),(4,68),(6,14),(6,22),(6,38),(6,70),(8,10),(8,40),(8,72),(12,14),(12,28),(12,44),(12,76),(16,20),(16,80),(18,22),(18,26),(18,50),(18,82),(24,26),(24,28),(24,56),(24,88),(32,34),(32,40),(32,96),(36,38),(36,44),(36,52),(36,100),(48,50),(48,52),(48,56),(48,112),(64,68),(64,72),(64,80),(64,96),(66,70),(66,74),(66,82),(66,98)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_126.map (·&&&dom_126)
def gM:=goal_126&&&dom_126
def NN:Nat→Nat
|5=>4
|6=>15
|7=>24
|8=>8
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0x54c1718fcc1829112bb8
|6,0=>0xc3f03b83868c37174528639b2580fb57b5947e8a3308831e4d202b81cdf01ca5708c0008916
|7,0=>0xd4fb5cfca7c7121bbb66bb86aab5f9a24c1916de79d20762786690a659295ad86501234c9e1358d8357e21dad31b26a1074e0cb1b0a0c3070f306fb5
|8,0=>0xc9098ac125a14c285fd04457d38cc63188f28a55
|9,0=>0x464f4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaaaaaaaaaaaaaaaaaaaaaaaaaa00aa0155555555540154015555555554015402aaaaaaaaaaaaaaaaaaaaaaa80000000555555555555555555005500550055000000aaaa0000aaaa0000a0a00000a0a11111111111111111111111111111111002a802a802a802a802a802a8000000000000000555555550000000055005500aaaa0000aaaa0000aaaa0000aaaa000044455554440155544444444444004402aaaaaaa800000002aaaaaaa8000000055005500550055005500550055005500a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a155540001555400014140000141400000888888888800880088888888880088055555555555555550000000000000000
|0,1=>0xaaaaaaaa0000aaaaaaaaaaaa000000015555555541414141555555554141414002a802a80280028002a802a802800285555555555555555444444444444444400aa00aa00aa00aa000000000000000111551155115511551111111111111112aaaaaaaaaaaaaaa888888888880088055555555050505055555555500000000aaaaaaaaaa0aaa0aaaaaaaaaaa00aa0155555555555555554141414141414142aaaa8282aaaa8282aaaa8282aaaa82855555555555555555555000055550000a0a0a0a0a0a0a0a0a0a00000a0a0000001540154000001540154015400000000282828282828282800000000000000055055505550555055500550055005500
|0,2=>0x2a802a80000000000000005555555500550055555555550000000000000000aaaaaaaa0000000000000001555555555541554155555555554155422a2a2a2a2a2a2a2a22222222222222200005555000055550000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0xe34730328038510328b0051c40d90171471032801471160c10055471030403851c44ca0051c40c101138d1cc0ca1473032890051c40ca4803851d00ca00f1c40ca20038d1c328900d1cc1032881440c12c01c32892001471031801440c2040
|1=>0x1c40ca01114710328094d1471032890051c40ca2001473040dc9051c40ca0051c40c10051cc1032a31471037233451cc1032803c51cc1032801440ca2c08851c40ca0051c40e101f14710328014710329d00e1473032801473040dc0051c40da
|2=>0x51c40ca00e1471032801473040ca0051c40dc0051c40ca0231471160ca0055471032807851c40ca0051c40ca0111471132803c51c40ca00e1471160ca00d1473040ca385547103280385
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x9303180cc006
|6,0=>0x1e1ce2e6b6323975cace4f7243909876e34716b899c3ee187
|7,0=>0x903465e2310a78143ea1e6eeb8723b799aeed16653b119790b4857329dd42c9a749ba31d0ae7f6
|8,0=>0xab3d3de92d4279dbcd1e5af267
|9,0=>0x15d6
|_,_=>0
def wAt:=mkWire dB 38 127 0x7fffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x280456d1008e2b1444502100450228045011004531100475a0c04e0d1444a450c085811c09e13143440114444012804a6d10085011004511144475a0c0451160445450c08e2b1444e2b14445110d407010c08e2b144450110045113c4c53110044450c08f17380441510d850114c8401
|1=>0x5111004a0114083011c3450d0c083501c04e0114445110c0450110045111c343021444e02144443614045321004401
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x80ce99c13265c8a91231e630c498000e410c11002
|7,0=>0xa253ca694b29251ca29432824fc9e93b2724dc9a9332624bc9692b25249c929232
|8,0=>0xb43646c0d71ac3546a0d31
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0xd96a180540ddf81a3502000034f4060880bbf013ee026fc04de809b7010ee020d40102001fb003f2006e4003f8007300086000ec001d000320005000080000980011000080000c000100000
|1=>0x648bd880aac68fd245ba48b54197a820f4cddf91bbf
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x1000
|6,0=>0xa11b0830d944f14018b207
|7,0=>0x6979ce78d58951d59c42128c8e59a291061d
|8,0=>0x4d5815a1f922
|9,0=>0x12
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 19 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_124 8 roots_124 ops++addP pm 1 dzo_84_2 4 roots_84 ops++addP pm 2 dom_122 7 roots_122 ops++addP pm 3 dom_62 6 roots_62 ops++addP pm 4 dom_118 7 roots_118 ops++addP pm 5 dom_94 7 roots_94 ops++addP pm 6 dom_84 4 roots_84 ops++addP pm 7 dzo_58_4 5 roots_58 ops++addP pm 8 dzo_46_16 5 roots_46 ops++addP pm 9 dzo_116_2 5 roots_116 ops++addP pm 10 dzo_110_16 6 roots_110 ops++addP pm 11 dom_110 7 roots_110 ops++addP pm 12 dzo_124_2 6 roots_124 ops++addP pm 13 dom_106 5 roots_106 ops++addP pm 14 dzo_122_4 6 roots_122 ops++addP pm 15 dom_92 5 roots_92 ops++addP pm 16 dzo_92_2 5 roots_92 ops++addP pm 17 dzo_106_4 5 roots_106 ops++addP pm 18 dom_42 4 roots_42 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_126 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_84_2_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_58_4_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_46_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_116_2_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_110_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_124_2_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_122_4_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_92 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_92_2_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_106_4_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_42 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_124 8 s (0,roots_124.map (·&&&dom_124)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_126 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_124 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_126==dom_126)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_126 gM v ys):RunD true dom_126 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_126 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 4 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 15 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 24 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 24 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 8 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_126 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 5 5=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_126 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_126 roots_126 goal_126 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_126
theorem lowS_126:Lower true dom_126 roots_126 goal_126 10:=S_126.noCircuit
theorem lowS_159:Lower true dom_159 roots_159 goal_159 9:=lower_slice_b [(0xaaaaaaaa000000000000000000000000aaaaaaaa,8,9)] (by decide +kernel) lowS_158
theorem lowS_187:Lower true dom_187 roots_187 goal_187 9:=lower_slice_b [(0xa0a0a0a0a0a0a0a00000000000000000a0a0a0a0a0a0a0a,8,9)] (by decide +kernel) lowS_186
theorem lowS_189:Lower true dom_189 roots_189 goal_189 9:=lower_slice_b [(0x222222222222222200000000000000002222222222222222,8,9)] (by decide +kernel) lowS_188
namespace S_190
def pG:List (Nat×Nat):=[(2,10),(2,34),(2,130),(4,20),(4,132),(6,14),(6,22),(6,38),(6,134),(8,10),(8,40),(8,136),(12,14),(12,28),(12,44),(12,140),(16,20),(16,144),(18,22),(18,26),(18,50),(18,146),(24,26),(24,28),(24,56),(24,152),(32,34),(32,40),(32,160),(36,38),(36,44),(36,52),(36,164),(48,50),(48,52),(48,56),(48,176),(128,130),(128,132),(128,136),(128,144),(128,160)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_190.map (·&&&dom_190)
def gM:=goal_190&&&dom_190
def NN:Nat→Nat
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|9,0=>0xf79e0
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x2aaaaaaa8000000000000000000000002aaaaaaa80000000555500005555000000000000000000005555000055550000aa00aa00aa00aa000000000000000000aa00aa00aa00aa0141414141414141400000000000000001414141414141414222222222222222200000000000000002222222222222222555555555555555500000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x2c688
|_=>0
def sO:Nat→Nat→Nat
|9,0=>6
|_,_=>0
def wAt:=mkWire dB 6 191 0x7fffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 7
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def pmP:Nat→Nat
|0=>0x3e0
|_=>0
def pmB:Nat→Nat→Nat
|9,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 1 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_188 8 roots_188 ops++addP pm 1 dom_186 8 roots_186 ops++addP pm 2 dom_182 8 roots_182 ops++addP pm 3 dom_174 8 roots_174 ops++addP pm 4 dom_158 8 roots_158 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_190 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_188 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_174 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_158 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_188 8 s (0,roots_188.map (·&&&dom_188)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_190 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_188 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_190==dom_190)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_190 gM v ys):RunD true dom_190 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_190 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_190 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z9 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 5 5=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_190 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_190 roots_190 goal_190 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_190
theorem lowS_190:Lower true dom_190 roots_190 goal_190 10:=S_190.noCircuit
namespace S_221
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(4,20),(4,68),(4,132),(5,13),(5,21),(5,69),(5,133),(8,9),(8,72),(8,136),(12,13),(12,28),(12,76),(12,140),(16,17),(16,20),(16,80),(16,144),(24,25),(24,28),(24,88),(24,152),(64,65),(64,68),(64,72),(64,80),(128,132),(128,136),(128,144),(129,133),(129,137),(129,145),(129,193),(192,193),(192,196),(192,200),(192,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_221.map (·&&&dom_221)
def gM:=goal_221&&&dom_221
def NN:Nat→Nat
|5=>3
|6=>5
|7=>4
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0x7369e63294612f8
|6,0=>0x9b2cb8aec169e9e3f6161826f
|7,0=>0xec255cd72391acb4c481
|8,0=>0x7369e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xc8c8c8c800000000c8c8c8c800000000c8c8c8c800000000c8c8c8cb3333333000000003030303000000000333333330000000030303030cccccc8800000000cccccc8800000000cccccc8800000000cccccc8b3333333000000003333333300000000000000000000000000000000cccccccc00000000cccc000000000000cccccccc00000000cccc00033333333000000003333330000000000333333330000000033333300cccccc0000000000cccccc0000000000cccccc0000000000cccccc030303030000000003030303000000000303030300000000030303030cccc000000000000cccc000000000000cccc000000000000cccc00033003300000000003300330000000000330033000000000033003300888888880000000088888888000000008888888800000000888888883030303000000000303030300000000030303030000000003030000cccccccc00000000cccccccc00000000cccccccc00000000000000033333333000000000000000000000000333333330000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x54630a54d630a954630a54c630a54631079630a875630a54c631756310b75630a79631875631543210
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x31433006
|6,0=>0x2b648e798c3117
|7,0=>0x8aef9dbbb16
|8,0=>0x4c6
|_,_=>0
def wAt:=mkWire dB 14 222 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x18d505810a41554551604295442954551
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x100
|6,0=>0x7261422211
|7,0=>0xc1b1a191
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0x8407ab3fb3eb1fb086006000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>8
|6,0=>0x64e7
|7,0=>0x925
|8,0=>4
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 12 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_213 7 roots_213 ops++addP pm 1 dom_156 5 roots_156 ops++addP pm 2 dom_149 5 roots_149 ops++addP pm 3 dom_217 6 roots_217 ops++addP pm 4 dom_29 4 roots_29 ops++addP pm 5 dom_93 7 roots_93 ops++addP pm 6 dom_220 6 roots_220 ops++addP pm 7 dom_157 6 roots_157 ops++addP pm 8 dom_201 5 roots_201 ops++addP pm 9 dom_205 6 roots_205 ops++addP pm 10 dom_197 4 roots_197 ops++addP pm 11 dom_212 5 roots_212 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_221 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_156 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_149 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_29 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_201 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_197 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_212 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_213 7 s (0,roots_213.map (·&&&dom_213)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_221 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_213 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_221==dom_221)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_221 gM v ys):RunD true dom_221 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_221 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 5 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 4 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_221 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 4 5=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_221 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_221 roots_221 goal_221 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_221
theorem lowS_221:Lower true dom_221 roots_221 goal_221 9:=S_221.noCircuit
namespace S_235
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(2,10),(2,34),(2,130),(3,11),(3,35),(3,67),(3,131),(8,9),(8,10),(8,40),(8,72),(8,136),(32,33),(32,34),(32,40),(32,96),(32,160),(64,65),(64,72),(64,96),(66,67),(66,74),(66,98),(66,194),(128,130),(128,136),(128,160),(129,131),(129,137),(129,161),(129,193),(192,193),(192,194),(192,200),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffff
def xsM:=roots_235.map (·&&&dom_235)
def gM:=goal_235&&&dom_235
def NN:Nat→Nat
|4=>12
|5=>44
|6=>169
|7=>126
|8=>34
|9=>7
|10=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x911538aa3a82b267594c7543c2509924dcc1f1fd1a1fa19dbc0a9f2059ef
|5,0=>0xaa5c97497e617d75ac00507f74fc4f4e92f4570641d8f3f3023d0e733e7b3301932ed432ebc30b292bd262ab2d2a6182921c27ff9263c4252fb2361922bca2045b1b8301a5c01672715d8115b8e1412e12e490fa9a0dadc0cf3b0c0070b7e906cd1066fe053b8038480340f0184a
|6,0=>0x408ff403d2403443ffa93e2ee3dded3c4f33b7db3b1713adff3953a38dea368a835a5434ccc33e493388f3258a319553133630a0d2fdd02fa482e4572d2202bb532b53129ae829746295f42919e28852285492794626b6726b452671224c5322ea421798209e3208261fe441fa271f9041e7b61c5731b5011b4b51abe01a9b71a4931a08319616195081924d18a3918047178261703016ec0160a515e9c1565114a85144bf1442c142b81372b133d712e1f11ac21136f112861124e10c0a1069f10404103400f9b30f8e80ed0e0e8c70e7bb0e6240d9c80d8970d2070cf840cbbc0c7fd0bedc0be370be140b7e90b5dd0ac200a88c0a78e0a40609dfc098d90965909485092d10904908d21089e707fa70614305efb05d36053e40466104561044e0044ce0444c0423d0408a03feb03bde0373402dc002559016df00dea005e5
|6,1=>0xb5a13a7c64a155f8db0380feb80fb57f51b7bfe87864f7638c75b69738f86f89e6c9ad6387162dd0617d75fe6e5fc525eeb25e2935d81e5c99e5bc6d5b7ed555105549a523164fa734dd924d6ed4bd7445e6f45bc24403642d2e42766427624212240fc240ce6
|7,0=>0xb3620b346aaa932a8f5d8ea3a8db038d7a4845c083015772a7754267217271ae36c33b635605f7db5d40c5bbeb52d6b4fee84bbbc498274629844eeb4382d4209641c653e6863e6743e6203bf183bdc93b411380a33633c35a073316331791316612d5622d1382c1e529532291aa2915a2836224c0622e8321dd120423200b21fe211e5901dae91cdfe1cd051bf3e1bc881b8cf1b4d61b3d41a8ca1a5881a0341976e1957f18d08189ac180e11690316889166f91639a1609f15c4e147fb13e021392f133e211ce2113361114410f3710c0a10af40e9d60e3f10e0f60de7b0dc0d0cd920c7bb0c4e90bf090b3d20b3630b1f00adf70ab880a8050a4a60a32f0a32d09ade098520882708384080b307c9306134055d7055be04f4604b18047280457e0443703f0902eb8024c8022a4020a901d3001a130168e00ffe
|8,0=>0x703f06885463b595de5e5656552d49509784e5a94365041c4d3f56d3f47f3bbd538e683891e3845935bb4303302fb992ccc619a561902015d601439c1342612e870e79c0ca6c0979904e7b03e38031d203047020d4
|9,0=>0xfffdaacfbe88bd051d3d43ee62ff10040d9
|10,0=>0xfffda
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f00000f0f00000f0f00000f0000000f0f00000f0f00000a0a00000a00f0f00000a0a00000f0f00000a0a00000f0f00000a0a00000f0f00000a0af0c00000f0c00000f0c00000f0c00000f0c00000f0c00000f0c00000f0cf0f00000f0f00000f0f00000f0f00000e0e00000e0000000e0e00000e00f0f00000f0f00000f0f00000f0f00000f0f0000000000000f0f00000000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0cf0f00000f0000000f0f00000f0000000a0a00000a0000000a0a00000a00f0f00000f0000000f0f00000f0000000f0f00000f0000000f0f00000f00f0f00000f0f00000f0f00000f0f00000a0a00000a0a00000a0a00000a0af0f00000f0f00000f0f00000f0f00000000000000000000000000000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000f00f0f00000f0a00000f0f00000f0a00000f0f00000f0a00000f0f00000f0af0f0000000000000f0f0000000000000f0f0000000000000f0f00000000f0f00000f0f00000f0f00000f0f00000f0000000f0000000f0000000f00f0f00000f0c00000f0f00000f0c00000e0e00000e0c00000e0e00000e0cf0f00000f0f000000000000000000000f0f00000f0f0000000000000000
|0,1=>0x5050000050500000505000005050000050500000505000005050000050030300000303000003030000030300000303000003000000030300000300f0f00000f0f00000f0f00000f0f00000f0f00000f0000000c0c00000c00f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000000000000000f0f00000f0a00000f0f00000f0a00000f0f00000f0a00000a0a00000a0af0f00000f0f00000f0f00000f0000000f0f00000f0f00000f0f00000f00f0f00000f0c00000f0f00000f0c00000f0f00000f0c00000c0c00000c0cf0f00000f0000000c0c00000c0000000f0f00000f0000000c0c00000c00a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0af0f00000f0f00000c0c00000c0c00000f0f00000f0f00000c0c00000c0cf0f00000f0c00000f0f00000f0c00000f0f00000f0c00000f0f00000f0cf0f00000f0f00000f0000000f0000000f0f00000f0f00000f0000000f00f0f00000f0a00000e0e00000e0a00000f0f00000f0a00000e0e00000e0af0f00000c0c00000f0f00000c0c00000f0f00000c0c00000f0f00000c0cf0a00000f0a00000f0a00000f0a00000f0a00000f0a00000f0a00000f0af0f00000f0f00000e0e00000e0000000f0f00000f0f00000e0e00000e00
|0,2=>0xf0f00000f0f00000f0f00000f0f00000505000005000000050500000500505000005000000050500000500000005050000050000000505000005003030000030300000303000003030000010100000100000001010000010000000000000000000000000000000000f0f00000f0c00000f0f00000f0c50500000505000000000000000000000505000005050000050500000504f0f00000f0f000000000000000000000f0f00000f0f00000f0f00000f00f0f00000f0f00000f0f00000f0f000000000000000000000f0f00000f00303000003030000030300000303000003030000030200000303000003020000000000a000000000000000a000005050000050a000005050000050ab0b00000b0a00000b0b00000b0a00000b0b00000b0a00000b0b00000b0a303000003000000030300000300000003030000030000000303000003000000000000000000b0b00000b0a000000000000000000000b0b00000b0a5050000050400000505000005040000050500000504000005050000050400f0000000e0000000f0000000e0000000f0000000e0000000f0000000ee0e00000e0000000e0e00000e0000000e0e00000e0000000e0e00000e00e0e00000e0e00000e0e00000e0e00000e0e00000e0e00000e0e00000e0e
|0,3=>0x3030000030300000303000003030000030300000303000003030000030030300000302000003030000030200000303000003020000030300000302f0f00000f0000000f0f00000f0000000f0f00000f0000000000000000000000000000000000303000003000000000000000000000003030000030050500000505000001010000010000000505000005050000010100000100f0f00000f0f00000f0f0000000000000f0f00000f0f00000f0f00000000f0f00000f0f00000f0f00000f0f00000f0f00000f0000000f0f00000f000000000000000000f0f00000f0f000000000000000000000f0f00000f0000000000f0f0000000000000f0f0000000000000f0f0000000000000f0000000000000000000000000000000000f0f00000f0f00000f0f00000f0c5050000050500000505000005000000050500000505000005050000050000000000000000000000000000000000d0d00000d0c00000d0d00000d0c003000000000000000300000f0000000003000000000000000300000f000000000000000000a0a00000a0a000000000000000000000f0f00000f0a00000000000000000000000000000000f0f00000f0a00000f0f00000f0a50500000505000005050000050500000505000005000000050500000500
|0,4=>0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f00f0f00000f0f00000f0f00000f0f00000f0f00000f0a00000f0f00000f0a0000000000000000f0f00000f0f000000000000000000000f0f00000f0af0e00000f0e00000f0e00000f0e00000f0e00000f0e00000f0e00000f0e00000000f0e0000000000000f0e0000000000000f0e0000000000000f0ef0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0000000f00f0f00000f0f00000f0f00000c0c00000f0f00000f0f00000f0f00000c0c0000000000000000f0f00000f00000000000000000000000f0f00000f00c0c00000c0c00000f0f00000f0c00000c0c00000c0c00000f0f00000f0cf0f00000e0e00000f0f00000e0e00000f0f00000e0e00000f0f00000e0e0000000000000000f0f00000f0a000000000000000000000f0f00000f0a00f0000000f0000000f0000000c0000000f0000000f0000000f0000000c00000000f0f0000000000000f0c0000000000000f0f0000000000000f0c505000005050000050500000504000005050000050500000505000005041010000010c000001010000010c000001010000010c000001010000010cf0a00000f0a00000f0a00000f0a00000f0a0000000000000f0a00000000
|0,5=>0xf0f00000f0c000000000000000000000f0f00000f0c00000000f0f0000000000000f0f0000000000000f0a0000000000000f0a10100000100000001010000010000000101000001000000010100000100000000000000000000000000000000000000000000000000f0f00000f0cf0f00000f0f00000f0f00000f0c00000f0f00000f0f00000f0f00000f0c0000000000000000f0f00000c0c000000000000000000000f0f00000c0cf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000000000f0000000f0000000f0000000f0000000f0000000f0000000f00000000f0f00000f0f000003030000030000000f0f00000f0f0000030300000300f0f00000f0e00000f0f00000f0e00000f0f00000f0e00000f0f00000f0e0000000000000000f0f00000f0e000000000000000000000f0f00000f0e0000000000f000000000000000f000000000000000a000000000000000af0f0000000f00000f0f0000000f00000f0f0000000a00000f0f0000000a0000000000000000000000000000000030300000300000003030000030000000000000000000000000000000000f0f00000f0e00000f0f00000f0ef0f00000f0f00000f0c00000f0c00000f0f00000f0f00000f0c00000f0c
|0,6=>0xf0f00000f0f00000f0f00000f0f00000f0f00000a0a00000f0f00000a0a00000000303000000000000030000000000000003030000000000000300f0f0000030300000f0f0000030000000f0f0000030300000f0f0000030030200000302000003020000030200000302000003020000030200000302a0a00000a0a00000a0a00000a0a00000f0f00000f0a00000f0f00000f0aa0f00000a0f00000a0f00000a0f00000a0f00000a0a00000a0f00000a0a000000000000000050500000500000000000000000000000505000005000000000000000000000000000000000000000000f0a0000000000000f0af0f00000f0f00000f0f00000f0f0000000000000f0a0000000000000f0a00000000000000000000000000000000f0f00000f0f00000f0f0000000000000000000000000000000000000000f0f00000f0f00000f0f00000f00f0f00000f0f00000f0f00000f0f00000f0a00000f0a00000f0a00000f0a000000000000000000000000f0c00000000000000000000000000000f0cf0f0000000000000f0f00000f0c00000f0f0000000000000f0f00000f0c00000000000000000000000000000000f0f00000f0000000f0f00000f00000000000000000000000000000000000000000000000000f0f00000f00
|0,7=>0xe0e0000000000000e0e0000000000000e0e0000000000000e0ed0d00000d0c00000d0d00000d0c00000d0d00000d0c00000d0d00000d0c00f0000000f0000000f000000000000000f0000000f0000000f000000000000000000e000000000000000e000000000000000e000000000000000e00000000f0f0000000000000f0f0000000000000f000000000000000f00a0a00000f0f00000a0a00000f0f00000a0a00000f0a00000a0a00000f0a0000000050400000000000005040000000000000504000000000000050430300000303000003030000030300000000000000000000030300000300f0c00000f0c00000f0c0000000000000f0c00000f0c00000f0c0000000000000000000000000000000000000000c0c00000c0c00000f0f00000f0ca0a00000a0a00000a0a00000a0a00000f0f00000f0e00000f0f00000f0e0000000000f000000000000000c000000000000000f000000000000000cf0f0000000f00000f0f0000000c00000f0f0000000f00000f0f0000000c00000000000000000000000000000000505000005000000050500000500f0f00000f0f00000f0f0000000000000f0000000f0000000f000000000050500000505000005050000050500000500000005000000050000000500
|0,8=>0xf0000000f0e00000f0000000f0e00000f0000000f0e00000f0000000f0e00000000f0f0000000000000f0f0000000000000a0a0000000000000a0af0f0000050400000f0f0000050400000f0f0000050400000f0f0000050400f0000000f0000000f0000000f0000000f000000000000000f00000000f0f00000f0f0000000f0000000f00000f0f00000f0f0000000f0000000000f0000000f0000000c0000000c0000000f0000000f0000000c0000000c00000000000000000000000000000000f0f00000f0f00000f0000000f0000f0000000f0000000f0000000f0000000a0000000a0000000a0000000a504000005040000050400000504000005040000050400000504000005045050000050500000505000005050000050500000000000005050000000000000000000000000000000000000000f0a00000f0a00000f0a00000f0a30300000202000003030000020200000303000002020000030300000202f0300000f0200000f0300000f0200000f0300000f0200000f0300000f020000000000000000f0f00000f0f000000000000000000000f0000000f0000f0000000c0000000f0000000c0000000f0000000c0000000f0000000c0000000000000000000000000000000000f0000000f0000000f00000000
|0,9=>0xf0000000f0000000f0000000f0000000f0000000f0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x2d00062c03050a2b0012051d17001503050c17002a2903050a1703051728000603050a270006150305241706081214181706030a23220006080e05100a0603051f1e00061503141d171a030d13061a03020a1b1a12051306080b14191715031413060812111006040b050a0f0403020a0f080e0d0c00040b0501000403020100
|1=>0x6080302191700080314191706150305101706080b020a3500081214173c0612112100060305351e00060812051300061a030d1817060812053b0006083a14171e0639030501170038050a173706030d1d1700080e05340a003603050a3500080311340a00080a17330006320302050a173103050a30001a1205181706040305
|2=>0x6080b4a0a171c0012030d1744000608483a020a170647030517250006080305130a0006080b020a172e004603110a220006450812050a1706150305173e00060a17444300060311100a0603050a4200060305174100061a03020a173d08400a070003051f3f00061a03050a1b061a030519170603173e22000608030d3b00
|3=>0x50a2300060e0305203e000608030d173c0006551503050a17060803140a173c06454603050a17060853050a1700062c1203051752001503052023000651034c050a17002a0302050a1700120d05174300063803050a171c060803140a173d060812052117000646050a174b00060311210a00064d0311050a170608110a174b
|4=>0xa17004603050a2300060305160a4200060803110a230006390305171e1c00150403052000060b03050a073000390803110a0700152c03051617003a03050a173c06085a0d1700060305172e2d0006083a4a0a171c0603051728000608590a17580006030501170006030d051757000649030d174400064903140a1744060e03
|5=>0xb0a17580006380314050a1706080e050a2300062a6003050a17065f4903050a1706080b4a140a17001a03050a173d0639080e050a0700040305210a0006080d0a174b00060846110a00060b050a175e000603050a175d0006453903050a17065b03050a4200064d0803050a1706080e110a2500060b0305172800062c5c0305
|6=>0x6906040305171e00060b03050a176700030d0526170006083a4a140a17060866140a17066503050a350006080e64020a000612050a174300060350050a420006080305173f000615080e110a0006030d20172200061a03050a173c0639030507171e00610b0305171e00083a050a173c063903050a170900623a050a17000608
|7=>0xe0a6c0006044503050a07062c034c050a17003203050a170608490a1744000665034a050a17000b64050a175e000311050a6a0006044503050a2e0604080b020a170004030a172200064e0305171e000603050a265d00064f0305171e00060803050a24170649050a17430006650302050a1700510e03050a1700044503050a
|8=>0x56050a174b00060305710a171c084812140a170608124c17000603020a17090008050a174b0006086f0b020a1700080b110a07002a3903050a17004f3803050a1706080b0a177000086f020a17001a0812051617060403050a2f0006030d05173c00060314050a173c06126d050a17000608493a140a170639050a1737000608
|9=>0x50a17002c080e050a1700752c03050a17003a050a17371c065603050a2300062c1203051617000812500d1700060873050a1700066103050a172f00081205173e0006361503050a17000859140a1706551203050a17060305173f1c0006564503050a17060403050a720006084914160a17060b050a1709003103050a071700
|10=>0x1c001a6503050a171c29030517780006380305171e0006470803140a1706152c030517250003050a42000608770a170006483a03050a35060e050a175e0006477603050a17000849500a1700063a0305160a35063a03140a174406565103050a17003a14050a1737060305172d00066b03050a070006031405173f0006653903
|11=>0x6490350050a17000603050a177c000603050a7a170006084905160a1700060e030d052000060305160a174300063a034a050a17064503050a1725062c03050a172e002c4803050a17005603050a1700066b080b050a170008121117250006150305175d00066b0803020a17002c120305201700080e020a2e00062903050a17
|12=>0x3500d050a17061a080305160a17062903050a17000608590b050a1700060311050a175e000603050a177d1c06460e0311050a00060803057e0a1700060305160a177d061a3903050a1700060812050a172e00060377050a1700060859050a170006450e03050a170639083a050a170006390302050a0717006f0311050a0700
|13=>0x63903050a17300006394803050a1700064f0302050a1700060803050a177400061a084803050a1706080e110a00060350050a174300060e036411050a00060302050a178000060314050a173700060803050a177200061a08030d0a1700061203500516170006560311050a17000604450311050a17060311050a7f00063a
|14=>0x60383050a1700064f034a050a170006560803050a17000604450803050a17060311050a2e00060b0305820a17003903050a172e000603050a17255d00060848030d0a17000604034c050a17000608034c0a1700064e0302050a1700060e03050a177900060305161781000603050a175d000603050a176e00060311050a173e
|15=>0x6080b140a17000608050a178600061a3a0305160a170612035014051700060812110a17000604031105200a0006150305161700060803500d0a1700060b0364050a17000803050a173e0006080311200a000608030d0a172e00062a03050a1700061203050a172300060803850a17000603050a18170006310e03050a1700
|16=>0x6040364050a1700064e0e03050a170006044603050a17000639610b03050a1700396103050a17003a0389050a170603050a174b0006040812050a1700060b034a02050a17003803050a1700066f0e0302050a170003050a176300060b03050a17880003050a1757250006080e05200a00061a483a03050a17061203051787
|17=>0x160a170006390803050a171c0015030520170006080b020a17008d03050a170006086f0e050a17000615034c050a1700060305171e000603050a178b0006152c1203050a1700080350160a170006120314051617060408030d0a17000603050a07177200064f3903050a170006450803050a17067303050a17000649030d0517
|18=>0x6081205172500064803050a172500061a03050a17250006120305172500061a03050a3500065603050a170006044503050a17060803050a1709000608483a050a17060403050a070006084803140a1706080314160a170615030517250006038f050a1700060311050a8e00061512030516170006081205161700065b0305
|19=>0x5160a1700061a0803050a17000612030d05170006040e03050a170006034c05200a1700060311050a0700060e0305200a00060364050a0717000603050a178600066103050a170006080b050a1700061503050a1700060803020a17000603050a1700900603050a178e000603050a17250006120314050a17000603050a1781
|20=>0x3050a1700060b03050a171c00034a02050a170006040803050a1700063903050a1700060803110a17000612030516170006151203050a1700060812050a1700061a3a03050a17000603500d050a1700060803050a172e00060385050a1700066f0e03050a170006084803050a170006034a050a170006034c050a1700060803
|21=>0x3050a17000603050a1700060305160a1700060803050a1700060e03050a1700061203050a1700060302050a1700060b
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x375032502d50285023501e50195014500f500a500550005
|5,0=>0x1396134512e61286122611d51176111610b610560ff60f960f360ed60e760e160dc50d660d060ca60c460be60b860b260ad50a760a1609b6095608f60896083607d60776072506c60666060605a6054604e60486042603c6
|6,0=>0x2f372ec72e572de72d772d072c972c272bb72b562ae72a772a072997292728b7284727d7276726f72687261725a7253724c7245723e72386231722a7224621d721762107209720271fb71f471ed71e671df71d871d171ca71c371bc71b571ae71a771a071997192718c6185717e7177717071697162715b7154714d7146713f7
|6,1=>0x4a974a2749b7494748d7487648074797473646c7466646064597452744c6445743e74386432642b7424741d7416740f7408740173fb63f473ed73e763e073d973d273cb73c473bd73b673af73a873a1739a7393738c7385737e7377737073697362735c6355734e7347734073397332732b7324731d7316730f7308730172fa7
|6,2=>0x5c475bd75b675af75a875a1759a7593758c7585757e7577757075697562755b7555654f65487541753a7533752c7525751e75177511650a750374fc74f574ee74e774e074d974d274cb74c474bd74b674b06
|7,0=>0x7ac77a4879d7795878e7787777f877877708768876087597752774a8742873a8732872b7723871b8714770d770676fe86f686ee86e686de86d686d066c886c086b886b086a886a0869886908688868176798671866a7662865a8653764b8643863c7634862c8625761e7617760f860785ff85f785f075e975e185da75d285cb7
|7,1=>0x977796f8967896079597952794b7943893c7935792e7927792079197912790a890378fb88f388ec78e668df78d788cf88c968c278ba88b288ab78a3889b8893888c7885787e7876886e8866885e885778507849784188398832782a8823781c7814880d780587fe77f777f077e887e087d977d187ca77c287bb77b38
|8,0=>0xa737a6b8a638a5c7a557a4e7a468a3f7a378a2f8a278a207a188a108a097a0279fa89f289eb79e389db89d479cd79c589be79b779b079a979a2799b7994798d7985897e7
|9,0=>0xaa46a9d7a967a8f7a887a817a7a7
|10,0=>0xaaa6
|_,_=>0
def wAt:=mkWire dB 145 236 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x30042019090a4201c170640c15061841429081600029030542058030a4140d0a2f8b819030541861081600029030a4140d06214202908200285d030549803251740c15210040c5d08200140d050042058030541429081600c15081c01419030540c29081600c15181741401081600c1503064201c050341419080700c15090a4201c03064140d0a094201c050640c15
|1=>0x800c14192500c0c151817420580a0040c1505064205f03064140d05468485d030a40c290400c205d05034102b080a4205d03054840108200285d051740c15081c0141903054185d0b1100c19173d420700800418010305428f5081c00c150a3d42070050640c1521004208003054141903064685f080040c15051740c2908200140d081601429030541401390ac2019
|2=>0x54984801030a41526031640029040a438150e0540c5d0816c0029030555803151740c150816c2801030540d5108078185d03054b02b1506c4815030a4545f120540c29035083401050a53c03081c40019030542070060041401030540c2908200285d05035300f052040c8108200285d051740c154e00c1019110340d32110a4145d051c40019030541526120040c29
|3=>0x50b40c190400c205d030556c5f08164002903055380304064205d080ac0c5d051740c154e0ace45d050b4541b080a40c15051240c295b17c205903054545f080a40c1506004e42b080640c15081742029030542c15030642019051740c151506c48150a0040c291a16c00293a0540c01050a44803030a4140d051c400190305564173a0640c01090a4201c170640c15
|4=>0x32045c292500c202b080040c1517064e42b080640c15390ace41b0b0540c190816c002903054201908070185d030540d8d0d3ac0c01050a564170b0040c194f00c0d2914064545f080a4140d0061584030806c0c155b00c1525120045019050040c19081c02001060040c15080640c5d05034205d08200285d030540d320d174142903204285d051740c154e03ce45d
|5=>0x400c205f081740c1503064205d050640c15050e4151a0e0a4e42b080640c152e0ac0c15390ac201903054980325174202b030556c0f0549448014f06ce40103025581b040a438154517c1003081740c15390ac201903055a0190b118145d030640c1503004501905004e81b050040c0105034085d050640c5d5b03c5401120553c2b1a0642001080a40c5d051740c15
|6=>0x50640c1503064145d03054018503054e4013900c201903054085f030641419030543819050640c5d050340c29080040c152e0640c151516c340d000a4685b000a40c51050040db91214814013a0a40c01050040c154f03ce40108064442b03174145d03054185d0400c205d03055ac0361174201b0305415263a0a40c011a06c0c51140640d92050745c190b11c0c19
|7=>0x3744205a000a4140d2e064201b0817c0c15040ac205d050356c1b15004202903054140d031c400190500558031517414494f0ac2071030541003081740c150407c3815031740c59000a40c15080705c1903064140d4e06c201d030540d2d034c814290600408e80300414190800c0c29052045c29030a4140d05064201c170640c155603c102908174140d0b1740c19
|8=>0x305434e80300414291a00c685f3a0540c014e03c10190e05520290800c0c15051640c59000a4140d1a17c00293a0540c014905ce82903005581b082045c29030540d2a1406414012f0acb8190817c0c150807c0c154f0ac0d2914064681b08004201903054541b080a40c5d05034541b080a40c15051c40019082040c151506c4815000a40c29030a43401050a40c15
|9=>0x3174201903004140d061740c09050640c1d17064145d031641459000a42082170a40c15177b4080f050640c59000a4140d031745c29050a40d42051640029051c400190300439e50d0ec0c5d050a4201b080ac145d0a254945f080ac0c150806c541b0a1741449030a414190817d8019081cc180103054681b080040c154806420030305420031506c2895080ac0c15
|10=>0x23a80c01034a8501905004201f061740c15080041429030541459000a40c29040a4440d05174100311034145d051740c820a1740c010d0041429000a420010305520190800c0c150b0040c19050340d9211064145d053a80c01060043829051740c5d2e0a4205f03054e817000a40c0108064200103054205f030a4140d0d3a00c01050a4e81903004140d0400c3815
|11=>0x40a4205d030541003081740c150417c440d051740803050640c190817c0c15080ac0c150800c142903054442911034145d110a4145d03054e45d0302414190d0ec14291205c0029030a4945f080ac0c15121481401030a4102b11034145d3917c2019030542003030540d290200414190816800290800c2001030540c5d051740c15035083401050a40c5d11064145d
|12=>0x305468033a0540c010d17c0c29050a4140103064140d0b17c0c190503400293a0540c01140a41401030a40c29051740c15170a4440d051744815000a40c290d004142903054141d170640c19040ac205d030545c29051740c150817c14290305584010806c0c151517c1449030a4441b051740c1508160002903054101b0e0540c5d05844382b031740d29020041419
|13=>0xa41401000a40c2908174142903054201f03054e401080640c150400c205d030540e29051680029120041429030a40c4511064145d0406438150317438290e0540c5d3906c142d0306419850806c0c1503004501b050040d320d1741429030a4205d030540c190200414193900c20190305414190e0640c5d0d3ac0c01050a40c1905078185d080ac0c15170a40c5d
|14=>0x400c205d03054201c061740c150800c0c0103054205d170640c150800c1401030542801050040c15080ac20290305415fd03208285d051740c1e170644815000a40c29000a40c29050342059030542019000640c1512054285d030a40c19050640c1503874345f050a4381903174140d030d4345d050a4e42b080640c158c0042c1703064541b051240c29030541459
|15=>0x3054441b05174381903174200303054080105064345d050a40029030542001030541429030a43815031741481170a4145d061745c2903174141d061742c5f03064201b030540c19030542029030541419030541472000640c1e06174202b030541401030a44817030a4202b030a40c150800c202b03054202b03054542b051240c291a17c2001030542081170a40c15
|16=>0x29030540c5d030a4141903064001903064080105064205d03054201903054145d030540029030a41449030a40c2903054e815030043401050a4205f
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x366060c0a981230000039000000b3010600000220004
|5,0=>0x191400000000c26178c00005950ac600000000524000013cc25a04a108c80000000043300000fd01d2800006aa0000000000000000000000032305e600001528255000000000000223000000000f20000
|6,0=>0x2426478c8d2117322864410869909420c640907f200001f663dd07a18f041da63a8c7410e531c4637906d98d921ac634906720ca4000031cc0000c43180800005e98ba317042d885998b0315a6000054a0a541446000000009f3136825d049a09031188224c431883310061f883e107840e881c4c36a0694
|6,1=>0x3d4679ccf219e133bc67690eb99d433a087388e521c6438486f90dd99b9236a86c50d6a1aa33504694cd0a19e3334865ccc9a18f4000062d0c41985330466008be217842ea65c8cb8116d32d28598cb1996032b88564caaa00002a28535000014a328e60000a21940427c44e909b2132425e64ad093a1243
|6,2=>0x12ea25c14b4495912a8a51449e492d1241a45300009105202000047888e111a9a32345c88a91139a234440687110d12173426883d1061a0a2410481110021fc43f087d4cf8a1ed4
|7,0=>0x6306c54d891b0f36186c24d831b0336006bf4d7d1af735e86bc897812ed35d46b9cd721ae225be6b70d6c9ad635a66b449671acc25926b18d619ac0357c4aecd5c1ab535646abcd561aa9354c6a8cd501a9d35346a5cd4a1a91351c6a2cd441a85350469fcd3e1a7934ec69ccd381a6d34d4699cd321a613
|7,1=>0x1e71bcb37924f18de19bc0377a6ee8ddb9bb437626eb8dd59ba8374a6e88dcf9b9d27346e5cdca1b91371c6e2cdc41b8537046dfcdbe1b7936ee4dd0db89b6e36d66da0db29b6236be6d70dac9b5636a66d40da69b4a368e6d10da1133f36786ce4d9b1b3336606cb4d951b2736486c84d8f1b1b3
|8,0=>0x2099411281e5034a059409280e5014a01940127fe4ff49fd93f927ee4fd49f993f127de4fb49f593e927ce4f949f193e127be4f749ed93d927ae4f549e993d12
|9,0=>0x20d0c191830305c60b0c151
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 15
def pmP:Nat→Nat
|0=>0xb0000154000298000510000a00001340002480004800008e000118000220000410000800000b8000140000190000300000580000880001000001a000030000050000090000100000180000280000400000600000800000800000
|1=>0xa000012740022f0004590008b0001120002200004190008200010300020500040800080c00101000200000210000410000800000ff80015000023e000454000850001090002080004000007f80009000011000020000033800059
|2=>0x2000602947c0508f80a086010bbe02157c040cf80811901020402004002002003008004abe00867c0100c0020030028380048200082200101800201c0040200068c800804000ebe001810002ef80057f000abe00157400284000506
|3=>0x40bb20815fc102af8204910409120812101024082019d0402fe0803701006a8200cd04019208010010007020000030bbe06147c0c0cf81819803023204957c0928501205a0240360480680900181155f022a3c04157c08048010007
|4=>0x12023024004041a8f08350810621c20957c4080c08055f10020420004028a8b050010084a3c10557420aac84151e0828a810513020a0604105c082038101d78202af84041c06021e0a957c1508c02a1090540320a803c102ef8205dd
|5=>0x8400bf00557e002ffc0055f8002210003fe0005bc00010800003000001203afa4055f44019e8801e11003720165e4024b0804021003afa0065f400abe8005690006fa0005a40000e800004800010d055f1a0a3c3410606808c0c0010
|6=>0xc808ad80157f002ade0041ac002b5800523000a060004bc00085101d7e2032c440650880c311009622002c42057f
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x20404040002000404000404
|5,0=>0x2c00000423000a0400003100020f2e21000004000f09000d00000000000004040008090000000200001300
|6,0=>0x1331a5274e5e01019907b96e08835c020a87824d04071813af07b33f001fae075601797801480555181307017a040d00a1950061130007c80715145130291b4a07a60a139436500b24b10d00020307200c310113b73917015f3f1bcf00a0005449002f2f01132f022f0008bb0300003034411c012d01b89e2f0cc73a10111803
|6,1=>0x6700c03220d0c35271300b6c9003d4c01261f1b2f27963805070908050c0537c51865723f9b
|7,0=>0xa83946aa91437f2b4f81888acb4459ccac1669ce6abc841d4253cac2b57501337f47b02a601a6668904374a24384bc5d32778bbf93528cc2a976cec46d732d2043195247287d0e127b3e6357013b1eba7101ad43891c03974b078d81c26c079f588fc3a77c25c48e439c6b64b2c8be4020439d7f6967851f4462afc0c1a3
|8,0=>0x9aa4806a45adcdab92c642458642a4bd4792ce80bd5b7e6f534353ce62985a43b4ab
|9,0=>0x3c47437dab6253
|10,0=>0x43
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 23 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_234 8 roots_234 ops++addP pm 1 dom_105 7 roots_105 ops++addP pm 2 dom_170 7 roots_170 ops++addP pm 3 dom_227 8 roots_227 ops++addP pm 4 dom_203 8 roots_203 ops++addP pm 5 dom_232 5 roots_232 ops++addP pm 6 dom_233 8 roots_233 ops++addP pm 7 dom_226 5 roots_226 ops++addP pm 8 dom_107 8 roots_107 ops++addP pm 9 dom_169 5 roots_169 ops++addP pm 10 dom_171 8 roots_171 ops++addP pm 11 dom_104 4 roots_104 ops++addP pm 12 dom_139 5 roots_139 ops++addP pm 13 dom_75 5 roots_75 ops++addP pm 14 dom_41 4 roots_41 ops++addP pm 15 dom_106 5 roots_106 ops++addP pm 16 dom_99 5 roots_99 ops++addP pm 17 dom_202 5 roots_202 ops++addP pm 18 dom_163 5 roots_163 ops++addP pm 19 dom_43 5 roots_43 ops++addP pm 20 dom_168 4 roots_168 ops++addP pm 21 dom_201 5 roots_201 ops++addP pm 22 dom_225 5 roots_225 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_235 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_226 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_169 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_104 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_201 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_225 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_234 8 s (0,roots_234.map (·&&&dom_234)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_235 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_234 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xcccccccccccccccccccccccccccccccc,126)],[(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccccccccccccccccccccccccccccccc,126)],[(0xffffffffffffffff0000000000000000,64),(0x2222222222222222222222222222222222222222222222222222222222222222,1)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xcccccccccccccccccccccccccccccccc,126),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_235==dom_235)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_235 gM v ys):RunD true dom_235 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_235 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 12 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 44 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 44 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 169 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 41 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 169 → Z 6 i = true := (range_split z6_0 z6_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 126 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 126 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 34 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 34 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 7 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s:Nat) (hs:s≤10):∀ i<NN s,bar dom_235 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤10) (h:RunD true dom_235 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_235 roots_235 goal_235 11:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_235
theorem lowS_235:Lower true dom_235 roots_235 goal_235 11:=S_235.noCircuit
theorem lowS_249:Lower true dom_249 roots_249 goal_249 9:=lower_slice_b [(0x303000003030000030300000303000003030000030300000303000003030000,1,17)] (by decide +kernel) lowS_233
theorem lowS_252:Lower true dom_252 roots_252 goal_252 9:=lower_slice_b [(0x1111111111111111000000000000000011111111111111110000000000000000,4,68)] (by decide +kernel) lowS_188
def isoMvS_119:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_119:Lower true dom_119 roots_119 goal_119 9:=lower_iso_b isoMvS_119 (by decide +kernel) lowS_95
def isoMvS_207:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_207:Lower true dom_207 roots_207 goal_207 9:=lower_iso_b isoMvS_207 (by decide +kernel) lowS_159
def isoMvS_215:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_215:Lower true dom_215 roots_215 goal_215 9:=lower_iso_b isoMvS_215 (by decide +kernel) lowS_95
def isoMvS_219:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_219:Lower true dom_219 roots_219 goal_219 9:=lower_iso_b isoMvS_219 (by decide +kernel) lowS_189
def isoMvS_222:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_222:Lower true dom_222 roots_222 goal_222 9:=lower_iso_b isoMvS_222 (by decide +kernel) lowS_189
def isoMvS_237:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_237:Lower true dom_237 roots_237 goal_237 9:=lower_iso_b isoMvS_237 (by decide +kernel) lowS_187
def isoMvS_238:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_238:Lower true dom_238 roots_238 goal_238 9:=lower_iso_b isoMvS_238 (by decide +kernel) lowS_187
def isoMvS_245:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_245:Lower true dom_245 roots_245 goal_245 9:=lower_iso_b isoMvS_245 (by decide +kernel) lowS_221
def isoMvS_246:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_246:Lower true dom_246 roots_246 goal_246 9:=lower_iso_b isoMvS_246 (by decide +kernel) lowS_189
def isoMvS_250:List (Nat×Nat):=[(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_250:Lower true dom_250 roots_250 goal_250 9:=lower_iso_b isoMvS_250 (by decide +kernel) lowS_187
def dzo_43_4:=0xf0f00000f0f0
def gzo_43_4:=0xf0e00000e000
def gsh_43_4:=0xf0e00000e00
theorem lowS_zo_43_4_43:Lower true dzo_43_4 roots_43 gzo_43_4 5:=lower_iso_b (d1:=dom_43) (r1:=roots_43) (T1:=gsh_43_4) [(dom_43,4)] (by decide +kernel) (lower_slice_b (T:=gsh_43_4) [] (by decide +kernel) lowS_43)
def dzo_111_16:=0xffff0000ffff0000ffff0000ffff0000
def gzo_111_16:=0xffff0000ffff0000fffe0000fefa0000
def gsh_111_16:=0xffff0000ffff0000fffe0000fefa
theorem lowS_zo_111_16_42:Lower true dzo_111_16 roots_111 gzo_111_16 7:=lower_iso_b (d1:=dom_111) (r1:=roots_111) (T1:=gsh_111_16) [(dom_111,16)] (by decide +kernel) (lower_slice_b (T:=gsh_111_16) [(0xaaaa0000aaaa0000aaaa0000aaaa,0,1),(0xf0f00000f0f00000f0f00000f0f0,0,4),(0xffff0000ffff0000000000000000,0,64)] (by decide +kernel) lowS_42)
def dzo_47_16:=0xffff0000ffff0000
def gzo_47_16:=0xfffe0000fefa0000
def gsh_47_16:=0xfffe0000fefa
theorem lowS_zo_47_16_42:Lower true dzo_47_16 roots_47 gzo_47_16 6:=lower_iso_b (d1:=dom_47) (r1:=roots_47) (T1:=gsh_47_16) [(dom_47,16)] (by decide +kernel) (lower_slice_b (T:=gsh_47_16) [(0xaaaa0000aaaa,0,1),(0xf0f00000f0f0,0,4)] (by decide +kernel) lowS_42)
def dzo_107_4:=0xf0f00000f0f00000f0f00000f0f0
def gzo_107_4:=0xf0f00000f0f00000f0e00000e000
def gsh_107_4:=0xf0f00000f0f00000f0e00000e00
theorem lowS_zo_107_4_43:Lower true dzo_107_4 roots_107 gzo_107_4 6:=lower_iso_b (d1:=dom_107) (r1:=roots_107) (T1:=gsh_107_4) [(dom_107,4)] (by decide +kernel) (lower_slice_b (T:=gsh_107_4) [(0xf0f00000f0f0000000000000000,0,64)] (by decide +kernel) lowS_43)
def dzo_117_2:=0xcc00cc00cc00cc00cc00cc00cc00cc
def gzo_117_2:=0xcc00cc00cc00c800cc00cc00c80000
def gsh_117_2:=0x330033003300320033003300320000
theorem lowS_zo_117_2_85:Lower true dzo_117_2 roots_117 gzo_117_2 6:=lower_iso_b (d1:=dom_117) (r1:=roots_117) (T1:=gsh_117_2) [(dom_117,2)] (by decide +kernel) (lower_slice_b (T:=gsh_117_2) [(0x330033000000000033003300000000,0,32)] (by decide +kernel) lowS_85)
def dzo_125_2:=0xcccccccccccccccccccccccccccccccc
def gzo_125_2:=0xccccccccccccccc8ccccccccccc8cc00
def gsh_125_2:=0x33333333333333323333333333323300
theorem lowS_zo_125_2_85:Lower true dzo_125_2 roots_125 gzo_125_2 7:=lower_iso_b (d1:=dom_125) (r1:=roots_125) (T1:=gsh_125_2) [(dom_125,2)] (by decide +kernel) (lower_slice_b (T:=gsh_125_2) [(0x33003300330033003300330033003300,0,8),(0x33333333000000003333333300000000,0,32)] (by decide +kernel) lowS_85)
def dzo_59_4:=0xf0f0f0f0f0f0f0f0
def gzo_59_4:=0xf0f0f0e0f0f0e000
def gsh_59_4:=0xf0f0f0e0f0f0e00
theorem lowS_zo_59_4_43:Lower true dzo_59_4 roots_59 gzo_59_4 6:=lower_iso_b (d1:=dom_59) (r1:=roots_59) (T1:=gsh_59_4) [(dom_59,4)] (by decide +kernel) (lower_slice_b (T:=gsh_59_4) [(0xf0f00000f0f0000,0,16)] (by decide +kernel) lowS_43)
namespace S_127
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(2,10),(2,34),(3,11),(3,19),(3,35),(3,67),(4,20),(4,68),(5,13),(5,21),(5,37),(5,69),(6,14),(6,22),(6,38),(6,70),(7,15),(7,23),(7,39),(7,71),(8,9),(8,10),(8,40),(8,72),(12,13),(12,14),(12,28),(12,44),(12,76),(16,17),(16,20),(16,80),(18,19),(18,22),(18,26),(18,50),(18,82),(24,25),(24,26),(24,28),(24,56),(24,88),(32,33),(32,34),(32,40),(32,96),(36,37),(36,38),(36,44),(36,52),(36,100),(48,49),(48,50),(48,52),(48,56),(48,112),(64,65),(64,68),(64,72),(64,80),(64,96),(66,67),(66,70),(66,74),(66,82),(66,98)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffffffffffff
def xsM:=roots_127.map (·&&&dom_127)
def gM:=goal_127&&&dom_127
def NN:Nat→Nat
|4=>1
|5=>14
|6=>82
|7=>161
|8=>145
|9=>49
|10=>7
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x4cd51
|5,0=>0xe47646a8b564e115c9b648cb54671435a563234f2ec0c25d301ccca1c3d20dd6d01ad6
|6,0=>0xefc92e5fc4e0e5ed8bbad7abad2f5fd1d56cedc9c4885c30e1c1206bff6abe5a7bde43bc178b565eb4a6bb42d3af13aacefda6832a199aa179097452963f08dd828dca28b9c38604182c4f7f84979d7378cad76b58761db74d506dc1068ec667056659b3657765d0525894f559ca4e5c14e18f4c27b4bb9d48dd648c634843c46436424563e58c3b2bc3938e390e936d3936c1335064331a1330ed3068d2f4d82d3262c30728fd52651f20d921f06b1eabe1d29619e70160fc160b414ec51161a106fd0b7a809e4203f11028e3
|7,0=>0xb2022afc7aad925ac891aae6ba9c1ea971aa6449a56ffa3591a27779e7199cac89aeca9aaff95e2994a85944e79383f9227e8fb6f8f2ff8e8ab8e7aa8a9d3872fa871308632b862fc839ed824ab80a7f803eb7c7fe7bb957adef797797933b712d96fe9e6b5d96985568bd7659b361dad60ffd60d665e87f5d97c5b83756b7856926565d555fc5556c3542e351dbc519ad50e144fc064f1a84f1634de0a4da4a4c2e24a5b848a6548a274770440d793ec003e1a43cc723bfd13bc1d3b3513a59b39afb39878375ea3608934e6734b5033b02313342faff2f1ef2e08b2e0312dfb92d1512bebd2ab572822325d99241a921f5321dee21a98214141fd1f1ca651c11318f9c18c5a169141612d1611115dd51368612199100500e90f0e6900d05d0a32d0936108af5055f0055760323002de80219901d0701c910162b0115100655
|7,1=>0xfd7fdf70aef6858f5bd2f3d6df0f6dea0e2e3147e21eee103ce0e95df5f4ddc65ddb19da9a2d95edd9598d6941d1cb1d0dfbcb0f7c662ec5243c384ac1ac6bf060be9e5bdc73b89ffb8684b7956b4a6bb2507
|8,0=>0xc49aebeb72b71bab4b6cb2507b1b9bb1b2aaf855ad598acb06abfe3aafd2aa618aa008a9331a4f499ed069ddb294dbc94279906eb8dd328d8bb8c35b8b62d89213891e488d6a83b4283606815fc8129e80b067ff647f90a7eb427dcd77dc1e7a19379381781ec7195c700846cc146c17b6afb36a9576a3166a154695ff6763f66d5864c956433c6410f63c4e6384662d3a62952608645a631586c8575e4537f650cf24b0f14a4d444fb043c61437b03ec2d3cbd73afdd39f8339f30396d4395ed394e238e1938c40383e637d4f3740a3623135f7b34e9c3421c31bd130f1930ea12ec2d2eac02e91a2e02c29f9627091259ad24cd62406a23ece2274f214141f6a41d5be1ca651a671197fc1949818ff918dfc16c9e16a7215dd514fea14fb61281912809125630ad6a0a55d0928f084d8076cc0611804b790353d00e2800aa2
|8,1=>0xfaf9af9f96f51fcee914e3f24de32dddfc2dd038dc480dbfa6d83f8d4e28cc039c98a9c7a44c6732c571c
|9,0=>0xeaa72de234da8e5d6882cec71c2985ba0a2b273db0480affa6afc7dad27aa8a85a7e31a36fa9850090c1a8dc818418680b067fcba776fa6a3f767fee5dfcc5529e47896466983e1543d5ff3d36c3b2ce3a67938013348ea323e429294241f02258c204a61a4a0156f11265d0d6d40ca260c807096970398a02d2c
|10,0=>0xe0a268d3bf83c7d71543581865254f05c14
|11,0=>0x2654f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x11111111115511551111111111551100ffffffffffffffff0000000000000000ffffffffffffffffffffffff00000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ffffffffffffaaaaaaaaaaaaaaaaaaaa33333333333333333333333333003300ffffffffffffffffffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00fffff3f3fffff3f0f0f0f0f0f0f0f0f0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa33333333330033003333333333003300ffffffff00000000ffffffff00000000ffff0000ffff0000ffff0000ffff0000ffffffffffffffffff00ff00ff00ff00ffffffffffaaffaaeeeeeeeeeeaaeeaa0f0f0f0f0f0f0f0f0f0f0f000f0f0f00
|0,1=>0xf0f0f0f0f0f0f0f0f0f03030f0f0300ffffffffffffff000000000000000000ffffffffffffff00ffffffffffffff00ffffffffffffff00ffffffff00000000fffffffffffffff0f0f0f0f0f0f0f0f00f0f000f0f0f000f0f0f000f0f0f00000f0f0f0f0f0f0f0f0f0f0f0f0f0f0000ffffffffff00ff00cccccccccc00cc00ffffffffff00ff00ffffffffff00ff00ffffffffffffffffccccccccccccccccccccccccccccccccccccccccccccccccffffffffffffffffffffffffffff0000ffffffffffffffff3333333333003300ffffffffffffffaaaaaaaaaaaaaaaaaaffffffffffffff00ff00ff00ff00ff00ffffbbbbffffbbaaaaaaaaaaaaaaaaaa
|0,2=>0xffffff00ffffff000000000000000000000000000000ffff00ff00ff0000000000ff00ff00ff00ff00ff00ff00ff00000000000000000000333333333300330000000000ffffffff00000000ffffff00ffffffffffffffffffffff00ffffff00555555555555555555551111555511000f0f0f0f0f0f0f0f0f0f00000f0f000000ff00ff00ff00ff00ff00ff00000000ffffffffffffffffffffffffffffff00ffffffffffffffffffffffffff00ff00ffffff33ffffff00ff00ff00ff00ff00000000000000ffffffffffffff00ff00ffff3333ffff33000000000000000000555555555555555555555555555555000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00
|0,3=>0xffffffff000000ffff00ff00000000003333ffff3300ffff33333333330033000000000000000000ffff3333ffff33000000000000000000333333333333330000000000ff00ffff00000000ff00ff003333333333ff33ff3333333333ff3300ffffffffffff00000000000000000000ffffffffffff0000ffffffffffff00000000000000000000ffffffffffffff00ffff0000ffffffffffff0000ffffff0033333333330033ff33333333330033000f0f00000f0f0f0f0f0f00000f0f0f00ffffffff000000ffffffffffff00ff0000000000ffffffff00000000ff00ff00ffffffffffffff00cccccccccccccc000f0f00000f0f000f0f0f00000f0f0000
|0,4=>0xffffffffff00ffffffffffffff00ff000000000000000000ffffffffff00ff00ffff0000ffff00ffffff0000ffff00000000000000ff00ff0000000000000000ffffffffffffffffffff3333ffff33000000ffff0000ffff0000000000000000ffffffff0000ffffffffffff00000000ffff00ffffff00ffffff00ffffff0000000000000000000000ff00ff00ff000000000000000000ffff00ff00ff00ff000000ffff0000ff000000ffff0000ff00f0f0fffff0f0fff0f0f0fffff0f0fff00f0f0c0c0f0f0c0f0f0f00000f0f000000ff00ff00ff00ff003300330000000000000000ffffffff0000000033003300ffffff00ffffff00ffffff00ffffff00
|0,5=>0xffff0000ff000000ffffffffff00ff00333300003300000033333333330033000000ffff0000ffff0000333300003300ffffffffffff0000ff00ff00ff0000000000000000ff00ffff00ff00ff00ff0033333333330033333333333333003300ffffffffff00ff000000000000000000ffffffffffaaffaaaaaaaaaaaaaaaaaa0000ffff0000ffff0000ffff0000ff000000ffff0000ffff0000ffff00000000ccccccccccffccffccccccccccffccccfffffffffffff0f0f0f0f0f0f0f0f0f000ff00ff00ff000000ff00ff00ff00000000000000ff00ff0000000000ff0000ffffffff00ff00ffffffffff00ff000000000000000000ff0000000000000000
|0,6=>0x3333333333ff33ff333333333300330000000000000000000000ffff0000ff00f0f0f0f0f0f0f0f0f0f0fffff0f0fff0000000ff000000ffff00ff00ff00ff00ffffffffffffff00ffff0000ffff0000ccccccccccffccff0000000000000000ffffccccffffccffffff0000ffff0000000000000000000000000000ffffff00ffffffffffffffff00000000ffffff000000cccc0000ccff0000000000000000ffffff00ffffff00ffffff0000000000ccccccccccffccffcccc0000ccff0000ff00ff00ff00ffffff00ff00ff00ff00ff00ffffff00ffffff00ffffff00ff00ffff3333ffff3300ffff3333ffff330033333333333333333333333333333300
|0,7=>0xff0000ffff0000ffff0000ffffffffff00ff00ffff0000ff000000fffffffffff0fff0f0f0f0f0f0f0f0f0ffffffff00ff00ffffffffff0000000000000000ffffffff00000000ffff0000ff00ff00ffffffffff00ff00ffffff00ffffffffffffffff00ff00ff00ff0000000000000000ffff0000000000000000ffffffccffffffcccccccccccccccccc000000ff000000ff000000ff00000000ccccccccffffffffccccccccccccccccffff0000ffff0000ffffffffffffff00ff00ffffff00ffffff00ff00ff00ff0000000000ffffffff0000000000000000ff00ff00ffffffffff00ff00ff00ff00fffffff0fffffff0f0f0f0f0f0f0f0f0
|0,8=>0xff00ff00ff00ff0000000000000000ffffffffffffffffffffccccffffcccc0f0f0f0f0f0f0f0f0f0f0c0c0f0f0c0cffff0000ffffffffffff0000ffff00000f0f00000f0f0f0f0f0f00000f0f0000000000ff00000000ffffffff00000000ffff0000ffff00ff0000000000000000ccccffffccccffffcccccccccccccccc33333333333333003333333333333300ffffffffffccffccccccccccccccccccffffffffffffffffffffffffcccccccc0000ffff0000ffff0000ffff0000cccc00ff00ff00ff00ff00ff000000ff0000ccccccccccffccffccccccccccccccccffffffffffffffff0000ffff0000ff00ccccccccccccffffcccccccccccccccc
|0,9=>0xccffccffccffccffcccccccccccccccc00000000ffffff0000000000ffffff00ffff00ffffff00ffffff0000ffff0000000000ff000000ff00000000000000000000000000000000ffffff00ffffff00
|_,_=>0
def sP:Nat→Nat
|0=>0x80c15060403080c0613220d0403080c16210403080605200e04030806131f0e170d03080c15120403080c10130409080c12051c03020c060a0409081b060504030216061a0d0308180619140d03080c010403080c12130d03080c12050d03110c06050409080c10050403080c0f0e0d03080c0b0a0409080706050403020100
|1=>0x3080c16062b0403080c10050e170d030c16062d170d03020c0613170409081b1506040308062c280e170d03021506190d03080c16062b250403081606000403020c06051e0403080c29130e040302110c1606040308160628271d0d03020c06050403080706050e040308060a190e250403080c16210403240c06050e230d03
|2=>0x20c15060d3603080c16060403080c06350e040308160600320d030208150634030c060a27320e330403020c1506030c1606273204030215061a0e0403020c15120409080c0605220403080c21050e0403020c31060403080605300e170409080c1512170d03081606280403020c060a2f170403021606000d03080c15062e25
|3=>0x27320403020c01040302080c063c04030806051f0e250403080c1512170d0302150628140d03080c18060d04030816061a0403080c06131e0403080c12050e040308060a200e0403110c06050e0d03080c16063b040308060a280e0403080c063a0e0403081b06050e0403080613280e250d03080c150b370403080c06131c03
|4=>0x409080c1512030c060527320e250403081606200409081b15060d0302441506250403081606280403080605430e171c03020c150617030c0642410e251c03020c15060409080c06051e0403080c210a0e0403023f0c16060d1c03020c15060403080c063e0e0403080c29050e04030208160620043d03080c061325030c1606
|5=>0x80c15210e174903080c06050e040903080c062c0e1d0409080c06050e042a03080c060a0e140403080c1606272504030c060a270e2504030c160627044003020c060a0e044803020c15060e040308150634320e040302080c160647040308150628320e0403080605280e04030208160600040302460c150604030816061a27
|6=>0x60e14170d03080c1606175103080c15060e4f0403080c15060e170d2a03020c15060403080c06130e170403080c15210e250403080c15210e0d03080c060a320e0d03080c160632170403081506300e170d0903080c16061c03080c15060e0d03020c15062732170403080c063e0e044b03080c06130e0d03080c150b0d0403
|7=>0xc1506170d030c15062d0e250403020c1606270409080c15061e0d0403020c15062d1703020c1606320d03080c15580d03080c15062b0e0403080c060a570e04360302080c1606170d03080c160656040903080605280e250403081506000e0403080c55060e0409085415060403024415060e0d03080c160653040302110c15
|8=>0x1606170403110c15060e1c0403020c15060409080c150b040903080c06130e170403081b15060e0d03085c0c15061d0d03080c160604030815061a0e170d03081506280e1703080c15062b0e170403021506000e0d040302081506280403025b0c1506490403080c065a0e2503080c15062b0e0d4003020c15063237170d0308
|9=>0xe2225042a03080c1606170403080605280e040302080c160657040308150600320e0403080c063e050e170403080c15120e170d03080c15061e0d03080c18060403080c06600e0403080c065a0e0403080c010e040903080c060a0e0403080c065e0e0403080c06135d0e4f0403080c065a0e030c150627320e38250d03080c
|10=>0x20c06050e0d0403080c150667170d03020c1506560403081506200e0403080c06050e660d03080c15063b0e0d046503080c16060403080c6406050e0d0302085c0c15061d0403020c06050e170403630c15060e260403080c060a0e0403080c060a560e170d0903020c15061c03020c15060d040362080c16060403080c0605
|11=>0x302080c1606046903080c06050e0d040302081506000d044803020c1506250403020c15062f1d0d03020c1506170409080c15061e2504030c0605270e170403081606280e0d04030815061a0e4e0403081506280e044003020c160632040302080c06600e170403020c06130e043603080c160632250403080c160657170d03
|12=>0x570e370403080c06050e0403080c063e0e046b080c15060e040302081506200e250403080c06600e0403080c0605520e17030c150627320e4f0403080c06050e25040903080c160625030c150627320e04030208160628046103080c06130e044b03080c06050e37040302080c15061703080c0613410e0403020c15061e2604
|13=>0x403081506200e250403081506200e0403086d15060e040903080c1606320403080c06050e1e250403081506280e1d0403080c06130e37250403080c1506170d03020c06050403026c0c150626250403080c1606250403080c1606560403023f0c15060e0403080c15210e1703020c0605320e0403081506300e0403080c0605
|14=>0x6470e040302081506000e17040903081506280e044003020c1606043d03080c06050e170d03020c16060403080c31060e260403080c06050e044d03080c06050e1d170d03020c1506250403080c15061e0403080c06055d0e0d03020c1506450d0403080c16062d0403080c06050e500403080c066f0e046109080c06050e17
|15=>0x80c15060e0403084415060e0403081506190e0d04090302080c15061c03080c15060e040362080c15060e040311080c15060e0403080c15063b0e040371080c16060403020c1506590403087015060e250403080c06050e1704030c1506270e140403080c1506270e4f490403080c15060e2504030c1506270e040302080c15
|16=>0x2080c150656046503080c15060e0403080c1506760e0d03080c1506530e0403080c060a0e14170d03080c15060e040302080c75060403080c1506520e140d040302080c15064f0403080c15060e0403080c16064c0d0403080c1606270403080c06130e170403020c06050e0d03080c1506320e740403080c15060e170d0903
|17=>0x6680e046b03080c15060e0403080c1506790e046103080c06050e042a0302080c1606250403020c1506270e040363080c15060e0403020c1506450e0403080c15066e0e1d250403080c15060e1703020c1506320e0403081606280e04360302080c15060e170d03080c1506560e0403080c1506570e0403080c77060e0d0403
|18=>0x60e170403080c06050e4a040302080c060a0e0403087d15060e38250d03080c15060e170403020c16060e177c03080c15060e1d170403020c15060e1d0d03080c15060e0d044003080c160604037a080c15060e170d03020c1506250403080c16060e0403080c06050e6a0403020c15062f17040903080c06050e0403080c15
|19=>0xd0302080c15060403080c1606320e044d03080c15060e17040903080c16060e4e040903080c15060e0403080c80060e047f080c15060e0d040362080c15060e1d0403080c06050e04037e080c15060e25042a03080c15060e251704030c1506270e0409080c1506530e0403080c150b0e040302080c1506570e5f0403080c15
|20=>0x80c15060e170403080c1506520e04090302080c1606250403080c15060e250403080c060a0e1d0409080c15060e4f170403080c15060e0d046503080c15060e250403080c1606170403080c06130e0403080c82060e0403080c1606530e0403080c1506810e0d0403020c15062725040302080c16060e260403080c15060e38
|21=>0x60e040302081506280e0d040302080c16060403080c1606840e26040302080c15060e1d0403080c16060e0403080c15062d0e0409080c150639170403020c1606044003020c1506320e170403080c1506570e37170403080c15060e043603080c1506320e250403080c1506570e3804080c1506830e0403080c15580e174903
|22=>0xe26250403080c15060e170403080c88060e250403080c1506560e0403080c0613050e0d0403080c160656170403080c15060e50046b080c15060e25040302080c060a0e0403080c06870e25040302080c16060403080c16063225040903080c15060e0403080c06050e4c0403080c86060e170403080c15060e1e0403080c18
|23=>0xe0403080c16068f0403080c06050e4a170d03020c15060e044803080c15060e04030816068d0e0d0403080c15062d0e0403080c062c0e04030815068b0e1d170409080c15060e040903080c1506320e040903080c06050e8a03080c15060e170403081506280e0403080c15060e8926170403080c15060e17044d03080c1506
|24=>0x9203080c15060e1d170403080c15060e0403080c15060e91380409080c15060e0403080c1506450e048e03080c16060e0403080c15060e4c0d0403080c1506270e049003080c15060e040371080c15060e040302080c16060e170403080c06050e040903080c16060e490403080c15060e042a03080c15060e044003020c1506
|25=>0x3020c15060e0403080c15067b0e04090302080c15060e250403080c15060e170403080c15060e4c0403081506280e0403080c1506560e0403080c88060e850403080c16060e040302080c1606380403080c16060e0d044003080c15060e170403080c16060e4e0403080c15060e0403080c1506930e042a0302080c15060e04
|26=>0x150625170403080c15060e1d0403080c15060e380440080c15060e170403080c15060e4a0403080c15060e590d0403080c1506560e25040302080c15060e0403080c1506320e0403080c06050e17040903080c15060e0403080c94060e0403080c15060e390d040302080c15060e040903081506280e0d0403080c15068f1704
|27=>0x403080c15060e0403080c16060e380403080c15060e170403080c15060e0403080c15060e4a040302080c15060e040903080c15060e0403080c15060e8f0d040302080c
|_=>0
def sO:Nat→Nat→Nat
|4,0=>5
|5,0=>0x53604d60476041603b6035602f60296023601d60176011600b60056
|6,0=>0x20c720571fe71f951f271eb71e471dd71d671cf71c871c171ba71b371ac71a5719e7197719071897182717c6175716e7167716071597152714c6145713f61387131712b6124711d7116710f7108710170fa70f370ec70e570de70d770d070c970c270bb70b470ad70a6709f70987091708a7083707c7075706e7067706070597
|6,1=>0x2877280727a6273726c7266626062597252724b7244723d7236722f72287221721a72137
|7,0=>0x46f7469646184598452744b7444743c8434842c8424841d7415840d840583fd83f583ed83e673de83d773d163c983c183b983b183a983a1839a7394638d7386737e8376836e8366835e8357734f8347833f8338733083288321731983118309830362fb82f382eb82e382db82d382cb82c472bc82b482ac82a4829c8295728e7
|7,1=>0x66086588650864886408638863086297621861986118609860275fa85f285ea85e285da85d375cb85c385bb85b385ab85a3859b8593858b8583857b8573856b8564755c8554854c8544853c8534852c8524851c8514850e650684fe84f684ee84e684de84d684ce84c684c064b974b274ac64a4849d7495848d8486747e84768
|7,2=>0x75d8756774f7747873f8737872f87278720771887108709770186f986f186ea76e286da86d286ca86c286bb76b476ac86a4869c8695768d8686767e8676866f76687
|8,0=>0x95d9955894d8944993c8934892c8925791d8915890e790598fd88f588ed88e588dd88d498cc88c488bc88b398ab88a4789b9892988a8883787a9872886a8862885b7852984b7843883a9832882b7823881c7814880c880487fb97f477ed77e497dd77d587cd87c587be77b777b077a887a08797978e9786877d9775876c97657
|8,1=>0xb659b5d8b558b4c9b457b3c9b357b2d8b267b1d9b158b0e7b059afe7af68aee8ae68add9ad58acd8ac67abf7ab69aad9aa49a9b9a929a8a8a837a7b8a729a6a8a628a5a8a528a499a409a397a318a2a7a228a1a8a128a099a0189f989f189e989e099d799d079c979c099b889b089a7999e9996898f7986997e8975996d89667
|8,2=>0xbf08be88be08bd97bd09bc97bc27bb99bb09ba88ba17b998b918b889b7f9b769b6e8
|9,0=>0xd7e8d759d6d8d658d5c9d548d4b9d429d3a8d337d2a9d237d1b8d129d0a8d028cfa8cf28ce99ce18cd89cd17cc98cc27cba8cb37cab8ca29c9a8c928c8a8c819c798c709c688c608c588c508c488c3f9c378c2f8c278c1f8c178c0f8c078bff8bf87
|10,0=>0xdb67dae8da68d9e8d968d8e8d868
|11,0=>0xdbd7
|_,_=>0
def wAt:=mkWire dB 149 128 0xffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x80d41039380e00c11041e47438170341021080e43423150e49413080d41039061e47438170341021080e47458170341021150e42039030e418791d0e05c0d040842011090cc1039080e414391715c1021030e430791d0e05c0d040842039140cc0c35040e410092a0cc0c09080e4981b250341009080e41039061e47438170342011180645c58030d42011150e41039
|1=>0x30e4a833030245439080e418791d0e05c0d030e41021260cc940d0402420390c1e47438170340c39040843115040e420391703c1021170e41021090cc0c39041e420391d0e05c0d04084104e050e45c571c02410bd080e5003803084100a2508c1009080e46019171601021150e42039061e47438170345c39090cc0c39040e42039171600c35080445439040e418e5
|2=>0x80d410394d0cc0d31170e81021040e45439030e420111d0d05c0d080441039040281039054a40c3a1715c10210313414391715c1021063941039380e00c112606c940d080d41129030e85c571716c5439030e41021170345c57030e41021030249457040242039080d80c35150e410392515c3421080d81039150e43421080d810392515c1009080e45c57040842433
|3=>0x30d82011150e41039090cc5c57030e4102104024a833030242039155245c26030e410210c3940c39380e00c110c45420391703c1021040e454393808c0c111d0205c0d030d42011150e41039045245c26030e4201117504743a1703410210804410390302420392c0e53857170ec10212606c940d170e410212606c940d0402420392515c9413080d41039150e49413
|4=>0x40e52033032742036040e41039080442433030e49813250345c390804410212a0cc0c09080e42433030e41039080e40967080e45c38040849813250342035040e4200d04028743b1703420111408c0c35040e454392508c1009080e47438170340c39040845023030d41039040281021150e42039040e41965170e020112604c940d080d41039033245439040282039
|5=>0x80445439040e49857170940c39040853c57174a41021030e86019171605439040849457170e40c39040857c57174ac1021030e814391715c1021174a41021030e834232504c2035040e42035030445439040e420791d0e05c0d0408410bd080e50038030840c3906394e0380304414391715c0c390408430791d0e05c0d04084e008080e40c11040e45c0d080445439
|6=>0x40e42039040840c36040e49833170940c3904084118a0856410390d400200d150e41039380202039040e421411d0e85c0d040849457250341009080e40c39040841039080e410bd080e50038030845439085640c36040e58438030545c57040841009030245439080e45c57040842433030e454392503c1009080e418791d0e05c0d0408410391d0e05c0d080445c58
|7=>0x150e42039036a4143a1715c1021040e4a833030242039080d81009080e50038030842039170342011040e40c391d0e05c0d0408494231715c5c39040845439040842433030e52033032742036170ec1021090cc0c39150e4200d0402820392615c940d040242039050e45c5704084543903324100a080e4940f040245439080e45c57040841039080e5a0390d408200d
|8=>0x170940c39040845c570402820394d0cc0d31170e810211d0ec1021054a40c3a1715c10211d0905c0d030e41021260cc940d04024940d0402420392504c9423170e41021040845c39150e40c3904084100a2508c1009080e45439080e42433030e414391715c10210313414391715c1021260ec940d0402420390413814391715c20111d0e05c0d040842039250341009
|9=>0x1715c1021040e420391703c1021081480c35150e41039054c45c57170e81021030545c57030e41021260cc940d170e41021260cc940d0402420390c6e45c27030e41021040282039030e454391d0e05c0d1715c1021170e41021090cc0c39050e41021170e4743b170341021040e420391715c1021022fc2039400e00c21250341009150e420390d0840c36040e4981b
|10=>0x30e821c9150e4103a080e45c380408430bd400e00c211715c5c39040849423170e410210d0342036040e52421044a40c3a0d0842036040e408e20403420392a0cc0c09080e42433030e41021030845439080e5843b1715c1021150e41021040e420391d1605c0d150e41021170945c57030e41021034c45c57170e81021040e420391703410211d0e05c0d170e41439
|11=>0x80d81039040e4e023030449457040242039080440c35040e4203915724103a170980c39040842039030d41039174a41021030e85c3a150e41021150e42036040e414391715c1021080e45c57040849413080d410394e0345c3b040841039030e420110c4545c0f040845033030d41039030e41039080e410bd400e00c21085640c36040e420e5380e00c117304c2129
|12=>0x50e85c57040842039400e00c211715c0c39040843502080341039035945c38040854c393808c0c11030545c57040840c09150e420392508c1009080e421e1380e80c11080e45c0f040845c27030e41021170345c39040842011040282039150e42433030e40cc9040282039040840c36040e4940f040242039152f50038030842039030d810390d400200d040e40c9e
|13=>0x40842159030d81039170345c57040845c24030e41021030241009080e49423170e41021030e4e0230304418e5380e00c112503c1009080e45d2b040840c3a030e85c570408494570402420390c5945c38040840c11080d41039080e45439040841131170e82011080e45c0d040845c0d080441039080345439040e421ed0904c0c39040e41021080e45c39150e41021
|14=>0x30e41021080e40c39150e45d31170e810212515c1009080e45c0d030e41021174a41021030e83500080341039040245439080e414391715c1021154c45c3a0408454393808c0c11450e45c0f040842039080d81039150e41009080e45c25030e41021080e40c11040e4100a150e42039034c45c3a040845439030e41021170ec0c390408455e1380e80c110359c5c38
|15=>0x170e40c39040845c57170e81021155945c38040847438170341021171605439040842039090cc0c39040e45439080e6140f041645439250341009080e45c0d150e41021081480c35040e40c39380e00c11040845439080e4200d0402820392503c5c3904084743b17034102103324100a080e4940f040242039030442423030e41965170e01021044a42011030e85c26
|16=>0x40e53857170ec10218c0cc0dc9040e85c0d030e41021030e4100a080e45c57030e41021042fd0038030841021090cc0c39450e85c0f04084940d170e41021034c45c3a04084940d040242039040845529030e83421030d81039050e45c57040845439030d810391d0e85c0d040840d65170e010212515c1009080e47457380840c11040245439080e4100a150e42039
|17=>0x41645439150e42039150e40c11080341039150e41021170ec10214004c0c21030242039038f4203a170341021400e80c21030e40c111703c1021031645439170e81021080d81039400ec0c2108724103a150e420391715c1021030e45439044a40c3a030242039030842039150e4203a030e85c57040841021040e42039032742036040e63833031645439081480c35
|18=>0x5439030441021030e82039030e4203a040e42039170e41021380840c11030840c11040840c3a170e01021030d810390402420390402820391715c1021030e41021158f4203a380e00c11040e42039090cc0c39080e810390408420390904c0c39030e42039040242039170e81021090cc0c39030d81039154a40c3a
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0xc00000000000000000000000000
|6,0=>0x29a04e5000000002520464082a000000000000000000000000000000000000003c500000dd40000000000000000000000064a000016a800000000a1400002350424000000000000000000000001c502ea000009a000001e800000000000000000000000000016800000000000000000000000065
|6,1=>0xeca000039206d50d0a191000005f50b8615d40000000000000000000000
|7,0=>0x2a6853d0a5a147428684fd09da137426684bd095a1274000048d090911e3236645d089a110321884210822000020083f107c20f441e083b107420e441c4437906d20d641a4833906520c6418482f905d20b6416482c085620a841488284c4f189a412c8249047208a410c820cc0000000000000003fa07b4
|7,1=>0x4526898c0002224442287510ca215442468391052206440487f90fd21f643ea27c50f6a1e943ca87850ef19da43ac874cce7a1cb438e870d0dfa1bb436e80000da19b0400006b4c0001a9434a80000d0a19d433286550c8a18d431280000000185430285f50bca17542e285b50b4a16632c6657d0ada1574
|7,2=>0x29835288a41146228845088a04d3f1a7a44ec8000139226e44d48999131225e44b4895912a1250449889211222241300008f511d1a36400008d0918222c4
|8,0=>0x6b06d54da91b4f36986d24da31b4336806cf4d9d1b3736686cc4d971b2b36506c94d911b1f36386c64d8b1b1336206c34d851b0736086c04d7f1afb35f06bd4d791aef35d86ba4d731ae335c06b74d6d1ad735a86b44d671acb35906b14d611abf35786ae4d5b1ab335606ab4d551aa735486a84d4f1a9b3
|8,1=>0x8307054e091c0f38187024e031c0338006ff4dfd1bf737e86fc4df71beb37d06f94df11bdf37b86f64deb1bd337a06f34de51bc737886f04ddf1bbb37706ed4dd91baf37586ea4dd31ba337406e74dcd1b9737286e44dc71b8b37106e14dc11b7f36f86de4dbb1b7336e06db4db51b6736c86d84daf1b5b3
|8,2=>0x44b38907114e211c3f387870e4e1b1c33386070b4e151c2738487084e0f1c1b3
|9,0=>0x4ae295852a8a5414a629485288a50149e29385268a4c149629285248a48148e29185228a44148629085208a40147e28f851e8a3c147628e851c8a38146e28d851a8a34146628c85188a30145e28b85168a2c145628a85148a28144e2
|10,0=>0x12d865a8cb4196632c86588cb01
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 15
def pmP:Nat→Nat
|0=>0x7000000000690000000061000000005e00000000500000000048000000004400000000410000000040000000003f000000003900000000380000000030000000002e000000002c0000000028000000002100000000200000000018000000001600000000110000000010000000000e000000000c00000000080000000007000000000600000000040000000003000000000200000000010000000000
|1=>0x40039000004002f000004001d0000040018000004001000000400050000020084000002001b0000020010000001081800000100f90000010059000001005800000100180000010010000001000f000001000c000001000b0000010008000000e02600000010000000000e0a0000000803000000060a000000013d0000000105000000010000000000e90000000080000000007f00000000790000000078
|2=>0x800340000080030000008002e00000800240000080020000008001e00000800190000080014000008000f000008000e000008000c00000800090000080006000008000100000800000000070000000005007f000005003f0000046137000004083f000004083b000004017f000004013f0000040137000004011000000400bf00000400bb000004007f000004007c000004007b0000040070000004003f
|3=>0x14011f000014011d00000e083f00000d007f00000d007b00000d001c00000c083f00000c017b00000c013f00000c00bf00000c007f00000c003f00000c003400000c001c00000c001400000c000000000a083f00000a003f00000a003500000a0016000009087f000009083f000009003f00000900390000090001000008083f0000080834000008081000000800b40000080094000008005c000008003f
|4=>0x100003f00010000370001000002000088000a00004c01ff00004c01bf00004c017f00004c013f00004c00bf00004c003400004c0024000045009800004400f800004400bf000044007f000044003f000044002f00004000bb000040009800004000790000400069000040003f0000400017000040000900002c01bf00002400010000200043000020004200002000030000200001000020000000001c003f
|5=>0x208003700020800360002080032000204087f000204083f000204007f000204003f0002020034000201001b000200081e000200001600020000100002000000000144017f00010e093f00010e011700010c093f000108003f000105017f000105007f000104013f000104007f000104007b0001040077000104003f0001040037000104002800010400090001000917000100017f000100007f0001000058
|6=>0xa080036000a00003f000a00003600092c093f000922007700090f013f00080f003c00080e003f00080e000f00080c083f00080c003f00080b007f00080b006c00080b003c000808083f000808003f0008080006000802085e0008000008000800000000040c0004000400013f00020d003f00020c093f00020c083f00020c013f00020c011600020c003f00020c001600020a003600020a00160002080102
|7=>0xc00014013f400014003f200014003d10000c013f10000401bf0c0124013f060124013f040105017f04000e093f021104013f021100013f020104003f020100003f01021c083f01001e003f010014003f010014003d010011003f008000000300400d203f004009209f004004063f0040000e3f004000069f002004003f002000083f001140013f00104c003f001040009300100c013f000a0c013f000a0c003f
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x500000000000000
|6,0=>0x2a1707290107000d1b1000002b00000000001a2c00000a1305000000000023000000000d0001000000001700010028000026000d25000000000000140d00130007000000000000000700000000000007
|7,0=>0xa2d003325091a7e04030ba03e2e0213b310d70d18470e079531a50508410f735400395e005c170b8300bd8a629e120d5800003c2fca54864d053a04078861118fe9050d6db0593b0b5b131500527050378b4bb421eb0f00b5cb050782e668a30ab50b2ddd010d071de30dc03d0a0d06e80e0a05840205181e1900005100017f
|7,1=>0x47827ed02d23104bfb400a49d0d07540c8507816742893007cc9c1f3f00813a3f
|8,0=>0xcdf487324020aeb2e556a8494f49fd9af538da6f4cad9672d9535566ec4636c67ca1799465a2aa49b16a4593667de474c556494063dbba5d3479ea5f4443aae761997bd3d8afde449bf4901cd0406ef3e18c40c9667a8cffdf71604973d5747dacc177b9c29248fba7a98e69c3eef1be40664090e274e7a235cf8d246480b6dc
|8,1=>0xa6756efab8a8fece6ca640ef4eb75a574a
|9,0=>0x404f666644407691909fbc774097f27544bbc4447cf07949f6abf7d6f84fd1e0c7d440796bf94046d67498a1c846d6d6fc
|10,0=>0x496f224040bb74
|11,0=>0x16
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 40 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_126 10 roots_126 ops++addP pm 1 dom_123 10 roots_123 ops++addP pm 2 dom_111 9 roots_111 ops++addP pm 3 dom_125 10 roots_125 ops++addP pm 4 dom_119 9 roots_119 ops++addP pm 5 dom_95 9 roots_95 ops++addP pm 6 dom_85 5 roots_85 ops++addP pm 7 dom_31 5 roots_31 ops++addP pm 8 dom_61 7 roots_61 ops++addP pm 9 dzo_46_16 5 roots_46 ops++addP pm 10 dzo_43_4 5 roots_43 ops++addP pm 11 dzo_111_16 7 roots_111 ops++addP pm 12 dom_101 5 roots_101 ops++addP pm 13 dom_84 4 roots_84 ops++addP pm 14 dom_124 8 roots_124 ops++addP pm 15 dom_53 4 roots_53 ops++addP pm 16 dzo_85_2 5 roots_85 ops++addP pm 17 dom_79 6 roots_79 ops++addP pm 18 dom_63 8 roots_63 ops++addP pm 19 dzo_47_16 6 roots_47 ops++addP pm 20 dzo_107_4 6 roots_107 ops++addP pm 21 dom_109 8 roots_109 ops++addP pm 22 dom_55 5 roots_55 ops++addP pm 23 dzo_110_16 6 roots_110 ops++addP pm 24 dzo_117_2 6 roots_117 ops++addP pm 25 dom_43 5 roots_43 ops++addP pm 26 dom_29 4 roots_29 ops++addP pm 27 dom_103 6 roots_103 ops++addP pm 28 dom_93 7 roots_93 ops++addP pm 29 dom_59 7 roots_59 ops++addP pm 30 dom_62 6 roots_62 ops++addP pm 31 dom_41 4 roots_41 ops++addP pm 32 dzo_107_16 6 roots_107 ops++addP pm 33 dzo_125_2 7 roots_125 ops++addP pm 34 dzo_93_2 6 roots_93 ops++addP pm 35 dzo_121_2 6 roots_121 ops++addP pm 36 dom_117 7 roots_117 ops++addP pm 37 dom_115 7 roots_115 ops++addP pm 38 dzo_59_4 6 roots_59 ops++addP pm 39 dom_121 8 roots_121 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_127 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_46_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_43_4_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_111_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_101 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_53 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_85_2_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_79 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_zo_47_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_zo_107_4_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_zo_110_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_zo_117_2_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_29 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_zo_107_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_zo_125_2_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_zo_93_2_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_zo_121_2_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_zo_59_4_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_121 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_126 10 s (0,roots_126.map (·&&&dom_126)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_127 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_126 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_127==dom_127)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_127 gM v ys):RunD true dom_127 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_127 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 14 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 14 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 82 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 82 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 161 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 33 128 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 161 → Z 7 i = true := (range_split z7_0 z7_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 145 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 17 128 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 145 → Z 8 i = true := (range_split z8_0 z8_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 49 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 49 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 7 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_127 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
  · exact z11 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 6 6=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤11) (h:RunD true dom_127 gM s xsM):False:=by
  have hmin:6≤s:=by have hl:=run_len h;change 7≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_127 roots_127 goal_127 12:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_127
theorem lowS_127:Lower true dom_127 roots_127 goal_127 12:=S_127.noCircuit
def dzo_212_2:=0x440044000000000044004400000000004400440000000000440044
def gzo_212_2:=0x440044000000000044004400000000004400400000000000400000
def gsh_212_2:=0x110011000000000011001100000000001100100000000000100000
theorem lowS_zo_212_2_84:Lower true dzo_212_2 roots_212 gzo_212_2 5:=lower_iso_b (d1:=dom_212) (r1:=roots_212) (T1:=gsh_212_2) [(dom_212,2)] (by decide +kernel) (lower_slice_b (T:=gsh_212_2) [(0x110011000000000011001100000000000000000000000000000000,0,128)] (by decide +kernel) lowS_84)
def dzo_209_2:=0xc000c00000000000c000c00000000000c000c00000000000c000c
def gzo_209_2:=0xc000c00000000000c000c00000000000c00080000000000080000
def gsh_209_2:=0x30003000000000003000300000000000300020000000000020000
theorem lowS_zo_209_2_81:Lower true dzo_209_2 roots_209 gzo_209_2 5:=lower_iso_b (d1:=dom_209) (r1:=roots_209) (T1:=gsh_209_2) [(dom_209,2)] (by decide +kernel) (lower_slice_b (T:=gsh_209_2) [(0x30003000000000003000300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_81)
def dzo_213_2:=0xcc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc
def gzo_213_2:=0xcc00cc0000000000cc00cc0000000000cc00c80000000000c80000
def gsh_213_2:=0x330033000000000033003300000000003300320000000000320000
theorem lowS_zo_213_2_85:Lower true dzo_213_2 roots_213 gzo_213_2 6:=lower_iso_b (d1:=dom_213) (r1:=roots_213) (T1:=gsh_213_2) [(dom_213,2)] (by decide +kernel) (lower_slice_b (T:=gsh_213_2) [(0x330033000000000033003300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_85)
def dzo_217_2:=0xc0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c
def gzo_217_2:=0xc0c0c0c000000000c0c0c0c000000000c0c0c08000000000c080c00
def gsh_217_2:=0x3030303000000000303030300000000030303020000000003020300
theorem lowS_zo_217_2_81:Lower true dzo_217_2 roots_217 gzo_217_2 6:=lower_iso_b (d1:=dom_217) (r1:=roots_217) (T1:=gsh_217_2) [(dom_217,2)] (by decide +kernel) (lower_slice_b (T:=gsh_217_2) [(0x3000300000000000300030000000000030003000000000003000300,0,8),(0x3030303000000000303030300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_81)
def dzo_221_2:=0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc
def gzo_221_2:=0xcccccccc00000000cccccccc00000000ccccccc800000000ccc8cc00
def gsh_221_2:=0x33333333000000003333333300000000333333320000000033323300
theorem lowS_zo_221_2_85:Lower true dzo_221_2 roots_221 gzo_221_2 7:=lower_iso_b (d1:=dom_221) (r1:=roots_221) (T1:=gsh_221_2) [(dom_221,2)] (by decide +kernel) (lower_slice_b (T:=gsh_221_2) [(0x33003300000000003300330000000000330033000000000033003300,0,8),(0x33333333000000003333333300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_85)
def dzo_220_2:=0x44444444000000004444444400000000444444440000000044444444
def gzo_220_2:=0x44444444000000004444444400000000444444400000000044404400
def gsh_220_2:=0x11111111000000001111111100000000111111100000000011101100
theorem lowS_zo_220_2_84:Lower true dzo_220_2 roots_220 gzo_220_2 6:=lower_iso_b (d1:=dom_220) (r1:=roots_220) (T1:=gsh_220_2) [(dom_220,2)] (by decide +kernel) (lower_slice_b (T:=gsh_220_2) [(0x11001100000000001100110000000000110011000000000011001100,0,8),(0x11111111000000001111111100000000000000000000000000000000,0,128)] (by decide +kernel) lowS_84)
namespace S_223
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(2,10),(2,130),(3,11),(3,19),(3,67),(3,131),(4,20),(4,68),(4,132),(5,13),(5,21),(5,69),(5,133),(6,14),(6,22),(6,70),(6,134),(7,15),(7,23),(7,71),(7,135),(8,9),(8,10),(8,72),(8,136),(12,13),(12,14),(12,28),(12,76),(12,140),(16,17),(16,20),(16,80),(16,144),(18,19),(18,22),(18,26),(18,82),(18,146),(24,25),(24,26),(24,28),(24,88),(24,152),(64,65),(64,68),(64,72),(64,80),(66,67),(66,70),(66,74),(66,82),(66,194),(128,130),(128,132),(128,136),(128,144),(129,131),(129,133),(129,137),(129,145),(129,193),(192,193),(192,194),(192,196),(192,200),(192,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffffffffffff
def xsM:=roots_223.map (·&&&dom_223)
def gM:=goal_223&&&dom_223
def NN:Nat→Nat
|4=>10
|5=>35
|6=>102
|7=>258
|8=>246
|9=>105
|10=>12
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xc26c59e8179be688138d6cbdf5d4df4dd52298991da9f150eb
|5,0=>0xfd692d9bb5d9aabd731fcbeaec5adac2affc0269bebf0bc35ab634dababba86559ec519c3bb982688cc2e795376486663d424cc8c4bf0948d7d480403aa2328dde28d9c23697217e31d6a306e1206d0803d9f015a100f59
|6,0=>0xfdaccfb236f89abf7829ecbc8de878d9bb5d9aabd3235d2607ce6f8cc149c2affbebf0bc134b9d0cb7ac1b71b4b7063b4504ae9cdae717a9012a8f9aa6bcea5e09a3240a301ea149b9ec51982869501b918f8913d98977487c598300d804d2798ff795a0785ad78252756d773f71710346b92f66247616255d1d15c57f565ec51e7e4e7a64d76b4ab174847a4761845cee45be44456b41cd5406043fe353f2053ca1b3c4da3c0db347e9344a9314362e9522e2152c7fe2bdfc2ad292ab1a297b32527124850246c722a411f4e31c70b1bf871a9a618fe817df61728314a78143b21300b123a010c5010b460ac3209015074d00724c060ee049b6035b2009e9
|7,0=>0x4a2d54a2d24a2cb4919f48b664847a480a047fd547d7546b12469264679c455784539c44cc544c47448e34456b43ab84369f4286341ade41aaf3fde23e8f03e2e73d74c3cf0a3cd323b6213adfb3aadd37b763731e35cc53517034fcf34c4834b673479a340ae3326a32da33215d3108d30c932fc3f2f7f72d9002acc12a3cf2a3ac2954c27f4927e7d2798f241fd23aae22c1b228bc2200421d6721712214682065b2009d1f72a1ea001e9721e7d11da731d5291d1871cca41cb491b8a31b87e1abdb19db417c4f179621750e168c515eea156e514fe414a7814a3b1482314481134e21340c131a2130f911614102300f5860f55d0ea540e6b90e5480d9f40d67e0d5d40c9720c71b0c2720bed30ad970a8f20a63c09e5809b380959009498088d707fdc07e94074e7072b70724c06d9a06783051820459c0244300881002d2
|7,1=>0xf401ff12aaef451ee91ae7dcfe6ee9e532fe47aee2ac4e1b9bde75bde58dd9baad6eecd3857cca8ccc91ecb176c6340c4913c3371c243bc1e8ac1b97c1838c139cbef29bca1abaff4ba186b7da0b5aa1b587bb4ec8b31d7b14e3b06a4af30cad8dfaaf62a96efa9502a8c71a7e3fa5056a4e5ea49e6a49a4a4817a4135a2a95a149ba02429c42b9b284966fe94e0d93151930d591161905ad8ece48dd828da738d1658ce4b8b5c1891b488e5f8871186eb585c248508484f3a8344780bb1804dc804d27f6527f5157f3ca7eff87e0ac7cf3e7b6067b2027af2a7acfb77f41771e57582570e0d6f3656eaa86d6396b42c6ace76a1ea69b356974b66bab65ae7635bf5cbcd5c5225be1059654595125819d5544754edc54c2f5333752f6851ee7519ca515cd515624fcf44de9f4de934cfd44cab94c5854bfd94bb134ba5c4ac7d
|7,2=>0xfdaccf69af
|8,0=>0x4e0c24de6a4cff24bd414b43f4a64f49f5b49d0746fd245d644553f44cfa44c05442f343ecf4387c4364f4354a42e134266f41d2a41ade41215407904014b3f0653ec353e32d3b99c3b5733980e3953738dee3881337be4375f6366bd35b843572d356c43567f3547b3541d34fe7346223448d33fda33f68327383167f30e5b30e2c3085d3080a2fe122f2662eb7f2eb7c2e7c42e3352d8152bbdb2b5712a6452a3ac2a19229e3329d0528c2e25e6c2521224f5624c7e24c0821f8520b9f1ff4d1f8511e1ca1d54f1bd621ba7b1b4fe1ae4f1ad1e1a6fd19b2519a641922418f35184b417ac41725816c00157ca14c8d14a3b13b291348a1316212c6c125631207211e0e117ff1123110efe10baf0f76e0f3360f1990e9740d9680c4d80b30c0b0b80a298098990880c0602a059040326d03107025e20134800afc00a9c0077d
|8,1=>0xf2d98eb1beea502e87fee7e80e44cfe13ebda658da2a3da1ced9fead7d07cf845cf532c8532bc413bbf9cb9fc5b8cd2b838eb6c32b5200b3b5ab29b5b21b2b1aa7b029daf616ac879aaab7a9f15a6be1a3654a1e42a1a3aa04a49ddb9975d99632d93e369333790726907128dd828d80f8ba428ab378a22889b8586fa686932853218529f852998416c8358a83447823fe81d6a814338104a8100f80ff680dd47d5ab7d3897cc157ca7c792f976cc87633674860743bb724097217a718897089870494701816fc5c6eaca6ca826b15269ffa6920466fef66049656706490063e77637c26378f62f1662491614476129c6124f610d960e8760cd1608ca5fd395e4745dacc5c6c15b9ff5b7825734a558655395e5357d529285265d5245f5180b501d44fd544f4e4
|9,0=>0xfabeaeb26adc5d7d6d3ccd971cb6dfc99f7c76b0c42f2c0783becb9bbbe3ba37bb9726b0d29ab461a69a6a5c93a368da2583a23daa123fa01009eebe9d7749d6319b951949349395e8fec58f40387e358792d866dc855f084dc982dfd806347eeaa7d5ab7d2e17c1e27a5f277ed377ea6775b672e2d720057139370e756c2316bc1d6b4d8635dd628ed6168f5916d57c13578ef56770561e553f0253072518fd4fa7d4d7b84d03f4ce6e4974c48c2b462ea44534430f93dbd93d23c3c7f9398d735f033573b33dff3335630b7f2e12b27042267b1242cf2356a1ffcb1fdfe1c0f519e441949e178f016a2a117201073a0febd0d6750c7390bd410b10509f9c06d07061a105aff
|10,0=>0xe9ab7c52d4ae79e7474a6375a4e3a9451472b9ac281b4259c11f14a1730e
|11,0=>0x1730e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffff0000000000ffffff0000000000ffffff0000000000ffffff00fffffff000000000fffffff000000000fffffff000000000f0f0f0f0ffffffcc00000000ffffffcc00000000ffffff0000000000cc00cc00ffffffff00000000ffff000000000000ffffffff00000000ffff0000ffffffff00000000ffffffff00000000ffff000000000000ffff0000ffffffff00000000ff00ff0000000000ffffffff00000000ff00ff00ffffffaa00000000ffffffaa00000000ffffffaa00000000aaaaaaaaffffffff00000000ffffffff00000000ff00ff0000000000ff00ff00ffffffcc00000000ffffffcc00000000ffffffcc00000000cccccccc000000ff00000000000000ff000000000000000000000000ffff0000000000ff000000000000000000000000000000ff00000000ff00ff00000000ff000000000000000000000000000000ff00000000ffff0000000000ff00000000000000ff000000000000000000000000ff00ff00f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0cccccccc00000000cccccccc00000000cccccccc00000000ccccccccaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa
|0,1=>0x55555555000000005555550000000000555555550000000055555500cccccccc00000000cccccccc000000000000000000000000cccccc00cccccccc00000000cccccccc00000000cccccccc00000000cc00cc00555555550000000055555555000000005555555500000000555555000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f00ffffffff00000000ffffffff00000000ffffffff00000000ffff0000000000cc00000000000000cc00000000000000cc00000000cccccccc33333333000000003333333300000000330033000000000033003300cccccccc00000000cccccccc00000000cc00cc0000000000cc00cc00ffffffff00000000ffffffff00000000ffffff0000000000ffffff00ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00ffff000000000000ffff000000000000ffff000000000000ffff0000ffffffff00000000ffffffff00000000ffffffff0000000000000000ffffffff000000000000000000000000ffffffff0000000000000000ffffffff00000000ffffffff00000000000000000000000000000000ffffff0000000000ffffff0000000000ffffff000000000000000000
|0,2=>0xff00000000000000ff00000000000000ff00000000ff00ff0000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff000033333333000000003333333300000000333333ff00000000333333000f0f0f0f000000000f0f0f0f000000000505050500000000050505000f0f0f0f000000000f0f0303000000000f0f0f0f000000000f0f030000000000000000000000000000000000ffffffff00000000ffffff00333333330000000033333333000000003333333300000000333333000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0000ffffffff00000000ffffff0000000000ffffffff00000000ffffff00555555550000000000000000000000005555555500000000555555000f0f000f000000000f0f000f000000000f0f000f000000000f0f0000000000000000000000ff0000000000000000ff000000000000ffff000000000000000000ffffffff000000000000000000000000ffffff000000ffff000000000000ffff000000000000ffff000000000000ff0033333333000000003333333300000000333333000000000033333300cccccccc00000000cccccccc00000000cccccc0000000000cccccc00
|0,3=>0xffffffff00000000ff00ff0000000000ffff000000000000ff00000000000000000000000000ffff0000000000ff00ff0000000000000000333333330000000033333333000000000000000000000000333333003333333300000000333333330000000033ff33ff0000000033ff3300cc0ccc0c00000000cc0ccc0c00000000cc0ccc0c00000000cc0ccc00cccccccc00000000cccccccc00000000cccccccc00000000cccccc0033003333000000003300333300000000330033330000000033003300000000ff00000000000000ff00000000000000ff000000000000000033333333000000003333333300000000333333330000000033003300ffffffff000000000000000000000000ffffffff00000000ffffff00ffffffff00000000ffffffff000000000000000000000000ffffff005555555500000000555511110000000055555555000000005555110033033303000000003303330300000000330333030000000033033300cccccccc00000000cccccccc00000000ccffccff00000000ccffcc00ffffffff00000000ffffffff00000000f0f0f0f000000000f0f0f0f033033303000000003303330300000000330333030000000033003300
|0,4=>0xff00ff0000000000ff00ff0000000000ff00ff00000000000000003333333300000000333333330000000033ff33000000000033ff330000000000000000000000000000000000ffffff0000000000ffffff00ffffffff00000000f0f0f0f000000000ffffffff00000000f0f0f0f0ff00ffff00000000ff00ffff00000000ff00ffff00000000ff00ff0033333333000000003333333300000000333333330000000033330000fff0fff000000000fff0fff000000000fff0fff000000000fff0fff0ffffffff00000000ffffffff00000000ffffffff00000000ff00ff00ffffffff00000000ffffffff00000000ffffffff00000000f0f0f0f0ffaaffaa00000000ffaaffaa00000000ffaaffaa00000000ffaaffaaffffffff00000000ffffffff00000000ffffffaa00000000ffffffaa55555555000000005555555500000000555555000000000055555500ffffffff00000000ffffffff00000000ffffffff00000000ffffff00000000000000000000000000000000000000000000000000ffffff00ffffffff00000000ffff000000000000ff00ff0000000000ff000000000000ff00000000000000ff00000000000000ff00000000ffff0000
|0,5=>0xffff00ff00000000ffff00ff00000000ffff00ff00000000ffff0000ffffffff00000000ffffcccc00000000ffffffff00000000ffffcccc00000f0f0000000000000f0f0000000000000f0f00000000000000000000ffff000000000000ffff000000000000ffff0000000000000000ffffffff00000000ffffffff00000000ffccffcc00000000ffccffccffccffcc00000000ffccffcc00000000ffccffcc00000000ffccffcc33333300000000003333330000000000333333000000000033333300ffffffaa00000000ffffffaa00000000ffffffaa00000000ffffffaaffffffff00000000ffffffff00000000ffffffff00000000fff0fff0333333330000000033333333000000003333333300000000333033303333333300000000333333330000000033323332000000003332333233333333000000003333333300000000333333220000000033333322ffffffff00000000ffffffff00000000ffffffff00000000ffffcccc0f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0c0cffffaaaa00000000ffffaaaa00000000ffffaaaa00000000ffffaaaaffffffff00000000ffffffff00000000555555000000000055555500
|0,6=>0x55555555000000005555554400000000555555550000000055555544cccccccc00000000cccc000000000000ccffccff00000000ccff0000ffffffcc00000000ffffffcc00000000ffffffcc00000000ffffffcc0000000000000000000000000000000000ff00ff0000000000ff0000ffffffff00000000ffffffff0000000000ff00ff0000000000ff0000ffffffff00000000fff0fff000000000ffffffff00000000fff0fff00f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f000f00ff0fff0f00000000ff0fff0f00000000ff0fff0f00000000ff0fff00fafafafa00000000fafafafa00000000fafafafa00000000fafafafaffffffff00000000ffffffff00000000aaaaaaaa00000000aaaaaaaa0f0f0f0f000000000f0f0f0f000000000f0f0f0f0000000000000000ff0fff0f00000000ff0fff0f00000000ff0fff0f00000000ff00ff0011111111000000001111110000000000111111110000000011111100000000000000000000000000000000000000ffff000000000000ff00ffff000000000000ffff000000000000ffffffff00000000ffffff000000000000000000ffffff00000000000000000000000000ffffff00
|0,7=>0xffffffff00000000ffffffff00000000fffafffa00000000fffafffaffff333300000000ffff333300000000ffff330000000000ffff3300ffffffff00000000ffff333300000000ffffffff00000000ffff3300cfcfcfcf00000000cfcfcfcf00000000cfcfcfcf00000000cfcfcccccccccccc00000000cccccccc00000000cc00cc0000000000cc00ccccfffafffa00000000fffafffa00000000fffafffa00000000fffafffaffffffff00000000000000ff00000000ffffff000000000000000000cccccccc00000000cccccccc00000000ccffccff00000000ccfcccfcffffffff00000000ffffffff00000000fff0fff000000000fff0fff0cccccccc00000000cccccccc00000000ccc0ccc000000000ccc0ccc00000000000000000ffff3333000000000000000000000000ffff3300000f000f00000000000f000f00000000000f000f00000000000f0000555555000000000055555500000000005555550000000000555555003333333300000000333333330000000011111100000000001111110000000000000000005555550000000000000000000000000055555500ffffffff00000000ffffffcc00000000ffffffff00000000ffffffcc
|0,8=>0xffffffff00000000ffffffff00000000ffffffff00000000cccccccc0000ffff000000000000ffff000000000000ffff000000000000cccc0f0f0f0f000000000f0f0f0f000000000f000f00000000000f000f00ffffffff000000000f0f0f0f00000000ffffffff000000000f000f000000000000000000ffffcccc000000000000000000000000ffffccccff00ff0000000000ffffffcc00000000ff00ff0000000000ffffffcccccccccc00000000cccccccc00000000ccffccff00000000ccffccccff00ff0000000000ffffffff00000000ff00ff0000000000ffffff00cccccccc00000000cccccccc00000000ccfeccfe00000000ccfeccfeffffffff000000000000ffff00000000ffffffff000000000000ff00ffffffff00000000ffffffff00000000cccccccc00000000ccccccccff00ff0000000000ff00ff0000000000ff00ff0000000000ffff0000ffffffff000000003333333300000000ffffffff00000000330033000000ffff0000000000003333000000000000ffff0000000000003300ffffcccc00000000ffffcccc00000000ffffcccc00000000ffffcccc00000000000000000000ffff0000000000000000000000000000ff00
|0,9=>0xffffffaa00000000ffffffaa00000000000000000000000000000000ffffffff00000000f0f0f0f0ff00ff0000000000ff00ff0000000000ffffffff00000000fff0fff000ff00ff0000000000ff00ff0000000000ff00000000000000ff0000ffffffff00000000ffffffff00000000fafafafa00000000fafafafa00ff00ff0000000000ff00cc0000000000ff00ff0000000000ff00cc0f0f0f0f000000000f000f00000000000f0f0f0f000000000f000f00ffffffff00000000ffffffff00000000ffffaaaa00000000ffffaaaa00ff00ff0000000000f000f00000000000ff00ff0000000000f000f0ffffffff00000000ffffffff0000000000ff00ff0000000000f000f0f0fff0ff00000000f0fff0ff00000000f0fff0ff00000000f0f0f0f00000000000000000000000000000000000fa00fa0000000000fa00fa0055005500000000005500550000000000550000000000000055000000ff00ff0000000000ff00000000000000ff00ff0000000000ff000033333333000000003333000000000000333333330000000033330000ff33ff3300000000ff33ff0000000000ff33ff3300000000ff33ff00
|0,10=>0xffffffff000000003333333300000000ffffffff0000000033330000ccffccff00000000ccffcccc00000000ccffccff00000000ccffcccc0000000000000000000000000000000033333333000000003333000000ff00aa0000000000ff00aa0000000000ff00aa0000000000ff00aaffffffff000000003333330000000000ffffffff000000003333330000000000000000000000000000000000ffffffff00000000ff00ff000000000000000000ffffffff000000000000000000000000ffff0000fcfcfcfc00000000fcfcfcfc00000000fcfcfcfc00000000fcfcfcfc0000000000000000000000000000000000ff00ff0000000000f000f055555555000000005555555500000000555500000000000055550000ff55ff5500000000ff55ff5500000000ff55ff0000000000ff55ff0000000000000000000000000000000000ffffffff00000000fff0fff0ffffffff00000000cccccccc00000000ffffffff00000000cccccccc0000ffff000000000000cccc000000000000ffff000000000000cccc333333330000000033333300000000003333333300000000333333000000000000000000ffffffff000000000000000000000000ff00ff00
|0,11=>0xff00ff00000000000000000000000000ff000000fa00fa0000000000fa00fa0000000000fa00fa0000000000fa00fa5555555500000000555555550000000055005500000000005500550000000000000000000000000000000000fcfcfcfc00000000fcfcfcfcffff333300000000ffff333300000000ffff333300000000ffff00003333333300000000333333330000000033333333000000000000000000000000000000000000000000000000555555000000000055555500000000000000000000000000000000000000ffff000000000000cccceeeeeeee00000000eeeeeeee00000000eeeeeeee00000000eeeeeeeecccccccc00000000ffffffcc00000000cccccccc00000000ffffffcc00000000000000000000000000000000fffafffa00000000fffafffa3333333300000000333333330000000033303330000000003330333000000000000000000000000000000000fafafafa00000000fafafafaff00ff0000000000ff00ff0000000000fffafffa00000000fffafffa00000000000000000000000000000000ffffcccc00000000ffffcccc33333333000000003333333300000000333300000000000033330000
|0,12=>0x5454545400000000545454540000000054545454000000005454545400000000000000000000000000000000ffffffff00000000ccccccccffffffff00000000fcfcfcfc00000000ffffffff00000000fcfcfcfcffffffff00000000ffffffff00000000fcfcfcfc00000000fcfcfcfcffffffff00000000ffccffcc00000000ffffffff00000000ffccffcc00ff00ff0000000000cc00cc0000000000ff00ff0000000000cc00cc0000000000000000fcfcfcfc000000000000000000000000fcfcfcfc00000000000000000000000000000000eeeeeeee00000000eeeeeeeefffcfffc00000000fffcfffc00000000fffcfffc00000000fffcfffc33333333000000003030303000000000333333330000000030303030fefefefe00000000fefefefe00000000fefefefe00000000fefefefe0000ffff000000000000ff00000000000000ffff000000000000ff0000003333000000000000333300000000000033330000000000000000aaffaaff00000000aaffaaff00000000aaffaaaa00000000aaffaaaa00000000000000000000000000000000ffffffff00000000ffff00000000ffff000000000000ffff000000000000ff00000000000000ff00
|0,13=>0x555544440000000055554444000000005555444400000000555544443333333300000000330033000000000033333333000000003300330000000000000000000000000000000000ffffaaaa00000000ffffaaaa32323232000000003232323200000000323232320000000032323232
|_,_=>0
def sP:Nat→Nat
|0=>0xc150219091114080e01091216140a0201090b0a021900100c08020018100c08021700101408020d0012160c150201090b150e01091214080207091214030e0100120c080e0100100f0c080201090c080e01090b0a0e01090c08020d000c080207090c030201090b0a020709060a020109040802070006050201000403020100
|1=>0x9110b150e0100121408020700120b150e0700120b0a020109100b15020709120c08020100100c08020700100c15020109110c15020709110615020109120c03020100100b0a0e0100130b0a020100100b0a02070010040802010010060a020100101a080e0100120415020700110b150e1900120c08021900101a0a0e010011
|2=>0x20001b12111415021f21121114050201001011141502201f1211141502070012110f0b021d001312140a02010913111415021e0013120b150e01001312140802070013120f0c021d0013111415011c1b12110c150e010013110b150201001210141500181b12110b1502070012100f1a0217001312141517001b12110c150e01
|3=>0xf1402171f1211231415021700130b150201091210140302010012101415002928121114081502012612271415022000130f0b15020126120c150201091011140801002513120f140a020700111415011f1b1211140a0e010013110f020100241211231502010022110f0c02170013141500211b12110f0b0a020100101415
|4=>0x301312142f0201001211160c150201001023140201002e1114080e01001312231415022000130f0c150e010011141502002d1211140802010012101415011f2c12110b150e01001210140802070012101415020109121114150207091211141500182b12110f0c08020100100b1415020126121415021c2912112a2314150201
|5=>0xa020100100b0a0201001338141500371b12111415021f3712110b150219001210161415020126120c15021900101114150e01091211141502011c121116140a020100101a0a0201001011363514150201001415020134121114080201091210141500332812110f0c08020018130f0c08021700131415023200121114153100
|6=>0x190912110f3f020100130c08020100100c15020109110c0802010013381415020100133e140a1502003d11141502003c12111415023a1c12111a150e0100121114153b00281211140802001812101408021700121014153a002812111a0802010012100b15020039131214151d001b121116141502010912141502190012110b
|7=>0x1210144948470100121135140a15020100110f140201002e12114514150201441211140a1501001b12110b1502010013123842140a15020100110c1502010010110c1502070010110f41020100131415011f281211401502010012112a140201002e120b150e0100121408020700120415020100101114080219001210141502
|8=>0x20150121127141502002912111415010028124f110f0c0201002e12110f0c0802010013141502002913121143141502002112110f0c080217001211141502004e12111a1415021d001211164d14150200211243141502200012111449484c010013110c4b150201001311141501004a28121114480201001210110b15020100
|9=>0x2011f591211140a020100133811140802001813124f581415020144121143141502011f121116141502001813120b4b150201001312144815023a00121114150200561312110f0c080200181211141502005512114514150200541211141501005213121116141502170013120f144802003712111415021900121011511415
|10=>0x141501001b12115f140a020100131123141502010013110f1448021d0012115e141501002812110b15010028125d1116141501002812110f0c1502002112110c141502011c12110b15010028125c1143141501001b12110f0c1502200012112a161415020100121614150200541211141502070012110c141502001812111415
|11=>0x111415021e001211140a15310100136514641531010013120f5115020144121114150200391312110f420c1502010011141502011f63121114150100282e1211610b15020100121123140815020100130f600c0802010011351415020100131227231415020100110f1415021900121114153f0201001358141502005412110f
|12=>0x28121114494801006912110f140a02200012111415020037126511146a150100691211230b1415020100130b14150200291211271415020100101116140201002e1211421408150201001214150201261211144b150200391211421415020100121114681501002812111449086701661216141502011c12110f140802011f12
|13=>0x541211420b1415020100120b15020100131210351415021e001211270f1408020100131a1415023a001211350c1415020100110f5f150201001211140a15020056121136140815020100120b141502016644125114150201441211420c1415020100110f140a020021121145141502002112110c150201001310111448150100
|14=>0x2012612111415020072121127141502011f7111144b0201001238110c141502016f1211141502170022121127141502003712111415026e0100121114490a02003712116d141502011f12111415020109121158141502002112111408150201006b1214481502011c12114d1415020126121114080201001312385114150200
|15=>0x111415023a0012110f1a1501002812111464150200301211141531020037131214150100287412110c145a080201001314150207001312112760141502011f111415020018221211141541020100135f1408020100131243141502002912111449084c010013360b1415020100121408020100121023140a1502010011361415
|16=>0x1279112a1a14150201001243231415020100111415027800121127161415020100130f14021d001211141502760013120f480201002212111a141502170013120c15010028125d110f4d0b0a020100120f51150200211211140a02010013101114490a4701001311272a1415020100130c15010028125c1175141502001812
|17=>0x200186c12112a140a150201001314150200301265110f4d0c080201001214150217006c12110c1415021700131a141502011c1211146a150200561211141502005412111464154c010013110c1415020029121114641547010012110f230c1502010011147a150200551211580f140217001211141501002513121114150201
|18=>0xf23140a0201001114157c01002812111415027b0012111415023a00131211141502010012101114150207001210110b0a15020100135c141502011c1211160f1446020166121408020100131210140a15010028131114490847010013120f51080201731211230c141502010011141502010913121116141502002912111415
|19=>0x1448020018124f116014150200211211140a0201002e1311141502010082121136161415020100120f811502011f12110f14021d001312111a141501001b12114314150201001211147f150200551211271502010022121114150e01001312111a141502011f12117d1415020100121116421415020100121415020030131211
|20=>0x6f12110f140a02003712111415026e00181211140a1502011f13110c145a08028500121484150201001211231448150201001153141501002812110f14021700131214494802003712110f0b4602016612160f0c15020100131a15020100123811146a15020037121114150219001211145a1501002812117e14150200831211
|21=>0x201002e131288140a0201001211160f140a020100130f1a0a020100131114150200376912114d0b141502002112141567020055121136421415020100112a1408150201001214154c02170013141502870012110c141502010086111a4b1502010012110f1446020144121116141502004e1211141502010912101114150201
|22=>0x12110f0b0a020100130c1415023a001211432a141502010012140a1502011c1211141502003d1211141502890012110c141502011f13111415020037221211141501001b13121114150200291211271415020021121114081502011c12112a0b1415020100121a14150100521211431415023a0012111415020039125c111408
|23=>0x2010012111448150200371312111415020100691312110f140802170012115e0c141502010013110b14150201006212110f0b150201007312110f144602017312110f14150201001210110c1502010010110f1408020018131243141502001812110f140802170013127d1415020018121143141502170012111415021d0022
|24=>0x110f600c1502010011580f0b1502010012110f1415020021121116141502010044121114901502010012110c141502170012110f14150220001211160f1446020100121114150201008e12111415020037121114150201008c1211430f14150201001211160b141502010013120c141501002812110f140802001812118a1415
|25=>0x12110f140802016600120f144802010012110c145b15020100121114150201009312111415020100921311450b1415020100121114150201006c12110c14150200181211144815021d001312110f0c150201005912111a140a1502010013111464150201001211271448150201001211145a08028500121449480a02010012
|26=>0xc14150201001114150201009913110f144602016612110f9815020100121116141502170012111415020100961211145a15020100125c1114150201009113111415020100221312110c1448150201001311141595020100121114150201009412111415021d0012111623141502010012110f141502011f12112a140a150201
|27=>0xa15020100691211147a159b0201001211140a153102010013147a150201661211141567020018121114150201009a12114214150201001211160f141502010013120f1a1502010013121114081502010013125c2760140a15020100111415670217001211430c1415020100121116141502001812110b144815020100131260
|28=>0x111448020100124f11361415020100121114771502010013121a145a1502010012112a0f141502010012111415020166009c124d1408150201001214480a15020037121114081502010022121135141502010012110f140a0201005912110f810a02010012110f4d0b15020100120f60140a02010011144b15020100125c1114
|29=>0x13111415020100a1121116141502002112111614150220001211146415020100126511531a141502010012110b140a150201001327140a1502011f12110f14a00201001211146a154c02010013119f14150201001211431614150201001211450f141502010012111614150201660012146a15470201001211149d1502010012
|30=>0x1001211147f1567020100121114490aa8010012110c14150201004a12111415020100a712116d0f0c15020100121114150201008012114d0b1415020100120f140802010073121114a5150201001211145a0802010013121a140815020100131214150201006b1211271a1415020100121114a41502010012111415020100a2
|31=>0x15020100121151141502001812110f0b1502010013122a0c141502010012111a15020100125c111457154702010012111415a83101001312364d1415020100121151141502170012115314150201001211146415020100131211140a150201002212110f0c1502010013110fa91502010012111415020100971311270f811502
|32=>0x121145161415020100121116141502010073121127600c1415020100110c1408150201001314576a1502010012110c14081502170012111415020166ac12110f1415020100ab12116114150201001211585114150201661211270f141502011f1211147f159b0201001211580f140802010012110c14150201001812110f1a0b
|33=>0x1211141502170013121449159b67010012110f14480802010012110f600b150201001211141502ae010012111415020100ad121114491567016612111448154c02010013114214150201001312111a141501002812111448154702010012111408150201006c12110c140815020018121158141502017312116d0f140a020100
|34=>0xb114150201001312271415020100a112117e1415020100121114150100281211231415020100121114490a31010012111415020100af12110f4d1408020100120f51150201731211146a48150201001211140a150200371211270c141502011f12115e14150201001311141502760012111415020100441211274d1415020100
|35=>0x131151141502017312111415020100121011140815670201661214b5150201001211144808020100124f1116144815020100121114150200b412115314150201001312115814150201661211141502001812110f980b150201001211431a1415020100121114150201001312381114b21502010012111a1415028f01001211
|36=>0x201001312bb141502010012110b145a1502010013120f140802010013124314150201001211144b150201001312111a141502010012ba114551141502010012110f1a0c1502010012111415020100b912110c145a1502010013111415020100b812111415a867b712115f1415020100131211b6141502010012111449154c01
|37=>0xf4d0c150201001211144815020100125c1114490802016600125e1a14150201001211c1145a150201001211141502010086121114150201009c131251140815020166121408154c020100131415020100bf12111415020166be12110f14020100bd1211881415020100121114480a020100124f11147f1502010012111415bc
|38=>0x11431408150201001211810b1502010013120f0b1502016600120b141501002812110f4d140a02010012111a14481502010012110b15020100125c1114153f02010012111449154701001312110f1415020100a1121145141502010012112a141502010012111a14150201002e121114150201c2001211160f14150201660012
|39=>0x110f811502010012111614081502010012111415670285010012111415020100c412111a141502010012119851141502010012110f1a150201001211430b141502010012110c145a0802010012111415410201001211141502010012c3110c145a150285001211530c141502010012117e141502001812110c14150201008012
|40=>0x1502010013125c11140a150201001311145a154c0201001211147a15670201001211144915a801001211160b1415020100121160141502010012111415c567020100121151145a150201001211145a1502b7001211140815670201001211144815020100131211146a0a1502010012111415a802b70012110f14150201005912
|41=>0x1114c71502010012111477150201001211580f141502010012110b141502a30100121114150201001265111a14150201001312116d0f1415020100121114490802010012115114081502010012111415020100c612110f1415020100731211981415020100121114461502b70112114d14150201001211811415028500121114
|42=>0x1502010012110b141502010013121415020100bd12110c141502010013115e0c1415020100121114153102010013121415c902010012118114150201001312110f1415020166001211145a080201001211140815020100131214490a02010012111449153101001211145a1502850012111415020100c01211141502c8010012
|43=>0x12111415670201661211141502001812111415474c0201001211145a150201001312111446153102010012111415cc02010012111415021700121114150201009912111415a8020100131211147a150201001211141502010091121114cb15020100121114150201009212111415020100ca12111415c502010012111a0b14
|44=>0x154c020100131114154702010012111415020100ac12111a0c141502010012111415020100d21211d1141502010012111415020100a212111415020100d0121114150201005912111415028f010012111415020100cf1211141502ce010012110b14461502010012111415cd4c02010012110b141502b701001211145b150201
|45=>0x2001812111415b3020100121114081502170012115e141502010012111614150201001211140a1502a301001114150201001812111415a8670100121181141502a30012110f4d141502010012111415cd02010012111415bc020100121151141502016612110b145a1502010012111415020100d3121114aa15020100121114
|46=>0x110b1415020100121114081502010012111415020100131211145a15020100121114491502010012111446150201001211141502b7010012118114150201001211141502010012110c14081502010012111449150201660012110c145a1502010012110b140a1502010012111415a802a30012110f1415020100131211140815
|47=>0x14150201001211511415020100121114156702010012110c141502010012
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x5aa0285011a80794032a0145007a8029400aa0005
|5,0=>0x3f981f0c0f260763039981c0c0da606a303398190c0c2605e302d98160c0aa6052302798130c0926046302198100c07a603a301b980d0c062602e3015980a0c04a6022300f98070c0326
|6,0=>0x15e38ad5c55ce2a7715038a65c524e28b7142389f5c4ece26f713438985c4b4e253712638915c47ce2377118388a5c444e21b710a38835c40ce1ff70fc387c5c3d4e1e370ee38755c39ce1c770e0386e5c364e1ab70d238675c32ce19060c4b8609c2f6e17470b6b8599c2bee15870a8b8529c286e13c709ab84b9c24ee120708cb8449c216e1047
|6,1=>0x77ee3b871d930eadc748e39d71cbb0e458714e38371be38dd986e0c36a61b1b8d71c6aae34e71a3b8d01c672e3327195b8c91c63ae3167187b8c21c602e2fb617a38bb5c5cce2df716c38b45c594e2c37
|7,0=>0x2dc416c20b5105a082cc416420b12e58182bcc15c60ad3056182acc15460a930541829cc14c60a530521828cc14460a14e502827d413ca09d504e2826d4134a099504c2825d412ca0956e4a3824dc124e09170483823dc11ce08d70463822e3915208990444821eb90d6085b0425820ec1056081b040581ff38fda07dd03e681ef40f5a079d03c68
|7,1=>0x3d8b9ea60f43079a73c941e2dcf07077b83ba39db20ec9075c83aa41d320e89073c839a41cb5ce4b071d838ac1c360e0b06fd837ac1bb60dcb06dd836ac1b360d8b06bd835ac1ab60d4b069d834ac1a360d0b067d833ac19b60ccb065d832ac19360c8b063d831ac18b9cc4d061e830b4183dcc0f05ff82fc397c20bd105e082ec417420b9105c08
|7,2=>0x4d4426821331099084c44260212f1097084b4ba58612b3095184a4c2509d275093284954248a1235091284854240a11f508f284754238a11b508d37465c230e1178e8b48456422921139089484464221210f90874843642195d0bb08567427ba11e107f08378417c209e103f08178407c201e0fff07f873f841fa20fc107d883e841f220f8107b88
|7,3=>0x5cf42e5a171d0b8685bf42dddd6df0b6785afc2d61d6a2eb4985a0c2ce61664eb2a859142c6a16250b0a858142bea15e50aea857142b6a15a50aca856142aea1566eaac755242a7215290a8c8542429f5d4eb0a6d8532c297614ab0a4d8522c28f9d46d0a2f7513c287e142f0a1075044280213f109f084f44278213b109d084e442702137109b08
|7,4=>0x175ceba68
|8,0=>0x6e3c36fa5b6b2dac96d1cb66e1b252d8a86c0cb5e61ae30d6986b0c35661aa30d4896a0434de5a5d2d26868f4345dda1d2d06867ecb3d619db0ce4966e4335219972cc3865dc32ca59532ca0964c4323e5910ec7f963bc31ba58cd0c5d962ac3136188b0c3c961a430b5d84b0c1c9609cb02e18070bfb85f94afa657c30bd895e7caf1a577d0bb59
|8,1=>0x7f0cbf661fa12fc887dfcbede1f5f0fa697cecbe561f1b0f8587be4bdce5ed70f6297ad43d465e930f41879c4bcc21e510f1f978bc3c3a5e0d0efe877b43bba1dcd0edd976a4bb321d872ebb87594baaa1d432e98974843a1e5cff0e778737c399e1cbd2e559726c39161c792e339715c388a5c350e128705438065bf12def96f3c377e1baf0dcf8
|8,2=>0x8fec47d623db11e588eec4752639731c478ddcc6ce2358f1a398cd4c6466313118098bc445be62cf116078ac4454222911140889c444be624f111e988b4443de20f10fe987bbc3ba61cb30dc986a44332218910bb98594c2aa214330989847cc21e20fd307598364c18e60b710529824cc106207130308813cc07a602b300c9801cbfea5fe50fea8
|8,3=>0x278913bb99d94ceaa2745139999c84ce2226ff337699b744d9a26bd135599a64cd122679133399954cc8a263513119984c4c0265ef32ee997344b7665a932cc896244af2256912ac895244a722529128b9941c49ee24e7126a99314496a24a33248991fcc8da645d1225990ec4859e41b32058
|9,0=>0xaee4d74e6b9715c47ade456ce6b5715a38acdc564e2b1715838abd4d5ca2ad515628aaccd5462a9315409a9bcd4be2a4f151f8a8bc543e2a0f14ff8a7bc53be29cd34dd9a6ac5332698734bb8a594d2aa294334998a48c5226290314789a384519e68bd34568a26cd116287934339a15c508a683334109a0444ffe67ef13ee99f2ccf7627ab13cc9
|9,1=>0x172f9b934dc766e29370c8b81cdbee2de716eb8b71c5b6e2da716cb8b61c5aee2d6536aa8b5145a6a2d2336898b40c59e62ce316698b304d9622ca116488b20458e22c6116288b104585e6c1d36059afec57d62bdcf5e59
|10,0=>0xbc7c5e1e2eff17778bb7c5d9e2ebf17578ba7c5d1e2e7f17387
|11,0=>0x17977
|_,_=>0
def wAt:=mkWire dB 212 224 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x141544845001043c4c141544845141245055151144845141240841141143c4c1415448451511404410f13050551211400410f1305055121145804110f450551412400410f1305055121145445141245055121145045021043c4c121145049021043c4c1211404410f1305055121142004151144845001044855130f048451511404410f1304845121440841130f04845
|1=>0x80102051111552004151344845110f85807110f4584916010443d14154544d121144c550f13050551211450450f1305055121144c09131544845130f448450b46450454302c9c450a144a84b2711c2851011043c4c141544845111440841130f04845141543c4c0f13050490f13050551511448451412400410f13048451413408410f13050550f1303c4c151245045
|2=>0xf1305055121156c075a11404552700c483d141542007121143c45141549c0327114483d14154200714084544548144544d121155c0747154084d141544455121442d191500450455302c68051413420510801054454801c48211115450550110c3c4c1415448454301c9c45141543045121445445141245055121150c070f1345055161245807110f4505514124585f
|3=>0x155c4504e2700c483d1415451890b0a85449141142051111550845130f84845141550c4b27114483d0110c4c3c1211448450b0a05449141150c0b130f448454312c3c4d1415448454801048211115450a21a02c2c491a02c50491601c443d141550c030c08454451a02c2c494302c4c3d121145055141245804110f450552711c443d120f5140716004443d141540441
|4=>0xa31444090b15450455108454451327830551211454491601c443d14154443d0f130504912114544d121145804110f4485514155a845121542c55141150c071a1542c49130f03c491415448450b124504511238584b08144d8034d124443e5c154504e1211454a11a02c504d121145409000244455001149c03120f4445514154d40460114483e14154443d141552c07
|5=>0x1511448450f13050551511448454312c9c450a1453449110f850555001c45cd000f850552700c50550f13848457000c31690115420044814c20494801c28450a14450494801c28450215448552700c483d1415400410f130505512115b0450c08c50494501d442115114584f121142c550f130504512114483e111543c49141550c041a1544845381443c4e121155c07
|6=>0xf12450554801048211115450557701020091511448451208444550801054451211450a21a02c30451601c443d001445055130f0485512114084d121149c47120f450551a02c304514154680b14134484515654084e1211444094801c544d12114680b1413448451211454451412404410f13050550f12c9c03120f448450c0805445141250c070f1345055121140849
|7=>0x430103c4d141544ce30f13850551211404410f1305055121143c45141543c4c15114484512154680b1413448450213448454312c3021151145049001043c4c141550c0716124443d141542851121544845080105445141250c031a15448454301c302115114443d1415420041511450555f02d3c511513848451660c443d141550c471413448454312c3c4d12114443d
|8=>0xf11450550f1384c5112114680b1413448451812460510801c44550801c2049141344845140149c03120f450551415520041513448454302c68551413448450c8043022151145049496640045021550c5327114483d021043c4c1415448450c1149c030c155f849181442007111544c5a1408454456401d945502138443d14154680b141344845016cc3023151145049
|9=>0x110f45055151244c511211458071611c2c5514115fc077a1159c55421244c3e121150c47161242051080100849151144845801243022151145049110f45055081444455001043c4c1415448451415520070a11448552700c48450a14448550111454451412404551a4fc4c511211448211612c2051121142004141545445121152007151344845110045055150045045
|10=>0x1211430210801c54451211420041115450557e12460510801c44550801058490814444554814d2004121145449141145055121150c040c08454452711c9c45120f50c032711428513501d8045120f848452700c3055121450c0b0f13450551601c443d141550c031612420514311c68550b12450455302c6805141344845430103c4d1415448451413448450a0b84451
|11=>0xc01c4851080105445141245804110f45055110f4005514154523e0113448454801c544d121144a350802c4455130f448451415448450b15450451a02c30451412420071115450558b156044b0114520071513448454802c544d1211420041115450550c0145049121142c2a15124003e111445055000f80055141544c3c1211450550f1305049141544845141545445
|12=>0x141549c03120f450552711c28511215444011115450551208444551415568451412404550b46c54011411430571412448450b46454011411430231511450490801c5445141252004151344845010f8485114154544914134484515654084e1211428450a144485515114044501154284502154485512144483e141545045000f450551601c443d14154443d141564455
|13=>0x141543c4514154484513144484514154504e1511448452712c28511215420040200454450c0845445141242007081444455151345045121149c4b0c154485112114280b12154540111004505514664440114154200408144445597115305702124504e12114300714124484514488544d12114544d1412448454f024544e12114219e02004544548010544d12114443d
|14=>0x13154544e121153449110f8505508024544512114504d1501448452711c483d141542c570011450451611c20511115520070a11448554814c2049151158045120f8505515124043e14154544901144505514114443e141544855120f850551413848454802c2845121559c456715400091211444091215524010011408550200420071511578570c0144851130f84845
|15=>0xb00c504515114540512114504d1511448459211430571214430550c11450496a11c2809121568c530112448452701c483d141545807110f4505516010443d14154084e121146805141344845141145449121149c030a144485512088445514154553102124484511588003d141545849110f4505558114003d141542051111540045154c530450212678554c11c0849
|16=>0x1415448452711c305512144504d14138484502134484502014084512114443e1415420041511400515e11430051412594550213848454814c2845121545049141544845120b844511415455320212448450f124045114155e8456715400091512408050215468070c11450494c08c445502124043d1214450550c08854451412458470b1545045000f84455141569855
|17=>0x130f850551a02c504d121144c550213448450c08c50490801c5445141243c03000f4505515124043d14154443d14154003e141549c4b0c15448511412454451211428091215420041511450495115c0051001156449010f8505514aa428471215444015115400512700c483d141559809001145445000f450550801c54451412450550b1245045001442007111545045
|18=>0x801c44551a02c504d12114584b110f45055021544409121544ac10b01c504515114443e14154003e0014450550a11428091215520070a11448552700c3055121443005141244845770112445021545803110f45055110f85055080105445121140855671140801120844455141544451120f8505501924305712144321712144044502004004502154544d021244845
|19=>0x20040805010053c5115138484560014483e1415448091502448455800d4455001443c4c14154484500024445500115e8474900408554815c20491511420490814444557701d24450215468051413448450f0044401141556c075a11404550b00444511415468551413448450f13850551211456cd6711c080101134504d1211448458111c04512701c483d141546051
|20=>0x1115448450b15c50450014444550011408491511448450a0b844511215444016715c00090800c445514156a4550b12c50454815c28451215525990011408551211446a201026e8510113848451411454051211450551511448450f134505512114557114138484501138504d1211544211511400510c1144851141543d9b110045055141245405121142e8e011245045
|21=>0x1115430221511458490814444551411450051211450451100450551a02c2c49141145449110f8505515134504d1211468530b12450450b0a054491411408550213448452701c483d141542d191500450452711c483d1415468571413448459c0042c57141143c4511004505514124443e14154504e1211400451511408550c0143045141243047141240455c01242053
|22=>0x121145449121140455021259c55000240805021542c5514114483e141559c0502004540500144540501004080115114544d12114280912154080501004043e14154045114154205111154000901114285312154504d121154445001444c511211450551a1542c491411454451412404550c0805445141257007141384845011145049011543215121440445181442007
|23=>0x10042c49141145045121142003151145049121143005141240845121144aa201024500512114440114154544501154544512114085512154084502154044501154205311156dc4701005240502155244502154003d14154044914114084e12114504d12114043d14154544502154544500145300702124003e141542c0114114540101004443e14154045101114504e
|24=>0x1144284712154084912114084d121154457001443045141242807121554447001468c53011259c0702004043e14154044d1211402a2010268c470112454011411530050212404011411568450115400090011420071511530450212454051211408450015446a101024200415114280b121540805121152401021543007141242805121543057121468c57011240add
|25=>0x1440801141245045151144845011540855001540401011445445141240045021545049011545449141144805010245055121142007151159c4702004200415114300514124443d14154480512154200715114000901024044901144443e1415530050212446a2010240051001145405141160403
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x2100000000008800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000
|6,0=>0x74800001b20351000000000000000000000000000000000000000000305056a000000000000000000000000000000000013a000000000000121800003ea000000000000000000000001b4000000000000000000000000000000000000000ba00000000000009a0000000003d00618000
|6,1=>0x5840000000000000000a6a148400005110000000026284840000000000000000000111000004310000000000000000000000000003e5000000000000000000000000000000
|7,0=>0x1ee83d480000f141dc63acc73a00001c8600007020dd30000368c6c88d541a4634086620c8418a630505ea0ba316e600005a90b3215e82b0c0000a9314c628cc0000a0313a6268c4b20924000023cc00008d21128218c41208110fa81e8c3b987340e24000000006d40d28198c00006420c4417cc00005c3
|7,1=>0x30a80000c0a17e300005e90bb997432e085b88b6116932cc658ccb1095e42b6655d0000154300000000000151329c652cca50947328860000a0993e300004f089d1137326684c84979800025a44a50000127224a4488c8f211c22326458c899800021e842d000010742068000000010121fc600007d98000
|7,2=>0x43468591099a0f44186824d039204340087f4cfca1f5400000000f991f033d887a880001e643c6677d00001dd2000000000001d943ac6000000000003a660000e89000039c67290e399c4338260000df19ba436c86d08d899ae300006a90d399a523446680800000003388664ccaa192331e6630cc498000
|7,3=>0x5786ae115a22b0455a6aa51531aa335406a74c00029940000a58c00029335206a31144228440000a08940127e24f6600013ba27434e269b8d35200004cc8000132126224bc800012d200004ac89491279a4c3496291d1221a40447c48ecc000000047068d1119100004604000000022c44508891110221d3
|7,4=>0x16122bf3
|8,0=>0x6fe6df0dbc9b7636e66dc0db69b6a36ce6d90db09b5e36b66d60daa9b5326a06d34da51b4736886d04d9f933c36726cd8d999b30365a6ca8d939b2436426c78d8d9b18362a6c48d879b0c36126c18d819b0125fc6becd7c1af535e46bbcd761ae935cc6b8cd701add35b46b5cd6a1ad1359e4b30d649ac63
|8,1=>0x87670e0e1b1433386250b8e159c28384a7088e0f9c1c38327058e099c10381a7028e039c0438026ff8dfd9bf837ea6fc8df79bec37d26f98df19be127bc6f6cdec1bd537a46f3cde61bc9378c6f0cde01bbd37746edcdda1bb1375c6eacdd41ba537446e7cdce1b99372c6e509c89b8e37166e20dc29b823
|8,2=>0x9e873c4e771ceb39d07394e711cdf39b87364e6b1cd339a07334e651cc739887304e5f1cbb397072d4e591caf395872a4e531ca339407274e4d1c98292a7248e479c8c39127218e419c8038fc51ece3c1c7628e671c0e369c6b28d25198e319c6128bc716ce2c1c5538a4713ce26944a388e7110e209c3e3
|8,3=>0x2ca1d913b1c762cec41d853b0475fcebe957a3aee75d0eb89d6e3ad675a0eb29d623abe7570eac9d563aa67540ea69d4b2a907514ea11d3f3a7874e4e9b1d333a6074b4e951d273a487484e8f1d1b3a307454e891d0f3a187424e831d033a0073f4e7d1cf73
|9,0=>0xc2a584cb08960f2c1a582cb0496072c0a580cb0095ff2bfa57ecafc95f72bea57ccaf895ef2bda57acaf495e72bca578caf095df2bba576caec95d72baa574cae895cf2b9a572cae495c72b8a570cae095bf2b7a56ecadc95b72b6a56ccad895af2b5a56acad495a72b4a568cad0959f2b3a566cacc95972
|9,1=>0x6672cca598cb30965f2cba596cb2c96572caa594cb28964f2c9a592cb2496472c8a590cb20963f2c7a58ecb1c96372c6a58ccb18962f2c5a58acb1496272c4a588cb10961f2c3a586cb0c96172
|10,0=>0xce639c87388e701cde39b87368e6c1cd639a873488000
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 15
def pmP:Nat→Nat
|0=>0x840000000000008000000000000066000000000000600000000000004e000000000000480000000000004600000000000040000000000000320000000000002e0000000000002c0000000000002800000000000026000000000000240000000000002200000000000021000000000000200000000000001e000000000000160000000000001400000000000012000000000000100000000000000e0000000000000c0000000000000a00000000000008000000000000060000000000000500000000000004000000000000020000000000000100000000000000
|1=>0x69e000000000006800000000000044e0000000000044400000000000420000000000004000000000000039e0000000000030200000000000300000000000002c2000000000002be000000000002a00000000000029e00000000000296000000000002880000000000028600000000000284000000000002800000000000021f0000000000021e000000000002060000000000020500000000000204000000000002000000000000015c00000000000144000000000001080000000000010600000000000102000000000000980000000000009600000000000090
|2=>0x52fe000000000052bf000000000051bf000000000047ff000000000046ff000000000046bf000000000042ff000000000042bf0000000000423d000000000040bf000000000040be000000000040800000000000402f00000000004020000000000040080000000000400400000000004000000000000016ff000000000016e0000000000016c4000000000016be0000000000131c000000000013160000000000130e0000000000129e00000000001204000000000010100000000000100200000000000800000000000007bf000000000006de000000000006c0
|3=>0x842ff00000000080153000000000800410000000004c000000000000242bf00000000010200000000000100410000000000d23f0000000000c7bf0000000000c6fe0000000000c04c00000000009086000000000090800000000000901e0000000000900d0000000000900700000000009004000000000087bf0000000000845a0000000000838000000000008090000000000080740000000000806c000000000080560000000000804e0000000000804400000000006000000000000057be000000000056ff000000000056bf000000000053bf000000000052ff
|4=>0x21242bf000000020f42df000000020742bf000000020442bf000000020062bf000000010060140000000100401400000000c1001000000000c0c28e00000000c042bf00000000c0001700000000c000000000000088477f0000000088437f0000000088427f0000000088423f00000000624287000000004242bf000000004046bf000000004012ae0000000040128e000000004000880000000040001e0000000040001700000000400000000000002242bf00000000200001000000001f42d5000000001742950000000013429d000000001042bf0000000008477f
|5=>0x600000040000004000844c000000400042bf000000400042bd000000400002bf000000260042bf0000002400c04c00000024000004000000220042bf0000002000c4ff000000200053bf0000002000139a0000002000130e00000020000000000000100000000000000f0402400000000e0042bf0000000b0442bc0000000a0042fd0000000a0042bf0000000804e01400000008040004000000050040040000000500201000000005002004000000040846ff000000040842ff000000040800410000000400c054000000040046ff000000040042ff000000021a42bf
|6=>0x18028000200000100c04656000001004046bf0000010040463f00000100400736000001004002560000010023429700000100210380000001000b46df000001000a07df00000100080001000001000346bf000001000307bf000001000242bf0000010001015500000100000001000000a000039a0000008020039f0000008000c3be000000800083bf00000080008282000000800053bf000000800051bf000000800043bf0000008000437f0000008000014e0000008000000800000080000000000000610084dc0000006000804e000000600042bf0000006000001e
|7=>0x100000601400001000000280000010000000960000088008435f000008040842ff000008020242bf000008020046bf0000080042463f0000080040802c000008000842760000080000c0bf000008000090ac0000080000802c000008000056bf000008000046bf0000080000463f0000080000437f0000080000429f00000800000280000008000000a000000800000022000008000000000000040904400c000004060446ff000004060446fd0000040300c6bd0000040204c29e00000400040004000003000a42bf000003000800010000020009000400000180400316
|8=>0x300000000200002880082463f0002880080002a0002800080002c000200000052bf0001c0800046bf0001c0800007bf0001c0000006bb000148001042bf000148000042bf00010040000222000100000046bf000100000000320000c8008246bf0000980080c6ae000080800042bf000080000002200000480200c6bf0000480002423f000048000046bf000048000042bf000040000056bf000040000046bf00004000000042000020020242bf0000140000c2bd0000100804e2bf0000100204c2bf0000100100c0580000100000c6bf0000100000c2bf00001000008054
|9=>0x2800000042bf0023008000433f0020c0000246bf002040001242bf002004022242bf002000061a42ff002000002247bf002000001b42dd001000023642bf001000020242bf0010000037429d000802000343b700080200010115000801006242bf0008010022029f0008010020001600080100200015000801002000130008000060028f000800004002a70008000040028f0008000003029f000800000242bf000800000042f7000800000042bf000400c0000202000400000016bb000360000042bf0003000000102000030000000220000300000000320003000000002a
|10=>0x80000200042bf0800000f0042fd080000090042bf080000060c46ff068040000042bf062140000042bf060140000042b9060048000646bf0600180004c6ae02a040001242bf011000060a42bf01100004080004011000000000150100040011001500aa00000042bf008660000042ff008660000042bf008448000042bf008420001242bf0080c0800242bf008068020242bf008060000042bf008048000246bf0080200002429f0080000002429f004100c00002200041000000023200408080000208002802000143bf002800000b02df002800000a42ff002800000142bf
|11=>0x260040000042bf220144000046bd220140000046bf20844c000042bf1a00600a0042bf1a00200a0042bf180568020046bf104080000052bf104080000010321002780200c6bf1001c8000056bf100180000016bb100150000042bf100140800047bf1000580200c6bf100050000042bf100050000003bb100048020046bf100010000042bf1000080000002e0e8260000642bf082300000042ff082200000042bf082000001142bf082000001042bf080300000040bf080300000000fd080220080042bf0800400a0042bf080004090042bf080004020442bf080004010042bf
|12=>0xc00140800047bf480140100042bf480040020046bf42a000001242bf400048122046bf
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x80000010000000000000000000000000000000000000000000000000000000000600
|6,0=>0x700000000004060003a000006003000000000000180018000000000000000030000000000000000000000000000060003818000000000000000000000000021190000000000000000000001600000003c0016000000000000000f0000000000000000000000006000000006000002c6e00
|7,0=>0x1580068b0001040601151cc060201879d45107824000300000000101014746b14000520300004020203ac40a002781c0065030081003018141e000fa10000b0a2c80001030001e000281928080180c56000180010020011588080108ca808018401a020780006d03d314003b03070000f03018223f00078000326819fc180e8a04c2e3e00000081c94000037100c0003
|7,1=>0x1706c5c2e019b004030180c000b00018001e01814a43e0000c061a2300048010180d780002800021c168000e000604c0603219609ed81280c00000781ccc0001800001203940800f0182450ed030180c0f0b018663559000f20506391280503050000a0021c00bb140000000010000c00428200c030180044552b8087025438100aaa1011000002803ca20307818de00
|7,2=>0x8e0f
|8,0=>0x72d14f7e4516216b90692d9aad7a292af1357c70b2e04ab22ca48310c9376f78bbd26b8a31b8e05f55b4862e16b26958c346b9e447267368d40946db222db4bafd3353734d6910c2d09c90c03a1606cfc33a2e0cd99a249591f9299cd0b7501600c780735ced0864139be62772f82a495d3f6a103464bde0d586161207e84be4b22f63175ed10349d52377012211e33
|8,1=>0xc8cb0b982280d93434044c8cb4d928915b3e02e979b8cb4296434512bf4f51646596650abcc8414a19100aad6613202d969850f3e929a521b6c5d66f1574acb5389b2f87b07a24c69533178393f158c3b21a562d39612de963fdea70ba160f68a5ed48da897942d06a303175523c0ecb63ae24c1d09ca80cca9ef01981c6a92e7592a8e42
|9,0=>0x634ec6cef162d3eecea5ba972e34bab459b97bad5027d4c80d76c52930c3a7f709e526f35bb9ce6f584a85a1f562b34eef85880df66f0abb17add1665321425ebc582ff1a6a5a94504b0d3cff83b5ba26572afad63d5ca0d8d1d43c03769cc1815926f5863a5b0351924e96d058b3e22480a6c04c343
|10,0=>0x93a04bcc853162d29c4360a7a53
|11,0=>0x58
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 56 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_222 9 roots_222 ops++addP pm 1 dom_207 9 roots_207 ops++addP pm 2 dom_215 9 roots_215 ops++addP pm 3 dom_159 9 roots_159 ops++addP pm 4 dom_95 9 roots_95 ops++addP pm 5 dom_221 9 roots_221 ops++addP pm 6 dom_85 5 roots_85 ops++addP pm 7 dom_158 8 roots_158 ops++addP pm 8 dom_79 6 roots_79 ops++addP pm 9 dom_203 8 roots_203 ops++addP pm 10 dzo_85_2 5 roots_85 ops++addP pm 11 dom_201 5 roots_201 ops++addP pm 12 dom_143 6 roots_143 ops++addP pm 13 dom_147 4 roots_147 ops++addP pm 14 dom_219 9 roots_219 ops++addP pm 15 dom_151 6 roots_151 ops++addP pm 16 dom_94 7 roots_94 ops++addP pm 17 dzo_212_2 5 roots_212 ops++addP pm 18 dom_211 7 roots_211 ops++addP pm 19 dom_84 4 roots_84 ops++addP pm 20 dom_218 6 roots_218 ops++addP pm 21 dom_214 7 roots_214 ops++addP pm 22 dom_199 5 roots_199 ops++addP pm 23 dom_197 4 roots_197 ops++addP pm 24 dom_27 4 roots_27 ops++addP pm 25 dzo_209_2 5 roots_209 ops++addP pm 26 dom_81 4 roots_81 ops++addP pm 27 dom_155 6 roots_155 ops++addP pm 28 dom_212 5 roots_212 ops++addP pm 29 dom_31 5 roots_31 ops++addP pm 30 dom_29 4 roots_29 ops++addP pm 31 dom_77 5 roots_77 ops++addP pm 32 dom_198 4 roots_198 ops++addP pm 33 dom_78 4 roots_78 ops++addP pm 34 dom_91 7 roots_91 ops++addP pm 35 dzo_213_2 6 roots_213 ops++addP pm 36 dom_149 5 roots_149 ops++addP pm 37 dzo_217_2 6 roots_217 ops++addP pm 38 dzo_221_2 7 roots_221 ops++addP pm 39 dom_205 6 roots_205 ops++addP pm 40 dzo_93_2 6 roots_93 ops++addP pm 41 dom_213 7 roots_213 ops++addP pm 42 dom_93 7 roots_93 ops++addP pm 43 dom_206 6 roots_206 ops++addP pm 44 dom_210 4 roots_210 ops++addP pm 45 dzo_92_2 5 roots_92 ops++addP pm 46 dom_141 4 roots_141 ops++addP pm 47 dzo_220_2 6 roots_220 ops++addP pm 48 dom_90 4 roots_90 ops++addP pm 49 dom_217 6 roots_217 ops++addP pm 50 dom_209 5 roots_209 ops++addP pm 51 dzo_89_2 5 roots_89 ops++addP pm 52 dom_157 6 roots_157 ops++addP pm 53 dom_89 5 roots_89 ops++addP pm 54 dom_220 6 roots_220 ops++addP pm 55 dom_92 5 roots_92 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_223 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45|h46|h47|h48|h49|h50|h51|h52|h53|h54|h55
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_207 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_221 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_79 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_85_2_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_201 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_143 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_212_2_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_197 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_zo_209_2_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_212 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_29 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_198 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_78 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_zo_213_2_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_149 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_zo_217_2_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_zo_221_2_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_zo_93_2_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h45;exact cpcs (by decide +kernel) lowS_zo_92_2_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h46;exact cpcs (by decide +kernel) lowS_141 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h47;exact cpcs (by decide +kernel) lowS_zo_220_2_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h48;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h49;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h50;exact cpcs (by decide +kernel) lowS_209 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h51;exact cpcs (by decide +kernel) lowS_zo_89_2_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h52;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h53;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h54;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h55;exact cpcs (by decide +kernel) lowS_92 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_222 9 s (0,roots_222.map (·&&&dom_222)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_223 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_222 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_223==dom_223)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_223 gM v ys):RunD true dom_223 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_223 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 10 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 35 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 35 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 102 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 102 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 256 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_256 : ∀ i, 256 ≤ i → i < 258 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 2 256 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 258 → Z 7 i = true := (range_split z7_0 (range_split z7_128 z7_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 246 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 118 128 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 246 → Z 8 i = true := (range_split z8_0 z8_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 105 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 105 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 12 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_223 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
  · exact z11 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 6 6=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤11) (h:RunD true dom_223 gM s xsM):False:=by
  have hmin:6≤s:=by have hl:=run_len h;change 7≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_223 roots_223 goal_223 12:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_223
theorem lowS_223:Lower true dom_223 roots_223 goal_223 12:=S_223.noCircuit
theorem lowS_239:Lower true dom_239 roots_239 goal_239 12:=lower_slice_b [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,64,68)] (by decide +kernel) lowS_235
theorem lowS_251:Lower true dom_251 roots_251 goal_251 12:=lower_slice_b [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000,1,17)] (by decide +kernel) lowS_235
def dzo_249_4:=0x3030303030303030303030303030303030303030303030303030303030303030
def gzo_249_4:=0x3030303030303030303030303030303030303030303030303030302030302000
def gsh_249_4:=0x303030303030303030303030303030303030303030303030303030203030200
theorem lowS_zo_249_4_41:Lower true dzo_249_4 roots_249 gzo_249_4 7:=lower_iso_b (d1:=dom_249) (r1:=roots_249) (T1:=gsh_249_4) [(dom_249,4)] (by decide +kernel) (lower_slice_b (T:=gsh_249_4) [(0x303000003030000030300000303000003030000030300000303000003030000,0,16),(0x303030303030303000000000000000003030303030303030000000000000000,0,64),(0x303030303030303030303030303030300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_41)
def dzo_185_4:=0x303030303030303000000000000000003030303030303030
def gzo_185_4:=0x303030303030303000000000000000003030302030302000
def gsh_185_4:=0x30303030303030300000000000000000303030203030200
theorem lowS_zo_185_4_41:Lower true dzo_185_4 roots_185 gzo_185_4 6:=lower_iso_b (d1:=dom_185) (r1:=roots_185) (T1:=gsh_185_4) [(dom_185,4)] (by decide +kernel) (lower_slice_b (T:=gsh_185_4) [(0x30300000303000000000000000000000303000003030000,0,16),(0x30303030303030300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_41)
def dzo_233_4:=0x303000003030000030300000303000003030000030300000303000003030
def gzo_233_4:=0x303000003030000030300000303000003030000030300000302000002000
def gsh_233_4:=0x30300000303000003030000030300000303000003030000030200000200
theorem lowS_zo_233_4_41:Lower true dzo_233_4 roots_233 gzo_233_4 6:=lower_iso_b (d1:=dom_233) (r1:=roots_233) (T1:=gsh_233_4) [(dom_233,4)] (by decide +kernel) (lower_slice_b (T:=gsh_233_4) [(0x30300000303000000000000000000000303000003030000000000000000,0,64),(0x30300000303000003030000030300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_41)
def dzo_169_4:=0x30300000303000000000000000000000303000003030
def gzo_169_4:=0x30300000303000000000000000000000302000002000
def gsh_169_4:=0x3030000030300000000000000000000030200000200
theorem lowS_zo_169_4_41:Lower true dzo_169_4 roots_169 gzo_169_4 5:=lower_iso_b (d1:=dom_169) (r1:=roots_169) (T1:=gsh_169_4) [(dom_169,4)] (by decide +kernel) (lower_slice_b (T:=gsh_169_4) [(0x3030000030300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_41)
namespace S_253
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(4,20),(4,68),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(8,9),(8,40),(8,72),(8,136),(12,13),(12,28),(12,44),(12,76),(12,140),(16,17),(16,20),(16,80),(16,144),(24,25),(24,28),(24,56),(24,88),(24,152),(32,33),(32,40),(32,96),(32,160),(36,37),(36,44),(36,52),(36,100),(36,164),(48,49),(48,52),(48,56),(48,112),(48,176),(64,65),(64,68),(64,72),(64,80),(64,96),(128,132),(128,136),(128,144),(128,160),(129,133),(129,137),(129,145),(129,161),(129,193),(192,193),(192,196),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffffffffffffff
def xsM:=roots_253.map (·&&&dom_253)
def gM:=goal_253&&&dom_253
def NN:Nat→Nat
|5=>6
|6=>46
|7=>107
|8=>128
|9=>61
|10=>10
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0x7eccf5c06a3bbc40f67e0f2f40ce22
|6,0=>0xf149accbbccc93cc7dc2c046db8badb5d93b3b94b22c5a098f9edb495e368560c819f480790745f1742236722863a48635805b0dd574715570d546fc519b2484db4589d43b214362b4198a3e8bc3ca9f3be7730fd028cef251942003f1dbc31d1f11920914f8d12cae109200c78404c1604991
|7,0=>0xfa877f36c9f305ef03e2ee9fde4648e3321e0bebdbe27d7c22d4425cf5cacc579cc3dfc2271bf439b8970b5e5db4fbdb12eba246c9f1ee9ee319bc969acc797d92979b5942c4938db921f0916868f90a8f6e4897f288d8288ce6873e3854367d4027bc817b4937919e75649721d870c2f6eef86b8fc696076753d639e15f1d65ef415ee005c0025bfd859edc5861e569944b4ff492274865947f7446db0466bc439cc41cc73947039443389fd381d43670834e213475b32b2c317d22ec972d1462ce182a98c2869726fdd25a2e258df2556c253d025030219592122f1fdb11eefc1eda71e95d1e0b11c4e31c1a6189a513aea1352b11798103b10f8630a9300863b04e3a02bcf01ad900429
|8,0=>0xfe5a2fe028f9264f7d86f3aa8f17b3ec92fea63ae723fe0b94dc876d7acdd1298d0fb0cfd57ca235c7371c6e03c698dbf32bb90d3b5459b2385b21b2b1281af9d8af747ad6e3acb21ac771aac59a75d0a28739ffef9d15c9b09f98c06988d0965db95e5a8f8e18f7e28f6158ea158c72082c3480e1e7c23d7ad1a794157542e74e99747ba729a472357713c0707cb6e4d66ace56ac2e6a6b567359641ed60f9e601ab5f1045e5275cec45a33258ae85885455e3a54f8154b6653b45509314c1704c0d44ac8c46e7d4441a4370142e6b42d1c429a9419be411423dfd7399203725f36a6635661340fe32d012fbbd2f7982d65d2c3442bf1b2bab62b9ba29e0c25452241121f30b1ef161d6901c8a11b06b1a4d9189b916e201507014b2b139f2128620cf1e0be3a0b8840a0a60a0300958f07a2d06477052a7027af01c4f00da6
|9,0=>0xfd1acee3edede17ea7c6e4532ccb84caaf3c87fec2cc9b3297af137af120a55359a16d905498f7948ed3d8e7fd88da6818b47b964766dc723be66fce66e6166af8642ba6361d63238617375c4d5594e75918855a7a53ea34be4f4bc384a3414935842aa64244c3c7483b1b03aacd3126629c26277cc1f08c1c19b1ade71abe0185d716568131de10ee50f65c0ebf00b0900af76084ec00776
|10,0=>0xc6eb183f357a07a66f6a47063460ee401573343a206100b254
|11,0=>0x1e31b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xc0c00000c0c0c0c0c0c00000c0c0c0c0c0c00000c0c0c0c0c0c00000c0c0c03333333333330000333333333333000033333333333300003333333333330000cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc03333000033330000333300003333000033330000333300003333000033330000cccccccccccccccc0000000000000000cccccccccccccccc0000000000000003333333333333333333333333333333300000000000000000000000000000000cccccccccccccc00cccccccccccccc00cccccccccccccc00cccccccccccccc03333333333333333333333333333333333333333333333333333333300000000cccccccccccccccccccc0000cccc0000cccccccccccccccccccc0000cccc0003333333333333333333333333333333333333333333333333300330033003300cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000003333330033333300333333003333330033333300333333003333330033333300cccccccccccccccccccccccccccc0000cccccccccccccccccc00cc00cc000003030303030303030303030303030303030303030303030303030303030303030888888888888888888888888888888888888888888888888888888888888888b333333333333333333333333333333333333333333333330000000000000000
|0,1=>0xcccc000000000000cccc000000000000cccc000000000000cc00000000033333300000000003333330000000000333333000000000033333300cccccccccccccccccccccccccccc0000cccccccccccccccccccccccccccc0000303030303030303030303030303030303030303030303030303030303030000cccccccccccccccc0000000000000000cccccccccccccccc00000000cccccc03300333333003333330033333300333333003333330033333300333333003300cccc0000cccccccccccc0000cccccccccccc0000cccccccccccc0000cccccc0333333333333333333333333333333333333333333333333333300003333000000cc00cc00cc00cc00cc00cc0000000000cc00cc00cc00cc00cc00cc000000033333333333333333333333333003300333333333333333333333333330033000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c00000c0c000333333333333333333003300330033003333333333333333330033003300330000000000cccccccc00000000cccccccc00000000cccccccc00000000cc00cc03333330033333300333333003333330033333300333333003333330000000000cccccccccccc0000cccccccccccc0000cccccccccccc0000cc00cc00cc000003333333333333333333333330000000033333333333333333333333300000000
|0,2=>0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccccccccc00000333300003333000033330000333300003333000033330000333300003300cccccccccccccccccc00cc00cc00cc00cccccccccccccccccccccccccccccc00000000000000000333333333333333300000000000000003333333333333300cccccccccccccccccccccccccccccc00cccccccccccccccccccccccccccccc0003300330032003200330033003200320033003300320032003300330032003200000000ccc8ccc800000000ccc8ccc800000000ccc8ccc800000000ccc8cccb3333333333333333333333333333333333333333333333333333300333333000c0c000c0c0c000c0c0c000c0c0c000c0c0c000c0c0c000c0c0c000c0c0c0000000000033333333000000003333333300000000333333330000000033333300000000000000000000000000000000000000000000000000cccccccccccc0003333333333333333000000000000000033333333333333333333330033333300cccccccccc00cc00cccccccccc00cc00cccccccccc00cc00cccccccccc00cc003030303030303030303030303030303030303030303030303030300030303004444444444444444444444444444440044444444444444444444444444444403333333333333333333333003333330033333333333333333333330000000000
|0,3=>0xccccccccccccccccccccccccc0c0c0c0ccccccccccccccccccccccccc0c0c0c333333333030303033333333303030303333333330303030333333333030303000cc00cc00cc00cc00cc00cc00c000c000cc00cc00cc00cc00cc00cc00c000c00330033003300330033003300330033003300330033003300330033000000000000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cc000000cc03333333333303330333333333330333033333333333033303333333333303330ccccccccccccccccccccccccccccccccccccccccccccccccc0c0c0c0c0c0c0c0000000033333333000000003030303000000000333333330000000030303030cc00cc00cccccccccc00cc00ccc0ccc0cc00cc00cccccccccc00cc00ccc0ccc3333333333333333333333003333330033333333333333333333330033333300444444444444444444444444444444444444444444444444444444444444440333333333333333330303030303030303333333333333333303030303030303000cc00cc00cc008800cc00cc00cc008800cc00cc00cc008800cc00cc00cc00880000000333333220000000033333322000000003333332200000000333333220c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c03333333333333333000000000000000033333333333333333333333333333300
|0,4=>0xcccccc00cccccc0000000000000000000000000000000000000000000000000003300330033000000000000cccccccc00000000cc00cc0000000000cccccccc00000000cc00cc03333000033333333333300003333330033330000333333333333000033333300ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc3333333322222222333333332222222233333333222222223333333322222222cc88cc88cc88cc88cc88cc88cc88cc88cc88cc88cc88cc88cc88cc88cc88cc8b33333333333333333333333333033303333333333333333333333333330333000000000cccccccc00000000cccccc0000000000cccccccc00000000cccccc03333333333333333333333333333333333333333333333333333333333003300cccccccccccccc88cccccccccccccc88cccccccccccccc88cccccccccccccc8b333333333223322333333333322332233333333332233223333333333223322ccccccccccc8ccc8ccccccccccc8ccc8ccccccccccc8ccc8ccccccccccc8cccb333222233332222333322223333222233332222333322223333222233332222cccccc88cccccc88cccccc88cccccc88cccccc88cccccc88cccccc88cccccc88033003300300030003300330030003000330033003000300033003300300030
|0,5=>0xccccccccccccccccccc0ccc0ccc0ccc0ccccccccccccccccccc0ccc0ccc0ccc00000000333333330000000033303330000000003333333300000000333033300000000000cc00cc0000000000c000c00000000000cc00cc0000000000c000c3333333333333333333333333333333333333333333333333333333333333300cccccccccccc8888cccccccccccc8888cccccccccccc8888cccccccccccc888b33333333333333333333333333333333333333333333333000000003333330000000000ccc0ccc000000000ccc0ccc000000000ccc0ccc000000000ccc0ccc3333333333333333000000003330333033333333333333330000000033303330c0ccc0ccc0ccc0ccc0ccc0ccc0c0c0c0c0ccc0ccc0ccc0ccc0ccc0ccc0c0c0c3333333333333333000000000000000033333333333333333333333333330000cccc00cccccc00cccccc00cccccc00cccccc00cccccc00cccccc00cccccc0003333333333333333000000003333330033333333333333330000000033333300cccccccc0000cccccccccccc0000cccccccccccc0000cccccccccccc0000cc00000000000000000000000000000000000000000000000003333333333333300cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc0000033003300330000003300330033000000330033003300000033003300330000
|0,6=>0xcccccccccccc00000000000000000000cccccccccccc000303330333032303230333033303230323033303330323032303330333032303200cc008800cc008800cc008800cc008800cc008800cc008800cc008800cc008b333333300330022333333330033002233333333003300223333333300330022444444004444440044444400444444004444440044444400444444004444440000000000000000033333333333333000000000000000000333333333333330000000000c8c8c8c800000000c8c8c8c800000000c8c8c8c800000000c8c8c8cb232323232323232323232323232323232323232323232323232323232323232cc00cc00ccc8ccc8cc00cc00ccc8ccc8cc00cc00ccc8ccc8cc00cc00ccc8ccc8000000011111100000000001111110000000000111111000000000011111100cccccccccccccccc00cc00cc00c000c0cccccccccccccccc00cc00cc00c000c0000000033223322000000003322332200000000332233220000000033223322444444444444000044444444444400004444444444440000444444444444000331133113311330033113311331133003311331133113300331133113311330000cc00cc0088008800cc00cc0088008800cc00cc0088008800cc00cc00880088000000033332222000000003333222200000000333322220000000033332222
|0,7=>0x44404440444044404440444044404440444044404440444044404440444044400000000000000003333333330303030000000000000000033333333303030300000000000000000cccccc00cccccc000000000000000000cccccc00cccccc00303030302020202030303030202020203030303020202020303030302020202444444444444440044444444444444004444444444444400444444444444440000000000032003200000000003200320000000000320032000000000032003200c800c800c800c800c800c800c800c800c800c800c800c800c800c800c800ca222222233323332222222223332333222222222333233322222222233323332ccc8ccc8ccc8ccc8ccc8ccc8ccc8ccc8ccc8ccc8ccc8ccc8ccc8ccc8ccc8cccb300330033003300333333333333330033003300330033003333333333333300000000000000000000cc00cc00cc0000000000000000000000cc00cc00cc00003030303030303030300030003000300030303030303030303000300030003000000000000cc00880000000000cc00880000000000cc00880000000000cc008a2222222333333222222222233333322222222223333332222222222333333220000cccc0000cccc0000cc000000cc000000cccc0000cccc0000cc000000cc03333003333330022333300333333002233330033333300223333003333330022
|0,8=>0x333300002222000033330000222200003333000022220000333300002222
|_,_=>0
def sP:Nat→Nat
|0=>0x5070d02011f0005070602011e001d0c0d020113000e05070d011c000504110201000b050c0d02011b0005070d1102010005071a0d02010010190c0d0201000504180201170016050c0d01150009080c140201000e070d020113000512070602010e120602010b100411020100100c0d010f00090807060201050403020100
|1=>0x2010b05120c140201000c02012a290b0a0e10280d02010005181402011e00050c0d0127000b09050706020100100c0d02012600250504140201000e05240d020100050c0d011517000e08040602010b2308070c0602010e0807060d02011d05040602010010050c0d012200080c0d1102010b1d050c0d02210005200c0d0201
|2=>0x20100100504180d020100050c370d0201000805360c0d020100050c0d0235000b23080c063402010c020133320b0a050c0d0131000b100c0d02011f0030050c0d0201002f100c0d02010005070d02012e000e10040602010023050c140115002d050c0d020100090518140201002c050c0d0201002b050c0d02210009080c06
|3=>0xb0a05040c0201330b0a050c0d340201130023080c0602010b0e100c060d02010043050c02012a0b0a0e410d0201320b0a050c0d34014000050c0d02013d0023050c063402010009050c0d02210b0a050c1402013c0005070d02013b000910040c0d0201003a100c1402010a090e100c0d02010009100c0d02010023050c1439
|4=>0x201002b050c0d020100090e100c1402010a050c140d01150009100c1402010a05040c02013c000b050c4b0d01380005040c0d0122000b05070c0d02013c00090e4a0c49020b0a094a0c49020b0a2b1d050c0d020100100c0d0201400048050c0d020100050c0d02014700050c0d0122000b050c0d02012e000b450c0d020132
|5=>0x70c0d020100100c0d020150001d050c0d02210b0a51050c0d011c000b05180d02011e000b080c0d020150000b0e05280d0201000b2505040d0201000b10054f0c0d02010005070d02011e00050c0d02014e000b0e040d0201320b0a054c0c0d020100050c0d020126000b0e080c140d0201002b0e050c0d0201001605180c0d
|6=>0x1000b050c0d0201540005180c0d02011700090c0d0201320b0a090e05070d0201000905070d020100052804070d02010005040c0201170016050c0d3902010053050c0d0201000b0e050c0d02210b0a050c0d02210b0a05120c0d0201000b1d0e05040d02010052050c0d0201000b08050c060d3402010e05360d0201004605
|7=>0xd02011f000b10050c0d02013b002b050c0d02210b0a091d050c0d02010008050c0d011c000b2f050c0d0201000b0e420d0201320b0a0e0504060201000b23050c0d0115000b1d0e05180d0201002305070c060201000e0507060d020100050c0d5702010056050c0d0201000905180d0201000b23100c0602010005550c0d02
|8=>0x49020b0a050c0d02015d005c050c0d0201000b46050c0d340201002b09050c0d0201003a050c0d3401000805070c060d02013a050c140201005b0c0d0201320b0a09050c060201000b2305180c14020100050c0d02015a000b0e05041402010005040706020100050c0d39020117000e080c060d02010b050c0d02015800050c
|9=>0x620d02010b0a05040c0201610b0a050c0d02015d0b0a510e050c0d0201000b05040d0201600b0a050c0d02015e0b0a51050c0d0201000b050c0d020140000b050c0d02013c000b10050c4b0d0201003a100c0d02010b0a16050c0d0201000e050c060d0201000b0e10041402010a0504181402010051050c140d0201000e4a04
|10=>0x1320b0a054f0c0d0201000b05040c060201000b05070c060d0201003e050c0d340100050c0d02013800050c370d02010b0a05360c140d0201000905040c1402010b0a10050c060d020100050c0d0201650b0a4509050c0d02010b0a090e050c1402010b0a5108050c0d0201000b09050c1402010b0a3e0c0d0201640b0a050c
|11=>0x10b0a050c0d0201470b0a0e050d02016b0b0a4608050c0d0201000b050c0d020150000b050c0d3401400b0a6a050c0d02010b0a23050c0d3402010046050c0d0201000b3a050c0d68010b0a4a0c0d0201500b0a050c670d02010b0a10050c4b1402010a3e100c0d020100050c0d0201660b0a0e050c140d02010005420c0d02
|12=>0x20b0a05420d02011e0b0a05700c0d02010b0a6f05040d02010b0a2b0e050c0d02010b0a05040c14020100050c0d6e02010b0a2b050c0d02010b0a4505410c0d02010b0a43050c0d02010b0a050c4b0d01380b0a050c0d0115000b050c0d020117002b1d050c0d02010b0a6c050c0d02010b0a100c0d0201400b0a48050c0d02
|13=>0x1750b0a050c0d6801400b0a0e0541040d02010b0a050c5f0d020100050c0d02017400450e050c0d02010b0a45050c0d02010b0a23050c060201000b0e05410d02010b0a050c0d0201730b0a0e100c140d02010a05070d02011e0b0a050c0d0272010b0a05180c140d020100054c0c0d02010b0a050c0d020171000e4a0c490d
|14=>0x100050c140d39020100090e05070d02010b0a0905070d02010b0a23050c14020100050c0d0278010b0a3e050c770d010b0a05040c0201170b0a090e05420d02010b0a0905420d02010b0a050c0d02013b000b1d0e05040d02010b0a0e05360d02010b0a76050c0d02010b0a100c0d0201500b0a0e05044902010b0a050c0d02
|15=>0xc0d02010b0a0905040c4902010b0a0e05040d0201000b05410c0d0201320b0a08050c060d02010b090e050c4902010b0a2305070c0d02010009050c4902010b0a050c0d5702010b0a050c060d340201000905410c0d02010b0a050c0d02017a0b0a050c0d0201540b0a050c0d0201290b0a3e050c0d01790b0a050c5f140d02
|16=>0xd0201001d050c0d020100090e050c0d0201000b09050c0d0201000b050c0d02017b0b0a0e05180d0201000b0e05041402010b0a05040c0d0201320b0a23100c1402010a0e05070d020100050c0d0201320b0a4505420c0d02010b0a3a050c0d0201000b234a0c49020b0a0e0541420d02010b0a2305180c0d0201000b091d05
|17=>0xd34010b0a050c0d02017c0b0a3e050c140d02010b0a050c4b1402010b0a1d0e050c0d02010b0a3e050c0d0201000b1d050c0d02010b0a3f10050c0d02010b0a05040c4902010b0a0541040c0d02010b0a05410c0d02010b0a5b05410c0d02010b0a2b09050c0d02010b0a3a050c0d34010b0a23050c0d390201000b1d0e050c
|18=>0xa23050c4902010b0a08050c0d0201000b050c0d0201590b0a0e050c140d02010b0a050c0d0201640b0a0e050c0d0201000b050c0d0201380b0a4a05040c0d02010b0a05360c140d02010b0a5b4a050c0d02010b0a050c140d020100057d0c0d02010b0a16050c0d02010b0a050c0d0201500b0a050c77490d02010b0a050c4b
|19=>0x50c0d0201630b0a050c0d0201710b0a05180c0d0201000b05040c1402010b0a44050c0d02010b0a050c0d0201790b0a05070c0d020100050c0d0201170b0a10050c140d02010a050c0d02017f0b0a7e050c0d02010b0a0541420c0d02010b0a050c770d02010b0a4a050c490d020b0a050c4b0d68010b0a23050c0d3402010b
|20=>0x800b0a0e05420d02010b0a2305070c0d02010b0a090e050c0d02010b0a09050c0d02010b0a2305420c0d02010b0a23050c1402010b0a050c0d390201000b3e050c490d02010b0a3a050c0d02010b0a050c0d0201600b0a0e05040d02010b0a050c5f0d02010b0a23050c0d6802010b0a050c0d0201740b0a23050c0d0201000b
|21=>0x50c0d02010b0a050c4b0d02010b0a05070c0d02010b0a05420c0d02010b0a23050c0d02010b0a050c140d02010b0a050c0d6802010b0a050c0d0201000b4a050c0d02010b0a0e050c0d02010b0a050c0d3402010b0a3e050c4b0d010b0a0e05070d02010b0a050c0d34020100050c0d0201
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x1e60186012600c600660006
|6,0=>0x15f71587151714a7143713c7135712e7127712071197112710b710470fd70f670ef70e870e170da70d370cc70c570be70b770b070a970a2709b7094708d7086707f70787071706a7063705c7055704e7047704070397032702b70247
|7,0=>0x34873408338833083297321831983118309830272fa82f372eb82e382db82d382cb82c382bb82b472ac82a4829d7295828d8285827d8276726e82677260725882517249824182398232722a8223721c7215720e720681fe81f681ee81e771df81d781cf81c871c171b981b181aa71a3719b8194718c8185717d8175816e71668
|7,1=>0x492748b7483847c7475746d8465845d8456744e8447743f8437842f84278420741974118409840273fa83f283ea83e283da83d283ca83c283ba83b283aa83a2839b7394738c8385737d8376736e8366835e8357734f8
|8,0=>0x694868c8685767d8675866d8665865c9655764d8645863c9634862c8625761e7615960d860585fd85f585ed85e495dc85d485cc85c485bc85b485ac85a4859c8595758d8585857c9574856c8564855d7556754e8546853d9535852d8524951b9512950a850284fa84f284ea84e194d984d184c984c184b984b184a984a274999
|8,1=>0x89e9895988d8884987c8875786c9864885c8854884c8843983c7835782d8824981c8815780c980397fa97f197e987e097d887cf97c787bf87b787af87a6979e8796878e8786877e8776876d9765875e7756874e8746873d9735872d8724971c8714870c870486fc86f486eb96e476dd76d496cc86c486bc86b486ac86a4869c8
|9,0=>0xa948a8c8a857a7d8a758a6c9a639a5b8a529a4a8a428a399a318a298a218a198a109a088a0089f889f089e889e089d889d089c979c189b989b189a989a0999889908988897f9977896f8967895e9956894e8946893d9934992b9924791c8914890c890398fb88f388ea98e288d998d188c988c098b888af98a78
|10,0=>0xae38adb8ad38acb8ac38abb8ab47aac8aa48a9c8
|11,0=>0xaeb7
|_,_=>0
def wAt:=mkWire dB 129 254 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xd0b430010e0d430150b0a48c1d0b0a414350c0b438350500430150b0a410200c0d414010b0a4142d0c06434010b0a414120d0b42c290d0042c290e0d430150c0b414010c0542c290c0b43401050042c290c0b414010c0542c290d00430410b0a430350e06030150405c30350e0603015100dc2c29050b410150500430350b0a410200c0d4302d0e0d414010c0542c29
|1=>0xb0a434fe3e0b41409050d4082d0d0042c292b01c242d230c434220d0b414010b0a4302d060cc34010b0a410150b0a4142d0c0d4342d23024142d0d054142d0c0542c290d0e4142d0c0542c29050d4342d020042c290c0042c29050b430350b0a434e105348082d040b43035050042c29050d41401020b434010b0a424030e0d430150c0d434010b0a434950e00c3015
|2=>0x50042c290d0143439050c414050e0d43405050c414050b0a4743507054302d3e0dc2c29050b414093a0b48c09050d42c290b0a4d817070d4302d2802c18310d0042c29460cc2035050042c294505d1031230143415450dc150504014303505068082d0d0042c29050d43401050042c290d004142d0c0542c29430dd1009230141435420d430053e0dc2c29020b41409
|3=>0xb0a410030c0d42c290405c2c290c0d4302d0e06c34010b0a414310541810050c0d42c290c4d414520d0b4a017060c434010b0a414010b0a4342d0c05474350b0a4382d0c0548c2d050d42c29230742c29050d4302d050b438350d0b430150d0b4600b0c0042c29230c4142d0d0b414350d0883035050042c29053482c29020b434092802c10010c0d42c290d088302d
|4=>0xe0d430150c0b410010b0a430350c0b434420b0a4142d0c0d414510d0b42c29053b418330d0042c292b01c38510d0b4ac070e144342d0c05410200c0d414010b0a430350b0a4382d0c0541401020b434010b0a430510b0a4342d0c0548c010b0a414350c0b4343a050b430150b0a5440b080c414010b0a430010405c30350b0a4343a050c430190d0042c290e00c3015
|5=>0xc055440b080c42c290400c30350b0a508350c01430350c05434010b0a414351802c30010b0a430010b0a4382d0c05434010b0a4302d0c0b430150d0042c290b0a4085d0d108142d250b438030c0542c290c00438350c0542c290d0042c29050b434150c3c42037050042c290b0a4782d0405c30350c0042c290d108142d4505c2405230c434150b0a430150c0b42c29
|6=>0x5064082d0d0042c29090b438350c0542c29020b48c09050d42c290c0b43401050042c290b0a48c090d0b414354105c35094205430050e0d430150d0042c290c0042c290d0b41435050c4342d0c0d42c290c0b434310d0042c290d108142d020042c290500430150b0a42c29590b4152e0d024381a0c0543401050b418330d0042c290e144342d0c05438350b0a4382d
|7=>0xd014358d0e01c30150d0c52837050148cd2050d4082d0e00430150b0a508170c0d43005055f92c2d0d0242031050042c290b0a434fa050242037050042c290b0a4142d0d0248c09050b43415230b414350b0a430150d0042c29050b430350d0b430150c004342d0c0d42c290e0042c290d0b430150501414310d0c434050b0a48cd2050d4082d0e06430150d0042c29
|8=>0x50c414050d69415a202014142d0d0b434090b0a4142d0502528120c0d414050b0a4342d0c0541506420d430050400c30350b0a434310d0042c290c0b434010b0a42c29020b4140905348082d0b0a434e105348082d0b0a430510d0b4342d040543035050b434010b0a5002d0d3e81409090148c31050d438350d0b43015080c414010b0a48c310d0b41435050252417
|9=>0xc054342d0c0d42c290261528370501438510d0b43015420d43005440248c05050d414d2020b434091802c30010b0a42c290d108142d1d0d41c150c0b415b5420dc30050d3e8142d050245809230b414353605c1c350c0b430150401c3035080d414010b0a438370c0542c29020b434fa05024242f230c41435020b414350b0a42035050042c2923024143502014343a
|10=>0xd0c434050e14c342d0c05408050d3e81409050c410050c0d52c2d0b0a434091402c342d0b0a4356d0e0143015440c48c05050d434150d0042c29420d430150c0148d0a050d43005050b4342d0c05410170c0d4302d011e410170c0d4342d0c0042c290c4d414520d0b42c290c148342d0d01414310501410170c0d430050c61528370501434310e0bc30150e144342d
|11=>0x20b434010b0a4141104014303523688143502014782d0405c3035057792c050d02435a20201414090b0a450090d0b4342d020042c290e0d430150c0b438350c054302d0b0a4342d050d40565054b83409490243405050243442050b430350e0d430150c01438350c0543005060cc34010b0a430350e0b43015070d430150c0b435bd0e0bc30150d0e8142d0c0541431
|12=>0xb0a42407230c414350c00430150b0a430350d0b430150541810050c0d4142d0d0b414350b0a430150c0b41506420d430052342414350c0148c09050d42c29050143405050d508350c0543005050d430010b0a438350e0b430150504434310d01430350c0542c290541908350c0143401050042c290d01438350c0542c29050d4302d230c43405050d4085d0d108142d
|13=>0xb0a414d2020b430350501430510d0b5283105014342d0b0a4102f0c0d48c2d050d438370c05524090d014082d0d025280b05014342d05024342d0d024382d0c0542c29050241c150c0b44009050b434310d01410050c0d508350c0141509420d43005090b48c31050d48c09050d4082d0200414350b0a42c290e0b430150e0b430150b0a438350c0542c290e0d43015
|14=>0xc014342d050d408010b0a4340505024152d0d02508170c01430350c0552c2d0d024143502014500b0d0b414350b0a438070c05430520d0b430010b0a4342d0c0d48c05050d435a202014302d0b0a43442050b4142d0d0b52c070d024f82f0502508350c0152c050d02434050501408050d0241435020b43405050d414010b0a4152e0d024342d0c05524170d0143015
|15=>0x34090c0b43005050d4342d020142c29050143015020b414090d02430150c0b4082d0b0a528330501430150c01414350c0b438350c0548c31050d41435
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x14800000000000014000
|6,0=>0x49500000000000463000000010cc000100c3b500003740cd02f400002b40a0c00008d40000000000000020307101840510000048800000000000408000000000000000e2000000002cc00001d0000
|7,0=>0x4d513234b912b349d123447d000046d117444d10f400010b441d1052408cff33f0cf843d4cf143b50e943950e14378cda43590d243390ca43190c242f90ba42d90b242b90aa42990a2427909a4259092423908a4219084220107c41e107531c506d41a50654188c5e4169056414904e4
|7,1=>0x1d447411cc47211c447011bc46e11b446c11ac46a11a4468100006711984651191363518a361918335fd17c35e4d7725cd16f45ad1683591160457115845511504531148451114134f51394
|8,0=>0xa50e913a38e8b3a20e853a08e7f39f0e7939d8e7429c4e6e39ace683994e62397ce5c3964e56394ce503934e4a391ce443904e3e38ece3838d4e3238bce2c38a4e26388ce203874e1a385ce143844e0e382ce083814e0237fcdfc37e4df637ccdf037b4dea379cde43784dde376cdd83
|8,1=>0xd50f513d38f4b3d20f453d08f3f3cf0f393cd8f333cc0f2d3ca8f273c90f213c78f1b3c60f153c48f0f3c30f093c18f033c00efd3be8ef73bd0ef13bb8eeb3ba0ee53b88edf3b70ed93b58ed33b40ecd3b28ec73b10ec13af8ebb3ae0eb53ac8eaf3ab0ea93a98ea33a80e9d3a68e973
|9,0=>0x3cf2f34bcb2f24bc72f14bc32f04bbf2ef4bbb2ee4bb72ed4bb32ec4baf2eb4bab2ea4ba72e94ba32e84b9f2e74b9b2e64b972e54b932e44b8f2e34b8b2e24b872e14b832e04b7f2df4b7b2de4b772dd4b732dc4b6f2db4b6b2da4b672d94b632d84b5f2d74b5b2d64b572
|10,0=>0xf687d91f607d71f587d51f507d31f487d11
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 14
def pmP:Nat→Nat
|0=>0x8148000000020120000000059b800000001006000000004008000000010010000000039b800000000ceb0000000023ac000000002500000000009080000000014800000000050000000000108000000000400000000000c20000000002000000000005000000000012000000000044000000000108000000000400000000000a000000000020000000000070000000000080000000000180000000000400000000000c0000000000200000000000400000000000
|1=>0x401000000000f8ff00000003e3ac0000000f87b00000003e1ac0000000f05200000003c0480000000e8f30000000383480000000d8ef0000000363ac0000000b8ef00000002e3ac00000009eef0000000273ac00000009c7b0000000271ac000000098ff0000000263ec000000098ef0000000263ac00000008eef0000000233ec00000008ceb000000020520000000080eb0000000200180000000800000000001c1b80000000600200000000c04800000002092
|2=>0x400013400000c00810000002066bbc00000800c6a0000010263ac0000020800200000082000000000200a000000006203b8000001098eb000000244bd800000088000000000200108000000800400000002000100000006c82e0000001ae3bc000000698ef0000001a40680000006004e0000001201200000004800800000010400c0000004001e0000000c0030000000280180000000641080000001804200000004400000000010cee0000000409dc00000010044
|3=>0x2803e1ec0000910d86b0000244201a800008408c2e0000202203b80000800c86a00002002e1ac0000800a82e0000200263ac00004409cfb0000110273ac00004010a0000000803e3ec0000200f8db00000803e1ec0000200f05000000803a3ec0000200e0d00000080263ac00002007052000008018348000020000c200000800000c0000101c06e0000040361ac0000100c06e00000402e3bc0000100b8eb0000040263fc000010098fb0000040263bc000010098eb
|4=>0x300404088000c0100022000240066b9c000900100400002240363bc0008900d8eb0002204200800008804d8ef0002201223bc0008800f86b0002200363ac0008800b8eb0002200273ac000880098ff0002200263ec000880098ef0002200263ac00042009002000100024008000400080c90000900263ac000240000010000880263ac0002200009000008800020800022000040000088000004000110198ef0000401763bc000100198ef000040044bdc0001000802b
|5=>0x22210273ac00804009ceb0020010269f000800009ceb0020000263ac0040c409ceb0010200271ac00400409eef0010010273ac004000098eb0008000021000018800b86b0006200263ec001880098eb0006200223fc0018800606300050412e3bc0014100b8eb00050402a3bc0014100304200050400810800104409eef0004000623bc001000108ee00040002e0f8001000098eb0004000261ac0010000886a0003084263ac000c2101022000308400088000c01080eb
|6=>0x400022233bc100000808ee0400000273fc10000009cfb0400000273bc10000009ceb0400000263ac100000008ee0280002a81200a00006b00d0280000ae3bc080800002e3020040a0014808010209af3020040244b9c08001088000020000226bbc08000089ae701000012429c040000090830080000020000200000000a005601027bbc01088008cef0040030273bc01000c098ef00400300604801000000800003011027bfc00c0040987b0030000260e40090c409c6b
|7=>0x4000000323ad0000000b8eb4000000263ed000000098eb4000000223eca08200098eb2000000273ec80000009ceb2000000263ac6002000a8e31800800263ec600200098eb18008001818c4002000d8eb1000800273ac400200098eb1000000323ac400000098eb1000000223ac20424009ceb08008003a3ac2002000d8eb0800800263ec2002000800008000803a3cc2000000a8e30800000263ac200000088eb080000020308200000080400422210263bc105804098eb
|8=>0x2040000498e750008002e3ad2000000d8eb4800000323ad200000040c2
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x800000000a00
|6,0=>0x150000000080000014000401c000f02814000d030001800000000002058081400020000000020000000000100000090000a00
|7,0=>0x2c0a0ca79b6012584f87416bd009008c113d1a16a020b90d380f46948140a1f86cbe0e05aa1184820b284c2734888464752310b4240d07156000a9f4b2780032c96510a00814661202cf61312a6494a010b3478542e125a0201c278f8182bb30b285019d0aa444502832420b009a8800fb043ca72f131bc53
|8,0=>0x828860c557ab4723e3693d2ce359994568861bd6004d471b87ae2688dcc6e753174d4f71a8c452e1631b0e2925d8a14a6b37a09587e199e5d6331440054c87422503017e2d0ce35271dd2ef67fbb876994c3b94686458c208a950bf1725b2b3bda634179b5bad214b99eec0648d520e31b20d08326fb6536704ead90e3a6b9fdc83376b65acfb18b5570ce553096245
|9,0=>0x753236de0fe311c8e6fd48b1dd8767e0f462f9498b8668f27255eaf830a9964be5bc0862f418b71d2cf5e251ca346d3c93503480d566337d0c5e2ba5fab970ae703aa0502
|10,0=>0x178607e0b51ef8163c066da
|11,0=>0x2b
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 46 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_125 10 roots_125 ops++addP pm 1 dom_245 9 roots_245 ops++addP pm 2 dom_61 7 roots_61 ops++addP pm 3 dom_233 8 roots_233 ops++addP pm 4 dom_213 7 roots_213 ops++addP pm 5 dom_188 8 roots_188 ops++addP pm 6 dom_221 9 roots_221 ops++addP pm 7 dom_252 9 roots_252 ops++addP pm 8 dom_101 5 roots_101 ops++addP pm 9 dzo_57_4 5 roots_57 ops++addP pm 10 dzo_249_4 7 roots_249 ops++addP pm 11 dom_249 9 roots_249 ops++addP pm 12 dom_189 9 roots_189 ops++addP pm 13 dom_205 6 roots_205 ops++addP pm 14 dom_229 6 roots_229 ops++addP pm 15 dom_237 9 roots_237 ops++addP pm 16 dom_117 7 roots_117 ops++addP pm 17 dom_41 4 roots_41 ops++addP pm 18 dom_109 8 roots_109 ops++addP pm 19 dom_93 7 roots_93 ops++addP pm 20 dom_165 4 roots_165 ops++addP pm 21 dom_85 5 roots_85 ops++addP pm 22 dzo_185_4 6 roots_185 ops++addP pm 23 dom_57 5 roots_57 ops++addP pm 24 dom_173 7 roots_173 ops++addP pm 25 dom_197 4 roots_197 ops++addP pm 26 dom_209 5 roots_209 ops++addP pm 27 dom_181 6 roots_181 ops++addP pm 28 dom_53 4 roots_53 ops++addP pm 29 dom_212 5 roots_212 ops++addP pm 30 dom_141 4 roots_141 ops++addP pm 31 dom_149 5 roots_149 ops++addP pm 32 dom_157 6 roots_157 ops++addP pm 33 dom_113 5 roots_113 ops++addP pm 34 dom_217 6 roots_217 ops++addP pm 35 dom_241 6 roots_241 ops++addP pm 36 dom_121 8 roots_121 ops++addP pm 37 dom_77 5 roots_77 ops++addP pm 38 dzo_233_4 6 roots_233 ops++addP pm 39 dom_29 4 roots_29 ops++addP pm 40 dom_185 6 roots_185 ops++addP pm 41 dom_244 6 roots_244 ops++addP pm 42 dom_220 6 roots_220 ops++addP pm 43 dom_248 6 roots_248 ops++addP pm 44 dom_236 6 roots_236 ops++addP pm 45 dzo_169_4 5 roots_169 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_253 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_188 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_221 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_101 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_57_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_249_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_189 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_229 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_237 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_165 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_zo_185_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_197 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_209 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_53 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_212 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_141 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_149 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_zo_233_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_29 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h45;exact cpcs (by decide +kernel) lowS_zo_169_4_41 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_125 10 s (0,roots_125.map (·&&&dom_125)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_253 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_125 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_253==dom_253)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_253 gM v ys):RunD true dom_253 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_253 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 6 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 46 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 46 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 107 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 107 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 61 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 61 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 10 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_253 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤11) (h:RunD true dom_253 gM s xsM):False:=by
  have hmin:6≤s:=by have hl:=run_len h;change 7≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_253 roots_253 goal_253 12:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_253
theorem lowS_253:Lower true dom_253 roots_253 goal_253 12:=S_253.noCircuit
def dzo_252_2:=0x4444444444444444444444444444444444444444444444444444444444444444
def gzo_252_2:=0x4444444444444444444444444444444444444444444444404444444444404400
def gsh_252_2:=0x1111111111111111111111111111111111111111111111101111111111101100
theorem lowS_zo_252_2_84:Lower true dzo_252_2 roots_252 gzo_252_2 7:=lower_iso_b (d1:=dom_252) (r1:=roots_252) (T1:=gsh_252_2) [(dom_252,2)] (by decide +kernel) (lower_slice_b (T:=gsh_252_2) [(0x1100110011001100110011001100110011001100110011001100110011001100,0,8),(0x1111111100000000111111110000000011111111000000001111111100000000,0,32),(0x1111111111111111111111111111111100000000000000000000000000000000,0,128)] (by decide +kernel) lowS_84)
def dzo_244_2:=0x44004400440044004400440044004400440044004400440044004400440044
def gzo_244_2:=0x44004400440044004400440044004400440044004400400044004400400000
def gsh_244_2:=0x11001100110011001100110011001100110011001100100011001100100000
theorem lowS_zo_244_2_84:Lower true dzo_244_2 roots_244 gzo_244_2 6:=lower_iso_b (d1:=dom_244) (r1:=roots_244) (T1:=gsh_244_2) [(dom_244,2)] (by decide +kernel) (lower_slice_b (T:=gsh_244_2) [(0x11001100000000001100110000000000110011000000000011001100000000,0,32),(0x11001100110011001100110011001100000000000000000000000000000000,0,128)] (by decide +kernel) lowS_84)
def dzo_250_4:=0x5050505050505050505050505050505050505050505050505050505050505050
def gzo_250_4:=0x5050505050505050505050505050505050505050505050505050504050504000
def gsh_250_4:=0x505050505050505050505050505050505050505050505050505050405050400
theorem lowS_zo_250_4_42:Lower true dzo_250_4 roots_250 gzo_250_4 7:=lower_iso_b (d1:=dom_250) (r1:=roots_250) (T1:=gsh_250_4) [(dom_250,4)] (by decide +kernel) (lower_slice_b (T:=gsh_250_4) [(0x505000005050000050500000505000005050000050500000505000005050000,0,16),(0x505050505050505000000000000000005050505050505050000000000000000,0,64),(0x505050505050505050505050505050500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
def dzo_238_16:=0x5555000055550000555500005555000055550000555500005555000055550000
def gzo_238_16:=0x5555000055550000555500005555000055550000555500005554000054500000
def gsh_238_16:=0x555500005555000055550000555500005555000055550000555400005450
theorem lowS_zo_238_16_42:Lower true dzo_238_16 roots_238 gzo_238_16 7:=lower_iso_b (d1:=dom_238) (r1:=roots_238) (T1:=gsh_238_16) [(dom_238,16)] (by decide +kernel) (lower_slice_b (T:=gsh_238_16) [(0x505000005050000050500000505000005050000050500000505000005050,0,4),(0x555500005555000000000000000000005555000055550000000000000000,0,64),(0x555500005555000055550000555500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
namespace S_254
def pG:List (Nat×Nat):=[(2,10),(2,34),(2,130),(4,20),(4,68),(4,132),(6,14),(6,22),(6,38),(6,70),(6,134),(8,10),(8,40),(8,72),(8,136),(12,14),(12,28),(12,44),(12,76),(12,140),(16,20),(16,80),(16,144),(18,22),(18,26),(18,50),(18,82),(18,146),(24,26),(24,28),(24,56),(24,88),(24,152),(32,34),(32,40),(32,96),(32,160),(36,38),(36,44),(36,52),(36,100),(36,164),(48,50),(48,52),(48,56),(48,112),(48,176),(64,68),(64,72),(64,80),(64,96),(66,70),(66,74),(66,82),(66,98),(66,194),(128,130),(128,132),(128,136),(128,144),(128,160),(192,194),(192,196),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffffffffff
def xsM:=roots_254.map (·&&&dom_254)
def gM:=goal_254&&&dom_254
def NN:Nat→Nat
|8=>2
|9=>13
|10=>4
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|8,0=>0x516952716a
|9,0=>0xac0b35ad9e420ac3bdc02af2e23e1b197d9188e1172e916d83122de0b30003069
|10,0=>0xe050c6f64d371a01a434
|11,0=>0xba90f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaaaaaaaaaa88aa88aaaaaaaaaa88aa88aaaaaaaaaa88aa88aaaaaaaaaa88aa884444444440404040444444444040404044444444404040404444444440404042aa82aa82aa82aa82aa82aa82aa82aa82aa82aa82aa82aa82aa82aa82aa82aa80504050405040504050405040504050405040504050405040504050405040504aaaaaaaaaa00aa00aaaaaaaaaa00aa00aaaaaaaaaa00aa00aaaaaaaaaa00aa015555555511111111555555551111111155555555111111115555555511111112aa22aa22aa22aa22aa22aa22aa22aa22aa22aa22aa22aa22aa22aa22aa22aa25555555500000000555555550000000055555555000000005555555500000000aaaaaaaaa0a0a0a0aaaaaaaaa0a0a0a0aaaaaaaaa0a0a0a0aaaaaaaaa0a0a0a15554000155540001555400015554000155540001555400015554000155540002a802a802a802a802a802a802a802a802a802a802a802a802a802a802a802a80505050505050505050505050505050505050505050505050505050505050505088888888888888888888888888888888888888888888888888888888888888880000000155115510000000015511551000000001551155100000000155115512aaaaaaaaaaaaaaa80000000000000002aaaaaaaaaaaaaaa80000000000000005555555555555555555555555555555500000000000000000000000000000000
|0,1=>0x15555540155555401555554015555540155555401555554015555540155555402aaaaaaaaaaaaa802aaaaaaaaaaaaa802aaaaaaaaaaaaa802aaaaaaaaaaaaa80555555555555000055555555555500005555555555550000555555555555000000aa00aa00aa000000aa00aa00aa000000aa00aa00aa000000aa00aa00aa0001515151515151515151515151515151515151515151515151515151515151515000000002a2a2a2a000000002a2a2a2a000000002a2a2a2a000000002a2a2a2a5554555455545554555455545554555455545554555455545554555455545554
|_,_=>0
def sP:Nat→Nat
|0=>0x418b220c20520c929020aa0c520c20418a41cc203a0c590c20418a41c420418a418820520cd29061020d02906103d0629061020c520dc102d462906101d0669461020c520d8102d4649020398a418820
|1=>0x20c520c204192520c205a0c520c20458c520c20
|_=>0
def sO:Nat→Nat→Nat
|8,0=>0x87008
|9,0=>0x7086886085885084883f93782f82781f81780f8
|10,0=>0x908888808788
|11,0=>0x987
|_,_=>0
def wAt:=mkWire dB 23 255 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x28d41529920d40d28d5994152d241941120d44a20d42628d29140d49128d42528d38f4112a140d41129149328d41540d28d4a341128d
|_=>0
def oO:Nat→Nat→Nat
|8,0=>0xcc03
|9,0=>0x1e2709a26096250922408e2308a220862
|10,0=>0x8c62184601
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 10
def pmP:Nat→Nat
|0=>0x8607ef040fdd0c1fb9d07d72807ae340f5c101ff8203f70307ee060f5c083eb80fbf70147fe009fdc00bfb8007f70007fe000fdc001eb800000
|_=>0
def pmB:Nat→Nat→Nat
|8,0=>0x83
|9,0=>0x2839736a18689547
|10,0=>0x1a5f2
|11,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 23 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_190 10 roots_190 ops++addP pm 1 dom_126 10 roots_126 ops++addP pm 2 dom_250 9 roots_250 ops++addP pm 3 dom_244 6 roots_244 ops++addP pm 4 dom_234 8 roots_234 ops++addP pm 5 dzo_252_2 7 roots_252 ops++addP pm 6 dom_252 9 roots_252 ops++addP pm 7 dom_246 9 roots_246 ops++addP pm 8 dom_238 9 roots_238 ops++addP pm 9 dom_222 9 roots_222 ops++addP pm 10 dom_214 7 roots_214 ops++addP pm 11 dzo_244_2 6 roots_244 ops++addP pm 12 dom_220 6 roots_220 ops++addP pm 13 dom_212 5 roots_212 ops++addP pm 14 dom_242 6 roots_242 ops++addP pm 15 dzo_250_4 7 roots_250 ops++addP pm 16 dzo_212_2 5 roots_212 ops++addP pm 17 dzo_220_2 6 roots_220 ops++addP pm 18 dzo_238_16 7 roots_238 ops++addP pm 19 dom_206 6 roots_206 ops++addP pm 20 dom_230 6 roots_230 ops++addP pm 21 dom_218 6 roots_218 ops++addP pm 22 dom_248 6 roots_248 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_254 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_zo_252_2_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_238 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_244_2_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_212 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_250_4_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_212_2_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_220_2_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_238_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_248 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_190 10 s (0,roots_190.map (·&&&dom_190)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_254 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_190 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_254==dom_254)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_254 gM v ys):RunD true dom_254 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_254 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 2 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 13 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 13 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 4 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_254 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
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
def isoMvS_247:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_247:Lower true dom_247 roots_247 goal_247 12:=lower_iso_b isoMvS_247 (by decide +kernel) lowS_223
namespace S_255
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(2,10),(2,34),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(4,20),(4,68),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(6,14),(6,22),(6,38),(6,70),(6,134),(7,15),(7,23),(7,39),(7,71),(7,135),(8,9),(8,10),(8,40),(8,72),(8,136),(12,13),(12,14),(12,28),(12,44),(12,76),(12,140),(16,17),(16,20),(16,80),(16,144),(18,19),(18,22),(18,26),(18,50),(18,82),(18,146),(24,25),(24,26),(24,28),(24,56),(24,88),(24,152),(32,33),(32,34),(32,40),(32,96),(32,160),(36,37),(36,38),(36,44),(36,52),(36,100),(36,164),(48,49),(48,50),(48,52),(48,56),(48,112),(48,176),(64,65),(64,68),(64,72),(64,80),(64,96),(66,67),(66,70),(66,74),(66,82),(66,98),(66,194),(128,130),(128,132),(128,136),(128,144),(128,160),(129,131),(129,133),(129,137),(129,145),(129,161),(129,193),(192,193),(192,194),(192,196),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffffffffffffffffffff
def xsM:=roots_255.map (·&&&dom_255)
def gM:=goal_255&&&dom_255
def NN:Nat→Nat
|13=>1
|_=>0
def HT:Nat→Nat→Nat
|13,0=>0x64457
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0xfac688
|_=>0
def sO:Nat→Nat→Nat
|13,0=>8
|_,_=>0
def wAt:=mkWire dB 8 256 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 8
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def pmP:Nat→Nat
|0=>0x3f80
|_=>0
def pmB:Nat→Nat→Nat
|13,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 1 (j%128);fld (pmP (k/32)) 7 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_254 12 roots_254 ops++addP pm 1 dom_127 12 roots_127 ops++addP pm 2 dom_253 12 roots_253 ops++addP pm 3 dom_251 12 roots_251 ops++addP pm 4 dom_247 12 roots_247 ops++addP pm 5 dom_239 12 roots_239 ops++addP pm 6 dom_223 12 roots_223 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_255 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_127 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_247 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_223 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_254 12 s (0,roots_254.map (·&&&dom_254)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_254 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_255==dom_255)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_255 gM v ys):RunD true dom_255 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_255 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z13 : ∀ i, 0 ≤ i → i < 1 → Z 13 i = true := span_ok (by decide +kernel : span (Z 13) 1 0 = true)
theorem checked (s:Nat) (hs:s≤13):∀ i<NN s,bar dom_255 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
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
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [6, 7] }, { op := GateOp.or, inputs := [3, 5] }, { op := GateOp.or, inputs := [0, 8] }, { op := GateOp.or, inputs := [4, 9] }, { op := GateOp.and, inputs := [10, 11] }, { op := GateOp.or, inputs := [4, 8] }, { op := GateOp.and, inputs := [2, 13] }, { op := GateOp.or, inputs := [7, 9] }, { op := GateOp.and, inputs := [1, 15] }, { op := GateOp.and, inputs := [0, 6] }, { op := GateOp.and, inputs := [3, 5] }, { op := GateOp.or, inputs := [12, 14] }, { op := GateOp.or, inputs := [19, 16] }, { op := GateOp.or, inputs := [20, 17] }, { op := GateOp.or, inputs := [21, 18] }]

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 22⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
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

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_51990_aux

theorem PEqualNP.Outside.L_meta_51990 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_51990_aux.main
