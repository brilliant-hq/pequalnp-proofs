import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_52446_aux
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
def goal_27 : Nat := 0xeeeeaa00eeeeaa00eeeeaa00eeeeaa00eeeeaa00eeeeaa00eeeeaa00eeeeaa00
def roots_27 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_29 : Nat := 0x33333333
def goal_29 : Nat := 0xfafaaa00fafaaa00fafaaa00fafaaa00fafaaa00fafaaa00fafaaa00fafaaa00
def roots_29 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_31 : Nat := 0xffffffff
def goal_31 : Nat := 0xfefeaa00fefeaa00fefeaa00fefeaa00fefeaa00fefeaa00fefeaa00fefeaa00
def roots_31 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_41 : Nat := 0x30300000303
def goal_41 : Nat := 0xffaaffaaaa00aa00ffaaffaaaa00aa00ffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_41 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_43 : Nat := 0xf0f00000f0f
def goal_43 : Nat := 0xffeeffeeaa00aa00ffeeffeeaa00aa00ffeeffeeaa00aa00ffeeffeeaa00aa00
def roots_43 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_53 : Nat := 0x33003300330033
def goal_53 : Nat := 0xfafaaaaafafa0000fafaaaaafafa0000fafaaaaafafa0000fafaaaaafafa0000
def roots_53 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_54 : Nat := 0x55005500550055
def goal_54 : Nat := 0xfcfcccccfcfc0000fcfcccccfcfc0000fcfcccccfcfc0000fcfcccccfcfc0000
def roots_54 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xfefeeeeefefe0000fefeeeeefefe0000fefeeeeefefe0000fefeeeeefefe0000
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_57 : Nat := 0x303030303030303
def goal_57 : Nat := 0xffaaffaaaaaaaa00ffaaffaaaaaaaa00ffaaffaaaaaaaa00ffaaffaaaaaaaa00
def roots_57 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_58 : Nat := 0x505050505050505
def goal_58 : Nat := 0xffccffcccccc0000ffccffcccccc0000ffccffcccccc0000ffccffcccccc0000
def roots_58 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xffeeffeeeeeeaa00ffeeffeeeeeeaa00ffeeffeeeeeeaa00ffeeffeeeeeeaa00
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xfffaffaafafaaa00fffaffaafafaaa00fffaffaafafaaa00fffaffaafafaaa00
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_62 : Nat := 0x5555555555555555
def goal_62 : Nat := 0xfffcffccfcfc0000fffcffccfcfc0000fffcffccfcfc0000fffcffccfcfc0000
def roots_62 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfffeffeefefeaa00fffeffeefefeaa00fffeffeefefeaa00fffeffeefefeaa00
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_73 : Nat := 0x3030000000000000303
def goal_73 : Nat := 0xffaaffaaffaaffaaaa00aa00aa00aa00ffaaffaaffaaffaaaa00aa00aa00aa00
def roots_73 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_77 : Nat := 0x33330000000000003333
def goal_77 : Nat := 0xfffafffafffafffaaa00aa00aa00aa00fffafffafffafffaaa00aa00aa00aa00
def roots_77 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_83 : Nat := 0xf000f00000000000f000f
def goal_83 : Nat := 0xeeeeaaaaeeeeaaaaeeee0000eeee0000eeeeaaaaeeeeaaaaeeee0000eeee0000
def roots_83 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_86 : Nat := 0x5500550000000000550055
def goal_86 : Nat := 0xfcfcf0f0fcfcf0f0fcfc0000fcfc0000fcfcf0f0fcfcf0f0fcfc0000fcfc0000
def roots_86 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_87 : Nat := 0xff00ff0000000000ff00ff
def goal_87 : Nat := 0xfefefafafefefafafefe0000fefe0000fefefafafefefafafefe0000fefe0000
def roots_87 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f
def goal_91 : Nat := 0xffeeffaaffeeffaaeeeeaa00eeeeaa00ffeeffaaffeeffaaeeeeaa00eeeeaa00
def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_93 : Nat := 0x333333330000000033333333
def goal_93 : Nat := 0xfffafffafffafffafafaaa00fafaaa00fffafffafffafffafafaaa00fafaaa00
def roots_93 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_94 : Nat := 0x555555550000000055555555
def goal_94 : Nat := 0xfffcfff0fffcfff0fcfc0000fcfc0000fffcfff0fffcfff0fcfc0000fcfc0000
def roots_94 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_95 : Nat := 0xffffffff00000000ffffffff
def goal_95 : Nat := 0xfffefffafffefffafefeaa00fefeaa00fffefffafffefffafefeaa00fefeaa00
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

def dom_102 : Nat := 0x55000000550000005500000055
def goal_102 : Nat := 0xfffffffff0f0f0f0cccccccc00000000fffffffff0f0f0f0cccccccc00000000
def roots_102 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_103 : Nat := 0xff000000ff000000ff000000ff
def goal_103 : Nat := 0xfffffffffafafafaeeeeeeee00000000fffffffffafafafaeeeeeeee00000000
def roots_103 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_104 : Nat := 0x101000001010000010100000101
def goal_104 : Nat := 0xffffffffff00ff00ff00ff0000000000ffffffffff00ff00ff00ff0000000000
def roots_104 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_105 : Nat := 0x303000003030000030300000303
def goal_105 : Nat := 0xffffffffffaaffaaffaaffaaaa00aa00ffffffffffaaffaaffaaffaaaa00aa00
def roots_105 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffffffffffaaffaaffeeffeeaa00aa00ffffffffffaaffaaffeeffeeaa00aa00
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_109 : Nat := 0x3333000033330000333300003333
def goal_109 : Nat := 0xfffffffffffafffaffaaffaaaa00aa00fffffffffffafffaffaaffaaaa00aa00
def roots_109 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_110 : Nat := 0x5555000055550000555500005555
def goal_110 : Nat := 0xfffffffffff0fff0ffccffcc00000000fffffffffff0fff0ffccffcc00000000
def roots_110 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xfffffffffffafffaffeeffeeaa00aa00fffffffffffafffaffeeffeeaa00aa00
def roots_111 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_113 : Nat := 0x30003000300030003000300030003
def goal_113 : Nat := 0xffffffffaaaaaaaaaaaaaaaaaaaa0000ffffffffaaaaaaaaaaaaaaaaaaaa0000
def roots_113 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_114 : Nat := 0x50005000500050005000500050005
def goal_114 : Nat := 0xffffffffcccc0000cccccccccccc0000ffffffffcccc0000cccccccccccc0000
def roots_114 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def goal_115 : Nat := 0xffffffffeeeeaaaaeeeeeeeeeeee0000ffffffffeeeeaaaaeeeeeeeeeeee0000
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_116 : Nat := 0x110011001100110011001100110011
def goal_116 : Nat := 0xfffffffff0f0f0f0f0f00000f0f00000fffffffff0f0f0f0f0f00000f0f00000
def roots_116 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_117 : Nat := 0x330033003300330033003300330033
def goal_117 : Nat := 0xfffffffffafafafafafaaaaafafa0000fffffffffafafafafafaaaaafafa0000
def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xfffffffffcfcf0f0fcfcccccfcfc0000fffffffffcfcf0f0fcfcccccfcfc0000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xfffffffffefefafafefeeeeefefe0000fffffffffefefafafefeeeeefefe0000
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_121 : Nat := 0x3030303030303030303030303030303
def goal_121 : Nat := 0xffffffffffaaffaaffaaffaaaaaaaa00ffffffffffaaffaaffaaffaaaaaaaa00
def roots_121 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_122 : Nat := 0x5050505050505050505050505050505
def goal_122 : Nat := 0xffffffffffccff00ffccffcccccc0000ffffffffffccff00ffccffcccccc0000
def roots_122 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffffffffffeeffaaffeeffeeeeeeaa00ffffffffffeeffaaffeeffeeeeeeaa00
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_124 : Nat := 0x11111111111111111111111111111111
def goal_124 : Nat := 0xfffffffffff0fff0fff0ff00f0f00000fffffffffff0fff0fff0ff00f0f00000
def roots_124 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xfffffffffffafffafffaffaafafaaa00fffffffffffafffafffaffaafafaaa00
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_126 : Nat := 0x55555555555555555555555555555555
def goal_126 : Nat := 0xfffffffffffcfff0fffcffccfcfc0000fffffffffffcfff0fffcffccfcfc0000
def roots_126 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xfffffffffffefffafffeffeefefeaa00fffffffffffefffafffeffeefefeaa00
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_141 : Nat := 0x333300000000000000000000000000003333
def goal_141 : Nat := 0xfffafffafffafffafffafffafffafffaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_141 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_143 : Nat := 0xffff0000000000000000000000000000ffff
def goal_143 : Nat := 0xfffefffefffefffefffefffefffefffeaa00aa00aa00aa00aa00aa00aa00aa00
def roots_143 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_154 : Nat := 0x505050500000000000000000000000005050505
def goal_154 : Nat := 0xffccffccffccffccffccffccffccffcccccc0000cccc0000cccc0000cccc0000
def roots_154 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def goal_155 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffeeeeeeaa00eeeeaa00eeeeaa00eeeeaa00
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_156 : Nat := 0x1111111100000000000000000000000011111111
def goal_156 : Nat := 0xfff0fff0fff0fff0fff0fff0fff0fff0f0f00000f0f00000f0f00000f0f00000
def roots_156 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_157 : Nat := 0x3333333300000000000000000000000033333333
def goal_157 : Nat := 0xfffafffafffafffafffafffafffafffafafaaa00fafaaa00fafaaa00fafaaa00
def roots_157 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_158 : Nat := 0x5555555500000000000000000000000055555555
def goal_158 : Nat := 0xfffcfffcfffcfffcfffcfffcfffcfffcfcfc0000fcfc0000fcfc0000fcfc0000
def roots_158 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_159 : Nat := 0xffffffff000000000000000000000000ffffffff
def goal_159 : Nat := 0xfffefffefffefffefffefffefffefffefefeaa00fefeaa00fefeaa00fefeaa00
def roots_159 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_162 : Nat := 0x50000000500000000000000000000000500000005
def goal_162 : Nat := 0xffffffffccccccccffffffffcccccccccccccccc00000000cccccccc00000000
def roots_162 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_163 : Nat := 0xf0000000f00000000000000000000000f0000000f
def goal_163 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeeeeeeeeeee00000000eeeeeeee00000000
def roots_163 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_166 : Nat := 0x550000005500000000000000000000005500000055
def goal_166 : Nat := 0xfffffffffcfcfcfcfffffffffcfcfcfccccccccc00000000cccccccc00000000
def roots_166 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_167 : Nat := 0xff000000ff0000000000000000000000ff000000ff
def goal_167 : Nat := 0xfffffffffefefefefffffffffefefefeeeeeeeee00000000eeeeeeee00000000
def roots_167 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_168 : Nat := 0x1010000010100000000000000000000010100000101
def goal_168 : Nat := 0xffffffffff00ff00ffffffffff00ff00ff00ff0000000000ff00ff0000000000
def roots_168 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_169 : Nat := 0x3030000030300000000000000000000030300000303
def goal_169 : Nat := 0xffffffffffaaffaaffffffffffaaffaaffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_169 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_170 : Nat := 0x5050000050500000000000000000000050500000505
def goal_170 : Nat := 0xffffffffffccffccffffffffffccffccffccffcc00000000ffccffcc00000000
def roots_170 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_171 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
def goal_171 : Nat := 0xffffffffffeeffeeffffffffffeeffeeffeeffeeaa00aa00ffeeffeeaa00aa00
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_173 : Nat := 0x33330000333300000000000000000000333300003333
def goal_173 : Nat := 0xfffffffffffafffafffffffffffafffaffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_173 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_174 : Nat := 0x55550000555500000000000000000000555500005555
def goal_174 : Nat := 0xfffffffffffcfffcfffffffffffcfffcffccffcc00000000ffccffcc00000000
def roots_174 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_175 : Nat := 0xffff0000ffff00000000000000000000ffff0000ffff
def goal_175 : Nat := 0xfffffffffffefffefffffffffffefffeffeeffeeaa00aa00ffeeffeeaa00aa00
def roots_175 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_178 : Nat := 0x500050005000500000000000000000005000500050005
def goal_178 : Nat := 0xffffffffccccccccffffffffcccccccccccccccccccc0000cccccccccccc0000
def roots_178 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_179 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f
def goal_179 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeeeeeeeeeeeeeee0000eeeeeeeeeeee0000
def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_180 : Nat := 0x1100110011001100000000000000000011001100110011
def goal_180 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0f0f00000f0f00000f0f00000f0f00000
def roots_180 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_181 : Nat := 0x3300330033003300000000000000000033003300330033
def goal_181 : Nat := 0xfffffffffafafafafffffffffafafafafafaaaaafafa0000fafaaaaafafa0000
def roots_181 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_182 : Nat := 0x5500550055005500000000000000000055005500550055
def goal_182 : Nat := 0xfffffffffcfcfcfcfffffffffcfcfcfcfcfcccccfcfc0000fcfcccccfcfc0000
def roots_182 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_183 : Nat := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
def goal_183 : Nat := 0xfffffffffefefefefffffffffefefefefefeeeeefefe0000fefeeeeefefe0000
def roots_183 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_185 : Nat := 0x30303030303030300000000000000000303030303030303
def goal_185 : Nat := 0xffffffffffaaffaaffffffffffaaffaaffaaffaaaaaaaa00ffaaffaaaaaaaa00
def roots_185 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_186 : Nat := 0x50505050505050500000000000000000505050505050505
def goal_186 : Nat := 0xffffffffffccffccffffffffffccffccffccffcccccc0000ffccffcccccc0000
def roots_186 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffffffeeffeeffffffffffeeffeeffeeffeeeeeeaa00ffeeffeeeeeeaa00
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_188 : Nat := 0x111111111111111100000000000000001111111111111111
def goal_188 : Nat := 0xfffffffffff0fff0fffffffffff0fff0fff0ff00f0f00000fff0ff00f0f00000
def roots_188 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_189 : Nat := 0x333333333333333300000000000000003333333333333333
def goal_189 : Nat := 0xfffffffffffafffafffffffffffafffafffaffaafafaaa00fffaffaafafaaa00
def roots_189 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_190 : Nat := 0x555555555555555500000000000000005555555555555555
def goal_190 : Nat := 0xfffffffffffcfffcfffffffffffcfffcfffcffccfcfc0000fffcffccfcfc0000
def roots_190 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xfffffffffffefffefffffffffffefffefffeffeefefeaa00fffeffeefefeaa00
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_196 : Nat := 0x11000000000000001100000000000000110000000000000011
def goal_196 : Nat := 0xfffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000
def roots_196 : List Nat := [xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_198 : Nat := 0x55000000000000005500000000000000550000000000000055
def goal_198 : Nat := 0xfffffffffffffffffcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f00000000000000000
def roots_198 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_199 : Nat := 0xff00000000000000ff00000000000000ff00000000000000ff
def goal_199 : Nat := 0xfffffffffffffffffefefefefefefefefafafafafafafafa0000000000000000
def roots_199 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_200 : Nat := 0x101000000000000010100000000000001010000000000000101
def goal_200 : Nat := 0xffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff000000000000000000
def roots_200 : List Nat := [xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_201 : Nat := 0x303000000000000030300000000000003030000000000000303
def goal_201 : Nat := 0xffffffffffffffffffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00aa00aa00
def roots_201 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffffffffffffffffffeeffeeffeeffeeffaaffaaffaaffaaaa00aa00aa00aa00
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_207 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def goal_207 : Nat := 0xfffffffffffffffffffefffefffefffefffafffafffafffaaa00aa00aa00aa00
def roots_207 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_210 : Nat := 0x50005000000000005000500000000000500050000000000050005
def goal_210 : Nat := 0xffffffffffffffffcccccccccccccccccccc0000cccc0000cccc0000cccc0000
def roots_210 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffffffffffffffeeeeeeeeeeeeeeeeeeeeaaaaeeeeaaaaeeee0000eeee0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_212 : Nat := 0x110011000000000011001100000000001100110000000000110011
def goal_212 : Nat := 0xfffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000
def roots_212 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xfffffffffffffffffcfcfcfcfcfcfcfcfcfcf0f0fcfcf0f0fcfc0000fcfc0000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xfffffffffffffffffefefefefefefefefefefafafefefafafefe0000fefe0000
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def goal_218 : Nat := 0xffffffffffffffffffccffccffccffccffccff00ffccff00cccc0000cccc0000
def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffffffffffffffffeeffeeffeeffeeffeeffaaffeeffaaeeeeaa00eeeeaa00
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xfffffffffffffffffffcfffcfffcfffcfffcfff0fffcfff0fcfc0000fcfc0000
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffffffffffffffefffefffefffefffefffafffefffafefeaa00fefeaa00
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_224 : Nat := 0x100000001000000010000000100000001000000010000000100000001
def goal_224 : Nat := 0xffffffffffffffffffffffff00000000ffffffff000000000000000000000000
def roots_224 : List Nat := [xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_225 : Nat := 0x300000003000000030000000300000003000000030000000300000003
def goal_225 : Nat := 0xffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaa00000000
def roots_225 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_226 : Nat := 0x500000005000000050000000500000005000000050000000500000005
def goal_226 : Nat := 0xffffffffffffffffffffffffccccccccffffffff00000000cccccccc00000000
def roots_226 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_228 : Nat := 0x1100000011000000110000001100000011000000110000001100000011
def goal_228 : Nat := 0xfffffffffffffffffffffffff0f0f0f0fffffffff0f0f0f00000000000000000
def roots_228 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_229 : Nat := 0x3300000033000000330000003300000033000000330000003300000033
def goal_229 : Nat := 0xfffffffffffffffffffffffffafafafafffffffffafafafaaaaaaaaa00000000
def roots_229 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def goal_230 : Nat := 0xfffffffffffffffffffffffffcfcfcfcfffffffff0f0f0f0cccccccc00000000
def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def goal_231 : Nat := 0xfffffffffffffffffffffffffefefefefffffffffafafafaeeeeeeee00000000
def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_232 : Nat := 0x10100000101000001010000010100000101000001010000010100000101
def goal_232 : Nat := 0xffffffffffffffffffffffffff00ff00ffffffffff00ff00ff00ff0000000000
def roots_232 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffffffffffffffffffaaffaaffffffffffaaffaaffaaffaaaa00aa00
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffffffffffffffffffccffccffffffffff00ff00ffccffcc00000000
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffffffffffffffffffeeffeeffffffffffaaffaaffeeffeeaa00aa00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xfffffffffffffffffffffffffffafffafffffffffffafffaffaaffaaaa00aa00
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_238 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def goal_238 : Nat := 0xfffffffffffffffffffffffffffcfffcfffffffffff0fff0ffccffcc00000000
def roots_238 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffffffffffffffffffefffefffffffffffafffaffeeffeeaa00aa00
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def goal_242 : Nat := 0xffffffffffffffffffffffffccccccccffffffffcccc0000cccccccccccc0000
def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffffffffffffffffeeeeeeeeffffffffeeeeaaaaeeeeeeeeeeee0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_244 : Nat := 0x11001100110011001100110011001100110011001100110011001100110011
def goal_244 : Nat := 0xfffffffffffffffffffffffff0f0f0f0fffffffff0f0f0f0f0f00000f0f00000
def roots_244 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_245 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
def goal_245 : Nat := 0xfffffffffffffffffffffffffafafafafffffffffafafafafafaaaaafafa0000
def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffffffffffffffffffcfcfcfcfffffffffcfcf0f0fcfcccccfcfc0000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffffffffffffffefefefefffffffffefefafafefeeeeefefe0000
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffffffffffffffaaffaaffffffffffaaffaaffaaffaaaaaaaa00
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffffffffffffffccffccffffffffffccff00ffccffcccccc0000
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffffffffffffffeeffeeffffffffffeeffaaffeeffeeeeeeaa00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_252 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
def goal_252 : Nat := 0xfffffffffffffffffffffffffff0fff0fffffffffff0fff0fff0ff00f0f00000
def roots_252 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffffffffffffffafffafffffffffffafffafffaffaafafaaa00
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffffffffffffffcfffcfffffffffffcfff0fffcffccfcfc0000
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffffffffffffffefffefffffffffffefffafffeffeefefeaa00
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
def isoMvS_73:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_73:Lower true dom_73 roots_73 goal_73 4:=lower_iso_b isoMvS_73 (by decide +kernel) lowS_41
def isoMvS_97:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_97:Lower true dom_97 roots_97 goal_97 4:=lower_iso_b isoMvS_97 (by decide +kernel) lowS_41
def isoMvS_104:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_104:Lower true dom_104 roots_104 goal_104 4:=lower_iso_b isoMvS_104 (by decide +kernel) lowS_41
def isoMvS_162:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_162:Lower true dom_162 roots_162 goal_162 4:=lower_iso_b isoMvS_162 (by decide +kernel) lowS_41
def isoMvS_168:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_168:Lower true dom_168 roots_168 goal_168 4:=lower_iso_b isoMvS_168 (by decide +kernel) lowS_41
def isoMvS_196:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_196:Lower true dom_196 roots_196 goal_196 4:=lower_iso_b isoMvS_196 (by decide +kernel) lowS_41
def isoMvS_200:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_200:Lower true dom_200 roots_200 goal_200 4:=lower_iso_b isoMvS_200 (by decide +kernel) lowS_41
def isoMvS_224:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_224:Lower true dom_224 roots_224 goal_224 4:=lower_iso_b isoMvS_224 (by decide +kernel) lowS_41
namespace S_27
def pG:List (Nat×Nat):=[(1,9),(1,17),(2,18),(3,11),(3,19),(8,9),(10,11),(10,26),(16,17),(16,18),(24,25),(24,26)]
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
def symsG:List (List (Nat×Nat)):=[[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
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
theorem lowS_43:Lower true dom_43 roots_43 goal_43 5:=lower_slice_b [(0xc0c00000c0c,32,34)] (by decide +kernel) lowS_41
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
theorem lowS_163:Lower true dom_163 roots_163 goal_163 5:=lower_slice_b [(0xa0000000a00000000000000000000000a0000000a,32,33)] (by decide +kernel) lowS_162
def isoMvS_29:List (Nat×Nat):=[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_29:Lower true dom_29 roots_29 goal_29 4:=lower_iso_b isoMvS_29 (by decide +kernel) lowS_27
def isoMvS_53:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_53:Lower true dom_53 roots_53 goal_53 4:=lower_iso_b isoMvS_53 (by decide +kernel) lowS_27
def isoMvS_54:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_54:Lower true dom_54 roots_54 goal_54 4:=lower_iso_b isoMvS_54 (by decide +kernel) lowS_27
def isoMvS_57:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_57:Lower true dom_57 roots_57 goal_57 5:=lower_iso_b isoMvS_57 (by decide +kernel) lowS_43
def isoMvS_58:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_58:Lower true dom_58 roots_58 goal_58 4:=lower_iso_b isoMvS_58 (by decide +kernel) lowS_27
def isoMvS_77:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_77:Lower true dom_77 roots_77 goal_77 5:=lower_iso_b isoMvS_77 (by decide +kernel) lowS_43
def isoMvS_83:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_83:Lower true dom_83 roots_83 goal_83 4:=lower_iso_b isoMvS_83 (by decide +kernel) lowS_27
def isoMvS_86:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_86:Lower true dom_86 roots_86 goal_86 4:=lower_iso_b isoMvS_86 (by decide +kernel) lowS_27
def isoMvS_99:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_99:Lower true dom_99 roots_99 goal_99 5:=lower_iso_b isoMvS_99 (by decide +kernel) lowS_43
def isoMvS_101:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_101:Lower true dom_101 roots_101 goal_101 5:=lower_iso_b isoMvS_101 (by decide +kernel) lowS_43
def isoMvS_102:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_102:Lower true dom_102 roots_102 goal_102 4:=lower_iso_b isoMvS_102 (by decide +kernel) lowS_27
def isoMvS_113:List (Nat×Nat):=[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_113:Lower true dom_113 roots_113 goal_113 5:=lower_iso_b isoMvS_113 (by decide +kernel) lowS_43
def isoMvS_114:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_114:Lower true dom_114 roots_114 goal_114 4:=lower_iso_b isoMvS_114 (by decide +kernel) lowS_27
def isoMvS_116:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_116:Lower true dom_116 roots_116 goal_116 4:=lower_iso_b isoMvS_116 (by decide +kernel) lowS_27
def isoMvS_141:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_141:Lower true dom_141 roots_141 goal_141 5:=lower_iso_b isoMvS_141 (by decide +kernel) lowS_43
def isoMvS_154:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_154:Lower true dom_154 roots_154 goal_154 4:=lower_iso_b isoMvS_154 (by decide +kernel) lowS_27
def isoMvS_156:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_156:Lower true dom_156 roots_156 goal_156 4:=lower_iso_b isoMvS_156 (by decide +kernel) lowS_27
def isoMvS_166:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_166:Lower true dom_166 roots_166 goal_166 5:=lower_iso_b isoMvS_166 (by decide +kernel) lowS_43
def isoMvS_169:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_169:Lower true dom_169 roots_169 goal_169 7:=lower_iso_b isoMvS_169 (by decide +kernel) lowS_105
def isoMvS_170:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_170:Lower true dom_170 roots_170 goal_170 5:=lower_iso_b isoMvS_170 (by decide +kernel) lowS_163
def isoMvS_178:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_178:Lower true dom_178 roots_178 goal_178 5:=lower_iso_b isoMvS_178 (by decide +kernel) lowS_43
def isoMvS_180:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_180:Lower true dom_180 roots_180 goal_180 4:=lower_iso_b isoMvS_180 (by decide +kernel) lowS_27
def isoMvS_198:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_198:Lower true dom_198 roots_198 goal_198 5:=lower_iso_b isoMvS_198 (by decide +kernel) lowS_43
def isoMvS_201:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96)]
theorem lowS_201:Lower true dom_201 roots_201 goal_201 7:=lower_iso_b isoMvS_201 (by decide +kernel) lowS_105
def isoMvS_210:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_210:Lower true dom_210 roots_210 goal_210 4:=lower_iso_b isoMvS_210 (by decide +kernel) lowS_27
def isoMvS_212:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_212:Lower true dom_212 roots_212 goal_212 5:=lower_iso_b isoMvS_212 (by decide +kernel) lowS_43
def isoMvS_225:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_225:Lower true dom_225 roots_225 goal_225 7:=lower_iso_b isoMvS_225 (by decide +kernel) lowS_105
def isoMvS_226:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_226:Lower true dom_226 roots_226 goal_226 5:=lower_iso_b isoMvS_226 (by decide +kernel) lowS_163
def isoMvS_228:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_228:Lower true dom_228 roots_228 goal_228 5:=lower_iso_b isoMvS_228 (by decide +kernel) lowS_163
def isoMvS_232:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_232:Lower true dom_232 roots_232 goal_232 7:=lower_iso_b isoMvS_232 (by decide +kernel) lowS_105
theorem lowS_31:Lower true dom_31 roots_31 goal_31 5:=lower_slice_b [(0xcccccccc,16,18)] (by decide +kernel) lowS_29
theorem lowS_55:Lower true dom_55 roots_55 goal_55 5:=lower_slice_b [(0xaa00aa00aa00aa,16,17)] (by decide +kernel) lowS_54
theorem lowS_59:Lower true dom_59 roots_59 goal_59 6:=lower_slice_b [(0xc0c0c0c0c0c0c0c,16,18)] (by decide +kernel) lowS_57
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
theorem lowS_62:Lower true dom_62 roots_62 goal_62 5:=lower_slice_b [(0x5050505050505050,16,20)] (by decide +kernel) lowS_58
theorem lowS_103:Lower true dom_103 roots_103 goal_103 6:=lower_slice_b [(0xcc000000cc000000cc000000cc,32,34)] (by decide +kernel) lowS_101
theorem lowS_107:Lower true dom_107 roots_107 goal_107 8:=lower_slice_b [(0xc0c00000c0c00000c0c00000c0c,32,34)] (by decide +kernel) lowS_105
namespace S_118
def pG:List (Nat×Nat):=[(2,18),(2,34),(4,20),(4,68),(6,22),(6,38),(6,70),(16,18),(16,20),(32,34),(32,96),(36,38),(36,52),(36,100),(48,50),(48,52),(48,112),(64,68),(64,96),(66,70),(66,82),(66,98),(80,82),(80,84),(80,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1ffffff
def xsM:=roots_118.map (·&&&dom_118)
def gM:=goal_118&&&dom_118
def NN:Nat→Nat
|4=>2
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x543390e9e0
|5,0=>0x93d491ec6e02a1b
|6,0=>0x93d49
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x550050005500500055005000550050a800a800a800a800a800a800a800a8440044004400000044004400440002a802a802a802a8000000000000000550055000000000055005500000000aa000000aa000000aa000000aa000140014001400140014001400140014220022002200220022002200220022550055005000500000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x43215432154832154372154326543210
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x15405
|5,0=>0x165418a6
|6,0=>0x1b5
|_,_=>0
def wAt:=mkWire dB 9 119 0x7fffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def pmP:Nat→Nat
|0=>0xf8820
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>9
|6,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 2 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_116 4 roots_116 ops++addP pm 1 dom_114 4 roots_114 ops++addP pm 2 dom_54 4 roots_54 ops++addP pm 3 dom_102 4 roots_102 ops++addP pm 4 dom_86 4 roots_86 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_118 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_86 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_116 4 s (0,roots_116.map (·&&&dom_116)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_118 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_116 h
def symsG:List (List (Nat×Nat)):=[[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_118==dom_118)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_118 gM v ys):RunD true dom_118 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_118 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_118 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_118 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_118 roots_118 goal_118 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_118
theorem lowS_118:Lower true dom_118 roots_118 goal_118 7:=S_118.noCircuit
theorem lowS_143:Lower true dom_143 roots_143 goal_143 6:=lower_slice_b [(0xcccc0000000000000000000000000000cccc,128,130)] (by decide +kernel) lowS_141
theorem lowS_167:Lower true dom_167 roots_167 goal_167 6:=lower_slice_b [(0xaa000000aa0000000000000000000000aa000000aa,32,33)] (by decide +kernel) lowS_166
theorem lowS_171:Lower true dom_171 roots_171 goal_171 8:=lower_slice_b [(0xc0c00000c0c000000000000000000000c0c00000c0c,32,34)] (by decide +kernel) lowS_169
theorem lowS_179:Lower true dom_179 roots_179 goal_179 6:=lower_slice_b [(0xa000a000a000a0000000000000000000a000a000a000a,16,17)] (by decide +kernel) lowS_178
def dzo_170_16:=0x50500000505000000000000000000000505000005050000
def gzo_170_16:=0x50500000504000000000000000000000504000004040000
def gsh_170_16:=0x5050000050400000000000000000000050400000404
theorem lowS_zo_170_16_168:Lower true dzo_170_16 roots_170 gzo_170_16 5:=lower_iso_b (d1:=dom_170) (r1:=roots_170) (T1:=gsh_170_16) [(dom_170,16)] (by decide +kernel) (lower_slice_b (T:=gsh_170_16) [(0x4040000040400000000000000000000040400000404,0,2)] (by decide +kernel) lowS_168)
namespace S_186
def pG:List (Nat×Nat):=[(2,18),(2,34),(2,130),(8,40),(8,136),(10,26),(10,42),(10,138),(16,18),(24,26),(24,56),(24,152),(32,34),(32,40),(32,160),(48,50),(48,56),(48,176),(128,130),(128,136),(128,160),(144,146),(144,152),(144,176)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_186.map (·&&&dom_186)
def gM:=goal_186&&&dom_186
def NN:Nat→Nat
|4=>1
|5=>1
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x89320
|5,0=>0x500b6
|6,0=>0x3e5e7
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x141414141414141400000000000000001414141400000002800280028002800000000000000000028002800280028050505050000000000000000000000000505050500000000a0a00000a0a000000000000000000000a0a00000a0a000101010101010101000000000000000001010101010101010028002800280028000000000000000000280028000000050505050505050500000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x8ea1a3a84688
|_=>0
def sO:Nat→Nat→Nat
|4,0=>5
|5,0=>0x56
|6,0=>0xb5
|_,_=>0
def wAt:=mkWire dB 7 187 0x7ffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 9
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x81
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
addP pm 0 dom_178 5 roots_178 ops++addP pm 1 dom_154 4 roots_154 ops++addP pm 2 dzo_170_16 5 roots_170 ops++addP pm 3 dom_170 5 roots_170 ops++addP pm 4 dom_168 4 roots_168 ops++addP pm 5 dom_58 4 roots_58 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_186 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_178 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_170_16_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_58 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_178 5 s (0,roots_178.map (·&&&dom_178)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_186 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_178 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff00000000ffffffff00000000,96)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_186==dom_186)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_186 gM v ys):RunD true dom_186 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_186 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_186 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_186 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_186 roots_186 goal_186 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_186
theorem lowS_186:Lower true dom_186 roots_186 goal_186 7:=S_186.noCircuit
namespace S_230
def pG:List (Nat×Nat):=[(2,34),(2,130),(4,68),(4,132),(6,38),(6,70),(6,134),(32,34),(32,96),(32,160),(36,38),(36,100),(36,164),(64,68),(64,96),(64,192),(66,70),(66,98),(66,194),(128,130),(128,132),(128,160),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffff
def xsM:=roots_230.map (·&&&dom_230)
def gM:=goal_230&&&dom_230
def NN:Nat→Nat
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x3fe0
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x5500000000000000550000000000000055000000000000005500000000a0000000a0000000a0000000a0000000a0000000a0000000a0000000a11000000110000001100000011000000110000001100000011000000112a8000002a80000000000000000000002a8000002a80000000000000005500000055000000550000005500000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x4688
|_=>0
def sO:Nat→Nat→Nat
|6,0=>5
|_,_=>0
def wAt:=mkWire dB 5 231 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffff
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
addP pm 0 dom_228 5 roots_228 ops++addP pm 1 dom_166 5 roots_166 ops++addP pm 2 dom_226 5 roots_226 ops++addP pm 3 dom_198 5 roots_198 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_230 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_228 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_166 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_226 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_198 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_228 5 s (0,roots_228.map (·&&&dom_228)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_230 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_228 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_230==dom_230)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_230 gM v ys):RunD true dom_230 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_230 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_230 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_230 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_230 roots_230 goal_230 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_230
theorem lowS_230:Lower true dom_230 roots_230 goal_230 7:=S_230.noCircuit
namespace S_233
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(1,129),(8,9),(8,40),(8,72),(8,136),(32,33),(32,40),(32,96),(32,160),(64,65),(64,72),(64,96),(64,192),(128,129),(128,136),(128,160),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffff
def xsM:=roots_233.map (·&&&dom_233)
def gM:=goal_233&&&dom_233
def NN:Nat→Nat
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|8,0=>0x80eb7
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x30300000000000003030000000000000303000000000000030300000000c0000000c0000000c0000000c0000000c0000000c0000000c0000000c020200000202000002020000020200000202000002020000020200000202c0c00000c0c000000000000000000000c0c00000c0c00000000000000030300000303000003030000030300000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x4688
|_=>0
def sO:Nat→Nat→Nat
|8,0=>5
|_,_=>0
def wAt:=mkWire dB 5 234 0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
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
|8,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 1 (j%128);fld (pmP (k/32)) 4 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_232 7 roots_232 ops++addP pm 1 dom_169 7 roots_169 ops++addP pm 2 dom_225 7 roots_225 ops++addP pm 3 dom_201 7 roots_201 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_233 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_169 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_225 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_201 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_232 7 s (0,roots_232.map (·&&&dom_232)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_233 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_232 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xffffffff000000000000000000000000ffffffff00000000,32)],[(0xffffffff00000000ffffffff00000000,96)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)],[(0xff00ff00ff00ff00ff00ff00ff00ff00,120)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_233==dom_233)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_233 gM v ys):RunD true dom_233 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_233 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_233 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 5 4=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_233 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_233 roots_233 goal_233 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_233
theorem lowS_233:Lower true dom_233 roots_233 goal_233 9:=S_233.noCircuit
def isoMvS_87:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_87:Lower true dom_87 roots_87 goal_87 5:=lower_iso_b isoMvS_87 (by decide +kernel) lowS_55
def isoMvS_91:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_91:Lower true dom_91 roots_91 goal_91 7:=lower_iso_b isoMvS_91 (by decide +kernel) lowS_61
def isoMvS_94:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_94:Lower true dom_94 roots_94 goal_94 5:=lower_iso_b isoMvS_94 (by decide +kernel) lowS_62
def isoMvS_109:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_109:Lower true dom_109 roots_109 goal_109 8:=lower_iso_b isoMvS_109 (by decide +kernel) lowS_107
def isoMvS_110:List (Nat×Nat):=[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_110:Lower true dom_110 roots_110 goal_110 6:=lower_iso_b isoMvS_110 (by decide +kernel) lowS_103
def isoMvS_115:List (Nat×Nat):=[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)]
theorem lowS_115:Lower true dom_115 roots_115 goal_115 6:=lower_iso_b isoMvS_115 (by decide +kernel) lowS_59
def isoMvS_117:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_117:Lower true dom_117 roots_117 goal_117 6:=lower_iso_b isoMvS_117 (by decide +kernel) lowS_59
def isoMvS_121:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_121:Lower true dom_121 roots_121 goal_121 8:=lower_iso_b isoMvS_121 (by decide +kernel) lowS_107
def isoMvS_122:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_122:Lower true dom_122 roots_122 goal_122 7:=lower_iso_b isoMvS_122 (by decide +kernel) lowS_61
def isoMvS_124:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_124:Lower true dom_124 roots_124 goal_124 7:=lower_iso_b isoMvS_124 (by decide +kernel) lowS_61
def isoMvS_155:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_155:Lower true dom_155 roots_155 goal_155 6:=lower_iso_b isoMvS_155 (by decide +kernel) lowS_59
def isoMvS_157:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_157:Lower true dom_157 roots_157 goal_157 6:=lower_iso_b isoMvS_157 (by decide +kernel) lowS_59
def isoMvS_158:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_158:Lower true dom_158 roots_158 goal_158 5:=lower_iso_b isoMvS_158 (by decide +kernel) lowS_55
def isoMvS_173:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_173:Lower true dom_173 roots_173 goal_173 8:=lower_iso_b isoMvS_173 (by decide +kernel) lowS_107
def isoMvS_174:List (Nat×Nat):=[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_174:Lower true dom_174 roots_174 goal_174 6:=lower_iso_b isoMvS_174 (by decide +kernel) lowS_167
def isoMvS_181:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_181:Lower true dom_181 roots_181 goal_181 6:=lower_iso_b isoMvS_181 (by decide +kernel) lowS_59
def isoMvS_182:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_182:Lower true dom_182 roots_182 goal_182 6:=lower_iso_b isoMvS_182 (by decide +kernel) lowS_59
def isoMvS_185:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_185:Lower true dom_185 roots_185 goal_185 8:=lower_iso_b isoMvS_185 (by decide +kernel) lowS_107
def isoMvS_188:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_188:Lower true dom_188 roots_188 goal_188 7:=lower_iso_b isoMvS_188 (by decide +kernel) lowS_61
def isoMvS_199:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_199:Lower true dom_199 roots_199 goal_199 6:=lower_iso_b isoMvS_199 (by decide +kernel) lowS_167
def isoMvS_203:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96)]
theorem lowS_203:Lower true dom_203 roots_203 goal_203 8:=lower_iso_b isoMvS_203 (by decide +kernel) lowS_107
def isoMvS_211:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)]
theorem lowS_211:Lower true dom_211 roots_211 goal_211 6:=lower_iso_b isoMvS_211 (by decide +kernel) lowS_59
def isoMvS_214:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_214:Lower true dom_214 roots_214 goal_214 6:=lower_iso_b isoMvS_214 (by decide +kernel) lowS_59
def isoMvS_218:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_218:Lower true dom_218 roots_218 goal_218 7:=lower_iso_b isoMvS_218 (by decide +kernel) lowS_61
def isoMvS_229:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_229:Lower true dom_229 roots_229 goal_229 8:=lower_iso_b isoMvS_229 (by decide +kernel) lowS_171
def isoMvS_234:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_234:Lower true dom_234 roots_234 goal_234 8:=lower_iso_b isoMvS_234 (by decide +kernel) lowS_171
def isoMvS_242:List (Nat×Nat):=[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)]
theorem lowS_242:Lower true dom_242 roots_242 goal_242 7:=lower_iso_b isoMvS_242 (by decide +kernel) lowS_186
def isoMvS_244:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_244:Lower true dom_244 roots_244 goal_244 7:=lower_iso_b isoMvS_244 (by decide +kernel) lowS_186
theorem lowS_63:Lower true dom_63 roots_63 goal_63 8:=lower_slice_b [(0xcccccccccccccccc,16,18)] (by decide +kernel) lowS_61
theorem lowS_111:Lower true dom_111 roots_111 goal_111 9:=lower_slice_b [(0xcccc0000cccc0000cccc0000cccc,32,34)] (by decide +kernel) lowS_109
namespace S_119
def pG:List (Nat×Nat):=[(1,17),(1,33),(1,65),(2,18),(2,34),(3,19),(3,35),(3,67),(4,20),(4,68),(5,21),(5,37),(5,69),(6,22),(6,38),(6,70),(7,23),(7,39),(7,71),(16,17),(16,18),(16,20),(32,33),(32,34),(32,96),(36,37),(36,38),(36,52),(36,100),(48,49),(48,50),(48,52),(48,112),(64,65),(64,68),(64,96),(66,67),(66,70),(66,82),(66,98),(80,81),(80,82),(80,84),(80,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_119.map (·&&&dom_119)
def gM:=goal_119&&&dom_119
def NN:Nat→Nat
|4=>5
|5=>16
|6=>36
|7=>9
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xe569173caf617781b0ed099cc
|5,0=>0xe3388e0385ca831bdb6eb02318e3f6572904d66b3b134386a23678530a972848116b960f61e041f9
|6,0=>0xe1441df20ade44bca831a8e489f89f89bed8918a873f784cb0822b46d5a36ce5669b3160f38567cc5625f54d9c5159e4872e458343875a3779f361f734a5a328c43222e320db30d572dcd02b7ce1a8ad1984213eed0b8f306d45
|7,0=>0xe8d9fd5f9e84cb0650b65d38a4ec5b493063e1803a8f4
|8,0=>0xdaa04
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xff00ff0000000000000000ff00ff00ff00000000000000000000f000f000f000f000f000ff00f000f0ff00ff00ff00ff0000000000000000ff00ff0000000000ff00ff0000000000000000ff00ff00ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff0000ff00ff00ff000000ff00ff00ff0000ff00ff00ff00ff00ff000000ff0000ff00ff00f000f000f000f000f000f0aa00aa00aa00aa00aa00aa00aa00aaff000000ff000000ff000000ff0000f000f000f000f000f000f000f000f0cc00cc00cc00cc00cc00cc00cc00ccff00ff00aa00aa00aa00aa00aa00aa0000ff000000ff000000ff00000000
|0,1=>0xff00ff00ff00ff0033003300000000ff00000000000000ff00ff000000000f000f000f000f000f0000000f0000330033003300330000000000000000ff00ff00ff00ff00cc00cc00cc00cc000000000000ff000000000000000000000000ff00ff0000000000f000f0550055005500550055005500550000ff00ff00ff000000ff000000ff00000000000000000000ff00ff000000000f000f000f000f000f000f000f0000ff00ff000000000000000000000000ff00ff00ff00ff00ff00ff0000000000000000ff00ff00ff00ff000000000f0000000f000f000f0000000f00000000000000000000ff00ff00ff0000
|0,2=>0xf000f000f000f0000000000000000cc00ff00cc00ff00cc00cc00cc00cc00000000cc00cc00cc00cc00cc00cc330033003300330033003300000000ff00ff00cc00cc00ff00ff00cc00ccff000000ff000000ff00ff00ff0000000000000f000f0000000000000000f000f000ff00ff00f000f000f000f000000000ff000000ff000000ff00000000ff000000ff0000000000000000ff00ff000000ff00ff00ff00000000cc00cc0000000000ff00ff00000000ff003300ff003300ff000000ff0000ff00ff00ff00ff00ff00ff00cc00ccff00ff0033003300ff00ff00000000
|_,_=>0
def sP:Nat→Nat
|0=>0x31a2c40c21593040c214050b10309830b5c308530b1c41821531030814840c214b1021553091030855081c30855134840c214810608530b1021513101030853cb1c308538b10d08530b1c40c204a1030852440c20481c30812071821440c2040
|1=>0xa4b10308530b1030853282c49c30853092c40c214c2e60c214c90b10308530b8c40c214c20b1c308530b8830853212c40c214c2c40c214c3a02c40c214c2c40c215f30b7840c214c2c710215d30b1060853132c40c215c4cb1036c214b103085
|2=>0x31c2c40db08530b5840c214c2c40c214c50b5871030855840c214f2c40c214030b5c308530b10215d30b103b4531310308550b5c40c214c40b1030853132c40c214c2c40ec14c2c40c216b30b5840c2165a8b1036c530b103081308103085314
|3=>0x2c40c214c2c40c214c94b10308532e4cb10308532a2c40c214c2c710308530b103085
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x14507a82940aa005
|5,0=>0x38b1ad8cac5f62d295549ec49621b0f586ec31615b09583ec196
|6,0=>0xb13d71aaaf4f6a4b50da7ad36797bca1e44d1b78a3c35e0ed0077cbbc9dd6ee476f335dda0ec9761b2f1d6aeae753ba81d32e936463a15cfce777
|7,0=>0x1a17cd3e4df18f857bf3dddee0f697
|8,0=>0x1a86
|_,_=>0
def wAt:=mkWire dB 47 120 0xffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x10c83322cc422d10c423208c4c2e2cc0c2e2cc8c2e1144b301c3c4310a544322cc0b3130882532cc0c2c30b93112cc44532cc0b952dcc47108c870f10c435130b0b31308d63d2cc8c2e
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x30000000000000000000000000
|6,0=>0x805e2001c26898258800544004c800000000012144400000f2348c12c4002480000000000001c852000410c400
|7,0=>0x291a0671986519063188611
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 10
def pmP:Nat→Nat
|0=>0xf55a7da5d7d16f96f56d53d525d24018118008004404104003002001400e00d009008002001000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x104000000000000
|6,0=>0x514010848050c20020ca6800f5b0ee0800000205025a0
|7,0=>0x12cc6b29d2f8
|8,0=>0x16
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 12 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_118 7 roots_118 ops++addP pm 1 dom_86 4 roots_86 ops++addP pm 2 dom_55 5 roots_55 ops++addP pm 3 dom_87 5 roots_87 ops++addP pm 4 dom_117 6 roots_117 ops++addP pm 5 dom_53 4 roots_53 ops++addP pm 6 dom_103 6 roots_103 ops++addP pm 7 dom_101 5 roots_101 ops++addP pm 8 dom_99 5 roots_99 ops++addP pm 9 dom_115 6 roots_115 ops++addP pm 10 dom_113 5 roots_113 ops++addP pm 11 dom_83 4 roots_83 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_119 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_53 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_101 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_83 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_118 7 s (0,roots_118.map (·&&&dom_118)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_119 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_118 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_119==dom_119)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_119 gM v ys):RunD true dom_119 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_119 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 5 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 36 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 36 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 9 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_119 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_119 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_119 roots_119 goal_119 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_119
theorem lowS_119:Lower true dom_119 roots_119 goal_119 9:=S_119.noCircuit
theorem lowS_123:Lower true dom_123 roots_123 goal_123 9:=lower_slice_b [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,16,18)] (by decide +kernel) lowS_121
def dzo_110_16:=0x55550000555500005555000055550000
def gzo_110_16:=0x55550000555400005554000054540000
def gsh_110_16:=0x5555000055540000555400005454
theorem lowS_zo_110_16_104:Lower true dzo_110_16 roots_110 gzo_110_16 6:=lower_iso_b (d1:=dom_110) (r1:=roots_110) (T1:=gsh_110_16) [(dom_110,16)] (by decide +kernel) (lower_slice_b (T:=gsh_110_16) [(0x4444000044440000444400004444,0,2),(0x5050000050500000505000005050,0,4)] (by decide +kernel) lowS_104)
namespace S_126
def pG:List (Nat×Nat):=[(2,18),(2,34),(4,20),(4,68),(6,22),(6,38),(6,70),(8,40),(8,72),(10,26),(10,42),(10,74),(12,28),(12,44),(12,76),(14,30),(14,46),(14,78),(16,18),(16,20),(24,26),(24,28),(24,56),(24,88),(32,34),(32,40),(32,96),(36,38),(36,44),(36,52),(36,100),(48,50),(48,52),(48,56),(48,112),(64,68),(64,72),(64,96),(66,70),(66,74),(66,82),(66,98),(80,82),(80,84),(80,88),(80,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffffff
def xsM:=roots_126.map (·&&&dom_126)
def gM:=goal_126&&&dom_126
def NN:Nat→Nat
|4=>3
|5=>5
|6=>9
|7=>3
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xc8ee58477339953
|5,0=>0xfea4bd83d1cc21c9f3074b3b7
|6,0=>0xf2893e6db0cc21ca0e9f972fa6cad8526a9223f2158e9
|7,0=>0xe6db02a6ae296e4
|8,0=>0x464f4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaaaaaaaa0000000000000001555400015554000155540002aaaaaaaa2222222222222222222222255555555555500005555000055550000aaaaaaaa00000000000000000000000154015401540154015401540154015402aaaaaaa800000002aaaaaaa8000000055555555555555550000000000000000aaaaaaaaaa00aa00aa00aa00aa00aa000000000155555555555555540000000002a802a802a802a802a802a8000000055555555555555555555555500000000aaaa0000aaaa0000aaaa0000aaaa000141414141414141414141414141414142222222222222222222222222222222200000000005500550055005500000000
|0,1=>0x555555550000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x123508282246a1050978d420a123508285bc6a1060448d420a123104a84b9420a123509a822462095041a8415a46710509628414186a10483104ab48c412a0861a84120ce209862080c3104a418820
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x2942a805
|5,0=>0x26540c698a30f5
|6,0=>0x5d6acf41a534467aedd98b2b6
|7,0=>0x1c5f53e37
|8,0=>0x786
|_,_=>0
def wAt:=mkWire dB 17 127 0x7fffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x4a14264a07a14264a14a04a122f4a04a122f4a04a14a04a1
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x53000004602
|6,0=>0x59000000050a080000
|7,0=>0x3c5c2d1
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 9
def pmP:Nat→Nat
|0=>0xffaca0f0c10100
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x1009
|6,0=>0x5602328
|7,0=>0x1ff
|8,0=>6
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 7 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_124 7 roots_124 ops++addP pm 1 dom_118 7 roots_118 ops++addP pm 2 dom_94 5 roots_94 ops++addP pm 3 dom_122 7 roots_122 ops++addP pm 4 dom_62 5 roots_62 ops++addP pm 5 dom_110 6 roots_110 ops++addP pm 6 dzo_110_16 6 roots_110 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_126 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_110_16_104 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_124 7 s (0,roots_124.map (·&&&dom_124)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_126 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_124 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_126==dom_126)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_126 gM v ys):RunD true dom_126 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_126 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 5 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 9 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 3 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_126 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_126 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_126 roots_126 goal_126 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_126
theorem lowS_126:Lower true dom_126 roots_126 goal_126 9:=S_126.noCircuit
theorem lowS_159:Lower true dom_159 roots_159 goal_159 7:=lower_slice_b [(0xcccccccc000000000000000000000000cccccccc,16,18)] (by decide +kernel) lowS_157
theorem lowS_175:Lower true dom_175 roots_175 goal_175 9:=lower_slice_b [(0xcccc0000cccc00000000000000000000cccc0000cccc,32,34)] (by decide +kernel) lowS_173
theorem lowS_183:Lower true dom_183 roots_183 goal_183 7:=lower_slice_b [(0xaa00aa00aa00aa000000000000000000aa00aa00aa00aa,16,17)] (by decide +kernel) lowS_182
theorem lowS_187:Lower true dom_187 roots_187 goal_187 9:=lower_slice_b [(0xc0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0c0c,16,18)] (by decide +kernel) lowS_185
def dzo_174_16:=0x555500005555000000000000000000005555000055550000
def gzo_174_16:=0x555500005554000000000000000000005554000054540000
def gsh_174_16:=0x55550000555400000000000000000000555400005454
theorem lowS_zo_174_16_168:Lower true dzo_174_16 roots_174 gzo_174_16 6:=lower_iso_b (d1:=dom_174) (r1:=roots_174) (T1:=gsh_174_16) [(dom_174,16)] (by decide +kernel) (lower_slice_b (T:=gsh_174_16) [(0x44440000444400000000000000000000444400004444,0,2),(0x50500000505000000000000000000000505000005050,0,4)] (by decide +kernel) lowS_168)
namespace S_190
def pG:List (Nat×Nat):=[(2,18),(2,34),(2,130),(4,20),(4,132),(6,22),(6,38),(6,134),(8,40),(8,136),(10,26),(10,42),(10,138),(12,28),(12,44),(12,140),(14,30),(14,46),(14,142),(16,18),(16,20),(24,26),(24,28),(24,56),(24,152),(32,34),(32,40),(32,160),(36,38),(36,44),(36,52),(36,164),(48,50),(48,52),(48,56),(48,176),(128,130),(128,132),(128,136),(128,160),(144,146),(144,148),(144,152),(144,176)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_190.map (·&&&dom_190)
def gM:=goal_190&&&dom_190
def NN:Nat→Nat
|4=>5
|5=>15
|6=>37
|7=>10
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xd4035bad953e56e3d0dd390ae
|5,0=>0xf3ed7d7b3ec8d97c2137be15bb9effb3d27a8754a10e78ddf76208351f4f3cbb72f8f11b01b
|6,0=>0xf68b6f3ed7e8fd1e14b8ddffdda8f8da4f4d5905d075fc241ac19bfbe4b4af12aadc55a4025a24aaa1bc29de4d9b9ea99370916bb7fa627a28a73282704ff6998f68c5665b8c63cae61feb5deea1e3eb0e26c0ddc00b95d08dab04a08
|7,0=>0xddffddbb9abda08b7830a2c2e8d12586ebf7660753afd148d0
|8,0=>0xf79e0
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaa00aa00aa00aa00000000000000000000000000000000000000000000000000000000000000015555555554015402aaaaaaaaaaaaaaa80000000000000002aaa80002aaa8000550055005500550000000000000000005500550055005500aaaaaaaa000000000000000000000000aaaaaaaa00000001555155515551555000000000000000015551555151515152aa22aa22aa22aa200000000000000002aa22aa22222222255555555555555550000000000000000000000000000000000000000aaaaaaaa0000000000000000aaaaaaaa000000011111111111111110000000000000000111111111111111100000000002a802a8000000000000000002a802a80000000555555555555555500000000000000005555555500000000aaaa0000aaaa00000000000000000000aaaa0000aaaa0001414141414141414000000000000000014141414141414142aaaaaaaa222222200000000000000002222222222222222005500550055005500000000000000000055005500000000
|0,1=>0xaaaa00000000000000000000aaaa0000aaaa000155540001555555540000000000000001555400015554000000000002aaaaaaa8000000000000000000000000000000055005500550055000000000000000000555555555500550000000000aa00aa000000000000000000aa00aa00aa00aa00000000000000000000000000000000015555555400000002a802a800000000000000000000000002aaaaaaa80000000555555550055005500000000000000005555555500000000aa00aa00aa00aa000000000000000000aa00aa000000000000000000000000000000000000000001555400015554000002a802a800000000000000000000000002a802a80000000555555555500550000000000000000005500550055005500aaaaaaaaaa00aa000000000000000000aaaaaaaaaa00aa01555555555555555400000000000000015401540154015402aaaaaaa8000000000000000000000000000000000000000555555555555555500000000000000000055005500000000
|0,2=>0x2aaaaaaaaaaa800000000000000000002aaa80002aaa8000000000000000000000000000000000000055005500000000aaaa00aaaaaa00aa0000000000000000aaaa0000aaaa0001555555554141414000000000000000014141414141414142aaa80000000000000000000000000002aaa80002aaa8000555555555555555500000000000000005555555555005500
|_,_=>0
def sP:Nat→Nat
|0=>0x8620b64330218810b0d708620b0c21802070cc0866030865482c32422041c330218b34218020b5821802042c32422040c21953c40d40861030860114c40d208610330204b0c21903ce2cd3021870c21802c32892070c21851030861440c2040
|1=>0xcc0860082da34c0862042d63021882da58c08620b84c0862202c330218810330219520b7cc0862132c34821882de30218868330219d4cb34c0862040cc08645c2c33021882c36c21882c33020482c35c21882c33021902131033021884da0cc
|2=>0xcc0862112c348c08620b0cc08620f2c330219520b94c08620b0c218020b0cc08690838b0cc0862042c33021882cd3021952042c308600860b0cc0862042c348c0862c30865483cb8cc08620b0cc88620b0d40862042c330218f10b34c08620b
|3=>0xb0cc0862042c33021882da0cc08620b34c08620b58c0862132c33021882c330218874b
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x14507a82940aa005
|5,0=>0x1a58c8a5e62ca94d89ac47620b0ed86ca30615309543ec196
|6,0=>0x15f6acb549e96f4479ebcd9e5ef28790bc6da2ad0f6843c05df4ef37763b95dbecd8768bb2d988ebe65c32c5d56ca474f3261924c8b74239f5cece6f7
|7,0=>0x344f9b7cab63db10f817bd3dcded8f657
|8,0=>0x1a96
|_,_=>0
def wAt:=mkWire dB 38 191 0x7fffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xb212c8c3210c8cb312c88b203084c222ccc3452c804332c843212c84b210cf4c220914b203114b202c84b210ddcb222c843472c803752c88b232c883212c84b20311cb201914b2010c0b212c84b232cfc4472c84b205c644302c84c452c84b202c846452c84b20
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x28c001cc00000000000010c000c40300000
|6,0=>0x2f2b480000000b06b1002a10028298a428c4000000088400808007c5d2001b2649815880050922408003c4e134400
|7,0=>0xe8791e0771d8751d0731c8711
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 10
def pmP:Nat→Nat
|0=>0xf77d5ef7b5e777dc5705c04c6304a128090220801404d1203d0b0180400e0240800400
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x60388001006031000
|6,0=>0x130800929406056317340c7b2605cc548994084900315c2
|7,0=>0x35abe2dbde716
|8,0=>0x15
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 10 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_188 7 roots_188 ops++addP pm 1 dom_156 4 roots_156 ops++addP pm 2 dom_186 7 roots_186 ops++addP pm 3 dom_54 4 roots_54 ops++addP pm 4 dom_182 6 roots_182 ops++addP pm 5 dom_166 5 roots_166 ops++addP pm 6 dom_158 5 roots_158 ops++addP pm 7 dom_62 5 roots_62 ops++addP pm 8 dzo_174_16 6 roots_174 ops++addP pm 9 dom_174 6 roots_174 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_190 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_188 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_156 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_166 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_174_16_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_174 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_188 7 s (0,roots_188.map (·&&&dom_188)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_190 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_188 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_190 gM v ys):RunD true dom_190 gM v (ori ys):=h
def Z (s:Nat):=barP dom_190 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 5 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 15 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 37 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 37 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 10 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_190 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_190 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_190 roots_190 goal_190 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_190
theorem lowS_190:Lower true dom_190 roots_190 goal_190 9:=S_190.noCircuit
theorem lowS_231:Lower true dom_231 roots_231 goal_231 9:=lower_slice_b [(0xcc000000cc000000cc000000cc000000cc000000cc000000cc000000cc,32,34)] (by decide +kernel) lowS_229
theorem lowS_235:Lower true dom_235 roots_235 goal_235 10:=lower_slice_b [(0xc0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c,32,34)] (by decide +kernel) lowS_233
def dzo_224_16:=0x1000000010000000100000001000000010000000100000001000000010000
def gzo_224_16:=0x1000000010000000100000000000000010000000000000000000000000000
def gsh_224_16:=0x100000001000000010000000000000001000000000000000000000000
theorem lowS_zo_224_16_224:Lower true dzo_224_16 roots_224 gzo_224_16 4:=lower_iso_b (d1:=dom_224) (r1:=roots_224) (T1:=gsh_224_16) [(dom_224,16)] (by decide +kernel) (lower_slice_b (T:=gsh_224_16) [] (by decide +kernel) lowS_224)
def dzo_230_16:=0x55000000550000005500000055000000550000005500000055000000550000
def gzo_230_16:=0x55000000550000005500000054000000550000005400000054000000540000
def gsh_230_16:=0x5500000055000000550000005400000055000000540000005400000054
theorem lowS_zo_230_16_224:Lower true dzo_230_16 roots_230 gzo_230_16 6:=lower_iso_b (d1:=dom_230) (r1:=roots_230) (T1:=gsh_230_16) [(dom_230,16)] (by decide +kernel) (lower_slice_b (T:=gsh_230_16) [(0x4400000044000000440000004400000044000000440000004400000044,0,2),(0x5000000050000000500000005000000050000000500000005000000050,0,4)] (by decide +kernel) lowS_224)
def dzo_228_16:=0x11000000110000001100000011000000110000001100000011000000110000
def gzo_228_16:=0x11000000110000001100000010000000110000001000000010000000100000
def gsh_228_16:=0x1100000011000000110000001000000011000000100000001000000010
theorem lowS_zo_228_16_224:Lower true dzo_228_16 roots_228 gzo_228_16 5:=lower_iso_b (d1:=dom_228) (r1:=roots_228) (T1:=gsh_228_16) [(dom_228,16)] (by decide +kernel) (lower_slice_b (T:=gsh_228_16) [(0x1000000010000000100000001000000010000000100000001000000010,0,4)] (by decide +kernel) lowS_224)
def dzo_226_16:=0x5000000050000000500000005000000050000000500000005000000050000
def gzo_226_16:=0x5000000050000000500000004000000050000000400000004000000040000
def gsh_226_16:=0x500000005000000050000000400000005000000040000000400000004
theorem lowS_zo_226_16_224:Lower true dzo_226_16 roots_226 gzo_226_16 5:=lower_iso_b (d1:=dom_226) (r1:=roots_226) (T1:=gsh_226_16) [(dom_226,16)] (by decide +kernel) (lower_slice_b (T:=gsh_226_16) [(0x400000004000000040000000400000004000000040000000400000004,0,2)] (by decide +kernel) lowS_224)
namespace S_246
def pG:List (Nat×Nat):=[(2,18),(2,34),(2,130),(4,20),(4,68),(4,132),(6,22),(6,38),(6,70),(6,134),(16,18),(16,20),(32,34),(32,96),(32,160),(36,38),(36,52),(36,100),(36,164),(48,50),(48,52),(48,112),(48,176),(64,68),(64,96),(64,192),(66,70),(66,82),(66,98),(66,194),(80,82),(80,84),(80,112),(80,208),(128,130),(128,132),(128,160),(128,192),(144,146),(144,148),(144,176),(144,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_246.map (·&&&dom_246)
def gM:=goal_246&&&dom_246
def NN:Nat→Nat
|4=>11
|5=>96
|6=>286
|7=>130
|8=>18
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xdba15b1c27a076d6c0d166a7b4e3bb3fee936dd8331533065109c49
|5,0=>0xfe5fafb60ae5a91e12a7df786df5eed2e84d0347c1037c0362bdd65bc7ecb7abdb6950add3eacf54a9f409c36396acf94e938fe708e3368bbd58a1c889ed77c05c7ae6274a5c74084720436ff666f83a6eca26d2456cfa96b18e6b060699a866c58645656366e600425f40a5a09057aaa543f0514644f8204648745e2444f20446e441e6d3bedf39efd3610b3568c3329731e283195b30c062f9e62d4df2d1ed2c6e72b5b028a0926d662696f24d3d24a432450d23e5c2341722c0820b302072e1e1dc1cebf18ed2175f616a8015dc212fe811a9d0d06e0c78d0b29509e6f0968607d1d07cf6076110141c011db00325
|6,0=>0x40eed40b913d60c3c5123c1be3be273afa83ae8539efd38867385ae3635435e4234c7f342bc3397c3273931e2831d7a30fe330576300652fe932f3be2d7a02d5302d46a2d15e2c9b22beb32bd952af532af222aa1d2a5ee294c82916028a9d28556281a326cc325ba92530824e642455f243e423fdc23a802365822c5822a0222951228a42259a222e9219c220b301f8d01e0f61dfc61d93c1d8fd1d7ab1d0c71d04c1cf7d1cf0e1c3571be821b1f01a69f1a49d1a16619cca1920118a64187831850216d59162881626215983159691548b14891147c713cad13c18135f51307712fe81133310c41105560fb9c0f93b0e15b0e0a30dd640d8cf0d7f30d7600d6460d0ac0c1260b5e80a656090ac08aca07b5807a130791d0715f0711206d9e06d72061ed055ee03bc2025a40235e01f070162500ef900dad00d7600d740020d
|6,1=>0xc013fbe64bbc76bbc2f9b9d52b1004b070aaffeeaf455ae5ceadd3ead9b6ad5b4acfcdacc41ab37daa664a5ddca4a28a3815a2e3da0dfc9e5f39b9c299ec497a2f965b195328909998dace8c2ac8b1698afff8a6d189b538959d8933d88e498830786fa0869d48649885a2784e97831a981e1c7cf737ba5c7998f78d8a78020778b173fc67306771603714f76fd1c6f7c16f5c86eaaa6ea756e3c46e1156c16e6c0006ba6c6b6306a8486a22668927687c36867367b7367b24675386562963bec6295962297616fb5f2345f1d65e9775e7b15dc035bc7e5b5cb59f535983f597a05843358431575a557571574245703656622549a5546315340352c15521a6518aa5151b512cb509c3505fa501934ecda4eca14dc704dbbb4ce8c4c87c4c7a84c4b54b2ca4a33149ce44999c494264838a4600945d7c447cb4428843feb41384
|6,2=>0xfc4d5f933cf5bddf2fc9f0013eec1fed53ee9969e741ee221ce12a7df12fdcaf7da55bd83f7d6edcd6876d023ecf7a7c9c47c944ec6e1dc59dbc5363c47fcc3d6bc21eac170dc0b19c04e0
|7,0=>0xeaa89e9d6be2c2bdcaf7da3f5d0f81c5a75bcec9b8b0ab7faab761ead9b6a5ddca4bc0a01179e6cb9e21c9c6809777e95f0c9529694284925488c57589b0e89966884398553484b538315c80cea7ca157c98e7c5107b0df7a23f7820d7605e75e7c7523f728737246071908710d86dc576c7626b8e769fc569bea65d69656f164c8c622c062297621ac61e03610bc60f0a605325d7d65b5cb58e39583ba55616554e7539c752e714e3004e0d24d7ca4c6f54ae514a40d498a9478e74322e417f8408153f3873f0423f03b3e00c3c44c3b3e83aa513a86d39eee39722371cd3558034bf232ae23271731d2930a2e2e8142cb562bd142a93629424289582886226e3e223b321975209d51f2d21e4421e42c1e12f1bf59174c812a80112dd10f5e0f4bc0f0d20efb70ee660a08e08ca906f0d05a6403a5303100024f2017b300ada
|7,1=>0xfaf7bf0013
|8,0=>0xbdea893f79839c67fdf67c5106eb085b99642c424126a3f43d27e52207031e4f817b54167391122d0d67003b70
|9,0=>0x3f43d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaa00aa00aa00aa00a000a000a000a000aa00aa00aa00aa00a000a000a000a154015401400140015401540140014001540154014001400000000000000002a802a802a002a002a802a802a002a002a802a802a002a002200220022002255005500500050005500550050005000550055005000500055005500500050aa00aa00aa00aa00aa00aa0000000000a000a000a000a000a000a00000000154015401540154015401540154015401540154015401540000000000000002a802a802a802a802a802a802a802a802a802a80000000002a802a8000000055000000550000005500000055000000550000005500000055000000550000a800a800a800a800a800a800a800a800a800a800a800a800a800a800a800a954015401400140015401540140014001100110010001000110011001000102a802a802a802a8000000000000000002a802a802a802a80000000000000000000000000000000000000000000000055005500550055005500550000000000000000aa00aa00aa00aa000000000000000000aa00aa00aa00aa0000000154015401540154015401540154015401540000015400000154000001540002800280028002800280028002800280028002800280028002800280028002844004400440044004400440044004400440044004400440044004400440044
|0,1=>0xa000a000a000a000a000a000a000a000a000a000a000a000a000a000a000140014001400140015401540140014001400140014001400154015401400142a802a800000000000000000000000002a802a80000000000000000000000055005500550055005500550050005000550055005500550055005500500050aa00aa00aa00aa00aa00aa00aa00aa00a000a000a000a000a000a000a000a000000000000000015401540154015400000000000000000154015401500152a802a80000000002a802a80000000002a802a80000000002a802a80000000550055000000000055005500550055005500550000000000550055005000500000000000000000aa00aa00000000000000000000000000aa00aa0000000154015401540154015401540154015401540154015400000154000001540002a802a802800280022002200200020002a802a80280028002200220020002055005500550055005500550055005500000000000000000000000000000000aa00aa00aa00aa00aa00aa0000000000aa00aa00aa00aa00aa00aa0000000154015401540154015401540154015401100110011001100110011001100112a802a802a802a8022002200220022002a802a80000000002200220000000000000000000000000000000000000000000000005500550055005500000000
|0,2=>0xaa00aa00aa00aa000000000000000000880088008800895401540154015401540110015401100154015401540000015401100154000000000000000000000000000000000002a802a80028002802a802a80000000550055004400440055005500550055005500000044000000550000005500000000000000000000aa00aa00a000a0000000000000000000aa00aa00a000a000000001540154000000000110011000000000015401540000000001100110880088008800880000000000000000008800880088008800000000000000055005500550055005500550054005400000000000000000000000000000000aa00aa00aa00aa000000000000000000aa00aa00a000a0000000000000000154015400000000015401540000000001540154000000000140014000000002a802a80220022002a802a80220022002a802a80220022002a802a8022002255005500550055005500550055005500550055005500550044004400440044000000008a008a00000000008a008a00000000008a008a000000000088008800000000000000000000000000000000440044004400440044004400000002a802a802a802a802a802a802a802a80000000002a802a802a802a8000000055005500550055005500550055005500110011001100110000000000000000
|0,3=>0xaa00aa00aa00aa000000000000000000a200a200a000a00000000000000001540154015401540154015400000000015401540154015401400140000000000000000000000002a802a8000000000000000002a802a802a802a8000000055005500550055004400440044004400550055004400440044004400440044aa00aa00aa00aa000000000000000000aa00aa00a800a80000000000000000540054001400140044004400000000005400540014001400440044000000000000000000000002a802a802a802a8000000000000000002a802a8028002855005500550055005400540054005400550055005000500054005400500050aa00aa0088008800aa00aa0088008800aa00aa00880088008800880088008954015401540154015401540154015401540014015400000154001401540002a802a802a802a802a802a802a802a802a802a8000002a80000000000000004400440055005500440044004400440044004400550055004400440044004400000000aa00aa0000000000aa00aa0000000000880088000000000088008954015401540154011001100110011001540154015401540110011001100112a802a802a802a802a802a802a802a8022000000220000002a8000002a800055005500500050005000500050005000550055005000500050005500500050
|0,4=>0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00a000a000aa00aa00a000a154015400440044015401540000000001540154004400440154015400000002a802a802a802a802a802a80220022002a802a802a802a802a802a80220022450045000000000045004500000000004500450000000000440044000000000a0000000a000a000a0000000a000a000a0000000a000a000a0000000a00015400000154000001540000015400000154000001540044015400000154000000000002a802a80000000002a802a80000000002a802a8000000000220022050005000500050005000500050005000500050000000000050005000000002200220022002200220022000000000022002200220022002200220000000014001400140014000000000000000000140014001400140000000000000002a802a80028002802a802a80000000002a802a80028002802a802a800000000000000000000000550055005500550000000000000000005100510050005000000000000000000000000000000000aa00aa00aa00aa00aa00aa00a000a154015401540154015401540154015401540154015401540154015400000002a802a802a802a802a802a802a802a802a802a80000000000000000000000044004400550055004400440055005500400040005000500040004000500050
|0,5=>0xaa00aa00aa00aa000000000000000000aa00aa00aa00aa00aa00aa00a000a014001400140014001400140000000000140014001400140014001400000002a802a802a802a802a802a802a802a80028002800280028000000000000000000000000000000000000000000000005500550055005500550055005400540000000008000800000000000800080000000000080008008800880088008800000001540154015401540154015400000000015401540154015400000002a8000002a8000002a8002802a8002802a8000002a8000002a8002802a80005000500050005000500050005000500055005500550055005500550050005000000000000000000000000000000000aa00aa0022002200aa00aa000000015401540154000001540000015400000154015401540000015400140154000000000002a802a800000000000000000000000002a802a8000000000000000550055005500550055005500550055000000000000000000000000005500000000000000000000aa00aa00aa00aa000000000000000000a000a000a000a15401540154015401500150015001500154015401540154015001500150015280028002800280028002800280028002a802a80280028002a802a8028002855005500550055005500550055005500550000005500110055000000550000
|0,6=>0xa8000000a8000000a8000000a8000000a8000000a8000000a8000000a80001540154015401540154015401540154015000000150000001500000015000008800880088008800880088008800880080008000800080008000800080008550055005500550011001100110011005500550055005500100010001000100a000a000a000a0008000800080008000a000a000a000a00080008000800080000000154015401540154015401540000000001540000015400000154000000000000000000000000000000000002a802a802a802a800880088000000000000000000000000000000000000000550055000000000055005500000000aa00aa00aa00aa000000000000000000aa00aa00aa00aa00aa00aa0000000000000001540154000000000154015400000000015401540000000000000002a802a802a802a8000000000000000002a802a80220022000000000000000055005500550055005500550055005500500050000000000055005500000000aa00aa00000000000000000000000000aa00aa00220022000000000000000154015401540154000000000000000001540154000000000000000000000002a802a802a802a802a8000002a8000002a802a802a8000002a8000002a800055005500550055005500550055005500000000000000000005000500000000
|0,7=>0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa0022002200aa00aa0000000014001400000000001400140000000000140014000000000014001400000002a8002802a8000002a8002802a8000002a8002802a8000002a8002802a80005500550055005500500050005000500055005500500050005000500050005000000000000000000000000000000000aa00aa00a000a000aa00aa00a000a00000000000000000000000000000000140014000000000015401540000000088008800880088008800880088008800880088000000000088008800000005500550055005500000000005500550055005500550055000000000055000000000000aa00aa0000000000aa00aa0000000000aa00aa0000000000aa000000015000000150000001500000015000000150000001500000015000000152280228022802280228022802200220022802280228022802280228022002200000000000000000000000000000000110011001100110000000000000000aa00aa00aa00aa00aa00aa0000000000aa00aa0088008800aa00aa0000000114011401140114011001100110011001140114011401140110011001100110880088008800880088008800880088008800880088008800800080008000800000000000000000000000055005500000000000000000000000000550000
|0,8=>0x220022002200220022002200220022002200220022002200000000000000015400440154004401540044015400440154004401540044015400000154000000000000000000000000000000000002a802a8000002a802a802a8000000055000000550000005500050055000000550000005500000055000500550000aa00aa00aa00aa00aa00aa00aa000000aa00aa00aa00aa00aa00aa00aa000000000000000000000000000000000001540154015401540154015401540002a802a802a802a802a802a802a802a80028002800000000002800280000000550055005500550055005500550055005500550055005500550000005500000a000a000a000a000a000a000a000a000a000a000a000a000a0000000a000044004400000000004400440000000000440044000000000044004400000000000000000000000000000000000000002800280000000000280028000000055000000550000005500000055000000500000005500000050000000550000a000a00000000000aa00aa0000000000a000a00000000000aa00aa00000001140114011401140114011401140114011401140110011001140114011001100002a800000000000002a800000000000002a800000000000002a8000000050005500500050005000550050005000500055005000500050005500500050
|0,9=>0xaa000000aa000000aa000000014001400000000001400140000000000140014000000000015401540000000220022002a802a80220022002a802a80220022002a002a00220022002a002a00000000050005000000000005000500000000000500050000000000000000aa000000aa00aa00aa000000aa00aa00aa000000aa00aa00aa000000aa000154015401540154015401540154015401540154015401540000015400000002a802a80000000002a802a80000000002a802a80000000000000000000000044004400440044005500550055005500440000004400000055000000550000aa00aa00a800a800aa00aa00a800a800aa00aa00a800a800aa00aa00a800a940014001540154014001400154015401400140015001500140014001500152a8000002a8000002a8000002a8000002a802a802a802a802a802a802a8000500050005000500055005500550055005000500000000000550055000000002200220020002000220022002000200022002200200020002200220020002154015401540154004400440040004001540154015401540044004400400042a802a80000000002a802a800000000028002800000000002800280000000005000500050005000000000000000000050005000500050005000500000000
|0,10=>0xa0000000a0000000a0000000a0000000a0000000aa000000a0000000aa000110011001100110015401540154015401100110011001100154015401100112880288028802880288028802880288028802880280028002880288028002855005500550055005500550055005500540054005400540054005400540054aa00aa00aa00aa000a000a000a000a00aa00aa00aa00aa000a000a000000015401540154015401540154015401540154015401540000015401540154000088008800880088008800880088008800880088008800000088008800880005500550055005500550055005500550011001100000000001100110000000022002200220022002200220022002200220022002000200022002200200021540154015401540154015401500150015401540154015401540154015001500000000000000002a802a802a802a8000000000000000002a802a80220022000000000000000005000500050005000000000000000000040004000400040000000022002200000000000000000000000000220022000000000000000014001400140014000000000000000001540154001400140154015400000002a802a80000000002a802a80000000002a802a80088008802a802a8000000055005500550055005000500050005000550055005500550055005500500050
|0,11=>0xaa00aa00aa00aa00aa00aa00aa00aa00aa002200aa002200aa000000aa000000015400000154000000000000000000000154000001540000000000000002a802a802a802a802a802a802a802a8000002a8000002a80000000000000000500050005000500050005000400040005000500050005000500050004000400000000aa00aa0000000000aa00aa0000000000a800a80000000000a800a800000000000000001400140000000000000000000000000014001400000000000000000000000000000000000000000000000000000002a802a800000000000000000000000000000000000000000000000550055000000000044004400000000aa00aa0000000000aa00aa0000000000a000a00000000000a000a000000001540154000000000154015400000000015400000000000001540002a802a800000000000000000000000002a802a8000002a8000000000000000440000004400000055000000550000004400000044000000550000005500008800880088008800880088008800880088008800aa00aa008800880088008954015401540154015401540154015401400140014001400154015401400142a802a802a802a802a802a802a802a802a802a802a802a802a002a002a002a55005500550055005500550055005500000000005500550000000000000000
|0,12=>0xaa000000aa00000000000000aa000000aa000000aa000154015400000000015401540000000001540000000000000154000000000002a802a802a802a802a802a80000000002a802a802a802a802a80000000000055005500550055005500550055005500550055005500550050005000500050aa00aa00aa00aa00aa00aa00aa00aa00aa00aa000a000a00aa00aa0000000110011001100110015401540150015001100110011001100154015401500150000000000000000028002800280028000000000000000000280028000000001000100010001000100010000000000010001000100010001000100000000020002000200020002000200020002000200020000000000020002000000015401540154015401540154015401540144014401400140014401440140014000000002a802a80000000002a002a00000000002a802a80000000002a002a55000000550000005500550055005500550000000000000055005500000000aa00aa00aa00aa00aa00aa00aa00aa0000000000aa00aa000000000088008800000000000000000000000000000000140014001400140014001400000002a802a802a802a802a802a802a802a8008800880088008800880088000000000000000000000000000000055005500000000000000000000000000440044
|0,13=>0xaa00aa00aa00aa000000000000000000015400000154000001540000015400000154000001540000015400000002a802a802a802a802a802a802a802a80028002800280028002000200020002440044005500550044004400550055004400440055005500440044004400440000000000000000a000a000a000a00000000000a000a000a000a000a000a154015401400140014001400140014001540154014001400140014001400142a802a802a802a802a802a802a802a802a802a802a802a802a802a802a800055005500000055005500550000000000550055000000550055005500000000000000000a000a00000000000a000a00000000000800080000000000080009540154015401540154015401540154015401540154015401540154014001400000000000000000880088008000800000000000000000008800880080008000000004400440044004400440044000000000044004400440044004400440000000000000000aa00aa00000000000000aa0000000000aa00aa0000000154015401540154000000000154015401540000015400000000000001540002a8000002a8000002a8000002a8000002a8002802a8000002a8002802a800050005000500050005000500050005000550055005500550054005400540054
|0,14=>0xaa00aa00aa00aa000a000a000a000a00aa00aa00aa00aa000800080008000954015401540154015401540154015400000150000001500000015000000152a802a802a802a80000000002a802a802a802a802a802a80000000002200221100110011001100110011001100110011001100110011001100110000000088008800aa00aa00000000000000000088008800aa00aa000000000000000154015401540154004400440044004401540154015401540044004400000002a802a802a802a8028802880280028002a802a802a802a802880288028002800000000500050000000000050005000000000005000500050005000500050aa00aa00aa00aa002200220000000000aa00aa00aa00aa002200220000000110011001100110011001100110011001540154015401540110011001100112a8000002a8000002a8000002a8000002a8008802a8008802a8000002a80005500550055005500000055000000550055005500550055000000550000000000000000000000000000000000000000aa00aa00a800a800aa00aa00a800a800015400000154000001540000000000000154000001540000015400000002a802a802a802a802a802a802a802a8000002a8000002a8000002a8000000005000500050005000100010000000000050005000500050001000100000000
|0,15=>0xaa00aa00aa00aa00aa00aa0000000000000000000000000000000154015400000000015401540000000000000000000000000154015400000000280028002800280028002800280028002000200020002000200020002000250000000550000005000000055000000500000005500000050000000550000aa00aa00aa00aa0000000000aa00aa00a000a000a000a00000000000a000a000000000000000015401540154015400000000000000000154015400000002a802a802a802a802a8000002a8000002a802a802a802a802a8000002a800000000000550000005500000055000000000000005500000055000000550000aa00aa00aa00aa00aa00aa00aa00aa0000000000aa000000aa000000aa000000000000000000000000000000000000140014001400140010001000100012a802a80000000002a802a802a802a802a802a80000000002a802a8022002255005500550055005500550000000000550000005500000055000000000000aa00aa0000000000aa00aa00aa00aa00aa00aa0000000000aa00aa00aa000154015401540154015401540154015401540154011001100154015401100110000000000000000000000000000000000000000088008800000000000000050005000550055005000500055005500500050005500550000000000000000
|1,0=>0x154015401540000015400000154000001540154015400000154000001540002880288028002800288028802800280028802880280028002880288028002855005500550055005500550055005500000055000000000000005500000000aa00a000aa00a000aa00a000aa00a000aa00a000aa00a000aa00a000aa00a154015401540154000001540000000001540154015401540000015400000002800000028002800280000002800280028000000280028002800000028002800000000000000000000000000000000550000005500000055000000550000aa00aa00aa00aa000000000000000000880088008800880000000000000001540154015400000154015401540000015401540154000001540154015400022002a8022002a80220022002200220022002a8022002a802200220022002200005500000055000000550000005500000055000000550000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x138501808130000a141282410011201410010008c0a140c80802001101426210400400140982410010008032080007c0a140f064041b00014060200800281c0c80836000286832080080028180b82002000a04c2016008001802058000a13080080200098200e150a04c10010904406100100400090403c000e04820020d02830100b000281208038180a04018080200
|1=>0xd80400050c8080200028d410011a0cc0a140c82002120881418130401c64140c82002000882832310084800050605c041b000143202180000a1415864041b000144a09040045e050c8b80200028505a1901004000502064040100014260401004001d0c8b00200028503208038004e14158200200150500610040040014020640401000a43208008000a280c8200200
|2=>0x502410010011c14190401c0c050a11412080080014190411002000a0241001000180a430c80802000290826080080082190401c80050a0641001000fc280c0980836000284c060200800280c040f800050a04c7a080080028190400478050a0300802008000a1904004003b0a06410071d01428390c82002000a06410380001428190401c2a050a02410011b8143236
|3=>0xd80014130400400150a064041b008004e130202002002094432020d8000a192800400050a13c260800800140c0402c00050a138120800800144d04820021202830120807800140c048200e120293412080080014190403c000e0a04c1208008c824080080098050a06410002581428192500400050a04c2008008002802008480049028640401058000a13040040048
|4=>0xc82002002f02828090c820020002974b8190400400050985802002086410010580014130400400410c820025b02850265a0400400140200c10010005026100400400410c96402000285026020080082580c80802000295c3202008000a210182002000a064ac01000142813048200200050640401001500a130400400110a0302e082980028420182002000a0641052
|5=>0xc820027202850320800800e2050a0640401001c00a140b80802002a8508a190100400050a064dc0100014320800800d8050a0641001001ac14140c808d4010001428190400400690285018670400400050a0303208008004e140c82002320019828190400400053285032640400400050a064100100014c6140c984020002850320800800c0050a17c3208008000a14
|6=>0x5014281904004a632000503208008004e143f864100100014281904004e40005050327d0080014050a064107c00014287b0c8200e000285018130406c00050a064f408008000a140c8200e013c814281901004004702850320800800f0050a0641001001dc0a140486402003b014281904004ea00028503208008480005100641001091ac0a14398641001000142825
|7=>0x2186410010001428090c820020005154328e008000a140482002002f014288d0c820020002850328c008000a144506410010001428130400400890285032080021c14050a04c3202008c800143d864100f0001428190401d0c05230503208008c866050a0641001390480a14098641001001d028190d80508000285032830100400050a0641001410000a140c8210000
|8=>0xc82002004d01428090c8200e01090141208008000a992706404010001428194c00400050a0103202008000a0c0c8081e00028502602008003a144b86410011901428250482002000501432084b00400050a2543208008000a142686404010001428194a02002000285032080d8046400050641001002480a140602122000285032080080120050a1081001001f80a14
|9=>0x1780a145286410010001428190400400a4028503202008000aa30a2883208008000a140c82002003801428030400400140c8200200240280aa10c82002000285140190400400050a06410010027c0a140c8200e0119028284534020020002850329e0400400050a0200200248280a140c820029d0001428190400400054e050329b0400400050a0307219040040014
|10=>0x51183201578000a140f06404010001428450c8200e00028507219040040014048641001190480aae0c82002000285032085680400050a06410ac008c80a140400424002481428190400400ab0285032080082c00050a0243208008c8000a0c82002a9028503208008c824550a064100700aa00a140c820020053814282b0c8200232000514c190400400050a0302608
|11=>0xc8080212000143208008c800b00a0641001002e00a140c82002005b8280a080089000490285032080386c64050a13c32080080014050c808020002ad4280c340201e00028503231008000a141286410011201428190400566000285164190400400050a06410011e01428510982002000285032085880400050a0243208008000ab02786410010009c28090c8200200
|12=>0x61014280c0b808020002850ce1904004000a0a0ac3202008000a140c82002006081428190b82002530005032080084854050a0641001003000a140cafc02000285012190400400055e8302608008c800140c8201e1b0002832080080178050a04c1001001f814140e1a010010001428190400400bb02850320800800540a0a0241001002e80a14062e41001000142813
|13=>0x986404010001428190400400c90285032080080190050a0642c010001428190400400c70285072190400400050a0101001001f80a140c82036010009c28130400400620a0641001000e80a140c8218c01000142819040040015028503208008018a050a14432080d8000a141286410011781428196202002000285032080080186050a04c32020080052140c8200200
|14=>0x6980802000285032080080080050a0640401003480a140486410010002852420c8200232000503208008f000050a0243208008004e143d84c10010001428130182002000a065a201000142819043400200028509e190400400050a0943202008480a196780400050a06404cd008000a140606410cc0001428cb0c82002000285026040c808020002b283208008000a14
|15=>0x3740a1409864101b00800141904005b800028503208008d024050a06410db0001428190400468000505032026d0000a140c8200e1b4301428d90c820020002851b0090400400050a0641007002dc0a140c82002006b8142819040040011028501208038050c050a020020040814cc142786410070001428d60c820020002850320800801aa050a06404016a0142819
|16=>0x505032020d804008502894320800b980a140c820022400154281972804240002850320800801c8050a04c1001001042813048641001000288a1904004000a0a064d4010001428580c820020002851c6190400400050a0641001003840a142b8641001000142819010040005208641001000180a140c82002007001428190400400476f850320800801bc050a0641001
|17=>0xc820020002850841304004001d0a064100100029d6140c8080224090000a1304004004802850320803800bc050a06410010001482040c8200232000509c1904004000a0a1343208008480a1406064100f00028284d0c82002000505018130401c00050a0641001003a80a140c821d20100014280404864100100014320800801120a0286410e80001428190400400e7
|18=>0x400400ef0285032082900424050a064020077014284f09820020002850320800801da050a0303208001b40a140c820a4010002828040c8081001000143216008000a410c820020076014284e048200200028503202008c8240506024100f0001428190133036010001426090400464000a10808190400400050c9b8020002850381904004000a0a04c1208008001442
|19=>0x7c82002000a19c3208008000a140cbdc02000285018190401c64050a04c0808008003a140e06410002f01428190400400f602850260800800821302064100100028261904004000a0a3d43208008000a140c809e80100014281901004240002955e6190100400050a06402840001428970c8200212028503208008000af10a0303208001780a140c820020002bc02819
|20=>0x1428190400400850285032085600424000285018190100400050a04c32080084800050a0641001001f814050a09432080d80400050a0640401090000a1901004000523050f6190400400050a065f0010001428130c820020005014284204864100100014280904004007e02851e4190400400050a0641001003ec0a140c821e8010001428130c80400760285032fa
|21=>0x2381428190400400057f830d008008000a141286410010901428190403c02004301428170400400550a1143208008000a14098103208008000a140cbf8100100014281904004000510050320800801fa050a1343208008c800050a0640401002d80a140c805f8000285032026700400050a064100100014c414098641001003880a140c820023400014280c0c8200232
|22=>0x1428190400400b6028504a090400400050a04c100100074284d0c8200200028503208008000b000a0642e02008000a140c8080200028a428250c820020002b7c280c0c8200e00028503208008010c052305026190400464000a0651008008000a140ca0c10010001428aa04864100100014281904005cc00028503208038000a460a0657208008000a140c8200200
|23=>0xc80802000285116190400400050a0641001298000a14790243208008000a140c8203601002140a140c820020002974284f0606410010001428130c8200e0100014281904004000520852041904004000a028504a1904004000a02850320800c040a140c820020002a8c2819040040048028503208008000a660a1383208008000a140c820a401190000a1406064100f
|24=>0x8000a1415864100100014281904004000a2a850326f008000a140986410010011c0a140c8200224000280a140c82002003c81428090c8200e010001428190400400b70285032080d80464000285032080d804000a0293c3208008000a1404864100100014aa140c8220a00028503304008c800050a06410010001606140c820a4010001428130c8200232000142813
|25=>0xa064fa0100014281904004000a230503208008c824050a03012190400400050a06410010024c0a140c8200232000282819042b002000285012190400400052305026190400400050a13426190400400050a06410cc0d80400050a04cd008008000a140c8200e010901428190400448120001428090c82002320001428090c82002000501426190400400290a0302e08
|26=>0x9866080100014281900800ec050a0243208008000abe0a06572080080014050a1083208008000a140c8200200029044a190100400050a0641001090000a550a0641109008000a1412864100f008000a140c82002008401428090cc1c100100014288b0986410010001428190406c02004301428190400401060285032086d0000a140c82002d4028503208008000ab0
|27=>0x28503208008000a140c8200200029182819040046400028503202008000a140c8201e010001428193402002000285032080380400050a064100100014aa140c82002000287428130c80810010001428670c82002000285084130c82002000285008190400400050a0640401000143a140986410010002828190400400e202850330a008000a140c820020043015be14
|28=>0x3208008000a140c80810010001428090c82002000285032080d80400050a06608010001428130c82002000285032f90400400050a06410010001452140cc1c1001000142819040040081
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x32502d50285023501e50195014500f500a500550005
|5,0=>0x1af61a961a3619d61976191618b6185617f61796173616d61676161615b6155614f61496143613d61376131612b6125611f61196113610d6107610250fc60f660f060ea60e460de60d860d260cc60c660c060ba60b460ae60a860a2609c60966090608a6084607e60786072606c60666060605a6054604e60495043603d60376
|5,1=>0x26c62675261625c52566250624a6244623e62395233622d62276221621b6215620f6209620361fd61f761f161eb61e561df61d961d361cd61c761c161bb61b56
|6,0=>0x422741b7414740e6407740073f973f273ec63e573de73d863d173ca73c373bc73b573ae73a773a073997392738b7384737d7376737063697362735b7355634e7347734073397332732b7324731d7316730f7308730172fa72f372ec72e662df72da52d372cc72c572be72b772b072a972a2729b7294728e62877280727972727
|6,1=>0x5d775d075c975c275bc65b575ae75a775a1659a7593758c7585757e75786571756a7564655d7556754f75487541753a7533752c7526651f75187511750a750374fc74f574ee74e774e074d974d454cd74c674bf74b874b174aa74a3749c7495748e7487748074797472746c6465745f64596452744c6445743e7437743074297
|6,2=>0x78e77877781677a7773776c7765775e7757775077497743673d6736772f77296723671c7715770e7707770076f976f276eb76e566de76d776d076c976c366bc76b576ae76a776a076997692768b7684767d7676766f76687661765a7653764c7646663f76387632662b7624761d7616760f7608760175fa75f375ec75e575de7
|6,3=>0x944693d7936793069297922791b7914790e6907790168fa78f378ec78e578de78d778d168ca78c378bc78b578ae78a778a078997892788b7885687e7877787078697862785b7855684e78477841683a7833782c7825781f68187811780a780377fc77f577ee77e777e167da77d467cd77c677bf77b877b177aa77a3779c77957
|6,4=>0xa107a097a0279fb79f479ee69e779e079d979d279cd59c679bf79b879b179aa79a3799d6996798f79887981797a7973796d6966795f79587951794a7
|7,0=>0xbdc8bd57bcd8bc58bbe7bb68bae8ba86ba17b9a7b937b8c7b848b7d7b767b6f7b696b627b5b7b547b4d7b458b3e7b368b2f7b287b217b198b127b0b7b047afd7af76af07ae97ae18adb6ad47acc8ac57abe7ab77aaf8aa87aa26a9b7a947a8c8a857a7d8a767a6e8a677a5f8a578a4f8a496a427a3b7a356a2d8a258a1e7a177
|7,1=>0xdaa8da37d9c7d957d8e7d886d808d797d736d6b8d638d5c7d566d4f7d478d407d388d317d298d218d198d127d0c6d066cff7cf96cf27ceb7ce38cdc7cd57cce7cc68cbf7cb78caf8ca87ca17c998c918c8a7c837c7c7c757c6e7c686c608c588c517c498c427c3a8c337c2c7c248c1e6c177c107c097c018bfa7bf37bec7be48
|7,2=>0xdb98db27
|8,0=>0xe357e2e7e277e216e1a7e137e0c7e057dfe7df86df17dea7de46ddd7dd67dcf7dc87dc17
|9,0=>0xe3c6
|_,_=>0
def wAt:=mkWire dB 267 247 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 9 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x4814210770c8140c815099070c8140c815040510e8510c8140c815098770c8140c8150c9550286702851048c8008c9028510001506051098010c8150c8510c851008650c8c90001506028099070c8140c8150986c028650c9190081609030008650c8140c815098770c8140c815048c802801000150086502865048c800015098770c8140c81502849098770c8140c81504051098770c8140c8150786500815
|1=>0xd81700851278140c86d0011900816041f90086600989048140c8510605300865048030c851098030c8150401e0080100179028653a0510284b00051008ca028010005102807000650980a0c8150c81602866040510c91900816378510401c029b500851008ca00015010770c814340150c85327814060510c82a02851028cf0906704189048140081509807028650c851041050e8510c8140c8150986c02865
|2=>0x128160980a0c815098770c8140c8150c85102851000150c8920500105067278170605105205028510c85105064028510c8a500016010a70405100016098530c81504051040510c8140c815000650285109067128150006502851000154981500865008650c86c0085102867028510423d05003028510c83f00815458530c8154400705021040510c815060530011902807042170c86f001210c85100a0504066
|3=>0x5c81505066028510c8ca028010408114851000165f0510c8510c805000150c8150085102851008150c8ca000150506602851040510c8152a8510c8160c86e028490c86d5b01601067008155a051040a7000160284900189048140c8510c853290510c8160c8510c85104123048070c8510c91900816278170c86d0d8010c892028490986c0286555003048210c851000514305100066060170c8050c94902865
|4=>0x481400155028670087502864040510c803098510caf90c851040160d86700851048c80c851000150c86d008511903202801000770c814040510c829028510293c0480506053098770c8140c815042150c86f190530005104051000650418b048140c85167015010640c815028320b81502866040510c8510c815041050c8140c8510293c0c86d0c815048140c851060c80c86f008510c8ca000150286604051
|5=>0x510c851040510c815378510401c0080107865008150c851028510c8150c8140c81502a1b000660980702865048140c851098530c815098010c8150c8c9000150086502865028653f0510285100a670506402a19000660c86f028530006502849041d10284b0e8510c8140c815028510c8150c91900816010770c814040514b853710510c815040510e8510c81409030008650506702851001550c8160098b
|6=>0x40770c814028510c815048150c8510c85100866128510006500851098080c8150401e048170c8517c051040770c8140c8140c815028650d8ca008510e8510c8140c815098530c8150c9550286702851098080c8150c81604051042170c86f00851128050006579016028653f02a028510005107801008150401e008010c86d00851028510780100815098530c815041050e8510c81414865000160405102801
|7=>0xc91b00816048210c8516f8010285300801008160506602851098030c8150e8520c8140c8050c85300051000650c803008150c8170c8160c91900816098530c8156f86602853148510001609007000510c8c9000150106704051041fb008660106404051048140c8510c815001550c8160c805000150c86f00851090050005100865040510c81502851008660085100065000510405100816040510605300865
|8=>0x510780100815000150c815040510c815098210c8150d81700851048010c8510c86f00851230510081606051008650c8150e8510c81404065028510285100065002f9040160289700065048070c85105067028510c8a500016008c9000150c8050081501067040510c851000650c8140c815098010c815050230285102866040510405100016028530006500005008650c80300816000150c8150502102851
|9=>0xc816041f900866028070285102801000510c85100865000320086502851000150d80100851008160c8510c8150c8150d815008510c85302865000050005102849000510c85100015028510c851000160c8150286600865028320086502867028510401c00801098030c8150500102851048030c851008010c8510c86e00851000150085102851008510c86d008510c8160c85100a0704066000150405302848
|10=>0x40530c81504015000160400504066008160001504051008150c853008010c8160c8140c815340150c8530c815098530c8150c81404051028510c815098230c815040750c8140006602853040530c8150401e008010c851040160506602851098510c8150e8510c8140405100065028670005100a19000660c8010081540851040660c851040050c8150c8030085140815040660087502864000770c8142a851
|11=>0x40510c85100851
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x884000000000000001f300001d2000000000001b20000192000017200000000000143000000000000000000000000000000000000000000000012203cc0d2000000000000000000000000000000000000000000028c000000000000000910000000018c000000000000900020000000
|5,1=>0x42410083f100003c30000393000035400000000c8c0000bcc0000b8400000002b30000000000000000002a100000000a082710948232
|6,0=>0x9b2264896300000000000942244c00000008f2234800022c8892220400000008620000842000082220087e21f080001e887821d4c73200000001c486f200000001b486b21a0c65300006320000612178c5c216885821588542000052214084e2000000013084a2124400011c8461
|6,1=>0xe5138c8e2137ccde1000000036ccda13644d720000d6134cc0003448cf200000000000ce13308000328800031ccc6131080003088c1130040000000bf10000bd22e8cb9100000000000b7200000002d480000000b412c88b022bc4ad22ac8a832988a51288ca1128049f100009d2
|6,2=>0x12c24a4c000000000000012720001252490521347c91e100011b3460d16200000004545141444d10143c50d2430400000010a241cc000000106100010420000000408800000010023f4c00000000003ec80003e0cf623cccf03000000000000003b880003b08ea23a0800039c4e61
|6,3=>0x610c00060897f35f857d100017c15e4d7725d0c0005c8970200000005b896c25a880005a080005989642000000058c561257c95d257055a2564557200015435489502534c00053054a2000147351480000000000000000050c94124fc93d24e8d3914e053534cc80004c0c00000012e2
|6,4=>0x6d45b326c85b020001ad30001ab26a85a82694da32680c00067899c2000199365c99616545932000190363898d100018c1624d872
|7,0=>0x8c4a2f28b4a2c18a8a282898a242888a202878a1c2868a182858a142848a102838a0c2828a082818a042808a0027f89fc27e89f827d89f427c89f027b89ec27a89e827989e427889e027789dc27689d827589d5174c9d1273c9cd272c9ca17209c627109c227009be26f09ba26e09b62
|7,1=>0xab86ac2aa8aa82a98aa42a88aa02a78a9c2a68a982a58a942a48a902a38a8c2a28a891a1ca852a0ca8129fca7d29eca7929dca7529cca7129bca6e19b466b29a4a672994a632984a5f2974a5b2964a572954a532944a4f2934a4b2924a472914a432904a3f28f4a3b28e4a3728d4a332
|7,2=>0xac46af2
|8,0=>0xb086c11b006bf1af86bd1af06bb1ae84000ae46b81adc6b61ad46b41acc6b21
|_,_=>0
def PO:=mkPO wAt oP oO 20 9 511 14
def pmP:Nat→Nat
|0=>0x82800040c00020400010100008000003c400018a0000c20000458000210000104000080000038800014000009c00004b0000220000108000082000040000010800004c00002000000e000005000002000000c0000040000018000008000002000000
|1=>0x86300041800020200010000006a780029180011800008460004200001f3c000f9600075f000300000173c000b960005820002a7800112800080000038800018300008080003820001a00000c800006380003140001800000b980005c4000242000113
|2=>0x26e68011f3c008c080045cf0022a7801133c008834004400002103001073c00831c00418c0020c5801040c00820200410000202780101140080840040070020030010008008002004000001125800880800410000204f001003000476c0023a20011cf
|3=>0x8040004018002008a010042008020804008002000400e1cb007067803812c01abbe00d45f0062e78030b3c01848400c1db0060e7803072c01838a00c17b006027803012c01808400947b004041802000800c50c006206003101001841800c00c006000
|4=>0x6008382c053c1489960a41cb0500e182427ac1082be08034b040183820000410000004200002018181000000508100245cf0120e7809053c04811602404f0108e78081028040810020008010001007018402199e01014100808100404000201820100a0
|5=>0x2003a3900011075009e3a004f1580258ab512c5589962ac44f1542258a427f45203d623404b11806788a0d3c45029e2205cf1100a7881633440a1962040c2100c67880232c4008002002cb0c000104810681e02960f0103078025834072c1a02c60c034b
|6=>0x10a14cb810021231012d1283d688c1cb443025a2105751002b6846001421001a04038501839e80c1cb402082a0004150002026060c2300565980032cc000004d01eb228030903010880c180400a42
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x2c15330002000200080000020005001b00000e000000000014000002140b0214000000000200020000000200020002000000020000000000000000000000000002130200000000000000000000000002000000001b00000200000025020000
|6,0=>0x7f14a704531b000071147a4a00482e000102000000800100150007480c00017a0c000095000731140000003e00000200003c0c06212b028d061426281b7a0002000c013800000005030000a98800021c14009279000c000c0201180002026901000012020000020c497b00500002550241010207000c0c0100000a022d000260
|6,1=>0x540002a3144500464202640002029400015d01000200021a00002a160202c5501b960036050225007a8800541d000000000001020202557e3d4a010020000001000c17000000000100021432027a00a407660000027a053c7a307a00000c4a000024000f00000200000c05000000020067580dac0000000002000c1c0100141b
|6,2=>0x4021b06002527023901354a0500071c00118309370c007c871400820e06
|7,0=>0x464f8f61b8904c749b5943475c9e518529b2d7917db15c5a77b0c2d63a9ad3c44d4fc9c162a1d01e646d5fab65421fcf9823c681c8c7578b6c6ed5cb8cb7c693be76c0225e8a1e9d70a8446fceaebd9732d1b78e9c52b64ed2ba5ba6cc862f995b3b9f195c6b4b5c78a2cabc40af7289cd2932c3b31c3f84a5b4aa566163bfa0
|7,1=>0x8a2f
|8,0=>0xb734c66875b96ed8b14f6ad4bbad2fb5735c
|9,0=>0x10
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 25 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_244 7 roots_244 ops++addP pm 1 dom_118 7 roots_118 ops++addP pm 2 dom_214 6 roots_214 ops++addP pm 3 dom_230 7 roots_230 ops++addP pm 4 dom_196 4 roots_196 ops++addP pm 5 dom_224 4 roots_224 ops++addP pm 6 dom_242 7 roots_242 ops++addP pm 7 dom_178 5 roots_178 ops++addP pm 8 dom_212 5 roots_212 ops++addP pm 9 dom_86 4 roots_86 ops++addP pm 10 dom_198 5 roots_198 ops++addP pm 11 dom_210 4 roots_210 ops++addP pm 12 dom_162 4 roots_162 ops++addP pm 13 dom_54 4 roots_54 ops++addP pm 14 dom_182 6 roots_182 ops++addP pm 15 dom_166 5 roots_166 ops++addP pm 16 dzo_224_16 4 roots_224 ops++addP pm 17 dzo_230_16 6 roots_230 ops++addP pm 18 dom_116 4 roots_116 ops++addP pm 19 dzo_228_16 5 roots_228 ops++addP pm 20 dom_102 4 roots_102 ops++addP pm 21 dzo_226_16 5 roots_226 ops++addP pm 22 dom_114 4 roots_114 ops++addP pm 23 dom_180 4 roots_180 ops++addP pm 24 dom_226 5 roots_226 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_246 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_196 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_224 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_178 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_212 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_198 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_162 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_166 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_224_16_224 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_230_16_224 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_zo_228_16_224 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_zo_226_16_224 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_180 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_226 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_244 7 s (0,roots_244.map (·&&&dom_244)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_246 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_244 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_246==dom_246)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_246 gM v ys):RunD true dom_246 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_246 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 11 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 11 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 96 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 96 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 256 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_256 : ∀ i, 256 ≤ i → i < 286 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 30 256 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 286 → Z 6 i = true := (range_split z6_0 (range_split z6_128 z6_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 130 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 2 128 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 130 → Z 7 i = true := (range_split z7_0 z7_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 18 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 18 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_246 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_246 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_246 roots_246 goal_246 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_246
theorem lowS_246:Lower true dom_246 roots_246 goal_246 10:=S_246.noCircuit
theorem lowS_249:Lower true dom_249 roots_249 goal_249 10:=lower_slice_b [(0x303000003030000030300000303000003030000030300000303000003030000,1,17)] (by decide +kernel) lowS_233
def dzo_234_16:=0x505000005050000050500000505000005050000050500000505000005050000
def gzo_234_16:=0x505000005050000050500000504000005050000050400000504000004040000
def gsh_234_16:=0x50500000505000005050000050400000505000005040000050400000404
theorem lowS_zo_234_16_232:Lower true dzo_234_16 roots_234 gzo_234_16 8:=lower_iso_b (d1:=dom_234) (r1:=roots_234) (T1:=gsh_234_16) [(dom_234,16)] (by decide +kernel) (lower_slice_b (T:=gsh_234_16) [(0x40400000404000004040000040400000404000004040000040400000404,0,2)] (by decide +kernel) lowS_232)
namespace S_250
def pG:List (Nat×Nat):=[(2,18),(2,34),(2,130),(8,40),(8,72),(8,136),(10,26),(10,42),(10,74),(10,138),(16,18),(24,26),(24,56),(24,88),(24,152),(32,34),(32,40),(32,96),(32,160),(48,50),(48,56),(48,112),(48,176),(64,72),(64,96),(64,192),(66,74),(66,82),(66,98),(66,194),(80,82),(80,88),(80,112),(80,208),(128,130),(128,136),(128,160),(128,192),(144,146),(144,152),(144,176),(144,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_250.map (·&&&dom_250)
def gM:=goal_250&&&dom_250
def NN:Nat→Nat
|4=>3
|5=>15
|6=>35
|7=>15
|8=>3
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xabce28f8a36f976
|5,0=>0xd39d48128573340706c26e8916aed661533517155079544f19341b5329621c10d09b6c017ec
|6,0=>0xb0d429922b84ecf6b2b266edd4f6b047c0b4497143eb7423523c3c036ad634c6f3419d336e3327bb32534307db2dcfa2680125d382451f210042053d1f4911f17c1d4e11a34015c190eee20e8e80bb8e09df709b6c0116f
|7,0=>0x5f07d5c585434893788a334b526cb923d7e1ab2518e58178f515a8e1104e09c370460f00db0
|8,0=>0xdf6064679b19912
|9,0=>0xef2e1
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xa0a0a0a0a0a0a0a00000000000000000a0a0a0a0000000001400140014001400140014001400140014001400140014001400140000000282828280000000028282828000000002828282800000000282828280000000505050505000500050505050500050005050505050005000505050505000500a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0000000141414141414141414141414141414140000000000000000000000000000000282828282828282828282828000000002828282828282828282828280000000505050505050505050505050505050505000500050005000500050005000500a000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a0141414141410141014141414141014101414141414101410101010101010101282828282828282800000000000000002828282828282828000000000000000505050505050505050505050505050505050505000000000505050500000000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a000141414141414141414001400140014001414141414141414140014001400140202020202020202020202020202020202020202020202020202020202020202505050505000500050505050500050005050505050005000000000000000000
|0,1=>0xa0a0a0a0a0a0a0a000000000a0a0a0a0a0a0a0a0a0a0a0a000000000a000a0141414141414141400000000000000001414141414001400000000000000000282828282828282828282828282828282828282828282828282828282800280000000005050505000000000505050500000000050505050000000000000000a000a000a000a000a0a0a0a0a0a0a0a0a000a000a000a000a0a0a0a0a000a01414141414141414141414141414141400140014001400140014001400000000028002800280028002800280028002800280028000000000028002800000005050505050505050505050505050505050505050500050005050505050005000000000000000000a0a0a0a0a0a0a0a00000000000000000a0a0a0a0a000a000000000000000000014001400140014000000000000000000140014000000000000000000000000000000000000000002800280028002800280028000000050005000500050005000500050005000500050005000500050005000000000000a000a000a000a000a000a00000000000a000a000a000a000a000a0000000141414141414141414141414140014001414141414141414141414141400140282828282828282828282828282828282828282828282828000000000000000000000000000000000000000000000005050505050505050505050500000000
|0,2=>0xa0a0a0a0a000a000a0a0a0a0a000a0141414141414141414141414141414141414141414141414140014001400140000000002828282800000000282828280000000028282828000000002800280000000000000000050505050500050000000000000000000505050505000500
|_,_=>0
def sP:Nat→Nat
|0=>0x1c128d0c705614a34304e14a3431c154528d3c350128c24320145234320144d0c71852840c70534490c70402840c70450121031c144d0c204028c10308144c2c320114c40308128c3c320114d0c138528c2c30812890c80401031c61440c2040
|1=>0x10d0c138528b34304e14a2440c21c12923431c144a24d0c81c144c3431c178a74d0c704528c34308144a3100c704528d0c21c170a24d3c31c128d0c220145b3431c114a3431c168528d0d404528434f0c70516090c704529834305914a5cd0c8
|2=>0x28c34320114a34320705114434308704529230d0c704528d3c31c114a2cd0c21c128d0c706114a5cd0c70452a01031c114a4840c704528d0c705344a3431c17c528434350114a2cd0d404528d0c704500a3431c165114c1031c14453040c8045
|3=>0x3431c114a34308704528d0c705114a10d0c704529830d0c70452843431c14452c43431c114a80d0c70452923431c114a30d0c20452843431c16452a33431c114a2cd0c704528c3431c1445
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x2940aa005
|5,0=>0x18d8bac57628b12d88ac3f61cb0cd85ac27610b06d82ac0f6
|6,0=>0x54de98f4579f3cdde60f297913c6de28f0d7833c019f2ef2775bb91dbaed6767bb21d82eba759bab594ce9f74cb249d16e8473eb9d9ce0c697
|7,0=>0x706374fb28d5be91f3af958c73e1deff1787b8bda62c315a7
|8,0=>0x75dfa0fc97
|9,0=>0x1de6
|_,_=>0
def wAt:=mkWire dB 36 251 0x7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x34a4d1d1ca4d292c7c41534a441534a4a3508d47156050a31289853544dc5292c5ca2514d47151ca4529105cd291c985352c7041534a441734a441d28d441d107cd29605cd213c7c41734a4b1f1054d2908d471544c0a151cd4c44347452908d47153110d1d14a4d291054a351054a35
|1=>0x71514a4d2928c473514a4d291054d2914c873508d47151cd451d107cd2928c87351054d29347452934747291ca452934a471514c4735105cd291054d2988dc2291c545321cd472514d472614d4b1c1054d293110d1d14a441f
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x102000000698a310414c2082200000000002
|6,0=>0x140a6980096524a3900088600209bf2000f0dc9b726c2d0800322000001812e2566a0d312424267c8e91a330454c91800
|7,0=>0x1b8b616a2d0598b21622c0578ae15a2b0558aa1522
|8,0=>0x1c8788f01
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0x8df8d76cf60a6013ff3382fd2df1050ff0fb0df0cf0c90bf09508f08908508108002001e018014012010008006002000
|1=>0xcdb9df995
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x1000182047243000003
|6,0=>0x32800410403c04c40123032410030000c35940c144511b0cd2c0
|7,0=>0x1c7a05da60e5e121d890653
|8,0=>0x157d3
|9,0=>0x13
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 12 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_234 8 roots_234 ops++addP pm 1 dom_122 7 roots_122 ops++addP pm 2 dom_218 7 roots_218 ops++addP pm 3 dom_242 7 roots_242 ops++addP pm 4 dom_186 7 roots_186 ops++addP pm 5 dom_178 5 roots_178 ops++addP pm 6 dom_232 7 roots_232 ops++addP pm 7 dzo_234_16 8 roots_234 ops++addP pm 8 dom_154 4 roots_154 ops++addP pm 9 dom_210 4 roots_210 ops++addP pm 10 dom_114 4 roots_114 ops++addP pm 11 dom_58 4 roots_58 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_250 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_178 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_234_16_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_58 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_234 8 s (0,roots_234.map (·&&&dom_234)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_250 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_234 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff00000000ffffffff00000000,96)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)],[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_250==dom_250)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_250 gM v ys):RunD true dom_250 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_250 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 15 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 35 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 35 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 15 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 3 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_250 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_250 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_250 roots_250 goal_250 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_250
theorem lowS_250:Lower true dom_250 roots_250 goal_250 10:=S_250.noCircuit
def isoMvS_95:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_95:Lower true dom_95 roots_95 goal_95 8:=lower_iso_b isoMvS_95 (by decide +kernel) lowS_63
def isoMvS_125:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_125:Lower true dom_125 roots_125 goal_125 9:=lower_iso_b isoMvS_125 (by decide +kernel) lowS_123
def isoMvS_189:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_189:Lower true dom_189 roots_189 goal_189 9:=lower_iso_b isoMvS_189 (by decide +kernel) lowS_123
def isoMvS_207:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_207:Lower true dom_207 roots_207 goal_207 9:=lower_iso_b isoMvS_207 (by decide +kernel) lowS_175
def isoMvS_215:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_215:Lower true dom_215 roots_215 goal_215 7:=lower_iso_b isoMvS_215 (by decide +kernel) lowS_183
def isoMvS_219:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96)]
theorem lowS_219:Lower true dom_219 roots_219 goal_219 9:=lower_iso_b isoMvS_219 (by decide +kernel) lowS_123
def isoMvS_222:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_222:Lower true dom_222 roots_222 goal_222 9:=lower_iso_b isoMvS_222 (by decide +kernel) lowS_190
def isoMvS_237:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_237:Lower true dom_237 roots_237 goal_237 10:=lower_iso_b isoMvS_237 (by decide +kernel) lowS_235
def isoMvS_238:List (Nat×Nat):=[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_238:Lower true dom_238 roots_238 goal_238 9:=lower_iso_b isoMvS_238 (by decide +kernel) lowS_231
def isoMvS_243:List (Nat×Nat):=[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)]
theorem lowS_243:Lower true dom_243 roots_243 goal_243 9:=lower_iso_b isoMvS_243 (by decide +kernel) lowS_187
def isoMvS_245:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_245:Lower true dom_245 roots_245 goal_245 9:=lower_iso_b isoMvS_245 (by decide +kernel) lowS_187
def isoMvS_252:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_252:Lower true dom_252 roots_252 goal_252 10:=lower_iso_b isoMvS_252 (by decide +kernel) lowS_250
namespace S_127
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(2,18),(2,34),(3,11),(3,19),(3,35),(3,67),(4,20),(4,68),(5,13),(5,21),(5,37),(5,69),(6,22),(6,38),(6,70),(7,15),(7,23),(7,39),(7,71),(8,9),(8,40),(8,72),(10,11),(10,26),(10,42),(10,74),(12,13),(12,28),(12,44),(12,76),(14,15),(14,30),(14,46),(14,78),(16,17),(16,18),(16,20),(24,25),(24,26),(24,28),(24,56),(24,88),(32,33),(32,34),(32,40),(32,96),(36,37),(36,38),(36,44),(36,52),(36,100),(48,49),(48,50),(48,52),(48,56),(48,112),(64,65),(64,68),(64,72),(64,96),(66,67),(66,70),(66,74),(66,82),(66,98),(80,81),(80,82),(80,84),(80,88),(80,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffffffffffff
def xsM:=roots_127.map (·&&&dom_127)
def gM:=goal_127&&&dom_127
def NN:Nat→Nat
|9=>1
|10=>1
|_=>0
def HT:Nat→Nat→Nat
|9,0=>0x761fa
|10,0=>0x2654f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffffffffffffffffffff00000000ffffffff00000000ffffffff00000000ffff0000ffff0000ffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ccccccccccccccccccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffff0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x1ac688fac688
|_=>0
def sO:Nat→Nat→Nat
|9,0=>8
|10,0=>0x87
|_,_=>0
def wAt:=mkWire dB 8 128 0xffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 8
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xc1
|_=>0
def oO:Nat→Nat→Nat
|9,0=>1
|_,_=>0
def PO:=mkPO wAt oP oO 8 3 7 5
def pmP:Nat→Nat
|0=>0x3f80
|_=>0
def pmB:Nat→Nat→Nat
|9,0=>1
|10,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 1 (j%128);fld (pmP (k/32)) 7 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_126 9 roots_126 ops++addP pm 1 dom_125 9 roots_125 ops++addP pm 2 dom_123 9 roots_123 ops++addP pm 3 dom_119 9 roots_119 ops++addP pm 4 dom_111 9 roots_111 ops++addP pm 5 dom_95 8 roots_95 ops++addP pm 6 dom_63 8 roots_63 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_127 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_63 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_126 9 s (0,roots_126.map (·&&&dom_126)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_127 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_126 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_127==dom_127)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_127 gM v ys):RunD true dom_127 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_127 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s:Nat) (hs:s≤10):∀ i<NN s,bar dom_127 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
  · exact z10 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 5 6=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤10) (h:RunD true dom_127 gM s xsM):False:=by
  have hmin:6≤s:=by have hl:=run_len h;change 7≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_127 roots_127 goal_127 11:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_127
theorem lowS_127:Lower true dom_127 roots_127 goal_127 11:=S_127.noCircuit
def dzo_187_4:=0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0
def gzo_187_4:=0xf0f0f0f0f0f0f0f00000000000000000f0f0f0e0f0f0a000
def gsh_187_4:=0xf0f0f0f0f0f0f0f00000000000000000f0f0f0e0f0f0a00
theorem lowS_zo_187_4_43:Lower true dzo_187_4 roots_187 gzo_187_4 7:=lower_iso_b (d1:=dom_187) (r1:=roots_187) (T1:=gsh_187_4) [(dom_187,4)] (by decide +kernel) (lower_slice_b (T:=gsh_187_4) [(0xf0f00000f0f000000000000000000000f0f00000f0f0000,0,16),(0xf0f0f0f0f0f0f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_43)
def dzo_59_4:=0xf0f0f0f0f0f0f0f0
def gzo_59_4:=0xf0f0f0e0f0f0a000
def gsh_59_4:=0xf0f0f0e0f0f0a00
theorem lowS_zo_59_4_43:Lower true dzo_59_4 roots_59 gzo_59_4 6:=lower_iso_b (d1:=dom_59) (r1:=roots_59) (T1:=gsh_59_4) [(dom_59,4)] (by decide +kernel) (lower_slice_b (T:=gsh_59_4) [(0xf0f00000f0f0000,0,16)] (by decide +kernel) lowS_43)
def dzo_175_16:=0xffff0000ffff00000000000000000000ffff0000ffff0000
def gzo_175_16:=0xffff0000fffe00000000000000000000fffe0000fefe0000
def gsh_175_16:=0xffff0000fffe00000000000000000000fffe0000fefe
theorem lowS_zo_175_16_168:Lower true dzo_175_16 roots_175 gzo_175_16 7:=lower_iso_b (d1:=dom_175) (r1:=roots_175) (T1:=gsh_175_16) [(dom_175,16)] (by decide +kernel) (lower_slice_b (T:=gsh_175_16) [(0xaaaa0000aaaa00000000000000000000aaaa0000aaaa,0,1),(0xcccc0000cccc00000000000000000000cccc0000cccc,0,2),(0xf0f00000f0f000000000000000000000f0f00000f0f0,0,4)] (by decide +kernel) lowS_168)
def dzo_171_16:=0xf0f00000f0f000000000000000000000f0f00000f0f0000
def gzo_171_16:=0xf0f00000f0e000000000000000000000f0e00000e0e0000
def gsh_171_16:=0xf0f00000f0e000000000000000000000f0e00000e0e
theorem lowS_zo_171_16_168:Lower true dzo_171_16 roots_171 gzo_171_16 6:=lower_iso_b (d1:=dom_171) (r1:=roots_171) (T1:=gsh_171_16) [(dom_171,16)] (by decide +kernel) (lower_slice_b (T:=gsh_171_16) [(0xa0a00000a0a000000000000000000000a0a00000a0a,0,1),(0xc0c00000c0c000000000000000000000c0c00000c0c,0,2)] (by decide +kernel) lowS_168)
namespace S_191
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,129),(2,18),(2,34),(2,130),(3,11),(3,19),(3,35),(3,131),(4,20),(4,132),(5,13),(5,21),(5,37),(5,133),(6,22),(6,38),(6,134),(7,15),(7,23),(7,39),(7,135),(8,9),(8,40),(8,136),(10,11),(10,26),(10,42),(10,138),(12,13),(12,28),(12,44),(12,140),(14,15),(14,30),(14,46),(14,142),(16,17),(16,18),(16,20),(24,25),(24,26),(24,28),(24,56),(24,152),(32,33),(32,34),(32,40),(32,160),(36,37),(36,38),(36,44),(36,52),(36,164),(48,49),(48,50),(48,52),(48,56),(48,176),(128,129),(128,130),(128,132),(128,136),(128,160),(144,145),(144,146),(144,148),(144,152),(144,176)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffffffffffffffff
def xsM:=roots_191.map (·&&&dom_191)
def gM:=goal_191&&&dom_191
def NN:Nat→Nat
|5=>9
|6=>35
|7=>56
|8=>46
|9=>9
|10=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0xf9c2fccbe7cbbb7b35b5ab425a3beb68a98590ce135be
|6,0=>0xefc6be6d14e211be0bbbde978d5516c9a1ec5b4cc01baba054b4b159b7439197b8fc628cb468bc118514a80298722826725265e1f3551f2dd942db6d2cd642cb3d2b6d829a271c23e186fc14fb313d5d137a812977047a2
|7,0=>0xf5b54f1e84e6d14e27dce211be20d8d6a76cf094ce945ce57cc215bc2028b2d06b2c59b296eae272adb72a3d2ba3980a2fa49c867964a591d7f8c3b08afca8aec387deb7f4177cdf5775da739626fe1e6e308582da4eb564d639430a141b41402083e2773e19f2ec7e2d3d72c77e253011e44518765129770aaf20a97009fce09e4a092e50833407d85008d9
|8,0=>0xefc2deded9e8895e856ee27dce2426e1716ddd31da0afd092dc5c8cbd6d4b3eceb2c59ab9d49f3969222291d7f902698f76d8afca8aec3893ad8628772efd71c8c701766f1d75f36750bdf4eb564c4cb430a139aea393082cc382aa91235c61b5f7198bc132050eaf80d9b60d4c40bd9a092e5
|9,0=>0xe03e0c84bea30e46f1d76d6c14eb9936c332eaa62e037
|10,0=>0x2bff1
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffff0000ffff00000000000000000000ffff0000ffff0000ffffffffaaaaaaaa0000000000000000ffaaffaaaaaaaaaa0f0f0f0f0f0f0f0f00000000000000000f0f0f000f0f0000ffffffffffffffff0000000000000000ffffff00ffff00000000000000000000000000000000000000ff00ffff00ff00ffffffffffffffff0000000000000000000000000000000000ff00ffff00ff00000000000000000000ff00ffff00ff0000000000000000000000000000000000ffffffffff00ff00ffaaffaaaaaaaaaa0000000000000000ffaaffaaaaaaaaaaf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0ffffffffff00ff000000000000000000ffffffffff00ff00ffffffffffffffff0000000000000000ffff0000ffff0000ffffffffffffffff0000000000000000ff00ff0000000000cccccccccccccccc0000000000000000ccccccccccccccccaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa0f0f0f0f0f0f0f0f00000000000000000f0f00000f0f0000
|0,1=>0xff00ff00000000000000000000000000ff00ff0000000000000000ff00ff00000000000000000000000000ff00ff0000000000ff00ff00000000000000000000ff00ffff00ff0000ff00ff00000000000000000000000000ff00ffff00ff00ffffffffcccccccc0000000000000000ffccffccccccccccffaaffaaffaaffaa0000000000000000ffaaffaaaaaaaaaaffffffffffffffff000000000000000000ff00ffff00ff00ffffffffffffffff0000000000000000ffffffffff00ff00ff00ff00000000000000000000000000ff00ff000000000000ff00ffffffffff000000000000000000ff00ffff00ff00ff00ff00ff00ff000000000000000000ff00ff0000000000ffffffffffffffff0000000000000000ffffffff00000000ffffffff000000000000000000000000ff00ff0000000000ffffffff000000000000000000000000ffffffff00000000ffffffffffffffff0000000000000000ff00ff00ff00ff00ff00ff00ff00ff000000000000000000ff00ff00ff00ff00
|0,2=>0xffffffff000000000000000000000000ff00ff00ffffffffffffffff000000000000000000ff00ff00000000fff0fff0f0f0f0f00000000000000000fff0fff0f0f0f0f00000000000000000000000000000000000ff00ff00000000ff00ff00ff00ff000000000000000000ffffffffff00ff0000ff00ffffffffff000000000000000000ff0000ffff0000ffffffff000000000000000000000000ffffffffff00ff00fff0fff0fff0fff00000000000000000fff0fff0f0f0f0f0ffffffffffff00000000000000000000ffffff00ffff0000ffccffccffccffcc0000000000000000ffccffccccccccccffffff00ffff00000000000000000000ffffff00ffff0000ffffff00ffffff000000000000000000ffffff00ffff0000fffffffff0f0f0f00000000000000000fff0fff0f0f0f0f00000000000000000000000000000000000000000ff00ff00ffffffffffffffff000000000000000000000000ff00ff00ffccffcccccccccc0000000000000000ffccffcccccccccc
|0,3=>0xff00ff00ff00ff000000000000000000ff00ff0000000000000000000000000000000000000000ff00ff00ff00ff00ffffffff00000000000000000000000000ff00ff0000000000ff00ffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffff00000000ff00ff00ff00ff00000000000000000000000000ff00ff00
|_,_=>0
def sP:Nat→Nat
|0=>0x28f18205924a3c608124b28511708100a1483c318205210740200a1441820492943ce4060853031820453c608158a14f0c608114f38608a14c0c204d14418204b10608124b10204024a14c18204b1441c200a2041820491481071821440c2040
|1=>0xa10608124a20f1820492851071822884844020401483c718228408101f78a14f18205d2853da1822983c608124a14f0c60812d21100c204014f18205c29814f1c608a48c4030813543db4060523da4460851031820453c608164a14f18204b
|2=>0x4551820452121101820452143d018205291018204a14f0c608148f8d008129448f4060818523da40608a1543d14060816123d018204a50f45018205f6053d718204a48481018129814f0c60811543d1182048484406081148117182052120401
|3=>0x4131820455123d11820523ce40608a14f4c60812885123d018204548440204029211008101f2853d518204a1523d118204a1445c608128848f40608128520f5c60812923e640604a5123d118205e4841d018229211008101e29231018204a48f
|4=>0x4a484b500812ab48f44608128848f450182052406081a8aa523d018204a3c608124a48fa100812921100c608148441708100a4a74060812853c71822982123d01820453c318204a15211018204a48c4031820523d00c60811543d018204a50f
|5=>0x48f1d01822923d018207248f406081c0a48f40318204a48f44608178a48f406081bca6123d140608129848f4060812853c608124a48f45018206e1543d118206b48f40608128848440608114848f4460811060817de2923db40604aa543d0182
|6=>0x18205f2852123d018204a48f406081b8a1523d14060812923d14060817ca1523d018204a5123d140608148440608178a1523d118204a60548f40608128848f4060812923d01820622923d018207329211008100a14f5c60812855123d018204a
|7=>0xc4f4060812923e040604a48f40608184a48f41518204a48441718204a61448f40608128f18205f78aa523d018204a48fb500812923d01820752923d1406081b0a15211018204a4844060817ca48f406081b0a48f40318204550f4060812943d0
|8=>0x48f40608129448f4060812923d0d060812923d05c608128548f4060812923d018205f29211018204a4b13d018204a48f45018204a48f40608178a48f41318204a5123d018206229295018204a1523f418204aad23d018204a5123d018205e285
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x306054c09180f30186024c03180330006
|6,0=>0x469c89b90c720ae3f9c7c30f171d6c391c6eb8d6719ee32586138bb7168e2b5c53389f7132c24d846b08670fee1e1c38b86a70c6e171c2ab84f6092c109c1e30366
|7,0=>0x574eaca155baa38538ea52146ba8674fd09ddd37c26784c0e962129324b7488e8f211aba2f644f0881d0c42117414e80a0fdb9f383d8e795ceec1d5839b0719cdf41b7735f069e0d039988322e6260c1397b72e705ae0b2395e62aee53e0a43940827104c209441217
|8,0=>0x21544219834f04a205440197f30fc9df543e287b50f465e53bc28776eece1d54ba287350e4a1c5bb8386f70dca5b5436196b12d421a4434086710cbe593c31f862f0c41d84bb0095f2ebc9d7542e285b50b4a164cac18
|9,0=>0x47188d3118622cc4518894f10a21d44328
|10,0=>0x4797
|_,_=>0
def wAt:=mkWire dB 54 192 0xffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 15
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x3ca570549052403ca5705490124154152415101229143d24149012415c1524048a5309491102940a550551012295ca52414900f29157d240490485f4901241157d240490455f4901241157d24149012294c1524440a52413c35729490185f490124154a5241510122949053054911029
|1=>0x48a5241106d241510122940a507d490d2414900f294901241542544048a522949090295c152403ca65293d7524040a544048a524114ad2413d5544048a52415ca52404c6524440a62295109229541544048a524148a5229490d2404904f295c25240490524049e5229490855f4905240
|2=>0x4a2544248a57194900f2942c524740a502914ad241117d2403ca455f4901241546544048a57294900f29490041b3ca4f4d49110294905705490052b14a524149057294900f2941f52433c357294901529510122948a507d490d24448a502940a52414c1524440a5244490502960ad441
|3=>0x4905f29490d24140a5029490d07d490d22940a4f29490924140a524114ad24151092294b4d02b106cf29490124149052295c152405ca9240c50922b5ca52404909029491902949150294915029157d2404905f2940a5243490522940a4f2914ad24114ad2414908f29490d3094911029
|4=>0x48a502b4901241490cf2948ad029490924440a544248a4f5d490102b490714148ad229490922b49057094901e29490944048a52403ca544148a5242490d2d140ad719490144348a524740a4f294904f29490d24740a5729490124148a5229490c52b
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x118886600000000007e80001da00007060000000d1000031300000005c600015209904481f30e1864c2c600000000002660f405a020c088004
|7,0=>0x689b38d966000641b189866c035e9ae8d6e6b4358980015c6ab3541a94d4469f34e1a64d2c6933481a34d146882429a08cfe67d20001e8cee67430001c88de66c33498000cc66333109808ba65a32b9950ca264f20001348964483
|8,0=>0x25a52b294949ca4a523290947ca3a51b28c945ca2a513288943ca1a50b284941ca0a50328093fc9fa4fb27c93dc9ea4f327893c05dc4ec27513a09cc4e427113809bc4dc26d13609ac4d42
|9,0=>0x13719b0cd46683331990cc466032f1
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 13
def pmP:Nat→Nat
|0=>0x97700965009570095500922009020087e00857008220080300802004550021100177001570010300102000d7000d6000940007700075000650005e000570005500047000230001c000070000200000
|1=>0xa0957704073405720d5720457200171c0470c957031530295702937029020285702822021d702157021220210202077020220202102003019570195300a53009d7009d6
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x13c00001c034004000d0010000404cc1c1041040000043281248
|7,0=>0x1d6c0018f7224345845001c573908e9923dc78fb95658941011551001c9a800d5205508b150b0f00f063
|8,0=>0x7e9eb176f7e4471dea751ceb5f7dd87717da75b6ddc377e775177846f85175f7d2b68
|9,0=>0x2e45d75dd9849d
|10,0=>7
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 20 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_190 9 roots_190 ops++addP pm 1 dom_63 8 roots_63 ops++addP pm 2 dom_189 9 roots_189 ops++addP pm 3 dom_54 4 roots_54 ops++addP pm 4 dom_187 9 roots_187 ops++addP pm 5 dom_55 5 roots_55 ops++addP pm 6 dom_175 9 roots_175 ops++addP pm 7 dom_182 6 roots_182 ops++addP pm 8 dom_183 7 roots_183 ops++addP pm 9 dom_157 6 roots_157 ops++addP pm 10 dom_43 5 roots_43 ops++addP pm 11 dom_159 7 roots_159 ops++addP pm 12 dom_181 6 roots_181 ops++addP pm 13 dom_31 5 roots_31 ops++addP pm 14 dzo_187_4 7 roots_187 ops++addP pm 15 dom_179 6 roots_179 ops++addP pm 16 dzo_59_4 6 roots_59 ops++addP pm 17 dzo_175_16 7 roots_175 ops++addP pm 18 dzo_171_16 6 roots_171 ops++addP pm 19 dom_167 6 roots_167 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_191 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_189 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_175 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_187_4_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_59_4_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_175_16_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_171_16_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_167 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_190 9 s (0,roots_190.map (·&&&dom_190)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_191 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_190 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_191 gM v ys):RunD true dom_191 gM v (ori ys):=h
def Z (s:Nat):=barP dom_191 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 9 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 35 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 35 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 56 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 56 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 46 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 46 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 9 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s:Nat) (hs:s≤10):∀ i<NN s,bar dom_191 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 5 6=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤10) (h:RunD true dom_191 gM s xsM):False:=by
  have hmin:6≤s:=by have hl:=run_len h;change 7≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_191 roots_191 goal_191 11:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_191
theorem lowS_191:Lower true dom_191 roots_191 goal_191 11:=S_191.noCircuit
theorem lowS_239:Lower true dom_239 roots_239 goal_239 11:=lower_slice_b [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,32,34)] (by decide +kernel) lowS_237
theorem lowS_247:Lower true dom_247 roots_247 goal_247 11:=lower_slice_b [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,16,17)] (by decide +kernel) lowS_246
def dzo_235_16:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000
def gzo_235_16:=0xf0f00000f0f00000f0f00000f0e00000f0f00000f0e00000f0e00000e0e0000
def gsh_235_16:=0xf0f00000f0f00000f0f00000f0e00000f0f00000f0e00000f0e00000e0e
theorem lowS_zo_235_16_232:Lower true dzo_235_16 roots_235 gzo_235_16 9:=lower_iso_b (d1:=dom_235) (r1:=roots_235) (T1:=gsh_235_16) [(dom_235,16)] (by decide +kernel) (lower_slice_b (T:=gsh_235_16) [(0xa0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a,0,1),(0xc0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c,0,2)] (by decide +kernel) lowS_232)
namespace S_251
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(1,129),(2,18),(2,34),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(8,9),(8,40),(8,72),(8,136),(10,11),(10,26),(10,42),(10,74),(10,138),(16,17),(16,18),(24,25),(24,26),(24,56),(24,88),(24,152),(32,33),(32,34),(32,40),(32,96),(32,160),(48,49),(48,50),(48,56),(48,112),(48,176),(64,65),(64,72),(64,96),(64,192),(66,67),(66,74),(66,82),(66,98),(66,194),(80,81),(80,82),(80,88),(80,112),(80,208),(128,129),(128,130),(128,136),(128,160),(128,192),(144,145),(144,146),(144,152),(144,176),(144,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffffffffffffff
def xsM:=roots_251.map (·&&&dom_251)
def gM:=goal_251&&&dom_251
def NN:Nat→Nat
|4=>2
|5=>5
|6=>8
|7=>42
|8=>50
|9=>17
|10=>4
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xbb6a20011c
|5,0=>0xda778d185c92a13568642b8eb
|6,0=>0xbe1e2b7b356d06f51e2c3e7d2092f60796705f47
|7,0=>0xcb394c5479b727fb722ba4835a31169883e92191905f98b16081b427e8977b52974a72741047320960f40604cb5fc3a5c83c4a42c3fdd53d37a396763745f2b1822752c24d77227fd204e81fb141ad601a66a19e2617c0f1597413deb137750f1760e5960a92803f6b
|8,0=>0xeb99de82d3b766eb4622a9143a04b99bc37905f98f88b8e3e27ee917c49074dc27364c722b96f2776063b5f6415a6bf5a199555884ea0c4e9124d865460303f40638d2e33e2a2ec812a30527e0f2782124a8822d781fcc11d649173b314de41443912a0c1118e0f4780e04307d1a06f0e057de05127039d402e2e00c17
|9,0=>0xcfbf0afda097a1e7ea1869ee75ab025a0b3469993cbc134d1b31e692602923bdb1c096182a816f1516091
|10,0=>0xeb5f5e3d5992b813ecf2
|11,0=>0xff75e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f000000000000000000a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0cf0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f00f0f0f0f0f0f0f0f0f0f0f0f0e0e0e0e0f0e0f0e0f0e0f0e0f0e0f0e0e0e0e0ef0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a0f0a0f0a0f0a0f0a0f0a0f0a0a0a0a0af0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f00000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000f0f0f0f0f0f0f0f0f000f000f000f000f0f0f0f0f0f0f0f0f000f000f000f00f0f0f0f0f0e0f0e0f0f0f0f0f0e0f0e0f0f0f0f0f0e0f0e0e0e0e0e0e0e0e0ef0f0f0f0f0a0f0a0f0f0f0f0f0a0f0a0f0f0f0f0f0a0f0a0a0a0a0a0a0a0a0a
|0,1=>0xf000f000f000f000f000f00000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f000f000f000f000f00000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f0f0f0f0f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000f0f00000f0f0000f0f0f0f0f0f0f0f0f0f0f0f0f000f000f0f0f0f0f0f0f0f0f0f0f0f0f000f00f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f000f00f0f0f0f0f0f0f000f0f0f0f0f0f0f000f0f0f0f0f0f0f000f0f00000f0f0000f0f0f0f0f0c0f0c0f0f0f0f0f0c0f0c0f0f0f0f0f0c0f0c0c0c0c0c0c0c0c0c00000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f000f0000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f000f00f0f0f0f0f0f0f0f0f0f0f0f000000000f000f000f000f000f000f0000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f000f000f000f000f000f00f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f00000000
|0,2=>0xf0f0f0f000000000f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f0000000000000000000000000000000000000000000000000000f0f0f0f0f000f00f0f0f0f000000000f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f0f000f0000000000f0f0f0f000000000f000f00000000000f0f0f0f000000000f000f000000000000000000f0f0f0f0f0f0f0f00000000000000000f000f000f000f0000f000f000f000f000f000f000f000f000f000f000f000f000000000000000000f000f000f000f000f000f000f000f000f000f000f000f000f000f0000000000f000f000f000f000f000f00000000000f000f000f000f000f000f0000000000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0f000f000f000f000000000000000000f0f0f0f0f000f0000000000000000000f0f0f0f0f000f00f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0f0c0f0c0f0c0f0c0f0c0f0c0c0c0c0c0000000000f000f00000000000f000f00000000000f000f0000000000000000f000f000f0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f000f000f00
|_,_=>0
def sP:Nat→Nat
|0=>0x4cc3591032c938560a09124e1481035c224e3084035d124e34a58b24e30d28308900d10309224e2832c100c3480d224e1440cb54e30a0c62c91540cb24e4cc1032c900c1032c100c20318914a0c20403480c718c3440c22402031c61440c2040
|1=>0xc248938d50a0d72c938c21b0d724e30d21b0d124e3086c344938531010309124e4035cb24e4cd6440d72c938c50a0d12c938c2040d724e14c1032c939314c51c2832c938c50a0c22c938521b0c224e3486c308938535440a68b24e3185cb24e
|2=>0xd708938d28309124e95808b24e4cc34a0cb24030d1032d224e31d2832c938c34840390938d8c40d124e3040d72c939331420a0d124e30a0e22ce30d7542832c938c21b40308938d4032c938f3592040d124e30828380938c34a0d12c939e30a
|3=>0xc244938c8ca0d124e30d6482832c938534a0d72c939330d70a0c224e30d21068b24e30d6501032c938c34a0e02c938c35010344b24e30810344938c2832c939e30d40a0d72c938d40a0d72c93853484035c938d2100d124e1582c939330d210
|4=>0x2832c93853086d00cb24e30d10a0d708b24e31c40344b24e30d29a2c93aa30d64a68b24e30d60a5d12c938c3442832e924e31828b24e32834a0cb24e9cc34a0cb48938c35440a0cb24e30d64a6822c938c34829a08938c34a0d12c939f30d10a
|5=>0x38c35d2832c938c34828308938535d2832c938530d28344b24e32574a0c22c938c34828390938c3596ca0cb24e30d64a0c244938c36c2832c938c34840344938c34a0c22c93a534840308938d10a0d72c938caca0cb24e30d70a0c244938c35c
|6=>0xd12c938c2100cb24e30d40a68b24e30d2832c938c94d2832c93a630d28390b24e30d6ca0cb24e30d28309124e30d6ca0cb24e14c35d64a0cb24e30d2832c93ae30d64a0d72c938c34a0cb24e4cc35d6ca0cb24e30d28308b24e4cc36d2822c9
|7=>0xa0cb24e30d28308b24e30d10a0cb24e30d60a2c938c34a0d12c938c34428308b24e30db4a2c938c34828344938c3582822c938c3482832c938530d64a0cb24e30d2835cb24e14c35928308b24e30d10a
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x154005
|5,0=>0x20606d415603d80a5
|6,0=>0x14984c6115c3f60e583360b1c266
|7,0=>0x641d897609d7a85cdd6b8591d5d755614e751dd3f84de13074a21208465d11842610183e9cf283aa0e3736e0d473320c482f20b482b20a48272095723608581f607671bdc67817e0587
|8,0=>0xcc27288c7e7178c3a7059bf62f58bb62e49b722d39b2e2c29ae66b18aa62a18a69e928a2a28199e6270999e65e995a24e891663d88d622d889621c984e60b880a5fa87ca1e997825d887421c796fe1b786c1da886821979
|9,0=>0x3bc9ed5fad8e9639c9e5238b9e0a77a8dca36a8d8a35a8d4a34a8d0a3399
|10,0=>0xf723d48f35fc58
|11,0=>0x3e47
|_,_=>0
def wAt:=mkWire dB 47 252 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 14
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x40b4d0d44c4b3534a4a0930b4c352cc4d2d2834c3534a4d092cc513128c4b350cf481434c4b293ce481434c4b312ca504434a4a312cc4b352ca514030d4d2d30a4d293c9481434c4b29392514030d4d2d30a4a353ce481434c4b2928b4e494500c3534b4c292cc4a353ce481434c4b29
|1=>0x2ca4b852058d312ca5f354508a312cd514028c4b312cd593708d42292cc452d14a4a2d30d50352ca4a312cd452934c4b2934a4a312cc4b352978d0930b4a3508d42292cc5d374114d2d30a4b2914b4c35297852d30d483535988312ca59372824c2d2ca4d4130b4c2914a4a2d30d4d66
|2=>0x44c4b2928c4b3530d4b2928c4b35283572b44c4b3530a4d092cc4b292cc452b30d4b355cac32908d4f392050d312ca4a354500a312cd4a313428b312ca4d2d20ccd292ca572b44c4b3535988312ca52254500a312cd4d5164dc8312ca4b293504c2d30a481430a4a2d30d4d2920c4d2d
|3=>0x2834b3544cca352cd452f2834c356cbca1530d514028c4b35359902d30a433508a4b3130b4d0d2ca514228c4a352cc4b3520ccd2d2ca483134c4b295cad1312cd4a452cc4b3528b4d0d30a502d34a4c292e54a1630d4a3128d4b3528b4a352cd663540bcc293424c2d30a452d28c4c35
|4=>0x64d48312ca4d312cc4b292054d312ca452b30d4b351024a352cc4d0a2cc4b292d04d4130a4a092cc4b351488a2d30d4b2928c4b352858c2d30d4c292cc4b2944c4a352cd4a9108dcb312914b312cd442d28d4c3540d4c292ca423528d4b3144a4a312cd4d0d08acb3140b4d0d30a5131
|5=>0xb3128d43292cd4a352cc440d28d4a2d2cd43292cc4d312ca48312ca452d30d42292cc4a352cd4c292ca4d0d30a4a1630d502f30a42372cc4a1530d4b312cd4a1530d48312ca440a28d4b3108d42292cc572b44c4b352854c355cac2352cc440d28d4b31
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x330000000006
|6,0=>0x12a88140001b50b284540000c5
|7,0=>0x1788b845a22c11588a9352a28500009d44ca258d2668f445a21d10687f43da1dd0e686f435a19d0c866042e99650aa852327992d09064442098f8c7843841a20c4c5c62a4
|8,0=>0x2a254e3a59d20e8c5433a01cf4e7473739a1cc4e5c72b3941c94e4471f38e1c64e2c7133881c34e147073821c04dfc6fb37c1bd4de46ef3761ba4dce4e43709b78db66d836a9b48d9e6cc3649b18d866c03
|9,0=>0x1732b895bcada56b2b4959caca5632b0957caba55b2ac955caaa5532
|10,0=>0xbc0ddc6ec3751
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 13
def pmP:Nat→Nat
|0=>0x33f819d00bfe057f02bd8108007f6037b00ff807ec0300017f00bd805e802f20130009500484021600db005f801c000bc003a0010000440020000e00068000800020000
|1=>0xabf855ec291e14240a1004fec27e013e009e804ec0273e137b09b8047ec22fe117b08af844001d020d30061002dec16d609b404cf825ec11ae0890040a01fec0efe077b
|2=>0x1917bc0bda4fed22f6897b40fda05ccc2f66100300a18040c00249ff24ea105ec8260277f13b20890040021d7f0ebd874d03a601d2b0e38070c036f61820
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x400004
|6,0=>0x1e2c00c0620009
|7,0=>0x222d1b15485245c02f3ead711a2a0cb90c1990114951bd804032b3524aa7481c3b526f1d8e
|8,0=>0x2a30204e92cad560ca554d8cd706112a752184b993e31eb36a19cb138b336cd02bf40de14c32dd31d425a3c5
|9,0=>0x31ac82e2a751dd1c335d3166141f50
|10,0=>0x6052d9b
|11,0=>0x13
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 7 (j%128);fld (pmP (k/32)) 17 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_250 10 roots_250 ops++addP pm 1 dom_249 10 roots_249 ops++addP pm 2 dom_91 7 roots_91 ops++addP pm 3 dom_235 10 roots_235 ops++addP pm 4 dom_243 9 roots_243 ops++addP pm 5 dom_219 9 roots_219 ops++addP pm 6 dom_187 9 roots_187 ops++addP pm 7 dom_155 6 roots_155 ops++addP pm 8 dom_123 9 roots_123 ops++addP pm 9 dom_211 6 roots_211 ops++addP pm 10 dom_115 6 roots_115 ops++addP pm 11 dom_59 6 roots_59 ops++addP pm 12 dom_179 6 roots_179 ops++addP pm 13 dom_83 4 roots_83 ops++addP pm 14 dom_27 4 roots_27 ops++addP pm 15 dzo_235_16 9 roots_235 ops++addP pm 16 dom_203 8 roots_203 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_251 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_235_16_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_203 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_250 10 s (0,roots_250.map (·&&&dom_250)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_251 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_250 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff00000000ffffffff00000000,96)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)],[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_251==dom_251)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_251 gM v ys):RunD true dom_251 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_251 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 5 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 8 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 42 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 42 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 50 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 50 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 17 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 17 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 4 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_251 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤11) (h:RunD true dom_251 gM s xsM):False:=by
  have hmin:6≤s:=by have hl:=run_len h;change 7≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_251 roots_251 goal_251 12:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_251
theorem lowS_251:Lower true dom_251 roots_251 goal_251 12:=S_251.noCircuit
def dzo_238_16:=0x5555000055550000555500005555000055550000555500005555000055550000
def gzo_238_16:=0x5555000055550000555500005554000055550000555400005554000054540000
def gsh_238_16:=0x555500005555000055550000555400005555000055540000555400005454
theorem lowS_zo_238_16_232:Lower true dzo_238_16 roots_238 gzo_238_16 9:=lower_iso_b (d1:=dom_238) (r1:=roots_238) (T1:=gsh_238_16) [(dom_238,16)] (by decide +kernel) (lower_slice_b (T:=gsh_238_16) [(0x444400004444000044440000444400004444000044440000444400004444,0,2),(0x505000005050000050500000505000005050000050500000505000005050,0,4)] (by decide +kernel) lowS_232)
namespace S_254
def pG:List (Nat×Nat):=[(2,18),(2,34),(2,130),(4,20),(4,68),(4,132),(6,22),(6,38),(6,70),(6,134),(8,40),(8,72),(8,136),(10,26),(10,42),(10,74),(10,138),(12,28),(12,44),(12,76),(12,140),(14,30),(14,46),(14,78),(14,142),(16,18),(16,20),(24,26),(24,28),(24,56),(24,88),(24,152),(32,34),(32,40),(32,96),(32,160),(36,38),(36,44),(36,52),(36,100),(36,164),(48,50),(48,52),(48,56),(48,112),(48,176),(64,68),(64,72),(64,96),(64,192),(66,70),(66,74),(66,82),(66,98),(66,194),(80,82),(80,84),(80,88),(80,112),(80,208),(128,130),(128,132),(128,136),(128,160),(128,192),(144,146),(144,148),(144,152),(144,176),(144,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffffffffffff
def xsM:=roots_254.map (·&&&dom_254)
def gM:=goal_254&&&dom_254
def NN:Nat→Nat
|6=>7
|7=>18
|8=>18
|9=>11
|10=>4
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0xed29fc3d7958756521c02ac4e23c0109fb1
|7,0=>0xf60b2edad6e0542c45b0b701c715fe661cf5cba3579ae52b311dfc01def11c0951be5b13e7f1044f0c7bf0a922
|8,0=>0xd6694a6900949a57641671f6f6b9bd66b405aaf75831f4cef038680300a427e8e1ca0611fad0e23e0a80e06b7e
|9,0=>0x92a018d8f46c32e60eff5b1cb54eb630a152ddff2ace10886a05515
|10,0=>0xbddde8a4255e2e92224d
|11,0=>0xba90f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaa00aa00aa00aa000000000000000000aa00aa000000015555555400000001555555540000000155555554000000015555555400000002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa8000000055555555555555555555555555555555555555550000000055555555000000000000000000000000000000000000000000aa00aa00aa00aa00aa00aa0000000155555555555555540000000000000001555555555555555400000000000000000000000002a802a80000000002a802a80000000002a802a80000000000000000000000000000000000000000000000055555555555555555555555500000000aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa000000000000000001555555555555555400000000000000015555555400000002aaa80002aaa80002aaa80002aaa80002aaa80002aaa80002aaa80002aaa800050505050505050505050505050505050505050505050505050505050505050508888888888888888888888888888888888888888888888888888888888888888015401540154015401540154015401540154015401540154015401540000000000000002aaaaaaa800000002aaaaaaa800000002aaaaaaa80000000000000005555555555555555555555555555555500000000000000000000000000000000
|0,1=>0xaaaa0000aaaa0000aaaa0000aaaa00015555555555555555555555555555555555540001555400015554000155540002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa80000000000000005555555555555555555555550000000055555555555555555555555500000000
|_,_=>0
def sP:Nat→Nat
|0=>0x718a418a206a1c520c4a314e41840c7148312d50718a41880e290627c408638a418950430c53906d438c53906d29062504102906f481a520de9035c520d6f438c520c4c2906b5250629c83098a418820
|1=>0x718a720e30718a720c08638a720d4d838a4189406b8c539071031c520c4a0418629c83035c629c83030c5390710c0c539061041c520c4f034c539061035c520c4f021c629c838a1c629c836b8a41896a
|2=>0x1c40d838a720d4083a4720d40821c53906a031c629c83501c53906a081b0718a720c0e290625020c29c838c1c520c4a0350e29c838a9c629c83881a8714e41aa08714e41c5ae290628a80d714831280c
|3=>0x38a720d4074ce41a810714e41a80e91c835018e29c835018e29c838aa0e99c83501ae29c838a80d714e41a808714e41a810714e4
|_=>0
def sO:Nat→Nat→Nat
|6,0=>0xa9c46e1c70ab839c0ee007
|7,0=>0x16f0af853c27e12f08f8443a020f1070834b9860b3051824c1060730318
|8,0=>0x29334279dbcce25532288d444a21330187cc3c61d30e096bcb3e18f0bf8
|9,0=>0x69a33d1959c6c6162fb1749b6458e6b53528
|10,0=>0xe2bef636cfae8
|11,0=>0x1cc7
|_,_=>0
def wAt:=mkWire dB 20 255 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x7296bb6ab80172912b8017296ab6838b95018036ab8017291038017296ab69f8b950180369f8017297466ab8b950110369f62970169f6ab80172950a69f8b950169f68362970153280370153268362970174669f8b950112b69f80110369f629
|1=>0x5016ab80172969f80172970150172969f8017296838b95016ab8b950168380172980350172969f8b950169f80172962b5017016ab80172968362970169f8017296ab8b950169f6297015327015396ab80172962b5016bb6ab80172912b69f801
|2=>0x2837292817015017017292838b950180172980372950172980172972928180372962b7018bb
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x33000000000003000000
|7,0=>0x4724343f43b43833443042d32942542141d41941541140e30a4064
|8,0=>0x7c37937637337036d36a36736436135e35b35835535234f34c3493
|9,0=>0x9329128f28d28b28928728528328127f2
|10,0=>0x981971961951
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 12
def pmP:Nat→Nat
|0=>0x39fc3f77edfd9f93f17e26c3f85707e0ec1b8300340600b0120200280300500600800800
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x80000800
|7,0=>0x4641ce561c815206a194e1
|8,0=>0x255ad6116bd357cf0b855ee
|9,0=>0x5696ad6b7adf35
|10,0=>0xa56b5
|11,0=>0x15
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 11 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_252 10 roots_252 ops++addP pm 1 dom_222 9 roots_222 ops++addP pm 2 dom_190 9 roots_190 ops++addP pm 3 dom_126 9 roots_126 ops++addP pm 4 dom_246 10 roots_246 ops++addP pm 5 dom_250 10 roots_250 ops++addP pm 6 dom_62 5 roots_62 ops++addP pm 7 dom_158 5 roots_158 ops++addP pm 8 dom_238 9 roots_238 ops++addP pm 9 dzo_238_16 9 roots_238 ops++addP pm 10 dom_94 5 roots_94 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_254 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_238 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_238_16_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_94 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_252 10 s (0,roots_252.map (·&&&dom_252)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_254 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_252 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_254==dom_254)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_254 gM v ys):RunD true dom_254 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_254 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 7 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 18 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 18 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 18 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 18 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 11 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 11 0 = true)
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
def isoMvS_223:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_223:Lower true dom_223 roots_223 goal_223 11:=lower_iso_b isoMvS_223 (by decide +kernel) lowS_191
def isoMvS_253:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_253:Lower true dom_253 roots_253 goal_253 12:=lower_iso_b isoMvS_253 (by decide +kernel) lowS_251
def dzo_93_2:=0xcccccccc00000000cccccccc
def gzo_93_2:=0xccccccc800000000cccc8800
def gsh_93_2:=0x333333320000000033332200
theorem lowS_zo_93_2_77:Lower true dzo_93_2 roots_93 gzo_93_2 6:=lower_iso_b (d1:=dom_93) (r1:=roots_93) (T1:=gsh_93_2) [(dom_93,2)] (by decide +kernel) (lower_slice_b (T:=gsh_93_2) [(0x333300000000000033330000,0,16)] (by decide +kernel) lowS_77)
def dzo_239_16:=0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
def gzo_239_16:=0xffff0000ffff0000ffff0000fffe0000ffff0000fffe0000fffe0000fefe0000
def gsh_239_16:=0xffff0000ffff0000ffff0000fffe0000ffff0000fffe0000fffe0000fefe
theorem lowS_zo_239_16_232:Lower true dzo_239_16 roots_239 gzo_239_16 10:=lower_iso_b (d1:=dom_239) (r1:=roots_239) (T1:=gsh_239_16) [(dom_239,16)] (by decide +kernel) (lower_slice_b (T:=gsh_239_16) [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,0,1),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,0,2),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,0,4)] (by decide +kernel) lowS_232)
def dzo_111_16:=0xffff0000ffff0000ffff0000ffff0000
def gzo_111_16:=0xffff0000fffe0000fffe0000fefe0000
def gsh_111_16:=0xffff0000fffe0000fffe0000fefe
theorem lowS_zo_111_16_104:Lower true dzo_111_16 roots_111 gzo_111_16 7:=lower_iso_b (d1:=dom_111) (r1:=roots_111) (T1:=gsh_111_16) [(dom_111,16)] (by decide +kernel) (lower_slice_b (T:=gsh_111_16) [(0xaaaa0000aaaa0000aaaa0000aaaa,0,1),(0xcccc0000cccc0000cccc0000cccc,0,2),(0xf0f00000f0f00000f0f00000f0f0,0,4)] (by decide +kernel) lowS_104)
def dzo_207_16:=0xffff000000000000ffff000000000000ffff000000000000ffff0000
def gzo_207_16:=0xffff000000000000fffe000000000000fffe000000000000fefe0000
def gsh_207_16:=0xffff000000000000fffe000000000000fffe000000000000fefe
theorem lowS_zo_207_16_200:Lower true dzo_207_16 roots_207 gzo_207_16 7:=lower_iso_b (d1:=dom_207) (r1:=roots_207) (T1:=gsh_207_16) [(dom_207,16)] (by decide +kernel) (lower_slice_b (T:=gsh_207_16) [(0xaaaa000000000000aaaa000000000000aaaa000000000000aaaa,0,1),(0xcccc000000000000cccc000000000000cccc000000000000cccc,0,2),(0xf0f0000000000000f0f0000000000000f0f0000000000000f0f0,0,4)] (by decide +kernel) lowS_200)
def dzo_231_16:=0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000
def gzo_231_16:=0xff000000ff000000ff000000fe000000ff000000fe000000fe000000fe0000
def gsh_231_16:=0xff000000ff000000ff000000fe000000ff000000fe000000fe000000fe
theorem lowS_zo_231_16_224:Lower true dzo_231_16 roots_231 gzo_231_16 7:=lower_iso_b (d1:=dom_231) (r1:=roots_231) (T1:=gsh_231_16) [(dom_231,16)] (by decide +kernel) (lower_slice_b (T:=gsh_231_16) [(0xaa000000aa000000aa000000aa000000aa000000aa000000aa000000aa,0,1),(0xcc000000cc000000cc000000cc000000cc000000cc000000cc000000cc,0,2),(0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f0,0,4)] (by decide +kernel) lowS_224)
def dzo_237_16:=0x3333000033330000333300003333000033330000333300003333000033330000
def gzo_237_16:=0x3333000033330000333300003332000033330000333200003332000032320000
def gsh_237_16:=0x333300003333000033330000333200003333000033320000333200003232
theorem lowS_zo_237_16_232:Lower true dzo_237_16 roots_237 gzo_237_16 9:=lower_iso_b (d1:=dom_237) (r1:=roots_237) (T1:=gsh_237_16) [(dom_237,16)] (by decide +kernel) (lower_slice_b (T:=gsh_237_16) [(0x222200002222000022220000222200002222000022220000222200002222,0,1),(0x303000003030000030300000303000003030000030300000303000003030,0,4)] (by decide +kernel) lowS_232)
namespace S_255
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(1,129),(2,18),(2,34),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(4,20),(4,68),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(6,22),(6,38),(6,70),(6,134),(7,15),(7,23),(7,39),(7,71),(7,135),(8,9),(8,40),(8,72),(8,136),(10,11),(10,26),(10,42),(10,74),(10,138),(12,13),(12,28),(12,44),(12,76),(12,140),(14,15),(14,30),(14,46),(14,78),(14,142),(16,17),(16,18),(16,20),(24,25),(24,26),(24,28),(24,56),(24,88),(24,152),(32,33),(32,34),(32,40),(32,96),(32,160),(36,37),(36,38),(36,44),(36,52),(36,100),(36,164),(48,49),(48,50),(48,52),(48,56),(48,112),(48,176),(64,65),(64,68),(64,72),(64,96),(64,192),(66,67),(66,70),(66,74),(66,82),(66,98),(66,194),(80,81),(80,82),(80,84),(80,88),(80,112),(80,208),(128,129),(128,130),(128,132),(128,136),(128,160),(128,192),(144,145),(144,146),(144,148),(144,152),(144,176),(144,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffffffffffffffffffff
def xsM:=roots_255.map (·&&&dom_255)
def gM:=goal_255&&&dom_255
def NN:Nat→Nat
|5=>1
|6=>9
|7=>103
|8=>524
|9=>661
|10=>268
|11=>51
|12=>9
|13=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0x60df6
|6,0=>0x9a6919803d9118f8fc61692f72746724c2b1589f0c6fd
|7,0=>0xfe9d1f3a47f25feed0afe51d2e118edf14ed3938cbd6cc94b3c80a0c4b4cbe5e1bdb4bb3792ad31aad24fabf8caaeacaaa0da5b98a51a3a43c2a3cd09eb9f9d70e9d0c79a5969538294a2e9430894207928058c77588fa3849bb7d9a87a7d078f537756977175761317381b6e0e0692bd66cd46218459d5f574965687551adf4fd304d38d491f747f5e423f5416a740e7e401bb3e576397e038eec362623573d3391f312d52e9982e1682dfba2cd762c4f12c2902b8ff2ad1f2a4df28f522804827dc127ca3278f2274df2747e26bdc26b3721fe41ed491e3901b7931a7d51901018fd6165a811b91107c10a49408ed30868008294066fd063cb05ae3008c40084c
|8,0=>0x2826227e2426ba026ae92681825fd625bfb25b58259a7257ec24f69245972400023f982327922f3122d28227f02276a2200421dc12169a2074f206e120286200421f5a41f1d01ef751ea531e3881e2a41d84d1cda61c81c1c4d21bf881bf141be871afae1ac5b1a36119ebc19e77190cf18fac1848618046174401704f16e86168271673b165b515f8b1543314f7d14ae31481b1403713f39138c113839131c913129129c1109b7103ab1019d0fc500fbc60efa60ec760ebd30eb920e8080dd0d0dcc20d9af0d93a0d5af0c53c0bab50baa20b6f80b3380ad8309e7509862095f90959008781087730832907cf30764d0760d075a8074820716006c830675105fb805fa505f3d05ae304bed04be80474d0458304253034980319c02fa3029950283201f3e0160c014b001437013bd00c140093b0071800558003f7003a9001f3
|8,1=>0x543075415f5407053abf539d05350c52aa452a2852a0b528cd5228051f9a5185c513d150e01501cd4fd724f78d4f6e64f2324eac44e9404e8004d4d84ced74c2204be0e4b8f04b5164a6234a51b4a1624a05c49a0f492d54884747c5d4795447715473bd4697f4686b45596451a244d1b44ab04414d43a1a4370c436ce42ceb4276e42380422a041a7b4190c412bc408173ff983f4e93eeb63eeb23e4203dd5f3db913d1963c6803c4073c3203b3743a15f39bad39a5438fd638c1d37bac371ff3700f36e57365203624835e5e359593516434e30345c33445233ef533d74336df332ad32d3b32956328da3275231bd130fd630dd62f5692f36d2eddd2e62d2e4402e3432dcd52d7322d2552d0382c9312c6642bffb2bff82bb5f2b8152b5cb2b2e22ac932a4f62a40229cc3297ee295dc2949d2908028f5228eed28ea2288b4
|8,2=>0x8d1158cd198c2558be918b47d8b4348b17b8aec68aeba8982e895cb8928987cf98783c875d9874d3865bd8603f85a55859d2858f084f2f84e4e84adc848da8456e83b3483597831c782004814d1807087fa697f89d7f2757f1077ec787e9877e5547dce57d8487d7727d6fb7d4547d24b7cf5b7ccc37c9be7b0de7b0937af427aa3c7a90a7a1b677ad0778a976717760d37604175c8b7557374d0f746d9743a073be673854730d872fb372b5a723777169270d9370d376fcdf6f1666e5096db8c6da3d6d9646d58d6d2606d04e6c3356bff16bef36a7fc6a5856a57f6a4a369a4169a15699f66787e678556720e66d7f6656165699646dd645ba63ca463c3061b3e6108260d7a60b2c604775fac95f8bd5ed755ebb35ddb75dd045dab95d6535d3735c6b85b87f5b02f5ab9b597a15914157a1255ee85527f5470554415543e2
|8,3=>0xe6352e5df5e23a9e164edc242db332db1cedab9bd9514d74d6d68dad58add5619d543ed34fad23dbd11bad0882d056ccfb63cec7acdaedcc71acbfd1cb2b2caf61caf4eca81cc9dfac97e9c8286c74d7c6b84c67fbc6360c5e37c5c06c3313c2909c2089c15b9c08e3c0867c0556c02c2bfe48bef4abee7bbea22bd8acbcc2cbc56dbbc32bbbe7bb45ebabbcba80bba73fb9762b9706b92ffb8b6eb878bb83fdb76deb522db42d6b0e50b0cb2b01ebaf9ccaf280aeb54aead1ae538adb38adab1acfeaacbbfab6f7ab2d5a9620a88eea743aa59bca5260a4a10a4190a3c96a315fa30a6a287ea2387a0f209ef629e1a79da279d9439cdbb9bfd79b95b9b8759b3969b3759afd89a901986ca9859e97bcb97ae99755b96c7f957e6948ea94617935fa934f19318392a23922e391d6791d5590e7d9091c8f18d8eeec8ec938e636
|8,4=>0xffa9ef7633eff73ee86bec0e0eb3c1eb162eaaa1ea1e6e7b4ee7430e6aee
|9,0=>0x1ddb11d83c1d6a31d6531d36c1d1631d11b1cb521c7941c2301c1bf1bc441ba111b3001b0cc1a8401989f19894197291962d18fe118fbe18daa18c4d18c36185f71785d1779e174a616f801664c1636716261160e115f8c15d1e15a371565d155e7155ca153f214f5614c9014a6914472142a913d8913a5c1395413647135d613423133f7131b11312912f5812b521259c11d9211d8b11b8811b8211a9b1113110f24109b2108ca10356100b20ff950fefb0feb60fdf70fcf20f11a0eec60e63c0e3b00dfb80d7a20d4610d3dd0cb690cacb0c9290c8460bf5a0b67c0b3ef0b0da0aa550a7670a0ee093240923b086770851c0837407eb207c2f07a160720706d91069140688f0675606467062a2058aa05252050c704f2304c230462804411041b904024035d0034e802c9901de401346010dd00e1a00c14008310038c00353
|9,1=>0x425d1423194106b40e4240e2b40b974020e401153f6ee3f1cd3ea363e5f53e3ec3dfe83d9603cebd3c6923c42a3b7d93b7ad3b0af3a9a63a6393a2773996838fe938d623846a3830037d2e3754b373e23719536e3436aaf369793672e366f1363f83631f35c32352e233df933b5c332763308f32fa33272f326493204831f9a30af730859304082fedf2fd592f7d82f7a52f3a62ea202e88d2df4c2ddeb2dd772d47a2cd3b2c8882c8662c7c82c07b2bd782b9712b92c2b0ff2b0592ad082ac732a25629c432966f2949d2940a291bb28fe528f8f28c732836f27c0026dc226ce726c2f269ac2655425fcf25d5825c3625176248112422f2381d233b722c5c229ed226e22223e21e152167c21669216512160121586213e9210d920e702081320660204482020a200bb1fb1f1faea1fa831f5de1f0921e84c1e2ca1e23c1e05c
|9,2=>0x686ba6859b680ad67b846745166b7d65893654e46511f648936460d643836437163f0b63c9d638526380762b6b6241f6227a621b061571611be6100d6081a6069560575603845f0de5eec65ee1e5e9e65e8dc5e8045e3905da445c5c35c52a5c2b35c15b5be9c5bbca5b7955b5f25b4d05b2fb5afc45abad5a7eb5a5f95a3ed5a2445a18159de959973598dd5976f58cd257f5657e9f57acb579f65745a5724c5652d55cec556b7552455403253ffb539a252cb752792524a0517815168b514605109650b5e50a4f507045039f4fe504fe1e4f9aa4f8984ed2f4eafb4d1304cf474cbbf4ca644c9254c6de4b7014adab4abfd4a8b54a5644935c48df647d28478b9473924715d46e1346b1f46aa74643e463a24635745f97459f3453f845388452df450b344ebe44eb244b8344ae54403143c674388f437674314b430e64262a
|9,3=>0x9408393a2f939239313a92d1092789925469160590fef90c37900968fddf8fd708fb9c8f2818e90f8e7a98df328dc7d8d3f28d26b8d15e8c3fb8c1538b2f48ad718abaf8993089889891bd890fc8902888fc2887128849387ce68755886d7385e5785d9e85cbf85abb853ff84fff84db184d0382d6982b4b82af5829ca82975828d28232f819968182180fb080d5d80d06801e87f58a7f3c97efe77ea7a7e6f77e09b7dc997d76b7c8a97b72b7b18d7a33278d1078c38785a677f3677ddd77a4f776bd77602774fc774cd768cc74e65748e973ebb73a7a73a2a731e77319c722ce722017210171995717357106170f5c7058d704ad7010f6ff426fb6c6f9506f5a46f59f6f2236ebd06e9ff6e35a6e1846d9446cf206ca8d6c9c56c2816be596b8916b3e16b0df6a82e6a3b86a0a86a00469f5e6979e6940d6938968c08687f7
|9,4=>0xe03f6deafbddbe4dd227dcb97dae62daafed944bd881fd78d7d779dd6814d642cd4a93d4873d3f94d28d7d2470d1b43d0ffecfe4bcf24fcdf46cdcb2cd73dcd227cd0feccf93ccb7ecb499ca170c9662c91fcc78c0c6dbbc67fbc5288c4825c3e5fc3917c3681c3299c1a72c1941c0924bf6eebf35abda0dbd72dbc927bbf39bb7a2bb274b90ebb8f7cb825db80ddb7791b75e3b622eb60d8b5d85b5d61b5950b4eacb4d6db3d12b3cf0b39e5b3075b1d9fb024fafd77aef75aed00aea8fae5aaae0e7ade92ac370abfe0abc33aa706a966aa9603a934ba8c01a862ca6d39a6b0ba61d1a57fea4ce2a4b6da3e4ca3311a2c10a243aa1ca9a17b4a1633a1119a0cc4a05d5a055da010f9ef349eedd9e6269e3b79d4cb9be5e9bd3b9b9d498f469890f988ff9863d9861f9759c972a396d839654c96100955e8953e694d5694766
|9,5=>0xfe561fcbaefa902f6a5ef68d9f64a4f4851f2b9af2409f1444f0a42eeff3eb162eb0d1e8416e788de6f04e61e5e564ce114de047e
|10,0=>0x510be50eb5509204f32f4cc924c6e24c1f54ba564a6314a3f749d634922848610486094840047bba46faa46f5b46f45461c4461c344eb64334942eca421e141f243fe5b3fc573ef4d3e0023dd833d15a3b77f3a75638d17382cb3769836dd1363c8356c13514f34bf73431132a29309b82f5bb2f0f32e8d32e4ca2cad02c30b2be292b9712b6b82b2872a88d295b62949d2932428aa1265e525bc1258c625442248ff2464b2455424534242d4235762338d22e1922b6222174217b21fe5b1fa2f1f4311e7a91e4861d7731beb61946c1857c1846a174ea16229157fe151771498714848140aa13a79138941363312c98120b511c43117b90fbad0fb3a0f8be0ec2c0db9a0d9400d71b0d2920c1060bfed0b3ec0a27f08e57070040658b058c6052c705297048d1043b404302027f5023e10206901f910118b0115b00e20007c8
|10,1=>0xe1775e114bdbb81db57fdaeced9971d992fd35f6d24bbd0629ce3e8ce136cb499c9e02c4335c42c5c33d7c1cfbbe74abca90bc4c1bc265bb9beba5a1b7efab6ce2b60a6b5a8cb51abb460ab0edfb021cb0167afe2aaf747af10badfe9ad4eaac39ba9e6da9aa4a863aa6899a482ca3112a2b93a0dbc9cb2d9c83c99f929935d987619788495d31959f69569c8ea0f8c9de8b7eb8b18a8a022896bc892ae8821388008875dc86aa583771807e37fbf17eed27d5027bd597b96d7b92b79eba79afe78bd6775b775406737b1712de711fc70c48700b96ec756da606bdfe6b06e6a3bc694ae68abd683266828367fe9673fb672ca662c1652c9647796370d632cb6308d62a5661a5e60a11607f96074660582602475f32b5e4bd5c9eb5beeb5a0ae59ce35977858baa58b755766756b6b54b48549fb53e2e5345e5285951f43512f6
|10,2=>0xff0defeb23fe383fc286f8d20f61c2f4b0ff1126eed0ce6abbe496ee384f
|11,0=>0xf0aa6ef327e85cddf1abdea9bd53aad3556cfa0dcd2dacc483cc1b8ca99ac6aa4c6279b63afb34e5ad9969d0a19b02d96cf9854997e7517e4387dbf67d4357939b71ffd6e56e641286159158c2f50bf84a3c245f5143a9539366388e736f152f5652a1bc214fe1c9381b7741a8bb1424a13088127db0e32d0b99a0730c01c32
|12,0=>0xd709ba74e69736a8f4ad8d5697ec633155a12dcb11ebd
|13,0=>0x4766c
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffffff00ff00ff00ff00ffffffff00000000ff00ff0000000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffeeffeeffeeffeeffffffffeeeeeeeeffeeffeeeeeeeeeeffffffffffffffffffaaffaaffaaffaaffffffffaaaaaaaaffaaffaaaaaaaaaaffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ffffffffffaaffaaffffffffffaaffaaffffffffffaaffaaaaaaaaaaaaaaaaaa3333333333333333333333333333333333333333333300003333333333330000
|0,1=>0x3333333333333333333333333333333333333333333333333333333333333300ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000ffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000ffffffffffccffccffffffffffccffccffffffffffccffcccccccccccccccccc0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0000fffffffffffafffafffffffffffafffafffffffffffafffafafafafafafafafaffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffff0000fffffffffffffffffffafffafffafffafffffffffafafafafffafffafafafafaffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000ffffffffff00ff00ffffffffff00ff00ffffffffff00ff000000000000000000ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffff00ffffff00ffffffffffffffffffffff00ffffff00cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
|0,2=>0xf0f0fffff0f0fff0f0f0fffff0f0fff0f0f0fffff0f0fff0f0f0fffff0f0fff0000000000000000000ff00ff0000000000000000ffffffff00ff00ffff00ff00ffffffffffeeffeeffffffffffeeffeeffffffffffeeffeeeeeeeeeeeeeeeeeeffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff00000000000000000000000000000000000000ff00ff00ff00ff00ff00ff000000000000000000000000000000000000000000000000ffffffff00000000ff00ff000000000000000000ffffffffffffffff0000000000000000ffffffffffffff0000000000ffffffff00000000ffffffff00000000ffffffff00000000ff00ff00ffffffffffffffffffffffffff00ff00ffffffffffffffffffffffffff00ff003333333333333333333333333333333333333333333333333333333333330000000000000000000000000000000000000000000000000000ffffffffff00ff0000000000ffffffff00000000ff00ff0000000000ffffffff00000000ff00ff00ffffffffffffffffffffffffffffffffffffffffffffffffff00ff00ff00ff0000000000000000000000000000000000ffffffffffffffffffffffffff00ff000000000000000000ffffffffff00ff000000000000000000ffffffffff00ff0000ff00ff00ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff00000000
|0,3=>0xff00ff00000000000000000000000000ff00ffffffffffff00ff00ffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00000000ffffffffffffffffffffffffffffffff00000000ffffffff00000000ff00ff0000000000000000000000000000000000ffffffffffffffffffffffffffffff00ffffffffffffffffffffffffffffffffffffffffffffffffffffff00ffffff000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f0f0f0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00000000ffffffffffffff00ffffffffffffff00ffffffffffffff00ffffffffffffff000000ffff0000ffff0000ff000000ff000000ffff0000ffff0000ff000000ff00ffffffffffffffffffffffffffffffffffffffffffffff00ffffffffffffff003333333333333333333333333333333333333333333333003333333333333300ffffffffffffffffffffffffffffffffffffffffff00ff00ffffffffff00ff00555555555555555555555555555555555555555555555555555555555555550000000000000000000000000000000000ffffffffffffffffffffffff00000000ccccffffccccffffccccffccccccffccccccffffccccffffccccffccccccffcc0000ffff0000ff000000ffff0000ff000000ffff0000ff000000ffff0000ff00
|0,4=>0xfffffffffffffffffff0fff0fff0fff0fffffffff0f0f0f0fff0fff0f0f0f0f00000000000ff00ff00000000000000000000000000ff00ffff00ff00ff00ff00ffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00003333003333330033333300333333003333330033333300333333003333330000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ffffffffffffffffffffffffffffffff0000ffff0000ff000000ffff0000ff00ffffffffffffffffffffffffffffff00ffffffffffffffffffffffffffffff000000000000ff00ff00000000000000000000000000ff00ffffffffff00000000ffffffffffffffffffffffffffffffff0000000000000000ffffffffff00ff00ffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000ff00ffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ff000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff000000ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00000000000000000000ffffffffffffffff0000000000000000ffffffffff00ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000000000000000000000000000000000000000000000ffffffffffffffffff00ff00ff00ff00
|0,5=>0xffffffffffffffff0000000000000000ffffffffffffffffffffffffff00ff000000000000000000ffffffffffffffff0000000000000000ffffffff000000000000ffff0000ffff0000ffff0000ffff0000ffff0000ff000000ffff0000ff000000000000000000000000000000000000000000000000000000ffff0000ff00ffffffffffffffffffffffffffffffff00000000000000000000ffff0000ff000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f000000ffff0000ffff0000ffff000000000000ffff0000ffff0000ffff00000000ffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000000000000000ffffffff00000000ffffffff00000000ffffffff00000000ffffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00ff00000000333300003333000033333333333333333333000033330000333333333333330000000000000000000000000000000000ffffffffff00ff00ffffffffff00ff00ffff0000ffff00ffffff0000ffff00ffffff0000ffff00ffffff0000ffff00000000000000ff00ff0000000000ff00ff0000000000ff00ff00000000000000000f0f00000f0f000f0f0f00000f0f000f0f0f00000f0f000f0f0f00000f0f0000
|0,6=>0xffffffff0000ffffffffffff0000ff00ffffffff0000ffffffffffff0000ff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fffff0f0fff03333333333333333333333333333333333330033333300333333003333330000ffffffffffffffff0000ffff0000ff00ffffffffffffffff0000ffff0000ff0000ff00ff00ff00ff000000000000000000ff00ff00ff00ff00ff00ff00000000000000000000000000ff00ff00ff00ff00000000ffffffff00000000ff00ff000000ffff0000ffff0000ffff0000ff000000ffff0000ffff0000ffff0000ff00000000000000000000ff00ff00ff00ff000000000000000000ff00ff0000000000000000ffffffff000000000000000000000000ffffffff00000000ff00ff000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff00000000000000000000000000ff00ff0000000000000000ffffffff00ff00ff00000000ffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffff000f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f00ff00ffffff00ffffff00ffffff00ff00ff00ffffff00ffffff00ffffff00ff00ff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ffffffffff00ff003333330033333300333333333333333333333300333333003333333333333300
|0,7=>0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff00ffffffffffffffffffffffffffffffff0000ffff0000ffff0000ff000000ff00ffff0000ffff0000ffffffffffffffffffff0000ffff0000ffffffffffffff000f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f0000ffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000ff00ffffffffffffffffffffffffffffffffffff0000ffff0000ffffffffffffff00333333333333333333333333333333333333000033330000333333333333330033333333333333333333003333330033333333333333333333330033333300000000000000000000ff00ff00ff00ff000000000000000000ffffffffff00ff00000000000000000000ff00ff0000000000000000ff00ff0000ff00ffff00ff00ffff0000ffff0000ffff00ffffff00ffffff000000000000ffff00ff00000000ffffffffffffffffffff00ffffff00ffffffffffffffffffffff00ff000000000f0f0f0f0f0f0f0f0f0f000f0f0f000f0f0f0f0f0f0f0f0f0f0f000f0f0f0000ffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00000000ff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffffffffffffffff00ff0000000000ff00ff0000000000ff00ff0000000000ffffffff00000000ff00ff00
|0,8=>0xff00ff00ff00ff000000000000000000ff00ff00ff000000000000000000000000000000000000000000000000ffff000000000000ff00ffffffff00000000ffffffff00000000ffffffff0000ffffffffffff0000ff00ffff0000ffff00ffffff0000ffff00ffffff0000ffff00ff0000000000000000ffffff00ffffffffffffff00ffffffffffffff00ffffffffff00ff00ff00ff0000ff00ff0000000000ff00ff0000000000ff00ff00ff00ff00ff00ff00000000ffffffffffffffffffff00ffffff00ffffffffffffffffffffff00ffffff00000000ffff0000ffff00ffffff00ffffff0000ffff0000ffff00ffffff0000ff000000000000000000ffffffff000000000000000000000000ffffffffff00ff00ffffff00ffffff00ffffffffffffffffffffff00ffffff00ffffffffffffff00ffff0000ffff0000ffff00ffffff00ffffff0000ffff0000ffff00ffffff00003333000033330000333300333333003333330000333300003333003333330000ffffffff00000000ffffffff00000000ffffffffffffffffffffffffff00ff00ffffffffffffffffffffffffffffffffffff00ffffff00ffffff00ffffff0000ff00ff00ff00ff00ff00ff0000000000ff00ff00ffffffffff00ff0000000000ffffffffff00ff000000000000000000ffffffffff00ff0000000000ff00ff00
|0,9=>0xffffffff0000ffffffffffff0000ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff0000ffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00000000ffff0000ffff0000ffff0000ffff00000000000000000000ffff0000ff000000000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff00000000000000000000ffffffffffffffff0000000000000000ffffffffffff0000ff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ffffffffffffff0000000000000000000000000000000000ff00ffffff00ffffff00ffffff00ff00ffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffff000000000000ffffffff00000000ffffffff00000000ffffffff00000000000000000f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f00000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000ffffffffff00ffffffffffffff00ffffffffffffff00ffffffffffffff00ff00ffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ff00fffffffffff0fff0fffffffffff0fff0fffffffffff0fff0f0f0f0f0f0f0f0f0ffffffffffffffffffccffccffccffccffffffffccccccccffccffcccccccccc
|0,10=>0xffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff0000ff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ff00ff00ff00ff00ffffff00ffffff00ffffff00ffffff00ffffff00ff00ff00ffffff00ff000000000000000000ff00ffffff00ffff0000000000000000ff00ffffff00ff000000ffff0000ffff0000ffff0000ffff0000ffff000000000000ffff00000000ffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff000000000000ffff0000ffff00000000000000000000ffff0000ffff0000ffff0000ff00000000000000000000000000000000000000ffff0000ffff0000ff000000ff00ffffff00ffffff00ffffff00ffffff00ffffffffffffffffffffffffffffff00ffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000ff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ff00ffffffffffffffffffffff00ffffff00ffffffff00000000ffffff0000000000ffffffffffffff00ffffffffffffff00ffffffffffffff00ffff0000ffff0000000000000000000000000000000000000000ffff0000ffff0000ffff0000ff00000000000000ffff000000000000ffff000000000000ffff000000000000ff00ffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000ff00
|0,11=>0xffffffff00000000ffffffff00000000ffffff0000000000ffffff00ffffffffffffffffffffffffffffffffffffff00ffffff00ffffff00ffffff00ffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffff00ffffffffffffffffffffffffffffffffff00ffffff00ffffff00ffffff00ff000000000000000000ffffffffffffff000000000000000000ffffffffffffff00ffffffffffffffffffffffffffffffff0000000000000000ffffffffffffff00ffff0000ffff0000ffff0000ffff0000ffffffffffffffffffffffffffffff00ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff000000ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff000000ff00000000ffffffffffffffffffffff00ffffff00ffffffffffff0000ffffff00ffff000000000000000000000000000000000000ffffffffffffff00ffffffffffffff00ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffff000000000000000000000000000000000000000000ffffffff00000000ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff000000000000ff00000000000000ff00000000000000ff0000ffff0000ffff000000ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff00ff00ff00ff00ff0000
|0,12=>0xffff0000ffff0000ffff00000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ffffff00ffffff00ffffff00ff00ffffffffffffffffffffffffffffffffffff0000ffffffffffff0000ffffff00000000ff000000ff000000ff00000000000000ff000000ff000000ff00000000ffffffffffffffffffffffffffffffff000000ff000000ff000000ff00000000ffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000ff0000000000000000000000000000000000ffff0000ffff0000ffff0000ffff00000000ffff0000ffff0000ffff0000ffff000000ff000000ff000000ff00000000ffff0000ff000000ffff0000ff000000ffff0000ff000000ffffffffff00ff00ffffffffffffffffff00ffffff00ffffffffffffffffffffff00ffffff00ff0000000000000000000000ffff0000ff0000000000000000000000ffff0000ff00000000000000ffff000000000000ff00000000000000ffff000000000000ff00ccccccccccccffffccccccccccccffccccccccccccccffffccccccccccccffccffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffff0000ff000000000000000000000000000000000000000000000000000000ffffffffffffff00ff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ff00ff00
|0,13=>0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff0000000000ff000000ff000000ff000000ff000000ff000000ff000000ff00000000000000000000000000ff000000ff000000000000ffff000000ff0000ffff0000ffff00ffffff00ffffff00ffffff00ffffff00ffffff0000ffff00ffffff00003333003333330033333300333333003333330033333300003333003333330000000000000000000000000000000000000000ffff0000ff000000ffff0000ff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fffff0f0fff0f0f0fffff0f0fff0000000000000000000000000ffffffff000000000000000000000000ffffff0000ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff000000ff000000000000ff000000ffff0000ff000000ffff0000ff000000ffff0000ff000000ff0000000000000000000000000000000000ffffffffffffffffffffffffffff0000ff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffffffffffffffffffff00ffffffffffff00ffffffffffffff00ffffffffffffff00ffffffffffffff0000ffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff000000000000ff000000ff000000ff000000ff000000ffff0000ffff0000ffff0000ff00ffffffffffff0000ffffffffffff0000ffffffffffffffffffffffffffffff00
|0,14=>0xffffffff00000000ffffffff00000000ffffffff00000000ffff0000ffff00ffffff00ffffff00ffffff0000ffff00ffffff00ffffff00ffffff0000ffff0000ffffffffffff0000ffffff00ffff0000ffffffffffff0000ffffff00ffff0000ffff0000ffff0000ffff0000ffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000ffff0000ffffffffffffffffffffff00ffffff00ffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff00000000ffffffffffffffffffffffff00000000ffffff00ffffff00ffffff000000000000000000ffffffff00000000ffffffff000000000000ffff000000000000ff00ffff0000ffff0000ffff0000ffff0000ffff0000ffffffffffff0000ffffff00ff00ff00ff00ff00ff00ff0000000000ff00ff00ff00ff00ffffffff00000000ffffff00ffffffffffffff00ffffffffffffff00ffffffffffffff00ffffff000000ffff0000ffff000000ff000000ff0000ffff0000ffff000000ff00000000
|_,_=>0
def sP:Nat→Nat
|0=>0x905040306020f00131d0406100f1c0a090407230b02101d0d040306100f192221050402100f200d040b020f1f0a0c0d040306100f1c121b05040b021a0f0a05040b0201000a09041607061013040e100f1912050403181001170904070602101304160710121315040702101205110403021001090408070602050403020100
|1=>0x21012210402100f20280c0504030210011332040302310f0c0d040306020f261222210d2c02100f20131d04032f100f0c131d0403100f190c170904060e02100f27040602100f2e0a13090403020f260c09040b022d010c132c02100f2b2a0a29040b02100f280c27050406020f000a131d0403020f260c2509040602100f24
|2=>0x9040b020f35121d0d040306020f002705040b021001272c02100f2b2a0a131d0406020f260a05040b020f002012340d04032f100f12090504230b020f001305040302310f121309040602100129220d040b02100f340d0403100f19120d0416070b10120d040b0210330a0c2221040602100f24090408070b020c0d1504070b
|3=>0x240c0d04160706100a340d0403020f00120d0406100f192412270402100f2b2412270402100f202a1234090403020f350c210402100f39240c250402100f20240c27252c0b02100f2a0904070602101b05040302100f143813040e02100f12131d04062f100f0a130402100f2b2412130402100f202a12270d040602310f1234
|4=>0x2100f3e240c0d04061810010a0d040b0e100f1912210402100f203d0c3c0d0402100f390a13050423100f3a0a170904070b02100c22212c0b02100f2413041607100a0c270d04062f100f12340402100f2024123409040302310f0c0d04031810010c130407030210122705040b02310f1213050403100f1912210402100f2b
|5=>0x3c040b02100f280a340d0403021001420402100f39280c25092c0b02100f2a0905040b020f35122705040b100f1912220402100f39280a0905040b020f00412725040602100f241309042302310f0c270402100f2b2a120d0408070b02123409040b2f100f12090504030602310f130904402f100f0c273f05040b02100f2104
|6=>0x40b02100f440c340d040b020f35120a270d040b100f1c0a0c212c02100f20240c2242040b02100f282725040602100f2a2704070602100a290d0402100f390c13090423100f190c3813040702100a0c220d0402100f430a211d040602100f243409040b020f0012130504232f100f0a13090403020f350c0402100f43280a0c
|7=>0xf280c2221090d2c0b02100f130948040b02100f0c1347090402100f200c1321042302100f240c131d11040302100f0c340d040302100f14420d04400b02100f122705040b2f100f0a0c2722420d040b02100f27050402100f2b0a460d040b02100f0a0c090504230302100f204522420d040b02100f13042302100f2a0a420d
|8=>0x342509040b02100f090d040b020f4c0a0c360905040b02100f1209042302100f20240c22040b02100f280a131d040602100f300a1d0904030602100f2413040602100f2a0a0d040602100f43120a0d040b020f1f0a0c270d040b02100f4a12090504230b02100f2a34250d040302100f12490d0402100f390a0c2109040b0210
|9=>0x2a0d04070602100a27050402100f2012270d040b0210330a0c1d0d04060b100f1c0a1332040302100f370c450d040b0210330a0c2721040b02100f3d0c0d040b100f500a0c2705042302100f200a42040b02100f280c2205040302100f200a2704070b02100a0c09044f030b100f0c22210d04030602100f0d04034e02100f0c
|10=>0x9040602100f1305040302100f37120905040b100f19120915040b02100f5512340d040b020f540a0c220402100f20240a0c271d040602100f240a530911040302100f0c250d04030602100f12340d11040302100f1227222c0b02100f2a0a2725040b02100f2a0c0d04030210010c130515042302100f0a1d0d04030602100f
|11=>0x100f121d0d040b100f5a0a0c1332040302100f12340402100f39280a0c13040602100f24120d040b100f593d0a0c210402100f20240c270d040602100f581205040b02100f560a0c381332040302100f0c22470d04030b02100f1d0d04030b020f260c090d04030602100f5713040b02100f560a0c130d040302310f120c1325
|12=>0x402100f200c270d040602100f570a2213040b02100f241238135e040602100f0a17090504230b02100f27210504030602100f340d0403020f350a0c42093205040b02100f381305040302100f120d0402100f395d0a0c272505040b02100f22250905040b02100f0905040b02100f2a120d040b02100f5b120a130932042302
|13=>0xc2721040602100f240c5f1305040b02100f12361309040302100f0c34090504230302100f27210d2c02100f200c3c0d04030602100f0a490905040b02100f1236040b02100f280a0c27040602100f2a0a090d04030b020f260c270d040602100f37123409040b020f000a0c2732040b02100f24120d04030b100f1c120c2105
|14=>0x2100f12450d040b020f260a0c1d0d040302100f2b090504030b020f000c0d04030b100f630a0c29270d040b02100f0c29450d040b02100f0c1d0d04620602100f0a171d0d04030602100f420d11040b02100f0c0904030b02100f560c36340d040302100f121d0d04030b100f190c610d040b020f600a0c090d040b100f5a0a
|15=>0x450d040b02100f0a0c0d040b100f19280a0c0d040b0210330a0c220d2c0302100f200a250d040302100f200c1304030e02100f12273405042302100f0a3c270d040b02100f1227470d040b02100f1234131d040302100f123c1d0d040b02100f0a09040b02100f650c131d040302100f2a0c2509040b02100f240c38270d0406
|16=>0x2100f390c2132040b02100f240c13040602100f670a0d040b020f4c120a0c130904032f100f0c1d0d040b020f350a0c1309040302100f570c1305040b0210010a22340d0402100f390a2725090d040602100f320d04030b02310f0c1b1305040302100f12130915042302100f0c1305040602100f660a132c02100f20240a0c
|17=>0x5040b02100f69121309040b02100f4a12340d040302100f2a122213050402100f200a0d040b02310f680a0c050d04030b02310f1222130d040302100f120d040b020f4c390a0c27220d0402100f2b122709040b02100f2a12340d040b100f5a0a0c1d32040b02100f280a27040602100f24122705040b020f000a0c210d0403
|18=>0x100f2e0a0c270d040302100f2b12250d040b100f190a0c1309044002100f580c49040b02100f280a0c0d040306100f191205040b021a0f0a45210d0402100f200c13212c0302100f240c0d040b02100f6a0a450d040b100f190a0c36220d040b02100f0a2722040b02100f24120d04230b100f5a0a0c0905040b02100f5d1227
|19=>0x2100f21040602100f240c131d04234002100f0a210d2c02100f200c22250d04030602100f530905040302100f17131d040302100f0c0d04060b100f1c120a13050402100f6b0a1709040b0e02100f0c3409040b02100f5812092c0302100f20240c2225090d2c0b02100f130904234002100f450d040b2f100f0a0c27040b02
|20=>0x100f280a0c132505040302100f12090504060b020f000a1309040602100f58120d04030b020f26120c530402100f20240a0c420d040302100f200c340d040302310f0a0c451305040302100f121d0d04060b100f190a270d040602100f3012340d0402100f430a0c220d040b02100f570a3c340d040b02100f0a27210504230b
|21=>0x22210d040602100f0515040b02100f20121309040b0210010c175309040302100f0c421d040b02100f280c210d040302100f2b0c09051504230b02100f340d040b02100f6c120d040b100f5a120a0c1d040302100f20240c221d040b02100f280a1305040302100f3d0a490d04030602100f122221040b02100f240c17040b02
|22=>0xf280a130d040602100f6c120d040b020f6d3e0a0c340d040302100f5d12270d040602100f141309040302100f4a0c341d0d04230302100f09040b02100f2a121309040302100f5d0c0d04034002100f39120d11040302100f140c383409040b02100f12131d040b020f260a0c2705040b02100f58122722050402100f200a27
|23=>0x2100f580c130d04032f100f120c290905040b02100f0c270d044002100f20121305040602100f690a2705040b02100f3712211d090d040602100f4209040b02100f280c1d0d04030b020f000c6f0d04030602100f120d040b6e100f120a0c130d0403100f19120c27250d040602100f121d0d1504030602100f2209040b0210
|24=>0x12270d11040602100f120d040b100f63280a0c5f050d040b02100f12130402100f6b670a0c3c0d040b02100f120a134709040b02100f122722470d040b02100f131d32040302100f12040b02100f2e0a0c09040b02100f70121309040b020f260a0c29340d040b02100f120d040302100f2b12381309040602100f1234090403
|25=>0x2100f300c0d04060b020f26120a3c270d040602100f0a220d040b02100f4a0a27130d0402100f2b12220d040b02100f5d0a34530d0402100f390a0d040b100f73720a0c0904070b02100c22210d2c030b02100f1321040302100f280c2234040b02100f280a131d040b2f100f0a0c3409040302100f370c382705040b02100f
|26=>0x27250d0402100f200c131d15040302100f0c340d040b2f100f120a050d04030602310f0a1d0d040b0210330a0c13040302100f760a0c1d0d04030602100f66130d04402f100f0a0c340d040b100f19120a3409040b02100f3012383409040302100f0c09040302100f20280c0d7404030b02100f0c05040b0210010a13090440
|27=>0xf390c1305040b02100f3d0a130d0406100f19120a29340d040302100f0c7709040b02100f700c1309040602100f3012050d04030b100f19121b2705040b02100f121305042302100f370a270402100f20280a0c4b0d0402100f390a0c2705040602100f690a27040b0e02100f1227220d2c02100f200a13093b042302100f0c
|28=>0x302100f3e0c42320d040b02100f120d040b020f78720a0c340d15040302100f12340d040b100f1c0a0c2509040b02100f2a0c0d040b100f1924120c0d040b020f1f120a0c3409040b02100f14090d040b0210330a0c1b2105040602100f0a050d040b020f000a412109040b02100f3d0c130d042302310f0a0c27210d040210
|29=>0x100f0a220d2c0302100f2b0a250d040302100f2b0c1b05040b02100f0a141309040602100f140d04030b100f5a0a0c420d040302100f390c0d04230b100f1c0a0c220d040302100f390a0d040b020f790a0c050d040b020f35120a27212c0b02100f240c05040302100f142709040602100f2412341d320d040302100f210d04
|30=>0x40b02100f7b0a291d0d040b02100f0c0d044f030b100f121325040302100f240c340d040b0210330a0c0d3b0402100f390a0c131d040302100f660c0d0416070b100a0c3409040302100f300c0d0402100f39690a0c13050402100f430a0c132509040602100f122722250d040602100f1e1305040602100f0a3c1305040b02
|31=>0xf0a2109040602100f240c050d040b020f540a0c220d15040b02100f0a27250d04030602100f0d040b100f7c0a0c272505040b02100f1249270d040602100f121305040b02100f6c12090d04030602310f0c2213050402100f2b0a0d040b100f630a0c05040b020f00200a0c2722040b02100f2a1234130d0402100f2012220d
|32=>0xf430a0c4521040b02100f240c22420d040b02100f12050d040b020f4c0a0c1305040302100f7e0a090d04620602100f123409040b020f350a0c29090d040b02100f0c1309040302100f660c420d15040b02100f0c09040302100f39240c27210d0402100f2b0c09053b04230b02100f040b02100f66280a0c131d1504060210
|33=>0x40602100f241217270d040602100f1222250d2c030b02100f34530905040302100f381309042302100f0c13040602100f800a3453040b02100f280a0d0402100f397f0a0c130d0403020f350a0c1305042302100f300a3c090d040b02100f120d040b100f1c390a0c270d040602310f0a0c47090d040b02100f120d04030210
|34=>0x20f00121b090504030602100f0d04030b020f840a0c830504030602100f0a2209040b02100f24120905040b02100f69120d040b020f6d0a0c1325090402100f200c09040b8102100f120d040b021033120a0c470d040302100f200c270d040b2f100f120c340d040b020f00120a212c0b02100f240c170905040b02100f4109
|35=>0x40b100f5a0a0c270402100f39280a0c1309042302100f440c450402100f39280a0c09040302100f2b240c2721040b02100f280c2722210d2c0b02100f2753040602100f240a0d040b020f600a0c0d0402100f39370a0c130402100f2024120c4b040b02100f280a0c290d04230b02100f0c220d040b02100f660a050d04030b
|36=>0xa2221090d040602100f2705040302100f20123413040302100f2412210d042302100f200c83870d04030602100f130d0423100f190a0c7109040b02100f7012130511042302100f0a090d04230b02310f0c380d0402100f390a0c1d0d04030602100f5813040302100f2a128305040b02100f3d0a1b2705040602100f0a130d
|37=>0x40302100f430c1e1d0d04030602100f090504030b02310f0c27220d0402100f390a45220d0402100f390a27210d0402100f3e0c270402100f2024120c2713040b02100f2a124b220d040b02100f0a09040602100f140d040b1810010a0c220d040b02310f0a0c0d040b02100f880a0c040b02100f69280a0c0d040703060210
|38=>0x220d040302100f3e0a1b090504230b02100f090504620b02100f12131d040302100f580c3409040b02100f5d12830504230b02100f0a27220d2c02100f2b0a27250d0402100f2b0c270d040b100f5a0a0c132509042302100f0c090d040b100f3a120c450d040b100f5a0a0c492705040b02100f122247090d040b02100f1d0d
|39=>0x40b02100f121304070302100a0c4b0d040b02100f0a0c0d040b100f730a0c131d040302100f370c040b02100f58280a0c090d040302100f430c1d0d040b100f7c0a0c13090402100f2b120d040b100f19390a0c22420d04030b02100f2725040b02100f240c0402100f39280a0c040b02100f7f280a0c171309040602100f12
|40=>0xc270d040b020f350a0c173409040302100f0c450d040b020f350a0c09040302100f3e240c130504062f100f0a273405040302100f12270d0402100f430a0c450d0402100f430a0c05040302100f20120d04030b0210330a0c3c450d040b02100f0a830d040302100f8a1229050d040b02100f121321040302100f3d0c172705
|41=>0x40302100f0c131d04034002100f120d040b020f780a0c21092c0b02100f240c1e1309040302100f0c0904230b02100f560c1e040b02100f280a0c1d0d040602100f430a3413040b02100f2412220d0402100f390a220d040b02100f7f0a27470d0402100f200c130d048b02100f0a0c0d0407230b02100a1e131d040302100f
|42=>0x27220d0402100f3e0a27210402100f20240c090d04030b100f3a0c1e220d040b02100f0a2742040b02100f280c4542040b02100f280c0d040b02100f7f0a0c420d040b020f350a0c1d0d1104030602100f131d32040302100f211d040b02100f240c8d05040b02100f0a0c27130d044002100f12420d040b02100f370c29130d
|43=>0xa0c2713040b02100f2a0a0c0d040b02100f8f0a0c0d04230b02100f2a0a5309040b02100f580a0c1e0d04030b02100f120c1b050d040b02100f0a41130d04234002100f0a1b1d0d04060b02100f0a2705040302100f200a0c460d040b02100f0a0c17090d04230b02100f0c27210d04030602100f0c3413040302100f240a0c
|44=>0x302100f24120c920d040b02100f0a0c340d040b02100f660a0c0d8504030b02100f0a0c5f130d040b02100f120c53050d040302100f0a130d040b91100f0a0c1d0d1104030b02100f0c830d040b02100f120a2705040b02100f2a0a0c49090d040b02100f120c0d04060b02100f570a4b1d0d040b02100f0a0c0d04900b020f
|45=>0x100f390a0c990d040b02100f0a0c090d04980b02100f0a0c1e131d040b02100f0a0c0d040b100f950a0c0d15040b02100f390a0c050d040b020f00120a135309040602100f0a17220d040b02100f0a0c930d040b02100f0a0c13092c0302100f0c0d040602100f39120a27211d0d040b02100f0c130915040b02100f120c1304
|46=>0x40b020f260a0c34050d040b020f350a0c4b090d040b02100f0a0c320d04030b02100f370c34130d040b020f350a0c45250d040b02100f0a0c0d040b02100f9b0a0c270d04030602100f120d11040b02100f280a0c492705040b02100f0a0c090d040302100f3e0c130911040302100f0c27470d04030b02100f0c34130d0402
|47=>0xa17090504030b02100f0c130d040b0210010a0c38130d044002100f0a0c4521090d040b02100f0c050d1504230b02100f0a275305040b02100f0a9f0d04030b02100f0a0c0d040b02100f9d0a0c3409040b02100f5d0a0c0d04030602100f690a0c0d040b02100f9c0a0c1b420d040b02100f0a0c132505040b02100f0a050d
|48=>0x2310f120c45220d040b02100f0a2713040b02100f24120c1b05040b02100f200a0c050d04030b02100f371234210d040302100f0c171309040602100f0a0c0d040b02100fa10a0c27220d04030b02100f1209040b0e02100f0c0d040b02100fa04a0a0c8305040b02100f0a0c090504620b02100f0a0c4553050d040b02100f
|49=>0x3a0a0c0da4040b02100f0a0c130da30b02100f0a0c0d040b02100f2a120a130d040302100f5d0a0c270d0402100f3e0a0c1d0d4d040b02100f0a0c13090402100f2b0a0c1305040b020f000a0c0d040b02100f68370a0c1e1309040b02100f0a0c131d040302100f0c38340d040b02100f120a0d040b02100fa20a0c0d04030b
|50=>0x2c0b02100f0c130d040302100f30120c270d040b02100f69120c0d1104030602100f123413090402100f200a0c1d0d3b040b02100f0a0c450d11040b02100f0a0c1d0d040b02100f690a0c22130d0402100f200a0c27420d040b02100f0c1d0d04a50b02100f0a0c130d040302100f4a0a0c45420d040b02100f0c0d040b100f
|51=>0xf0a0c29050d040b02100f0a0c130d040b100f190a0c4b340d040b02100f0a0c0d040302100f8a0a0c29130d040b02100f0a0c220d2c0b02100f0a0d040b021a0f0a0ca70d040b02100f0a0c172705040b02100f0a0c09320d04230b02100f1234420da6040b02100f0c1b131d040b02100f0a0c320d04030b02100f1221090d
|52=>0x273405040302100f0a0c090d4d040b02100f0a0c270d04400602100f0a13470d040b02100f120a05040302100f200a0c27092c0b02100f240a0c0d04030b02100faa0c0d040b02100fa90a0c210d04030602100f0c0d040b100f1c0a0c38130d040602100f120a8d0d040b02100f0a0c830d040302100f8a0a0c0d89040b0210
|53=>0x40b02100f2a0a0c0d040b02100faf0a0c0d040b02100f43120a0c270d2c0302100f200a0c131d32040b02100f0a130d04ae02100f0a0c1e0d04060b02100f120a5309040302100f0c090d04a50b02100f0a0c340d040302100f125f250d040b02100f120c270905040602100f0a0d04ac0b02100f0a0c13090402100f20120c
|54=>0x1d05040b02100f280a0c27220905040b02100f0a340d040302100f370a0c1b0d040b02100f2a0a0c27210d04230b02100f0c220d2c04030b02100f0a22210d04030b02100f0c45340d0402100f390a0c0db20402100f390a0c0db10b02100f0a0c27130402100f20240a0c131d040b02100f300a0c1d0904030b02100f240c13
|55=>0x2100f0a0c470d04030b02100f0c13250d040302100f120c0d82040b02100f3e0a0c1d0d040b02100f7f0a0c1d0d04030b02100f2a0c13470d040302100f0c0d04070b02100a0c1305042302100f120a45130d040302100f120c1d050d040b100f1c0a0c130d040302100f140c466f0d040b02100f0a0c0d040b02100fb30a0c
|56=>0x50d04060b02100f660a170905040b02100f12132509040b02100f0c36270d040b02100f0a0c250d040b02100f0a0c0d04030b0e02100f12b40d040b02100f0a0c36450d040b02100f0a0c711d0d040b02100f0a130d044002100f300a0c250d04030b02100f120c3413040b02100f240a0c2713050402100f200a0c450d040b
|57=>0xf12270d040b02100f58120c17090504060b02100f0a0db60b02100f0a0c27220d0402100f200a0c340d040b02100f690a0c130904034002100f0c090d04030b02100f570c220d0423030b02100f0a340d040b02100f30120a38340d040302100f0a0c1b050d04030b02100f12090d1504230b02100f0c27340d040b02100f12
|58=>0x130d040602100f1227210d0402100f200c0d040b02100fb70a0c130d3b042302100f0a0c130d11040302100f120c4b0d040b02100f120a0c090d040b02100f7f0a0c0d64040b02100f280a0c131d040602100f0a0d040b02100f4a120a0905040b02100f2b0a13040b02100f24120c420d0423030b02100f0c220d04030b0210
|59=>0xd040b02100f37120c47250d040b02100f120a270d040b2f100f0a0c270d040b02100f570a0c0d04030b02100f7b0a0c130d040602100f30120ab9090d040b02100f0a0c1709040b02100f550a0c450d040302100f200a0c6f05040b02100f0a0cb8040b02100f28120a0c13531d05040b02100f0a38135e040b02100f0a0c27
|60=>0xf120a3405040b02100f280a0c0905b2040b02100f120905040b02100f2012451d040b02100f280a0c340d040b02100f0a142722130d040b02100f12221d050d040b02100f0a451d320d040b02100f0a3c0d04030b02100f0a0c090d0423400b02100f27040b02100f2a0a0cba0d040b02100f0a0c2209040b02100f2a0a0c27
|61=>0x2100f120d04bc620b02100f0a0c38270d040b02100f120c220d040302100f2b0a0c340d0402100f390a0c340d040b02100f7f0a0c1d0d0423400b02100f0a27050423030b02100f0a130402100f20240a0c1b340d040302100f0a0c0d2c0302100f200a0c1d0d04620b02100f0a0c171d0d04030b02100f0c34250d040b0210
|62=>0xd040b02100fbd0a0c0d04a50b02100f120a0c45130d040602100f120a1305040b02100f660a0c130d040602100f0a14134209040b02100f0c0d4d040b02100f120a0c1d090d04030602100f45050d04030b02100f12340d040b020f350a0c1309042302100f120c220905040b02100f0a49450d040b02100f0a0c270504030b
|63=>0xa0c340d040302100f300a0c13250d040602100f120a2709040b02100f280a0c0d4d040b02100f390a0c13050402100f200a0c34420d040b02100f124509040b02100f280a0c2722090d2c0b02100f0a2725090d040b02100f0c36420d040b02100f0a0c420905040b02100f0c090d04060b02100f5812171309040302100f0c
|64=>0x2721320d040b02100f0c1d050d040b020f260a0c0d040602100f2412090d04060b02100f570a271d0d040602100f0a090d04400b02100f120d04030602310f0a0c320d1104030b02100f0c27220d04030602100f0a0d040b02100f560a0c1321040302100f240c130d04c002100f0a0c27040b02100f24120c13040b02100f67
|65=>0xa0d11040b02100f680a0c1d0d040b02100f440a0c0d040b02100fa0120a0c5f34050d040b02100f0a270d040602100f690a0c050d3b04230b02100f0a17450d040b02100f0a0c1332040b02100f120a050d1104030b02100f121305a6040602100f0a0d040b02100f5c120a0c09040302100f20240c7d340d040b02100f0a0c
|66=>0x7f120a0c1d320d04030b02100f12270d040b02100f5d0a0c450d040b02100f5d0a0c27210d2c030b02100f0c0d04c20b02100f0a0c77090d040b02100f0c4534040b02100f280a0c470d040b02100f120ac10d040b02100f120a0c2234050d040b02100f0a210d0402100f200c27221d0d040b02100f0a45221d0d040b02100f
|67=>0x120c360905040b02100f0a0c1d040b02100f280a0c341309040b02100f120d040b02100f5b0a0c27320d040b02100f121e340d040b02100f0a0c1332040302100f0c361309040b02100f0a0c710d040b02100f120a090515040b02100f12270d040b02100f4a0a0c0d040b02c30f0a0c22250d04030b02100f0c0d040b02100f
|68=>0xd040602100f0c1309040b02100f58120c171d0d04060b02100f0a130504230302100f0a131d09040302100f0c0d040302100f140c3453050d040302100f0a090d040b02100fa20a0c4522090d040b02100f0a0d64040b02100f0a0c1d0d040b100f1c0a0c340905040b02100f1238130d042302100f0a0c270d040b02100f30
|69=>0x2100f0a0c0904030b02100f3d0c920d04230b02100f0a0cc70d040b02100f0a0c1d0db20402100f390a0c135e040602100f0a34420d040302100f0c34131d040b02100f120a490d04030b02100f120c090d04030602100f580c27050402100f200a0c1305040302100f120d04c60b02100faa0a0c1d0d040b02100f2b0a2721
|70=>0xc090d040b100f1c0a0c1b050d04030602100f0a0d85040b02100f0a0c09040b02100f280a0c1309c90302100f0c27220d2c040b02100f0a2722210d040b02100f0c1b1305040b02100f120a22090d2c0b02100f0a25090d040b02100f0c050d3b040b02100f120a0d040b02100fc80a0c27530d0402100f200a0c86610d040b
|71=>0xf6c120c27470d040b02100f0c251d0d040b02100f0a0c45320d040b02100f120a4522340d040b02100f0a22130d040b02100f120a4b0d04030b02100f0a0c1d0d04030602100f12270d040b02100f140c220d04030602100f0a270d040602100f580a0c090d04030602100f370c093204030b02100f240c1309040b2f100f0a
|72=>0x40302100f0c1305040b02100f690a0c211d090d040b02100f0c090d3b04230b02100f0c130d042302100f440a0c0905040b02100f41b804030b02100f280a0c6f0d04030b02100f120c270d040602100f1245210d04030b02100f0c090db20402100f390a0c0905040b02100f2a0a0c2722340d040b02100f0a130d040b0210
|73=>0xc27220d040b02100f12a7710d040b02100f0a0c050d040b02100fca0a0c270d040602100f370a0c270d040302100f390a0c132105040602100f0a221d0d040b02100f0a0d04230b02310f0a0c130d040b02100fca0a0c450d040302100f390a0c381309040b02100f120c0d04060b100f19120a9f0d040b02100f0a0c13092c
|74=>0xd2c0302100f200c270d11040b02100f120c0d04ce0b02100f0a0c341309040302100f0c220d040b02100f690a0c1e0d040b02100f390a0c050d04030b02100f2a12210d2c030b02100f0c0d82040b02100f0a0c34040b02100f280a0c13210d2c0302100f0c0dcd040b02100f0a0c0d040b02100fcb0a0c0d04030b02100f72
|75=>0xf0a0c130d3b040302100f0a0c3c270d040b02100f0a0c0d040602100f0a1438270d040602100f0a0cd40d040b02100f0a0cd0830d040b02100f0a0c270d040b02100f7b0a0c0904030602100f240cd3d20d040b02100f0a0c0d040b02100fd10a0cd00d040b02100f0a0c1353040302100f240a0c45270d0402100f200a0c09
|76=>0x2c040b02100f0a175309040b02100f0a0c1d0d04030b02100f660c131d040302100f120c45220d040b02100f120a270d2c02100f200a0c13050402100f390a0c0d040b02100fd70a0c0d7504030b02100f0a0c0d040b02100fd60a0c090d040b02100f69120c0d1504030602100f121b1305040302100f0a0c450d15040b0210
|77=>0x5d0a0c1309040b02100f4a0a0c5f340d040b02100f0a0d040bd9100f0a0c1309040b02100f5d0a0c13250d042302100f0a0c090d04230b02100f580c342109040b02100f0c45420d040b02100f120c1d0d040302100f200c0d040b100f3a120a0c050d04030b02310f0a0c0d040b02100fd80a0c27220d0402100f2b0a0c220d
|78=>0xb0e02100f12270d040302100f2b0a0c0d04bc0b02100f0a0cb9220d040b02100f0a0c130d040b100f19120a0c1b050d04230b02100f0a1309040b02100f30120c0d040b020fdb0a0c130932040b02100f1222340d040b02100f0a340d040b02100f5d120a1305040302100f300a0c250d04230b02100f0a0c0905040b02100f
|79=>0x120db20402100f39120a0c0d030b02100fdd0a0c5f130d040602100f0a050d04030b02100f7e0a131d32040b02100f120a0d040302100f390a0c0d040b02100f2b120a0d04030b02100f7f0a0c1b2105040b02100f0a0c2721040b02100f240c090d04230b02100f370c090d04030b02100f660c220d040b02100f580a0c0d04
|80=>0x602100f300a270d040b02100f660a0c0d040b02100fe00a0c220d040b02100f370a0c450d040b02100f660a0c130d040b02100fdf0a0c0905040b020f000a0c71090d040b02100f12b90d04030b02100f0a0c2709040b02100f24120c0d040b02100fde0a0c1353090402100f200a0c1d0d040b100f190a0c3409040b02100f
|81=>0x12132509040b02100f120c340d040b02100f6c0a0c3c0d040b02100f0a0c2722250d040b02100f0c711d0d040b02100f120a830d04030b02100f12490d04030602100f0a0c0d04bc0b02100f570a0c1309040b02100f140c0db6040b02100f0a0c0d040b02100f7b0a0c0d04620602100f0a0c271d090d040602100f0a130504
|82=>0xb02100f0a0c420d040b02100f120c2705040b02100f1227220d2c030b02100f0a130511040302100f0a0c1d0d04060b02100f660a131d040602100f120a491d0d040b02100f0a0c220d040b02100f120a383409040b02100f0a0c4534530d040b02100f0a38220d040b02100f0a0c050d040b02100f44120a1309040602100f
|83=>0x40302100f2b0a0c090d0423400b02100f122721090d040602100f0c130d04034002100f120d04230b02100f560a0c05040b02100f28120a090d1104030602100f0c1d090d040b100f1c0a0c460d04030b02100f0a0c1d09040b02100f280a0c130d040602100f6c0a0c130932040302100f0c341d0d040302100f0c131d1504
|84=>0xb02100f58120904230b02100f280c341d320d040b02100f0a09040b02100f24120c220d040b02100fa20a0c0d04230b100f190a0c13040b02100f800a0c4527210d040b02100f0c7177090d040b02100f0c3409040302100f0c21040b02100f240c4b270d040b02100f0a0c27220d040602100f0a4b450d040b02100f0a0c0d
|85=>0x4030b02100fa20a0c5f0d040b02100fa90a0c45220d04030b02100f0a0de1040b02100f0a0c0d040b02100f430a0c25050d040b02100f120a27210d2c0b02100f0c0dcd040b02100f3d0a0c34130d042302100f120a2747090d040b02100f0c0d040b020f26120a0c45270d0402100f390a0c0d04230302100f200a0c090504
|86=>0xf0a13040302100f280a0c13250d040302100f0c0d04c6030b02100f0a0c450d040b02100f690a0c1d0d040302100f390c2753040b02100f240a0c27420d04030b02100f0c45420d04030b02100f0c0d04030b100f3a0a0c221d090d040b02100f0a270d040302100f3e0a0c49340d040b02100f0a0c130d040302310f0a0c0d
|87=>0xd04030b02100f0c4b0d040b02100f0a0c090d040302100f390c7d050d040b02100f0a0c420da6040b02100f0c7d130d040b02100f0a0c21090d040602100f0c0d04980b02100f0a0c0d040b2f100f120a0c0d04c6ad0b02100f0a0c1d0d04030b02100f580c090de2040b02100f0c1b2705040b02100f0a0c220d2c030b0210
|88=>0x370c47090d040b02100f0c270d0402100f390a0c270d040b02100f7f0a0c092c030b02100f240c450d0402100f390a0c0d040b02100f0a8c0c450d040b02100f7f0a0c710d040b02100fd10a0c450d04030b02100f0a0c090d040b02100fd80a0c22090d2c040b02100f0a2221090d040b02100f0c1309040302100f580c8387
|89=>0x602100f390a0d04a50b02100f0a0c49270d040602100f0a0c0d4d040b02100f0a0c050de3040b02100f0a0c420d04030b02100f0c0d040302100f3e0a0c1b090504060b02100f0a272109040b02100f240c450d040b02100f580a0c0d044f030b100f0a0cb9270d040b02100f0a0c090d04bc0b02100f0a0c1309040302100f
|90=>0x402100f2b0a0c1e270d040b02100f0a0c1e450d040b02100f0a0c17270d040602100f0a0c4527040b02100f280a0c3c090d040b02100f0a0c0d040b02100fe40a0c1d0d04060b02100f580a170d040b02100f390a0c090d040b02100f7b0a0c090d04620602100f0a0c450d040b02100f370a0c13250d040602100f0a1d0d04
|91=>0x430a0c49220d040b02100f0a0c0de5040b02100f0a0c270d040b02100fa20a0c4527220d040b02100f0a05040b02100f20121d0d040b02100f430a0c1e1d0d04060b02100f0a2109040b02100f240c2722090d040602100f0ab90d040b02100f0a0c0d040b02100f7f0a0c27340d0402100f200a0c270905040b02100f12270d
|92=>0xf0a0c1d090db2040b02100f0a0c1e0d040b02100f0a0c27090d040b02100f690a0c490d04030b02100f0a0c0d0423400b02100f0a0905040b02100f580a0c320db2040b02100f0a0c050d11040b02100f0a0c1309040b02100f580a0c1d050d04060b02100f0a0d04620b02100f0a0c27220d2c0b02100f0a090d040b02100f
|93=>0xf0a0c1e1d050d040b02100f0a0c130d040b02100f6c0a0c130d042302100f120a0c2722090d040b02100f0a0c45270d040b02100f0a0c090d2c030b02100f0c0d04030b02100f24120c090504060b02100f0a050db2040b02100f120a27090d040602100f0a0c0905040b02100f120d04030b02100f680a0cb80d04400b0210
|94=>0x100f120a270d2c0b02100f0a0c36130d040b02100f0a0c0d97040b02100f0a0c0d040b02100f440a0c17090d040b02100f120c270dc9030b02100f0a0c2721090d040b02100f0cb80d04060b02100f120a09040b02100f550a0c42050d040b02100f0a0c090d1104030b02100f0c13420d040b02100f0a0c4927130d040b0210
|95=>0x30b02100fab0a0c0d040b02100f280a0c1309040302100f0c0d040b02100f66120a0c270d2c04030b02100f0a0c131d05040b02100f0a0c270d11040b02100f0a0c090d040b02100f2b0a0c1d0d04030b02100f0c17090d04060b02100f0a0c0d040b02100fbf0a0c0d040b02310f0a0c36050d040b02100f0a0c0d04400b02
|96=>0x9040b02100f0a0c1b0905040b02100f0a0c050d040b02100f2a0a0c34130d040b02100f120a1d32050d040b02100f0a0d040b02100f39120a0c090db2040b02100f120c050d15040b02100f120a090d040b02100f20120c0d04ae0b02100f0a0c090d040b02100f690a0c71320d040b02100f0a0c130d040b2f100f0a0c0d04
|97=>0x40b02100f300a0c250d040b02100f0a0c0d04030b02100f3d0a0cb80d04030602100f0a0c0d04030602100f1222090d040b02100f0a0c450d040b02100f0a0c1d0db2040b02100f120a0c270d04030b02100f120c270d0423030b02100f0a0ce60d040b02100f0a0c450d0423030b02100f0a0c34050d040b02100f120a1353
|98=>0x50d040b02100f0a411d0d04060b02100f0a0d040b02100f3e200a0c0d3b04230b02100f0a0c0d1104030b02100f120c451d050d040b02100f0a0c0db2040b02100f0a960c0d04030602100f370a0c21090d040b02100f0c1d0d040b02100f580a0c130dc90302100f0a0c340da6040b02100f0a0c093205040b02100f0a1309
|99=>0xd04030602100f240a0c050d040b02100f5d0a0c130d040b02100f4a0a0c130d040b02100f5d0a0c34130d040302100f0a0cbb0d040b02100f0a0c210dc90b02100f0a0c270905040b02100f0a0c270d04400b02100f0a0c38130d040b02100f120a0c130d2c040302100f0a0c270d040302100f200a0c0d040b02100f9e0a0c
|100=>0xf0a0c830d040b02100f0a0c090d04620b02100f0a0c17090d04030b02100f0c05040b02100f200a0c47210d040b02100f0a0c210d2c040b02100f0a0c0d040b02100fb00a0c090d040b02100f3e0a0c090d04230b02100f120c130d040302100f120c49270d040b02100f0a0c0d040b02100f6c0a0c1e1d0d040b02100f0a0c
|101=>0xb100f190a0c27130d040b02100f120c17270d040b02100f0a0c1b1d0d040b02100f0a0c0d04060b02100f580a0ce80d040b02100f0a0c34210d040b02100f0a0c050d040b020f000a0c1e090d040b02100f0a0c0d040b02100fc50a0c4534050d040b02100f0a0c0d04c00b02100f0a0c0de7040b02100f0a0c360d040b0210
|102=>0x27090d2c0b02100f0a0c5309040b02100f0a0c340d040b02100f120a0da6040b02100f550a0c830d04400b02100f0a0c1d320d040b02100f0a38340d040b02100f0a0c130d044002100f0a0c0d040302100f200a0c0d040b02100f570a0c4527090d040b02100f0a0c0d04230b02100f370a0c130d040b02100f30120a0c0d04
|103=>0xc0d5e04060b02100f0a0d040b02100f680a0c130d040602100f120a13250d040b02100f120a0c050d04030b02100f1238130d040602100f0a0c490d040b02100f0a0c270d04030602100f0a0c45130d040b02100f120a0c130d040b02100f0a140c1d090d04030b02100f0c270d04030b02100f690a0c320d04030b02100f0c
|104=>0x210d04030b02100f0c1305a6040b02100f0a0c3634050d040b02100f0a0c3634130d040b02100f0a0c1b340d040b02100f0a0c0d2c0b02100f200a0c0d040b02100f24120c271d0d040b02100f0a0c090dc9030b02100f0c451d0d040b02100f0a0c27220d04030b02100f0a0c130d15040b02100f0a0c090dbe040b02100f0a
|105=>0xa0c090d0423030b02100f0c270d2c040b02100f0a0c0d040b02100fda0a0c0d04230b02100f280a0c0de9040b02100f0a0c0d040b02100f4a0a0c340d040302100f0a0c45090d040b02100f0a0c090d2c04030b02100f0c1e0d040b02100f120a0c270dc90b02100f0a0c0d0423400b02100f120a0d04230b02100f440a0c27
|106=>0x2100f0a0c0d040b02100f3d0a0c210d04030b02100f0c13210d040302100f0c0d040b02100f30120a0c320d040b02100f120a270d040b02100f120c220d04030b02100f0a0c1b050d04030b02100f0a0c27340d040b02100f0a0c45340d040b02100f0a0c1d090d04060b02100f0a135e040b02100f0a0c0d04030b02100f69
|107=>0x100f0a0c090d040b02100f570a0c130d040302100f370a0c0d1504030b02100f120c090d04060b02100f580a0c0d2c030b02100f240a0c450d040b02100f120a0c0d040b02100f0a140c270d0402100f200a0c1b050d04060b02100f0a090d040302100f200c210d040602100f0a0c4927090d040b02100f0a0c1e1d090d040b
|108=>0x100f300a0c451d090d040b02100f0a0c45270d04030b02100f0a0c27320d040b02100f0a0c171d0d040b02100f0a0c5f130d040b02100f0a0c0d040b02100feb0a0c49090d040b02100f0a0c0d0403400b02100f1209320d04030b02100f0c0dea040b02100f0a0c38130d040302100f0a0cb50d040b02100f0a0c710d040b02
|109=>0x2100f200a0cb80d04230b02100f120a0c131d040b02100f120a0c27090dc90b02100f0a0c0d040b02100f390a0c270d2c030b02100f0a0c090d04030602100f0c13530d040302100f0a0c1309040b02100f120c0d040b02100f660a0c0d040b02100fcc0a0c090d2c0b02100f200a0c271d090d040b02100f0a0c1305040b02
|110=>0xd2c0302100f0a0c0d040b02100f2b0a0c170d04060b02100f0a0c0d2c040b02100f200a0c450d04030b02100f0a0c27210d040b02100f0c0dc90b02100f200a0c27220d040b02100f0a0c13530d040602100f0a27090d2c040b02100f0a0c270d040602100f0a0c1d0db2040b02100f0a0c270d040b02100f690a0c1d0d040b
|111=>0x390a0cb80d0423030b02100f0a0c1d0d040b02100f660a0c0ddc040b02100f0a0c71090d040b02100f0a0c0904030b02100f240c220d040b02100f0a0c210d2c0b02100f0a0c270d040b02100f370a0cd20d040b02100f0a0c341d0d040b02100f0a0c0d040b02100f690a0c090d04230b02100f0c270d040b02100f580a0c13
|112=>0x40b02100f0a0c1b0d040b02100f0a0c09320d040b02100f0a0c0d04230b02100f120a0c0d040b02100f240a0c0d15040b02100f120a0c380d040b02100f0a0cd50d040b02100f0a0c090d040b02100f390a0c0d040b02100f3e0a0c0d040b02100fcf0a0c090d040b02100f660a0c13250d040b02100f0a0c1d0d040b02100f
|113=>0xf0a0c1d050d040b02100f0a0c050db2040b02100f0a0c0d04030b02100f120c0d0423030b02100f0a0c0d2c04030b02100f0a0c090d040b02100f580a0c0da604060b02100f0a0c0dc9030b02100f0a0c270d040b02100f0a0c090d04030b02100f0c0dbe040b02100f0a0c0d040b02100f300a0c0d040b02100f0a410c530d
|114=>0x340d040b02100f0a0c0d04030b02100f370a0cb80d04030b02100f0a0c1d0d040b02100f0a0c130d040b02100f120a0c0d040b02100f200a0c0d04030602100f0a0c0d040b02100fab0a0c090d2c0b02100f0a0c27090d040b02100f0a0c170d040b02100f0a0c0d04060b02100f120ab80d040b02100f120a0c0905040b0210
|115=>0xf0a0c13530d040b02100f0a0c090dc90b02100f0a0c0d2c030b02100f0a0c050d040b02100f120a1d090d040b02100f0a0c38130d040b02100f0a0c270d04030b02100f0a0c320d040b02100f0a0c090db2040b02100f0a0c090d040b02100f200a0c17090d040b02100f0a0c0d5e040b02100f0a0c0d04030b02100f240a0c
|116=>0xd040b02100f0a0c0da6040b02100f0a0c0d04060b02100f0a0c0d2c040b02100f0a0c090d040b02100f0a0c0dc90b02100f0a0c0db2040b02100f0a0c0d2c0b02100f0a0c050d040b02100f0a0c130d040b02100f0a0c0d040b02100f580a0c090d04060b02100f0a0c130d040302100f0a0c090d2c040b0210
|_=>0
def sO:Nat→Nat→Nat
|5,0=>6
|6,0=>0x3a700d1802d7009d802070069801370031c0066
|7,0=>0x8b2022480875c2167083a0206807fa01f7707be01e78077e01d78073e01c7806fe01b7806c581a9806860199806460189806060179805c6016a7058a015a8054a014a8050a013a804cdc12b8048e011c70452010c80415c0fd803d600ef6039e00df8035e00cf8031e00bf802de00af802a1c0a0802620090802220080801e20070801a5c0618016600518012600418
|7,1=>0x35f80d5e034f80d21c34080ce2033080ca2032080c62031080c22030080be202f170ba602e180b6602d180b2602c180ae602b180aa602a270a6a029280a2a0282809ea0273709ae02638096e02538092e0243808f1c2348
|8,0=>0x162e4582915ea0571915a605609155e454e91516453c914ce452a91486451891445c508913fe44f8713c204e79137a44d59133244c3912ee04b2912aa04a1912660491812224480811e2046f9119a445d91156044c9110e443b810ca442a8108644189103e440690ff643f490fae43e290f6643d090f2203bf90eda43ad90e96039c90e4e438a90e0a037990dc243679
|8,1=>0x1f0e47ba91ec647a891e7e479781e3a478591df2477391dae076291d66475091d1e473e91cd6472c91c8e471a91c46470891bfe46f691bb646e491b6e46d291b2646c091ade46af81a9a469d91a52468b91a0a467a819c646689197e4656919364644918ee4632918a6462181862460f9181a45fd917d245ec8178e45db8174a45ca8170645b8916be45a69167645949
|8,2=>0x27d609ec9279209db9274e09ca9270649b9826c249a79267a4995926360984925ee4972925a649609255e494f82521c93f924da492e82496491c9244e490a9240648f8923be48e69237648d49232e48c2922e648b09229e489e92256488d82212487b921ca486a821864859821424847920fe0836920b648249206e481292026480091fde47ee91f9a07dd91f5247cc8
|8,3=>0x30be0c278307a4c15930360c0492fee4bf292fa64be092f5e4bce92f164bbc92ece4baa92e864b9892e3e4b8692df64b7492dae4b6292d6a0b5192d224b4082cde4b2e92c964b1c92c4e4b0a92c064af892bbe4ae782b7a4ad592b324ac392aea4ab192aa24a9f92a5a4a8d92a124a7b929ca4a69929824a579293a4a45928f24a33928aa4a21928624a0f9281a49fd9
|8,4=>0x39a24e5f9395a4e4d939124e3b938ce0e2a938864e189383e4e06937f64df4937ae4de2937664dd09371e4dbe936d64dac9368e4d9a9364a0d89936024d77935ba4d65935724d539352a4d41934e24d2f9349a4d1d934524d0b93411ccfb933ca4ce9933824cd79333a4cc5932f24cb5732b24ca39326a4c91932224c7f931da4c6d931924c5b9314a4c49931024c379
|8,5=>0x428250979423a5085941f25073941aa506194162504f9411a503d940d2502b9408a501994042500793ffa4ff593fb24fe393f6a4fd283f264fc093ede4fae93e964f9d83e524f8b93e0a4f7993dc24f6883d7e4f5693d364f4493cf20f3393caa4f2193c624f0f93c1a4efd93bd24eeb93b8a4eda83b464ec893afe4eb693aba0ea593a724e9573a324e83939ea4e719
|8,6=>0x4b5652cc94b0e52ba94ac652aa74a8a129994a425287949fe1276949b652649496e5252949265240948de522e94896521c94852120b9480a51f9947c251e79477a51d59473251c3946ea51b2846a651a09465e518e94616517c945ce516a9458651589453e5147844fa5136844b651249446e51129442a1101943e610f09439e50de9435650cd8431250bb942ca50a99
|8,7=>0x54325503953ea54f1953a614e09535e54ce9531654bc952ce54ab8528a5499952425488851fe5476951b654649516e54538512a5441950e254308509e541e95056540c9500e53fa94fca13e994f8613d894f3e53c694ef653b584eb253a394e6a539284e26538094dde536e94d96535c94d4e534a94d06533894cbe532694c76531494c2e530294be652f094b9e52de9
|8,8=>0x55de556e95596555c9554e554a955065538954be55278547a55159
|9,0=>0x5f6297cea5f1657bba5eca57a8a5e7a979595e2e978295de6576fa5d96975ba5d469747a5cfa573595cae9721a5c62570f95c1696fba5bca56e8a5b7a96d685b3296c395aea56b0a5a9e569f85a5a568ca5a0a9679959c25666a59729652a59265640958da962d9588e9619a58425606a57fa15f4a57ae55e29576295cea571295bb956c695a7a567a5594a562a9580a
|9,1=>0x68d25a2b9688e1a19a68425a06a67f659f3a67aa59e0a675e59cda671619bd866d259aaa66829996a66329983965ea5970a659a995d9654e9949a64fe9935a64ae992296462990ea641658fd863d258eb9638a58d8a633e58c5a62f258b3962a6989fa625e188da6212587b961ca5868a617a9854a612e5841a60e2582ea609a181ca604e5809a5ffe97f5a5fb257e2a
|9,2=>0x724e9c89a72025c76a71b65c649716a9c51971225c3f970d69c2c9708a9c18a703a9c04a6fee5bf296fa29bdea6f529bcaa6f065bb986ec25ba6a6e729b9396e269b8096dda9b6ca6d8a9b58a6d3a9b44a6cea9b30a6c9e5b1f86c569b0ba6c069af896bbe5ae5a6b6e9ad296b265abfa6ade1aada6a961a9ba6a4a5a8996a025a76a69b29a63969669a509691a9a3d9
|9,3=>0x7bf25ef2a7ba29edea7b565ecba7b069eb7a7aba5ea4a7a6e5e91a7a1e9e7da79ce9e6a979865e57a793a5e44a78ea9e30a789a9e1d978525e0b978069df7a77b69de49776a9dd0a771a9dbca76ca9da8a767e5d95a762e9d81a75e25d6f9759a5d5ca754a9d48a74fa9d34a74b21d239746a5d119741e9cfe973d29ceaa738a1cd8a733a9cc5972ee9cb1a729e9c9da
|9,4=>0x857aa154a852e6142984e2a12f98496a11ba844e2109a83fea0f5a83aea0e1a835ea0cda830ea0b9a82c260a6a82766093a822a6080a81daa06ca8192205aa81466048980fe6035a80aea0229806660109801e5ffe97fd29feaa7f829fd6a7f365fc497eea9fb0a7e9a9f9ca7e4e5f89a7e025f7797db69f63a7d669f5097d1e5f3da7cd25f2aa7c865f1897c3e5f05a
|9,5=>0x8ee263af98e9a639ca8e4aa388a8dfe637698db2a36398d6a635288d22a33ea8cd2a32b98c8a6318a8c3e6305a8beea2f298ba2a2df98b56a2cd88b1262baa8ac2a2a6a8a76629588a2ea282989e6626fa8996a25c9894e624b88906a237a88b6a2249886e621298822a1fea87d2a1eb9878a61d99874261c6a86fa21b4a86ae61a298662a1908861aa17ca85caa168a
|9,6=>0x986aa6119981ea5fda97cea5e9a978625d7a973a65c4a96eaa5b19969ea59e99656658ba9606a578995baa565995726552a9522a53ea94d6652c9948e651a994466508993fe64f6993b2a4e2a9362a4cea931664bc992ce64a9a927ea495a92326483991ea6470a919aa45ca914aa44a89102a436a90ba2424a906aa410a901aa3fca8fce63e9a8f7ea3d5a8f2ea3c1a
|9,7=>0xa1ea6870aa19e685daa14ea849aa10268379a0b6a823aa06a6810aa01e67ff89fd6a7ec99f8e67d9a9f3ea7c699ef667b3a9ea6a7a099e5aa78ca9e0aa77a89dc2a76799d76a753a9d26a73fa9cde272e99c96671ba9c46a707a9bf6a6f3a9baa66e289b62a6cea9b12a6bb99ac6a6a899a7e6695a9a326682a99e6666fa9996a65c9994aa649999026637998b6a6249
|9,8=>0xab6a6ad19ab1eaabe9aad2aaaaaaa82aa979aa36aa83aa9ea6a719a99eaa5e9a952aa4b9a90a6a38aa8baaa268a87a2a14aa82e6a01aa7e269eeaa792a9db9a746a9c89a6faa9b4aa6aaa9a0aa65aa98d9a612697aaa5c669698a57ea955aa52ea9429a4e2a92f9a496a91baa446a907aa3fe28f5aa3aea8e29a362a8ceaa31668bbaa2c6a8a89a27e68969a2366883a
|9,9=>0xb4fa6d34ab4aaad20ab45aad0cab40e6cfa9b3c66ce7ab37a6cd4ab32e6cc29b2e2acaeab292ac9b9b246ac87ab1fa6c759b1b26c62ab1666c509b11e6c3dab0ceac29ab07eac15ab02eac029afe2abef9af9a6bdcaaf4e6bc9aaf026bb79aeba6ba4aae6aab919ae1eab7e9add66b6c9ad8aab58aad3e6b45aaceeab31aaca26b1eaac52ab0aaac066af7aabb6aae3a
|9,10=>0x2e079b7f6adf3ab7aa6de0ab75aadce8b712adbaab6c66da7ab67a6d959b62ead829b5e66d6fab596ad5bab546ad47a
|10,0=>0xc1e2b06eac192b05aac142b046ac0f2b032ac0a2b01f9c056b00bac00a6ff8abfbe6fe78bf76afd2bbf22afbeabed2afab9be82ef979be3e2f85abdf26f739bda6af609bd5e6f4dabd0eaf39abcbeaf269bc72af12abc22aefdbbbcaeee8abb7aaed3bbb26aec09badaaead9ba8eae99aba462e87ab9f6ae72bb9a66e5ebb952ae4b9b906ae37ab8b6ae23ab866ae109
|10,1=>0xcb9ab2dcacb4ab2c99cafeb2b69cab2b2a39ca62f28f9ca1a727d9c9d2726aac982b2579c936b243ac8ea7230ac89ab21d9c84eb20a9c802b1f6ac7b2b1e2ac762b1ceac71671bc9c6cab1a8ac676f193ac626b1809c5de716e9c592b15aac542b145bc4eeb131ac4a2711eac456710bac40a70f8ac3be70e5ac36eb0d38c326b0c09c2d6f0abac282f0979c232f082a
|10,2=>0xd55ab54d9d512753aad4bef525ad46eb511ad42274fead3d2b4eaad38674d7ad33a74c59d2f274b2ad2a2b49ead256748bad206b477ad1b6b462bd15ef44dad112743b9d0c6b4289d07ab413bd026b3ffacfda73ed9cf9273d9bcf4273c6acef673b3acea2f39eace52b389bce027376acdb673649cd6ab350acd1e733daccd2732b9cc8a7317bcc36b302bcbea32f0a
|10,3=>0xdf0e77ba9dec2b7a79de76b7949de2e7781adde2776f9dd96b75badd46b7489dcfe7735adcb27721bdc62770eadc12b6faadbbef6e5adb6eb6d29db22b6bf9dad6b6ac9da8e769a9da42b685bd9eeb670bd996f65bad946b647ad8fa7634ad8ae7621ad862760ead81675fc9d7cab5e8ad77ab5d3bd726b5bfad6da75ad9d68eb59a9d6467586bd5eef5729d5a675609
|10,4=>0xe0de782dae092781b9e046b807adff6b7f2bdfa2b7df9df56b7cc9
|11,0=>0x3a1a9e842ba079e7f6b9f3ae7aa79e19e76279ceae712b9baae6c679a7ae676b993ae62a7980ae5de796dae58eb95a9e542b9479e4fa79359e4b27922ae46679109e41ab8fd9e3ceb8e9ae38278d6ae332b8c2ae2e2b8af9e29a789d9e252788b9e20a78799e1c27866ae172b8539e126b8409
|12,0=>0x3a699e9827a579e93a7a468e8f67a358e8b27a239
|13,0=>0x3a728
|_,_=>0
def wAt:=mkWire dB 236 256 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 18
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 11 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 1000003 zs)
def oP:Nat→Nat
|0=>0x305034310b0a4540b120d448110a0c4780b1d0442c31120d428311410434311312028310b0d41c090f0e42c310a0d40c140d0c42c29020142c29140f434311312028310b0d4383d0b0c428350305034310b0a4081d0b0d4383d0a0c40c140d0c42c29120442c350e0f428310305034310b0a434310f1444c480a0c42c290b0d42c310710434290f0e40c140d0c42c29
|1=>0x12044383d0a0c40c140d0c42c290b0a4503d0d0c44c480a0c42c351e10c74110b0c448350a0c408c1050a434311304c34491502c10490a0c42c310a0d40c140d0c42c291e10c2c291d04424310d0a404410a0d43c511312028310b0d41031220dc9c33130a40c351b10c10150b0a478431d04424310a0d428351b10c10150b0a4780b1d04424310a0d434290f0e40c31
|2=>0xa0c42c350a0c40c140d0c42c350b0a408c1050a434311304c40dd030d40c130b0a4d8433404418350b0c428151b10c10150d0c434310f1444c291312028310b0d478431d04424310d0a44c3102304104e0b0d4482d0a0c46c430504434310a0d43c511312028310b0d42c31130c4540b0d0b4104902074383d0a0c40c140d0c42c290710434290f0e40c140d0c42c29
|3=>0xd0c42c2902074342d0f0e40c140d0c42c2902304104e0a1342c35130c42831270bc9c37130a42c350d06440dd0b0c40c130b0a404090f1444c480a0c42c350e0f428310b0d40c140d0c42c2910374340d040382c291502c342d070242c310f0e40c140d0c42c29050b46c430405434313610cd011060d42c310f0e42c310a0d40c140d0c42c2905044282d0d0c44c48
|4=>0x120b408c10413828313610c28350b0a410d1130c4282d0f1444c311312028310b0d4882b040c49c33090b4d8430a0c410d1050b434310a134540b0d0b41049103740c310304c2c2910074383d0a0c40c140d0c42c29023044c311304c2c350d0c43429103740c13010242c310f1444c480a0c42c3505030540b0b0a410490d0c4ec0b2304418290b0c434290f0e40c14
|5=>0xa1380c310b0a424310d0b42835030442c29130c42c291312028310b0d48c330d234482d02304284d1304c2c35090b4241b0b0c434310a0d40c310a0b43431090bc2835050382c35030c434310b0a4d8433404418350b0c4340d0f0e40c140d0c42c290b0c4540b0b12410490a0c43c390305034310b0d42c29090c49c370b0c49c2b090b43429050b46c43050443431
|6=>0xa0c410d1050b43431090bc0c310b0a51437450cc8c35060a42c31050a434310b0c44c130b0d42c31090c43429030dc2c290b0c49c170a13434310b0d4782f1d04448350a0c52c4345044d029060d42c31130a44c130b0d40c17030c42c29121384c310b0d5142f270c4242d0d0a49c2b270c4242d270ac1031270cc242d0d0a424530d0a44c480a0c484310b0d4242f
|7=>0xd0c4242f0a0d4780b1d04424310a0d4342d090cc34290304c2c29240c49c370a2144c2b0b0d5480b045144c4a0a0c42c35270bc3431030c40c350b0a4d02b450dcd029060d42c31270bc9c330b0a43c39030d40c140d0c42c290d0a408390305034310b0a49c2b270cc340d0b0c40c530b0a44c480a0c42c351312c2831130c42c350a0d5344304394742f090c42835
|8=>0x304c2c290d0c4540b0d0a448110a0c4142f0412434290a0c43431270dc242f270cc242d090c42c31270dc242d0a0d44c330d0b42835030442c290b0c49c4b0d03428310b0a43419040342c310a0c42c29220dc242d0a0d48837220ac242d0d0a4282d0f1444c480a0c42c35120b4342d0412428310d0c40c170b0a414290d0c42c310f0e40c140d0c42c290a0c4242d
|9=>0x5c0c410961312c28310b0d424330b12434290a0c42c351d0cc2c290b0d448350a0c51437450bc18350b0c42831270dc284d0b0d42c31130ac9c2f270dc4c290b0d4242d0904c34294b0dd14111d0b414290d0c424330a0b43429130442c351e10c7411090c434290b0a42c31580c424130d0a52c37450444c490a0c42c350d0a44c4b0a0c42c350b0c434310b0d42831
|10=>0xb0c40c130b0a4142d1b10c14110d0c4282d1e02c7411120d42831090bc9c2b0d0c4242d0a0d4242d0904c3429270cc9c370b0d42816041342c310d0c42c350b12424110d0a428310d0c43431270ac340d0b0a42c313610cd011060d42c31090cc28d2050b434310a0c42c290b0d43431130a44c4b0a0c42c35220ac3431270cc242d0a0d48c170b12434290a0c43431
|11=>0xb0a4ec37042340c310b0a4282d340442831060d42c31120d4540b0412428314b02d1411270c4242d270dc284d130ac2c350d0c494291312c2c350a0d42c29043444c310b0d42c150d0c40c310b0a4242f270ac242d0d0a5243327044340d0b0a49c11090b434290a0c43431450dc28d1060d42c310b0c40c350305c34310b0a478430b0a47411090c43429030d42831
|12=>0x490cc9c11090b43429250c44c4b130a42c35120d44c310a0c42c35090c5243327044242d0d0a4243b0a0d40c140d0c42c290305c2c29050a434312712c2831090b4283104134284d0b0d4241b0b0c424310b0a434291b10c2c296402ca0110d2380c314b0ad1411270c4242d0d0a4d82b0a344d011060d42c31090c424130d0a42c31090c424110d0a5142b030543431
|13=>0x580c42c290b0d424130a0d4503d0d0c44c480a0c42c35450cd142f060d42c31220ac242d0d0a440dd090cc34290304c342d0a0b410150d0c428310b12410490d0a428310b0d42c311d04c28150d0c42c35040c49c2f270dc4c290b0d52c3f45044d029060d42c31270bc9c330d03410310b0a49c4b0d03428310a0c42c350305034310b0a42c150d0c40c31030d42c29
|14=>0xb0a42831300c428350b0d428310305c2c150d0c42c29270cc284d0d0c43431450cc4c490a0c42c35220bc9c330d03428310b0a488370a0c49c33090b434291d0cd14371d0b424310a0d428310d0342c31030dc2c291b10c284d040542c35270ac9c31030d49c37270ac242d090cc34295f0dd4c29130cc2c350b0c5344304394742f120d4283502304104e0b0d42c29
|15=>0x40c4340e0d0a4882b040c49c33090b40c310b0d40c330b0a43429270ec0c35030503431220bc9c330d03428310b0a40c330b0a42c350a0d48c37030c40c350b0a42c311502c10490a0c42c291410434311312028310b0d410310d0384c2b0b0a48c3b030c40c140d0c42c29450cc28d1060d42c310a0c49c330b0a428350a0c410d2050b434310d0c49c130d0342831
|16=>0x90b560310904c3429130c52433270444c290b0d49c2b0d0c40c31030d42c29270dc284d0b0c44c2b0b0d44835230cc2c490a0c42c350a1389c2f0a13410310b0d42c31220ac9c33030d42c29340cc2c150a0d434310b0a4342d090c42c290904434290b0c4780b1d04448350a0c57c2f0d0c54c29130cc2c350904428350305034310b0a434190904c2c310a0c43429
|17=>0x450cc24310a0d4a8310305c2c290a0c49c110d0342c290b0c49c33270dc2885130ad14371d0b424310a0d42c351b10c14110a0d4342d0904c2c310a0c434290b0a478431d04448350a0c44c33270bc9c37130a42c35450ac9c31030d43419103742c310304c140d0b0a428310d0c4540b120d448110a0c4283104138284d0b0d42c311e0bc7411050b414290d0c49c33
|18=>0xb0d43449030cc283113120100d0a0c42c290b0d42831041344c310b0d478431d04424310a0d42413090b434290d0c49c330a0d49c330b0d42c310d0c4242f0d0a448110a0c434290f1444c480a0c42c350b0a424110d0a44c330b0d5142b450dc24310a0d49c1b0d0342c31120442c490d0a428310d0c44c311304c2c354b02d14111d0b44835090c4340e0d0a51437
|19=>0x90c42c31270ac242d0d0a5142b270c4242d1b10c1015050a434310a0c434dd0b0c40c130b0a40971042584c4b0b0d4540b0d0b44c4b130a42c350a0b448350b0c448110a0c428310a3042c310b0d42c293404c2831060d42c310b0c44c291312028310b0d434290b0a4c0311304c2c350b0540c310b0a414290d0c434292305c2c490a0c434310b0a43429043484c31
|20=>0x130cc2c354b0cd14111d0b448350a0c494311312c2c350d0b4282d1d0cc48350a0c49c3b030d40c140d0c42c29710dc2831320b424330d0a478430b0d47411090c428350a368d011060d42c310a0c49c1b0d0342c290b0c42c310a0c43429130442c35130c42c350b0a424130d0a42831360ac10d1050b434310b0c434312704c4c290b0d4340d040382c290a0c43431
|21=>0xb0d478431d0442c31120d42831490cc9c11090b43429270cc4c29300c44c130b0d4882f130a42c35450bc28d1340cc18350b0c434290f0e40c140d0c42c29270cc9c2b0d03410310b0a48c37030c44c2b450cd1437060d42c310230424310a0d44c130d0a4100e0b0a418350b0c44c11130a428310b0d4340d040342c310a0c42c29250a4d04b0b0557c2f5f0dd4c29
|22=>0x40c4242f270cc242d0d0a43429230442c35060a42c31120d4342d0412428310b0a408c1130c44c130b0d43431130ec2c350305034310b0a42c311d04c2c29090c43429030cc08c1041382c290b054540b0412434311304c2831130c42c350a0d42c29041344c310b0d42835090bc0c310b0a5d4293705834310304c503d0d0c44c480a0c42c35030cc2c290a0d44c13
|23=>0x1b10c10150a0c49c2b240c4242d030c440dd040382c29270ad142f270c4242d0d0a4a8312705c284d1502c2c350a368d011060d42c31710ddc42b320b424330d0a42c311304c34290a0c42c350d034282d0405434310a0c4100e0b0d40c310d0c42c29450dc9c2f270c4242d0a0d4742f45044742d090c434292704c242d0b0c434310a0d42831030d40c140d0c42c29
|24=>0xb0d4d8430a0c410d1050b434310d0389c2b0d0342c290a0b434311312028310b0d428310b0c49c37090b428350b05474330b0a414290d0c48031270ac0c351d0cc742d120d42c150b0a410490a0c43431220ac8837270cc242d0a0d4540b0d03810490b0a52c4345044742d120d44c480a0c44c310b0d428354b0fd1411270c4242d0b0c4284e0405434310b0d42c4a
|25=>0xb0a424310d0a41c090f0e40c140d0c42c290a0b42835130c44c130b0d4782f1d04414290d0c434291312c2c350b0c4882b270cc242d0d0a42c351d0442c31050a43431490cc9c11130a42c35040c4882f270cc0c35220ac882f270cc0c350b0a410150d0c44c480a0c42c350d0a44c480a0c42c350b0c52c0b450440c150d0c5142b0305434317a10c111d210c44c2b
|26=>0xa0d44c4b130a42c3527044242d0b0c428310d0a43431300a428310b0d43429103740c130d0c4882f270cc4c290b0d5900b042848c37060a42c31090bc6c430a0d414110a0c48837270cc242d0a0d42831270bc4c31130a42c35690c49c332704c242d0d0a41429360ac10d1050b434310a0c408390305034310b0a4340e1312c2831450bc348d060a42c310d0b47413
|27=>0x1d0bc14290d0c42c35370c42c290a0c42d610b0c424130d0a4d8433404418350b0c52c2b450449c31090b434290d0b42c291d04c24310d0a5142b1d0b448350a0c424310d0a40c370d0a48c110d0c418290b0c448350412428310b0d42c31270dc2c31270ac242d0d0a5f4434204428d2050b5143312134342d0a0c4882b270cc340d0b0a42c314d02c10e51d0bc2431
|28=>0xb0c49c370a0c4242d0d0a4242d090442c310d0a4882b270cc340d040c4d0330b05428350d0c42c29030c4282d0d0a44c110b0d42c31135ec342d050ac3431130cd14370a3444c310b0d4282d3610c10d1130c42c35060a434310b0c44c130b0d5243327044242d0d0a440dd0d0340c130b0a494312712c242d4b0bd14110305434310b0a514331d0b448354d10c10e5
|29=>0x230d418290b0c46c430a0b42c310405428350d0c42c298510c11a10305834312a0d40c170b0a42c31270cc2831090b49c13090b434290a0c434318210c10f9200c4242f0d0a44c4b0a0c434290955c2c160a0d434310a0c52c3f45044742d120d48431270bc0c3502304284d1304c2c35050b46c430405434310d0389c2b0d03410310b0a42c4a0904434290a0c43431
|30=>0x304c2c29450bc4c490a0c42c350904c24310d0a428310b0d40c170d0c42c292a0c40c170b0a4340d0405434310b0a42c314b02d1411131242831450dd142f090b428350b0d4108e0a0d418290b0c4241b0b0c42c29270ac8c37030c40c350b0a49c2b270cc340d040c42c298610c11855e0b4142b0d0c42831270bc9c37130a42c35450dc8c35060a42c314b0ad1411
|31=>0xd0a48837130a42c35450ccd029060d42c310b0c434291312028310b0d404090f1444c480a0c42c35270cc340d0b0a43c390305034310b0a42c31270ac9c330d0a43431270bc340d0a0c42c29030dc2c29130c428310b0d40c31270bc9c2b030d42c290b0c60c2b400d40c330b0a4540b041242c490a0c5c4370a0c4c82d090cc34290d0c40c31030442c29103740c31
|32=>0xd0a40c310405428350d0c42c290a0c434310b58424130a0d424310b0a42c350904c28350a0c410d20d0a418350b0c40c310305c2c29220bc340d0b0a4882f220ac242d0d0a44c4b0b12434290a0c42c350d0a4ec0b04234482d0a0c428310d0c49c11090b428351e0bc7411090c434291d04428150d0c42c290b0c43431270ac242d200c4242f0d0a4242f270dc242d
|33=>0x4b0fd1411030543431270c5243327044242d0d0a60c2f0a0c50035030cc2c290a36810d1050b43431240c44c2b0b0a4242d0904434290a0c434310f0e42c350305034310b0a51411052a40c170d0c42c298902dc8110a554142f0d0c448350b0d428310304c2c291e0bc7411090c434290b0d4241b0b0c428310d0a4742f450dc742d090c428350b0d424110b0c42831
|34=>0x90c434290a0c49c37130c44c290b0d5142f450ccd029060d42c31090bc8431270ac242d0d0a6302d3012828311304c2c350f0e40c310305034310b0a474110d12428310b0a42c35130c4282d0b0d424110a0d4340e200c434290d0c408c10b0c44c130b0d42c15030d434310b0a52c2f450449c31090b434291e0bc742d1d04424310d0a43431270bc340d0a0c42c29
|35=>0xb0a514331d0b424310d0a5142b450dc242d0a0d43449040342c310a0c42c290b0a424310b0d424330a0d42431270dc9c2b090b434298e0d410aa0305c34310b0a44c29360ac10d1130c42c35030cc2c290b0d448350a0c62443720442955050bc3431270ac9c37040c4242d0a0d42c290b0d47411090c428350d3b88c11060a42c31450dc742d090c428351e0bc7411
|36=>0x305034310b0a49c170a13434310b0d40c6e0405434310b0a4a033230dc18290b0c424130d0a44c330b0d42c291d04448350a0c4482f0405434310a0c48c330b0d418290b0c414290b0c414110d0c49c2f030d434310b0a5f835370c40c130b0a40c310b0a424110d0a49c2b0d0342c290b0c44c31030dc2c350b0a49c2f270dc2885130ac2c350d0a4ec0b042340c31
|37=>0x1d0bc2c31120d42831270ac2431090b434290412434290a0c42c350a0c40c370b0d42c290d4448c13060a42c311d04c142d050a43431046840c160d0c42c29250a44c4b0a0c42c350a0b4d033050b43431021444c480a0c42c35090c42835030442c290d4048c33120b428310305c0c350b0a4283127044242d0d0a560310b0c424130d0a514111d0b424310d0a44039
|38=>0x230dc0c31030442c290d0c49c11090b428350b0a48031090bc34290d0b42835030442c29210c49c2b030d42c29450bc28d1130c42c350b9a46c2b050443431620cc2d610904c34290b0d47411090c428359702e5811120dc28311d0bc34491204428311b10c10150d0c428310d0a44c330b0d42c31090449c33090b43429139442c351204c28310d0a410310b0a42c35
|39=>0xd0c44c33130a42c356f0cc34dd0304c2c299e0a46c2f050443431043483429060d42c312704c340d0b0a42c31044788431130ac2c350504428d2050b434310d0c44c4b0a0c42c351e10c7411050a434313610c10d1050b43431450449c31090b43429090cc34290304c2c293610c10d1130c42c35122544c4b0a0c42c351706c2c310904434290a0c4340d0b0a42c31
|40=>0x90bc2835050443431040382c290a0c43431130c44c2b0b0a42c350b0c42c35090442835042888c37060a42c31270cc340d0a0c42c290a0d40c140d0c42c294a0a4c0311304c2c350d2a40c170d0c42c290d0c42d610904c2835340cc28d1050b434310904428350d0c42c290f1444c480a0c42c35130440c330b0a42c35270ac9c31090b434290b12410490a0c43431
|41=>0x51100c110d0c42c29041444c480a0c42c352305c2c490a0c434310b0a410d2130c42c35090b48031090bc342904394742f090c434290b0d4241b0b0c428351b10c10150d0c42c350305834310304c2c290b0d47411090c428350d12428310b0a42c350a0c44c31130442c352204c9c33090b434291037428310304c2c29450ccd029060d42c31270dc4c290a0c42c35
|42=>0xb0c428150405434310b0d42c291d0cc48350a0c49c2b040c4242d0d0a42c290a0c44c130b0d49c130d03428310b0a4100d0b0c428310b0a4242f130c42c350a0d4483504234482d0a0c40c150d0c42c29090c49c13090b43429270bc9c33130a42c35340ac4c31130a42c350b6647413090c434290b0a4c0311304c2c35450acd029060d42c313b02c8c11060a42c31
|43=>0xd0342c290b0c4780b1d04424310a0d428310b0d42c31a80d50013030cc2c29830bd0035030cc2c29720442955050bc3431360ac10d1050b434311502c10490a0c42c3545044d029060d42c31830bd0035030cc2c29360ac10d1130c42c35040c49c33090b43429101444c480a0c42c3571044c82d090cc3429090443431090b42835120b42831090cc3429340ac1835
|44=>0xb0c448350a0c42c290d0a44c330b0d42d991d04c24310d0a428310b0a418350b0c428951312c28310b0d4242d0b0c434310a0d42ab60bab414130d0c4342d0a0c4242f0d0a42c15030d434310b0a410e51d0bc24310d0a40c35030cc2c290b0c494311312c28310b0d49c2f030d434310b0a49c37040c4242d0a0d6ac290b0a414130d0c57c13530a44c330b0d49c2b
|45=>0x305c34310b0a49c2b030c40c350b0a49c33040c40c350b0a49c33270ac0c350b0a5142f340a418350b0c4102d1d0bc24310d0a410531312028310b0d49c2f270dc4c290b0d424310a0d44c130b0d424310d0a40c370b0a49c170a13434310b0d6c031170bc24110d0a4782f1d04448350a0c49c2f0d03410310b0a424310b0d424330a0d42e510b0d448130a0c47411
|46=>0xd0c42c29210c49c2b030d42c291312c28310b0d410f9200c4242f0d0a514131d0b424310d0a40c170b0a414290d0c48431130ac2c290b0d43c390305034310b0a4482d0b0d434310a0c44c490a0c42c351e02c7411050a434310b0a44c480a0c42c35370d40c130b0a414460304434310b0a514371d0b414290d0c43431270cc242d0a0d4100e0b0a418350b0c41411
|47=>0xd0c42831120b434291204428310a0c44c31130a42c351d04c2c31050a434310904434290a0c434310d0a44c4b0a0c42c35130a410d1130c42c351314c4c480a0c42c350a0c40c140d0c42c29b50a4e033130442c350a344d011060d42c31090c4c82d090cc34291304c0c330b0a42c352712c340d0a0c42c29270dc4c31130a42c35270bc284d0d0c42c35052a40c17
|48=>0xa0c42c350b0c42831300c44c130b0d4241b0b0c434310a0d49c37130a428310b0d5142b0d2340c310b0a49c330d03428310b0a42413090b43429090442c310d0c42835040e40c140d0c42c29090bc9c33090b434292704c4c31130a42c350b0d40c330b0a434290b0a560310904c3429270cc0c31030d42c290a0c44c311304c2c350b0a44c31130442c350a0b41015
|49=>0xa0c42c350b0c48811270cc242d0d0a42c160d0c424110a0d49c2f270c40c350b0a43431370d40c130b0a410350d238482d0a0c42815130cc34310b0d44c110d0b4142b0d0c44c290a0c42c350b0c49c2f0a2144c2b0b0d42d5e580c424130d0a48c110b0d418290b0c4100d0a0c42c290b0d514111d0b448350a0c51413270c4242d0d0a410a1230dc18290b0c43449
|50=>0xa0c4242f0d0a514371d0b424310a0d44c311312028310b0d49c33130a428310b0d514331d0b414290d0c474331d0b424310d0a52433270440c350b0a40c31030cc2c290d0a40c350305c34310b0a6ec31380ac4c110b0d48837270cc242d0a0d4100e0d03428310b0a494311312c28310b0d408c10a1344c130b0d4242d580c424130d0a5a4312704c0c350b0a44c13
|51=>0xd0a42831030d434310b0a42d610904c3429130444c290a0c42c35220bc9c33030d42c291d0bc142d050a434314504cd029060d42c31230cc482d120d42831030c40c350d0c42c29270bc9c37130a42c35040542c150d0c42c29270bc340d040c42c290b58424310904c3429090c42c290904434293412c18350b0c514370a344142d0d0c4102d0d0a428310d0c43431
|52=>0xb0c434290a348142d0d0c424130b0c428310d0a4342d0b0a424110d0a6fc29be0dc10190b0c42d991d04c48350a0c44c490a0c42c350b0c474130a05434310b0d44c480a0c42c350b0c428d2130c42c350a0d410e51d0bc48350a0c42c31090c42c290d0a4140d0b0a428310d0c4d8433404418350b0c42c490d0a428310b0d43431270cc242d0a0d49c11270c4242d
|53=>0x30442c29270cc340d0b0a42c313b0dc8c11060a42c310d0384c2b0b0a42c350b5144c4a0a0c42c350a0c43491030dc2c295f0dd4c29130cc2c350a0b44c311304c2c351312c28310b0d51437270c4242d0a0d410e51d0bc24310d0a49c2f0a13434310b0d42831340ac18350b0c51437270c4242d0a0d41031270cc242d0d0a4882b270cc242d0d0a410d1340ac1835
|54=>0xb0c49c13090b43429230443431060a42c311d0b424310d0a474330b0d448350a0c42c290a0c434310b0c428110d0c42c35042584c4b0a0c42c350d0382c29090bc342904424d02b060d42c31270ac242d090cc34291e10c7411050a434310a0c42c31030dc2c290b0c560310904c34290b0c42431090b434290d0a48c33120b42831103742c310304c2c29090cc2835
|55=>0x120d42831130a410d2130c42c35060d42c31270ac340d040c42c291315010490a0c42c35710acc82d090cc3429450dcd029060d42c31250c44c4b0a0c42c35123884c110a0c42c35450cc28d1050b43431270bc2885130ac2c35090c49c33090b43429450cc742d090c43429040340c160d0c42c29120d4108e120b428313012428311304c2c350a534d033050b43431
|56=>0x60a42c311304c4c290a0c42c350d0a410d1050b43431450dc742d090c428350a0c44c310b0d42835c50c41086130ac2c350a0c4242d090cc34291d044142d050a434310d0b424330b0a434290d0a410d1130c42c35320b47433120d428310412434290a0c43431130a4c0311304c2c3510c441092030dc2c29220ac9c33030d42c294504c742d120d428310a0b47433
|57=>0x90b43431090bc28350d0b42c290a0c43431ab0a414130d0c4e4331d0bc24310d0a4284d0b0c44c2b0b0d434290a0c42c350b0c424310904434290b0d40c310d0c42c290d0b424310b0a434290b0a44c480a0c42c35340cc2c150d0c42c292204c9c33090b43429270c49c33090b43429042848c37060a42c311e02c7411090c428350b05428350d0c42831041342c35
|58=>0xb0d42c350405434310a0c41031270cc242d0d0a4882b270cc242d0d0a4343104234482d0a0c410fa200c4242f0d0a49c2f130cc4c290b0d411855e0b4142b0d0c43429240c40c370b0a435112304c18290b0c44e530b0d448130a0c4742f090c434290d0b42c31050ac34310a0b4d02b060d42c31130c42c35120d428310a0c49c11030d42c290b0c42c290904c3429
|59=>0x340a418350b0c514331312428310b0d514110305434310b0a4282d0b0c448350a0c44c291312028310b0d49c330d0342c290b0c4242d0904c34290d0a42c310304c2c290d0382c29090cc34290230428351304c2c351e02c7411090c428350405434310b0a42c31046840c160d0c42c29450dc9c31090b428350d0a410330b0a42c35270cc242d0d0a49c330a2144c2b
|60=>0x2704c4c290b0d49c2b090c4242d0d0a434292304418290b0c48c130b0d418290b0c42c4a0d0a428310d0c410350d2380c310b0a4dc350a0c40c130b0a4242d0b0c428310d0a49c2b270c40c350b0a4102d1d0bc24310d0a49c170d0c4242d0a0d49c33130c44c290b0d4c0290a0c44c130b0d484310a2144c2b0b0d5144b1d0b448350a0c474331d0b448350a0c51433
|61=>0xb0a7303104208242f0d0a5a0290305834310b0a49c330d03428310b0a4c82d090cc34295d0a410d2050b4343104038340d0b0a42c31450bc9c31030d42c290d0c42c31130ac2c35450cc742d090c43429103740c310304c2c295d0a410d2130c42c35450bc0c150d0c42c290a0c434290b0d4540b0b0c448110a0c5bc33370d40c130b0a4342d040c42c290d0a43431
|62=>0xa0c5c413320b424330d0a60c11400d40c330b0a44c33030dc2c350b0a49c2f270c4242d0d0a42c29040c4242f0d0a42831030d40c110b0a42f3d3204c24330d0a4282d130c42c350a0d49c332704c242d0d0a4742f1d04424310d0a4140e0b0a428310d0c49c2b0d03410310b0a410f9200c4242f0d0a51437340a418350b0c41031130ac2c290b0d410f5240c40c37
|63=>0xd0c42c35aa0beac290504c34313705834310304c2c2904c0a582d120dc28312704c2831090b434290a0b42c311204428310a0b410150d0c42c3512134342d1204428310b0d4108d030c42c29490cc9c11090b434291312028310b0d42c3104134284d0b0d42c31d50b45c33090443429400d40c330b0a5a4312704c242d0d0a434290b0c40c370b0a748110d414482f
|64=>0x130c42c351312c2c490a0c42c35030c42c290904c34290a1384c310b0d42835450ac742d120d42831090c42c29090bc34293b02c108d120b428311037434310304c2c2909be83429040642c31220bc9c33090b43429040c49c33090b43429090443429130cc2c351d04c2c29090c434290b0a42c35120d42831450cc742d120d42831090b41031090bc34291d0bc2815
|65=>0xd0342c290b0c419610b0c424130d0a49c33090b434290b0d4540b120442831120b410150d0c428311304c34290a0c42c35dc10c1155050bc34310a0c42c35090cc2835270cc4c31130a42c353404c2831060d42c310b0a434311304c2c354512c348d120b428310d0a410d2050b43431300c428351304c2c35530c54c29130cc2c3502da54c13130cc2c350d0a410d2
|66=>0x1502c48110a0c418350b0c428310d0a4742f040b448350a0c4103b0305034310b0a54c29130cc2c350b0c4dc310d0c40c130b0a474330b0d448350a0c5142f0305434310b0a4741b0b0c448350a0c514130305434310b0a4284e0405434310b0d49c370a2144c2b0b0d43429030c40c130b0a42c291d04c24310d0a42413270cc242d0d0a428310305034310b0a49c1b
|67=>0xb0d410390305034310b0a5a4312704c242d0d0a42d610b0c424130d0a42c31090c4242d0d0a434310b0c44c130b0d4242d1d04c24310d0a5c8130a554142f0d0c49c330d0340c130b0a424310d0a44c560412428310b0d46c430a0d414110d0c42831320b424330d0a48811270cc0c350b0a49c370a0c4242d0d0a410e61d0bc24310d0a4242f130cc2c350a0d44835
|68=>0xa0c4243127044242d0d0a514331d0b448350a0c4104d130c42c350a0d428d1340cc18350b0c49c33130a44c110b0d4343104238482d0a0c42c350b0c428310d0a44c4b0d0a428310b0d428c1130c44c130b0d5243327044242d0d0a4882b270cc242d0d0a4c82d1d0cc48350a0c42831400d40c330b0a49c110d0342c290b0c42d5d580c424130d0a43429131202831
|69=>0xa0c42c290d3b88c11060a42c31230dc2c490a0c434310b0c42835030442c291e02c7411090c428353705434310304c2c29450dc742d090c428350a3042c311304c2c350d0b42c29090cc34290b0542c29050a43431041242c35120d42831450ac742d120d42831090b434290a0c43431270cc340d040c42c290d0c42c350b0a474130b0c424310d0a42c310b0d44835
|70=>0x230dc18290b0c4142d1d0cc14290d0c49c370a0c4242d0d0a49c33090b43429120b4540b120442831135ec342d050ac34310a1389c31130a42c35710acc82d090cc34290d0a42c29060d42c31270dc2885130ac2c35450449c31090b434290b0c49c33090b4342945044d029060d42c312706c340d0b0a42c310d0a48c33120b428310b0c49c2b090b434290d0b40c33
|71=>0x270444c31130a42c3510374100e0b0a42c352204c9c33030d42c29530a44c330b0d49c33270c40c350b0a41301960b448370a0c4782f1d04424310d0a4d04b0b05434310a0c410310a2144c2b0b0d410f5240c40c370b0a44c310b12428310b0d48431270ac242d0d0a478431d04448350a0c5142f270c4242d0d0a49c2f030c40c350b0a424130d0a428310d0c43429
|72=>0x1304c2c350bab414130d0c424310b0a424130d0a425070d0a4482f0a0c4284d0405434310b0d49c330d03410310b0a42c350d2380c310b0a42c291312c28310b0d40ead0b0a414130d0c49c31090b434290b0a4742f090c43429270dc4c33130a42c35450ac9c31030d42c29450ac0c150d0c42c293b02c108d030c42c29450cc742d090c43429200c49c2f030d42c29
|73=>0x3012828311304c2c35340a418350b0c4c82d090cc3429036840c160d0c42c2909be83429040642c31270cc1031090b43429270ac9c33090b434290b0a42c350904c2835830ad0035030cc2c2945044d029060d42c310b0a4742f090c434294204428d2050b434310a044d02b060d42c314204428d2130c42c350b0c49c2b090b43429620cc2d610904c34290a0c408c1
|74=>0x27044242d0d0a410e51d0bc24310d0a410a90305c34310b0a5142b0305434310b0a48031270bc0c350b0a414110b0c434310a0d49c37270ac242d0d0a43429020e40c140d0c42c29220449c33090b434290b57560310904c34290b0d434290304c2c29210c49c2b090b43429450bc9c31090b434294504c9c31090b434290d0a4340e040c42c29450bcd029060d42c31
|75=>0x90b434290a0c43431090b4241b0b0c43429090b47411090c434291d0b47411090c434290b0c4242d090443429450dc9c31090b42835490cc9c11090b434297e0dcdc310304c2c29090c424130d0a424111d0bc24310d0a5a4312704c242d0d0a42d610b0c424130d0a4348d030c40c130b0a44c4b0a0c42c350b0c42c311d0bc24310d0a42d991d04c24310d0a42c31
|76=>0xb0d424130a0d42c31050a434310b58424130d0a49c330d03410310b0a4782f1d04424310d0a49c3327044242d0d0a426f80d0a410190b0c49c33090b43429270cc9c31090b43429090bc34290a0c434311e0bc7411090c434290b0c47411090c43429270dc9c2b090b434290b0c49c33090b43429220449c33090b434294504cd029060d42c31270bc4c31130a42c35
|77=>0xb0d47411050a434310a3044c130b0d42c490a0c42c35270cc242d0d0a49c31090b434290d0a410310b0a4340e0a0c42c290b0c434310a0d4102d0a0c434310b0c4242d0d0a434290a0c434310305834310b0a41035030cc2c29090c4102d0d0a47411090c434292704c242d0d0a49c11030d42c29230cc18290b0c434310904c2835090cc102d0d0a40c110d0c42c29
|78=>0xd0c42c35030d40c110b0a4241b0b0c434290b0a424310d0a42c31090443429be0dc10190b0c440dd0304c2c2904344142d0d0c48c33120b428310d03410310b0a410d1130c42c359604448370a0c48c13060a42c310a0c424110d0a41033030d42c29270ac242d0d0a42831040d42c310a0d4142f0d0c428d2050b434310a0d40c110b0a428d2130c42c35270444c29
|79=>0x940d448130a0c4348d030c42c290b05434310a0c44c330b0d428350a0d414110d0c40c170d0c42c29130c428310b0d47433050a434311d0bc48350a0c42831040b434290412428310d0c42831090bc34290b94448130a0c49c13090b43429320b424330d0a408c11304c2c350b0a414130d0c48c37060a42c310d0a42c290b0d47413120d42831040c40c350b0a42815
|80=>0xd0a48031090bc34292304418290b0c4100d0a0c42c291d0b414290d0c4102d120dc28310b0c40c130b0a49c2b090b43429090c424130d0a410330b0a42c35040a418350b0c43431090cc28350a0d44c130b0d48433130ac2c35240c40c370b0a4282d040d42c310b0c428310b0a49c33090b43429340a418350b0c4102d120d428310d03428310b0a40c31030d42c29
|81=>0x90443429200c4242f0d0a4482d0a0c434290a0c42c290b0d49c11090b43429300a44c130b0d47411090c434290b0c40c370b0a410d2050b43431300c44c130b0d410d2130c42c35130c42c350b0a4e02b130442c35040cc4c2b0b0d43431090b42835030cc0c350b0a42831130442c35040c42c290b0d49c2f030d42c291b0bc14110d0c42c4a0a0c434310b0c42431
|82=>0xa0c44c130b0d4540b120442831130a428310b0d4242d0904434290a05414110d0c42c310904c34293204424330d0a44c31130ac2c351b10c14110d0c47411090c43429042184c2b0b0d428d1050b43431960b448370a0c50011030cc2c293404418350b0c50035030cc2c290b58424130d0a42c290904434290d0c4242f0a0d48431130ac2c35040c44c2b0b0d45c2f
|83=>0xb0d42c290a0c434310b0c44c110b0d49c11090b434290d0342c290b0c44c490a0c42c351312028310b0d424310b0a434292704c0c350b0a424330b0a43429040c4242d0d0a43429130cc2c350a0c418350b0c42811050bc3431400d40c330b0a47433090c43429130c44c110b0d40c330b0a42c35270bc0c350b0a560310904c3429270c4242d0d0a40c310304c2c29
|84=>0xb0a434291d04448350a0c4242d040cc3429230cc482d0a0c48c13060a42c31270ac0c350b0a428110d0c42c3504344142d0d0c410d1130c42c350b05414110d0c41031090bc34290d03828310b0a42431090b434290b0a410330d0a4742d090c43429270cc0c350b0a410490a0c42c350d0a410190b0c42c31050ac34310305834310b0a428310b0d42c311312c2831
|85=>0x240c40c370b0a49c2b030d42c29130ac2c290b0d428311304c2c351d0cc48350a0c4340d0a0c42c29270cc0c350b0a4282d050443431130c44c290b0d4d029060d42c310b0c424310d0a4342d050ac34312704c0c350b0a40c310b0a43429040c4242d0d0a54c13130cc2c35230dc18290b0c41091030dc2c29300c44c130b0d42c29060d42c31270c4242d0d0a41031
|86=>0xb0d4543712044283127044242d0d0a40c330a0c42c290b0a424330d0a41081090bc3429041342c350b0a4e033130442c35320b424330d0a560310904c3429040382c290b0d410490a0c42c290b0c424130d0a4340e040c42c291d0b448350a0c44c480a0c42c35270bc242d0d0a42c310504434310b0a4242f0d0a42c31130ac2c3527044242d0d0a47411090c43429
|87=>0xb0a42c31040b424310d0a49c13090b43429090c4242f0d0a42c49040d428310b0d448350a0c4242d040cc34291d0bc24310d0a4340d040c42c290d0a42c290b0c44c330b0d42c290d0a428310b0d47413090c4342904208242f0d0a41031090bc3429090c4242d0d0a434311304c2c351d0b424310d0a49c31030d42c29090b424330d0a42431090443429530a44c33
|88=>0x4554142f0d0c4c82d090cc34290d0a40c370b0a49c33090b43429040c44c2b0b0d4340d0304c2c290d414482f0a0c4142d050a434312704c242d0d0a42835060a42c31090b424130d0a410310b0a42c35200cc242f0d0a42c31090443429040c4242f0d0a40c150d0c42c290a2144c2b0b0d4242f040cc3429270cc242d0d0a44c330b0d42c31040c4242d0d0a4340d
|89=>0xd0c428310b0a40c310b0a42c29040c424130d0a410290b0c410330b0a4242d0d0a42c290d0a410190b0c44c130b0d4482f0a0c44c330b0d414110d0c424330d0a4482d0a0c40c370b0a448110a0c44c110b0d45c330904434291d0bc24310d0a48031090bc34293204c24330d0a47413090c434291312c28310b0d4742f090c434290d0440c310b0a47413090c43429
|90=>0xd0a42c310d0a42c290b0d410310d0a44c330b0d410330d0a410310b0a428310d0c424310d0a44c110b0d40c350b0a424330d0a4102d0d0a4242f0d0a424110d0a4142b0d0c40c370b0a418350b0c40c130b0a410350b0a424310d0a428310b0d4242f0d0a42c290b0c414130d0c410310d0a4242d0d0a424110d0a428310b0c410350a0c434310a0d414290d0c4102d
|91=>0x40a42c31040c43429040cc102d040c434310b0d42413
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x14380000042e01b600a38035c00ec0007
|7,0=>0x77303a901c8c0de606d20360800000d260672000000000000006520000000000000062302f98172a0b5400000000016280ad4054a028d8000009f40000026d012e8096104830000011880866000000000100c07a6000001d18000006f5000001ad00ce806250000017540aec05340000013d009680000023a010d007ac0394000000000068a02f5
|7,1=>0xa9b0000029e814a5000005118280813c409ba8000000001316000004b50250a12440000000000000120400000469822c81124000000000000010c6083a800000000103407f2800001f0c0f44
|8,0=>0x124280000486a23e511ca88d1400002304115a88994442a21c510c988550420a20b5103a080943faa00000fca07d1400001ef50f52879543c0a1dd30ec2874d439e81ca50e2a87050378a1b930da286bd4354a1a550d0a06714332619630c99863d0318618750c1a0600c2fa617850b9a85c0c2d8800000b3a800002c4a00000aea800002b280000
|8,1=>0x1a028cf1067083344197a8ca9464c8323318fa00000634a318218a20c3d4614a3073181a0bfd05f682f651792000005dc82ea417320b8545ba82d9416aa0b41459882c7516128af545728000015a28abd455862a9315228a7d4534a296414998a3d0000028a5142a8a0144f6a2765000009c544da826850000098d44c0625b512b2800004a4824d5
|8,2=>0x216a90a14846a41e520ca9051481ea40a5202a900147fa63f941fa2800007e083eb500000f9d07c683de51eca800007aa83d0500000f310792600001e228efd477683b651d998000076423ae400000ea54748a00001cfa8e69472c839331c728e25470a8380500000ded46eca37241b798dad06cca36151ae28d5d4000000001a928d35469463455
|8,3=>0x2962949d4a44a51e428ca94514a1ea50e1285200000a0aa500527da93e0c9e884ef5275a13a489cc64e1500001375000004d85269a93394992a4c4525fa92f0c96ea4b34257a12b0c95264a63250a9271492ea49342481922d491064844240991f508f464755238a11b508d8246932322917d48b4a4573229a113d089684465220a90f1486ea4325
|8,4=>0x1871400006175309a183d0c14a6064300a97f50bf465f642f8a97b8cbd845e842f1a9779400005d952ea2973d4b94a5c552e0296ed4b6ca00002d8a96b50b58200002d3a96894b3c859a42caa96414b1a658942c2295fd4af4a57642b8a95b8c00005695000015914abea55c32ac215510a9ea54b42a3280000a86653e529ca94d8c00005315
|8,5=>0x388a00000e1a870a3382a80000e0466fe437d21bd54de286ec5373a9b8d0dc06000036da80000daca6d15366a1b250d88a6bf535e19add4d6686b03355a9a994d44869d534c29a4d4d1ca6895343180000d04867d533c299cd4000066f43361999d4cc4a65e432d219554ca0a64b5323a1910c0000000031fa98e94c6c863153162989d4c4866213
|8,6=>0x200d4ffe87fc33fc21fcd4fdca7eb3000000000fcca7e333ef29f654fa8a7cf53e5a1f194f8487be43dd21edccf64a7af33d529e990f44879d500001e68cf2aa790500001e2d4000078653c121df54000077b23bb29dc90edc876b33b329d854ebc675953aaa1d48ce9c874a43a2a9d014e76a7374399a1cb94e52a724538fa80000e34a7155
|8,7=>0x4710800011bc88d9546a2a33d5194a8c64461222f91172a8b45000022bd5154a8a55450280001136a000044c1a24d511e888a5442aa20150f8887754392a1b910d668665430aa17150aea85250000213900000849500000000000008445000020fd4000083a541aaa0c15056a82834129a0850000081c540ba80001024a000040722025501020000
|8,8=>0x241151fea8fb447ba00000000000004792a3b551d0a8e35
|9,0=>0x5022280113f889f844fa227c113d889e844f22278113b889d844ea22741139889c844e222701137889b844da226c1135889a844d2226811338899844ca226411318898844c22260112f8897844ba225c112d8896844b22258112b8895844aa22541129a694944a2a2505127a8939449aa24c5125a89294492a2485123a8919448aa2445121a89094
|9,1=>0x580a2bf515f28af6357922bb915d48ae6457122b7915b48ad6456922b3915948ac6456122afcd5768ab74559a2abd15568aa74551a2a7d15386a98454a22a4115188a88454222a0114f88a78453a229c114d88a6845322298114b88a58452a2294114988a4845222290114788a38451a228c114588a2845122288114388a18450a2284114188a084
|9,2=>0x5ff22fe917ec8bf245f722fa917cc8be245ef22f6917ac8bd245e722f29178c8bc245df22ee9176e6bb345d7a2ead174e8ba345cfa2e70d7308b9445c89ae3517128b8545c0a2df516f28b7545b8a2db516d28b6545b0a2d7516b28b5545a8a2d3516928b4545a0a2cf516728b354598a2cb516528b254590a2c7516328b154588a2c3516128b054
|9,3=>0x67da33e0d9e88cf04676233a119c88ce0466e2336119a88cd0466623324d98a8cc1465ea32e5196a8cb14656a32a5194a8ca1464ea3265192a8c914646a3225190a8c81463ea31e518ea8c714636a31a518ca8c61462ea316518aa8c514626a3125188a8c41461ea30e5186a8c314616a30a5184c6c22460f23069182c8c12460723029180c8c024
|9,4=>0x6fc137d11be08dec46f4237911bc08ddc46ec237511ba08dcc46e4237111b808dbc46dc236d4db628dae36d5236991b448d9e46cd236591b248d8e46c5236191b048d7e46bd235d91ae48d6e46b5235991ac48d5f36ada355d1aa68d4f46a5a351d1a868d3f469da34dd1a668d2f4695a349d1a468d1f468da345d1a268d0f4685a341d1a068cff4
|9,5=>0x778a3bb51dd28ee6377123b791db48ed6476923b391d948ec647619bafd1d768eb74759a3abd1d568ea74751a3a7d1d368e97474a1ba411d188e88474223a011cf88e78473a9b9c51cda8e6a3733239891cbc8e5a472b239491c9c8e4a4723239091c7c8e3a471b238c91c5c8e2a4713238891c3c8e1a470b238491c1c8e0a4703238091bfc8dfa4
|9,6=>0x7f723fa91fcc8fe247ef23f691fac8fd247e723f2cdf8e8fc347dfa3eed1f6e8fb347d7a3ead1f4e8fa347cfa3e6d1f2e8f9347c7a3e2d1f0e8f8347bfa3ded1eee8f7347b81bdb11ed08f6447b023d711eb08f5447a823d34de928f4547a0a3cf51e728f354798a3cb51e528f254790a3c751e328f154788a3c351e128f054780a3bf51df28ef54
|9,7=>0x875a439d21c690df486e9436521aa90d14866a4325218a90c1485ea42e5216a90b14856a42a5214a90a1484ea4265212a90914846a4225210a9081483ea41e520ec70724837241a920cc9062482f2416920ac9052482724129208c9042481f240e9206c90324817240a9204c9022480f24069202c9012480724029200c900247ff23fe91fec8ff24
|9,8=>0x8f4a479523c291dd48eca475523a291cd48e4a4715238291bd48dca46d5236471ae48d5246992344919e48cd246592324918e48c5246192304917e48bd245d922e4916e48b52459922c4915e48ad2455922a4914e48a52451ce286913f489da44dd2266912f4895a449d2246911f488da445d2226910f4885a441d220690ff487da43dd21e690ef4
|9,9=>0x97024b74e5b292d54968a4b35259292c54960a4af5257292b54958a4ab5255292a549520ca8125389298494a24a4125189288494224a0124f89279393b1c9c924dc926a49332498924bc925a492b24949249c924a492324909247c923b391ba48cd245e922b4913a488d243e921c390c248512420920c490424811240091fc48fc247d123e271ed4
|9,10=>0x13334997a4cad264e9324399024c7126309314498824c3126109304498024bf125f092f4497824bb125d092e44
|10,0=>0x9fa1cfc4e7dc73eb39f41cf94e7c473df39ee1cf64e7ac73d339e81cf34e79473c739e21cf04e77c73bb39dc1ced4e76473af39d61cea4e74c73a339d01ce74e734739739ca1ce44e71c738b39c41ce14e704737f39be1cde4e6ec737339b81cdb4e6d4736739b21cd84e6bc735b39ac1cd54e6a4734f39a61cd24e68c734339a01ccf4e67473373
|10,1=>0xa5a1d2c4e95c74ab3a541d294e944749f3a4e1d264e92c74933a481d234e91474873a421d204e8fc747b3a3c1d1d4e8e4746f3a361d1a4e8cc74633a301d174e8b474573a2a1d144e89c744b3a241d114e884743f3a1e1d0e4e86c74333a181d0b4e85474273a121d084e83c741b3a0c1d054e824740f3a061d024e80c74033a001cff4e7f473f73
|10,2=>0xaba1d5c4eadc756b3ab41d594eac4755f3aae1d564eaac75533aa81d534ea9475473aa21d504ea7c753b3a9c1d4d4ea64752f3a961d4a4ea4c75233a901d474ea3475173a8a1d444ea1c750b3a841d414ea0474ff3a7e1d3e4e9ec74f33a781d3b4e9d474e73a721d384e9bc74db3a6c1d354e9a474cf3a661d324e98c74c33a601d2f4e97474b73
|10,3=>0xb1a1d8c4ec5c762b3b141d894ec44761f3b0e1d864ec2c76133b081d834ec1476073b021d804ebfc75fb3afc1d7d4ebe475ef3af61d7a4ebcc75e33af01d774ebb475d73aea1d744eb9c75cb3ae41d714eb8475bf3ade1d6e4eb6c75b33ad81d6b4eb5475a73ad21d684eb3c759b3acc1d654eb24758f3ac61d624eb0c75833ac01d5f4eaf475773
|10,4=>0xb2c1d954eca4764f3b261d924ec8c76433b201d8f4ec7476373
|11,0=>0x5afcad7a56bb2b5c95adcad6a56b32b5895abcad5a56ab2b5495a9cad4a56a32b5095a7cad3a569b2b4c95a5cad2a56932b4895a3cad1a568b2b4495a1cad0a56832b40959fcacfa567b2b3c959dcacea56732b38959bcacda566b2b349599cacca56632b309597cacba565b2
|12,0=>0x16c91b640db1c6d8c36c51b620db0c6d8436c11
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 17
def pmP:Nat→Nat
|0=>0x293c0000000005080000000000a008000000001400000000000204200000000040800000000008040000000001004000000000200200000000040000000000006000000000000880000000000100a0000000002000000000000240800000000042800000000008480000000001080000000000202000000000040100000000008000000000000c3000000000006f00000000000a4000000000005000000000000900000000000108000000000020000000000003c00000000000340000000000008000000000000
|1=>0x10083c0000000201000000000040014000000008002400000001000400000000200020000000040000800000008000000000000c080000000001800000000000280000000000048028000000009000000000001042040000000200100000000040000000000007d6d800000000c52000000000182008000000030000000000004204000000000820000000000102670000000020028000000004004000000000800040000000100000000000011400000000002180000000000400240000000080000000000008000
|2=>0x200840000000040100400000008020000000001000280000000200048000000040008000000008000400000001000010000000200000000000038001400000006080000000000c0400000000018005000000002c00000000000540a600000000a14000000000141800000000028203400000005040280000000a0401000000012210000000002410000000000442008000000081801000000010285a0000000205004000000040a00000000008130c000000010205a00000002040000000000403860000000080420
|3=>0x28084000000004c7004000000098600000000012148100000002418000000000481000000000090010000000011800100000002228000000000444014000000088406800000011080900000002210020000000441024000000088200000000011000000000002120020000000423004000000084200000000010800100000002030020000000405080000000080a028000000101400000000020261800000004040b4000000080810000000010101e000000020200200000004040000000000806000000000100800
|4=>0x30380000000006060000000000c0b86000000018148d000000030287e00000006050b40000000c0a0f000000018140d000000030281200000006050140000000c0a008000000181400000000030205a00000006040800000000c08008000000181000000000030180000000006020140000000c04000000000180420000000030080a00000006010040000000c0200000000018005e000000030004000000006000780000000c0000000000016142d000000029385a00000005050140000000a0a008000000141020
|5=>0x34290a00000006850b40000000d0a0680000001a1409000000034280200000006831380000000d060080000001a0400000000034000200000006650b40000000cc8000000000191c2d000000032380200000006452b40000000c8a44800000019142d000000032281a00000006450040000000c86068000000190c010000000320ed800000006412040000000c8200000000018f32c000000031385a00000006260340000000c4c00800000018942d000000031080200000006070b40000000c0e068000000181c05
|6=>0x38385a00000007070340000000e0a1680000001c140d000000038281200000007050140000000e0a0080000001c1400000000038200200000007000000000000dce1680000001b9800000000037105a00000006c72b40000000d8e4680000001b1c2d000000036381a00000006c52b40000000d8a1680000001b140d000000036091200000006c12040000000d824000000001b040d000000035385a00000006a60040000000d444680000001a880d000000034887c00000006870b40000000d0e0080000001a1489
|7=>0x12202180000002427004000000480a67000000090147e000000120101c0000002400004000000450000800000089040100000011020020000002200004000000420800800000082407e00000010400400000002021004000000400e0000000008000200000000c0004000000007e20040000000f8e1680000001f140d00000003d385a00000007a70000000000f480080000001e8c0500000003c380000000007850b40000000f0a0680000001e0c0500000003a385a00000007470340000000e4a1680000001c940d
|8=>0x2100040000000420000000000080080000000009b1cad000000136385a00000026c60000000004d824000000009a9c01000000134285a00000026840000000004d04168000000991c2d000000132300200000026450b40000004c88008000000990c80000000132181a00000026430040000004c8600000000099088d000000132080200000026270b40000004c4e068000000981c2d000000130300a00000026052b40000004c0a16800000098140900000013008020000002600004000000488a068000000910c0d
|9=>0x82008020000010401000000002070a0080000040e100000000081609020000010241000000002040810000000405080000000080820000000010081004000002010012000000400102400000080008480000010000080000002000000000000200140000000023e185a00000047a70b40000008f461680000011e1c2d00000023c28de00000047850b40000008e8e1680000011d142d000000238385a00000047053bc0000008e0a1780000011c142d000000230285a00000046010800000008408100000001080024
|10=>0x839281a00000106c72b40000020d8e1680000041b14ad000000836285a00000106c50340000020d824480000041a1c2d000000834381a00000106870140000020d0a0680000041a1405000000834215a00000106810240000020c8e068000004191481000000832281a00000106070340000020c0e02800000418140d000000830281200000106050140000020c0a00800000418100100000082920020000010504004000002090200800000412040000000082400000000010463000000002080a008000004101000
|11=>0x1838081a00000306c70b40000060d8a16800000c1a1c2d000001834285a00000306454b40000060c4e16800000c181c2d000001830305a00000306055b40000060c0a96800000c18142d000001830205a00000305040b40000048c0a168000009081400000001210200000000240040000000040d8000000000818142d00000102620000000020080080000004000a100000008001020000001000200000000200010800000040002068000008000400000001000004000000126a720000000242ca0000000041e1405
|12=>0xa21000480000140201090000024040204000004800140800000900008000000104201010000020040012000004008000d000008000080000001000000000000180c0016000003010042c000006020000000000806040a00000100802140000020100028000004020001a00000804000000000100180140000020010028000004000081000000800000200000088400000000010180024000002020000800000404000000000080400020000010080000000001930385a00000326054b40000060e0a16800000c1c102d
|13=>0x10032385a00002006450b40000400c86068000080181c0d000010030380a00002006050b40000400c0a068000080181405000010030280200002006050000000400c08008000080180420000010030000200002006000000000400a48000000080130005000010022080a0000200405080000040080800000008010040000001001200000000200205024000040040a00800008008100000001000820000000200084004000040000000000006800042800000c030085000001804010a00000300002000000051180020
|14=>0x11810205a00002301000040000428e0a1680000841a140d000010834281200002104a6200000042090a0080000840a1001000010810201200002047000340000404d8e1680000809b0801000010132385a00002026470000000404c86068000080981c01000010130285a00002026050340000404a08008000080910c0100001003c281a00002007450340000400e880080000801b1c2d000010036381a00002006c70000000400d8a1680000801b140d000010034381a00002006870140000400d0a1680000801a1409
|15=>0x30032385a00006006450b40000c00c0e16800018018142d000026020005800004c0400080000090080806000012010040c000022030001800004404000000000848e0a16800010918142d000021200204000004204050000000840808000000108001400000020230285a00004040040000000800c0a168000100180420000020024000000004004040800000800800100000100100000000020012300000004002430000000800108000000100020020000020000200000002307040b40000460c0a16800008c18102d
|16=>0x10000000000001800487024000300040e048000410000824000080230004000010040000800002000802060000400001400000080000200800010000040000002000002120000400000420000080000081a00010000000000001300c02000000230180000000044002005000008202010a00001000f4e168000200100000000040000205000008000010100000c48c0a1680001811c142d000030132385a00006026430b40000c00e0a1680001801b1c2d000030036285a00006006c30b40000c00d0e1680001801a142d
|17=>0x1008202840000201040108000040204021000008011a9c2d000100230285a00020042000800004008000120000801000020000100120004000020007850b40004000e0a1680008001c1020000100034285a00020006450b40004000c0e16800080018142d000100022004000020004020800004000800160000800100028000100020004000020002800800004000440100000800080028000100010004000020000040800004000002140000800000420000100000005a00020000000900004000000100000800000001
|18=>0x126020005800024806470b40004848e0a16800090918142d000121230284000024246000800004820c02168000900991c2d000120030285a00024000000b0000480000010000088098142d000110034284000022006840800004400c0a16800088018002000010d030085000021446870b40004140d8a16800082018142d000104000005000020406050b4000408000016000080c1b142d000101038085a00020206050b400040400021000008041814ad000100830285a00020106050900004020c02168000804180020
|19=>0x150132285a0002a026050b40005400c0a168000a6818142d00014d026205000029806010a00005180c00160000a0918142d000141030285a00028106852b40005020c8a568000a0118142d000140120004000028007a70b40005000e0a168000a0018142d000140030085a00028006000800005000808160000a0010102000014002000400002800200080000500000a140000a00001420000140000205a00028000040800005000002500000a00000420000140000004000026246050b40004c00c8e168000930191c2d
|20=>0x200200004000040006000100008000808000001000100020000200020001a000400000400000080000020000010000000000001c2230385a00038406870b40007080c8e168000e10181c2d0001a6012185800034244010800006828c0a168000d0418142d000181036285a00030206450b40006000d0a168000c0019142d000180030285a00030004010a00006000008100000c0000042800018000008400002cc06050b4000598048c160000b0918142d00016123020400002c046050b40005800c0a168000a80991c2d
|21=>0x321230004000064006470b4000c800c8c100001900190c20000320030385a00064006050b4000c448c0a16800188818142d000310030285a00061a06c00a0000c240c8a168001809081420000300032385a00060006450b4000c000c0e16800180018142d00030003000480006000404080000c00080016000180010002000030001000400006000004080000c00000800000180000042000028021420400005004204080000a000800100001048080408000209010080000040242050000008040402100001008000020
|22=>0x900034385a00120006070b40024000800100004800081020000900000201000120000010800022800808100004400080020000844024085000108804010a0002100040014000420000102800082402008180010480401000002084080a000004100100420000820004004000101000050a0002010080814000402001002800080102020400010020000080002000800a100004000100000000800010005000100002000800010000008160001d011c142d000380238385a00070046850b4000e008c0a16800190918142d
|23=>0x10000030285a01024006050b40204040c0a16804080018142d004000338281a00800047070b40100008e0a168018000190425001000030284a00160346050b4002c060d0a16800580c18142d000b01030284000140002000800026c08c0a168004d80181c2d0009b0030285a00134006850800026800c0a168004b2019142d000944036285a00128806450a00024900c0e16800490918142d000921038285a00124204050800024040e0a1680048011a1820000900234285a00120046830800024008c0a1680048001c142d
|24=>0x80100830285a10018004870342001800c0a16840020118142d080020032385a10000006050b42000000c0a148300800100000060000030285a0c000004000001800000002000280800100000050000030285a09020004000801200000c0a168240000001000040120030285a08020806050b41004000c0a16820000018142d030100010000006000006050b40a04000002100140800000400020101030285a04020006050b40800000c0a1680c000018142d018000000200002021006050b40404080c0a16808080018142d
|25=>0x4400100191c2948000023438524010c002450b48021040c8816900420019142d200840012381a40100006070b48004000c0a16900040019142d200001036285a40000006050b44000002c0a128401000181c2d
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0xc00028040240601003
|7,0=>0xa4000e0040008502c382140000051000380f81600000000380008602c3600000000414c000000380100007c161740b11125058120003f02c000000002c00000003d00701057000000580b15cff000570000b0e0335d40002c8800000190060002f0005d0005715c040008519c570001615c000b0573ec5700000174ef
|8,0=>0x141ee07061004911c03859c002382115e20880577ac04611a415c000e1373c5a31281659d700101d2141902da5189d70580b5a2c60c80b0e1630006321489030480004e02d36001de058395980015c271602004c34875200000b2411f22614058162a1851c0c305c0015c070004206c9005c383f6fb0dc971c838674380045b2dc5e6381b0583802c040e0392140b0e29c314150580007400408001300002c00
|8,1=>0x1a5af175a122d6a039315903021c191ec3815c7f02c1205988001320000e312402e08b21c574896415c1615c0b665827a45702d8802c0b15c57149f215c04050253cc624f85702d3815c180040100490518b810c851d1ea175527b00e15c381340015c94000040121ebe0002148a000040e0002301a4c87150c000c06d00042250001c017058576c94502e41002505e80b058576318521c5d00000b145815d28
|8,2=>0x474000580b1600002c380c47902c3921c0415c0067c0061d3c0e0042401b059f34c8252241b0586251220006fa15c000105a2640f001e80a8427dde302c626497c15c570000006c3e058d36988f15c1500215000420580b43038640380e038188380499b6a1350020b0e8420141a4000167c0061c0b0c0002245a0e00b035690e0572ac061756e004160007a000fc1605702c570416748400059400302300073
|8,3=>0xd40065c6b06c8565589011934e8010001c0ecba7ec008500015d53092208805615e20151970e1ea4980206c5c00186000260000000017001e4002c76d05a03838058160008d108007cc007d9fb0c0000006269c16011152761f000004ac573d449214d60e1ac47838010570883882c570583b00038108014c41b001b101001000216345712dab2301b15c7602c0b0580b199686c1e515c2db18bb128000f83c
|8,4=>0x1214040580000000a707521439
|9,0=>0x8c160c6aa08c0d88c2a3c661336a119bef78c1ea30687645c36e93406ac22ee9e8866b524958de3d2471a8c243370406de5f70329165942d1648c08322947b385355acf8c05544b09261ae3e2d95daa13dd885466ec300e07a30a2951c916d6605c5acf2c44e6b71f36eec12507cc166e7ef1aabf275566cc4e70331b5870e08c2998b0fe53d74a94dc0596fbf29bc8468c5ce4039f9838e8645cdc12d84f4ae
|9,1=>0x38f1059c94302242e4e77758b376737a80b2aab0800fa3446843873b98e8207052501903291aaa2f4cea2b246fc02da2cecb561dfbf19fa996589e22342fc7115f294a105acf2609599128940c68296983d8856887bb54e9a5744a6fc895d10f09e541d94194a182568aca95509b3554279979c0f0442dad0422835e6b364118c09a4fc5b2b8dbc32d235dd1c35f85de2a3400c7170c7382e9e4ec1f9cb6d706
|9,2=>0x46d092f69a0a1b79671d83e302609a99895b5a705319a8c13f92cde8a49aab0ce2fc7d7c42b6a8b4c59bd520f07aced6fca74ee6e3e630c6ccebca17671015763070e19801a26e694a27252522475216848d78c1b904498c20ca781b53ea2bb23083241a67e2170e1aa2c0d75a4f6cde64be5271ce22121b156305fc982094b03c602462d76cc83d8902428827079bb6ff915da1957c2bed372161c8cc22be26
|9,3=>0x9da9a8c2dba6314ca9bcb45c98c149cb0d0aa09a55634730966e62bb35720f487aa4b4117118849fb5534c89bc32c0e020a31aa3e5671a17c8f0ed513c9c2c80d8c28948c2d0168b43c8474130516a3024a96b322267a5b30969bf238898e5926308c14905c9a4863056e26ab471376302c49a8c230260989563a064915f50f8362e1b2cac7aff9c0657419f0ed14b74803086faac775063f525031b8114618f
|9,4=>0xbf20caba2a9498a55cad8c1f38c227259b8b5db365af996e2ab814c256262684626a218845ec2e6a6deb736230282a48c27a7730cc67151694cb52702f14dc626341d3f2546cc71132421891e6e884788c23023c938e44f2532605ce99f8a62b1ca8872b52c176d8cd60267262236e0ee760de680cca9de78bd114e60033d87284b42429f1691ba74a15a42d9a08c3088d996302510d379f0c49838c230c35c6
|9,5=>0x270842668c26305e027e9fb788908c230505ba6a66d8b5e505eb4
|10,0=>0x98a5e8ce575fb28a1a30464a78ee3037651bc6035d277c3dff31ca2973069812a8ca449195cc1d6c6f928bce788170e2d0d07f24eb0d10ac636786805c68f7fa905d12cb8cc22689aaf0df3ab00350d25e2ec2c15e81d14aee958070d95dfcc7e3b2909a8c6834525d800b4bbb02c96b549e709f24a8c2f07d5e1b7d1233ac433a92a4e4331db626a704a4cdacdc12d0b0b86bd8c25aba12d9feba8cab846f0d
|10,1=>0x26a70b9d084723030ab99c1fc8ce812d9737b49a5ee832fabe97204b891b825059c4be5e0c28c2309f5d29d51a2d60098574c06c049e0095ef6bf5ba952e5a5e539c50a289fcbadfc5eebfa14e1605748c5fd2889aba95c339d52ca3b3ae848c0c78eefc33517a0ae97d12e8f181a3ab69ee4d9c12974def450d891a57334b03089f2d2f58c0e65897874e5a8027d5e0d0a312481a484a208bf1169ca42c6958
|10,2=>0xbf91473e3095d78452e49624c7f124
|11,0=>0x2302f89aa05747b6702d207bd1247f2ba7f2ef2c12433635b84b4289fc2fa309c1fc8c0c2b78b0452b22892e9d251a35232689a8c230289748c1fc31d24a5230
|12,0=>0x28b2fa702689aac2702c09a
|13,0=>0x9a
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 10 (j%128);fld (pmP (k/32)) 51 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_254 12 roots_254 ops++addP pm 1 dom_182 6 roots_182 ops++addP pm 2 dom_251 12 roots_251 ops++addP pm 3 dom_253 12 roots_253 ops++addP pm 4 dom_166 5 roots_166 ops++addP pm 5 dom_239 11 roots_239 ops++addP pm 6 dom_246 10 roots_246 ops++addP pm 7 dom_87 5 roots_87 ops++addP pm 8 dom_214 6 roots_214 ops++addP pm 9 dom_198 5 roots_198 ops++addP pm 10 dom_191 11 roots_191 ops++addP pm 11 dom_63 8 roots_63 ops++addP pm 12 dom_127 11 roots_127 ops++addP pm 13 dom_54 4 roots_54 ops++addP pm 14 dom_222 9 roots_222 ops++addP pm 15 dom_55 5 roots_55 ops++addP pm 16 dom_95 8 roots_95 ops++addP pm 17 dom_119 9 roots_119 ops++addP pm 18 dom_183 7 roots_183 ops++addP pm 19 dom_223 11 roots_223 ops++addP pm 20 dom_247 11 roots_247 ops++addP pm 21 dom_229 8 roots_229 ops++addP pm 22 dzo_93_2 6 roots_93 ops++addP pm 23 dom_31 5 roots_31 ops++addP pm 24 dom_167 6 roots_167 ops++addP pm 25 dzo_59_4 6 roots_59 ops++addP pm 26 dom_215 7 roots_215 ops++addP pm 27 dom_199 6 roots_199 ops++addP pm 28 dom_43 5 roots_43 ops++addP pm 29 dom_77 5 roots_77 ops++addP pm 30 dom_103 6 roots_103 ops++addP pm 31 dom_159 7 roots_159 ops++addP pm 32 dom_143 6 roots_143 ops++addP pm 33 dom_111 9 roots_111 ops++addP pm 34 dom_175 9 roots_175 ops++addP pm 35 dzo_239_16 10 roots_239 ops++addP pm 36 dom_231 9 roots_231 ops++addP pm 37 dzo_238_16 9 roots_238 ops++addP pm 38 dom_207 9 roots_207 ops++addP pm 39 dom_61 7 roots_61 ops++addP pm 40 dom_245 9 roots_245 ops++addP pm 41 dom_91 7 roots_91 ops++addP pm 42 dzo_111_16 7 roots_111 ops++addP pm 43 dzo_207_16 7 roots_207 ops++addP pm 44 dzo_175_16 7 roots_175 ops++addP pm 45 dzo_231_16 7 roots_231 ops++addP pm 46 dzo_235_16 9 roots_235 ops++addP pm 47 dom_181 6 roots_181 ops++addP pm 48 dzo_237_16 9 roots_237 ops++addP pm 49 dom_243 9 roots_243 ops++addP pm 50 dom_219 9 roots_219 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_255 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45|h46|h47|h48|h49|h50
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_166 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_198 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_191 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_127 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_223 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_247 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_229 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_zo_93_2_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_zo_59_4_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_143 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_175 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_zo_239_16_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_zo_238_16_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_207 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_zo_111_16_104 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_zo_207_16_200 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_zo_175_16_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h45;exact cpcs (by decide +kernel) lowS_zo_231_16_224 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h46;exact cpcs (by decide +kernel) lowS_zo_235_16_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h47;exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h48;exact cpcs (by decide +kernel) lowS_zo_237_16_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h49;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h50;exact cpcs (by decide +kernel) lowS_219 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_254 12 s (0,roots_254.map (·&&&dom_254)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_254 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_255==dom_255)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 1000003 zs symsG zs (hk 1000003 zs)
theorem ori_ok {v ys} (h:RunD true dom_255 gM v ys):RunD true dom_255 gM v (ori ys):=pickMin_runD 1000003 ys h symsG ys (hk 1000003 ys) symsG_ok h
def Z (s:Nat):=barP dom_255 gM mpG SD SS NN hAt idxH ori 1000003 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 9 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 103 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 103 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 256 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_256 : ∀ i, 256 ≤ i → i < 384 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 256 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_384 : ∀ i, 384 ≤ i → i < 512 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 384 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_512 : ∀ i, 512 ≤ i → i < 524 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 512 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 524 → Z 8 i = true := (range_split (range_split z8_0 z8_128) (range_split z8_256 (range_split z8_384 z8_512)))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_0 : ∀ i, 0 ≤ i → i < 128 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_128 : ∀ i, 128 ≤ i → i < 256 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_256 : ∀ i, 256 ≤ i → i < 384 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 256 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_384 : ∀ i, 384 ≤ i → i < 512 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 384 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_512 : ∀ i, 512 ≤ i → i < 640 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 512 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_640 : ∀ i, 640 ≤ i → i < 661 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 21 640 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 661 → Z 9 i = true := (range_split (range_split z9_0 (range_split z9_128 z9_256)) (range_split z9_384 (range_split z9_512 z9_640)))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_0 : ∀ i, 0 ≤ i → i < 128 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_128 : ∀ i, 128 ≤ i → i < 256 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_256 : ∀ i, 256 ≤ i → i < 268 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 12 256 = true)
private theorem z10 : ∀ i, 0 ≤ i → i < 268 → Z 10 i = true := (range_split z10_0 (range_split z10_128 z10_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 51 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 51 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z12 : ∀ i, 0 ≤ i → i < 9 → Z 12 i = true := span_ok (by decide +kernel : span (Z 12) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z13 : ∀ i, 0 ≤ i → i < 1 → Z 13 i = true := span_ok (by decide +kernel : span (Z 13) 1 0 = true)
theorem checked (s:Nat) (hs:s≤13):∀ i<NN s,bar dom_255 gM mpG SD SS NN hAt idxH ori 1000003 mkCut s i=true:=by
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
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [2, 0] }, { op := GateOp.or, inputs := [8, 7] }, { op := GateOp.or, inputs := [3, 1] }, { op := GateOp.or, inputs := [7, 6] }, { op := GateOp.or, inputs := [0, 11] }, { op := GateOp.or, inputs := [1, 8] }, { op := GateOp.or, inputs := [7, 4] }, { op := GateOp.or, inputs := [3, 5] }, { op := GateOp.and, inputs := [12, 15] }, { op := GateOp.and, inputs := [13, 14] }, { op := GateOp.and, inputs := [5, 10] }, { op := GateOp.and, inputs := [6, 9] }, { op := GateOp.or, inputs := [16, 17] }, { op := GateOp.or, inputs := [20, 18] }, { op := GateOp.or, inputs := [21, 19] }]

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 22⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
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

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_52446_aux

theorem PEqualNP.Outside.L_meta_52446 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_52446_aux.main
