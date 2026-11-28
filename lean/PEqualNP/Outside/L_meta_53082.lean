import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_53082_aux
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
def dom_15 : Nat := 0xffff
def goal_15 : Nat := 0xeea0eea0eea0eea0eea0eea0eea0eea0eea0eea0eea0eea0eea0eea0eea0eea0
def roots_15 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0]

def dom_21 : Nat := 0x330033
def goal_21 : Nat := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0
def roots_21 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0]

def dom_23 : Nat := 0xff00ff
def goal_23 : Nat := 0xfefea0a0fefea0a0fefea0a0fefea0a0fefea0a0fefea0a0fefea0a0fefea0a0
def roots_23 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0]

def dom_29 : Nat := 0x33333333
def goal_29 : Nat := 0xfafaaaa0fafaaaa0fafaaaa0fafaaaa0fafaaaa0fafaaaa0fafaaaa0fafaaaa0
def roots_29 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_30 : Nat := 0x55555555
def goal_30 : Nat := 0xfcfccc00fcfccc00fcfccc00fcfccc00fcfccc00fcfccc00fcfccc00fcfccc00
def roots_30 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_31 : Nat := 0xffffffff
def goal_31 : Nat := 0xfefeeea0fefeeea0fefeeea0fefeeea0fefeeea0fefeeea0fefeeea0fefeeea0
def roots_31 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_39 : Nat := 0xff000000ff
def goal_39 : Nat := 0xfefefefea0a0a0a0fefefefea0a0a0a0fefefefea0a0a0a0fefefefea0a0a0a0
def roots_39 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0]

def dom_42 : Nat := 0x50500000505
def goal_42 : Nat := 0xffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00
def roots_42 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_43 : Nat := 0xf0f00000f0f
def goal_43 : Nat := 0xffeeffeeee00ee00ffeeffeeee00ee00ffeeffeeee00ee00ffeeffeeee00ee00
def roots_43 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_45 : Nat := 0x333300003333
def goal_45 : Nat := 0xfffafffaaaa0aaa0fffafffaaaa0aaa0fffafffaaaa0aaa0fffafffaaaa0aaa0
def roots_45 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_46 : Nat := 0x555500005555
def goal_46 : Nat := 0xfffcfffccc00cc00fffcfffccc00cc00fffcfffccc00cc00fffcfffccc00cc00
def roots_46 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_47 : Nat := 0xffff0000ffff
def goal_47 : Nat := 0xfffefffeeea0eea0fffefffeeea0eea0fffefffeeea0eea0fffefffeeea0eea0
def roots_47 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_53 : Nat := 0x33003300330033
def goal_53 : Nat := 0xfafafafafafaa0a0fafafafafafaa0a0fafafafafafaa0a0fafafafafafaa0a0
def roots_53 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xfefefefefefea0a0fefefefefefea0a0fefefefefefea0a0fefefefefefea0a0
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_57 : Nat := 0x303030303030303
def goal_57 : Nat := 0xffaaffaaaaaaaa00ffaaffaaaaaaaa00ffaaffaaaaaaaa00ffaaffaaaaaaaa00
def roots_57 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_58 : Nat := 0x505050505050505
def goal_58 : Nat := 0xffccffcccccccc00ffccffcccccccc00ffccffcccccccc00ffccffcccccccc00
def roots_58 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xffeeffeeeeeeee00ffeeffeeeeeeee00ffeeffeeeeeeee00ffeeffeeeeeeee00
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_60 : Nat := 0x1111111111111111
def goal_60 : Nat := 0xfff0fff0f0f00000fff0fff0f0f00000fff0fff0f0f00000fff0fff0f0f00000
def roots_60 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xfffafffafafaaaa0fffafffafafaaaa0fffafffafafaaaa0fffafffafafaaaa0
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_62 : Nat := 0x5555555555555555
def goal_62 : Nat := 0xfffcfffcfcfccc00fffcfffcfcfccc00fffcfffcfcfccc00fffcfffcfcfccc00
def roots_62 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfffefffefefeeea0fffefffefefeeea0fffefffefefeeea0fffefffefefeeea0
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_69 : Nat := 0x330000000000000033
def goal_69 : Nat := 0xfafafafafafafafaa0a0a0a0a0a0a0a0fafafafafafafafaa0a0a0a0a0a0a0a0
def roots_69 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 6 0]

def dom_71 : Nat := 0xff00000000000000ff
def goal_71 : Nat := 0xfefefefefefefefea0a0a0a0a0a0a0a0fefefefefefefefea0a0a0a0a0a0a0a0
def roots_71 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0]

def dom_74 : Nat := 0x5050000000000000505
def goal_74 : Nat := 0xffccffccffccffcccc00cc00cc00cc00ffccffccffccffcccc00cc00cc00cc00
def roots_74 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_75 : Nat := 0xf0f0000000000000f0f
def goal_75 : Nat := 0xffeeffeeffeeffeeee00ee00ee00ee00ffeeffeeffeeffeeee00ee00ee00ee00
def roots_75 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_77 : Nat := 0x33330000000000003333
def goal_77 : Nat := 0xfffafffafffafffaaaa0aaa0aaa0aaa0fffafffafffafffaaaa0aaa0aaa0aaa0
def roots_77 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_78 : Nat := 0x55550000000000005555
def goal_78 : Nat := 0xfffcfffcfffcfffccc00cc00cc00cc00fffcfffcfffcfffccc00cc00cc00cc00
def roots_78 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_79 : Nat := 0xffff000000000000ffff
def goal_79 : Nat := 0xfffefffefffefffeeea0eea0eea0eea0fffefffefffefffeeea0eea0eea0eea0
def roots_79 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_81 : Nat := 0x300030000000000030003
def goal_81 : Nat := 0xffffaaaaffffaaaaaaaa0000aaaa0000ffffaaaaffffaaaaaaaa0000aaaa0000
def roots_81 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_82 : Nat := 0x500050000000000050005
def goal_82 : Nat := 0xffffccccffffcccccccc0000cccc0000ffffccccffffcccccccc0000cccc0000
def roots_82 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_83 : Nat := 0xf000f00000000000f000f
def goal_83 : Nat := 0xffffeeeeffffeeeeeeee0000eeee0000ffffeeeeffffeeeeeeee0000eeee0000
def roots_83 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_84 : Nat := 0x1100110000000000110011
def goal_84 : Nat := 0xfffff0f0fffff0f0f0f00000f0f00000fffff0f0fffff0f0f0f00000f0f00000
def roots_84 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_85 : Nat := 0x3300330000000000330033
def goal_85 : Nat := 0xfffffafafffffafafafaa0a0fafaa0a0fffffafafffffafafafaa0a0fafaa0a0
def roots_85 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_86 : Nat := 0x5500550000000000550055
def goal_86 : Nat := 0xfffffcfcfffffcfcfcfc0000fcfc0000fffffcfcfffffcfcfcfc0000fcfc0000
def roots_86 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_87 : Nat := 0xff00ff0000000000ff00ff
def goal_87 : Nat := 0xfffffefefffffefefefea0a0fefea0a0fffffefefffffefefefea0a0fefea0a0
def roots_87 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_89 : Nat := 0x30303030000000003030303
def goal_89 : Nat := 0xffffffaaffffffaaaaaaaa00aaaaaa00ffffffaaffffffaaaaaaaa00aaaaaa00
def roots_89 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_90 : Nat := 0x50505050000000005050505
def goal_90 : Nat := 0xffffffccffffffcccccccc00cccccc00ffffffccffffffcccccccc00cccccc00
def roots_90 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f
def goal_91 : Nat := 0xffffffeeffffffeeeeeeee00eeeeee00ffffffeeffffffeeeeeeee00eeeeee00
def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_92 : Nat := 0x111111110000000011111111
def goal_92 : Nat := 0xfffffff0fffffff0f0f00000f0f00000fffffff0fffffff0f0f00000f0f00000
def roots_92 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_93 : Nat := 0x333333330000000033333333
def goal_93 : Nat := 0xfffffffafffffffafafaaaa0fafaaaa0fffffffafffffffafafaaaa0fafaaaa0
def roots_93 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_94 : Nat := 0x555555550000000055555555
def goal_94 : Nat := 0xfffffffcfffffffcfcfccc00fcfccc00fffffffcfffffffcfcfccc00fcfccc00
def roots_94 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_95 : Nat := 0xffffffff00000000ffffffff
def goal_95 : Nat := 0xfffffffefffffffefefeeea0fefeeea0fffffffefffffffefefeeea0fefeeea0
def roots_95 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_106 : Nat := 0x505000005050000050500000505
def goal_106 : Nat := 0xffccffccffccffccffccffcccc00cc00ffccffccffccffccffccffcccc00cc00
def roots_106 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffeeffeeffeeffeeffeeffeeee00ee00ffeeffeeffeeffeeffeeffeeee00ee00
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_110 : Nat := 0x5555000055550000555500005555
def goal_110 : Nat := 0xfffcfffcfffcfffcfffcfffccc00cc00fffcfffcfffcfffcfffcfffccc00cc00
def roots_110 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xfffefffefffefffefffefffeeea0eea0fffefffefffefffefffefffeeea0eea0
def roots_111 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_117 : Nat := 0x330033003300330033003300330033
def goal_117 : Nat := 0xfffffafafffffafafafafafafafaa0a0fffffafafffffafafafafafafafaa0a0
def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xfffffcfcfffffcfcfcfcfcfcfcfc0000fffffcfcfffffcfcfcfcfcfcfcfc0000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xfffffefefffffefefefefefefefea0a0fffffefefffffefefefefefefefea0a0
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_120 : Nat := 0x1010101010101010101010101010101
def goal_120 : Nat := 0xffffff00ffffff00ff00ff0000000000ffffff00ffffff00ff00ff0000000000
def roots_120 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_121 : Nat := 0x3030303030303030303030303030303
def goal_121 : Nat := 0xffffffaaffffffaaffaaffaaaaaaaa00ffffffaaffffffaaffaaffaaaaaaaa00
def roots_121 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_122 : Nat := 0x5050505050505050505050505050505
def goal_122 : Nat := 0xffffffccffffffccffccffcccccccc00ffffffccffffffccffccffcccccccc00
def roots_122 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffffffeeffffffeeffeeffeeeeeeee00ffffffeeffffffeeffeeffeeeeeeee00
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_124 : Nat := 0x11111111111111111111111111111111
def goal_124 : Nat := 0xfffffff0fffffff0fff0fff0f0f00000fffffff0fffffff0fff0fff0f0f00000
def roots_124 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xfffffffafffffffafffafffafafaaaa0fffffffafffffffafffafffafafaaaa0
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_126 : Nat := 0x55555555555555555555555555555555
def goal_126 : Nat := 0xfffffffcfffffffcfffcfffcfcfccc00fffffffcfffffffcfffcfffcfcfccc00
def roots_126 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xfffffffefffffffefffefffefefeeea0fffffffefffffffefffefffefefeeea0
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_135 : Nat := 0xff000000000000000000000000000000ff
def goal_135 : Nat := 0xfefefefefefefefefefefefefefefefea0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0
def roots_135 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 7 0]

def dom_139 : Nat := 0xf0f00000000000000000000000000000f0f
def goal_139 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffeeee00ee00ee00ee00ee00ee00ee00ee00
def roots_139 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_142 : Nat := 0x555500000000000000000000000000005555
def goal_142 : Nat := 0xfffcfffcfffcfffcfffcfffcfffcfffccc00cc00cc00cc00cc00cc00cc00cc00
def roots_142 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_143 : Nat := 0xffff0000000000000000000000000000ffff
def goal_143 : Nat := 0xfffefffefffefffefffefffefffefffeeea0eea0eea0eea0eea0eea0eea0eea0
def roots_143 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_146 : Nat := 0x5000500000000000000000000000000050005
def goal_146 : Nat := 0xffffccccffffccccffffccccffffcccccccc0000cccc0000cccc0000cccc0000
def roots_146 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_147 : Nat := 0xf000f000000000000000000000000000f000f
def goal_147 : Nat := 0xffffeeeeffffeeeeffffeeeeffffeeeeeeee0000eeee0000eeee0000eeee0000
def roots_147 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_149 : Nat := 0x33003300000000000000000000000000330033
def goal_149 : Nat := 0xfffffafafffffafafffffafafffffafafafaa0a0fafaa0a0fafaa0a0fafaa0a0
def roots_149 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_150 : Nat := 0x55005500000000000000000000000000550055
def goal_150 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfcfcfc0000fcfc0000fcfc0000fcfc0000
def roots_150 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_151 : Nat := 0xff00ff00000000000000000000000000ff00ff
def goal_151 : Nat := 0xfffffefefffffefefffffefefffffefefefea0a0fefea0a0fefea0a0fefea0a0
def roots_151 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_153 : Nat := 0x303030300000000000000000000000003030303
def goal_153 : Nat := 0xffffffaaffffffaaffffffaaffffffaaaaaaaa00aaaaaa00aaaaaa00aaaaaa00
def roots_153 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def goal_155 : Nat := 0xffffffeeffffffeeffffffeeffffffeeeeeeee00eeeeee00eeeeee00eeeeee00
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_156 : Nat := 0x1111111100000000000000000000000011111111
def goal_156 : Nat := 0xfffffff0fffffff0fffffff0fffffff0f0f00000f0f00000f0f00000f0f00000
def roots_156 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_158 : Nat := 0x5555555500000000000000000000000055555555
def goal_158 : Nat := 0xfffffffcfffffffcfffffffcfffffffcfcfccc00fcfccc00fcfccc00fcfccc00
def roots_158 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_159 : Nat := 0xffffffff000000000000000000000000ffffffff
def goal_159 : Nat := 0xfffffffefffffffefffffffefffffffefefeeea0fefeeea0fefeeea0fefeeea0
def roots_159 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_170 : Nat := 0x5050000050500000000000000000000050500000505
def goal_170 : Nat := 0xffccffccffccffccffccffccffccffccffccffcccc00cc00ffccffcccc00cc00
def roots_170 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_171 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
def goal_171 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeee00ee00ffeeffeeee00ee00
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_174 : Nat := 0x55550000555500000000000000000000555500005555
def goal_174 : Nat := 0xfffcfffcfffcfffcfffcfffcfffcfffcfffcfffccc00cc00fffcfffccc00cc00
def roots_174 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_175 : Nat := 0xffff0000ffff00000000000000000000ffff0000ffff
def goal_175 : Nat := 0xfffefffefffefffefffefffefffefffefffefffeeea0eea0fffefffeeea0eea0
def roots_175 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_182 : Nat := 0x5500550055005500000000000000000055005500550055
def goal_182 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfcfcfcfcfcfcfc0000fcfcfcfcfcfc0000
def roots_182 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_184 : Nat := 0x10101010101010100000000000000000101010101010101
def goal_184 : Nat := 0xffffff00ffffff00ffffff00ffffff00ff00ff0000000000ff00ff0000000000
def roots_184 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_185 : Nat := 0x30303030303030300000000000000000303030303030303
def goal_185 : Nat := 0xffffffaaffffffaaffffffaaffffffaaffaaffaaaaaaaa00ffaaffaaaaaaaa00
def roots_185 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_186 : Nat := 0x50505050505050500000000000000000505050505050505
def goal_186 : Nat := 0xffffffccffffffccffffffccffffffccffccffcccccccc00ffccffcccccccc00
def roots_186 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffeeffffffeeffffffeeffffffeeffeeffeeeeeeee00ffeeffeeeeeeee00
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_188 : Nat := 0x111111111111111100000000000000001111111111111111
def goal_188 : Nat := 0xfffffff0fffffff0fffffff0fffffff0fff0fff0f0f00000fff0fff0f0f00000
def roots_188 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_190 : Nat := 0x555555555555555500000000000000005555555555555555
def goal_190 : Nat := 0xfffffffcfffffffcfffffffcfffffffcfffcfffcfcfccc00fffcfffcfcfccc00
def roots_190 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xfffffffefffffffefffffffefffffffefffefffefefeeea0fffefffefefeeea0
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_195 : Nat := 0xf000000000000000f000000000000000f000000000000000f
def goal_195 : Nat := 0xffffffffffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0000000000000000
def roots_195 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_197 : Nat := 0x33000000000000003300000000000000330000000000000033
def goal_197 : Nat := 0xfffffffffffffffffafafafafafafafafafafafafafafafaa0a0a0a0a0a0a0a0
def roots_197 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_198 : Nat := 0x55000000000000005500000000000000550000000000000055
def goal_198 : Nat := 0xfffffffffffffffffcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc0000000000000000
def roots_198 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_199 : Nat := 0xff00000000000000ff00000000000000ff00000000000000ff
def goal_199 : Nat := 0xfffffffffffffffffefefefefefefefefefefefefefefefea0a0a0a0a0a0a0a0
def roots_199 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_202 : Nat := 0x505000000000000050500000000000005050000000000000505
def goal_202 : Nat := 0xffffffffffffffffffccffccffccffccffccffccffccffcccc00cc00cc00cc00
def roots_202 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffffffffffffffffffeeffeeffeeffeeffeeffeeffeeffeeee00ee00ee00ee00
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_205 : Nat := 0x3333000000000000333300000000000033330000000000003333
def goal_205 : Nat := 0xfffffffffffffffffffafffafffafffafffafffafffafffaaaa0aaa0aaa0aaa0
def roots_205 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_206 : Nat := 0x5555000000000000555500000000000055550000000000005555
def goal_206 : Nat := 0xfffffffffffffffffffcfffcfffcfffcfffcfffcfffcfffccc00cc00cc00cc00
def roots_206 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_207 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def goal_207 : Nat := 0xfffffffffffffffffffefffefffefffefffefffefffefffeeea0eea0eea0eea0
def roots_207 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_208 : Nat := 0x10001000000000001000100000000000100010000000000010001
def goal_208 : Nat := 0xffffffffffffffffffff0000ffff0000ffff0000ffff00000000000000000000
def roots_208 : List Nat := [xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_209 : Nat := 0x30003000000000003000300000000000300030000000000030003
def goal_209 : Nat := 0xffffffffffffffffffffaaaaffffaaaaffffaaaaffffaaaaaaaa0000aaaa0000
def roots_209 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_210 : Nat := 0x50005000000000005000500000000000500050000000000050005
def goal_210 : Nat := 0xffffffffffffffffffffccccffffccccffffccccffffcccccccc0000cccc0000
def roots_210 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffffffffffffffffffeeeeffffeeeeffffeeeeffffeeeeeeee0000eeee0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_212 : Nat := 0x110011000000000011001100000000001100110000000000110011
def goal_212 : Nat := 0xfffffffffffffffffffff0f0fffff0f0fffff0f0fffff0f0f0f00000f0f00000
def roots_212 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_213 : Nat := 0x330033000000000033003300000000003300330000000000330033
def goal_213 : Nat := 0xfffffffffffffffffffffafafffffafafffffafafffffafafafaa0a0fafaa0a0
def roots_213 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xfffffffffffffffffffffcfcfffffcfcfffffcfcfffffcfcfcfc0000fcfc0000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xfffffffffffffffffffffefefffffefefffffefefffffefefefea0a0fefea0a0
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_216 : Nat := 0x1010101000000000101010100000000010101010000000001010101
def goal_216 : Nat := 0xffffffffffffffffffffff00ffffff00ffffff00ffffff000000000000000000
def roots_216 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_217 : Nat := 0x3030303000000000303030300000000030303030000000003030303
def goal_217 : Nat := 0xffffffffffffffffffffffaaffffffaaffffffaaffffffaaaaaaaa00aaaaaa00
def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def goal_218 : Nat := 0xffffffffffffffffffffffccffffffccffffffccffffffcccccccc00cccccc00
def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffffffffffffffffffffeeffffffeeffffffeeffffffeeeeeeee00eeeeee00
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_220 : Nat := 0x11111111000000001111111100000000111111110000000011111111
def goal_220 : Nat := 0xfffffffffffffffffffffff0fffffff0fffffff0fffffff0f0f00000f0f00000
def roots_220 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def goal_221 : Nat := 0xfffffffffffffffffffffffafffffffafffffffafffffffafafaaaa0fafaaaa0
def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xfffffffffffffffffffffffcfffffffcfffffffcfffffffcfcfccc00fcfccc00
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffffffffffffffffffefffffffefffffffefffffffefefeeea0fefeeea0
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def goal_230 : Nat := 0xfffffffffffffffffcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc00000000
def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_232 : Nat := 0x10100000101000001010000010100000101000001010000010100000101
def goal_232 : Nat := 0xffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000
def roots_232 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffffffffffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffffffffffccffccffccffccffccffccffccffccffccffcccc00cc00
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffffffffffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeee00ee00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_236 : Nat := 0x111100001111000011110000111100001111000011110000111100001111
def goal_236 : Nat := 0xfffffffffffffffffff0fff0fff0fff0fff0fff0fff0fff0fff0fff000000000
def roots_236 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_238 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def goal_238 : Nat := 0xfffffffffffffffffffcfffcfffcfffcfffcfffcfffcfffcfffcfffccc00cc00
def roots_238 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffffffffffefffefffefffefffefffefffefffefffefffeeea0eea0
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_241 : Nat := 0x3000300030003000300030003000300030003000300030003000300030003
def goal_241 : Nat := 0xffffffffffffffffffffaaaaffffaaaaffffaaaaffffaaaaaaaaaaaaaaaa0000
def roots_241 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def goal_242 : Nat := 0xffffffffffffffffffffccccffffccccffffccccffffcccccccccccccccc0000
def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffffffffffffeeeeffffeeeeffffeeeeffffeeeeeeeeeeeeeeee0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_244 : Nat := 0x11001100110011001100110011001100110011001100110011001100110011
def goal_244 : Nat := 0xfffffffffffffffffffff0f0fffff0f0fffff0f0fffff0f0f0f0f0f0f0f00000
def roots_244 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffffffffffffffcfcfffffcfcfffffcfcfffffcfcfcfcfcfcfcfc0000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffffffffffefefffffefefffffefefffffefefefefefefefea0a0
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_248 : Nat := 0x101010101010101010101010101010101010101010101010101010101010101
def goal_248 : Nat := 0xffffffffffffffffffffff00ffffff00ffffff00ffffff00ff00ff0000000000
def roots_248 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffffffffffaaffffffaaffffffaaffffffaaffaaffaaaaaaaa00
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffffffffffccffffffccffffffccffffffccffccffcccccccc00
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffffffffffeeffffffeeffffffeeffffffeeffeeffeeeeeeee00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_252 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
def goal_252 : Nat := 0xfffffffffffffffffffffff0fffffff0fffffff0fffffff0fff0fff0f0f00000
def roots_252 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffffffffffafffffffafffffffafffffffafffafffafafaaaa0
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffffffffffcfffffffcfffffffcfffffffcfffcfffcfcfccc00
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffffffffffefffffffefffffffefffffffefffefffefefeeea0
def roots_255 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

namespace S_21
def pG:List (Nat×Nat):=[(1,5),(1,17),(4,5),(4,20),(16,17),(16,20)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3f
def xsM:=roots_21.map (·&&&dom_21)
def gM:=goal_21&&&dom_21
def NN:Nat→Nat
|2=>1
|3=>1
|_=>0
def HT:Nat→Nat→Nat
|2,0=>0xd83d3
|3,0=>0xd83d3
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x330000c000c220022
|_,_=>0
def sP:Nat→Nat
|0=>0x924
|_=>0
def sO:Nat→Nat→Nat
|2,0=>3
|3,0=>0x33
|_,_=>0
def wAt:=mkWire dB 3 22 0x3fffff
def SS:=mkSS wAt sP sO 2 7
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def mkPools (_ _:Nat):List (Nat×Nat×(Nat×List Nat)):=[]
def mkCut (_ _:Nat) (_:Nat×Nat×Nat) (_:List Nat):Bool:=false
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_21 gM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_21 gM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat×Nat)):=[[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_21==dom_21)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_21 gM v ys):RunD true dom_21 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_21 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s:Nat) (hs:s≤3):∀ i<NN s,bar dom_21 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 2 2=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤3) (h:RunD true dom_21 gM s xsM):False:=by
  have hmin:2≤s:=by have hl:=run_len h;change 3≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_21 roots_21 goal_21 4:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_21
theorem lowS_21:Lower true dom_21 roots_21 goal_21 4:=S_21.noCircuit
def isoMvS_42:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_42:Lower true dom_42 roots_42 goal_42 4:=lower_iso_b isoMvS_42 (by decide +kernel) lowS_21
def isoMvS_69:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_69:Lower true dom_69 roots_69 goal_69 4:=lower_iso_b isoMvS_69 (by decide +kernel) lowS_21
def isoMvS_74:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_74:Lower true dom_74 roots_74 goal_74 4:=lower_iso_b isoMvS_74 (by decide +kernel) lowS_21
def isoMvS_81:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_81:Lower true dom_81 roots_81 goal_81 4:=lower_iso_b isoMvS_81 (by decide +kernel) lowS_21
def isoMvS_82:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_82:Lower true dom_82 roots_82 goal_82 4:=lower_iso_b isoMvS_82 (by decide +kernel) lowS_21
def isoMvS_84:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_84:Lower true dom_84 roots_84 goal_84 4:=lower_iso_b isoMvS_84 (by decide +kernel) lowS_21
def isoMvS_146:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_146:Lower true dom_146 roots_146 goal_146 4:=lower_iso_b isoMvS_146 (by decide +kernel) lowS_21
def isoMvS_208:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_208:Lower true dom_208 roots_208 goal_208 4:=lower_iso_b isoMvS_208 (by decide +kernel) lowS_21
namespace S_15
def pG:List (Nat×Nat):=[(1,5),(1,9),(2,10),(3,7),(3,11),(4,5),(6,7),(6,14),(8,9),(8,10),(12,13),(12,14)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfff
def xsM:=roots_15.map (·&&&dom_15)
def gM:=goal_15&&&dom_15
def NN:Nat→Nat
|3=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x3d209
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xff00f0f0ccccaaaa
|_,_=>0
def sP:Nat→Nat
|0=>0xe4
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|_,_=>0
def wAt:=mkWire dB 4 16 0xffff
def SS:=mkSS wAt sP sO 2 7
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def mkPools (_ _:Nat):List (Nat×Nat×(Nat×List Nat)):=[]
def mkCut (_ _:Nat) (_:Nat×Nat×Nat) (_:List Nat):Bool:=false
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_15 gM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_15 gM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat×Nat)):=[[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_15==dom_15)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_15 gM v ys):RunD true dom_15 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_15 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s:Nat) (hs:s≤3):∀ i<NN s,bar dom_15 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 1 3=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤3) (h:RunD true dom_15 gM s xsM):False:=by
  have hmin:3≤s:=by have hl:=run_len h;change 4≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_15 roots_15 goal_15 4:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_15
theorem lowS_15:Lower true dom_15 roots_15 goal_15 4:=S_15.noCircuit
theorem lowS_23:Lower true dom_23 roots_23 goal_23 5:=lower_slice_b [(0xcc00cc,16,18)] (by decide +kernel) lowS_21
theorem lowS_43:Lower true dom_43 roots_43 goal_43 5:=lower_slice_b [(0xa0a00000a0a,8,9)] (by decide +kernel) lowS_42
namespace S_85
def pG:List (Nat×Nat):=[(1,5),(1,17),(1,65),(4,5),(4,20),(4,68),(16,17),(16,20),(16,80),(64,65),(64,68),(64,80)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfff
def xsM:=roots_85.map (·&&&dom_85)
def gM:=goal_85&&&dom_85
def NN:Nat→Nat
|3=>3
|4=>8
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x5bd4055c85319d6
|4,0=>0x8bae8419fa1e5c817049120fd0d46506756036b3
|5,0=>0x5c79a2d7ad168b5
|6,0=>0x168b5
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x33003300000000003200324400440000000000440000000320000000000000032cc00880000000000cc00880003300000000000000300000000000000000c800c9100110000000000110010c000c00000000000c00083300000000000000330000c000c00000000000c000c3300330000000000000000cc00c00000000000cc00c3300330000000000330000cc00cc0000000000c000c2200220000000000220022
|_,_=>0
def sP:Nat→Nat
|0=>0x6504365042650465046e504650d4650c43b50436104650a42615069504658467043210
|_=>0
def sO:Nat→Nat→Nat
|3,0=>0x21022004
|4,0=>0x5eaa952aa0536a5948a8c5
|5,0=>0xf55c2b44
|6,0=>0x424
|_,_=>0
def wAt:=mkWire dB 15 86 0x3fffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x5659160595545595459164551
|_=>0
def oO:Nat→Nat→Nat
|3,0=>2
|4,0=>0x6242002200
|5,0=>0x918100
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0xfc7630
|_=>0
def pmB:Nat→Nat→Nat
|3,0=>2
|4,0=>0x1810
|5,0=>0x16b
|6,0=>5
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 4 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_84 4 roots_84 ops++addP pm 1 dom_81 4 roots_81 ops++addP pm 2 dom_69 4 roots_69 ops++addP pm 3 dom_21 4 roots_21 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_85 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_69 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_21 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_84 4 s (0,roots_84.map (·&&&dom_84)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_85 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_84 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60)],[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_85==dom_85)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_85 gM v ys):RunD true dom_85 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_85 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 3 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 8 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_85 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_85 gM s xsM):False:=by
  have hmin:3≤s:=by have hl:=run_len h;change 4≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_85 roots_85 goal_85 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_85
theorem lowS_85:Lower true dom_85 roots_85 goal_85 7:=S_85.noCircuit
def isoMvS_29:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_29:Lower true dom_29 roots_29 goal_29 5:=lower_iso_b isoMvS_29 (by decide +kernel) lowS_23
def isoMvS_30:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_30:Lower true dom_30 roots_30 goal_30 4:=lower_iso_b isoMvS_30 (by decide +kernel) lowS_15
def isoMvS_39:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_39:Lower true dom_39 roots_39 goal_39 5:=lower_iso_b isoMvS_39 (by decide +kernel) lowS_23
def isoMvS_45:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_45:Lower true dom_45 roots_45 goal_45 5:=lower_iso_b isoMvS_45 (by decide +kernel) lowS_43
def isoMvS_46:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_46:Lower true dom_46 roots_46 goal_46 5:=lower_iso_b isoMvS_46 (by decide +kernel) lowS_23
def isoMvS_53:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_53:Lower true dom_53 roots_53 goal_53 5:=lower_iso_b isoMvS_53 (by decide +kernel) lowS_43
def isoMvS_57:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_57:Lower true dom_57 roots_57 goal_57 5:=lower_iso_b isoMvS_57 (by decide +kernel) lowS_23
def isoMvS_58:List (Nat×Nat):=[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_58:Lower true dom_58 roots_58 goal_58 5:=lower_iso_b isoMvS_58 (by decide +kernel) lowS_23
def isoMvS_60:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_60:Lower true dom_60 roots_60 goal_60 4:=lower_iso_b isoMvS_60 (by decide +kernel) lowS_15
def isoMvS_71:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_71:Lower true dom_71 roots_71 goal_71 5:=lower_iso_b isoMvS_71 (by decide +kernel) lowS_23
def isoMvS_75:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_75:Lower true dom_75 roots_75 goal_75 5:=lower_iso_b isoMvS_75 (by decide +kernel) lowS_43
def isoMvS_77:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_77:Lower true dom_77 roots_77 goal_77 5:=lower_iso_b isoMvS_77 (by decide +kernel) lowS_43
def isoMvS_78:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_78:Lower true dom_78 roots_78 goal_78 5:=lower_iso_b isoMvS_78 (by decide +kernel) lowS_23
def isoMvS_83:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_83:Lower true dom_83 roots_83 goal_83 5:=lower_iso_b isoMvS_83 (by decide +kernel) lowS_43
def isoMvS_86:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_86:Lower true dom_86 roots_86 goal_86 5:=lower_iso_b isoMvS_86 (by decide +kernel) lowS_43
def isoMvS_89:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_89:Lower true dom_89 roots_89 goal_89 5:=lower_iso_b isoMvS_89 (by decide +kernel) lowS_43
def isoMvS_90:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_90:Lower true dom_90 roots_90 goal_90 5:=lower_iso_b isoMvS_90 (by decide +kernel) lowS_43
def isoMvS_92:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_92:Lower true dom_92 roots_92 goal_92 5:=lower_iso_b isoMvS_92 (by decide +kernel) lowS_23
def isoMvS_106:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_106:Lower true dom_106 roots_106 goal_106 5:=lower_iso_b isoMvS_106 (by decide +kernel) lowS_43
def isoMvS_120:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_120:Lower true dom_120 roots_120 goal_120 4:=lower_iso_b isoMvS_120 (by decide +kernel) lowS_15
def isoMvS_135:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_135:Lower true dom_135 roots_135 goal_135 5:=lower_iso_b isoMvS_135 (by decide +kernel) lowS_23
def isoMvS_139:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_139:Lower true dom_139 roots_139 goal_139 5:=lower_iso_b isoMvS_139 (by decide +kernel) lowS_43
def isoMvS_142:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_142:Lower true dom_142 roots_142 goal_142 5:=lower_iso_b isoMvS_142 (by decide +kernel) lowS_23
def isoMvS_147:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_147:Lower true dom_147 roots_147 goal_147 5:=lower_iso_b isoMvS_147 (by decide +kernel) lowS_43
def isoMvS_149:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_149:Lower true dom_149 roots_149 goal_149 7:=lower_iso_b isoMvS_149 (by decide +kernel) lowS_85
def isoMvS_150:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_150:Lower true dom_150 roots_150 goal_150 5:=lower_iso_b isoMvS_150 (by decide +kernel) lowS_43
def isoMvS_153:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_153:Lower true dom_153 roots_153 goal_153 5:=lower_iso_b isoMvS_153 (by decide +kernel) lowS_43
def isoMvS_156:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_156:Lower true dom_156 roots_156 goal_156 5:=lower_iso_b isoMvS_156 (by decide +kernel) lowS_23
def isoMvS_170:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_170:Lower true dom_170 roots_170 goal_170 5:=lower_iso_b isoMvS_170 (by decide +kernel) lowS_43
def isoMvS_184:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_184:Lower true dom_184 roots_184 goal_184 4:=lower_iso_b isoMvS_184 (by decide +kernel) lowS_15
def isoMvS_195:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_195:Lower true dom_195 roots_195 goal_195 5:=lower_iso_b isoMvS_195 (by decide +kernel) lowS_43
def isoMvS_197:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_197:Lower true dom_197 roots_197 goal_197 7:=lower_iso_b isoMvS_197 (by decide +kernel) lowS_85
def isoMvS_198:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_198:Lower true dom_198 roots_198 goal_198 5:=lower_iso_b isoMvS_198 (by decide +kernel) lowS_43
def isoMvS_202:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_202:Lower true dom_202 roots_202 goal_202 7:=lower_iso_b isoMvS_202 (by decide +kernel) lowS_85
def isoMvS_209:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_209:Lower true dom_209 roots_209 goal_209 7:=lower_iso_b isoMvS_209 (by decide +kernel) lowS_85
def isoMvS_210:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_210:Lower true dom_210 roots_210 goal_210 7:=lower_iso_b isoMvS_210 (by decide +kernel) lowS_85
def isoMvS_212:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_212:Lower true dom_212 roots_212 goal_212 7:=lower_iso_b isoMvS_212 (by decide +kernel) lowS_85
def isoMvS_216:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_216:Lower true dom_216 roots_216 goal_216 5:=lower_iso_b isoMvS_216 (by decide +kernel) lowS_43
def isoMvS_232:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_232:Lower true dom_232 roots_232 goal_232 5:=lower_iso_b isoMvS_232 (by decide +kernel) lowS_23
theorem lowS_31:Lower true dom_31 roots_31 goal_31 6:=lower_slice_b [(0xcccccccc,8,10)] (by decide +kernel) lowS_29
namespace S_47
def pG:List (Nat×Nat):=[(1,5),(1,9),(1,33),(2,10),(2,34),(3,7),(3,11),(3,35),(4,5),(4,36),(6,7),(6,14),(6,38),(8,9),(8,10),(8,40),(12,13),(12,14),(12,44),(32,33),(32,34),(32,36),(32,40)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffff
def xsM:=roots_47.map (·&&&dom_47)
def gM:=goal_47&&&dom_47
def NN:Nat→Nat
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0xa2a89
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffff00000000ff000000ff00f0f00000f0f0cccc0000ccccaaaa0000aaaa
|_,_=>0
def sP:Nat→Nat
|0=>0x4688
|_=>0
def sO:Nat→Nat→Nat
|6,0=>5
|_,_=>0
def wAt:=mkWire dB 5 48 0xffffffffffff
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
addP pm 0 dom_46 5 roots_46 ops++addP pm 1 dom_45 5 roots_45 ops++addP pm 2 dom_43 5 roots_43 ops++addP pm 3 dom_39 5 roots_39 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_47 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_46 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_39 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_46 5 s (0,roots_46.map (·&&&dom_46)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_47 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_46 h
def symsG:List (List (Nat×Nat)):=[[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_47==dom_47)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_47 gM v ys):RunD true dom_47 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_47 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_47 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_47 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_47 roots_47 goal_47 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_47
theorem lowS_47:Lower true dom_47 roots_47 goal_47 7:=S_47.noCircuit
theorem lowS_55:Lower true dom_55 roots_55 goal_55 6:=lower_slice_b [(0xcc00cc00cc00cc,16,18)] (by decide +kernel) lowS_53
theorem lowS_87:Lower true dom_87 roots_87 goal_87 8:=lower_slice_b [(0xcc00cc0000000000cc00cc,16,18)] (by decide +kernel) lowS_85
theorem lowS_91:Lower true dom_91 roots_91 goal_91 6:=lower_slice_b [(0xa0a0a0a000000000a0a0a0a,8,9)] (by decide +kernel) lowS_90
theorem lowS_203:Lower true dom_203 roots_203 goal_203 8:=lower_slice_b [(0xa0a0000000000000a0a0000000000000a0a0000000000000a0a,8,9)] (by decide +kernel) lowS_202
namespace S_213
def pG:List (Nat×Nat):=[(1,5),(1,17),(1,65),(1,129),(4,5),(4,20),(4,68),(4,132),(16,17),(16,20),(16,80),(16,144),(64,65),(64,68),(64,80),(64,192),(128,129),(128,132),(128,144),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffff
def xsM:=roots_213.map (·&&&dom_213)
def gM:=goal_213&&&dom_213
def NN:Nat→Nat
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|8,0=>0x724b8
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x330000000000000033000000000000003300000000000000330000c000c00000000000c000c00000000000c000c00000000000c000c220022000000000022002200000000002200220000000000220022cc00cc00000000000000000000000000cc00cc000000000000000330033000000000033003300000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x4688
|_=>0
def sO:Nat→Nat→Nat
|8,0=>5
|_,_=>0
def wAt:=mkWire dB 5 214 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffff
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
addP pm 0 dom_212 7 roots_212 ops++addP pm 1 dom_149 7 roots_149 ops++addP pm 2 dom_209 7 roots_209 ops++addP pm 3 dom_197 7 roots_197 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_213 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_212 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_149 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_209 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_197 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_212 7 s (0,roots_212.map (·&&&dom_212)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_213 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_212 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)],[(0xffff0000ffff0000ffff0000ffff0000,112)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60)],[(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124)],[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_213==dom_213)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_213 gM v ys):RunD true dom_213 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_213 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_213 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_213 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_213 roots_213 goal_213 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_213
theorem lowS_213:Lower true dom_213 roots_213 goal_213 9:=S_213.noCircuit
theorem lowS_241:Lower true dom_241 roots_241 goal_241 8:=lower_slice_b [(0x3000300000000000300030000000000030003000000000003000300000000,1,33)] (by decide +kernel) lowS_209
def dzo_216_32:=0x101010100000000010101010000000001010101000000000101010100000000
def gzo_216_32:=0x101010100000000010101000000000001010100000000000100010000000000
def gsh_216_32:=0x1010101000000000101010000000000010101000000000001000100
theorem lowS_zo_216_32_208:Lower true dzo_216_32 roots_216 gzo_216_32 5:=lower_iso_b (d1:=dom_216) (r1:=roots_216) (T1:=gsh_216_32) [(dom_216,32)] (by decide +kernel) (lower_slice_b (T:=gsh_216_32) [(0x1000100000000000100010000000000010001000000000001000100,0,8)] (by decide +kernel) lowS_208)
namespace S_248
def pG:List (Nat×Nat):=[(8,40),(8,72),(8,136),(16,80),(16,144),(24,56),(24,88),(24,152),(32,40),(48,56),(48,112),(48,176),(64,72),(64,80),(64,192),(96,104),(96,112),(96,224),(128,136),(128,144),(128,192),(160,168),(160,176),(160,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_248.map (·&&&dom_248)
def gM:=goal_248&&&dom_248
def NN:Nat→Nat
|4=>1
|5=>1
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x444be
|5,0=>0x5f926
|6,0=>0x47128
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x4040000040400000404000004040000040400000404000004040000040400020202020202020202020202020202020202020202020202000000000000000101010100000000010101010000000001010101000000000101010100000000800080008000800080008000800080008000800080008000800080008000804040404040404040000000000000000040404040404040400000000000000000002020000020200000202000002020000020200000202000000000000000101010101010101010101010101010100000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x99a133a84688
|_=>0
def sO:Nat→Nat→Nat
|4,0=>5
|5,0=>0x56
|6,0=>0xb5
|_,_=>0
def wAt:=mkWire dB 7 249 0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 9
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x41
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
addP pm 0 dom_232 5 roots_232 ops++addP pm 1 dom_184 4 roots_184 ops++addP pm 2 dzo_216_32 5 roots_216 ops++addP pm 3 dom_216 5 roots_216 ops++addP pm 4 dom_120 4 roots_120 ops++addP pm 5 dom_208 4 roots_208 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_248 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_184 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_216_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_216 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_120 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_208 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_232 5 s (0,roots_232.map (·&&&dom_232)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_248 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_232 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_248==dom_248)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_248 gM v ys):RunD true dom_248 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_248 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_248 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_248 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_248 roots_248 goal_248 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_248
theorem lowS_248:Lower true dom_248 roots_248 goal_248 7:=S_248.noCircuit
def isoMvS_59:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_59:Lower true dom_59 roots_59 goal_59 6:=lower_iso_b isoMvS_59 (by decide +kernel) lowS_55
def isoMvS_61:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_61:Lower true dom_61 roots_61 goal_61 7:=lower_iso_b isoMvS_61 (by decide +kernel) lowS_47
def isoMvS_62:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_62:Lower true dom_62 roots_62 goal_62 6:=lower_iso_b isoMvS_62 (by decide +kernel) lowS_31
def isoMvS_79:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_79:Lower true dom_79 roots_79 goal_79 7:=lower_iso_b isoMvS_79 (by decide +kernel) lowS_47
def isoMvS_93:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_93:Lower true dom_93 roots_93 goal_93 8:=lower_iso_b isoMvS_93 (by decide +kernel) lowS_87
def isoMvS_94:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_94:Lower true dom_94 roots_94 goal_94 7:=lower_iso_b isoMvS_94 (by decide +kernel) lowS_47
def isoMvS_107:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)]
theorem lowS_107:Lower true dom_107 roots_107 goal_107 6:=lower_iso_b isoMvS_107 (by decide +kernel) lowS_91
def isoMvS_110:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_110:Lower true dom_110 roots_110 goal_110 6:=lower_iso_b isoMvS_110 (by decide +kernel) lowS_55
def isoMvS_117:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_117:Lower true dom_117 roots_117 goal_117 8:=lower_iso_b isoMvS_117 (by decide +kernel) lowS_87
def isoMvS_118:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_118:Lower true dom_118 roots_118 goal_118 6:=lower_iso_b isoMvS_118 (by decide +kernel) lowS_55
def isoMvS_121:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_121:Lower true dom_121 roots_121 goal_121 7:=lower_iso_b isoMvS_121 (by decide +kernel) lowS_47
def isoMvS_122:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_122:Lower true dom_122 roots_122 goal_122 7:=lower_iso_b isoMvS_122 (by decide +kernel) lowS_47
def isoMvS_124:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_124:Lower true dom_124 roots_124 goal_124 6:=lower_iso_b isoMvS_124 (by decide +kernel) lowS_31
def isoMvS_143:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_143:Lower true dom_143 roots_143 goal_143 7:=lower_iso_b isoMvS_143 (by decide +kernel) lowS_47
def isoMvS_151:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_151:Lower true dom_151 roots_151 goal_151 8:=lower_iso_b isoMvS_151 (by decide +kernel) lowS_87
def isoMvS_155:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_155:Lower true dom_155 roots_155 goal_155 6:=lower_iso_b isoMvS_155 (by decide +kernel) lowS_91
def isoMvS_158:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_158:Lower true dom_158 roots_158 goal_158 7:=lower_iso_b isoMvS_158 (by decide +kernel) lowS_47
def isoMvS_171:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)]
theorem lowS_171:Lower true dom_171 roots_171 goal_171 6:=lower_iso_b isoMvS_171 (by decide +kernel) lowS_91
def isoMvS_174:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_174:Lower true dom_174 roots_174 goal_174 6:=lower_iso_b isoMvS_174 (by decide +kernel) lowS_55
def isoMvS_182:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_182:Lower true dom_182 roots_182 goal_182 6:=lower_iso_b isoMvS_182 (by decide +kernel) lowS_55
def isoMvS_185:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_185:Lower true dom_185 roots_185 goal_185 7:=lower_iso_b isoMvS_185 (by decide +kernel) lowS_47
def isoMvS_186:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_186:Lower true dom_186 roots_186 goal_186 7:=lower_iso_b isoMvS_186 (by decide +kernel) lowS_47
def isoMvS_188:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_188:Lower true dom_188 roots_188 goal_188 6:=lower_iso_b isoMvS_188 (by decide +kernel) lowS_31
def isoMvS_199:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_199:Lower true dom_199 roots_199 goal_199 8:=lower_iso_b isoMvS_199 (by decide +kernel) lowS_87
def isoMvS_205:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_205:Lower true dom_205 roots_205 goal_205 8:=lower_iso_b isoMvS_205 (by decide +kernel) lowS_203
def isoMvS_206:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_206:Lower true dom_206 roots_206 goal_206 8:=lower_iso_b isoMvS_206 (by decide +kernel) lowS_87
def isoMvS_211:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_211:Lower true dom_211 roots_211 goal_211 8:=lower_iso_b isoMvS_211 (by decide +kernel) lowS_203
def isoMvS_214:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_214:Lower true dom_214 roots_214 goal_214 8:=lower_iso_b isoMvS_214 (by decide +kernel) lowS_203
def isoMvS_217:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_217:Lower true dom_217 roots_217 goal_217 8:=lower_iso_b isoMvS_217 (by decide +kernel) lowS_203
def isoMvS_220:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_220:Lower true dom_220 roots_220 goal_220 8:=lower_iso_b isoMvS_220 (by decide +kernel) lowS_87
def isoMvS_230:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_230:Lower true dom_230 roots_230 goal_230 6:=lower_iso_b isoMvS_230 (by decide +kernel) lowS_55
def isoMvS_233:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_233:Lower true dom_233 roots_233 goal_233 8:=lower_iso_b isoMvS_233 (by decide +kernel) lowS_87
def isoMvS_234:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_234:Lower true dom_234 roots_234 goal_234 8:=lower_iso_b isoMvS_234 (by decide +kernel) lowS_87
def isoMvS_236:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_236:Lower true dom_236 roots_236 goal_236 6:=lower_iso_b isoMvS_236 (by decide +kernel) lowS_55
def isoMvS_242:List (Nat×Nat):=[(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_242:Lower true dom_242 roots_242 goal_242 8:=lower_iso_b isoMvS_242 (by decide +kernel) lowS_241
def isoMvS_244:List (Nat×Nat):=[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_244:Lower true dom_244 roots_244 goal_244 8:=lower_iso_b isoMvS_244 (by decide +kernel) lowS_241
namespace S_63
def pG:List (Nat×Nat):=[(1,5),(1,9),(1,17),(1,33),(2,10),(2,18),(2,34),(3,7),(3,11),(3,19),(3,35),(4,5),(4,20),(4,36),(6,7),(6,14),(6,22),(6,38),(8,9),(8,10),(8,40),(12,13),(12,14),(12,28),(12,44),(16,17),(16,18),(16,20),(24,25),(24,26),(24,28),(24,56),(32,33),(32,34),(32,36),(32,40),(48,49),(48,50),(48,52),(48,56)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_63.map (·&&&dom_63)
def gM:=goal_63&&&dom_63
def NN:Nat→Nat
|5=>3
|6=>5
|7=>4
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0xa725c4e21f4c8ee
|6,0=>0xc029aa84844d9a93ed612184e
|7,0=>0xb93537adc377e251fb9e
|8,0=>0xc6758
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xfff0fff0fff0fff0ffffffffeeeeeeeefffffffffffff0f0ffaaffaaffaaffaaffffffffaaaaaaaaccccccccccccccccaaaaaaaaaaaaaaaa0f0f0f0f0f0f0a0affff0000ffff0000ffffffffffffaaaaffffffffffff0000ffffffff00000000ff00ff00ff00ff00f0f0f0f0f0f0f0f0eeeeeeeeeeeeeeee
|_,_=>0
def sP:Nat→Nat
|0=>0x36219836b2198432198a36219836e2198d362108c43219843210836b2104a21984a210432987543210
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x31433006
|6,0=>0x2a746e758bb116
|7,0=>0x8aefd9c3b17
|8,0=>0x4c6
|_,_=>0
def wAt:=mkWire dB 15 64 0xffffffffffffffff
def SS:=mkSS wAt sP sO 4 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xa1634e1216616366163609984e16358d
|_=>0
def oO:Nat→Nat→Nat
|5,0=>1
|6,0=>0x8171523212
|7,0=>0xc1b1a191
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0xacdb000bf65bb11807ec00c000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>1
|6,0=>0x3d3a
|7,0=>0x964
|8,0=>4
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 13 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_61 7 roots_61 ops++addP pm 1 dom_58 5 roots_58 ops++addP pm 2 dom_46 5 roots_46 ops++addP pm 3 dom_62 6 roots_62 ops++addP pm 4 dom_23 5 roots_23 ops++addP pm 5 dom_31 6 roots_31 ops++addP pm 6 dom_15 4 roots_15 ops++addP pm 7 dom_55 6 roots_55 ops++addP pm 8 dom_47 7 roots_47 ops++addP pm 9 dom_29 5 roots_29 ops++addP pm 10 dom_59 6 roots_59 ops++addP pm 11 dom_43 5 roots_43 ops++addP pm 12 dom_60 4 roots_60 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_63 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_46 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_23 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_15 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_47 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_29 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_60 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_61 7 s (0,roots_61.map (·&&&dom_61)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_63 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_61 h
def symsG:List (List (Nat×Nat)):=[[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_63==dom_63)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_63 gM v ys):RunD true dom_63 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_63 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 5 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 4 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_63 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_63 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_63 roots_63 goal_63 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_63
theorem lowS_63:Lower true dom_63 roots_63 goal_63 9:=S_63.noCircuit
namespace S_95
def pG:List (Nat×Nat):=[(1,5),(1,9),(1,17),(1,65),(2,10),(2,18),(2,66),(3,7),(3,11),(3,19),(3,67),(4,5),(4,20),(4,68),(6,7),(6,14),(6,22),(6,70),(8,9),(8,10),(8,72),(12,13),(12,14),(12,28),(12,76),(16,17),(16,18),(16,20),(16,80),(24,25),(24,26),(24,28),(24,88),(64,65),(64,66),(64,68),(64,72),(64,80)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffff
def xsM:=roots_95.map (·&&&dom_95)
def gM:=goal_95&&&dom_95
def NN:Nat→Nat
|4=>21
|5=>61
|6=>70
|7=>45
|8=>10
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xee457d84c8d69eca2979840b37f9347e3287c6f47bec87b94d789c67237d6e3886b82860f9c3ab643652332c062d125120070629e
|5,0=>0xb677eb02cba998ba83dfa6a04a3aff9f7609f4e89ef0f97ad09670d947fc9407e93dcf92dc78efda86ea985d28826b4802977df517d1557c7136e7446d0276a6b96a36e6495461b2057098555bc5472751e5c4e93b4a6293ef593c022386423293231f2e29d65245ce234531ff191d70f1ccca1c1b71b66e198d818ab016d86165d5155431192e0d3840aaf206e9204042025d90234e00225
|6,0=>0xc6392c2b39c283ac1df5bfba0be064b8a6bb7212b3d66a9710a5969a34389d59d9c4209a8aa97578920d5904fe8fa8a893dc859df835fa8129f800b47f65e7f40c78f1a70e4b6df1466fdf609bb5c484596ed56b074d50a446be4461342a7e3960335e633306a2ef372ee9b2dab42d74f2d4eb29b3f274a02557a2307c225e72183e20b9c1e5b61e3301cf1115c0f15a82156811199710e6c0e8180ab6a08fac08b00077fd03698035330238501d90
|7,0=>0xe7ba9de0b1d703eca6a5c9172c6768ae0d7ab336a8bc1a80e3a10389b9f39650c901b587b7c8461f6e7186764163fbb60f44576644cf6e47df241a713fb473f9d53e7703a50d3583b316d62fd50268f0220e61a6c516fc31683c1662015fec10ca50f8150cb5b032dc02ee1018a70131f
|8,0=>0xa80e3827c27feef762dd71a7e4088a2a99626a1e25bbe02d40
|9,0=>0xc3264
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xff00ff0000000000ff00ff00ffffffff00000000f0f0f0f0fefefefe00000000aaaaaaaaffffaaaa00000000ffffaaaa000000ff00000000000000eeffffff0000000000ffffff000000ffff000000000000ffaaffffffff0000000000000000ffffffff00000000ffffff00ffff000000000000ffff0000fffffffc00000000ccccccccffffffff00000000ffff0000f0f0f0f000000000f0f0f0f0eeeeeeee00000000eeeeeeeeffffff0000000000eeeeee00aaaaaaaa00000000aaaaaaaa
|0,1=>0xffff00ff00000000ffff00000000000000000000ffffffaaffffffee00000000ccccccccffffffff00000000ffffaaaa0f0f0f0f000000000f0f0a0aeeeeeeee00000000eeeeee00ffffffee00000000ff00ff00fffffefe00000000f0f0f0f0fffffffa00000000f0f0f0f0ffffeeee00000000ffffeeeeffffbbbb00000000ffffaaaacccccccc00000000ccccccccfffffffa00000000aaaaaaaaffffeeee00000000aaaaaaaafffffefe00000000ffff0000ffffffff00000000aaaaaaaa
|0,2=>0xafafafaf00000000aeaeaeaebbbbbbbb00000000aaaaaaaa111111110000000000000000aaaabbbb00000000aaaaaaaafefefefe0000000000000000ffffffaa0000000000000000555555550000000054545454333333330000000033333300ffffffaa00000000ffffffaaffffffff00000000eeeeeeeeffffaaff00000000ffffaaaa0000000000000000fefefefe0f0f0f0f000000000f0f0f000000f0f0000000000000f0f00000000000000000ffffeeeeffff00ff00000000ffff00aa
|0,3=>0xffff000000000000eeeefefefefe00000000fefefefe00ff00ff0000000000ee00eeffff111100000000ffff000051515151000000005050505055555555000000005555444400ee00ff0000000000ee00ee111111110000000010101010bbbbbbbb00000000babababa00ff00ff0000000000ff00ee333333030000000033333300fffffff00000000000000000111111110000000011111100f1f1f1f100000000f0f0f0f05050505000000000505050500f0f0f0f000000000f0f0f0a
|0,4=>0xefefefef00000000eeeeeeeef0f0f0f00000000000000000fffff0f000000000ffff0000ffffeeee00000000000000000f0f0f0f0000000000000000fffff0f000000000fffff0f00000111100000000000000000000ffff00000000000000000000ffff000000000000f0f0bbbbbbbb00000000bbbbbbaaffff000f00000000ffff000000ff00ff0000000000fe00fefffffff000000000fffffff0ffffffff00000000ffffeeee555555550000000055555550111111110000000011110000
|0,5=>0xffff000000000000aaaa0000000f00000000000000000f0f0f0f00000000f0f0f0f0ffffffff00000000fafafafaffffffff00000000fefefefefafafafa00000000fafafafa555555550000000050505050aaaaffff00000000aaaaaaaa0f0f0f0f000000000e0e0e0effffffff0000000050505050555555550000000000000000000000ff0000000000000000f0f0f0ff00000000f0f0f0f0000000ff00000000000000f0ffff0f0f00000000ffff0000ffffffff00000000ffffffaa
|0,6=>0xffff0f0f00000000000000000000555500000000000000000f0f000000000000ffff00000000000000000000f0f0f0f0ffff555500000000ffff0000ffffffff00000000fffff0f0fcfcfcfc00000000ccccccccafafafaf00000000aaaaaaaa0f0f0f0f000000000a0a0a0affffffff000000000000f0f000000f0f0000000000000000f5f5f5f500000000f0f0f0f0ffffffee00000000ffffffeeffffff5500000000ffffff00
|_,_=>0
def sP:Nat→Nat
|0=>0x1e901822028a00468840a420c1001028303284c40a400c108147c182207850406085061c509870c0ce80147011b1028603342031906088041e601001410b9400282030a00b03020040a2a0c1080e181942610783044888f06088061e3810d180c10b1028182122038606140040608080
|1=>0x101c3032801a1c0c3c11b102830300cc4061ec8131102831400c04061e0c12f1028303340040a0c0c12e102860304216871430194201878304b04061e38100561c303280150a0c0ce80101878304a440a080d302002818050884271410182105820f069800a4a0ca001028e040608406
|2=>0x6088061e0c1121028303290442714101942028b034c0040a080ca005431e0f060840a0608040103078304fc4061e0c1105629003280040c0c0c13d1029e0304004061e0c13b101878304e840a3e0ca100078504065000606080391028214006c4061e0c137101818200d840a0c0c035
|3=>0x180c1080c3c182002260a080ca00972820f1c500061e0c100112430f06088481438194011c40a0c0e3001028203044040a0c5ca00103020f060968a0c0c2801028303284150a380c10814301a6042054506500080c0c100882218a0838a00141018200b454206080080c3c1821a20504
|4=>0x7a205510650008a02830328004270e18194002038a180ca00103020f065083c0c3c182002030f073c10010187830401f88941078e280040a2c0c1001028e03280040a065004710187be06088080c3c182622169c0c3c182202050406508009a3c71400187a406080080818794006c40a
|5=>0x10187db06080080c3c18200215861f68714b22030f060ac080c3df034c004061e0c12e10187830402b880c3c182ac205041c0ca00101030f060802d0e283032802a8a0c0d30200206041e0ca10102820e06500061e0c1008020506a60ca0010283032802908141019420004060698100
|6=>0x650859102860328004543818794006c4271418194202050e2801108c02830328004061e5001b102820304004061f74a00143019420203030401e880c3c182be2138a080ca001028303280045e0e2819400884061e381942164f0a0c0ca00101878eba500061f70182202030fb80ca59
|7=>0x101c50606500080c3c19401944061e0ca00c82030f0650008c6187e206500080c3c19420025861e0ca00be202061e38194002030f06080089018783040042d0c3df0304004061e0c110101878304c44611418182002030f7c381001028303040042d0e28303284001c0818783042030f
|8=>0x16440a180ca0011a430f06500089a3c19400205061c0ca0011a02061e0ca00112820f06500080c3c1e700202061e0ca00aa1878e06508000c3ee0328004061e38a006220506065080010702061e0ca0010187832998008141819400225ca0c3c71400206041e0ca0010187dc1c0ca00
|9=>0x181878328004040c3c194002030f06500089c18783d4500080c3c1940022a840c3c19420004061e0ca0011b4e061e0ca00101030f06508000c3c714013830f0650008d82830304004061e0ca00b22030f1c0ca00901878e06500084e28303280046b1e0ca0010187ea28025861e38194
|10=>0xc3c194002030f1c0ca00102830328004061e0ca00622030f0650008972830f0650008
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x6450bea16942aa8505096a119420a83c506ea0c9416a8285046a07940ca814501ea029402a8005
|5,0=>0x1cf6392c70d8deb1b76362c6b14d331a06334c6518c731886304c5f54bbb17162d6c5958afb15962a6c5358a3b1416276c4d5897b1296246c47588bb1116216c41587fb0f961e6c3b5873b0e161b6c355867b0c96186c2f585bb0b16156c29584fb0996126c235843b08160f6c1d5837b0696
|6,0=>0x6e8edb5db33b6066b2ed4d9a6b3485684ccf199b332f7650ec85d8d3b13761acc19d7fbaf875e2eba9d7232dd75aecb41d6532c37578ead5d573aa77542ca69d49ba8c750ae9f9d3c327174d4e98dd2eb256749ee921d20ba3b646ac8bd9143a217434e851907aa087402e7f14fab9ef63d2c789cee31d57
|6,1=>0x1cf3b977720ee25dc13b7b7
|7,0=>0x4d5899cf31de603cba6966f2b5a533c9f7930f245e45b48568fb11dda383c6a68c6f16e22a3c4e688ef101e1cbc327856f08e20e3c15781cf01ddffc3f877e2efa9df1bbdc77aaef39de343bf7770eec5dd5b3a56
|8,0=>0x28dbd156a1cf41de803cf979e4f3ade723cdd7
|9,0=>0x5226
|_,_=>0
def wAt:=mkWire dB 110 96 0xffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 15
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 8 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x7c23040d380f08010c0128011e192c200419280106220c3d0c2106210c2106190c22005100210c3a06211e190c3d0c214e201e190c3d0c211e19140d06214c190421280100214e207c20144200e1043a06210c21041c14211e191e190422280114211e1900214e200c3d00510c2104210c21280114222c23202b0c3d0c210422
|1=>0x42228011e191e190421280100210c010c2106210c3d0c210751142200210c3d0c214c3f042128010d2d06221e190e0114211e1914211e190c0114211e190c0100210c210cb50422052d062228014c1b042128010c0d06211e190419280100110c3d0c211e191c1b06210021042228010051002100210c3d0c210d3906200621
|2=>0x61b155500221e19380f08010c2100510c3d0c211d3b062006211e19001900214c3f042128010c42005100210c3d0c210c0e14211e191c0306214e2314011d3b062006210051002101651c0306214c0d042128017c20040d28011c030621005101210c22040d0421280100b5042228014c0f042100516221060306210c3d0c21
|3=>0x601062106031e19002108010c21012d062206221e19062106190c010c21062114211e19200f00214421061b942206190755002206220021201b002106210c210c22280104222801040d280100510021000e280114091e19040d0621042228011e19002114211e19280108010c2100211c03062114221e190c2100211e190621
|4=>0x6211e190603062206190c010c2106200623002200210c214422061b08010c2100210c210620062118220c0128011e191c03062106210c22072d062214011e190d3b0620062306221c0306210c011e190d5500220d39062006211e19080d0c210c2106192939062000220c2106210021b421
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x3100000000000000090000000000000000000000100000000000000000000000000
|5,0=>0x1410000000000131090846200000008480001e300000000000000e8800038200000000003621a1000000000000000000000000000b980000000000b0800000000000004cc00010306980000000c10000000162000049018c0a20000000000082000
|6,0=>0x62130c5842bf35e1ae4d6c6b33581ab4d546a82000294d464a124f1a709326963499a4491c68b3441a1890668033f11f44f467733a18000e440003799b0cd26663321184cbc65c22c9958ca8451327192cc94248223110cc8063e21e10e4c6c633318180005a62a3
|6,1=>0x1a84d22679b30d926c63
|7,0=>0x12d29594a4a4e5252919484a3e51d28d9464a2e5152899444a1e50d2859424a0e50528194049fe4fd27d93e49ee4f527993c49e02ee27613a89d04e627213889c04de26e13689b04d62
|8,0=>0x27033719b0cd46683331990cc466032f1
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 13
def pmP:Nat→Nat
|0=>0x1c00006200011840046000108000400000d8800300000998002000007bc001e700072c0017f0005840011000042000100000218000820001900005800012000040000088000180000200000400000c0000200000400000
|1=>0x1859c0616501819c06044014d840526001459c051650145840512301440004200010594040400100a40400400cd9c03163008e880236500878c0216f00859c0214000848c021000081000136f0045bc0116b00459400800
|2=>0x6858c1a14006079c181c205c1841606705059c12367048994103660407081018204059c100440401041000503c48c0f10b03c4000d1000300340b16302878c0a14b028500080e701c5ac0716701c5940712301c4000700b
|3=>0x380200206dbc803ef11c5944436710090040204100100231690880002004908012020001
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x200000000800000000000200000000000000
|5,0=>0x10000001034b00003c00700000000a002800000b020000000000000002000000800000000401812000050000d000c6010c0001000
|6,0=>0x36673186ad1121034bc0451a12676b0a00c529042c28072ec948bae21d411d8cfa89c007008e793831189588367136b8cdb334a9210e51da8cc084016b5
|7,0=>0x5e7d76fb85291fc28649f4378554c38b327e9576a9db5571fc58526964b2cd73f7b4e6af59a2c3b
|8,0=>0x22226f11c94950e1a9
|9,0=>0x11
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 7 (j%128);fld (pmP (k/32)) 22 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_93 8 roots_93 ops++addP pm 1 dom_74 4 roots_74 ops++addP pm 2 dom_90 5 roots_90 ops++addP pm 3 dom_71 5 roots_71 ops++addP pm 4 dom_86 5 roots_86 ops++addP pm 5 dom_87 8 roots_87 ops++addP pm 6 dom_94 7 roots_94 ops++addP pm 7 dom_78 5 roots_78 ops++addP pm 8 dom_79 7 roots_79 ops++addP pm 9 dom_92 5 roots_92 ops++addP pm 10 dom_29 5 roots_29 ops++addP pm 11 dom_77 5 roots_77 ops++addP pm 12 dom_75 5 roots_75 ops++addP pm 13 dom_31 6 roots_31 ops++addP pm 14 dom_91 6 roots_91 ops++addP pm 15 dom_15 4 roots_15 ops++addP pm 16 dom_30 4 roots_30 ops++addP pm 17 dom_23 5 roots_23 ops++addP pm 18 dom_89 5 roots_89 ops++addP pm 19 dom_85 7 roots_85 ops++addP pm 20 dom_69 4 roots_69 ops++addP pm 21 dom_84 4 roots_84 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_95 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_71 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_78 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_79 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_92 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_29 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_15 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_30 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_23 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_69 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_84 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_93 8 s (0,roots_93.map (·&&&dom_93)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_95 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_93 h
def symsG:List (List (Nat×Nat)):=[[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_95==dom_95)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_95 gM v ys):RunD true dom_95 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_95 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 21 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 21 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 61 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 61 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 70 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 70 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 45 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 45 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 10 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_95 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_95 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_95 roots_95 goal_95 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_95
theorem lowS_95:Lower true dom_95 roots_95 goal_95 10:=S_95.noCircuit
theorem lowS_111:Lower true dom_111 roots_111 goal_111 8:=lower_slice_b [(0xffff000000000000ffff00000000,1,33)] (by decide +kernel) lowS_79
theorem lowS_119:Lower true dom_119 roots_119 goal_119 9:=lower_slice_b [(0xcc00cc00cc00cc00cc00cc00cc00cc,16,18)] (by decide +kernel) lowS_117
namespace S_207
def pG:List (Nat×Nat):=[(1,5),(1,9),(1,65),(1,129),(2,10),(2,66),(2,130),(3,7),(3,11),(3,67),(3,131),(4,5),(4,68),(4,132),(6,7),(6,14),(6,70),(6,134),(8,9),(8,10),(8,72),(8,136),(12,13),(12,14),(12,76),(12,140),(64,65),(64,66),(64,68),(64,72),(64,192),(128,129),(128,130),(128,132),(128,136),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffff
def xsM:=roots_207.map (·&&&dom_207)
def gM:=goal_207&&&dom_207
def NN:Nat→Nat
|8=>1
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|8,0=>0x5bf25
|9,0=>0x83b1d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xff00000000000000ff00000000000000ff00000000000000ff00f0f0000000000000f0f0000000000000f0f0000000000000f0f0cccc000000000000cccc000000000000cccc000000000000ccccaaaa000000000000aaaa000000000000aaaa000000000000aaaaffff000000000000ffff000000000000ffff0000000000000000ffff0000000000000000000000000000ffff0000000000000000ffff000000000000ffff00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x6b191ac688
|_=>0
def sO:Nat→Nat→Nat
|8,0=>7
|9,0=>0x76
|_,_=>0
def wAt:=mkWire dB 7 208 0xffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 8
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x21
|_=>0
def oO:Nat→Nat→Nat
|8,0=>1
|_,_=>0
def PO:=mkPO wAt oP oO 8 3 7 5
def pmP:Nat→Nat
|0=>0xfc0
|_=>0
def pmB:Nat→Nat→Nat
|8,0=>1
|9,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 1 (j%128);fld (pmP (k/32)) 6 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_206 8 roots_206 ops++addP pm 1 dom_143 7 roots_143 ops++addP pm 2 dom_79 7 roots_79 ops++addP pm 3 dom_205 8 roots_205 ops++addP pm 4 dom_203 8 roots_203 ops++addP pm 5 dom_199 8 roots_199 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_207 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_143 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_79 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_199 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_206 8 s (0,roots_206.map (·&&&dom_206)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_207 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_206 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xffffffffffffffff0000000000000000,64),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_207==dom_207)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_207 gM v ys):RunD true dom_207 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_207 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_207 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 5 5=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_207 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_207 roots_207 goal_207 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_207
theorem lowS_207:Lower true dom_207 roots_207 goal_207 10:=S_207.noCircuit
namespace S_215
def pG:List (Nat×Nat):=[(1,5),(1,17),(1,65),(1,129),(2,18),(2,66),(2,130),(3,7),(3,19),(3,67),(3,131),(4,5),(4,20),(4,68),(4,132),(6,7),(6,22),(6,70),(6,134),(16,17),(16,18),(16,20),(16,80),(16,144),(64,65),(64,66),(64,68),(64,80),(64,192),(128,129),(128,130),(128,132),(128,144),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffff
def xsM:=roots_215.map (·&&&dom_215)
def gM:=goal_215&&&dom_215
def NN:Nat→Nat
|4=>4
|5=>73
|6=>156
|7=>89
|8=>20
|9=>4
|10=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x1cab814288083420776b
|5,0=>0x98ea193b4693a9b910cc8f1e885d6477cbd7651573fe5706866970965dd3608845ff475d5e15bad855bda52b1e529544f49f4d1194c7a1498cc483eb464314555943c0840e4e3ed653dea33af5e3a9ba350ac32c2c320be304152fa692d9d92c62e2a9c3291b52444823beb22cb921986206de1fe291fd761bd401b7a51b76319ea919afa185e218534179a1175d1175691628e15e071489d1216f0d6d60b4e8070f906dd10689d068010674805f4500d2400cb700a60
|6,0=>0x445d342f0e42eb142e5e42c2a4290041a3240b7e3fec73fb353ed2f3e4fc3c7cf3c0da3baad3ad2b3aa1238fd3388ea380a537d0535a31352bf3440f32ec5328bd322ab317e330738306a62fef22f3e72ecc12ccb32c7662c62e2bb3a2b5be2b4362ab972a32429a5a293ab28bd528ae32850f26e53267ce264c4260bd25c29258f723de1238462382a2327422f0e2216221d1421a49217f820eb91ff031fc9c1faac1eb271e85b1e77f1e6ff1e68d1d2c81d0b71c5ed1c1261a9b51a89c1a5c918f9818d1c174101567e143a013cea1394c12a30111c2102700f4050f23b0f1470ee9c0edd10ec6c0eba80eb650e1a30d7d40d6d60d27d0c1950bd290b38a0b0d20b01209ad0099310918b09143090260843507624075fc06e9d05e5705d6a05675050fd050cc03fe303ce50369a034f1030dd02b7f014c40112e00e6c00a60
|6,1=>0xb92c7a5ccca4e9c9a0038917882ad87cc77737e26fac86b80c6a6b0672c56552d64727625f95fba25f3985ab335245f522e24e9d44d7f44cefb4ad6049ab848ceb45c1945535
|7,0=>0xd3f01ce2a2accbdac9f08b6c28b5d387a71788336e135678036264560a305eff15e2c75cb7a5bd1c5ba4f5a42d58a8c57d9a566ed53d2f4e9d44d44f492d53f2873cd7539a4c3778a351ef34ee634947324d7313be304632f8a62f8042e102296b827b7626624265e02650c25da72586822b87220e3204691fbc8193cd17f75163851444912ced11c881108d0e6230d76c0d1d50d1890d0390cf470c8530c6010bb0d0ba540a9a10a6cb09d750930f0850907349072fe06df906a36065cf0649405dc0054430513804bc60457c04107029de0191300c7600ac7009260017a
|8,0=>0x8d72c5ade64fec1318c32cc9c2974d2759523b071891e108990dddb0cda00ada70aa0e08b53062b60614e05a59041d701512
|9,0=>0x5caae335f02ce631e7eb
|10,0=>0xde6cd
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xff00ff0000000000fa00fa0000000000ff00f00000000000fa00f0ff00ff0000000000f000f00000000000ff00000000000000f00000aa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aaff00ff0000000000ff00ff0000000000ff00000000000000ff0000ff00ff0000000000f000f00000000000ff00ff0000000000f000f0ff00000000000000ff00000000000000ff00000000000000ff0000ff00ff00000000000000000000000000ff00ff0000000000000000ff00f00000000000ff00f00000000000ff00f00000000000ff00f0ff00ff0000000000fa00fa0000000000ff00aa0000000000fa00aacc00cc0000000000cc00cc0000000000cc00cc0000000000cc00ccff00ff0000000000ff00ff0000000000ff00ff00000000000000000000000000000000ff00ff00000000000000000000000000ff00aaf000f00000000000f000f00000000000f000f00000000000f000f0ee00ee0000000000ee00ee0000000000ee00ee0000000000ee00ee0000ff00000000000000ff00000000000000ff00000000000000aaff00ff0000000000ff00ff00000000000000000000000000000000
|0,1=>0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00f0ff00ff0000000000ff00ff0000000000ff00ff0000000000ff0000330033000000000033003300000000003300330000000000330000ff00ff0000000000ff00ff00000000000000000000000000ff00f0ff00ff0000000000ff00ff0000000000aa00aa0000000000aa00aaff00ff0000000000ff00ff0000000000ff00aa0000000000ff00aaff00ff0000000000ff00000000000000ff00ff0000000000ff0000ff00ff0000000000ff00ff0000000000ff00ff0000000000aa00aaff00ff0000000000ff00aa0000000000ff00ff0000000000ff00aa0f000f00000000000f000f00000000000f000f00000000000f000a0000000000000000ff00ff00000000000000000000000000ff00f0fc00fc0000000000fc00fc0000000000fc00fc0000000000fc00fc0000ff00000000000000ff00000000000000ff00000000000000f0ff00ff0000000000aa00aa0000000000ff00000000000000aa0000ff00ff0000000000aa00aa0000000000ff00ff0000000000aa00aaff00aa0000000000ff00aa0000000000ff00aa0000000000ff00aa
|0,2=>0x30003000000000003000300000000000300030000000000030000330033000000000033003300000000003300330000000000330030ff00000000000000ff00ff0000000000ff00000000000000ff00f00b000b00000000000b000b00000000000b000b00000000000b000abb00bb0000000000bb00bb0000000000bb00bb0000000000bb00aa55005500000000005500550000000000550055000000000055000000000000000000000000000000000000ff00ff0000000000ff00aa550055000000000055005500000000005500550000000000550050000000000000000000000000000000000000000000000000ff00aaff00ff0000000000ff00ff0000000000ff00ff0000000000ff00aaff00ff0000000000ff00f00000000000ff00ff0000000000ff00f000000000000000000000000000000000ff00ff0000000000ff00f0110011000000000011001100000000001100110000000000110000ff00ff0000000000ff00ff0000000000f000f00000000000f000f0ff00ff0000000000ff00ff0000000000ff00f00000000000ff00f0ff00ff0000000000ff00ff0000000000ff00ff0000000000f000f0
|0,3=>0x330011000000000033001100000000003300110000000000330000330033000000000033003300000000003300330000000000330022ff00ff0000000000ff00cc0000000000ee00ee0000000000ee00ccff00ff0000000000ff00000000000000f000f00000000000f00000ff00ff0000000000ff00cc0000000000fc00fc0000000000fc00ccff00ff0000000000ff00000000000000aa00aa0000000000aa0000ff00ff0000000000ff00f00000000000fa00fa0000000000fa00f0ff00f00000000000ff00f00000000000ff00f00000000000000000ff00fc0000000000ff00fc0000000000ff00fc0000000000cc00cc0f000f00000000000f000f00000000000f000f00000000000f0000000000000000000055005500000000000000000000000000550000ff00ff00000000005500550000000000ff00ff0000000000550000ff00ff00000000000000ff0000000000ff00ff00000000000000aaf300f30000000000f300f30000000000f300f30000000000f300f0510051000000000051005100000000005100510000000000510050030003000000000003000300000000000300030000000000030002
|0,4=>0xff00ff0000000000aa00aa0000000000000000ff00f000000000000000000000000000ff00f00000ff00000000000000ff00000000000000ff0000000000000000f000ff0000000000f000ff0000000000f000ff0000000000f000f00000000000000000ff00ff00000000000000000000000000ff0000ff00ff0000000000ff00aa0000000000fa00fa0000000000fa00aa00000000000000000000000000000000ff00aa0000000000ff00aaff00ff00000000000000000000000000ff00ff0000000000ff00aa00000000000000000000ff000000000000000000000000000000aa00000000000000000f000f000000000000000000000000000f0000000000000000000000000000000000000f000f00000000000f0000ff00ff0000000000ff00ff00000000000f000f00000000000f00000f000f00000000000f000000000000000f000f00000000000f0000330033000000000033003300000000000300030000000000030000550055000000000055005500000000005500550000000000000000ff00550000000000ff00550000000000ff00550000000000ff0000
|0,5=>0xff00ff0000000000f000f00000ff00000000000000aa00000000000000ff00000000000000aaff00ff0000000000ff00ff00000000000000ff00000000000000aaff00000000000000ff00000000000000ff00ff0000000000ff00aaaa00aa0000000000ff00ff0000000000aa00aa0000000000ff00aa0000000000000000ff00ff00000000000000000000000000aa00aaff00ff0000000000fc00fc0000000000ff00cc0000000000fc00cc00000000000000000000000000000000ff00ff0000000000ff0000000000000000000000000000000000000000ff00000000000000f00000000000000000ff00ff00000000000000000000000000f000f0550055000000000055005500000000005500000000000000550000ff00aa0000000000ff00aa0000000000ff00aa0000000000000000000000000000000000000000000000000000ff00000000000000aa000000000000000000000000000000000000000000000000ff00f0000000000000000000000000000000005500550000000000550000aa00aa0000000000aa00aa0000000000ff00ff0000000000ff00aa
|0,6=>0xff00000000000000ff00000000000000aa00000000000000aa0000ff00000000000000ff00000000000000f000000000000000f000000000000000000000ff000000000000000000000000000000f00f000f00000000000f000f00000000000f000000000000000f000000000000000000000000000000000000ff00f00000000000ff00f0550055000000000055000000000000005500550000000000550000ff00ff0000000000ff00ff00000000005500550000000000550000f000f00000000000f000f00000000000ff00ff0000000000ff00f0
|_,_=>0
def sP:Nat→Nat
|0=>0x618681125d48a060828c283498512281a83a240252a28a0d0064a0b1a4c00a1e18d8932887061a98503042400a168869d0a9520a283428a066d1890084c94403401f28349890040c83227401c14506851268c830460017180c10514186961200a941a4c0101e182880e182840608080
|1=>0x140d88900281112c2400a1a5980900643830c0130a04584804a286af12005031ab8480323c30d00b4c941a2401706080890030182360449a1408b090084c94443429e142d10d3a646030461499180c10942646141a1420a060888014356090040c83462400a06ad509009820a0608029
|2=>0x64186364920a288868920781913a00c8c0608c1b527850304246037a3449732301820a21e061a14503308c4804a28a28120080a068c4800619501120063b06344a9140c1051241c861200f141a4c480180db8d12545061ad80083235789002818222d000c2834989006450304cc019
|3=>0x7860a282c680802818d7e24010180c318222549e140c30d125c80c06084804228a0d0a252991850689007850304442803228182306c00a0c34b090020f0d5e2401f14357890020514502400a640d8890078503622400a1af8b0900281b13a2400a06ad1890040f0346240191435609
|4=>0x182c1861a14f0c140c11100291030c36209320c30d2400532063428900290030ca0480140d58d0a240151828a0d1200c8a2888685102830d6c2400c140c6be1200b90180c31b12281ab1a74480140c6c21200c8c0618c1b1a105030c6c6853c28186226c2a12a28a0d120081e0634e89
|5=>0x1a0448a0618c2a1200a9e140c30d005cf0a0618d893c2818d7c2401708281861a00f0c140c311365cf0a060848010650061a01208148830d1268c830c44d802a28a221a2400a282c6c61200f0c140c11b12405030ca84803e28186502401a320c11b120130a06084804a845030c342a5
|6=>0x61940900685031a744804a205141a1400a293068900785035634480140c1010a2401a140c311361444b441868914506931201099182c30d0068503046c289142c18d3a1400a940c30900281861a482c8140c1090020f0b0c342804a291061a148190618c110064503051c480180c318
|7=>0x4ca45030c3449006186811200503054c4802e6850304240521450685120280a0618d8900290061ad8480140c6aa3a24019140c14f00206061ad84809c311061a246030c34085124020a0618880320c7061a01099168830d004020a06084803230a0b1a00f0a2888689140c6af120050b
|8=>0x2e2818212008580608480142de061a006030c3618514506d71200f0a160c69d0030514ac344a54228a0d120041e0c35b0900641861b5428a06188d400985031a7448032281911a7400a063570900685031af84802030186302480c0619509007c5061ad848010651061a14c8c0608880
|9=>0x60848010791061a2460a0619409008441928344801418d8d2c24019140c6a31200c8c400c30d0a94f0a283448008645030c3401008641861a0081e320c31100281911af84804a906030c344903c64182120080c061ad094c2818d7c2400ab20c6890028186501448020781865424026
|10=>0x6188802a28a0d1201319140c10900646030c606853e0c30d26240213c285861a00b9a140c30d0a64603043429f140c30d120130a0608d8900785030ca04803e645141a24008b05068900305030c36e89152c182362460a0608c05127c40a2834480140c11ba22405c180c30d1202d8a
|11=>0x1a2400a061888d0224019140c30d5424049140c10900645030c606850068503042402118281861a1448a06355231200c8c400c30d3e785141a2401e140c6a3120128c0618685140c69d4624017180c1090068c8c0618880140d58d1200f0a061889b08305030c3429e140c111006820a
|12=>0x1200415140c30d120280a0618689006450b441868034105030c3448034405030c342894c645030c34480c0281861a24019157c1861a00f0a0634e89016050b0618680140c15e120050378186890084522061868512645141634025180c30d120060a280c6851228182306c4804228586
|13=>0x1450689005c5030c4468500785030c60689009450b441868900281861b144803c291030c342894a28a0b1a24029140c30d12005030c34985120054b280c68900645030c35b0900785030c4468032281822200f19142c1861a005030c370890028a221a14490140c318362401e140c10d
|14=>0x222404e180c30d120040a40186851200d0a0618c0d120080a061a7890040f0c061868900305030c36b8900225830c3448042785030c3448018281863044689320c30dc824008322c30d01705030c344804228a0d120040c06186851240f030c34289005c6030c344802e281863624063
|15=>0x18281861b6848a0608c051200f0c142c1861a00f19140c69d1200f0a06186aa1202c0a060868900405030414480140c69d120050b0c373090020f030c344803e281861a24026140c30d0a2400a06186e5120130a0618c0d1200c8c440c30d129880a061868900285830c366802030186
|16=>0x1200b8a0618689003050b061868900305030c6c689140c3181a1448018281821a24019180c30d0a646030434480322818d3a2400a06186aa120130a061888d120051440342890078c8a280c689009440a061868500205141a14480142c1861b184804c785030c344803c645030434480
|17=>0x1200c8a061868900205030c34480140c31b1a2401e140c30d12005030c3720900646030c3448020641861a2401a20281861a2402114881861a2401e140c30d0a2402118281861a24010140c31112005030444480142d1061a2400a06186899a005030c37389002af830c34480145058d
|18=>0x5030c34480140c10d
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0xd5009400540005
|5,0=>0x17f617a5174616e61686162615d51576152514c61466140613a6135512f612a5124611f51196113610d6107610160fb60f560ef60ea50e460de60d860d350cd60c760c160bb60b560af60aa50a4609e60986093508d60876081607b6075606f60696063605d60585053504d60476041603b6035602f60296023601d601850126
|5,1=>0x1b561af61a961a3619d61976191618b61856
|6,0=>0x367636073597352734c6346633f73387331732b6325631f63187312630b730472fd72f672ef72e872e172da72d372cc72c662bf72b872b172aa72a3729c7295728e72886281727a7273726c7266625f72587251724a7244623d7236722f72287222621b7214720d720671ff71f871f171ea71e371dc71d661cf71c871c171bb6
|6,1=>0x5107509750274fc64f664ef74e874e174da74d374cc74c574be74b774b074a974a2749c6495748f64887481747a7474646e64686462645b7455644e74477441643b6434742d74276420741a6413740c7406640063f973f273ec63e573de73d773d073c973c363bc73b663af73a873a2639b7394738e63886382637b7374736d7
|6,2=>0x5ca75c465bd75b675b065a975a3659c7596659065897583657c7576656f75687561755a7553754d6546753f75387531752b6524751e65177
|7,0=>0x79a8793778b8784777d7776776e8766875f7757874f8748774087388731772b6724771e6717770f8708770176fb66f386eb86e386dc76d486cd76c676be86b776af86a876a2669a8693768d6685867e7676866f766876608658865086497642763b7634762e6627761f86196612760b760475fd75f585ed85e765df85d965d18
|7,1=>0x853684c7845783e7836882f7827881f881878108808880087f977f277ea87e287da87d377cc77c667bf77b877b177a987a27
|8,0=>0x8e278db78d478cd78c588bd88b588ad88a678a068997892788b7884787e6877786f8868786088597
|9,0=>0x8fe68f778f078e97
|10,0=>0x9046
|_,_=>0
def wAt:=mkWire dB 104 216 0xffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x3c1b0a290025220114010c35123514252e03061906311401120112292e0314821a01240d184414011a25060116301229002906254e15201712011a2906013c1b0a2900254a0306194429128906013c1b320112351425146d0c3536251a01140100250c3520251a2900251a29240d184400291a25062900251c35182c14010625
|1=>0x12351a013c1b0a2900250c35362514251a010ce91401326c12291a010c35323500291201140d12013288142506010cf114013288142506011435740d326c14251a01701910141401120106296a2522320029643706753c1b320114251c35182c002906254c0f34250c3520011a291425240d184414011a250619148914250601
|2=>0x42270c0d100106293c1b0a29120106250c0d1825002982290a3712012201140112354c033c353201122920250c351435002912010c0d1001062906650619140114251a191a250a2900250c35362514251a014c0f2e0120251a290a29120106ba3e1b4a01102506293c1b320112290a29120106ae1a753c1b3201122918440029
|3=>0xc3520011a291001122112010629142d140106250c351235182514018a01328b142506011425184414011a2506753c1b0a291a753c1b0a2912860619180d002906010619122912013e0f4225100106294c1b3c351825202500291a011a293c1b320112290d128601320f1229362514251a01342736291a011a251a010a291201
|4=>0x1a29366700350c35302b22011a254c37302936251a0112311286180d14011a650035320112293c35320112291241342720011a2918250029123532350c353201122916011229062506294a03122106291425146d1a0142270619148906011a011a19182500294c370a4112011a293e374a011025062914251a19146d1a013425
|5=>0x3e37182d140106191221120106299a0d06190a2b12011a753c1b3201122914620c350a3512011a251201146d1a011827002906010629402b16010c0d06250625180d140100251a19146d1a013c1b06250a29002578353288142506010025184414011a2592251a1920031a29140d0a29002512011629000d0625220112291a25
|6=>0x20011a291a19184614011a250041202514350c351017061906291b45326f14251a010a0d3c0f0a2912013c373201122922030c35123514253c0f18250029102714010629060114620a350025342720011a2916301229002906251489142506010c35342720011a2914010c0d120d142506010c0d320112293c530c0d32011229
|7=>0x29002516330619140106253c1b18250029128a0029000d0c0d10010619122106293c0f320112291a321401120112290a40120114351a253c1b320112293c1b3201123514253e1b4a01102506291a29002922011a253c371825140106d93c0f3201122900251425000d06291229002912350c35005e2e0120251a294c2b3425
|8=>0xc3532011229061512011401142500650619320d14254c273c3532011425342700411a29320112291a251a294c1b302922014a031025062914351a19320112291401362714351a014c1b2e0120251a291c19182c140106253e373c0d0a293c370a2912012e010c3520251a291a19320314351229062532881425060106661229
|9=>0x200112011a2914251a1900290025195d182e140106251461362500353e373c0d320112290c0d32891425060100661425140d0c0da601184614011a251a19182714011a0114010c350a3512014a0112210629154d184614011a250c351b2d1827002918250029060106293e37182d062510011229140d0c0d4c0f342536293c0b
|10=>0x3201122906151201140114253c0d320112293c0b3201122906651229002900253c1b3201122914010c3520251a291235183514013c1b320112291a01182514011a2534271835002912350c3532011425342720011a2942270c0d100106290c353c35320112290a351401120112293e2b4a01102506291231180d140106251241
|11=>0x342720011a29120120011a29326d14251a010761320312291603142506253c1b3201122932031425062514460c351a253288142506011201148906011425120d0c0d140110250629061900290025362500350c35062510010629302b22011a253c3732011229200314350c350a35120112290c3520011a29180d002900253c37
|12=>0x1a25061910030629222900251a251a150a291201142d06010625328b1425060106010a2912010619142d06252e0320251a2914820a0d12010619182714013c0f32011229182514011a250c3512351425320114250625c401323712290025000d0c0d362514351a010c35320112294227002106291b6132031229142506010625
|13=>0x302936251a01142514010601342520011a2906250a2b0025140112351a291027140d00290a0d120106293625146d1a01220314351a25182514350029182e06251827140d00291825180d0029220114011a251229180f14011229062506299e2900461a2510010c0d062914011201062914350a291201140122291a2522290035
|14=>0x32011229184514011a2506190a0d0025061932011229122112010629061912010629182f14013c35320112290c35320112291401126e1a010c350a3512011825140106253c1b320112293c37320112290c3532031229120114350c353c1b32011229148a06250601140d320112294a01102506293c350a291201328a14250601
|15=>0xc351229140d1a0132011229180f0029140114251435122920011a29148906010a291201180d002914351a2512350c35062506010a2b1201146e1a01160306250c0d062520251a291401062514011a010a3512010c3500291201140114250c35140114253c1b320112293c37
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x660018000
|5,0=>0x20d07e500007b31dd00001c946e41a540000000000000064500005f500005a5000000015cc00000005340000000139449500000001114000000000000004040f4c3850dc43250000000000000000000000c44301000000000002b5099422407901d10000194000015400001140314000
|5,1=>0x912231400000000000000000224c872
|6,0=>0x5d517145b516945951614578d5a4559152453914a451cd4344fd13c34e4d3544c512d44a8d26448cd1f446d1183454d11400010d442510544050fd43e50f633c90ee43a90e730000e433810dc43610d533450ce33290c73310cc042f10b932d50b232bccab429d0a3427d09b425d0934
|6,1=>0x95cc00094d24f492d248391124138f523948d523148b8e2a489ce24388121c48612144844e0e382920648091fe47e91f737cd1ef47b0de847911e137751d940001d54748dce47291c647091be46e91b646ccdaf46ad1a836911a1367519a365cd934640d8c4621184460117d30001794
|6,2=>0xaf8eba4adceb43ac12ad3aa52a63a8ce9f4a70e984a54e914a352894a1528149f527949d527239b926a4999262497925a4
|7,0=>0xdf4f7a3ddcf743dc4f6e3dacf683d94f623d80b5d3d68f573d50f513d38f4b3d20f453d08f3f3cf0f393cd8f333cc0f2d3ca8f273c90f213c78f1b3c60f153c48f0f3c30f093c18f033c00efd3be8ef73bd0ef13bb8eeb3ba0ee53b88edf3b70ed93b58ed33b40ecd3b28ec73b10ec13
|7,1=>0x3c73f10fc13ef8fbb3ee0fb53ec8faf3eb4baa3e9cfa43e84f9e3e6cf983e54f923e3cf8c3e24f863e0cf803
|8,0=>0xfc0bee2fb0bea2fa0be62f90be22f80bde2f70bda2f60bd62f50bd22f40bce2f30bca2
|9,0=>0xfd47f41fcc7f21
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 14
def pmP:Nat→Nat
|0=>0x10c001080010100100000ec000c1000a4000a3000a0000840006c0006400061000590004900041000400002d0002c00024000210002000014000100000f0000c000090000800004000030000100000
|1=>0xecc00ec000ded00cec00bed00bec00acc009ed0090800900008ed0084000800007ed007cd007840060c0044500400003ed0034900200001fd001ed001ec0018800184001830014400141001400010d
|2=>0x85ed083cd081ed081000807d0806508020071ed06080051ed051ec041fd041ed040fd04080040690403c04000031fd031ed030dc021ed020b40203c0201c020140200c011cc010dc010610102801000
|3=>0x10a481050c104041030c10208101ed100491000c10008100040e1ed0e0ed0e0e10e0c90e0a40e08c0e0840d1ed0d0cc0c0fd0c0ed0c0800b0cc0a08008ccc08bed08acc089ed087ed087cd0878c08788
|4=>0x501ed489ed48880481ed48100480fd48020460cd441ed440ed421fd420fd420ed4207d4203c42004411ed40a4c409ed407cd40404403c9401ed40141400bc40004200ad20085185c5181cd10ded10bed
|5=>0xc0804c0189c0100c00a990bed903ed903889030c9028c9024d9020c90188900088a0518900c889c88880c8880888020851fd840d9840798403c820ed811fd810dc803cd801ed80141505ed505845050c
|6=>0xc90a8c89edc8988c81edc81cdc81adc8189c8185c8149c810dc810cc8101c80edc80a9c8089c8065c802dc802cc20edc11edc106c
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x20200
|5,0=>0x401000000000000f33042b001c7700232f5a0000000014008400140000330000040000180b00002400000000090a7f2d470000000000002a080000000750100c4e0006001e00063e00
|6,0=>0x10000538c504491c1ea9410586ce1c689d83101b039b1a676b5b550a4316998a31341e1300b65c10b265011d3a16031d010139599277766b46786dc0270a0057281d7ca09844907e1785a53cad72b904b30101260101bd37ab517d4500bf1d1d7d35196aaf0b5e03000348a60b04612115b386cb471cb1017b01304b6fae7b1d
|6,1=>0x1aa4236731c3f8b21cc76b07d4479b8010d25381010011269058eb5
|7,0=>0xd19ecf2888acd4714c0a22d282bbc3c6c9643d2852c8282e29119aa3a88c93a91f31cd04930eb996752c4dc2ca62624c6020705dc458284f8fbcd066c75da7b7d3875d6ca0a1795d6bcf6b3b5d916e74c18094b4be3db98191
|8,0=>0xd1899c5fa295cf95323b54a47a535663979fba8d
|9,0=>0x385d4a7a
|10,0=>0x28
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 20 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_213 9 roots_213 ops++addP pm 1 dom_146 4 roots_146 ops++addP pm 2 dom_151 8 roots_151 ops++addP pm 3 dom_199 8 roots_199 ops++addP pm 4 dom_83 5 roots_83 ops++addP pm 5 dom_211 8 roots_211 ops++addP pm 6 dom_210 7 roots_210 ops++addP pm 7 dom_87 8 roots_87 ops++addP pm 8 dom_214 8 roots_214 ops++addP pm 9 dom_150 5 roots_150 ops++addP pm 10 dom_198 5 roots_198 ops++addP pm 11 dom_212 7 roots_212 ops++addP pm 12 dom_209 7 roots_209 ops++addP pm 13 dom_195 5 roots_195 ops++addP pm 14 dom_147 5 roots_147 ops++addP pm 15 dom_135 5 roots_135 ops++addP pm 16 dom_86 5 roots_86 ops++addP pm 17 dom_82 4 roots_82 ops++addP pm 18 dom_71 5 roots_71 ops++addP pm 19 dom_23 5 roots_23 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_215 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_146 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_150 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_198 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_212 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_209 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_195 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_135 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_71 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_23 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_213 9 s (0,roots_213.map (·&&&dom_213)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_215 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_213 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)],[(0xffff0000ffff0000ffff0000ffff0000,112)],[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112)],[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)],[(0xffffffffffffffff0000000000000000,64),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_215==dom_215)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_215 gM v ys):RunD true dom_215 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_215 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 73 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 73 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 156 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 28 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 156 → Z 6 i = true := (range_split z6_0 z6_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 89 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 89 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 20 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 20 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 4 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s:Nat) (hs:s≤10):∀ i<NN s,bar dom_215 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤10) (h:RunD true dom_215 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_215 roots_215 goal_215 11:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_215
theorem lowS_215:Lower true dom_215 roots_215 goal_215 11:=S_215.noCircuit
theorem lowS_235:Lower true dom_235 roots_235 goal_235 9:=lower_slice_b [(0xa0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a,8,9)] (by decide +kernel) lowS_234
theorem lowS_243:Lower true dom_243 roots_243 goal_243 9:=lower_slice_b [(0xa000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a,16,17)] (by decide +kernel) lowS_242
def dzo_217_32:=0x303030300000000030303030000000003030303000000000303030300000000
def gzo_217_32:=0x303030300000000030303020000000003030302000000000302030200000000
def gsh_217_32:=0x3030303000000000303030200000000030303020000000003020302
theorem lowS_zo_217_32_208:Lower true dzo_217_32 roots_217 gzo_217_32 6:=lower_iso_b (d1:=dom_217) (r1:=roots_217) (T1:=gsh_217_32) [(dom_217,32)] (by decide +kernel) (lower_slice_b (T:=gsh_217_32) [(0x2020202000000000202020200000000020202020000000002020202,0,1),(0x3000300000000000300030000000000030003000000000003000300,0,8)] (by decide +kernel) lowS_208)
namespace S_249
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(1,129),(8,9),(8,40),(8,72),(8,136),(16,17),(16,80),(16,144),(24,25),(24,56),(24,88),(24,152),(32,33),(32,40),(48,49),(48,56),(48,112),(48,176),(64,65),(64,72),(64,80),(64,192),(96,97),(96,104),(96,112),(96,224),(128,129),(128,136),(128,144),(128,192),(160,161),(160,168),(160,176),(160,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffff
def xsM:=roots_249.map (·&&&dom_249)
def gM:=goal_249&&&dom_249
def NN:Nat→Nat
|5=>2
|6=>8
|7=>9
|8=>3
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0x33beb01b95
|6,0=>0xec1d9c3532920ea4552629cd1283aa157f814bb5
|7,0=>0xe3008a769aa510a7ffde78d6c54cc73e71b0943c0102a
|8,0=>0x5733737bef2f1be
|9,0=>0x2c020
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xc0c0c0c0c0c0c0c0000000000000000080808080808080800000000000000000000000000000003030303030303030303030300000000c0c0c0c0c0c0c0c0c0c0c0c000000000c0c0c0c0c0c0c0c0c0c0c0c0000000303030303030303030303030303030303030303030303030202020202020202c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c000000000c0c0c0c0000000000030300000303000003030000030300000303000003030000020200000202c0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c000000030303030303030303030303030303030303030303030303000000000000000080808080808080808080808080808080808080808080808080808080808080b03030303030303000000000000000003030303030303030000000000000000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0000000000000000000000000000000303030303030303030303030303030303030303030303030303030300000000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c000300030003000300030003000300030003000300030003000300030003000300c0c0c0c0c0c0c0c08080808080808080c0c0c0c0c0c0c0c080808080808080b03030303030303030303030303030302020202020202020202020202020202
|0,1=>0x30303030303030300000000000000000303030300000000
|_,_=>0
def sP:Nat→Nat
|0=>0x188e62a462080c520c4731523100e832462600e62b46201cc548c4c398b0188e62a4623bcc568c413952261d462a447518a9188204386209cad18981395631040648827518a41880732c403a8c418820
|1=>0x9188e62a46201cc548c47418ab
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x56005
|6,0=>0x3773162b62561e71861170b6
|7,0=>0x7476e66775f85875174b64473e6
|8,0=>0x8878177b6
|9,0=>0x8f6
|_,_=>0
def wAt:=mkWire dB 17 250 0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x3953154953993954a13153953150193954993953a131559b49501b3954993993a13151b23a13153993953156974993994990953993954953991b20954a13953153994a1395315
|_=>0
def oO:Nat→Nat→Nat
|5,0=>4
|6,0=>0x6095348cf330c931c843
|7,0=>0x2a2a0a6290a22809e2709a2
|8,0=>0x2e1b46c1
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 10
def pmP:Nat→Nat
|0=>0xcf9e74f2c57d77ada7cd3a67d73af957c7b63570f9874c322070020003c004000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>2
|6,0=>0x194e823c2a
|7,0=>0x125ba2c9a5b0
|8,0=>0x34e9
|9,0=>6
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 13 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_241 8 roots_241 ops++addP pm 1 dom_248 7 roots_248 ops++addP pm 2 dom_153 5 roots_153 ops++addP pm 3 dom_89 5 roots_89 ops++addP pm 4 dom_121 7 roots_121 ops++addP pm 5 dom_57 5 roots_57 ops++addP pm 6 dom_233 8 roots_233 ops++addP pm 7 dom_217 8 roots_217 ops++addP pm 8 dom_185 7 roots_185 ops++addP pm 9 dzo_217_32 6 roots_217 ops++addP pm 10 dzo_216_32 5 roots_216 ops++addP pm 11 dom_120 4 roots_120 ops++addP pm 12 dom_184 4 roots_184 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_249 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_153 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_217_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_216_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_120 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_184 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_241 8 s (0,roots_241.map (·&&&dom_241)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_249 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_241 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_249==dom_249)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_249 gM v ys):RunD true dom_249 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_249 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 2 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 8 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 9 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 3 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_249 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_249 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_249 roots_249 goal_249 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_249
theorem lowS_249:Lower true dom_249 roots_249 goal_249 10:=S_249.noCircuit
theorem lowS_252:Lower true dom_252 roots_252 goal_252 9:=lower_slice_b [(0x1100110011001100110011001100110011001100110011001100110011001100,32,40)] (by decide +kernel) lowS_244
def isoMvS_123:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_123:Lower true dom_123 roots_123 goal_123 8:=lower_iso_b isoMvS_123 (by decide +kernel) lowS_111
def isoMvS_125:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_125:Lower true dom_125 roots_125 goal_125 10:=lower_iso_b isoMvS_125 (by decide +kernel) lowS_95
def isoMvS_126:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_126:Lower true dom_126 roots_126 goal_126 9:=lower_iso_b isoMvS_126 (by decide +kernel) lowS_63
def isoMvS_159:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_159:Lower true dom_159 roots_159 goal_159 10:=lower_iso_b isoMvS_159 (by decide +kernel) lowS_95
def isoMvS_175:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_175:Lower true dom_175 roots_175 goal_175 8:=lower_iso_b isoMvS_175 (by decide +kernel) lowS_111
def isoMvS_187:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_187:Lower true dom_187 roots_187 goal_187 8:=lower_iso_b isoMvS_187 (by decide +kernel) lowS_111
def isoMvS_190:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_190:Lower true dom_190 roots_190 goal_190 9:=lower_iso_b isoMvS_190 (by decide +kernel) lowS_63
def isoMvS_221:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_221:Lower true dom_221 roots_221 goal_221 11:=lower_iso_b isoMvS_221 (by decide +kernel) lowS_215
def isoMvS_222:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_222:Lower true dom_222 roots_222 goal_222 10:=lower_iso_b isoMvS_222 (by decide +kernel) lowS_207
def isoMvS_238:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_238:Lower true dom_238 roots_238 goal_238 9:=lower_iso_b isoMvS_238 (by decide +kernel) lowS_119
def isoMvS_246:List (Nat×Nat):=[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_246:Lower true dom_246 roots_246 goal_246 9:=lower_iso_b isoMvS_246 (by decide +kernel) lowS_243
def isoMvS_250:List (Nat×Nat):=[(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_250:Lower true dom_250 roots_250 goal_250 10:=lower_iso_b isoMvS_250 (by decide +kernel) lowS_249
theorem lowS_127:Lower true dom_127 roots_127 goal_127 11:=lower_slice_b [(0xcccccccccccccccccccccccccccccccc,8,10)] (by decide +kernel) lowS_125
theorem lowS_223:Lower true dom_223 roots_223 goal_223 12:=lower_slice_b [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,8,10)] (by decide +kernel) lowS_221
theorem lowS_239:Lower true dom_239 roots_239 goal_239 11:=lower_slice_b [(0xffff000000000000ffff000000000000ffff000000000000ffff00000000,1,33)] (by decide +kernel) lowS_207
theorem lowS_247:Lower true dom_247 roots_247 goal_247 12:=lower_slice_b [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000,1,33)] (by decide +kernel) lowS_215
theorem lowS_251:Lower true dom_251 roots_251 goal_251 11:=lower_slice_b [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,8,9)] (by decide +kernel) lowS_250
theorem lowS_253:Lower true dom_253 roots_253 goal_253 12:=lower_slice_b [(0x3333333300000000333333330000000033333333000000003333333300000000,1,33)] (by decide +kernel) lowS_221
def dzo_214_32:=0x55005500000000005500550000000000550055000000000055005500000000
def gzo_214_32:=0x55005500000000005500540000000000550054000000000054005400000000
def gsh_214_32:=0x550055000000000055005400000000005500540000000000540054
theorem lowS_zo_214_32_208:Lower true dzo_214_32 roots_214 gzo_214_32 6:=lower_iso_b (d1:=dom_214) (r1:=roots_214) (T1:=gsh_214_32) [(dom_214,32)] (by decide +kernel) (lower_slice_b (T:=gsh_214_32) [(0x440044000000000044004400000000004400440000000000440044,0,2),(0x500050000000000050005000000000005000500000000000500050,0,4)] (by decide +kernel) lowS_208)
def dzo_220_32:=0x1111111100000000111111110000000011111111000000001111111100000000
def gzo_220_32:=0x1111111100000000111111100000000011111110000000001110111000000000
def gsh_220_32:=0x11111111000000001111111000000000111111100000000011101110
theorem lowS_zo_220_32_208:Lower true dzo_220_32 roots_220 gzo_220_32 6:=lower_iso_b (d1:=dom_220) (r1:=roots_220) (T1:=gsh_220_32) [(dom_220,32)] (by decide +kernel) (lower_slice_b (T:=gsh_220_32) [(0x10101010000000001010101000000000101010100000000010101010,0,4),(0x11001100000000001100110000000000110011000000000011001100,0,8)] (by decide +kernel) lowS_208)
def dzo_218_32:=0x505050500000000050505050000000005050505000000000505050500000000
def gzo_218_32:=0x505050500000000050505040000000005050504000000000504050400000000
def gsh_218_32:=0x5050505000000000505050400000000050505040000000005040504
theorem lowS_zo_218_32_208:Lower true dzo_218_32 roots_218 gzo_218_32 6:=lower_iso_b (d1:=dom_218) (r1:=roots_218) (T1:=gsh_218_32) [(dom_218,32)] (by decide +kernel) (lower_slice_b (T:=gsh_218_32) [(0x4040404000000000404040400000000040404040000000004040404,0,2),(0x5000500000000000500050000000000050005000000000005000500,0,8)] (by decide +kernel) lowS_208)
def dzo_222_32:=0x5555555500000000555555550000000055555555000000005555555500000000
def gzo_222_32:=0x5555555500000000555555540000000055555554000000005554555400000000
def gsh_222_32:=0x55555555000000005555555400000000555555540000000055545554
theorem lowS_zo_222_32_208:Lower true dzo_222_32 roots_222 gzo_222_32 7:=lower_iso_b (d1:=dom_222) (r1:=roots_222) (T1:=gsh_222_32) [(dom_222,32)] (by decide +kernel) (lower_slice_b (T:=gsh_222_32) [(0x44444444000000004444444400000000444444440000000044444444,0,2),(0x50505050000000005050505000000000505050500000000050505050,0,4),(0x55005500000000005500550000000000550055000000000055005500,0,8)] (by decide +kernel) lowS_208)
namespace S_254
def pG:List (Nat×Nat):=[(2,10),(2,18),(2,34),(2,66),(2,130),(4,20),(4,36),(4,68),(4,132),(6,14),(6,22),(6,38),(6,70),(6,134),(8,10),(8,40),(8,72),(8,136),(12,14),(12,28),(12,44),(12,76),(12,140),(16,18),(16,20),(16,80),(16,144),(24,26),(24,28),(24,56),(24,88),(24,152),(32,34),(32,36),(32,40),(48,50),(48,52),(48,56),(48,112),(48,176),(64,66),(64,68),(64,72),(64,80),(64,192),(96,98),(96,100),(96,104),(96,112),(96,224),(128,130),(128,132),(128,136),(128,144),(128,192),(160,162),(160,164),(160,168),(160,176),(160,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffffffff
def xsM:=roots_254.map (·&&&dom_254)
def gM:=goal_254&&&dom_254
def NN:Nat→Nat
|5=>21
|6=>143
|7=>273
|8=>197
|9=>63
|10=>8
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0xe047edd4e2d2975b86e19d4609a2479a0a4900d08c58e855e183fab83b687de1774bd2642d65cfd0335ab2305b1f09f0af9a0586f
|6,0=>0xa845ea4dbca44bca098fa033a9e20c9d02f9bf3a98a63984b9972b39638b949d292e869271d90d1c8cf648c0b78b0ab8a01583ba6820e3801077fd037eeb97eaf37e8767d8067d2cb7caf47c8827664a7535572882726df701406ed796df7a6df2b6d64a6d1546c3d36a45968bd86870b67d7666ceb66c74651c364f2263d7b621da604675dc1c5d2395c1a359d94597e258f945635755ff8552495427151a2c4f0114ea904e0014d20d4cdf84cb854b69e4ac2246bc0444bc4043d3f2ef3e6593c9113b85839fb639abf39510371ea3560b350e3334a530b172e3c82cc382a5b828d432547024d47247e7239d923646225882210821f60211a71f5f81ebd91d9b91d82c1c4ac1c3ed199af1902217eb1172851506e14c3e139301344a116f910d8810c8d106a20ef000c1440bbe60b71e0a21709aa9096ad0546d048690225f
|6,1=>0xff8bef72dbf3f4fe506bd19a3c8884c5638c3b6bc2fa6c2a33bb550b21ccae796ad6f4aa6f4
|7,0=>0x42a944216d41ed8417634141640f303ed873e8ef3e7733e1883d9403d7fe3d33e3d2cb3d0053c7d73c5ad3bbb439ab138ce03828a3758f36e9b36c20358fa33c7c333003269f32549323cf31046306512eb732e7182e48b2c97a2c8e42c8ac29a59290e92903e285b12840d27f1c27ab52620a254fc2543324dc1243f723c17236062329a2247121a35215bf2136d20f741f1fb1eca21e3781df351d8d21d8791d0ee1d01a1c09e1b8881b36c1b2da19dcb19cf319a0c19861194a517f1517ddc17c051787f174831707e16e10168681646b1636a1634e15b45156f8143201406613faa1374d132fb12a74125f111f3d11b4b1034a103160f26a0e66a0e5dd0e4750e31a0d71e0ba420b1330abd10a7670a1a0098ac08dae082e20827306f1105de405a4d0516c04fc903bc1036500331a030c102d9b014fa00d930094e00294
|7,1=>0xc9328c777ec6b3cbdf8cbd3cebb9c8bb36ebae0cb77ecb63beb46c2afd95afd00af1cea9fdea8798a2e3ba10afa07a99e4d09dec99a59d99bda9807796a839585c9543b9274990ce98fd448f71d8f0428ec8a8df4d8d754887a98839e88195876b5869e5861ec85f4a82d2f81d867df797caf77bcd87ba617a8de7a733768567660e74e6f746a6740ce7211a71fa27078e6c3f36be7e6953b6876a67f43675a56722566ceb66cb565a67646f263a306268c61fd361ef86125f611d0600db5f93c5d90a5d14e5ce405c28c5b2955abcd5aa065a71e5a52c5a23959ae4597d65947b58b735898d5809e5759f574f755d8e54ebd541c353adf522cd522695206a517c350b364f1f64ecdf4ecdd4ec854eb154d7964d0de4c5b34bda74ae8c493fa491df490e348f934880c4853447c3d4762d465dd4646f446ed44126440b743c5a
|7,2=>0xff93cfd92ef8609f835af0506efe24eed2ae7e47e477fdfb09df659dcee7d8222d4c59d340bd2badcc58a
|8,0=>0x6dd566cf1c6bb0769dc4699bc6861d667c66491f63836631d66002f5f22c5ee745d1ee5bb085ae6359dc059584591e358a6258588585005737f56bcf54ca553bbc52aba516fd505f6505bc4fc2e4f91d4ee534ebb74de8f4cb2c4c10d4b7f24a8884a0e74950a4907f4673b465904645b46251455c445059444ee429844229740da540c023c8c83a71936b1f32d4f310d82e69e2e13c2c7742b90b2a0dd2773626e3326ce525f7824a44247f3243e2230c5230302245320fe1205ef1e18e1dd8a1d4bc1d0a21c79d1c4631bf911ba141b0761a8491a5b817e27167c716313160df15f7115b3a1561914f0c14b1a14ae9146d4141de13e441257b120c2118001131b102c90e0b10d5ef0c3760c3430bc520bc3c0a8df098e50989208c58087c307b5806e0a063fe04f6d04ce603e4003026016ac0127d0111d00a8400870005f0
|8,1=>0xfb4c5fa9e5fa727f6fdcf6d0af12a9ebbade52d2e2095dd64ed9fe5d537ed2c6cd047ed00e8cd9d4cb486c9a15c87f3c8083c4cb9c4569c409bbf0b6bd996bd82abc72ab9791b886bb7a1db4a93b0335ad969ad84caa7b99ffa39fa399e7e59dcfc9984e9953a969369516a942a490c02905df8e8fe8b91f8b24588e7586c0685f2b7fa807f3b87e49d7df017c0407bed97be9a78765782f976ef1763f1756c9740c3739477235d6f2be6e0f3
|9,0=>0xfe463f29b8e43f0df15ad3d2bd07dabd694b6cccb10c9acc1ca5c9a9e6a69d97094f9d8997b892a1889498600781b917cc157b2f57ae887444d73725719a36dee66a30c5f64c5eedd5eeda59c8657c8456f0c560644f2014d0164bfbc4b93a4a1c34a05843620425cf414ff40d043c3ab3b7e63b6693937a2d42d2b9a624e8f2315220ef4205401a2d115e8813d581190a109bc101780a1ea0673d0390f
|10,0=>0xc5d3eab89d950797d51a5b02e420a2371a00a6d4
|11,0=>0xba90f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaaaaaaaaaaaaaaaaaaaa0000aaaa0000aaaaaaaaaaaaaaaaaaaa0000aaaa00000000000000000000000000000000000155555555555555555151515151515152aaa80002aaa80002aaa80002aaa80002aaa80002aaa80002aaa80002aaa80005555555555555555555555555555555555555555555555550000000000000000aaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa00000000000000015555555400000001555555540000000155555554000000015555555400000002aaaaa2a2aaaaa2a2aaaaa2a2aaaaa2a2aaaaa2a2aaaaa2a2aaaaa2a2aaaaa2a5555555555555555555555555555555555555555555555555555000055550000aaaaaaaaaaaaaaaaa8a8a8a8a8a8a8a8aaaaaaaaaaaaaaaaa8a8a8a8a8a8a8a95555555555555555555555555555555511111111111111111111111111111112aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa800000005500550055005500550055005500550055005500550055005500550055005500a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a955555555555555551111111111111111555555555555555511111111111111100002aaa80002aaa80002aaa80002aaa80002aaa80002aaa80002a2a00002a2a5555555555555555555555555555555500000000000000000000000000000000
|0,1=>0xaaaaaaaa0000aaaaaaaaaaaa0000aaaaaaaaaaaa0000aaaaaaaaaaaa000000000000000000000000000000000000000155555555555555555555111155551112aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa2222aaaa2222aaaa2222aaaa22255555555555555555555555555555555555555555555555544444444444444440000aaaa0000aaaa0000aaaa0000aaaa0000a8a80000a8a80000a8a80000a8a800015554000155540001515000015150000155540001555400015150000151500002aaa80002aaa80002aaa80002aaa800022220000222200002222000022220000000000000000000000000000000055555555555555555555000055550000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000aaaaaaaa0000000141414141414141414141414141414141414141414141414141414141414141422222222222222222222222222222222222222222222222222222222222222225555555555555555555555550000000055555555555555555555555500000000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000aaaa0000aaaa0000aaaa00015555111155551111555511115555111155551111555511115555111155551112aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a0000000000000000555555555555555500000000000000005555444455554444
|0,2=>0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa88888888aaaaaaaa888888895554000155540001555400015554000155540001555400015150000151500000000002a8000002a8000002a8000002a8000002a8000002a8000002a8000000000000000000000000000000000000000555555555555555555555500555555000000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aa000000aa0155555555555555555555555555555555555554015555540155555401555554000000000000000002aaaaaaaaaaaaaaa80000000000000002aaaaa802aaaaa805555555555555555555555555555555555005500550055005500550055005500aaaaaaaaaaaaaaaaaaaa8888aaaa8888aaaaaaaaaaaaaaaaaaaa8888aaaa88880000000000000000000000000000000000015554000155540001515000015152aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa2a2a2a2a2a2a2a5555555555555555555554545555545455555555555555555555545455555454aaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa015555540155555401555554015555540155555401555554015555540000000002aaaaaaaaaaaaaaaaa802a802a802a802aaaaaaaaaaaaaaaaa802a802a802a805555555555555555555555555555555555555454555554545555545455555454
|0,3=>0xaaaa0000aaaa00000000000000000000a8a80000a8a80001555400015554000155540001555400015554000155540001555400000002aaa80002aaa80002aaaaaaaaaaaaaaaaaaa80002aaa80002aaaaa2a2aaaaa2a5555444455554444555544445555444455554444555544445555444400000000aaaaaaaa8888aaaaaaaaaaaa8888aaaaaaaaaaaa8888aaaaaaaaaaaa88888888000044440000444400004444000044440000444400004444000044440000000002a802a8022002a802a802a8022002a802a802a8022002a802a802a8022002244444444444444444444444444444444555555555555555555554444555544440000000000000000aaaaaaaaaaaaaaaa0000000000000000a8a8a8a8a8a8a8a951515151515151515151515151515151555555555555555555555151555551500002aaa80002aaa80002aaa80002aaa80002aaa80002aaa800000000000000055555555555555555555555555555555555555555555555555554444555544440000000000000000aaaaaaaaaaaaaaaa000000000000000088888888888888880000000000000000000000000000000155555555555555555555555400000002aaaaaaaaaaaaaaa80002aaa80002aaaaaaaaaaaaaaaaaaa80002a2a00002a2a0000000000000000000000000000000055555555555555555555545455555454
|0,4=>0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000141414141414141414141414141414141414141414141414141414141414000000000000000000000000000000000002aaaa2222aaaa2222aaaa2222aaaa22200000000000000000000000000000000555555555555555544444444444444440000000000000000aaaaaaaaaaaaaaaa0000000000000000aaaaa8a8aaaaa8a95555555555555555555555555555555555555555555555555401540154015402aaaaaaaaaaaaaaaaaaaaa802aaaaa802aaaaaaaaaaaaaaaaaaaaa802aaaaa805555555555555555555555555555555555555555550055005555555555005500000000000000000000000000000000000000aaaa0000aaaa0000888800008889555555555555555555555555111111115555555555555555555555551111111008080808080808080808080808080808080800000808000008080000080800045454545454545454545454545454545454544444545444445454444454544440000aaaa0000aaaa00008888000088880000aaaa0000aaaa000088880000888800000000000000000000000000000001555554015555540155555401555554022222222222222222aaaaaaaaaaaaaaaa2222222222222222aaaa2222aaaa2220000000000000000555555555555555500000000000000005555000055550000
|0,5=>0x8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a888888888888888955555555555555555555555555555554000155540001555400015150000151500002aaa80002aaa80002aaa80002aaa80002aaa80002aaa800022220000222200000000000000000000000000000000000000000000000055554444555544440000aaaa0000aaaa0000aa000000aa000000aaaa0000aaaa0000aa000000aa015555555555555555555555555555555555555555555555555555555511111112aaaaaaaaa802aaaaaaaaaaaaa802aaaaaaaaaaaaa802aaaaaaaaaaaaa802a800000555500005555000055550000555500005500000055000000550000005500020202020202020202020202020202020202020202020202000000000000000155555554040404055555555404040405555555540404040555555554000000000000000000000002aaaa2222aaaa22200000000000000002aaaa2222aaaa2225555555555555555555555555555555500000000000000005555444455554444aaaa0000aaaa0000aaaaaaaaaaaaaaaaaaaa0000aaaa0000aaaa8888aaaa8889540154015401540155555555555555555401540154015401555554015555540002a802a802a802a802a802a802a802a802a802a802a802a802a802a800000005555555555555555555555555555555555555555555555555555550055555500
|0,6=>0xaaaaaaaa22222222aaaaaaaa22222222aaaaaaaa22222222aaaaaaaa000000015554000155540001555400015554000155555555555555555555540155555400000000000000000000000000000000000000000000000002aaaaa802aaaaa800000000000000000000055550000555500000000000000000000550000005500aaaa0000aaaa0000aaaa0000aaaa0000aaaaaaaaaaaaaaaaaaaa8888aaaa8889555555555555555555555555540154015555555555555555555555555401540000000000000000000000000000000002aaaaaaaaaaaaaaaaa802a802a802a800000000000000000000055550000555500000000000000000000444400004444aaaaaaaaaaaaaaaa0000aaaa0000aaaaaaaaaaaaaaaaaaaa0000aa000000aa0155555555555555540000000000000001555555555555555555555401555554000000000000000002aaaaaaaaaaaaaaa80000000000000002aaaaaaa8000000054545555545455555454555554545555545455555454555554545454545454548888aaaa8888aaaa8888aaaa8888aaaa8888aaaa8888aaaa8888888888888889555555555555555555555555555555555555555555555555555551515555515002a802a802a802a802a802a802a802a802a802a802a802a802a802a802200225555555555555555555555555555555500005555000055550000444400004444
|0,7=>0x444444444444444444444444444444444444000044440000444400004444000002a802a802a802a802a802a802a802a802a8000002a8000002a8000002a8000555555555555555555555555555555555555555555550000555555555555000000aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00000000000000015555555401540155555555540154015555555554015401555555555400000002a802aaaaa802aaaaa802aaaaa802aaaaa802aaaaa802aaaaa802a802a802a800000000000000000555555005555550000000000000000005555550055555500aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00aa000154015401540154015400000154000001540154015401540154000001540002aaaaaaa802a802aaaaaaaaa802a80002aaaaaaa802a802aaaaaaaaa802a80001111111111111111111111111111111111111111111111110000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x430b9230103833e342070618b8930101820a486840e445120844d0c3e34207225428d081c89c0a246840e1851e203420328489840e44b9d1e1019c284820736005040668c8c2e24c040e54b891e1038628249840e1851210103910a4068406185091e1070614244040e182840608080
|1=>0x4258aad002880d080c30c14206840e0c30a1e4c2033818b891e1039500296042c5558b0aa46a80858a8a123c203380051d1e1018c149c684220c614124c2072a0051210108831628904069858028786842c0830a123c2252a0052426101861628f1d1a1018b0a886a12c5400a4034203
|2=>0xa24684225459720342030c2c5091e10386005098d081c8951478684067058a58a46842c54bb01a1019516506840e54d805e5cc0d080c597243c2163818ba71a10883165098d080ce02287480d080c00a1e4c2250654b9e2434203165d48d42a0b1528103835c5400a1220203040028d
|3=>0x2a0051d1e1019c005d20d080c30b1424784220800a124c203662cb891e1018616286842254d0c14249840e5460a243c20e06019091a103950028793081c1862824984061858a12602072a005301a10186165020706540801448203622c00a123c2030c30512203c203002878d0838186
|4=>0x220c5941a103833200a12080cd8b00146840e44a973c34203165c918080c5976c342032a2cf8d080c30b1448784220c61412342070c00b923010b021480784065461f1a10b020c2820334645802e24c04065458a243c20722005091a107061628e901a1018c2ed0684061858a403c207
|5=>0x3a3c2030c2ca091a10882005c78d081c1863e34b15722c00a241089a1600527244c203185dc0d080c58a1a103912ad4b9d1e10b020c1448d080c30b14747840e0c00a080ca811600a131a103830c146840e44a8c2e48784220c58554350a82c545092611b951628e8f080c30c2848984
|6=>0x63050d081c89c18286840e0cc8c144820336305973c34203042c5091a1038618142032a045802834203046c00a2034203040050d080c31a185cc0d081c1950a342160ce85944e342033800b981a1018228486840e4401440342072a005121e11283007c684220ca8b0a342110670597
|7=>0x81c1866a2890d081c88c0a342070618632243420706005201a103951828918081c180142440422545851a854162af828d081c1860a74684061858a7a3420304002bc1a10b0616c848d080c1000a406842c18a853a342160418509301018200ecf8d080c5800a48684220c58a4e74684
|8=>0x858a8c149c913085830b147490d080c60b14906840618580149ce8d0858a8c147880d0858a973a3c216385450f26103912a146842c0833e14206840e44a8a68406840600512080c08b0028793080ce0a080c301182c50d080c13f005d1a82c5558b149cf13080c5851a112830c2c50d
|9=>0x68342030c2c00a1e34203381801420342162a005092610395160050d080e20b0050e8d08581002e342160d0c58a3c34216041859484350962a00a411a10b1500ecf8d0858a8b007c68406545800a34203382c00a1a10199182ca128010b15005c78d0844195165138d080c10014a46a8
|10=>0x80c10014342038e2c00a1e34225065400a7a342032a2c01752354042c5458a124c2032a3058a246021604019091a10195160028d0858aad1600a1d1a1018b0014e8d08583151629012261018b00146842c08346284c684062c0141a11287065400a12602032a2c00a1a10895342c00a
|11=>0x8581061828904066c5801448c04062c0141a1019c04005491aa0b1518295291a10b15181448d080ca8b002848d0844a8c162820706b8a8b0028913085810c14d8684065458014a918f0858a8c64486842c0800a244c21638185851a101861720b981a10b151628e901a10b02005098d
|12=>0x8c506c00858a8014a87a80858a8c0a342030c3058a403c2032a2c00a1a10b020cd4512261018c16506840e44a806448684062c00a4e4c2162a30b8f1a103832a00a2a46350962a002921a10b020028e901a1018b005c78d080c1001448984220c5944e4c216045400a3c34203160028d
|13=>0x1a101861628e8f0858106005d6231a10b1516293921a10b0618286840654d8c165150d42a0b15005e48d5058a8b14342030c2da8a4e789842c5458a243c211062c0173a342163854594464d0962a005121e10b4c001490d080c580152c684065458015242162aac580144c6840e44a8b
|14=>0x894a8b00287930858e1514746842c0860a1234203662c0051a842162af800a92a46842c540171a10ace160054d1e10b020014684220ca8b2ea87a80858a8b1474784061858014103832a045802836004065400a1e3420706180051a10b15742c00a70342031600a091a101861600b89
|15=>0xc2cb891a1039516005181a103832a005272610b06162848d080ce0b0028e8d080c60b2e342032a685800a34211065460b149c913080c58014342032afc5801460684060800a129c784062c0054634b15a22c00a68406842c5400a9a3c20316005091e10395005d3921a10b06162848d
|16=>0x2a98d080c580143c684220c100154160d0858a8b29486842c5400a4e4c216045460578342162a2c00a3a487842c546321a103832a0190d080c1002e34203862c00a3c34203042c00a2634207065460a1a108832a2da8a3c342160c5458a263420304305343a3420316005131a1019c
|17=>0x2c5458a12342070c2c00a464d0962a30b921a1088316c918d4258a80144880d085810014101ae2a2c00a1e34203980050d080c31a1600a201a101951602b0d080ca8b005148d0858a802e486842c7030b149cf0d0858a8c1434207225460a548c6a12c5460aa834203160028d4258ad1
|18=>0x1a10b151600a341a10b022a005091a10186182ca101a10b062a00a0d4258ad800286841c0c30b14b06a80858a8b14246846e5458028746842c0830014789130858a8b144880d080c580149c80d0858a800a8c6a12c5400a54350a82c546142434211062c0174034211065458a588c6a8
|19=>0x16828d080c60b005d50d42a0b151628684220ce0c1628684065408b0028908085830b29346842c080144e34216041800a1e4c2163808a941a103830c00a1d1a1018616005341a1019c160028d089419516005273a3420316002aa1aa02162a2cba73c342162a2c50d081c1991602c9f
|20=>0x261018b00291842c5558b005d60d4210b1516286a82c56d8c14806840e545802e9c90d080c580141019502305801474684067058015402162aac58014406842c70a80144c68406dca8b2934684062c01412342072a00509261018216005121a107031600ba31b294162a2c504065408b
|21=>0x80ca8c1474684061860b1420684061858a1a10195bc2c00a20342160c5460a1a101dd160055c1a1018b0028e8d0858106182840d08581062e8cc042c5458a2434211063059754365042c5458a6848684062c00a40342032a305941a1088304005235058aab16005121a103911600527
|22=>0x2c0830a2434225062c00a58350a82c5458a1a112830c3058a24202031600549584c2162a2c523523c2162a0052a1e10b15185c80d0858315162848f080c10014746840e0c5801434203be2c00a12202032a2c01426342163808a8a243c2163800b9e24342162a2c50d081c1861828793
|23=>0x42a0b1518287930844195167c6842c18a8b0a350a82c545621a101951600b8d5010b15562c52c1b282162a2cb921e10b061629a0d080c580143c684067000a3a3c21638540051a58ae1182c014244c2160c2c50d080f00b0028793080c30b152550d0858a8c1420684220ca8b143c984
|24=>0x858a8b1434216041860a0894195022c00544342162a2c00a1a10b068630bd01aa02162a2ca12261018b005cc0d085811514a948d4258a8014112835c545802824984065458014487842c70300148e5162aac58014342640654580284c6842c0831792b06842c5458a1a101e3160028d
|25=>0x858adb18005551a1018b002848d080ca8c160050d083819516005101a10b15160050d080c30c1628e8d085810b005cc0d0858a8b15086a12c54580ca342032a2c00a82342162a2c00a928c9842c54580144a0042c5458014746842c18a8c162938d080c10b002840d085831517946a8
|26=>0x2c54600148c7842c546001480684220ca8b007c6842c54580144c6840e0ca8b002890d084418b002898d080c10b00289080858a8b002848f080ca8b005c6842c0830b14486842c0860014486842c7030b00286844a1c19516005201a10195160050d0858ae716005661a10b15160050d
|27=>0x3c342162a2c00aa0365042c5458014342072254580d45098d0858a8b00295231a84b1516005231ba4b151600b8d0858adb16005272610b022a2c00a3a487842c5458014342162ba058028a918d0858a8b0028684067010b002890f08581001448684063058014342032b14580149c684
|28=>0x2c54580284c6a10858a809e506842c5458014a86a15058a8b002920f1a101951600ba71a10b15160050d0844195182c50d0858ae0160050f2610b062a2c5232684b151600a2a1aa02162a2c00aaa4c2162a2c01754354042c545972434216042c014464c2162a2c00a243c2031600527
|29=>0x14342250654580143c6840e0ca8014a86ca0858a8b005048d080ca8b002878d080c1001420684065458014342162bb058014b06a10858a8b00bcb8f1a10b1516005501a10b1516005341a10b15160050f1a10b1c2a0050d8010195160056b1a10b15160054946342162a3000a4636528
|30=>0x14a86a80858a8c165d38d08581151600b8d081c1951600a121a1018b005c684060858014a46842c54580648c6842c54580143c6842c18a8c148c6a12c5460028342162a645801434216c65458015486842c54580148cc042c54580287490d0858a8b005090d085810014354162b6c580
|31=>0x154248d0858a8b005d18d4258a8b0029a0d085811516005101a10b062a2c00a1e342163808a802f546842c5458014746842c0830b002898d4210b151828e8f0858a8b005098d0858315162890d085a60b002a4934210b1516002a31a10b15160051e24342162a2c00a1a112832a30580
|32=>0x1600b8d94a02162a2cb8d0858abe160052a1e10b15160050d080e18b00146a10858a8c002848d081ca8b002b68d0858a8b00509130858a8b00286840654d0b002a68d085810b00286840e0c30b0028793080ca8b00146a10858a80144c6842c5598b14487842c546002e3c6842c18a8b
|33=>0x858a8b00286a80858aab160050f1a10b1c0c540730a342162a3058014487842c185802e8c6a82c545f11a10b15160028d0858e15160050d0858a99182ca271a10b022a00a0d081c1950028e921a10b15182ca0d080c100de342162a2c00adc342162a2c00a3a4c684062c0462834203
|34=>0x54350962a2c00a1e4c2162a30a2a1a10b15160050d085831516d42921a10b15160054958342162a2c0051a10b062a305b224342162a2c00a3a48684062c01426342032a2c0141a854162a00a0d0858e022a0028d0858315162ba130858a8b002878d080ca8c00286840730580152550d
|35=>0x1a10182160050d080ca8bae0028d9410b151600bf41a10b1516005121a10b1c16005541a10b15160050d42a0b15182a80d5010b15160190d08581150029a1d1a10b1516005181a10b022a0055046342162a2c00a92342162a300051a10b157c2c00a46365162a2c00a1e34216041800a
|36=>0x160050d080ce0b0028e8d0858e15160050d9410b15562c00a1bd42162a2c05a0a342162a3058014342032a2da8014d06842c70a8b002939d1a10b15160028d080ca8c160051d1a1018b00291880858a8b0028e921a10b02160050d0858343160052352342162a2c0051a101951600509
|37=>0x160050dd210b15160050f1a10b062a2c00a1a10b1517c00651a10b151600ba31a10b15160050d0858ad816005131a10b062a2c5121a1018b00286842c54c8b0028e921a10b15160050d0858add160055c1a10b151603b0d0858a8b0028684067060b00286842c5558b0029a121a10b15
|38=>0x14206842c545802e342160c5458a463c2162a2c00a2434216042c00a46342162a3058014342162a2fb8014746842c54580148c6a82c5458014360042c545800a5c6842c5458014342162be458014365280858a8b01e0b8d0858a8b002898d4210b1516017971a10b1516005122610b15
|39=>0x2c18a8c162938d0858115160050d081c195160050d080c10b00287930858a8b00286842c70a8c160054946342162a2c00a1a10b1c2a2c0171a842162a2c00a4e3c6842c545802e486842c5458014a86842c5458014342162acc58014350842c5460028342160c54580144c6840654580
|40=>0xc2c00a84342162a2c00a1a10195182c00a1b282162a3058015246a10858a8b00286ca0858a8b00286842c57d0b005098d0858a8b002878d0858a8c00286a15058a8b00286842c7011516005121a10b15182c0171a101951600b8d5010b15162aa8d0858a8b01a8a0d0858a8b0028684
|41=>0x50d0858a8b00286842c5460b002868406545802e342162a2c00a24342162a2c00a26342162a2c00a1aa02162a2c00a46342162a2c00a1a10b062a2c00a12342032a2c00a923c6842c5458014342162a2da800a342162a305800a342162a2c00a1a10b02
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x786039301b180ccc060602d30151809cc0486021300f1806cc030601530091803cc018600930031800cc0006
|6,0=>0x11ab88bd8450e221710d3884dc418e20570ff387ddc3e0e1e970f13876dc3a8e1cd70e3386fdc370e1b170d53868dc338e19570c73861dc300e17970b9385adc2c8e15d70ab3853dc290e141709d384cdc258e125708f3845dc220e1097081383edc1e8e0ed70733837dc1b0e0d1706538311817ae0b67057b82a1c142e09a7049b8231c10ae07e7
|6,1=>0x1f6b8f99c7bee3d871e8b8f29c788c3bd71db38ebdc750e3a171cd38e4dc718e38571bf38dddc6e0e36971b138d6dc6a8e34d71a338cfdc670e331719538c91863ae3167187b8c21c602e2fa7179b8bb1c5cae2de716bb8b458594e2c3715e38ad5c55ce2a7715038a65c524e28b7142389f5c4ece26f7134b098d84bac256712830925c484e23c6
|6,2=>0x1155c89ce4477220390e5c864e42b7212b1079c82ee4107204b9009c7f6e3f47
|7,0=>0x31b418ba0c4ee61f830c39845cc13060272fdb97d1cbdae5e672efb975e0b9f05c782dfc16e1cb6105a882d0b96660b26c58b82c1c15f1caeae56d82b2c15760aab054e72a3414fa0a6ee52f8293c14858a3305118284c140609f304f182753938a09b6e4d47266b9316097ce4b77257c12a1c942e49a7249b922e0908e47c823a411b208c9045c8
|7,1=>0x40ec2056101ce80683ff41fda0fdd07e773efc1f61cfa107c883e041ee20f62e7a983d0c1e660f24e78b73c1c1dee0ee8e76d73b2c1d760eab074e73a3b9d01ce710730839441c85ce330711838539c0a0df6e6f38375c1b8e0db706d3836639b15cd7b06b58356c1a99cd3ee698734841a220d0106788338419a5ccc3065a7329b9931cc8ae63e7
|7,2=>0x503427fdd3ef09ef84f3c277e13b0e9d174e4c27061374e9b284d54268a1335099284c54260a12f5097284b54258a12b6e95474a64251212790934849642492123ae9158486c241611fb08f584773a39dd1c0e8d88468ba329d18508ba8459ba2b1d149089c844aba236110ce87f743c3a1c210d10861742cc214610930842741e320d5d05b08258
|7,3=>0x5f63af9997bd0bd685e742f1dd780ebb975d8c2ea61744eb9b75ca3ae3217090b7d75bac2db616cb0b5e75ab42d3a168eeb3f859c3acc21652eb21858cc2c49d6150b03757e3abd215daeae5856ec2b59d59eeac785603aae5d5630aa98550c2a661524ea8a8541429edd4e70a6b85323a97214a90a4c8522428f214690a2c8512ba879d42d0a0e8
|7,4=>0xc6d8632c3179d8ad0c4f76243b10218710c3086144308218310c117604c3009d7f6ebf38
|8,0=>0x73a439b21cc72e5a97294392a1c850e3a8719438a65c430e198708c38261c04edf996f84b7a21bbf2dd696e74371a1b7b2db496d64368e5b370d9476c6436121af90d7486b5cb591dab72d5386a5c350e1a770d3476964348e5a352d1286854340a19f50cf376754b38a19b50cd37665c3311d9790cb57656c329259390c939645c320e18f8ec757
|8,1=>0x83f3c1da20dd1066882fbc15e209f1047881fc40de205f1027880fc4061e0211008880043fde5fdf0fe697eecbf525f990fc397ddc3ece1f570fa387cd4be4a1f132f8097bbcbdba5ecd0f5f77ac3bd421e910f40879c43cc21e510f20878c43c3e5e10ef00877c43bc21dcf2edf876c3bb421d910ebf975b4baba1d4d0e9e874b43a3a1d0b2e7c9
|8,2=>0x93f4c9dde4dd3265992ec495264991243991d4c8ca2456f223890d4c84a2413320278fd447ca23d511e288ed4474a2396f1c298ddbc6ca635511a198ccc46462313118188bcc45c9e2d5116288ad4454662931141889cc44c62254f122888dbc44e22171104787dcc3ca61d330e0986c44345e194f0c2885d442ca2156f0a2984e34255e11b10858
|8,3=>0x12a6894f44a5de51f12878
|9,0=>0x5296293934948a4645215e8fb14758a36c519268b734538a25c510e287714338a154d0866834f4137a05c500e27f713f299f544f8de7b713d299e4ccf06277313b099d444e822731139089c444e0226f1137179b4c4d8626b1335089a444d0226711330899444c7e662f130e998344bfa25ed12ed9972c4b79e5ad12ce896344afde56f12ae9
|10,0=>0xa71c5371e9aaf4cd8a62c52f6296b14ad8
|11,0=>0x14eb7
|_,_=>0
def wAt:=mkWire dB 123 255 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x222d06012c551a940e011a3116011a3116011a2d2c550c2d2a011a0d062d2c551401542f14312a31002d24011a2d002d2c551a552c552c551e011a2d0631002d2c551e0d1a2d2c550a8c1431002d12011a0d2c552a31062d1431002d06012c552c550c2d1a1914012c552a0114012a011a0d062d2c552c551e011a2d1a311601
|1=>0x1a0d2c552a2d2a0114d51a32160114011e032c553a2f1a4506012c550c2d2c551a192a011e0d14011a2d2c552a012c551a0d2c550c2f1a0d14011a2d2c552a0116012c550e032c551a0d1a012c55142d1a960e01002d2a011a0d062d2c552c55480314012c552e551e031a2d1a2d0c2d14012a012c550401142d1a012c552a2d
|2=>0x1e031a2d1a1914011a2d2a011431002d2c552a012c551a012c55142d062d1431002d06012c551a2d14012c55143116011aa1082d08011a2d2c551a192a011a0106012c55142d1431062d002d06012c554e031a092a2d2c5514012c551e031a551a2d140114012c552a0114d51a3216012c55142d2a2d1e031a551a2d14011201
|3=>0x1601143116012c55242d24011a55062d2a31002d06012c551a1a062d2c5516012c551e031401142d04012c551a092a2d1e031a2d2a2d2c5514011a4506012c550631002d2c5514d51a322a311431002d06012c551a1914011a2d2c552a01142d2a2d1a0d06012c55062d14011a2d2c552a01242d16012c551a552c5514013055
|4=>0x16012a2d2a01262d1a011a012c551a2d04012a2d4e032c551a3216011a55062d06012c5514311601062d2c552803142d1a4506012c551e031a2d1e011a2d08010a371431002d082d14312a011601062d2c551431002d2c551a192a010a48143116012a2d28032c55142d14313a2f2a2d1a192e2d14012a011e031a2d14d51a32
|5=>0x2a014e031a092a2d082d4603142d1a11142d8055262f1a0114d51a3216012c5514d51a3216012c5514312a3116012c5516011a1a2a01262f1a551a01142d140106012c551a2d142d2c551a092a2d542f1aa10801242d1a011a552a01160124012c551a551e0d1a2d2c552a011601242d24011a5514010c2d1a192a012c551431
|6=>0x222d06012c551add222f06011401542f1aa116011e031a2d1a552a2d28032c55142d1a192a012c55142d1a192e2d14012a011a011a55143116012a2d2a011a0128552c55142d0e01062d2c55142d1e031a2d1a1e062d2c551a2d2c550c2d2a01142d3a2f1a192a012c552b15260f2c551a0126551a01142d2a2d1a0a14012a2d
|7=>0x2a2d2a2d2a01143116011a551a4606012c551a552c551e031a2d142d2c5504012a2d462d080116011a11542f46011a11143116012c55002d1a940e012c55002d1a011a552a2d460116011a111a552803142d2a2d0c2d1a011a552a012a012e2d2c55140114011e031a2d3a2f1a192a01142d1a012c552a2d2c55260a1a012a2d
|8=>0x142d262f1a011a2d1aa108012c552a011431160112011a0d2c551a3216012a2d2a011a0116012c551a55062d06012c55142d1a5528032c55142d1a01242d1a55002d1a2d062d2c551401082d4601142d1a112e2d14011a552a2d2c553a2f1a192a011a2d2a2d2c55140106011a012c551a55142d1a011a092a2d2c554e031a09
|9=>0x2a011a0d2c55142d2a011a0d2c5514011a2d1a192a019203462d1401002d242d1a551a4606012c551aa10801142d082d1e111a2d140108011a32002d2c552a014e031a092a2d1a5506012c551a2d0c2d14011a192a011a111a01142d082d04031a2d1a552a2d143116012c551a55402f260d1a011b2a42011a85082d2c552855
|10=>0x2c551a2d242d1a5514012a010e01062d2c551a011a2d04012a2d2a2d24011a5516011a0d0c2f2c552a010a371431002d082da02f9201462d1a119e5b2e3d1a2d140124031a2d1a552a2d1431002d06012c5514011a2d1aa108011a2d2c551a192a011a960e012c55142d2c55262f1a01062d1a2d2c552a0130552c551e031a2d
|11=>0x2a2d16012c551a012c551a192a011a012c550c2d2a011a0d062d2c5514011e031a2d242d1a011a552a0104012c552a2d2c5524011a5516011a1e062d14011431002d06012c551a01242d2c551a551e4606011a2d2a2d2c551e031a2d1a0d2c551e551a2d0a13143116011a113a2d3a2f1a192a012c551a2d24031a55062d1a0d
|12=>0x62d002d06012c554601002d1a11aa012c55242f1a550a131431002d082d2c551acd0c2f2a012a2d06012c551a2d92039201462d1a11142d8011262f1a011a011a092a2d0a481431160124011a55002d062d28032c55142d2a2d28032c55142d1a0a2a2d2c5514014e032c551a092a2d1a012c551a32002d68033a2d1a192a01
|13=>0x16011aa1082d08011a5506012c55142d1a4506012c551401462d1a112a011a0d062d2c551a01082d002d1a11060114012c551a55082d1a112803142d3a2f24011a551a940e01062d2c552c5504031a2d2a2d2a011a1e062d2c551a4506012c55142d155d06322c551601142d542f46011a110c2d1a5514012a014e03242d1a55
|14=>0x2c551431242d24012c551a551aa114311601080114014e031a092a2d062d1a1a2c552a0114d51a321601142d2a2d1a0d002d2c552a01142d3a2f1a19142d1aa2082d08012a010e03062d2c55a003542d1aa10801222f06012c55142d2a2d1a192a014e03242d1a553a2f24012c551a55682f4e011a092a2d1431082d002d1a11
|15=>0x24031a55062d1a0d2c55142d1a0d1a012c552a2d1a550e03062d2c551401502d08011a111a960e01062d2c550a552c55143116011aa1082d140108012a31002d06012c551a960e01062d1e011a2d1a552a0124031a55142d2a2d142d2a011a092a2d04012a2d1a01062d2a012c55142d142d2c551a192a0104012c552a2d0631
|16=>0x1a55002d06012c551401502d1aa108011a4506012c552a2d06012c55142d502d08011a550601062d2c551a091a012c552a2da037463116011a11140192031a8516011a860801082d1a4506012c551401242d2c551a551a9606312c5516010c2d2c551a192a01a037463116011a110c2d3a2f1a192a01222f06012c552c55142d
|17=>0x1a2d26552c551a012b5d06322c5516011e011a2d04011a01142d2a2d0c2d1a2d1a552a0114014e03242d2a011601062d2c551a01002d2c551a2d002d2c551a192a012c551e011a2d2a0134011a1e062d2c553a2f1a192a011a7204012c552a2d243316012c551a551a1916012a2d2a012a2d1e011a2d2a0114011a111e031a2d
|18=>0x1a552c551a2d04012a2d0c2d1a2d1a192a01b4130a5514311601142d1a011a552a0186011a0a2c552a2d1a011a2d2c552a014601462d002d1a111a31002d1a011a2d2a012a2d1a550e01062d2c5592031a85082d002d2c552a011a3116012c551a5592031e111a2d46011a1146011a2d002d1a1114013a2f1a192a2d1a0d2c55
|19=>0x8012c551a551a01142d14012a2d1e031a2d542f1aa108011a941a011a0d2c55142d0c2d1a2d2a01083116011a321601142d1a012a2d2a0192031a851401082d2c552ad51a32160108011431002d082d2c551a2d2a0114d51a32160108011431002d082d1b2a502d1401420192031a85082d14011a2d1a552a01243116012c55
|20=>0x82d2c55242f1a5516011a0d2c550e03062d2c553a2f1a192a01002d2c552a011a192a2d2a0114011e031a2d4603082d1a112e2f2c5514018055262f1a01462d1a011a111a55262f1a01002d1a192a012c551a092a2d1e011a2d2a012e2f1401080116012a2d2a011a960e01062d2c550a8c143116011a0a002d2a012a2d1401
|21=>0x142d1a112c5504012a2d1a2d1a552a2d16012c551a55260f2c551a01242d1a55002d1a2d002d1a111a4506012c5514d51a321601062d2c551a0106012c551a551a012c552a2d1a311a5516011a0d2c551a2d14012a2d2a0116011a552a2d0c2d1a552a010e01062d2c55260d2c551a01b02d1aa20801842d46031a111a86002d
|22=>0x1a2d1e551a2d1401002d06012c5586011a0a2a2d2a011a2d1a011a01082d1a111aa1142d08011a01242f1a551aa11401080114011a552a2d1a111a01142d1a2d2c551a554e031a092a2d502d08010601062d2c5528111a01142d4601082d1a114203082d1a111a861401082d1a011a092a2d1a2d24011a551e1a1a2d2a014601
|23=>0x142d2a2d1a860801082d0e01062d2c55062d2c551a2d502d1aa108011a0d2c55142d1a2d2c552a2d262d2c551a011ea21a2d080192031a85082d2e551a2d1401463116011a1124311a5516011a2d04012a2d2c55262f1a011b3104032a2d462d002d1a11502d08011a111a01142d082d284d1a01142d1aa1082d08011e0d2c55
|24=>0x26551a2d1a012a011a01142d04031a552a2d1a011a85082d143116011a114e03242d1a5506312c5516011aa11601080114011a092a2d062d2c551401142d2c551a552a2d2c551401542f46011a111a112803142d16011a2d2a01082d002d1a11142d1a1a2a012ad51a3216018011262f1a011a111e031a2d142d24011a551a55
|25=>0x1a2d1a011a0a2c552a2d1431002d082d1a0d062d2c55463316011a111a551a01142d1a1e062d2c552a2d24031a55062d2c552a012c551a2d1a011431002d082d0c2f1a012a011a2d1a55002d1a2d14012a01462d1a111a111401082d4e011a092a2d3a2f1a192a011a2d04012a2d1401242f1a552a2d1a192a011a01002d082d
|26=>0x2d2c551a2d04032c552a2d4601462d1a111b2a502d08011a2d0c2d2a010a11143116011a2d1a552a011a111401080115c91e131a2d14312a31160116011a1a2a01142d1a092a2d062d2c55142d24011a5516012a2d2c55142d15c12a3216011ba54203082d2c5526551a0128552c55142d502d140108010a372e2d14012611
|27=>0x142d2a2d1a192a012a2d1e031a2d463116011a11462d002d1a110a372e2d1401083116011a111a2d2a012a2d1aa1082d080116011a2d1a011aa1142d08011a3216012a0114311a5516019203462d1a112a011431160128031a55142d24012c551a551a012c55142d0801142d082d0401142d2a2d2e2d14012a01462f1a011a11
|28=>0x2a011b2a502d080108d51a3216010a55143116011a322c5516010c2d2a01242d24011a552c551431160124012c551a551a3116011a1124011a552a2d1a0a2a012a2d542f46011a112e2d2c5514011a0d2c552a2d06322c551601143108311601462f14011a1104011a552a2daa01242f1a550801002d082d542d1aa108012803
|29=>0x16011a192a0108011a11262f1a012e2d140126131a01502d08012e3514011a01082d2e5514011a551a014203082d1a2d2a012a3216012e2f140114011a111aa208011a012a012c551a551a1a2a0124011a551a720c2d2a0124331a55160115dd083216012c552a3116011b2a502d080124311a55160104012c552a2d0c2d1a19
|30=>0x80126571a011a01142d002d1a2d082d080104012a2d1a5516012c55140114010801242f1a552811142d16012a011a092a2d062d2c552c552a2d1a2d1a012a311601462d1a110c2d2a011401082d1e551a2d1a55140146011a110c2f2a01002d082d142d2a012c551a01262d1a0114012a011a2d1a111a552a2d16011a110832
|31=>0x16012c5514011a551a0108011a112a011a0d2c551e111a2d1a321601143116012e2d14012a2d2a0146031a112c551601083116011a85082d502d
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x418000000001e202940000000000001540208022000000000010000
|6,0=>0xfc61e5400007720ec200003a880000e461b9034a86810ca6181400005e20ba200002e08584000000002b100000aa2000000000000000145028080000000138800004a408c81144202800007a6000000003b207240000000037206680bd000002d20564099412882410444000000001f3038600000c98163
|6,1=>0x25484a089299232242447148ba9125000043cc85a1092208a40887f98fd21f283d14789800000003c04000000000003bc476900001d0a38d40000e031ba636c86b28d15198a31d4000000018682f940000ba416c82d440000b2315aa2a8c52a8000142827500000000130a24d447288d1110a21c44308815
|6,2=>0xa12141127a84ec8000000026ca0000000000026a24d0499112e4
|7,0=>0x436885d109a20f4416881d101a1ff43f687dd0f9a1ef43d687a0cf299e413c2677500001da33ac87490e721cb339067110e021bd337466dccdb09b2435e60000d5a1a7434a46850cea199432e4650c0001904318862c4c3a18342fe85f0cbc217442e265b50b4a16542c285750aca15632a485390a521464
|7,1=>0x6084c0117e22f935ea8bc517792eb45d06b911709add45b28b58d6922ce45948b1916122be45748adcd59a2af45568a9d151a29f45368a5d149a28f45186a211422000050089f113c227534e469bcd361a6844c8898112e9a5944aa8945126a249448c69091208a3d447468d91199a2f4456889d111a21f4
|7,2=>0x7dc8fa91f323e247bc8f6cdeba3d3479e8f30de423c447826ef8ddd23b647648eb91d59ba9274a8e88dcf239a472c8e4cdc7a38c37108e111c0237c46f08dd11b9136e46d48d991b1235f36b68d5d1a9a34f46968d1d1a1a34036788ce4d9aa331465a8ca5192a321463c6c6cd8c1b1446208c3118423062
|7,3=>0x9a4933900004cb398e930d25fa4bb496e92cd257a4ab494e928d250949d49329258e499c8f49187228a43248338fe91f0e3c247628e491b92359c6748c6917d22da45748a8714122624484888910121e2438400010d4e18a42f2856909d211a42038389064e0aa411481a9025202a40237fc8fe91fb23f24
|7,4=>0x5084a0a740527f94fb49ee93d0e798cef49d873a8a7414e449c0937126c24d62
|8,0=>0xb907714ee11dbf3b7876e4edb1db33b6076b4ed51da73b487684ecf1d9b3b325658ec99d903b1a7628ec39d843b0275f8ebd9d783aea75c8eb79d6c3ad27598eb19d603aba7568eab9d543aa27538ea59d483a8a7508e9f9d3c3a7274d8e999d303a5a74a8e939d243a427478e8d9d183a2a7448e879d0c3
|8,1=>0xd0e7a10f409e7e3cf679e0f3a9e723cde79b0f349e663cc67980f2e9e5a3cae7954b291e4f3c987924f231e433c8078f4f1d1e373c6878c4f171e2b3c507894f111e1f3c387864f0b1e133c207834f051e073c087804eff1dfb3bf077d4ef91def3bd877a4ef31de33bc07774eed1dd73ba87744ee71dcb3
|8,2=>0xe8a7d08f9f9f3c3e727cd8f999f312e5c7cacf941f253e447c7cf8e1f193e2c7c4cf881f0d3e147c1cf821f013dfc7bf0b7c9ef63de67bc0f769eea3dce7b90f709ede3db67b60f6a9ed23d9e7b30f649ec63d867b00f5e9eba3d6e7ad0f589eae3d567aa0f529ea23d3e7a70f4c9e963d267a40f469e8a3
|8,3=>0x7543ea27d38fa59f483
|9,0=>0x1f4cbe897cf2f9a5f2cbe497c72f8a5f0cbe097bf2f7a5eecbdc97b72f6a5eccbd897af2f5a5eacbd497a72f4a5e8cbd0979f2f3a5e6cbcc97972f2a5e4cbc8978f2f1a5e2cbc497872f0a5e0cbc0977f2efa5decbbc97772eea5dccbb8976f2eda5dacbb497672eca5d8cbb0975f2eba5d6cbac97572
|10,0=>0xfb83f6c7ed0fd91fb03f5c7eb0fd51
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 15
def pmP:Nat→Nat
|0=>0x10100000000010000000000009800000000009500000000009000000000008800000000008000000000007800000000006400000000006000000000005600000000005100000000005000000000004e00000000004800000000004400000000004200000000004000000000002000000000001800000000001400000000001100000000001000000000000c00000000000a000000000008000000000006000000000004000000000003000000000002000000000001000000000000
|1=>0x201000000000200800000000200400000000200200000000200000000000185e00000000180000000000140200000000140000000000115900000000105000000000101800000000100100000000081200000000081000000000080c00000000080400000000080200000000080000000000050000000000041800000000041000000000040200000000040000000000024800000000021c000000000218000000000202000000000200000000000150000000000118000000000108
|2=>0x1000080000001000040000001000000000000a301400000008011800000008010800000008010200000008010000000008004400000004240800000004100000000004001000000003f90400000003f15500000002c01500000001995500000000944900000000900000000000801800000000801000000000800800000000800100000000800000000000604c00000000420000000000404800000000401800000000400000000000300e000000003000000000002204000000002014
|3=>0x80001000000080000a0000008000080000008000030000008000010000008000000000006000150000004184d90000004014d00000004014980000004014180000004010980000004004d800000040049800000040041000000040009800000040009000000040005800000040004000000040000000000020424c00000020024400000020020000000020004400000020000800000020000400000020000000000018084000000010104000000010100000000010001200000010000c
|4=>0x102915900000101955b00000101915d00000101915900000100b95400000100a64d0000010095db00000100955f00000100955d00000100955b0000010095590000010095490000010091d900000100915d00000100915b0000010091590000010090490000010084da0000010081dc00000100815c0000010081490000010080da00000100515300000100115d00000100101100000100015300000100014b000000881002000000880098000000801018000000800018000000800012
|5=>0x14095d900000140955b0000014094d900000140945900000140935d00000140915f00000140915d00000140915c00000140915900000140849b00000140845a00000140825800000140815c0000014080da000001408092000001209b1c00000120935d00000120125e0000011011510000010b915f0000010b915b0000010a91de00000108941c0000010891df0000010891db00000108915f00000108915d00000108915b00000108915900000108885500000103001000000102915d
|6=>0x88810c80000088800d800000880109800000841904900000840105000000840005000000840004000000808908900000808109800000808000800000802909900000801905900000800808800000800008800000800000800000500915b000004039159000004030008000004000100000003001000000003000000000002009449000001a0015c00000180915b0000018091590000018081590000016095df00000148915b00000148905900000148805900000148801c0000014095dd
|7=>0x1100945900001100915b00001003915d00001003915900001001e15d0000100010000000098991d90000098891dd0000098891d90000098890d90000098881d90000098080d800000948905b00000948840300000940915900000940905900000940805800000920915d0000092081580000090891df0000090891db0000090880c900000908805a0000090391d300000900949b0000090091d900000900915f00000900915d0000090091590000090090d900000900805800000900115c
|8=>0x4000010000004000004000004000000200002502915900002501855900002108915b0000210091590000210085590000200004100000200000400000200000100000194090590000192091580000190291d900001902915d00001901915d0000180391d900001801814e0000180094cb00001142915900001141915d00001140945c00001140945900001140935c0000114081d900001121d35d00001102d95d0000110291d900001102915d00001101955f0000110191d90000110094d9
|9=>0x4840104800004840005000004800848300004800105800004800004800004800004000004148905b00004140915f0000414090db00004140805c00004120931d00004120821d00004108955f00004108955b00004108945b00004108941100004108940900004108915b0000410890db00004108855b00004102911900004100955b0000410094db0000410094540000410091db0000410090db0000410090d9000040400040000040028119000040009019000040001000000040000102
|10=>0x8502915900008501955b00008403915900008403815900008108915b00008108855b00008100955b00008100915900008100855b00008001815900006108815b00006100915b00006100815900006000015800005942915900005900905c0000510291db00005040909b00004940915d00004940915b00004940915900004940905b00004940905100004940904900004940904300004940805900004940805100004920915f0000490090db00004900905900004900804c000048401058
|11=>0x1250195590001210095590001210091590001210085590001210085130001200005500001200005180001200004580001200004500001200004180001200000100001050291590001010091590001000800180001000005580001000004180001000004100000e100915b0000e10091590000e100815b0000e100804b0000e00280590000e00001580000e00001500000e00001480000a50281590000a500854b0000a10884030000a108815b0000a100855b0000a10081590000a0018149
|12=>0x10040181410010010b91db0010010b915b00100100915900100000905900100000010800081500005900044941915900044940815900040901915900040901815d00024120991d00024020122d00021101d95d00021101d95500021001f955000201209b1d00020100995d000201009055000200000a0c0002000008460001850191590001840391590001810a915900018108915b00018108915900018108815900018100915900018100851b000181008159000180080058000180018149
|13=>0x4000000000002000000854902000000010001200302915901200202104801040303901001040303801000c01102f34d00821021db1d00801022c35d00420118915d00420118101700420100b95500420018085000400108b15500400104975d00400100b35d00400100904d00400004264800400000080600240301d15d00240201001800201801905900201503915900201502115900201403115900201103d15d00201003d1dd0020100391d90011810b915b0010810b915b0010090b91db
|14=>0x88201502915980201501115940000500915b320001030110200121029559200101029159122001019159122000000118080125029159080019419159
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x280000010300000000300404000000800
|6,0=>0x2b810120402080a20c003e80c28158109204098501c000008c0000000085a000892c8809030ec141b23020000036934001b0300800051a81456000d820000029934980d060088e4a2a0040065010003200048302c020702c0024118000410000005a0011800000000094047a0003400cb0d009a2002f800002d0200000040d030002832ac40402020000006070019a09
|6,1=>0x180203010f400698000000360080813
|7,0=>0x1e8cdd27f6e9145f4533ac8725c6d90a8279671f168b09f019b0b613e680399a414ade6f18a506000481af6c6f8fb647f76b530648150659692fd2a80404ccb7aa8a8c25ae413b47185df5270a826a748c55eba6cf5b5dbcce2318bc81b176a35f49bd37c39c05f2a8b0d346338020e2b20c3f54643303800d2478090a786a9b6c0ca270d9d08a2790f2e2aa01bc2e35
|7,1=>0xcde277e5800d398cf41a285feed470887b3d3045b59288b026f6379a0c90c666b3aa42a2489d1526315325707697c8c800c3d151f60609bbc3f1fc1825b4874080cf63e846dcd58cb92b773700e18a60dc9db5b22703e984262b8f0603c29130df018d0f818e51e0e806b979241581c25b26e2ac1b48387165444a2d073a4ddd5679f4684807be9d3e8e250cac4cdc2e
|7,2=>0x5f66b9e3b0a91454ba6869018bd0d8f221563c
|8,0=>0xd5e234f7c776871f1984e39e18e955764b39a783ecc383ab7e1873ad2f600f0b3b3e79b4bccfe0b0b88a41392db1c054695a99df8182dae504306a24cee752dda4590f64bb8ed181af722f193a8ec5c729b15e579c58a46e714003ecf8578b0d7e7e7749de9f14c5d2629555d6e7075af72cc66b1279b7b65b0b9c66aebb5763920a85ecaec2a04ada17876a6cc788eb
|8,1=>0xc75bb41d890423e1045a51ee94a7e1aab1812c39b8ae3a557a9b451c7b2df0f20cb2028459b669b0b43be4cafec37e5a73c9c6040b14f9d1c625ce41116dafc69bf078fa0936632477883fab0c5
|9,0=>0x2bedca3ceea1cd195361edb864b27a5d847bb1207745bf0d4f4bc739254ebb6bdebf4c865f9275b80a626504aa3c634a45fdf52ba84b61b9359de2fab1275227e39734cae526bf
|10,0=>0x522493eb74b5ce3293
|11,0=>0x90
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 48 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_250 10 roots_250 ops++addP pm 1 dom_46 5 roots_46 ops++addP pm 2 dom_248 7 roots_248 ops++addP pm 3 dom_238 9 roots_238 ops++addP pm 4 dom_190 9 roots_190 ops++addP pm 5 dom_170 5 roots_170 ops++addP pm 6 dom_126 9 roots_126 ops++addP pm 7 dom_124 6 roots_124 ops++addP pm 8 dom_246 9 roots_246 ops++addP pm 9 dom_232 5 roots_232 ops++addP pm 10 dom_110 6 roots_110 ops++addP pm 11 dom_186 7 roots_186 ops++addP pm 12 dom_252 9 roots_252 ops++addP pm 13 dom_122 7 roots_122 ops++addP pm 14 dzo_216_32 5 roots_216 ops++addP pm 15 dom_244 8 roots_244 ops++addP pm 16 dom_158 7 roots_158 ops++addP pm 17 dom_94 7 roots_94 ops++addP pm 18 dom_106 5 roots_106 ops++addP pm 19 dom_62 6 roots_62 ops++addP pm 20 dom_58 5 roots_58 ops++addP pm 21 dom_234 8 roots_234 ops++addP pm 22 dom_236 6 roots_236 ops++addP pm 23 dom_60 4 roots_60 ops++addP pm 24 dom_222 10 roots_222 ops++addP pm 25 dom_220 8 roots_220 ops++addP pm 26 dzo_214_32 6 roots_214 ops++addP pm 27 dom_188 6 roots_188 ops++addP pm 28 dzo_220_32 6 roots_220 ops++addP pm 29 dom_230 6 roots_230 ops++addP pm 30 dom_174 6 roots_174 ops++addP pm 31 dom_182 6 roots_182 ops++addP pm 32 dom_118 6 roots_118 ops++addP pm 33 dom_184 4 roots_184 ops++addP pm 34 dom_156 5 roots_156 ops++addP pm 35 dzo_218_32 6 roots_218 ops++addP pm 36 dom_30 4 roots_30 ops++addP pm 37 dzo_222_32 7 roots_222 ops++addP pm 38 dom_120 4 roots_120 ops++addP pm 39 dom_202 7 roots_202 ops++addP pm 40 dom_92 5 roots_92 ops++addP pm 41 dom_214 8 roots_214 ops++addP pm 42 dom_42 4 roots_42 ops++addP pm 43 dom_206 8 roots_206 ops++addP pm 44 dom_150 5 roots_150 ops++addP pm 45 dom_86 5 roots_86 ops++addP pm 46 dom_142 5 roots_142 ops++addP pm 47 dom_78 5 roots_78 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_254 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45|h46|h47
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_46 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_238 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_216_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_60 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_zo_214_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_188 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_zo_220_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_174 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_184 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_156 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_zo_218_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_30 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_zo_222_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_120 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_92 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_150 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h45;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h46;exact cpcs (by decide +kernel) lowS_142 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h47;exact cpcs (by decide +kernel) lowS_78 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_250 10 s (0,roots_250.map (·&&&dom_250)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_254 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_250 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_254==dom_254)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_254 gM v ys):RunD true dom_254 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_254 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 21 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 21 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 143 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 15 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 143 → Z 6 i = true := (range_split z6_0 z6_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 256 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_256 : ∀ i, 256 ≤ i → i < 273 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 17 256 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 273 → Z 7 i = true := (range_split z7_0 (range_split z7_128 z7_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 197 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 69 128 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 197 → Z 8 i = true := (range_split z8_0 z8_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 63 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 63 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 8 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 8 0 = true)
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
def isoMvS_191:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_191:Lower true dom_191 roots_191 goal_191 11:=lower_iso_b isoMvS_191 (by decide +kernel) lowS_127
def dzo_223_32:=0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000
def gzo_223_32:=0xffffffff00000000fffffffe00000000fffffffe00000000fffefffe00000000
def gsh_223_32:=0xffffffff00000000fffffffe00000000fffffffe00000000fffefffe
theorem lowS_zo_223_32_208:Lower true dzo_223_32 roots_223 gzo_223_32 8:=lower_iso_b (d1:=dom_223) (r1:=roots_223) (T1:=gsh_223_32) [(dom_223,32)] (by decide +kernel) (lower_slice_b (T:=gsh_223_32) [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,0,1),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,0,2),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,0,4),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,0,8)] (by decide +kernel) lowS_208)
def dzo_219_32:=0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000
def gzo_219_32:=0xf0f0f0f000000000f0f0f0e000000000f0f0f0e000000000f0e0f0e00000000
def gsh_219_32:=0xf0f0f0f000000000f0f0f0e000000000f0f0f0e000000000f0e0f0e
theorem lowS_zo_219_32_208:Lower true dzo_219_32 roots_219 gzo_219_32 7:=lower_iso_b (d1:=dom_219) (r1:=roots_219) (T1:=gsh_219_32) [(dom_219,32)] (by decide +kernel) (lower_slice_b (T:=gsh_219_32) [(0xa0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0a,0,1),(0xc0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c,0,2),(0xf000f00000000000f000f00000000000f000f00000000000f000f00,0,8)] (by decide +kernel) lowS_208)
namespace S_255
def pG:List (Nat×Nat):=[(1,5),(1,9),(1,17),(1,33),(1,65),(1,129),(2,10),(2,18),(2,34),(2,66),(2,130),(3,7),(3,11),(3,19),(3,35),(3,67),(3,131),(4,5),(4,20),(4,36),(4,68),(4,132),(6,7),(6,14),(6,22),(6,38),(6,70),(6,134),(8,9),(8,10),(8,40),(8,72),(8,136),(12,13),(12,14),(12,28),(12,44),(12,76),(12,140),(16,17),(16,18),(16,20),(16,80),(16,144),(24,25),(24,26),(24,28),(24,56),(24,88),(24,152),(32,33),(32,34),(32,36),(32,40),(48,49),(48,50),(48,52),(48,56),(48,112),(48,176),(64,65),(64,66),(64,68),(64,72),(64,80),(64,192),(96,97),(96,98),(96,100),(96,104),(96,112),(96,224),(128,129),(128,130),(128,132),(128,136),(128,144),(128,192),(160,161),(160,162),(160,164),(160,168),(160,176),(160,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffffffffffffff
def xsM:=roots_255.map (·&&&dom_255)
def gM:=goal_255&&&dom_255
def NN:Nat→Nat
|8=>9
|9=>39
|10=>46
|11=>24
|12=>5
|13=>1
|_=>0
def HT:Nat→Nat→Nat
|8,0=>0xd906ad7d73ae1ea6ea6f5508d2376f201b6195400baff
|9,0=>0xd9134d7e3dd3083c7a38c1275ae2b49239d8b33b87bab86e5285eda78b8a6c35c62df05974f56e6155157501eb4dd024c58345dbc456444095b3d03d32b322faa424f6b234f42164a202801960a16f0b0bbc9090b906c85036c00316002ed6006bb
|10,0=>0xf68fcc133fc0b9ab2a74acf5dab043a7429a36d79bbed988339579b924677904078c54779076e5b56a8b86759c6511962eba6272258c3d5252e4d9db4b0764918541eb6404273863032bfc2aee529690250352426f235be1da3e1ca2e1aad70bec70b80a06d4f06c9402fa002ee50083500785
|11,0=>0xf426fdddb2d2767c0c64bdbc39bcb7904578e1d86a8d064a3e4dfa647d6c37dd234e5531fd22e2232d29828e7624a4722c211c7200f24c031cb008ff
|12,0=>0xc88289905e8fd7c86e2a792e4
|13,0=>0x64457
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffffffffffff0000000000000000ffff0000ffff00000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff00000000fffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00fffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000ffffffffffffffffffffffffffffffff00000000000000000000000000000000
|0,1=>0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000f0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0fffff0f0fffff0f0fffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffffffff0f0fffff0f0fffffffffffffffffffff0f0fffff0f0ffffffffffffffffffffffffffffffffffffffff00000000ffffffff0000000000000000000000000000000000000000fffffffffffffffffffff0f0fffff0f00000ffff0000ffff0000ffff0000ffff0000f0f00000f0f00000f0f00000f0f0ffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff000000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000fffffffffffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f000000000000000000000000000000000fffffffffffffffffffffffff0f0f0f00000000000000000ffffffffffffffff0000000000000000fffffffff0f0f0f0ffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0
|0,2=>0xf0f0f0f0f0f0f0f0f0f00000f0f00000f0f0f0f0f0f0f0f0f0f00000f0f00000000ffff0000ffff0000f0f00000f0f00000ffff0000ffff0000f0f00000f0f0fffffffffffffffffffffffffffffffffffffffffffffffffffff0f0fffff0f00000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000f0f00000f0f0ffffffffffffffff0000ffff0000ffffffffffffffffffff0000f0f00000f0f0ffff0000ffff0000ffff0000ffff0000fffffffffffffffffffff0f0fffff0f0000000000000000000000000000000000000ffff0000ffff0000f0f00000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fffffffffffffffffffff0f0fffff0f00000000000000000ffffffffffffffff0000000000000000f0f0f0f0f0f0f0f0f0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0f0f000000000000000000000000000000000ffffffffffffffffffff0000ffff000000000000000000000000000000000000fffffffffffffffff0f0f0f0f0f0f0f00000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000f0f0ffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000fffffffffffffffffffffffffffffffffffff0f0fffff0f0fffff0f0fffff0f0fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0f0
|_,_=>0
def sP:Nat→Nat
|0=>0x1c61490c204800b41215d0c220b18510309929b6861490c221140f1490c20111851030990074061440c20076061440c200718510309700c1851030960144c718524308c1d01440c201140f14d0c21c614434308e30718510d0c21c61440c2040
|1=>0xc5461490c22006e51851090c22d07c59030805541c61490c221b41f14d0c22151c61490c28c800b88614434308b85f1440c20201c61490c22006d07c510308045218510d0c245e1852430801c614d24308e20c1c614d2430881c614d0c2588
|2=>0xc25c800718510d0c22df48510d0c22d09451030803061490c258800b8461440c22941c61490c221b70614d0c220b7d215d2430871852430a32002d08851030802e17c524308a2d048510308a1c616624308801518524308e200307405243088
|3=>0xc1c61490c22004521853490c221b18510d0c220b8861442430802da18524308800b7d21490c229b40614d0c220b1852430992882d21851090c22911852430992004521851090c200b7c61443430801d01852430880076061490c22001c6149
|4=>0xc200b4121490c22882ea18524308800b8461440c22006e11853490c221b18574d2430886d018510308800b1852430a92002d018574308800ba061490c22002d01859c308800b85f1490c22001c61490c238800b4121440c22006d07c5243088
|5=>0x1857490c220b1853430ae2002df4851090c200b4861499c30882d018510308a0151c61490c22002ed18524308800b8461490c22886e51852430882d088524308800b1852430ac2002c614434308a2c61490c2ac801b7061490c22002e5185109
|6=>0x4861490c228845218524308800b85218524308800b18574424308800b1859090c22002d01853430880114061490c22002c61490c2b8800b7061490c22002df1853490c22001c61490c258800b4251490c22002d07c51030801c61442430802d2
|7=>0xb1857490c22001c61490c22002df48524308800b41f1490c22006c614d2430882d018524308a2002e518524308800b1852430af20044614d24308800b7c61442430802c614424308a00b8861490c22002dc1851090c22002c614434308800b
|8=>0xb18524308801b18524308800b1851090c22002df18524308800b4061490c22002c61490c2288
|_=>0
def sO:Nat→Nat→Nat
|8,0=>0x3f806f00be013c01f8030e04200440008
|9,0=>0x6124bdc97472d905920adc9538297050e09dc1329255048a08d4111921123fe47b48ee81cd037646ac0cba18702ee05948aa8145026a048c888910101de437c06780bf015e027c0478
|10,0=>0x18dcb1296150c0a17ccaf095cf2b7a56acacc95872aea55942a995412a62147ca8694fb29d2535ca6294b32942523ca3e946b28b2511ca1a942328224ffc9f693db27960ee49d39397070e0dd49b19351267e4cb498d9
|11,0=>0x7ed2fba1f2cbdc97a90f2a9e0cbb8975f2e9a5cecb9497154e065bc4b6f96cb4d6e9a94b4996812cde5974b24a
|12,0=>0x423883530466044bff9
|13,0=>0x42b8
|_,_=>0
def wAt:=mkWire dB 48 256 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 15
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x18d80212405c032c0461124852232c84601189492118d8b2124049212ca402118946591c9cb2920049211d0c9212ca402118947271c64b292004921548d5031c94b2920049211c64b290084625488c6251804b2124049211c6cb29008490124847192ca40212404c271c64b292004921
|1=>0x1884b012484625100c62124855031c94b2920046251884b01240551b1c94b29200462924048012485225180462124847412ca480118946251884b0124849011804b212484f252c85223180471b2ca402124047192ca402124047272ca40212404c271c64b29200492918048011894921
|2=>0x2ca48012484901180462124846252485f0318847271c64b292005001248402118955031c94b292005f251884b0124049291884021180551b1c94b2920046292484021189500118840211894921180480118949391c6cb2920047251c6cb2920047192ca480118947251c64b292005f03
|3=>0x1884d2318949011884635240471b2ca480124846011894b0118846251c64b2920046012c849012404b0124849214884601700c611248462100846012404b0118946360084901180480124846362c849011804b21248462124849012ca480118946591c9cb2920047432ca48011894901
|4=>0x1884921348c601240492100846251c94b292005029200462540048011894b017c0c62118a4801189467610049212404801248592118d89012c0461124849217c0c62118048011894691100c921248463524046352c049012c04d2124046252c049214848601248492920046259495f03
|5=>0x200460118846211894b0124048011895f031885f271884b21240462124848012485f011884611248490124840211804b2118052251804401248440324846252404b2118946122484611248462124047272ca48017c0c621189492118846252ca48012484601100492118489212404601
|6=>0x2c04921188462520044012484b29
|_=>0
def oO:Nat→Nat→Nat
|8,0=>0x28511a879432a14507a82940aa005
|9,0=>0x3151828bd45ca2d51628ad454a29514289d44ca25512288d444a21510287d43ca1d50e286d434a1950c285d42ca1550a284d424a11508283d41ca0d506282d4
|10,0=>0x2a074d3a51d1ce8874139f1cece707353991cbce587293931c8ce4071d38d1c5ce287113871c2ce107053811bfcdf86f937b1bccde06ed3751b9cdc86e136f1b6cdb06d53691b3cd986c93
|11,0=>0xc095fcafa57b2bc95dcaea5732b895bcada56b2b4959caca5632b0957caba55b2ac955caaa5532
|12,0=>0x1871c30e147083831
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 13
def pmP:Nat→Nat
|0=>0xf913c003e40f000ed03c003a50f000e913c003a40f0007d43c001e40f0006d13c001b40f0006943c001a40f0006143c001754f0004ff7c0013fcf0004f11c001354f0004bf3c00127df0004957c001254f0004907c000f44f0000ff3c0003ccf0000b33c00024cf0000753c0000fcf000000fc0000000
|1=>0xbf903c02da40f00a6d03c029a40f009ed03c025a44f0076d03c01da40f005ed03c015b40f004fd03c013e40f004e903c012e40f0047d03c011b40f0046903c00ba40f0027d43c009f40f0027c03c009e40f0027143c009b50f0026d03c009a50f0026903c009850f001ed03c007a44f0016d13c005244f
|2=>0x1004f5bc40004380a04147c17bb50f050ed43c0c32d0f0204f53c0812fdf0204b53c081255f0204953c081053f01d7d03c06de40f01af903c06ba40f01a7d03c069e40f019f913c065e44f014f903c051e40f010f953c043e40f010ed03c043a44f010d953c041654f00f6d03c03da40f00d7d03c035a40f
|3=>0x3821a40f8127d03e009f50f8006903d047a50f405ed03d007b40f214f903c853a50f204fd03c813e40f2006903c481343f
|_=>0
def pmB:Nat→Nat→Nat
|8,0=>0x51e18087100c104
|9,0=>0x36cc57eb08b7bab5a0b72de0d7c0404a95752e5e708efa69a82c8db431ab22684f92
|10,0=>0x2ba79f1311ea4b98d6d99d243c32cd6a54d8c66d190c98c694ee6ab4d4584526169856d9d3373288e
|11,0=>0xca29f3d38c12bc8d3a542d72203a7794c472e635d0
|12,0=>0x1530f0b2f
|13,0=>0x14
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 7 (j%128);fld (pmP (k/32)) 30 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_254 12 roots_254 ops++addP pm 1 dom_253 12 roots_253 ops++addP pm 2 dom_247 12 roots_247 ops++addP pm 3 dom_251 11 roots_251 ops++addP pm 4 dzo_223_32 8 roots_223 ops++addP pm 5 dom_139 5 roots_139 ops++addP pm 6 dom_159 10 roots_159 ops++addP pm 7 dom_143 7 roots_143 ops++addP pm 8 dom_95 10 roots_95 ops++addP pm 9 dom_79 7 roots_79 ops++addP pm 10 dom_239 11 roots_239 ops++addP pm 11 dzo_219_32 7 roots_219 ops++addP pm 12 dom_235 9 roots_235 ops++addP pm 13 dom_127 11 roots_127 ops++addP pm 14 dom_187 8 roots_187 ops++addP pm 15 dom_223 12 roots_223 ops++addP pm 16 dom_191 11 roots_191 ops++addP pm 17 dom_123 8 roots_123 ops++addP pm 18 dom_111 8 roots_111 ops++addP pm 19 dom_175 8 roots_175 ops++addP pm 20 dom_63 9 roots_63 ops++addP pm 21 dom_47 7 roots_47 ops++addP pm 22 dom_43 5 roots_43 ops++addP pm 23 dom_31 6 roots_31 ops++addP pm 24 dom_207 10 roots_207 ops++addP pm 25 dom_155 6 roots_155 ops++addP pm 26 dom_75 5 roots_75 ops++addP pm 27 dom_59 6 roots_59 ops++addP pm 28 dom_107 6 roots_107 ops++addP pm 29 dom_171 6 roots_171 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_255 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_247 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_zo_223_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_143 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_79 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_219_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_127 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_223 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_191 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_175 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_47 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_207 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_171 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_254 12 s (0,roots_254.map (·&&&dom_254)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_254 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_255==dom_255)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_255 gM v ys):RunD true dom_255 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_255 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 9 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 39 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 39 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 46 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 46 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 24 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 24 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z12 : ∀ i, 0 ≤ i → i < 5 → Z 12 i = true := span_ok (by decide +kernel : span (Z 12) 5 0 = true)
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
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [0, 1] }, { op := GateOp.or, inputs := [2, 8] }, { op := GateOp.or, inputs := [6, 7] }, { op := GateOp.or, inputs := [3, 9] }, { op := GateOp.or, inputs := [5, 10] }, { op := GateOp.and, inputs := [11, 12] }, { op := GateOp.or, inputs := [9, 10] }, { op := GateOp.and, inputs := [4, 14] }, { op := GateOp.and, inputs := [3, 8] }, { op := GateOp.and, inputs := [7, 6] }, { op := GateOp.and, inputs := [0, 2] }, { op := GateOp.or, inputs := [13, 15] }, { op := GateOp.or, inputs := [19, 16] }, { op := GateOp.or, inputs := [20, 17] }, { op := GateOp.or, inputs := [21, 18] }]

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 22⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
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

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_53082_aux

theorem PEqualNP.Outside.L_meta_53082 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_53082_aux.main
