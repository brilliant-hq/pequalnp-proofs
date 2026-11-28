import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_52868_aux
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

def dom_45 : Nat := 0x333300003333
def goal_45 : Nat := 0xfffafffaaa00aa00fffafffaaa00aa00fffafffaaa00aa00fffafffaaa00aa00
def roots_45 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_46 : Nat := 0x555500005555
def goal_46 : Nat := 0xfffcfffccc00cc00fffcfffccc00cc00fffcfffccc00cc00fffcfffccc00cc00
def roots_46 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_47 : Nat := 0xffff0000ffff
def goal_47 : Nat := 0xfffefffeee00ee00fffefffeee00ee00fffefffeee00ee00fffefffeee00ee00
def roots_47 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_51 : Nat := 0xf000f000f000f
def goal_51 : Nat := 0xeeeeeeeeaaaa0000eeeeeeeeaaaa0000eeeeeeeeaaaa0000eeeeeeeeaaaa0000
def roots_51 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_54 : Nat := 0x55005500550055
def goal_54 : Nat := 0xfcfcfcfcf0f00000fcfcfcfcf0f00000fcfcfcfcf0f00000fcfcfcfcf0f00000
def roots_54 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xfefefefefafa0000fefefefefafa0000fefefefefafa0000fefefefefafa0000
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_57 : Nat := 0x303030303030303
def goal_57 : Nat := 0xffaaffaaaaaaaa00ffaaffaaaaaaaa00ffaaffaaaaaaaa00ffaaffaaaaaaaa00
def roots_57 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xffeeffeeeeaaee00ffeeffeeeeaaee00ffeeffeeeeaaee00ffeeffeeeeaaee00
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_60 : Nat := 0x1111111111111111
def goal_60 : Nat := 0xfff0fff0f0f00000fff0fff0f0f00000fff0fff0f0f00000fff0fff0f0f00000
def roots_60 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xfffafffafafaaa00fffafffafafaaa00fffafffafafaaa00fffafffafafaaa00
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_62 : Nat := 0x5555555555555555
def goal_62 : Nat := 0xfffcfffcfcf0cc00fffcfffcfcf0cc00fffcfffcfcf0cc00fffcfffcfcf0cc00
def roots_62 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfffefffefefaee00fffefffefefaee00fffefffefefaee00fffefffefefaee00
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_73 : Nat := 0x3030000000000000303
def goal_73 : Nat := 0xffaaffaaffaaffaaaa00aa00aa00aa00ffaaffaaffaaffaaaa00aa00aa00aa00
def roots_73 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_75 : Nat := 0xf0f0000000000000f0f
def goal_75 : Nat := 0xffeeffeeffeeffeeee00ee00ee00ee00ffeeffeeffeeffeeee00ee00ee00ee00
def roots_75 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_77 : Nat := 0x33330000000000003333
def goal_77 : Nat := 0xfffafffafffafffaaa00aa00aa00aa00fffafffafffafffaaa00aa00aa00aa00
def roots_77 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_86 : Nat := 0x5500550000000000550055
def goal_86 : Nat := 0xfcfcfcfcfcfcfcfcf0f00000f0f00000fcfcfcfcfcfcfcfcf0f00000f0f00000
def roots_86 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_87 : Nat := 0xff00ff0000000000ff00ff
def goal_87 : Nat := 0xfefefefefefefefefafa0000fafa0000fefefefefefefefefafa0000fafa0000
def roots_87 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_92 : Nat := 0x111111110000000011111111
def goal_92 : Nat := 0xfff0fff0fff0fff0f0f00000f0f00000fff0fff0fff0fff0f0f00000f0f00000
def roots_92 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_93 : Nat := 0x333333330000000033333333
def goal_93 : Nat := 0xfffafffafffafffafafaaa00fafaaa00fffafffafffafffafafaaa00fafaaa00
def roots_93 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_94 : Nat := 0x555555550000000055555555
def goal_94 : Nat := 0xfffcfffcfffcfffcfcf0cc00fcf0cc00fffcfffcfffcfffcfcf0cc00fcf0cc00
def roots_94 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_95 : Nat := 0xffffffff00000000ffffffff
def goal_95 : Nat := 0xfffefffefffefffefefaee00fefaee00fffefffefffefffefefaee00fefaee00
def roots_95 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_97 : Nat := 0x3000000030000000300000003
def goal_97 : Nat := 0xffffffffaaaaaaaaaaaaaaaa00000000ffffffffaaaaaaaaaaaaaaaa00000000
def roots_97 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_98 : Nat := 0x5000000050000000500000005
def goal_98 : Nat := 0xffffffffcccccccccccccccc00000000ffffffffcccccccccccccccc00000000
def roots_98 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_99 : Nat := 0xf0000000f0000000f0000000f
def goal_99 : Nat := 0xffffffffeeeeeeeeeeeeeeee00000000ffffffffeeeeeeeeeeeeeeee00000000
def roots_99 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_102 : Nat := 0x55000000550000005500000055
def goal_102 : Nat := 0xfffffffffcfcfcfcfcfcfcfc00000000fffffffffcfcfcfcfcfcfcfc00000000
def roots_102 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_104 : Nat := 0x101000001010000010100000101
def goal_104 : Nat := 0xffffffffff00ff00ff00ff0000000000ffffffffff00ff00ff00ff0000000000
def roots_104 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_105 : Nat := 0x303000003030000030300000303
def goal_105 : Nat := 0xffffffffffaaffaaffaaffaaaa00aa00ffffffffffaaffaaffaaffaaaa00aa00
def roots_105 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_106 : Nat := 0x505000005050000050500000505
def goal_106 : Nat := 0xffffffffffccffccffccffcccc00cc00ffffffffffccffccffccffcccc00cc00
def roots_106 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffffffffffeeffeeffeeffeeee00ee00ffffffffffeeffeeffeeffeeee00ee00
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_108 : Nat := 0x1111000011110000111100001111
def goal_108 : Nat := 0xfffffffffff0fff0fff0fff000000000fffffffffff0fff0fff0fff000000000
def roots_108 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_109 : Nat := 0x3333000033330000333300003333
def goal_109 : Nat := 0xfffffffffffafffafffafffaaa00aa00fffffffffffafffafffafffaaa00aa00
def roots_109 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_110 : Nat := 0x5555000055550000555500005555
def goal_110 : Nat := 0xfffffffffffcfffcfffcfffccc00cc00fffffffffffcfffcfffcfffccc00cc00
def roots_110 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xfffffffffffefffefffefffeee00ee00fffffffffffefffefffefffeee00ee00
def roots_111 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_116 : Nat := 0x110011001100110011001100110011
def goal_116 : Nat := 0xfffffffff0f0f0f0f0f0f0f0f0f00000fffffffff0f0f0f0f0f0f0f0f0f00000
def roots_116 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_117 : Nat := 0x330033003300330033003300330033
def goal_117 : Nat := 0xfffffffffafafafafafafafafafa0000fffffffffafafafafafafafafafa0000
def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xfffffffffcfcfcfcfcfcfcfcf0f00000fffffffffcfcfcfcfcfcfcfcf0f00000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xfffffffffefefefefefefefefafa0000fffffffffefefefefefefefefafa0000
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_121 : Nat := 0x3030303030303030303030303030303
def goal_121 : Nat := 0xffffffffffaaffaaffaaffaaaaaaaa00ffffffffffaaffaaffaaffaaaaaaaa00
def roots_121 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_124 : Nat := 0x11111111111111111111111111111111
def goal_124 : Nat := 0xfffffffffff0fff0fff0fff0f0f00000fffffffffff0fff0fff0fff0f0f00000
def roots_124 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xfffffffffffafffafffafffafafaaa00fffffffffffafffafffafffafafaaa00
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_126 : Nat := 0x55555555555555555555555555555555
def goal_126 : Nat := 0xfffffffffffcfffcfffcfffcfcf0cc00fffffffffffcfffcfffcfffcfcf0cc00
def roots_126 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xfffffffffffefffefffefffefefaee00fffffffffffefffefffefffefefaee00
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_138 : Nat := 0x50500000000000000000000000000000505
def goal_138 : Nat := 0xffccffccffccffccffccffccffccffcccc00cc00cc00cc00cc00cc00cc00cc00
def roots_138 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_139 : Nat := 0xf0f00000000000000000000000000000f0f
def goal_139 : Nat := 0xffccffccffccffccffccffccffccffccee00ee00ee00ee00ee00ee00ee00ee00
def roots_139 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_141 : Nat := 0x333300000000000000000000000000003333
def goal_141 : Nat := 0xfff0fff0fff0fff0fff0fff0fff0fff0aa00aa00aa00aa00aa00aa00aa00aa00
def roots_141 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_142 : Nat := 0x555500000000000000000000000000005555
def goal_142 : Nat := 0xfffcfffcfffcfffcfffcfffcfffcfffccc00cc00cc00cc00cc00cc00cc00cc00
def roots_142 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_143 : Nat := 0xffff0000000000000000000000000000ffff
def goal_143 : Nat := 0xfffcfffcfffcfffcfffcfffcfffcfffcee00ee00ee00ee00ee00ee00ee00ee00
def roots_143 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_148 : Nat := 0x11001100000000000000000000000000110011
def goal_148 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0f0f00000f0f00000f0f00000f0f00000
def roots_148 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_149 : Nat := 0x33003300000000000000000000000000330033
def goal_149 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0fafa0000fafa0000fafa0000fafa0000
def roots_149 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_150 : Nat := 0x55005500000000000000000000000000550055
def goal_150 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfcf0f00000f0f00000f0f00000f0f00000
def roots_150 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_151 : Nat := 0xff00ff00000000000000000000000000ff00ff
def goal_151 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfcfafa0000fafa0000fafa0000fafa0000
def roots_151 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_154 : Nat := 0x505050500000000000000000000000005050505
def goal_154 : Nat := 0xffffffccffffffccffffffccffffffcccc00cc00cc00cc00cc00cc00cc00cc00
def roots_154 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

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
def goal_165 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0fafafafa00000000fafafafa00000000
def roots_165 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_166 : Nat := 0x550000005500000000000000000000005500000055
def goal_166 : Nat := 0xfffffffffcfcfcfcfffffffffcfcfcfcfcfcfcfc00000000fcfcfcfc00000000
def roots_166 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_169 : Nat := 0x3030000030300000000000000000000030300000303
def goal_169 : Nat := 0xffffffffff00ff00ffffffffff00ff00ffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_169 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_170 : Nat := 0x5050000050500000000000000000000050500000505
def goal_170 : Nat := 0xffffffffffccffccffffffffffccffccffccffcccc00cc00ffccffcccc00cc00
def roots_170 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_171 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
def goal_171 : Nat := 0xffffffffffccffccffffffffffccffccffeeffeeee00ee00ffeeffeeee00ee00
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_172 : Nat := 0x11110000111100000000000000000000111100001111
def goal_172 : Nat := 0xfffffffffff0fff0fffffffffff0fff0fff0fff000000000fff0fff000000000
def roots_172 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_173 : Nat := 0x33330000333300000000000000000000333300003333
def goal_173 : Nat := 0xfffffffffff0fff0fffffffffff0fff0fffafffaaa00aa00fffafffaaa00aa00
def roots_173 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_174 : Nat := 0x55550000555500000000000000000000555500005555
def goal_174 : Nat := 0xfffffffffffcfffcfffffffffffcfffcfffcfffccc00cc00fffcfffccc00cc00
def roots_174 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_175 : Nat := 0xffff0000ffff00000000000000000000ffff0000ffff
def goal_175 : Nat := 0xfffffffffffcfffcfffffffffffcfffcfffefffeee00ee00fffefffeee00ee00
def roots_175 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_180 : Nat := 0x1100110011001100000000000000000011001100110011
def goal_180 : Nat := 0xfffffffffffff0f0fffffffffffff0f0f0f0f0f0f0f00000f0f0f0f0f0f00000
def roots_180 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_181 : Nat := 0x3300330033003300000000000000000033003300330033
def goal_181 : Nat := 0xfffffffffffff0f0fffffffffffff0f0fafafafafafa0000fafafafafafa0000
def roots_181 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_182 : Nat := 0x5500550055005500000000000000000055005500550055
def goal_182 : Nat := 0xfffffffffffffcfcfffffffffffffcfcfcfcfcfcf0f00000fcfcfcfcf0f00000
def roots_182 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_183 : Nat := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
def goal_183 : Nat := 0xfffffffffffffcfcfffffffffffffcfcfefefefefafa0000fefefefefafa0000
def roots_183 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_185 : Nat := 0x30303030303030300000000000000000303030303030303
def goal_185 : Nat := 0xffffffffffffff00ffffffffffffff00ffaaffaaaaaaaa00ffaaffaaaaaaaa00
def roots_185 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_186 : Nat := 0x50505050505050500000000000000000505050505050505
def goal_186 : Nat := 0xffffffffffffffccffffffffffffffccffccffcccc00cc00ffccffcccc00cc00
def roots_186 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_188 : Nat := 0x111111111111111100000000000000001111111111111111
def goal_188 : Nat := 0xfffffffffffffff0fffffffffffffff0fff0fff0f0f00000fff0fff0f0f00000
def roots_188 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_189 : Nat := 0x333333333333333300000000000000003333333333333333
def goal_189 : Nat := 0xfffffffffffffff0fffffffffffffff0fffafffafafaaa00fffafffafafaaa00
def roots_189 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_190 : Nat := 0x555555555555555500000000000000005555555555555555
def goal_190 : Nat := 0xfffffffffffffffcfffffffffffffffcfffcfffcfcf0cc00fffcfffcfcf0cc00
def roots_190 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xfffffffffffffffcfffffffffffffffcfffefffefefaee00fffefffefefaee00
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_195 : Nat := 0xf000000000000000f000000000000000f000000000000000f
def goal_195 : Nat := 0xffffffffffffffffcccccccccccccccceeeeeeeeeeeeeeee0000000000000000
def roots_195 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_197 : Nat := 0x33000000000000003300000000000000330000000000000033
def goal_197 : Nat := 0xfffffffffffffffff0f0f0f0f0f0f0f0fafafafafafafafa0000000000000000
def roots_197 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_198 : Nat := 0x55000000000000005500000000000000550000000000000055
def goal_198 : Nat := 0xfffffffffffffffffcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc0000000000000000
def roots_198 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_201 : Nat := 0x303000000000000030300000000000003030000000000000303
def goal_201 : Nat := 0xffffffffffffffffff00ff00ff00ff00ffaaffaaffaaffaaaa00aa00aa00aa00
def roots_201 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_202 : Nat := 0x505000000000000050500000000000005050000000000000505
def goal_202 : Nat := 0xffffffffffffffffffccffccffccffccffccffccffccffcccc00cc00cc00cc00
def roots_202 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffffffffffffffffffccffccffccffccffeeffeeffeeffeeee00ee00ee00ee00
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_205 : Nat := 0x3333000000000000333300000000000033330000000000003333
def goal_205 : Nat := 0xfffffffffffffffffff0fff0fff0fff0fffafffafffafffaaa00aa00aa00aa00
def roots_205 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_207 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def goal_207 : Nat := 0xfffffffffffffffffffcfffcfffcfffcfffefffefffefffeee00ee00ee00ee00
def roots_207 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_212 : Nat := 0x110011000000000011001100000000001100110000000000110011
def goal_212 : Nat := 0xfffffffffffffffffffff0f0fffff0f0f0f0f0f0f0f0f0f0f0f00000f0f00000
def roots_212 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_213 : Nat := 0x330033000000000033003300000000003300330000000000330033
def goal_213 : Nat := 0xfffffffffffffffffffff0f0fffff0f0fafafafafafafafafafa0000fafa0000
def roots_213 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xfffffffffffffffffffffcfcfffffcfcfcfcfcfcfcfcfcfcf0f00000f0f00000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xfffffffffffffffffffffcfcfffffcfcfefefefefefefefefafa0000fafa0000
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_217 : Nat := 0x3030303000000000303030300000000030303030000000003030303
def goal_217 : Nat := 0xffffffffffffffffffffff00ffffff00ffaaffaaffaaffaaaaaaaa00aaaaaa00
def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_220 : Nat := 0x11111111000000001111111100000000111111110000000011111111
def goal_220 : Nat := 0xfffffffffffffffffffffff0fffffff0fff0fff0fff0fff0f0f00000f0f00000
def roots_220 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def goal_221 : Nat := 0xfffffffffffffffffffffff0fffffff0fffafffafffafffafafaaa00fafaaa00
def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xfffffffffffffffffffffffcfffffffcfffcfffcfffcfffcfcf0cc00fcf0cc00
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffffffffffffffffffcfffffffcfffefffefffefffefefaee00fefaee00
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_225 : Nat := 0x300000003000000030000000300000003000000030000000300000003
def goal_225 : Nat := 0xffffffffffffffffffffffff00000000ffffffffaaaaaaaaaaaaaaaa00000000
def roots_225 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_226 : Nat := 0x500000005000000050000000500000005000000050000000500000005
def goal_226 : Nat := 0xffffffffffffffffffffffffccccccccffffffffcccccccccccccccc00000000
def roots_226 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def goal_227 : Nat := 0xffffffffffffffffffffffffccccccccffffffffeeeeeeeeeeeeeeee00000000
def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_228 : Nat := 0x1100000011000000110000001100000011000000110000001100000011
def goal_228 : Nat := 0xfffffffffffffffffffffffff0f0f0f0fffffffff0f0f0f0f0f0f0f000000000
def roots_228 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_229 : Nat := 0x3300000033000000330000003300000033000000330000003300000033
def goal_229 : Nat := 0xfffffffffffffffffffffffff0f0f0f0fffffffffafafafafafafafa00000000
def roots_229 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def goal_230 : Nat := 0xfffffffffffffffffffffffffcfcfcfcfffffffffcfcfcfcfcfcfcfc00000000
def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_232 : Nat := 0x10100000101000001010000010100000101000001010000010100000101
def goal_232 : Nat := 0xffffffffffffffffffffffffff00ff00ffffffffff00ff00ff00ff0000000000
def roots_232 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffffffffffffffffff00ff00ffffffffffaaffaaffaaffaaaa00aa00
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffffffffffffffffffccffccffffffffffccffccffccffcccc00cc00
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffffffffffffffffffccffccffffffffffeeffeeffeeffeeee00ee00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_236 : Nat := 0x111100001111000011110000111100001111000011110000111100001111
def goal_236 : Nat := 0xfffffffffffffffffffffffffff0fff0fffffffffff0fff0fff0fff000000000
def roots_236 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xfffffffffffffffffffffffffff0fff0fffffffffffafffafffafffaaa00aa00
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_238 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def goal_238 : Nat := 0xfffffffffffffffffffffffffffcfffcfffffffffffcfffcfffcfffccc00cc00
def roots_238 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffffffffffffffffffcfffcfffffffffffefffefffefffeee00ee00
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_241 : Nat := 0x3000300030003000300030003000300030003000300030003000300030003
def goal_241 : Nat := 0xffffffffffffffffffffffffffff0000ffffffffaaaaaaaaaaaaaaaaaaaa0000
def roots_241 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def goal_242 : Nat := 0xffffffffffffffffffffffffffffccccffffffffcccccccccccccccc00000000
def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_244 : Nat := 0x11001100110011001100110011001100110011001100110011001100110011
def goal_244 : Nat := 0xfffffffffffffffffffffffffffff0f0fffffffff0f0f0f0f0f0f0f0f0f00000
def roots_244 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_245 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
def goal_245 : Nat := 0xfffffffffffffffffffffffffffff0f0fffffffffafafafafafafafafafa0000
def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffffffffffffffffffffffcfcfffffffffcfcfcfcfcfcfcfcf0f00000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffffffffffffffffffcfcfffffffffefefefefefefefefafa0000
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_248 : Nat := 0x101010101010101010101010101010101010101010101010101010101010101
def goal_248 : Nat := 0xffffffffffffffffffffffffffffff00ffffffffff00ff00ff00ff0000000000
def roots_248 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffffffffffffffffff00ffffffffffaaffaaffaaffaaaaaaaa00
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffffffffffffffffffccffffffffffeeffeeffeeffeeeeaaee00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_252 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
def goal_252 : Nat := 0xfffffffffffffffffffffffffffffff0fffffffffff0fff0fff0fff0f0f00000
def roots_252 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffffffffffffffffff0fffffffffffafffafffafffafafaaa00
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffffffffffffffffffcfffffffffffcfffcfffcfffcfcf0cc00
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffffffffffffffffffcfffffffffffefffefffefffefefaee00
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
def isoMvS_97:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_97:Lower true dom_97 roots_97 goal_97 4:=lower_iso_b isoMvS_97 (by decide +kernel) lowS_41
def isoMvS_98:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_98:Lower true dom_98 roots_98 goal_98 4:=lower_iso_b isoMvS_98 (by decide +kernel) lowS_41
def isoMvS_104:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_104:Lower true dom_104 roots_104 goal_104 4:=lower_iso_b isoMvS_104 (by decide +kernel) lowS_41
def isoMvS_138:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_138:Lower true dom_138 roots_138 goal_138 4:=lower_iso_b isoMvS_138 (by decide +kernel) lowS_41
def isoMvS_148:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_148:Lower true dom_148 roots_148 goal_148 4:=lower_iso_b isoMvS_148 (by decide +kernel) lowS_41
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
theorem lowS_45:Lower true dom_45 roots_45 goal_45 5:=lower_slice_b [(0x303000003030,32,36)] (by decide +kernel) lowS_41
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
|0=>0x204c1324d1404c1424c930409
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
def isoMvS_46:List (Nat×Nat):=[(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_46:Lower true dom_46 roots_46 goal_46 5:=lower_iso_b isoMvS_46 (by decide +kernel) lowS_45
def isoMvS_51:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_51:Lower true dom_51 roots_51 goal_51 4:=lower_iso_b isoMvS_51 (by decide +kernel) lowS_27
def isoMvS_54:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_54:Lower true dom_54 roots_54 goal_54 4:=lower_iso_b isoMvS_54 (by decide +kernel) lowS_27
def isoMvS_57:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_57:Lower true dom_57 roots_57 goal_57 5:=lower_iso_b isoMvS_57 (by decide +kernel) lowS_45
def isoMvS_60:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_60:Lower true dom_60 roots_60 goal_60 4:=lower_iso_b isoMvS_60 (by decide +kernel) lowS_27
def isoMvS_75:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_75:Lower true dom_75 roots_75 goal_75 5:=lower_iso_b isoMvS_75 (by decide +kernel) lowS_43
def isoMvS_77:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_77:Lower true dom_77 roots_77 goal_77 5:=lower_iso_b isoMvS_77 (by decide +kernel) lowS_45
def isoMvS_86:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_86:Lower true dom_86 roots_86 goal_86 4:=lower_iso_b isoMvS_86 (by decide +kernel) lowS_27
def isoMvS_92:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_92:Lower true dom_92 roots_92 goal_92 4:=lower_iso_b isoMvS_92 (by decide +kernel) lowS_27
def isoMvS_99:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_99:Lower true dom_99 roots_99 goal_99 5:=lower_iso_b isoMvS_99 (by decide +kernel) lowS_43
def isoMvS_106:List (Nat×Nat):=[(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_106:Lower true dom_106 roots_106 goal_106 7:=lower_iso_b isoMvS_106 (by decide +kernel) lowS_105
def isoMvS_116:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_116:Lower true dom_116 roots_116 goal_116 5:=lower_iso_b isoMvS_116 (by decide +kernel) lowS_45
def isoMvS_139:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_139:Lower true dom_139 roots_139 goal_139 5:=lower_iso_b isoMvS_139 (by decide +kernel) lowS_45
def isoMvS_141:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_141:Lower true dom_141 roots_141 goal_141 4:=lower_iso_b isoMvS_141 (by decide +kernel) lowS_27
def isoMvS_142:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_142:Lower true dom_142 roots_142 goal_142 5:=lower_iso_b isoMvS_142 (by decide +kernel) lowS_45
def isoMvS_149:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_149:Lower true dom_149 roots_149 goal_149 5:=lower_iso_b isoMvS_149 (by decide +kernel) lowS_45
def isoMvS_150:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_150:Lower true dom_150 roots_150 goal_150 5:=lower_iso_b isoMvS_150 (by decide +kernel) lowS_45
def isoMvS_154:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_154:Lower true dom_154 roots_154 goal_154 5:=lower_iso_b isoMvS_154 (by decide +kernel) lowS_45
def isoMvS_156:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_156:Lower true dom_156 roots_156 goal_156 5:=lower_iso_b isoMvS_156 (by decide +kernel) lowS_45
def isoMvS_163:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_163:Lower true dom_163 roots_163 goal_163 5:=lower_iso_b isoMvS_163 (by decide +kernel) lowS_45
def isoMvS_165:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_165:Lower true dom_165 roots_165 goal_165 5:=lower_iso_b isoMvS_165 (by decide +kernel) lowS_45
def isoMvS_166:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_166:Lower true dom_166 roots_166 goal_166 5:=lower_iso_b isoMvS_166 (by decide +kernel) lowS_43
def isoMvS_169:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_169:Lower true dom_169 roots_169 goal_169 5:=lower_iso_b isoMvS_169 (by decide +kernel) lowS_43
def isoMvS_170:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_170:Lower true dom_170 roots_170 goal_170 7:=lower_iso_b isoMvS_170 (by decide +kernel) lowS_105
def isoMvS_172:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_172:Lower true dom_172 roots_172 goal_172 5:=lower_iso_b isoMvS_172 (by decide +kernel) lowS_43
def isoMvS_180:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_180:Lower true dom_180 roots_180 goal_180 5:=lower_iso_b isoMvS_180 (by decide +kernel) lowS_43
def isoMvS_195:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_195:Lower true dom_195 roots_195 goal_195 5:=lower_iso_b isoMvS_195 (by decide +kernel) lowS_45
def isoMvS_197:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_197:Lower true dom_197 roots_197 goal_197 5:=lower_iso_b isoMvS_197 (by decide +kernel) lowS_45
def isoMvS_198:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_198:Lower true dom_198 roots_198 goal_198 5:=lower_iso_b isoMvS_198 (by decide +kernel) lowS_43
def isoMvS_201:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_201:Lower true dom_201 roots_201 goal_201 5:=lower_iso_b isoMvS_201 (by decide +kernel) lowS_43
def isoMvS_202:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_202:Lower true dom_202 roots_202 goal_202 7:=lower_iso_b isoMvS_202 (by decide +kernel) lowS_105
def isoMvS_212:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_212:Lower true dom_212 roots_212 goal_212 5:=lower_iso_b isoMvS_212 (by decide +kernel) lowS_43
def isoMvS_225:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_225:Lower true dom_225 roots_225 goal_225 5:=lower_iso_b isoMvS_225 (by decide +kernel) lowS_43
def isoMvS_226:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_226:Lower true dom_226 roots_226 goal_226 7:=lower_iso_b isoMvS_226 (by decide +kernel) lowS_105
def isoMvS_228:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_228:Lower true dom_228 roots_228 goal_228 7:=lower_iso_b isoMvS_228 (by decide +kernel) lowS_105
def isoMvS_232:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_232:Lower true dom_232 roots_232 goal_232 7:=lower_iso_b isoMvS_232 (by decide +kernel) lowS_105
theorem lowS_31:Lower true dom_31 roots_31 goal_31 5:=lower_slice_b [(0xcccccccc,8,10)] (by decide +kernel) lowS_29
theorem lowS_47:Lower true dom_47 roots_47 goal_47 6:=lower_slice_b [(0xaaaa0000aaaa,8,9)] (by decide +kernel) lowS_46
theorem lowS_55:Lower true dom_55 roots_55 goal_55 5:=lower_slice_b [(0xaa00aa00aa00aa,16,17)] (by decide +kernel) lowS_54
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
theorem lowS_61:Lower true dom_61 roots_61 goal_61 6:=lower_slice_b [(0x3030303030303030,16,20)] (by decide +kernel) lowS_57
def dzo_46_16:=0x5555000055550000
def gzo_46_16:=0x5554000054500000
def gsh_46_16:=0x555400005450
theorem lowS_zo_46_16_42:Lower true dzo_46_16 roots_46 gzo_46_16 5:=lower_iso_b (d1:=dom_46) (r1:=roots_46) (T1:=gsh_46_16) [(dom_46,16)] (by decide +kernel) (lower_slice_b (T:=gsh_46_16) [(0x505000005050,0,4)] (by decide +kernel) lowS_42)
namespace S_62
def pG:List (Nat×Nat):=[(2,10),(2,34),(4,20),(4,36),(6,14),(6,22),(6,38),(8,10),(8,40),(12,14),(12,28),(12,44),(16,20),(18,22),(18,26),(18,50),(24,26),(24,28),(24,56),(32,34),(32,36),(32,40),(48,50),(48,52),(48,56)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1ffffff
def xsM:=roots_62.map (·&&&dom_62)
def gM:=goal_62&&&dom_62
def NN:Nat→Nat
|4=>2
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xae7d077c2a
|5,0=>0xf6ea34f5852440f
|6,0=>0xaaa4e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x2aa22aa22aa22aa25555555544444444aa00aa00aa00aa00444444440000000002a802a802200225555555500000000aaaa0000aaaa000154015401100110028282828282828284444444444444444
|_,_=>0
def sP:Nat→Nat
|0=>0x437104397108437104371064310543210
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x15405
|5,0=>0x166418a6
|6,0=>0x1c5
|_,_=>0
def wAt:=mkWire dB 10 63 0x7fffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x103
|_=>0
def oO:Nat→Nat→Nat
|5,0=>1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 5
def pmP:Nat→Nat
|0=>0xf9c40
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x16
|6,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 2 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_46 5 roots_46 ops++addP pm 1 dom_60 4 roots_60 ops++addP pm 2 dzo_46_16 5 roots_46 ops++addP pm 3 dom_42 4 roots_42 ops++addP pm 4 dom_54 4 roots_54 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_62 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_46 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_60 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_46_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_54 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_46 5 s (0,roots_46.map (·&&&dom_46)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_62 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_46 h
def symsG:List (List (Nat×Nat)):=[[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_62==dom_62)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_62 gM v ys):RunD true dom_62 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_62 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_62 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_62 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_62 roots_62 goal_62 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_62
theorem lowS_62:Lower true dom_62 roots_62 goal_62 7:=S_62.noCircuit
theorem lowS_107:Lower true dom_107 roots_107 goal_107 8:=lower_slice_b [(0xa0a00000a0a00000a0a00000a0a,8,9)] (by decide +kernel) lowS_106
theorem lowS_109:Lower true dom_109 roots_109 goal_109 8:=lower_slice_b [(0x3030000030300000303000003030,32,36)] (by decide +kernel) lowS_105
theorem lowS_117:Lower true dom_117 roots_117 goal_117 6:=lower_slice_b [(0x220022002200220022002200220022,16,17)] (by decide +kernel) lowS_116
theorem lowS_121:Lower true dom_121 roots_121 goal_121 8:=lower_slice_b [(0x3030000030300000303000003030000,1,17)] (by decide +kernel) lowS_105
theorem lowS_143:Lower true dom_143 roots_143 goal_143 6:=lower_slice_b [(0xaaaa0000000000000000000000000000aaaa,8,9)] (by decide +kernel) lowS_142
namespace S_158
def pG:List (Nat×Nat):=[(2,10),(2,130),(4,20),(4,132),(6,14),(6,22),(6,134),(8,10),(8,136),(12,14),(12,28),(12,140),(16,20),(16,144),(18,22),(18,26),(18,146),(24,26),(24,28),(24,152),(128,130),(128,132),(128,136),(128,144)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_158.map (·&&&dom_158)
def gM:=goal_158&&&dom_158
def NN:Nat→Nat
|3=>1
|4=>4
|5=>10
|6=>4
|7=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x124b0
|4,0=>0x3dec70b22607559042bb
|5,0=>0x7ad8671c83439753853529d7a1dd2510db10900506480055d3
|6,0=>0x7fdda4c31a2089208b1f
|7,0=>0x7fdda
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaaaaaa001414141400000000000000000000000000000002aa82aa80000000000000000000000002aa82aa85555555500000000000000000000000050505050a2a2a2a2000000000000000000000000a0a0a0a044004444000000000000000000000000440044002828282800000000000000000000000028282805555555500000000000000000000000055550000aa00aa00000000000000000000000000aa00aa0155555400000000000000000000000000000000022222222000000000000000000000000222222225555555500000000000000000000000000000000aaaa0000000000000000000000000000aaaa000155515550000000000000000000000001540154028282828000000000000000000000000282828285555555500000000000000000000000044444444
|0,1=>0x15555555400000000000000000000000151515152a2a2a2a0000000000000000000000002a2a2a2a5454545400000000000000000000000000000000000022220000000000000000000000000000000001540154000000000000000000000000011001102828282800000000000000000000000028280000055005500000000000000000000000000500050
|_,_=>0
def sP:Nat→Nat
|0=>0xce12906709483384a470cf50948819c2520cf609483384a4a0ce1292630964440ce5890670960478ce1290676148e1b4ec29067584a419c2a20ce549107094c3104a418820
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|4,0=>0x26a3944a845
|5,0=>0x26b47682cf15b330654c918f3186
|6,0=>0xcab7dacb536
|7,0=>0x6a5
|_,_=>0
def wAt:=mkWire dB 23 159 0x7fffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x92095191615091a90407191091292
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x52410000220000001101
|6,0=>0x918171
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 8
def pmP:Nat→Nat
|0=>0xffbce260f30a200
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x3400600251
|6,0=>0x7898
|7,0=>9
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 6 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_156 5 roots_156 ops++addP pm 1 dom_154 5 roots_154 ops++addP pm 2 dom_148 4 roots_148 ops++addP pm 3 dom_138 4 roots_138 ops++addP pm 4 dom_150 5 roots_150 ops++addP pm 5 dom_142 5 roots_142 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_158 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_156 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_138 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_150 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_142 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_156 5 s (0,roots_156.map (·&&&dom_156)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_158 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_156 h
def symsG:List (List (Nat×Nat)):=[[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_158==dom_158)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_158 gM v ys):RunD true dom_158 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_158 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 4 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
theorem checked (s:Nat) (hs:s≤7):∀ i<NN s,bar dom_158 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤7) (h:RunD true dom_158 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_158 roots_158 goal_158 8:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_158
theorem lowS_158:Lower true dom_158 roots_158 goal_158 8:=S_158.noCircuit
namespace S_173
def pG:List (Nat×Nat):=[(1,9),(1,33),(4,36),(4,132),(5,13),(5,37),(5,133),(8,9),(8,40),(8,136),(12,13),(12,44),(12,140),(32,33),(32,36),(32,40),(32,160),(128,132),(128,136),(128,160),(129,133),(129,137),(129,161)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffff
def xsM:=roots_173.map (·&&&dom_173)
def gM:=goal_173&&&dom_173
def NN:Nat→Nat
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x4866c
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x33330000000000000000000000000000333300000000cc000000cc0000000000000000000000cc000000cc0303000003030000000000000000000003030000030308888000088880000000000000000000088880000888b3330000333300000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x4688
|_=>0
def sO:Nat→Nat→Nat
|6,0=>5
|_,_=>0
def wAt:=mkWire dB 5 174 0x3fffffffffffffffffffffffffffffffffffffffffff
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
addP pm 0 dom_172 5 roots_172 ops++addP pm 1 dom_45 5 roots_45 ops++addP pm 2 dom_169 5 roots_169 ops++addP pm 3 dom_165 5 roots_165 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_173 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_172 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_169 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_165 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_172 5 s (0,roots_172.map (·&&&dom_172)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_173 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_172 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_173==dom_173)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_173 gM v ys):RunD true dom_173 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_173 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_173 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_173 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_173 roots_173 goal_173 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_173
theorem lowS_173:Lower true dom_173 roots_173 goal_173 7:=S_173.noCircuit
namespace S_234
def pG:List (Nat×Nat):=[(2,10),(2,34),(2,66),(2,130),(8,10),(8,40),(8,72),(8,136),(32,34),(32,40),(32,96),(32,160),(64,66),(64,72),(64,96),(64,192),(128,130),(128,136),(128,160),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffff
def xsM:=roots_234.map (·&&&dom_234)
def gM:=goal_234&&&dom_234
def NN:Nat→Nat
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|8,0=>0x83d77
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x50500000000000005050000000000000505000000000000050500000000a0000000a0000000a0000000a0000000a0000000a0000000a0000000a0101000001010000010100000101000001010000010100000101000001012828000028280000000000000000000028280000282800000000000000050500000505000005050000050500000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x4688
|_=>0
def sO:Nat→Nat→Nat
|8,0=>5
|_,_=>0
def wAt:=mkWire dB 5 235 0x7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
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
addP pm 0 dom_232 7 roots_232 ops++addP pm 1 dom_170 7 roots_170 ops++addP pm 2 dom_226 7 roots_226 ops++addP pm 3 dom_202 7 roots_202 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_234 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_226 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_202 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_232 7 s (0,roots_232.map (·&&&dom_232)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_234 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_232 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xffffffff000000000000000000000000ffffffff00000000,32)],[(0xffffffff00000000ffffffff00000000,96)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)],[(0xff00ff00ff00ff00ff00ff00ff00ff00,120)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_234==dom_234)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_234 gM v ys):RunD true dom_234 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_234 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_234 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_234 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_234 roots_234 goal_234 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_234
theorem lowS_234:Lower true dom_234 roots_234 goal_234 9:=S_234.noCircuit
def isoMvS_87:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_87:Lower true dom_87 roots_87 goal_87 5:=lower_iso_b isoMvS_87 (by decide +kernel) lowS_55
def isoMvS_93:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_93:Lower true dom_93 roots_93 goal_93 6:=lower_iso_b isoMvS_93 (by decide +kernel) lowS_61
def isoMvS_94:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_94:Lower true dom_94 roots_94 goal_94 7:=lower_iso_b isoMvS_94 (by decide +kernel) lowS_62
def isoMvS_110:List (Nat×Nat):=[(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_110:Lower true dom_110 roots_110 goal_110 8:=lower_iso_b isoMvS_110 (by decide +kernel) lowS_109
def isoMvS_118:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_118:Lower true dom_118 roots_118 goal_118 7:=lower_iso_b isoMvS_118 (by decide +kernel) lowS_59
def isoMvS_124:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_124:Lower true dom_124 roots_124 goal_124 7:=lower_iso_b isoMvS_124 (by decide +kernel) lowS_59
def isoMvS_151:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_151:Lower true dom_151 roots_151 goal_151 6:=lower_iso_b isoMvS_151 (by decide +kernel) lowS_143
def isoMvS_157:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_157:Lower true dom_157 roots_157 goal_157 6:=lower_iso_b isoMvS_157 (by decide +kernel) lowS_61
def isoMvS_171:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_171:Lower true dom_171 roots_171 goal_171 8:=lower_iso_b isoMvS_171 (by decide +kernel) lowS_109
def isoMvS_174:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_174:Lower true dom_174 roots_174 goal_174 8:=lower_iso_b isoMvS_174 (by decide +kernel) lowS_109
def isoMvS_181:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_181:Lower true dom_181 roots_181 goal_181 6:=lower_iso_b isoMvS_181 (by decide +kernel) lowS_117
def isoMvS_182:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_182:Lower true dom_182 roots_182 goal_182 7:=lower_iso_b isoMvS_182 (by decide +kernel) lowS_173
def isoMvS_185:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_185:Lower true dom_185 roots_185 goal_185 6:=lower_iso_b isoMvS_185 (by decide +kernel) lowS_117
def isoMvS_186:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_186:Lower true dom_186 roots_186 goal_186 8:=lower_iso_b isoMvS_186 (by decide +kernel) lowS_121
def isoMvS_188:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_188:Lower true dom_188 roots_188 goal_188 7:=lower_iso_b isoMvS_188 (by decide +kernel) lowS_173
def isoMvS_203:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_203:Lower true dom_203 roots_203 goal_203 8:=lower_iso_b isoMvS_203 (by decide +kernel) lowS_109
def isoMvS_205:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_205:Lower true dom_205 roots_205 goal_205 7:=lower_iso_b isoMvS_205 (by decide +kernel) lowS_173
def isoMvS_213:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_213:Lower true dom_213 roots_213 goal_213 6:=lower_iso_b isoMvS_213 (by decide +kernel) lowS_117
def isoMvS_214:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_214:Lower true dom_214 roots_214 goal_214 7:=lower_iso_b isoMvS_214 (by decide +kernel) lowS_173
def isoMvS_217:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_217:Lower true dom_217 roots_217 goal_217 6:=lower_iso_b isoMvS_217 (by decide +kernel) lowS_117
def isoMvS_220:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_220:Lower true dom_220 roots_220 goal_220 7:=lower_iso_b isoMvS_220 (by decide +kernel) lowS_173
def isoMvS_227:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_227:Lower true dom_227 roots_227 goal_227 8:=lower_iso_b isoMvS_227 (by decide +kernel) lowS_109
def isoMvS_229:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_229:Lower true dom_229 roots_229 goal_229 8:=lower_iso_b isoMvS_229 (by decide +kernel) lowS_109
def isoMvS_230:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_230:Lower true dom_230 roots_230 goal_230 8:=lower_iso_b isoMvS_230 (by decide +kernel) lowS_107
def isoMvS_233:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_233:Lower true dom_233 roots_233 goal_233 8:=lower_iso_b isoMvS_233 (by decide +kernel) lowS_107
def isoMvS_236:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_236:Lower true dom_236 roots_236 goal_236 8:=lower_iso_b isoMvS_236 (by decide +kernel) lowS_107
def isoMvS_241:List (Nat×Nat):=[(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_241:Lower true dom_241 roots_241 goal_241 6:=lower_iso_b isoMvS_241 (by decide +kernel) lowS_117
def isoMvS_242:List (Nat×Nat):=[(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_242:Lower true dom_242 roots_242 goal_242 8:=lower_iso_b isoMvS_242 (by decide +kernel) lowS_121
def isoMvS_244:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_244:Lower true dom_244 roots_244 goal_244 8:=lower_iso_b isoMvS_244 (by decide +kernel) lowS_109
def isoMvS_248:List (Nat×Nat):=[(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_248:Lower true dom_248 roots_248 goal_248 8:=lower_iso_b isoMvS_248 (by decide +kernel) lowS_121
def dzo_47_16:=0xffff0000ffff0000
def gzo_47_16:=0xfffe0000fefa0000
def gsh_47_16:=0xfffe0000fefa
theorem lowS_zo_47_16_42:Lower true dzo_47_16 roots_47 gzo_47_16 6:=lower_iso_b (d1:=dom_47) (r1:=roots_47) (T1:=gsh_47_16) [(dom_47,16)] (by decide +kernel) (lower_slice_b (T:=gsh_47_16) [(0xaaaa0000aaaa,0,1),(0xf0f00000f0f0,0,4)] (by decide +kernel) lowS_42)
namespace S_63
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(2,10),(2,34),(3,11),(3,19),(3,35),(4,20),(4,36),(5,13),(5,21),(5,37),(6,14),(6,22),(6,38),(7,15),(7,23),(7,39),(8,9),(8,10),(8,40),(12,13),(12,14),(12,28),(12,44),(16,17),(16,20),(18,19),(18,22),(18,26),(18,50),(24,25),(24,26),(24,28),(24,56),(32,33),(32,34),(32,36),(32,40),(48,49),(48,50),(48,52),(48,56)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_63.map (·&&&dom_63)
def gM:=goal_63&&&dom_63
def NN:Nat→Nat
|4=>5
|5=>15
|6=>37
|7=>10
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xf1020923f59089f6129a2d780
|5,0=>0xe2aafdfcf6d9245cdbbcca973bc4f1b08c8a544199818971348e1da428452133316de40ba3d
|6,0=>0xf47e6e62f6ddd8bdd808cf6b2cf246bad5eb52c4b40d5b30d0b17a7a528aa43039c2ed9ba9c96bec91e73908be8e1da888bc84f7c7c4e3785bc758e072b0e692a4664126324a5ce5b5a9d24d95439e342b5df2b4e3241930779704701
|7,0=>0xf8293dd808d42517adc35f7114f362414e64017b29ed429720
|8,0=>0xc6758
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xff33ff33ff00ff0000000000ffff000033333333000000003300330033003300ffffffff00000000ff00ff00ff00ff00fefefefefefafefaeeeeeeeeeeaaeeaaffaaffaaaaaaaaaa333333333300330000ff00ffff00ff00ffffffffff00ff00ffff0000ffff0000f0f0f0f0f0f0f0f0aaaaaaaaaaaaaaaa0033003333003300
|0,1=>0xccccccccffccffcc00000000ff00ff00ffff3333ffff000000ff00ff00000000ff000000ffff0000cc00cc00ff00ff000000000033003300ffccffccccccccccffffffff33003300ffffffffccccccccffccffccffccffcc00000000ffccffcccccccccccc00cc00ccccccccccccccccff00ff0000000000ffffffffffff0000
|0,2=>0xfff0fff0f0f0f0f000ff0000ffff0000ffffffffffccffcc00cc00ccccccccccffffff00ffff0000ffff00ffffff0000
|_,_=>0
def sP:Nat→Nat
|0=>0x48150b0ca0920591160ca0920440d80815c328204d1160d508140a0920541031c24842c32822040c248114b0ca0880c24811440d108118b0ca0811902ca08118b0cf08130b2820463840c204d30b0ca2481031c21830811400c20461440c2040
|1=>0xca0920464042ca09204309205c78b0ca0811902ca09205e2e12824812e02824815cb0ca09204b0ca09f4812c360a08158b0d52820442ca09204e2c33ca09204b28248139e2c31ca09210328248134b74a09204b29b09204b0ca0926812c3282
|2=>0xca09204d2c354a09204b0ca09205c2c32824813102d528248110b0ca0930502ca09204c10b0ca0920440d109204b0ca0930442c35424812c394a4812ca0920648cb0ca09204b0d509205e10b0ca0811842c309204c2c32820622c328204d30b
|3=>0xb0ca0920562c328248110b0ca09204b0ca09205e40b2824812c329109204b28248138b
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x14507a82940aa005
|5,0=>0x1a94c8c5e62c314d49ac4762128f546ec31615b09583ec196
|6,0=>0x15e7abbd41e92f4369eb4d9e60d2a691bc71e2af0e7843405df4ef3776b39d9c0eda66a3335d8cec065cbac9d56ea474f325dd22c8b64239f5cece6f7
|7,0=>0x344f9b7ca3e39b0ef816bd3dcded8f657
|8,0=>0x1a96
|_,_=>0
def wAt:=mkWire dB 38 64 0xffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xb492ca4b2a2c34b282c38b4b2924b2b292cb0d2c34b282ca44482ca4b294424b280d1cb282ca8b292ca514a2ca0b2b2ca844b2ca43452ca03712cad1492ca0b294414b282ca43352d2c3732caca372ca4b294524b282ca4b294414b284c144482ca44472ca0b29
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0xa30009100063000000cc03000000000000000
|6,0=>0x301002f1002d2acaa1a0a62002519063184800000007c9d2001b26480000172001610000050931448f238400000d1
|7,0=>0xe8791e0771d8751d0731c8711
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 10
def pmP:Nat→Nat
|0=>0xf9fe5ebf6fdb767c9705c04d4304a021c8218049120421002f088200580e00c0200400
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0xc070144220c0000000
|6,0=>0x7119cf41e33018d06000a88533a001112c09936b368007
|7,0=>0x31ad5b77be779
|8,0=>0x15
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 10 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_62 7 roots_62 ops++addP pm 1 dom_29 4 roots_29 ops++addP pm 2 dom_59 7 roots_59 ops++addP pm 3 dom_45 5 roots_45 ops++addP pm 4 dom_54 4 roots_54 ops++addP pm 5 dom_61 6 roots_61 ops++addP pm 6 dom_31 5 roots_31 ops++addP pm 7 dom_55 5 roots_55 ops++addP pm 8 dzo_47_16 6 roots_47 ops++addP pm 9 dom_47 6 roots_47 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_63 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_29 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_47_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_47 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_62 7 s (0,roots_62.map (·&&&dom_62)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_63 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_62 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_63 gM v ys):RunD true dom_63 gM v (ori ys):=h
def Z (s:Nat):=barP dom_63 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 5 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 15 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 37 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 37 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 10 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_63 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_119:Lower true dom_119 roots_119 goal_119 8:=lower_slice_b [(0xaa00aa00aa00aa00aa00aa00aa00aa,16,17)] (by decide +kernel) lowS_118
theorem lowS_125:Lower true dom_125 roots_125 goal_125 9:=lower_slice_b [(0x30303030303030303030303030303030,16,20)] (by decide +kernel) lowS_121
def dzo_110_16:=0x55550000555500005555000055550000
def gzo_110_16:=0x55550000555400005554000054500000
def gsh_110_16:=0x5555000055540000555400005450
theorem lowS_zo_110_16_106:Lower true dzo_110_16 roots_110 gzo_110_16 8:=lower_iso_b (d1:=dom_110) (r1:=roots_110) (T1:=gsh_110_16) [(dom_110,16)] (by decide +kernel) (lower_slice_b (T:=gsh_110_16) [(0x5050000050500000505000005050,0,4)] (by decide +kernel) lowS_106)
namespace S_126
def pG:List (Nat×Nat):=[(2,10),(2,34),(2,66),(4,20),(4,36),(4,68),(6,14),(6,22),(6,38),(6,70),(8,10),(8,40),(8,72),(12,14),(12,28),(12,44),(12,76),(16,20),(18,22),(18,26),(18,50),(18,82),(24,26),(24,28),(24,56),(24,88),(32,34),(32,36),(32,40),(32,96),(48,50),(48,52),(48,56),(48,112),(64,66),(64,68),(64,72),(64,96),(80,82),(80,84),(80,88),(80,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_126.map (·&&&dom_126)
def gM:=goal_126&&&dom_126
def NN:Nat→Nat
|4=>3
|5=>15
|6=>35
|7=>15
|8=>3
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xb1e139818219e6a
|5,0=>0xcf37aa8164a7bdb9081b88e4e7c75673efb731ed6d7bf36d91298c3214eb116650a922042be
|6,0=>0xdb587d2e059081b7c1dc7c1c86dfc06dcee58875559cf4af36496523c07f3b4ed36df536da4333d133088310d7306b92f87e2a4fe27b562503221eaf19fce13dc1133bf11d3e0ddcc0d3ec08c000523403991009e0008fe
|7,0=>0x916de8322182ed8705636806f5374b52da0330f73047e2ffcc23990224b00d1e10a0c301539
|8,0=>0xe6db0e296500935
|9,0=>0x464f4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaaaaaaaaaaaaaaaaaaaaaaaaaa00aa0044444444444444444400440044004402aaaaaaa800000002aaaaaaa8000000055555555444444445555555544444444aaaaaaaaaa00aa00888888888800880155555555555555540000000000000002aaaaaaaaa2a2a2a2aa82aa82a282a28550055005500550055005500550055008888888888888888888888888888888955555555540154015555555554015402aaaaaaaaaaaaaaaa22222222222222255555555555555555555555500000000aaaa0000aaaa0000aaaa0000aaaa000155115511551155115511551155115512aaaaaaaa22222222a802a802200220050505050505050505050505050505050
|0,1=>0xaa00aa00aa00aa008800880088008954015401555555555401540155115512aaaaaaaaaaaaaaaaaaaaaaaaaa22aa255555555111111115555555511001100aa00aa00aa00aa00aa00aa0088008801555555555555555555555555111111100000000000000002aaaaaaaaa802a80000000000000000055555555554455448888888888888888888888888800880001540154015401540154015400000000888888888888888888888888880088011111111111111111111111100000000aaaaaaaaaaaaaaaaaa88aa88aa88aa8955555555551155115555555555115512aaaaaaaaaaaaaaaaa802a802a802a8000000000000000005555555544444444
|0,2=>0x5500550044004400550055004400440022002200220022002200220000000000000001555555540000000111111112a88aa88aa88aa88aa88aa88aa802a8000000000000000001111111111001100
|_,_=>0
def sP:Nat→Nat
|0=>0x1d464c0c80072983432001ca30d0c244028d0c05d628d0c200b28630344014d0c801528d0c92072860d100750c1034c801234344014f3032001440c80072cc10309100640308028f34308014610300738c0c800b2840c92071830401440c2040
|1=>0x30308028d0de2001ca10d0c24401c61034401c434320054a30d0d120015d3432001ca1840c80051da34344800770d0c80072921032001ca3cd0c801528d0db0051ca18d0c801529a34308800a3432001cb28c34320050a1840c01d628d0d1200
|2=>0x34309100729230d0c800729a30d0c80072863434401ca18d0c80051ca3432001e328f3432005ca34320054a10d0db00728d0c220088a10d0c80077cd0c800754a34384800728f34300758a30d0d320028d0c801728d0c800780a30d0c801f286
|3=>0x3432001ca10d0c800728d0c22001ca30d0c80072843432001d62843430880072861032001ca3c43432001ca48d0c800728d0d120014768d0c800728d0c800790a3432001d42993432001ca
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x2940aa005
|5,0=>0x18d8bac57628b12d88ac3f61cb0cd85ac27610b06d82ac0f6
|6,0=>0x54de98f4669fbce1e62f2a791bc71e2af0f6843c05df6cf4776bb9d9c0ed97693b2dd88ebd75b3abdd50ea174d3a4dd18e8573f39ddce0e697
|7,0=>0x7063731b27d5468df38f957c73e1df00f797b8c5a62c4f5a8
|8,0=>0x75dfa0fc97
|9,0=>0x1de6
|_,_=>0
def wAt:=mkWire dB 37 127 0x7fffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x14847293c7062920d45231ca481d348473528d482934a48353c7c42134a4c291cd511f20a461d20d462920d5a2014d4f1f18a4c291cd461420d4729687cc291cd442334a441f28d4a1a20d522b308473518508351ca45211ca4c213474d4528846141ca483528d462920d45182874d21
|1=>0xd292074735108cd292074d2934a48351084d293084735288472930a4735308c735107cd2918ac8351c84829308473530a473520a483520d4729214841f34a4f1f18a4835688041d34a4d161ca45231ca441f34a4f2318a4835
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x79800000000000d2164248318510000c800003
|6,0=>0x13cc004c39271ca2900086500df13b3000e49b18006a2c8d79800000001692b25249c92923242478cd99922e454891800
|7,0=>0x1b8b616a2d0598b21622c0578ae15a2b0558aa1522
|8,0=>0x1c8788f01
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0x5344ef4053eb3693012f71ef1eb0ff0fd0ef0eb0c507f06b04d04904504104002e02802402001000c00a008004002000
|1=>0xcefc06ae75ff
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x200000003042106002005
|6,0=>0xd00c3c70c01da0d20035401933800001c30420871d47491c22c0
|7,0=>0x104576e08637946197e270a
|8,0=>0x1459e
|9,0=>0x14
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 12 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_110 8 roots_110 ops++addP pm 1 dom_62 7 roots_62 ops++addP pm 2 dom_124 7 roots_124 ops++addP pm 3 dom_94 7 roots_94 ops++addP pm 4 dom_116 5 roots_116 ops++addP pm 5 dom_118 7 roots_118 ops++addP pm 6 dzo_110_16 8 roots_110 ops++addP pm 7 dom_106 7 roots_106 ops++addP pm 8 dom_86 4 roots_86 ops++addP pm 9 dom_54 4 roots_54 ops++addP pm 10 dom_92 4 roots_92 ops++addP pm 11 dom_60 4 roots_60 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_126 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_110_16_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_92 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_60 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_110 8 s (0,roots_110.map (·&&&dom_110)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_126 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_110 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_126==dom_126)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_126 gM v ys):RunD true dom_126 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_126 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 15 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 35 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 35 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 15 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 3 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_126 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_175:Lower true dom_175 roots_175 goal_175 9:=lower_slice_b [(0xaaaa0000aaaa00000000000000000000aaaa0000aaaa,8,9)] (by decide +kernel) lowS_174
theorem lowS_183:Lower true dom_183 roots_183 goal_183 8:=lower_slice_b [(0xaa00aa00aa00aa000000000000000000aa00aa00aa00aa,16,17)] (by decide +kernel) lowS_182
namespace S_189
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(4,20),(4,36),(4,132),(5,13),(5,21),(5,37),(5,133),(8,9),(8,40),(8,136),(12,13),(12,28),(12,44),(12,140),(16,17),(16,20),(16,144),(24,25),(24,28),(24,56),(24,152),(32,33),(32,36),(32,40),(32,160),(48,49),(48,52),(48,56),(48,176),(128,132),(128,136),(128,144),(128,160),(129,133),(129,137),(129,145),(129,161)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_189.map (·&&&dom_189)
def gM:=goal_189&&&dom_189
def NN:Nat→Nat
|5=>3
|6=>5
|7=>4
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0xe425c4646e3bbfb
|6,0=>0x9f0e48741685b147771f50839
|7,0=>0xcf2a17dfef60ace103e1
|8,0=>0x3abd3
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xccccccccc0c0c0c00000000000000000ccccccccc0c0c0c333033303330333000000000000000003330333033303330cccccccccccccccc0000000000000000cc88cc88cc88cc8b33333333333333300000000000000003300330033003300cccccccccccccccc0000000000000000cccccccc8888888a22222222222222200000000000000002222222222222222cccccccccccccccc0000000000000000cccccccc0000000333333333333333300000000000000003333333333330000cccccccccccc00000000000000000000cccccccccccc000330033003300330000000000000000003300330033003300cccccccc000000000000000000000000cccccccc0000000333300003333000000000000000000003333000033330000c0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0c0c33333333333333330000000000000000222222222222222200cc00cc00cc00cc000000000000000000cc00cc0088008b33333333333333300000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x5463a095463a0f5463a07563a054e63a054d632075632054c632b5463207963a079632875632543210
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x31433006
|6,0=>0x2a748c798bb916
|7,0=>0x8aef9dc3317
|8,0=>0x4c6
|_,_=>0
def wAt:=mkWire dB 16 190 0x3fffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1413551563681a051506681a054145515
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x100
|6,0=>0x8162423112
|7,0=>0xc1b1a191
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0xbc9bf4dda67d3070006000c000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>8
|6,0=>0x29dd
|7,0=>0x934
|8,0=>4
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 13 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_188 7 roots_188 ops++addP pm 1 dom_57 5 roots_57 ops++addP pm 2 dom_45 5 roots_45 ops++addP pm 3 dom_180 5 roots_180 ops++addP pm 4 dom_181 6 roots_181 ops++addP pm 5 dom_156 5 roots_156 ops++addP pm 6 dom_157 6 roots_157 ops++addP pm 7 dom_149 5 roots_149 ops++addP pm 8 dom_185 6 roots_185 ops++addP pm 9 dom_61 6 roots_61 ops++addP pm 10 dom_173 7 roots_173 ops++addP pm 11 dom_141 4 roots_141 ops++addP pm 12 dom_60 4 roots_60 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_189 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_188 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_180 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_156 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_149 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_141 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_60 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_188 7 s (0,roots_188.map (·&&&dom_188)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_189 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_188 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff00000000ffffffff00000000,96),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_189==dom_189)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_189 gM v ys):RunD true dom_189 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_189 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 5 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 4 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_189 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_189 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_189 roots_189 goal_189 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_189
theorem lowS_189:Lower true dom_189 roots_189 goal_189 9:=S_189.noCircuit
namespace S_190
def pG:List (Nat×Nat):=[(2,10),(2,34),(2,130),(4,20),(4,36),(4,132),(6,14),(6,22),(6,38),(6,134),(8,10),(8,40),(8,136),(12,14),(12,28),(12,44),(12,140),(16,20),(16,144),(18,22),(18,26),(18,50),(18,146),(24,26),(24,28),(24,56),(24,152),(32,34),(32,36),(32,40),(32,160),(48,50),(48,52),(48,56),(48,176),(128,130),(128,132),(128,136),(128,144),(128,160)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_190.map (·&&&dom_190)
def gM:=goal_190&&&dom_190
def NN:Nat→Nat
|6=>1
|7=>5
|8=>2
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0xc7549
|7,0=>0xb27668862485897833ba0724b
|8,0=>0xe260976607
|9,0=>0xf79e0
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x15401540154015400000000000000000110011001100112aaaaaaaaaaaaaaa80000000000000002aa22aa22aa22aa2550055005500550000000000000000005500550055005500888888888888888800000000000000008888888888888889555555555555555400000000000000000000000000000002aaaaaaa8000000000000000000000002aaaaaaa80000000555500005555000000000000000000005555000055550000aa88aa88aa88aa880000000000000000aa88aa88aa88aa8955555555555555540000000000000001540154015401540282828282828282800000000000000002828282828282828555555555555555500000000000000004444444444444444
|_,_=>0
def sP:Nat→Nat
|0=>0x5481765438176542817654817a654981765428107543810654928176543210
|_=>0
def sO:Nat→Nat→Nat
|6,0=>6
|7,0=>0x23771d5739c68
|8,0=>0xc5ea7
|9,0=>0x386
|_,_=>0
def wAt:=mkWire dB 11 191 0x7fffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x21d864237649d865d9865e17649d86619785d9
|_=>0
def oO:Nat→Nat→Nat
|6,0=>3
|7,0=>0xb292725232
|8,0=>0xe1d1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0x1ffe35fe7eff5f9fc7e00
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>1
|7,0=>0x28647
|8,0=>0x35
|9,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 9 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_186 8 roots_186 ops++addP pm 1 dom_188 7 roots_188 ops++addP pm 2 dom_182 7 roots_182 ops++addP pm 3 dom_62 7 roots_62 ops++addP pm 4 dom_158 8 roots_158 ops++addP pm 5 dom_174 8 roots_174 ops++addP pm 6 dom_60 4 roots_60 ops++addP pm 7 dom_180 5 roots_180 ops++addP pm 8 dom_54 4 roots_54 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_190 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_188 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_174 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_60 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_180 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_54 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_186 8 s (0,roots_186.map (·&&&dom_186)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_190 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_186 h
def symsG:List (List (Nat×Nat)):=[[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_190==dom_190)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_190 gM v ys):RunD true dom_190 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_190 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 5 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 2 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_190 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
namespace S_235
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(2,10),(2,34),(2,66),(2,130),(3,11),(3,35),(3,67),(3,131),(8,9),(8,10),(8,40),(8,72),(8,136),(32,33),(32,34),(32,40),(32,96),(32,160),(64,65),(64,66),(64,72),(64,96),(64,192),(128,130),(128,136),(128,160),(128,192),(129,131),(129,137),(129,161),(129,193)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffff
def xsM:=roots_235.map (·&&&dom_235)
def gM:=goal_235&&&dom_235
def NN:Nat→Nat
|4=>4
|5=>71
|6=>147
|7=>80
|8=>21
|9=>4
|10=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x7c1b44a09a2d71f06929
|5,0=>0xc1d67a24ef8fa407c89f721ef6d6206892e679ba617d75fa165c7d95680455c1f54bbb54a9851a264f0b04e92f4a3d54889d46ea9458583f55f3d9953d83a3bd3e394ea36ae035797348fa3453032ebc31a0b300292add02a96929dfe253782361922842222c421df12107120a9e209f5208f51eb8b1e2291c1371b830166e3166dc154a514d1014a9912211119f71099a0dadc0c3310b29409f35094c608fff08aab073b60718a06d6006003047d5016f1
|6,0=>0x6a72662b59623ed617d760f7f5d69f5d1735d0225c35459d1b56d2c5551054f6a4a8074a63249a534670745d584465642702410d640fc240ce6403d2400653e52b3e2ee3b1b13b1713abdf396ad38c193807236ae0358a93453033aaf3388f3264f3238b3133630b6b2fc382f9802f5912e4572d2202ce2f2c3702bb532a9f9298872836a2700426eaf260f622db0229fb224a1209381ff751fe441fc1e1f8de1f1581e35b1df6e1d23a1cdb41bbab1b4b51abe01a9b71a083196161950818d8818cfa189b5184211823717c8b176a416fa316b0415e9c1565114a851460614322142b812e9612af2119f0104040f6030ed970ea580e8100e7bb0cd830be140b5dd0a8eb0a78e0a5900a40609a940965908f3708e3a08e2208dbc067330663c053e404eb904bca047fa0438004312041260408a03feb02582024fe0199a00e3d
|6,1=>0xb6e95b25bbaec07a8740a6d659ea7c95f0789b3a879ca80e9e7eeb57c2097a54c788367843c71369709bf6e87d6dab7
|7,0=>0xe72dae2b71aec078ea3a8aeef742956fed0623345636754a0052c004c5b64bbbc43c6d43a7e3f65a3f5ef3e6743da1938a3b380a3377fd336b73290e30f342eb812d3062915a2830327f7624c06249c123b5f22c7b20bb51fab71f8da1eeaf1e5901d50f1cd051bdd51b8cf1b4d61976e176301688912fc6121a710f3710af40e2490de7b0dc0d0d3e70c4e90c4410b3d20b3630adf70ab8809ade098520902908827083e4080b307e00055d7055be04b18047280443702bdf026c0024c801d300168e00ffe0065a
|8,0=>0xa773a8781b76f7a61f5d52d495097841c4d3891e303302fb992be2925d2424f140e79c0ca6c097990863504e7b031d203047020d4
|9,0=>0x9c31e88bd02ff10040d9
|10,0=>0xfffda
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f00000f0f00000f0f00000f0f00000f0f00000f0000000c0c00000c00f0f00000f0f00000f0f00000f0f00000a0a00000a0a00000a0a00000a0a00f0000000f0000000f0000000f0000000f0000000f0000000f0000000000000000f0f0000000000000f0f0000000000000f0f0000000000000f00f0f00000f0f00000f0f0000000000000f0000000f0000000f0000000000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0cf0f00000f0f00000f0f0000000000000f0f00000f0f00000f0f00000000f0f00000f0f00000f0f00000f0f00000f0000000f0000000f0000000f00f0f0000000000000f0f0000000000000f0f0000000000000f0f00000000f0f00000f0f000000000000000000000f0f00000f0f0000000000000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000f00f0f00000f0f00000f0f00000f0f00000000000000000000000000000000f0f00000f0000000f0f00000f0000000f0f00000f0000000f0f00000f00f0f00000f0f00000f0f00000c0c00000f0c00000f0c00000f0c00000c0ca0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0af0f00000f0f00000f0f00000f0f00000f0f00000f0f0000000000000000
|0,1=>0x10100000101000001010000010000000101000001010000010100000100f0f00000f0f00000f0f00000f0c00000f0f00000f0f00000f0f00000f0c00000000f0f0000000000000f0c0000000000000f0f0000000000000f0c00000000000000000000000000000000f0f00000f0f00000f0f00000f0cf0f00000f0f00000f0f00000f0000000f0f00000f0f00000f0f00000f00f0f00000f0c00000f0f00000f0c00000f0f00000f0c00000f0f00000f0c00f0000000f0000000f0000000c0000000f0000000f0000000f0000000cf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f00f0f00000f0f00000f0c00000f0c00000f0f00000f0f00000f0c00000f0ce0e00000e0e00000e0e00000e0e00000e0e00000e0e00000e0e00000e0e0000000000000000f0f00000f0f000000000000000000000f0f00000f00f0f00000f0000000c0c00000c0000000f0f00000f0000000c0c00000c00f0f00000f0f00000c0c00000c0c00000f0f00000f0f00000c0c00000c0cf0f00000c0c00000f0f00000c0c00000f0f00000c0c00000f0f00000c0cf0f00000f0f00000f0000000f0000000f0f00000f0f00000f0000000f00
|0,2=>0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0000000f003030000030300000303000003030000030300000303000003030000030000000000000000000000000000000000d0d00000d0d00000d0d00000d0cf0f00000f0f00000f0f00000f0f000005050000050500000505000005003030000030300000303000003030000010100000101000001010000010000000000000000003030000030000000000000000000000030300000300f0f00000f0f000003030000030000000f0f00000f0f000003030000030050500000505000005050000050000000505000005050000050500000500f0f00000f0f0000000000000f0f00000f0f00000f0f0000000000000f00f0f00000f0f00000f0f00000f0f00000f0f0000000000000f0f0000000000000000000000000000000000000000505000005050000050500000500f0f00000f0f00000f0f00000f0f00000f0f00000f0000000f0f00000f000000000000000000f0f00000f0c000000000000000000000f0f00000f0cf0c00000f0c00000f0c00000f0c00000f0c00000f0c00000f0c00000f0cf0f00000c0c00000f0000000c0000000f0f00000c0c00000f0000000c00f0f00000e0e00000f0a00000e0a00000f0f00000e0e00000f0a00000e0a
|0,3=>0xf0000000f0f00000f0000000f0f00000f0000000f0f00000f0000000f00f0f00000f0f00000f0f00000c0c00000f0f00000f0f00000f0f00000c0c00000000f0f0000000000000f000000000000000f0f0000000000000f0000f0000000f0000000c0000000c0000000f0000000f0000000c0000000c000000000000000000000000f0f00000000000000000000000000000f00d0d00000d0d00000d0d00000d0c00000d0d00000d0d00000d0d00000d0c50500000505000005050000050400000505000005050000050500000504303000003030000030300000300000003030000030300000303000003005050000050500000505000005050000050500000505000005050000050000000000000000000000000000000000f0f00000f0f00000f0f00000f00f0c00000f0c00000f0c0000000000000f0c00000f0c00000f0c00000000f0f00000f0f00000f0f00000f0f00000f0c00000f0c00000f0c00000000f0f0000000000000f0f00000f0c00000f0f0000000000000f0f00000f0c0000000000000000000000000000000000000000f0f0000000000000f00f0f00000f0f00000f0000000f0000000f0f0000000000000f000000000010100000101000001010000010100000101000001010000010100000100
|0,4=>0xf0f00000f0f00000f0f00000f0f0000000000000f0f0000000000000f00f0f0000000000000f0f0000000000000f0f00000f0f00000f0f00000f000000000000f000000000000000c000000000000000f000000000000000cf0e00000f0e00000f0e00000a0a00000f0e00000f0e00000f0e00000a0a0000000030300000000000003000000000000000303000000000000030000f0000000f0000000f0000000f0000000f0000000f00000000000000000000000000000000f0c00000f0c000000000000000000000f0c00000f0cf0000000f0000000f0000000f0000000f0f00000f0f00000f0f00000f005000000050000000500000005000000050500000505000005050000050000000000000000000000000000000000f0f00000f0f00000f0f0000000030300000303000003000000030000000303000003030000030000000300f0f0000030300000f0f0000030000000f0f0000030300000f0f0000030050500000101000005050000010000000505000001010000050500000100000000000000000000000000f0c00000000000000000000000000000f0c00f0000000f0000000f000000000000000f0000000f0000000f0000000000000000f0f0000000000000f0f0000000000000f0f0000000000000000
|0,5=>0xc0c00000f0f00000c0c00000f0c00000c0c00000f0f00000c0c00000f0cf0f0000000f00000f0f0000000c00000f0f0000000f00000f0f0000000c0000000000000000f0f00000f0f000000000000000000000f0000000f0000000000000000000000000000000000f0f00000f0000000f0f00000f00f0f00000f0f000000000000000000000f0f00000f0f00000f0f00000f0000f0000000c0000000f0000000c0000000f0000000c0000000f0000000c0000000000000000000000000000000000f0000000f0000000f0000000000000000f0f0000000000000c0c0000000000000f0f0000000000000c0c000000000000000000f0000000f00000000000000000000000f000000000000000000000000f0f00000f00000000000000000000000f0f00000f00f0f00000f0f00000f0f00000f0f000000000000000000000f0f00000f0030300000300000003030000030000000303000003000000030300000300
|_,_=>0
def sP:Nat→Nat
|0=>0x340c4902a10d910a7c30448253101438e072c14a86481c28a4a1920920287110a3c086348c3902a10187447c304068050608444853e1821e381c2950c682953a1821c0e14a920c6c38a1c3431a0e54c86080c48a1c343170a2870c0c0c4962a10a051438611203c08a1c346060608080
|1=>0x381c28a02181a610294060e8829f0c101881438606122188a029828a1c3031b0e88f86081c2ad14a03140a2808c081c80a1e043855cc03040ebc28e5c1931016280870ab4506061c2ab0c10c0514386060e4050e1a183852a4948448503901438e070a2940634251102a104870a28727
|2=>0x14e43040e5829f0c10a0714046843c1c29f0c10d940e1450e0e1491f0c10194121450e369840a501838220042070add70608504870a287032254c86080ca072028736281c28a026c38556182170e2870d0c45a0502199890a5430448257851438b870a2870606604901438d092c14a84
|3=>0xe4028a3e1821a0e140b80c1039010280c00e882953a18224122028a1c183bf0a28706069978a02003110e880990c104a65e4028a021c40a02f401112140bc081c28a1cec3230e140b808d838514b031b2214928081c2ba3e18203228940608503900a287116a400840e1562b0c10385
|4=>0xa280847c243a220042070a485390c101980a287000c0c4af140400406605011a18203281c28a1c19f074404c86089828a1d0433e0e405013210d830e2050e0c243af0a28700361c28a721823e0e402952410c070a2870d0c2530514a0304481c80a0200d894c205010c503851404004
|5=>0x2a18224129828a0200db60e205010c6df070a543042214ac10c103852a49506080df090a54304662428a02182034c2808d0c10a072014501086d30514a0304482428a02011be0e14501089838514386860e082810c11b094c145010c7838514e4304361c40a50182070a2870d0c68496
|6=>0xc103900a287406c1c40514043075e145280c11f0744409010879f070a54304661c2950c10385151c30436d9305140431b121c40a1c18d832214a86080c4af2028084071880a0211b070a29406084428a02743040e5828a72182030e140ae0c122070a2a18608243af201450e3c44385
|7=>0x210b980e1450e0cd83901028086360c3852a4820798145060846205140430406f849014042110a480c10845a8502182240a2808c0c11b070a29286086d31010280867c1cb052a1820720205280c10c260e4040a0224385143a5180e4040a020c88a0264304369978514043072014539
|8=>0x21819820280840e140ae00182260e1450e6418c07201450e06f881214042030e1452c0c1038516280802e9838514383072014a9d0c10d875e1450e0c6c38502b83042e1c28a1c181910a29406087038514043030e14acd0c10b940e14501086c19144043040e582953a1821b0644292
|9=>0xa21c28a1c1838514e4304121c8081438f030e14a86082480a03402030e280990c101895e28084361c28a58182260e145019e184900a2808c081c80a26042094c4040a021c28a507c3049c9828a021820322140b80c10385147c3043644485240421a0e40a86081da90140421c341c28a
|10=>0xc10f070a28086086c885240421e0e140b80c10d870a29286087838514a0304222511002103900a287530c6c3881438303124050e0878d870a543040e14a9d0c10f230e1450108708870a28086466c385140421e121c2950c10b870a05706081c28a6e00304369840a0218485144c084
|11=>0x309828a02182090e4040a02103851406080081c295a8182070a485018210da40e145010c103b50a28086080cc051404304480c4851404304361c8051438304301c28a1c0033e0e5828a02182037c1490a02182070a485013a182090ebc28a021130720205010c1c28a58a03040e1452c
|12=>0x20280d00c101875e28086081c29203583040e1450196182094c2028a0218b8710145010c101870a280cd0c104a62014501081cb051404e8608f84870a543040e2028a03543040e4028a0230304360c3a21404304221cb052404304360c3852428084a21c28a021821b222428a0218203
|13=>0xc10385140610608243880a28706121c80514382580e405010c104851406806082428a035830436243851404004061c28a02e0304069880a021823e0e14a920c108872c402810c11307201450e0c683852404304061cb221404304ae1c28a021821b061c28a50182170ebc28a0218207
|14=>0xc101a610280860e16d8a021821b0e1450e0c104872c4028a02112030e1450e0c443900a48084361c28a02e03043c1d1051404304b41c28a021821e061c28a02182360e145010c10d070a54304121d7880a28084061ec8a021821b4c145010c10a070a28086086c38814043040e14ad6
|15=>0x341c28a02182030e205010c1038514380060e145010d282070a280d00c1088720145010c103851406b06081c28a5018203124050108783851404304361c28a5018203228808609483852a28304061c28a50182030e2050e0c78d870a2808608443851406586086038514383520e1450e
|16=>0x1c182030e145010c103880a2808608983851404304361c28a02182090e4028a021039620145010c112260e145010c108870a4808608688870a28086081cb220a28086081d7851404304360c3851404304221d10502182070a280c10c1048744145010c101870a28706080d3051404304
|17=>0x70a28086081c28a
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0xd5009400450004
|5,0=>0x182617c61766170616a6164615e61586152614d51476141613b6135612f61296123611e51186112610c6106610060fa60f460ee60e860e350dd60d760d160cb60c650c060ba60b550b050aa60a4609e60986092608c60866080607a6074606e60686062605d50585052604c60475041603b6035602f60296023601d601760125
|5,1=>0x1ab61a5619f61996193618d61885
|6,0=>0x35c7356635063497342733b7334732e6327732073197312730b730472fd72f672ef72e872e262db72d472cd72c672bf72b872b262ab72a4729e6297729072897283627c7275726e7267726072597252724b7245623e7237723072297222721b7214720e6207720071f971f271ec61e571de71d861d171ca71c371bd61b761b16
|6,1=>0x506650064fa64f464ee64e774e164da74d464cd74c674bf74b964b364ac74a5749e74986491748b6485647e74786471746a7464645d7456745064497442743b7434742e64277421641a7413740c740573fe73f773f073e973e363dc73d573cf63c963c273bb73b473ad73a6739f73996393638c7385737e73786371736a73637
|6,2=>0x584757e65777571656a7563755c7556654f75496543653c7536652f75287521751a7513750c7
|7,0=>0x75b7754774c8744873d7735872e7728672087197712770b770476fe66f776f076e976e276db76d476cc86c486bd76b676ae86a776a07698869176898681867a7673766c7665765e7656864e8647763f8638763086288620861886108609760185f985f275eb75e565de75d685cf75c875c085b885b175a985a185998592758b7
|7,1=>0x7c967c367bc77b577af67a877a1779b6793878b8785677e77786771776a77628
|8,0=>0x861785a7852884a8843783b8833882c7824881d7816780e8807780077f977f277ec67e577de77d687cf7
|9,0=>0x87d6876786f78687
|10,0=>0x8836
|_,_=>0
def wAt:=mkWire dB 92 236 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x81d0c1d0a1114b25011360706190ca9240e0a1d481b0e190e8902290a29062902290c150e19201d0a190a9902110c150e11061102110e190a190a1d2611240c141d0a1d0c29341b42050e1520440c150e2902293c13362906190a1d0a62202902290e150c150c1d0a192611240c141d0a1d0c290a1d0c11162912200e190a11
|1=>0x36070e2906190e150e2944240a190c1d0a2970297007362b06190a1d481b3607201d0a190a19162912200e190a11481b0e296a1112880c1d0a290c210805101d0a114cc9209b0a190e11121102110e150c150c1d0c890e8902290a290a110e11360706190a114c400e110c150c1d06190a1d26110c1506480e150c290a191024
|2=>0x12150e1906110c150a1d0c110a1112150e192e1b3015001d0c113657201d02290a19362b0c0d06290a1d001f0a110c150c112c1f140544190a290e190e2102110a110b010e0202110c1100150a1d0c110afa22190e2920110c150e110a11201f0c150c11141d0c1d24170c2910270a1102110e1936070e410a19360706190a1d
|3=>0x6190a1d360712150c1d021130174c190e110e890c1d44190a290a2912290c1d3c077c15241d0e150805001d0c1100150e150c110a624c190e11481b061102110a1d7c1712290e19021112170e190e117c1712290c1d080506190a1d0a1100150c1102110c1d362906190a1d0a190e4902290c2930170e0102110c1136070e11
|4=>0x8a1d202b0a190c1d201102110c157c150c450e290c1d0c114c150e11361306190a1d1215140512290e190e29140512170e190a1d140512290c1d0f09128a0c1d0a2930174c190e112e1b0ebd20110a193607201d0a190e1906110e150c11341b221522190e2930170c9902110e11162912200e190a11361312150e193c073629
|5=>0xc117c1722190e292011201d0c150e113c070e592029001f0c1102110c152e134819101d0a11241d0a190c290a297c150e4902290c291405921d441b0a2990078c1512130c1d3613201d0a190a250a1102110e1914050e2906190e150a1d0e1920110a190e1512130c150c1d361306190a1d3c1f341922150e292e2b0c910611
|6=>0x24150c290c0d0a1d0c2902113015001d0c113613201d0a19140506190e150c296a0512880e190a290f2d22420a190e2912290e150c150c1d0e290c2912170c1d4424141d0c1d0a292e1f48194c150e11361306190a1d081d201d0a190a490e4902290c293607201d0a190a110c154c190e1108050c1d00170c11001d0c150a11
|7=>0x12880e190a294c190e150a190e112e2b3015001d021112110c150c1d0e15241d0c2950113607061910240a110c1d0c1148194c150e112c1f140520290a19201d201102110a192e2b361106190a1d4c410e1102110a190e29360706190a1d3c13362906190a1d1405064a0c292819481b4c150e1114150e2906190e1514052c1f
|8=>0x6190a1d02110a190c1d0a113419062902290a1d0e190a19062b0a1d3c170c6906290a1d20110e150c150c1d5011360706190a1d08c94c420a190e110ebe20110a19240c0c150a1d0c290a110e190c150e11360706190a1d0ec9209b0a190e11362b06190a1d3657061902290a1d0e290c2912150e190a19062902290a1d0a19
|9=>0x360706190a1d360706190a1d0e1914150c150e29209a08050e11021106190a1d0a1102110e150c150c1d362906190a1d2c1f202902290a193c1b362912150c1d3c13341922150c0d0c6a06290a1d128914050e190a292e2b361106190a1d2e073015001d0e11201d0a190a11240c0c290e150e1908050949061b0e153c073629
|10=>0xe110c1d0a190a1112170c1d0c110e4a02290c290c2912170c1d0c0d06110a1d12880e190a2912110e150e190c1d06110a1d201d02110a190e0102110c11241d24150c290e15241d0c292c1f24150c2900150c1d0c110e110a190a11360706190a1d360706190a1d0735064a0e150c290e4114190a190e293629362b06190a1d
|11=>0xc290a1d44190a29b01906130a1d360706190a1d5e1d00150c110a19062b0a1d00150a1d0c11141922170e2920470a190e29081d0c1d0a114819101d0a11064a0c290e110c150c1d2c1f24150c29140512290e1912230e190ebe20110a1906190a1d0a290e2924150c2906190e150c29a411061b0a1d0e2912150e190e154c19
|12=>0x6290a1d361306190a1d062902290a1d0c1d10190a11101b0a1d0a11081d201d0a19481b4c150e1106190a1d0a110a4602290e29128a0e190a2908050e190a110c1502110c1d06130a190a1d062b0e150e190e1922170e290c1112150e19362b06190a1d0e150a190e111405241d0c290e2920290a190e1102110a1906290e15
|13=>0xe29360706190a1d0e150c150c1d362906190a1d360706190a1d0e150a290e291405061b0a1d360706190a1d0a1102110a1d362906190a1d22420a190e0102110c11061b02110a1d0e110a1d0a1114f5201f0c15061902110a1d0e1920290c15061102110a1d14190a190e29362b06190a1d3419441d0a29781d24170c290c69
|14=>0x2110a1d0a110e1106190a1d0c150c1d20290a194c150e110c290e2922150e2944190a2910190a1106190a1d0a290e2912170c1d0e190a2902110a1d0e110a1d22150e290a1d0a1102110c1100170c11062b0a1d0a190e292217
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x660000006
|5,0=>0x1c9400000007111b8c695000000000006810000000000063500005f416d056514900001390000000049500004720000000109400000003d5000039400000000d8c351000031400002d40ac8274000000008941d5070400005d400004940000000000000011100000c5
|5,1=>0x833200c7c40000775
|6,0=>0x595161457515a3559152453914a451cd43400014034f4d3944d8d3244bcd2b449d000048d11f4470d184454d114435109441510233f90fb33dd0f343c0ced33a50e6338ccdf4370cd84354cd143350ca33190c242f90ba42dccb342bd0ab429d0a3427d09b4260c953248c8e42290864
|6,1=>0x929246490923e48e923648c922e48a9226488921f386d2174850e104834e09481520147f500007e51f630001f247bcdec37a11e537851dd47651d547451cd4728dc647091be46ecdb746d0db046b11a846911a046711984654d92363918a461cd8345fd17c35e117535c516d40001694
|6,2=>0x28f3a30e884a1128049f4e7a39d927339bd26b49a0e64498125d3965255494524e3
|7,0=>0xd34f4a3d1cf443d04f3e3cecf383cd4f323cbcf2c3ca4f263c8cf203c74f1a3c5cf143c44f0e3c2cf083c14f023bfcefc3be4ef63bccef03bb4eea3b9cee43b84edf2b70ed93b58ed42b44ece3b2cec83b14ec23afcebc3ae4eb63acceb03ab4eaa3a9cea43a84e9e3a6ce983a54e923
|7,1=>0xdf0f793dd8f733dc0f6d3da8f673d90f622d7cf5c3d64f563d4cf503
|8,0=>0x3a72e94ba32e84b9f2e74b9b2e64b972e54b932e44b8f2e34b8b2e24b872e14b832e04b7f2
|9,0=>0xeb07ab1ea87a91
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 14
def pmP:Nat→Nat
|0=>0x70c001c080050200102900402000c21002200008000012000042100102000401000f8000380000800001800004000008d00022c00081000200000300000a40002100008000010000024000080000140000300000400000
|1=>0x400000f4a90392a40dc800370200cca90330200b4a902d0200aca902702008829021ba0084e90212a00848002104008408021014080a00200c4080210200200800102000005c88011ea4046e80110a40300800b2e002c08
|2=>0x772a41c4a906d2e41b4a906b2a41a4b90692a4194b90652a418ca9061ba4186a90617a4185a90613a4184a90612a0147a904b2e410cb80412e0104a804122c1044804102010403040e20100890402001004004008010001
|3=>0x110c844409810c220410081032e040ca9101ba040429100420400291000203c6a90e17a4384e90e12a4346a90d1884346080c1820285e9091a202460809100020608081800205e8081420204e8081000201080800201e4a9
|4=>0x240e20900002312a48b0a922b2a4894a92250a484448210300807a1201e20803a91c16a4704a91c0620701291814a45c4e91712a45b4b91632a4584a9151aa4545a9141ea4506a91302244b4081232a44802112000046821
|5=>0x3713a4dc4a9371224d44a9351284d4448351024d40a1340000cc481331024cc089330220cc029330004c84a9320000c4089300240b04a126b2a4987a9261aa4985a92613a4984b92612a4945a9251380944a9250000906a9
|6=>0xe61fa6084e8661ba5284e8
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x30002
|5,0=>0x2707290034000000000800000f3f46000000110000000d00170865170015000023000600002d0000780004000006110019002006100000130e18002c0040000000000f001f
|6,0=>0xb8b0322a241c99056f4014639d7f2714814fb5213a00900b00667c0492083548013229280401b41eaf099e7e3128847a360101a1154362648f75470464050084094c4ab798ad6ebb01280004016a0895a12f7b007d1475053f940161499e083fc2307c276269774522797c97680137624396b70c2901ac1d12c0671b69259c33
|6,1=>0x414108b208420a8004a3512b4b0127011a280b
|7,0=>0x50be50bdaba6bdc12a276ca7aa5ebf3bc33eb182571c504d6ba0bc50bc5a56558ea29a3db985a45d3b539b3ca5ae169a70385e877604883b8c046db626b3a5b491898658834456939fba732e8439704e
|8,0=>0xbe8d5faa5cab5f74bd5b8a8ba7a8aba97271a56059
|9,0=>0x51a55452
|10,0=>0x50
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 22 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_234 9 roots_234 ops++addP pm 1 dom_97 4 roots_97 ops++addP pm 2 dom_41 4 roots_41 ops++addP pm 3 dom_227 8 roots_227 ops++addP pm 4 dom_232 7 roots_232 ops++addP pm 5 dom_105 7 roots_105 ops++addP pm 6 dom_106 7 roots_106 ops++addP pm 7 dom_171 8 roots_171 ops++addP pm 8 dom_75 5 roots_75 ops++addP pm 9 dom_99 5 roots_99 ops++addP pm 10 dom_203 8 roots_203 ops++addP pm 11 dom_225 5 roots_225 ops++addP pm 12 dom_169 5 roots_169 ops++addP pm 13 dom_201 5 roots_201 ops++addP pm 14 dom_163 5 roots_163 ops++addP pm 15 dom_233 8 roots_233 ops++addP pm 16 dom_107 8 roots_107 ops++addP pm 17 dom_43 5 roots_43 ops++addP pm 18 dom_139 5 roots_139 ops++addP pm 19 dom_195 5 roots_195 ops++addP pm 20 dom_202 7 roots_202 ops++addP pm 21 dom_226 7 roots_226 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_235 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_97 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_225 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_169 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_201 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_195 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_226 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_234 9 s (0,roots_234.map (·&&&dom_234)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_235 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_234 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)],[(0xcccccccccccccccccccccccccccccccc,126)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xcccccccccccccccccccccccccccccccc,126)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_235==dom_235)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_235 gM v ys):RunD true dom_235 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_235 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 71 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 71 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 147 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 19 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 147 → Z 6 i = true := (range_split z6_0 z6_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 80 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 80 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 21 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 21 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 4 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 4 0 = true)
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
namespace S_237
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(4,36),(4,68),(4,132),(5,13),(5,37),(5,69),(5,133),(8,9),(8,40),(8,72),(8,136),(12,13),(12,44),(12,76),(12,140),(32,33),(32,36),(32,40),(32,96),(32,160),(64,65),(64,68),(64,72),(64,96),(64,192),(128,132),(128,136),(128,160),(128,192),(129,133),(129,137),(129,161),(129,193)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffff
def xsM:=roots_237.map (·&&&dom_237)
def gM:=goal_237&&&dom_237
def NN:Nat→Nat
|8=>1
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|8,0=>0x743d3
|9,0=>0xf0cad
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x333300003333000033330000000000003333000033330000333300000000cccc000000000000cccc000000000000cccc000000000000cccc0000000330000003300000033000000330000003300000033000000330000003300c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c222200002222000022220000222200002222000022220000222200002222cccc0000cccc00000000000000000000cccc0000cccc000000000000000333300003333000033330000333300000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x58d11ac688
|_=>0
def sO:Nat→Nat→Nat
|8,0=>7
|9,0=>0x76
|_,_=>0
def wAt:=mkWire dB 7 238 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 8
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xa5
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
addP pm 0 dom_236 8 roots_236 ops++addP pm 1 dom_109 8 roots_109 ops++addP pm 2 dom_233 8 roots_233 ops++addP pm 3 dom_229 8 roots_229 ops++addP pm 4 dom_205 7 roots_205 ops++addP pm 5 dom_173 7 roots_173 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_237 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_229 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_173 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_236 8 s (0,roots_236.map (·&&&dom_236)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_237 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_236 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32)],[(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_237==dom_237)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_237 gM v ys):RunD true dom_237 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_237 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_237 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_237 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_237 roots_237 goal_237 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_237
theorem lowS_237:Lower true dom_237 roots_237 goal_237 10:=S_237.noCircuit
theorem lowS_245:Lower true dom_245 roots_245 goal_245 9:=lower_slice_b [(0x22002200220022002200220022002200220022002200220022002200220022,16,17)] (by decide +kernel) lowS_244
def dzo_102_16:=0x550000005500000055000000550000
def gzo_102_16:=0x550000005400000054000000500000
def gsh_102_16:=0x55000000540000005400000050
theorem lowS_zo_102_16_98:Lower true dzo_102_16 roots_102 gzo_102_16 5:=lower_iso_b (d1:=dom_102) (r1:=roots_102) (T1:=gsh_102_16) [(dom_102,16)] (by decide +kernel) (lower_slice_b (T:=gsh_102_16) [(0x50000000500000005000000050,0,4)] (by decide +kernel) lowS_98)
def dzo_230_16:=0x55000000550000005500000055000000550000005500000055000000550000
def gzo_230_16:=0x55000000550000005500000055000000550000005400000054000000500000
def gsh_230_16:=0x5500000055000000550000005500000055000000540000005400000050
theorem lowS_zo_230_16_98:Lower true dzo_230_16 roots_230 gzo_230_16 6:=lower_iso_b (d1:=dom_230) (r1:=roots_230) (T1:=gsh_230_16) [(dom_230,16)] (by decide +kernel) (lower_slice_b (T:=gsh_230_16) [(0x5000000050000000500000005000000050000000500000005000000050,0,4),(0x5500000055000000550000005500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_98)
namespace S_246
def pG:List (Nat×Nat):=[(2,34),(2,66),(2,130),(4,20),(4,36),(4,68),(4,132),(6,22),(6,38),(6,70),(6,134),(16,20),(16,144),(18,22),(18,50),(18,82),(18,146),(32,34),(32,36),(32,96),(32,160),(48,50),(48,52),(48,112),(48,176),(64,66),(64,68),(64,96),(64,192),(80,82),(80,84),(80,112),(80,208),(128,130),(128,132),(128,144),(128,160),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffff
def xsM:=roots_246.map (·&&&dom_246)
def gM:=goal_246&&&dom_246
def NN:Nat→Nat
|5=>2
|6=>8
|7=>9
|8=>3
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0xeacb780cd7
|6,0=>0xfef4eadd3e909d57f06119a70175c513a820ece0
|7,0=>0xdcaf7b9489ad9b6728736a68b478e72f73f23c94024f2
|8,0=>0x93f797c5102722a
|9,0=>0x3f43d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaa00aa0000000000aa00aa0000000000aa00aa000000000000000000000000000000015401540154000000000000000000000154015401540002a802a802a8000002a802a802a8000002a802a802a8000002a802a802a800055005500550055005500550055005500550055005500550055005500000000aa00aa00aa00aa00aa00aa0000000000aa00aa00aa00aa00aa00aa0000000154000001540000015400000154000001540000015400000154000001540002a802a802a802a8000000000000000002a802a802a802a800000000000000055005500550055005500550055000000550055005500550055005500550000aa00aa00aa00aa00aa00aa00aa00aa00aa00aa0000000000aa00aa0000000110011001100110011001100110011001100110011001100110011001100112a802a80000000002a802a80000000002a802a80000000002a802a8000000055005500550055005500000055000000550055005500550055000000550000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a044004400440044004400440044004400440044004400440044004400000002a802a802a802a802a802a802a802a802a802a802a802a800000000000000055005500550055005500550055005500000000000000000000000000000000
|0,1=>0x550055000000000055000000000000005500550000000000550000
|_,_=>0
def sP:Nat→Nat
|0=>0x28cc902caa19820414664818550cc901caa1982928cd0480aa1992f014833040729066481872a8664818550c4902cea1982550c49034e33052828cc1015431052071c66481ac38cc9020e3304a418820
|1=>0x550cc901caa19920595433240d
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x65006
|6,0=>0x3773162b62561f61871260b7
|7,0=>0x7476e66776075a65374d64673e8
|8,0=>0x8878177b6
|9,0=>0x8f6
|_,_=>0
def wAt:=mkWire dB 17 247 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x2812a55154812a56a55155812a54812812175250974814815252815253a52815812a52a548128161b5812a55152814815a94812a561b0952816a751549d2815155a92a5481281
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x1000
|6,0=>0x6095348cf330ca21cc43
|7,0=>0x2a2a0a6290a22809e2709a2
|8,0=>0x2e1b46c1
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 10
def pmP:Nat→Nat
|0=>0x33cf961c73dbde3cf0e7737a39cdee6e727b93bc8de27f0f385041ce0e2020007c002000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x40
|6,0=>0x9c8f40d26
|7,0=>0x116566b849b4
|8,0=>0x38ea
|9,0=>5
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 13 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_244 8 roots_244 ops++addP pm 1 dom_242 8 roots_242 ops++addP pm 2 dom_118 7 roots_118 ops++addP pm 3 dom_198 5 roots_198 ops++addP pm 4 dom_166 5 roots_166 ops++addP pm 5 dom_214 7 roots_214 ops++addP pm 6 dom_182 7 roots_182 ops++addP pm 7 dom_230 8 roots_230 ops++addP pm 8 dom_150 5 roots_150 ops++addP pm 9 dzo_102_16 5 roots_102 ops++addP pm 10 dzo_230_16 6 roots_230 ops++addP pm 11 dom_86 4 roots_86 ops++addP pm 12 dom_54 4 roots_54 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_246 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_198 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_166 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_150 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_102_16_98 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_230_16_98 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_54 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_244 8 s (0,roots_244.map (·&&&dom_244)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_246 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_244 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_246==dom_246)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_246 gM v ys):RunD true dom_246 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_246 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 2 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 8 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 9 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 3 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_246 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_249:Lower true dom_249 roots_249 goal_249 9:=lower_slice_b [(0x202020202020202020202020202020202020202020202020202020202020202,8,9)] (by decide +kernel) lowS_248
def isoMvS_95:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_95:Lower true dom_95 roots_95 goal_95 9:=lower_iso_b isoMvS_95 (by decide +kernel) lowS_63
def isoMvS_207:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_207:Lower true dom_207 roots_207 goal_207 9:=lower_iso_b isoMvS_207 (by decide +kernel) lowS_175
def isoMvS_215:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_215:Lower true dom_215 roots_215 goal_215 8:=lower_iso_b isoMvS_215 (by decide +kernel) lowS_183
def isoMvS_221:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_221:Lower true dom_221 roots_221 goal_221 9:=lower_iso_b isoMvS_221 (by decide +kernel) lowS_189
def isoMvS_222:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_222:Lower true dom_222 roots_222 goal_222 10:=lower_iso_b isoMvS_222 (by decide +kernel) lowS_190
def isoMvS_238:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_238:Lower true dom_238 roots_238 goal_238 11:=lower_iso_b isoMvS_238 (by decide +kernel) lowS_235
def isoMvS_252:List (Nat×Nat):=[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_252:Lower true dom_252 roots_252 goal_252 10:=lower_iso_b isoMvS_252 (by decide +kernel) lowS_246
theorem lowS_127:Lower true dom_127 roots_127 goal_127 11:=lower_slice_b [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,8,9)] (by decide +kernel) lowS_126
theorem lowS_191:Lower true dom_191 roots_191 goal_191 11:=lower_slice_b [(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,8,9)] (by decide +kernel) lowS_190
theorem lowS_239:Lower true dom_239 roots_239 goal_239 12:=lower_slice_b [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,8,9)] (by decide +kernel) lowS_238
theorem lowS_247:Lower true dom_247 roots_247 goal_247 11:=lower_slice_b [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,16,17)] (by decide +kernel) lowS_246
theorem lowS_251:Lower true dom_251 roots_251 goal_251 12:=lower_slice_b [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000,1,17)] (by decide +kernel) lowS_235
def dzo_108_16:=0x11110000111100001111000011110000
def gzo_108_16:=0x11110000111000001110000010100000
def gsh_108_16:=0x1111000011100000111000001010
theorem lowS_zo_108_16_104:Lower true dzo_108_16 roots_108 gzo_108_16 5:=lower_iso_b (d1:=dom_108) (r1:=roots_108) (T1:=gsh_108_16) [(dom_108,16)] (by decide +kernel) (lower_slice_b (T:=gsh_108_16) [(0x1010000010100000101000001010,0,4)] (by decide +kernel) lowS_104)
def dzo_109_16:=0x33330000333300003333000033330000
def gzo_109_16:=0x33330000333200003332000032320000
def gsh_109_16:=0x3333000033320000333200003232
theorem lowS_zo_109_16_104:Lower true dzo_109_16 roots_109 gzo_109_16 6:=lower_iso_b (d1:=dom_109) (r1:=roots_109) (T1:=gsh_109_16) [(dom_109,16)] (by decide +kernel) (lower_slice_b (T:=gsh_109_16) [(0x2222000022220000222200002222,0,1),(0x3030000030300000303000003030,0,4)] (by decide +kernel) lowS_104)
def dzo_233_16:=0x303000003030000030300000303000003030000030300000303000003030000
def gzo_233_16:=0x303000003030000030300000303000003030000030200000302000002020000
def gsh_233_16:=0x30300000303000003030000030300000303000003020000030200000202
theorem lowS_zo_233_16_104:Lower true dzo_233_16 roots_233 gzo_233_16 6:=lower_iso_b (d1:=dom_233) (r1:=roots_233) (T1:=gsh_233_16) [(dom_233,16)] (by decide +kernel) (lower_slice_b (T:=gsh_233_16) [(0x20200000202000002020000020200000202000002020000020200000202,0,1),(0x30300000303000003030000030300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_104)
def dzo_236_16:=0x1111000011110000111100001111000011110000111100001111000011110000
def gzo_236_16:=0x1111000011110000111100001111000011110000111000001110000010100000
def gsh_236_16:=0x111100001111000011110000111100001111000011100000111000001010
theorem lowS_zo_236_16_104:Lower true dzo_236_16 roots_236 gzo_236_16 6:=lower_iso_b (d1:=dom_236) (r1:=roots_236) (T1:=gsh_236_16) [(dom_236,16)] (by decide +kernel) (lower_slice_b (T:=gsh_236_16) [(0x101000001010000010100000101000001010000010100000101000001010,0,4),(0x111100001111000011110000111100000000000000000000000000000000,0,128)] (by decide +kernel) lowS_104)
def dzo_237_16:=0x3333000033330000333300003333000033330000333300003333000033330000
def gzo_237_16:=0x3333000033330000333300003333000033330000333200003332000032320000
def gsh_237_16:=0x333300003333000033330000333300003333000033320000333200003232
theorem lowS_zo_237_16_104:Lower true dzo_237_16 roots_237 gzo_237_16 7:=lower_iso_b (d1:=dom_237) (r1:=roots_237) (T1:=gsh_237_16) [(dom_237,16)] (by decide +kernel) (lower_slice_b (T:=gsh_237_16) [(0x222200002222000022220000222200002222000022220000222200002222,0,1),(0x303000003030000030300000303000003030000030300000303000003030,0,4),(0x333300003333000033330000333300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_104)
namespace S_253
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(4,20),(4,36),(4,68),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(8,9),(8,40),(8,72),(8,136),(12,13),(12,28),(12,44),(12,76),(12,140),(16,17),(16,20),(16,144),(24,25),(24,28),(24,56),(24,88),(24,152),(32,33),(32,36),(32,40),(32,96),(32,160),(48,49),(48,52),(48,56),(48,112),(48,176),(64,65),(64,68),(64,72),(64,96),(64,192),(80,81),(80,84),(80,88),(80,112),(80,208),(128,132),(128,136),(128,144),(128,160),(128,192),(129,133),(129,137),(129,145),(129,161),(129,193)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffffffff
def xsM:=roots_253.map (·&&&dom_253)
def gM:=goal_253&&&dom_253
def NN:Nat→Nat
|5=>21
|6=>143
|7=>268
|8=>197
|9=>63
|10=>8
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0xc8951bf17eafdfea055f989b7907507b6bc6f5226af6c615a15c2e157f2e41ef33872336241341e6314782ce5f1d5fc1518b0db4b
|6,0=>0xb2b99adcf7ab8c0a928ca91a2a7d6ea7958a1b919fbd09a06f9927699062978bf969609604c9139c9082f9032d8db2d887938489183e677fd1f7f6857dd527d5957cef97911c788c577e7b745126e5646de2b6dd076db3e683dd682c666f0d6684a6675364f626433c627446127a602a65ff575e0be5acd65acc959a685870956d3b548f453ccd53a1c537b1515214dc0b4a8c64a3244a29c49d604920c48deb47050460d7458564396242ebf41f2b405ca4003f3ec393e8d53c3223bdd33b4be3a0b139ded38926383353828f343e1331c13126d2f7002f6972d80b2cec92ad3c24edb248512430d1e23c1de0a1d89b1d68d1bb461987818be517d7d16eb91667d161e51604d1473a121cf1062c0f37f0f2200dc060c38d0c3200c3110bb510a86709e53085b9080d707be005e3205a4705a0503bbd028130214d00a9700326
|6,1=>0xf2193e4f35e2c36dc72bd6529d2e44d03dfcdc2ecb82ccb024c55a0c17b2be742bdaa5ba38d
|7,0=>0x4633b45c49447434187b4174a40b99405ca402e93faff3f0bd3ccc83be6f3ba593b3f83ac863a3ee39b0238edd381c53812a373e437161366de35f5c357b0349af34668343ff33cd13349d32efb327fb326a531fd33198e313b63136530d1e3095e3050c30478303512ecab2d5be2cffd2cc662cc102cbd42c8c52c7bc2bb522b9632b10f2a14d28971288f528135280d626e4b2635a259d32548923c072370d22e842264c216751fe151f58a1f0811efbb1ec8d1eac51e8c71e86c1de3a1de341dbcf1da131cfe51cb401bb581b4891acff1ab181899a17a561726515978154c514f6a14cb7148f21403d13a9913a8712cc112a0911696111881038b0f9590f8630f80a0e8a30da510d2dd0cb270bafd0b7a10b6120b0900a25e0a2260965408e8f087e20803607767069020575e0564004ee80383e0305802d220266501fee
|7,1=>0xd09c9ce041cdeb0c9645c8484c8057c0f14bee4ebe567bcf35bb1fcb83f9b7fe8b7260b6cf2b435bb31ebb11bfafd71aefcfae2d0ae12aac911ab142a9dc2a8d28a42a1a29769cfb99c3849bdfd99bd599aa6996fb988f095eec94b98935ca91efe9003d8ffd68d8bf8d0c28cb988c6268bd3f8b8628ad1486bf58606485acd8464483e5a83c8783b9082420815c9815467f43a7e1207d2387c88a797fb79345772ba772ad76ea176a0075f2f749e773bbb7232c71d28710a76fb5f6f6006d8496d6296c9f06ac746a79268a16688ae674da66eaa66de76689866344662b0651c9644fc6349062e686276461e3a5f3685d5ec5c9915c7f35c7b557eae57921570fe566e056695563d15596355382549195487353995509c5505525034e4fe2a4fabe4f7a54ece84e8664c7124aa0649def4884947bb44735d466fd46579463ba
|7,2=>0xff21afda96f7241ec189e9263e9124e112ee0e18dff90de691d87e5d3e5f
|8,0=>0x734b3733126ff796e6256e4ad6d6456cb366b9cf69b82690ab6904b66b296441f641986299e6222d614a05fd5d5f93c5f550592ac58c3557fa0548e4547a95254050eb0502b54fc384f4104eef94eddf4d9494c9354c0d4495e1494d948ea94329a42e6b42d8542d1c428174073b4067e3fcf13d9223b2713ae503a41e3a1b339f7d39920395e33912438ae53813c378633719a35b143456934100332a73156830ed6302ea2fa032f7982d3422bdee2b2fa29e2427d852767426a0d25c1f2547324a73244ff23d4b23196228f32232521a2a219222151c20cd6204871f9491f62e1f3061ef161bea81b0811a4d9199a2195e61936b183e91811e169ae168b6138cb138251303b1284b127041222111c71118cb11004103c00ec0f0e85d0d8180d6b50cebc0be3a0b8dd0b2310a1340a03008ae8082f5069d306099027af00ec2
|8,1=>0xf1862ed4d7eb8b2eb653eb207e5c29e463bda6e5d425ed1298ce188cd7a3cb262cab25ca70ec7726c6ffcc6af2c5a8fc530cc37a0c2321c0d67bfd37bf1e9bd05abbea2b4195b39ceb29c8ae4e2adeddad44eacb21a917ca703ca4da4a4c63a3c97a0c289e9d79ba1e9a3f899aff98c8797b3692fe491ca48e9108e6ee8d68b8bbe489e2d890f9875d8850988289482467811a5804b2802a67f1ab7e7797e50e7b6fa7b4a97a8ef7a58378f75
|9,0=>0xd25e6ca4c1c1388c1247bafbbb84dcb3297af85da3bbca2a0494a3f8f8df8f7948e7fd8562f8310d7ed62790a876db37570c74a3a6d4946578e642ba638886361d61f545cd1f5b0485971f526aa50ade506e44b8094a3414981f4154f3db003ca6b3c7483832a35f8634d4732cb6313692d5e829dfc2780e2585e226e42267d1f08c1c1b21abe016568152a613b71131de0c9080b09006fe906190059bd
|10,0=>0xc6eb1887d379b4e7762c6ec8e470633920c0b254
|11,0=>0x1e31b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcccccccccccccccccccc0000cccc0000cccccccccccccccccccc0000cccc0003333333333333333000000000000000033333333333333330000000000000000cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc03333333333333333333333333333333322222222222222222222222222222222cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0003333333300000000333333330000000033333333000000003333333300000000cccccccccccccccccccccccccccccccccccccccc00000000cccccccc00000003333333333333333333333333333333333223322332233223322332233223322888888888888888888888888888888888888888888888888888888888888888b333333333333333333333333333333300000000000000000000000000000000cccccccccccc0000cccccccccccc0000cccccccccccc0000cccccccccccc0003333333333333333333333333333333333333333222222223333333322222222cccccccccccccccccc00cc00cc00cc00cccccccccccccccccc00cc00cc00cc03333333333333333333333333333333333003300330033003300330033003300c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c3333333333333333333333333333333333333333333333332222222222222222
|0,1=>0xcccccccc00000000cccccccc00000000cccccccc000000008888888b33333333300330033333333330033003333333333003300333333333300330000cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc000000000000000333333333333333333333333333333333333333333333333333333330000000000000000cccccccc00000000cccccccc00000000cccccccc00000000cc00cc0000000000000000033333333333333330000000000000000333333333300330000000000cccccccc00000000cc00cc0000000000cccccccc00000000cc00cc0333333333333333333333333333300003333333333333333333333333333000000cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00880088033003300330033003300330033003300330033003300330022002200220022cccccccccccccccccccccccc00000000cccccccccccccccccccccccc00000000033003300330033003300330033003300330033002200220033003300220022cccc00cccccc00cccccc00cccccc0000cccc00cccccc00cccccc00cccccc0003333333333333333333333333300330033333333333333333333333333003300cccccccccccccccccccccccccccccccccccccccccccccccc0000000000000000000000000000000333333333300330000000000000000003333333333003300
|0,2=>0xcccccccccccccccc0000000000000000cccccccc8888888b3333333333333333333333333333333000000000000000033333333330033000000000000000000cccccccccccccccc0000000000000000cccccccc00000000000000000000000333333333333000000000000000000003333333333330000ccccccccccccccccccc0ccc0ccc0ccc0ccccccccccccccccccc0ccc0ccc0ccc333333333333333330303030303030303333333333333333303030303030303000cc00cc00cc00cc00cc00cc0000000000cc00cc00cc00cc00cc00cc000000033333333333333333333333333333333333333333333333333330000333300000000000000000000ccccccccccc0ccc00000000000000000ccccccccccc0ccc0000000033333333000000003330333000000000333333330000000033303330cccccccccccccccccccccccccccccccccccccccccc00cc00cccccccccc00cc033333333333333333333333333333333333333333322332233333333332233220000000000cc00cc0000000000cc00cc0000000000cc00cc000000000088008b333333333333333333333333333333333333333333333333333333322222222cc00cc00cc00cc00cccccccccccccccccc00cc00cc00cc00cccccccccc88cc8b333333333333333333333333333333333333333333333333300330033003300
|0,3=>0xccccccccc0c0c0c0ccccccccc0c0c0c0ccccccccc0c0c0c0ccccccccc0c0c0c3330333033303330333033303330333033303330333033303330333033303330000000000000000000cc00cc00cc00cc000000000000000000cc00cc00880088303030303030303030303030303030303030003030300030303000303030000cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc0000033003300330033003300330033000000330033003300330033003300330000cccccccccccccccc00cc00cc00cc00cccccccccccccccccc00cc00cc0088008b333333333333333333333333333333322222222333333332222222233223322cccccccccccccccccccccccccccccccc00cc00cc00cc00cc00cc00cc00cc000003300330033003300330033003300330033003300000000003300330000000000000000cccccccc00000000cccccccc00000000cccccccc00000000cc88cc88033003300330033003300330030003000330033003300330033003300300030cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00880088033333333333333333333333333333333333333333333333333223322332233220000000000000000cccccccccccccccc0000000000000000cccccccccc88cc8b333333333333333333333333333333333333333333333333333333333003300
|0,4=>0x4444444444444444444444444444440044444444444444444444444444444400000000000000000000000000000000011111111111111111100110011001100cccccccccccccccccccccccccccccccc4444444444444444440044004400440333333330000000033333333333333333333333300000000333333333300330000000000ccc0ccc000000000ccc0ccc000000000ccc0ccc000000000ccc0ccc33333333333333333333303033333030333333333333333333333030333330300000000000000000cccccccccccccccc0000000000000000cc00cc00cc00cc00303030303030303030303030303030303030303030303030303030303030000cc00cc00cccccccccc00cc00cccccccccc00cc00cccccccccc00cc00cc88cc88000000033333333000000003333000000000000333333330000000033330000cccccccccccccccccccccccccccccccc00cc00cc00cc00cc00cc00cc00000000000000000000000003300330033003300000000000000000033003300000000ccccccccccccccccccccccccccc0ccc0ccccccccccccccccccccccccccc0ccc3333333333303330333333333330333033333333333033303333333333303330cccccccccccccccccccccccccccccccccccc00cccccc00cccccc00cccccc0000033003300330033003300330033003300330033003300330033003300330000
|0,5=>0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00000003333333333333333333333333333333333333333333333333333333333223322cccccccccccccccccccccccccccccccc88cc88cc88cc88cc88cc88cc8888888b33300003333000033330000333300003333111133331111333311113333000000000000cccccccc00000000cccccccc00000000cc00cc0000000000cc00cc00000000033333333000000003333333300000000333333330000000000000000000000000000000000000000000000004444444444444444444444440000000333333333333333333333333333333331111111111111111111111110000000000cc00cc00c000c000cc00cc00c000c000cc00cc00c000c000cc00cc00c000c3030303033333333303030303330333030303030333333333030303033303330cc00cc00cc00cc00cccccccccccccccccc00cc00cc00cc00cccccccccc00cc03333333300330033333333330033003333333333003300333333333300000000cccccccccccccccccccccccccccccccc00000000cccccccc00000000cc00cc03333303333333033333330333333303033333033333330333333303333333030ccccccccccccccccccccccccc0c0c0c0ccccccccccccccccccccccccc0c0c0c3333333333333333333333333333330033333333333333333333333333333300
|0,6=>0xccc0ccc0000000000000000000000000ccc0ccc30303030303030303333333333303330303030303030303033333333333033300c0c0c0c0c000c000c0c0c0c0c000c000c0c0c0c0c000c000c0c0c0c0c000c03333030333330300333303033333030033330303333303003333030333330300cccccccc00000000ccccccccccc0ccc0cccccccc00000000ccccccccccc0ccc00000000000000000000000000000000111111111100110011111111110011000000000000000000ccc0ccc0ccc0ccc00000000000000000ccc0ccc0ccc0ccc0303030303030303030303030000000003030303030303030303030300000000cccc0c0ccccc0c0ccccc0c0ccccc0000cccc0c0ccccc0c0ccccc0c0ccccc0000000000033333333000000003030303000000000333333330000000030303030cc00cc00cccccccccc00cc00ccc0ccc0cc00cc00cccccccccc00cc00ccc0ccc3333333333333333003300330030003033333333333333330033003300300030cccccccccccccccc00cc00cc00cc00cccccccccccccccccc00cc00cc000000033333333333333333333333333333333333333333333000033333333333300000000000000cc00cc0000000000c000c00000000000cc00cc0000000000c000c0000000000000000000000003333333300000000000000000000000033003300
|0,7=>0xc0c0c0c0c0c0c0c0c000c000c000c000c0c0c0c0c0c0c0c0c000c000c000c0000000000000000000000000000000003333333333333333330033003300330000cc00cc00cc00cc00c000c000c000c000cc00cc00cc00cc00c000c000c000c3333333333333300333333333333330033333333333333003333333333333300ccccccccccccccccccccccccccccc0c0ccccccccccccccccccccccccccccc0c0000000000000000000000000000000033333333333333333333333300000000cccc0000cccc0000cccc0000cccc0000cccccccccccccccccccccccccccc0003033303330333033303330333030303030333033303330333033303330303030
|_,_=>0
def sP:Nat→Nat
|0=>0x1844f1c1e8008c122c403027cc040434080084c6811844f091e200800a08080186490416080802a2c08c2874c043834080301040d0244d0b1a0461b306848d02302880230c91302408c2e382840404b0e2a2c10100502131a04006241058802448041e200860a2440302002840608080
|1=>0x24245880230715142c101185880a503c681189c58d021d3060a3408c3245295160c101182458d0230d8e3c2458802007242a2c681001828910340801c4820b040460e122c681188c718083408c224048f0404392122c6810030f0416080801c6110a1a046110a1010d0200721142c681
|2=>0x100460e142c1010030cb1142c6811844f22160c08c0cc0d0a163408c3c10782023072c1220681183850f1a0461b227848f1a0400c3cbc58802383181420681001970a1e3408c3cb4588023070a16080802839604043408c1c7850f400461130355010e983151680681186c5131a04611
|3=>0x82c681001850f660400c0c602021a0460e0a106811838e95122c08c2e38f1c122c1811878e0b400460e143c080185c305382418d02302b0123408c1c68e0a163408c302900d023088a1e0808c283910a16201810c5448b643408c4a545a01a0461c142c403023048a1e20681007848f
|4=>0x1864310122c4011838a8916201811828581185071d3c88582023071e2a2d001182c087689870624105880238310143c101189450f1a0400c122c681003149a143c10d0230f1516080801894d0a1e3408c302440d0230710143c4011818f04160c08c2228581185c706122c18d0230f92
|5=>0x143c401184450f1a040140c285880200c862a2c68118508a4142c1811844f1c160c08c08545881a04895163408018d8c042a3408c22785a00230d8e3c1078802383051a046351c18e0a1e806811868a89163408c142c101185c72c08206811c185131a0400c0c7820f1a040060a34080
|6=>0x1894a89160c08c5e285881a0489e2a2c401001928b1a0461b1c1058d0201486762868118e87184a246810e44c091a0463a1c144b21a0460e30246810ee88a4143c6810018d0b1a0439b0c285820231c8e306848d021c3051a05c0c1c1821516806811810e151634080302868118dc71e
|7=>0x168008c1c7820b640470608545821a040054efc6aa0e1821516340960c2450b100c08030fc6aa0ee830534246810e442bf7c1da0e0c90a8b06046060a3408c3638284060808c1c285820231e8e302808c2e3830a26343bc1c18c041a040060a2418d02006053824182021cc1c1434080
|8=>0x1a04386849ca8b1a04386607050b1a0460e142c68170307060a2840302307063010a8d020031e383d0010e18541263408c1c1420806047063cbc582023071e082c1810018f091e800872261fab1aa8386342450f1a046092634087226850b060808c30286811900705123408c2c38f04
|9=>0x1e3408c0c1410d021cd8e0c9c50b1aa80870c2858d023228e142c403020032c123408c1c1050f1a040063c70582021c88e3c5458d02006060a2818202307042a2c681184428a0608087222858d023220e3c545ab5404386142df010ed0706482878d0230706445450b1a0461134285a0
|10=>0x1c18a8b1aa80874c18f15162008c1c185021a046461c285c71a0460e0c2810d021e3114e285be0604386342878d021c30a16206813e38309142d90d023071e442c6811838304163408c5238310082c68118383422a2c1810e1928a16806811838f0b040439b1c185081a046461c1880a
|11=>0x21d30e0c15fab1aa838e0c2458d023148e202458d0230725143c6810e44a89160c681182458d021d491142c681185c706242858d023089e2a2c101183938a16f86aa0e18f151608087225450b10340800c5448b1a0439d305450d0200606845458d541c31e143df2a0e1828d021cd91
|12=>0x32443252a2c182021c31e142c1010030709163408736383051408681003070a1a0400c8c18f0a172408c1cecc0a1a0460e0a286c90230718083408c1c1910a16206811c18c1514343c81c18e0a16206811838c22143408c1c1828a1a046161c1850b1080181183928a1e3408c1c15f0d
|13=>0x541c3181234087230c58d021d30e0d3050b1a0460e7e2c6aa0e987062a285a0043408c3c7048b1a0460e0b09f83021c7062a2d00d021cd86143c6aa0f2c31e142d00118385131a0460e0c4054a1e340870c2898d021c88638287821a0439112285831a0400c202940f1a043860a34087
|14=>0x40086810e3850b1a0464d1c5450b403408c222450b100c08c1d08a8b56340870c1613f1aa838e0c6053e1aa8386142c681186c72e143c6810e182a4083408c1c18f0a1e3408c224848b040438e5e2858d02308857eac6871c1963f7c3438e0c6048d023071e143d0010e44342143df0d
|15=>0x1c1855226340871c1850b0230b8e0c245821a0439b1c144a01a043911c10a8b043408c1c6848a163408c1c6848a163408722fc50b7c1da0e0c2858d0231c8e0d4450f7c355070cc0d0a16340870c7968b040438e3c245a0040438e2a2c68118d870a1e34087364430a1e340cf1c18289
|16=>0x14806810e4431e14a078d02307053824681183820a16c86811c1850f04340801894a8b40340870c2858d0230a111cc050b043408c1d5050b1a0460e2a245881a0460e142d98118383304a2858d0230704142c40d024470a163408ca63850b1a0400c6c38f091680087223988a163408c
|17=>0x1c18c3f1aa83863c7058d02307151635507ae18f09162008c1c1420d023088e3c7048b06043863c705a0021c7060a36b010e383051220681183829c120c6810e182b012340871c1aa8a163408c1c68e0a16340870cc050b1a046111c7050b060808708285a01a0460e3c105820230718
|18=>0xcbc50b043408c1cfca8b7c0c3863c545a0021c31812086810e382891a0438e3a4050f0404386307050d0230704142c18d0200312142c681003030a160808c283828d54043a61c1848a1e806810e4529a143c6810e18f04160c08c1c18284063408c1c1929c142c681183850b1a0463d
|19=>0xe18d15122c6810e1880916080871c4850b040460e0a340874c383057e3408768383424e2878d021c3251228583023070a1e34087b64450b063408cb44850b100460e0c9450f043408c1c7848b060460e142c681196071e122c1810e442890634087227850b100400e0c145081a0400e
|20=>0x37460e0c78e0916080871c2878d54043a60c285821a0461b1c145201a046111c5458d0230a0e0c9050b060460e0c94a891634087230c50b021da0e0c78e0b06043867660a8a1a0460e0b0df8d021c7063c285a0040460e3c2d0010e6c70615706811838304143c6811844e0a1e80681
|21=>0x23075a3cbc58d0230706085458d0200315122d00d021cc0a56355010e1820a16086810038e15142c68100302a5123408c1c9c50b56340870c5450b643408c0c1050b1a04b0e0c287881a04006305448d023073f2a2d5be1a1c3182a246810e44f0a1e08087227848b1a0400c1c2858d
|22=>0x1c4050b100460e0cfc5ab1a1d30e0c78e0b1a046111c285b3020060e0c145031a04611122d00d021cd8e4a5458d02307252a24583021c3181408681183850b02006171c1850f1a046361c605081a0460e0c161511a0438e0d4458d021d30e0c9450b06043912a28581185c706142c40d
|23=>0x242458d021c8a2142d981183833f2a2d58d541c30a16ac0876838322142c08c2e3830a163408cc03850f1aa83d70c2858d0232f8ebc2858d0230706442878d020060620287be021c3243c285820230710142c101183a11516f81810e18c3f2a355070c2450f103408c1c94d0a163408c
|24=>0x1c19f8a16340876838318a2286810e38327142df0d021c70614a078d02307422a2c6810e3831e143df010e3830a824c6810e38351142df076838330142c6811838f15160c08c0c5448b40086810e785ab021d30e0c7848b920438e3c1078d023070644285821a0460e302868118e8706
|25=>0xc4145031a0438e0d0df8a16340871c18e0a1e3408722185131a0438e0c285a0043408c1c9448a1e340871c1850b403408736383051a043991c18e0a163408c1c28583021ed8e0c1450d020060e0c2858d021f08e0c7848f1a0438e0c287ab1aa80870c9450b06080871c1850b1a043a6
|26=>0x21c706142f28d021c70684287be1a0438e0c94a8b04340871c1850b1a043e41c1850b403408c223850f103408c1c1850b1a043b62238e09142c10d021c70a1e340879638342142d58d021c706142c1010e6470638285831a04386602858d021c7063c1058d0230706142c6810f8c706
|27=>0x163408c28383042a2c6811838305140c1010e3831814355010e1820a16206811c1850b1a043c41c1850b1a046591c185671a0438e0c88a8a163408c1c1963f1a0438e0d4050f1a0438e0c7848b1a0460ea2285ab1a0438e0c287821a0460e3029f0d021c706143c10d021c8b0382858d
|28=>0x2a285be1aa8386142c68119a87067e545831a043862a2458d0230715122c6810e4450f1a0400c0c2810d021e30e0c8850b1a0400c1c1880a16f80871c18a8a16f81810e193bf142c6810e38325142d00d021c706a22878d54043867e285e91a1c706142c6810f1470658246810e3830a
|29=>0x84fc50f1a0438e0c2858d023071d122858d020060e0a286c9021c706d62858d021c7064a2878d021c706122c6810ea4706202458d021c7062a245831a04386242858d0230706142c6aa0f5c706142c6810ed0706242858d021c886143c6810ee87063c54582021c706482858d0230706
|30=>0x21c8864a2858d023070a1634087363831e143c681183832f142c681183830ad8340871c18f0a1e340872218c091a0438e0d3050b1a0438e0c285be1a1f30e0c78e0916340871c19f8a16f81871c18f0a16800871c18e0a16086810e38a8b1a043d71c182891a0460e862858d021c706
|31=>0x2a2858d023071c142c6811844725122858d021c88e60285821a0438e0cc128a16340871c1850b1a043d31c1850b1a043ef1c18f0a17a40871c18f0916340872239f9516355070c6848a16340871c1848a160c1010e3b70a16340871c18a8a16adf0d021c31516340876c38315142d00d
|32=>0x63408c0c1050b1a0400e0c285ab1a043a61c1848a16806810e38f0916080871c94e0a16340871c1848a16364810e3a10a1e340871c1aa8a16340871c19f8a16adf0d0e3831e152878d021c706142c40d023088e602858d021c88e0cb050d02307062a245821a0438e0afdf0d0e3831c
|33=>0x18383251228583021c706a2fc50b7c3438e0c285831a043da0c9450f04340871c18f09160c0871c1853e1a043c61c1850b1a0460eb41453e1aa838e0c60e0a1a0438e0c15f831a0438e0c1448d021c88e487850b1a0460e0c60a8a1aa80870c2858d023148e0c4050b1a0460e0c5450b
|34=>0x2307057e355071c1850b1bc00871c18c1512340871c18a8a1620681183830a163408cb63848a1e3408c1c7850b1a046111c285821a0439b1c1850b060808c1cecc1514340871c1a10a16f81810e383253c2858d0230715142d58d5404386142c40302307062428582021c7063028681
|35=>0x82858d0230706442858d02307067e285ab1a1c706143c6810ed870630286810ee8706e660a8a1a0438e0d09f8a160c0871c1b88a1a0438e0d4450b7c3438e0c285821a0438eb4285821a0400c1d0c50b56340871c1850f1a043d71c19f8a16ac6aa0e383054a246810e38315142c10d
|36=>0x1c18c15143408c1c1a18a16f86810e3831e142c681003070624285be021c706142c6810f80706142c6810f7c70612287821a0438e874450b1a0438e0c78a8b06043863c2858302307063c7058d021c88e0c2450b40086810e3a88a163408768383252a2c6810e3831814086810e38324
|37=>0x943c6810e38315142df0d021c70614a078d021c706242858d021c70612285831a0438e0c285be1aa838e0cfc50b06340871c1848a1634087223b90a16340871c1850b7c0c0871c1848a16086810e3a895142c6810e3830a1e3408c1c1850f1a043910c285a006340871c1a10a160c087
|38=>0x21c706142c40d0230706142c6810f2c706142c6810fd47067e2858d541c7063c2458d021c706143c10d021c706142c6810f98706142d5be1a0438e0c285a01a043911c18f0a1e340871c1ba0514340871c1828a7c340871c1850b40086810e3831c142c6810e38315142c6aa021c30a
|39=>0x7e2858d021c706301450d021c70630286810e3830514355010e383427e2858d021c7064a2858d021c706142fb0d021c706142c6810ea4706202858d021c7062a285831a04386142c18d0230706142c6810e38e86142c68118447057e340871c1850b043408c1cb050d021c7062a2458d
|40=>0xe38315142c10d021c706142c6810f6c706122878d021c706142c182021c706142d5831a0438e0c7850b060438e0d4450b1a0438e0c2858d021c75a0c2858d020060e0c5450b1a0460e0c2858d021f40e0c285ab1a0438e0c2858d021fb8e0c70a8a16340871c18e0a16340872238351
|41=>0x50b1a0438e0c285be1a0438e0c1450d021c7062a2858d021c706142c6810e44706142c10d021c706142c18d021c706142c681183830a16355010e383182a28681
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x786039301b180ccc060602d30151809cc0486021300f1806cc030601530091803cc018600930031800cc0006
|6,0=>0x119388adc448e21d710b3883dc410e20170fd387cdc3d8e1e570ef3875dc3a0e1c970e1386edc368e1ad70d33867dc330e19170c53860dc2f8e17570b73859dc2c0e15970a93852dc288e13d709b384c18252e122708db8451c21ae1067080303e5c1e4e0eb70723837981aee0d07064b8309c176e0b47056b829d8142c09a7049b8231c10ae07e7
|6,1=>0x1f6b8f99c7bee3d871e8b8f29c786e3bc71db30ebdc750e3a171cd38e51871ae38671bfb8de1c6e2e36a71b1b8d71c6aae34e71a3b8d01c672e3327195b8c91c63ae3167187b8c21c602e2fa7179b8bb1c5cae2de716c30b45c594e2c3715e38ad5c55ce2a7715038a65c524e28b7142389f5c4ece26f713438985c4b6c2547126b891d8480e2397
|6,2=>0x1155c89ce4477220390e5c864e42b721239075c82ec4107204b9009c7f6e3f47
|7,0=>0x31d398ca0c550622830d4184a0c15060372fdc17ce0bd8e5e572ef3975dcba0e5c882e0b96e9cb6505ab72d1c1671cb29058d72c3395fa0aed056e82b3b957e0ab0e55082a4b95060a7305318294c14860a34e51282854140a09f6e4f38275c1391c9bae4d7626839322098104b97259392adc948e49c824a412320909047c823a411b208c9045c8
|7,1=>0x40ec2059d01d080683ff41fda0fdee7e783efc1f5e0f9f07c783dfc1ede0f5f07a783d039e620f22e78983c139dea0ee6e76b83b1c1d6e0ea7074c73a2b9cf9ce6d072f739439c85ce34e7137386b1c160dfb06f76377c1ba1cdc106d8836841b220d8106b9735939aadcd47069c734a41a320d09067d733ac19b60ccb065d832b3993dcc90e6417
|7,2=>0x4ff427da13dee9e874f0ba76613a309c984e13a6edd36709ab84d23a675d32ce98f74c3c25fe12ef097074b4ba589d2b6e95474a6ba516127b093674974249a123d091684874241a11fd08f86478ba3a9d1c6e8dc746a42332118ae8be745b422ba114ee89f844bc2241d1110881743cc21c610d4e862842dba14e10970843841e3a0d2105ae8258
|7,3=>0x5f4c2f8617b30bd275e5baf11d7790bb485d6bae96173ceb9685c7bae1e16ff0b7785b7c2d9e16bf0b5875a842d25d6830b3a759942cadd6470b1b8589c2c31d6090afc857a42bb5d5cceade856b42b3a158eeabf855bc2abe1550eaa1754cc2a49d516ea83853dc29ce14d70a63852dc294e14970a43851dc28d1d4590a24850e42852141aea067
|7,4=>0x622c30f6186cec2f7613c307e1830ec1086044300217f2ebf18
|8,0=>0x725c390a5c750e328714cb8825c310e10870443805dbf30df186f4c3789dbb50dd286e54370ddb752db376d5c3691db372d9476c643615daf92d7486b5cb58a5ab50d5286a54350a1a732d3186944b4821a310d1086844340219ef2cee96734337dd9af0cce9662cb2f9d96eecaf8653c327e192f0c8f86434b1fa18eb2c6d86324b175d8ab0c4d8
|8,1=>0x8254410a2075103198144c082202f3010780444005dff30ff187f44bf7e5fad2fce87e343efa1f6d0faf77d34be7a1f2d0f8d97c2c3df25eeaef6d87b2c3d761eacef4e87a3bbcfe1e6f0f2e979343c7a1e2d0f0e878433c021def2ef0777443b821db10ed0876443b021d710eb0875443a821d310e90874443a021cf10e70873443985dcb4ee537
|8,2=>0x92a449322489123b991a3c8b22447321a9908cc826240311f898f8447a223c111d888e7cc71a637ef1b788d7c469e233d319688c6cc61622fb117678b74459a22bb315678a7bc51e227d313778974c496623b111498864441221faf0f49875cc38e21b530d288654430de17710b38855c4291e13730938845c420e20f7107388354c18a20b6f0529
|8,3=>0x127e893b449b664c9325c8
|9,0=>0x51f628e9346c8a324517228a7344b8a21c50ee2867142b8a11c506e2827140a9a00ccfe267e113e979f0c4f6267a113c889e044ee2276113a889d044e65e724f38b79c23cdf226e9136c89b244d7226a9134c89a244cee6665332a899144c6a262333098980c4be625e132e8897044b5e659f12c6995f44ada255d12a6894ecca59e51ef2869
|10,0=>0xa5dc52d1e95914a48a4e45252291af4858
|11,0=>0x14c37
|_,_=>0
def wAt:=mkWire dB 120 254 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x2a3714391c791a290e191e191c7a1a2916291c19140e1a390e1904291c291a190e190e1910291a310e191a3114191c3116290e1906291a391c192a2d18291c290e1916393c3b143514191a191c791a290e190e191c2d0e1914451a451c190e1906291a392a2d143118392a1914390e19140d1a391c311a310e19141916290e19
|1=>0x1c251a390e19141916290a39142d0e191a451c192a3114390e1910391a310e190e19140904391a192a191439163914351a3116390e19062b1a392a310e19143918290e19143516390a3b141916290e1916391a290e191c2d0e1920191c7a1a291a310e191c260a3b16291a451a290e191c1916391629562b402b16a50e191c19
|2=>0x1c290e1914821a31143116390e19642b16291c2d0e1914451a451c1916a52a370e19062b16291c7a1a290e192a311c290e1906190e1914351a3914391c791a290e191a1916391c7a1a290e192a371c290e1914192a2d1c290e1916391c7a0e19140d1a39443414012a2d1c291c350e191c25141922290e191a451c1944371401
|3=>0x14192a2d18392a1914390e191c350e191a2514190e1930372a2d14391c19143d1c2d1a25141914192a2d1c290e19142d141906311a390e192a2d143914191c193c311a290e191c961c2d142d0e19143118392a1914390e191a311a290e191c1916390e193c311a290e192a190e1914351a3914390e191c311a260e1918292a2d
|4=>0x1c2d1a451c1916a52a3714390e190e190e191c2d14351a451c190a391aa902391405162916a51c1914192a371c290e1906311a390e191a19143118390e19183914191a310e1930372a2d14051439023910291a310e19142d0e19402b04391a1916291a390e1918392a2d18291c290e191c3514191c3116290e191c3516291c25
|5=>0xe1914190e190a3b16291c31143116390e19222914351c191a290e190e191c3516291a191c1918291c290e1916291c351c191a19062614191a390e1914351aa90239863714ad7c391a0514211a3116390e192a3114390e194a3b140904391a19843b1afd02290e1914451c191c351a3116290e19143118392a2d14390e191445
|6=>0x1a190e191e2b16393e35140218390e191a191c191e2b16397c291a051c2d4a3b04291a19140218390e19141906311a390e1914011c310e192a371c291c7a1a291a391afd1c2902290e19140904391a19402b1c091a19143e16390e190e1916391c7a1a29402b1c091629863b56291aa9023952192a3714390e1918391a311a39
|7=>0x16290e1914192a371c2914191c7a1a290e191c19140916391a19141914391a390e191c1914192a371c2944372a3114390e191c19140d1a390e190e191a291c291a197c291a051c191a291c291a190e191419223714391c1918392a2d14390e1902391afd1c2902291c2d1c051a291a05162914821a45562b1aa902391c290e19
|8=>0x1a191a191c311a290e19602b1c951a2514191a191c3116290e191c310e191e2b16391a29043b1a190e1930192a2d14390e190e191c0a16291a192a2d18291c290e192a3114390e19760730192a2d14392a1914390e192a2d2a310e191a021c3116290e1906191a311a390e1916393c191a290e19162914ae7c391aa902391405
|9=>0x1c1914ad14ae7c391a050e199229043b1a19562b1aa90239043914391a190e191a290e191c2514197e351a3914051629402b04391a197c2b1a051c051639061914351a390e1916a52a3714390e1916391c7a1a2916a51c192a3714391a19163914451c191a39141918390e191e1916391c7a1a291c191629140e1a3904291439
|10=>0x1c1914191a311a390e19143914f97c391a051c05142d1afd02291a051e291c0516390e19402b04391a19201916391c7a1a29142d1a1118290e191a290e191c1916393c39143514191a191c191c1218290e19142d06051c3502291a050a3b140516290a390e19141916291c2d14351a451c1902391c2d7c291a052a2d14391419
|11=>0xe19148204391a191419142d1a451c1918291c291a190e191c960e191a2514191c961a2514191cfd022928391a1218290e191a0554291c051639603b120d1c3514191a191a291c2614191435043914191a190e1912371c2914191c2d14821a451c19a01f3c3d1a291639142d043914191a199c1906331a390e1914390e191a45
|12=>0x1c1914351e1916390e1916290e191c25141906311a390e191a19183916390e191439140904391a191c191a1218290e190e1914751a461c1914191a311c290e1944342a3114390e190e1904291a191c191a3118290e190e193219140e1a391c311a2614190e191a451a291c19483b3c311a290e1916a52a37143944372a311439
|13=>0x1a392a2d1405143902390e19222914351c1914391afe1c05022914191a311a290e191c19182916290e1912391c3514191a2914451a451c1916293205140e1a3914191a3116290e191c3516291c251419162914191ab50e191c2614194a3b1c251a2514191a1912391c35141906191a390e191a2918291a190e191c15142d1a45
|14=>0x1c190e191c311a3116290e191a191c1218290e19143914051a391a0504391a291c291a19143d141916391a1916291a4614191c191a1916391c7a1a292a192a2d14390e190e19140d1a391a191a1218290e191629562b1aa9141916391a451c191c2d4a3b04291a191c350e19162914311a390e190e191c251a25141906121431
|15=>0xe191c19143116390e191c2d14451a451c191c961a2514193c3b143514191a191a19140d1a390e19562b1aa902391629142da2371cfd1c2d1d0a7c291a051c350e191a2514191c19140a16391a190e191a3914461c192a3514390e19140916391a190e1914351c351419b2192a3314390e191a391a291c19141916291a391419
|16=>0x1a051c1914192a2d1c291c2d1a1914351c1914191c311a290e192a3714391239143514191a191c2d562b1aa90e19148204391a19142d0e191a451c191a1218290e193c311a290e191a251c291c1914191ad1a23714a90239143512391c3514190e1930192a2d1439140516290e191c091a291a19148222351c1917652a331439
|17=>0x16295429562b1aa902391a251a3914191c1944372a3114390e191a310e1914461c191c1218290e191439143118390e19043914191c291a191aa91e291c0516391a19143118390e1918392a1914390e1916290e191a2514197c391d0a7c291a0510391a310e191a0218390e1918391a3116390e190e1914192a2d1c2914397c39
|18=>0x3c311a291a191c7a1a290e191c297c291a052a2d14051439023914191a3116390e190e194a3b04291a191c7a1a2914ae06051c3514350e1914451c19443414010e1916291c191a390e19402b04391a1904291c291a190e191c351a2514192a2d14391a190e19443714010e190e191237141916392a2d14390e191afd7e391405
|19=>0x14190e1914351a391439143904391a1914ae7c391a05043b143514191a191a29143116390e192a3114391a190e1930372a2d14390e193c391a291c19141944341aa91405143902395435a23714a9023944372a3114390e190e192a0a14391a1916391afe1c0502290e19383714451c191639140118390e193c3b1c2d1a291a05
|20=>0x2a37143904391a190e191c2d1a251419402b04391a191629140e1a392a1914390e19140a1a391a191c3116290e19547b143502391435141916391c2d1aa9023914091a391a1914ae7c391a05a2371cfd02292a2d2a0514391d0a7c291a051e1916390e191afd1c2902291c2d1a291a0516a52a37143914a902390e19120d1c35
|21=>0xe190a391a0516291c1916391a1914451c191b9914aa02391c2d7c291a0504291c291a191d5d1afe02290e191a451c191a3116390e191a261c1914191a191c2514197c2b1a05163914f97c391a051a19140e1a3912391c351419120d1c35141918291a290e191cd91a2614190a191a39162984391afd0229163914451c1916a5
|22=>0x1a291a0514391a391a05843b1afd0229140904391a1954291c0516391cfa02291a0552192a37143914190a3b16291a1218290e1918291c290e191c3516291a191e291c0516391a3118290e19120f1c3514192a3314390e1917a12a0714392a3114390e190a3b140516293c3d1a29163914191a290e1954291aa9023916391a19
|23=>0x1c0a16291a19d2297c3b1a05140916391a1914192a371c2914191c7a1a2914391c351419140d1a390e191afe1c050229a23714a902391c7914351c1930371e2916391a291c291a193c311a290e191a05143902393c331a290e191c351c29022914191c290e19143914191c19183916390e191a191e2b1639140118390e191c7a
|24=>0x1a0512371c29141914391a451c193c191a290e19402b04391a191c2d1a290e191c1218290e1917b53c071a291c2d14351c19143d141916399229043b1a1914aa02391a051a291c25141914051a391a05223514351c191a1914451c191afe1c2902290e1914191629a23514a9023916391afd02291a461c190e19141918390e19
|25=>0x1ab51c26141914057c391a0514351e0516391a311c190e1914811a451c190e190a3b162914191c291a191a05140516292a1914390e190e1914451c191c191a2514192a0914391a1904291a193219140e1a392afa14391a051cfa1a291a051a291c1914191405143902391c961a2514191a191c35141920051c7a1a2914397c39
|26=>0x2291a3914461c19140916391a1914351c3514191a051e2b16390e1914461c191a05023916292a2d2a1914391a391405162914191c1916293c311a290e192a2d143902392a3714390e191c7a1a290e1914391a390e19143118390e1914ae7c391a051a4514191c19143514191a191c251a251419043b14191a191afd02291639
|27=>0x229163902291aa9023916291a25141914391a190e1902391405162902a52a37143914192a2d1c291a3114390e19042b1a190e190e19141916391c191a290e19148204391a191a191a390e1930192a2d14391c357c291a050e193c191a291c291aa902391a311a390e191a192a3514392a2d14390e191c351a2514191a051cfd
|28=>0x14451c19141916391a1914a9023914351a39143914351a390e19143514451c19043914191a19a23714a9023904291c291a19143d16391a191a1118290e192a3114390e1906051c35022912371419163930370a39162930052a2d14391a391afd0229e42d2a1b14391a0514a902391a1914461c1918391a190e197c391a051afe
|29=>0x1a051a451c191a2916390a3516291a05162904391a1914451c19143902391e05163914391a051e1916392a3514391c35141902391a051c35022914191c192a1b14391a391a0514191a192a05143916390e191c19163906191a3914f91a391a052a2d14390e1914ad7c391a051c311a290e19140d1a391a052a0a14391a193837
|30=>0x1c1918390e1914390e192a0714397c391a0506071a392a19143914451c191cfd02290a3916290a391629023916291afd022904291a19061b1a392a3714391c7a1a291a3914391a390e191a461c191c190e19140516291a190e190a3b16291c2914191a310e197c2b1a051aaa0239140502391a29141916391a1914aa02397c39
|31=>0x1a05162914391c191a191a390e1902392a2d143914391a19042b1a19141916391a391a1906051a3914351a3914a902391446
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x11500000000000010100000388000008600000000000000000000000000000000c4000000a8001
|6,0=>0x25c4000093412242404000000011c4230845100000000219041208020f6a0000000076500001ccc38186c40d441a4432a06320000180c00005c40b0800002a9800000001414269800009641194221043107ca0f08000038400000cd417a000005c20acc1328242000007d40d2818202e205840000000
|6,1=>0x2428000000011d4230a00000001153220a434c00000000000421481a8ff41f4a3d900000f51000000007918ed51d2839147020dd3000000006d90da11b2235140000cf5000000006708cb318ca31446118be417a22e505b90b25000000000000b0215e22b485590aa1000029cc5128000140426d44d08982
|6,2=>0x50549ea13a327224e049b8933425ca000094a8000000000009409253
|7,0=>0x43e8870d0c2215342468391052206440667fd0fda1f743e687bd0f5a1e743c6877d0ee91d943b027510e821cc43908714ce119c0237886e10da21b2235c86accd3a1a4334446808ce2198432a6648cc7218b330e860d0bfa17b42ee85d0cb9116e42d485990b1215f32b6855d0aa1950429a6528c0001464
|7,1=>0x62a8c45186a30a360c8c0cd7fa2fc35f08bd117822ed35d64b9d171a2df45b68b5d169a2cf45968b1d161a2bf45768add159a2af45568a9d151a29f45368a5d149a28f45168a1d141a27f44f689dd13a1a7044d889a11329a6144ba896512b1a52449c89291232242447e68ed11ba233445e88ad113a2234
|7,2=>0x7ee8fd0df823ec47d08f94df0a3dd47b28f551e993cf47968f1d1e1a3bf477c2ee91db23b2475c8ea91d323a2473c8e745cd939747286e411c6238a270c8e091bf9b7b46ee8dcd1b7a36b46d06d911b0235c46b08d589a9234e40000d291a39b43467e8ced19ba33436608cb1194200006488c8118e23193
|7,3=>0x9b8936126a24d04998932100004c4498092f8a5d24b7396692bd255a4a9294c728924f9c9b493072512489c8d491472192419c7f48f691dd239a46f48d871a1232246048b8916122a2450489a7128e232442487e70ed21ba433486250b52151c264844907ce0e1c1848289041206240a280c900cdffa3fb4
|7,4=>0xa0a740ca7fa4fb49f073d4e78a4ed49d29395270a4e01
|8,0=>0xb887704edf1dbb3b7076d4ed91daf3b5876a4ed31da33b407674ecd1d973b287644ec71d8b3b107614ec11d7f3af875e4ebb95743ae275b8eb59d683aca7588eaf9d5c3ab27558ea99d503a9a7528ea39d443a8274f8e9d9d383a6a74c8e979d2c3a527498e919d203a3a7468e8b9d143a227438e859d083
|8,1=>0xd067a00f3e9e7a3cee79d0f389e6e3cd679a0f329e623cbe7970f2d16573ca87944f271e4b3c907914f211e3f3c7878e4f1b1e333c6078b4f151e273c487884f0f1e1b3c307854f091e0f3c187824f031e033c0077f4efd1df73be877c4ef71deb3bd07794ef11ddf3bb87764eeb1dd33ba07734ee51dc73
|8,2=>0xe827cf8f9d9f392e6c7cccf981f2d3e547c9cf921f213e3c7c6cf8c1f153e247c3cf861f093e0c7c0cf8096fe3df67be0f7a9ef23dde7bb0f749ee63dc67b80f6e9eda3dae7b50f689ece3d967b20f629ec23d7e7af0f5c9eb63d667ac0f569eaa3d4e7a90f509e9e3d367a60f4a9e923d1e7a30f449e863
|8,3=>0x7503e9a7d28fa39f443
|9,0=>0x1f3cbe697cb2f925f1cbe297c32f825efcbde97bb2f725edcbda97b32f625ebcbd697ab2f525e9cbd297a32f425e7cbce979b2f325e5cbca97932f225e3cbc6978b2f125e1cbc297832f025dfcbbe977b2ef25ddcbba97732ee25dbcbb6976b2ed25d9cbb297632ec25d7cbae975b2eb25d5cbaa97532
|10,0=>0xfb03f5c7eb0fd51fa83f4c7e90fd11
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 15
def pmP:Nat→Nat
|0=>0x14000000000021800000000041000000000081000000000100000000000140000000000250000000000480000000000880000000001080000000002000000000003c0000000000600000000000a0000000000130000000000250000000000480000000000880000000001080000000002000000000003c000000000060000000000090000000000110000000000200000000000280000000000400000000000600000000000800000000000800000000000800000000000
|1=>0x1f95a0000000282a40000000467680000000204e00000000400c00000000800000000000a0d0000000014000000000020600000000040400000000080600000000100a00000000201000000000401000000000801000000000c27000000001048000000002088000000004010000000008010000000010000000000012000000000023f0000000004240000000008040000000008180000000010200000000012800000000024c000000000480000000000800000000000a2
|2=>0x10110e0000002020d40000004041780000008081700000010094e0000002010840000002001300000004001400000008002400000010004400000020003000000040004000000080004000000100004000000200000000000288a300000004240400000008128c0000001000a0000000200060000000400080000000800000000000840800000001080000000002090e000000040088000000080100000000100100000000200080000000400080000000800000000000fcc8
|3=>0x4010040000008020000000010000600000018040000000030000000000048128c0000006065b8000000c0ca700000018114e0000002c32dc000000582560000000a8cb700000014197e0000002832bc000000506538000000a0ca300000012994e0000002432fc0000004865b800000090ca70000001180400000002232bc00000044653800000084caf00000010994e00000020b0d400000040e760000000818ae00000010196e0000002032bc000000406538000000808a7
|4=>0x110194e0000022023b8000004404170000008800b6000001040008000002000010000004000010000004a10ab0000008040000000010040200000020001100000040001e00000080000c000000ac32fc0000015865b8000002b08b700000056096e000000ac121400000158241800000290cb7000000520954000000a332fc0000014665b8000002810ad00000050197e000000a032dc00000140657800000280ca70000004800240000008211a000000100408000000200806
|5=>0x248004400000428129c0000085024b8000010818af00000210197e0000042032bc000008406538000010800a600000204810e0000040400980000080801100000101002000000201094e0000040000a400000800011000001000020000002000000000002a412dc0000054265f000000a80cbf00000150196e000002a002d8000005000010000008b04b700000116094a0000022832dc000004502538000008a00b600000114011c0000022432dc0000044825b8000008904a7
|6=>0x410197e0000082032bc000010406538000020808ee00000410115c0000080800980000101000200000201002000000400004c00000800001000001000000000001ac8ca700000358195e000006b0329c00000d60457800001ac08a700000358094e000006a032fc00000d4065b800001a800a300000348080c00000690009800000d00241800001a0002600000318014c0000062812dc00000c4665a800001880ca700000308000c0000060c024400000c00041000001800002
|7=>0x600004400000c0000800000154025b8000028a0cb700000514194e00000a2822bc0000145025b8000028a00a700000514014a00000a2412dc000014406538000028800b600000505014e00000a0810900000141001300000280002600000500004800000a00001000001240c578000024800a600000454096e000008a8121c0000114065b8000022804a700000450015c000008a0029c000011040518000020a00b600000414015c0000082432fc0000104865b8000020904a7
|8=>0x1090087c0000210080a8000042000060000080c082e00001000002000002000003000004000004000008000002000010000000000010800180000020406128000040004020000080000600000100000280000200000400000400000600000800000400001000000000001950048800003090cb700000612195e00000c24329c000018482588000030904a700000612016600000c2002c00000184005300000301042200000602004c00000c04009000001808011000003000024
|9=>0x6014112a0000c028025c0001804845b8000300808a70000600410480000c0082018000180100120000202908b700004050196e00008028229c0001004865b800020080ca700004004104c000080080010000100000100000102908b700002012196e0000402422dc0000804065380001002082600002004000c0000400800100000800245380000a8a0cbf00001400001a0000242022bc000048404530000088a0cbf00001094015600002124323c00004240667000008480caf
|10=>0x10001995e00020002e2bc0003014045b800060090cb70000c012194e00018024229c000300406538000600808a70000c002814e000180042090000300084110000600100260000c002004400018002228c00030000010000050288ca70000a050196e000140a0329c000281404538000502000260000a012116600014020329c000280404538000500088a300008050196e000100800088000200406538000400100200000605201220000c028329c0001805045b8000300a08a7
|11=>0x20514114e00040221329c000804424578000888808a600011091595e00020c0812cc000414546538000828808a700010510094e000209202398000410482570000820904a700010411195e00020822329c00041042653800081884ca700010302092e00020603329c0004085465b8000810904ae00010211194e0002040222e800040450253800080888caf00010111194e0002022132bc0004005465f8000800904a700010011195e00020021b3bc0004004065b80008000ecaf
|12=>0x201090395600402108182c00804050e558010004a0eaf002000842444004000a072b400800040e578010000800ad0020001001560040000040700080000080d00088008acef0011000179da0020012033bc004000406778008000010180008c014116600118021229c0022804265380045000cca700088010994e0010c02a329c00210054453800420088ca700084010994e0010402532dc00208044653800410084ca700080010196e000c00631280001800c60500001028a4ca7
|13=>0x8000351996e100002a332dc2000014665b840000080ca708000000094e08000000000008240046653810480088c2702090001984e04110003329c0822000645381040000cca702060001d95a04080062b2bc081000c465381020010800602020020886404020203b2bc080404066538100808044a702010001994e02120020009c0244420566780488048accf00811080d15e00800004221c01000000400001804280caf00300850087200601080019000c00040e76801080087cad
|14=>0x92090010994f0010c021329e00041844653b0200008c82042400011194e8480000020190003004c653900010084ca712090011184e2010002032dc2002814665b84004028ccb7
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0xe00000000700014000d000000000000000000028000807
|6,0=>0x780000931680000250f0280000001000c9906a68000700000364c010880403000009421038400012000000e036081c187d6a838420e000000015038540a070000a0c000287c0e050001c00028b81c0000028540a00002641c154c800a20e00008180f8ba5c24050043ca20601000140000080180002ac082af07014007b00075ac000380c7605000f838050381c7400
|6,1=>0xa01c1b0381c0eb0230000200000000e0c
|7,0=>0x4a98046fe128ae2ab0808d5aed6014428c5653c0d3845d5408b8ff8e8be57b5321e89f6a47662af29d72d2736e0437262fe61ca96952828c34bbb5f864f8476c8501a3c1ebb367761f808d7188985a4f782454dcea379aa9cd1445b90070d03af5053ec790c8b1b3508966032d808490f198ce7e0f22c60e04216176437dc9b003575445913b441609720019514c431a
|7,1=>0xaa8061edba4473751628259c73244c79e11998b002f6c7f3d1375f0bdf2300400bdcb426189960e4607acafe011103352ada8a26f40b88b2090b17f8c84af104327024480360cd5e0712df0752f9f896ee72ae232ef52179856f038ef2b4384eb16e4e6281c3197242d496361c954718c63d2e47a0548474da7549113c52003306e98236c1a00cd40472c5192a50c054
|7,2=>0x15008ee637f4c5d4348909d1b0e
|8,0=>0x746293f54e34809a687ef299cd378a0cb06c9a4d98d4f6d3d8e35650c11f461b2e67856dd6b76b0cb9ec219f2eb318e7526c8dc66979742955c92a49851fb875e72ba73982b19b9434e8a6d3899846a13c425fb339aba6db3e9f43e0f47c4e1c905d73da724af459dbc65b0bbda81958817b819e79cea7f5e496a6f216f1809bda2e0b1516d3c57918501c1966ca8389
|8,1=>0x1404520452906e9e2ee09489d991033fbe7579bd256acfb7e44eac34d5f6482785aa601bf8d426fa3eedb42ed6ce2c14ee51559123ec0f1a62f9e2a834af31dbfc35c33dc0429c919a1aac21f859
|9,0=>0x6f5d2ddb3b86b876a72e722874356cdacd6953b73b9c5d09f66d421c5186e5caeb08de33aae4134a2d294d72a2d6e1474e5e1e14d2a3f1e6fb148a8ab32f6221a6af5a7d8ed70c
|10,0=>0x9a19d0cb96e9b4c545
|11,0=>0x61
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 47 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_252 10 roots_252 ops++addP pm 1 dom_245 9 roots_245 ops++addP pm 2 dom_189 9 roots_189 ops++addP pm 3 dom_124 7 roots_124 ops++addP pm 4 dom_149 5 roots_149 ops++addP pm 5 dom_221 9 roots_221 ops++addP pm 6 dom_188 7 roots_188 ops++addP pm 7 dom_121 8 roots_121 ops++addP pm 8 dom_180 5 roots_180 ops++addP pm 9 dom_212 5 roots_212 ops++addP pm 10 dom_125 9 roots_125 ops++addP pm 11 dom_249 9 roots_249 ops++addP pm 12 dom_220 7 roots_220 ops++addP pm 13 dzo_108_16 5 roots_108 ops++addP pm 14 dom_205 7 roots_205 ops++addP pm 15 dom_173 7 roots_173 ops++addP pm 16 dom_181 6 roots_181 ops++addP pm 17 dom_213 6 roots_213 ops++addP pm 18 dom_29 4 roots_29 ops++addP pm 19 dom_237 10 roots_237 ops++addP pm 20 dom_109 8 roots_109 ops++addP pm 21 dom_157 6 roots_157 ops++addP pm 22 dom_116 5 roots_116 ops++addP pm 23 dom_93 6 roots_93 ops++addP pm 24 dom_61 6 roots_61 ops++addP pm 25 dom_117 6 roots_117 ops++addP pm 26 dom_156 5 roots_156 ops++addP pm 27 dom_244 8 roots_244 ops++addP pm 28 dom_217 6 roots_217 ops++addP pm 29 dom_241 6 roots_241 ops++addP pm 30 dom_185 6 roots_185 ops++addP pm 31 dzo_109_16 6 roots_109 ops++addP pm 32 dom_77 5 roots_77 ops++addP pm 33 dom_45 5 roots_45 ops++addP pm 34 dzo_233_16 6 roots_233 ops++addP pm 35 dom_60 4 roots_60 ops++addP pm 36 dom_92 4 roots_92 ops++addP pm 37 dom_233 8 roots_233 ops++addP pm 38 dom_228 7 roots_228 ops++addP pm 39 dzo_236_16 6 roots_236 ops++addP pm 40 dzo_237_16 7 roots_237 ops++addP pm 41 dom_148 4 roots_148 ops++addP pm 42 dom_141 4 roots_141 ops++addP pm 43 dom_197 5 roots_197 ops++addP pm 44 dom_201 5 roots_201 ops++addP pm 45 dom_169 5 roots_169 ops++addP pm 46 dom_229 8 roots_229 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_253 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45|h46
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_189 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_149 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_221 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_188 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_180 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_212 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_108_16_104 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_29 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_237 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_156 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_zo_109_16_104 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_zo_233_16_104 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_60 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_92 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_228 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_zo_236_16_104 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_zo_237_16_104 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_141 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_197 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_201 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h45;exact cpcs (by decide +kernel) lowS_169 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h46;exact cpcs (by decide +kernel) lowS_229 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_252 10 s (0,roots_252.map (·&&&dom_252)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_253 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_252 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_253==dom_253)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_253 gM v ys):RunD true dom_253 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_253 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 21 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 21 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 143 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 15 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 143 → Z 6 i = true := (range_split z6_0 z6_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 256 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_256 : ∀ i, 256 ≤ i → i < 268 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 256 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 268 → Z 7 i = true := (range_split z7_0 (range_split z7_128 z7_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 197 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 69 128 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 197 → Z 8 i = true := (range_split z8_0 z8_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 63 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 63 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 8 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 8 0 = true)
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
theorem lowS_254:Lower true dom_254 roots_254 goal_254 12:=lower_slice_b [(0x5555000055550000555500005555000055550000555500005555000055550000,4,20)] (by decide +kernel) lowS_238
def isoMvS_223:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_223:Lower true dom_223 roots_223 goal_223 11:=lower_iso_b isoMvS_223 (by decide +kernel) lowS_191
def dzo_239_16:=0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
def gzo_239_16:=0xffff0000ffff0000ffff0000ffff0000ffff0000fffe0000fffe0000fefa0000
def gsh_239_16:=0xffff0000ffff0000ffff0000ffff0000ffff0000fffe0000fffe0000fefa
theorem lowS_zo_239_16_106:Lower true dzo_239_16 roots_239 gzo_239_16 10:=lower_iso_b (d1:=dom_239) (r1:=roots_239) (T1:=gsh_239_16) [(dom_239,16)] (by decide +kernel) (lower_slice_b (T:=gsh_239_16) [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,0,1),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,0,4),(0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_106)
def dzo_111_16:=0xffff0000ffff0000ffff0000ffff0000
def gzo_111_16:=0xffff0000fffe0000fffe0000fefa0000
def gsh_111_16:=0xffff0000fffe0000fffe0000fefa
theorem lowS_zo_111_16_106:Lower true dzo_111_16 roots_111 gzo_111_16 9:=lower_iso_b (d1:=dom_111) (r1:=roots_111) (T1:=gsh_111_16) [(dom_111,16)] (by decide +kernel) (lower_slice_b (T:=gsh_111_16) [(0xaaaa0000aaaa0000aaaa0000aaaa,0,1),(0xf0f00000f0f00000f0f00000f0f0,0,4)] (by decide +kernel) lowS_106)
namespace S_255
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(2,10),(2,34),(2,66),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(4,20),(4,36),(4,68),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(6,14),(6,22),(6,38),(6,70),(6,134),(7,15),(7,23),(7,39),(7,71),(7,135),(8,9),(8,10),(8,40),(8,72),(8,136),(12,13),(12,14),(12,28),(12,44),(12,76),(12,140),(16,17),(16,20),(16,144),(18,19),(18,22),(18,26),(18,50),(18,82),(18,146),(24,25),(24,26),(24,28),(24,56),(24,88),(24,152),(32,33),(32,34),(32,36),(32,40),(32,96),(32,160),(48,49),(48,50),(48,52),(48,56),(48,112),(48,176),(64,65),(64,66),(64,68),(64,72),(64,96),(64,192),(80,81),(80,82),(80,84),(80,88),(80,112),(80,208),(128,130),(128,132),(128,136),(128,144),(128,160),(128,192),(129,131),(129,133),(129,137),(129,145),(129,161),(129,193)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffffffffffffffffff
def xsM:=roots_255.map (·&&&dom_255)
def gM:=goal_255&&&dom_255
def NN:Nat→Nat
|6=>7
|7=>35
|8=>72
|9=>126
|10=>90
|11=>29
|12=>6
|13=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0xe300fd9a12d81a5c114d52e9f3e1a50cb16
|7,0=>0xd8831d261cd0bf2b08bfa2a6b9f79f950178263f7373a6642f61f1360d625aa315776555ef84cf224964e406363eea03a54a2c82b2b5b927d71274c624aa5241fa19e1e168bf14aee10c9a0ba550b93509c840754d01559
|8,0=>0xf148de4182e239ec3287be389ae6b4aa9c2aa57ea930ca5ac4a5219a2fdea27f8965898e9ed8ae1e8a7198678e852a0841aa778be7701375e6a725597211571c4c6aea564eb1617565ed3b5d5a5598505709a5658452b83525e051457510a65036f4feef4af30464764468d431aa3f4553e7d53c17e394c7388f73573032bf0324642f39f2e6122bdc82b64a29b57256bc223f0207be1d4f21b33519b9f13b2e1372412d6a07dfa0752a06a96063c3040fb02a70
|9,0=>0xfa50ff4d66f02ace8bf8e810adf4a9dc647dc4a1d67dbd4dedd2f59d10e5d08d6d0333cb553cad18ca373c9b72c9b1fc7bd7c20a6bd1a8bc528b77f3b721ab0943a939da8a95a4ad1a438ea340fa212d9c01398b78988cb927a58f7208e5588dcbb8b84e890148518e847e9841167d5ab7d4f77c9fd7bcc678d03766c270f3a7030b696ec655d3628b75f4ac5ddfd5661a53f3a532a7525bd506b34f6b24db424cee34a9ac49ff24978c47d54425de4115840ff140fda37a2134a5e348a533cc732e423223c2fbf72fa9f2e5cd2ce9b2cdac2c4072be862bda52acf92873b287152700f2544924f122498c23e3d22ac92100620d3120446203c32020a1e8521e12f1d1ea1baa61a7c216eee15d081490a145d6142dc140a012bb012a281266c104270a75a0970108b710846c075d6067cd06349044e1021ca01efd
|10,0=>0xf8adcf73fbf6a56dc7f7d436dd1c8dd0d34ce406cc8decb895c815cbeeabbea0eb7f36b1a1ab0b95aca28a9af8a50d2a2c65a0e2a9f6fe9ed599e11695367949c29329691df3903bf8e17a84ec5845207c9ea7b9157b5077986678262752096fbdd6bdc46b3716ac2e689f266ac965855620bf5f4185f16b5bed05a39a58ba758a755747b51dfb50f6c4f7dd4ee384cbc84c81a4be7549f4848a6b478c5460ec4592a441c33fdf93e7b238dc23554632b5029a83267e825344249261fe801f392195e11661e13ddb13d1612b7b104f80d4730ba0e093df0789106d6704a35034ef
|11,0=>0xfb047f2f5cb6b15a763d9bd26975d496f2d9608e958018e32277077732c866f0c64123616d65fc7f57fb951a4a4ea8745eaf35c892bfee1780c130ba0c98c09e0809dfc0946306fa0
|12,0=>0x9e29199b3f792e461eec0eef70c075
|13,0=>0x64457
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ff000000000000000000ffffffffffffffff0000000000000000ffffffffff00ff00ffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000000000000000333333333333333300000000000000003333333333003300ffffffffffffffffffffffffffffffffffffffffff00ff00ffffffffff00ff0000330033003300330033003300330033003300330033003300330033000000000000000033333333000000003333333300000000333333330000000033003300ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa333333333333333333333333333333333333333333333333333333333300330000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000ffffffff00000000ffffffff00000000ffffffff00000000ff00ff00ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
|0,1=>0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000ffffffffffffffffffffffffffffffff00000000ffffffff00000000ff00ff000000000000000000ffffffffffffffff0000000000000000ff00ff00ff00ff00ffffffff00000000ffffffffffffffffffffffff00000000ffffffffff00ff0000000000ffffffff00000000ff00ff0000000000ffffffff00000000ff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffffffffffffffffffffffff00ff00ffffffffffffffffffffffffff00ff00aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffffffffffffffffffffffffffffffffffffffff00ff00ff00ff00ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000
|0,2=>0xffffffffffffffffffffffffff00ff00000000000000000000000000000000000000000000000000ffffffffff00ff00ffffffffffffffffffffffffffffffff0000000000000000ffffffffff00ff0000ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff00ff00ff00ff00ff0000ffffffff00000000ffffffff00000000ffffffffffffffffffffffffff00ff0000000000000000000000000000000000ffffffffffffffffff00ff00ff00ff00000000000000000000000000ffffffff000000000000000000000000ff00ff000000000000000000ffffffffffff00000000000000000000ffffffffffff000000000000000000000000000000000000ffffffffff00ff00ffffffffff00ff00ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff000000000000ffffffff00000000ffff000000000000ffffffff00000000ffff00000000000000000000ffffffffff00ff000000000000000000ffffffffff00ff00ffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffff000000000000ffffffff00000000ffffffff00000000ff00ff0000000000ff00ff00
|_,_=>0
def sP:Nat→Nat
|0=>0x54614f10204035019114f10225018510320055018550a2133462c53c404918b1440c701518b1440c101518b1542874d01921440c200d40644b1440ce40614428834614f10204e18b1442873462c510304c18b1442872461442070061440c2040
|1=>0x101921440c800d4066453c408e4061542884cd4061540c24cd1853d40814ce18b1542874d01911440c200d40664b1440ce3501853c408d18b1540c14d01911542884cd40614f10231018b1440ca38d4062c510355018510308038d18b14f101
|2=>0x1540c201340644b1540ca4c940614f10201a6064453c438d31018b14f1154061540c80133894062c51030153462c53c404e4061440c800c18b1542874ce4062c510328d31018b1440cd3062c53c40501991440c20101991542884ce4061440c2
|3=>0x19914f1091853d40810136862c53c404039018b1540ca4d019148b1440c054d4062c53c44064455032004cc4062c510300c18b14f10100d31018b1540d334c18b14f5014ce2501853c40802462c55030404d81992c53c404c4066453c4090199
|4=>0x48b1440c024d6062c53c43501912c53c43901855032004d01992c55032936901853c408039a4062c51030101914853c408039a18b14f10100e54d4062c53c440648b1440c06981916453c438c4062c510301a19214f1010094061540c201368c
|5=>0x14f11540614f10201a1853d40810133954062c51030153501853d40934066455032004ce4064853c408038d40644b14f10960644b14f10e6901853c40806862c55030404d535018b1540d34064853c408054d18b14f5014c935019914f10e406
|6=>0x3c439018b1440c03501853d409331018b1540ca4ce35018b1540d35501855030804c96901853c408038d18b14f5014da35019914f10d18b14f5014ce5501853c408025a4062c510300d4064592c53c44064855030804d01912c510300e35018b
|7=>0x3d46d739540614f50201325a4062c550301368c19214f5006901916453c401525018b14f10035019164b14f5135561912c53d40101912c55030133901855030804d01921540c801355018b1540ca4ce40614f10200e3501853d4093698191485
|8=>0x4064592c53c400935018b14f1004064453d40804cd40664b14f5133901912c55030134062c55030132501922c550301368d4066453d44c96907cb14f10068d6062c53d44d018b14f11e0155862c53c401c4062c53c401569019214f517406485
|9=>0x19914f51739018b1540c04c969818b14f5173862c53d40404e14122c53c400969819914f51341f2c53d48173501922c53d45da6064853c40096901853d40804cd40665214f5136967cb14f1002507d22c53c401840644b14f1155864853d400e
|10=>0x3d401a5866453d45c940665214f5174122c53c48c089019214f1008502c53c45ce40664b14f1002507cb14f51739019114f50201325019214f50201361619148b14f51a60645214f5136967d214f5002501912c53c400e3501992c53d44c9690
|11=>0x14f11569019214f1003894062c53c40101922c53c40409164522c53d401018b14f10201a5867453d400c40664b14f1101992c550301360644b14f5014d558664b14f10068c1853d40804e44112c53c40102c53c48d73901853d40804da586445
|12=>0x6453c400e2462c53d40404da41f4853d45c960648b14f1006901914853c400e4066453d40804da41f2c53c45cd31018b14f5132462c53d40404d569618b14f5174066453d40804da35018b14f1003901992c55030139102dd14f10061019164b
|13=>0x65214f51731018b1540c04ce40648b14f10099648b14f5008562c53d45d540664b14f11791065214f10039019148b14f10095819914f51389618b14f10085648b14f50038c4062c53c401858644b14f51a6064453d44ce34c4062c53d44da586
|14=>0x7cb14f5176161992c53c469819914f1134066453c480055618b14f5174062c53c49c03954062c53c400e54d4062c53d44d01922c550301355019214f10038c4062c550301368c19914f51354d4062c53d44d018b14f1010245992c53d45d5406
|15=>0x4062c53c401540614f5020133954062c550301339019214f50201331019214f50200960644b14f51331018b14f1020154062c55030136161994853d44064853d40804c935018b14f51769019114f10024d4066453d44ce40648b1540c04c9690
|16=>0x14f5005501912c53d40135501992c53d45d340644b14f50101339a4062c53d401391048b14f5170244194853d401339019148b14f5004e25862c53d40134064592c53c40102c53c48c04ce31018b14f5004e44192c53c4013910a0b14f5004ce
|17=>0x6453d48004d84062c53c45d018b14f52701361019148b14f5133954062c53d401325018b14f1006101922c53c40154064853d40134062c53c480055018b14f1004d018b14f50101340665214f100a5018b14f5004ce40648b14f5004cc40648b
|18=>0x1992c53d40404cc4062c53d40804e54066453d4013ad018b14f5004e56062c53d401325818b14f5004d641f2c53d45d640644b14f50069019114f5004e140b14f52a0135901992c53d45da4066453d45d34062c53d481701858664b14f513406
|19=>0xb1018b14f5004da3062c53d401339018b14f5004cc4062c53c402658b14f5004ce25a4062c53d401391664b14f5004d540665214f5004e440b14f11702441148b14f5004ce40644b14f5004e45922c53d402158b14f5004d540664b14f1004d0
|20=>0x1994853d401858648b14f50069819214f5004da59f2c53d40135901992c53c401a4066453c401369818b14f1004c96907cb14f5004d55862c53d401371018b14f5004d64064592c53d401a40645914f5004d569018b14f5174d019148b14f100
|21=>0x14f51340664b14f11740648b14f50101369819914f5134062c53d40804d07d22c53c40244112c53d4013b5018b14f5004e458b14f1004122c53d48c04e24064853d401361618b14f5172501912c53d401389018b14f1004e14122c53d4013590
|22=>0x14f5004d54062c53d40135907cb14f5004d640664b14f5004d84062c53c40135901922c53d40102c53d48c04da4064853d401391064b14f5004e140b14f1004d64064522c53d401a40645214f5004d01994853d45e440b7453d401361019164b
|23=>0x19914f5004d01a82c53d401369818b14f5004d01922c53c40164062c53d45c061618b14f5004d018b7453d40132501922c53d40135501992c53d401359018b14f10025a4062c53d401340644b14f5004d01992c53d45d341f48b14f5004e458b
|24=>0x1018b14f5004d07cb14f5004d01992c53d40134062c53d45c04d018b14f1004d84062c53d401340648b14f5004e140b14f5004cc4062c53d40136101922c53d401389018b14f5004d07cb14f1004d01992c53c4013690
|_=>0
def sO:Nat→Nat→Nat
|6,0=>0x2a7023701c7015700e700770007
|7,0=>0x13f8137812f8127811f8117810f810780ff80f780ef80e780df80d780cf80c780bf80b780af80a780a0709880908088808080788070806880608059705180498041803980318
|8,0=>0x365935c9353934a9341933983318328931f9316930d930582fd82f582ec92e392da92d192c892bf92b782ae92a5929c9294828b9283827a9272826a8261925892508247923e9235922c9224821c8213920b820291fb71f291ea81e191d891d081c791bf81b781ae91a5919c9193918b8183817a9171916981627159915091479
|8,1=>0x3a993a09397938f8386937e8376836e8
|9,0=>0x5d995d185c985c185b895af95a6959d9595858e7585957d8575856c9564855c8555754c9544853aa530a527951e9516850d9503a4fa94f194e894df94d784ce94c684bd94b584aba4a2949a8491948984818477a46e9465945c9452a44a8440a437942e9425941d8415840d840493fc83f2a3e8a3e083d793ce93c4a3bb93b29
|9,1=>0x7f987f097e6a7dca7d397ca97c197b897b087a7979e9796878d9783a77a9772876a8762875a87528749973fa736972e8724a71c8713970b870386fa96f196e896e086d976d096c886bea6b686ae86a6869d9695868d8683a67b8671a66986609657964da645863c9633962a96219618960ea60685fd95f495eb95e29
|10,0=>0xa439a39aa309a279a1daa13aa09aa0099f799ee99e599dd89d589cab9c199b7a9af89a5a99ba993898b8981a977a96da964995b9952994999418938992f9926991d9914990b990298f998f188e898dea8d4a8cc88c398ba98b288a998a09898888f9885a87c9872a868a85ea854a84b98429837b82e9825981d8813a80a98019
|10,1=>0xb2b8b21ab17ab0f8b069afcaaf48aeaaae28ad99ad18ac89abf9ab87aaf9aa69a9e8a94aa8b9a829a799a709a679a5e9a559a4c9
|11,0=>0xc2f8c269c1cac139c0b8c029bf99bf09be79bdf8bd69bcd9bc49bbaabb0aba88b9eab959b8c9b839b7b8b729b699b5fab569b4d9b458b3c9b339
|12,0=>0xc638c5a9c519c498c409c379
|13,0=>0xc6b8
|_,_=>0
def wAt:=mkWire dB 46 256 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 8 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x2d350015134e43380d84d400430338fd665413544d2c398492d35001380d44d599504d30bd44d380cc2d6135001240d44d38bc0252d6504d513430330b584d40050465134e034114b5d0134e2f5134e032d7404d5134b0e0094b59413544d240ce430094b59413544d0d0c0252d6504d
|1=>0x61350015134e2f0094b594134e4338fc0252d6504d0105046513594d2c0544d2c04c2f613500138fce2f599402d413430338fd0452d7404d5134e2f0094b59413544d4804b412d340415134e0330b584d4004b0e553582d400544d38fc0252d6504d2c39665513402d413544d0c0d849
|2=>0x38fcc2d613500140b544d450d2012d34e2f38fc0252d6504d580502d513402d4134e4338bcb594134e43513576940b404d0c0ce3f6124b4d400544d38fd1412d3544d01a49036934b412c38e3f4114b5d013544d38fcc2d61350015134e4330b584d0104e0338fcc2d6135001390ce03
|3=>0x412544d2c04b4d51358492d3500140049035134b59413490341252012d3544d2c38e3f6124b4d400430338fd66500b504d38bd44d5da502d0134e3f513576940b404d5134e2f45052012d34e43513576940b404d380d54d513582d400544d38fd8492d350016534b012d0544d010544d
|4=>0x240d44d2d6504d38bd54d513582d4004e435da404d38fd82d4004e0338bd82d4004b0e38fd66500b504d5134e2f6124b4d400544d380d0452d7404d48052415134b4d010544d38bd76940b404d38fce435da502d0134e0338fd54d60b50015134e2f6124b4d4004e43380d82d4004026
|5=>0x94b59413430338fcc2d61350010098e3f0094b594134e2f38fd54d60b500138bc0255135a4d2d04903390c0252d6504d2c040265135a4d2d04903390c0252d6504d38bd54d513582d4004e3f009544d6934b41380d045513594d2c04e3f38bd8492d3500138fd44d4114b5d0134901
|6=>0x38fc9016934b416134b412d3404140b544d6534b0101a544d6934b41380d1416534b01653506500b504d38fd0452d7404d30bce3f30b584d4004b0e38fd8492d350010c0d54d60b500138bd665513402d413402638bc0252d6504d2d052015134b4d4004e3f599544d00b504d0098e2f
|7=>0x411544d6534b01240d44d2d6504d38bd0452d7404d380d66500b504d38fd0452d7404d38fd8492d3500138fc9014904b4d00b49036934b41006544d6934b4100990016934b416d3544d4198b01419544d00b504d750544d480cb4d0135a012d04b4d0134b4d4198b0138bd54d60b5001
|8=>0x380d66500b504d693404d40b4b0138fd8492d35001693404140b404d41190452d7404d606544d2d3500100b50016934b410134019490cb4d01349034904b4d010544d2d04b4d38bc9016934b4100b49034904b4d51340192d0504d51350492d34601480544d2d350012d340692d0504d
|9=>0x7d0c04d180544d2c24c2f613500140b504d2d7404d40b504d2c0404d4124b4d2c0404d513507e2d3460101a944d2d04b4d01358195135001513566500b504d006404d2d6504d38bd0452d7404d38bc9014904b4d40052012d3504d4804b412d340412d340192d0504d41252012d3544d
|10=>0x9944d6934b4138fd66500b504d5135019480cb4d400544d6534b0101a544d2d04b4d51340252d6504d51351434804b4d41340492d346415134c2f6135001413502d480cb4d580544d00b504d38fd66500b504d40050462d7404d419544d00b504d2d04c2f613404151350192d7404d
|11=>0x41358192d3404130b584d5135001400504d2d7404d4804b412d34041380cc2d613500140b544d00b504d390c0252d6504d2d040192d3404d490544d2d34041012544d2d04b4d38bd66500b504d006544d40b404d380cc2d6135001390c0252d6504d01a404d2d0504d38bd66500b504d
|12=>0x419544d2c04b4d38fcc2d61350012c040592d0504d01a49036934b41450d44d2d7404d41350192c0404d01359412c04b4d38fcc2d6135001612544d2d35001900d0192d3504d6065001413404d013544d4194b01406544d2c04b4d51351414804b4d2c04041693cb41413544d01a8b41
|13=>0x38fd54d60b50014134b012d3500138bd8492d35001009804d2d6504d012544d2d04b4d009802d2d6504d38fd8492d350010135a4d40b4601400544d00b504d2c04b415134041412944d2c04b4d01340692d0504d513584a2d35001553544d60b5001380d54d60b500138fd8492d35001
|14=>0x4194b0101350462d7404d5da502d0134b4d406404d2d3402d19051414804b4d413406a2d0544d6534b0141f86015134c2d613500100b4641513594f00b4641599544d00b504d38bd54d60b500138fd54d60b500138bd8492d350012d34c2f613500140052014904b4d5134c2f6135001
|15=>0x13612f60650014134b01013404d40b4b0101352432d3500100b504d00b52432d3404d51350016128b4d40052012d35001553582d400544d2d6504d5134b4d400582d2d3500151352432d3544d60b50014118b5d013544d2c04b4d428594f2c058492d350016134b4d40059416534b01
|16=>0x2d0504d6124b4d400584d5135001900c64141349016934b41413402d19059412c04b4d013464151340492d346414114b5d01350192d3504d4135819010544d4194b01450d94d2c04c2f6135001693c02d2d0624d01a8b410105a4f2d052412d34041180504d013504d2d7404d40b4b5d
|17=>0x41f8b4d1804b4d01a8b41400504d01352014904b4d513406a2d058192d350012d3402d413504d2d340412d04b4d01040192d0504d513402d413544d40b4b012d0544d0105a4d40b460101a4b414135075480cb4d653402d413594d40b4b0101a502d01352012d3544d5da902d0134059
|18=>0x2c0404d2d34601190504d60b5001006504d00b504d51350012d3504d41f86012d04b4d00b4641606544d40052012d3504d4804b412d34b4d2c0404d40652032d340416534b015134b0101351434804b4d400502d2c04c2f61350012d3460151350192d7404d553d82d400504d190544d
|19=>0x1804b01013544d4004b4d606500161350012d3500101a8b41180544d2c0544d40b4b01653cb012d040412d3544d413404d4134041480cb4d4904b4d4194b01513504d6934b412d7404d
|_=>0
def oO:Nat→Nat→Nat
|7,0=>0x21a800007ca00001ca800006a8000018282c4000000000000000000000001330000000008180da8000000005580000105016a000002b0005000000000000000
|8,0=>0x2f0a5cd4b7296952c8a57d4ad295552a0a52d4a329415278a4dd49a1931325a84a1491a91e5232a451487a90a520aa40507e28f841e6a3b9474a8e451bea36946aa8d05196a319460a8bc516ea2c9456a8a94148a27d44da0965122a231443a88250fc81e543a286f50d4a195430285b50aca145426a0485
|8,1=>0x33ea6694cb21915318a61d4c1297d5
|9,0=>0x5408a7114c229445208a311442284450089f113c227444e089b1134226444c0897112c225444a089311242244448088f111c2234446088b111422244440887110c2214442088311042204440087f10fc21f443e087b10f421e443c087710ec21d443a087310e421c4438086f10dc21b4436086b10d421a44
|9,1=>0x1cc239447208e311c4238447008df11bc237446e08db11b4236446c08d711ac235446a08d311a4234446808cf119c233446608cb1194232446408c7118c231446208c31184230446008bf117c22f445e08bb117422e445c08b7116c22d445a08b3116422c445808af115c22b445608ab115422a44
|10,0=>0x8b27158e299c50389a7128e239c44388270f8e1d9c38386a70c8e179c2c38527098e119c20383a7068e0b9c1438227038e059c08380a7008dff9bfc37f26fd8df99bf037da6fa8df39be437c26f78ded9bd837aa6f48de79bcc37926f18de19bc0377a6ee8ddb9bb437626eb8dd59ba8374a6e88dcf9b9c3
|10,1=>0x2539ca439427278e4d9c98392a7248e479c8c39127218e419c8038fa71e8e3b9c7438e271b8e359c6838ca7188e2f9c5c3
|11,0=>0x4e229c05378a6e14da29b05358a6a14d229a05338a6614ca29905318a6214c2298052f8a5e14ba297052d8a5a14b2296052b8a5614aa2
|12,0=>0x2748ce819ce33986728ce41
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 15
def pmP:Nat→Nat
|0=>0x6860000c0c00010580001ff00003f600007dc0000df800013f000026e000040800008000000c3000018400003000000538000093000010000001280000230000042000008200000fc0000130000012000001400000240000040000004000000600000080000008000000
|1=>0x10010001e6fc003c9f80077bf000cb7e00186fc0030dd80055bf000a37e00116fc0022dd80041ff000837e0010128001f9f800373f0006a7e000c6fc0012df800253f000491000086fc0010050001d3f0002b7e00054fc0008df800113f000225e0001cfc00038480005bf
|2=>0x10000e016c4fc0270ff804e1bf009817e012c4fc02109d804004b008001600b54fc0168df802953f004bb7c00854fc01089f801b13f003207e00444fc00809f800f53f001c3fe00386fc006c9f800d5bf001aa7e002c4fc0050df800a13f0010a7e00214000041ff80081bf
|3=>0x20e37e041c6f80832df81051bf0208b7e04106fc08189f81027bf020491004090300811df81021bf020237e0401e2408038681005bf020037e02a56fc05189f808c7060116e7e0229238044adf808803f011001a0214efc0421ff808050d0100496020080c0400258080047
|4=>0x51011a0a016fc11a09f821d1be043237e08454fc1072df820c5bf041817e08296fc1050df82085ff0410b7e08206fc1032df82061bf04083fe08086fc10109f8201dbf040237e08016fc1000df8133fbf024ab7e044c6fc0872df810c0bf0214f9404296fc08489f81081bf
|5=>0x718bfe0e29efc1c42df8337fbf064ab7c0c396fc1870ff830e1bf0618b7e0c307fc1860df830a5bf061437e0c187fc1830df83051ff060a37e0c117fc1820ff83041bf060237e0c0449c1800ff83001bf0533b7e0a396fc146edf828c74e0518b7e0a296fc1442ff82885bf
|6=>0x7004b7ee0086fd6050dfac021bf5802b7eb0046fd6002dfa80019f3410b7e68016fcd000df980a59f301437e60254fcc010df9801dbf3003a7e60046fcc002df8d025bf1a0437e30cd6fc6098df8c0e59f1818b7e30296fc60489f8c044bf1806b7e30046fc6000df83995bf
|7=>0x78031bf981237ef02867de048cfbc0219f780233ef00067dc048dfb8085bf
|_=>0
def pmB:Nat→Nat→Nat
|7,0=>0x2000200050005000205000000000000020000090200000200040200080200000000
|8,0=>0xb1302170c4818110c0b0b210c9a10032b6706430aaa050f1216625f4c1d060b4d1228023d680c07233f641d0325480751015015240c429d0c445901051e01494f060c2256570216
|9,0=>0x24a9136344ba5eac91192c547032c83e3753b826af1434af0e4a8f51d3b54b66d1e69cd06c8479e45a999858861fc73c6961e75b75b8198829cfa5bb306ed44e35462a977e39d2c51a96b382c281e56dc6607199b7c16b61b41c851be37dc4458772a8c9c347b16a319e190d19768aca3a247f28b78d14774ac0bc9fba94
|10,0=>0xe3a2bd93cda39ba0ac19dbd71ce8c1804abe73e2913b7bcb2eab7cccb220a6bdb9696f4a1c46d183d1aee1d7a1dfe4b0a05c806f7a7ddd9693d895b33690365520a3ad2f38ad52af198c89654abfb6a041e0d6a474a7c25dced5
|11,0=>0xe24a366fda8ba8897a27453a2078ad2e789392d9deaddc8e372dc170d5
|12,0=>0xc18940253320
|13,0=>0x19
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 27 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_254 12 roots_254 ops++addP pm 1 dom_253 12 roots_253 ops++addP pm 2 dom_223 11 roots_223 ops++addP pm 3 dom_247 11 roots_247 ops++addP pm 4 dom_251 12 roots_251 ops++addP pm 5 dom_239 12 roots_239 ops++addP pm 6 dom_151 6 roots_151 ops++addP pm 7 dom_127 11 roots_127 ops++addP pm 8 dom_191 11 roots_191 ops++addP pm 9 dom_87 5 roots_87 ops++addP pm 10 dom_119 8 roots_119 ops++addP pm 11 dom_190 10 roots_190 ops++addP pm 12 dom_126 10 roots_126 ops++addP pm 13 dom_95 9 roots_95 ops++addP pm 14 dom_159 9 roots_159 ops++addP pm 15 dom_63 9 roots_63 ops++addP pm 16 dom_246 10 roots_246 ops++addP pm 17 dom_222 10 roots_222 ops++addP pm 18 dom_31 5 roots_31 ops++addP pm 19 dom_55 5 roots_55 ops++addP pm 20 dom_215 8 roots_215 ops++addP pm 21 dom_183 8 roots_183 ops++addP pm 22 dom_175 9 roots_175 ops++addP pm 23 dzo_239_16 10 roots_239 ops++addP pm 24 dom_207 9 roots_207 ops++addP pm 25 dzo_111_16 9 roots_111 ops++addP pm 26 dom_238 11 roots_238 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_255 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_223 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_247 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_127 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_191 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_175 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_zo_239_16_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_207 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_zo_111_16_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_238 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_254 12 s (0,roots_254.map (·&&&dom_254)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_254 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_255==dom_255)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_255 gM v ys):RunD true dom_255 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_255 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 7 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 35 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 35 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 72 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 72 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 126 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 126 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 90 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 90 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 29 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 29 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z12 : ∀ i, 0 ≤ i → i < 6 → Z 12 i = true := span_ok (by decide +kernel : span (Z 12) 6 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z13 : ∀ i, 0 ≤ i → i < 1 → Z 13 i = true := span_ok (by decide +kernel : span (Z 13) 1 0 = true)
theorem checked (s:Nat) (hs:s≤13):∀ i<NN s,bar dom_255 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [3, 5] }, { op := GateOp.or, inputs := [2, 1] }, { op := GateOp.or, inputs := [0, 1] }, { op := GateOp.or, inputs := [5, 6] }, { op := GateOp.or, inputs := [7, 2] }, { op := GateOp.or, inputs := [3, 9] }, { op := GateOp.or, inputs := [6, 10] }, { op := GateOp.or, inputs := [11, 7] }, { op := GateOp.or, inputs := [0, 12] }, { op := GateOp.or, inputs := [11, 4] }, { op := GateOp.and, inputs := [16, 17] }, { op := GateOp.and, inputs := [14, 8] }, { op := GateOp.and, inputs := [13, 15] }, { op := GateOp.or, inputs := [18, 19] }, { op := GateOp.or, inputs := [21, 20] }]

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 22⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
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

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_52868_aux

theorem PEqualNP.Outside.L_meta_52868 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_52868_aux.main
