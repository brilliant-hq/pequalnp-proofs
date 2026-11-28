import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_53032_aux
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
def dom_21 : Nat := 0x330033
def goal_21 : Nat := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0
def roots_21 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0]

def dom_23 : Nat := 0xff00ff
def goal_23 : Nat := 0xfefea0a0fefea0a0fefea0a0fefea0a0fefea0a0fefea0a0fefea0a0fefea0a0
def roots_23 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0]

def dom_27 : Nat := 0xf0f0f0f
def goal_27 : Nat := 0xeeeecc00eeeecc00eeeecc00eeeecc00eeeecc00eeeecc00eeeecc00eeeecc00
def roots_27 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_30 : Nat := 0x55555555
def goal_30 : Nat := 0xfcfccc00fcfccc00fcfccc00fcfccc00fcfccc00fcfccc00fcfccc00fcfccc00
def roots_30 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_31 : Nat := 0xffffffff
def goal_31 : Nat := 0xfefeeca0fefeeca0fefeeca0fefeeca0fefeeca0fefeeca0fefeeca0fefeeca0
def roots_31 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_37 : Nat := 0x3300000033
def goal_37 : Nat := 0xfafafafaa0a0a0a0fafafafaa0a0a0a0fafafafaa0a0a0a0fafafafaa0a0a0a0
def roots_37 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0]

def dom_39 : Nat := 0xff000000ff
def goal_39 : Nat := 0xfefefefea0a0a0a0fefefefea0a0a0a0fefefefea0a0a0a0fefefefea0a0a0a0
def roots_39 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0]

def dom_42 : Nat := 0x50500000505
def goal_42 : Nat := 0xffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00
def roots_42 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_43 : Nat := 0xf0f00000f0f
def goal_43 : Nat := 0xffeeffeecc00cc00ffeeffeecc00cc00ffeeffeecc00cc00ffeeffeecc00cc00
def roots_43 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_45 : Nat := 0x333300003333
def goal_45 : Nat := 0xfffafffaa0a0a0a0fffafffaa0a0a0a0fffafffaa0a0a0a0fffafffaa0a0a0a0
def roots_45 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_46 : Nat := 0x555500005555
def goal_46 : Nat := 0xfffcfffccc00cc00fffcfffccc00cc00fffcfffccc00cc00fffcfffccc00cc00
def roots_46 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_47 : Nat := 0xffff0000ffff
def goal_47 : Nat := 0xfffefffeeca0eca0fffefffeeca0eca0fffefffeeca0eca0fffefffeeca0eca0
def roots_47 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_53 : Nat := 0x33003300330033
def goal_53 : Nat := 0xfafafafafafaa0a0fafafafafafaa0a0fafafafafafaa0a0fafafafafafaa0a0
def roots_53 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xfefefefefefea0a0fefefefefefea0a0fefefefefefea0a0fefefefefefea0a0
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_57 : Nat := 0x303030303030303
def goal_57 : Nat := 0xffaaffaaaaaa0000ffaaffaaaaaa0000ffaaffaaaaaa0000ffaaffaaaaaa0000
def roots_57 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_58 : Nat := 0x505050505050505
def goal_58 : Nat := 0xffccffcccccccc00ffccffcccccccc00ffccffcccccccc00ffccffcccccccc00
def roots_58 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xffeeffeeeeeecc00ffeeffeeeeeecc00ffeeffeeeeeecc00ffeeffeeeeeecc00
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_60 : Nat := 0x1111111111111111
def goal_60 : Nat := 0xfff0fff0f0f00000fff0fff0f0f00000fff0fff0f0f00000fff0fff0f0f00000
def roots_60 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xfffafffafafaa0a0fffafffafafaa0a0fffafffafafaa0a0fffafffafafaa0a0
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_62 : Nat := 0x5555555555555555
def goal_62 : Nat := 0xfffcfffcfcfccc00fffcfffcfcfccc00fffcfffcfcfccc00fffcfffcfcfccc00
def roots_62 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfffefffefefeeca0fffefffefefeeca0fffefffefefeeca0fffefffefefeeca0
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_69 : Nat := 0x330000000000000033
def goal_69 : Nat := 0xfafafafafafafafaa0a0a0a0a0a0a0a0fafafafafafafafaa0a0a0a0a0a0a0a0
def roots_69 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 6 0]

def dom_71 : Nat := 0xff00000000000000ff
def goal_71 : Nat := 0xfefefefefefefefea0a0a0a0a0a0a0a0fefefefefefefefea0a0a0a0a0a0a0a0
def roots_71 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0]

def dom_75 : Nat := 0xf0f0000000000000f0f
def goal_75 : Nat := 0xffeeffeeffeeffeecc00cc00cc00cc00ffeeffeeffeeffeecc00cc00cc00cc00
def roots_75 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_77 : Nat := 0x33330000000000003333
def goal_77 : Nat := 0xfffafffafffafffaa0a0a0a0a0a0a0a0fffafffafffafffaa0a0a0a0a0a0a0a0
def roots_77 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_78 : Nat := 0x55550000000000005555
def goal_78 : Nat := 0xfffcfffcfffcfffccc00cc00cc00cc00fffcfffcfffcfffccc00cc00cc00cc00
def roots_78 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_79 : Nat := 0xffff000000000000ffff
def goal_79 : Nat := 0xfffefffefffefffeeca0eca0eca0eca0fffefffefffefffeeca0eca0eca0eca0
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
def goal_89 : Nat := 0xffffffaaffffffaaaaaa0000aaaa0000ffffffaaffffffaaaaaa0000aaaa0000
def roots_89 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_90 : Nat := 0x50505050000000005050505
def goal_90 : Nat := 0xffffffccffffffcccccccc00cccccc00ffffffccffffffcccccccc00cccccc00
def roots_90 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f
def goal_91 : Nat := 0xffffffeeffffffeeeeeecc00eeeecc00ffffffeeffffffeeeeeecc00eeeecc00
def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_92 : Nat := 0x111111110000000011111111
def goal_92 : Nat := 0xfffffff0fffffff0f0f00000f0f00000fffffff0fffffff0f0f00000f0f00000
def roots_92 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_93 : Nat := 0x333333330000000033333333
def goal_93 : Nat := 0xfffffffafffffffafafaa0a0fafaa0a0fffffffafffffffafafaa0a0fafaa0a0
def roots_93 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_94 : Nat := 0x555555550000000055555555
def goal_94 : Nat := 0xfffffffcfffffffcfcfccc00fcfccc00fffffffcfffffffcfcfccc00fcfccc00
def roots_94 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_95 : Nat := 0xffffffff00000000ffffffff
def goal_95 : Nat := 0xfffffffefffffffefefeeca0fefeeca0fffffffefffffffefefeeca0fefeeca0
def roots_95 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_103 : Nat := 0xff000000ff000000ff000000ff
def goal_103 : Nat := 0xfefefefefefefefefefefefea0a0a0a0fefefefefefefefefefefefea0a0a0a0
def roots_103 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_106 : Nat := 0x505000005050000050500000505
def goal_106 : Nat := 0xffccffccffccffccffccffcccc00cc00ffccffccffccffccffccffcccc00cc00
def roots_106 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffeeffeeffeeffeeffeeffeecc00cc00ffeeffeeffeeffeeffeeffeecc00cc00
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_109 : Nat := 0x3333000033330000333300003333
def goal_109 : Nat := 0xfffafffafffafffafffafffaa0a0a0a0fffafffafffafffafffafffaa0a0a0a0
def roots_109 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_110 : Nat := 0x5555000055550000555500005555
def goal_110 : Nat := 0xfffcfffcfffcfffcfffcfffccc00cc00fffcfffcfffcfffcfffcfffccc00cc00
def roots_110 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xfffefffefffefffefffefffeeca0eca0fffefffefffefffefffefffeeca0eca0
def roots_111 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_113 : Nat := 0x30003000300030003000300030003
def goal_113 : Nat := 0xffffaaaaffffaaaaaaaaaaaaaaaa0000ffffaaaaffffaaaaaaaaaaaaaaaa0000
def roots_113 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_114 : Nat := 0x50005000500050005000500050005
def goal_114 : Nat := 0xffffccccffffcccccccccccccccc0000ffffccccffffcccccccccccccccc0000
def roots_114 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def goal_115 : Nat := 0xffffeeeeffffeeeeeeeeeeeeeeee0000ffffeeeeffffeeeeeeeeeeeeeeee0000
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

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
def goal_121 : Nat := 0xffffffaaffffffaaffaaffaaaaaa0000ffffffaaffffffaaffaaffaaaaaa0000
def roots_121 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_122 : Nat := 0x5050505050505050505050505050505
def goal_122 : Nat := 0xffffffccffffffccffccffcccccccc00ffffffccffffffccffccffcccccccc00
def roots_122 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffffffeeffffffeeffeeffeeeeeecc00ffffffeeffffffeeffeeffeeeeeecc00
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_124 : Nat := 0x11111111111111111111111111111111
def goal_124 : Nat := 0xfffffff0fffffff0fff0fff0f0f00000fffffff0fffffff0fff0fff0f0f00000
def roots_124 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xfffffffafffffffafffafffafafaa0a0fffffffafffffffafffafffafafaa0a0
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_126 : Nat := 0x55555555555555555555555555555555
def goal_126 : Nat := 0xfffffffcfffffffcfffcfffcfcfccc00fffffffcfffffffcfffcfffcfcfccc00
def roots_126 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xfffffffefffffffefffefffefefeeca0fffffffefffffffefffefffefefeeca0
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_135 : Nat := 0xff000000000000000000000000000000ff
def goal_135 : Nat := 0xfefefefefefefefefefefefefefefefea0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0
def roots_135 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 7 0]

def dom_139 : Nat := 0xf0f00000000000000000000000000000f0f
def goal_139 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffeecc00cc00cc00cc00cc00cc00cc00cc00
def roots_139 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_141 : Nat := 0x333300000000000000000000000000003333
def goal_141 : Nat := 0xfffafffafffafffafffafffafffafffaa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0
def roots_141 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_142 : Nat := 0x555500000000000000000000000000005555
def goal_142 : Nat := 0xfffcfffcfffcfffcfffcfffcfffcfffccc00cc00cc00cc00cc00cc00cc00cc00
def roots_142 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_143 : Nat := 0xffff0000000000000000000000000000ffff
def goal_143 : Nat := 0xfffefffefffefffefffefffefffefffeeca0eca0eca0eca0eca0eca0eca0eca0
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
def goal_153 : Nat := 0xffffffaaffffffaaffffffaaffffffaaaaaa0000aaaa0000aaaa0000aaaa0000
def roots_153 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_154 : Nat := 0x505050500000000000000000000000005050505
def goal_154 : Nat := 0xffffffccffffffccffffffccffffffcccccccc00cccccc00cccccc00cccccc00
def roots_154 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def goal_155 : Nat := 0xffffffeeffffffeeffffffeeffffffeeeeeecc00eeeecc00eeeecc00eeeecc00
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_156 : Nat := 0x1111111100000000000000000000000011111111
def goal_156 : Nat := 0xfffffff0fffffff0fffffff0fffffff0f0f00000f0f00000f0f00000f0f00000
def roots_156 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_157 : Nat := 0x3333333300000000000000000000000033333333
def goal_157 : Nat := 0xfffffffafffffffafffffffafffffffafafaa0a0fafaa0a0fafaa0a0fafaa0a0
def roots_157 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_170 : Nat := 0x5050000050500000000000000000000050500000505
def goal_170 : Nat := 0xffccffccffccffccffccffccffccffccffccffcccc00cc00ffccffcccc00cc00
def roots_170 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_171 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
def goal_171 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffeeffeeffeecc00cc00ffeeffeecc00cc00
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_173 : Nat := 0x33330000333300000000000000000000333300003333
def goal_173 : Nat := 0xfffafffafffafffafffafffafffafffafffafffaa0a0a0a0fffafffaa0a0a0a0
def roots_173 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_177 : Nat := 0x300030003000300000000000000000003000300030003
def goal_177 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaaaaaaaaaaaaaa0000aaaaaaaaaaaa0000
def roots_177 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_179 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f
def goal_179 : Nat := 0xffffeeeeffffeeeeffffeeeeffffeeeeeeeeeeeeeeee0000eeeeeeeeeeee0000
def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_180 : Nat := 0x1100110011001100000000000000000011001100110011
def goal_180 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0f0f0f0f0f0f00000f0f0f0f0f0f00000
def roots_180 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_181 : Nat := 0x3300330033003300000000000000000033003300330033
def goal_181 : Nat := 0xfffffafafffffafafffffafafffffafafafafafafafaa0a0fafafafafafaa0a0
def roots_181 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_184 : Nat := 0x10101010101010100000000000000000101010101010101
def goal_184 : Nat := 0xffffff00ffffff00ffffff00ffffff00ff00ff0000000000ff00ff0000000000
def roots_184 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_185 : Nat := 0x30303030303030300000000000000000303030303030303
def goal_185 : Nat := 0xffffffaaffffffaaffffffaaffffffaaffaaffaaaaaa0000ffaaffaaaaaa0000
def roots_185 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_186 : Nat := 0x50505050505050500000000000000000505050505050505
def goal_186 : Nat := 0xffffffccffffffccffffffccffffffccffccffcccccccc00ffccffcccccccc00
def roots_186 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffeeffffffeeffffffeeffffffeeffeeffeeeeeecc00ffeeffeeeeeecc00
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_188 : Nat := 0x111111111111111100000000000000001111111111111111
def goal_188 : Nat := 0xfffffff0fffffff0fffffff0fffffff0fff0fff0f0f00000fff0fff0f0f00000
def roots_188 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_189 : Nat := 0x333333333333333300000000000000003333333333333333
def goal_189 : Nat := 0xfffffffafffffffafffffffafffffffafffafffafafaa0a0fffafffafafaa0a0
def roots_189 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xfffffffefffffffefffffffefffffffefffefffefefeeca0fffefffefefeeca0
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_195 : Nat := 0xf000000000000000f000000000000000f000000000000000f
def goal_195 : Nat := 0xffffffffffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0000000000000000
def roots_195 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_196 : Nat := 0x11000000000000001100000000000000110000000000000011
def goal_196 : Nat := 0xfffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000
def roots_196 : List Nat := [xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_197 : Nat := 0x33000000000000003300000000000000330000000000000033
def goal_197 : Nat := 0xfffffffffffffffffafafafafafafafafafafafafafafafaa0a0a0a0a0a0a0a0
def roots_197 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_198 : Nat := 0x55000000000000005500000000000000550000000000000055
def goal_198 : Nat := 0xfffffffffffffffffcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc0000000000000000
def roots_198 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_199 : Nat := 0xff00000000000000ff00000000000000ff00000000000000ff
def goal_199 : Nat := 0xfffffffffffffffffefefefefefefefefefefefefefefefea0a0a0a0a0a0a0a0
def roots_199 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_200 : Nat := 0x101000000000000010100000000000001010000000000000101
def goal_200 : Nat := 0xffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff000000000000000000
def roots_200 : List Nat := [xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_201 : Nat := 0x303000000000000030300000000000003030000000000000303
def goal_201 : Nat := 0xffffffffffffffffffaaffaaffaaffaaffaaffaaffaaffaa0000000000000000
def roots_201 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_202 : Nat := 0x505000000000000050500000000000005050000000000000505
def goal_202 : Nat := 0xffffffffffffffffffccffccffccffccffccffccffccffcccc00cc00cc00cc00
def roots_202 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffffffffffffffffffeeffeeffeeffeeffeeffeeffeeffeecc00cc00cc00cc00
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_204 : Nat := 0x1111000000000000111100000000000011110000000000001111
def goal_204 : Nat := 0xfffffffffffffffffff0fff0fff0fff0fff0fff0fff0fff00000000000000000
def roots_204 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_205 : Nat := 0x3333000000000000333300000000000033330000000000003333
def goal_205 : Nat := 0xfffffffffffffffffffafffafffafffafffafffafffafffaa0a0a0a0a0a0a0a0
def roots_205 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_206 : Nat := 0x5555000000000000555500000000000055550000000000005555
def goal_206 : Nat := 0xfffffffffffffffffffcfffcfffcfffcfffcfffcfffcfffccc00cc00cc00cc00
def roots_206 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_207 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def goal_207 : Nat := 0xfffffffffffffffffffefffefffefffefffefffefffefffeeca0eca0eca0eca0
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
def goal_217 : Nat := 0xffffffffffffffffffffffaaffffffaaffffffaaffffffaaaaaa0000aaaa0000
def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def goal_218 : Nat := 0xffffffffffffffffffffffccffffffccffffffccffffffcccccccc00cccccc00
def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffffffffffffffffffffeeffffffeeffffffeeffffffeeeeeecc00eeeecc00
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_220 : Nat := 0x11111111000000001111111100000000111111110000000011111111
def goal_220 : Nat := 0xfffffffffffffffffffffff0fffffff0fffffff0fffffff0f0f00000f0f00000
def roots_220 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def goal_221 : Nat := 0xfffffffffffffffffffffffafffffffafffffffafffffffafafaa0a0fafaa0a0
def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffffffffffffffffffefffffffefffffffefffffffefefeeca0fefeeca0
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_225 : Nat := 0x300000003000000030000000300000003000000030000000300000003
def goal_225 : Nat := 0xffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000
def roots_225 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def goal_227 : Nat := 0xffffffffffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee00000000
def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_228 : Nat := 0x1100000011000000110000001100000011000000110000001100000011
def goal_228 : Nat := 0xfffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000
def roots_228 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_232 : Nat := 0x10100000101000001010000010100000101000001010000010100000101
def goal_232 : Nat := 0xffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000
def roots_232 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffffffffffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa00000000
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffffffffffccffccffccffccffccffccffccffccffccffcccc00cc00
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffffffffffeeffeeffeeffeeffeeffeeffeeffeeffeeffeecc00cc00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_236 : Nat := 0x111100001111000011110000111100001111000011110000111100001111
def goal_236 : Nat := 0xfffffffffffffffffff0fff0fff0fff0fff0fff0fff0fff0fff0fff000000000
def roots_236 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xfffffffffffffffffffafffafffafffafffafffafffafffafffafffaa0a0a0a0
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffffffffffefffefffefffefffefffefffefffefffefffeeca0eca0
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

def dom_245 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
def goal_245 : Nat := 0xfffffffffffffffffffffafafffffafafffffafafffffafafafafafafafaa0a0
def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffffffffffefefffffefefffffefefffffefefefefefefefea0a0
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_248 : Nat := 0x101010101010101010101010101010101010101010101010101010101010101
def goal_248 : Nat := 0xffffffffffffffffffffff00ffffff00ffffff00ffffff00ff00ff0000000000
def roots_248 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffffffffffaaffffffaaffffffaaffffffaaffaaffaaaaaa0000
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffffffffffccffffffccffffffccffffffccffccffcccccccc00
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffffffffffeeffffffeeffffffeeffffffeeffeeffeeeeeecc00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_252 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
def goal_252 : Nat := 0xfffffffffffffffffffffff0fffffff0fffffff0fffffff0fff0fff0f0f00000
def roots_252 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffffffffffafffffffafffffffafffffffafffafffafafaa0a0
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffffffffffcfffffffcfffffffcfffffffcfffcfffcfcfccc00
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffffffffffefffffffefffffffefffffffefffefffefefeeca0
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
def isoMvS_37:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_37:Lower true dom_37 roots_37 goal_37 4:=lower_iso_b isoMvS_37 (by decide +kernel) lowS_21
def isoMvS_42:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_42:Lower true dom_42 roots_42 goal_42 4:=lower_iso_b isoMvS_42 (by decide +kernel) lowS_21
def isoMvS_69:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_69:Lower true dom_69 roots_69 goal_69 4:=lower_iso_b isoMvS_69 (by decide +kernel) lowS_21
def isoMvS_81:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_81:Lower true dom_81 roots_81 goal_81 4:=lower_iso_b isoMvS_81 (by decide +kernel) lowS_21
def isoMvS_82:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_82:Lower true dom_82 roots_82 goal_82 4:=lower_iso_b isoMvS_82 (by decide +kernel) lowS_21
def isoMvS_84:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_84:Lower true dom_84 roots_84 goal_84 4:=lower_iso_b isoMvS_84 (by decide +kernel) lowS_21
def isoMvS_146:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_146:Lower true dom_146 roots_146 goal_146 4:=lower_iso_b isoMvS_146 (by decide +kernel) lowS_21
def isoMvS_196:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_196:Lower true dom_196 roots_196 goal_196 4:=lower_iso_b isoMvS_196 (by decide +kernel) lowS_21
def isoMvS_200:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_200:Lower true dom_200 roots_200 goal_200 4:=lower_iso_b isoMvS_200 (by decide +kernel) lowS_21
def isoMvS_208:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_208:Lower true dom_208 roots_208 goal_208 4:=lower_iso_b isoMvS_208 (by decide +kernel) lowS_21
theorem lowS_23:Lower true dom_23 roots_23 goal_23 5:=lower_slice_b [(0xcc00cc,16,18)] (by decide +kernel) lowS_21
namespace S_27
def pG:List (Nat×Nat):=[(1,17),(2,10),(2,18),(3,11),(3,19),(8,10),(9,11),(9,25),(16,17),(16,18),(24,25),(24,26)]
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
theorem lowS_53:Lower true dom_53 roots_53 goal_53 5:=lower_slice_b [(0x33000000330000,1,17)] (by decide +kernel) lowS_37
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
def isoMvS_30:List (Nat×Nat):=[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_30:Lower true dom_30 roots_30 goal_30 4:=lower_iso_b isoMvS_30 (by decide +kernel) lowS_27
def isoMvS_39:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_39:Lower true dom_39 roots_39 goal_39 5:=lower_iso_b isoMvS_39 (by decide +kernel) lowS_23
def isoMvS_43:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_43:Lower true dom_43 roots_43 goal_43 5:=lower_iso_b isoMvS_43 (by decide +kernel) lowS_23
def isoMvS_45:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_45:Lower true dom_45 roots_45 goal_45 5:=lower_iso_b isoMvS_45 (by decide +kernel) lowS_23
def isoMvS_46:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_46:Lower true dom_46 roots_46 goal_46 5:=lower_iso_b isoMvS_46 (by decide +kernel) lowS_23
def isoMvS_57:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_57:Lower true dom_57 roots_57 goal_57 4:=lower_iso_b isoMvS_57 (by decide +kernel) lowS_27
def isoMvS_58:List (Nat×Nat):=[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_58:Lower true dom_58 roots_58 goal_58 5:=lower_iso_b isoMvS_58 (by decide +kernel) lowS_23
def isoMvS_60:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_60:Lower true dom_60 roots_60 goal_60 4:=lower_iso_b isoMvS_60 (by decide +kernel) lowS_27
def isoMvS_71:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_71:Lower true dom_71 roots_71 goal_71 5:=lower_iso_b isoMvS_71 (by decide +kernel) lowS_23
def isoMvS_75:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_75:Lower true dom_75 roots_75 goal_75 5:=lower_iso_b isoMvS_75 (by decide +kernel) lowS_23
def isoMvS_77:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_77:Lower true dom_77 roots_77 goal_77 5:=lower_iso_b isoMvS_77 (by decide +kernel) lowS_23
def isoMvS_78:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_78:Lower true dom_78 roots_78 goal_78 5:=lower_iso_b isoMvS_78 (by decide +kernel) lowS_23
def isoMvS_83:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_83:Lower true dom_83 roots_83 goal_83 5:=lower_iso_b isoMvS_83 (by decide +kernel) lowS_53
def isoMvS_86:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_86:Lower true dom_86 roots_86 goal_86 5:=lower_iso_b isoMvS_86 (by decide +kernel) lowS_53
def isoMvS_89:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_89:Lower true dom_89 roots_89 goal_89 5:=lower_iso_b isoMvS_89 (by decide +kernel) lowS_23
def isoMvS_90:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_90:Lower true dom_90 roots_90 goal_90 5:=lower_iso_b isoMvS_90 (by decide +kernel) lowS_53
def isoMvS_92:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_92:Lower true dom_92 roots_92 goal_92 5:=lower_iso_b isoMvS_92 (by decide +kernel) lowS_23
def isoMvS_106:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_106:Lower true dom_106 roots_106 goal_106 5:=lower_iso_b isoMvS_106 (by decide +kernel) lowS_53
def isoMvS_113:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_113:Lower true dom_113 roots_113 goal_113 5:=lower_iso_b isoMvS_113 (by decide +kernel) lowS_23
def isoMvS_114:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_114:Lower true dom_114 roots_114 goal_114 5:=lower_iso_b isoMvS_114 (by decide +kernel) lowS_23
def isoMvS_120:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_120:Lower true dom_120 roots_120 goal_120 4:=lower_iso_b isoMvS_120 (by decide +kernel) lowS_27
def isoMvS_135:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_135:Lower true dom_135 roots_135 goal_135 5:=lower_iso_b isoMvS_135 (by decide +kernel) lowS_23
def isoMvS_139:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_139:Lower true dom_139 roots_139 goal_139 5:=lower_iso_b isoMvS_139 (by decide +kernel) lowS_23
def isoMvS_141:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_141:Lower true dom_141 roots_141 goal_141 5:=lower_iso_b isoMvS_141 (by decide +kernel) lowS_23
def isoMvS_142:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_142:Lower true dom_142 roots_142 goal_142 5:=lower_iso_b isoMvS_142 (by decide +kernel) lowS_23
def isoMvS_147:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_147:Lower true dom_147 roots_147 goal_147 5:=lower_iso_b isoMvS_147 (by decide +kernel) lowS_53
def isoMvS_149:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_149:Lower true dom_149 roots_149 goal_149 7:=lower_iso_b isoMvS_149 (by decide +kernel) lowS_85
def isoMvS_150:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_150:Lower true dom_150 roots_150 goal_150 5:=lower_iso_b isoMvS_150 (by decide +kernel) lowS_53
def isoMvS_153:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_153:Lower true dom_153 roots_153 goal_153 5:=lower_iso_b isoMvS_153 (by decide +kernel) lowS_23
def isoMvS_154:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_154:Lower true dom_154 roots_154 goal_154 5:=lower_iso_b isoMvS_154 (by decide +kernel) lowS_53
def isoMvS_156:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_156:Lower true dom_156 roots_156 goal_156 5:=lower_iso_b isoMvS_156 (by decide +kernel) lowS_23
def isoMvS_170:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_170:Lower true dom_170 roots_170 goal_170 5:=lower_iso_b isoMvS_170 (by decide +kernel) lowS_53
def isoMvS_177:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_177:Lower true dom_177 roots_177 goal_177 5:=lower_iso_b isoMvS_177 (by decide +kernel) lowS_23
def isoMvS_180:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_180:Lower true dom_180 roots_180 goal_180 5:=lower_iso_b isoMvS_180 (by decide +kernel) lowS_23
def isoMvS_184:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_184:Lower true dom_184 roots_184 goal_184 4:=lower_iso_b isoMvS_184 (by decide +kernel) lowS_27
def isoMvS_195:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_195:Lower true dom_195 roots_195 goal_195 5:=lower_iso_b isoMvS_195 (by decide +kernel) lowS_53
def isoMvS_197:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_197:Lower true dom_197 roots_197 goal_197 7:=lower_iso_b isoMvS_197 (by decide +kernel) lowS_85
def isoMvS_198:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_198:Lower true dom_198 roots_198 goal_198 5:=lower_iso_b isoMvS_198 (by decide +kernel) lowS_53
def isoMvS_201:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_201:Lower true dom_201 roots_201 goal_201 5:=lower_iso_b isoMvS_201 (by decide +kernel) lowS_53
def isoMvS_202:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_202:Lower true dom_202 roots_202 goal_202 7:=lower_iso_b isoMvS_202 (by decide +kernel) lowS_85
def isoMvS_204:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_204:Lower true dom_204 roots_204 goal_204 5:=lower_iso_b isoMvS_204 (by decide +kernel) lowS_53
def isoMvS_209:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_209:Lower true dom_209 roots_209 goal_209 7:=lower_iso_b isoMvS_209 (by decide +kernel) lowS_85
def isoMvS_210:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_210:Lower true dom_210 roots_210 goal_210 7:=lower_iso_b isoMvS_210 (by decide +kernel) lowS_85
def isoMvS_212:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_212:Lower true dom_212 roots_212 goal_212 7:=lower_iso_b isoMvS_212 (by decide +kernel) lowS_85
def isoMvS_225:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_225:Lower true dom_225 roots_225 goal_225 5:=lower_iso_b isoMvS_225 (by decide +kernel) lowS_23
def isoMvS_228:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_228:Lower true dom_228 roots_228 goal_228 5:=lower_iso_b isoMvS_228 (by decide +kernel) lowS_23
def isoMvS_232:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_232:Lower true dom_232 roots_232 goal_232 5:=lower_iso_b isoMvS_232 (by decide +kernel) lowS_23
def dzo_23_8:=0xff00ff00
def gzo_23_8:=0xfe00ec00
def gsh_23_8:=0xfe00ec
theorem lowS_zo_23_8_21:Lower true dzo_23_8 roots_23 gzo_23_8 5:=lower_iso_b (d1:=dom_23) (r1:=roots_23) (T1:=gsh_23_8) [(dom_23,8)] (by decide +kernel) (lower_slice_b (T:=gsh_23_8) [(0xcc00cc,0,2)] (by decide +kernel) lowS_21)
namespace S_31
def pG:List (Nat×Nat):=[(1,5),(1,17),(2,10),(2,18),(3,7),(3,11),(3,19),(4,5),(4,20),(6,7),(6,14),(6,22),(8,10),(9,11),(9,13),(9,25),(12,13),(12,14),(12,28),(16,17),(16,18),(16,20),(24,25),(24,26),(24,28)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1ffffff
def xsM:=roots_31.map (·&&&dom_31)
def gM:=goal_31&&&dom_31
def NN:Nat→Nat
|4=>2
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x305f01ca78
|5,0=>0x7e5bd4cf0421390
|6,0=>0x510d7
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xfafafafa55550000fffff0f0f0f0f0f055555050ffff0000ff00ff00f0f0a0a0ccccccccaaaaaaaa
|_,_=>0
def sP:Nat→Nat
|0=>0x436104396104361087436104361543210
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x15405
|5,0=>0x166418a6
|6,0=>0x1c5
|_,_=>0
def wAt:=mkWire dB 10 32 0xffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x103
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x20
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 5
def pmP:Nat→Nat
|0=>0x1f41c40
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x53
|6,0=>4
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_23 5 roots_23 ops++addP pm 1 dom_30 4 roots_30 ops++addP pm 2 dzo_23_8 5 roots_23 ops++addP pm 3 dom_27 4 roots_27 ops++addP pm 4 dom_21 4 roots_21 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_31 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_23 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_30 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_23_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_21 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_23 5 s (0,roots_23.map (·&&&dom_23)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_31 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_23 h
def symsG:List (List (Nat×Nat)):=[[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_31==dom_31)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_31 gM v ys):RunD true dom_31 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_31 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_31 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_31 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_31 roots_31 goal_31 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_31
theorem lowS_31:Lower true dom_31 roots_31 goal_31 7:=S_31.noCircuit
namespace S_47
def pG:List (Nat×Nat):=[(1,5),(1,33),(2,10),(2,34),(3,7),(3,11),(3,35),(4,5),(4,36),(6,7),(6,14),(6,38),(8,10),(8,40),(9,11),(9,13),(9,41),(12,13),(12,14),(12,44),(32,33),(32,34),(32,36),(32,40)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_47.map (·&&&dom_47)
def gM:=goal_47&&&dom_47
def NN:Nat→Nat
|3=>1
|4=>4
|5=>10
|6=>4
|7=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0xa0e5
|4,0=>0x32b9c270322126c0c7bd
|5,0=>0xaa88b92cb08eb6e7a6b34ced820423128d411eb8106f001e3d
|6,0=>0xa2a8927eef227c803a9c
|7,0=>0xa2a89
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xfff00000fff0ffff0000fff0ffff0000ff003333000033000f0f00000e0effff0000aaaaffaa0000000000dd000000ccffff00000000ffee0000ccccf0f00000f0f0aaaa0000aaaaffff0000f0f0ff000000ff00fefe0000aaaacccc0000cccc
|0,1=>0x333300000000eeee0000eeee00000000eeee03030000000000ff000000000f0f00000a0a333300002222ffaa0000ffaafcfc0000fcfcfcfc00000000f0ff0000f0f0
|_,_=>0
def sP:Nat→Nat
|0=>0x1c45010e22808711404d28e2280871172021c450130711404bb4e5012c710095388a025147988a038a25010e28140471c45011a71148c388045a922280e501107308a418820
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|4,0=>0x26a3944a845
|5,0=>0x26b47682cf15b330654c918f3186
|6,0=>0xcab7dacb536
|7,0=>0x6a5
|_,_=>0
def wAt:=mkWire dB 27 48 0xffffffffffff
def SS:=mkSS wAt sP sO 5 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x3833910113913c838b3bd683389
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x5141312102
|6,0=>0x817161
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 8
def pmP:Nat→Nat
|0=>0x3ff7a9227dd506080
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x70028163
|6,0=>0x495a
|7,0=>0xa
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 6 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_46 5 roots_46 ops++addP pm 1 dom_42 4 roots_42 ops++addP pm 2 dom_39 5 roots_39 ops++addP pm 3 dom_43 5 roots_43 ops++addP pm 4 dom_45 5 roots_45 ops++addP pm 5 dom_37 4 roots_37 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_47 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_46 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_39 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_37 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_46 5 s (0,roots_46.map (·&&&dom_46)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_47 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_46 h
def symsG:List (List (Nat×Nat)):=[[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_47==dom_47)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_47 gM v ys):RunD true dom_47 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_47 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 4 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
theorem checked (s:Nat) (hs:s≤7):∀ i<NN s,bar dom_47 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤7) (h:RunD true dom_47 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_47 roots_47 goal_47 8:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_47
theorem lowS_47:Lower true dom_47 roots_47 goal_47 8:=S_47.noCircuit
theorem lowS_55:Lower true dom_55 roots_55 goal_55 6:=lower_slice_b [(0xcc00cc00cc00cc,16,18)] (by decide +kernel) lowS_53
theorem lowS_59:Lower true dom_59 roots_59 goal_59 6:=lower_slice_b [(0xa0a0a0a0a0a0a0a,16,17)] (by decide +kernel) lowS_58
def dzo_53_8:=0x3300330033003300
def gzo_53_8:=0x3300330032002000
def gsh_53_8:=0x33003300320020
theorem lowS_zo_53_8_21:Lower true dzo_53_8 roots_53 gzo_53_8 5:=lower_iso_b (d1:=dom_53) (r1:=roots_53) (T1:=gsh_53_8) [(dom_53,8)] (by decide +kernel) (lower_slice_b (T:=gsh_53_8) [(0x33003300000000,0,32)] (by decide +kernel) lowS_21)
namespace S_61
def pG:List (Nat×Nat):=[(1,5),(1,17),(1,33),(4,5),(4,20),(4,36),(8,40),(9,13),(9,25),(9,41),(12,13),(12,28),(12,44),(16,17),(16,20),(24,25),(24,28),(24,56),(32,33),(32,36),(32,40),(48,49),(48,52),(48,56)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_61.map (·&&&dom_61)
def gM:=goal_61&&&dom_61
def NN:Nat→Nat
|4=>1
|5=>1
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x40a0c
|5,0=>0xbe280
|6,0=>0xd596d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x3333000033330000c8c8c8c8c8c8c8cb333333300000000cc00cc00cc00cc030303030303030308888888888888888000323200003232
|_,_=>0
def sP:Nat→Nat
|0=>0x99a333a8c688
|_=>0
def sO:Nat→Nat→Nat
|4,0=>5
|5,0=>0x56
|6,0=>0xb5
|_,_=>0
def wAt:=mkWire dB 7 62 0x3fffffffffffffff
def SS:=mkSS wAt sP sO 3 9
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x45
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
addP pm 0 dom_53 5 roots_53 ops++addP pm 1 dom_60 4 roots_60 ops++addP pm 2 dzo_53_8 5 roots_53 ops++addP pm 3 dom_45 5 roots_45 ops++addP pm 4 dom_57 4 roots_57 ops++addP pm 5 dom_21 4 roots_21 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_61 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_53 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_60 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_53_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_21 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_53 5 s (0,roots_53.map (·&&&dom_53)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_61 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_53 h
def symsG:List (List (Nat×Nat)):=[[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_61==dom_61)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_61 gM v ys):RunD true dom_61 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_61 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
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
theorem lowS_87:Lower true dom_87 roots_87 goal_87 8:=lower_slice_b [(0xcc00cc0000000000cc00cc,16,18)] (by decide +kernel) lowS_85
namespace S_91
def pG:List (Nat×Nat):=[(1,17),(1,65),(2,10),(2,18),(2,66),(3,11),(3,19),(3,67),(8,10),(8,72),(9,11),(9,25),(9,73),(16,17),(16,18),(16,80),(24,25),(24,26),(24,88),(64,65),(64,66),(64,72),(64,80)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffff
def xsM:=roots_91.map (·&&&dom_91)
def gM:=goal_91&&&dom_91
def NN:Nat→Nat
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x9f8ac
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0000000000000f0f0000f000f00000000000f000f00c0c0c0c000000000c0c0c0ca0a0a0a000000000a0a0a0af0f0f0f0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x4688
|_=>0
def sO:Nat→Nat→Nat
|6,0=>5
|_,_=>0
def wAt:=mkWire dB 5 92 0xfffffffffffffffffffffff
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
addP pm 0 dom_90 5 roots_90 ops++addP pm 1 dom_89 5 roots_89 ops++addP pm 2 dom_83 5 roots_83 ops++addP pm 3 dom_75 5 roots_75 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_91 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_75 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_90 5 s (0,roots_90.map (·&&&dom_90)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_91 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_90 h
def symsG:List (List (Nat×Nat)):=[[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_91==dom_91)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_91 gM v ys):RunD true dom_91 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_91 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_91 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_91 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_91 roots_91 goal_91 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_91
theorem lowS_91:Lower true dom_91 roots_91 goal_91 7:=S_91.noCircuit
theorem lowS_93:Lower true dom_93 roots_93 goal_93 8:=lower_slice_b [(0x330033000000000033003300,64,72)] (by decide +kernel) lowS_85
theorem lowS_211:Lower true dom_211 roots_211 goal_211 8:=lower_slice_b [(0xa000a00000000000a000a00000000000a000a00000000000a000a,16,17)] (by decide +kernel) lowS_210
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
def isoMvS_62:List (Nat×Nat):=[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_62:Lower true dom_62 roots_62 goal_62 6:=lower_iso_b isoMvS_62 (by decide +kernel) lowS_59
def isoMvS_79:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_79:Lower true dom_79 roots_79 goal_79 8:=lower_iso_b isoMvS_79 (by decide +kernel) lowS_47
def isoMvS_94:List (Nat×Nat):=[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_94:Lower true dom_94 roots_94 goal_94 7:=lower_iso_b isoMvS_94 (by decide +kernel) lowS_91
def isoMvS_103:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)]
theorem lowS_103:Lower true dom_103 roots_103 goal_103 6:=lower_iso_b isoMvS_103 (by decide +kernel) lowS_55
def isoMvS_107:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_107:Lower true dom_107 roots_107 goal_107 6:=lower_iso_b isoMvS_107 (by decide +kernel) lowS_55
def isoMvS_109:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_109:Lower true dom_109 roots_109 goal_109 6:=lower_iso_b isoMvS_109 (by decide +kernel) lowS_55
def isoMvS_110:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_110:Lower true dom_110 roots_110 goal_110 6:=lower_iso_b isoMvS_110 (by decide +kernel) lowS_55
def isoMvS_115:List (Nat×Nat):=[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_115:Lower true dom_115 roots_115 goal_115 6:=lower_iso_b isoMvS_115 (by decide +kernel) lowS_55
def isoMvS_117:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_117:Lower true dom_117 roots_117 goal_117 8:=lower_iso_b isoMvS_117 (by decide +kernel) lowS_87
def isoMvS_118:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_118:Lower true dom_118 roots_118 goal_118 6:=lower_iso_b isoMvS_118 (by decide +kernel) lowS_55
def isoMvS_121:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_121:Lower true dom_121 roots_121 goal_121 6:=lower_iso_b isoMvS_121 (by decide +kernel) lowS_59
def isoMvS_122:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_122:Lower true dom_122 roots_122 goal_122 7:=lower_iso_b isoMvS_122 (by decide +kernel) lowS_91
def isoMvS_124:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_124:Lower true dom_124 roots_124 goal_124 6:=lower_iso_b isoMvS_124 (by decide +kernel) lowS_59
def isoMvS_143:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_143:Lower true dom_143 roots_143 goal_143 8:=lower_iso_b isoMvS_143 (by decide +kernel) lowS_47
def isoMvS_151:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_151:Lower true dom_151 roots_151 goal_151 8:=lower_iso_b isoMvS_151 (by decide +kernel) lowS_87
def isoMvS_155:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_155:Lower true dom_155 roots_155 goal_155 7:=lower_iso_b isoMvS_155 (by decide +kernel) lowS_91
def isoMvS_157:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_157:Lower true dom_157 roots_157 goal_157 8:=lower_iso_b isoMvS_157 (by decide +kernel) lowS_93
def isoMvS_171:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_171:Lower true dom_171 roots_171 goal_171 6:=lower_iso_b isoMvS_171 (by decide +kernel) lowS_55
def isoMvS_173:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_173:Lower true dom_173 roots_173 goal_173 6:=lower_iso_b isoMvS_173 (by decide +kernel) lowS_55
def isoMvS_179:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_179:Lower true dom_179 roots_179 goal_179 6:=lower_iso_b isoMvS_179 (by decide +kernel) lowS_55
def isoMvS_185:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_185:Lower true dom_185 roots_185 goal_185 6:=lower_iso_b isoMvS_185 (by decide +kernel) lowS_59
def isoMvS_186:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_186:Lower true dom_186 roots_186 goal_186 7:=lower_iso_b isoMvS_186 (by decide +kernel) lowS_91
def isoMvS_188:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_188:Lower true dom_188 roots_188 goal_188 6:=lower_iso_b isoMvS_188 (by decide +kernel) lowS_59
def isoMvS_199:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_199:Lower true dom_199 roots_199 goal_199 8:=lower_iso_b isoMvS_199 (by decide +kernel) lowS_87
def isoMvS_203:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_203:Lower true dom_203 roots_203 goal_203 8:=lower_iso_b isoMvS_203 (by decide +kernel) lowS_87
def isoMvS_205:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_205:Lower true dom_205 roots_205 goal_205 8:=lower_iso_b isoMvS_205 (by decide +kernel) lowS_87
def isoMvS_206:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_206:Lower true dom_206 roots_206 goal_206 8:=lower_iso_b isoMvS_206 (by decide +kernel) lowS_87
def isoMvS_214:List (Nat×Nat):=[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_214:Lower true dom_214 roots_214 goal_214 8:=lower_iso_b isoMvS_214 (by decide +kernel) lowS_211
def isoMvS_217:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_217:Lower true dom_217 roots_217 goal_217 8:=lower_iso_b isoMvS_217 (by decide +kernel) lowS_87
def isoMvS_218:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_218:Lower true dom_218 roots_218 goal_218 8:=lower_iso_b isoMvS_218 (by decide +kernel) lowS_211
def isoMvS_220:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_220:Lower true dom_220 roots_220 goal_220 8:=lower_iso_b isoMvS_220 (by decide +kernel) lowS_87
def isoMvS_227:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_227:Lower true dom_227 roots_227 goal_227 6:=lower_iso_b isoMvS_227 (by decide +kernel) lowS_55
def isoMvS_233:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_233:Lower true dom_233 roots_233 goal_233 6:=lower_iso_b isoMvS_233 (by decide +kernel) lowS_55
def isoMvS_234:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_234:Lower true dom_234 roots_234 goal_234 8:=lower_iso_b isoMvS_234 (by decide +kernel) lowS_87
def isoMvS_236:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_236:Lower true dom_236 roots_236 goal_236 6:=lower_iso_b isoMvS_236 (by decide +kernel) lowS_55
def isoMvS_241:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_241:Lower true dom_241 roots_241 goal_241 8:=lower_iso_b isoMvS_241 (by decide +kernel) lowS_93
def isoMvS_242:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_242:Lower true dom_242 roots_242 goal_242 8:=lower_iso_b isoMvS_242 (by decide +kernel) lowS_93
def isoMvS_244:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_244:Lower true dom_244 roots_244 goal_244 8:=lower_iso_b isoMvS_244 (by decide +kernel) lowS_93
def isoMvS_248:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_248:Lower true dom_248 roots_248 goal_248 7:=lower_iso_b isoMvS_248 (by decide +kernel) lowS_61
theorem lowS_63:Lower true dom_63 roots_63 goal_63 9:=lower_slice_b [(0xffff0000ffff0000,1,17)] (by decide +kernel) lowS_47
namespace S_95
def pG:List (Nat×Nat):=[(1,5),(1,17),(1,65),(2,10),(2,18),(2,66),(3,7),(3,11),(3,19),(3,67),(4,5),(4,20),(4,68),(6,7),(6,14),(6,22),(6,70),(8,10),(8,72),(9,11),(9,13),(9,25),(9,73),(12,13),(12,14),(12,28),(12,76),(16,17),(16,18),(16,20),(16,80),(24,25),(24,26),(24,28),(24,88),(64,65),(64,66),(64,68),(64,72),(64,80)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_95.map (·&&&dom_95)
def gM:=goal_95&&&dom_95
def NN:Nat→Nat
|6=>1
|7=>5
|8=>2
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x28a88
|7,0=>0x47df241a713325e268f01a6c5
|8,0=>0x8047773606
|9,0=>0xc3264
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffff00000000fafafafa0f0f0f0f000000000a0a0a0af0f0f0f000000000f0f0f0f0aaaaaaaa00000000aaaaaaaaffffffff0000000000000000ffff000000000000ffff0000ff00ff0000000000ff00ff00fafafafa00000000fafafafaffffffff00000000f0f0f0f0cccccccc00000000ccccccccffffffff00000000aaaaaaaa
|_,_=>0
def sP:Nat→Nat
|0=>0x54817654810765438176542810754a8176543217654a281765481796543210
|_=>0
def sO:Nat→Nat→Nat
|6,0=>6
|7,0=>0x23771d5736067
|8,0=>0xc5ea7
|9,0=>0x386
|_,_=>0
def wAt:=mkWire dB 11 96 0xffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1d98761976601765e1865c9866027661d865d9
|_=>0
def oO:Nat→Nat→Nat
|6,0=>3
|7,0=>0xb292725232
|8,0=>0xe1d1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0xfff1b7f3f7f9fc7e00
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>1
|7,0=>0x5ef4
|8,0=>0x22
|9,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 9 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_93 8 roots_93 ops++addP pm 1 dom_94 7 roots_94 ops++addP pm 2 dom_91 7 roots_91 ops++addP pm 3 dom_31 7 roots_31 ops++addP pm 4 dom_79 8 roots_79 ops++addP pm 5 dom_87 8 roots_87 ops++addP pm 6 dom_90 5 roots_90 ops++addP pm 7 dom_27 4 roots_27 ops++addP pm 8 dom_30 4 roots_30 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_95 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_79 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_30 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_93 8 s (0,roots_93.map (·&&&dom_93)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_95 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_93 h
def symsG:List (List (Nat×Nat)):=[[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_95==dom_95)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_95 gM v ys):RunD true dom_95 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_95 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 5 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 2 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_95 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_111:Lower true dom_111 roots_111 goal_111 9:=lower_slice_b [(0xffff000000000000ffff00000000,1,33)] (by decide +kernel) lowS_79
theorem lowS_119:Lower true dom_119 roots_119 goal_119 9:=lower_slice_b [(0xcc00cc00cc00cc00cc00cc00cc00cc,16,18)] (by decide +kernel) lowS_117
namespace S_123
def pG:List (Nat×Nat):=[(1,17),(1,33),(1,65),(2,10),(2,18),(2,34),(2,66),(3,11),(3,19),(3,35),(3,67),(8,10),(8,40),(8,72),(9,11),(9,25),(9,41),(9,73),(16,17),(16,18),(16,80),(24,25),(24,26),(24,56),(24,88),(32,33),(32,34),(32,40),(48,49),(48,50),(48,56),(48,112),(64,65),(64,66),(64,72),(64,80),(96,97),(96,98),(96,104),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_123.map (·&&&dom_123)
def gM:=goal_123&&&dom_123
def NN:Nat→Nat
|5=>3
|6=>5
|7=>4
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0xdea2e4ef2009085
|6,0=>0xca36c761a86878b3557719b80
|7,0=>0x7f4936900d4f9493cae4
|8,0=>0x62b5b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f0f0f0f0f0f000f000f000f00f0f0f000f0f0f000f0f0f000f0f0f00f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0cf0f0c0c0f0f0c0c0f0f0c0c0f0f0c0cf0f0f0f0f0f0f0f0f0f0f0f0f000f00a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f0e0e0e0e0e0e0e0ef0f0f0f000000000f0f0f0f00000000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0000f0f00000f0f00000e0e00000e0ef0f0f0f0f0f0f0f0000000000000000f0f0f0f0f0f0f0f0f0f0f0f00000000f0f00000f0f00000f0f00000f0f0000f000f000f000f000f000f000f000f00e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0ef0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c
|_,_=>0
def sP:Nat→Nat
|0=>0x8327a583f27a58e327a54327a583207a543217543207ad4327a58c3215b4327a543291782176543210
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x2d82b005
|6,0=>0x2b64ac79cc3117
|7,0=>0x8aef9dc3317
|8,0=>0x4c6
|_,_=>0
def wAt:=mkWire dB 16 124 0xfffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x9532615755e98561575615a74dd855e9
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x10000
|6,0=>0x7252412211
|7,0=>0xc1b1a191
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0x8a03775aba5dd14007f400c000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x40
|6,0=>0x4bd3
|7,0=>0x934
|8,0=>4
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 13 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_122 7 roots_122 ops++addP pm 1 dom_58 5 roots_58 ops++addP pm 2 dom_43 5 roots_43 ops++addP pm 3 dom_107 6 roots_107 ops++addP pm 4 dom_91 7 roots_91 ops++addP pm 5 dom_120 4 roots_120 ops++addP pm 6 dom_113 5 roots_113 ops++addP pm 7 dom_115 6 roots_115 ops++addP pm 8 dom_121 6 roots_121 ops++addP pm 9 dom_83 5 roots_83 ops++addP pm 10 dom_59 6 roots_59 ops++addP pm 11 dom_27 4 roots_27 ops++addP pm 12 dom_89 5 roots_89 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_123 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_120 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_89 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_122 7 s (0,roots_122.map (·&&&dom_122)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_123 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_122 h
def symsG:List (List (Nat×Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_123==dom_123)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_123 gM v ys):RunD true dom_123 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_123 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 5 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 4 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_123 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_123 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_123 roots_123 goal_123 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_123
theorem lowS_123:Lower true dom_123 roots_123 goal_123 9:=S_123.noCircuit
theorem lowS_125:Lower true dom_125 roots_125 goal_125 9:=lower_slice_b [(0x33003300330033003300330033003300,32,40)] (by decide +kernel) lowS_117
namespace S_207
def pG:List (Nat×Nat):=[(1,5),(1,65),(1,129),(2,10),(2,66),(2,130),(3,7),(3,11),(3,67),(3,131),(4,5),(4,68),(4,132),(6,7),(6,14),(6,70),(6,134),(8,10),(8,72),(8,136),(9,11),(9,13),(9,73),(9,137),(12,13),(12,14),(12,76),(12,140),(64,65),(64,66),(64,68),(64,72),(64,192),(128,129),(128,130),(128,132),(128,136),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffff
def xsM:=roots_207.map (·&&&dom_207)
def gM:=goal_207&&&dom_207
def NN:Nat→Nat
|4=>8
|5=>51
|6=>158
|7=>121
|8=>27
|9=>5
|10=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x762145c3ce1dbee1b5150f18c0de750c68a0973c
|5,0=>0x8e77b6b4bb693ec6611757bb755ff1519bf50e7a4cd8a4bc644519743e2243922415083b811393953900034f3033eb732349317c930f442d3d12c7ed2bf552b5842b0132810624cec238dd212cf207571fc531c9ae1b91b1b6f51a7751713b1653b12fe112a240fdc70d2bf0a05b09afc08cd50699205d59058570233c0059f
|6,0=>0x48135441a9426a04248f416a6415ef4157f4126740c45400f33e9de3d3fb3cb6a3bbc83af4e3a6183900338fe138d16381603740b369c0361ea35a67352d03518b34f7033ea833b3e326ef323ad314b23110d302f82f2312d3d12c25e2baba2b8d82b3f32ac8a2a31a2a2762910f2840427da6272cf2672f24e9423b9223a2b233152287821ab3217b82053d201511f9f01f5e41ee3e1e79c1e4f11d9111d4bb1c5541c2a41bcb31b6691b3741a138194e018b081840717a2f17a2d173be1730f1716016c54160af1550b146de13fd013ebe136c312e3512a2412a041293f11f98118061166a10a871058f0f2a60dfea0d9f70c73a0beb10be3b0b1ba0a6f00a3ff0a31509d9f0986a0982609515090bf08f8c088820828507ed50768e06cc5068ca0677b06694063410615c057d9051ca051c40433303a4d0321a0241d01871
|6,1=>0x9a2c19508f925768bfa27d1f07797c74d0373091726c96f1eb6bd3f6ab0368665680106563e64ed0637e26212361754607ea5f5855f05e5edf14f1d94dc394c7734ba9c4af26494b748378
|7,0=>0x9806a8f3c88b91f8963f8778e81ef365df2651706472b63d275fe7d5e1ae5ab415675d55c9655b71545d351cd751c104faa44ea2d4ca784beca4b81e495cf439e641a8a3e9343cb333bcb2365b6353d434f703482d3384a3221631bef319ae302f830164300572eb652e50e2df6e2ccc42c6a029888286232861a280e527dfe26e35252bc243ee2324322ae72290022849227d32263220ccd20b06205891df881da791d41f1c6741c4c81c3aa1abd21a6781a5e91a3f917ea41669316447162e515c4b1581113fc413eba13a86136eb129d1126b81228f116c3116680e61b0e1e10d3900d3780d2470d1e60c60d0bdcd0bc520a5d70a1d90a04a087000845f07a7c0779406ff806f650639c058a505288044a7039fa038400365f0322702fc202aa6023ca020a10160c00bd100bc9
|8,0=>0x8e7d660e3c5468f511ef4579840be839244379fa308422e20e2ca972bc16295f727f50210ee1d860184c715b7413c7c1071b103ff0a479086c506ecc0430f0429a02736
|9,0=>0x83b1d5bf2518802039ea0016d
|10,0=>0x83b1d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffff000000000000ffff000000000000ffff000000000000ff00ffff000000000000f0f0000000000000ffff000000000000f0f0fffc000000000000fffc000000000000fffc000000000000ccccaaaa000000000000aaaa000000000000aaaa000000000000aaaaeeee000000000000eeee000000000000eeee000000000000eeeefefe000000000000fefe000000000000fefe000000000000f0f0ffff000000000000ffff000000000000cccc000000000000ccccff00000000000000ff00000000000000ff00000000000000ff00ffaa000000000000ffaa000000000000ffaa000000000000ffaaffff000000000000ffff000000000000ffff0000000000000000ffff0000000000000000000000000000ffff0000000000000000ffff000000000000ff00000000000000ffff000000000000ff00fffa000000000000fffa000000000000fffa000000000000f0f0cccc000000000000cccc000000000000cccc000000000000ccccffff000000000000ffff000000000000ffff000000000000aaaaffff000000000000ffff00000000000000000000000000000000
|0,1=>0xfffa000000000000fffa000000000000fffa000000000000aaaa030300000000000003030000000000000303000000000000f0f0fcfc000000000000fcfc000000000000fcfc0000000000000000fcfc000000000000fcfc000000000000fcfc000000000000fcfcfffc000000000000fffc000000000000fffc000000000000ff00ffaa000000000000ffaa000000000000ffaa0000000000000000ffff000000000000aaaa000000000000ffff000000000000aaaaffff000000000000ffff000000000000ff00000000000000ff00fefe000000000000fefe000000000000fefe000000000000aaaafff0000000000000fff0000000000000fff00000000000000000ffff000000000000ffff000000000000ffff000000000000f0f0ffee000000000000ffee000000000000ffee000000000000ff00ffff000000000000cccc000000000000ffff000000000000ccccffff000000000000ffff000000000000aaaa000000000000aaaaf0f0000000000000f0f0000000000000f0f0000000000000f0f0fff0000000000000fff0000000000000fff0000000000000fff0
|0,2=>0x555500000000000055550000000000005555000000000000505000000000000000000000000000000000ffff000000000000ffaa5555000000000000555500000000000055550000000000005500eeee000000000000eeee000000000000eeee000000000000000000dd00000000000000dd00000000000000dd00000000000000ccffff000000000000aaaa000000000000cccc00000000000088880f0f0000000000000f0f0000000000000f0f0000000000000f0affff000000000000ffff000000000000f0f0000000000000f0f033330000000000003333000000000000333300000000000030300f0f0000000000000f0f0000000000000f0f0000000000000c0cf3f3000000000000f3f3000000000000f3f3000000000000f0f0cfcf000000000000cfcf000000000000cfcf000000000000cccc0a0f0000000000000a0f0000000000000a0f0000000000000a0e00ff00000000000000ff00000000000000ff00000000000000cc0a0f0000000000000a0f0000000000000a0f0000000000000a0affee000000000000ffee000000000000ffee000000000000cccc
|0,3=>0xff00000000000000ff00000000000000ff00000000000000f0bbbb000000000000bbbb000000000000bbbb000000000000aaaa33330000000000003333000000000000333300000000000000000b0b0000000000000b0b0000000000000b0b0000000000000a0a000f000000000000000f000000000000000f000000000000000033330000000000003333000000000000333300000000000033003333000000000000333300000000000033330000000000003322ffff000000000000ffff000000000000ffff000000000000cccc00000000000000000000000000000000ffff000000000000fcfc0000000000000000ffff0000000000000000000000000000fcfc555500000000000055550000000000005555000000000000444400000000000000000f0f00000000000000ff000000000000000000ff00000000000000ff00000000000000ff00000000000000ee0f0f0000000000000f0f0000000000000f0f0000000000000a0a0000000000000000ffff0000000000000000000000000000eeee3333000000000000333300000000000033330000000000002222
|0,4=>0xffff000000000000ffff000000000000fcfc000000000000fcfcffff000000000000ffff000000000000ffff000000000000fff0ffff000000000000ffff000000000000ffff000000000000eeee00000000000000000000000000000000ffff000000000000eeeeffff000000000000ffaa000000000000ffff000000000000ffaa5555000000000000555500000000000055550000000000000000dddd000000000000dddd000000000000dddd000000000000cccc1111000000000000111100000000000011110000000000000000ffff000000000000ffff000000000000ffff000000000000ffaa111100000000000011110000000000001111000000000000aaaa005500000000000000550000000000000055000000000000aaaaff0f000000000000ff0f000000000000ff0f000000000000ff000f0f0000000000000f0f0000000000000f0f00000000000000003303000000000000330300000000000033030000000000003300030300000000000003030000000000000303000000000000000000000000000000000000000000000000ffff000000000000fff0
|0,5=>0x333300000000000000000000000000003030ffff0000000000003333000000000000ffff0000000000003030ffff000000000000ffff000000000000ffff000000000000fcfc5555000000000000555500000000000055550000000000005454ffff000000000000fff0000000000000ffff000000000000fff0ff55000000000000ff55000000000000ff55000000000000ff00ffff000000000000ff00000000000000aaaa000000000000aa00ffff000000000000ffff000000000000ffaa000000000000ffaa003300000000000000330000000000000033000000000000000033330000000000003333000000000000333300000000000033300000000000000000ffff0000000000000000000000000000fff00f0f0000000000000f0f0000000000000f0f0000000000000f0000ff00000000000000ff00000000000000ff00000000000000aa000000000000000000000000000000000000000000000000ffaaffff000000000000ffff0000000000000000000000000000ffaa0055000000000000005500000000000000550000000000000000
|0,6=>0xffff000000000000eeee000000000000ffff000000000000eeee000f000000000000000f000000000000000f000000000000000affff000000000000f0f0000000000000cccc000000000000c0c0ffff000000000000ffff000000000000fff0000000000000fff0cfcf000000000000cfcf000000000000cfcf000000000000cece5055000000000000505500000000000050550000000000005050f0f0000000000000f0f0000000000000ffff000000000000fff0f0ff000000000000f0ff000000000000f0ff000000000000f0f0ffff000000000000ffff000000000000eeee000000000000eeee0000000000000000000000000000000033330000000000002222cccc000000000000cccc000000000000ffff000000000000eeee00ff00000000000000ff00000000000000ff00000000000000fc00ff00000000000000ff00000000000000f000000000000000f0ffff000000000000fcfc000000000000ffff000000000000fcfc0f0f0000000000000f0f0000000000000c0c0000000000000c0c00ff00000000000000ff00000000000000ff0000000000000000
|0,7=>0xffff0000000000000000000000000000aaaaff00000000000000ffff000000000000ff00000000000000ffaa55550000000000005555000000000000550000000000000055000000000000000000fff00000000000000000000000000000fff000000000000000000000000000000000ffff000000000000ff00aaaa000000000000aaaa000000000000ffff000000000000ffaa0f0f0000000000000f000000000000000f0f0000000000000f00ffff000000000000ffff0000000000000f0f0000000000000f0000000000000000000000000000000000ffaa000000000000ffaa0000000000000000ffff0000000000000000000000000000f0f000000000000000005555000000000000000000000000000055003333000000000000333300000000000030300000000000003030000000000000000000000000000000000f0f0000000000000c0c0f0f0000000000000f0f0000000000000f000000000000000f0000000000000000000000000000000000fcfc000000000000fcfc0000000000000000ffaa0000000000000000000000000000ffaa
|0,8=>0xfcfc0000000000000000000000000000fcfc0000000000000000000000000000000000ff00000000000000f0000000000000000000000000000000000000000000000000eeee0000000000000000ffff0000000000000000000000000000ff00ffff00000000000000ff000000000000ffff00000000000000f05555000000000000444400000000000055550000000000004444
|_,_=>0
def sP:Nat→Nat
|0=>0x192c0811200105001102122b060508110b2a0604020c21060008020c2905000828021f05080c272605000825240c0500020c2322050004020c2105000411200c000815021f0500081e020c05001b15020c050018110d0c050f0302190018150d0c05080e09170604150d0c0014111312060f0e0d0c00080a0901050403020100
|1=>0xc392905001803020c06050815090c051d080e380c1d0008030201050008373611020c0811310235000811020c063411020c3305000418020c32060811310c30000f11021f050011022f22050008280d0c0605080e021f06001411021906001b0e020c06000f28020c05161811200c06052e0811022d050f1102191a00081109
|2=>0x5081c150c27050008114c0b0212050708020c2905000811490c0548000408020c290500470811022d0500080c3a2905000f110d0c05000811024605000811024505000411021f060008150c420500080e090c06414011020c3f050428020c061608380c3c0500080c393205000428020c063b081119123a061411130c060008
|3=>0xc3005004e08110c56050010550411020c00114d020c2205000811200c060500084f020c2605000828020c5405004b11020c530500510811020c060508113102190c001028020c3f05000411020c065000084f3611130c00081102190548001811020c051a110b090c2205001811020c3f050011020c33060500472e0811020c
|4=>0x500082811025c050008020c2905000838020c3205005b400828020c050811130c0541001008020c5405005a08110212060508110219064800075a11020c05000711025905000828020c54060507181102190608020c3c053d004b580811020c06070411020106001811020c3f06051102010c33050011380c22055700081138
|5=>0x411020c06080e09020c06430811130c61064b071811020c0608362811020c064b041811020c0608113113020c0018110c3a0560000815110c3a0500081113020c5e00041811020c064a080e2838020c06082811130c063d0408020c32060008361138020c00080b021932050008020c3c060500081138025c05004e11020c3f
|6=>0x2c00080e020c1d006211020c6405001138020c330500081165090c05000811130c061d0008623711020c06041102120c06600811021706050008110b090106051113020c6405002e0f0811020c051811020c06053b2e580811020c05080e020c630608371113020c06081c130c26050040081511020c050811130c0641005807
|7=>0x690828020c0500186811020c05004b08110c3905000811200c05000811020c053b002e081102010c0511020c330500081167310219005b0811022f0500081102012d05002e041811020c05580411020c062e0811020c06051015020c3f05004b1811020c0611090c220557001811020c0605160811022f053d000811380c05
|8=>0x26d0c065b550811020c0018080e020c064308020c3c0500086b020c320500081524020c050008621c11090c0611380c22053d000868020c053b001c11380c220500186811020c0605080e110c3a0600086811026a05000809020c32060558180811021906085d3611020c0008114d020c050011020c22054300085d11025c05
|9=>0x1205100f15020c0500080e28020c06605a11020c0560004b08110219120608110c3a54050008116702190611020c2b06050011020c2622050008110217050008621c28020c060811020105500008111309010c0608371113090c050811120c39050055041811020c00100f28020c0605081113090c06430811383e0c05000811
|10=>0x380c05410008110b01300500081102010548000711020c5305001c11020c64050008110219061a00084f11025c050008116f0212066c08110c3a0500116f020c2205000868020c054300081c25020c050008116f09190c064411020c05600008020c326e05000811490219060058041811020c06081167090219062e08110219
|11=>0x20c540500087111130c0500470f0811020c05004b070811020c0600081138020c35050047580811020c0500510811020c0500100f11020c05000f1808110c3a05004b040811020c060008621c11090c050008361109020c0500040811020c064a000811023e0c053d00081102191a000815020c0516000811380c051d000811
|12=>0xc050008114d020c06050008621c28020c05000811020c350500081102190c7505000811020c05433b000f11020c060560001008150e020c050008116f02190c06000811020c5f05000811020c06053b000811023e0c0605000811026d0c05000811020c7406050811020c7305006c081511020c05000411020c720500180811
|13=>0xc05000811020c052c00085d1113020c05002e070811020c0500084f1c0e020c05004b081102191205000811670219050008113802120c060508110b380c05000811020c7805004b0811020c06007708110219050008114d02010c05000811020c054a48000811020c06051600086211020c060008110b020c054800081c7602
|14=>0x2190c0500082511020c053d00070411020c060008151113020c0600086811020c060500080e28020c06081109020c06054a08116f0b020c0600580f0811020c050018080e11020c060811020c3f050008621511020c050008020c320500070811021206050811020c2d060500085d6211020c05007c0828020c05007a081102
|15=>0x3d43000811023e0c05000811022f0605000f081102010c050008116f09190c05000f0811020c05430008281113020c0658041811020c05000811670902190500081102190c06600008110b38090c050047070811020c05001138020c220605002e0811020c05000411020c7d05000f0411020c056000081c28130c050008114c
|16=>0xf082811020c060508114d09020c05005a0811020c060500180811020c06054a084f3611020c05000811380c06053d00081c11380c06050007081102010605001808110c3a050008114d020c0500081511020c3f05000f11020c0560007e0811020c0500081167130c0500081102010c053d000811020c053b000811020c05
|17=>0x6731020c0500180811020c840500081113090c060811380c053d00081183020c0605000411020c0660000708110201050004081102010c06000811022f050008624f11020c05000411020c056000078211020c0500082511020c05000811020c8105000811020c8006001138020c2205000811020c053d41000811020c260605
|18=>0x500081102120c0605070411020c05000708110212050008116f0b020c05007b0811020c050008116f13020c0500081113020c06004b0811020c05000811020c054a00086211020c050008110902190c05000811020c7405000811020c27060500085d2811020c0500081183020c050008110219064a000811090c06053d0811
|19=>0xc050008110b020c0500081113020c050008113809020c0500081102010c05000811020c053d000f0811020c05000811020c8005000f040811020c0500081102010c0605000811020c0605430008116702120c0500081113090c05000811020c06053d00081c11020c0605000f0811020c0605000811020c7f0500088511020c
|20=>0x811020c05000811020c05000811020c06050008110212
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x23501e50195014500f500a500550005
|5,0=>0x14f61496143613d61376131612b6125611f61196113610d6107610160fb60f560ef60e960e360dd60d760d160cb60c560bf60b960b360ad60a760a1609b6095608f60896083607e50786072606d50676061605c50566050604a6044603f50396033602d60285
|6,0=>0x309730272fb72f472ee62e772e072d972d272cb72c472bd72b672af72a872a1729a7293728c7285727e72777271626a7263725c7255724e72477240723a6233722d6226721f72187211720a720371fc71f571ee71e771e071d971d271cb71c471bd71b671af71a871a1719b6194718d7186717f71787171716a7163715c71557
|6,1=>0x4c164ba74b374ac74a5749e7497749074897482747c6475746e74686461745a7453744c7445743e7437743074297422741b7414740d740673ff73f873f173ea73e463dd73d673d063c973c273bb73b473ae63a773a0739a6393738c7385737e73786371736a7363735c7355734e7347734073397332732b7324731e631773107
|6,2=>0x59065897582757b7574756d7566755f75587551754b6544753d7536752f75287521751a7513750c750574fe74f774f074e974e274db74d564ce74c77
|7,0=>0x773876c7764875c8756674e8746873e8737773077288722671b7713870b870476fd76f676ee86e686de86d686cf76c786c076b976b276ab76a3869b8693868c7684867d7675866d8666765e8656864e8646863e8637762f8627862076197612760a860375fb85f475ec85e485dc85d485cd75c675be85b685ae85a6859e85968
|7,1=>0x91f891789107909790278fa88f288ec68e578dd88d678cf78c788c168b988b278ab78a4789d7896788f7887887f8877886f8867885f8857884f8847883f8838783178298822781b7814780c880577fd87f677ef77e787df87d787d077c887c087b887b087a887a087997792778a8783777b8
|8,0=>0x9e789e079d979d279cb79c389bb89b389ab89a4799c8994898c8985797e7977797079697961895a7952894b7944793d7936792e89277
|9,0=>0xa0b6a0479fd79f679ef7
|10,0=>0xa116
|_,_=>0
def wAt:=mkWire dB 134 208 0xffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x110044018050042001021a41c18050041c180c05400150b0603015020041401021a41c18050043009190900801110043059100602045050042015021a41c180c08414011106430591006020450500420751c0601401080040859100602045050044469070603015000540859080044018050042015021644018000544415100600015020042c18000542015070601401
|1=>0x20652c034b0042065021584419050042c15020c51c474b0041c15024a4092a0c06814014711c3c3104004201905004201902164401808114140102448210d050041401113e830f50500400150c0043c0b080641401082c408150b0600015020047018000547018110541401111a41c18080c430190500444060c0642001050043059100601401110543059100601401
|2=>0x201414010222820e20206414010201808190c0641401024e860391105420011000420450838808190500408690706020310500424453811c24150428420154708d2c010819548010706c2031050053417091940801280544401084a8301a000553c170911408010b01830091900430150706020310005420010838808310905408014e08c3c45180542001084d830e1
|3=>0x1101830190005424154f05c24450111c30091900430153e11c30f50206814015d0cce045130042055081584419050057433132840815110183019050056c0304114201502268e0471300408155b00440150c068092a0c0681401085041c1a0500420311204020150c0043c470806414010c0542001050041401070041c150c08420150c06414011508c4419000542136
|4=>0x805445820806814014b00c1c010705444150828844010500588031311408151300408155b00c3801080e444f6020680015050041c01080c4441a020042447020041401020541c15080c400154f05c08a1110041031080540015080053417380c44c01020543c0b180543c0b0806414015f0544ca211004301a08004140108054441511004081900054081a110042015
|5=>0x50052c03040c420150c18420010500420154700c20050c06414011508c380111054103108054001508004088a0838824150200420011006044210500408190b06008310500444151c06008450005421360c38408190500409990919830150200408151c06008450005588031311408150806830010c1d470180211414010c0640801050042176381144c014700c1001
|6=>0x10004401508004441a113e830f50206814010111c64010c054090d0500470151102414013802c20e20206414010843814010211420e2020641401080683c0b110542019050044581080681401110183019020041401180c43015080053c154f05c24450b4842c1a050043176090e444150200410a3080540869070602031050051c030801400156705c2431020042019
|7=>0x4b00c20650c05444190806414010806844151100414010850431820806814010819430010c0540015090c414010c05408014908c09290c06814010c1d470180211414011c0540845000543019084a8301a05004301902004140102055880311134081502478104908055b0171811420011100420190500408011106808150005430f505004382402004441500055b017
|8=>0xc06800150206814010706020310c05400151106440180811414011c060440902064140102064090e1106814010201830190500430c2020183019050051c234b0041c155d08d88011c05430150706020310500408650c054300105004210e0500445051c068140102194301502004201a08434441a0500404471900430150c0683061080041401080543025020043015
|9=>0x21943015000544ca211004081508438441a0500430f5020681401090e044150200408a21100414011328c440102054a0150828444011811c2001080543c471805420011c00c0845020543c31040042015050041c15080c430e20206414015805420490c005c0010705c302104004204508054083e180542001040c414010805470151102408014f05c2445020042015
|10=>0x1300408154b00c1c15080c470011102444150819430010c05424310c05408010206430010500430090206414017900410470805420650c05400150700c20310c05408050c06414010c06814011006020450500408391105400150b068140102114a0171100408050c06414011100470150211430e20206414011819c200111068140108604201a0500444210e0044415
|11=>0x80043c2304004201502114440102055bc03021943015020681401080c4140108054441905004081511604201a05004441511004140102004301a050042c15020c40015180c460150800414011105420010815844190500438090e00444151101830190500420310c00414010f0cc201905005880113114081511004401708115ec310400c20150b060083105004e045
|12=>0x18054200109194301502004205611064140108064201a0500421fd1205c300102124300102054081a05004210e11068140102068441a0500430f50206814010c15844190500420190c064140102194301502004441a050040815110041401180c420010805424310c05408010806830150005408310905408014b0041c15083880819050052c03190843015180cc2015
|13=>0x20c42015080681401080c430190500420150c0640015150cc38011105470011c05408450f08c1001080546017080c42001113d4081a050058c15082884401130cc14010205420e20206414010206814011138808190500444010806400156705430250200421290c068140108004301a050053c17091140801020680819050040845020641401080c4301905004083e
|14=>0xc004080102054081a0500408450500420190500448170c00470170211430010500420310805420310c0042c15020c41003080544c310205414010205420650c054301a050044c450205430150200408a2110040856110641401132844401020542c1b020c414010c054301a00054081a0200414016705c08490c004603a110540801050040815020680819050042c1b
|15=>0x14010c004083102054241502004301905004081a050041001080544c3302054100108054301905004441a050040849
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x4500d40000094000006300cc003
|5,0=>0x1994000000000018cc621000000017cc00017845a415900000000533140c4b50000000000000011d0000110c000000040400000000f4c39400003630c902f300002c3000000009d4000000000000002250754000068c155
|6,0=>0x4b4d2a349cd25248511e346cd17444d1112438d0b341d10344048fd43e8cf643c90ef33ad0e830000e53388cde43708db1360cd533450ce332cc00031d0c43304cbe32e90b642c90b022b4ca94298ca42284c9d4268c982254c92323908a421908241fcc7c31e4c7721d0c7041b4c6b2
|6,1=>0x7891df376d1d74750dd13738dcb371d1c527051be36f09b846d4db326c0dac46a89a646945a14678d9a465cd943644c00063518b2000000061d0000610c000604c0005fc97c35e117445c4d6d45a5165400016145750000565155454514e35309484514d4234fcd3c34e4d3544c8d302
|6,2=>0x8e123448c122c48a4e254888e1f386d000085d00000002152848e0f382d208381c6034800dfd37e8df647c91ee40001ea47990000
|7,0=>0xbd0af13bb8eeb3ba0ee53b88edf3b70ed93b58ed33b40ecd3b28ec73b10ec13af8ebb3ae0eb53ac8eaf3ab0ea93a98ea33a80e9e2a6ce983a58a933a40e8d3a28e882a18a833a00e7d39e8e7739d0e7139b8e6b39a0e653988e5f3970e593958e533940e4d3928e473910e4138f8e3c2
|7,1=>0x3983e54f923e3cf8c3e24f872e10f813dfcb7c3de4f763dccf703db4f6a3d9cf643d84f5e3d70b593d58f533d40f4d3d28f473d10f413cf8f3b3ce0f353cc8f2f3cb4b2a3c9cf243c84f1e3c6cf192c58f133c40f0d3c28f082c14f023bfcefc3be4ef63
|8,0=>0x3cf2f34bcb2f24bc72f14bc32f04bbf2ef4bbb2ee4bb72ed4bb32ec4baf2eb4bab2ea4ba72e94ba32e84b9f2e74b9b2
|9,0=>0xf507d31f487d11
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 14
def pmP:Nat→Nat
|0=>0x2580008a000220000860002100008200020400080000120000400000d00002b0000a40002800009c00024000084000200000600000e0000300000a0000240000800001c000060000140000400000c0000200000400000
|1=>0x22000082c0020a00082600209000820002030008090020200080400200800800001400004a800122400488001100004290010800041d0010240040600100400400000a1c0020e0008200020500048800108000400000a8
|2=>0xd0e40343800d0c40342900d0640341700d00002caf0092a8024390090a801caf0052fc0143f00500001008003abc00d280033bc00caf0032b400cab00323800c8800321000c2e0030a000c2000300400c000022a400888
|3=>0x21a4408689021864084400210800841002000006caf01b2ac06ca901a0a8068020192a8064220182a00602b0180a80602901800c05caf0170bc05016014020048020120000443f0100800400000f2fc03caf00f0bc0343f
|4=>0x1002104003d0e321828caf0a32ac28ca90a2228288880a12a82840b0a02a0280a00a022c2808a0a008820cbf081228200080633bc18cce063120184c806100014c2e0433b81044004100008ebf02333808caf02201808696
|5=>0x2432a490c842422209082c2420109042c2233bc88c8e2034b880cef2032bc808c82002188002020000060eaf181a3c6028e180a246000812123c454091140a44500f11002041caf1052bc40cbf1032f440caf1010d44009d
|6=>0x200c2980001100ca8282320a04c824b09890caf
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x204000400020404
|5,0=>0xa000000041600000200210901000004020b0000000012000200000e0000020100022704000d00002000000000430b000438
|6,0=>0xc48610a02f0122684802493408321a047c94363ab142011da718060003340000c600010025000551a809105a7b44001e87000f19408908409f18013301c18534341769089d598e5f196504182e99082d181d1d02353400023337346425035c676a002b15b20491031b08c51318340109010e50171d6b293a08011b2801030e05
|6,1=>0x53391e351b1b01181300800000bb1b7a740e79a9ac513c456d5f00ae0900
|7,0=>0xbd814f2c8fad0e9c970855a4a14a30576c4cb5ab9a3498751f702ec392999e764c3b73a2af244c3f4cbf117f23b8aaad2e9607954c6672b97e3661bebcc0317d14884c474aa56e2ab7584fb356c25eaf939c5860521c18468c01b6268a4c010e6fba7fb54ea04cb8823e883d83075b030c5478715d8bb42e05
|8,0=>0x9ba44c788277a34bb09c4a4d77a24da262a684588482634c8d90b5
|9,0=>0x414ca24f82
|10,0=>0x4c
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 22 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_206 8 roots_206 ops++addP pm 1 dom_197 7 roots_197 ops++addP pm 2 dom_202 7 roots_202 ops++addP pm 3 dom_143 8 roots_143 ops++addP pm 4 dom_142 5 roots_142 ops++addP pm 5 dom_199 8 roots_199 ops++addP pm 6 dom_201 5 roots_201 ops++addP pm 7 dom_205 8 roots_205 ops++addP pm 8 dom_195 5 roots_195 ops++addP pm 9 dom_204 5 roots_204 ops++addP pm 10 dom_79 8 roots_79 ops++addP pm 11 dom_203 8 roots_203 ops++addP pm 12 dom_198 5 roots_198 ops++addP pm 13 dom_135 5 roots_135 ops++addP pm 14 dom_71 5 roots_71 ops++addP pm 15 dom_141 5 roots_141 ops++addP pm 16 dom_139 5 roots_139 ops++addP pm 17 dom_77 5 roots_77 ops++addP pm 18 dom_78 5 roots_78 ops++addP pm 19 dom_75 5 roots_75 ops++addP pm 20 dom_200 4 roots_200 ops++addP pm 21 dom_196 4 roots_196 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_207 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_197 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_143 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_142 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_201 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_195 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_204 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_79 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_198 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_135 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_71 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_141 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_78 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_200 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_196 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_206 8 s (0,roots_206.map (·&&&dom_206)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_207 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_206 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xffffffffffffffff0000000000000000,64),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)],[(0xffffffffffffffff0000000000000000,64),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_207==dom_207)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_207 gM v ys):RunD true dom_207 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_207 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 8 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 51 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 51 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 158 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 30 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 158 → Z 6 i = true := (range_split z6_0 z6_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 121 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 121 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 27 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 27 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 5 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s:Nat) (hs:s≤10):∀ i<NN s,bar dom_207 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤10) (h:RunD true dom_207 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_207 roots_207 goal_207 11:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_207
theorem lowS_207:Lower true dom_207 roots_207 goal_207 11:=S_207.noCircuit
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
|0,0=>0xff00ff0000000000fa00fa0000000000ff00f00000000000fa00f0ff00ff0000000000f000f00000000000ff00000000000000f00000aa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aaff00ff0000000000ff00ff0000000000ff00000000000000ff0000ff00ff0000000000f000f00000000000ff00ff0000000000f000f0ff00ff00000000000000000000000000ff00ff0000000000000000ff00000000000000ff00000000000000ff00000000000000ff0000ff00f00000000000ff00f00000000000ff00f00000000000ff00f0ff00ff0000000000fa00fa0000000000ff00aa0000000000fa00aacc00cc0000000000cc00cc0000000000cc00cc0000000000cc00ccff00ff0000000000ff00ff0000000000ff00ff00000000000000000000000000000000ff00ff00000000000000000000000000ff00aaf000f00000000000f000f00000000000f000f00000000000f000f0ee00ee0000000000ee00ee0000000000ee00ee0000000000ee00ee0000ff00000000000000ff00000000000000ff00000000000000aaff00ff0000000000ff00ff00000000000000000000000000000000
|0,1=>0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00f0ff00ff0000000000ff00ff0000000000ff00ff0000000000ff0000330033000000000033003300000000003300330000000000330000ff00ff0000000000ff00ff00000000000000000000000000ff00f0ff00ff0000000000ff00ff0000000000aa00aa0000000000aa00aaff00ff0000000000ff00ff0000000000ff00aa0000000000ff00aaff00ff0000000000ff00000000000000ff00ff0000000000ff0000ff00ff0000000000ff00ff0000000000ff00ff0000000000aa00aaff00ff0000000000ff00aa0000000000ff00ff0000000000ff00aa0f000f00000000000f000f00000000000f000f00000000000f000a0000000000000000ff00ff00000000000000000000000000ff00f0fc00fc0000000000fc00fc0000000000fc00fc0000000000fc00fc0000ff00000000000000ff00000000000000ff00000000000000f0ff00ff0000000000aa00aa0000000000ff00000000000000aa0000ff00ff0000000000aa00aa0000000000ff00ff0000000000aa00aaff00aa0000000000ff00aa0000000000ff00aa0000000000ff00aa
|0,2=>0x30003000000000003000300000000000300030000000000030000330033000000000033003300000000003300330000000000330030ff00000000000000ff00ff0000000000ff00000000000000ff00f00b000b00000000000b000b00000000000b000b00000000000b000abb00bb0000000000bb00bb0000000000bb00bb0000000000bb00aa55005500000000005500550000000000550055000000000055000000000000000000000000000000000000ff00ff0000000000ff00aa55005500000000005500550000000000550055000000000055005000000000000000000000ff000000000000000000000000000000aaff00ff0000000000ff00ff0000000000ff00ff0000000000ff00aaff00ff0000000000ff00f00000000000ff00ff0000000000ff00f000000000000000000000000000000000ff00ff0000000000ff00f0110011000000000011001100000000001100110000000000110000ff00ff0000000000ff00ff0000000000f000f00000000000f000f0ff00ff0000000000ff00ff0000000000ff00f00000000000ff00f0ff00ff0000000000ff00ff0000000000ff00ff0000000000f000f0
|0,3=>0x330011000000000033001100000000003300110000000000330000330033000000000033003300000000003300330000000000330022ff00ff0000000000ff00cc0000000000ee00ee0000000000ee00ccff00ff0000000000ff00000000000000f000f00000000000f00000ff00ff0000000000ff00cc0000000000fc00fc0000000000fc00ccff00ff0000000000ff00000000000000aa00aa0000000000aa0000ff00ff0000000000ff00f00000000000fa00fa0000000000fa00f0ff00f00000000000ff00f00000000000ff00f00000000000000000ff00fc0000000000ff00fc0000000000ff00fc0000000000cc00cc0f000f00000000000f000f00000000000f000f00000000000f0000000000000000000055005500000000000000000000000000550000ff00ff00000000005500550000000000ff00ff0000000000550000ff00ff00000000000000ff0000000000ff00ff00000000000000aaf300f30000000000f300f30000000000f300f30000000000f300f0510051000000000051005100000000005100510000000000510050030003000000000003000300000000000300030000000000030002
|0,4=>0xaa00aa0000000000aa00aa0000000000ff00ff0000000000ff00aa00000000000000000000000000000000ff00ff0000000000aa00aa0000000000000000ff00f000000000000000000000000000ff00f00000ff00000000000000ff00000000000000ff0000000000000000f000ff0000000000f000ff0000000000f000ff0000000000f000f00000000000000000ff00ff00000000000000000000000000ff0000ff00ff0000000000ff00aa0000000000fa00fa0000000000fa00aa00000000000000000000000000000000ff00aa0000000000ff00aaff00ff00000000000000000000000000ff00ff0000000000ff00aa00000000000000000f000f000000000000000000000000000f0000000000000000000000000000000000000f000f00000000000f0000ff00ff0000000000ff00ff00000000000f000f00000000000f00000f000f00000000000f000000000000000f000f00000000000f0000330033000000000033003300000000000300030000000000030000550055000000000055005500000000005500550000000000000000ff00550000000000ff00550000000000ff00550000000000ff0000
|0,5=>0xf000f00000000000f000f00000000000ff00ff0000000000ff00f000000000000000000000000000000000ff00ff0000000000f000f00000ff00000000000000aa00000000000000ff00000000000000aaff00ff0000000000ff00ff00000000000000ff00000000000000aaff00000000000000ff00000000000000ff00ff0000000000ff00aaaa00aa0000000000ff00ff0000000000aa00aa0000000000ff00aa0000000000000000ff00ff00000000000000000000000000aa00aaff00ff0000000000fc00fc0000000000ff00cc0000000000fc00cc00000000000000000000000000000000ff00ff0000000000ff0000000000000000000000000000000000000000ff00000000000000f00000000000000000ff00ff00000000000000000000000000f000f0550055000000000055005500000000005500000000000000550000ff00aa0000000000ff00aa0000000000ff00aa0000000000000000000000000000000000000000000000000000ff00000000000000aa000000000000000000000000000000000000000000000000ff00f0000000000000000000000000000000005500550000000000550000
|0,6=>0xff00000000000000ff00000000000000aa00000000000000aa0000ff00000000000000ff00000000000000f000000000000000f000000000000000000000ff000000000000000000000000000000f00f000f00000000000f000f00000000000f000000000000000f000000000000000000000000000000000000ff00f00000000000ff00f0550055000000000055000000000000005500550000000000550000ff00ff0000000000ff00ff00000000005500550000000000550000
|_,_=>0
def sP:Nat→Nat
|0=>0x618681145d489060828c283498514241a83a280252a24a0d0064a0b1a4c0091e18d8a32887061a984830428009168869d0a952092834289066d18a0084c94403401f283498a0040c83227401c12506851468c830460017180c10512186961400a941a4c0101e182880e182840608080
|1=>0x120d88a00241112c280091a5980a00643830c0130904585004a246af14004831ab8500323c30d00b4c941a28017060808a0030182360451a1208b0a0084c94443429e122d10d3a646030461499180c10a42646141a142090608880123560a0040c83462800906ad50a00982090608029
|2=>0x641863649209288868a20781913a00c8c0608c1b527848304286037a3451732301820a21e061a14483308c5004a24a281400809068c5000619501140063b0634529120c1051441c861400f141a4c500180db8d14544861ad8008323578a002418222d000c283498a006448304cc019
|3=>0x78609282c680802418d7e28010180c318222949e120c30d145c80c06085004224a0d0a29299185068a007848304442803224182306c0090c34b0a0020f0d5e2801f123578a00204945028009640d88a007848362280091af8b0a00241b13a2800906ad18a0040f034628019123560a
|4=>0x182c1861a14f0c120c11100251030c3620a320c30d24004b2063428a00250030ca0500120d58d0a280151824a0d1400c892888685102430d6c2800c120c6be1400b90180c31b14241ab1a74500120c6c21400c8c0618c1b1a104830c6c6853c24186226c2a12a24a0d140081e0634e8a
|5=>0x1a045090618c2a1400a9e120c30d005cf090618d8a3c2418d7c2801708241861a00f0c120c311365cf09060850010650061a01208128830d1468c830c44d802a24a221a28009282c6c61400f0c120c11b14404830ca85003e24186502801a320c11b140130906085004a844830c342a5
|6=>0x61940a00684831a745004a204941a14009292c68a00784835634500120c1010a2801a120c311361444a441868a12506931401099182c30d0068483046c28a122c18d3a14009920c30a00241861a482c7120c10a0020f0b0c342804a251061a148190618c110064483049c500180c318
|7=>0x4ca44830c345100618681140048305485002e684830428051125068514027890618d8a00250061ad8500120c6aa3a28019120c14e00206061ad85009a311061a286030c3408514402090618880320c7061a01099168830d004020906085003230a0b1a00f09288868a120c6af140048b
|8=>0x2e2418214008570608500122de061a006030c3618512506d61400f09160c69d0030494aa345254224a0d140041e0c35b0a00641861b5028906188d300984831a7450032241911a74009063570a00684831af85002030186302880c061950a007c4861ad850010651061a14c8c0608880
|9=>0x60850010791061a28609061940a008441928345001218d8d2c28019120c6a31400c8c400c30d0a94f09283450008644830c3401008641861a0081e320c31100241911af85004a906030c345103c64182140080c061ac8a4c2418d7c28009b00c68a0024186501450020781865428026
|10=>0x6188802a24a0d1401319120c10a00646030c606853e0c30d26280213c245861a00b9a120c30d0a64603043429f120c30d14013090608d8a00784830ca05003e644941a28008ae5068a00304830c36e0a132818236286090608c05147c4092834500120c11ba02805b180c30d1402d09
|11=>0x1a28009061888d0228019120c30d5428048120c10a00644830c606850068483042802118241861a1450906355231400c8c400c30d3e784941a2801e120c6a3140128c0618685120c69d4628017180c10a0068c8c0618880120d58d1400f09061889b08304830c3429e120c1110068209
|12=>0x1400415120c30d1402789061868a006448b441868034104830c3450034404830c3428a4c644830c34500be241861a2801913781861a00f090634e8a015c48b0618680120c15d1400483781868a00844a2061868514644941634025180c30d1400609280c6851424182306c5004224586
|13=>0x125068a005c4830c4468500784830c6068a009448b441868a00241861b145003c251030c3428a4a24a0b1a28029120c30d14004830c3498514004ca280c68a00644830c35b0a00784830c4468032241822200f19122c1861a004830c3700a0024a221a14510120c318362801e120c10d
|14=>0x222804d180c30d140040940186851400d090618c0d1400809061a70a0040f0c061868a00304830c36b0a00225030c3450042784830c345001824186304468a320c30dc628008322c30d016c4830c345004224a0d140040c06186851440f030c3428a005c6030c345002e241863628062
|15=>0x18241861b645090608c051400f0c122c1861a00f19120c69d1400f0906186aa1402b89060868a00404830414500120c69d140048b0c3728a0020f030c345003e241861a28026120c30d0a2800906186e414013090618c0d1400c8c440c30d1498809061868a00245830c366002030186
|16=>0x1400b89061868a003048b061868a00304830c6c68a120c3181a1450018241821a28019180c30d0a646030434500322418d3a2800906186aa1401309061888d1400494403428a0078c89280c68a0094409061868500204941a14500122c1861b185004c784830c345003c644830434500
|17=>0x1400c89061868a00204830c34500120c31b1a2801e120c30d14004830c3718a00646030c3450020641861a2801a20241861a2802112881861a2801e120c30d0a2802118241861a28010120c31114004830444500122d1061a28009061868a98004830c3730a0026f030c34500125058d
|18=>0x4830c34500120c10d
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
def wAt:=mkWire dB 103 216 0xffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x3c1b0a25002922011a2912010c3514252e030029180d12290c0d00252e031282064918441a290035120106011229182c06290025329d326e1a01142506013c1b0a2500294a03442514890c0d06013c1b3201143512290c35362936251a01124500251a290c3514010029064918441a2912350025062500291c35182c06290025
|1=>0x3512013c1b0a2500291425362900350c350ce91201326c1a0112290029002532350c35120d14013288060114250cf112013288060114251235740d326c1a011425701910140625002500296a2918470025643706753c1b320112291c35182c062912011a194c0f3c35320114250649122918441a2900250619128906011425
|2=>0x29422b180d0c0d00253c1b0a251401062918290c0d002582250a371401120122011a294c033c3532011425202912350c3500251401180d0c0d0025320d12010c0d14251a290a250c3514010c35122936291a014c0f3c3532011425182900253c533c0d320114253c1b320114250a25140106ae1a753c1b3201142518441a29
|3=>0x342918350c3500251001142106250029122d062900250c351435182912018a01328b06011425122918441a29002506753c1b0a251a753c1b0a250619422b180d0025142506010c0d00293e0f4229100106254c1b18451a29202912351a0100253c1b320114250d128601320f1425122936291a01342b36251a011a010a251435
|4=>0x1a2914251a19326e1a01302736291a010a353c370a2514011431422b180d002500351a65320114253c35320114252029342b00411a251a2918291201323532010c35142512290a0d062514014a0314210625126d1a0114250619422b128906011a011a19182900254c370a411a2500293e373c0d320114251229126d0c351a01
|5=>0x14253e37182d00250619142106250029061907310a2714011a753c1b3201142512620a350c3500291a291401126d1a01182b120d06010025402716010c0d0629180d06291201126d002900350c353c1b06290a2500297835328806011425002918441a2900250c35902900421a25120d0a25002914011625000d062922011235
|6=>0x342920011a251a1918461a2900250c35202920011a251017061906251b41326f1a0114250a0d3c0f0a2514013c3732011425220314350c3512293c0f18290025102b000d0625120130270a350029342b20011a2516300629122912011289060114250c35342b20011a25062912010c0d14251829000d0c0d120106763c1b3201
|7=>0x14250025002916330619062900253c1b182900250025442b0c0d0601100114210c0d06253c0f3201142514011837120112290a401a25143500293c1b320114253c1b3201143512293e1b3c0d320114251a2536291a0100253c37182912013c0f3c0d3201142500290601120d142514251a290c3512014c033c35320114254c27
|8=>0xcaa3c3732011425061514011201122900650619320d12294c2b326d1a011425342b00411a25320112351a2914254c1b302522014a03320d122912351a193201142512011a25146e1a014c1b3c35320114251c19182c062900253e373c0d0a253c370a2514012e0132350c351425320312350c35142506293288060114250666
|9=>0x29202920011a25140112290c3500251719182f06290025326d1a0114253e373c0d320114253c0d32010c0d14250619062532031425a40118461a2900251a191a01182b120112010a350c350029422910010625134918461a29002594350c35182b00251829120d060100253e37182d0629100106250c0d12294c0f34293625
|10=>0x3c373201142506151401120112293c0d320114250caa3201142514011029062512013c1b32011425120132350c3514251435183512013c1b320114251a011a2918290025342b1835002514311a290c350025342b18350025422b180d0c0d002536651a010c3512290a351201140114253e273c0d320114251431180d06290025
|11=>0x1425342b18350025140120011a25326d1a011425075d320314251603062914253c1b3201142506293203122912460c351a2932880601142514011289060106290c0d1425320d1229120114010c0d00250c3536291a01180d06290025302722011a293c37320114250c3500421a250a351401142518350c350025180d00250029
|12=>0x351a2910030c0d0625140122251a291a150a2514010601122d0629328b0601142506010a251401122d0c0d06292e033235142540270a0d0029182b0c0d00253c0f320114251a291829002514350c351229062932011229c201323714250029000d0c0d1a2536291a0118290c350025422b002106251b5d3203142506290601
|13=>0x142530250a351401060112011229342920011a2506290a2700291a2912350025102b120d00250a0d06250029362936251a011a2500461a29182912350025182e0629182b120d00251829180d002522011a290025180f12011229120d062914259c2500461a2910010c0d062506250025002912350a25140120291a2512012225
|14=>0x3c373201142518451a29002506190a0d0029061932011425142106250029061906250029182f00253c353201142532010c3514251201146e1a010a350c3500291829062900253c1b320114253c37320114250c35320314251a250c3500293c1b32011425128a06290601120d320114253c0d320114253c350a251401328a0601
|15=>0xc351425120d1a0132011425180f0025120112291235142520011a25128906010a251401180d002512351a2914350c35062906010a271401126e1a01160306290c0d062932351425062900251a0100250a3514010c35002514011201122912290c3500253c1b32011425
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x660018000
|5,0=>0x20d07e500007b31dd00001c946e41a540000000000000064500005f500005a5000000015cc00000005340000000139449500000001114000000000000004040f4c3850dc43250000000000000000000000c44301000000000002b5099422407901d10000194000015400001140314000
|5,1=>0x902231000000000000000000224c872
|6,0=>0x5d117045b116845911604574d59455515145351494518d4244f913b34e0d3444c112c44a4d254488d1e44691173450d10400010c442110444010fc43e10f533c50ed43a50e630000e3337d0db435d0d433410cd33250c6330ccbf42ed0b832d10b132b8caa42990a2427909a42590924
|6,1=>0x958c00094924e4929247390d24038f123848d123048b4e294898e23387d21b485d2134840e0d382520548051fd47e51f637c91ee47acde7478d1e037711d840001d44744dcd47251c547051bd46e51b546c8dae46a91a7368d1a036711993658d92463cd8b461d18345fd17c30001784
|6,2=>0xaf4eb94ad8eb33abd2ac3aa12a53a88e9e4a6ce974a50e904a312884a1128049f127849d127139b5269499526149752594
|7,0=>0xdf0f793dd8f733dc0f6d3da8f673d90f613d7cb5c3d64f563d4cf503d34f4a3d1cf443d04f3e3cecf383cd4f323cbcf2c3ca4f263c8cf203c74f1a3c5cf143c44f0e3c2cf083c14f023bfcefc3be4ef63bccef03bb4eea3b9cee43b84ede3b6ced83b54ed23b3cecc3b24ec63b0cec03
|7,1=>0x3c63f0cfc03ef4fba3edcfb43ec4fae3eb0ba93e98fa33e80f9d3e68f973e50f913e38f8b3e20f853e08f7f3
|8,0=>0xfbcbed2facbe92f9cbe52f8cbe12f7cbdd2f6cbd92f5cbd52f4cbd12f3cbcd2f2cbc92
|9,0=>0xfd07f31fc87f11
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 14
def pmP:Nat→Nat
|0=>0x4000031900228002200021400211002100020d0020c00208002010020000100000cc000c40009900084000800004c00030000200001900011000100000f0000c000090000800004000030000100000
|1=>0x19300110c010150100000f3d00f3c00f1d00e9d00e5d00e3d00e1d00e1c00cc400c3d00c1c00c0400c0300c0000a0800a0400a030093c0081100804004cc0041c00414004110040d0040c0040400401
|2=>0x893c088400849d08415084000820004e9d04e1d04c9d04840048000448c044190400003c3d0320c0300402f3d02e1d0230c0213802108020190200c020080200401f1d01e3d01c3c01b1d01b040193c
|3=>0x20edd20e5d20a1c208dc2089c20411204082000010c0d108050ce5d0cc9d0cc5d0cc510cc440cc1d0c8590c84c0c8440c8000ba150aa1d09f1d09e1d09b1d09b0c09b080983c08f3d08e3d08e1d08b1d
|4=>0x48c9d48820484004820044e1d44c1d4485d43e1d43a044320c42e1d41b1d4100440edd40e3d40e1d40cdd40c8c40c5d40b19404dd404cc402114013c40044400042ce1d2c81c2885c24e5d24e1d24e1c
|5=>0xc0c09c0a09c0200c0024a800ca4e9da0e9da089c88a3888400880d18802c8802884899844998448c82f3d82f1d82b0882a088290c8230c8211d8210c8200880e1d80c5d80b1d8021160e1d48e3d48e1d
|6=>0xe8c08e0e1de041cc8e3dc8e1dc8e0dc8c1dc8c09c8a28c8a1dc8a09c8a05c8809c8415c840dc840cc8219c820dc820cc8201c0c5d
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x20200
|5,0=>0x78090000000000080b041e001447001b3e5c00000000250076002500000b00000400002f2000002b000000000f1f4b3c12000000000000130e00000007530921520006001600063f00
|6,0=>0x9000536c704331416b0790586ca145e9e6b0931039c2964705d801f7b289d8c420c162400a95a09b55f01153a28031501012a5b8b474670114884d2341f005635154c96997d87502e77a443b66fad04a701012d0101bd1db2554f0d00bc15154f32306cb4206003000327b82004661926a786c31214bb014a01417c6db34a15
|6,1=>0x1b17a1c7214409319c446b74f7d49aa01222c3609090110830588a8
|7,0=>0xd0a1cf3589bad4717e1f1acc6aafc5c8c162443557ce353d380a9fa3a5948db01742c9048d23ad9a75397fc0c267677e65186e61c6823554a2bfcb63cd61b9abd18e61749697496170cf703b618a8573d34e8facbe44ad518a
|8,0=>0xd090a0689892cf92453b59a64d5881699b95ae91
|9,0=>0x3661374d
|10,0=>0x35
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 20 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_213 9 roots_213 ops++addP pm 1 dom_146 4 roots_146 ops++addP pm 2 dom_151 8 roots_151 ops++addP pm 3 dom_199 8 roots_199 ops++addP pm 4 dom_210 7 roots_210 ops++addP pm 5 dom_212 7 roots_212 ops++addP pm 6 dom_195 5 roots_195 ops++addP pm 7 dom_83 5 roots_83 ops++addP pm 8 dom_150 5 roots_150 ops++addP pm 9 dom_214 8 roots_214 ops++addP pm 10 dom_211 8 roots_211 ops++addP pm 11 dom_87 8 roots_87 ops++addP pm 12 dom_198 5 roots_198 ops++addP pm 13 dom_86 5 roots_86 ops++addP pm 14 dom_147 5 roots_147 ops++addP pm 15 dom_135 5 roots_135 ops++addP pm 16 dom_82 4 roots_82 ops++addP pm 17 dom_209 7 roots_209 ops++addP pm 18 dom_71 5 roots_71 ops++addP pm 19 dom_23 5 roots_23 ops
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
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_212 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_195 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_150 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_198 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_135 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_209 _ g hchk
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
namespace S_219
def pG:List (Nat×Nat):=[(1,17),(1,65),(1,129),(2,10),(2,18),(2,66),(2,130),(3,11),(3,19),(3,67),(3,131),(8,10),(8,72),(8,136),(9,11),(9,25),(9,73),(9,137),(16,17),(16,18),(16,80),(16,144),(24,25),(24,26),(24,88),(24,152),(64,65),(64,66),(64,72),(64,80),(64,192),(128,129),(128,130),(128,136),(128,144),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffff
def xsM:=roots_219.map (·&&&dom_219)
def gM:=goal_219&&&dom_219
def NN:Nat→Nat
|8=>1
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|8,0=>0xa019f
|9,0=>0x798d4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0000000000000f0f0000000000000f0f0000000000000f0f0000f000f00000000000f000f00000000000f000f00000000000f000f00c0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0ca0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0af0f0f0f000000000f0f0f0f000000000f0f0f0f0000000000000000f0f0f0f0000000000000000000000000f0f0f0f0000000000000000f0f0f0f000000000f0f0f0f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x6b191ac688
|_=>0
def sO:Nat→Nat→Nat
|8,0=>7
|9,0=>0x76
|_,_=>0
def wAt:=mkWire dB 7 220 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffff
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
addP pm 0 dom_218 8 roots_218 ops++addP pm 1 dom_155 7 roots_155 ops++addP pm 2 dom_91 7 roots_91 ops++addP pm 3 dom_217 8 roots_217 ops++addP pm 4 dom_211 8 roots_211 ops++addP pm 5 dom_203 8 roots_203 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_219 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_203 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_218 8 s (0,roots_218.map (·&&&dom_218)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_219 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_218 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xffffffffffffffff0000000000000000,64),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_219==dom_219)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_219 gM v ys):RunD true dom_219 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_219 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_219 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_219 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_219 roots_219 goal_219 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_219
theorem lowS_219:Lower true dom_219 roots_219 goal_219 10:=S_219.noCircuit
theorem lowS_221:Lower true dom_221 roots_221 goal_221 10:=lower_slice_b [(0x33003300000000003300330000000000330033000000000033003300,64,72)] (by decide +kernel) lowS_213
theorem lowS_243:Lower true dom_243 roots_243 goal_243 9:=lower_slice_b [(0xa000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a,16,17)] (by decide +kernel) lowS_242
def dzo_216_32:=0x101010100000000010101010000000001010101000000000101010100000000
def gzo_216_32:=0x101010100000000010101000000000001010100000000000100010000000000
def gsh_216_32:=0x1010101000000000101010000000000010101000000000001000100
theorem lowS_zo_216_32_208:Lower true dzo_216_32 roots_216 gzo_216_32 5:=lower_iso_b (d1:=dom_216) (r1:=roots_216) (T1:=gsh_216_32) [(dom_216,32)] (by decide +kernel) (lower_slice_b (T:=gsh_216_32) [(0x1000100000000000100010000000000010001000000000001000100,0,8)] (by decide +kernel) lowS_208)
def dzo_218_32:=0x505050500000000050505050000000005050505000000000505050500000000
def gzo_218_32:=0x505050500000000050505040000000005050504000000000504050400000000
def gsh_218_32:=0x5050505000000000505050400000000050505040000000005040504
theorem lowS_zo_218_32_208:Lower true dzo_218_32 roots_218 gzo_218_32 6:=lower_iso_b (d1:=dom_218) (r1:=roots_218) (T1:=gsh_218_32) [(dom_218,32)] (by decide +kernel) (lower_slice_b (T:=gsh_218_32) [(0x4040404000000000404040400000000040404040000000004040404,0,2),(0x5000500000000000500050000000000050005000000000005000500,0,8)] (by decide +kernel) lowS_208)
namespace S_250
def pG:List (Nat×Nat):=[(2,10),(2,18),(2,34),(2,66),(2,130),(8,10),(8,40),(8,72),(8,136),(16,18),(16,80),(16,144),(24,26),(24,56),(24,88),(24,152),(32,34),(32,40),(48,50),(48,56),(48,112),(48,176),(64,66),(64,72),(64,80),(64,192),(96,98),(96,104),(96,112),(96,224),(128,130),(128,136),(128,144),(128,192),(160,162),(160,168),(160,176),(160,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffff
def xsM:=roots_250.map (·&&&dom_250)
def gM:=goal_250&&&dom_250
def NN:Nat→Nat
|5=>2
|6=>8
|7=>9
|8=>3
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0xc3aa53abdf
|6,0=>0xe7ff1c50cba90be77f4867bbd664d91c99a1460d
|7,0=>0xfd7b9f09c5c39e79eaf99c49434d60257c52224f0a1a7
|8,0=>0x9d4154679b22d09
|9,0=>0xef2e1
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xa0a0a0a0a0a0a0a00000000000000000a0a0a0a0000000141414141414141414141414000000001414141414141414141414140000000000000000000000000000000000000002828282828282828282828280000000505050505050505050505050505050505050505050505050404040404040404a0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0a0000000141414141414141414141414141414141414141414141414000000000000000282828282828282828282828282828280000000000000000000000000000000505050505050505050505050505050505050505050505050505050500000000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a000141414141414141410101010101010101414141414141414101010101010101282828282828282828282828282828282828282800000000282828280000000500050005000500050005000500050005000500050005000500050005000500a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0808080808080808080808080808080901010101010101010101010101010101010101010101010101010101010101000028280000282800002828000028280000282800002828000020200000202505050505050505000000000000000005050505050505050000000000000000
|0,1=>0x5050505050505050404040404040404
|_,_=>0
def sP:Nat→Nat
|0=>0x390404ace430c0959c8c101253906202ce4618404ace43094959c901012e39062025072080979c82025672186a29c8c1880d390c24a0e43092b23041025641040929c8618164308204a0e430ca418820
|1=>0xb390404ace43080959c8250125
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x65006
|6,0=>0x3863172b62561e71861260b7
|7,0=>0x7476d76765f85875174a74463e6
|8,0=>0x8878177b6
|9,0=>0x8f6
|_,_=>0
def wAt:=mkWire dB 17 251 0x7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1010255a51251011290251255a53251011014813271011255812815a52835a50251251015a51811251017275815a91014811290253b21290255a51251013b23251255a9101481
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x1000
|6,0=>0x5cd4344ce33089318c42
|7,0=>0x2a2a0a6290a22809e2709a2
|8,0=>0x2e1b46c1
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 10
def pmP:Nat→Nat
|0=>0xf39f94f4c5673b29b94d0a07fb3eb9f4ceb66533088fec6ae2df020003c004000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x40
|6,0=>0x734a419cc1
|7,0=>0x109b2327ad49
|8,0=>0x3dc9
|9,0=>8
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 13 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_242 8 roots_242 ops++addP pm 1 dom_248 7 roots_248 ops++addP pm 2 dom_154 5 roots_154 ops++addP pm 3 dom_90 5 roots_90 ops++addP pm 4 dom_186 7 roots_186 ops++addP pm 5 dom_120 4 roots_120 ops++addP pm 6 dom_234 8 roots_234 ops++addP pm 7 dzo_216_32 5 roots_216 ops++addP pm 8 dzo_218_32 6 roots_218 ops++addP pm 9 dom_122 7 roots_122 ops++addP pm 10 dom_218 8 roots_218 ops++addP pm 11 dom_58 5 roots_58 ops++addP pm 12 dom_184 4 roots_184 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_250 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_120 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_216_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_218_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_184 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_242 8 s (0,roots_242.map (·&&&dom_242)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_250 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_242 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_250==dom_250)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_250 gM v ys):RunD true dom_250 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_250 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 2 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 8 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 9 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 3 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_250 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def isoMvS_126:List (Nat×Nat):=[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_126:Lower true dom_126 roots_126 goal_126 9:=lower_iso_b isoMvS_126 (by decide +kernel) lowS_123
def isoMvS_187:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_187:Lower true dom_187 roots_187 goal_187 9:=lower_iso_b isoMvS_187 (by decide +kernel) lowS_123
def isoMvS_189:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_189:Lower true dom_189 roots_189 goal_189 9:=lower_iso_b isoMvS_189 (by decide +kernel) lowS_125
def isoMvS_235:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_235:Lower true dom_235 roots_235 goal_235 9:=lower_iso_b isoMvS_235 (by decide +kernel) lowS_119
def isoMvS_237:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_237:Lower true dom_237 roots_237 goal_237 9:=lower_iso_b isoMvS_237 (by decide +kernel) lowS_119
def isoMvS_245:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_245:Lower true dom_245 roots_245 goal_245 10:=lower_iso_b isoMvS_245 (by decide +kernel) lowS_221
def isoMvS_249:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_249:Lower true dom_249 roots_249 goal_249 9:=lower_iso_b isoMvS_249 (by decide +kernel) lowS_125
def isoMvS_252:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccccccccccccccccccccccccccc,126),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_252:Lower true dom_252 roots_252 goal_252 9:=lower_iso_b isoMvS_252 (by decide +kernel) lowS_125
def dzo_119_8:=0xff00ff00ff00ff00ff00ff00ff00ff00
def gzo_119_8:=0xff00ff00ff00ff00ff00ff00fe00ec00
def gsh_119_8:=0xff00ff00ff00ff00ff00ff00fe00ec
theorem lowS_zo_119_8_21:Lower true dzo_119_8 roots_119 gzo_119_8 7:=lower_iso_b (d1:=dom_119) (r1:=roots_119) (T1:=gsh_119_8) [(dom_119,8)] (by decide +kernel) (lower_slice_b (T:=gsh_119_8) [(0xcc00cc00cc00cc00cc00cc00cc00cc,0,2),(0xff00ff0000000000ff00ff00000000,0,32),(0xff00ff00ff00ff0000000000000000,0,64)] (by decide +kernel) lowS_21)
def dzo_55_8:=0xff00ff00ff00ff00
def gzo_55_8:=0xff00ff00fe00ec00
def gsh_55_8:=0xff00ff00fe00ec
theorem lowS_zo_55_8_21:Lower true dzo_55_8 roots_55 gzo_55_8 6:=lower_iso_b (d1:=dom_55) (r1:=roots_55) (T1:=gsh_55_8) [(dom_55,8)] (by decide +kernel) (lower_slice_b (T:=gsh_55_8) [(0xcc00cc00cc00cc,0,2),(0xff00ff00000000,0,32)] (by decide +kernel) lowS_21)
def dzo_117_8:=0x33003300330033003300330033003300
def gzo_117_8:=0x33003300330033003300330032002000
def gsh_117_8:=0x330033003300330033003300320020
theorem lowS_zo_117_8_21:Lower true dzo_117_8 roots_117 gzo_117_8 6:=lower_iso_b (d1:=dom_117) (r1:=roots_117) (T1:=gsh_117_8) [(dom_117,8)] (by decide +kernel) (lower_slice_b (T:=gsh_117_8) [(0x330033000000000033003300000000,0,32),(0x330033003300330000000000000000,0,64)] (by decide +kernel) lowS_21)
namespace S_127
def pG:List (Nat×Nat):=[(1,5),(1,17),(1,33),(1,65),(2,10),(2,18),(2,34),(2,66),(3,7),(3,11),(3,19),(3,35),(3,67),(4,5),(4,20),(4,36),(4,68),(6,7),(6,14),(6,22),(6,38),(6,70),(8,10),(8,40),(8,72),(9,11),(9,13),(9,25),(9,41),(9,73),(12,13),(12,14),(12,28),(12,44),(12,76),(16,17),(16,18),(16,20),(16,80),(24,25),(24,26),(24,28),(24,56),(24,88),(32,33),(32,34),(32,36),(32,40),(48,49),(48,50),(48,52),(48,56),(48,112),(64,65),(64,66),(64,68),(64,72),(64,80),(96,97),(96,98),(96,100),(96,104),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffffffffffffff
def xsM:=roots_127.map (·&&&dom_127)
def gM:=goal_127&&&dom_127
def NN:Nat→Nat
|5=>6
|6=>45
|7=>106
|8=>129
|9=>61
|10=>10
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0xb1f97728df717904f5e306d2e0652c
|6,0=>0xd889bd5b4cd5339d3b80cddbaa09f99d7c89a8a596f41913368e8c47c6367286861f12610e85eecf53708524cb516a14f57c4be094b353438813cbe4343e333d81339462c48225bcc2022d1ee501d8b81cc3719716167711569415357148ad14431140bc0ee6209c160935e037bb0047a
|7,0=>0xffc2cf3684efe56dc274d9196d8f19d3a1fccc38c73e2c1c36c122ac0f30bfb6bb181eaf56aadf37ab097a604aa38e1a2a8ca089e9ac6a932749303d917e99019c8c49087f47852508424f7f7a37bd907a0ec75dac757506e1436d5ff6d0136b5d66a7b4688f0683385f287565f0545894ffaa4f24d4ef004e06b4a6e047f1f45743439394391d40e733b0f738ac63729c36f40367783543034bbf3390531d653185b312a9311132f8c72c6372c4392918d27e73272ec2654a2651e25faf237502311522c1b21d38206612016f1fb1f1ed641ea301cb121a83e19dc517a391731912e7111bd0114df114c30f41b0eed00e08f0bc3107bbe0753d0666e04a0b0487a024cc01a370146e
|8,0=>0xf6acff3a3fef186dc870da688d8292d5175d3421cfdd3cfb20ce1cec56a2c4f7fc2af1c26b0be81cb7619b4a8cb169fa6eafa5675a1026a07759e7239c5c099ad9953368cb098ae4c89deb871da852ec851c6851568390a823fb7beb679ff279ecc777937698475be9741b270b556e18c6c1e46b77167f5b6767f65522655066491e62494619b35d9915bb1855ecf54c56547ff52eae52e9252b6a5023b4eaf74e0224de9f48d14442d341bcf4123d410bf40c043e9eb3cf8a3ce343b9ae3af5c3ac8e3a82d395cf3813d374df3474333f3f3354732a202fc2a2cf5c2be512b6a52aa4f29d592999e2940626a53265f425b9f23057220eb1d8c61a921172d015a13157721526d1052610389100a20e7a40dca90bc9f0870f07b1a071ff06a5205c3605b250428b036050343d032fb02bf9023b802005013530100900ee3000d0
|8,1=>0xffdec
|9,0=>0xf96b8e9e82e9b32e5e72d2632cdf0fc9b06bb6c2b9cdbb2c55afb5ba904ea8842a5099a39939987d92afc917868c01e8b85885b427f23979a8474789719096b1ed69a565c7525bce154f2646b3244cca42e873e88c3e2c43e0063cb5b375fc3549130394292d4291b81fc3a1b6f51914a18d211685b1643f1285f10fcf101700f9760ce710b65c0a79209fe006e0805b690414303dcb01b47
|10,0=>0xf90dcf69edbbe948f8cb6c3bf581863fcd23da333b65b2fbbe
|11,0=>0x2654f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xfafafafafafafafafafafafafafafafaffffffffffffffffffffffff00000000ffffffff00000000ffffffff00000000fefefefefefefefefefefefefefefefef0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ccccccccccccccccccccccccccccccccfffffffffffffffffffffffff0f0f0f0fcfcfcfcfcfcfcfcfcfcfcfca8a8a8a8ffffffffffffffffccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffffffffffffaaaaaaaaffff0000ffff0000ffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00fcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfceeeeeeeeeeeeeeeeeeeeeeeee0e0e0e0ffffffffffffffff0000000000000000
|0,1=>0xfffffffffffffffffcfcfcfcfcfcfcfcaaaaaaaaaaaaaaaaaaaaaaaafefefefeffffffffffffffffeeeeeeeeeeeeeeee0000ffff0000ffff0000fefe0000fefe0f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a00cf00cf00cf00cf00cf00cf00ce00cefffffffffffffffff0f0f0f0f0f0f0f000ff00ff00ff00ff00ff00ff00ee00ee0000000000000000fffffffffefefefe5555555555555555505050505050505000ff00ff00ff00ff00ff00ff00cc00ccffffffffffffffff000000000e0e0e0efffffffffffffffffcfcfcfca8a8a8a8eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeffffffffffffffffaaaaaaaaaaaaaaaa00dd00dd00dd00dd00dd00dd00dc00dc
|0,2=>0x3030303030303030303030302020202f3f3f3f3f3f3f3f3f3f3f3f3f2f2f2f2333333333333333333333333323232320000ffff0000ffff0000ffff0000fefeffffffffffffffffffffffffcccccccc0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a5555555555555555555555555050505055555555555555555555555554545454ffffffffffffffffff00ff00ff00ff00ffffffffffffffff00000000eeeeeeeefffffffffffffffff0f0f0f0fefefefe000000000000000000000000fcfcfcfcdddddddddddddddddddddddddcdcdcdc54545454545454545454545454545454ffffffffffffffffffffffffeeeeeeeefffffffffffffffffefefefefefefefe
|0,3=>0xdddddddddddddddddcdcdcdcdcdcdcdcffffffffffffffffffffffffff00ff00fffafffafffafffafffafffafffafffafffffffffffffffffff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff055555555555555555550555055505550ff55ff55ff55ff55ff50ff50ff50ff5055555555555555555500550055005500f5f5f5f5f5f5f5f5f5f0f5f0f5f0f5f00e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0efffffffffffffffffafafafafafafafaffffffffffffffff00000000fefefefeffffffffffffffffeeeeeeeee0e0e0e000ff00ff00ff00ff00ff00ff00fe00fe555554545555545455555454555554540f0f0e0e0f0f0e0e0f0f0e0e0f0f0e0e
|0,4=>0xffffaaaaffffaaaaffffaaaaffffaaaa000000000000000000000000545454540f0f0f0f0f0f0f0f0f0f0f0f0e0e0e0e000000000000000000000000eeeeeeeefffffffffffffffffffffffffefefefe33333333333333333333333330303030fffffffffffffffffffafffafffafffa55555555555555555454545454545454ffffeeeeffffeeeeffffeeeeffffeeeecfcfcfcfcfcfcfcfcfcfcfcfcecececefffffefefffffefefffffefefffffefefffff0f0fffff0f0fffff0f0fffff0f0fffffcfcfffffcfcfffffcfcfffffcfcffffccccffffccccffffccccffffcccc55505550555055505550555055505550ffffffffffffffff5550555055505550
|0,5=>0xffffff00ffffff00ffffff00ffffff00555555005555550055555500555555000000000000000000eeeeeeeeeeeeeeeef0f0f0f0f0f0f0f0fefefefefefefefe33333333333333333030303030303030fffffffffffffffffffffffffcfcfcfccfcfcececfcfcececfcfcececfcfcece0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0affffffffffffffffffffffff0e0e0e0e000000000000000000000000fefefefe05050505050505050500050005000500ffffffffffffffff0e0e0e0e0e0e0e0e33333333333333333333333322222222fffffffffffffffffffffffffafafafaffaaffaaffaaffaaffaaffaaffaaffaa0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a
|0,6=>0x555544445555444455554444555544440000000000000000fefefefefefefefeffffffffffffffffffaaffaaffaaffaa0f0f0f0f0f0f0f0f0f0a0f0a0f0a0f0a55555050555550505555505055555050ff55ff50ff55ff50ff55ff50ff55ff50ff0fff0fff0fff0fff0aff0aff0aff0acfcfcfcfcfcfcfcfcecececececececeffffffffffffffff54545454545454540000fcfc0000fcfc0000fcfc0000fcfcaaaafefeaaaafefeaaaafefeaaaafefefffffff0fffffff0fffffff0fffffff0555555505555555055555550555555500f0f0f0f0f0f0f0f0f000f000f000f00afafafafafafafafafaaafaaafaaafaaffffffffffffffff0f0a0f0a0f0a0f0a
|0,7=>0xff00f000ff00f000ff00f000ff00f005050500050505000505050005050500ffff5454ffff5454ffff5454ffff54540f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a050504040505040405050404050504040000fefe0000fefe0000fefe0000fefe000000000000000054545454545454540f0f0f000f0f0f000f0f0f000f0f0f00afafafaaafafafaaafafafaaafafafaa00ff00ff00ff00ff00aa00aa00aa00aa00000e0e00000e0e00000e0e00000e0effffffaaffffffaaffffffaaffffffaafffffffafffffffafffffffafffffffaffff0f0affff0f0affff0f0affff0f0a0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0cafafaeaeafafaeaeafafaeaeafafaeae
|0,8=>0xfffffafafffffafafffffafafffffafa333333333333333322222222222222223333303033333030333330303333303000ff00ff00ff00ff00f000f000f000f00000000000000000ffaaffaaffaaffaa0000ffaa0000ffaa0000ffaa0000ffaa
|_,_=>0
def sP:Nat→Nat
|0=>0x6090e04030c0706090504030212000e03200b0a061c050e04031f0b120e04030b0a1e110e030b1d0a061c0e04030207061b0e040b0a061a000e04190b0a0618090403080a0600170e04030b0a060e040b0a0616150e04030b0a06140e04030201110e0403130b120e040b0a1110090504030c07090403080706050403020100
|1=>0xa062f2b0e04031906222b0e04030c19060e04032e0b0706090504030c0a000e04030b07062d0e030b0a062c002b0e040302062a0e04030b1d0a29050e04030219120e04030b0a112809050427030f0a0e040308190a060e0403250b0a060e04030b1211240e04030b230a110e040b12070618090e0403070622210e04030219
|2=>0xb0a110e0403370b0a06090504030b120a00090e0427030f0a060e04030b0a11360e04350b0a06150e04030b0a0634090504030f070a0e0403020106000e04030b330a060e04030b07062f0e040b0a0632000e040f190a06150e0403020b0626090504030207060d04030a313000050e04030c190a0e0403080b07060e040319
|3=>0xa06400e043b0b0a06380e040b0a1106150e04030c0b0a11210e04030b1207060e0403020a061b000e04030b3f0a063e0e04030b0a062a0e043d03190a060e04030c19120a060e04030b0a063a2b0e0403190b12060e0439030b0a060e040b0a061800050e040b0a0618000e04031f020b1206210e0403190b0a062b0e04030f
|4=>0x50e0403190b120a0d04030c190a110d04030c0a0630000e0403200c0b0a062b0e04030219060e04030b460a0600050e04030b12070e04030c0b1d0a060e0403200b1d0a060e040b120a0618002b0e0403350b0a06090e04030a0622000d4304030a0630000e04030b070636090e04030c0a06000d420403020630000e04030b
|5=>0x30b0a064e000d043d03190a110d04030c19120a11050e04030f0b070a0e04030b0a06260e04030c0b07060e04030b0a064d000e04030b0a1e06000e0403190b0a064c0d03020b0a061c002b0e04030b0a062a0d4504030b0a31004b0e04030b0a06000e04030b07064a0e04030c0b120a110e0449030b0a060e04030b0a0648
|6=>0xe04030b120a162b0e04031f020b060d030c0b0a061c00090e04030f0a110d03200b0a061c000d030b1d0a061c00520e04030b070a06210e0403020b06000e04032e0b0a06000e04030b0a062d000e04030c0b1207060d04030b120a31000e0427030b0a06290e04030b120624000e04270b0a06500d444f030c020a000e04
|7=>0x4030b0a062f000e043d270b0a062b0e04030c0b06000d444f030212000e0403200b120a060e04031f0b12060d47040302063000050e04031f0b0a060e04030b0a11064a2b0e04030b063600050e0403020b12000e04030b0a0655210e040b0a0618000e0403200b0a06090504030b070a060e04030b0a06540e0403080b0a06
|8=>0x3021912110e04030b070a06290e040f0b0a06150009050427030b0a060e04030b0a11500d444f030c0a00090e04030b120706520e0427030b0a063e0e04030f190a060e0403021912060d030b0a061c00090504030f0a00570e04030b0a06000e04030b0a065600090e04030b120a110d0403020b1231000e0403190a061b0e
|9=>0xb0a06000e04030b0a065b0d440403021206000d4f04030c0b120a005a090e04030b0a06003e0e04030f0b0a0600210e04030b0a06000d043b03190a11060e0403020b1206000d04030b590a06000d4204030b0622000d043b030a0658000d04030c020b0706000e0403020b0706050e0427030b0a063e0e0403350b0a060d04
|10=>0xd4504030b0a06000e0427030f0b0a06210e04030b120a06000d4204030c0b1206000e0451030b0a110d444f03020a06000d040302191206000d04030b0a066000090e04030b0a11062b0e0403190b0a060d434204030b1206000d043b0b0a065e002b0e04030b1206000e04031f020b0a060d4204030b0a0630000d04035c
|11=>0x30b0a064a000d0469030b0a06000e04030b0a064c000e04030b0a0641000d04030b680a06000d04030b0a1150000d04030b0a066700050e04030f0b0a000d04030b0a6506000d0403020b1d06000d6404030b0a066300050e04030b120a000d04030b0a6106002b0e04030f0b0a06000d0403020b0a0631000e04030b0a0636
|12=>0xa066c000d040320020b0a06003e0e04030b0a11060d0403020b1d1206000d444f030f0a000d4404030a0622000d4404030c0a06000d5f040b0a0650000d430403020b1206000e04030c0b0a06000d0403020a062a000d470403020b06000e045103190b0a060d4504030b120a06000e04030b0a06380d046a030b0a06000e04
|13=>0x90504030b0a06000d04030b0a7006000d0403020b066f000d0403020b5d06000e0403020b0a11060d4404030c120a06000d4304030b0a0631000e04031f190b0a060e043d030b0a06000e04030c0b120a0600520e04030b0a06000d0403190a06220052050e04030b0a06000d04030c190a06000d04036e0b0a06000d04030b
|14=>0xb0a06000d0403200c0b0a06000d04030c0b1d0a06000e04030b1d0a060d0403200b1d0a06000d7304030b0a06000d4304030c0b0a06000d04030b070636000d043b0b0a0638000d040302190a11060d0403020a0658000d7204030b0a06000d454204030b0a06000e04030f190a060d043d03190a06000d04030c19120a0600
|15=>0x43c03190b0a060e0403350b0a06050e04030b070a060d04030b0a7706000d04270b0a0650000e04030b0a06760d04030f190a110d5f043d0b0a06000d04030c0b0706000d04030b120666000d04030b0a0675000e0451270b0a060d04030c0b120a11000e04030b120a110d0449030b0a06000d04030b0a0648000d43470403
|16=>0x6404510b0a06000e04030b0a0629000d04030b0a0655000e046d030b0a060d04030b0a067c000d0403200b0a0600090e04030b120a06000d4504030c0b0a06000d454304030b0a06000d04030b0a067b000e040b0a0615000d04030b0a067a000e04030f0b070a060e04030b0a062a0d04030b0a0679000d04030b0a0631000e
|17=>0xb0a067f000d5f04030f0b0a06000d434204030b0a06002b0e04030b0a06000d04030b0a062a000d644404030b0a06000d7404030b0a06000d440403020a06000d04030b0a066f000e0427030b0a060e0403020b0a06000d04030b5d0a06000d4204030c0b06000d043d270b0a06000d04030b0a067e000d7d04030b0a06000d
|18=>0x60d046d030b0a1106000d430403020b0a06000d043b270b0a06000e0451030b0a06000d04030b0a0684000d4f0403020b0a06000d04030b0a065e000d046d030b0a06000d04030b0a0683000d04030b0a0682000d0481030b0a06000d04030b0a066b000d04030b0a0680000d040302190a06000d04030f0b070a06000d0403
|19=>0x6600050e04030b0a06000d4204030f0b0a06000d440451030b0a06000d5f04510b0a06000d474f04030b0a06000d0427030f0b0a06000d4204030b1206000d0451030b0a11000d04031f020b0a06000d4f04030f0b0a000d0403020b0706000d04030c020b0a06000d043b030b0a1106000d04030b0a0662000d0403190b0a11
|20=>0x6000d444f030b0a06000d04030c0b0a06000d04030b1d0a06000d4304030b0a06000d04030f190a06000d04030b0a0636000d043b510b0a06000d0403020b0a1106000e04030f0b0a06000d04031f190b0a06000e04030b070a060d8504030b0a06000d0403020b1206000e0403190b0a060d04030b0a0650000d04030b0a06
|21=>0xd04030b0a06000d04030b070a06000d5f04030b0a06000d4f04030b0a06000e04030b0a06000d4204030b0a06000d0427030b0a06000d04030f0b0a06000d04030b120a06000d04030b0a1106000d043b030b0a06000d0403350b0a06003e0e04030b0a06000d043d030b0a
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x1e60186012600c600660006
|6,0=>0x1587151714a7143713c7135712e7127712071197112710b710470fd70f670ef70e870e170da70d370cc70c570be70b770b070a970a2709b7094708d7086707f70787071706a7063705c7055704e7047704070397032702b70247
|7,0=>0x341833983318329832183198311830a730282fa82f372eb82e382dc72d572cd82c582bd82b582ad82a5829d8296728e828772807278827172698261825a7252824b7243823b8233822b8223821b8214720c820481fd71f671ef71e871e081d881d171c981c271ba81b371ab81a4719d7195818d8185817d8176716e8166815f7
|7,1=>0x482847b7473846b8463845c7455744d8445843d8436742f74287420841884108408840173f983f273ea83e373db83d473cc83c483bc83b483ac83a5739d8396738e8387737f83787370836883617359835183498
|8,0=>0x68c8684867c8673966b8662965b7653864b8643863a9632862a8622861a8611960a760285fa85f285ea85e285da85d285ca85c285ba85b285a995a1859985909587957f8577856f8566955d9556754e8546853e8536852e8525951d8515850d850494fc84f574ed84e494db94d294ca84c284ba84b284aa84a284999492748a8
|8,1=>0x891888988818879887188698862785a8852884998409837982f88287820881888117809880187f987f277ea87e287da87d377cc77c487bc87b487ac87a5779c9795778d8785877c9773976a9763775a9752874997418739873187298721871897117709870096f886f086e886e086d886cf96c696be86b686ad96a5869d86949
|8,2=>0x8998
|9,0=>0xa8e8a868a7e8a768a6e8a668a5e8a568a4e8a468a3d9a358a2c9a257a1d8a158a0e7a0689fe89f689ed99e499dc89d399ca99c289ba89b199a989a18998998f9987897f8976996d9965895d8955894c9944893c8934892c8924891c8914890c890398fb88f298e998e188d988d098c888c088b888b178a988a18
|10,0=>0xadd8ad58acd8ac67abe8ab68aae8aa68a9e8a968
|11,0=>0xae57
|_,_=>0
def wAt:=mkWire dB 134 128 0xffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xd00414080b0a42c010206c34010f0a42c01060b438290d0043c290b064382d0d004442f0600434010e06428190d0040c010b064382d0e0643401050202c290e06434010b264384a0a064180a0a0b414290b00438190d0043c290a004182d0e0b434010b0a4382d0d00434010b1d41c190a00464290e06428190d00414080b0a428010f0a42c190e0b43401050202c29
|1=>0xb00428190d00434013c06cec01030b428190e0a42c010d00434010316418660b004840f050a438190d004840f050a434010a064340102004282d2b06438290b0043401060042c190e0a434010d0042ce12706c0c010e06418290e0b4340103004182d0e0b434010d004482f0a06418010e0c83c290b06428010e0b438190d004282d0a004382d0d0042c490e0642819
|2=>0xd0042c750706428012103c38490a06434010f0042c190d004180a0a0b5142f430651029040b4482f0d00428190a0042c49060a4382d0d0050819040a4340141004ec1b030b49c1b0d0040c01030b418012b03c38290d00434010f0a418010b06438490d00428190a004142f0b0a438190d00434010a16418660b0042c4606004380d0d0042c010d0040c3d060b4482d
|3=>0xa064340104208300106024442f0e0a418010d005141b420f410290b0642449060a4382d0d004242b0a004382d0d00434010600428193d0043401030f42c190d004187e070b428010e0642c010a0643401060043c290b004182d470bc482d0412428190d00430010f0a42c190b0a438290b00434010a1b4142f0e06434010e06434010a0642801120b43401120042819
|4=>0xa00414290e06434010b534142b0e0643401520ac142d0e0643401120b434010a06428014506d1c2d04124281903004241b0e0b434010e028282d0d005442f0d0040c0103064102d0406418090a0b4140a0e0643401030f418010b004182d120b42c010a06428010e06434014c004384a0a06434010206434010a0b42801210bc14290e06434010e028282d0d004384a
|5=>0xa0053c290406408010b0a438190d004242b06004382d0d0043829120bc28190d00418290b0a438190d0043401270fc0c010b064840f050a438190d00434010b1d41c190a00428010e0b438190d004d801120bc28190d00414080b0a438190d0043401060a418660b00438290d00408010a0b410820c0043c2906004182d0e0b434010b1d41c190a004383d0d0042c19
|6=>0xd0041801510bc0c190f0a42c19040b410190a00418290e0b4340103004142d0e0643401060b42c010e03434010a0b42c010a0643401042082c750706428010b064382d0e06434010600418290e0b4340104024282d050bc2c010e06434010502c2c290e0640c010d0040c3d0b0643c290b06438290d00410190a064282d040b4742d0d00448010a0641c2d0d0042819
|7=>0xb5d448030a06434010a1982c010a064282d040b4482d0a0641019090a4382d0d0042c190e0343401050a438190d00418010b0040c2d0a064282d0d00429614f0bc101906028282d040a40c2d4f0bc101902064282d0a00434010a0b428010300438190d0042c450600434010a06418010a0b42c010906c28010e0b434010b064ac0f0e0a4340103004382d0e0643401
|8=>0xa0b4280144034102d0a06438190d0041989270bc0c010b06438290d0050c1b04024282d120bc28190d005083d040a42c190b0640c010d00438490a0643401040a42c490a0643401060040c1904064282d040b428190a0b42c0150005442f0306418010e0b434010e0a42c010d005082d0a0641029030b57c1b0403438290a06434010d00408010a0b51c2f420641029
|9=>0xb064102d04064081b0a0b4102d02064282d040b4100d510bc0c190a06410090a0b434010f0a42c190b0a42c460600508190a0b41029030642c010d0051c2d0412428192706c0c010d0040dad4406c102d090ac382d0d0040ca90b11818010e12828190d00434013b06c0c2d0a2a42c46060041801510bc0c1922004180a0a0b42c190e064340106664100a0a0b41c19
|10=>0x60b40c3d0b004182d0b0042c490a064382d0e064340106715082f040a42c294206c10290b0a448030a06418010a0b43401040b42c490a0650c1b440a4102d190a42c010d0043401030f42c190d0042c490a064142d0e06434010206c282d0b004142d0e06434010f0a42c01060b430030f0a42c196d0bd440103064300106024282d06004380d0d004282d120042819
|11=>0xa0b428010a064100a0a0b5104a060a4102d0d0040c010306418010b12428190d004281906004f401030f42c19061f81c2d0a0050819420b410290c0043c290b06448010b12428190d0041c190a0042c75070642801740b53c0d04064081904024282d120bc28190a0049c1b030040c2d06004282d0b004282d4f0bc101904505442f03065083d040a42c190d0042c01
|12=>0xb0640c45060043401740bd3c0d040642c75070642801060a4382d0d00410310f0a42c19440a4102d420fc10290b064ac0f0e0a43401040c83c290b06434010b06428010d0042c460600408470b0a418014306d1029040b40c650b0043401190642c010d00428010e0643401067857c2f04035442f030040c190d0040c460600418010b004182d040340c3d0b0640819
|13=>0xb0a410195f06c100d510040c19440ac102d031982c015100c0c194406c102d045180c190a0b42c010b06428014403c102d040342c19420b410290e0a434010b118180144034102d4f03410190a0b4102d4206c10290300434010a0b434011200c28190f0a410290b0640c01030f42c195f0fc100d0b064108906028282d03065100d040b4241b0e0b43401270fc0c01
|14=>0xb004182d0b1282819030640c2d0b0a418010b06434010a1942c010a00434014f0b410190b0a428190b0043401510bc0c1904028282d0e0643401040a42c1903064102d040340c194f0a41019030042c190a0641029060040c1902004282d0b06410190a0b4280106024282d060040c2d270bc0c010b004180103114180104024282d030040c2d0306434010a1181801
|15=>0xa004100d040643401040a40c010b0642819060040c2d0f0042c190e0343401030f42c19040b410190f0a42c19070642801440a4102d
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x250008000
|6,0=>0x12cc47400000000000000000000010d00000fd03d200003a30d540000c5000000002e300002b3000026508901f3000000000001d20650145044c0d402500000000000000000001c80000000000
|7,0=>0x4f0d3844d113044b11284494d21447511a34591133440d0c44211044404cfe33eccf743cd0ef43ad0e833910e043710d843510d043310c843110c042f10b842d4cb322bd0ab429d0a5228509d4265095424508d4225085420507d41e507541c506d41a8c66418905e4169056414904e4
|7,1=>0x740dcc47211c447011bc46e11b446c11ac46a11a44681000000019c4668996464cd8f462d187460d17f45f497945d517145b5169459516145751594555151453514a3519143300013f4
|8,0=>0xa3ce8c3a24e863a0ce8039f4e7a39dce7439c4e6e39ace683994e62397ce5c3964e56394ce503934e4a391ce443904e3e38f0a3938d8e3338c0e2d38a8e273890e213878e1b3860e153848e0f3830e093818e033800dfd37e8df737d0df137b8deb37a0de53788ddf3770dd93758dd33
|8,1=>0xd38f4b3d20f453d08f3f3cf0f393cd8f333cc0f2e2cacf283c94f223c7cf1c3c64f163c4cf103c34f0a3c1cf043c04efe3becef83bd4ef23bbceec3ba4ee63b8cee03b74eda3b5ced43b44ece3b2cec83b14ec23afcebc3ae4eb63acceb03ab4eaa3a9cea43a84e9e3a6ce983a54e923
|8,2=>0x3513
|9,0=>0x3cc2f28bc82f18bc42f08bc02ef8bbc2ee8bb82ed8bb42ec8bb02eb8bac2ea8ba82e98ba42e88ba02e78b9c2e68b982e58b942e48b902e38b8c2e28b882e18b842e08b802df8b7c2de8b782dd8b742dc8b702db8b6c2da8b682d98b642d88b602d78b5c2d68b582d58b542
|10,0=>0xf5c7d61f547d41f4c7d21f447d01f3c7ce1
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 14
def pmP:Nat→Nat
|0=>0x1220000000002f5d00000000b5740000000215d0000000080d00000000200c0000000080280000000200000000000717000000000d5d000000002574000000004de00000000101000000000284000000000848000000002080000000004000000000008c000000000140000000000400000000000c0000000000180000000000400000000000c00000000002800000000008000000000018000000000050000000000100000000000200000000000400000000000
|1=>0x110a57400000422f5f00000108bd7400000422d5f00000108b5740000042295d00000102a5740000040a85d00000100b97400000402ddf00000100b57400000402c5d00000100ad7c00000402b5d00000100a57c0000040295d0000010013780000040000a00000100001000000400001000000f000300000038205c00000080006c0000014285c00000040a170000000403040000001008300000002095e00000006b17800000011a0000000001801000000006000
|2=>0x100008580000280001200000800884000001c003ce0000050080300000100a95f000004008030000010002cf0000040000180000100000200000300e77c00000c000000000024085780000090095e00000220857800000823d5f000002082578000008020000000020035780000080000c00000200002000000800004000001f0a5740000064295f00000190a57400000602b5f00000180ad740000060295f00000180a5740000048295d00000112a1740000044295f
|3=>0x8002a178000200002080000612001100001808215d0000602001200001800a0400000410000300001000211500003040a57c0000874295f000021d0a5740000854a85d00002150a5740000850ab5d00002142a57400008502d5d00002140ad7c00008502b5d00002140a57c0000844a95d00002102a57c0000840a95d0000206001100000810ab5f00001900a57c0000640221400001810a1680000600001e000011f0a57c0000440000500001000806000004002010
|4=>0x20104e57c00080411a0400020000200000040000800000100000060000400000080001000000000003060a95d0000c182a1740003060800c0000c082a57c0002c40a95f0000a150a1740002814804d00009900a57c00020a0205e00008180a17400020442b5f00008110a9740002044295d00008110a1740002044020c0000811001780002040aa5a00008100a57c0002040295d0000810008100002020205e00008010ad340002004295d000080100c300002004000c
|5=>0x2080108c200082004030c00206120a574008184800440020602001200081040000c00200100a5740080000210400200000001400501c001cf00140201083000500406bcd00102500a73c0040900000400100c1080e0004014029cf00100500a57c004012020000010000081640020853295f00080104b77c00200412ad600080100b5740016640001700058900a57c00124c0295f00042000073400100e0295f00040300a77c00100c003cf00022002b57c00080413d5f
|6=>0x42000000410108000000040420000000040c200412fdf03080104bd740c000402d5d02080104a97408200402a5102022106b77c0800843a95d02002106b57408000412ddf02000104b5740800040ac5d02000100b5740800040295d0200000eb77c0420051ac5d01080106b5740400100088001000144b77c04000412d5d0080000020100100440214700400100841400820542a5d00208110ad7400820442b1d00208110a9740082044220800208110083000820042b5d
|7=>0x50008000a5752000044295d4800001004310002040295d40000100ad750000040295d40000000ad748100440294f1c008010013470000402b5d1c000100a5747000004294d14000110a57450000402b5d14000100a5744000040295d10000010a5744000004294d10000000a5744000000200c0f000100b5743002004295d0c000110a57430000402d5d0c000100a5743000000000408208010ad342000040295d0800000084102000000000404200100a57410800002200
|8=>0x92000100b5763020040295d80000100bd7600000402d5d80000100a5755002040295d
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x140400
|6,0=>0x60200000000000000018000e0200024220002800000b00018000e0383000000000814050183c0c00000000000010000000
|7,0=>0x13a92570b41c23418203e22140b0b8990016406a52a0bcbef7348a80c4c5918496244e1f0101c1709c52032c03c00204d884408002330061413061b085081e1129a01818301b6e8355a7e0b144328d5b9f4ca9b481e4f6623015802842b8182a1764220bc4e29b25542526990a4c7250ad365d27820247f
|8,0=>0x1bc047e1d580e99e355e96dbede7d3e172462d0fc60ac342920234509c83cc3412186cc24a0d4841a5e2e92abb1aae11e373a3b5a0e037b6514b67d3e5166b40b88ecdc452d082b5632e46a7a4fa59ecee72875fa8e1c3fd96e6283915e3943aac72d21fa887e9709a98746671a1dc23e542f9aef449b4166677e879226376218eeea5fac53ca767231e0ef76b049055
|8,1=>0xc0
|9,0=>0x725036deac54c3f8dc86651b06675223d9186d688fd46fb758d6003d7e35492f223b119a3b38b59fc356a1a9e7021ab9ce0d372368e6457440dfc671cc120ae97d0f08086
|10,0=>0x8702788c5f43b19218d4a9
|11,0=>0x30
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 46 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_95 10 roots_95 ops++addP pm 1 dom_31 7 roots_31 ops++addP pm 2 dom_126 9 roots_126 ops++addP pm 3 dom_123 9 roots_123 ops++addP pm 4 dom_117 8 roots_117 ops++addP pm 5 dom_89 5 roots_89 ops++addP pm 6 dom_47 8 roots_47 ops++addP pm 7 dzo_23_8 5 roots_23 ops++addP pm 8 dom_111 9 roots_111 ops++addP pm 9 dom_122 7 roots_122 ops++addP pm 10 dzo_119_8 7 roots_119 ops++addP pm 11 dom_119 9 roots_119 ops++addP pm 12 dom_23 5 roots_23 ops++addP pm 13 dom_125 9 roots_125 ops++addP pm 14 dom_90 5 roots_90 ops++addP pm 15 dom_62 6 roots_62 ops++addP pm 16 dzo_55_8 6 roots_55 ops++addP pm 17 dom_55 6 roots_55 ops++addP pm 18 dom_121 6 roots_121 ops++addP pm 19 dom_57 4 roots_57 ops++addP pm 20 dom_59 6 roots_59 ops++addP pm 21 dom_61 7 roots_61 ops++addP pm 22 dom_63 9 roots_63 ops++addP pm 23 dom_94 7 roots_94 ops++addP pm 24 dom_91 7 roots_91 ops++addP pm 25 dom_21 4 roots_21 ops++addP pm 26 dom_93 8 roots_93 ops++addP pm 27 dom_58 5 roots_58 ops++addP pm 28 dom_60 4 roots_60 ops++addP pm 29 dom_124 6 roots_124 ops++addP pm 30 dom_92 5 roots_92 ops++addP pm 31 dom_87 8 roots_87 ops++addP pm 32 dom_30 4 roots_30 ops++addP pm 33 dom_115 6 roots_115 ops++addP pm 34 dom_27 4 roots_27 ops++addP pm 35 dom_120 4 roots_120 ops++addP pm 36 dzo_117_8 6 roots_117 ops++addP pm 37 dom_83 5 roots_83 ops++addP pm 38 dom_114 5 roots_114 ops++addP pm 39 dom_118 6 roots_118 ops++addP pm 40 dom_106 5 roots_106 ops++addP pm 41 dom_107 6 roots_107 ops++addP pm 42 dom_110 6 roots_110 ops++addP pm 43 dzo_53_8 5 roots_53 ops++addP pm 44 dom_109 6 roots_109 ops++addP pm 45 dom_103 6 roots_103 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_127 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_47 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_23_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_119_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_23 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_55_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_60 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_92 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_30 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_120 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_zo_117_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_zo_53_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h45;exact cpcs (by decide +kernel) lowS_103 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_95 10 s (0,roots_95.map (·&&&dom_95)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_127 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_95 h
def symsG:List (List (Nat×Nat)):=[[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_127==dom_127)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_127 gM v ys):RunD true dom_127 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_127 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 6 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 45 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 45 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 106 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 106 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 129 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 128 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 129 → Z 8 i = true := (range_split z8_0 z8_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 61 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 61 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 10 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_127 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_223:Lower true dom_223 roots_223 goal_223 12:=lower_slice_b [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,2,10)] (by decide +kernel) lowS_215
theorem lowS_239:Lower true dom_239 roots_239 goal_239 12:=lower_slice_b [(0xffff000000000000ffff000000000000ffff000000000000ffff00000000,1,33)] (by decide +kernel) lowS_207
theorem lowS_247:Lower true dom_247 roots_247 goal_247 12:=lower_slice_b [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000,1,33)] (by decide +kernel) lowS_215
def dzo_217_32:=0x303030300000000030303030000000003030303000000000303030300000000
def gzo_217_32:=0x303030300000000030303020000000003030302000000000302030200000000
def gsh_217_32:=0x3030303000000000303030200000000030303020000000003020302
theorem lowS_zo_217_32_208:Lower true dzo_217_32 roots_217 gzo_217_32 6:=lower_iso_b (d1:=dom_217) (r1:=roots_217) (T1:=gsh_217_32) [(dom_217,32)] (by decide +kernel) (lower_slice_b (T:=gsh_217_32) [(0x2020202000000000202020200000000020202020000000002020202,0,1),(0x3000300000000000300030000000000030003000000000003000300,0,8)] (by decide +kernel) lowS_208)
def dzo_211_32:=0xf000f00000000000f000f00000000000f000f00000000000f000f00000000
def gzo_211_32:=0xf000f00000000000f000e00000000000f000e00000000000e000e00000000
def gsh_211_32:=0xf000f00000000000f000e00000000000f000e00000000000e000e
theorem lowS_zo_211_32_208:Lower true dzo_211_32 roots_211 gzo_211_32 6:=lower_iso_b (d1:=dom_211) (r1:=roots_211) (T1:=gsh_211_32) [(dom_211,32)] (by decide +kernel) (lower_slice_b (T:=gsh_211_32) [(0xa000a00000000000a000a00000000000a000a00000000000a000a,0,1),(0xc000c00000000000c000c00000000000c000c00000000000c000c,0,2)] (by decide +kernel) lowS_208)
def dzo_219_32:=0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000
def gzo_219_32:=0xf0f0f0f000000000f0f0f0e000000000f0f0f0e000000000f0e0f0e00000000
def gsh_219_32:=0xf0f0f0f000000000f0f0f0e000000000f0f0f0e000000000f0e0f0e
theorem lowS_zo_219_32_208:Lower true dzo_219_32 roots_219 gzo_219_32 7:=lower_iso_b (d1:=dom_219) (r1:=roots_219) (T1:=gsh_219_32) [(dom_219,32)] (by decide +kernel) (lower_slice_b (T:=gsh_219_32) [(0xa0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0a,0,1),(0xc0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c,0,2),(0xf000f00000000000f000f00000000000f000f00000000000f000f00,0,8)] (by decide +kernel) lowS_208)
namespace S_251
def pG:List (Nat×Nat):=[(1,17),(1,33),(1,65),(1,129),(2,10),(2,18),(2,34),(2,66),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(8,10),(8,40),(8,72),(8,136),(9,11),(9,25),(9,41),(9,73),(9,137),(16,17),(16,18),(16,80),(16,144),(24,25),(24,26),(24,56),(24,88),(24,152),(32,33),(32,34),(32,40),(48,49),(48,50),(48,56),(48,112),(48,176),(64,65),(64,66),(64,72),(64,80),(64,192),(96,97),(96,98),(96,104),(96,112),(96,224),(128,129),(128,130),(128,136),(128,144),(128,192),(160,161),(160,162),(160,168),(160,176),(160,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffffffff
def xsM:=roots_251.map (·&&&dom_251)
def gM:=goal_251&&&dom_251
def NN:Nat→Nat
|5=>21
|6=>147
|7=>282
|8=>202
|9=>63
|10=>8
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0xf3c6fd5a0da8daca7edea0a8c88f2686ecb8687a8481f7c8cd68da261d225d9c95a08259cc45943e402ed3f61920d9b120360f020
|6,0=>0x9c1719b01f987f397d40975bd962b5953a6931c493046929b68bf518a16c88ce788042874b58656684e9c84dd884b2b834bd82c237b3ac751567378f6ffcf6febd6f7eb6f3646e3716e0cd6c88b6bb646b4596aec46746a66ba666a7363c486397c636a862c6661e6b612d060e8e60e765d0995cb425ca835c7f65bf1a5ab2b562a8545a352a04526b24ee194e7244d2a54c6744b4724a1de49de7488934667c44c9044b5d43da943b3243926430a0421dd41b8d3ff573fe5e3f4b43e0c53b6cc392c236b3e35d64341f833ef93387b32107317e830aee2d4602cff72af9c2a75e29c6928ad826ea226212241b723b6621b0b2020d1bbd71b49719bbf16cd0162141571c151a814f1e13df213ded122e20ea680e0a20dacc0d29f09432051fb0456a0435d0433803e9803d3303a5a036fb02b4f0232f0115300c27007ff00379
|6,1=>0xfc930fade5e3e2de2ce9daeebd7787d05efc3787becf9ba74bb238cb0a43af9d9adb87aab7eaa44d9e0109d02f9cb4c
|7,0=>0x456d94478d4442142a52422d0415fc41023403ea3ef963eb5d3e5263a7093a5e33a2d7397773910438ac83811737803373e136d0a364a53643b35c0f34d7a348a9343e0342a6335ce32692313e42febc2f6812f30b2f1c42ef382be192bdaf2b5762b5552b52f2a8812a6372a2742a1cb2a0db29ef12999a27df1279da2593d2532e252ad24ba324b8a235f422bde2121020fa4207a01f6e61ec571dc551db131d9811b43a1b2ac1ae7c1a53c19dac19bba1896317e90176cf1742217339172291722116e5f16c6a168361674c1606215dea15dbf15a71158ed13ded13bfd129d0127af125b112558124421201211bd6117610e6ed0e41c0e02b0db9f0d6dd0d1a60d0220b41909ca809b77093e308a5e0839407a9107a4d06ff6062ee0608605b51058e3058d804765040d703a2702fa2028ec020e201c5b0123400f9c006d5
|7,1=>0xc6bc3c6aa5c1c14c0cb6c045cbf955bf465be2e7bce82bb185ba588b98f4b82f7b7758b737bb6d99b61d6b1babb10ceac56eab50caa615aa4b0aa1d7a9865a91e9a6664a2ec5a26bda1d8ea0a019fd339ca419c6e39935598fb197ec397af29796c9757096c2f95d24901bc8ff888ef478e9358c9e889c438508e849cd82d8082b7c8289a7e95c7e7bf7e7507e3547deab7ce367c7c37af197ac887aae2794bf7934876dcf762c774ab773fd473e777362a733a17329572949728117209470f2570d2b70b8e6eef46c2c96bbe26ac546a49d69f4669d356836e6806f6738f66bba65b5565a4d655d3652d964a506318a5ef6f5dddf5cece5ccc35cab35ca6c567ea562c1549e9543835430453fea522e851f6151dd350d2a4ffdc4f01d4ec1c4dfa14df7e4d7524d2624cf3d4c96e4a716498924972548ecc48cb54858247d30
|7,2=>0xfcf41fc0cbfa288f83a7f0e38ee875eaa14e9fdbe8274e66d4e5277e4842e070bdd948d8884d6eb7d5549d2a3ad0f26ce441ca2e3c96fcc877fc8288c75c2c74e5
|8,0=>0x6c20e6b7e4694996764566bd9664f164a7564902642da63ff5615ef5daf85d6cf5c0145bf6d594ba5939c587ab58499562645557554a7c52ceb5224c51a805182550be94d61e4d1764c0064b39f49e3947a2c4716a46b7b466ce44ad2444a243ddf428bb4089f3fe9a3f1613dced3d7163cf0c3ccc63c4a13bdc63bae03b4ff380a237c03375cf3649f356b235501350b234fb4331d132b2e329cf31d2b3166b3112c2f7362d2b32bd312b8a82b2382b14a2a76529f052969f26f2824e0524d1723f39234a721e53210432074c1fc3c1e9dc1e71d1d54c1ceef1c44c1c44319b1e1922c1897d1881d18811179851676615fd51579815191136b3126f411ce10e0520d2560bd500ade809e2909d0b08f6708b210836807eba078b706da404f0e048d0044730381c035a903216031e902c120244d021e800e8300b000057700498
|8,1=>0xf53b2eb19ee56ffe468fe464ee349ddcbb8dc69bdab5dd7b61d62a6d0b4ecd8b1cb554c94f9c8348c10fabf7f7beee3bdbaab8cd5b8b43b590cb58f9b0facb0425afba5af16daedfeae20ead773ad63ba9e45a81e4a80bfa3fde9d9969d38c99749992d19810397cf89617b960b894c0e93b2b917109161490c298bb548a06d893448857c869318674c8633385540843198414281b6d818b1813aa812847f70d7d87c7be4d7bd537713975f047565e75142727c8719186fba4
|9,0=>0xf396dda323d7efcba537af21eab7fca131b9f10496e3e949ec87ae2858cb7ec097bed674a496c4956c0dd68a735e8db5c2ca5a0b35726d51e22505c24d3b84cd1b4816140a003ff043f29d3ef5e3d0123b92a3a5cc38cac36b5f351b5341a32f6942da7c2bb01283a02753125e8a2371f1c0961b3f61a49d19398179af16f1515de613d1813b5e10b8a0b32d09d920908f0790f05c10028070199301154
|10,0=>0xfd5476efcd53593527d9411753ecf2294df280a1
|11,0=>0xff75e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000e0e00000e0ef0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0000f0f00000f0f00000e0e00000e0e00000f0f00000f0f00000e0e00000e0e0000f0f00000f0f00000f0f00000f0f00000c0c00000c0c00000c0c00000c0cf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000000000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f00000000f0f0e0e0f0f0e0e0f0f0e0e0f0f0e0e0f0f0e0e0f0f0e0e0f0f0e0e0f0f0e0ef0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000f0f00000f0f0000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00f0f0f0f0f0f0f0f0e0e0e0e0e0e0e0e0f0f0f0f0f0f0f0f0e0e0e0e0e0e0e0ef0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
|0,1=>0xf0f0f0f0f0f0f0f0e0e0e0e0e0e0e0e0000000000000000f0f0f0f0f0f0f0f00000000000000000f0f00000f0f000000000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0c0c0f0f0c0c0000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0c0c0f0f0c0cf0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0ef0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0cf0f0f0f0f0f0f0f0f0f0c0c0f0f0c0c0f0f0f0f0f0f0f0f0f0f0c0c0f0f0c0cf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0cf0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0000f0f00000f0f00000f0f00000f0f00000e0e00000e0e00000e0e00000e0e00000000000000000000000000000000f0f0f0f0f0f0f0f0f0f00000f0f0000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f00000000f0f0f0f0f0f0f0f0f0f00000f0f00000f0f0f0f0f0f0f0f0f0f00000f0f0000
|0,2=>0xf0f0f0f0f0f0f0f0f0f0e0e0f0f0e0e0f0f0f0f0f0f0f0f0f0f0e0e0f0f0e0e0000000000000000f0f0f0f0f0f0f0f00000000000000000c0c0c0c0c0c0c0cf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0e0f0f0e0e0f0f0e0e0f0f0e0e000000000000000000000000000000000000f0f00000f0f00000e0e00000e0ec0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0f0f0f0f0f0f0f0f0f0f0c0c0f0f0c0c0000f0f00000f0f00000c0c00000c0c00000f0f00000f0f00000c0c00000c0cf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0e0e0e0e0e0e0ef0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0cf0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f00f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f00000000000000000000000000f0f0f0f0f0f0f0f00000000000000000e0e0e0e0e0e0e0e0000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000000000000000f0f0f0f0f0f0f0f0f000f000f000f000f0f0f0f0f0f0f0f0f000f000f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f000f000f000f000f000f000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0000
|0,3=>0xf000f000c000f000f000f000c000f000f000f000c000f000f000f000c000cf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0f0f0c0cc0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0c0c0000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f000000000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0000000f00000000f0000000f0000000f0000000f0000000f0000000f0000000f000000000000303000003030000030300000303000003030000030300000303000000000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0e0e0f0f0e0ef0f0f0f0f0f0f0f00000f0f00000f0f0f0f0f0f0f0f0f0f00000e0e00000e0ef0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0cf0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0000000000000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f000f0f0f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f0f0f000f0f0f000f0f0f000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f000f0f0f00f0f00000f0f00000f0f0f0f0f0f0f0f0f0f00000f0f00000f0f0e0e0f0f0e0e00000000000000000000f0f00000f0f000000000000000000000e0e00000e0e
|0,4=>0x5050505050505050505050505050505050505050505050505050505050500000000f0f00000f0f00000f0f00000f0f00000f0000000f0000000f0000000f0000000000000000000000000000000000f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0cf0f0f0f0f0f0f0f0f0f0f000f0f0f000f0f0f0f0f0f0f0f0f0f0f000f0f0f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f0f0f00f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0cf000f000f000f000f000f000f000f000f0f0f0f0f0f0f0f0f0f0f000f0f0f0000000000000000000000000000000000f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0cf0f00000f0f00000f0f00000f0f00000f0f0f0f0f0f0f0f0f0f0c0c0f0f0c0cf0f0f0f0c0c0f0f0f0f0f0f0c0c0f0f0f0f0f0f0c0c0f0f0f0f0f0f0c0c0c0cf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c00000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f000000000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000c0cf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000e0e00000e0e0000e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0f0f0f0f0f0f0f0f0f0f0e0e0f0f0e0e
|0,5=>0xc0c0c0c0c0c0c0c0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0f0f0c0c0f0f0c0c101010101010101010100000101000001010101010101010101000001010000d0d0d0d0d0d0d0d0d0d0c0c0d0d0c0c0d0d0d0d0d0d0d0d0d0d0c0c0d0d0c0cf000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0e0f0f0e0ef0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000f0f00000c0c00000c0c00f000f000f000f000f000f000f000f000f000f000f000f000f000f000c000c0000f0f00000f0f00000f0000000f0000000f0f00000f0f00000f0000000f00f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0f0f0c0c0f0f0c0c0000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000c0c00000c0cf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f0f0f0f0f000f00e0e0f0f0e0e0f0f0e0e0f0f0e0e0f0f0e0e0f0f0e0e0f0f0e0e0e0e0e0e0e0e0000000000000000f0f0c0c0f0f0c0c00000000000000000f0f0c0c0f0f0c0cf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000
|0,6=>0xf000f000f000f000f000f000f000f000f0000000f0000000f0000000f0000f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f00000f0f0f0f000f0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000f0f0f000f0f0f0000000000000000000000000000000000f0f0f0f0f0f0f0f0f000f000f000f00f0f00000f0f00000f0f00000f0f00000f0f0f0f0f0f0f0f0f0f0f000f0f0f00000000000000000000000000000000000000000000000000f0f0f000f0f0f00d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0c0c0c0c0c0c0c0cf0f0f0f0f000f0f0f0f0f0f0f000f0f0f0f0f0f0f000f0f0f0f0f0f0f000f00000000000000000000000000000000000000000000000000f0f0c0c0f0f0c0c00f000f000f000f000f000f000f000f000f000f000f000f000f000f00000000c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0c0c0c0c0c0c101010101010101010101010101010101010101010101010000000000000000f0f0f0f010101010f0f0f0f010101010f0f0f0f010101010f0f0f0f000000003030303030303030303030303030303030303030303030303030303000000000000000000000000f0f0f000f0f0f0000000000000000000f0f0f000f0f0f00000000000000000000000000000000000000f0f00000f0f00000c0c00000c0c
|0,7=>0xf000f000f000f000f0000000f0000000f000f000f000f000f0000000f0000303030303030303030303030303030303030000030300000303000003030000f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f0f0f0f0f0f0f0f0f0000f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f000f000f00303030303030303030303030303030303030303030303030000000000000000f0f0f0f030303030f0f0f0f030303030f0f0f0f030303030f0f0f0f00000000f0f0f0f0f0f0f0f0f0f0f0f0f000f000f0f0f0f0f0f0f0f0f0f0f0f0f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000f0f00000f0000000f0010101010101010101010101010101010101000001010000010100000101000000000000000000000000000000000000f0f0f000f0f0f000f0f0f000f0f0f0000f000f000f000f000f000f000f000f000f000f000f000f0000000000000000f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f0000000000000000000000000000f0f00000f0f000000000000000000000f0000000f00
|_,_=>0
def sP:Nat→Nat
|0=>0xc84896280808b1e4c101345cd930404d0718581012a20296060809a18590020268796260809a181100234647842608d1918108023e002843c085801e70982160061d384c10b364c11a166429806085970a581012a48884280808722108020200782160070d180858a12202840608080
|1=>0x26085971a14c03042cc920a0c982342cc852c7098216482960608b990c44b130404d0d1ea0982320030c2c0c129163489304685aa1a44b14046430f2608599424879304a45992430b0216386922210982346468c504010116487a626883861a30b03042d28d364c11a161c68f268d107
|2=>0xe488962008d0b1a30203042d70d1859002022c90f2c4c10116486044008599243c213042cc921858802342c40c5a4c1010e20d93042cc922240982165c00c2c085ac1a4860326085a53245410045c3860a4c1010e5490c26085992a208ab260858d18085871c3490c200c101341c8a8
|3=>0x4643121840182165cc8c5a4010b0e208902608d0b3214203042cc921860982342c405684d1a20e186282c4010b1030803040458018b4802166490f644d1020e186312608599243098216658121810f02341c68f2608d0b2e346044008d071a3c213046838d22bc982341c68c0840129
|4=>0x225810b143490c30a098216208a82008c800c30203049438d22bc982160068c260809a2e2060420085972430b0216284121e4c11a1664793046859910310130404d070a10182341c68c5e4c10b0020628384c10b1030c03042cb8d18581012a3490c042caaa1a488982608d0b1a3da93
|5=>0x160028406085801a30982021ca881858802026890f268c386744879304643392430982022c4881810802346490504045871c4861c26085992430e96060858d186018216644053a4c1190018283260809a0e31a3226083860ae0982161c90c2c085b71a49b11284c10b1a3021e042c00d
|6=>0x2250982166489d260858d18f8e13042c90c5a401010e48793042de8d2444210046838d2210982020068c2608d0b32907a826085801a44b14042c69130749821634896200808b24f0b13046858d1810802341c40c3aa09821634602166470824302130404008229d1070cec68c404c101
|7=>0x166490f384c1000e18782161c70d241410117043921874e13041c311085010b0e347930404d0718d01070cec68f260809a0e2061c26085972444982160050d22f8982160068c200c129161c60406085991014e13042c01218101823464691804c10b0e34616280808b246c9870cfc692
|8=>0x883c982162069218589820268445364c10b1a4a213042d08d2431410042c41b2608c800c30e13042c0081840182165c7930464006423098202683a47810982341c68f664d1a20e186042608f801a44a1304045878610982166490c50708021648793042e10d2431c13042cc920a74982
|9=>0x1034793042cc882430210046838d2430e130464006243c9a3441c30c084c101003490c260858714209052c4c11a16349490a4cf020e1890c064c10b2e3479346883861030982341c50d2444c13042c692883c982163490c2c5010b1a486183a4c10b1a488c826083861a32313042c692
|10=>0x2444210042c38d2430982161db8d243010b0e3840d2430b1304a458d243d393441c30d224c10b0e2869218589821694692180948b0e3869218749822e1c30d1860b130400308184c101341c40c200c1170e18793042cc921810802161c4121e4c1070ce46920a9c1a30e1890c2c0c10b
|11=>0x9a401190c482be2608c870c4862826085881a30c1c26083862414b13045cc862430982342c38d4832603460838610319b226083861030813042e3922260b13040030d224c101341c68c042c38e1a4864a041c33b1a4889d2c4c1070c3462764401070c4861c26080070c206282008c86
|12=>0x18d09a3441c30d18409820268392884c1070c846920a4d1870d3890c50401070c2060326085991015416260858d2415913041c3122270982001c30d1858802022c90c804c10b0e34905984d1a20e18911084c10b003460420085992430a13042cc921874982163490c4f2c386763490c
|13=>0x161c69218cd393461c30819301820e18411204c101161c90c3a58982001868c304c119001840c664d1a20e1840c2c0c101163490c2608580143490c080c10b323490c7c4c10b003490c5a5818216349055a4c10b0e349052608c8612488d126080061a3263426883861a149820f3c692
|14=>0xe487962608c862430213042d70d244651344083861a3c982022c388243098216652120aa0e13041c3121860e83041c30d1e60982321c3122274982321c30d184c101160040c084c11f0e349432c4c10b1a486162008b800c4889426085871a1541304640062444813042c00d1810a02
|15=>0x1e4c1190e1909218c89a3041c312a644a13041c30d1874982001c30d0a4d1820e19d9218581825c1868c04685871c3490c6608386763490c260a90b0e34911260808b00342933c080070c4539396883861a31413040458d2430b2004643128a6c9820e186920a60982166490f260808b
|16=>0x3490caa4c10b1a488a82608b870c348cc684c1070c342980608c870c488b4268c1070c34603260808b0e20602522e0871a48604304010b1a4863826085871a486100608c800c3098217506921850982022c3921840982022c01218f8c13042c69218d09a3041c3081931913041c312
|17=>0x2444813045c0070c30b1304685881b0c213042c38d243c9870d5c69218581822e0030d0a10982341c6921e4c386ae206921860982165c692189c8220e1840c2688386ac208ab26083861a14b03046431218085c10e3490c3058982162090c204c10b2e6490c5e0c10b0e3490c504010b
|18=>0x3462d26085991a486102608f8b0e4860420080872431a1396083861a3c9820e1ac8d24314162008c862430b1e040030d0a58982022c911a24c10b1a482cc272c1070c4860426094871a48613042ec0d24153b226083862430b10045c3120aa0982321890c7c4c10b1a48d930464386
|19=>0xe2068c5070982321890c04685c10e3490c384c10b0034911304c10b323490c2608c8612208cc268d1070c34793b8083861a486282c401070c2029304a408b0e48627644d1870c4864c4e0c1070c2065b26085871a4861d2c4c10b1a48618260859910486100608d0b0e34603260808b
|20=>0x41c308784c11a161c68c300c1170e1868c084c10b2e3490c504010b1a4863364401070c4864c2688386110d393461c31218401822e64386197c982163490c260948b32209052c0c1000c346202608c800c309821774692184c11f160068c064c10b2e64685084c10b003490c5a4c10b
|21=>0x6083861a30b130404d0d2430c0304643861030213042cc882430982342d50d250c982166490c94d09820e1868c200c10b0e20293042c48d241419304640061ecc9a2041c30d1861413041c30823309a20e1868c200c10b3248613042f00d2432690042c69222a0982320030d18a0e13
|22=>0x464362243141304643082258a020e1868f2608587423490f260948b0e3490c7c589821634911c24d1070c34627461c33b1a4861304685971034893042cb801a30b20042c6921810982341c40d1e58982163490c2c0c1190c206202608d0b0e34610260948b0e488a728083861a30e96
|23=>0x26085871a482af260808b0e4a1962608c862444e93041c30d184c10b0e3869218f8e13041c312184c10b542090f268c1070c8490c26085e51a48296060858d258c982161c6921860182320030d1880982166490c5a4c1010e3490f2609e870c34911644d1020e18685084c1010e48793
|24=>0x2608d0b0e34793041e78d243d3930e1b30d2431893042c38d2433393042c6921e4d1870d9890c2608587583490c5058802163490c4e08386763490c088010b0e3490f2608c800d24283260858d243c213042c38d24166034608386243c9823200308224c11a1664691989c9a20e1869b
|25=>0xc2068c3058982163490c7c4c1190e18692224c10b0034893041c32a1a486162608b990c3490c98cc9820e1840c26085e91a4828326085801a31f13042cb8d243098232003241e4c10b2e34968364c1070c3490c30a0982163490c2c085951a487b526083861a48793041c3421a48890
|26=>0x64c1190e18911272d1020e18685084c10b0e3490c664e5820e186920b349820e18692184d1870d386921931383041c30d2431913041c30d24319a72608386103464d260858d243261346883861a4a485064c1070c3490cd44c1070c34905504c1070c34911284c1070c346332688107
|27=>0xc3490c204c1170e1890c2608386122068c984d1070c3495a1e4c1070c206920a4c11a161c6921858982162069218a0982320030d2445390041c30d24449820e1ab0d2433393041c30d2430193045c0070c3461304643091a486282c401070c3490c4e401070c2090c2608386ac20905
|28=>0x22588020e18692184d1820e19d8d2432883041c30d2430982522c38d243099e04003861a314130400386103461304a4587103490c304c10b323490c26085a50e3490c404c1000e1868cd64c1070c3490c2c401070c2090c26085ae1a48628384c1070c3490c080c10b0e3495a1e4c107
|29=>0x300c1190e186921929993041c30d2430b1c26083861a4860326085801a31a2726083861a482a7268c38624149a3441c31223309a3041c30d2431394041c30d2444b13040030d1840182161c6921858802321890c66401070c3490f2608b870c349052608b990e1890c30a09820e18692
|30=>0x26083861a4861628083861a486162608d0b1a4a193042c38d2432313041c30d2433093441c30d2510793041c3081a48613041c33b1a486160608c861a4864c2608386104866d26083861a482a726883861a486182608386104828326080070c34613042cb801a4863e2608b870c3490c
|31=>0x864d1820e1890c084c10b323490c9a4c1190c3490c4e4f6070c349112608c800c3461304a4d0b0e3490c2c4c12e0c3490c504c1190c3490f2608c870c4863226881070c349490a4c10b1a4879304643861048613042c38dc8488cc26083861a4861304640061030213042c3881a4a20f
|32=>0x25c49820e186920a4c10b003490c5a4c10b0e3490c2608d0b323490c989c9a20e18692180c982321c30822cc9a2041c30d0aa0b13041c30d250d393041c30d24309820e1b80d243c9820e1b10d2430e93041c30d25b89820e186921840982320031218409828e1c312224c1070c84692
|33=>0x161c6920a4c101161c90c944d1820e18692184c10b5434905304c1190e1890c2608c870c909112c4c10b1a4863320881070c3490c200c1070c2219626083861a48613042cb8d2430982342c3881a31393461c3082430982165c40d2447093041c30d243099e042c38d2431013042c38d
|34=>0x2414b13040030d241419346083862432a93041c30d2433990041c30d2431403260858d243c9820e1908d244662726083861a4a81126083861a4862d2608d0b0e3490c26085991048613041c3541a4863e304c1070c3490c268d1070c206102608d0b0e3490c4e4e5a30e186920a0c982
|35=>0x2c4c1190c3491b26083861a4864c664c1070c3490c2608386b03490c2608386ea3490c2c4010b1a486139608386763490c904c1070c3490c2608587e83490c7c4c1070c3490c2c4c1170c3490c304c1170e18692189c9cb0e186921810982341c6921860b13041c3082432513041c30d
|36=>0x1a4a80f26083861a48633644c1070c3490f26085871a48793041c3661a48618260858d2430193045cc870c34793042c3881a4861c26080070c34911304c1190e1869218589823218412184c101341c692ec14193041c30d2430982161ca8d243179026085871a4861026085871048628
|37=>0xe18692ee4c1070c3490f2c4c1070c3490c26085871a9090c204c101161c9432608c870c4861026881070c2062740083861a487a726083861a4864a4e4c1070c3490f268c1070c486100608c870c4879346083861048613041c3601a4862820083861a4860326085991a4865f2608386
|38=>0x24309822e643861a48613041c30df0482a726083861a4862826080070c3490526881070c3490ce64c1070c3490c200c1070c34905268c1070c48613041c3091a4861305943861a4862720883861a48613f2083861a4863e2c4c1070c3490f272c1070c3490c944e5820e186921859002
|39=>0x184c1070d386921931393041c30d2430b03041c30d24309820e1bd8d25e8293041c30d2430982161c40d25d8293041c30d24309ec041c30d2414b13041c30d2431383041c30d2431393461c30d2430b13042c692184d1a20e186921930813041c30d2430c1026083861a4a193041c30d
|40=>0x26085871a486162608386103490c2608d0b0e34905064c1070c3490c272d1820e18692184c1070df06921810982161c69219349820e18692189c9820e1840d2430c1626083861a4889304003861a31413041c30d243099e041c30d24309a3041c3082431013041c30d24309821664692
|41=>0x2e1c30d24309822e1c3081a4829304003861a48613041c30de448793041c30d243c9820e1840d2524293041c30d2444982161c69218409820e18412180c982001c30d1e449820e1869218409a2041c30d2430b13046430d24309cb041c30d24309cb041c3081a48613041d7061a48610
|42=>0x613041c30d24309820e1840d2430982321c30d24449820e1869218589820e18692189c9820e18692184d1020e1869218409820e18692184c10b0e3490c064c1190e18692184c119001869219309a3041c30d2430982321c30824309820e186a42431993041c30d2430982
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x786039301b180ccc060602d30151809cc0486021300f1806cc030601530091803cc018600930031800cc0006
|6,0=>0x11a388b5c44ce21f710c38845c414e20370fe387d5c3dce1e770f038765c3a4e1cb70e2386f5c36ce1af70d438685c334e19370c638615c2fce17770b8385a5c2c4e15b70aa38535c28ce140609cb84c9c256e124708eb8459c220c1097081383edc1e8e0ed70733837dc1b0e0d170653830dc17ac0b67057b82a1c142e09a7049b8231c10ae07e7
|6,1=>0x1f7b8fa1c7c2e3da71ea30f35c78ce3bf71dc38ec5c754e3a371ce38e55c71ce38771c038de986e8c36d71b338d7dc6b0e35171a538d0dc67ac3367197b8ca1c642e31a7189b8c31c60ae2fe717bb8bc1c5d2e2e2716db8b51c59ae2c6715fb8ae1c562e2aa7151b8a71c52ae28e7143b8a01c4f2e2727135b8991c4bae2567127b8921c484c23b7
|6,2=>0x11c5c8d4e463722eb115d88a0e44a6221b90f1c86ae42e7213b9081c832e4127205b9011c7fae3f67
|7,0=>0x329b992e0c88e63c831ab98b60c4b061e730bb9841cc12e60182fd397ca0bd6e5e382edc174e0b9705c382de396d20b5ae5a672cf4165a0b1d058682bfb95de0adf056782afc1561caa1054882a0414e20a6105297291394718a29050c8282b93f9c9eee4ef8273c138589b304d18264c13060974e4b37255c1291c93ae49672474121dc900e4788
|7,1=>0x41f420da105ee82874104206210210808840041fe20fe107e883f041f620fa2e7c983e0c1ee60f64e7ab73d1c1e6e0f28e78c83c2b9df9ceeee76f83b3c1d7e0eb0e75083a441d020e7107317394c1c89ce3507137385c1c11cdf906f48376b9b960dbb06d58366c1b160d7b06b58356c1a960d3b06967347b9a1e0d00e6788338419a20cc2e65a7
|7,2=>0x5153a88dd438ea157506c281613fb09f584f6c279613bb09d674e74271a137d09b684d74269a133d099684c74261a12fd097684b74259dd2bf095784a7c2521d282e93a7499424aa1246e91b848a3a435d20ce8ff747bc23be11cf08e0746c42342119108c0845cba2c9d156e8a4744eba256111b0885843ec21d9d0dd0866842f4215a109d08468
|7,3=>0x604bb00617f4ebf285f5baf91d7b90bd485e6baf16177cebb775d83aea21742eb9985c8c2e261704eb7b75ba3adb5d6cb0b5d85aac2d39d68d0b3e859bbacc1d6510b21758d3ac4a16150b03757dc2bce15d70ae3856dc2b55959b0ac6755fbaae1d5610aa88550baa69d526ea8c7542429f214eaea6d8532c2979d4ad0a4f75243a9021472ea318
|7,4=>0x199b0cc6765fbb2de1960eca97650c32661924ec8a8641431ea18e6ec6b8631c3171d8aaec4d8622c30f6186b0c2f6613c307e182f0c107
|8,0=>0x76b4bb3ddd90eebf975bc3ac1dd510ea1774cc3a461d130e80973c439be5ccf0e5f872bc393a5c8b2e3d871ac38b61c4b0e1d870b3b8365c0b0dfd86fac37b61bcb0ddc96ea437321b872dbb86d9c36ae1b452d9a86c8cb6261b030d7986b8c35a61ac12d5886a84351e5a7f0d369697bb49a5a3b2d158686c3419d9fb2cf586764b39999bd0cd59
|8,1=>0x86ac4339e18b30be785b442bde14f109f884bc423e210f107f883c3c1c5e0d31061882c4c1422091103f981bc40be204f101f880c3c0422011100087fcbbfc61fd30fe187ed3bf465f930fc187dd3bec65f54efa287cd43e4a1f16ef8297bd43dca1ed50f6377adc3d4e1e952f42879d43cca1e550f22878d43c4a1e150f01977c4bbbe5dcd2edf7
|8,2=>0x96ec4b59e59d12c6895f44ad6655cf2a6894f44a5a251d1286893f449da24db3266792f4495de49d3246891ecc8d264591224890dcc84e2415320288fccc7c9e3d331e188ecc4749e39331c188dcc46c6235311a098cc44642230f317f88bbc45be22cf115f88abc453e228d313e889acc4b9e24d111d988b3c436620930fc887abc3b261caf0dd8
|8,3=>0x265d1326898f44c56661b1304997e44bd5e5db12e58
|9,0=>0x54b26a49151b9a89c542e2a0714fb8a794d3aa29c514db7a69c532e2988f4bc8a5a452b22947349b8a49c522a6905147a8a38cd1a628c314589a2845122288114379a174d09de83f14178a07c501e2800f3f889f7ccf9e27bf13d789e7c4f1e277f13b789d7c4e9e2740f39889c7cce1a66fef37699b744d9a26bb335589a6c4d16267cf3368
|10,0=>0xab5c558e2ab8f5548aa6455122a7915357
|11,0=>0x15737
|_,_=>0
def wAt:=mkWire dB 125 252 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x18350e19164926490e3518350e192649183532490e352601223518490e490e3516210e191a490e35204b18492635261d0e190e35182124350e1918490e191e9c18211a49343718912622044904351e4f1821243518210e211a49163516490e190e1926211a49063526490e191835324926650e351635262d0e4918490e190e19
|1=>0x182166370e21164918210e191a4926211a49260516350e19024916350e19263518490e190037262d0e192049263518212435063526490e3518210e1924350e190849262d0e1918910e3526220e1924351849003526350e490e191849003526010e490e1918490e19281d204b26350e190035184926010e490e19266526490e35
|2=>0x18491849202d26350e490e190e211a49163516490e1900350e490e35182116490e191a49164918210e191a4906352649262d183516490e19202d26350e195037266532490e350e190e191e5818212435324926490e350e19062d0e192649263518490e19262d26490e3518350e190e192c490e19261d24350e19062d26490e19
|3=>0xe350849262d0e190e191635262d0e4918490e19262224352235184926010e490e190e19204b18492635261d1849163526350e19223718490e191a49243520492635262d264918350e190e19163526020e190e1926a60249264926650e350e190e1918355a37221d204b26350e19063726490e192c492c35261d26010e492635
|4=>0x2635243518910e4926220e3524350e210e192649263524350e490e351821243526890a49043518350449204b18490a4b0e3518350e1950371835503726a402491849204b18211a49163516490e191649163518210e19243516210e1924351a4916490e35262d0e191849204b2635204b26350e3518490e190e19304b26651849
|5=>0xe19260616350e191649261d18350e19063726490a1d1835324926490e350e190449182104352435260616350e192c35261d18490e190e191e1d18211a49261d204b26350e19304b26650e350e1918492809204b2635271d324b0e350e191e1d18210e191a4916351649261d0e19189126221a491e4f18211a492c490e19261d
|6=>0xe191a4934351649261d0e191821260904491a4918492606163534371649261d0e1926a616210e191a493249304b26650e352c35261d1a491a49163516490e19324926350e35264922350e3518490e19243504352649183526090e19261d26491a490e3518210e1924350e19503726010e490a490435183504490e491635262d
|7=>0x18350e352c49261d0e191a4950372c352c49261d261d183532490e3526221a492649268d04356637060926492635324b0e350e190e4918492c35261d1849163516490e1926a616210e191a49944f272d04211a49304b18492c354e492609503726010e49061d26350e3526491849262d26350e192a35266a16490e1926a61621
|8=>0xa01b0a0d18352649984b268d04350e191e4f18211a49268a0435183504492c49261d263524350e190e3526491a490e1918352c49261d663726891835044918495037260126351635261d0e19268d043518350449262d0e4918490e190e35262d26350e19204b26350e350e190e19304b2c35261d04211a490e352c4b2635261d
|9=>0x204b26350e19183526010e490e3526350e4918490e19204b263524354e49260926492009263524351849163526350e19304b2c35261d0e4926650e3524350435268904491a4926491635261d0e190e49260616350e190e35262d26490e19062d26492669164918350e19183526020e490e352c37261d18490e49984b268d0435
|10=>0x261d0e190e352621261d2435189126221a49183526650e350e19182116350e192435261d223518490e35262d00370e490e1918490449163518210e1924350e3526220e1924355037260118350e49304b26650e35182126650e3524351849304b2665243516350e490e19024b16350e190a4b261d18350e1900350e4926351849
|11=>0x265e32490e350e19204b26350e49163526350e190e192c35261d984b268d043594379849200926350e351e4f182124359437068d04352649204b263518497c4b20010e4926351835272e46492649261d00370e4926a634350e19272e26894435044926221a490e49163518490e190637264918350e4918494435044926092c49
|12=>0x24350449268e04351849281d204b26352649261d18350e3526a416210e191a491a490e192c35261d324926350e350e190835262d0e19263526010e490e199a350e192c4b261d2601184900350e491849984b20092635183526650e352649984b268d184926490e1926a4201d262d26350e195a37062d26490e4926350e352649
|13=>0x268d4649043516210e191a49544926660e350e19183566374e490e21261d26352435260118350e350e492c21261d0e191a490e351891262224352635184900350e491a491649261d0e190a4b18350e19880b1e1d18211a4900350e492649261d18351649262d0e19880b1e1d18211a49324926650e350e192635260904491a49
|14=>0x1e4f18211a492c49261d24351835024916350e194e4926091a494e352609304b0e192c35261d0e1926650e35243526350e19163526490e490e19062d26490e350e19024b16350e1926351635262d0e19984b268d46490435b44f18211a490e3526352c49261d06370e492649261d1635261d18350e192c37261d18490e191835
|15=>0x2435260904350a4b183532490e3526490e193c1d0637264916210e192435261d264918350e49204926350e350e490f79202f26350e190e49024b16350e19324926490e350e19262d0e4918350e190849262d0e19503726010e4926a434350e190e19503726010e4926650e3518490e191a4926020e490e350449268d18490435
|16=>0xe19264926352435183526020e490e190e35264918350e490a492689183504491a492c492c35261d268d0449184904350e1926350e352649066626490e350e1926350e192c4b261d184926010e490e355037061d26491649223718490e192649324926650e350e210e191a49260126350e490e19663706092649044920092635
|17=>0x18210e1918494e3704492609464904350e2116490e191a490e19184900350e492621261d0e191a491a492235261d18490e190e35261d26491a4906352649024916350e19204b263518492609304b2c35261d16351649261d0e19264926650e350e35262d0e192435164926660e350e190e350a4b18350e19944b272d04211a49
|18=>0x266518490e3526a616211a497c37265d0e2124351a4926660e350e1904351e4f182124350e9126220e191a492649261d18350e19199116220e191a49264926650e35063526490e350e190849262d0e1918496637268918351635262d0e190e351e1f18212435061d0e3526491a49204b18492635261d0e191e4f18211a491621
|19=>0x2695343716490e192c23261d1a4904351e0b1821243506061635264926350e192c49261d944f98494e35260926211a49223518490e490e3526490a1d18350e1918210e191a492649268d183504350e4918210e35243516490e3518490e19184904494e3526090e19189126221a491835260516350e19261d0e350a4b1835304b
|20=>0xe192c35261d06650e3526490e4918490e19266618490e35261d32490e354e3524354e4926090f9116220e191a4926490e4918350e190e190e211a490e4926220e3524350e2118210e191a49189126221a492c490e192c35261d266a1649261d0e191e5818211a492635164918490e19a01b1e4d18211a4926091e0b18211a49
|21=>0x1a49264900350e4926020e490e3526352c49261d2609263524352435268e043518350e352649443518490449262d18350e1926894435044918352c4b261d0435268a04494e352609264966370609264924354e4926090e192c4b261d268d0449043526490a1d18354e2326091a49260118350e491849204b2635268904491a49
|22=>0x637264926010e491a4916210e191a4926650e350e19343716490e1920490e49263527b1464b0435261d2635243500370e490e1950372c49261d262d26490e191e0918211a490e212635243526020e491a49268d044904351e0918211a49164918350e19261d0e191a4926010e490e35263518492609268e184904352c23261d
|23=>0xe490e190e211a4926650e3526490609264950372c49261d26490e490e19984b4e352609043518352609043518350449268d18490435204b26092635261d18490e49264926350e190e352635261d4e492609263518210e211a49183532490e352c492c35261d18492635261d272e464904352c372649261d16210e191a490e49
|24=>0x6637268904490a1d18350e1918210e35243516220e191a49268d184904351a490e490e35262d0e191a491e1d18211a49204b2635261d1649261d0e190a4b18350e19271d324b0e354e37044926091e1d18211a49272e04211a49261d0e352649200926352435c2494e372609260918350449201d26352435264918350e490035
|25=>0xe1904494e3526090e3526491a4926891849044918352c49261d0a4b18352609208a044926351e1f18211a49304b2c35261d19bd060b264926350e350e492635324b0e351e4f2235184904350a4b1835262d0e350e190e352c4b261d464b0435260918490e490e35343516490e19261d00370e4926010e490e35223518490e35
|26=>0x4352609264918350e19163518350e19068d0435264926660e350e19183526650e3526220e352435261d18490e19268904492635264926352435261d0a4b183532490e350e1916490e191a492609043524350e210e191a494e3718492609063726490e1926210e191a4919c904221a490e4918350e19062d26490e1916490e35
|27=>0xe19265d0e211a49261d0e211a49324926650e35260904211a491649262d0e191a492c35261d272d04211a49261d18350e491835043526499a352c4b261d4e4b260926350e19061d26491e4f18211a494e3518492609224118492635266916490e191a490e350e19265e0e211a492c35261d044904352435164926350e194649
|28=>0x18490e191e0b18211a4926650e350e1932490e35264918210e191a49503726010e49266518490e350e35261d2435163516490e1926490a091835266a16490e19202d26350e190e19263524350e352c49261d189126221a494e494e352609544926660e35ac49268e0435261d26350e19272e04211a492809204b2635062f2649
|29=>0x261d182104211a4904211a492621261d1a4919e10e221a49261d18211a4926220e191a49163526350e190e350a4b18350449263524350635260926490a491835260998494e35260922351849043526350e35264918210435243506660e35264926010e49263526490e350e193c1d063726491e4d18211a496637060926492235
|30=>0x1a490e350e19268a04494e3526092649261d061f26490a4d18350e191a490a091835464b04351835261d2609264904352609261d0e190435044920092635201d26350a4b183532490e350e221a491835260926010e49183504494e4b2609264926351835043526020e490e9126221a49044926092635049126221a4930492c35
|31=>0x1a49060926490e211a490e211a4918350e4904221a4918211a4918211a490a1d183518490e19263524350e49264922351849044926350e35261d04211a4904211a4900370e4926350e19261d1a4916490e191835264946490435200b2635262d0e192c4b261d26091a492c35261d18490e492c49261d06372649043524352621
|32=>0x1a490e351849261d2609044926350e190e3526490e490e35268d04350e3524352622
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x1060000000000f100d2000000b20000000000000000000000000065000000000015000000000001
|6,0=>0xa820a440a130a0109c40000000009b109830944091308e308950881000008440831080307e20000000000000795077200000743071306e306b30692067206520614060105d3058505350000000004f4000004e1049500000481043503e50395000003540000030502d3000002850244023100000221021101e301d101b20165
|6,1=>0x1202000011e211950000114500000000000011131101000010c410b11092000010450ff500000fc300000fb10f650f420ef50ea500000e640e420e22000000000e1100000df20db400000da1000000000d730d610d42000000000d0400000cf100000cd200000c940c7200000c340bf400000ba50b550b3200000ae50aa4
|6,2=>0x14941463143313e513950000134513040000000012b500001292125412410000000000001222
|7,0=>0x22942254221421e321a400002164212420e420a42064204220041fe21fa41f641f241f021ed31ea31e641e241de41da41d641d331d121ce31ca41c641c241be41ba41b641b331af41ab41a741a431a0419c4198419710000193418f418b418a11873183417f417c317841744170416c416931654161415d415941554151414d4
|7,1=>0x3074304330042fc42fa22f642f332f032ec42e842e442e132dd42da32d642d332cf42cd22c942c542c142be32ba42b732b342af42ab42a742a522a1429d429942963292428f328b428832844281327d4279427542732270326c426842653261425d4259425542514000024f224b424742434240323c4239323812353231422d4
|7,2=>0x3ed43e943e543e143dd43d943d633d333d033cc43c843c443c043bd33ba33b643b423b1300003ad43a943a723a3439f439c339843944391338d438943854381437d437a33764373336f436b43674363435f435b435833544350434c434843444340433c433843344330432c432843253321431d431943154311430e330c230b1
|7,3=>0x4d144cd44c944c544c144bd44ba34b644b244ae44aa44a644a2449f349b4498300004953491448d448944854481447e3000047a447824744470446c446b146744634461245e345a445734534450344c444844444440443c443844344430442c442844244420441c441844153411440d440a3406440333ff43fb43f833f443f13
|7,4=>0x52d452945254522351e451a45173513450f450c300005084504450044fd34f944f544f234ee44ea44e824e444e044dd34d944d54
|8,0=>0x5ee35eb35e835e535e235df35dc35d935d635d335d035cd35ca35c735c435c135be35bb35b835b535b235af35ac35a935a635a335a0359d359a359735943591358e358b358835853582357f357c3579357635733570356d356a356735643561355e355b355835553552354f354c3549354635433540353d353a3537353435313
|8,1=>0x6ac36a936a636a336a0369d369a369736943691368e368b368836853682367f367c3679367636733670366d366a366736643661365e365b365836553652364f364c3649364636433640363d363a363736343631362e362b362836253622361f361c3619361636133610360d360a36073604360135fe35fc25f935f725f435f13
|8,2=>0x76b376837653762375f375c3759375637533750374d374a374737443741373e373b373837353732372f372c3729372637233720371d371a371737143711370e370b37083705370236ff36fc36f936f636f336f036ed36ea36e736e436e136de36db36d836d536d236cf36cc36c936c726c436c136be36bb36b836b536b236af3
|8,3=>0x78837853782377f377c377a277737743771376e3
|9,0=>0x80728052803280127ff27fd27fb27f927f727f527f327f127ef27ed27eb27e927e727e527e327e127df27dd27db27d927d727d527d327d127cf27cd27cb27c927c727c527c327c127bf27bd27bb27b927b727b527b327b127af27ad27ab27a927a727a527a327a1279f279d279b27992797279527932791278f278d278b2
|10,0=>0x810180f180e180d180c180b180a18091
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 16
def pmP:Nat→Nat
|0=>0x20400000000020100000000012000000000010000000000009900000000008800000000008400000000008000000000006c00000000005800000000004800000000004000000000003a00000000003000000000002900000000002800000000002400000000002000000000001e00000000001400000000001200000000001000000000000c00000000000a000000000009000000000008000000000006000000000004000000000003000000000002000000000001000000000000
|1=>0x400800000000400400000000400100000000400000000000243400000000202400000000200c00000000200000000000122d00000000102800000000100c000000001004000000001001000000001000000000000a0000000000082000000000081400000000081000000000080a00000000080400000000080200000000080000000000063e000000000616000000000420000000000418000000000410000000000402000000000400000000000240000000000228000000000224
|2=>0x10002200000010002000000010000600000010000400000010000300000010000100000010000000000009d22d00000009783d00000009509e00000008020000000004020800000004020000000004001400000004001000000004000a00000004000400000004000000000002200000000002041000000002003400000002002400000002000c00000002000200000002000000000001fe1000000001fa3900000001d22d00000001563900000000e03100000000420000000000400c
|3=>0x100523d00000100522f00000100522d00000100503c00000100502500000100420d00000100322b00000100123d00000100102b00000100100f000001000209000000900202000000840820000000808a3000000080102400000080100400000080100200000080100000000080008400000080001800000041822900000041800400000040100000000021428d0000002002a80000002000a800000020008800000020000c000000200008000000200000000000100224000000100024
|4=>0x129523d00000128d22d0000012842ad00000122523d00000122402c00000120523f00000120523d00000120523c00000120522d00000120503c0000012042ad0000012040ae0000012040ac00000120408a00000110522f00000110522d00000110502d0000010952bd0000010952ad00000109523d00000108f63d00000108d2bd00000108d2ad00000108522f00000104122900000101800800000101522d00000100d23d00000100d22d000001005e380000010052bd0000010052ad
|5=>0x49000240000048042850000048002a400000480028c00000480000400000420022400000420002c0000042000240000042000200000041002a400000400c2a500000400c22d00000400408400000400008400000400002c000004000020000004000004000003000200000003000000000001a0522f000001a0422d000001a0403c000001a0402d00000181d23f00000181d22f00000180523f00000180523d00000180522f00000180522d00000180483900000140522f0000012a523c
|6=>0x8000000000005a0422f00000590d2ad0000059052bd0000059052ad0000059050ad0000059042ad00000580d23e0000058052bf0000058052af00000580523f00000580522f0000058040a500000580402e00000528502d00000520522d00000520422d0000051040ac0000050952ad00000509522d00000501d2ab0000050052ad00000500523f00000500523d00000500522d00000500503c0000050042ad00000500402e00000500402c00000500123c00000490028c0000049000ac
|7=>0x1020028c00001020020c0000102000ac00001020008c0000102000080000100042250000100010020000100010000000100002ac00001000020200001000020000001000008c00001000008800001000000c00001000000800001000000200001000000000000d00523d00000d00502c00000910103c0000090af23d0000090852ac000009025a1c00000902523d00000902023e000008200019000008022034000008020030000008020000000008000018000008000010000008000004
|8=>0x15a0400300001580422f00001520422f00001520402d00001508d22f00001500522f00001500422d0000142842270000140842a700001128d2ad00001128423c0000112052ad00001120522f0000112042ad00001120428b00001120422d0000112040a900001120408f00001120402e00001108d23f0000110842bc0000110842ad00001108422d00001100d22f0000110052af00001100523f00001100523d00001100522f00001100522d00001020c0ad0000102002ac0000102002a8
|9=>0x4128422d00004120523f0000412042a900004120422d00004120403c00004102481d00004101520d00004100523f00004100522f00004100522d00004100520d0000410042af00004020002000004001500d00004000420d00004000100000004000090400004000020000004000002400004000002000004000000200003100522f00003000100c00002180522f00002141522d00002140d22d00002100522d0000200000200000200000080000192052bf0000190252350000190052bf
|10=>0x6100502d00006000002000005500422f00005400408300005180523f00005180522f00005180502f00005180422f00005180422100005180420500005100522f00005100423800004902401d00004520523d00004520522f00004520522d00004520422f0000452042250000450042af0000450042a700004500422d00004500403400004500402e00004420022c00004420022800004420022400004420002800004400002000004200420d000041a0422f00004180522f000041804234
|11=>0x10109f23d00010041d22d00010001f23d0000e141522d0000e100522f0000e100522d0000e100502f0000e100502d0000e10050230000e10040270000e001402d0000e00010280000e00010240000e000002c0000e00000280000e00000240000c000102c0000c00000240000c00000200000b14050270000a180502f0000a100522d0000a100502d00009140d22f00009100502f00008180522f00008141522d00008140d22d00008100522d00008000d02d00006180502f00006141502d
|12=>0x90200820c00090200800c00084520d22d00084520502d00080500d22d00080500d03d000449005a1d00044802031500040108fa3d00040100423900040000083200040000041200030041d22d00030009d22d00030001922d00028181d22f00020581d2af00020581d22f00020181d22f00020100522d00020040d02100020008c22100020000422d00020000100400020000020400018041d22d00010409f23d00010409d2ad00010409d22d00010408c22d00010149d22d00010149122d
|13=>0x208181522d00208180522f00208180522d00208180502d00208140d22d00208100522d00208100502d00208080002c00208000d02500206180400300206100502f00204180502f00204100522f00203100522d00203100502d00203000102800203000100c00202140d02d00202100502d00202001500d00202000000800201000000800200140d22d00200100522d00200080000c00200041d02d00190001f23900190001d22d00180301c20800180301c00800090300f23d00090300d22d
|14=>0x40203101522d22010100d22d22010000100c20008100d22d18010049922d10000140522f08010149122d04000000000002004000500d0200000010000104080afa1d0104010afa1d0100080b703d00800148002d00800049802900440184523d00440184021b004401005e3900440084042800401102527d00401002046400400902563500400180563900400109763900400102563d00400100563d004001004235004000097e3900400002041400228181d22f00218041d22d00209100500f
|15=>0x88010148d22d8000a140d22d8000012952ad62000101900860010001d22d
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x380000020500014000000000000003c0000048000002
|6,0=>0xa800df230004259000009e4700128380a000f88059030000439050247e000602890000011c000a09000040000038042a0000160000100028005682800100d0003a116f800846c0503c1c180780000022aabc2a0b09008006301019de00000000e0a00038080b07028140a020080c0f0c800000900008800001025600c002bc70f2020007a04010009a023491c4634
|6,1=>0x40783c4900400b30200000f2000a808620000000ef
|7,0=>0x7308ab8ec170bcbd2c00e1c67d60f1ba7a2700944aefad38b6ae41ce117044a959c954f199cb65ca20221165357e159c3abbb8bd6148d784f2ae4001302ab534493a524010f36f1169198f6f59d072ddd3a9d28f804a73c128015f896dbaa61d17888701cb80cf187b88a8752969863c3279696e825f615c600b6435b00231f0492301dab99ca7073474b3b5cf5d8da2
|7,1=>0xe45c46f2f5a1e8a65b62620f1153cade8006003e3ab8a874c43e502ceb0081b6d5508f7d8f8949f3296042884b0be68067e7545de421bad25849b7a3cc86207024e4776b12ecfb9484d58ed96593942a6513991714cb80c9f6730357bb0b15d0901a16163a4023280c73a8a007811daf869c091f8936899c06b5e0e90c60db70287183eadd6c1d32a58132ca24c0564e
|7,2=>0x6c778597152cb190438a55000a3a26a112631631338cdc384cf382daa7
|8,0=>0x55a7f5f5a41b73936b6bc9e0b5b50a2b99c6b947bbf0041ea3247ded5369780ee3a19f6966f352b12c1ca7438e535f1ace7d24f38e8463eb7467d8ede64baea7c29b85da3021ef20b7f8f7773aff8aab51d8e3dba219f9c621d08cbff9f52e3562c74240bfe43e06ccd2f1e145a69fb60b2a5d82c580586cf1bdfbac6a9edcdd0fbb04e5cb3f258b4e75f527b23998c0
|8,1=>0x147b5519d38405ac220b0a5cce6f6959bf1bf0d5dc831e24c981f6f5f7fc9d497aa87f519bdceeef1b31417ee306cc7b1cf8e13683245b261de72a8e7e4eda12f5f91646e9d9e5b55205fdf0a7710ccbbe5dd9d
|9,0=>0x469957a6a28f64db6b2254844c6e81194183e0766d0deef901385671a11bd9bba12f28a82362903b356991a8bd44e09e45377ac69e955a933babdd4506db5249a29a992d56c880
|10,0=>0x5231d0a9792ea26e7f
|11,0=>0x7d
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 48 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_250 10 roots_250 ops++addP pm 1 dom_43 5 roots_43 ops++addP pm 2 dom_235 9 roots_235 ops++addP pm 3 dom_187 9 roots_187 ops++addP pm 4 dom_248 7 roots_248 ops++addP pm 5 dom_123 9 roots_123 ops++addP pm 6 dom_106 5 roots_106 ops++addP pm 7 dom_121 6 roots_121 ops++addP pm 8 dom_170 5 roots_170 ops++addP pm 9 dom_249 9 roots_249 ops++addP pm 10 dom_122 7 roots_122 ops++addP pm 11 dom_186 7 roots_186 ops++addP pm 12 dom_243 9 roots_243 ops++addP pm 13 dzo_216_32 5 roots_216 ops++addP pm 14 dom_241 8 roots_241 ops++addP pm 15 dom_155 7 roots_155 ops++addP pm 16 dom_91 7 roots_91 ops++addP pm 17 dom_232 5 roots_232 ops++addP pm 18 dom_58 5 roots_58 ops++addP pm 19 dzo_217_32 6 roots_217 ops++addP pm 20 dom_57 4 roots_57 ops++addP pm 21 dom_233 6 roots_233 ops++addP pm 22 dzo_211_32 6 roots_211 ops++addP pm 23 dom_59 6 roots_59 ops++addP pm 24 dom_219 10 roots_219 ops++addP pm 25 dom_217 8 roots_217 ops++addP pm 26 dom_185 6 roots_185 ops++addP pm 27 dom_234 8 roots_234 ops++addP pm 28 dom_107 6 roots_107 ops++addP pm 29 dom_227 6 roots_227 ops++addP pm 30 dom_171 6 roots_171 ops++addP pm 31 dom_179 6 roots_179 ops++addP pm 32 dzo_219_32 7 roots_219 ops++addP pm 33 dom_27 4 roots_27 ops++addP pm 34 dom_184 4 roots_184 ops++addP pm 35 dom_153 5 roots_153 ops++addP pm 36 dom_89 5 roots_89 ops++addP pm 37 dom_115 6 roots_115 ops++addP pm 38 dom_120 4 roots_120 ops++addP pm 39 dzo_218_32 6 roots_218 ops++addP pm 40 dom_202 7 roots_202 ops++addP pm 41 dom_211 8 roots_211 ops++addP pm 42 dom_42 4 roots_42 ops++addP pm 43 dom_139 5 roots_139 ops++addP pm 44 dom_75 5 roots_75 ops++addP pm 45 dom_147 5 roots_147 ops++addP pm 46 dom_83 5 roots_83 ops++addP pm 47 dom_203 8 roots_203 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_251 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45|h46|h47
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_216_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_zo_217_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_zo_211_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_zo_219_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_184 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_153 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_120 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_zo_218_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h45;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h46;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h47;exact cpcs (by decide +kernel) lowS_203 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_250 10 s (0,roots_250.map (·&&&dom_250)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_251 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_250 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_251==dom_251)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_251 gM v ys):RunD true dom_251 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_251 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 21 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 21 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 147 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 19 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 147 → Z 6 i = true := (range_split z6_0 z6_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 256 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_256 : ∀ i, 256 ≤ i → i < 282 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 26 256 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 282 → Z 7 i = true := (range_split z7_0 (range_split z7_128 z7_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 202 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 74 128 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 202 → Z 8 i = true := (range_split z8_0 z8_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 63 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 63 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 8 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_251 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_149_8:=0x3300330000000000000000000000000033003300
def gzo_149_8:=0x3300330000000000000000000000000032002000
def gsh_149_8:=0x33003300000000000000000000000000320020
theorem lowS_zo_149_8_21:Lower true dzo_149_8 roots_149 gzo_149_8 5:=lower_iso_b (d1:=dom_149) (r1:=roots_149) (T1:=gsh_149_8) [(dom_149,8)] (by decide +kernel) (lower_slice_b (T:=gsh_149_8) [(0x33003300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_21)
def dzo_220_32:=0x1111111100000000111111110000000011111111000000001111111100000000
def gzo_220_32:=0x1111111100000000111111100000000011111110000000001110111000000000
def gsh_220_32:=0x11111111000000001111111000000000111111100000000011101110
theorem lowS_zo_220_32_208:Lower true dzo_220_32 roots_220 gzo_220_32 6:=lower_iso_b (d1:=dom_220) (r1:=roots_220) (T1:=gsh_220_32) [(dom_220,32)] (by decide +kernel) (lower_slice_b (T:=gsh_220_32) [(0x10101010000000001010101000000000101010100000000010101010,0,4),(0x11001100000000001100110000000000110011000000000011001100,0,8)] (by decide +kernel) lowS_208)
def dzo_213_8:=0x33003300000000003300330000000000330033000000000033003300
def gzo_213_8:=0x33003300000000003300330000000000330033000000000032002000
def gsh_213_8:=0x330033000000000033003300000000003300330000000000320020
theorem lowS_zo_213_8_21:Lower true dzo_213_8 roots_213 gzo_213_8 6:=lower_iso_b (d1:=dom_213) (r1:=roots_213) (T1:=gsh_213_8) [(dom_213,8)] (by decide +kernel) (lower_slice_b (T:=gsh_213_8) [(0x330033000000000000000000000000003300330000000000000000,0,64),(0x330033000000000033003300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_21)
def dzo_221_32:=0x3333333300000000333333330000000033333333000000003333333300000000
def gzo_221_32:=0x3333333300000000333333320000000033333332000000003332333200000000
def gsh_221_32:=0x33333333000000003333333200000000333333320000000033323332
theorem lowS_zo_221_32_208:Lower true dzo_221_32 roots_221 gzo_221_32 7:=lower_iso_b (d1:=dom_221) (r1:=roots_221) (T1:=gsh_221_32) [(dom_221,32)] (by decide +kernel) (lower_slice_b (T:=gsh_221_32) [(0x22222222000000002222222200000000222222220000000022222222,0,1),(0x30303030000000003030303000000000303030300000000030303030,0,4),(0x33003300000000003300330000000000330033000000000033003300,0,8)] (by decide +kernel) lowS_208)
def dzo_181_8:=0x330033003300330000000000000000003300330033003300
def gzo_181_8:=0x330033003300330000000000000000003300330032002000
def gsh_181_8:=0x3300330033003300000000000000000033003300320020
theorem lowS_zo_181_8_21:Lower true dzo_181_8 roots_181 gzo_181_8 6:=lower_iso_b (d1:=dom_181) (r1:=roots_181) (T1:=gsh_181_8) [(dom_181,8)] (by decide +kernel) (lower_slice_b (T:=gsh_181_8) [(0x3300330000000000000000000000000033003300000000,0,32),(0x3300330033003300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_21)
def dzo_85_8:=0x330033000000000033003300
def gzo_85_8:=0x330033000000000032002000
def gsh_85_8:=0x3300330000000000320020
theorem lowS_zo_85_8_21:Lower true dzo_85_8 roots_85 gzo_85_8 5:=lower_iso_b (d1:=dom_85) (r1:=roots_85) (T1:=gsh_85_8) [(dom_85,8)] (by decide +kernel) (lower_slice_b (T:=gsh_85_8) [(0x3300330000000000000000,0,64)] (by decide +kernel) lowS_21)
def dzo_245_8:=0x3300330033003300330033003300330033003300330033003300330033003300
def gzo_245_8:=0x3300330033003300330033003300330033003300330033003300330032002000
def gsh_245_8:=0x33003300330033003300330033003300330033003300330033003300320020
theorem lowS_zo_245_8_21:Lower true dzo_245_8 roots_245 gzo_245_8 7:=lower_iso_b (d1:=dom_245) (r1:=roots_245) (T1:=gsh_245_8) [(dom_245,8)] (by decide +kernel) (lower_slice_b (T:=gsh_245_8) [(0x33003300000000003300330000000000330033000000000033003300000000,0,32),(0x33003300330033000000000000000000330033003300330000000000000000,0,64),(0x33003300330033003300330033003300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_21)
namespace S_253
def pG:List (Nat×Nat):=[(1,5),(1,17),(1,33),(1,65),(1,129),(4,5),(4,20),(4,36),(4,68),(4,132),(8,40),(8,72),(8,136),(9,13),(9,25),(9,41),(9,73),(9,137),(12,13),(12,28),(12,44),(12,76),(12,140),(16,17),(16,20),(16,80),(16,144),(24,25),(24,28),(24,56),(24,88),(24,152),(32,33),(32,36),(32,40),(48,49),(48,52),(48,56),(48,112),(48,176),(64,65),(64,68),(64,72),(64,80),(64,192),(96,97),(96,100),(96,104),(96,112),(96,224),(128,129),(128,132),(128,136),(128,144),(128,192),(160,161),(160,164),(160,168),(160,176),(160,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffffffff
def xsM:=roots_253.map (·&&&dom_253)
def gM:=goal_253&&&dom_253
def NN:Nat→Nat
|4=>4
|5=>69
|6=>235
|7=>289
|8=>124
|9=>27
|10=>4
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x83dd9614e12d55001493
|5,0=>0xa1d0583dd9839e6824c66f3236e4ca66155614e15991657bc5538434fc7e4f5c7496e0414a43cdce373d634e3e341a4305192d63a2d3862ce1226b1125d6f253a622a302207420ee0209341eebd1e4f51bc161ace01a3ee1987518a9a17fc216a13132711279a1202811c7f117b910a9e0e1a90ded30d8910c4aa0c0c50ad420acd909da9081e20779a071c20627f0557504b71043d604194025370204001dc60187c0123200f3000809000a2
|6,0=>0x1c6561bd531bb581b2481ab141a5ef1a3f3196da1952b194571908d18b8418aff18a9f184631835c182f817d2b17b1b17a7f179d3178f717587167fd1627f162481608915ce81592815751152f014788146ab1465f12c1e1296b128ae122261208d11e3b11a861193111669115751146a10f0610ea8108a1104480f8610ee110ea020e1da0e0450dfb80d5670c96b0c37d0be360b8ba0b1870affb0a81a0a51e0a4ac0a3a109e5d09dba09bb509a920989c09700096ed096c508ce408b10089ca0895e0853c0829f07d6e07cb407a2507967077470763b0738c072720716006bcc0630705e74059380581e0564f055c1054b20539c04d1b04af904a2f049b9049120422e0406603eda03c1c038c2032bc031b50318402ad402933026dd023680231101e4301bb901a8601a7e0149801233011d40104700ebc007ec0067c0042f
|6,1=>0xd9620cec07aeceea8209a578da200d9e3468e6338b90788c997e4c67e0977d9467b5717ace276a1174b4573ce7727236f3236e4ca6da106bcd1681d361a0d5a3f55780c577375203d4f8954f4b74eaf84dc3c4c8974bcdf4bae84b6e948af244ca443f5e4319d4183140e6e408a0406a640331400d43f3833ed8d3d5023cf723b1c83a36f39a60399c939725395e23946637a3637041362f335ce13507e33bcc3180f3111830f6030ac6305b32fe662fc4b2f8552ed872cffd2c1cc2b73f2b6df2b1b92aa5529f9f2969028a52286f628495282792812027a43272bd2718f26ddc26a70269f7263db257af2457e243f922ae12130020eeb2086e207cc1feab1fdf31fb631faf51f2331da87
|7,0=>0x13f9f13da0137c3135ca134fc134ed1340a12c6912ad8128071249a11d0411ca611c6c11a18114da113f5110511100510ef710e9710d8610a080f6c60f3520f30d0f2350e9ba0e81e0e03c0dee50de8e0ddf00dc830d3e00d1b80d14c0ccc20c9900c4740c35f0c20e0c1bc0b85c0b8050b5cd0b2cc0b0ad0ad540a9ca0a7b10a4030a0bc09f61095cf093fd08f1508a6f08a5f0891708647083fb0836c07fc207ec107eaa07e6807dcb07af5079c8079ba079740763507381073240716f06e3706dee06c830667106666056310559e0505704ee704dc204d6504b1f04ae00494a04618044a0042e7040d003fe903f7603c0503ab203a640336f02eea02d8902b5e02b0202a880286d0245c02409023440218f01c2f01af40197701920016d9015d30153b0145601336011b500eb800e7200c9b00b2b007a7006e2004090014c
|7,1=>0x560445371d51b4f4e7e74d31a4d0aa4a1f4494554811c460604593e43a0c42e184247941a58407f03ff3f3e3ef3d2e83cbb13af3f39a93391903879b383373813c37e58377d136f8836bfc3689435cbe352623516834940346463326a31d1731b69319cb30c43306522f3c72ee6e2e4aa2dcde2d3502c3b82b7742b11e2adaf29f6129ccd2902b289ff28592284bc282a02829127ee62729a2714726dfe26b022659f262d22607625983250f424b0423744235fc2327d229fe228e42212821e042177120d4a209601ff111fb0e1f6811f1e71ea6e1e9591e8f01e29f1d9141d5c71d4a01cc2a1c8b51c71c1bfcb1b6251b6091b0d81ab101a9f01a97c1a53c19fd019f50197b3196b5196a319681194cc190fe18cc018bd71853017b7a17967178031738a169e516456159341539215381152b114b5c14b4e14a491466c14652
|7,2=>0xec591e3639d9620cc12bb5e0bab32fa31e6a200d978d19684a900c38ddd38b90789ff48991681b2e819fa743787145d6dc836cb3f66fb5650a564e30623c560d216008f5e2ab5b37158ab057b6c577ac56b62
|8,0=>0xc9927c876ca77aaa48ba9684a95e9487e768798a86fbb82e1b7c67377b1d73f9e6c9e8635156117b56772543c553c8e536164fa5b4d2ed4c2644b8e74899c4780d45f2d4097e3ed003cc0d3b1383601435c6534cc62e49e2e3342d90a2c3262b942279d92761925ca9256e5223f7210e520a1b204d61f0761f06c1eba21e29f1d59b1d1cb1b54f19e86196e8193b81925f187c21860617f3617d3d17cce17aeb175b81717616ada1614f15a58157161461d13d34139b61364f12b0a11b0810a09107280fa710e5240e13a0c8c90b8ad0ae7f0a7310a57c0a1d109c40099e7097f9097df092f6091a00916808fb208dfd089a1088dc0878b0859e08090070d106b530613f05d6705d5a04448039c00256e0256002514023ce01efa016bb0169b01680008ef008dc008cb006a00068f0029e001e700042
|9,0=>0xc1cf7a52b39f3ff7e5b863ab757908500b04de4947710449ba433823e5b63ce373a9d8347502d25d2bb242b843252ec1e0f11cc840f76e0e325075ab0629b0559a01ee9
|10,0=>0x460ee0b2540a7a603200
|11,0=>0x1e31b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccc00000003332333233323332333233323332333233323332333233323332333233323332888888888888888888888888888888888888888888888888888888888888888b030303030303030303030303030303030303030303030303030303030303030cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000003333333333333333333333333333333333333333333333330000000000000000cccccccccccccccccccccccccccccccc00000000000000000000000000000003333333333333333000000000000000033333333333333330000000000000000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0003332333233323332333233323332333233323332333233323332333200000000cccccccccccccccccccccccccccccccc8888888888888888888888888888888b33333333333333333333333333333333333333300000000333333330000000000000000000000000000000000000000cccccccccccccccccccc0000cccc0003322332233223322332233223322332233223322332233223322332233223322ccccccccccccccccc0c0c0c0c0c0c0c0ccccccccccccccccc0c0c0c0c0c0c0c1111101011111010111110101111101011111010111110101111101011111010
|0,1=>0xccccccccccccccccccccc0c0ccccc0c088888888888888888888808088888083333333333333333333333333333222233333333303030303333333330302020cccccccccccccccccccccccccccccccccccc0000cccc0000cccc0000cccc00033333333333333333333333333333333333333333333333330303030303030300000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000c8c80000c8cb33333333333333333333333000000003333333333333333333333330000000044444444444444444444404044444040444444444444444444444040444440433303330333033303330333033303330333033303330333033303330333033300c0c08080c0c08080c0c08080c0c08080c0c08080c0c08080c0c08080c0c080b333333333333333333330303333303033333333333333333333303033333030cccccccccccccccccccccccccccccccccccc8888cccc8888cccc8888cccc888b333333333333333333333333333333330303030303030303030303030303030cccccccccccccccc8888888888888888cccccccccccccccc888888888888888b333333333333333333322223333222233333030333330303333202033332020cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc03232323232323232323232323232323232323232323232323232323232323232
|0,2=>0xccccc8c8ccccc8c8ccccc8c8ccccc8c8ccccc8c8ccccc8c8ccccc8c8ccccc8cb333333333333333333033303330333033333322333333223330332033303320cccccccccccccccc0c0c08080c0c0808cccccccccccccccc0c0c08080c0c080b333303033333030333330303333303033333030333330303333303033333030cccccccccccccccccccc8888cccc8888cccccccccccccccccccc8888cccc888b333333333333333333333333333333332323232323232323232323232323232cccccccccccccccccccc8888cccc8888c0c0c0c0c0c0c0c0c0c08080c0c08083333333333333333333333333333333333333333333333332222222222222222cccccccccccccccccccccccccccccccccccccccccccccccccccc0000cccc00033333333333333333333000033330000333333333333333333330000333300000000000000000000cccccccccccccccc0000000000000000cccc0000cccc0003333333333333333333333333333333333333030333330303333303033333030cccccccccccccccc8888888888888888ccccc0c0ccccc0c088888080888880833333333333333333333303033333030333322223333222233332020333320204444444444444444444444444444444444444040444440404444404044444043333222233332222333322223333222233332222333322223333222233332222
|0,3=>0xccccccccccccccccccccccccccccccccccccc8c8ccccc8c8ccccc8c8ccccc8c8000000000000000000000000000000011111111111111111111101011111010cccccccccccccccc8888888888888888c0c0c0c0c0c0c0c080808080808080833330000333300003333000033330000333300003333000032320000323200000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c08080c0c08080c0c08080c0c08080003333000033330000222200002222000033330000333300002222000022220000cccc0000cccc0000cccc0000cccc0000c0c00000c0c00000c0c00000c0c0000000000000000333333333333333300000000000000003333222233332222cccccccccccccccccccccccccccccccc44444040444440404444404044444040202020202020202030303030303030302020202020202020303020203030202ccccccccccccccccc0c0c0c0c0c0c0c0cccc8888cccc8888c0c08080c0c08083030303030303030303030303030303033333333333333333333303033333030ccccccccccccccccc8c8c8c8c8c8c8c8ccccccccccccccccc8c8c8c8c8c8c8c80000000000000000000000000000000333333333333333322222222222222220000cccc0000cccc0000c0c00000c0c00000cccc0000cccc0000c0c00000c0c3333333333333333000033330000333333333333333333330000222200002222
|0,4=>0xc0c0c0c0c0c0c0c0ccccccccccccccccc0c0c0c0c0c0c0c0c8c8c8c8c8c8c8c91111111111111111010101010101010111111111111111110101010101010100000444400004444000044440000444400004040000040400000404000004042222333322223333222232322222323222223333222233332222323222223232c0c0ccccc0c0ccccc0c0c8c8c0c0c8c8c0c0ccccc0c0ccccc0c0c8c8c0c0c8c8000000000000000000000000000000000003333000033330000222200002222ccccccccccccccccccccccccc0c0c0c0cccccccc88888888cccccccc808080800000000000000003333333333333333000000000000000030303030303030308888cccc8888cccc8888cccc8888cccc8888c8c88888c8c88888c8c88888c8c83030303030303030303020203030202030303030303030303030202030302024444444444444444444444444444444440404040404040404040404040404043333000033330000333300003333000033333333333333333333303033333030ccccccccccccccccc0c0c0c0c0c0c0c088888888888888888080808080808080303030303030303030303030303030302020202020202020202020202020202cccccccccccccccc0c0c0c0c0c0c0c0ccccccccccccccccc0808080808080808000333300003333000033330000333300003232000032320000323200003232
|0,5=>0xc8c8c8c8c8c8c8c8ccccccccccccccccc8c8c8c8c8c8c8c8ccccc8c8ccccc8c8000333300003333000032320000323200003333000033330000323200003232cccc0000cccc0000cccccccccccccccccccc0000cccc0000cccc8888cccc8888033003300330033003300330033003300330033003300330033003300000000ccccccccccccccccccccccccccccccccccccccccccccccccc8c8c8c8c8c8c8c8000000000000000333333333333333300000000000000002222222222222222ccccccccccccccccccccc8c8ccccc8c8ccccccccccccccccccccc8c8ccccc8c800000000000000033333333333333330000000000000000111110101111101000000000000000000000000000000000ccccccccccccccccc0c0c0c0c0c0c0c2222222222222222222222222222222233333333333333333333222233332222c0c0c0c0c0c0c0c0ccccccccccccccccc0c0c0c0c0c0c0c0ccccc0c0ccccc0c333333333333333303030303030303033333333333333333030302020303020200000000000000000000000000000000ccccccccccccccccccccc0c0ccccc0c3333333333333333333333333333333303030202030302020303020203030202c0c0ccccc0c0ccccc0c0ccccc0c0ccccc0c0c8c8c0c0c8c8c0c0c8c8c0c0c8cb333333333333333333333303333333033223322332233223322332033223320
|0,6=>0xcccccccccccccccc0000000000000000c8c8c8c8c8c8c8cb33333333333333333333333333333331111111111111111101010101010101000000000000000000000000000000000cccccccccccccccc0c0c08080c0c0808303030303030303030303030303030303030303030303030202020202020202cccccccccccccccccccccccccccccccccccccccccccccccccccc8888cccc8888000000000000000000000000000000033333333333333333232323232323232cccc0000cccc0000cccc0000cccc0000cccccccccccccccccccc8888cccc888800000003332333200000000333233320000000033323332000000003332333200000000000000000c0c0c0c0c0c0c0c000000000000000008080808080808080000000000000000000000000000000030303030303030303030202030302020c0c0c0c0c0c0c0c08080808080808080c0c0c0c0c0c0c0c08080808080808080000000000000000000000000000000333311113333111133331010333310100000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000c0c00000c0c00003333000033330000333300003333000022220000222200002222000022228888888888888888cccccccccccccccc8888888888888888c8c8c8c8c8c8c8c8000000000000000333333333333333300000000000000003333323233333232
|0,7=>0x444444444444444444444444444444444444000044440000444400004444000000033330000333300003333000033330000333300003333000033330000222200000000000000000000444400004444000000000000000000004040000040400000303000003030000030300000303000002020000020200000202000002020000000000000000000000000000000044444444444444444040404040404042222222222222222222222222222222233333333333333333232323232323232c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0ccccccccccccccccc8c8c8c8c8c8c8c8000000000000000000033330000333300000000000000000000323200003232cccc0000cccc0000cccc0c0ccccc0c0c88880000888800008888080888880808000000000000000333322223333222200000000000000003333222233332222cccccccccccccccccccccccccccccccc0000cccc0000cccc0000c0c00000c0c33333333333333333333333333333333333333333333333333333030333330300000000000000000cccccccccccccccc0000000000000000ccccc0c0ccccc0c333300003333000033330303333303033333000033330000333302023333020200000000000000000c0c00000c0c000044440000444400004c4c00004c4c0003333333333333333333333333333333333333333333333333333333322222222
|0,8=>0xcccc0000cccc0000cccc0000cccc0000ccccccccccccccccccccc8c8ccccc8cb333303033333030333333333333333333333030333330303333323233333232c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0ccccc0c0ccccc0c0c8c8c0c0c8cb33333333333333333333333333333333333333333333333333332323333323200000000000000000000000000000000cccccccccccccccccccc8888cccc888b3333333333333333333333333333333303033333030333330303232303032324444000044440000444444444444444444440000444400004444404044444040000111100001111000010100000101000001111000011110000101000001010c0c0ccccc0c0ccccc0c0ccccc0c0ccccc0c0ccccc0c0ccccc0c0c8c8c0c0c8cb333333333333333333333333333333300003333000033330000222200002222cccccccccccccccc4444444444444444cccccccccccccccc4444404044444040000000000000000111111111111111100000000000000001010101010101010ccccccccccccccccccc8ccc8ccc8ccc8ccccccccccccccccccc8ccc8ccc8ccc8000000033333333000000003332333200000000333333330000000033323332cccc0000cccc0000cccccccccccccccccccc0000cccc0000ccccc0c0ccccc0c3333333333333333333333333333333300000000333233320000000033323332
|0,9=>0x3333333233333332333333323333333233333332333333323333333233333332040404040404040404040404040404040404000004040000040400000404000111111111111111111110000111100001111111111111111111100001111000000000000000000000000000000000000cccc8888cccc8888cccc8888cccc8888303030303030303030303030303030303030000030300000303000003030000c4c4c4c4c4c4c4c4c4c4c4c4c4c4c4c4c4c4c0c0c4c4c0c0c4c4c0c0c4c4c0c333333333333333333333333333333333333333333333333333333333333000000cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc0000000333300003333000033330000333300003333000033330000222200002222
|_,_=>0
def sP:Nat→Nat
|0=>0xa042c2b1101050b24201101280b2c2b112a0a040718290d080b16070214280b20271814130b26021c00091a25180d17090b07020123090b220711100a1a07020121090b2011141f081e07180d08091a161d181c0d1a020c131b091a070e0119090f07180517080b16151114130b121101050b1211100a070601050403020100
|1=>0x180d36091a2025180c050f2c070214130b12071101051a07023314280b2f1d1101280b1d020c190a07060c05080b2618350d09043420110c130f2c071133050b201d1801280b1d111029080407112a13310b26183217090b11103130090403110c13170b2f271114130b072e0c0d0a042026181413040718052d080b07111029
|2=>0xb11140d31300f2c201133090f2f071101050b110105393a0b0718052d0a1a201d11331404023c0c05080b0718133b0a1a20251110140416070214130b2b1d181c0d040711101f080b07110129050b1110393a0a1a07020105391a2f25110c051a2c3811140d0b261d0e14130b26020c370a0f0702331413042c03020c131a07
|3=>0x2f07111405080b2026110c41090407110c0521080b2007181c13091a1d07112a0c130b2b1d111c0c0d1a0711010d40090b2f2711010d090b2025180c05080b1d0702010c281a201d18140d080b3f26110c13090b242b11100a0b121101050407020c3e080f070e01050b12110c05080b12110c0d0a1a2c1d0201050b1211100a
|4=>0x3301140d0b071110014a090f07112a140c134907111008090b1d11480d00080b070e0132090b07110c47130a0b07022a0128091a2f07111413090b0711194608090407021c140c130b26180d3b08091a2c1511010d091a1d070201140d0b1607110d450a0b07180d3608090b4407111013090b07111413430b20271101140d1a
|5=>0x7500c0d08090b2c3811140d081a07114f010d090b0711144c0508040307110c0d4e1a0711010d4d090b2f07111c05080b200318010d09042f2611010d090b1207110c05080b0711144c0d0a0b1207110c0d0a0b201d181c0d080b2f1d110c2808042c2b111008090407114b140d080b1d110c13170a0b261d1801050d0f0711
|6=>0x8090b2c26113305091a0711101c01050b2b07181405081a0718010d19090b2b0711101c090b07110c133b0a0b161d110d45081a07250e0c0d090b5520110c0508042b07112a0c080b07180d5408091a070e0105090b2b0718140d0a045307110c130d0b2f25110c05080b07180d520a081a0711510c13090420261101140d0b
|7=>0x2010d090b2c20114f08090b5907110c050a0b07020c5808090b0702011339090b1507180c130a1a201d110c28130b2b0718570d090b0702010539080b070201000a09042c20112a05081a1d07110c13420b0702010d390a1a2c2b11101309045607180c0d081a2007183301090424070e140d080b0718135208090407181317
|8=>0x32090b2c260214130904530711100d080f2c07010d5c090b1d02010008090407112a01130b2c27110d4e091a2c20112a08090b2c1d11105a080b2420182a08090b1d180517080b152618140d081a07020100090f07022a0c05080b07181c0113050b26070e0105090b2c20115b08090b2026180c050a0b2c11350d08090f2c07
|9=>0x1511140d081a07020c1339090b2f26110c050a0b2c2602570d090b1620110c050a0b5520111008090b07110c2905080b18140d1b08090b0311010d00090f071133140d1a07020c0539080b2c1d020c130a0b07110c290d0a0b0711102839080f2c2011140d081a1607181c0d090b591d110c0d0a0b1d111c0d00080b26070e0c
|10=>0x80b261d11100c280b20071133140a1a6007110c0d090b1620180113091a5f07110c0d091a0702010c19090b202718140d080b2c201101050a0b152611330c090b07110114053a1a07181413051a1d020c0008090b110c0d3130090b07110c052d0a0b07110c055e0a042c07113305080b2f0711145a080b5d0718140d080b16
|11=>0x140d080b201d113314081a1d07110c05650b5507020c05080b20261110140a046407110c0d080b162011100a090403110c0d17080b2607181413050f2007111001090b07110c1305630b07250e140d08042c2b11010d090407112a0d3b08042c07021413081a07111001620904202618140d0804590711140d080b2c1d11610d
|12=>0xb26070e1405080b4420110c13090b07180d6608090b161d1114130d0407025b0c050807060c0d080904202611330c090b2007110114280b24071110130a043420110c0d081a070e1405081a2b1d020c13090b1607111413050407022a0105080f2c0711330d091a53071101140d0b0711330539080407112a0d3108043f0718
|13=>0x546080b183c1c0d0809042c261101050d0b2026116a0c090b2c070201050a0b201d115b0c080b2c26112a0d0a0b2c6911100809042c26110d45080b27020c0008090f2f07110c05080407110c0d1f080b2c271101050d0b110c05393a080b110c0d393a0a0b261d11330c05070e011368090b2c2b110c050a1a0718010d6709
|14=>0x5080b12110c0d0a0f070e0c05080f530711010c0d0f200718010d091a3807180c0d090b1507111c0c130b261d110c0d6c042c20112a0804200311100c08042b0711010c050b2c20115713090f16071101140d04113c140c0d080b2026110114051a1507180c13090f071110010504071110053b080b6b071101140d0407110c
|15=>0x2c20111008090b242b110c0d0a1a201d180c05080b201d110c67080b113c0c0d08090b0711103d0a0b1d110c0d460a0b12110c0d08090b07111013390a0b1526020c28090407182a1c0d08042007181413080b181c0d1b08091a150718010d090b07021c0008090b2707111001050b261d0201140d0b1620111405080b12110c
|16=>0x11101c13090b2b3807110c0d090b2f26110c13090f2c070c0d5c08090b160711100508090b1620110c13090b07180c0d3a0a090b070e0c280508090b2c1d1101130d090407112a0c13080b071814130d0a0b2007116f0c0809042007180c05080b160711100d0a090b2c07110d6e08090b07110c0d6d08090b110c0d1b08090f
|17=>0x1305090b7207110c0d08090b380711100c08090b261d0e0c0d08090b1d071133140d080b5f07110c0d08090b110c0d71080904070201140d080b2c26110c280d090b260711101405080b0702010c190809700f07020c0809042026110c05080b07020c053b08090b07180c053a08090b26071110140d0a0b0718141305080b07
|18=>0x10c0d67090b071110142805080b270711330c0d090b07110c050d75080b7407110c050d080b1507111014080b260711010d460904071833010d08090b260711101413090b6007110c0d08090b747307110c0d09042607110c28050d042026110c13090b165307110c0d0a0b07110c0d6608090b03110c0d0008091a2c07110c
|19=>0x1a07110c0d7c08090b07117a0c0508090b2c20110113090b530718010d08090b26071110570d091a0711330c1305090b161d11100d08090b200711790c08090b07110c0d7808090b07110c130d75090b07020c05310809042007110c6508090b2007110c6c08090b071857130d090b07110c0d7708090b761d110c05081a0711
|20=>0xa090b0711140c053a080b24201d11100809043f07112a0c0d0804242011140c0d081a2c1d110c130d090b0718140d7f080b16070e010d08090b1d07020c2805080b200718480d08090b261d1110140d080b071110016208090f07110c0d7e08090b07110c0d7d08090b2b071101140d09042f07110c05081a2c1d110c050d08
|21=>0xb0711101c1413090b071801320d09070e0c0d8008090407113301140d080407112a140c13080b1d07110c0565080b2407020c2108090b07114b0c0d0a091a240711010d090f0718010d090b1d07110c0d650a0b2003110c13090b7307111c0c0d0904260711330c0d090b113c0c280d08090b16531d110c0d080b2b07020c13
|22=>0xe140d0a084907110c0d08091a2c0711100508091a2c20110c13090b2f0711480d08090b2c2b1101130d090b3807110c050d0a1a07110c0d5208090b53071101140d080b202611010c05090b4407110c130d090b160702010c13090b8107020c0d08091a2b07020c13090b1620111008090b270702140c0d080b070e0c5a0809
|23=>0x80904260702140c0d0804242611140c0d080b740711100d08090b0702140008090b162b07111008090f200711100c08090b030711330c0d09041607020c0d08090b071110145a080b1d07020c2813081a071801050d090f07112a0c0d08042c2b110c0d08090b1d07112a010d080b0711010c0d4a090b150702140c05080b07
|24=>0x170a080b07180c0d8608090b07110c0d850809042007111014080b07110c053a0a0b1d07115b0c0d080b1d07110c0d84081a2c1d11100d08091a07111c010c050d0b2b07111c0c0d090b2c15112a0d08090b1d07020c5a080b07020c1908090f071101140d1a1d0718010d090b26110c0d2108090b070e14130809070e0c0d82
|25=>0xb440711100d08090b0711140d43080b241d07020c05080b2007181c0d08090407182a140d080b26071801050d09070e0c056808090b0711480d0008090b2c2011100a08090b3f26110c0d08090b115b3c0c0d0809040711140d3108042c0702010d08090b240711101405080b0711870c0d08090b1d070e0c05080b07110c05
|26=>0xc1362080b07110c0d880a090b2c0711141305080b2c1d110c0d5a0804071133140d080b2b0702330c08090b1607110d4508090b1d110c0d170a081a07110c1317090b07180128050d090b2007112a0c0a081a2c20111008091a590711010c0d091a1d071101140d0b202611330c13090b5907020c1308090b2025180c0d0809
|27=>0x14130d081a0711140d0008090b07110c133b08090b2c071157130d091a0711101c010d090b2b0718140d08091a2007110c2813091a150711100c08090b5520110c0d08090b071133141305080b2f25110c0d08090b07110c280d39080b1207110c0d080904200711010c13090b2607180d4608090b1d110c131708090b071114
|28=>0x2c07112a0d080b1d07110c0d6e080b2c2611140d0a0b1507180c1308090b560711100c08090b2c07020c050a0804240702140c0d080b6b07180c0d08090b2b8b07110c05080b07118a0c0d080904030711100c0d081a0702010c05090b201d110c2108091a1d07110c0d42080b2c27110c050d080b07110c0d8908090b2c1d11
|29=>0x8090b261d02010c0d090b8c07110c0d08090b202611140c0d0a0b150711140c13080b1620110c0508090b2f26110c0d0a090f200711010c0d090b07110c290d08091a07020c0d3908090b2c2611570d090b2607111c0c050d0b162607111013090b201d110c28080b260702010c05090b1d180d1708090b2c1d112a050d0804
|30=>0x1140d0a0407112a0c280d080b3807180c0d08090b110c280d1b08090407115b140c0d080b2c20110c320809045607110c0d081a1d0711100c05080b27071101140d0b2c2011010508090b2407181c0d08090b2c1511100508090b07110c052d08090b07110c055e08090b07185b1c0d08090b07110c0d5e0a09042c0711330d
|31=>0x711100c05080b2c0702010508090f2f07110c0d08090b113c0c050d08090b8e07110c0d08090b110c0d393a08090b2c2b110c0508090b261d11330c0d090f2007180c0d08090b115b0c0d1b08090b07118d0c0d08090b2c69110c0d08091a070e140d08090b2c2011331308090b201d11100c0a080b2b201d110c05080b0702
|32=>0xd08090b110c050d1b08090b2c27020c0d08090b12110c0d08090f070e0c0d08090b2c20113308090b270711010c050d0b07180c0d9008090b8f07110c0d08090b07110c0d1b08091a2c1d020c0d08091a07180d1708090b2c0711102808090b0711331405080f07110c0d0008090b07110c052108090b0711331c0c05080b27
|33=>0x8090f0711140c0d081a1d07180c0d0809040711100c05080b1d07110c0d2108090b1d071101140d08070e0c0d6808090b07115b0c280d08090b2f27110c0d08090b0711011413050b110c0d1b08090b242b110c0d08090f070c0d9108090b07110c0d3d0a0b0711100d390a080b113c0c0d08090b07111001050a0b07115b0c
|34=>0x50d080b2607180c050d08090b2b1507110c0d08090b1607110c0d1908090b3f1d07110c0d08091a240711140c0d08090b590711330c0d08090b07110c0d3b08090b270711010c0d090b2b07110c0508090b742407110c0d0809040307110c0d080b2b07110c0d0a090b1d07110c0d45080b07110c131708090b590711010c0d
|35=>0x2010c0d0a090b2407111c0c0d08090b0711930c0d08090b1d07110c280d080b2007110c4208090b071110480d08090b2007112a140c08091a0711140c130d090b1507180c0d08090b0711101c010d08090b2b1d110c0d08090b162011010c0d080904260711010c0d090b2007110c281308090b07110c0d8808091a0711140c
|36=>0x390a080b0711100c2808090b5907110c0d08090b0711140c28050d080b5d07110c0d08090b260711140c130d090b2c1d020c0d08090f07020c0d08090b260711140c050d080b1607110c050d08091a0702010c0d090b07111c0c050d080b07110c0d3008090b20110c0d9408090b07180c28050d08090b2c07020c0508090b07
|37=>0x110c320d08090b2b2607180c0d08091a071133010c0d090b2027110c0d08090b1507110c130508090b0702330c1308090b24201d110c0d08090f2c07110c0d08091a07110c1305090b07180c0d5a08090b9507110c1308090b260702010c0d090b071133010c0508090b0711010c0d6208090b1507110c050d0a080b07110c0d
|38=>0xd0a08090b201d11100c080904200711140c0d080b26110c0d0008090b2c2011010d08090b1d0711100c0d0a080b2707180c0d08090b0711140c0d5a080407110c0d45080b26071110140d08090b07110c0d2d08090b07110c0d5e08090b2607110c050d0a042c0711140d080b1d07111c140c0d080b07180c0d9608090b2c07
|39=>0xd08090b2c07020c0d0a08090b0711790c0d08091a07020c13090b07116f0c0d08090b162607110c130d090b1507020c0508090b1d071110140d080b07110c053a08090b07110c0d170a08090b260711330c0d090407110c0d0008090b3807110c050d08090b2026110c13091a0711330c0d091a2c20110c0d08090b2c20110c
|40=>0xe0c0d08090b0711100c050a080b270711100c0d08090b0711330c280d08090b2c07110c280d08091a0702140c0d08091a200711100c08090b071101140d0a0b07110c130d8408090b202611140c0d08090b07180c280d08090f0711100c0d08091a07110c0d3908090b07115b0c050d08090b16260711100d08090b2c261114
|41=>0x7020c050809040711100c0d08090b0702140c0d08090b0711330c0d08090b07110c0d3108090b200711100c08090b2607110c130d090b7607110c0d08090b98070e0c0d08090b07110c0d3d08090b0711010c1305090b0711010c050d0a0b07115b0c0d08090b07110c0d8408090b261d110c0d0a0b07110c0d9708090b0783
|42=>0x140d08090b2c07110c0d0a08090b07110c0d0008090b2607180c0d08090b2f07110c0d08091a07180c0d08090b160711010c0d08090b2b2007110c0d08090b07110c28050d08090b1507110c0d08090b2607110c050d08091a1d07110c0d08090b07110c320d08090b2c1d110c0d08090f07110c0d08090b0711010c0d0a090b
|43=>0xb07110c0d08090b0711100c0d08090b0711010c0d08090b2c07110c0d08090b07020c0d08090b0711010c050d08090b261d110c0d08090b0711100c0d0a08090b071101
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x728025400a80005
|5,0=>0xc5b06158300a17a60ba305b982d0c16260ae3055982a0c14a60a2304f98270c1326096304998240c11a608a304398210c102607e303d981e0c0ea60723037981b0c0d35066b031d8182c0bb605ab02bd8152c0a3604eb025d8122c08b6042b01fd80f2c0736036b019d80c2c05b602ab013d8092c043601eb00dd8062c02b6012b007d8032c0136
|5,1=>0x1a760d128671832ea1916
|6,0=>0x1b138d6dc6a8e34d71a338cfdc670e3317195b0c91c63ae3167187b8c21c602e2fa7179b8bb1c5cae2de716bb8b41c592e2c2715db8ad1c55ae2a6714fb8a61c522e28a7141b89f1c4eae26e713430985c4b6c2547126b8919c47ee2387118b88a9c446e21c710ab8839c410c20170fd387cdc3d8e1e570ef3875dc3a0e1c970e1386edc368e1ad7
|6,1=>0x28f3945dca20e5097281393edc9e8e4ed72733937dc9b0e4d172653930dc97ac4b67257b92a1c942e49a7249b9231c90ae47e723bb91c1c8d2e462722e31155c89ce4477220390e98866e42d62133907dc830e41172053900dc7f8e3f571f738f9dc7c0e3d971e938f2dc788e3bd71db38ebdc750e3a171cd38e4dc718e38571bf38dddc6e0e3697
|6,2=>0x36d39b4dcd98e6c5735f39addcd60e6a9735139a6dcd28e68e6343b9a01ccf2e6727335b9991ccbae657632839925cc84e63b731ab18b9cc4ee620730cb9849cc16e60472feb97d9cbdee5e872f0b9769cba6e5cc72e2b96f9cb6ee5b072d4b9689cb36e59472c6b9619cafee57872b8b95a9cac6e55c72aab9539ca8ee540729cb94cd8a58e5257
|6,3=>0x2005cff4e7f373f639f95cfbce7d863e8b9f29cf86e7bc73dab9eb9cf4ee7a073ccb9e49cf16e78473bf31de18ee4c76b73b239d75ceace74f73a4b1d09ce76e7347396b9c99ce3ee718738931c2dce08e6fd737b39bbdcdd0e6e17
|7,0=>0x4f8427a5d3c309d984e8c2726138309b984d8c26a61343099984c93a62a1306e97b84b9c25ae12c7095b84aa3a5321289093c849a424b21249091d748ac2436120b08fd847ac23b611cb08dd846ac2339d18ee8bf845bc22be1150e8a1744cc224611130882743dba1ce10d8e864842e42155d09b0845841ec20d9d05ee82784103a062102108088
|7,1=>0x5efbaf5e179f0bc785dfc2ee1d7610ba975d13ae6a17250b8a85c142dedd6e8eb6c85b2bad7616ab0b4d85a2c2cf6166b0b2d8592c2c76162ceb0f7583c2c01d5f10af175753ab8a15b50ad2856542b0a1576eab56556c2a99d53d0a96854742a1a14fd0a7685374299a14bd0a568527ba91e147f0a378517c289e143f0a178507c2821d40109f88
|7,2=>0x6e6437121b790db486d6436921b390d9486c6436121af90d7486b6435921abaed5586a6c35161a7ced3686974349dda3f0d187688434221a010cf88678bb3a619c30cda76694332dd9870cbb8659c32ae1948ec9c864a43232190aec7d863ac31b618ccec5f762bc313e188f0c3f861bc30be1850ec21760db3051d8190c0575ff3afda17dd0be68
|7,3=>0x7e143eea1f650faa87d143e6ddf270f8b87c1c3df1dee90f6c87b243d721ea90f4d77a2c3cf9de6d0f2e879343c7a1e2d0f0e878343bfa1ded0eee877343b7a1dad0ece876343afa1d6d0eaf7753c3a7e1d30ee908744bba061cf4ee728735bb98e1cb70e538725c390e1c770e338715c3891dc390e148706438121bf90df486f6437921bb90dd48
|7,4=>0x10bf885c3c2c5e15310a2784dbc24e2118f085783ec41d620db1066782fbc161e0a110488820440e2206110297810c4069e025100a880143fea1fe50fea87f143f6a1fa50fca8
|8,0=>0x96844b1e657f12b8795844aa22541129799474ca1664fb12758936c499264b912539925c4911e47732329915bc88e2437121389054c80a23f511f198f4c478623b311d188e44c702237111af98d3c467a632d118d98c2c45f622e9316b98b14c56662a13147989fc44de225f1126988fbc45e221f1107887f4c3dde1df10e8786fcc35e21a0f0c79
|8,1=>0xa5d452ca295514a28a4d4524a2916f4838a3dc51ce28d534619a2c4d142289114417a1c4d0be684f141f8a0bc503a680b33fd89fa4cfb227ccd3de89eaccf36278b13bd89da4ceb22749139b99ca3ce35e70b137c99ba44db226c9135c89a9ccd2e2687133c7999cccae2647131b898a3cc2e660712fa9978ccba625c312d89
|9,0=>0x56566b1b15849abe455ce6ad715638aadc5551ea9735429a9ccd4c62a5135208a8c454422a12f5018a7d3d3ca29d514e28a6d4534a299514c28
|10,0=>0xadac56b62b4b159e7
|11,0=>0x15bd7
|_,_=>0
def wAt:=mkWire dB 153 254 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xd08430210d09480310b0841c350842414330d0942405080949825070842c21240d474310709424210c0d41cf50c0d420251413034210c0943035010942c21130944435130c42035200c41c350d0943c38111042c2908094343115010ac501d0841c25110c41c210d0842c25090c424210d14414212413058140701404250b0844431080c43c38090d430210b0a42421
|1=>0x80d41c35010d444310b08430210b0946035110c41c51090c42c210109434250c08404250c05444410d09434310b0843021310d41c06080c41c410c0d4b0350b0941c31080941c410c0d42c25260d41c21200cc1c350b0a42421090c420310b0a42d0d0d0c40414090d420310c08444411309c3431080d434e5071483025050844435050c42435110d44435010503025
|2=>0x110c42031160d4b021070c42441080d434310b09430211009430350b0841c31140d44431071442431200cc3425110c41c350709430212c0dc2c21110d41c310b0a42025110d42435110c404250c0843425280c414210d0944431070d45404200941c350c5a414230d0941ccd130c42035070543425110c42c21130941c250d0841c31050c42c250d0942c21071341c31
|3=>0x80d42c251110424310c0d42c210d0944435070942c210713434210b0944435050c42031090d43035070941c4d0b09420350b0944431090c42c25070841c35160d41c050c0841c35110c41c05080c404350c0942c21080d43025110c42435170848033070d48031070d494311d08c1c252b14098350708420410c0942c290809430352b1409835070841c05010942c21
|4=>0x908468251609c44310b0a42421080c404251009430350b0941c35070c41c35090c468250b0841c050c0848025070d44431090d430210b0a424210c0d41ca10508434250708430210b09424350d1c42831080945035073244c270d0841c211605098310708430350c08434210e0bc44410d0c424311110430350d0941d5d0109c20310f0e044410b0a420250d0c4304d
|5=>0x90d43015090d42c250d0842035080944431090c420aa140d42431110c41c350b0943425094e40437080c41c310b0a41c35080944431090d42c2107094303508094504c0d08430250d0844435050841c150d0945021140d444310b0943025110c434210b0941c35090c474210709444350d0941cf51413034210c0941cf508094504c0d08430250b0a42435111043035
|6=>0x111041c210709434310d0c41d0f0105034250c0844435090c42c250c08424210d0943431070843025160dc44350701444350f0d42c290809424350b0941c21070d45433110d41c15090d41c4e110c42035080d43025110c424350d08430350109430211508c8021200941c350710420350708430350f11c2c2908094b021070d41c31080d41c4e110c42035111043431
|7=>0x110d42031130cc2c250d084a0330d0a42421090183021110c420350531c34250701830210709434252008c1c350c0d43025050843425070a42025310941c060c0845825260c41c211d0d424310709434312b0cc9835070842c25110c420312408c9021071443025080542c25070843425080d42c25070841c351609c1c050c0841c31080d42c210d09454231d0d41c25
|8=>0x71342421110d42035090c474310709430350b0945035090c41c350b0941c510c09420350b0841c25070c43025110c47437070946035110c41c05080c41421070944435090d41c351408c4431090c420310710430350b09434250b085ec35050182031090d43421070c41c35080c45827110c41c05080c4304d080d42c210d09430c91309c3421093141c06080c41c06
|9=>0xb0844435071342035260c41c35070843035110d41c290809444410508c3431090d450210d0843025091383021110c4203568094382f111043431090c42c250c0842c25140d42035090c41c25240dc1c51110d424310c3a41c4e0d0841c51080c42c210c0942c29090844431080c41c25080d49827070841c352408c5021071443025010d42c250c0845827070143021
|10=>0xb0944435080c41423090d43035090c44c25110d41c250d08430210b0844431090d42c29090841431090d480210b0941c351d1381c250d0841c150d0944435090c42431111043431090842d0d010502435080c42c210d0842c21070d41c31071341c31080d45423070543425170948033070d458270701430210757404270c0841c050d0844435080c41d211408c2431
|11=>0xc09434210b0841c250b08404250d0943021140841c31050c41c15090d41c250508c4435090d45837070144435080c46825080c42c210c09444310b0841c250c08490370714430251110424310d0c420350b8383821111043431110d42c25070843025070842c25071443025071c450210c094b037070c44435090c43431260c498350708434310b0a41c35080941c05
|12=>0x501030250d09430211d0c41c25110d42435140844431070d42431140d444310b0943025090d41c21110c420310d094382f1110434310c0d41c35070c42025201441c35090c41c06090c42c250c0841c31110d42c250c0843431090d41c51090c41ca2050843425111042435070943035200cc1c35070d434310b09430250d0941c4e080943421330940435080c44c52
|13=>0xb0843021200844431070d44c25070d42c210d0841c150b0843425250c47423070944c31080d424310b09444312b0cc9835200181c35080c41c310d01424310b0943021110d44c31071342035200cc1c35200cc1c350b0843421110c414210c08434250c0d42c21070d41c310709420310b0843025070d4304d070843421110d420351d08c4431070941d5d0109c3021
|14=>0x200cc4431070d41c25050c41c31090d414310b0941c31090d42539010dc2031090c41c21070c42421200941c35110c40c352609c1c21070c42025110d42435110d42c25071443025270d41c2908094ac270713434210b09498270708434310d0942c21110d42031240dc74310709414330b08434250c0941c310709434212c0dc1c310b08454331d0d41c25010943431
|15=>0xb09434251508c1c15090d41c310b0940c352609c1c210b0841c250c0942031070a42025110c45021071443025070541c31090d45c21200cc1c35073380435080c40425110c42031073380435080c404350b0943021110d4b035070c42c29090841c35080c4ac50260d41c210c0941c21090181c31080c498310708430350a0d41c25070d42025080c44435070843425
|16=>0x80943431010d41c31070d420310b0844435070c41c25200cc2c21110c41c35050840435090c42031090d4fc372c0541c31090d40425010d42435080c47421070943021110d41c31090d41d6c010543021010d444310b0a41c3508094cc25010d42031073244c270d08444410d0c42c210c0944c31070c42035090d48021070941c350c0942421110d42031050c42015
|17=>0x200cc1c35080d48005070d420311a0942c210c09444310b0841c250c0d42c250d09490371d0c41c250c0941c250c084382f111043431050843425070a424210c09434210c0843425075b8cc25010d42031119283c1d0b0a4202508094504c0d0843025075b0cc25010d420310c0843431090843425075b804150c0847421110d41c25073d4504c0d0843025111042c29
|18=>0x80d42c210c0941c15110c42435010943035080c41c4d070943421070141c35080c41c210b0943021091341c35080d48006070d42031090d42c210c0944431070843425200948021070d458370701420311d1041c250d0c42c21071443025010d42031150cc1c15090d42031070a42025260d41c210d0941c510c09498270b0941c21200841c35090843452070943025
|19=>0xd094bc210710434310c09414210d0941d690508c34250d0841c210c0944435070c41c25110d42c29080943025070843425260c41c210d0942c21110d42031090d404250c0858821070583425070d47433070941421110c42435110d41c31090d42421110d42031140841c510c095fc311d0dc1c25130941c250d0841433070d424351408c3035090c45035070d42431
|20=>0x10d42031080941c210d0941c310b0943025140841c250c0944431260dc1c21091381c31080d49835110c41c21010d42c210c0841c35070a424210d0841c150d094304d110d420351d0c41c35070942c29070c42025080d42c210d0941423110c424350d0848027070d41c21110d42031010d42435080c43021070583425090841c150d0941c520908430250d0c41421
|21=>0x110d41c15090d424310709434310d0941c4e0d0848033070d42025081041c210c0d4b0370b0941c311508c1c150d0943421070841c35010d42c210c0842c21070d41c31070d41c31080941c350709430350b0941c35090c4b037070c41c21070c41c35080c42421070943431110c41c290809430250508c3425140dc2c250c0943431070843025170848033070d41cce
|22=>0x709434310e08444410d0c434310908434250d0c41c2908094304d130943421080541c31090d42c21110d424310b0841c350d0c43025080943021131483025070d41c210c0941421110c424350b0a420250d0c41c520b08430250105434250c0849831070843431070c41c210c0944435070c420250c3244c270d0842c21110d420352a08c5035090c49831070843421
|23=>0x110c41c210710434310b0844431070143021200841c350508434250705434250708434250b0841c251309c3421070941c310b0a42025080943021110d424350b0943431110d42431010d42031070183021070d434310708434212008c1c350e07444410d0c4504c0d08430250d08430210d0943425080943021330940435080c44c520c0943421070941c21080947443
|24=>0xd0c43021070c444350d0943021070841c250809434310c0943021070c420252c0dc1c31
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x28000
|5,0=>0x13b000000000000000000004c200000000000000009440000000000000000000000000000000000000000000000000000040a0788000018602e20000000000002c2000000000000000050800000f50000000000000e101a200000608000000000000588000000002840000055000000000000000
|5,1=>0x1690000
|6,0=>0x1c0400000000000000037880000d4a000000000000000000000000000000000033980000000194800006230000000000006110be4170c00005a20000159000005510a0a000025a8483088800000000431000000002108000000000001ea800007460dcc000036100000d4400003320000000019082f3
|6,1=>0x1a6600000000000000000000000d12000000006718cb3000000006328000000030cc000000017ca2ecc000000000000000000000016ca00005998b2115c82a540000a4514082710000099312e4250c000091311c6000000008b310e8000000000001068000000007f400001e943aa80000000000038a0000
|6,2=>0x236646848b991610000000089980000000000089090d50000000084a10630000000000010151fc6000000000001f2a3d140000ef500000000000000000003b8476880000000000000000000000000000000001d46000074880001c8a384c0000000000000006ea0000000000000000dc11b6235940000000
|6,3=>0xb4a00002ca80000000160500000000af895b42aca54540000000000053c8a708000292a51149fa93d2272800009c08000266a0000000132125aa000000012a324aa00009118000000047900000000
|7,0=>0x426883d105a000040e80001021800040267f8cfd99f833e887c10f6200003d087988f199e033b88764ceb1800000007490e721ca438e600000001c340000700cde21bb100006dd0d9a1b2135c86accd3a1a3433e8670c000198432886410c62189300006150c1197f300005ed0bba17432e080000b698000
|7,1=>0x5928b15160a000057a8ae515aa2b1455a8aa8c0002a735468a7d14da29a152c80001499a90351a6a28c00028735068a00d3e227844ea69c51371a6a44cc898cd2fa25e14b4895cd29a24f449c2929123224330000900d1e223b147068d4d18a22d44528895110a21d4000087040000000000086110b88000
|7,2=>0x6ee8dd0db89b6e30000000000036d16d46000000036730000d985b1235e40000d709ac235440000d41000034c46908d189a19b4036788ce119a233046588ca100003244642600018ea319462a8c48d87230c20000000184230446026bf8d7e12f845ee2bcd177a2eb45ce8b8d1701adc45b08b5116822cd3
|7,3=>0x836305d20a1800082270352051800080c90091ff23fb300000001fd0bf647e84fc100003ec47d26f98df19be037ba6f68dec88000000000000003d727a68f3d00003cb40000f20de223c047788ee4ddaa3b2375c8eacdd41ba447408e74dcd1800072c8e491c79b8c300000001c42385370460001bf237b3
|7,4=>0x46428c09171000045848a88000228244c40001124e231c42487c90e900000000000000021b2432486230b50000429484a908ca0fa0000838600000000000
|8,0=>0xa407474e8d1d173a287444e871d0b3a107414e811cff39f873e4e7b1cf339e073b4e751ce739c87384e6f1cdb39b07354e691ccf39987324e631cc3398072f4e5d1cb7396872c4e571cab39507294e511c9f39387264e4b1c9429227238e459c89290c720ce401c7d38f471dce3a1c7138dc71ace341c662
|8,1=>0xba67740ee69dca3b8e7710ee09dbe3b7676e0eda9db23b5e76b0ed49da63b485684ecf1d9b3b307654ec91d8f3b187624ec31d833b0075f4ebd1d773ae875c4eb71d6b3ad07594eb11d5f3ab87564eab1d533aa07534ea51d473a887504e9f1d3b3a7074d4e991d2f3a5874a4e931d233
|9,0=>0x1828b0416062c085808b0015fe2bf857e8afc15f62be857c8af815ee2bd857a8af415e62bc85788af015de2bb85768aec15d62
|10,0=>0xc1e38387068e0c1
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 15
def pmP:Nat→Nat
|0=>0x22400000000004404000000000800000000000088000000000010000000000001c0000000000031000000000006000000000000a000000000001100000000000210000000000041000000000008000000000000b00000000000140000000000026000000000004800000000000880000000000100000000000018000000000002800000000000440000000000080000000000008000000000000c000000000001000000000000108000000000020000000000002000000000000380000000000008000000000000
|1=>0x144600000000028804000000004a008000000008a000000000010ce00000000021980000000004310800000000843000000000108400000000021000000000004100000000000814000000000100a000000000201000000000040100000000008000000000000cc2200000000120000000000023000000000004400000000000858000000000109c000000000213000000000042400000000008420000000001038000000000204000000000040000000000007002000000000a884000000000a300000000001260
|2=>0x114fd20000000229ea400000004533180000000805a2000000010000400000001899b0000000017264000000002be210000000054dc600000000a99a400000001533080000000286600000000050200000000008210000000001002000000000200000000000036ec20000000060838000000006b30800000000c86100000000189c000000000308c0000000005f30800000000b6610000000016460000000002b9c0000000005714800000000a6aa0000000014cd20000000029984000000005310800000000a261
|3=>0x8104e0000000100500000000020082000000004004000000000800400000000100010000000020000000000002b83210000000554c420000000a299840000001257510000000230150000000045484400000008a0400000000114000800000022126000000004400800000000869dc400000010c39480000002113710000000416c42000000082b904000000105651000000020a6690000000414cc200000008010c0000000100000000000010a08a0000000194f54000000032922800000004c317000000008b371
|4=>0x140784200000028000800000004453b480000008844e20000001100bc400000020ab88400000041533080000008238010000001032a420000002040484000000405754800000080ae610000001014cc2000000200888400000040089000000008008200000001000080000000200008000000040000000000004aa6610000000914ec20000001209924000000217420800000042aee3000000085144000000010a228000000021400000000004200400000000817042000000102b88400000020533080000004088a0
|5=>0x80100800000010009900000002000200000000400020000000080000c00000010000080000002000008000000240a480000000303cc8200000060289a4000000c008100000001800400000000281ccc20000005000800000000817630800000102e661000000203c8c200000040689840000008073318000001008061000000200088000000040000000000007100000000000c2a6210000001816802000000302c1400000006012510000000c0162000000018024c0000000282b9840000005053308000000a0a621
|6=>0x20022ea2000004002d9c4000008005638800001000ac6000000200150e200000400299c4000008005330800001000246000000200040000000040000840000008000100000001000004000000100b07100000016039804000002c05818800000580a661000000b0044620000016004980000002c001300000005800060000000b0000400000014839904000002903400800000500040000000088144c200000108009800000020400a0000000402a6790000008034ec2000001002b984000002005338800000400a661
|7=>0x804346c60000100029984000020000828000002010262a0000040094454000005300804000000a405138800001408a3710000028016ce2000005002c844000008a07338800001140e46100000228158c200000450299c4000008a05230800001140a44100000228108c0000004500098000000881e030800001048037100000209006c2000004102898400000820022000000104004000000020404cc2000004022cdc40000080450b180000100307730000020054cd200000400899c40000080101200000010020200
|8=>0x40011cdc600008002399840001000073308000200008000000040000ece2000080001c188000100000030000010042ec610000200857c4200004010ab984000080215430800010042a461000020085188000004010a28800000802140300000100400c400000200054cc200004000208000000800000000000080a182410000101415c4200002028230800000405045200000080800c20000010001800000002000209000000400020008000080000001000008105684200001020a988400002011c1908000040230371
|9=>0x8800130cc20010020261fa400200004c3308001408a987610002810530ec20001020265d84000108015331800021002a661000042005088000008400a018000010801192080002100080600000420006ce20000810a21104000102104120000020420062000004084004c0000081080088000010200733880002040026790000408002040000080403bb8c000100807730800020100ee41000040201d8c200008040399840001008035208000200a84641000040141cc820000800820000000100101b308000200200020
|10=>0x2110000025337200000421a6712000000914cd238400001299a81080140253f7810000003b7610100010084f54010000402018402000010d1b0802000002a6a800208101b0f5400410203610040040e000533080081c00002000010200000c4000202020000800040200000100008000c8a7610010001904ec2002000302d9840040006059308008000c087000010001014944002000102d9a4004000205330800800000a6710010000014cc20020000000140003e0004c21480044008987e3
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x400
|5,0=>0x18000000046000000000001200000000000c00000000000000000000000000000000c06c004e0180000000180000000007400070000000031200006000000006000000c0016000000000
|6,0=>0x9800120000000001b000000814000012c00000b000000b04c000000000000038800165003b5c00c506a3800061709c00060980000303d000000028800007b0023c0e00048011c000000c00000000048002e00000000000000000000026000006c00300000000030d834001b0423800501e80170301a824001c0000048000000124000981800030000c001d000200630
|6,1=>0x1c0003800008300000ca32188d000000007448001f089a6aa0200006003a000008d5580000300f0001a00000a00000030901a65000005800000004864000000c04000000061030000000311f0005300000000000090f2000000000000000000000680014001884c0000000011c000000000243c96c0000
|7,0=>0x5f0401e000ac0d089b3c034000d709d4720a76001651c182f400046601114d108d513ca57e244e4795d04e65403cbc2080600321d2799581a402d8d2ee22660014000000037c060002be97e00a40000c000204c1606a383db6004387408049a9ec3e0000414a4af5a000001a000346c2400104da03102f282ed6a84c00734f805ec0d0033c268500404d206720000c00
|7,1=>0x120380c000698cfa00779161c0d00434f3560ec9400327004c274d0982c4a0000000001b070bc00d2002d512126c1be0006648c01a3c8c835d00056179740600000541718002101388034087e0000000036a0000013001412e0f0006dd68000180012451ae40804504b870ff1355c004718002183497834b41b00000d915030183a9001840b2409e27060447d8ae4404
|7,2=>0x1d549040152410008498000101a41a9a9800000000030e501a9c00050c8746600020000000
|8,0=>0xad205509aa899e531dae9609b4f1d97dcca202129113a3b5399cca23516b6fe66b8e43146e52587347ad2df03f999b98ef9264aa055510b6686b1ae4255a7f775324f37a34c27e8c2bb756ca42a4d8d517a2448aa29964f8203a4ec2e1f1b433112b068ec61c46b3822e730a7a3356f13499dc963765bf66342214a1e307573cdceea6b4ee3f586348eb350
|9,0=>0x2664c4950b0980ad7b975a0f28b4e1611e40cb67a942b13cd14a49b7966da
|10,0=>0x2424d8243
|11,0=>0x42
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 51 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_245 10 roots_245 ops++addP pm 1 dom_241 8 roots_241 ops++addP pm 2 dom_208 4 roots_208 ops++addP pm 3 dom_244 8 roots_244 ops++addP pm 4 dom_232 5 roots_232 ops++addP pm 5 dom_252 9 roots_252 ops++addP pm 6 dom_237 9 roots_237 ops++addP pm 7 dzo_53_8 5 roots_53 ops++addP pm 8 dzo_216_32 5 roots_216 ops++addP pm 9 dom_249 9 roots_249 ops++addP pm 10 dom_125 9 roots_125 ops++addP pm 11 dom_61 7 roots_61 ops++addP pm 12 dom_248 7 roots_248 ops++addP pm 13 dom_221 10 roots_221 ops++addP pm 14 dom_45 5 roots_45 ops++addP pm 15 dom_189 9 roots_189 ops++addP pm 16 dom_93 8 roots_93 ops++addP pm 17 dom_124 6 roots_124 ops++addP pm 18 dzo_117_8 6 roots_117 ops++addP pm 19 dom_157 8 roots_157 ops++addP pm 20 dzo_149_8 5 roots_149 ops++addP pm 21 dom_121 6 roots_121 ops++addP pm 22 dom_188 6 roots_188 ops++addP pm 23 dom_185 6 roots_185 ops++addP pm 24 dom_173 6 roots_173 ops++addP pm 25 dom_113 5 roots_113 ops++addP pm 26 dom_233 6 roots_233 ops++addP pm 27 dzo_220_32 6 roots_220 ops++addP pm 28 dom_236 6 roots_236 ops++addP pm 29 dzo_213_8 6 roots_213 ops++addP pm 30 dom_120 4 roots_120 ops++addP pm 31 dom_57 4 roots_57 ops++addP pm 32 dom_60 4 roots_60 ops++addP pm 33 dom_109 6 roots_109 ops++addP pm 34 dzo_217_32 6 roots_217 ops++addP pm 35 dom_156 5 roots_156 ops++addP pm 36 dzo_221_32 7 roots_221 ops++addP pm 37 dom_92 5 roots_92 ops++addP pm 38 dom_21 4 roots_21 ops++addP pm 39 dom_184 4 roots_184 ops++addP pm 40 dzo_181_8 6 roots_181 ops++addP pm 41 dom_177 5 roots_177 ops++addP pm 42 dom_220 8 roots_220 ops++addP pm 43 dzo_85_8 5 roots_85 ops++addP pm 44 dom_217 8 roots_217 ops++addP pm 45 dzo_245_8 7 roots_245 ops++addP pm 46 dom_225 5 roots_225 ops++addP pm 47 dom_228 5 roots_228 ops++addP pm 48 dom_213 9 roots_213 ops++addP pm 49 dom_205 8 roots_205 ops++addP pm 50 dom_180 5 roots_180 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_253 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45|h46|h47|h48|h49|h50
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_237 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_53_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_216_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_221 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_189 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_117_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_zo_149_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_188 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_zo_220_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_zo_213_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_120 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_60 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_zo_217_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_156 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_zo_221_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_92 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_184 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_zo_181_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_177 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_zo_85_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h45;exact cpcs (by decide +kernel) lowS_zo_245_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h46;exact cpcs (by decide +kernel) lowS_225 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h47;exact cpcs (by decide +kernel) lowS_228 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h48;exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h49;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h50;exact cpcs (by decide +kernel) lowS_180 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_245 10 s (0,roots_245.map (·&&&dom_245)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_253 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_245 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xffffffffffffffff0000000000000000,64),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_253==dom_253)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_253 gM v ys):RunD true dom_253 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_253 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 69 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 69 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 235 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 107 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 235 → Z 6 i = true := (range_split z6_0 z6_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 256 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_256 : ∀ i, 256 ≤ i → i < 289 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 33 256 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 289 → Z 7 i = true := (range_split z7_0 (range_split z7_128 z7_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 124 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 124 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 27 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 27 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 4 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_253 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def isoMvS_191:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_191:Lower true dom_191 roots_191 goal_191 12:=lower_iso_b isoMvS_191 (by decide +kernel) lowS_127
def isoMvS_254:List (Nat×Nat):=[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_254:Lower true dom_254 roots_254 goal_254 12:=lower_iso_b isoMvS_254 (by decide +kernel) lowS_251
namespace S_255
def pG:List (Nat×Nat):=[(1,5),(1,17),(1,33),(1,65),(1,129),(2,10),(2,18),(2,34),(2,66),(2,130),(3,7),(3,11),(3,19),(3,35),(3,67),(3,131),(4,5),(4,20),(4,36),(4,68),(4,132),(6,7),(6,14),(6,22),(6,38),(6,70),(6,134),(8,10),(8,40),(8,72),(8,136),(9,11),(9,13),(9,25),(9,41),(9,73),(9,137),(12,13),(12,14),(12,28),(12,44),(12,76),(12,140),(16,17),(16,18),(16,20),(16,80),(16,144),(24,25),(24,26),(24,28),(24,56),(24,88),(24,152),(32,33),(32,34),(32,36),(32,40),(48,49),(48,50),(48,52),(48,56),(48,112),(48,176),(64,65),(64,66),(64,68),(64,72),(64,80),(64,192),(96,97),(96,98),(96,100),(96,104),(96,112),(96,224),(128,129),(128,130),(128,132),(128,136),(128,144),(128,192),(160,161),(160,162),(160,164),(160,168),(160,176),(160,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffffffffffffffff
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
|0=>0xff00
|_=>0
def pmB:Nat→Nat→Nat
|13,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 1 (j%128);fld (pmP (k/32)) 8 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_254 12 roots_254 ops++addP pm 1 dom_191 12 roots_191 ops++addP pm 2 dom_253 12 roots_253 ops++addP pm 3 dom_251 12 roots_251 ops++addP pm 4 dom_247 12 roots_247 ops++addP pm 5 dom_239 12 roots_239 ops++addP pm 6 dom_223 12 roots_223 ops++addP pm 7 dom_127 12 roots_127 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_255 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_191 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_247 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_223 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_127 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_254 12 s (0,roots_254.map (·&&&dom_254)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_254 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xffffffffffffffff0000000000000000,64),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
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
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [6, 7] }, { op := GateOp.or, inputs := [5, 8] }, { op := GateOp.or, inputs := [0, 1] }, { op := GateOp.or, inputs := [10, 2] }, { op := GateOp.or, inputs := [4, 9] }, { op := GateOp.and, inputs := [11, 12] }, { op := GateOp.or, inputs := [1, 9] }, { op := GateOp.and, inputs := [3, 14] }, { op := GateOp.and, inputs := [4, 8] }, { op := GateOp.and, inputs := [7, 6] }, { op := GateOp.and, inputs := [2, 0] }, { op := GateOp.or, inputs := [13, 15] }, { op := GateOp.or, inputs := [19, 16] }, { op := GateOp.or, inputs := [20, 17] }, { op := GateOp.or, inputs := [21, 18] }]

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 22⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
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

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_53032_aux

theorem PEqualNP.Outside.L_meta_53032 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_53032_aux.main
