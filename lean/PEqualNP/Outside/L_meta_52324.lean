import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_52324_aux
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

def dom_43 : Nat := 0xf0f00000f0f
def goal_43 : Nat := 0xffccffccaa00aa00ffccffccaa00aa00ffccffccaa00aa00ffccffccaa00aa00
def roots_43 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_45 : Nat := 0x333300003333
def goal_45 : Nat := 0xfff0fff0aa00aa00fff0fff0aa00aa00fff0fff0aa00aa00fff0fff0aa00aa00
def roots_45 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_47 : Nat := 0xffff0000ffff
def goal_47 : Nat := 0xfffcfffcaa00aa00fffcfffcaa00aa00fffcfffcaa00aa00fffcfffcaa00aa00
def roots_47 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_51 : Nat := 0xf000f000f000f
def goal_51 : Nat := 0xeeeecccceeee0000eeeecccceeee0000eeeecccceeee0000eeeecccceeee0000
def roots_51 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_57 : Nat := 0x303030303030303
def goal_57 : Nat := 0xffaaff00aaaaaa00ffaaff00aaaaaa00ffaaff00aaaaaa00ffaaff00aaaaaa00
def roots_57 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_58 : Nat := 0x505050505050505
def goal_58 : Nat := 0xffccffcccccc0000ffccffcccccc0000ffccffcccccc0000ffccffcccccc0000
def roots_58 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xffeeffcceeeeaa00ffeeffcceeeeaa00ffeeffcceeeeaa00ffeeffcceeeeaa00
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_62 : Nat := 0x5555555555555555
def goal_62 : Nat := 0xfffcfffccccc0000fffcfffccccc0000fffcfffccccc0000fffcfffccccc0000
def roots_62 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfffefffceeeeaa00fffefffceeeeaa00fffefffceeeeaa00fffefffceeeeaa00
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_73 : Nat := 0x3030000000000000303
def goal_73 : Nat := 0xffaaffaaffaaffaaaa00aa00aa00aa00ffaaffaaffaaffaaaa00aa00aa00aa00
def roots_73 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_75 : Nat := 0xf0f0000000000000f0f
def goal_75 : Nat := 0xffeeffeeffeeffeeaa00aa00aa00aa00ffeeffeeffeeffeeaa00aa00aa00aa00
def roots_75 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_77 : Nat := 0x33330000000000003333
def goal_77 : Nat := 0xfffafffafffafffaaa00aa00aa00aa00fffafffafffafffaaa00aa00aa00aa00
def roots_77 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_79 : Nat := 0xffff000000000000ffff
def goal_79 : Nat := 0xfffefffefffefffeaa00aa00aa00aa00fffefffefffefffeaa00aa00aa00aa00
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

def dom_85 : Nat := 0x3300330000000000330033
def goal_85 : Nat := 0xfffffafafffffafaaaaa0000aaaa0000fffffafafffffafaaaaa0000aaaa0000
def roots_85 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_86 : Nat := 0x5500550000000000550055
def goal_86 : Nat := 0xfffffcfcfffffcfccccc0000cccc0000fffffcfcfffffcfccccc0000cccc0000
def roots_86 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_87 : Nat := 0xff00ff0000000000ff00ff
def goal_87 : Nat := 0xfffffefefffffefeeeee0000eeee0000fffffefefffffefeeeee0000eeee0000
def roots_87 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_89 : Nat := 0x30303030000000003030303
def goal_89 : Nat := 0xffffffaaffffffaaaaaaaa00aaaaaa00ffffffaaffffffaaaaaaaa00aaaaaa00
def roots_89 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_90 : Nat := 0x50505050000000005050505
def goal_90 : Nat := 0xffffffccffffffcccccc0000cccc0000ffffffccffffffcccccc0000cccc0000
def roots_90 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f
def goal_91 : Nat := 0xffffffeeffffffeeeeeeaa00eeeeaa00ffffffeeffffffeeeeeeaa00eeeeaa00
def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_93 : Nat := 0x333333330000000033333333
def goal_93 : Nat := 0xfffffffafffffffaaaaaaa00aaaaaa00fffffffafffffffaaaaaaa00aaaaaa00
def roots_93 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_94 : Nat := 0x555555550000000055555555
def goal_94 : Nat := 0xfffffffcfffffffccccc0000cccc0000fffffffcfffffffccccc0000cccc0000
def roots_94 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_95 : Nat := 0xffffffff00000000ffffffff
def goal_95 : Nat := 0xfffffffefffffffeeeeeaa00eeeeaa00fffffffefffffffeeeeeaa00eeeeaa00
def roots_95 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_98 : Nat := 0x5000000050000000500000005
def goal_98 : Nat := 0xffffffffcccccccccccccccc00000000ffffffffcccccccccccccccc00000000
def roots_98 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_99 : Nat := 0xf0000000f0000000f0000000f
def goal_99 : Nat := 0xffffffffeeeeeeeecccccccc00000000ffffffffeeeeeeeecccccccc00000000
def roots_99 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_100 : Nat := 0x11000000110000001100000011
def goal_100 : Nat := 0xfffffffff0f0f0f0f0f0f0f000000000fffffffff0f0f0f0f0f0f0f000000000
def roots_100 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_101 : Nat := 0x33000000330000003300000033
def goal_101 : Nat := 0xfffffffffafafafaf0f0f0f000000000fffffffffafafafaf0f0f0f000000000
def roots_101 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_104 : Nat := 0x101000001010000010100000101
def goal_104 : Nat := 0xffffffffff00ff00ff00ff0000000000ffffffffff00ff00ff00ff0000000000
def roots_104 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_105 : Nat := 0x303000003030000030300000303
def goal_105 : Nat := 0xffffffffffaaffaaff00ff00aa00aa00ffffffffffaaffaaff00ff00aa00aa00
def roots_105 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_106 : Nat := 0x505000005050000050500000505
def goal_106 : Nat := 0xffffffffffccffccffccffcc00000000ffffffffffccffccffccffcc00000000
def roots_106 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffffffffffeeffeeffccffccaa00aa00ffffffffffeeffeeffccffccaa00aa00
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_108 : Nat := 0x1111000011110000111100001111
def goal_108 : Nat := 0xfffffffffff0fff0fff0fff000000000fffffffffff0fff0fff0fff000000000
def roots_108 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_109 : Nat := 0x3333000033330000333300003333
def goal_109 : Nat := 0xfffffffffffafffafff0fff0aa00aa00fffffffffffafffafff0fff0aa00aa00
def roots_109 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_110 : Nat := 0x5555000055550000555500005555
def goal_110 : Nat := 0xfffffffffffcfffcfffcfffc00000000fffffffffffcfffcfffcfffc00000000
def roots_110 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xfffffffffffefffefffcfffcaa00aa00fffffffffffefffefffcfffcaa00aa00
def roots_111 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_113 : Nat := 0x30003000300030003000300030003
def goal_113 : Nat := 0xffffffffffffaaaaaaaa0000aaaa0000ffffffffffffaaaaaaaa0000aaaa0000
def roots_113 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_114 : Nat := 0x50005000500050005000500050005
def goal_114 : Nat := 0xffffffffffffcccccccccccccccc0000ffffffffffffcccccccccccccccc0000
def roots_114 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def goal_115 : Nat := 0xffffffffffffeeeeeeeecccceeee0000ffffffffffffeeeeeeeecccceeee0000
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_116 : Nat := 0x110011001100110011001100110011
def goal_116 : Nat := 0xfffffffffffff0f0f0f0f0f000000000fffffffffffff0f0f0f0f0f000000000
def roots_116 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_117 : Nat := 0x330033003300330033003300330033
def goal_117 : Nat := 0xfffffffffffffafafafaf0f0aaaa0000fffffffffffffafafafaf0f0aaaa0000
def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xfffffffffffffcfcfcfcfcfccccc0000fffffffffffffcfcfcfcfcfccccc0000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_120 : Nat := 0x1010101010101010101010101010101
def goal_120 : Nat := 0xffffffffffffff00ff00ff0000000000ffffffffffffff00ff00ff0000000000
def roots_120 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_121 : Nat := 0x3030303030303030303030303030303
def goal_121 : Nat := 0xffffffffffffffaaffaaff00aaaaaa00ffffffffffffffaaffaaff00aaaaaa00
def roots_121 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_122 : Nat := 0x5050505050505050505050505050505
def goal_122 : Nat := 0xffffffffffffffccffccffcccccc0000ffffffffffffffccffccffcccccc0000
def roots_122 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffffffffffffffeeffeeffcceeeeaa00ffffffffffffffeeffeeffcceeeeaa00
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_126 : Nat := 0x55555555555555555555555555555555
def goal_126 : Nat := 0xfffffffffffffffcfffcfffccccc0000fffffffffffffffcfffcfffccccc0000
def roots_126 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xfffffffffffffffefffefffceeeeaa00fffffffffffffffefffefffceeeeaa00
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_137 : Nat := 0x30300000000000000000000000000000303
def goal_137 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_137 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_143 : Nat := 0xffff0000000000000000000000000000ffff
def goal_143 : Nat := 0xfffefffefffefffefffefffefffefffeaa00aa00aa00aa00aa00aa00aa00aa00
def roots_143 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_149 : Nat := 0x33003300000000000000000000000000330033
def goal_149 : Nat := 0xfffffafafffffafafffffafafffffafaaaaa0000aaaa0000aaaa0000aaaa0000
def roots_149 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def goal_155 : Nat := 0xffffffeeffffffeeffffffeeffffffeeeeeeaa00eeeeaa00eeeeaa00eeeeaa00
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_158 : Nat := 0x5555555500000000000000000000000055555555
def goal_158 : Nat := 0xfffffffcfffffffcfffffffcfffffffccccc0000cccc0000cccc0000cccc0000
def roots_158 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_159 : Nat := 0xffffffff000000000000000000000000ffffffff
def goal_159 : Nat := 0xfffffffefffffffefffffffefffffffeeeeeaa00eeeeaa00eeeeaa00eeeeaa00
def roots_159 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_165 : Nat := 0x330000003300000000000000000000003300000033
def goal_165 : Nat := 0xfffffffffafafafafffffffffafafafaf0f0f0f000000000f0f0f0f000000000
def roots_165 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_173 : Nat := 0x33330000333300000000000000000000333300003333
def goal_173 : Nat := 0xfffffffffffafffafffffffffffafffafff0fff0aa00aa00fff0fff0aa00aa00
def roots_173 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_174 : Nat := 0x55550000555500000000000000000000555500005555
def goal_174 : Nat := 0xfffffffffffcfffcfffffffffffcfffcfffcfffc00000000fffcfffc00000000
def roots_174 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_175 : Nat := 0xffff0000ffff00000000000000000000ffff0000ffff
def goal_175 : Nat := 0xfffffffffffefffefffffffffffefffefffcfffcaa00aa00fffcfffcaa00aa00
def roots_175 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_177 : Nat := 0x300030003000300000000000000000003000300030003
def goal_177 : Nat := 0xffffffffffffaaaaffffffffffffaaaaaaaa0000aaaa0000aaaa0000aaaa0000
def roots_177 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_180 : Nat := 0x1100110011001100000000000000000011001100110011
def goal_180 : Nat := 0xfffffffffffff0f0fffffffffffff0f0f0f0f0f000000000f0f0f0f000000000
def roots_180 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_181 : Nat := 0x3300330033003300000000000000000033003300330033
def goal_181 : Nat := 0xfffffffffffffafafffffffffffffafafafaf0f0aaaa0000fafaf0f0aaaa0000
def roots_181 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_182 : Nat := 0x5500550055005500000000000000000055005500550055
def goal_182 : Nat := 0xfffffffffffffcfcfffffffffffffcfcfcfcfcfccccc0000fcfcfcfccccc0000
def roots_182 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_186 : Nat := 0x50505050505050500000000000000000505050505050505
def goal_186 : Nat := 0xffffffffffffffccffffffffffffffccffccffcccccc0000ffccffcccccc0000
def roots_186 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffffffffffeeffffffffffffffeeffeeffcceeeeaa00ffeeffcceeeeaa00
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_190 : Nat := 0x555555555555555500000000000000005555555555555555
def goal_190 : Nat := 0xfffffffffffffffcfffffffffffffffcfffcfffccccc0000fffcfffccccc0000
def roots_190 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xfffffffffffffffefffffffffffffffefffefffceeeeaa00fffefffceeeeaa00
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_193 : Nat := 0x3000000000000000300000000000000030000000000000003
def goal_193 : Nat := 0xffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000000000000000
def roots_193 : List Nat := [xs256.getD 0 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_196 : Nat := 0x11000000000000001100000000000000110000000000000011
def goal_196 : Nat := 0xfffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000
def roots_196 : List Nat := [xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_197 : Nat := 0x33000000000000003300000000000000330000000000000033
def goal_197 : Nat := 0xfffffffffffffffffafafafafafafafafafafafafafafafa0000000000000000
def roots_197 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_198 : Nat := 0x55000000000000005500000000000000550000000000000055
def goal_198 : Nat := 0xfffffffffffffffffcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc0000000000000000
def roots_198 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_200 : Nat := 0x101000000000000010100000000000001010000000000000101
def goal_200 : Nat := 0xffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff000000000000000000
def roots_200 : List Nat := [xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_201 : Nat := 0x303000000000000030300000000000003030000000000000303
def goal_201 : Nat := 0xffffffffffffffffffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00aa00aa00
def roots_201 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffffffffffffffffffeeffeeffeeffeeffeeffeeffeeffeeaa00aa00aa00aa00
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_204 : Nat := 0x1111000000000000111100000000000011110000000000001111
def goal_204 : Nat := 0xfffffffffffffffffff0fff0fff0fff0fff0fff0fff0fff00000000000000000
def roots_204 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_205 : Nat := 0x3333000000000000333300000000000033330000000000003333
def goal_205 : Nat := 0xfffffffffffffffffffafffafffafffafffafffafffafffaaa00aa00aa00aa00
def roots_205 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_206 : Nat := 0x5555000000000000555500000000000055550000000000005555
def goal_206 : Nat := 0xfffffffffffffffffffcfffcfffcfffcfffcfffcfffcfffc0000000000000000
def roots_206 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_207 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def goal_207 : Nat := 0xfffffffffffffffffffefffefffefffefffefffefffefffeaa00aa00aa00aa00
def roots_207 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

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
def goal_212 : Nat := 0xfffffffffffffffffffff0f0fffff0f0fffff0f0fffff0f00000000000000000
def roots_212 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_213 : Nat := 0x330033000000000033003300000000003300330000000000330033
def goal_213 : Nat := 0xfffffffffffffffffffffafafffffafafffffafafffffafaaaaa0000aaaa0000
def roots_213 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xfffffffffffffffffffffcfcfffffcfcfffffcfcfffffcfccccc0000cccc0000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xfffffffffffffffffffffefefffffefefffffefefffffefeeeee0000eeee0000
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_217 : Nat := 0x3030303000000000303030300000000030303030000000003030303
def goal_217 : Nat := 0xffffffffffffffffffffffaaffffffaaffffffaaffffffaaaaaaaa00aaaaaa00
def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def goal_218 : Nat := 0xffffffffffffffffffffffccffffffccffffffccffffffcccccc0000cccc0000
def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffffffffffffffffffffeeffffffeeffffffeeffffffeeeeeeaa00eeeeaa00
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xfffffffffffffffffffffffcfffffffcfffffffcfffffffccccc0000cccc0000
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffffffffffffffffffefffffffefffffffefffffffeeeeeaa00eeeeaa00
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_225 : Nat := 0x300000003000000030000000300000003000000030000000300000003
def goal_225 : Nat := 0xffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaa0000000000000000
def roots_225 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_228 : Nat := 0x1100000011000000110000001100000011000000110000001100000011
def goal_228 : Nat := 0xfffffffffffffffffffffffff0f0f0f0fffffffff0f0f0f0f0f0f0f000000000
def roots_228 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_229 : Nat := 0x3300000033000000330000003300000033000000330000003300000033
def goal_229 : Nat := 0xfffffffffffffffffffffffffafafafafffffffffafafafaf0f0f0f000000000
def roots_229 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def goal_230 : Nat := 0xfffffffffffffffffffffffffcfcfcfcfffffffffcfcfcfcfcfcfcfc00000000
def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def goal_231 : Nat := 0xfffffffffffffffffffffffffefefefefffffffffefefefefcfcfcfc00000000
def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffffffffffffffffffccffccffffffffffccffccffccffcc00000000
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffffffffffffffffffeeffeeffffffffffeeffeeffccffccaa00aa00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_236 : Nat := 0x111100001111000011110000111100001111000011110000111100001111
def goal_236 : Nat := 0xfffffffffffffffffffffffffff0fff0fffffffffff0fff0fff0fff000000000
def roots_236 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xfffffffffffffffffffffffffffafffafffffffffffafffafff0fff0aa00aa00
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_238 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def goal_238 : Nat := 0xfffffffffffffffffffffffffffcfffcfffffffffffcfffcfffcfffc00000000
def roots_238 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffffffffffffffffffefffefffffffffffefffefffcfffcaa00aa00
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_240 : Nat := 0x1000100010001000100010001000100010001000100010001000100010001
def goal_240 : Nat := 0xffffffffffffffffffffffffffff0000ffffffffffff00000000000000000000
def roots_240 : List Nat := [xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_241 : Nat := 0x3000300030003000300030003000300030003000300030003000300030003
def goal_241 : Nat := 0xffffffffffffffffffffffffffffaaaaffffffffffffaaaaaaaa0000aaaa0000
def roots_241 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffffffffffffffffffffeeeeffffffffffffeeeeeeeecccceeee0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_244 : Nat := 0x11001100110011001100110011001100110011001100110011001100110011
def goal_244 : Nat := 0xfffffffffffffffffffffffffffff0f0fffffffffffff0f0f0f0f0f000000000
def roots_244 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_245 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
def goal_245 : Nat := 0xfffffffffffffffffffffffffffffafafffffffffffffafafafaf0f0aaaa0000
def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffffffffffffffffffffffcfcfffffffffffffcfcfcfcfcfccccc0000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffffffffffffffffffefefffffffffffffefefefefcfceeee0000
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffffffffffffffffffaaffffffffffffffaaffaaff00aaaaaa00
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffffffffffffffffffccffffffffffffffccffccffcccccc0000
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffffffffffffffffffeeffffffffffffffeeffeeffcceeeeaa00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffffffffffffffffffafffffffffffffffafffafff0aaaaaa00
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffffffffffffffffffcfffffffffffffffcfffcfffccccc0000
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffffffffffffffffffefffffffffffffffefffefffceeeeaa00
def roots_255 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

namespace S_73
def pG:List (Nat×Nat):=[(1,9),(1,65),(8,9),(8,72),(64,65),(64,72)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3f
def xsM:=roots_73.map (·&&&dom_73)
def gM:=goal_73&&&dom_73
def NN:Nat→Nat
|2=>1
|3=>1
|_=>0
def HT:Nat→Nat→Nat
|2,0=>0x7d42
|3,0=>0x7d42
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x3000000000000000300808000000000000080b030000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x924
|_=>0
def sO:Nat→Nat→Nat
|2,0=>3
|3,0=>0x33
|_,_=>0
def wAt:=mkWire dB 3 74 0x3ffffffffffffffffff
def SS:=mkSS wAt sP sO 2 7
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def mkPools (_ _:Nat):List (Nat×Nat×(Nat×List Nat)):=[]
def mkCut (_ _:Nat) (_:Nat×Nat×Nat) (_:List Nat):Bool:=false
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_73 gM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_73 gM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_73==dom_73)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_73 gM v ys):RunD true dom_73 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_73 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s:Nat) (hs:s≤3):∀ i<NN s,bar dom_73 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 2 2=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤3) (h:RunD true dom_73 gM s xsM):False:=by
  have hmin:2≤s:=by have hl:=run_len h;change 3≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_73 roots_73 goal_73 4:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_73
theorem lowS_73:Lower true dom_73 roots_73 goal_73 4:=S_73.noCircuit
def isoMvS_81:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_81:Lower true dom_81 roots_81 goal_81 4:=lower_iso_b isoMvS_81 (by decide +kernel) lowS_73
def isoMvS_82:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_82:Lower true dom_82 roots_82 goal_82 4:=lower_iso_b isoMvS_82 (by decide +kernel) lowS_73
def isoMvS_98:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_98:Lower true dom_98 roots_98 goal_98 4:=lower_iso_b isoMvS_98 (by decide +kernel) lowS_73
def isoMvS_100:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_100:Lower true dom_100 roots_100 goal_100 4:=lower_iso_b isoMvS_100 (by decide +kernel) lowS_73
def isoMvS_104:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_104:Lower true dom_104 roots_104 goal_104 4:=lower_iso_b isoMvS_104 (by decide +kernel) lowS_73
def isoMvS_137:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_137:Lower true dom_137 roots_137 goal_137 4:=lower_iso_b isoMvS_137 (by decide +kernel) lowS_73
def isoMvS_193:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_193:Lower true dom_193 roots_193 goal_193 4:=lower_iso_b isoMvS_193 (by decide +kernel) lowS_73
def isoMvS_196:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_196:Lower true dom_196 roots_196 goal_196 4:=lower_iso_b isoMvS_196 (by decide +kernel) lowS_73
def isoMvS_200:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_200:Lower true dom_200 roots_200 goal_200 4:=lower_iso_b isoMvS_200 (by decide +kernel) lowS_73
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
theorem lowS_75:Lower true dom_75 roots_75 goal_75 5:=lower_slice_b [(0xc0c0000000000000c0c,64,66)] (by decide +kernel) lowS_73
theorem lowS_83:Lower true dom_83 roots_83 goal_83 5:=lower_slice_b [(0xa000a00000000000a000a,16,17)] (by decide +kernel) lowS_82
namespace S_201
def pG:List (Nat×Nat):=[(1,9),(1,65),(1,129),(8,9),(8,72),(8,136),(64,65),(64,72),(64,192),(128,129),(128,136),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfff
def xsM:=roots_201.map (·&&&dom_201)
def gM:=goal_201&&&dom_201
def NN:Nat→Nat
|3=>3
|4=>6
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x64b4b1903600d53
|4,0=>0x69260381401ea121ad4610232048c0
|5,0=>0x462633e64c01756
|6,0=>0x46263
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xc0c000000000000080b03000000000000030300000000000003000000000000000300c080000000000000c080000000000000c080000000000000c0b0300000000000003030000000000000303000000000000020200c000000000000000c000000000000000c000000000000000303000000000000020200000000000003030000000000000202c0c0000000000000c0c0000000000000808000000000000080b03000000000000030300000000000003030000000000000000c0c00000000000000000000000000000c0800000000000000030300000000000003030000000000000000000000000000000000000000000000000000000000000000c0c0000000000000c0b0000000000000003000000000000000300000000000000030080800000000000008080000000000000808000000000000080b03000000000000000000000000000003030000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x2104210421604271042d104c216028704b27042a10421094287621543210
|_=>0
def sO:Nat→Nat→Nat
|3,0=>0x8411004
|4,0=>0x956056d565454c5
|5,0=>0x344bd6a5
|6,0=>0x384
|_,_=>0
def wAt:=mkWire dB 14 202 0x3ffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x4045124501015052150504505
|_=>0
def oO:Nat→Nat→Nat
|3,0=>0x20000
|4,0=>0x6242220000
|5,0=>0x9181
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0xfcba630
|_=>0
def pmB:Nat→Nat→Nat
|3,0=>0x40
|4,0=>0x3540
|5,0=>0x136
|6,0=>6
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 4 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_200 4 roots_200 ops++addP pm 1 dom_137 4 roots_137 ops++addP pm 2 dom_73 4 roots_73 ops++addP pm 3 dom_193 4 roots_193 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_201 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_200 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_193 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_200 4 s (0,roots_200.map (·&&&dom_200)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_201 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_200 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)],[(0xff00ff00ff00ff00ff00ff00ff00ff00,120)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff00ff00ff00ff00ff00,120)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_201==dom_201)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_201 gM v ys):RunD true dom_201 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_201 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 3 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 6 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 6 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_201 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_201 gM s xsM):False:=by
  have hmin:3≤s:=by have hl:=run_len h;change 4≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_201 roots_201 goal_201 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_201
theorem lowS_201:Lower true dom_201 roots_201 goal_201 7:=S_201.noCircuit
def isoMvS_43:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_43:Lower true dom_43 roots_43 goal_43 4:=lower_iso_b isoMvS_43 (by decide +kernel) lowS_27
def isoMvS_45:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_45:Lower true dom_45 roots_45 goal_45 4:=lower_iso_b isoMvS_45 (by decide +kernel) lowS_27
def isoMvS_51:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_51:Lower true dom_51 roots_51 goal_51 4:=lower_iso_b isoMvS_51 (by decide +kernel) lowS_27
def isoMvS_57:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_57:Lower true dom_57 roots_57 goal_57 4:=lower_iso_b isoMvS_57 (by decide +kernel) lowS_27
def isoMvS_58:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_58:Lower true dom_58 roots_58 goal_58 4:=lower_iso_b isoMvS_58 (by decide +kernel) lowS_27
def isoMvS_77:List (Nat×Nat):=[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_77:Lower true dom_77 roots_77 goal_77 5:=lower_iso_b isoMvS_77 (by decide +kernel) lowS_75
def isoMvS_85:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_85:Lower true dom_85 roots_85 goal_85 5:=lower_iso_b isoMvS_85 (by decide +kernel) lowS_75
def isoMvS_86:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_86:Lower true dom_86 roots_86 goal_86 5:=lower_iso_b isoMvS_86 (by decide +kernel) lowS_75
def isoMvS_89:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_89:Lower true dom_89 roots_89 goal_89 5:=lower_iso_b isoMvS_89 (by decide +kernel) lowS_83
def isoMvS_90:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_90:Lower true dom_90 roots_90 goal_90 5:=lower_iso_b isoMvS_90 (by decide +kernel) lowS_75
def isoMvS_99:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_99:Lower true dom_99 roots_99 goal_99 5:=lower_iso_b isoMvS_99 (by decide +kernel) lowS_75
def isoMvS_101:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_101:Lower true dom_101 roots_101 goal_101 5:=lower_iso_b isoMvS_101 (by decide +kernel) lowS_75
def isoMvS_105:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_105:Lower true dom_105 roots_105 goal_105 5:=lower_iso_b isoMvS_105 (by decide +kernel) lowS_83
def isoMvS_106:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_106:Lower true dom_106 roots_106 goal_106 5:=lower_iso_b isoMvS_106 (by decide +kernel) lowS_83
def isoMvS_108:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_108:Lower true dom_108 roots_108 goal_108 5:=lower_iso_b isoMvS_108 (by decide +kernel) lowS_83
def isoMvS_113:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_113:Lower true dom_113 roots_113 goal_113 5:=lower_iso_b isoMvS_113 (by decide +kernel) lowS_75
def isoMvS_114:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_114:Lower true dom_114 roots_114 goal_114 5:=lower_iso_b isoMvS_114 (by decide +kernel) lowS_83
def isoMvS_116:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_116:Lower true dom_116 roots_116 goal_116 5:=lower_iso_b isoMvS_116 (by decide +kernel) lowS_75
def isoMvS_120:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_120:Lower true dom_120 roots_120 goal_120 5:=lower_iso_b isoMvS_120 (by decide +kernel) lowS_75
def isoMvS_149:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_149:Lower true dom_149 roots_149 goal_149 5:=lower_iso_b isoMvS_149 (by decide +kernel) lowS_75
def isoMvS_165:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_165:Lower true dom_165 roots_165 goal_165 5:=lower_iso_b isoMvS_165 (by decide +kernel) lowS_75
def isoMvS_177:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_177:Lower true dom_177 roots_177 goal_177 5:=lower_iso_b isoMvS_177 (by decide +kernel) lowS_75
def isoMvS_180:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_180:Lower true dom_180 roots_180 goal_180 5:=lower_iso_b isoMvS_180 (by decide +kernel) lowS_75
def isoMvS_197:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_197:Lower true dom_197 roots_197 goal_197 5:=lower_iso_b isoMvS_197 (by decide +kernel) lowS_83
def isoMvS_198:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_198:Lower true dom_198 roots_198 goal_198 5:=lower_iso_b isoMvS_198 (by decide +kernel) lowS_83
def isoMvS_204:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_204:Lower true dom_204 roots_204 goal_204 5:=lower_iso_b isoMvS_204 (by decide +kernel) lowS_83
def isoMvS_209:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_209:Lower true dom_209 roots_209 goal_209 7:=lower_iso_b isoMvS_209 (by decide +kernel) lowS_201
def isoMvS_210:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_210:Lower true dom_210 roots_210 goal_210 7:=lower_iso_b isoMvS_210 (by decide +kernel) lowS_201
def isoMvS_212:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_212:Lower true dom_212 roots_212 goal_212 5:=lower_iso_b isoMvS_212 (by decide +kernel) lowS_83
def isoMvS_225:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_225:Lower true dom_225 roots_225 goal_225 5:=lower_iso_b isoMvS_225 (by decide +kernel) lowS_83
def isoMvS_228:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_228:Lower true dom_228 roots_228 goal_228 7:=lower_iso_b isoMvS_228 (by decide +kernel) lowS_201
def isoMvS_240:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_240:Lower true dom_240 roots_240 goal_240 5:=lower_iso_b isoMvS_240 (by decide +kernel) lowS_83
theorem lowS_47:Lower true dom_47 roots_47 goal_47 5:=lower_slice_b [(0xcccc0000cccc,32,34)] (by decide +kernel) lowS_45
namespace S_59
def pG:List (Nat×Nat):=[(1,9),(1,17),(2,18),(2,34),(3,11),(3,19),(3,35),(8,9),(8,40),(10,11),(10,26),(10,42),(16,17),(16,18),(24,25),(24,26),(24,56),(32,34),(32,40),(33,35),(33,41),(33,49),(48,49),(48,50),(48,56)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1ffffff
def xsM:=roots_59.map (·&&&dom_59)
def gM:=goal_59&&&dom_59
def NN:Nat→Nat
|4=>2
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x1150d06449
|5,0=>0x9abd70e01a0a6f0
|6,0=>0x9abd7
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0c0f0c0f0c0f0cf0f0f0f0f000f00f0f00000f0f0000f0c0f0c00000000f0f0f0f00000000f000f000f000f00c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a0000e0e00000e0e
|_,_=>0
def sP:Nat→Nat
|0=>0x46321463214683217463216532143210
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x15405
|5,0=>0x165418a6
|6,0=>0x1b5
|_,_=>0
def wAt:=mkWire dB 9 60 0xfffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def pmP:Nat→Nat
|0=>0xf9040
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>6
|6,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 2 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_58 4 roots_58 ops++addP pm 1 dom_57 4 roots_57 ops++addP pm 2 dom_51 4 roots_51 ops++addP pm 3 dom_43 4 roots_43 ops++addP pm 4 dom_27 4 roots_27 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_59 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_27 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_58 4 s (0,roots_58.map (·&&&dom_58)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_59 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_58 h
def symsG:List (List (Nat×Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0x2222222222222222222222222222222222222222222222222222222222222222,1)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_59==dom_59)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_59 gM v ys):RunD true dom_59 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_59 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
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
theorem lowS_79:Lower true dom_79 roots_79 goal_79 6:=lower_slice_b [(0xcccc000000000000cccc,64,66)] (by decide +kernel) lowS_77
theorem lowS_87:Lower true dom_87 roots_87 goal_87 6:=lower_slice_b [(0xaa00aa0000000000aa00aa,16,17)] (by decide +kernel) lowS_86
namespace S_91
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(2,18),(2,66),(3,11),(3,19),(3,67),(8,9),(8,72),(10,11),(10,26),(10,74),(16,17),(16,18),(16,80),(24,25),(24,26),(24,88),(64,65),(64,66),(64,72),(64,80)]
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
def symsG:List (List (Nat×Nat)):=[[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
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
theorem lowS_110:Lower true dom_110 roots_110 goal_110 6:=lower_slice_b [(0x4444000044440000444400004444,32,34)] (by decide +kernel) lowS_108
namespace S_117
def pG:List (Nat×Nat):=[(1,17),(1,65),(4,36),(4,68),(5,21),(5,37),(5,69),(16,17),(16,80),(20,21),(20,52),(20,84),(32,36),(32,96),(33,37),(33,49),(33,97),(48,49),(48,52),(48,112),(64,65),(64,68),(64,80),(64,96)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_117.map (·&&&dom_117)
def gM:=goal_117&&&dom_117
def NN:Nat→Nat
|3=>1
|4=>4
|5=>10
|6=>4
|7=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x4466a
|4,0=>0x29c730917203704035dd
|5,0=>0x8575a5073a49f993a36f3352f2bd072818a2147e1c27a0c5a0
|6,0=>0x96c74298131cc1b0ebe4
|7,0=>0x96c74
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcc00cc00cc00cc00cc000000cc000000033000000330000000000000000000000004400440000000000000000000000033003300000000003000308c008c008c008c008800880088008b200320032003200000000000000000c000c000c000c000c000c0008000800000003000330000000000300030cc00cc0000000000cc00cc0000000300030003000300030003000300030cc00c800cc00c8008800880088008b30033003300330000000000000000cc00cc00cc00c000cc00cc0000000330000003300000033000000330000cc00cc00cc00cc00c000c000c000c220022002200220022002200220022
|0,1=>0xcc00cc0088008800cc00cc00880088300030003000300000000000000000000000000000000cc00c000cc00c3300330033003300330033000000000c000c000c000c000c000c0000000330030003300300000000000000000c800c800c800c800c800c800c800cb30030003300300033003000330030cc00cc00cc00cc00cc00c000cc00c110011001100110011001100000000
|_,_=>0
def sP:Nat→Nat
|0=>0x1c46010e230096388c0264e23008711804c1ee2300963881521c460128714c2021e22300871181021de6011c711804688c0610e232c043882051c404904602087118a418820
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|4,0=>0x26a3944a845
|5,0=>0x26b47682ced9ab2f652c8d8f2986
|6,0=>0xcab7dacb536
|7,0=>0x6a5
|_,_=>0
def wAt:=mkWire dB 26 118 0x3fffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x391381312b1b391910311911312
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x423121110000000001
|6,0=>0x817161
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 8
def pmP:Nat→Nat
|0=>0xffdb68792446080
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x653402001
|6,0=>0x7898
|7,0=>9
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 6 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_116 5 roots_116 ops++addP pm 1 dom_100 4 roots_100 ops++addP pm 2 dom_101 5 roots_101 ops++addP pm 3 dom_113 5 roots_113 ops++addP pm 4 dom_81 4 roots_81 ops++addP pm 5 dom_85 5 roots_85 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_117 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_100 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_101 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_85 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_116 5 s (0,roots_116.map (·&&&dom_116)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_117 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_116 h
def symsG:List (List (Nat×Nat)):=[[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28)],[(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_117==dom_117)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_117 gM v ys):RunD true dom_117 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_117 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 4 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
theorem checked (s:Nat) (hs:s≤7):∀ i<NN s,bar dom_117 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤7) (h:RunD true dom_117 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_117 roots_117 goal_117 8:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_117
theorem lowS_117:Lower true dom_117 roots_117 goal_117 8:=S_117.noCircuit
theorem lowS_203:Lower true dom_203 roots_203 goal_203 8:=lower_slice_b [(0xc0c0000000000000c0c0000000000000c0c0000000000000c0c,64,66)] (by decide +kernel) lowS_201
theorem lowS_211:Lower true dom_211 roots_211 goal_211 8:=lower_slice_b [(0xa000a00000000000a000a00000000000a000a00000000000a000a,16,17)] (by decide +kernel) lowS_210
def isoMvS_62:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_62:Lower true dom_62 roots_62 goal_62 5:=lower_iso_b isoMvS_62 (by decide +kernel) lowS_47
def isoMvS_93:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_93:Lower true dom_93 roots_93 goal_93 6:=lower_iso_b isoMvS_93 (by decide +kernel) lowS_87
def isoMvS_94:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_94:Lower true dom_94 roots_94 goal_94 6:=lower_iso_b isoMvS_94 (by decide +kernel) lowS_79
def isoMvS_107:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_107:Lower true dom_107 roots_107 goal_107 7:=lower_iso_b isoMvS_107 (by decide +kernel) lowS_91
def isoMvS_109:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_109:Lower true dom_109 roots_109 goal_109 7:=lower_iso_b isoMvS_109 (by decide +kernel) lowS_91
def isoMvS_115:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_115:Lower true dom_115 roots_115 goal_115 7:=lower_iso_b isoMvS_115 (by decide +kernel) lowS_91
def isoMvS_118:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_118:Lower true dom_118 roots_118 goal_118 7:=lower_iso_b isoMvS_118 (by decide +kernel) lowS_91
def isoMvS_121:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_121:Lower true dom_121 roots_121 goal_121 7:=lower_iso_b isoMvS_121 (by decide +kernel) lowS_91
def isoMvS_122:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_122:Lower true dom_122 roots_122 goal_122 7:=lower_iso_b isoMvS_122 (by decide +kernel) lowS_91
def isoMvS_143:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_143:Lower true dom_143 roots_143 goal_143 6:=lower_iso_b isoMvS_143 (by decide +kernel) lowS_79
def isoMvS_155:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_155:Lower true dom_155 roots_155 goal_155 7:=lower_iso_b isoMvS_155 (by decide +kernel) lowS_91
def isoMvS_158:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_158:Lower true dom_158 roots_158 goal_158 6:=lower_iso_b isoMvS_158 (by decide +kernel) lowS_79
def isoMvS_173:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_173:Lower true dom_173 roots_173 goal_173 7:=lower_iso_b isoMvS_173 (by decide +kernel) lowS_91
def isoMvS_174:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_174:Lower true dom_174 roots_174 goal_174 6:=lower_iso_b isoMvS_174 (by decide +kernel) lowS_110
def isoMvS_181:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_181:Lower true dom_181 roots_181 goal_181 8:=lower_iso_b isoMvS_181 (by decide +kernel) lowS_117
def isoMvS_182:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_182:Lower true dom_182 roots_182 goal_182 7:=lower_iso_b isoMvS_182 (by decide +kernel) lowS_91
def isoMvS_186:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_186:Lower true dom_186 roots_186 goal_186 7:=lower_iso_b isoMvS_186 (by decide +kernel) lowS_91
def isoMvS_205:List (Nat×Nat):=[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_205:Lower true dom_205 roots_205 goal_205 8:=lower_iso_b isoMvS_205 (by decide +kernel) lowS_203
def isoMvS_206:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96)]
theorem lowS_206:Lower true dom_206 roots_206 goal_206 6:=lower_iso_b isoMvS_206 (by decide +kernel) lowS_110
def isoMvS_213:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_213:Lower true dom_213 roots_213 goal_213 8:=lower_iso_b isoMvS_213 (by decide +kernel) lowS_203
def isoMvS_214:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_214:Lower true dom_214 roots_214 goal_214 8:=lower_iso_b isoMvS_214 (by decide +kernel) lowS_203
def isoMvS_217:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_217:Lower true dom_217 roots_217 goal_217 8:=lower_iso_b isoMvS_217 (by decide +kernel) lowS_211
def isoMvS_218:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_218:Lower true dom_218 roots_218 goal_218 8:=lower_iso_b isoMvS_218 (by decide +kernel) lowS_203
def isoMvS_229:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_229:Lower true dom_229 roots_229 goal_229 8:=lower_iso_b isoMvS_229 (by decide +kernel) lowS_203
def isoMvS_230:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_230:Lower true dom_230 roots_230 goal_230 8:=lower_iso_b isoMvS_230 (by decide +kernel) lowS_211
def isoMvS_234:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_234:Lower true dom_234 roots_234 goal_234 8:=lower_iso_b isoMvS_234 (by decide +kernel) lowS_211
def isoMvS_236:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_236:Lower true dom_236 roots_236 goal_236 8:=lower_iso_b isoMvS_236 (by decide +kernel) lowS_211
def isoMvS_241:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_241:Lower true dom_241 roots_241 goal_241 8:=lower_iso_b isoMvS_241 (by decide +kernel) lowS_203
def isoMvS_244:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_244:Lower true dom_244 roots_244 goal_244 8:=lower_iso_b isoMvS_244 (by decide +kernel) lowS_203
theorem lowS_63:Lower true dom_63 roots_63 goal_63 8:=lower_slice_b [(0xf0f0f0f0f0f0f0f0,32,36)] (by decide +kernel) lowS_59
def dzo_27_4:=0xf0f0f0f0
def gzo_27_4:=0xe0e0a000
def gsh_27_4:=0xe0e0a00
theorem lowS_zo_27_4_27:Lower true dzo_27_4 roots_27 gzo_27_4 4:=lower_iso_b (d1:=dom_27) (r1:=roots_27) (T1:=gsh_27_4) [(dom_27,4)] (by decide +kernel) (lower_slice_b (T:=gsh_27_4) [] (by decide +kernel) lowS_27)
def dzo_91_4:=0xf0f0f0f000000000f0f0f0f0
def gzo_91_4:=0xf0f0f0f000000000e0e0a000
def gsh_91_4:=0xf0f0f0f000000000e0e0a00
theorem lowS_zo_91_4_27:Lower true dzo_91_4 roots_91 gzo_91_4 5:=lower_iso_b (d1:=dom_91) (r1:=roots_91) (T1:=gsh_91_4) [(dom_91,4)] (by decide +kernel) (lower_slice_b (T:=gsh_91_4) [(0xf0f0f0f0000000000000000,0,64)] (by decide +kernel) lowS_27)
namespace S_95
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(2,18),(2,66),(3,11),(3,19),(3,67),(4,68),(5,13),(5,21),(5,69),(6,22),(6,70),(7,15),(7,23),(7,71),(8,9),(8,72),(10,11),(10,26),(10,74),(12,13),(12,76),(14,15),(14,30),(14,78),(16,17),(16,18),(16,80),(20,21),(20,22),(20,84),(24,25),(24,26),(24,88),(28,29),(28,30),(28,92),(64,65),(64,66),(64,68),(64,72),(64,80)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_95.map (·&&&dom_95)
def gM:=goal_95&&&dom_95
def NN:Nat→Nat
|3=>10
|4=>54
|5=>113
|6=>61
|7=>11
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0xea0289c6e7748da67b635379f47c01466013ce8130c0e1593d
|4,0=>0xe38a3d6a76c3d81c3665c1658a8e19a8224a0b859f76096dfe92dc791b3a8739d8591285124817dd7f0b079ce86eba86aebf69bde660b65ce5c5a98b54cc14951d44f9844d22441dc437673c94a3797833e3d2f7192a51224345226b0201131faa11dc081c8a91baa019d32170e616dfb14226112f80e7b90d8cf093c7051f801dec014080090f
|5,0=>0xd7933d5cf5d4844ced92cdfeccbe2ec73bac65f0c5c7fc13fdbc3d5b29fab0dfbab33ba3438a12809d59d9cbcf9ab7f9ab649a8aa9a55f98c2d975789715496a0e93d37920d58fd9e8fd158f6f98ae9a87d958691884b6c83df581aa5816758095b7f4df7e5aa7df777dcbd764696df146c13c6bc636a86367822649da609bb5fde757616556465403853cf352383506194ff0e4f4f84978f47a5f47120450b94233f41db8419c03e7853e0183c7f73bf293725d36fad36c653669a3558433b4933ae1329f63036c2cb6a2aab8283de27ea1279ee279e926b7a2557a247422066b1e3301d4ba1cf2a1b80b1ac4a159ce1445311997118e11077a0f8340c9cf0b9480b1e10900808fac085280718c05f6d0580803a250238500f1e
|6,0=>0xf549ee9bd5e06f7ddcbadc968d79c7d703ece6dcca6a5c7dddc6768c0484bd7adaf52eae0d7a1345a103895267927f587b7c8461f7e7ff742af700976c056687b867ed366ee0644006055f59f8e597a0536534cf6e460be3f9d53bd1d39f9a3718b2fd502ef5c220e62036e197a419734183d517479152e610ca510ae3106140e2c90d93d0cb5b0c6f309a6a08bbc083d0032dc018a7015c6
|7,0=>0xda081a8252827c2510b64c8574088a326322ca4f2c9c22a99602d40
|8,0=>0xc3264
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaaaaaaaa00000000aaaaaaaaffffff0000000000ffffff00ffffafaf00000000ffffaaaaffffffff0000000000000000ffffffff00000000ffffff00ffffffff00000000ffff0000f0f0f0f000000000f0f0f0f0ffffff0000000000aaaaaa00ffff000000000000ffff0000ffffffff00000000ff00ff00cccccccc00000000ccccccccfffffffa00000000aaaaaaaafffffefe00000000ffff0000ff00ff0000000000ff00ff00eeeeeeee00000000eeeeeeeeffffffff00000000aaaaaaaa
|0,1=>0x333333030000000033333300ffff050500000000ffff0000fffffff000000000fffffff0aaaaaaaa00000000aaaaaa0000ff00af0000000000ff00aaffffeeee00000000ccccccccffffaaaa00000000ffffaaaaeeeeeeee00000000eeee000000af00af0000000000af00aa0000efef000000000000eeeeffffffaa00000000aaaaaaaafffffff00000000000000000fafafafa00000000fafafafafffefffe00000000ff00ff00fffffefe00000000ccccccccfffffffc00000000cccccccc
|0,2=>0xfffff0f000000000fffff0f0111101010000000011110000fefefefe00000000fefefefe0000000000000000eeeeeeee5555050500000000555500001111111100000000eeeeeeeeffffeeee00000000ffff0000333300030000000033330000ffff0f0f00000000ffff0000afafafaf00000000aaaaaaaabbbbabab00000000bbbbaaaaffffffcc00000000ccccccccfffffafa00000000fffffafa00aa00af0000000000aa00aafefefefe000000000000000000ef00ef0000000000ee00ee
|0,3=>0x1111111100000000111100000000ffff0000000000000000ffffff000000000000000000454545450000000044444444fffffafa00000000000000000000000000000000ffffaaaa333303030000000033330000ffffffff00000000ffffaaaa0f0f0f0f0000000000000000555555500000000055555550afafafaf00000000afafaaaa0000fefe000000000000fefe555555050000000055555500ffff000f00000000ffff0000fefefefe00000000aaaaaaaa00af00af0000000000ae00ae
|0,4=>0xfffffff000000000f0f0f0f0333333330000000000000000fffffafa00000000f0f0f0f0ff00ff0f00000000ff00ff000f0f0f0f000000000f0f0000ffffeeee00000000ffffeeeefffffefe00000000fffffefe00000f0f0000000000000000ffffffff00000000ccccccccaaaaafaf00000000aaaaaaaa232323230000000022222222ffff000000000000eeee00000f0f0f0f000000000e0e0e0e050505050000000004040404333333330000000033332222eeeeeeee00000000aaaaaaaa
|0,5=>0x111111110000000000000000333311110000000033330000f5f5f5f000000000f5f5f5f0555555000000000055555500f0f0f0f000000000fffffafa0f0f0f0f000000000c0c0c0c0000000000000000ffffff00ffffffff00000000eeeeeeee333333330000000033330000ffffaaaa00000000000000000000afaf000000000000aaaafff0fff000000000fff0fff0fefefefe00000000f0f0f0f00f0f0f0f000000000a0a0a0a00af00af0000000000aa00aabbbbbbbb00000000bbbbaaaa
|0,6=>0xffff000000000000aaaa000005050000000000000000cfcfcfcf00000000cccccccccfcfcfcf00000000cecececeffffff0f00000000ffffff00030303030000000003030000050505050000000005050000f0f0f0f000000000fffffff000bb00bb0000000000aa00aaafafafaf00000000aeaeaeae0000ffff000000000000eeeeaaaaffff00000000aaaaaaaa00ff00ff0000000000ee00ee0000000f00000000000000000000eeee000000000000eeeebbbbbbbb00000000aaaaaaaa
|0,7=>0xffff00ff00000000ffff0000eeeeeeee000000000000000055555555000000000000000000ff00ff00000000000000000f0f0f0f000000000f000f000000ff00000000000000ff00000f000f0000000000000000000f000f00000000000f0000000000aa00000000aaaaaaaa0f0f0f0f000000000f0f0a0afcfcfcfc00000000fcfcfcfc55555555000000004444444401010101000000000000000000ff00ff0000000000aa00aa5555555500000000555555000000ffff000000000000ff00
|0,8=>0x444444440000000044444444050505050000000000000000000055550000000000000000ff00ffff00000000ff00ff00333333330000000022222222ffffffaa00000000ffffffaaffff555500000000ffff0000
|_,_=>0
def sP:Nat→Nat
|0=>0x19010c0302010f0c07050f220c070205002107050f200c070205040c0e070f1f0c0e1e050f0c0b07050f141d07051c0c07050f1b0c0a02091a0f190209180c07050f170c02010f160c0a020905150706050f140d0702010c030205000a130508071205000a02110f0e0a100f0e0d010c0b0705040a0901080706050403020100
|1=>0xe1905360c070201350c0e010f340c070205330c0e07100f0c0712050f0c0e32050f0c070201310c070901080c07050f300c1d0e19010c2f0a0201000b0709051507020f2e0c0702010021070609051507022d2c000e050f2b0c0702092a0f290209010007020f280c0e27010f0c0e1905260c0702250f0c0a0209240f0e23
|2=>0x2050f0c020901440f0c0702050f430c1d0e07010f0c0702050f420c0e1909010c0e27050f0c0702090f410c070205350f0c07020901400c0702090f3f0c07020901003e0e0a09050f3d0e0a09240f0702013c0c2f02180f0c0a02050f3b230a0205000e3a09010c07020918000e270f390c0e3809010c0e19010c370e0a0901
|3=>0x705260f510c070209500f0c0e074f050f0c0702050f0c210702092c0f4e07024d050f0c0e3a09050f0c074c02050f0c190a020905000702010f4b0c0e071305000c0e3809050f0c490702010f0c0702010f0c48290209050f0c07022d470f0c0e19050f0c37070205460f0c0e0a0905000f0e0709240f0c0702050f450c1d0a
|4=>0x50f0c0e1909055c0c07022d2c0f0c070201260c375b0702050f0c290209010f0c0702010f5a0c590754050f0c07022d580f0c0a0209050f3d07020f574b0c0a0209050f560702091a0f0c0e07010f0c370702010f430c0702050f550c0e07050f360c07020f390c0e0a54050f0c070253050f0c07020100520c320702050f0c
|5=>0x2050f690c2f0a020f570c680e07050f0c0d0702050f0c0709050f670c070205660f0c0209050f650c0e0709015c0c07020901640c07050f510c370709050f630c0e07050f0c620e590a09050f2f02010f610c07020901600c0e2702050f0c0702092c0f5f0702050f3c0c0702090f5e0c0702010f0c21070209240f0c0e075d
|6=>0xc0e2319050f0c0e0a09010f0c0702750f740c0702050f0c7307090100720c0e190905000c0b0709050f3d0e070905710c0709010f630c0e09050f700c07020f570c370702130f570c070209016f0c0702050f0c6e0702016d0f0c070201000c372f070201000c07026c050f0c6b0e07050f0c070609050f3d07020f576a0c07
|7=>0x2f070205000f0c0702090f570c0702090105000c070209010f0c5f07020901000c07050f7a0c370e07050f0c790702050f780c0e0705260f0c1d0e0a050f0c0e070905770c230a02050f0c6b0702050f0c192702050f0c0775050f720c680702050f0c070275580f0c070209180f0c1907022d010c0a07021305000702050f76
|8=>0xf0c2f0a02050f0c070209050f740c1d0e0702050f0c190a0209050f0c0e0709050f0c3d0b0e0709050f0c1d0702050f0c0702050f5a0c070905000f720c0702050f0c7907026d050f0c37070205260f0c070209050f6f0c070602050f7b0c0e07050f0c37070205000f0c370e0713050f0c070209010f0c3e0e070609050f0c
|9=>0xc070275470f0c070209012c0f0c0e1909050f0c80070209050f0c0e0709050f0c7c270702050f0c377f070209050f0c070209050f0c56070209050f0c7e0e0702050f0c370702092c050f0c07026d050f0c0a0702050f4b0c23190702050f0c07020958050f0c070209010f610c0a070209050f7d0e0754050f0c0e07090500
|10=>0xc0a070209050f0c070209050f0c7d0702050f520c07027505000f0c3a070209050f0c07022d010f0c230702050f0c070209050f0c5f38070209050f0c190702050f0c370a07020905000f0702050f0c85070209050f0c84070247050f0c3707021347050f0c07830209050f0c0e0709010f0c070209050f820c810e0709050f
|11=>0x70209050f0c0e070209050f0c070209050f0c4e0e0709050f0c0702050f0c372f0702050f0c19070209050f0c07020947050f0c0702090f860c070275050f
|_=>0
def sO:Nat→Nat→Nat
|3,0=>0x1220204038806100a20104018802100220004
|4,0=>0x98a92c524ea48948ea9185226a439484a90451fea3e947aa8f051d6a399470a8dc51aea349466a8c85186a2f945ca8b4515ea2a9452a8a05136a259448a88c510ea20943ea87850e6a1b9434a86450bea16942aa8505096a119420a83c506ea0c9416a8285
|5,0=>0x55aca9d950b29b652aca3d944b28364fac9dd938b26b64cac97d92cb253649ac91d920b23b646ac8bd914b223643ac861509320c640cc8018fd31f463dcc7a18f131dc63acc7418e531c4637cc6e18d931ac634cc6818cd3194631cc6218c1317c62ecc5c18b5316462bea5694aa314e6290c50989e31366
|5,1=>0x3d3679acf1d9e0b3bb676acebd9d4b3a3673ace5d9c8b38b670acdfd9bcb37366dacd9d9b0b35b66aacd3d9a4b343667accdd998b32b664acc7d98cb313661acc1d980b2fb65eacbbd974b2e365bacb5d968b2cb658acafd95cb2b36
|6,0=>0x56b6ac8f575eabb5516a94f50de9e3d357a5ed4a1e90bd1a7a26f435a833cff79f2d3c9e7634e579bcf35de683cc97984f2ede5a3cae694ef281e4cbc927916f215a3f3c7868e2f1a9e31bc5c78aaf13da24b4427878d0d5e17b4287842f06da0a3c0e680ef001dfcbbf367d8ef95defb3d96
|7,0=>0x16c9ed5bda56b3ed665ac93d8b7b0ad5fdabc3d717
|8,0=>0x5b96
|_,_=>0
def wAt:=mkWire dB 135 96 0xffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 15
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 8 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xf0c4042801094143d070f41c31050c4143d0f0c41c02090c8241d0a05c1c310e0cc383f050f41c320107c143d010c8b430050f4383f090c80431050f464300f1d8382502074149e090c81c310009cb4300f0c41c310f0c4081d070043c314a094143d050c41c310f054382502074143d020743c1d090c88c300f0c41c31190c4b41f070243800090e4081d050f41c3d
|1=>0x537424320a09c1c31190941c3d470f414310107c143d0f0c80825020743c31020741c31470fc14310e094081d070c4383002074383102074382502074251e050c4000b0f0c425f2020c824320f37424320007c3c31090680831020742432090c8081d090f43c15070c8081d020c43c31090742817070c43c31050f40432050f43c31050f424320207c2439070c41401
|2=>0x20741432020742432090741c3d050c4143f090541c310f0c800270f0c43c31090546433070f40425050f4bc3d090740432050f46431070f424320f0c41c31097d86432070f42432090f41431023e41c32050f4081d0005c3c310e0f4081d090541431010cc143d020743c1d077d43c32020740832090c81df1020c86430070f40430050f42432010cc143d
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0xa1082000000000071000000000000052000000000000000041000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
|5,0=>0x2c22b10000000000002920002810000002710000000000002520000002410000000000002131f21e10001d10000000000001c10000000000001a20001821621420000001310000000000000001210000000f30000c30b1000000000000000000
|5,1=>0x4210004110000000000003f23e13b33a10000000003910003720000000000000000000003610000003513410000000000000003223110000000000002f22e1000000000000
|6,0=>0xb12af2ad2ab2a92a72a52a41a22a119f29e19c29a29829629429229028e28c28a28918728528328218027e27c27a27827627517327127016e26c26b16926726526326125f25e15c25a25825625515325124f24d24b2492472452432
|7,0=>0xbd1bc1bb1ba1b91b81b71b61b51b41b31
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 12
def pmP:Nat→Nat
|0=>0x4010300026902410240022102040201020000c100c0008000530049004100400029002800210020001800140012001100100009000800040003000200010000
|1=>0x40583e6d3e6b3ac93a693a4934212c012acb2a0920801a711a691a611a4d1a411a211849144c141012411069104110090883084108000600044a044904210410
|2=>0xfa69f021c0499000867a82207e617a61762568c85e495a615004480146234221
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x8480000070000000040000000001401500000000000000000000000000000000000000000000000000000000
|5,0=>0x6000e00000003461940001000e0128000000000000280002c28000000000650000000128500000000614000000008028000050000000020001700000002c5da800a0000000280000000d801038f00001c00000000140000a8060300000000000
|6,0=>0x225a058cb023c81b7e061ac3ec00928ea59213129c1d54948ce804c7ab48f0e41229c81a1addca68d3268684bdfb438611985005736
|7,0=>0xea4b29ef59c866fa245
|8,0=>0x3b
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 7 (j%128);fld (pmP (k/32)) 16 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_91 7 roots_91 ops++addP pm 1 dom_75 5 roots_75 ops++addP pm 2 dom_89 5 roots_89 ops++addP pm 3 dom_86 5 roots_86 ops++addP pm 4 dom_90 5 roots_90 ops++addP pm 5 dom_77 5 roots_77 ops++addP pm 6 dom_94 6 roots_94 ops++addP pm 7 dom_83 5 roots_83 ops++addP pm 8 dom_73 4 roots_73 ops++addP pm 9 dom_79 6 roots_79 ops++addP pm 10 dzo_27_4 4 roots_27 ops++addP pm 11 dom_87 6 roots_87 ops++addP pm 12 dom_93 6 roots_93 ops++addP pm 13 dom_85 5 roots_85 ops++addP pm 14 dom_27 4 roots_27 ops++addP pm 15 dzo_91_4 5 roots_91 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_95 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_79 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_27_4_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_91_4_27 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_91 7 s (0,roots_91.map (·&&&dom_91)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_95 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_91 h
def symsG:List (List (Nat×Nat)):=[[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_95==dom_95)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_95 gM v ys):RunD true dom_95 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_95 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 10 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 54 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 54 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 113 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 113 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 61 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 61 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 11 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 11 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_95 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z3 i (Nat.zero_le i) hi
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
theorem lowS_111:Lower true dom_111 roots_111 goal_111 8:=lower_slice_b [(0xcccc0000cccc0000cccc0000cccc,32,34)] (by decide +kernel) lowS_109
namespace S_123
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(2,18),(2,34),(2,66),(3,11),(3,19),(3,35),(3,67),(8,9),(8,40),(8,72),(10,11),(10,26),(10,42),(10,74),(16,17),(16,18),(16,80),(24,25),(24,26),(24,56),(24,88),(32,34),(32,40),(32,96),(33,35),(33,41),(33,49),(33,97),(48,49),(48,50),(48,56),(48,112),(64,65),(64,66),(64,72),(64,80),(64,96)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_123.map (·&&&dom_123)
def gM:=goal_123&&&dom_123
def NN:Nat→Nat
|5=>5
|6=>27
|7=>16
|8=>4
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0x8264f5a551194340b67a09148
|6,0=>0x76b716536551c844f3fe419d63e75c3e1673d9d035c44356cc2e7992bb382b89929af2294581df341a2a715dc2104630f3a70b0ee0aa7d0593a03f55016c8015f7007ba
|7,0=>0x3ed4a36ae0353242cd922c917205631f1651dab61d04819f6a0fa540dbd309d39048d003cf302058
|8,0=>0x62b5b5f5a81cf4b07721
|9,0=>0x62b5b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f0f0f00000f0f0f0f0f0f0000f0f0f0f0f0f0f0f0f0f0f0f00000000f0f0f000f0f0f000f0f0f000f0f0f0000000000f0f0f0f000000000f0e0f0ef0a0f0a0f0a0f0a0f0a0f0a0f0a0f0af0f00000f0f00000f0f00000f0f0000f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0ef0f0f0f0f0f0f0f0f000f000f000f00f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0000c0f00000c0f00000c0e00000c0ef0f0f0f000000000f0f0f0f00000000f000f000f000f000f000f000f000f00c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0000f0f00000f0f00000f0f00000e0ef0f0f0f0f0f0f0f0000000000000000
|0,1=>0xf000f000f000f000f000c000f000ca0f0a0f0a0f0a0f0a0e0a0e0a0e0a0ef0f0f0f0f0f0f0f0f0f00000f0f00005050505050505050505000005050000f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c5050505050505050404040404040404f0f0f0f0f0f0a0a0f0f0f0f0f0f0a0a0030003000300030002000200020002005000500050005000400040004000400f000f000f000f000c000c000c000cf0f0f0f0f0f0f0f0c0c0c0c0c0c0c0cf0f000f0f0f000f0f0f000c0f0f000cf0f0f0f0a0a0a0a0f0f0f0f0a0a0a0af0f0f0f0f0f0f0f0f0f0f0f0f000f00f0f0f0f0f000f000f0f0f0f0f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00
|0,2=>0xf0f0f0f0f0f0f0f0f0f0a0a0f0f0a0af0f0f0f0f0f0f0f0e0e0e0e0e0e0e0e30303030303030303030000030300003030303030303030303030302020202f0f0f0f0f0f0f0f0f0f0f0f0f0f0000f000f0f0f000f0f0f000f0c0f000f0c303030303030303030303000303030000f000f000f000f000f000f000a000af0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c00f000f000f000f000f0000000f0000f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a0000000000000000f0f0f0f0f0f0f003030303030303030303030303030000e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0ef0f0f0f0f0f0f0f0f0c0f0c0f0c0f0c00000000f0f0f0f000000000f0c0f0c
|0,3=>0xf0f00000f0f00000f0f00000000f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0cf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a
|_,_=>0
def sP:Nat→Nat
|0=>0x1c52840a300529b1221c02a11030a00052840c27c014a10378201314a10370014a6c409a01914a1031c014a1030980052840c25c01542840c200f4ca1031c04052840c20052892030803ce3480c22840c230014a2480c71440c21801440c2040
|1=>0xe14d2840c200f38a10308014a12e54308014a1030ad00f14a1031c20052840c2b00ac53440c20052aa10308014a1030a900529b2031c214a0c70a80059dd11508a1150c28003c51030a602514a1220c09052840c201938a10308014a204883
|2=>0x52840c20052840c201114a1030803c52840c200e14a1030806452840c20052840c2c803d32840c201214a10308014a2c80c20313852840c200574a1150c2385c0a10308014a8440c2005bca1031c2005284b831c2
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x18609303180cc006
|6,0=>0x349d96ec475ebad9d5eea96513a6dd28e8d74339fdcf2c72735b991cbae56727b921c82e3a719b8b1c4ae1e7
|7,0=>0xa4bd09e76f34796bc9623cf16887bc1e1ff0f78783ba21c2ed98
|8,0=>0xb2b579eaef507
|9,0=>0x16b6
|_,_=>0
def wAt:=mkWire dB 51 124 0xfffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1034729080470d0804a11140450114a55090c05d0f28042012854f0114a552b100420110344961c54a010c043291619511744ca0108e45011404f0928543090804401080420d6c0440d09d8a01542c3013c242012854a59544c50908052294404b0d1004409100450114a4b0d1004409
|1=>0x1054a151404f092854e2b1404509285510110544011024e0d1404301280450108a5b01
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x3300000c00000
|6,0=>0x1792e1000acd49263484889010003a668c001822c4000001422443cc000001a42c849063
|7,0=>0x9e534a594928e514a194127e4f49d93926e4d4999312
|8,0=>0x14c690d11
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0x14288c040a633090054c1a04200503acc0706f300a1bcc02863300a185c0107f300388c000a7b7000400c0008020002004000633000188c00060a0001814000400000084000020400006000000820000200000060000008000001100000380000020000004000000
|1=>0x3400201840c0858027374001004802727
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x3004000
|6,0=>0x20701105514c18011301230000c08b00014a244
|7,0=>0x89881a75c7e16e48ce5e378d
|8,0=>0x3d6519
|9,0=>0x10
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 26 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_122 7 roots_122 ops++addP pm 1 dom_115 7 roots_115 ops++addP pm 2 dom_75 5 roots_75 ops++addP pm 3 dom_99 5 roots_99 ops++addP pm 4 dom_59 7 roots_59 ops++addP pm 5 dom_121 7 roots_121 ops++addP pm 6 dom_82 4 roots_82 ops++addP pm 7 dom_81 4 roots_81 ops++addP pm 8 dom_98 4 roots_98 ops++addP pm 9 dom_107 7 roots_107 ops++addP pm 10 dom_91 7 roots_91 ops++addP pm 11 dom_113 5 roots_113 ops++addP pm 12 dom_120 5 roots_120 ops++addP pm 13 dom_104 4 roots_104 ops++addP pm 14 dom_105 5 roots_105 ops++addP pm 15 dom_73 4 roots_73 ops++addP pm 16 dom_83 5 roots_83 ops++addP pm 17 dom_27 4 roots_27 ops++addP pm 18 dom_51 4 roots_51 ops++addP pm 19 dom_89 5 roots_89 ops++addP pm 20 dom_57 4 roots_57 ops++addP pm 21 dom_114 5 roots_114 ops++addP pm 22 dom_43 4 roots_43 ops++addP pm 23 dom_90 5 roots_90 ops++addP pm 24 dom_106 5 roots_106 ops++addP pm 25 dom_58 4 roots_58 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_123 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_98 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_120 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_104 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_58 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_122 7 s (0,roots_122.map (·&&&dom_122)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_123 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_122 h
def symsG:List (List (Nat×Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0x2222222222222222222222222222222222222222222222222222222222222222,1)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_123==dom_123)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_123 gM v ys):RunD true dom_123 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_123 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 5 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 27 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 27 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 16 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 4 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_123 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_207:Lower true dom_207 roots_207 goal_207 9:=lower_slice_b [(0xcccc000000000000cccc000000000000cccc000000000000cccc,64,66)] (by decide +kernel) lowS_205
theorem lowS_215:Lower true dom_215 roots_215 goal_215 9:=lower_slice_b [(0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa,16,17)] (by decide +kernel) lowS_214
namespace S_219
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(1,129),(2,18),(2,66),(2,130),(3,11),(3,19),(3,67),(3,131),(8,9),(8,72),(8,136),(10,11),(10,26),(10,74),(10,138),(16,17),(16,18),(16,80),(16,144),(24,25),(24,26),(24,88),(24,152),(64,65),(64,66),(64,72),(64,80),(64,192),(128,129),(128,130),(128,136),(128,144),(128,192)]
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
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xffffffffffffffff0000000000000000,64),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
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
theorem lowS_238:Lower true dom_238 roots_238 goal_238 9:=lower_slice_b [(0x444400004444000044440000444400004444000044440000444400004444,32,34)] (by decide +kernel) lowS_236
namespace S_245
def pG:List (Nat×Nat):=[(1,17),(1,65),(1,129),(4,36),(4,68),(4,132),(5,21),(5,37),(5,69),(5,133),(16,17),(16,80),(16,144),(20,21),(20,52),(20,84),(20,148),(32,36),(32,96),(32,160),(33,37),(33,49),(33,97),(33,161),(48,49),(48,52),(48,112),(48,176),(64,65),(64,68),(64,80),(64,96),(64,192),(128,129),(128,132),(128,144),(128,160),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffff
def xsM:=roots_245.map (·&&&dom_245)
def gM:=goal_245&&&dom_245
def NN:Nat→Nat
|4=>8
|5=>46
|6=>170
|7=>125
|8=>31
|9=>5
|10=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x5f2485bd3a3740812a031204e112240a2f809fe9
|5,0=>0x795285c0a755462524b74cc0a4c6ff48ccd379ed3759531aef30af82e3e52d77c2c0bb2ba452a8c0282c427cd12752c272ef2662725a9022f2d1f3f81cafd19b58161fa1521710dbe1033d0f0bb0dbfb0cdad0bcf60b99c09c19074740568d04e750361602c3201f94015780116f00bf800444
|6,0=>0x32f8c31c7c3120030af830a752d70a2ca372b6a52b3a82accf2aa4d29c52298b32927228eb7288a428800287ff285ec277bb27728276d3253ed252af24a0c23ee022e9822a4c21fe021de421ab3212b720cf620a99208e02058b203251fd141fb901f8ef1ef6d1ed481e59a1e3c01d9fa1d8211caa01a0cc19e9219a2e1960d194ed18deb184c01848f17ecf171ae16e7516e3816ad81667015e0415da915b2015b11157a3149ce13b40133d212994128f7124b211e9011c931106a10db2104ca100b10ff480f4fe0ece20e23c0e0ef0db9d0d6330d2160d0e00ccb60c6a00c3810c2820c1a00c1730ba2a0ae7c0ab5a0a64a0a0e609fb909dd009aef0958f09402092990903008e6a08b04086780831906b4a0687f0674a064dd0611b0517b0515a04d1304683045ca038f7037a30216b014c200f7900d8500857005220026b
|6,1=>0xb18d0a53dd706806f4fc6f2d36945164d8463c8560ff45d5445bffc5ae1b58a5255fda55cc454141540dc51c1e4f6c04c6ff4a99446dec42dfa42cad422ab421a741f2240f263fd823f78a3f7893d65e3d17c3cea53cd5b3a38e3a1ac391a337e4337931378c037496
|7,0=>0xc90e9a3f658a6e57d39f7ce036f2216d3016b5ab66fac593f2572185712656d25568d3561f055fce54fac4d02345d40433d341c5c40668405ca3e8643e3ff3bfb43b96d39a6537451369c5339e1332fc32a97329de3228931cf730943304c5300c02ee8c2cf6e2cc392b15a2af032a35a2957728db4286fe285a8284fd283af27dd3245222405423fb2231a52244021d74215fc20f4b1e99f1e9871e9721e1e91e1241d1f11bc8e1bb661b2a41a367194b7191871906317ecf164751556615307150e213ccd13bc0129a0128f81258411c1311c0b11bec11a9e1168a106be0fb350f2fe0eea10ebde0e61f0e3fa0d9670d7c00d2320cec50ad550a36409d490958f094f108ed808214075d306c0406693061c3056160415a03b5f035da0313902dc90283a0230101bc601a390105100ece00bd2009ac00904
|8,0=>0x81d56795b27905175d23687d361ebb57ec951d904c2644ac084673b453db3abae3731f269d3234181e9811c4391a52b1740014b000f8960e8f20bbde0ad740a5ee09a5e069d704fe8020c201a11
|9,0=>0xfdbf5bf1f12cd2a07d3705190
|10,0=>0xbf1f1
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcc00c000cc00c000cc00c000cc00c000cc00c000cc00c000cc00c000cc00c33003300330033000000000000000000330033003300330000000000000000cc00cc00cc00cc00cc000000cc000000cc00cc00cc00cc00cc000000cc00033003300330033003300330033003300330033003300330030003000300030cc00cc00cc00cc00cc00cc00cc00cc000000000000000000000000000000033003300330022003300330033002200330033003300220033000000330000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c33003300330033003300330000000000330033003300330033003300000000cc000000cc000000cc000000cc000000cc000000cc000000cc000000cc00033003300320032003300330032003200330033003200320030003000300030cc00cc00cc00cc00cc00cc00cc00cc0088008800880088008800880088008b3003300000000003300330000000000330033000000000033003300000000cc00cc00cc00cc00cc00cc00cc00cc00cc000000cc000000cc000000cc00033003300330033003000300030003000330033003300330030003000300030cc00c800cc00c800cc00c800cc00c800cc00c800cc00c8008800880088008b3003300330033003300330033003300330033003300330000000000000000
|0,1=>0xc000c0000000c000c000c0000000c000c000c0000000c000c000c00000003300330032003200330033003200320033003300320032003300330000000000000000000000000000000000000000cc00cc00cc00cc00c800c800c800c8300030003000300030003000300030003000300030003000200020002000200000000000000000000000000000000cc00cc00cc00cc00cc00cc008800880000000000000003300330033003300000000000000000033003300220022c800c800c800c800c800c800c800c800c800c800c800c800000000000000033003300330033002200220022002200330033003300330022002200220022c800c800c800c800c800c800c800c800c800c800c800c800c800c800c800cb3003200330032003300320033003200330032003300320033000000330000cc00cc00cc00cc00cc00cc00cc00cc00c000c000c000c000c000c000c000c33003300330033003300330033003300330033003300330022002200220022cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc000000cc000330033003300300033003300330030003300330033003000330033000000008800880088008800880088008800880088008800880088008800880088008b3003000330030003300300033003000330030003300300000000000000000
|0,2=>0x440044004400440044004400440044004400440044004400400040004000400003300000033000000330000003300000033000000330000002200000022cc00cc0044004400cc00cc0044004400cc00cc0044004400cc00cc0000000220022003300330022002200330033002200220033003300220022002200224400440044004400440044004400440044004400440044004400000044000030003000300030003000300030003000300030003000300030003000300000000000000000000440044004400440000000000cc00cc00000000000000000002200000033000000220000003300000022000000330000002200000022040004000400040004000400040004000400040004000400000000000000033003300220022003300330022002200330033002200220000000000000000cc00cc0088008800cc00cc0088008800cc00cc0088008800cc00cc0088008b3003300330033003300000033000000300030003000300030000000300000cc00cc00cc000000cc00cc00cc000000cc00cc00cc000000cc00cc00cc00033003300330030003300330033003000330033003300300030003000300030cc00cc00cc00cc00cc00cc00cc00cc00cc00cc0000000000cc00cc000000033003300330000003300330033000000330033003300000000000000000000
|0,3=>0x440000004400440044000000440044004400000044004400440000004400000003300000033000000330000003300000033000000330000003200000032440044004400440044004400440044004400440044004400440044000000003000300030003000300030003000300030003000300030003000300000000000000000000cc00000000000000cc00000000000000cc00000000000000000000000110011000000000011001100000000001100110033003300000000c000cc00c000cc00c000cc00c000cc00c000cc00c000cc00c000c000c000c0000330000003300000033000000330000003300000033000000000000000000000000440044000000000044004400000000004400440088008800880088000220000003300000022000000330000002200000033000000220000003200000000cc00cc0000000000cc00cc0000000000cc00cc0000000000c000c1100110011001100110011001100110011001100110011001100100011001000000000cc00cc0000000000cc00cc0000000000cc00cc0000000000cc00c3300330033002200330033003300220033003300330022002200220022002200008c0000008c0000008c0000008c0000008c0000008c00000088000000880000000300033000000000030003300000000003000330000000000300030
|0,4=>0xcc00cc00cc00cc00cc00cc00cc000000cc00cc00cc00cc00cc00cc00cc0003300330033003300330033003300330033003000330030003300300033003000000000000000000000cc000000cc0000000000000000000000c0000000c33000000330000003300330033003300330000003300000033003000330030000000000000000044004400440044000000000000000000440044000000033003300330033001100110011001100330033003300330011001100000000cc000c00cc000c00cc000c00cc000c00cc000c00cc000c00cc000000cc00003000300030003000300030003000300030003000300030000000000000000440004004400040044000400440004004400040044000400440000004400031003100310031003100310031003100310031003100310030003000300030cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc0088008b30033003300330033003300330033003300330022002200330033002200220000cc000000cc000000cc000000cc000000cc000000cc000000cc0000008b300000033003300330000003300330033000000330033003300000033000000000000cc00cc0000000000cc00cc0000000000cc00cc00000000000000033003300330033003300330033003300330033003300330033003300000000
|0,5=>0xcc00cc00cc00cc00cc00cc00cc00cc00c800c800c800c800c800c800c800ca3002300230023002300230023002300230023002300230022002200220022cc00cc000000cc00cc00cc000000cc00cc00cc000000cc00cc00cc000000000003300000033000000330000003300000033000000330000003300000000cc00cc00cc00cc00c800c800c800c800cc00cc00cc00cc00c800c800c800c80000000330033000000000033003300000000003300330000000000320032cc00cc00cc00cc00cc00c000cc00c000cc00cc00cc00cc00cc00c000cc00c330033003300330033003300330033003300330033003300320032003200320c000c000c000c000c000c000c000c000c000c000c000c000c0000000c00000000300000003000000030000000300000003000000030000000000000000c000cc00c000cc00c000cc00c000cc00c000cc00c000cc00c000c800c000cb30033003300330033003300220022003300330033003300330033002200220c000c00040004000c000c00040004000c000c00040004000c000c0000000000000003300330000000000330033000000000033000000000000003300000000cc000000cc000000cc000000cc000000cc000000cc000000c0000000c11001100110011001100110011001100110011001100110000000000000000
|0,6=>0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00c000cc00c000000000000000000000000000000003300330033003300330030003300300000440000004400000044000000440000004400000044000000000000000000000001100110000000000110011000000000011001100000000000000000c000c000c000c000c000c000c000c000c000c000c000c000c000c0008000b30033003300330033003300000000003300000033000000330000000000000000000000000000cc00cc00cc00cc000000000000000000cc00c000cc00c00000000000000000000000000000000330033003300330033003300330000c000c000c000c000c000c000c000c000cc00cc00cc00cc00cc00c000cc00c00003300000033000000330000003300000033000000000000003300000000cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc000000cc00cc00cc000110011001100110011001100110011001100110011001100110011001100000000000000000000cc00cc00cc00cc000000000000000000cc00cc00cc0003300330033003300330033003300330033003300330033003300330033000000000000000000000c000c000c000c0000000000000000000c0000000c00033003300330033000300030003000300330033003300330003000000030000
|0,7=>0xcc00cc00cc00cc000000000000000000cc00cc000000022002200220022003300330033003300220022002200220033003300220022000000000000000000000000000000000000000000000000cc00cc00cc00000000000000000000000000000000000000000000000000033003300220022000000000000000000000000000000000c000c000c000c00080008000800080000000000000000000000000000000330033003300330022002200220022440044004400440040004000400040004400440044004400400040004000433003300330033003300330033003300110011001100110010001000100010000000000000cc00000000000000cc00000000000000cc000000000000008b3003300330033000000000000000000330033003300330032003200320032000000000c000c00000000000c000c00000000000c000c00000000000000000000000000000000000000000000000000000000000000032003200320032cc00cc00cc00cc00cc00cc00cc00cc000000000000000000c800c800c800cb3003300330033003300330000000000220022002200220022002200000000cc00cc00cc00cc00cc000000cc000000cc00cc0000000000cc0000000000000000000330033000000000033003300000000003300330000000000220022
|0,8=>0xcc000000cc000000cc00000000000000cc000000cc000000cc00000000000000000000000000000000000000033003000330030003300300033003000000000cc00cc00000000008800880000000000cc00cc000000000088008b30033003300330033003300330033000000000033003300000000002200220c000c000c000c000c000c000c000c0008000800080008000800080008000800000000000000000003300000033000000000000000000000033000000000000000000000000c800c800c800c8000000000000000000c800c800c800c8000330000003300000033000000330000003000000030000000300000003000000000cc00cc0000000000cc00cc0000000000cc00cc0000000000cc00000000000000000000000000000000000330033002200220033003300220022000000000000000000000000000000000000cc000000cc000000cc000000011001100110011001100110000000000110011001100110011001100000000000000000000000000000000cc00cc00000000000000000000000000cc00033000000330000003300330033003300330000003300000033003300330000440044004400440044004400440044004400440000000000440044000000000000000000000003300330033003300000000000000000030003000300030
|0,9=>0xcc00cc00cc00cc000000000000000000cc000000cc00000000000000000000000000000000000330033003300330033003300000000
|_,_=>0
def sP:Nat→Nat
|0=>0x2921091128000e0407020500270807090526080706110b040f24110021072211000e04070214190b210d09110020121309110e0b0403111f0e0b1e070211000b04071d111c0e1b1a04070911041315110e10041609180b041315010e041615140e121302110b12030c110e040d0c010b080a09050008070605000403020100
|1=>0x1309320e0b040709340e0b210a0911000e04113c2e0e0b08030911003b3a0709110e0b130911300e0b040d09010b040709370e0b091136350e0b070934330e0b040d0932000b04021131000b04030c110e100d091130000b04071d092f0e04072f1c0e0b040215112e002d07092c0e0b04072b2a0e0b211309110e2004070911
|2=>0x709110e410b4f2304030911004e070911330e0b120709110e0b23400d0911000b044c0d09110e0b04070918114a0b040715110e1004070947000e0b0407460905000e04090511430e0b1e070c110e0b04070c010e0b4007093f0e0b07092b330e0b1e070918000b0409113e0e0b0709180535001b0407093d0e120702110b04
|3=>0x92b570e0b040f13092b0e0b04071d1709050e040709110e560b041309110e560b045509112e0e0b54080407090500040711530e500b040d09115200040d091100100b0413092b0e380b040717051c0e0b0709112f350e0b4f04030911001a04070905110004071511000e270403091151000e040f030211000407093f0e0b2d
|4=>0x407020911600b4425040709180004091411430e0b04075f0918050023401309110e0b1b40040709110e251a080709110b0407095e0e270b5d04030911000e450409112e0e0b044209110e3b0b44082107091100232109115c0e0b04075b02151100071509115a0e0b5425210709110004070211570e0b040702111c0e0b0407
|5=>0x91100440409112e0e0b040715092b000e040715110e560b2508070914000b040717141c0e0b041309110e100b04590711570e0b234007113c0e0b6304070911000b040709180500412d040709050e0b620409115c0e0b040702151100504f0407113c0e0b210709110e2004071511000e19040718113c000b040717181c0e0b
|6=>0x23210709110e04670715110e0b040709053d0e0b400709110e200b21040d091100386308040709110b0403070211004804071d0215110e04590302091100541b210709110e2d040711530e0b041307112a0e0b04075809110e0b08070911660004075b5f09110062040709640e0b044209110e380b0407151811004804075b1d
|7=>0x6d0b6268040709110e07170211350e0b1a08210709110b400407092b0e0b04070918006c0b04075f111c0e0b65080307091100210409112e000e0407171514000e4f63040709110b04071d0911000e0407116b000e0b2d040709140e0b04075b1d09050e236a09110e0b044e6907091100044e690d09110b540407093d0e0b68
|8=>0x407170c2f0e0b040709143d0e0b620407113c0e0b451b040709110e070911300e0b0469070c09110b04075b09180500040f0d092b0e0b210709110e26040d09110e560b040702151411002107092c11000e0407113c0e500b040d092b0e380b040717111c0e0b25070914700e0b4f2107091100046e030709110e0413092b0e
|9=>0xb1a40040709110b04071511000e100407730911000e046e070209110040070911700e0b040709053d000e040717095e0e0b040709117200040309110e10040771091100040d07112a0e0b040758111c0e0b04071d0918050e440807091100040709320e0b04590911510e0b040709340e0b235d0709110e0b04071d09181100
|10=>0x209340e0b0409112e770e0b40040911430e0b25040911430e0b0469130709110b044207093f0e0b0407760911000b040709140e6c0b04071d0905110e0409113e0e0b4404070918000409112e0e480b04070c09180500040717092f0e0b040739110e560b12070911000e0b0449070c110e0b2107113c0e750b040714113c0e
|11=>0x18050e0b04074609110e0b04071509117b0e0b04071d09110e0b4004070914110e0b250407097a0e0b04070c09112f0e0b04070911780e0b400709110e3b0b045809113e0e0b04070932000e0b04070934000e0b2107091170000e07091130000e0b04590709340e0b0f070911330e0b041309110e3b0b04071d0914110e0407
|12=>0x80407113c0e0b046e0f0709110e0b040709110e560b04071511000e480407091181000e040f0780110e0b5421070918110e0b7e040709110e0b0407170905000e04070c11000e480b2521070911000e7d04070911000e0b0469030709110e0b7c040709110e0b5404070911000b0407113c000e0b040709050e500b44040709
|13=>0xe21040d0709110021070911840e0b2540070911000e0b04091405112e0e0b0413070911570e0b040709140e500b04070911830e0b82040709110e0b6204030709110e0b0403070911000e4104420709110e0b04070209051100040709110e383b0b23400709110e0b046f4e0709110e0b54040709050e0b04070911000e200b
|14=>0x7091188000e2104070911000e505444040709110e0b040d070911870e0b4504070918110e0b2540080709110e0b04070911000e270b04075809110e0b6321040709110e0b86080709110e0b044e03070911000e044e0d0309110e0b040709110e100b4f040d0309110e0b04070911850e0b257f0709110e0b40040709051100
|15=>0x8070911000b4404070914110e0b040709110e48560b040709118b000e6223040709110e0b040702091100500b04071709110e270b040d0709118a0e0b04070905000e5004075f0911000e2304030911000e0821070911004504070914110e0b04075b020911000b40040d070911000b04077309110e0b041307150911000e04
|16=>0x3909110e380b04075f1709180e0b25080709050e0b40040709110e380b040f130d09110e0b0407170c11000e0b6563040709110e0b04130d09110e380b86040709180e0b040709118d000b0407091170000e0b0459070215110e0b04075b15110e0b040709118c0e0b4f68040709110e0b04075b0209050e0b0409112e0e0b25
|17=>0xb5d040709110e380b0442070911000e0b04075b1709050e0b0407580209110e0b040709110e50480b4425080709110e0b0407460911000e0b041307092b000e0b040709113d0e0b04075b170911000b04076a09110e0b440407090511000e046f070c09110e0b040709058d0e0b0407170914000e0b210407091411000e0407
|18=>0x9110e0b23040309110e0b400407113c000e0b040914112e0e0b400407113c0e0b040d03091100040709113d000e0b4f210709110e0b040f1309110e0b0459070c09110e0b0409112e000e0b04070914110e480b040f070c110e0b400709110e410b04070911870e0b0407580911000e0b6504130709110e0b040f130309110e
|19=>0x4070914110e0b04070c09110e0b04130d0709110e0b040709110e500b0459070209110e0b04070911000e480b4404070905110e0b040709118f0e0b04070918050e0b048e0709110e0b2104070918110e0b4f040709110e0b0407091811000b040f0702110e0b4f23040709110e0b040709110e410b040709118b0e0b04075f
|20=>0x709110e0b04070911000e0b040709110e0b04070905110e0b04071709110e0b08040709110e0b04079109110e0b0407091411000e0b0407150911000e04070c0911000e0b08210709110e0b25040709050e0b040d070911000b90040709110e0b0407090511000e04075f1709110e0b0407170911000e0b04070911000e410b
|21=>4
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x23501e50195014500f500a500550005
|5,0=>0x130612a6124611e61186112610c6106610150fb60f560ef60e960e360dd60d760d250cc60c660c060ba60b460ae60a860a2609c60966090608a6084607e60786072606d50685063505d60576051604b6045603f60396033602d60285
|6,0=>0x2e872e172da72d372cc72c572be72b772b072a972a2729b7295628e7287728072797272726b7264725d7256724f72487241723a7233722c7225721e721772107209720271fb71f471ed71e671df71d871d171ca71c461bd71b671af71a871a2619b7194718d71876181617a7173716c7166615f71587151714b6144713d71367
|6,1=>0x4a1649b6494748e6487748074797472746b7464745e6457745074497443643c7435742e7427742074197412740c640573fe73f773f073e973e273db73d473cd73c673bf73b873b173aa73a3739c7396638f73887381737a7373736c7365735e7357735073497342733b7334732d7326732063197312730b730472fd72f672ef7
|6,2=>0x5c175ba75b375ac75a5759e7597759075897582757b7574756d7566755f75587551754a7543753d6537653075297522751b7514750d750674ff74f874f174ea74e374dc74d574ce74c864c264bc64b574ae74a77
|7,0=>0x7a08798879087897781877a7772876a8762875a8752874a8743773b8734772c8724871d7715870e770776ff86f876f176e986e186d986d276cb76c476bc86b486ad76a6769e8697768f8688768086797671866a7663765c7655764d8646763f763786307628862086197612760b760475fc85f575ed85e675de85d775cf85c87
|7,1=>0x96d8966795f79596951894a7943793b8934792c8925791e7917790f890788ff88f788ef88e788df88d788cf88c788bf88b878b088a978a188998892788a8882887a8872886b7863885b8853884b8843883c7835782d8825881e7817780f8807880167fa77f287ea87e377db87d387cb87c387bc77b577ae77a86
|8,0=>0xa527a4a8a437a3b8a347a2d7a267a1f7a187a108a088a0089f979f279ea89e379db89d389cb89c479bd79b679ae89a779a079997991898a7983797c79757
|9,0=>0xa747a6e6a677a607a597
|10,0=>0xa7b6
|_,_=>0
def wAt:=mkWire dB 146 246 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xe0b41c39070b43c000b0e4501f11004242d0e0b4102d23000382d0e0b41039110b494000b0e424992500044110e0b41039070943454090b4102d092048c000e0b45c000e0b42439041043c000e0b41065090e45c000e0b4242d0f000382d110e41c6517000382d09114242d0f0002c39090b45c000e0b41041090e43c000b0e43c000b0e41c2d070e444410f0002c39
|1=>0x230e4101d041043c000e0b4241d070e410010e0b41d35150dc1c39090b52c392118c102d090b43c000e0b4241d4911c1d2109008382d11009141f440e4101509004106517000382d0911444410f000382d4211c1d050e0b4442d040c824010b0e42439041043c000b0e4241d112048c0007004382d040742c390439824e10e0b41c39111043c000b0e4241d112048c00
|2=>0x250e42c3904115642d02075602702054442d090e41c2511138342d070e45c39091141ce1093881c020e0b41c52180b44439081141039110b41c3904038382d070b43c0009074382d070e41c02111381c010e0b41439110b4201d040e42c39070b5103b04054442d0950844020e0b4301f09004382d090e42c39070b508470741410020e0b411411100810020e0b4382d
|3=>0x110e410010e0b4243911008242d0e0b48c00070442c39040b45c0009114242d0e0b444390940810010b0e4602d110e58439020381c2d0e0b4942d041141d1614044602d110e41425110e4382d110b41c0104004382d080b5502f040e4942d0411424020e0b41c020714844010e0b410e20e0b48445040b42c39040e48439040b4242d0211424390b0e41162151844439
|4=>0x20742439540bc2045040e4114111008382d6209c104d0d0b45c9d17008382d040e42c392107c102d170b45c390b0e4244511629943921074102d04008382d0900844395b0bc2461110e44c4707004242d0e0b41d220c09c5439090b444010e0b410390914844010e0b43c00070941c010e0b4342d070e4101d09408202d040e5883b4007410010e0b41002110b42c39
|5=>0x4114382d09148143909054100d040e41c2d040b41c52110042c3911004242d0e0b5883b4f0b41039580bc304509004382d0945900450400411410e0b56c2f02114243904074200c070b410394e0ec541d090b5383b15074242d080b41039230e4101d150d81c39440e410152300010010e0b41c1107008102d620ec200d070b41039090081c2d5b0bc0845090e41c2d
|6=>0x540b410390439824e107008382d6f0ec301d020b42461110b42c39110e44c470d0b41c3909074102d25000382d110441d5e1309c342d070e4243911004242d0e0b410021311c342d5809c5c010e0b41052050e4442d040b410350b0e41c396f0bd3839090341c2d072b8444e0d0b41c394f0bd3c2d040e424450c04c082d090e5103b21114102d111381c010e0b49402
|7=>0x740b45c030e0b42445590bc081d090e410010414844010e0b50047040042c3917008382d0805010390e0b4442d070b43c000b0e4241d210d0102d0e0b41c396209d3c2d040d450250914844010e0b56c2f091844439040e44485040b4382d112048c000e0b4101d6f07d642d0207410ed23008382d5b0bc6025110e43047150e4242d04004382d09408202d040e5142f
|8=>0x580bc2451180b445be020341c2d07148602d110e5141f40114202d4507c94010e0b5383b030e41c2d0741410020e0b5d0391700c382d0911445410450844020e0b5602f5f0e41425110e44485040b4382d09004442d0b0e4443917004382d07008382d041043c000e0b4241d07484382d043c90027210e4102d4009c10010e0b48439440ec102d090b43c000b0e4241d
|9=>0x70b494030e0b41045041842c39110e4250204004382d1411c1439110b41015110e4442d0950444020e0b45462110e56c2f0211424391100410010e0b4602f0411444390c11c082d090e5e42d0211c24392300810010e0b41d625f0e41425110b4448123000382d0407445be0c07424010414844010b0e410e6093841c020e0b5bc130f004382d074181c0104008382d
|10=>0x40b59439040341c2d04008382d070b41d0504008382d090e4382d110b41c020e0b4843907044102d4e0e4541d090b4442d08114103923000382d040750027080b41039590bc3c390907424e207008382d090b424020e0b42c392111c102d09074543b090b4102d1804444397f114843b040b424450e0b4442d0948424020e0b41045040b4382d2300c101d4e0ec240d
|11=>0xd0b41c39540b46011110e4202d0411410391148824020e0b57c3915114242d650ec841d040b4942f04114103909034382d070b40c25070b41c390f000382d090743411070b41c390803c1c2d040e41045210ec102d04004382d110b4102d0e0b41c39040b42047040e4104504004382d1407c1439110b4244e07004382d1100844010e0b4200e070b41039077f4843b
|12=>0x40e40845110b4243907148602d110e4382d041141039050e41015110b424020e0b424160e0b4442d23004382d110082c39090e45c020e0b48437040b444020e0b4442d11154242d0e0b4101d0b0e41c2d040b4382d040e41051180b444390211424390b0e410010e0b41c39890b45c3b091141c01090b4382d07158242d0e0b44402040b4382d250e4942d041144c13
|13=>0x40e45c390b0e42445080301c2d040e410150e0b4442d0c074082d090e4442d0418844390911444010e0b4102d110042c3907008382d170b4443909114103904114442d07008382d0d0b4241d070e424010e0b44425650ec841d040b44c1f0d0b41c39250bc1045110e410620e0b444390414844010e0b4242d020742439090b40845090e6342d0418844394f0bc201d
|14=>0x40e41c2d0b0e41c394011c10010e0b4201d040e4102d07004382d09074082d0207424390714844010e0b424020e0b45439090b41c250441410020e0b4104e07004382d0c11424010e0b40c11030e41c2d030e41c2d090741c020e0b41d0504008382d170e42445110b40815110b424391100824020e0b4942d0411410390950444020e0b4444e07004382d4011c202d
|15=>0x9004382d040b41039110b410450e0b41c39080bc1039110b4382d170b424450e0b4244504008382d11004382d020b424390d0b41c3911008382d02074243909008382d04054442d0807c1039110e4442d0f0bc241d110e4102d0807410390b0e44439090742439230e4101d04008382d09058442d15114242d040741c2d0940810010e0b41c5211004382d09408202d
|16=>0xe0b4442d091141039030ec1c2d11004382d090b4382d
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x1c602cc03a0043000800000000000
|5,0=>0x2fa85c30b26000000000000aa8000028284b50000000000004a1000011cc2128000000000001f2000007660000000000006e8000000003430000000019882f4054a09cc11a02030000074c0000194000000000b18115
|6,0=>0x22e8450c88990d4216441d081a0ff400003f487ca00001ea83c5076a0eb21d06394c70a0dd41b4635cc6a90d321a4233cc6690c9418e430d06018bd317642dd00000b341624000056a0aa314e6000051a09f4136826480000954124623cc461889310a820503f180000f481dcc39a07030d881a103388643
|6,1=>0x3ac87490e7980003986724ce319c4238266f8cdd21b7336686bd0d5a1a74346868840001a0233a6668ccb2192431c862ccc3a184330265f8cbd997832e885c4cb7196a42ce65948b1195e42b66560cab115422a445408a6214a228c85108a0993e327664e0c9a9932325c84a909321242244447cc00011b4
|6,2=>0x12c9a5544a28938d259a4740000910d20223d347468dcd1a1a31345c68acd13a2234440600010e20000430885890a1210441c48291039a04340087f10fc99f543e467c08f621e843c88784ceea1da3
|7,0=>0x62c6c4cd881b0d36146c1cd821b0135fc6becd7c1af535e46bbcd761ae935cc6b8cd701add35b46b5cd6a1ad1359c6b2cd641ac535846afcd5e1ab9356c6accd5892ae35566aa0d529aa2353e6a70d4c9a9635266a40d469a8a350e6a10d41127f34f869e4d3b1a7334e069b4d35926834ca6988d2f9a5c3
|7,1=>0x3c537846efcdde1bb9376c6eccdd81bad37564ea0dd29ba2373e6e70dcc9b9727286e44dc71b8b37106e14dc11b7f36f86de4dbb1b7336e06db4db51b6826ca6d88db0135d36b46d5cdaa1b51369c6d2cda41b4536846cfcd9e1b39366c6cccd98932e36584ca4d93932526446c7cd8e1b193
|8,0=>0x1010a01140027fc4ff09fd13f827ec4fd09f913f027dc4fb09f513e827cc4f909f113e027bc4f709ed13d827ac4f509e913d0279c4f309e513c82
|9,0=>0x409100010206038c061
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 15
def pmP:Nat→Nat
|0=>0x43800103000400000c00002c0000a000022000069000184000600001280004800011800044000108000400000a400021000080000100000380000c00002800009000020000060000140000400000c0000200000400000
|1=>0x2180008480021000082900208400808002010008020020040080000181c004200010200026e0009a00026000092800248000918002400008bc002290008500020c00082c0020800081c002060008100020200080000120
|2=>0x118bc04420010bf8042f8010ae0042b60109e0040f60101180404400b9bc02a6f0099bc022ee008b980227f00802002007008004020000069a0010040039bc00b6f002bbc00a6f0029b400a490028a000a200024a400864
|3=>0x8a9bc2222f0839bc20a6f0818bc202020629bc18a6d0620341880c0429bc108e8040280100200229bc088ee0220b00804002000006a6f01a9a406a2c01a82006264018834062090180b406005012bfc04a6f0120800466f
|4=>0x201020802002001ac8002b20000048008110b984225810802040aef102bac40a7f1029f840a6f102328408aa100b2840258100388400c9100308400c110020c3092f0c24a4309280c2484301290c00802462f09188424020
|5=>0x4229bd0886f42212100a6f400020a0a6f2829aca0a6928202ca022f28082ca02092801aca00492420bc88b6f2224bc8892822242484e6f2108bc82e6f2098a08260e2098248242920903c80e6f202cbc80a6f20201880802
|6=>0x20086980000950006522121488285029b910aef4429bd100e8
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x202020404000000
|5,0=>0xa0404000000080017090000000c0002420000002100040000003a00000200001d35171910020002000100000242
|6,0=>0xa54b360012720503c7011836873a533ab79b001c0122583d891008330433019726a01008070220599abb010d360128072c07207334360206510f058b0d83003a167a3815363d142a00113c00503b0e36369f2cad2d0107034c4a11a71087365e363700370d0038398000993e8a36005a4f206ec643641b00c8563d01be3a6d01
|6,1=>0x12122e079e140036220136210401360108220100a8007701393e046102013f081a054d032bc332100520
|7,0=>0x69b86b96665d9640b81e796a461f2f90238f86a137a6778c468446a713b6b7b539aeac299077988d7b7eb4c0887c5c8545602710b1133c01109caf936c2485684891702a0f304e6541468e5fc5c4bc5b62556752ab67b238b39254573146b1216c0b82326b74466f7ebf8154a3765307bd49826b9da9463646257d0575
|8,0=>0x92b971786ca44762a2b04845ba799546c245aa62babc7f637cc16346a2b094
|9,0=>0x4644a24862
|10,0=>0x46
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 22 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_244 8 roots_244 ops++addP pm 1 dom_228 7 roots_228 ops++addP pm 2 dom_209 7 roots_209 ops++addP pm 3 dom_181 8 roots_181 ops++addP pm 4 dom_197 5 roots_197 ops++addP pm 5 dom_117 8 roots_117 ops++addP pm 6 dom_229 8 roots_229 ops++addP pm 7 dom_165 5 roots_165 ops++addP pm 8 dom_240 5 roots_240 ops++addP pm 9 dom_213 8 roots_213 ops++addP pm 10 dom_212 5 roots_212 ops++addP pm 11 dom_241 8 roots_241 ops++addP pm 12 dom_196 4 roots_196 ops++addP pm 13 dom_85 5 roots_85 ops++addP pm 14 dom_149 5 roots_149 ops++addP pm 15 dom_113 5 roots_113 ops++addP pm 16 dom_177 5 roots_177 ops++addP pm 17 dom_180 5 roots_180 ops++addP pm 18 dom_101 5 roots_101 ops++addP pm 19 dom_116 5 roots_116 ops++addP pm 20 dom_225 5 roots_225 ops++addP pm 21 dom_193 4 roots_193 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_245 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_228 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_209 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_197 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_229 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_165 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_240 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_212 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_196 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_149 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_177 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_180 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_101 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_225 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_193 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_244 8 s (0,roots_244.map (·&&&dom_244)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_245 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_244 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28)],[(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xffffffffffffffff0000000000000000,64),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xffffffffffffffff0000000000000000,64),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_245==dom_245)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_245 gM v ys):RunD true dom_245 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_245 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 8 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 46 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 46 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 170 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 42 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 170 → Z 6 i = true := (range_split z6_0 z6_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 125 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 125 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 31 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 31 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 5 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s:Nat) (hs:s≤10):∀ i<NN s,bar dom_245 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤10) (h:RunD true dom_245 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_245 roots_245 goal_245 11:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_245
theorem lowS_245:Lower true dom_245 roots_245 goal_245 11:=S_245.noCircuit
def isoMvS_126:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_126:Lower true dom_126 roots_126 goal_126 8:=lower_iso_b isoMvS_126 (by decide +kernel) lowS_111
def isoMvS_159:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_159:Lower true dom_159 roots_159 goal_159 9:=lower_iso_b isoMvS_159 (by decide +kernel) lowS_95
def isoMvS_175:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_175:Lower true dom_175 roots_175 goal_175 8:=lower_iso_b isoMvS_175 (by decide +kernel) lowS_111
def isoMvS_187:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_187:Lower true dom_187 roots_187 goal_187 10:=lower_iso_b isoMvS_187 (by decide +kernel) lowS_123
def isoMvS_190:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_190:Lower true dom_190 roots_190 goal_190 8:=lower_iso_b isoMvS_190 (by decide +kernel) lowS_111
def isoMvS_222:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_222:Lower true dom_222 roots_222 goal_222 9:=lower_iso_b isoMvS_222 (by decide +kernel) lowS_207
def isoMvS_231:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_231:Lower true dom_231 roots_231 goal_231 9:=lower_iso_b isoMvS_231 (by decide +kernel) lowS_215
def isoMvS_235:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_235:Lower true dom_235 roots_235 goal_235 10:=lower_iso_b isoMvS_235 (by decide +kernel) lowS_219
def isoMvS_237:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_237:Lower true dom_237 roots_237 goal_237 10:=lower_iso_b isoMvS_237 (by decide +kernel) lowS_219
def isoMvS_243:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_243:Lower true dom_243 roots_243 goal_243 10:=lower_iso_b isoMvS_243 (by decide +kernel) lowS_219
def isoMvS_246:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_246:Lower true dom_246 roots_246 goal_246 10:=lower_iso_b isoMvS_246 (by decide +kernel) lowS_219
def isoMvS_249:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_249:Lower true dom_249 roots_249 goal_249 10:=lower_iso_b isoMvS_249 (by decide +kernel) lowS_219
def isoMvS_250:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_250:Lower true dom_250 roots_250 goal_250 10:=lower_iso_b isoMvS_250 (by decide +kernel) lowS_219
theorem lowS_127:Lower true dom_127 roots_127 goal_127 11:=lower_slice_b [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,32,36)] (by decide +kernel) lowS_123
theorem lowS_223:Lower true dom_223 roots_223 goal_223 11:=lower_slice_b [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,64,68)] (by decide +kernel) lowS_219
theorem lowS_239:Lower true dom_239 roots_239 goal_239 11:=lower_slice_b [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,32,34)] (by decide +kernel) lowS_237
theorem lowS_247:Lower true dom_247 roots_247 goal_247 12:=lower_slice_b [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,16,18)] (by decide +kernel) lowS_245
namespace S_251
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(1,129),(2,18),(2,34),(2,66),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(8,9),(8,40),(8,72),(8,136),(10,11),(10,26),(10,42),(10,74),(10,138),(16,17),(16,18),(16,80),(16,144),(24,25),(24,26),(24,56),(24,88),(24,152),(32,34),(32,40),(32,96),(32,160),(33,35),(33,41),(33,49),(33,97),(33,161),(48,49),(48,50),(48,56),(48,112),(48,176),(64,65),(64,66),(64,72),(64,80),(64,96),(64,192),(128,129),(128,130),(128,136),(128,144),(128,160),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1ffffffffffffff
def xsM:=roots_251.map (·&&&dom_251)
def gM:=goal_251&&&dom_251
def NN:Nat→Nat
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|11,0=>0xff75e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x1ac688
|_=>0
def sO:Nat→Nat→Nat
|11,0=>7
|_,_=>0
def wAt:=mkWire dB 7 252 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 7
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def pmP:Nat→Nat
|0=>0xfc0
|_=>0
def pmB:Nat→Nat→Nat
|11,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 1 (j%128);fld (pmP (k/32)) 6 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_250 10 roots_250 ops++addP pm 1 dom_187 10 roots_187 ops++addP pm 2 dom_249 10 roots_249 ops++addP pm 3 dom_243 10 roots_243 ops++addP pm 4 dom_235 10 roots_235 ops++addP pm 5 dom_219 10 roots_219 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_251 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_219 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_250 10 s (0,roots_250.map (·&&&dom_250)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_251 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_250 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0x2222222222222222222222222222222222222222222222222222222222222222,1)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_251==dom_251)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_251 gM v ys):RunD true dom_251 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_251 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_251 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def isoMvS_191:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_191:Lower true dom_191 roots_191 goal_191 11:=lower_iso_b isoMvS_191 (by decide +kernel) lowS_127
def isoMvS_253:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_253:Lower true dom_253 roots_253 goal_253 12:=lower_iso_b isoMvS_253 (by decide +kernel) lowS_247
def isoMvS_254:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_254:Lower true dom_254 roots_254 goal_254 11:=lower_iso_b isoMvS_254 (by decide +kernel) lowS_239
def dzo_155_4:=0xf0f0f0f0000000000000000000000000f0f0f0f0
def gzo_155_4:=0xf0f0f0f0000000000000000000000000e0e0a000
def gsh_155_4:=0xf0f0f0f0000000000000000000000000e0e0a00
theorem lowS_zo_155_4_27:Lower true dzo_155_4 roots_155 gzo_155_4 5:=lower_iso_b (d1:=dom_155) (r1:=roots_155) (T1:=gsh_155_4) [(dom_155,4)] (by decide +kernel) (lower_slice_b (T:=gsh_155_4) [(0xf0f0f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_27)
def dzo_59_4:=0xf0f0f0f0f0f0f0f0
def gzo_59_4:=0xf0f0f0f0e0e0a000
def gsh_59_4:=0xf0f0f0f0e0e0a00
theorem lowS_zo_59_4_27:Lower true dzo_59_4 roots_59 gzo_59_4 5:=lower_iso_b (d1:=dom_59) (r1:=roots_59) (T1:=gsh_59_4) [(dom_59,4)] (by decide +kernel) (lower_slice_b (T:=gsh_59_4) [(0xf0f0f0f00000000,0,32)] (by decide +kernel) lowS_27)
namespace S_255
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(1,129),(2,18),(2,34),(2,66),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(4,36),(4,68),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(6,22),(6,38),(6,70),(6,134),(7,15),(7,23),(7,39),(7,71),(7,135),(8,9),(8,40),(8,72),(8,136),(10,11),(10,26),(10,42),(10,74),(10,138),(12,13),(12,44),(12,76),(12,140),(14,15),(14,30),(14,46),(14,78),(14,142),(16,17),(16,18),(16,80),(16,144),(20,21),(20,22),(20,52),(20,84),(20,148),(24,25),(24,26),(24,56),(24,88),(24,152),(28,29),(28,30),(28,60),(28,92),(28,156),(32,34),(32,36),(32,40),(32,96),(32,160),(33,35),(33,37),(33,41),(33,49),(33,97),(33,161),(48,49),(48,50),(48,52),(48,56),(48,112),(48,176),(64,65),(64,66),(64,68),(64,72),(64,80),(64,96),(64,192),(128,129),(128,130),(128,132),(128,136),(128,144),(128,160),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffffffffffffffffff
def xsM:=roots_255.map (·&&&dom_255)
def gM:=goal_255&&&dom_255
def NN:Nat→Nat
|6=>14
|7=>114
|8=>474
|9=>405
|10=>141
|11=>30
|12=>5
|13=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x9a1f877e937142067b185792043adf3f3fe35c3b2f5b3156af1559711ca809dce04f42
|7,0=>0xf33b4e7bdae49bcd2095cb498c4d97bdf73b99fdb8f6fb0363ac537ac32aabc40a72dea6e80a164f96a929553394d658791984ed17b0c97a1347954f774ca771e07324e6d96a6c35968ae2663fb63a6f627f06161161534607a5606775e0f15dcc15939750be34ba9f4b9a7496cd489a1477734743a461c9456c544a9044123432d8429ee3e86c3e5c93db973d06a3cdd639ad5392be36c3735f3834c43326bf30f192f4502f0512af9328d2728c1724bdb2458b2427623b23236d8236aa2340e230f8224fd223f0204941f0011e1141d2c91ad851accf19dd018c3c1883e17196150c214f3f14886139c111b9a1005f0fce80fab90ec140bf680bec40b9430b601084370716706967045ed030700278c011a5010ef00e630042e0021d
|8,0=>0x1989f19788193d31931d18f4118729186fd17c2e179d417900176e3174c1173ef1702116bc31607815dea15d4e15bb3157c5155f3155d314a6a148ca1451814462144161430c13f8413c5e13a8a139761373f135ec1314a12f9612d4012c8c12a181220812095119c91178a113b5105d9102150fdb50fb670f9650f87c0f0520ed300eb0e0e8da0e8550e6330e5570df660df260dd4b0dd0f0dcb60dc100db220da210d8b30d3be0d2e50ce080c1040c07e0c0220bd170b2700b04f0afee0aef30ae140ad240a6410a4570a2fe09fbe09bb8098f1098a708fe208f3208d63086cf086b1082d3082c907b3307acf07a4a0790206fac06ae4069f40680806483057ae0564e05437053da048a1045c60453b03c070377b0343e032da0311a02f9502e3a02cf402bb602a2b0278d0263e01bf701a1b0179d01667014d9006e90043f
|8,1=>0x3c0013a46339ddc390c038fa5388d8387f43748b3723936c25366e036365357c735610354b2353ef3520e34f7f34ccb3480d3446c33aea3388233760331cb322803210e31d5d31c3f31bae3156830c5630c353047e2fdde2fc4f2fc162f3302f2b32f23e2edb22ecfc2e0672dfbf2dae62d6e12cd462cc3c2ca432ca0c2c9de2c3af2bbaa2b92a2b5192b3b92b3402b1d62ac772aaac2a5242a2f02940128d272856d284a42809c27d7027a5c276762764e27633274e2270372666025a8f25938257f92579b253d024d7024d5124cc724b4a2496a2434d239e723479233f323229230c722cdb2275f21e3921dff218ed215632120820fc720bb82085e2065f1fc611f7541f3821ecde1ec261eb6f1d8b81d8361d46e1cc431c5c51baf01ba861b9161b7131b6c91b65d1b3ad1b3721ae111a7561a6981a13c1a0b019f7d19e23
|8,2=>0x7771c772d7767297660474e9274b787414e73a2e7383b72caf7245172214718c46fa556f3156f0b56e4126da9c699ce646f56408463eef6337a62feb62ab56253861ec261dd761133608395fdd95f2aa5f0b85ef765ea7f5ea655e7945e6c05e4075e3825da2a5d7265bd2b5bc755b1325a5175990359653595965763e572e65706756f5256f1b562d35616754d3d5402353de2539b8539b6539af5318752a28524a05226b521f251b9f514ca51401510cc5073e4fd3b4f8254ec734e5e14dd114dd0f4dbbe4d1654c79b4ba9f4b72e4a16249dee49c3d49b434963c493c8493524890b4861d4810147c6047b5e479f245d5245b4044cb343dbb43941436404362c432ae42e9a42b20427414210b41e9241a424112f40389401793fca43f9e33f77d3ef573ee6e3edf43d9f83d93a3d6383d5823d2f63ce7d3cd383c8fc3c087
|8,3=>0xfce2ef9f61f70cee5d9de2d91d86b5d53e2d0970cf50bce4e7cc97ecc31fcb498c827ac65bfc4b24be261bbaf7ba780b9a52b7908b7581b269db21bfb1069b0e8bb0bdbb01e4adcdfada28acbc8abfcfabd0ca9a06a89e9a6beea3679a2b16a214ca0ae6a05739e9be9e7d39cc629a1cc97f649694d963fb954539490592d2191c399113a907818d15c8cbd68c8568c1b08bc298b8d28aeae899d48991388b7988a8e8894c87b8387012869c98699685ec885ca0853d084cc2827e4822a982141812437ffc37fbeb7e1337db3579a2c7978e78e0478d2778c4d7812a77c2077b5c
|9,0=>0x1e3011e1ad1e0e41de581ddfc1dda61dda21da221d6f61cfa11cafe1c5b41c4a51b2cb1b0701ae7a1adbc1ad0c1aaea1a9851a48b1a2a31a1f519cab19b4b190df1909b183fb18355182d11818b17eea17dfb17617171c516ea4167b6164e715f6115daf15a5315555153bb14afe14977144181430413bfe13a6f13589134511317712cb212a23129e01236811e4511dfb119d311980118f411815112b310133100360f8e80f7640eb8a0e9440e63d0e5340da5f0d6770d30b0d0320cf470ce6b0cc3e0c8050c4610c0db0bea60bddb0ae1c0a6080a54609d4109b2c0983b0950e093b30918e0903f08f3b088630870e082de081fd081970781406e1806d73068af0682b0677506618064ff05dbc057ce05399052cc04b3004923047c3045130425903bb603715033b902b3801f5600dce00d84007fa007740060b003de0002c
|9,1=>0x4a0414926548fab48d2a488744766a4699b46861463e44601e45e8945576446e4430cf42c25420c041e06412c240a1e405ff3f4443f2b63f1f53eed93e7203e37c3dfdf3de7a3dac73cf553caca3c9783c0113b9803b9063b4ab3b2073ae3c39e9d39e1e38766386a33837c37f6936c2536bcf3625d35dde359ae35731351cd34428338013368e32ac631b1b315e43115130ab8308753011c300832f90d2f6be2f33f2efc92e45d2e0342de7f2dafb2d2ea2cd0a2ca952c74e2c4902c31f2c04f2be8a2bdd12b7712b4d92ad3b2aa052a7e22a7c82a62d2a35529709294bd290c328e0528c242888428630278ac2743426f7d26c9b26a18261f026131260e625d5e25a38249922407e23e6f23b1f237a322fc622e2d22c1f2241b2224121bca219292115720dad20caf2062f205a320226201891f9651ed971eb841e46e1e381
|9,2=>0xbfcbfbe089bcd25b975eb8563b75dcb4c06b009dace79ac8bcaa483a9f3aa656da214ca13599dc2b9dbda9db1e9bf309bb7199a769863a97b3b95d0f95ae894ce49479093d61935d790bc7903d58fd3b8fa798f57a8d3248ae7088b428878388612881cb87b06876a38614283b24838fc83310826bf7f6887d6607cdfb7bf9a7bf3a7bdda7b8397b211799b57864377d5577afa76b8275ab675a6a743bc73230719e16f3026f2616e6516e42a6d1a86cd656c5a06be766b3706b2886a35c69148689a065eb865500652c56422963fcc63f9c63e626239a615ff60d4f5ff975fa465e7615e3825d7de5c6035c3185bf4d5b73e57acd57a41570c0562265524454fe254d3c548af547125403953f0c533b65332452c09524a0519665152a513b55106d504594fe6f4fcad4f2b34cd8d4b8934b7424b6b44b5184ac044a4c84a416
|9,3=>0xfb3e0fa2f2f7e6bf70cef6242ec9d0ec189e91aee74ece5dc6e4e5fddc5bd9167d1d5bd0895cc06bc602fc5fa7c4d88c26a8c1faa
|10,0=>0x9d5bc9d4438f6358ebcc89d6e8568a806587d8ee7bc8e7b29a7a3437868477ef17716976c6b767c8758be7517472b29706af7015c6a66c68e24682ff67eaa6572164d835eae15e7615cad25b72b5a85659a9e5998a5871156cb455cdb55cb453b4b51f195140e4ed2f4dfdd4caf04ca1f4c88a4c7764b66c4b1b44a9b74975d45ff1453e043956430fd42d324215341a0041498405e83c7df3b45e3a64e39d17374ed36403360bf35d4033496324df2e93e2e2ad2d33c2bafe2b3932af1f2a7032823a270b42695825d412576822ea6210f3204171edfc1ecf51dbc61d92f1cf5a1ce331c4e91be1b1b7421b3781aa2d1a68019b5e18bdd1868915c6a147b21450c13f06132061287d1174a10c9c1005a0d7740d2ec0a7ba0a06508b25077cf071b90710306e7906dc50612d05e62047a504544043a90204b0175c0141700b7d
|10,1=>0xf6393ed9cee465cdb337d01f2cf8dfbfe10bebcebbc0db9476b6bdba9a3ca31f5
|11,0=>0xf43cfed44ae9e94d6bf3b9af3b4f9ba46ac856317a3df5d9114b5b34697f407183dd1c32ff03018a2ee582c48c2558c24abe196b713f93108a60e7be0c7af0c11306dd304aa30290102655
|12,0=>0xf9c0764c784da8f340e91641b
|13,0=>0x43e5c
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x50505050505050500000f0f00000f0f05050f0f00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ffffffffffffffffffff0000ffff0000aaaaaaaaaaaaaaaaaaaa0000aaaa0000ffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000ffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00fffffffffffffffffffff0f0fffff0f0fafafafafafafafafafaf0f0fafaf0f0ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000
|0,1=>0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa00000000000000000000ffff0000ffff55555555555555555555ffff00000000ffffffffffffffffffffffffaaaaaaaaffffffffffff0000ffffffffaaaa00000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0000ffffffffffffffffffffff00ffffff00ffaaffaaffaaffaaffaaff00ffaaff00ffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffffffaaaa0000000000000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffaaffffffffffffffaaffffffffffffffaaff00ff00ff00ff00ffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffffffaaaa333303033333030333330303333303033333030333330303333303033333000000af00af00af00af00af00af00af00af00af00af00af00af00af00af00aa00aaffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffffffffffffeeeeeeeeeeeeeeeeffffccccffffcccceeeecccceeeeccccffffffffffffffffffffffffffff0000ffffffffaaaaaaaaffffffffaaaa00000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000
|0,2=>0xffffffffffffffffffffffffffff0000aaaaaaaaaaaaaaaaaaaaaaaaaaaa000000ff00ff00aa00ff00ff00ff00aa00ff00ff00ff00aa00ff00ff00ff00aa00aa000f000f000a000f000f000f000a000f000f000f000a000f000f000f000a000a0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000a0a000000000000ffff000000000000ffff000000000000ffff000000000000aaaaffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaa0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaffffffffffffffffffffffffaaaaaaaaffffffffffffffffffffffffaaaaaaaa0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0affffffffffffffffffffccccffffcccceeeeeeeeeeeeeeeeeeeecccceeeeccccffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff00003333333333333333333333333333333333333333333333333333333333330000ffffffffffffffffaaaaaaaaaaaaaaaaffff0000ffff0000aaaa0000aaaa0000ffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000
|0,3=>0xff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000aa000f000f0000000f000f000f0000000f000f000f0000000f000f000f0000000a3333232333332323333323233333232333332323333323233333232333332222333333333333333333333333333333333333333311111111333333331111000003030303030303030303030303030303030303030101010103030303010100003333333311111111333333331111111133333333111111113333333311110000333333333333333333333333333333333333333333333333333333333333222255555555555555555555555555555555555555555555555555555555000000000000ffff0000ffff0000ffff0000ffff0000aaaa0000aaaa0000aaaa0000aaaaffffffffffffffffffffffffffffffffffffffffffffffffffffffffaaaa000033330303333303033333030333330303333303033333030333330303333302020f0f0f0f050505050f0f0f0f050505050f0f0f0f050505050f0f0f0f050500000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00aa0000555500005555000055550000555500005555000055550000555500000000ffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffff0000
|0,4=>0x55555555555555555555555555555555555555555555555555555555555500000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f00000a0a00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff000000aa5555555555555555555555555555555555555555555555555555000055550000ffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaa000f000f000f000f000f000f000f000f000f000f000f000f000f000f000a000a0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000aa00aafffffffffffffffffafafafafafafafafffff0f0fffff0f0fafaf0f0fafaf0f000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000000000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000a00000000ffffffff00000000ffffffff00000000ffffffff00000000ffff000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00aa00aa00000000ffffffff00000000ffffffff00000000ffffffff00000000aaaaaaaaffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff00005555555555555555555500005555000055555555555555555555000055550000
|0,5=>0xffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000aaaaffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffaaaafffffffffffffafafffffffffffffafafffffffffffffafaf0f0f0f0f0f0f0f00000000000000000ffffffffffffffff0000000000000000ffffffffffffaaaa0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffaaaaffffffffffffffffffff0000ffff0000ffffffffaaaaaaaaffff0000aaaa0000ffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00aa333303033333010133330303333301013333030333330101333303033333000033333333333311113333333333331111333333333333111133333333333300000f0f0f0f050505050f0f0f0f050505050f0f0f0f050505050f0f0f0f000000000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000aaaa0000aaaaffffffffffffeeeeffffffffffffeeeeffffffffffffeeeecccccccccccccccc00000000000000000000000000000000ffffffffffffffffffffffffffffaaaa0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000aaaa5555555500005555555555550000555555555555000055555555555500000000
|0,6=>0xffffffffffffffffffffaaaaffffaaaaffffffffffffffffffffaaaaffffaaaaffffffff00005555ffffffff00005555ffffffff00005555ffffffff0000000000005555000055550000555500005555000055550000555500000000000000000f0f0f0f000005050f0f0f0f000005050f0f0f0f000005050f0f0f0f000000000000000055555555000000005555000000000000555555550000000055550000ffffffffffffffffffffffffffffffffffffffffffffaaaaffffffffffffaaaaafafafafafafafafafafafafafafafafafafafafafafafafafafafafaaaaaaaaffffffff00000000ffffffff55555555ffffffff00000000ffffffff55550000ffff5555ffff5555ffff5555ffff5555ffff5555ffff5555ffff5555ffff0000aaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaaaaaffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0000000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000aa00bb00bb00bb00bb00bb00bb00bb00bb00bb00bb00bb00bb00bb00bb00bb00aaffffffffffffffffffffffffffffffffffffaaaaffffaaaaffffaaaaffffaaaa0f0f0f0f0f0f05050f0f0f0f0f0f05050f0f0f0f0f0f05050f0f0f0f0f0f00000f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000a
|0,7=>0x303030303030303030303030303030303030303030303030303030303030000aaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffaaaaffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaaaaaffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff000000000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff000000000000000000000000ffffffff00000000aaaaaaaa00000000ffffffff00000000aaaaaaaa5555555555555555555555555555555555555555555500005555555555550000ffffffff55555555ffffffff55555555ffffffff55555555ffffffff55550000ffffffffffffffffffffffffffffffffffffffffffffffffffffaaaaffffaaaa0000000000000000000000000000ffff0000000000000000000000000000aaaaffffffff00000000ffffffff0000ffffffffffff00000000ffffffff0000aaaaffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffaaaa0000333300003333000033330000333300003333000033330000333300000000ffffffff0000ffffffffffff0000ffffffffffff0000aaaaffffffff0000aaaaffffffffffffffffffaaffaaffaaffaaffffff00ffffff00ffaaff00ffaaff00ffffffffffffffffffffffffffffaaaaffffffffffffffffffffffffffffaaaa
|0,8=>0xaaaaaaaaffffffffaaaaaaaaffffaaaaaaaaaaaaffffffffaaaaaaaaffffaaaa0000000000000000ffffffffffffaaaa0000000000000000ffffffffffffaaaaffff0000ffffffffffff0000ffffaaaaffff0000ffffffffffff0000ffffaaaa0000000000000000000000005555555500000000000000000000000055550000ffffffffffffffff0000000055555555ffffffffffffffff000000005555000000000000333333330000000033333333000000003333333300000000333300000000ffff0000ffff0000aaaa0000ffff0000ffff0000ffff0000aaaa0000aaaaffffffffffffffff00000000ffffffffffffffffffffffff00000000ffff000000000000ffffffff00000000ffffaaaa00000000ffffffff00000000ffffaaaa55555555555555555555555555550000555555555555555555555555555500000000000000000000000000000000000055555555555555555555000055550000ffffffffffffffffffffffffffffffff5555555555555555555500005555000000000000555555550000000055555555000000005555555500000000555500005555555555555555555555555555555555555555555555550000000000000000ffffffff55555555ffffffff55555555ffffffff55555555ffffffff000000000000000000000000ffffffffffffffff0000000000000000aaaaaaaaaaaaaaaa
|0,9=>0xffffffffffffffffffffffffffffffffffffffff55555555ffffffff555500000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f050505050f0f0f0f05050000000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0000ffffffffffffffff000000000000ffffffffffffffffffff000000000000aaaaffffffffffffffffffffffff0000ffffffffffffffffffffffffffff0000aaaa00ff00ff00ff00ff00ff00ff000000ff00ff00ff00ff00ff00ff00ff000000aa0000000000005555000000000000555500000000000055550000000000000000aaaaaaaaaaaaffffaaaaaaaaaaaaffffaaaaaaaaaaaaffffaaaaaaaaaaaaaaaa5555000055555555555500005555555555550000555555555555000055550000ffffffffffffffffffffffffffffffff00000000ffffffff00000000ffff0000ffffffffffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaaffffaaaa0000ffff0000ffff0000ffff0000ffff0000aaaa0000ffff0000aaaa0000aaaa0505050505050505050505050505050505050505050505050505050500000000aaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaaaaaaaaaaaaa0000aaaa0000ffff0000aaaa0000ffff0000aaaa0000ffff0000aaaa0000aaaa00000000ffffffff00000000ffff000000000000ffffffff00000000ffff0000
|0,10=>0xffff0000ffff00000000000000000000ffff0000aaaaffff0000ffff0000ffffffffffffffffffff0000ffff0000ffffffffffffaaaa00000000000000000000000000000000000000000000ffff000000000000aaaaffff0000ffff0000ffff0000ffff0000ffff0000ffffffffffff0000ffffaaaaffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000aaaa0000ffff0000ffff0000aaaa0000aaaa0000ffff0000ffff0000aaaa0000aaaa000000000000000000000000000000000000ffff0000ffff0000aaaa0000aaaa0055005500550055005500550055005500550055005500550055005500000000ffffafafffffafafffffafafffffafafffffafafffffafafffffafafffffaaaa00000000ffffffff00000000ffffffff00000000aaaaaaaa00000000aaaaaaaaffffffffffff5555ffffffffffff5555ffffffffffff5555ffffffffffff00000f0f0f0f0a0a0f0f0f0f0f0f0a0a0f0f0f0f0f0f0a0a0f0f0f0f0f0f0a0a0a0a00000000afafafaf00000000afafafaf00000000afafafaf00000000aaaaaaaaffffffffffffffffffffffffaaaaaaaaffff0000ffff0000ffff0000aaaa0000ffffffffffffffff5555555555555555ffffffffffffffff55550000555500000f0f0f0f0f0f0f0f0f0f0f0f050505050f0f0f0f0f0f0f0f0f0f0f0f05050000
|0,11=>0xffffffff00000000ffffffff00000000ffff000000000000ffff0000afafafafafafafafafafafafafafafafafafafafafafafafafafafafafafaaaa00000000ffffffff00000000ffffffff00000000ffffaaaa00000000ffffaaaa0000050500000505000005050000050500000505000005050000050500000000ffff0505ffff0505ffff0505ffff0505ffff0505ffff0505ffff0505ffff0000ffffffff00000000ffffffff00000000ffffffff55555555ffffffff55550000ffffffffaaaaaaaaffffffffaaaaaaaaffffffffffffffffffffffffffffaaaa000000000000000000000000000000000000000000000000ffffffffffffaaaaffffffffffffffffffffffffffffffff0000000000000000ffffffffffffaaaaffffffffffffffffffffffffffffffff0000ffff0000ffff0000aaaa0000aaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffaaaaaaaaaaaaaaaaaaaaaaaaffffaaaa1111111111111111111111111111111111111111111111111111111111110000555555555555555555555555555555555555000055550000555500005555000000000000ffff555500000000ffff555500000000ffff555500000000ffff0000000000000000000000000000000000000000ffff0000ffff0000ffff0000aaaaffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000aaaa
|0,12=>0xffffffffffffffff0000000000000000ffffaaaaffffaaaaffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffaaaa00000000000000005555555555555555000000000000000055555555555500000000000000000000ffffffffffffffff0000000000000000ffff0000ffff000000000000000000000000ffff0000ffff00000000000000000000aaaa0000aaaa0000000000000000000000000000000055555555555555555555555555550000ffffffff55555555ffffffff55550000ffffffff55555555ffffffff55550000ffffffffffffffffffffffffffffffff555555555555555555555555555500000000000000000000555555555555555500000000000000005555000055550000ffffffffffffffff0000ffff0000ffffffffffffffffffff0000aaaa0000aaaaffffffff55555555ffffffff55555555ffffffff55550000ffffffff555500005555050555550505555505055555050555550505555505055555050555550000ffffffffffffffffffff0000ffffffffffffffffffffffffffff0000ffffaaaa00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000a0affff0f0fffff0505ffff0f0fffff0505ffff0f0fffff0505ffff0f0fffff00000f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000000
|0,13=>0xffffffffffffffff0000000000000000ffffffffffffffffffffffffffffaaaaffffffff00000000ffffffff00000000ffffffffffffffffffffffffaaaaaaaa0000000055555555000000005555555500000000555500000000000055550000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffffffffaaaaffffaaaa00000000000000000000000000000000ffffffffffffffffaaaaaaaaaaaaaaaa000000000000000055555555000000000000ffff000000005555ffff000000000000000000000000ffffffffffffffff0000000000000000ffffffffffff000000000000ffffffff000000005555555500000000ffffffff0000000055550000ffffffffffffffff00000000ffffffffffffffffffffffff00000000aaaaaaaa0000ffff0000ffff000000000000ffff0000ffff0000ffff000000000000aaaa00000000000000000000000000000000ffffffffffffffffffffffffaaaaaaaaffff0000ffff0000ffff0000ffff0000ffffffffffffffffffffffffffffaaaa0000000000000000000000000000000000000000ffffffff00000000ffff0000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffaaaaaaaaffffaaaa00000000ffffffff00000000ffffffff00000000ffffffff0000000000000000aaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaa
|0,14=>0xffffffffffffffff0000000000000000ffffffffaaaaaaaaffff5555ffff5555ffff5555ffff5555ffff5555ffff5555ffff0000ffff0000ffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffaaaaffffffffffffffffffffffffffffffffffff0000ffffffffffff0000ffffaaaa000000000000ffff000000000000ffff000000000000ffff0000000000000000ffffffffffff0000ffffffffffff0000ffffffffffffffffffffffffffffaaaaaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffaaaaaaaaaaaaffffaaaa000000000000ffff000000000000aaaa000000000000ffff000000000000aaaaffffffffffffffffffffffffffffffff000000000000ffff000000000000aaaaffffffff00000000ffff000000000000ffffffff55555555ffff000055550000ffffffffffffffffffffffff55555555ffffffffffffffffffffffff55550000ffffffffffffffffffffffffffffffff00000000ffffffff00000000aaaaaaaaffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffff00000000000000000000000000000000000000000000ffffffff00000000ffffaaaaffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffaaaa00000000000000000000000000000000ffffffffffffaaaaffffffffffffaaaa
|0,15=>0xffffffff00000000aaaaaaaaffff0000ffff0000ffff0000ffff0000ffffffffffffffffffffaaaaffffaaaa0000ffff0000ffff0000ffff0000aaaa0000ffff0000ffff0000ffff0000aaaaffffffff00000000ffffffffffffffffffffffff00000000ffffffffffff0000000000005555555500000000555555550000000055555555000000000000000000000000000000000000000000000000ffffffffffffffffffffaaaaffffaaaa
|_,_=>0
def sP:Nat→Nat
|0=>0x806040e20030d2508130e09030d2507000e2309030d1f0a221d1309030d0107000409030d011e001d090301071c000e0903120710000513030d12070005041b0d01000e1a03010c1000041309030201001809170d010a1613030d010c000e090715140806041309030d1200110903010710000e090301070f00050403020100
|1=>0x1323030d011f0a0420030d012f08161320030d011f000e0901072e2d08060e230301072c08061820030d010719161320030d012a081820030d01072b0005040302010806130e090302010700052723030d010a000420030d011f2900041309030d012100160e030d0121000420030d012a29080e1a0b03011f26060504030d25
|2=>0x9030d1f3a00060e0903073d1008060e0903073c3b08060e1a2003012a10080e09030d2a3a08060e090307391008060e230903011f0a10050b030d012a38060e0b20030d012a380513030d011f3700361d09030d0107000e0903010a3400080e090307352608060e0903010a3408060e090107333208060e23030d011f310605
|3=>0x274b09030d014c004a09010749480806040e09034701000e1a2003012a2608040b030d012a2b060e090107144608060e090107324508060e090d01073208060523030d011f0a44090d0138434208060e1a2003011f1000410420030d014000050e1b0d0107000e0903011f1037000e0901073f3e0806161823030d010a000e
|4=>0x49080641040b20030d012a0e09030757550806161823030d012a060e09030756550806520e030d010754080e090307393308060e230903011f0a334b09030d530708520e030d010751080e0b0d012a073f060e030d014c5108060e0b030d012a50060e090d07393208060e0b030d011f31060e0901074e4d08060504030d010c
|5=>0x20030d011f31001809035d0107060e09030d01071e0013090107494808060e09030107211000525c0e09030d01070e1a0b0d012a43060e0b030d5307060e20030d011f190e0b200d010743000e0901072c3f08060e0901075b4308065209030d01075a081109030d0107000e0b03011f072c06130e1a030d0121000e58090107
|6=>0x2a0e090d0722630806050e030d1207000e0b2003010726000e620903011f10000e0b0d011f073f060e0b030d011f50060e09030756610806040b030d011f2b060409030d012f000e090d07224308060e2003012a072c080e090107604308060e09030d1f3a08065f5e030d01070806050b030d011f380609030138264208060e
|7=>0x1074c100806160e20030d012a00080e23090301075b0806304b09030d012a07000e67030d016608060e650901071408060e090107496408060e090d07223208060e090301075b08060e030d014f5108060e090107334308060e1a0b0d011f430628090107494808060e0901075b320806030d0107515a0806184b1a23030d01
|8=>0xd011f0700240e2309030d011f0a30042309030d010a08721809030d0107000e1a0903011f2608060e09710d010a08050e030d01070c00520e6f09030d010a080e090301076c08065f0e0b030d010700060e20030d01076b006a0e2009030d011f000e0903016907460806130e090301075b0806046809030d011f08060e0903
|9=>0x5c0e6f09030d010706307509030d010708060e23090d0107430806300420030d010a080520030d01075a08060e090301660710080674520e09030d010708740e09030d014c08060e6f2320030d011f0a030d01072944080670304b09030d0107000e1a23030107330806240e09030d073908060e20030d072273080605272003
|10=>0x320806054a23030d01070008410e09030722330806130e1a0b030d012a06410e030d07222908060409030d010a2b0806050e6223030d011f06050e23030d011f0a006a161809030d0107000e2009030d073a08066a0e0b20030d011f06184b7709030d0107000e09030107103108060518030d010737000e7709030d07220806
|11=>0xe090107101408064109030d017e0708062809030d01075a08060e09030715100008060e0901074349000806410e6209030d011f000e090d01072e080641181a20030d010a080e6f6223030d010a08160e030d012108060e6209030d010a7a001809030d010779000e0b09030d011f4f06045e09030d010a0806160e090d0107
|12=>0x5b0806040e09030d010a84080e20030d012a0751080e0b09030d011f83060e23090307223308060e090d0107432908060e23030d072229080605810903010755080652304b09030d010708700e2309030d010a080e09030d0739000806050420030d0180080e20090307227f08060523030d017e070806740e09030107260806
|13=>0x9030d017e0708060e58090d01074308060e2309030d0a072208410e620b030d011f06130e6209030d011f000e09030d010a8700700e20030d010a08410e1a23030d010a080e6709030d012a08060e20030d010786004b0e1a23030d012a08130e090307223308060e6f09030d014f080605186220030d0107006a0e09030107
|14=>0x11f078b06704b6f09030d0107000518030d0107540006180e20030d010754000e09030d011f0a29000e6709030d011f0006054a09030d011f004b0e1a23030d011f006a0e0b20030d010700410e0b20030d012a073009030d07228a0806050420030d012a080e1a030d0121002404090301071008060e030d01078988080613
|15=>0x161809030d012a000641272009030d010700050420030d011f000e09030d010a5008062709030d01075a0806300e1a0b030d010a000504030d011f5408061309030107104408060e09030d01663108060e1a20030d072208060e8d20030d0107000420030d01072908066a0e090d01074308065f0e0b030d012a07060e09030d
|16=>0x1070870270e09030d010a008e0e20030d010a084a0e09030d014c08060504230b030d011f0604130903010a100008165c1809030d01070670520e20030d010708520e0b09030d01070005130b030d012a0706130e0b20030d012a070420030d0107290008270e09030d011f0a7b1809030d01078300060e23030d01072b0806
|17=>0x192072e08064a0e09030d014c00085c280e09030d010706410e620b030d0107000e23030d0107910806410e6f20030d010700740e090d01073208060e20030d018f0a08240409030d014c08060509030d012a380806240e030d01075108060e2009030d012a3808300e0b20030d011f0a0e0903012a38260806524a0e09030d
|18=>0x1320030d01070008160e09030d01980806240e030d0107540806040b09030d012a42060e5e09030d01970806780e09030d011f08060e0b090301072600060e09030d2a073908060e030d0195079408060e0903012a269308060e2009030d011f3800054b23030d012a07086a0e6209030d011f000e09012a07434908060e090d
|19=>0x708054a0b030d01070070160e20030d0107006a0e620b030d011f060e20090301073408065c0e0b20030d0107060e77090301071008069b0e090d01079a0806280e09010710430806054b23030d011f07000e09030d011f0a440013090d01074342080652270e09030d010a080e0b0903012a0710062809030d013842080616
|20=>0x90301079e08060e030d0107545a08060513090301072608061309030107339d08060e091b0d0107000e090301074c330806240e030d07227308066a1809030d010700300e09030d01079c06410409030d014f08060e23030d010731080652300e09030d0107000e0b090301075b0806700e09030d07390806051323030d010a
|21=>0x14c0806041309030d014f08060e090d01073f0008060513030d01073700080e6f090301071000060e090301072c080641040b20030d010a08160e230b030d010a080e1a23030d010a4408410420030d014008060e090d011f38430806050e1b0d0107080630042309030d011f063009030d07224408060e090d01073208060e
|22=>0xe09030d014f08060e09030d014ca60008810e09030d075608060e09030107a40806130903010710a3080605040b030d012a0a06040e0b20030d012a0a0e09a2030d010a08520e7709030d01070813090d01074348080652160e20030d0107082709030d0138420806051367030d010708060e09030107a1a00806160e20030d
|23=>0x6050e23030d010a4c080e0b090307223308060e0b0903012a0726060e030d0107914408064a0e090d0143a808060ea709030107100806051820030d012a0700300e090301075b08065f0e23030d01070806304b1a0b030d010700050b030d0107380006240e090307227f08064a0e090d01073208060409030d012a2b080627
|24=>0x30d010a00410e1a23030d011f060e090d01074d0806740e09030d010708064109030107334408060e1a20030107100008184b2309030d012a07304a09030d0107000e09030107103700080e77090301072608067809030d0107830806520e6f09030d0107005f0e090301072c08060528090d0107430806280e090107264308
|25=>0x64b09030d011f0744000504030d010c0806040e20030d010c08130e09030d01070c000e0b030d01072b080604130903012a100806700e030d01075108061309030107334408060e09030d010a4f08060e09030d011f310806300e1a0b030d012a06040e0903470108062404090301073308062404030d0107290806040e620b
|26=>0x10754080605040b030d012a00060e0903019207a408060e0b030d01079108060509030107381008060e6f090301075b0806410eac030d01070806410e0b030d012a0700a50e090301076108061d0e09030d0107000e09030d010a4f00080e090d012a073f0806161809030d010a000527090d01074308060e09030d012a5008
|27=>0x80e0b030d012a07290641042009030d012a08300e620b030d011f065c0e09030d010700060e6f090d0107430806160e20030d018008ae0e0b030d01070806052709030d011f0a000e030d014c540806130e09010710140806700e20030d0107000e77090d01073208060e09030d010a8300080e0b090d011f074306700e030d
|28=>0x30d018f07000e09010710430008060e090d0107435108060e2009030d0107b008410e030107332908061109030d010700160e20030d012a08285e09030d010708060e0b030d016607080652130e09030d0107080e090d011f073208061809030d01075a00062809030d01072b080624042309030d010a08520e2309030d0107
|29=>0x72b0806050e23030d011f0a130e0b030d0107b3001109030d0107080641040b20030d011f06160e230b030d011f0604132009030d011f000e09030107340008061309030d0107b208060e0959030d010700160e030d01075108060e2309030107260806160e20030d011f007009030d01075a0806706a0e09030d0107000e20
|30=>0x2409030d07228a0806050e030d011f37000e1a030d011f5108060e09030107262908060567030d0107380806526a0e09030d010708280e090301075b08060e090107434908060e09030d01b51f0806720e09030d011f00047809030d014c08060e090d010743540806054a030d01075408060e09030d0722b408062709030d01
|31=>0x2a06b90e09030d010a08060e20090d01074300084a0e090301269308060e09010726430008060e77030d014c540806b70e09030d010700086a0e090301072608064a0e090107434908060e090d01074db6080605280b030d01070006280e0b20030d0107009f0e090301079e0806054a09030d01380806410e090d0107320806
|32=>0x30d010a21304a20030d010a070805ab030d0107b60806780e09030d073a08060ebb0903010710080604130b20030d0107001609030d01075a08060e09030d012a4f08060e1a090d012a430806740e030d01075108060e09030d530708066a160e0b030d011f060523030d0107380806130e090d0107320806280e1a0b030d01
|33=>0x80670524b09030d0107080e65090307151008067409030d01075a08060e0b20030d012a07420e0903011f382608060e0b030d011fbd060e20030d010708190e0903010710bc0806050423030d012a0806184b09030d010754002409030d07224408064a0e09030d010aaa000e1a23030d014f08065f0e0b030d011f07060e0b
|34=>0xd011f4c060e20030d0107310008184b1a09030d012a00040b09030d011f42060e0b030d012a07bf00270e0b20030d012a070e09030d1f07390806280e09030d072208060e0903011f269308067c0e09030107a4080670300e20030d010a080e090301be073308060e1a0b030d011f44060e09030d074c3a08060e090d01073f
|35=>0x9030d010719060527090301072608067d0e09030107c008061309030d0107830806185e09030d010700060e0903010710510806161309030d012a0806240e030d0722290806240409030d013808060513030d01075408060e20030d012a072b08300e6220030d0107000e090301075b000806041309030d07220806050e0b03
|36=>0x4c3408066a4a0e0b030d0107004a186209030d0107000e6f090301072608060e2309030d0739080670520e09030d010700130e090107434908062409030107104408060e0b0903011f0726060409030d012f0806052823030d010708060e6f6220030d011f000e77030d01075108060e0903470107000ec10903010755080618
|37=>0x9030d014c420806240409030d014f08060ec309030d010708060e0b030d011f072906050423030d014c08060e6f090d01073208060e0903010726c20806520e2009030d0107080e1a0903012a1008060e090107104308060e09030107265108060e0b20030107100024040b09030d011f06130e1a20030d011f000e09030107
|38=>0xd011f060523030d01075a08062409030107334408067d0e090d01072e0806164b0b030d011f066a182009030d0107000e23030d0722730806050e030d120708060e200903011f071000160e090301075b08061613090301071008060e09030d017e830806160e23030d012a08060e09010726430806166e09030d010708060e
|39=>0x23090301073408060e770b20030d011f0a130e09010710430806130e0b2003010710000e09035d010708060e090301075b0806240e030107332908060e09030107c4100806740e090d0107430806740e090301075b0806280e090301073308060e65090301690708060e6f030d014c5408061309030d01075a0806280e1a0b03
|40=>0x20030d010700700e6f09030d010a0806040e09030d019208060e0b09030d011f074406050e20030d012a1f0708c51809030d0107080624300e09030d07220806740e090301071008066e0e090301076c08060e09030d01075a08060e77090301075b0806280e09030126930806160e23030d014c0806240e090d01073208060e
|41=>0x776f030d01075408060e1a030d012a5408060e6f09030d0107440806280e2309030d010708060e230b030d0107540806161820030d0107080674700e09030d010708060e0903012a1f072608060e0b20030d012a1f07180e09030d01074c00065f0e09030d0107000806240409030d01070008060e20030d0107540008410e0b
|42=>0x1809030d012a00060e6f20030d012a0708130e090d01074308060e09030d017e070008060e770b20030d011f0706280e09030d01380806130e09030107260008060e09030d01070c000e1a23030d011f0605130b030d01070006130e0b20030d010700040e0b09030d012a0641042309030d010708060e09030d01070899060e
|43=>0x80604132309030d0107080670304b09030d01070806240e7709030d01070806052720030d011f070806130e1a09030d012a08060e2309030d0107420806160e23030d01070806050e030d01070c0806058109030d01070806050e030d0107c608060e20030d01076b08066a0e2009030d011f0806130e0903012a0710080604
|44=>0xd01380806050e0b030d012a070006130e1a09030d011f00060518030d0107370806040e09030d011fc7080604182009030d010a0824410e09030107330806130e0903011f0710000630040b09030d010700060e2309030d011f0a0024410e030d01072908060e6f20030d011f07000e1a0b030d014c0806280e09030d010729
|45=>0x6040e2309030d010a08c90e09030d01070006040e09030d010a540806270e09030d013808060e7709030d01075a0806240e23090301073308060e6209030d010a7a08061809030d0107790806240e23030d01072908060e0b090301071000060e1a20030d012a00080e09030d0107c808066a161809030d0107080604130903
|46=>0x70806240e2309030d010a0708050e2320030d011f07060e20030d012a075408411809030d0107006a0e2009030d01070008410e2009030d012a07080e6f0b20030d010a080e09030d010a07ca0806280e090d010743000806041309030d01072908066a280e09030d0107080624130e09030107330806410e6209030d011f08
|47=>0x30d011f070074160e09030d010708060e62230b030d010a07080e09030d010a8708060e09030d011f075a0806160ecc030d010708060513090301071008064b0e6f0b09030d010700750e09030d010708060e20030d0107860806130e09030169071008065f0e09030d012a0708060e2009030d0107ad080605186220030d01
|48=>0x60e2309030107330008060e62030d0107540806050e6223030d01070806050e23030d010a0700080e09030107260806054a09030d011f08066a0e0b20030d010708060e09030d0107cd0806040e2309030d014c0806130e2009030d012a07080e1a030d012108060e7720030d0107540806240e1a20030d01070806410e2009
|49=>0x9030d010708060e09030d010a380806050420030d011f0806051309030d011f070006410e6209030d01070008410e09030d07220806130e2009030d011f0700300e1a0b030d010a08060e09030d019507960806160e0b030d011f060e0b09030d01074f08060e8d20030d010708060e0b030d0107b300704b6f09030d010708
|50=>0x80e09030d010a38000870270e09030d010a0806281309030d0107420806040e09cc030d010a080e0b09030d01078308060e09030d01d2070806780e09030d01074c0806520e0b09030d010708060e09030d01077608060e1a09030d01d00806300e09030d012a070006410e0b20030d011f0706ce0e09030d01070806412720
|51=>0x107000806054a09030d010700084b0e1a23030d01070008050e09030d011f0a000e09030d012a07900006410e620b030d0107080670300e09030d01070006130e6209030d01070008410e6f20030d01070806240e2009030d07220806184b2309030d0107000e2309030d072208064a0e0903010726080641042009030d010a
|52=>0x50420030d01070008040e7709030d011f0806300e09030d01074f0806780e09030d010708060e6509030107100806280e09030d011f380806054b0b030d010700040e0b09030d012a1f06d40e09030d010708064b09030d0107440008180e7709030d010700060e09030d010a07290008280e090d012a074308060e6709030d
|53=>0xe09030d010708060e2309030d01075a0806700e7709030d010708060504230b030d01070806054a0b030d0107080670160e20030d0107080609030d0107da0806d90409030d01070806050e0b030d011f0a06270e2009030d010a080e09030d0107d808067c0e09030107c008060e09030d0107d608060409030d011f420806
|54=>0xe09030d010a070806040e6f09030d011f0006df0e09030d010708064b0e1a09030d011f00180e09030d0107b30005de09030d010708060e091b0d010708066a1809030d010708060e09030d0107dd00080edc09030d010a08060e7709030d014c0806050409030d01db08060e6f09030d010a00243009030d01074408065230
|55=>0x7e20806050e0b030d010a0700051323030d010708064b0e1a0b030d011f060e09030d010a074400080e5e09030d010708060e09030d011f4c08060e09030d01072b08060ee109030d010708067d7c0e09030d010708060509030d010738000806180e2309030d010a07006a0e6209030d01070008130e1a09030107100806ba
|56=>0x520e6f09030d010708060e0903011f072608064a0e1a20030d010a086e0e09030d010708060e2009030d0107e4080e1a230b030d010a080ee1e309030d01070806270e09030d01078c08060e09030d0107910806040e09030d012a540806304b1a0b030d01070806740e09030d01070806240e0b090301073308060e09030d01
|57=>0x166070806040e0b09030d014c08060e2309030107100806040e620b030d010a0806054b09030d011f07000e1a09030d010a420806744a0e09030d01070806040e09030d010a087be50e09030d01070806050e23030d012a0708064a0e09030d011f000e090d012a0a0743080605282709030d01070806304a09030d01070806
|58=>0x220806700e2309030d010708060e09030107102908061d0e09030d01070806300e09030d010a07000e6f0b20030d010700280e6f09030d010708060e09030d012a380806050409030d012a0008060e2009030d010a7a080e09030d01073108060e09e6030d010708060e2009030d0107b608280e0b09030d011f07060e09030d
|59=>0x240409030d01070806280e0903010710000806280e09030d0107510806052709030d011f0a08060e09030d010a0790000523030d01074408064109030d01074408060e09030d0107870006700e20030d01070806410e1a23030d010708060e09030d012a07290806052809030d010a0708060e090301075508060e0b09030d07
|60=>0xd011f0706180e2309030d012a0706130e09030d0107b300088e0e20030d01070806041309030107100008061109030d01070806280e09030d0107540806740e7709030d01070806270e09030d011f077b06130e090301072608060e090d012a07430008061309030d0107440806300e1a0b030d010700060e09030d011fa600
|61=>0x806280e2009030d01070008280e0903010726000806270e09030d0107540806720e09030d011f08060e0959030d01070806740e09030d011f0708060e2309030d011f0a160e20030d011f08060e5e09030d011f070806706a0e09030d010708060e09030d0107e708060e1a20030d0180080e20030d018f070806300e0b2003
|62=>0xe09030d012a1f3808060e23090301073308064a0e0b09030d012a0706160e230b030d01070806ea0e09030d010708060e1a23030d01074408060e09030d01e9070008160e20030d010700080e1a230b030d011f06050e030d011f370806280e1a09030d012a08060e7709030d010708060e1a20030d011f00280e090d010743
|63=>0x930806052809030d012a0708060e09030d01077900085f0e09030d011f07080674130e09030d010708060e6f09030d01075a08066a160e09030d01070008740e2309030d01070806050e030d01073700084a182009030d010a07080e09030d010a21080e09030d01980708069b0e09030d0107c608064a0e7709030d01070806
|64=>0x1070008060509030d0107380806160e09030d012a000806050e0b030d012a1f0706130e09030d0107310806050e030d010754000806161809030d01070006130e09030d01660708064a0e09030d010aaa08060e09030d0107510008060e2009030d012a074208050ecc030d010a0708130e09030d01074c08060e0903010710
|65=>0x4b09030d011f07000e090d0107430008060e2309030d017e070806e01809030d010708060e0b09030d011f4c06270e0b20030d011f070624041309030d010708060e09030d011f0a7b0e771a20030d011f0806165c0e09030d010708060e09030d01660729080624280e09030d010708060e09030d010783000806b80e09030d
|66=>0x1070806050e030d0107cb080628130e090d010743080670520e09030d010708060e09030d0107b208060e6f6220030d011f08060e09030d0107ed0806050e7723030d010708060e09034701070806050409030d012a08066a0e09030d01070008300e6220030d010708060eec2009030d010708060e09030d012a0751080627
|67=>0x301072608060ec309030d01070806a50eee09030d010708060e09030d017e0744080604182309030d010700060e09030d01075008065c0e09030d01070806161309030d0107000806410e2309030d010a07086a4a0e0b030d010708064a186209030d010708060e090301690710000806280e09030107100806130e7709030d
|68=>0x1070806050e030d01075408060e09030d0107510806130e090d0107430008064b0e6f09030d0107000e6f20030d010a080e1a23030d012a08066a182009030d010708060e0b20030d011f0a0e1a09030107100008060e09030d01075a000806740e6f09030d010708060e23030d01075408060e7709030d0107440806280e09
|69=>0x8060e09030d01070819067d0e09030d01070806160e09030d0107089906161309030d0107080605040b030d011f06184b1a09030d010700270e09030d0107c708060e090d01074308060e090301072600080628130e09030107100806b80e09030d010708062409030d01074408060e7723030d010754080674280e09030d
|70=>0x70806044b0b09030d010708060e2009030d012a1f07080e776209030d010708060e0b09030d01078206410e2009030d01070008040e2309030d01070008060e7709030d010a0708060e2309030d01078308060e1a090301071008060e09030d0107310008060e09030d01075a0806130e09030d0107510806740e09030d0107
|71=>0x9030d01070806050e6f0b030d010708060e09030d01070c08060e09030d0107c608060ef009030d010708060e090301071008060e772009030d011f070806410e0b20030d01070806051309030d0107000806130e2009030d01070008300409030d01070806ef0e09030d01070806180e6209030d0107080628130e09030d01
|72=>0x6411809030d010708068e0e09030d01070806410e6209030d010708064b0e09030d012a0700080e2009030d01074408060e1a23030d010708060e09030d0107d708060e09030d010708f1060e7709030d01070008064a0e09030d012a0708060e6f20030d011f0708060e0b09030d012a070006700e09030d010708066a0e20
|73=>0xe2309030d010708060e0b030d0107b3080624410e09030d01070806130e1a09030d0107000806410e2009030d011f0708060e622309030d010708064b0e6f0b09030d01070806160e09030d011f08060e77232009030d010708060e09030d0107b30008040e0b09030d010700060e09030d018f070806300e0b09030d011f07
|74=>0x30d0107b308060e6f09030d010a0806810e09030d010708060e0b09030d011f0a06054b0b030d010708066a0e6209030d010708060e1a0b030d011f06050e09030d011f0a0806050e23030d01070008060e09030d0107dd0806054b09030d010700080e7709030d012a0708060e1acc030d01070806050420030d0107080624
|75=>0x9030d0107c70806130e09030d012a0708060e2009030d0107a908060e2309030d012a0708064b0e1a09030d01070008130e09030107100806050e0b030d010a0708060e09030d01074c0806280e09030d012a0a0708060e0b09030d010a0700040e09030d014008060e09030d0107290008064b0e1a09030d011f0806180e09
|76=>0x64a0e09030d01070008280e09030d012a070008060e09030d0107f30806300e09030d010a0708060e6f0b20030d01070806f20e09030d01070806040e2309030d010708060ee309030d01070806240e0b09030d010708060e772309030d0107000806050e0b030d010700060e09030d0107440008064a0e09030d011f08060e
|77=>0xe0b09030d011f060e7709030d010708060e0b09030d012a07060e09030d010790000641042009030d01070806c50e09030d010708060ef409030d01070806040e09030d012a0a08060e09030d0192070806040e09030d01db08060e09030d011fa60806050e09030d01078008060e09030d010a07900806051309030d010708
|78=>0x708040e09030d0107087b060e622009030d010700080e1a09030d010708d106050e23030d010708060e1a230b030d010708060e2309030d01074c08060e1a20030d01070008130e1a09030d010708066a160e09030d010708060e09030d010a075408064b0e09030d011f07000e6f09030d010700060e1a20030d011f080604
|79=>0x10708060e09030d012a074208060e09030d0107440806274b09030d011f0708060e1a09030d012a000806280e09030d01070008060e09030d01072908060e0b09030d012a1f07060e09030d0107540008060e09030d0107bd0806050e09030d012a1f0708060e09030d0107f5080670300e09030d010708060e09cc030d010a
|80=>0xe0903010710000806184b09030d010700184b1a09030d01070806160e09030d01070008060e0b20030d010700280e09030d010708060e09030107100008064b0e0b09030d011f070628130e09030d0107000806164b09030d01070806130e09030d01072908060e09030d0107086d06050409030d0107000806410e1a20030d
|81=>0xd01070008060e1a09030d011f0806160e09030d01070806054b09030d010708060e09030d0107b308060e6f0b09030d010708060e09030d011f070006040e09030d011f08060e09030d012a070806180e09030d010700060e09030d0107800806300e0b09030d01070806180e09030d010a0708060e232009030d0107080613
|82=>0x8060e0b20030d010708060e6f09030d010708060e0b09030d011f07060e09030d0107087b060e09030d010708d106130e09030d010708060e09030d0107a608064a0e09030d01070806050e09030d01070008060e0b09030d010a0708064b0e1a09030d01070806050e09030d010a070806130e09030d01070008060e230903
|83=>0xe09030d010708060e09030d01070008060e09030d011f0708064b0e09030d010708060e1a09030d01070806040e09030d01070806184b09030d01070806050409030d010708060e1a09030d010700
|_=>0
def sO:Nat→Nat→Nat
|6,0=>0x161c05170129c043700f58036700bdc02960089c01b70051c00d70019c0006
|7,0=>0x9360245808f9c236808ba02268087a02168083a0206807fdc1f7807be01e87078201d88074201c88070201b8806c201a8806820199706460189806060179805c60169805860159805460149805060139804c601298048601198044601098040600f9803c9c0ea8038a00da8034dc0cb8030e00bc702d200ac80292009c80255c08d80216007e701ddc06f8019e005f8
|7,1=>0xf5e03cf80f1e03bf80ede03af80e9e039f80e5e038f80e1e037f80dde037070da2036080d62035080d22034080ce5c33180ca6032180c66031180c26030180be602f270baa02e280b6a02d280b2a02c370af1c2b480ab202a480a72029570a360285809f60275809b602658097602558
|8,0=>0x18264600917e205ef9179a45dd9175245cb9170e05ba916c645a98168245988163e4586915f64574915ae45629156645509151e453e914d6452c9148e451a9144645098140244f7913ba44e59137604d49132e44c2912e644b0912a2049f9125a448d91212447b911ca446991186045891145c449811024438810be44278107a441591032440390fea43f190fa243df9
|8,1=>0x20fe4836920b648249206e481292026480091fde47ee91f9a07dd91f5247cb91f0a47b991ec247a791e7e079691e36478491dee477291da6476091d5e474e91d1a073d91cd2472b91c8a471a81c4dc70a91c0646f891bbe46e691b7646d491b3206c481aee46b291aaa06a191a62468f91a1a467d919d2466b9198a4659919424647918fa4635918b246239186e06129
|8,2=>0x29e60a709299e4a5e9295dca4e929164a3d828d24a2b9288a4a19928424a07927fa49f6827b649e49276e49d29272649c0926de49ae92696499c9264e498a926064978925be49669257649549252e4942924e649309249e491e92456490c9240e48fa923c648e89237e48d69233648c4922f208b3922aa48a192262488f9221a487d921d2486c8218e485a9214648489
|8,3=>0x32c24ca79327a4c96832364c84931ee4c72931aa0c61931624c4f9311a4c3e830d64c2c9308e4c1a930464c0892ffe4bf692fb64be492f6e4bd292f264bc092ede4bae92e964b9c92e4e4b8a92e064b7892dbe4b6692d7a0b5592d324b4392cee0b3292ca64b2092c5e4b0e92c164afc92bce4aea92b864ad892b420ac792afa4ab592ab24aa392a6e0a9292a264a818
|8,4=>0x3b8e0eda93b464ec893afe4eb693aba0ea593a724e9483a2e4e82939ea0e71939a24e5f9395a4e4f7391e0e3e938d64e2c9388e4e1a938464e08937fe4df6937b64de49376e4dd29372a0dc1936e24db08369e4d9f8365a4d8d936124d7b935ca4d69935824d579353a4d45934f24d33934ae0d22934664d11834224cff933da4cee8339a0cdd933524ccb9330a4cb99
|8,5=>0x4462510f9441a50fe843d650ec9438e50da9434650c98430610b8942be50a69427650949422e5082941edd072941a650609415e504e94116503c940ce502a9408a101994042500793ffa4ff593fb24fe393f6a4fd193f224fbf93eda4fad93e924f9b93e4a4f8993e024f7793dbe0f6693d764f5493d2e4f4293cea0f3193ca60f2093c5e4f0e93c164efc93bd20eeb9
|8,6=>0x4d42534794cfe133694cb6532494c6e531294c2a130194be252ef94b9a52dd94b5252cb94b0a52b994ac252a884a7e529784a3a5285949f25273949aa526194962524f9491a523d948d2522c8488e521a94846520a7480651f9847c251e79477a51d59473251c3946ea51b1946a2519f9465a518d94612517b945ca51699458251579453a5145944f25133944aa51219
|8,7=>0x50de542e95096541c9504e540a9500653f894fbe53e694f7653d584f3613c494eee53b294ea653a094e5e538e94e16537c94dce536a94d8653598
|9,0=>0x5a5e568e95a12967b959c69667a597a5654a592e5641a58de962da5892561aa58465608957fa95f4a57aa95e0a575a95cca570a95b9956c255a79567a55959562e9581a55e2556f9559a555ca554a9549954fe9537854be15269547655149542a9501953de94ee9539294daa534294c7952f694b3a52aa54a0a525a948ca520e547a951c29467951769453a512a5440a
|9,1=>0x63e698f09639e58dda634e98ca9630298b6a62b298a48626a989196226187fa61d6986c9618a9858a61421847960f69834960aa9820a6062180ea601297faa5fc297e6a5f7657d3a5f2a57c195ede97ae95e96579ba5e469787a5df69773a5da6976095d62174ea5d12973b95cc69727a5c769713a5c2696ffa5bda56ed95b8e96da95b4296c6a5af296b395aa696a09
|9,2=>0x6d4a5b4996d061b3896cbe5b2696c765b1496c321b02a6be29aeea6b929adaa6b465ac7a6afe1ab696ab65aa496a6e5a9296a265a80969de5a6da698e9a5a969465a47a68fe1a35a68b25a23968669a0fa681699fba67ca59e8a677e59d5a672e99c1a66de99ada668e999a966465988965fe5976965b29962a6566594fa651a593ca64ca9929964825916a643299039
|9,3=>0x76b25da2a76629d8ea761a1d7d975ce9d6a975865d589753e5d45a74f25d32a74a65d209745e5d0e974129cfb973c69ce89737a9cd59732e9cc1a72e25caf972969c9d8724e9c89a72025c76a71b65c649716e5c52971265c3fa70d69c2c9708a9c18a703e5c05a6ff25bf396faa5be196f5e9bce96f165bbc96ece5ba9a6e7e9b95a6e2e9b81a6dde9b6da6d925b5b9
|9,4=>0x801a9ffd97fce9fea97f829fd6a7f329fc2a7ee29faf97e969f9d87e525f8aa7e029f76a7db65f63a7d669f5097d1a9f3d97cd25f2b97c8a5f18a7c3e5f0787bfa5ef4a7baa9ee0a7b5e5ece97b129ebc87ace5ea9a7a7e9e9697a3a1e85979ee9e71a799e9e5e979529e4c8790a9e38a78ba9e259786e9e12978229e00877de5deda778e9dd9a77425dc7976fa5db59
|9,5=>0x89aa6260a895e624f8891a623ca88d2222aa8882a216a88366203a87ea61f19879ea1dda874ea1ca9870661b7a86b6a1a3a8666a18fa861a617ca85ce6169a857ea15698532a143984e6a131884a2611f98456a10ba8406a0f8983be60e5a837260d398326a0bfa82de20ada828ea099a823ea085a81eea072981a2a05ea8152a04aa81066037a80b6a023a8066a0109
|9,6=>0x232da8c92631aa8c466307a8bf6a2f498bae62e1a8b6262d088b1e62bda8ad622ac98a8aa29998a426286a89f2a2739
|10,0=>0x965e658da960ea579a95c265679957a65559952ea543894e6a52fa949a651d9944ea50a9940664f7a93ba64e4a9366e4ceb9312a4b9b92c264a5b92726492a9226647fa91da646d9918ea459a913ea446990f66434990aaa420a905aa40ca900e63f9a8fbea3e698f7663d498f3223c1b8edea3ada8e8ea39a98e466387a8df6a373a8da6a35fa8d5a634ca8d06e337a
|10,1=>0x9ff2a7f2a9fa667dfa9f56a7cba9f0a67b8a9ebaa7a599e6ae79199e1ea77e99dd2a76aa9d82a75799d36a743a9cea6730a9c9aa71ca9c4e670a99c0666f899bbe66e699b7666d3a9b2a66c199adea6ae99a96669c99a4aa688a99fe6676999aee66299962a64ea9916663ba98ca6628a9876e6149982aa601997e265eea9792a5daa9742a5c7996f6a5b4996a6e5a09
|10,2=>0x2877aa1be2865aa16ea8538a12a68419a0dea82cba08e6819aa0426806a
|11,0=>0xa64669889a5faa9759a5b269639a56a69519a522693f9a4da692caa48aa918aa43aa904aa3eaa8f19a3a268df9a35a68ccaa30e68ba9a2c668a89a27e6895aa22ea881a
|12,0=>0x29be9a6d669ac9a68e699a9
|13,0=>0x29c78
|_,_=>0
def wAt:=mkWire dB 246 256 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 18
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 3000009 zs)
def oP:Nat→Nat
|0=>0xe09420190e1a4201909074807c090641c210e004201909084a03727064387d07084381d0e09404310b0a024210706424190e07404310b0a024210706404310b0a01c190908438010608490070e2342401080643801080643885201f024190708418210e094381d030c4282c070642421070640c650e084580004094381d0608420190e094381d0d0c42c28090841c19
|1=>0xe084381d080641c01130dc3801080644c37090043801060841c191d00418210e214807c090641c21131ac24010e0041821090041c190708438250e004182109064381d300a014210e0941c190507438010e094201916000141d0e08438250906420190e1a41c010e00420190700418210e094381d0d0c42c28090841c190d0c42c280706424210e00418210e1f42401
|2=>0x608438810e0743869090041c01060843821240dc388d09004182101194381916000141d0e0942019094f8901f07084c0190e0b424210b0a01c190e07438250908418210d438390e4a0852c1d0e06420190e0743485201f0241907084a0370e2a41c01080647c190708438250e2382401080644c370e00420190e20424210e0942019030c4282c070642421090041025
|3=>0x80646819090744c370e00439511f0647c190708420190e074c028050843825070649c190e1f438010806438210d1945800050743825060844c37201f01c210906438012803c38a907004182109084046516000141d0e0941821160003869070841c250906420192803c241913074380108064396508065282c04064381d09084380108064241d201f02419070841c01
|4=>0x908418217006c39bd0b07424216e0dc39b51a008241d08064a82709064102e06084381d090841c2104204381d090644c69090752c210e0647c82070842419090641c010507438250806414210e0641c010e09420192803c242127064387d07084350e0e43928214b07438190e084241d090041c010806438190e094201901214807c090641c21280dc2419130743801
|5=>0x806411312307c80210e074241920084247d070842419240ec9027410852c250e064381908064c01d180943821240dc388d0900420197401c901d410852c250e064248a2401d04210e20424190e0942419070841c190e2342401080641c190e0b42c190e07424210e08420190e374242a07064241d280dc9c190e1f41c21070640c851f2001c21090642c28070643825
|6=>0xe00418212409c9007410852c250e064282107064801d0708480210e0942419090043825070641c2106084382116064141d0e09420197801c39312307c80210708410810e07424190e06424a90700418210e084242a0608438210e0941c197408dc0190e6f4247d0708439d9300a814210e0941c190906414210e0743825070647c810708424197406c5801050743825
|7=>0x80640596091044c370e00420190d438a00f130743801080641c210e20418210720424197d03df01d0e7b424020806438810e0841c250706424190b06428250b074242107064386909074807c090641c21090a4387e070841c190806420190e085041f4b094381930064382d0908425090a0841c197403c5801040942019090052c1d0e09420190e064241d090841c01
|8=>0xe084382507204241985064282e09084a0270e2a41c0108064108e0b064381d0908490270e23424010806604370e8241c0208065c01b3007460250e0841c190b064102d0e07424217401c58010507438250e094282307064381d09064348a2401d04210e20424190e094388e09004201928094a0374a0852c1d0e065a40f071044c374b08438190e2a439de092a41c01
|9=>0x8064201909074807c090641c21130dc4c254b084381909434a00f4a0852c1d0e06490070e234240108064801d090843881070842419200741c210906438010806420190706439be091f41c2107064582104094381d09064388107064241d2008424190806424193007c60250e084241d090041c010806438192401c4c254b08438190b074901f30064382d090842019
|10=>0x4b08438190907490074108438810906425e908064387e090641c21092aa302127208387d090641c210e6f43819091f41c210e094a8270e084a827070844c270706438010806424e11307c38010608410190e094381d0708418210907424010e0641c210608420190908410810e07424190a0841c1909084388109064388a2401cc01918094382107004381d0e0942419
|11=>0xe07424210e0041c01060842421090641c010e00420191309c1c1909008387d0708418210423824010e0741821095a81c8d09004201905074382107004382506084601d0e0841c210e07438250906420195f07c39512a09c282107064387d0e778807d090641c210e0b42421090741c190806438250e074a8271f0641c21130dc388e090043801080641cc5131ac241d
|12=>0x7403c580104094381d08064241907904382e07064242120084241913094a027130752c210e0641c1907084241909084a0372807c38a90700420197406d282d04064381d090841c19080649c2518074382107064582304094381d09065dc1f0b0a4242107064381d0b06424210e0941c21130dc38010806438216a08c581904094381d7006c582104094381d7006c102d
|13=>0xe09420191309424aa07004380108064381d0e2a81c010608425090e2a82019280dc2421130743801060841e5990064382e0726838a90700420191307c24190e0941c010900420190e0641c210e62424290706420190d438a00f0e2a41c010806438292307d28216a08d28254b0743819090843881060841c810906425fa0744424010806420190e2047c25070842419
|14=>0x908418211608410250e074182109084398920074241907085e0370e4c48c1f20085a82304204381d090666c0f183743821090a81c19130dca00f130752c210e0643825090043819070841821070841c190e238240108064a00f280ec4c1d4b08438197006c9c25180743821130dc1c010e00418211307ca03b130752c210e064141d0e0043825080641e6516008141d
|15=>0x1809438217403c580104094381d080667c374b4043819070b82421280dc4c1d4b08438190e3389037130952c210e0642019030c4282c070642421092289007410852c250e06439890e084242907064201976084c02a0508438250706504214b0943819094f8388d0900420197006cc01d180943821740ddc019040b4381d0e0941c19090043801080652c1d0e0643825
|16=>0x938438251307d2c210e064141d0e0948c1f200842419130952c210e0657c0f0e544a827070042019090a81c191a084241d130dc38015f0dc3951092a81c0108064388109084381d090641c190b06410250e0742421070641c250e2382401080641c2e0e20424212803ca01f27064387d070843825030c4282c07064242107084382d0b064381d09084903b2401cc019
|17=>0x90844c1f0d2289007410852c250e064282107065d01f2720410210e07424190e0a88c1fa501e04250e8241c0208065f4377c07439ed0900820190e6981c41130dd2c210e06438250908428210e0741c190906424210a084381d070641c192720010210e07424196f065c01b0e6f4247d07084390e2803c4c1d4b08438197006c5821050743825280eca01f180743821
|18=>0xe08420190e0a414210e0941c19130dc3801090a81c190e834108e20084381d09065c01b0e6f4247d070857c370e54424aa0700420192803d2c7d0e0641c212803ca0374a0852c1d0e0641c8e2008424190e09490372401cc0190e0b4a0370e2a41c01060841d0e2803d28214b0743819650742441130dd2c210e0641c010e08438250906420190709420190e064382d
|19=>0x2809c9c19180743821240dc903b130952c210e065d01f6a08414290e0941c1907518a02727064387d07084241d07004382d0908418210e0743485201f024190708490374b0b438190908424210a094381d0706420190e2041c21200842419ab03d2ea90e064247e0708439dd20a94807e090641c21240dc903b410852c250e0644c370e00420190e0642401070041821
|20=>0x9ad5047e050643825070852c25070043819090841821a50de04250e8241c020806420190e214807c090641c212407c4c250e00420190409438210e0741c1908064a00f27064601d0e0857c1f0e5441c0108064388e07084381d0e094282c0706424210e074282c090642421070642c280706424210e0041821095a839de0a0b41c19090841c01130dc3801080649c25
|21=>0x9064382d09085d02316004141d0e09418210906428230507438250706426bd4a0bc10190e074242108064387d070643825070848c1f09004a827070042019036981c41130dd2c210e06420191608410250e07424190423824010e07420192803c242127064387d07084247d2a09c7c19070841c010e074382506085f82707444388e0b0642421130dc4c1f4b0843819
|22=>0xe0b82421090642019130dca00f130743801b10649c8304084381d0906490372409d04214b09438190806438310b0a0242107064241907004141d0e094201907294c0190e0b5d01b131a4241d4b08438197403dc019051f438250e77824a9070041821052a838a90700420190e234240108065c01b0b064102d0e07424210e00418211f064381d0e2041c21200741c21
|23=>0x52a8387d1f0641c21070642c190908438250708438012007c2419090841821304a03829050843825070641c210e074386907084241d0b064242109064380108065e0370e4c48c1f0900420190e67824e14b084381908065282c04064381d09085d0271600410250e07420190e1a41c210709424190806439bd0e779bc19091f41c210806458211606410250e0741e41
|24=>0x130743801060842421090644c1d0e00420199f0dd2d010e0641c2e09084388a2401d04214b09438190e0942827070641c2106084a02727064387d070844c1f4b08438197006c58211606410250e075d0372809528214b07438190d438a00f4a0852c1d0e0641e3127208387d090641c210e3742827070641c21060848c1f2008424190a0841c192401d04214b0943819
|25=>0x2407c140107004382508064a00f0e2a41c0108065d0271600410250e074201901194580005074382508064581909084141d0e0941c210e00420197403c4c69070952c210e06424210709438a9070041821ba0743a150a0b81c1909084a00f090644c1d0e00420190726928214b0743819280dca00f130743801b8064580305074382508064350e2803d28214b0743819
|26=>0x280dca01f27064387d07084242107084398a090a41c1909064580004094381d0806424010e0741c010e09420190e06438212a09c1c010608490070e234388e0900420190e0a47c27070841c1908064901f0e2342401080642421201f01c19070842419180943821aa064247e07085e0070e4c41c8e0900420190906424210e074380106085d03b16004141d0e0942019
|27=>0xe2082419090841821090647c190e1f41c217401dc019051f43825130749007130952c210e0641c9a280dc9c190e1f41c217c07439ed0900820193007414210e0941c19073349037410852c250e064388e07084241d0b06424215f03c3951092a81c0108065c01b040b4381d090859407091044c374b08438190e77839dd0b0a424210706424210906438aa070042019
|28=>0x6084a03727064601d0e085f0377c07439ed0900820190423838010900420190e2a8141d0e0041c01080644c272401c4c254b08438194b0843819070042019052a828210e0941c1905084801d0e094241908065d03716004141d0e0949007130952c210e06438252307c2c19090844c6b0e0041c25080641c250700420190e08438190e07438aa1f0642421070841c01
|29=>0x9064380108065282504064381d0908438210e0a41821090a41c197006c58210507438250d438a00f130752c210e0644c37240ec4c254b0843819280dc242127064387d07084381d300a014210e0941c190e094100109004381d08064801d1f0941c210906424a92809c38a9070042019080643485201f02419070842555810dc3a090700820190e0845800050743825
|30=>0x7834108e20084381d090643869090041c010907420192803ca0374a0852c1d0e0643a6516008141d0e0942019410852c250e0642dd9300a8382d09084c0190e0b438252307c80210e0742419280dd28214b07438197406da82104204381d090641c01130dc3801080644c372803c4c1d4b0843819090642421130dc380106084381d07084c0190e0b42421090741c21
|31=>0x4b0843819071042441130dd2c210e065dc1f7709c1c2d09085d03b131a4241d4b08438190e2a42421070947c190708438250e7781c8d090042019240dc388d0e238240108065f40f7c07439ed0900820190e1a438190907424210708410810608438210e07424190922890070e234240108064382501214807c090641c21740dc58010e09420190e1a44c374b0843819
|32=>0x130dc4c69090752c210e06439b51a008241d080641c9a4a0852c1d0e06410252307c80210e07424197403c901d410852c250e0642419070841c1909084a00f130752c210e0642419130dc24210e00418210d194580005074382508065d03716004141d0e0942019240dc9027410852c250e064a00f2809528214b0743819740dc5801050743825080644c1d240dc4c25
|33=>0x7709c8c1d0b06424210e08410250e074241970064147d0e0941c21280dc38a91f0641c211f0642421090641c210e0848c1f0900418210e544a8270700420190e23424010e074201909064a8270700420190e20424190908418210e6f42c1d090841c19077b424020e07420190e2382c19070842421090647c190e0941c210eb3438210720824192401cc019180943821
|34=>0x2803c4c1d4b084381907444388e0900420191f2042421090641c212807d28214b0743819280dc4c1d0e0042019080642c28090841c1909004241d0708418210e00438250908418210e00424190908418211f0641c210e07424210e20480210e074241916008141d0e09420197709dbc19070b424212a09c1c010907420190e2382c19070b424210400424010e0742019
|35=>0x130744c274b08438190e00424010e07420190e064c01d18094382123074388d0900420190e094387d090641c21090741c010e00420190e2a81c010900420190900410250e07420190e094282c0706424210e0943a090700820190e094dc21090a81c19040b824190e07424210708410810e0742419130dc1c010e004201907004381d0608438211f0647c25070842419
|36=>0x70041c2509064201986064c01f18094382116064382104094381d0e0744c1f4b08438190700438250908418210e004241d0708418210a09c38210e0941c190e0747c820708424190706438210e0742419240dd04214b0943819130dc1c210e00418210e074382d090841821090041c190708418212409d04214b0943819090642019091f41c21070948c1f0b0642421
|37=>0x90841c19300ac14210e094a00f13074380108064381d1309d2c210e06528214a0952c1d0e0649037130952c210e064801d0e2041c210906424010e0741c190806418210e4041c2e09084381d2a09c282107064a01f27064601d0e0842c29090841c19240dc388d090042019090a4387e070841c190e085041f4b09438192409c388d090042019090844c370e0041821
|38=>0x201f4241907084802304094381d090644c370e0952c210e0643819080641c2d090843b2d0b0a824210706424193007c60250e0841c41130dd2c210e0643951092a81c0108065047e0e2041c210e084382507204241907064388d0900420190708480210e0942419092a87c190708424194b09420190e08438190806410810e0742419070043881090642019070b42419
|39=>0x2a09c2821070641c81200843825090641c1909004382508064a0374a0852c1d0e0652c1d0e064382507084242104204381d09065047f050643825070848c1f20084381d09064241907004380108064241d201f0241907085dc271f2041c2109064388d090748021090641c210e2042419080645801050743825080642c190a0941c19090841c190e6f8247d0708439de
|40=>0xecf58823090a41c191807438210e20424192807d28210e0a41c190708438250e07424190708438250e00418210e20418210720424192401d04214b09438190708424190e0042019090741c19090841e5990064382e09084242105074382507084901f30064382d0908425e90e1f8241907084801f0906424210608438190e6f4247d0708490370e2342401080642429
|41=>0x900420190e08438192401c388d090042019280dd28214b07438190e2041c190e07424191307c1c190e0042019070649c25180743821280ec4c1d4b08438192008c1c190e0742419042382c190e074242107d352c2e0908438190e4c41c8e0900420197006c102d0e0742421300a814210e0941c1907d14241d0e0082019050841c010e0941821090843881070842419
|42=>0x1f0641c210e0742421d50949c1b1807438210e2382401080643819092a41c010608438211309c1c190e00420192803c38a9070042019093844c1f0e00420194b07438250806438190e06424010709420190e0941c1907084182107004382e0908418212007424210e204241908064c01d1809438210e00424290706420190e2047c250708424192401d04210e2042419
|43=>0x1608410250e07424190e21c807c090641c210e07504234b09438190706424210e0941c21040841c190e07424190ea1acc210720824197c0dc39ed09008201909d7a98210e0a81c190e2a87c190e0741c210e0743825090642019092a47c190e0741c212407cc0191809438210e4c41c8e090042019091044c374b08438192807c9c190e1f41c210e0643825090841821
|44=>0xe064241d0708418210806438210720824190e0943b6d1f06c1c21030c4282c0706424210420438210e07424190420820190e074241907854282e0706424217707c2c29090841c191f06c381d0e0941c2107064247d070841821240ecc0191809438217006cc01d1809438210e7781c8d0900420196f06439bd091f41c210e0942c190e07424210406438250e0742421
|45=>0x706438250908418210e09424010e00420190e064241d090841c2107064388e0900420190942438aa0700420197707c807d090641c21052a828210e0941c191ad14241d0e00820197c07439ed0900820191307c38250e00420190900438210706420190e6242429070642019130dc241d4b08438190e854282e0706424211f094381d070841821e0084581b04094381d
|46=>0x6084a00f0e2a4282107064382527064601d0e084382905084382507065c01b0e6f4247d07084a03727064387d0708438290907424190706439b51a008241d0806424197a064387e070841c19090742c190908427450e0082019d009c1f450e00820192a09c1c010e07420190709438190e0b4242116004141d0e0942019240dcc0190e0b424214b6f8247d070843819
|47=>0x8064387e070641c21090644c6b090752c210e0642e9b0e0a8242107066a419201f8241907084242127064387d070841ca51309d2c210e0641c8e0b064381d090842401130dc380108064381d0a0941c190908420190e06438250708438aa07094282107065282d04064381d0908424020e0741c190806462cd0e0841c820906424010700438250806410190e0741c21
|48=>0x8064903b410852c250e06418210e6f8247d07084582104094381d090643881090748021090644c270700438010806438a90a08438250706604370e8241c0208064900730064382d090842c19040b4381d090844c371309d2c210e0643885201f02419070842019050843825070642c1d090842419080647c2527064387d07084a01f0e2a41c0108064381d070043825
|49=>0x90644c370e07438010806438310b0a0242107064a8270e2a41c010806439dd0b0a424210706424020e1f41c2106084a037130752c210e064a00f0e2a41c0108064388e09004380108064241d0e0b4242106084382a070641c21060852c2d0e064381d090844c1d130dc380108064a0274a0852c1d0e064387d0706438250708420190e0b81c190908438250e2382401
|50=>0x8064a03713074380108064387d2a09c7c19070841c210e374242a07065282c04064381d09085c019051f43825070842401070641c210608424190507438250708425090e2a87c190708458211606410250e077a019051f83825070841c2509064282307064241907904382e090841c2109064382d0908424010700418210e084380107208241908064582304094381d
|51=>0x7064282d0e0a4242107064a01f0e2a47c190708490370e23424010806428210e0a42421070642c1904094381d0908778250edb47c1b070841c250e2382401080641efd0e208241908064241904094381d080641c21090742c1909084242a070843825070641c250e2a41c010806482a5201f82419070841c2107094241908064a00f4a0852c1d0e0642419130743801
|52=>0x806424190e2a81c01080648023090643825070641c8e090043801080641c42130dd2c210e06438250e2a41c010806418214107d2c250e06439512a09c7c19070844c69090752c210e06439de6f064247d07084581905074382508064901d0e2342401080643825090a81c190806424190e084382907064807c070641c21090641fad050083825080643b1937084242a
|53=>0x13094381d4b0843819090081c19070841821201f4241907085a8231606410250e0744c274b0843819130944c1d4b08438190423824010e07420191600c141d0e0944c1f0e0952c210e0641c010507438250806424211f0643825070844c6b090752c210e064a827070043825080643821050743825060841ca51309d2c210e0647c2707084382907064a027130743801
|54=>0x70843bba098241c0208064801d1f0941c21090661c190e6f8247d070848c1d090043825080643485201f024190708428210e07438250706458190507438250806414210e0941c810906481e90e1f8241907084a0270e2a41c010806420190e064387d07084a00f130743801080641d110e238240108064581b0e08410250e0741c212307c2c19090842421090641c21
|55=>0xe064275da6084382a070643bb9098241c02080641d110e238240108064382109004381d06085f01f0e7b4240208065a823050a43825070643801050743825080641c1920084388109065282504064381d0908424290e0843829070641c41130dc3801080644c1d130dd2c210e06424a90700438010806438250b0a8242107064a00f130752c210e065c01b051f43825
|56=>0xe238240108065dc2707234240108064a0254a0852c1d0e064a8270a084382507064a0274a0852c1d0e064a00f130743801080643819091f41c210608424190b074242107064240107004241d08064382104204381d090642419070841c1909084241d130dc38010806439de1a004241d08065c0190e6f4247d0708424012a09c1c0108064240108064a0374a0852c1d
|57=>0x90644c37090752c210e0644c6b0907438010806439de0b0a4242107064a027130752c210e064580105074382508064580005074382508065f01d0e7b424020806458020e09420190e004141d0e09420190708438250e07424210907420190e08438191f208241907084a00f4a0852c1d0e064a037130743801080644c1d130dd2c210e064580305074382508064388d
|58=>0x90643825070b424210b0a0242107064dc21090a81c196f06c247d070844c374b0843819201f424190708424210e20424190e09438010806424190e00420190e0b4381d0908528234b0743819090a41c190e0844c1d4b08438190e064381d090847c19070842419620842429070641c020908418210e20424190806424010e07420190b0a4242107064108e20084381d
|59=>0x720424190e0641c2d09084141d0e0941c21230748021090641c8209064201906084381d090841e410e0b8242107084382d0908438214b09438191608c10250e07438810720424190700420190e064388e200842419090041c250806698210e0a81c1904008381d0806468010907420190a0843829070647c2507084241907004242106084147d0e0941c2104204381d
|60=>0x1309c380108064241d0708438190e0841c82090642c1d090841c190e8241c02080641c210706424210e0643825090843989090a41c19090742421070841c210e0941c190900438250806410820e07424190e09420190e06424a90700420190709480230906438250e07424190e2342401080642421072082419410852c250e064241d0e00420190e2041c21090648021
|61=>0xe08414210e0941c19090641c2d090843b312008c241920084381d0906427450e008201930064382d090848c1d0900420190e094242106084388e090042019070852c1d0e0647c8207084241907004380108064807e090641c2107004240108064241d080643819130dd2c210e06424210e0941c190723824010806438a90a0841c19080642421070641c2e0e0742421
|62=>0x4094381d2a09c2821070643819070841821091f41c2106084241d090641c2107084381d090842c29090841c190a0841c1909084382e0908418210e204381d090643acd07208241909db47c1b0708428210e0741c19077b42402080647c1b0e0741c210e0a81c190708428230e0941c190e0b81c190908438254b0843819080652c1d0e06438a90700420192709c601d
|63=>0xe2a81c0108064388e0900420190e064387d070841c01090742019130743801080644c274b08438191f064242107084a8270700420190e6282429070647c190e0941c214b1f81c210e064c01d1809438210706480230906424020e0742019060841c8109064241d0e008201909004382508064241d0b0642421072382401080641c25090642019090752c210e0645819
|64=>0xe0943819072082419070b424210708418210e0741c210700420190608438210a08c1c190e0b42421070643821200842419130dc38010806420190e08438190907438210e064141d0e09420190906424210608528214b0743819130dc380108064242107084381913074380108064381904094381d1309d2c210e06468020907420190e074382508064241d0e2042419
|65=>0x201907084381909074381d0e08438190e094381d090742019090642421091f41c21090841c210900820190e00820194b08438190e0a81c194b07438190e0942019090841c190907438190e0941c190e0042019090042019090741c2104094381d
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x1ce00000000001dc0000000000000000000000007
|7,0=>0x2d1015cc000000000000000000000054300000144c000004ea825d812680912000000000000008d400000228c110408260000000000faa00000000000000f280000000001d500000000003a081b98000000000000000000d48064602f3016900000000002a30141009c40486021300f900000000001c300d88062a02b6012b007d803680156
|7,1=>0x4554220a00000000042980000104607fa83ed000000f92000003dc81e2c0000000000000000000000779000001da40e760000000001c4a000006f2036181a4c0cd500000000000000c7600000305800000bd4000002e1400000000
|8,0=>0x107208254408a00000ffa87e943eaa1f050f5a879943c2a1dc50eba8749439e61cc30e42070d400001be50dca86dc8364a1ad50d4286910340819b5000006594000019150c628000030ea1843000005fd42f4a17640b8a85b142d0816350af2857082aea15250a6a85214286a13e509d204d54268212f5095a0000024e812430000047d4000011a5
|8,1=>0x18120bf905f662f6517a88bc145d882e84171a8b8485b8a2d7516928b354590a2c3515f28ae54568a000000000acc455ca2aa415410a988542a29d414c28a4d451ca2895142289fd44f4a27640000000004e2a26d41342898d44bca259512a28000049ea24a5123209054478a000011c988d5046280000000008b504528225411028871042ea2125
|8,2=>0x1fa2800007e083eb51f32800007c2a3dc51eba8f50c7a083cc41e4200000786a3be51dd20ed5476283ad400000ea14746a39e51cca8e514720838c41c3a8e0d06fca37951baa0dc8c000036d500000da8c6cc836421afa8d6946aaa00001a990d394692a34541a028ced466ca334200000cbd4000032b419328c854638a3175189a0c39461663065
|8,3=>0x279293b549d0a4e3526fa000009b4a4d64268a9331498ea4c4325fa92e9496c80000258a92b50950a4a4424fa926d092e84934000012394912a48450000000008fea47e123ca800008ee44725238111ad48cca461522e2915d48a4a44d5224291110880843b5000010d94866642e5216110a10846a41f420d290554824640d52042900d47fca3f95
|8,4=>0x2f6a97ac8bcca5e332ef297690baaa5d050000172d4b8ca5c152de296e1000005b352d7296a54b48a00002d0996714b30859442c821634cb10a58622c1215f54af0a00002b9a95b94ad2a56452afa95694000055642a8a95350a92800002a2295010000053b529b294c54a58a52840000148d4a3e851b428c914514a1ea50a5282a940509f8a4f75
|8,5=>0x36ea9b61400006d35367a1b294d8aa6c0535da9ad94d62a000035629a9d4d44a69d534ca00000d28a692234799a29400006855340299ed4cee86725336a99a14ccc4661532e2995d4ca4a64e4325200000c8aa0000320280000c7a66385319a80000000062e5314a989500000622330ea98614c26a60e5304a9818c00006042300217f10beea5f25
|8,6=>0x3e929f354f90a00003e221f010f76a7b653d8a9eb1400007a933d2a1e8c8f3ca00003cd21e554f22878c500001e1d4f04a77d500001de50ee8a000000001dc10ed6a76653b0a9d714eaea75343a729d254e88a73f539da1cd94e648731100001cb50e50a726239211c810e36a7174389a1c3d0e1687065380a9bf14df086f44377a9ba94dcc86e24
|8,7=>0x1076a8374000000001066882e5414a8000104a8821440e2a05d5024a80d5000020215006a7fe53fca9fd50fe0a7eb53f329f854fb8a7d75
|9,0=>0x49e224e1126889304496224a112488920448e224611228891044862242112088900447e223e111e888f04476223a111c888e0446e2236111a888d0446622321118888c0445e222e1116888b04456222a1114888a0444e222611128889044462222111088880443e221e110e888704436221a110c88860442e2216110a88850442622121108888404
|9,1=>0x51c228d114608a2c45142289114408a1d350ca285514228a0d4504a2815140289fd44fca27d513e289ed44f4a279513c289dd44eca275513a289cd44e4a2715138289bd44dca26d5136289ad44d4a26951342899e34cd226591324898e44c5226191304897e44bd9a5dd12e6896f44b5a259d12c6895f44ada255d12a8695044a622521128889404
|9,2=>0x59c22cd116608b2c459422c9116408b1c458c22c5116208b0c458422c1116008afc457c22bd115e08aec457422b9115c08adc456c22b5115a08acc456422b1115808abc455c22ad115608aac455422a9115408a9c454c22a5115208a8c454422a1115008a7c453c229d114e08a6c45342299114c08a5c452c2295114a08a4c45242291114808a3c4
|9,3=>0x619a30bd18568c274611a307d18368c174609a303d18168c074601a2ffd17f68bf745f9a2fbd17d68be745f1a2f7d17b68bd745e9a2f3d17968bc745e1a2efd17768bb745d9a2ebd17568ba745d1a2e7d17368b98300002e5117208b8c45c422e1117008b7c45bc22dd116e08b6c45b422d9116c08b5c45ac22d5116a08b4c45a422d1116808b3c4
|9,4=>0x699a34bd1a568d274691a347d1a368d174689a343d1a168d074681a33fd19f68cf74679a33bd19d68ce74671a337d19b68cd74669a333d19968cc74661a32fd19768cb74659a32bd19568ca74651a327d19368c974649a323d19168c874641a31fd18f68c774639a31bd18d68c674631a317d18b68c574629a313d18968c474621a30fd18768c374
|9,5=>0x716a38a51c4a8e21470ea38651c2a8e114706a38251c0a8e0326ffa37ed1bee8df346f7a37ad1bce8de346efa376d1bae8dd346e7a372d1b8e8dc346dfa36ed1b6e8db346d7a36ad1b4e8da346cfa366d1b2e8d9346c7a362d1b0e8d8346c01b5f11af08d7536b8a35b8dad48d6646b19b57d1ab68d5746a9a353d1a968d4746a1a34fd1a768d374
|9,6=>0xe7f473da39dd1ce68e6f4735a399d1cc68e60372e239611ca88e513726a39251c8a8e41471ea38e51c6a8e314
|10,0=>0x7a01bcf4de746f37379a1bcc4de5c6f2b37941bc94de446f1f378e1bc64de2c6f1337881bc34de146f0737821bc04ddfc6efb377c1bbd4dde46eef37761bba4ddcc6ee337701bb74ddb46ed7376a1bb44dd9c6ecb37641bb14dd846ebf375e1bae4dd6c6eb337581bab4dd546ea737521ba84dd3c6e9b374c1ba54dd246e8f37461ba24dd0c6e833
|10,1=>0x8001bff4dff46ff737fa1bfc4dfdc6feb37f41bf94dfc46fdf37ee1bf64dfac6fd337e81bf34df946fc737e21bf04df7c6fbb37dc1bed4df646faf37d61bea4df4c6fa337d01be74df346f9737ca1be44df1c6f8b37c41be14df046f7f37be1bde4deec6f7337b81bdb4ded46f6737b21bd84debc6f5b37ac1bd54dea46f4f37a61bd24de8c6f433
|10,2=>0x102738121c084e03c701b380c1c054e024700f38061c024e00c70033
|11,0=>0x20c85062283014178a0b8505a282c14158a0a85052282814138a098504a282414118a08850422820140f8a078503a281c140d8a06850322818140b8a058502a2
|12,0=>0x106a18348c1a060ce30661
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 17
def pmP:Nat→Nat
|0=>0x182000000000c000000000044a00000000220000000001080000000008040000000040000000000180000000000b00000000005000000000022a000000001140000000008280000000040400000000200000000000c0000000000400000000000d40000000006000000000024000000000108000000000800000000002a00000000014000000000088000000000400000000001a00000000007000000000028000000000100000000000200000000000
|1=>0x8100000000040540000000200000000000d200000000059a800000002c800000000160000000000a11000000005000000000024500000000120a000000009000000000047000000000208000000001008000000008010000000040000000000189000000000c40000000006000000000028a000000001410000000008480000000041500000000200000000000e50000000007000000000033100000000193800000000c900000000064000000000315
|2=>0x180a80000000c00000000004640000000023140000000110a800000008810000000044000000000200400000001000000000007cd400000003e6200000001e0000000000dda800000006dd40000000366a00000001b3100000000d93800000006c540000000362200000001a2400000000d0a800000006800000000032220000000190500000000c1a800000006044000000030000000000132000000000988800000004c000000000240000000001100
|3=>0x20d9a0000001048d00000008162800000031b340000001819a000000052d540000002766a00000012a0000000009100000000046dd40000002268000000010a2000000008280000000040880000000202400000001010000000008060000000040000000000130280000000630000000002d9a8000000148140000000a00200000005000000000020808000000100040000000800000000003b3500000001d8a80000000e3800000000702a00000003300
|4=>0x80b200000004049000000020184800000100820000000802120000004009d40000020000000000093f3500000048d9a80000024288000000120440000000901600000004800000000021080000000107eea00000083b3500000041890000000208c54000001044000000008212000000041000000000207cd400000103e0000000081c3500000040d9a80000020548000000100e4000000080620000000402120000002010000000010064000000080215
|5=>0x109d9a800000846dd40000042268000000210b4000000108530000000842554000004210c0000002101400000010808000000080ecd400000403eaa00000201f3500000100e00000000806dd40000040366a00000201800000001009c0000000804800000004022ea00000200e35000001004100000008000000000032762a00000191a15000000c0d9a8000004509d4000002236ea00000105b750000008208280000040edd40000020440000000101b75
|6=>0x400008000001806dd400000a2040000000501035000002803000000010228d00000080366a00000401a2000000200d000000010034000000080120000000383b75000001c09ba800000c4ac000000062060000000301b7500000148dba800000a44d8000000521aea00000290b60000001481b0000000a40400000005076ea000002833600000014119a800000a07dd4000005036ea00000281b3500000140920000000a038d40000050148000000213b75
|7=>0x88bd9a80000445cc000000222b6ea00001115b350000088ab10000004246dd40000212366a00001083b3500000840fba800004207cd40000210366a00001080b350000080adba8000040500800000202762a00001013a1500000808dba800004046cd4000020214aa0000100442000000801d9a80000400ad54000020046000000100200000000800dba800004006cd400002000400000010000200000080000a8000020004400000100004000000800011
|8=>0x1940faa80000ca07cd400006423e6a0000320352000001900fba80000c807cd40000640366a0000311522000001802010000009006cd40000480322a00002401020000012008008000090034800000480184000002400820000012001100000090000000000440366a00002001b3500001000800000008002c54000040000400000200000000000940dba80000484ecd4000024236ea00001203b3500000900f9a800004806dd40000240366a00001185b75
|9=>0x2080d9a800010403c000000820184800004100b2000002080492000010402090000082006480000410000400002048d9a80001020efd400008103e6a0000408040000002009dfa800010046cd4000080220400000401012000002008080000010010000000080077ea0000400220000002000f9a800010006cd40000800204000004000400000020001ca00001000045000008000080000040000150000200000000000d801dd40000662b66a00003281f75
|10=>0x2840d9a80001404eed40000a02366a00005003b350000280014a80001100ffd40000852366a00004283bf500002141d9a800010a07cd4000084077ea000042029f500002100f9a800010806fd40000840366a00004201a35000020c9f8a800010646cd40000830544000004181f35000020c0f92000010606cd400008301e40000041808240000208ad00000010444c000000822160000004105200000020815c000001040ac0000008203e6a00004101f20
|11=>0x4000c5a8000200046500001000200000008000994000040001d0000020000d0000010000528000080001b400004000092000020000400000100001680000800009400004000048000020000080000100000200000800000000003940d9a80001c801c800000e40044000006001f3500003000d9a8000180014d40000a4042ea00005201f3500002900d9a800014805cd40000a400c6a000051919350000288bdea800014410f540000a12366a00005081b75
|12=>0x100008100000800040000004000102a000200008000000a0c0c988000400000440001e40a0000000c383b3500006181d9a800030606ed4000182055680000c00092400005002800000028006cd4000140020000000880289000004189c80000020c0c880000106000400000830000000004101d1a800020806cd40001020068000008083bb5000040081d000002001400000010005328000080029800000400144a00002000a2400001000376a00008001b35
|13=>0x200005900001000008540008000040000040000001000179028100000ac8140800005622b66a0002a005b3500015002d900000a80168000005400b06a0002a005235000150029000000a80144000005400364000028005b2000014001c800000a000400000048027e6a0002200500000010909f9a8000840079d400040427e6a00020201f35000100c9d9a800080407cd40004020244000020093f35000100410aa80008004fcd40004000a00000020001b35
|14=>0x302005ca800181002600000c000150000045001b35000220001800001100004140008080374000040400a6000020200520000101002800000808011000004031031500020108d9a800100406cd40008012960000040014a0000020002d9a8001000140140008000900a00040004305000200021128001000108000008000820a00040004025000200020020001000100040008000800000040003b35000200011900001000088000008000366a00040001a20
|15=>0x402004300002010020800010070366a00080281f7500040140f9a800200a06cd40010042766a00080203b7500040100f9a800200806cd40010040002a00080101b3500040048f1a80020024288000100103e6a00080081b3500040009d9a800200008c80001000044000008000200000040000f9a800200007c540010000366a0008000197500040000710000200002a0000100001100000800002200004000000000018104fed4000c080376a00060401a80
|16=>0x40900020000204600c8000102127c6a00081091b3500040841dba80020420ecd40010210764000081083a0000040840fba800204207cd40010210366a00081080b3500040840480000204200cd40010202640000081003b200004080190000020400ac80001020044400008100220000040800d9a80020400488000102001c000008100020000040308d9a800201806dd400100a03eea000805009a0000402804c0000201207dd400100803e2a00080401d60
|17=>0x60000d9a800280a010d400140427e6a000a0091f3500050009f9a80028004a1d400140023e6a000a0003b35000500015c000028000a60000140003500000a0000b800005000040000022080edd40010a32366a00085181b3500042100dba8002100404800010800000000083281f3500041900fba80020c807cd400104d00e0000082401f7500040a01d9a8002050079d400102503eaa00081281f3500040940dba800204a04cd4001024036ea00081201b35
|18=>0x82040d3a8004004000000020010366a0010008070400080000d9a8004000068d400200000e40001000004000008000018200040000089000200000400001000000010008000000000038100eed4001c0803fea000e04008e000062808d9a80031104cdd400188823eea000c4402200000620c8d9a800310446cd40018812366a000c4015b3500062009d9a800310047cd40018802366a000c4011b2000062000110000304216cd400180020440000c0010000
|19=>0x200140fba801000a06dd40080040366a0040020126100200040d9a801000202d540080010064000400011120002000081800010000404d00080000766a00400001b7500200000d9a801000000c0000800000200004000000b400200000020000800200c9c0030830366a001400040010008a0c8d9a800430606ed40021820052800108801bb10008440014a000420000a540020832366a00104181b3500082080d8a80041040489000208201e0000104100004
|20=>0x400100d8a802000206cd4010001006400080008020000400001192002000006cd401000000640008000003000040000011280200000008000a1830556800508282af400284041dda801410e06dd400a004034ea00500001b350028000010a001200a07dd4009000036aa00408380af4002040001da001020000a54008085077ea00404281b7500201a00dba801009a06dd40080440060000401281b7500200200d9a801000a0edd40080050624000400282160
|21=>0x640940dba80320400685401804903e6a00c00001b35006000001000024104064540120000004a008c1085b3500442000c9a80220da02c000110440128000881481f7500440848d9a802204207cd40110210366a0088100322000440801590002204006cd40110200260200880081b35004400401000022000000000108a00b66a0084401193500420002c8a8021000100940108000366a0080240020100401200080802008000c000100080366a00800281b15
|22=>0x20012210366300015181935800020c0d9ac00000006cd50000000366a4000088033120000000d988e0001002d942000000000a0400000001101020002000804020000a4001906901e0000c82601f00
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x100000005000000000000007
|7,0=>0x1e01800000390007b0d02f000270006e17c00000000000009c0009c4300000114000447e2203400000000090000c000700007700000000191f4000000000000078003c000018240446e000000001900027040230000023400000000440000019000001945800000000000642118482000002a0731b84638459000002b0270786d3680c0645a
|8,0=>0x6857d1c02248d9f3a00a32a2d7d440004ec05a54004415980000170069992aa6f4f8925502d8d0716f0ba308190000004c197589d5a9b56fc0029839008013740015c1822c00000010459e1082f3b4670659a12c000053a609d712145151a8355d40640a065ed0002a6f06e35c96774118cd100009a00001004001e80a00001034ae025b3064031a58c72c6c3a834b18ee6b84d5c214794000080a0009400075
|8,1=>0x68341c450065c57fdbd0d4096f0270e9620bc000058602011022ab044110017101cd10000051099b0c001b80178c02126602e0177a0015cc685f41e000e5064344b83d1264c830841bc1a13c6c198030e000045c79b800719df0041906591044000855b6b2500459c0000837c9583801678115d1340680b9c419000400001100a5e1ca505cc0078c01762964a409540570000194d17004016ca3a02a114b037
|8,2=>0x6c85000486781200481068dc7cc001e0b97183372800489255c8030014206801044011fde009c025e03f0d0020bd0e0c0005c4005d97c00c0f001c62b418000110040811c1a5a40a0006e064118497713a40860a10de553d01a0023e0044a5942f000126f08e334000440106509045c2006584bc9c0c0006a812348094e1b4001ec0780a2dc000c811000012f00331dbd001a304671aa8f189c4c0c81c00401
|8,3=>0xb10020000000a0800c0087c024ec5001dc6002c5024e20790b00426071c6021a2799c61f0000642c0047800c1a00019066588200004412044e00019b07829001d580c0000193b0a6c07863078b0006c8048a9044df0650800073718271b8932782f0669c4a03c9c97a5d81902031009ac
|9,0=>0x8ba5a7e546762484e4f2a89ab76d19889bb84e01361f2145558d5c1834222d2a31aa43202095ade48e66b5b45229269a2c1136dcb82a7a92e344c22b0658397036725d786cf3a058b029c8359d2a9acc7f06b7826332c9b294ab289cd988fe855cd8b1ea0ac5d6cc1d6382a9de1d3ba5d1da0b8da563511f65912ad57f520f589164528c970c8744cb51785cab63b0f8c388eb0615d0a36456ea7ba74ce8fdce
|9,1=>0x6e1c096589b29dc1825b2c50046926a44bc8bc511444e09a5b7bacd80159218e3246a51d1583057e58db05455a21e7d85ebb00273a0147145da430fa8c568abe73a7c51af28f4f21e9402e0711c681567f58a13de17c10a454bf481ce6c4210fe0f579b60edc441632a6a5d9ce757bdfe1069ab268a584c8602b7452615d5d14cde733caf761b34f53128e309092d93a5f6ca667e08f39a976bc529ecbd904d9
|9,2=>0x145485be2b896378848944524af85760683ae6983a65b145496fdde811959a029149796de9a2cd0c43ec7301e127e855ed986229969aa0635cc31a2976655082100bc56330ce20cbb69e57189849e607a6ec961dd349c280fde016c7650cde21e703927c8542586192212058f2162c978a85fb6057c60e78548e66fa238f5e4128b18996746044652385344e9d80e69596306ba3ecd373d900518f582aeaa16c
|9,3=>0x8c155401441f67498a401953d065300a1458899da0a9ea405451
|10,0=>0x91a7ea69979fe9396e849f8d9338b16e6062420222a1cacab17c54c78a7e55d1e7dd044590757e478fd0da0a7b2d8d01d8e753936a51803f62a8fe1aa7aa9b04f9ac5557a6927dabf4d6643be9aa30f73ae6454df446e5d4095d945032fab37a537a19eb7beb88824852e44ad16e6a6b67e8f846521929a093688ab2169d087af6898aa846e252474e69d10c146c093e659b4ff14e059a95ca3a283da4986687
|10,1=>0x2645294169215606cb59e956b66421c79
|11,0=>0x4fc7922a0b4690121c87528524b49739d2b1da64ac4b4689327a51a310b6314a7148fc282b1
|12,0=>0x872c52a15864
|13,0=>0x51
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 10 (j%128);fld (pmP (k/32)) 45 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_253 12 roots_253 ops++addP pm 1 dom_118 7 roots_118 ops++addP pm 2 dom_251 12 roots_251 ops++addP pm 3 dom_198 5 roots_198 ops++addP pm 4 dom_247 12 roots_247 ops++addP pm 5 dom_223 11 roots_223 ops++addP pm 6 dom_126 8 roots_126 ops++addP pm 7 dom_94 6 roots_94 ops++addP pm 8 dom_239 11 roots_239 ops++addP pm 9 dom_254 11 roots_254 ops++addP pm 10 dom_238 9 roots_238 ops++addP pm 11 dom_191 11 roots_191 ops++addP pm 12 dom_127 11 roots_127 ops++addP pm 13 dom_222 9 roots_222 ops++addP pm 14 dom_143 6 roots_143 ops++addP pm 15 dom_173 7 roots_173 ops++addP pm 16 dom_207 9 roots_207 ops++addP pm 17 dom_109 7 roots_109 ops++addP pm 18 dom_204 5 roots_204 ops++addP pm 19 dom_63 8 roots_63 ops++addP pm 20 dom_159 9 roots_159 ops++addP pm 21 dom_190 8 roots_190 ops++addP pm 22 dom_110 6 roots_110 ops++addP pm 23 dom_250 10 roots_250 ops++addP pm 24 dom_175 8 roots_175 ops++addP pm 25 dom_174 6 roots_174 ops++addP pm 26 dom_95 9 roots_95 ops++addP pm 27 dom_158 6 roots_158 ops++addP pm 28 dom_235 10 roots_235 ops++addP pm 29 dom_206 6 roots_206 ops++addP pm 30 dom_79 6 roots_79 ops++addP pm 31 dom_111 8 roots_111 ops++addP pm 32 dom_27 4 roots_27 ops++addP pm 33 dom_246 10 roots_246 ops++addP pm 34 dom_62 5 roots_62 ops++addP pm 35 dom_47 5 roots_47 ops++addP pm 36 dom_243 10 roots_243 ops++addP pm 37 dom_249 10 roots_249 ops++addP pm 38 dom_234 8 roots_234 ops++addP pm 39 dom_230 8 roots_230 ops++addP pm 40 dom_231 9 roots_231 ops++addP pm 41 dom_182 7 roots_182 ops++addP pm 42 dom_186 7 roots_186 ops++addP pm 43 dzo_155_4 5 roots_155 ops++addP pm 44 dzo_59_4 5 roots_59 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_255 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_198 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_247 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_223 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_238 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_191 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_127 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_143 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_207 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_204 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_175 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_174 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_79 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_47 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_zo_155_4_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_zo_59_4_27 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_253 12 s (0,roots_253.map (·&&&dom_253)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_253 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xffffffffffffffff0000000000000000,64),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_255==dom_255)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 3000009 zs symsG zs (hk 3000009 zs)
theorem ori_ok {v ys} (h:RunD true dom_255 gM v ys):RunD true dom_255 gM v (ori ys):=pickMin_runD 3000009 ys h symsG ys (hk 3000009 ys) symsG_ok h
def Z (s:Nat):=barP dom_255 gM mpG SD SS NN hAt idxH ori 3000009 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 14 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 14 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 114 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 114 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 256 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_256 : ∀ i, 256 ≤ i → i < 384 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 256 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_384 : ∀ i, 384 ≤ i → i < 474 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 90 384 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 474 → Z 8 i = true := (range_split (range_split z8_0 z8_128) (range_split z8_256 z8_384))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_0 : ∀ i, 0 ≤ i → i < 128 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_128 : ∀ i, 128 ≤ i → i < 256 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_256 : ∀ i, 256 ≤ i → i < 384 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 256 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_384 : ∀ i, 384 ≤ i → i < 405 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 21 384 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 405 → Z 9 i = true := (range_split (range_split z9_0 z9_128) (range_split z9_256 z9_384))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_0 : ∀ i, 0 ≤ i → i < 128 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_128 : ∀ i, 128 ≤ i → i < 141 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 13 128 = true)
private theorem z10 : ∀ i, 0 ≤ i → i < 141 → Z 10 i = true := (range_split z10_0 z10_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 30 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 30 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z12 : ∀ i, 0 ≤ i → i < 5 → Z 12 i = true := span_ok (by decide +kernel : span (Z 12) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z13 : ∀ i, 0 ≤ i → i < 1 → Z 13 i = true := span_ok (by decide +kernel : span (Z 13) 1 0 = true)
theorem checked (s:Nat) (hs:s≤13):∀ i<NN s,bar dom_255 gM mpG SD SS NN hAt idxH ori 3000009 mkCut s i=true:=by
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
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [3, 1] }, { op := GateOp.or, inputs := [8, 2] }, { op := GateOp.or, inputs := [4, 3] }, { op := GateOp.or, inputs := [7, 6] }, { op := GateOp.or, inputs := [11, 10] }, { op := GateOp.or, inputs := [5, 11] }, { op := GateOp.or, inputs := [1, 11] }, { op := GateOp.or, inputs := [4, 5] }, { op := GateOp.and, inputs := [6, 7] }, { op := GateOp.and, inputs := [14, 15] }, { op := GateOp.and, inputs := [12, 0] }, { op := GateOp.and, inputs := [9, 13] }, { op := GateOp.or, inputs := [16, 17] }, { op := GateOp.or, inputs := [20, 18] }, { op := GateOp.or, inputs := [21, 19] }]

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 22⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
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

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_52324_aux

theorem PEqualNP.Outside.L_meta_52324 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_52324_aux.main
