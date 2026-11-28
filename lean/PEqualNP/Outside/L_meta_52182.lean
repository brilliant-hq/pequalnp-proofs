import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_52182_aux
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

def dom_53 : Nat := 0x33003300330033
def goal_53 : Nat := 0xfafaf0f0fafa0000fafaf0f0fafa0000fafaf0f0fafa0000fafaf0f0fafa0000
def roots_53 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xfefefcfcfefe0000fefefcfcfefe0000fefefcfcfefe0000fefefcfcfefe0000
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_57 : Nat := 0x303030303030303
def goal_57 : Nat := 0xffaaff00aaaaaa00ffaaff00aaaaaa00ffaaff00aaaaaa00ffaaff00aaaaaa00
def roots_57 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_58 : Nat := 0x505050505050505
def goal_58 : Nat := 0xffccffcccccc0000ffccffcccccc0000ffccffcccccc0000ffccffcccccc0000
def roots_58 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xffeeffcceeeeaa00ffeeffcceeeeaa00ffeeffcceeeeaa00ffeeffcceeeeaa00
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_60 : Nat := 0x1111111111111111
def goal_60 : Nat := 0xfff0fff0f0f00000fff0fff0f0f00000fff0fff0f0f00000fff0fff0f0f00000
def roots_60 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xfffafff0fafaaa00fffafff0fafaaa00fffafff0fafaaa00fffafff0fafaaa00
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_62 : Nat := 0x5555555555555555
def goal_62 : Nat := 0xfffcfffcfcfc0000fffcfffcfcfc0000fffcfffcfcfc0000fffcfffcfcfc0000
def roots_62 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfffefffcfefeaa00fffefffcfefeaa00fffefffcfefeaa00fffefffcfefeaa00
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_73 : Nat := 0x3030000000000000303
def goal_73 : Nat := 0xffaaffaaffaaffaaaa00aa00aa00aa00ffaaffaaffaaffaaaa00aa00aa00aa00
def roots_73 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_75 : Nat := 0xf0f0000000000000f0f
def goal_75 : Nat := 0xffeeffeeffeeffeeaa00aa00aa00aa00ffeeffeeffeeffeeaa00aa00aa00aa00
def roots_75 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0]

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
def goal_85 : Nat := 0xffffaaaaffffaaaafafa0000fafa0000ffffaaaaffffaaaafafa0000fafa0000
def roots_85 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_86 : Nat := 0x5500550000000000550055
def goal_86 : Nat := 0xffffccccffffccccfcfc0000fcfc0000ffffccccffffccccfcfc0000fcfc0000
def roots_86 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_87 : Nat := 0xff00ff0000000000ff00ff
def goal_87 : Nat := 0xffffeeeeffffeeeefefe0000fefe0000ffffeeeeffffeeeefefe0000fefe0000
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

def dom_92 : Nat := 0x111111110000000011111111
def goal_92 : Nat := 0xffffff00ffffff00f0f00000f0f00000ffffff00ffffff00f0f00000f0f00000
def roots_92 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_93 : Nat := 0x333333330000000033333333
def goal_93 : Nat := 0xffffffaaffffffaafafaaa00fafaaa00ffffffaaffffffaafafaaa00fafaaa00
def roots_93 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_94 : Nat := 0x555555550000000055555555
def goal_94 : Nat := 0xffffffccffffffccfcfc0000fcfc0000ffffffccffffffccfcfc0000fcfc0000
def roots_94 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_95 : Nat := 0xffffffff00000000ffffffff
def goal_95 : Nat := 0xffffffeeffffffeefefeaa00fefeaa00ffffffeeffffffeefefeaa00fefeaa00
def roots_95 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_98 : Nat := 0x5000000050000000500000005
def goal_98 : Nat := 0xffffffffcccccccccccccccc00000000ffffffffcccccccccccccccc00000000
def roots_98 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_99 : Nat := 0xf0000000f0000000f0000000f
def goal_99 : Nat := 0xffffffffeeeeeeeecccccccc00000000ffffffffeeeeeeeecccccccc00000000
def roots_99 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_101 : Nat := 0x33000000330000003300000033
def goal_101 : Nat := 0xffffffffaaaaaaaaf0f0f0f000000000ffffffffaaaaaaaaf0f0f0f000000000
def roots_101 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_103 : Nat := 0xff000000ff000000ff000000ff
def goal_103 : Nat := 0xffffffffeeeeeeeefcfcfcfc00000000ffffffffeeeeeeeefcfcfcfc00000000
def roots_103 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

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
def goal_108 : Nat := 0xffffffffff00ff00fff0fff000000000ffffffffff00ff00fff0fff000000000
def roots_108 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_109 : Nat := 0x3333000033330000333300003333
def goal_109 : Nat := 0xffffffffffaaffaafff0fff0aa00aa00ffffffffffaaffaafff0fff0aa00aa00
def roots_109 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_110 : Nat := 0x5555000055550000555500005555
def goal_110 : Nat := 0xffffffffffccffccfffcfffc00000000ffffffffffccffccfffcfffc00000000
def roots_110 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xffffffffffeeffeefffcfffcaa00aa00ffffffffffeeffeefffcfffcaa00aa00
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

def dom_117 : Nat := 0x330033003300330033003300330033
def goal_117 : Nat := 0xffffffffffffaaaafafaf0f0fafa0000ffffffffffffaaaafafaf0f0fafa0000
def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xffffffffffffccccfcfcfcfcfcfc0000ffffffffffffccccfcfcfcfcfcfc0000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xffffffffffffeeeefefefcfcfefe0000ffffffffffffeeeefefefcfcfefe0000
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

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

def dom_124 : Nat := 0x11111111111111111111111111111111
def goal_124 : Nat := 0xffffffffffffff00fff0fff0f0f00000ffffffffffffff00fff0fff0f0f00000
def roots_124 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xffffffffffffffaafffafff0fafaaa00ffffffffffffffaafffafff0fafaaa00
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_126 : Nat := 0x55555555555555555555555555555555
def goal_126 : Nat := 0xffffffffffffffccfffcfffcfcfc0000ffffffffffffffccfffcfffcfcfc0000
def roots_126 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xffffffffffffffeefffefffcfefeaa00ffffffffffffffeefffefffcfefeaa00
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_137 : Nat := 0x30300000000000000000000000000000303
def goal_137 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_137 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_139 : Nat := 0xf0f00000000000000000000000000000f0f
def goal_139 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffeeaa00aa00aa00aa00aa00aa00aa00aa00
def roots_139 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_151 : Nat := 0xff00ff00000000000000000000000000ff00ff
def goal_151 : Nat := 0xffffeeeeffffeeeeffffeeeeffffeeeefefe0000fefe0000fefe0000fefe0000
def roots_151 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def goal_155 : Nat := 0xffffffeeffffffeeffffffeeffffffeeeeeeaa00eeeeaa00eeeeaa00eeeeaa00
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_156 : Nat := 0x1111111100000000000000000000000011111111
def goal_156 : Nat := 0xffffff00ffffff00ffffff00ffffff00f0f00000f0f00000f0f00000f0f00000
def roots_156 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_157 : Nat := 0x3333333300000000000000000000000033333333
def goal_157 : Nat := 0xffffffaaffffffaaffffffaaffffffaafafaaa00fafaaa00fafaaa00fafaaa00
def roots_157 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_158 : Nat := 0x5555555500000000000000000000000055555555
def goal_158 : Nat := 0xffffffccffffffccffffffccffffffccfcfc0000fcfc0000fcfc0000fcfc0000
def roots_158 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_159 : Nat := 0xffffffff000000000000000000000000ffffffff
def goal_159 : Nat := 0xffffffeeffffffeeffffffeeffffffeefefeaa00fefeaa00fefeaa00fefeaa00
def roots_159 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_167 : Nat := 0xff000000ff0000000000000000000000ff000000ff
def goal_167 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeeefcfcfcfc00000000fcfcfcfc00000000
def roots_167 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_171 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
def goal_171 : Nat := 0xffffffffffeeffeeffffffffffeeffeeffccffccaa00aa00ffccffccaa00aa00
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_174 : Nat := 0x55550000555500000000000000000000555500005555
def goal_174 : Nat := 0xffffffffffccffccffffffffffccffccfffcfffc00000000fffcfffc00000000
def roots_174 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_175 : Nat := 0xffff0000ffff00000000000000000000ffff0000ffff
def goal_175 : Nat := 0xffffffffffeeffeeffffffffffeeffeefffcfffcaa00aa00fffcfffcaa00aa00
def roots_175 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_179 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f
def goal_179 : Nat := 0xffffffffffffeeeeffffffffffffeeeeeeeecccceeee0000eeeecccceeee0000
def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_182 : Nat := 0x5500550055005500000000000000000055005500550055
def goal_182 : Nat := 0xffffffffffffccccffffffffffffccccfcfcfcfcfcfc0000fcfcfcfcfcfc0000
def roots_182 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_183 : Nat := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
def goal_183 : Nat := 0xffffffffffffeeeeffffffffffffeeeefefefcfcfefe0000fefefcfcfefe0000
def roots_183 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_186 : Nat := 0x50505050505050500000000000000000505050505050505
def goal_186 : Nat := 0xffffffffffffffccffffffffffffffccffccffcccccc0000ffccffcccccc0000
def roots_186 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffffffffffeeffffffffffffffeeffeeffcceeeeaa00ffeeffcceeeeaa00
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_189 : Nat := 0x333333333333333300000000000000003333333333333333
def goal_189 : Nat := 0xffffffffffffffaaffffffffffffffaafffafff0fafaaa00fffafff0fafaaa00
def roots_189 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_190 : Nat := 0x555555555555555500000000000000005555555555555555
def goal_190 : Nat := 0xffffffffffffffccffffffffffffffccfffcfffcfcfc0000fffcfffcfcfc0000
def roots_190 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xffffffffffffffeeffffffffffffffeefffefffcfefeaa00fffefffcfefeaa00
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_193 : Nat := 0x3000000000000000300000000000000030000000000000003
def goal_193 : Nat := 0xffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000000000000000
def roots_193 : List Nat := [xs256.getD 0 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_195 : Nat := 0xf000000000000000f000000000000000f000000000000000f
def goal_195 : Nat := 0xffffffffffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0000000000000000
def roots_195 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_200 : Nat := 0x101000000000000010100000000000001010000000000000101
def goal_200 : Nat := 0xffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff000000000000000000
def roots_200 : List Nat := [xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_201 : Nat := 0x303000000000000030300000000000003030000000000000303
def goal_201 : Nat := 0xffffffffffffffffffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00aa00aa00
def roots_201 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_202 : Nat := 0x505000000000000050500000000000005050000000000000505
def goal_202 : Nat := 0xffffffffffffffffffccffccffccffccffccffccffccffcc0000000000000000
def roots_202 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffffffffffffffffffeeffeeffeeffeeffeeffeeffeeffeeaa00aa00aa00aa00
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_209 : Nat := 0x30003000000000003000300000000000300030000000000030003
def goal_209 : Nat := 0xffffffffffffffffffffaaaaffffaaaaffffaaaaffffaaaaaaaa0000aaaa0000
def roots_209 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_210 : Nat := 0x50005000000000005000500000000000500050000000000050005
def goal_210 : Nat := 0xffffffffffffffffffffccccffffccccffffccccffffcccccccc0000cccc0000
def roots_210 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffffffffffffffffffeeeeffffeeeeffffeeeeffffeeeeeeee0000eeee0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_213 : Nat := 0x330033000000000033003300000000003300330000000000330033
def goal_213 : Nat := 0xffffffffffffffffffffaaaaffffaaaaffffaaaaffffaaaafafa0000fafa0000
def roots_213 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xffffffffffffffffffffccccffffccccffffccccffffccccfcfc0000fcfc0000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xffffffffffffffffffffeeeeffffeeeeffffeeeeffffeeeefefe0000fefe0000
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

def dom_220 : Nat := 0x11111111000000001111111100000000111111110000000011111111
def goal_220 : Nat := 0xffffffffffffffffffffff00ffffff00ffffff00ffffff00f0f00000f0f00000
def roots_220 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def goal_221 : Nat := 0xffffffffffffffffffffffaaffffffaaffffffaaffffffaafafaaa00fafaaa00
def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xffffffffffffffffffffffccffffffccffffffccffffffccfcfc0000fcfc0000
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xffffffffffffffffffffffeeffffffeeffffffeeffffffeefefeaa00fefeaa00
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def goal_227 : Nat := 0xffffffffffffffffffffffffeeeeeeeeffffffffeeeeeeeecccccccc00000000
def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def goal_230 : Nat := 0xffffffffffffffffffffffffccccccccffffffffccccccccfcfcfcfc00000000
def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def goal_231 : Nat := 0xffffffffffffffffffffffffeeeeeeeeffffffffeeeeeeeefcfcfcfc00000000
def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffffffffffffffffffccffccffffffffffccffccffccffcc00000000
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffffffffffffffffffeeffeeffffffffffeeffeeffccffccaa00aa00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xffffffffffffffffffffffffffaaffaaffffffffffaaffaafff0fff0aa00aa00
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_238 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def goal_238 : Nat := 0xffffffffffffffffffffffffffccffccffffffffffccffccfffcfffc00000000
def roots_238 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xffffffffffffffffffffffffffeeffeeffffffffffeeffeefffcfffcaa00aa00
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_241 : Nat := 0x3000300030003000300030003000300030003000300030003000300030003
def goal_241 : Nat := 0xffffffffffffffffffffffffffffaaaaffffffffffffaaaaaaaa0000aaaa0000
def roots_241 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def goal_242 : Nat := 0xffffffffffffffffffffffffffffccccffffffffffffcccccccccccccccc0000
def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffffffffffffffffffffeeeeffffffffffffeeeeeeeecccceeee0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_245 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
def goal_245 : Nat := 0xffffffffffffffffffffffffffffaaaaffffffffffffaaaafafaf0f0fafa0000
def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xffffffffffffffffffffffffffffccccffffffffffffccccfcfcfcfcfcfc0000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xffffffffffffffffffffffffffffeeeeffffffffffffeeeefefefcfcfefe0000
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_248 : Nat := 0x101010101010101010101010101010101010101010101010101010101010101
def goal_248 : Nat := 0xffffffffffffffffffffffffffffff00ffffffffffffff00ff00ff0000000000
def roots_248 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffffffffffffffffffaaffffffffffffffaaffaaff00aaaaaa00
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffffffffffffffffffccffffffffffffffccffccffcccccc0000
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffffffffffffffffffeeffffffffffffffeeffeeffcceeeeaa00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_252 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
def goal_252 : Nat := 0xffffffffffffffffffffffffffffff00ffffffffffffff00fff0fff0f0f00000
def roots_252 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xffffffffffffffffffffffffffffffaaffffffffffffffaafffafff0fafaaa00
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xffffffffffffffffffffffffffffffccffffffffffffffccfffcfffcfcfc0000
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xffffffffffffffffffffffffffffffeeffffffffffffffeefffefffcfefeaa00
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
def isoMvS_104:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_104:Lower true dom_104 roots_104 goal_104 4:=lower_iso_b isoMvS_104 (by decide +kernel) lowS_73
def isoMvS_137:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_137:Lower true dom_137 roots_137 goal_137 4:=lower_iso_b isoMvS_137 (by decide +kernel) lowS_73
def isoMvS_193:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_193:Lower true dom_193 roots_193 goal_193 4:=lower_iso_b isoMvS_193 (by decide +kernel) lowS_73
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
|0=>0x4045124501015052150514501
|_=>0
def oO:Nat→Nat→Nat
|3,0=>0x20000
|4,0=>0x6242220000
|5,0=>0x9181
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0xfca7630
|_=>0
def pmB:Nat→Nat→Nat
|3,0=>0x40
|4,0=>0x2940
|5,0=>0xf6
|6,0=>6
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 4 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_200 4 roots_200 ops++addP pm 1 dom_137 4 roots_137 ops++addP pm 2 dom_193 4 roots_193 ops++addP pm 3 dom_73 4 roots_73 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_201 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_200 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_193 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_73 _ g hchk
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
def isoMvS_29:List (Nat×Nat):=[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_29:Lower true dom_29 roots_29 goal_29 4:=lower_iso_b isoMvS_29 (by decide +kernel) lowS_27
def isoMvS_43:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_43:Lower true dom_43 roots_43 goal_43 4:=lower_iso_b isoMvS_43 (by decide +kernel) lowS_27
def isoMvS_45:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_45:Lower true dom_45 roots_45 goal_45 4:=lower_iso_b isoMvS_45 (by decide +kernel) lowS_27
def isoMvS_51:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_51:Lower true dom_51 roots_51 goal_51 4:=lower_iso_b isoMvS_51 (by decide +kernel) lowS_27
def isoMvS_53:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_53:Lower true dom_53 roots_53 goal_53 4:=lower_iso_b isoMvS_53 (by decide +kernel) lowS_27
def isoMvS_57:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_57:Lower true dom_57 roots_57 goal_57 4:=lower_iso_b isoMvS_57 (by decide +kernel) lowS_27
def isoMvS_58:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_58:Lower true dom_58 roots_58 goal_58 4:=lower_iso_b isoMvS_58 (by decide +kernel) lowS_27
def isoMvS_60:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_60:Lower true dom_60 roots_60 goal_60 4:=lower_iso_b isoMvS_60 (by decide +kernel) lowS_27
def isoMvS_85:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_85:Lower true dom_85 roots_85 goal_85 5:=lower_iso_b isoMvS_85 (by decide +kernel) lowS_75
def isoMvS_86:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_86:Lower true dom_86 roots_86 goal_86 5:=lower_iso_b isoMvS_86 (by decide +kernel) lowS_75
def isoMvS_89:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_89:Lower true dom_89 roots_89 goal_89 5:=lower_iso_b isoMvS_89 (by decide +kernel) lowS_83
def isoMvS_90:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_90:Lower true dom_90 roots_90 goal_90 5:=lower_iso_b isoMvS_90 (by decide +kernel) lowS_75
def isoMvS_92:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_92:Lower true dom_92 roots_92 goal_92 4:=lower_iso_b isoMvS_92 (by decide +kernel) lowS_27
def isoMvS_99:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_99:Lower true dom_99 roots_99 goal_99 5:=lower_iso_b isoMvS_99 (by decide +kernel) lowS_75
def isoMvS_101:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_101:Lower true dom_101 roots_101 goal_101 4:=lower_iso_b isoMvS_101 (by decide +kernel) lowS_27
def isoMvS_105:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_105:Lower true dom_105 roots_105 goal_105 5:=lower_iso_b isoMvS_105 (by decide +kernel) lowS_83
def isoMvS_106:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_106:Lower true dom_106 roots_106 goal_106 5:=lower_iso_b isoMvS_106 (by decide +kernel) lowS_83
def isoMvS_108:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_108:Lower true dom_108 roots_108 goal_108 5:=lower_iso_b isoMvS_108 (by decide +kernel) lowS_75
def isoMvS_113:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_113:Lower true dom_113 roots_113 goal_113 5:=lower_iso_b isoMvS_113 (by decide +kernel) lowS_75
def isoMvS_114:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_114:Lower true dom_114 roots_114 goal_114 5:=lower_iso_b isoMvS_114 (by decide +kernel) lowS_83
def isoMvS_120:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_120:Lower true dom_120 roots_120 goal_120 5:=lower_iso_b isoMvS_120 (by decide +kernel) lowS_75
def isoMvS_139:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_139:Lower true dom_139 roots_139 goal_139 5:=lower_iso_b isoMvS_139 (by decide +kernel) lowS_75
def isoMvS_156:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_156:Lower true dom_156 roots_156 goal_156 4:=lower_iso_b isoMvS_156 (by decide +kernel) lowS_27
def isoMvS_195:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_195:Lower true dom_195 roots_195 goal_195 5:=lower_iso_b isoMvS_195 (by decide +kernel) lowS_83
def isoMvS_202:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_202:Lower true dom_202 roots_202 goal_202 5:=lower_iso_b isoMvS_202 (by decide +kernel) lowS_83
def isoMvS_209:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_209:Lower true dom_209 roots_209 goal_209 7:=lower_iso_b isoMvS_209 (by decide +kernel) lowS_201
def isoMvS_210:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_210:Lower true dom_210 roots_210 goal_210 7:=lower_iso_b isoMvS_210 (by decide +kernel) lowS_201
theorem lowS_31:Lower true dom_31 roots_31 goal_31 5:=lower_slice_b [(0xcccccccc,16,18)] (by decide +kernel) lowS_29
theorem lowS_55:Lower true dom_55 roots_55 goal_55 5:=lower_slice_b [(0xcc00cc00cc00cc,16,18)] (by decide +kernel) lowS_53
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
def dzo_89_4:=0x303030300000000030303030
def gzo_89_4:=0x303030200000000030302000
def gsh_89_4:=0x30303020000000003030200
theorem lowS_zo_89_4_73:Lower true dzo_89_4 roots_89 gzo_89_4 5:=lower_iso_b (d1:=dom_89) (r1:=roots_89) (T1:=gsh_89_4) [(dom_89,4)] (by decide +kernel) (lower_slice_b (T:=gsh_89_4) [(0x30300000000000003030000,0,16)] (by decide +kernel) lowS_73)
namespace S_93
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(4,20),(5,13),(5,21),(5,69),(8,9),(8,72),(12,13),(12,28),(12,76),(16,17),(16,20),(16,80),(24,25),(24,28),(24,88),(64,65),(64,72),(64,80),(68,69),(68,76),(68,84)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_93.map (·&&&dom_93)
def gM:=goal_93&&&dom_93
def NN:Nat→Nat
|4=>1
|5=>1
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xc09ca
|5,0=>0x1e1fd
|6,0=>0x4011c
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x330033000000000033003300cccccccc000000008888888b33300000000000033330000c0c0c0c000000000c0c0c0c22222222000000002222222200cc00cc000000000088008b33333330000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x99a133a84688
|_=>0
def sO:Nat→Nat→Nat
|4,0=>5
|5,0=>0x56
|6,0=>0xb5
|_,_=>0
def wAt:=mkWire dB 7 94 0x3fffffffffffffffffffffff
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
addP pm 0 dom_89 5 roots_89 ops++addP pm 1 dom_92 4 roots_92 ops++addP pm 2 dzo_89_4 5 roots_89 ops++addP pm 3 dom_85 5 roots_85 ops++addP pm 4 dom_29 4 roots_29 ops++addP pm 5 dom_73 4 roots_73 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_93 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_92 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_89_4_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_29 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_73 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_89 5 s (0,roots_89.map (·&&&dom_89)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_93 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_89 h
def symsG:List (List (Nat×Nat)):=[[(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_93==dom_93)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_93 gM v ys):RunD true dom_93 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_93 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_93 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_94:Lower true dom_94 roots_94 goal_94 6:=lower_slice_b [(0x505050500000000050505050,16,20)] (by decide +kernel) lowS_90
theorem lowS_117:Lower true dom_117 roots_117 goal_117 6:=lower_slice_b [(0x300030003000300030003000300030,16,20)] (by decide +kernel) lowS_113
theorem lowS_118:Lower true dom_118 roots_118 goal_118 6:=lower_slice_b [(0x500050005000500050005000500050,16,20)] (by decide +kernel) lowS_114
theorem lowS_203:Lower true dom_203 roots_203 goal_203 8:=lower_slice_b [(0xc0c0000000000000c0c0000000000000c0c0000000000000c0c,64,66)] (by decide +kernel) lowS_201
theorem lowS_211:Lower true dom_211 roots_211 goal_211 8:=lower_slice_b [(0xa000a00000000000a000a00000000000a000a00000000000a000a,16,17)] (by decide +kernel) lowS_210
theorem lowS_213:Lower true dom_213 roots_213 goal_213 8:=lower_slice_b [(0x300030000000000030003000000000003000300000000000300030,16,20)] (by decide +kernel) lowS_209
def isoMvS_47:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_47:Lower true dom_47 roots_47 goal_47 5:=lower_iso_b isoMvS_47 (by decide +kernel) lowS_31
def isoMvS_61:List (Nat×Nat):=[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_61:Lower true dom_61 roots_61 goal_61 7:=lower_iso_b isoMvS_61 (by decide +kernel) lowS_59
def isoMvS_62:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_62:Lower true dom_62 roots_62 goal_62 5:=lower_iso_b isoMvS_62 (by decide +kernel) lowS_55
def isoMvS_103:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_103:Lower true dom_103 roots_103 goal_103 6:=lower_iso_b isoMvS_103 (by decide +kernel) lowS_94
def isoMvS_107:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_107:Lower true dom_107 roots_107 goal_107 7:=lower_iso_b isoMvS_107 (by decide +kernel) lowS_91
def isoMvS_109:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_109:Lower true dom_109 roots_109 goal_109 7:=lower_iso_b isoMvS_109 (by decide +kernel) lowS_93
def isoMvS_110:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_110:Lower true dom_110 roots_110 goal_110 6:=lower_iso_b isoMvS_110 (by decide +kernel) lowS_87
def isoMvS_115:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_115:Lower true dom_115 roots_115 goal_115 7:=lower_iso_b isoMvS_115 (by decide +kernel) lowS_91
def isoMvS_121:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_121:Lower true dom_121 roots_121 goal_121 7:=lower_iso_b isoMvS_121 (by decide +kernel) lowS_91
def isoMvS_122:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_122:Lower true dom_122 roots_122 goal_122 7:=lower_iso_b isoMvS_122 (by decide +kernel) lowS_91
def isoMvS_124:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_124:Lower true dom_124 roots_124 goal_124 6:=lower_iso_b isoMvS_124 (by decide +kernel) lowS_117
def isoMvS_151:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_151:Lower true dom_151 roots_151 goal_151 6:=lower_iso_b isoMvS_151 (by decide +kernel) lowS_87
def isoMvS_155:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_155:Lower true dom_155 roots_155 goal_155 7:=lower_iso_b isoMvS_155 (by decide +kernel) lowS_91
def isoMvS_157:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_157:Lower true dom_157 roots_157 goal_157 7:=lower_iso_b isoMvS_157 (by decide +kernel) lowS_93
def isoMvS_158:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_158:Lower true dom_158 roots_158 goal_158 6:=lower_iso_b isoMvS_158 (by decide +kernel) lowS_94
def isoMvS_167:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_167:Lower true dom_167 roots_167 goal_167 6:=lower_iso_b isoMvS_167 (by decide +kernel) lowS_94
def isoMvS_174:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_174:Lower true dom_174 roots_174 goal_174 6:=lower_iso_b isoMvS_174 (by decide +kernel) lowS_87
def isoMvS_179:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_179:Lower true dom_179 roots_179 goal_179 7:=lower_iso_b isoMvS_179 (by decide +kernel) lowS_91
def isoMvS_182:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_182:Lower true dom_182 roots_182 goal_182 6:=lower_iso_b isoMvS_182 (by decide +kernel) lowS_118
def isoMvS_186:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_186:Lower true dom_186 roots_186 goal_186 7:=lower_iso_b isoMvS_186 (by decide +kernel) lowS_91
def isoMvS_214:List (Nat×Nat):=[(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_214:Lower true dom_214 roots_214 goal_214 8:=lower_iso_b isoMvS_214 (by decide +kernel) lowS_213
def isoMvS_217:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_217:Lower true dom_217 roots_217 goal_217 8:=lower_iso_b isoMvS_217 (by decide +kernel) lowS_211
def isoMvS_218:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_218:Lower true dom_218 roots_218 goal_218 8:=lower_iso_b isoMvS_218 (by decide +kernel) lowS_203
def isoMvS_220:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_220:Lower true dom_220 roots_220 goal_220 7:=lower_iso_b isoMvS_220 (by decide +kernel) lowS_93
def isoMvS_230:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_230:Lower true dom_230 roots_230 goal_230 8:=lower_iso_b isoMvS_230 (by decide +kernel) lowS_213
def isoMvS_241:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_241:Lower true dom_241 roots_241 goal_241 8:=lower_iso_b isoMvS_241 (by decide +kernel) lowS_203
def isoMvS_242:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_242:Lower true dom_242 roots_242 goal_242 8:=lower_iso_b isoMvS_242 (by decide +kernel) lowS_211
def isoMvS_248:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_248:Lower true dom_248 roots_248 goal_248 8:=lower_iso_b isoMvS_248 (by decide +kernel) lowS_203
theorem lowS_63:Lower true dom_63 roots_63 goal_63 8:=lower_slice_b [(0xcccccccccccccccc,16,18)] (by decide +kernel) lowS_61
def dzo_75_4:=0xf0f0000000000000f0f0
def gzo_75_4:=0xf0e0000000000000a000
def gsh_75_4:=0xf0e0000000000000a00
theorem lowS_zo_75_4_75:Lower true dzo_75_4 roots_75 gzo_75_4 5:=lower_iso_b (d1:=dom_75) (r1:=roots_75) (T1:=gsh_75_4) [(dom_75,4)] (by decide +kernel) (lower_slice_b (T:=gsh_75_4) [] (by decide +kernel) lowS_75)
def dzo_91_4:=0xf0f0f0f000000000f0f0f0f0
def gzo_91_4:=0xf0f0f0e000000000f0f0a000
def gsh_91_4:=0xf0f0f0e000000000f0f0a00
theorem lowS_zo_91_4_75:Lower true dzo_91_4 roots_91 gzo_91_4 6:=lower_iso_b (d1:=dom_91) (r1:=roots_91) (T1:=gsh_91_4) [(dom_91,4)] (by decide +kernel) (lower_slice_b (T:=gsh_91_4) [(0xf0f0000000000000f0f0000,0,16)] (by decide +kernel) lowS_75)
namespace S_95
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(2,18),(2,66),(3,11),(3,19),(3,67),(4,20),(5,13),(5,21),(5,69),(6,22),(6,70),(7,15),(7,23),(7,71),(8,9),(8,72),(10,11),(10,26),(10,74),(12,13),(12,28),(12,76),(14,15),(14,30),(14,78),(16,17),(16,18),(16,20),(16,80),(24,25),(24,26),(24,28),(24,88),(64,65),(64,66),(64,72),(64,80),(68,69),(68,70),(68,76),(68,84)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_95.map (·&&&dom_95)
def gM:=goal_95&&&dom_95
def NN:Nat→Nat
|3=>1
|4=>30
|5=>85
|6=>62
|7=>14
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x3ce81
|4,0=>0xf1b5fe8564e38a3df1a9df031dee1bdd909dcf9ad646ad6072c134abba51af1e2ae412aa1cea8e19a8224a01709f76092dc76aebf5a98b44f9844964285eb25092243450e7b90d8cf01dec
|5,0=>0xfa06ef09e8ef388eecefea2aae9a8fe98c1e95f1e0848df30bd96cfd750bce476cdfeccdf39cc784cb911c825ec7c94c14ffc1115c0e05bffdfb75e0b7389b5b07b29fab1180ae24daa946a09479ef609d59d9ab649a8aa9a55f98c2d9757897154942609242e920d584b6c764696df14678226649b61b2761880609bb5d57c5bccb5ae8d5a1e55846e5821857fc35503a54c4254038523834ff0e4bad5419c03e0183c7f72fe2a2ddb22d69a2cb6a2923d279e92557a1f99c1f7881e3301c17911997118e108fac0718c03a2502385011a000f1e
|6,0=>0xf5039f4153f13f9ecae4e506be06f7ddcbad9a5dd72c4d703ed6b93d6302ca6a5c9547c6768c229ec1cbac0be3b4f33b36b1b2d7cb1d89af52eae7d1ae0d7a10389586087b7c8610f850b58461f80f557e7ff71c88702ee700976f9fe6c056679346346962b885c521562ab5376d535b84fe624cf6e400cf3f9d52fd502ef5c23e95220e61c84a1973410ca50cded0cb5b0c6f308bbc032dc018a7
|7,0=>0xeeb79e1246da081bf2a182ebc827c280477737744e3df4d1954088a2a99627e5802d40
|8,0=>0xc3264
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x33300330000000003030000ffff000000000000ffff0000bbbbbbbb00000000ababaaaaffffffcc00000000ccccccccffffeeee00000000ccccccccaaaaaaaa00000000aaaaaaaaffffaaaa00000000ffffaaaaeeeeeeee00000000eeee0000ffffffff0000000000000000ff00ff0000000000ff00ff00cccccccc00000000ccccccccffffffaa00000000aaaaaaaaffffffff00000000ffff0000f0f0f0f000000000f0f0f0f0eeeeeeee00000000eeeeeeeeffffff0000000000aaaaaa00
|0,1=>0xfff00ff000000000faf00aaffff000000000000fefe0000131311110000000003030000ffffffff00000000afafaaaaffffffff000000000f0f00000000000000000000afafaaaa0000000000000000fefefefe111111110000000000000000000000ff00000000ffffff000000000000000000ffffaaaaffffffaa00000000ff00ff00ffffffff00000000ffffaaaaffffff0000000000ffffff00ffffffff00000000aaaaaaaaffffffff00000000ffffff00ffffffff00000000ff00ff00
|0,2=>0xffffaaaa0000000000000000111111110000000010101010bbbbbbbb00000000bbbbaaaaffffff0000000000ffff00005f5f5555000000000f0f0000f1f1f1f100000000f0f0f0f0ffffffff00000000f0f0f0f000ff00ff0000000000aa00aa3333333300000000333322221111111100000000111100000000ffff0000000000000000333333330000000003030000ffffff000000000000000000555555550000000054545454333333330000000023232222111111110000000001010000
|0,3=>0xffff000000000000ff00555555550000000000000000000000ff00000000000000000000ffff000000000000aaaaaaaaffff00000000aaaaaaaa0f0f0000000000000f0f0000bbbbbbbb00000000aaaaaaaa0000000000000000ffffff0000ff00ff0000000000000000000000ff00000000000000aaffffffff00000000fafafafaffffffff00000000fefefefe0fff00ff000000000f0f0000afafaaaa00000000afafaaaa333311110000000033330000555555000000000055555500
|0,4=>0xefefeeee00000000efefeeeeffff00ff00000000ffff00aa000000aa00000000aaaaaaaaaaaaaaaa00000000aaaaaa00f0fff0ff00000000f0faf0faffff555500000000ffff000033330033000000003333000000aa00ff0000000000aa00aafefefefe00000000fefefefe333333330000000033330000ffff00ff00000000ffff000033333333000000003333330055555555000000000505000000ff00ff0000000000ff00aa55555555000000005555550000ff00ff0000000000ee00ee
|0,5=>0xff00000000000000ff00fafafafa00000000fafafafaf5f5f5f500000000f0f0f0f0ffffeeee00000000ffffeeee00005555000000000000000000ff00ff0000000000ff0000ff00ffff00000000ff00ff00ffffffaa00000000ffffffaa555555550000000050505050ffffffff00000000eeeeeeeef0fff0ff00000000f0f0f0f0555555550000000055550000
|_,_=>0
def sP:Nat→Nat
|0=>0xc640920c7808a0e3830a3a1c706027038e0c0491b260c105080c1051400706026838e0c645182e38105144cb02021c706042090e2a0829226501010e4c182024870202003911c082841c401050824105001c706143c38e0c34507061810c140c302162848604203830c082840608080
|1=>0xe3830114b838e0c0968a0e4d6020a283932c0828a0e24186041490e0c1452b0e3832a0228393280828a0e3948514a03930608292144c702182839312080871c1810a4e1c70604293071c181012494706146d207260c105148c706028838e0c29087260c10c143830a401c705147c38e
|2=>0x249d072c38302021c706041492f1c18101721dc0e04145371c0828a6c1c7066a049071c19a01141ca0e0c080871c1828a661c70602c838e0c14e0a0e383052428d8e0c085310e38302182839312082b00e0c70604049030c0828a460c3020a2978e0c0858a0e383020a1038e0c14d0a
|3=>0x1cd428a501c7060420507120c302021c98e042a2071c54105141c7060a2a1871c0828a841c98304045071c08092501c98904149072238105148c98e04160871c0808a801c9820a29f87260c10514f9c0e041453d1c18101781c71004145232638101601c7060405d8726e01820a28706
|4=>0x151038e0c292071c0828a001c7060ac89071c18c81141c7060228d871c1a781141c70604160871c1828a36fa70e041450726381059a1c98e04166071d2c28a501c9ca04145071c1810a921c7020a2a4071c19481241c70514e94072638101241c7068e28398260c10a8c1c9c50414507
|5=>0xc0828a7c383290a48507263810524283890618105141c98e0414507463830514e83b7224c7020a2838e0cd428a0e3810524294071c1810514f038e2019485141c70604045074a4c71004145071c1810a8c1c70604045073038302024839304145500e3834702483931c082840e38302
|6=>0x120828a0e38305154c38e0c0a901141e50e0c0828a0e383020a485252638105141db93060828a0e0c706042a3078a383020a2838e0c0828a0e8c70604145075e3830514e83be1c1a885141c88e0c0828a0e3810514a03831c18101141c7060229d0712383020a4838e0c0828a7e1c18e
|7=>0x1c18101141ca0e0c0828a0e3830564283b81c18105141c18e0c08292144c18604145071c18105141eb931c0828a0ef848e0c080871c18105155838e0c1451b0e4c7020a283bd1c18105154038e201828a741c7550c0828a0e3832902283931c0808a0f5098e041450726e07020a28393
|8=>0xe383020a283b71c19485141c98e04145071c18105242838e041455b0e3835a0a2838e2018105141c48e0c0828a0e0c70604145071c1828a741c70604145077c4c7020a298071c18105141de8e0d6428a0e383020aec5071c1829214e83961c18105141c7068e045071c19a8524283d8
|9=>0xe0c0828a0e38302022838e0c0828a0e9498e0c0828a
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|4,0=>0x4aa8905116a219440a87c50eea1c9436a86850c6a17942ca854509ea129422a8405076a0d9418a82c504ea08940ea8185026a039404a8045
|5,0=>0x424c831903320063f4c7d18f731e863c4c7718eb31d06394c7118df31b86364c6b18d331a06334c6518c731886304c5f18bb317062d4c5918af315862a4c5318a331415276c4d5897b1296246c47588bb1116216c41587fb0f961e6c3b5873b0e161b6c355867b0c96186c2f585c28b26158c299850309a6
|5,1=>0x28f6512ca0d93eb27854e4c9b1933326064b4c95192732486484c8f191b32306454c89190f32186
|6,0=>0x2183c297846d071e0abc0e7810d005dfd3bf377dacf99defbbd877a2ef29de233bd776ecec1dd4bba27736ee559c7b3887702eded9bab36e76ceed81dacbb536698ed15d9f3b377660eca9991bb1d662cec41984bb0275f6ebd1d76bae675beeb61d68bacb6588eaf5d5b3aaf7550ea8994dba956
|7,0=>0x246b48678fef1e1e39346c68caf17da2cb4527896f111e1f34377
|8,0=>0x4936
|_,_=>0
def wAt:=mkWire dB 92 96 0xffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 15
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 8 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1c0b0c1e261d1c190449141d0c4a141d1c4a141d041d0a291c1e0c1d06171c1d021e0a29141d0a29141d04050a6e26488e1f0a29041d021e0a290617141d06041c1d0a290a29141d0a29141d141e1c4a262b0a291c1e261f1c0b121c021e044906291c1d0a291c0b262b121c1c1d141d121d141d1c291c190a29261c121d2648
|1=>0x1c19141e1c290a29741d1c0b261e1c19062b1c1d1c0b0a29041d1c190a2926291c19261f1c191c291c19522b041d021d0a291cf9141e141d1c1e1c190c1e1c1d1c1906171c1d1cdd0c1e261c1c19121c1c291c0b141e04dd0c1e1c410c1d0c4a141d1c1d0a291c0b0a29141d1c420c1d141e141d041d1c19141d1c1d261c1c19
|2=>0xa291c1e1c190c1e041d1c19141d1c1a04290c1d1c291c1d1c0b141e262b1c19261e1c1904f9141e14951c1e141d1c0b121f1c2904050a290449141d1c050a291c49141d14e91c0b261f1c191c1d141d1c1d121e1c29
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x11000001000000000000000000000000000
|5,0=>0x2322210002111f21e10000000000001d11b21a10000000000001910001810001621511411310001211110000001010000e20000c20000000000000b10000000a1000000000000000000000082000000071000061000033000000000000021
|5,1=>0x2a2000000291281000262000000000000000000000000000000000251000
|6,0=>0x9b29929729529329128f28d28b28928728528328218027e27c20007a27827627510007327126f26d26b26926726526326125f25d25b25925725525325124f24d24b24a14824714524324214023e23c23a23823623513323213022e22c2
|7,0=>0xaa1a91a81a71a61a51a41a31a21a11a019f19e19d1
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 12
def pmP:Nat→Nat
|0=>0xb380540026e0135009a004c4026001100081004000140007400390019000c200500020000d4006800330019000c400600020000a000400010000400018000800020000
|1=>0x420890260517321311018862ee317310ba8859c33ee137709a9845dc22ce1163089b84484208410400802025dc12ce08830433820800800020200bb805d402e60170
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x80080000000000000
|5,0=>0xa0001608054014000000000000008000818094118000000610600000018008010218200f08002400301700000018001600000500001e000080180500000006
|6,0=>0x509e0bb49d7bf4cc19787260a80b892840328936e2f3e29065c68e761b2f31183160d63a8106ab2b348b1205999a7
|7,0=>0xa778f6e62da3d368f7c76
|8,0=>0x1f
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 17 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_93 7 roots_93 ops++addP pm 1 dom_86 5 roots_86 ops++addP pm 2 dom_87 6 roots_87 ops++addP pm 3 dzo_89_4 5 roots_89 ops++addP pm 4 dzo_75_4 5 roots_75 ops++addP pm 5 dom_91 7 roots_91 ops++addP pm 6 dom_94 6 roots_94 ops++addP pm 7 dom_89 5 roots_89 ops++addP pm 8 dom_75 5 roots_75 ops++addP pm 9 dom_90 5 roots_90 ops++addP pm 10 dom_83 5 roots_83 ops++addP pm 11 dom_92 4 roots_92 ops++addP pm 12 dzo_91_4 6 roots_91 ops++addP pm 13 dom_31 5 roots_31 ops++addP pm 14 dom_27 4 roots_27 ops++addP pm 15 dom_73 4 roots_73 ops++addP pm 16 dom_29 4 roots_29 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_95 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_zo_89_4_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_zo_75_4_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_92 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_91_4_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_29 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_93 7 s (0,roots_93.map (·&&&dom_93)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_95 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_93 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_95 gM v ys):RunD true dom_95 gM v (ori ys):=h
def Z (s:Nat):=barP dom_95 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 30 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 30 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 85 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 85 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 62 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 62 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 14 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 14 0 = true)
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
theorem lowS_119:Lower true dom_119 roots_119 goal_119 8:=lower_slice_b [(0xf000f000f000f000f000f000f000f0,16,20)] (by decide +kernel) lowS_115
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
|0,0=>0xf0f0f0f0f0f00000f0f0f0f0f0f0000f0f0f0f0f0f0f0f0f0f0f0f00000000f0f0f000f0f0f000f0f0f000f0f0f0000000000f0f0f0f000000000f0e0f0ee0e0e0e0e0e0e0e0e0e0e0e0e0e0e0ef0f00000f0f00000f0f00000f0f0000f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0ef0f0f0f0f0f0f0f0f000f000f000f00f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0000c0f00000c0f00000c0e00000c0ef0f0f0f000000000f0f0f0f00000000f000f000f000f000f000f000f000f00c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0000f0f00000f0f00000f0f00000e0ef0f0f0f0f0f0f0f0000000000000000
|0,1=>0xa0f0a0f0a0f0a0f0a0e0a0e0a0e0a0ef0f0f0f0f0f0f0f0f0f00000f0f00005050505050505050505000005050000f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c5050505050505050404040404040404f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0af0f0f0f0f0f0a0a0f0f0f0f0f0f0a0a0030003000300030002000200020002005000500050005000400040004000400f000f000f000f000c000c000c000cf0f0f0f0f0f0f0f0c0c0c0c0c0c0c0cf0f000f0f0f000f0f0f000c0f0f000cf0f0f0f0a0a0a0a0f0f0f0f0a0a0a0af0f0f0f0f0f0f0f0f0f0f000f0f0f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a
|0,2=>0xf0f0f0f0f0f0f0f0f0f0a0a0f0f0a0af0f0f0f0f0f0f0f0e0e0e0e0e0e0e0e30303030303030303030000030300003030303030303030303030302020202f0f0f0f0f0f0f0f0f0f0f0f0f0f0000f000f0f0f000f0f0f000f0c0f000f0c303030303030303030303000303030000f000f000f000f000f000f000a000af0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c00f000f000f000f000f0000000f0000f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a0000000000000000f0f0f0f0f0f0f003030303030303030303030303030000f0f0f0f0f0f0f0f0f0c0f0c0f0c0f0c00000000f0f0f0f000000000f0c0f0c00f000f000f000f000f000c000f000c
|0,3=>0xf0f00000f0f00000f0f00000000f0f0f0f0f000f000f0f0f0f0f000f00f0f0f0f0f0f0f0f0f0f0f0f0f000f00f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c
|_,_=>0
def sP:Nat→Nat
|0=>0x1c52840a300529c10b1c02a21030a10052840c280014a1037c201314a10374014a70409b01914a1031c014a1030980052840c25c01542840c200f4ca1031c04452840c20052892030803ce3480c22840c230014a2480c71440c21801440c2040
|1=>0xe14d2840c200f38a10308014a12e54308014a1030ad00f14a1031c20052840c2b00ac53440c20052aa10308014a1030a900529c2031c214a0c70a80059de11508a1150c28403c51030a602514a10b0c09052840c201938a10308014a2042c3
|2=>0x52840c20052840c203214a1030803c52840c200e14a1030806452840c20052840c2cc03d32840c203114a10308014a4080c20303852840c200578a1150c238568a10308014a8840c2005bca1031c2005284b831c2
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x18609303180cc006
|6,0=>0x349d96ec475ebad9d5eea96513a6dd28e8d74339fdcf2c72735b991cbae56727b921c82e3a719b8b1c4ae1e7
|7,0=>0xa4bd09e76f34796bc9623cf16887bc1e1ff0f78783ba21c2ed98
|8,0=>0xb2b579eaef507
|9,0=>0x16b6
|_,_=>0
def wAt:=mkWire dB 52 124 0xfffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1004729080470d0804a11140452914055090c05e0f2804a150804f0114a552b100440d08044961c54a0d0c04a011629511784ca0138245011405a1508a4309080440108342012034401782ca01542c3010805a1508a4a59544c509080521520a440140342111404529100442d0c24401
|1=>0x1054a151405a1508a4e2b1404509285720110544011024e0d1404301280450108a480d
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x3300000c00000
|6,0=>0x1792e1000acd49263484889010003a668c001822c4000001422443cc000001a42c849063
|7,0=>0x9e534a594928e514a194127e4f49d93926e4d4999312
|8,0=>0x14c690d11
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0x108640420004104946401051d30341f4c0847d3021074c0840d70121f4c0305f3003575c008400001c64000080300010080004000000c000001d3000070c00010000003280000c500002400000840000100000022000008400001100000380000020000004000000
|1=>0x20a0140406084ca091d7202471c700081
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x3004000
|6,0=>0x4500050533073c01120061c0007089000308504
|7,0=>0x89985b8e475e5a07cb61f70a
|8,0=>0x35755a
|9,0=>0xe
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 26 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_122 7 roots_122 ops++addP pm 1 dom_115 7 roots_115 ops++addP pm 2 dom_75 5 roots_75 ops++addP pm 3 dom_99 5 roots_99 ops++addP pm 4 dom_59 7 roots_59 ops++addP pm 5 dom_113 5 roots_113 ops++addP pm 6 dom_91 7 roots_91 ops++addP pm 7 dom_107 7 roots_107 ops++addP pm 8 dom_121 7 roots_121 ops++addP pm 9 dom_82 4 roots_82 ops++addP pm 10 dom_81 4 roots_81 ops++addP pm 11 dom_120 5 roots_120 ops++addP pm 12 dom_104 4 roots_104 ops++addP pm 13 dom_105 5 roots_105 ops++addP pm 14 dom_73 4 roots_73 ops++addP pm 15 dom_98 4 roots_98 ops++addP pm 16 dom_51 4 roots_51 ops++addP pm 17 dom_57 4 roots_57 ops++addP pm 18 dom_83 5 roots_83 ops++addP pm 19 dom_27 4 roots_27 ops++addP pm 20 dom_43 4 roots_43 ops++addP pm 21 dom_106 5 roots_106 ops++addP pm 22 dom_58 4 roots_58 ops++addP pm 23 dom_90 5 roots_90 ops++addP pm 24 dom_114 5 roots_114 ops++addP pm 25 dom_89 5 roots_89 ops
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
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_120 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_104 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_98 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_89 _ g hchk
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
def dzo_73_4:=0x30300000000000003030
def gzo_73_4:=0x30200000000000002000
def gsh_73_4:=0x3020000000000000200
theorem lowS_zo_73_4_73:Lower true dzo_73_4 roots_73 gzo_73_4 4:=lower_iso_b (d1:=dom_73) (r1:=roots_73) (T1:=gsh_73_4) [(dom_73,4)] (by decide +kernel) (lower_slice_b (T:=gsh_73_4) [] (by decide +kernel) lowS_73)
def dzo_105_4:=0x3030000030300000303000003030
def gzo_105_4:=0x3030000030200000303000002000
def gsh_105_4:=0x303000003020000030300000200
theorem lowS_zo_105_4_73:Lower true dzo_105_4 roots_105 gzo_105_4 5:=lower_iso_b (d1:=dom_105) (r1:=roots_105) (T1:=gsh_105_4) [(dom_105,4)] (by decide +kernel) (lower_slice_b (T:=gsh_105_4) [(0x303000000000000030300000000,0,32)] (by decide +kernel) lowS_73)
def dzo_121_4:=0x30303030303030303030303030303030
def gzo_121_4:=0x30303030303030203030303030302000
def gsh_121_4:=0x3030303030303020303030303030200
theorem lowS_zo_121_4_73:Lower true dzo_121_4 roots_121 gzo_121_4 6:=lower_iso_b (d1:=dom_121) (r1:=roots_121) (T1:=gsh_121_4) [(dom_121,4)] (by decide +kernel) (lower_slice_b (T:=gsh_121_4) [(0x3030000030300000303000003030000,0,16),(0x3030303000000000303030300000000,0,32)] (by decide +kernel) lowS_73)
namespace S_125
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(4,20),(4,36),(5,13),(5,21),(5,37),(5,69),(8,9),(8,40),(8,72),(12,13),(12,28),(12,44),(12,76),(16,17),(16,20),(16,80),(24,25),(24,28),(24,56),(24,88),(32,36),(32,40),(32,96),(33,37),(33,41),(33,49),(33,97),(48,49),(48,52),(48,56),(48,112),(64,65),(64,72),(64,80),(64,96),(68,69),(68,76),(68,84),(68,100)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_125.map (·&&&dom_125)
def gM:=goal_125&&&dom_125
def NN:Nat→Nat
|4=>11
|5=>96
|6=>286
|7=>130
|8=>18
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xf185aaf7d38aa1c879626b5656b0653ab253686b3605716aab115db
|5,0=>0xf2783d4ac6c5f30c5ec4c38f0bfe1db8bb8b46e7b4516b1813a9685a3278a203e9b426969c194e868fdb68e11d8af5e8a7ab87ae4845ea81d1e817b77fc7b7c9c27c4887bb0f7a33d7186370de96e1a561eff5d03f5c9995b2bb5a7d0592e958f77570ba54f275476453afe528f0507024ecc04ec274be844be0249ff549acd48a354625245eda4597b44dc941d983fa943d1ba3c3fe39a63376c73751a37093323c330ad62f07b2da992a72029d72255e8246b82419022de6229a81f35d1dbec1d2d01bbb01778416649155fe1529713d4d1270f1110b10a840d2040c14c09f76090640872308031043de03aa403938
|6,0=>0x4b9484b4e04a204495d5493d74907c48ee747d85479554768f46923464f8449c643d2041ca441a804120741050409c03fc0c3d4113d1ba3c50d3baa23ab3938ef2384f736f2836a88369e03617c35d323421b32fe132faa325f8317e93147230bc1300362f9bf2f4d52b8502ae642a14d29e2129d722973328ce628b9c283a627b8f277ac26f00264b325ba8254772516c24d8923865236362337c22cb32198d20804201d11ff9e1f2221ebf31e4181d39c1d37f1d0351c6e21b97a1b3c319d7219c5d1911b1816817551173001602d15c7b1486c14377132f8131601270f11d0f0ec740e92a0e0f00def10ddd80d9060d2380cd970ccd90c7770bf980a8ca0a4940a3d00a2b40993f091be087c50869b079bc07224069e7060b705cae05b1b04abe044c10401c03f1f03e450301002582020d501d3501a5b018e50138b011c5
|6,1=>0xb7a2fb70b2b684fb65a5b560ab2c33b232ab0388af2e4ae9feae93aae615ab96aaa6fea9894a7572a6adea598aa49109c6b09be1d98f7e9799896b62961dc95ae19386a92b2a9081a8fd468f7b08ef918d28e8d2228b8df8a7c48a7018a17c888aa87cb98717b84e218462d82d9482c7a827de8226f81fce81d58818f3816d88163180c0b806ef7f7e77e0ed7df7c7d20a7b6177b0037ab437a33d75e3c75aa373d7072cf2724fa724eb7125d711e5709e370958708107000c6e3736d83c6cede6ceb76c1646c15e6b5e56acb86a23969dd769708696146939c68bc6681ba6733a6657f64b7763a4a6329f62e056243c61eff6165860c44609885f9e85ee485e05d5db805d4145d1045c3c55c2145c1ed5b2ce5aecc59d375629c5601355f1f557bc541ba53ca553b8153afe51d48518874f9b04e14b4da4a4cc4e4cbb94bf3e
|6,2=>0xf5658f46b0f1d3be7088e5e0fdc9efdc6fed9baad76d8d34aacf4d4cd5f8cb73ccaec1caca6ca86fc9e96c9d35c9848c7ebbc65cec50eac1c05c06e2bf8eabeb4bbd7a4ba5ebb8fbcb7a44
|7,0=>0xf5520de26bdb0cfd8387c500dc19e3bfefebfe42bc204b8fbcb1d7fb00d9af1e4ad7dcab9d8aa6fea446ca394496df894a88910a28ccae8bb348b8df863d48624985ea985cb0847d87ee7e7ba9f7846077492768797140d6cce86ab4769d286926e689bd664ec65e0565b1863f2a62a2b616cc5e2505dcc65d3c55c3445ab7e59232570a456c2d566ce55b215545f551915465d53cd851b9a517e64ae8148f5748c6947f7147a4d4583b430ba42a26421c24169b413a63dc6539c4b399bd3984938a13383793331331df93129b303332bbdc2afe42ab022a360292e028f8128c9e25576240df23d8a23967239612357222f75225ac2250e22110200351e6fc1dae01beca1bd1d1a7de1a41316f771670d122e711e831099d0e4b00e0f30d8560bf98092a1091be07f25079680528b04e7703cbc0377402d7001a5b0042f0004d
|7,1=>0xf9c09f72bd
|8,0=>0xcb8e6c68b0c4051b382ab25508e2267f2e4789cf7749274b3a6951e4af0c4624f33280228b5213f11bbc00f7ba
|9,0=>0x7f2e4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcccccccccccccccccccccccc000000033333333222222223300330022002200cccccccc88888888cccccccc8888888b3330000333300003333000033330000cc88cc88cc88cc88cc88cc88000000033333333333333333030303030303030cccccccc00000000cccccccc000000033333333333322223333330033332200cccccccc88888888cccc0000888800033003300330033003300330033003300cccccccccccccccc888888888888888b3333333333300003333333333330000cccccc0088888800cccccc00888888033223322332233223322332233223322c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c33333333333333330000000000000000
|0,1=>0xcc00cc00cc00cc00cc00cc0000008b3333333330033003333333333003300cccccccccc88cc88cccccccccc88cc8b33333333333333333330000333300004444440044444400444444004444440330033003300330033003300220022008888888888888888888888888888888b3332222333322223333222233332222cccccccccccccccccc00cc00cc00cc033333300333333002222220022222200ccccccccccccccccc8c0c8c0c8c0c8c00000000000000001122112211221122cccccc00cccccc00cccccc00cccccc0332233223322332233220000332200000000000000000000cc88cc88cc88cc891221122112211221122112211221122
|0,2=>0xcc88cc88cc88cc88cc88cc88cc00cc033333300333333003333330000000000880088008800880088008800880088033333333333333331122112211221122444444444444444444444444000000000330033000000330033003300000022cccc4444cccc4444cccc4444000000000000000332233220000000033223322cccccccccccccccc88008800880088033331100333311003333110033331100444444444444444444440000444400033333333333333330010001000100010000000008888888800000000888888880000000313131310000000031303130ccccccccccccccccc0c0c0c0c8c8c8c80003333000033330000330000003300
|0,3=>0x888888888888888888880000888888030303030303030303030303030323032000000004444000000cc000044cc00022222222222222222222220022222200cc00cc00cc00cc00cc00cc00cc0088033333333333333330000330000003300cccc0000cccc0000cccccc00cccccc022332233223322332233223322222222008800880088008800880088008800880000000000000002222332222223322c0c0c4c4c0c0c4c4c0c0c4c0c0c0c4c33333333333333003333333333333300444444444444444444444400444444000330033002200220033003300220022cccccc88cccccc88cccccc88cccccc8b3003300332233223300330033223322
|0,4=>0x88888888cc88cc8888888888cc88cc880000000000000003333333333333322cccccccccc00cc00cccccccc88008800022002200220022112211221122112244004400440044004400440044004403333333333333333332233223322332244cc44cc44cc44cc44884488448844880000000333333330000000033323332ccccccccccccccccc0c0c0c0404040400000000000000000000000033223322c8c0c8c0c8c0c8c0c8c0ccc0c8c0ccc33333333333333333333330033333300cccccc00cccccc00cccc8800cccc88000330033003300330033003300330022cccccccccccccccc8c008c008c008c033333333333333333030313030303130
|0,5=>0xcccccccc00008888cccccccc000088880000000000000002222222233223322cccccccccc44cc44c0c0c0c0c040c0433333333000000003333333333223322cccccccccccccc8800000000000000033003300330033003300220033002200cccccccccccccc00cccccccc88888803333333300220022333333330022002200cc00cc00cc00cc00cc00cc0088008b333333033333330323232303232323088880000888888888888000088888800000222233003322000022223300332200cc00cc00cc00cc00cc00cc000000000000000000000003333333333223322cccc8800cccc8800cccc8c00cccc8c000000000330033000000000033003300
|0,6=>0xcccccccccccccccc0000cccc0000888a2222222222222222200220022002200c4c4c4c4c4c4c4c4c4c0c4c0c4c0c4c30303030303230323030303030323032888888888888888888888888000000000003333000033330000332200003322cccccccccccccccccccccccc8888888b333333333003322333333333300332240c040c040c040c040c040c040c040c3333333333333333103010301030103000000000cccccccc000000008888888b3330000333333333333000033332222ccc8ccc8ccc8ccc8ccc8ccc8ccc8ccc800000000000000033323332333233320000cc880000cc880000cc880000cc880002222000022220000222200002222
|0,7=>0x44cc44cc44cc44cc40c040c040c040c22002200220022002200220022222222cccccccccccccccc00000000888888880220022002200220222022202220222000000000000000088888888008800880000000000033330000000000003300cccccccccccccccccccccccccccc0000000000033333333000000003333000088888888cccccccc88888888cccc888b3333333111111113333333311110000c0ccc0ccc0ccc0cc808880888088808a2222222222222223322332233223322cccccccccccccc88cccccccccccccc880000000000000000000330000003300c0c0c0c0c0c0c0c0c0c000c0c0c000c30303333303033333030333030303330
|0,8=>0xcccc0c00cccc0c00cccc0c00cccc0c03300332233003322330033223300332200000000000000000c080c080c080c0b33333331111111130303030101010100000000000000000888888888888888911111111111111111001100110011000000000000000000008800880088008b3113311331133113010301030103010004400440044004400400040004000400110011001100110011001100000000cccccccccccc8888cccccccccccc888b300330033003300220022002200220000cc000000cc000044cc000044cc00002020202020202020202020202020202cccccccccccccccc080808080808080b3333333222222223333333322002200
|0,9=>0xc0c00000c0c00000c0c000c0c0c000c33003300333333333300330033223322cc004400cc004400cc004400cc004403333333333333333333033303330333000000000cccccccc00000000ccc0ccc00003333000033330000222200002222cccccccccccccccc0c0c0c0c0c0c00033330000333333333333000033333300cc88cc88cc88cc88c080c080c080c083333333333333333111111001111110088888888cccccccc88888888cc88cc8b3333333333333333333332233333322cccccccccccccccccc08cc08cc08cc080000000000000000000000022222222cccccccccccccccc44004400440044003000300030003000300030003000300
|0,10=>0xcc00cc000000000088008b3333333000000003333333333333300000088880000cc88000088880000cc8b3113311331133113311331100000000cc44cc44cc44cc44cc40cc40cc40cc433332200333322003333220033332200cccccccc44444444cccccccc4400440323232323232323232323232323232320000888800008888cc00cc88cc00cc8911111111111110011111111111111000c0c0c0c0c0c00000c0c0c0c0c0c00033003300330033003322332233223322404040404040404040c040c040c040c30303030303030303030333030303330cccccccccccccccc00000000cc88cc880000000000000000000333300002222
|0,11=>0xcc000000cc000000880000008b30033003300330033333333332233228888cccc8888cccc8888cccc888888880000000000000003300330033003300c0c0c0c0c0c00000c0c0c0c0c0c000033333333333333333030303030300000000044000000440000004400000044000002222000022220000332200003322cccccccccccccccc88888888008800880330033000000001133113300000000cccc0000cccccc88cccc0000cccccc8b0303030303030303030303032323232ccccccccccccccccccc8ccc8ccc8ccc83030303030303030302030203020302444444444444444444404440444044433332222333322223333220033332200
|0,12=>0xcc00cc00cc00cc00c000c000c000c0033223322332233223222322232223222cccccccccccccccc008800880088008b33300003333000033331100333311008c8c8c8c8c8c8c8c8c888c888c888c8b31133113311331133113311330033000000cc000000cc000000cc000000cc000000000000000001111110011111100cccccccccccccccccccc4400cccc44030303030101010103030303010101010c0c0c0c0c8c8c8c8c0c0c0c0c8c8c8cb3333333333333333333222233332222888888880088008888888888008800880000000333333000000000033333300cccccccc00000000cccccccc8888888b3333333003300333333333300220022
|0,13=>0xcccccccccccccccccccc0000cccccc033003300330033003300330033223322888888880000000088888888008800880000000333333220000000033333322cccc4444cccc4444cc004400cc0044000000000000000003333333333332222cccc8888cccc8888cccccc88cccccc880003333000033330000333300002222444444444444444444444444444400000330033003300330022002200220022cc88cc88cc88cc88cc888888cc88888b3330000333333003333000033333300cc08cc08cc08cc08cc08cc08cc08cc0b03030303030303033323332333233320000000000000000cc08cc08cc08cc0b3333333111111113300330011001100
|0,14=>0x88008800880088008c008c008c008c0003300330033003300330000003300000000000000000000cccccc00cccccc022222222222222222222222222002200cccccccccccccccccccccccccc00cc000000000000000000000000000220022cccc00cccccc0088cccc00cccccc008a2223322222233222222332222223322444444444444444444444444440044000000000000000003333333322222222cccccccccccccccc00000000cc00cc033333333333333332222222233223322c8c8c8c8c8c8c8c8c8c0c8c0c8c0c8c00000000003300330000000000330000cccc4444cccc4444cccc4444cccc00000000000000000003300330033223322
|0,15=>0x8888888888888888808080808080808113311331133113300000000000000000c0c0c0c0c0c0c0c08080808080808083020302030203020302030203020302cccccccccccccccc0c080c080c080c080000000000033220000000000003322cccccccccccccccc000088880000888b333333333333333000011000000110088888888cccccc8888888888cccccc880000000333333330000000033332222000000cc00000088000000cc000000880000000111111110000000011110000cccccccccccccccccccccccccccc88891330000113300001133000011330000cccccccccccccccc8888cc888888cc891111111111111111010101010101010
|1,0=>0x33333030333330303333303033333030cccccccccccccccc0c000c000c000c0000033330000333300003333000000008c888c888c888c888c888c888c888c8b1313131000000003131313100000000cc00cc00cc00cc00cc000000cc0000033333333333333333232323232323232c8c0c8c0c8c0c8c0c8c0c8c0c8c0c8c333033303330333033303330333033300000cccc000088880000cccc000088880000000000000003030303030303030c0c000c0c0c000c0c0c000c0c0c000c22222222222222220022002200220022
|_,_=>0
def sP:Nat→Nat
|0=>0x814120c010044e0913018022500024180200858000906018141912024181103028460c0300432220003c120c0308432090600802051002418010c87c001d078300c0a0c824380605064360f04830340a0c824180a0805012180b8042c09060082a1404830040a0a024261200814120c08828200f060081c01068301606050241006008140807030040a04018080200
|1=>0xe01814190203034010c800120c0880420000483002381b800120c030286c19048300c350c800680f0605c0219048300c0119800120c0086c6400048c4181700814120c0b8043216048306017008141a0c178180200048b8181700864120c0100458000f0302e010c8ac120c008645400020a40c010c800120c0b8040a280484c24010c8001218030042c000f0341817
|2=>0xc80012440600802050490c0c010c800120c0086484000683c18020b804120c01004280004830161700864120c0302882190682418110302812310e0180205048700c010c858120c010544e09060188019000241802088285a09060081427048300c011f800120c030f832000481802191e800120c0300478000483076010c8001203060080200048300401028e81239
|3=>0x18180219000241801160400052048300c0a0c824261c050649604068700c0102824a206050640009060480c0a0c8101a130100400090605c024f02824181103028324e048300c010c934181700864120c01004980004830041700814120c010049200020b80c010c800120c010044e14060180219240001e09060188e1904910300600814120c030283246048300c45
|4=>0x20240c010c984005f078300c010c800120c2500420000483004110089c12130e0081419048300c0a2f064120c0317432002e024180605064120c008402800048300c010c96c12132d00432002c8300c010c800b00f0601814190483014100003c120c05064ae090600814100002418062b0640009061280401138241806009540004030043254000341801298dc0004
|5=>0x1cc120c030043200048300c710c800120c031c032000782418020b8043209060180219378001213060081419000241802009b8000906018da010c800120c031b03200068300c01358001a0906004325700024180600864d400348241802030040009220600c010c800d0090601802190002418060c9980009320300c010c800120c250180219000241862030043200
|6=>0x2418020089c1206008650600048302e06008650280048300c010c800120c03028327f00024180600864fc00048300c210c800120c03028327c000241802088045a00048300c010c9ec000906008022700024180600864f400048300417008640009098600c0a0c800f209098180219000241806009dc32003b02418060086400090601802193a800120c3a0180219
|7=>0x8648c0007824260c0b804320909830021948800128f030040a1900024188e030283200048300c010ca34000906019181900034180600864a600048300c0127a2c0004049100c010c800121306004328a001a4120c0b818021906824180600a2400090601814880c800120c0300432870002418020b8180205048300c010ca180085048300c01028001a09060440c01
|8=>0x242618030040a00048302e9d00864000c03004329b00024180600864ae00048302e0127864000909818021930800080903004329a0002418060ca6400094c0300c010c800080f0605c0c010c824260c010040a00048300c014b86400090601802194b000d20906068021900024180600a54320004a5018060086400090624c0c010c8001e090601802193e8241806
|9=>0x5482418060086400090601950014500008090980802190002418a7030043200048300c010ca9800090e0300c0a0c9c8120c0101832a5002141e0c0300432000483148170086400090601832a3000101a1c0300432001a03418060086400090e0300ca20c800120c0300432a1000241806008cc000906018021950000120c0327c32000f03c181700864120c4f0180219
|10=>0x901802190002560060086400090600432531b800120c0300432af000241806070043200570241806008640009148300c010c800120c0300432ad000241806008f00009060080c0a11800080600864c0500002418ac0300432000483156060086400090601814191900012aa0302832000484c1817008143258048300c0a0c80012440e0300c0a0c824181700864c200
|11=>0x864f000048300cba0c800120c0302832b90002418060086570000487018063886400090601802195b800a40906018021900024260c0300478000601802195b0000809470180219000256a0c0300432000484c38010c92c000906018141943800120c032d03200048300c050ca940009062cc0c010c800120c0300432b200024301c03028320906018021958800120c
|12=>0xc800121306128021900024180203004fa000484c380600814320962070180605064120c0302832c30002418170086584000f30418060086400c0048300c010c800120c0300432bf000241811030040a19048300c0a4b8640009060180205190017c0906018021900160120c030040a00048300cba0c82486060086400090601802bd0c800120c5e0043261000242606
|13=>0x48300cce05064000f0483002192b800120c0b8180219668241802008400009660300c010c8001a0906018143700024260c3a0043200049101806008cc000909b100c010c800120c0300596190002418ca03004320004830041700814120c010040ac900024260c008646400048300c010cb200009638300c010c800120c0302832280002418062386400090605c0cc5
|14=>0x86464000483004110302832090634c2e010c800120c0b8180233001601e0c03004320004831a4060086400090605c0c010c9f4120c00840000c0b81802194d8001213060043253000241817030040a23048c41806050640009098602e010c800120c5581814190002418300302832000484c04010c9840009063440c010c800120c0b8040a19280241806680043200
|15=>0x6e000120c0336c0219000241806008143220048701806008f000da048300c010c800121c0300432c200024261c0302832096c8300c010c800120c010285a00048311c17008640085048700c010c800120c0881814010c824180600865b000608241802030040009060440c0a0c824180600865ae00048300219483580009063540c010c80012186a01802190003c1806
|16=>0x601814191b824180208818020504831c0060086400090987004010c800120c03004bc19000241806008644e096f8300c010c800120c6f018021900024620c030040a000483060060081400090986178010c800b809060180219000245c0c030043200048302e06008f0001e06018021915800120c0300432dd000741806008645000020242617008640009060180219
|17=>0x76001820f06018021900024180600865d400048300406050640009748300c010c800120c03005d00500024180600865ce0007824180203028320d0484c1802008003ce60601802190002418060081432e5048300c0172064000906019c61900024180203004ca00048300c010cb880009060080c0149000120c25018022300025c20c030043200048302e010ca101e09
|18=>0x2418060a8644e090605c021914000120c030047019000241806050644e096a0302e010c800124406004324b00024880c03004320004818141979000120c03005e21900010181700864a000048300c0a7786400090601802192a000120c0305432000480c18060086400090601802050cbb812ed0600802190002418170086572000e8241806008140009060180219
|19=>0x6018028b00010120600865f200020700c010c94000090605c02050c92c120c03064fe0004830144b1b800120c08818022300024180600865f000048309402008b4001d078300c010c800080c03004322b0001012ed0300432000f02418170081432090601802f70c800120c0300432f600024184a088180219048300c010cbd400090601802197a001e609060180219
|20=>0x30043200048603806008640009060082e010c800120c010180223000241874030043200048300c010ca2ca000068241802030043200048300c010c8c800090e0300c010c940000955018021900160120c030043200048300c0a0c88c0009061280c010c80012440605c0c010c800120c01018028b000101a13030043200048300c010cbec00090601802197d0003a09
|21=>0x300432001a024180600864000406018021928000120c318080c010c80012130605c021900024180600814460006824180600814320006824260c030043200048300c010cc00000906018021966800120c0300432b900024180605065fe00048302e06008644600048300cc50c800120c0300432fe048300c010c94c0009061280c010286400090601802197e800128f
|22=>0x52800120c18018021900034120c030046e00048c418020300432001a024260c0300432000f0241806008143200048300c010c8a0000906018021978000120c030040a1948000120c318180219000781a0c030043200048300c010cb0c00096a0300c010c800120c032ec3200048300d010c800120c01018021914000120c03004327d00010121c03004320004b10380c
|23=>0x3c120c030043292000241806008660600048300401168001a09060080c010003c121806018021900024621306018021900024261c030043200048300c010ca240009060080d020c8001a0906018141900024180600814324b0002418110300432006082418060086400090983178010c800123106018021900024189c030043200048300411030043200048300c19
|24=>0x7e000120c03004326028000120c0341802050c8000809060080c010c800120c0302832f00002418020300432fc00024180600864ca00048300c010ca480069068241806008640009098300d020c8001e090601802191b8001a090605c0c010c800120c034143200048300c0a0c98000090605c021928000120c8201802050c8003c0906018141900034121c060180219
|25=>0x1e4120c030043200048300c010c89c00090601802197c800120600865e400048300c010c9b80079078241806008640004048300c01028640009060080c010c800180684004320002034180600864000f048300406008640009768300c010c800120c0b818021930000120c03004322b00078120c03004328b000241806050649600048300d07008640009060180219
|26=>0x26180c0b81802190002418060086616000491018060086400090601802051b800120c03004330a00024180600c24320007824180605064120c0101814010c800120c010181419000241801258dc00090c0300c0102801d60906018021900024300c0300432500002418060093c3200048302e06008651200048300c010cb580009060180219138241802030040a19
|27=>0x3c120c0300432000202418060086400090601a0419000241904030043200048300c010c92c0009060180219300003c09060180219000241806008652000068241806008640009061280406008640009060181419168003c090c0300c010c801d6090605c0c010c800120c0b81802050c82418060c99c00090601802194d0001e090605c0c010c9a41e09060180219
|28=>0x120c030043200048300c010cb24000906018021945800120c03004322d000241806050043200048300c0a0c800120c030040a19000241806008640009860300c010c800120c010180219
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x32502d50285023501e50195014500f500a500550005
|5,0=>0x1ae61a861a2619c61966190618a6184617e61786172616c61666160615a6154614e61486142613d51376131612c51266120611a6114610e6108610260fc60f660f060ea60e460de60d860d260cc60c660c060ba60b460ae60a860a2609c60966090608a6084607e60795073606d60676061605b6055604f60496043603d60376
|5,1=>0x26c62666260625a6254624e62486242623c62366230622b5225621f62196213620d6207620161fb61f561ef61e961e361dd61d761d161cb61c561bf61ba51b46
|6,0=>0x41f74187411740a740373fc73f573ee73e773e073d973d363cc73c573be73b773b073a973a2739b7394738d7386737f737a5374636d7366735f73587352634b7344733d7337633073297322731b7314730d730672ff72f872f262ec62e572de72d772d162ca72c462be62b772b072a972a2729b7295628e72877280727972727
|6,1=>0x5d375cc75c665bf75b875b175aa75a4659d7596758f75896582757b7575656e7567756075597552754b7545653e7537753075297522751c6515750e7507750074f974f274eb74e474dd74d674cf74c874c174bb64b474ad74a6749f74996492748c6486647f74787471746b6464745d7456744f74496442743b7434742d74267
|6,2=>0x78a7783777c7775776e7767776077597752774d5746773f77387731772a7723771c7715770e7707770076f976f276eb76e566de76d776d076c976c276bb76b476ae66a776a076997692768b7685667e7677767076697662765b7654764d7646763f76387631762a7623761c76175611660a760375fc75f665ef75e875e175da7
|6,3=>0x943793c7935792e79286921791a7913790c790578fe78f778f078e978e278db78d478cd78c678bf78b878b178ab68a4789d7896788f78887882687b7874786d7866785f78596852784b7844783d7836782f78287821781a7813780c780577fe77f777f077e977e277db77d567ce77c867c177ba77b377ac77a5779f679877917
|6,4=>0xa107a097a0279fb79f479ed79e679e069da69d379cc79c579be79b779b079a979a2799b7994798d7986797f79796972796b7965695e79577950794a6
|7,0=>0xbdb8bd38bcc7bc57bbe7bb77baf8ba87ba17b9a7b937b8c7b848b7e6b777b707b688b608b588b517b4a7b428b3b7b347b2d7b267b206b1a6b128b0b7b047afc8af57aee7ae68adf7ad87ad08ac88ac17aba7ab37aac7aa48a9e6a986a917a898a827a7c6a757a6e7a677a607a588a508a497a418a3b6a347a2d7a267a1e8a177
|7,1=>0xdaa8da28d9b7d956d8e7d877d7f8d778d707d697d627d5b7d547d4e6d468d3f7d396d327d2b7d238d1c7d148d0d7d076cff8cf87cf17cea7ce46cdd7cd58ccd8cc67cc06cb97cb18caa7ca28c9b7c938c8c7c857c7e7c768c6e8c668c5f7c578c507c497c418c3a7c328c2a8c246c1d7c167c0e8c077bff8bf78bf07bea6be37
|7,2=>0xdb98db27
|8,0=>0xe357e2e7e277e207e1a6e137e0d6e067dff7df87df17deb6de47ddd7dd67dcf7dc87dc17
|9,0=>0xe3c6
|_,_=>0
def wAt:=mkWire dB 269 126 0x3fffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 9 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x801010b703065030640306503064258dd030660c81a048650c8010e008030650601904865030650c9410481a0c92d0c81a03001250b703065030640109f03065030640e01909801088b70306403065078080c819098650601909814060190089d03065168010306416801008010306503064060790300104819060090c81909814060190983c06019010b70306503064098140c80103001098140f06504819
|1=>0x3001050b7030640c94f0781b009f5118010486603064030651680103065030640205e030010c92d0c81a03001008010603d0c9e10e027048950e0670200903065009cb0e01a06001008810605e03001008010c819030650c85c030010c85e0f066048190486507864048013481b06801078650e01933801008b703064061950c80131803030650600a030650498106066258dd030660c81a258dd030660c81a
|2=>0xe0190687306001008830605e03001048010300104819031830606604a720085d030010c9410481a0c819060160c801020070483103001010280306509867060190ba09030014900107866048010601903001258010c81a062410300703181060660508f00801048660e019060010b86703001078650c85f030010102a030650c80103065048610c801060650100303065030651680103064062130301441001
|3=>0x6211030140c801060015d80102004048310c01a009cb0e01a220640980104a13030140318106066060a10c819060010102a0306500a49078660200704831010010600100801060650e00803065061b90c85c030010c8010685c048650300109803220640e0190480100801060b5030640c85e03001060190c8190e01a02007048610480106065032250c85f03001009bb0c85c0300109825009c90e01a22067
|4=>0x30661180103001258dd030660c81a04a720085d0781b048010600903065030010308d048660c8190c8010b88f030010cb3d050183481b078650c85f03001010b7030650306403066008015e065030030e0190c801030010c8190681b048650480a0c819630010088f048660088d04866010010c819008010484e06019048190c803030160c8010306501028030650681b04865048dd030665d8010200404831
|5=>0x8010681b0cb250601a008010c819060190486503065068030c801009b90c85c030140c801030660080101003030650c85c030010c01906065060650983c06019220640605d0c819060190300103001220640e019428030600109827060190600106019008010080103065030640318106066068310486501003030650c8030100303065060650481a0681b0486503065032090c80703001220670605d048dd
|6=>0x30010c803030657e001030650200a0306530001060660481a0c81a03001050b70080103064030660c81a00801060650306503064048090c819078670480109803060190c8010cb090982703065098360601907865048010089d16801030640480a0c819168010080103064061410481a0e01900801060b703064033c305067050b500801030640684c0e01b098030f065048190786604801758660c92d0c81a
|7=>0x6001048310e0650600102019060250481a060250306506019030010c80104866048650c80106019048650caf3030031b801030660c01a06065050640080103001048660088d0486616802030640781b04801030150c801008160c801062410081a0600106065030010c8190c819048660caf1030030c8030481a04865030650681b04865060010481a060b503064048dd03066008010486601001030650605d
|8=>0x4865030650306404865030650480106065098650601906019060010c85f0300100803030650486500801030670c801010030306504a2d0c803060190300306009030650085d03001010030306502007048310308d0486604865030660306509825060190c801048190480a0c8190506700801030070c801010050306504865048190c9430481a061410481a020040483100b270601a0480a0c8191180104866
|9=>0x6066060b7030640c85c0300107831048010c801048310306504a0b0086604865048310c8190980306019030010606607867048010c803048190c81a008010e0180600101007030650481a06066008150c80103065050670080103065048160c80107866048010680104865060190080303066048010486503001008b5030640080106066030010481a0c8010081900801048190486506001078660480106833
|10=>0x803008190c81a06066048190081a0486503065008010306406065048190485d03001030010c801008b703064060160c801030010480107865048010600503001480010081a0e01906001030660c80107833048010ca410081a0080104801030650080103065030660c81a0c801060650f00104819060650481a0c9410481a0c85f03001030160c80116801030640c801030650200104831168010306430001
|11=>0x601a0c8030306400801008010c80106005030650480104831
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0xacc283000025300000000904000000023100000000000203078800000001c206881640000000049000000000000000000000000000000000000000000000003cc00000000d202c80000000092018c00000000000000000014404100c400000840000000000000000000000020000000
|5,1=>0x10cc000000000000003f400003c300003a2000000000000000dcc000000035200003320c0c2e200000000000000
|6,0=>0xa42284c00027c89d226c899200009630000000250892224448f200008d222c8000220c86220cc8121fc80001f487b21e0c0001d880001ccc7121b8c6d11b046a21a08000000066218cc603000000017885b31684582154c53200005211444000138c4c200004a21208462
|6,1=>0xf423c88f023b88ed13ac8e9239c8e610000e330000e12378c0003744da336440000000d72000000035840000000d33000000000000000000d1233c80000000ce13344ca331ccc430000c3130480002fc8bd22e8cb7300000002d48b230000b022bc4ad22ac80002a840002a08a62
|6,2=>0x149251c946150cd4124fc80004f493a34e0936200013424cc40004c4930100012f14b492b24a49272490c000488920247c40000000000470c00046880000001182454d1324448000000110100010e243090a2000109141c90520001032400cfd300000003f04f933e040003d88000
|6,3=>0x6348000628d89162058710001852000183260857f35f857c200017a25dcd7615d440005cc8000000000000000005c496f25b4800000000005ac8000000169200016810001662590800000016315848000000160157895d1568d57300015435489502538800053454b20000000
|6,4=>0x1bb26e480006dc9b616d09b136b8c0006b45ab26a49a726949a41688800068459f200019d2668d982000195364c992100018f3
|7,0=>0x8e4a3728d4a3328c4a2f28b4a2b28a4a272894a232884a1f2874a1b28686182858a142848a102838a0c2828a082818a042808a0027f89fc27e89f827dc5f527cc9f127bc9ed27ac9e9279c9e5278c9e1277c9dd276c9d9275c9d5274c9d1273c9cd272c9c9271c9c5270c9c126fc9bd2
|7,1=>0xad0ab22ac0aae2ab0aaa2aa0aa62a90aa22a80a9e2a70a9a2a646972a54a932a44a8f2a34a8b2a24a872a14a832a04a7f29f4a7b29e4a7729d867429c8a7119bca6d29aca69299ca65298ca61297ca5e1970a5b1964a572954a532944a4f2934a4b2924a472914a432904a3f28f4a3b2
|7,2=>0xae06b62
|8,0=>0xb246c81b1c6c61b146c410002c31b086c11b006bf1af86bd1af06bb1ae86b91
|_,_=>0
def PO:=mkPO wAt oP oO 20 9 511 14
def pmP:Nat→Nat
|0=>0x10800008100004040002000000a000004580002080000c900004a800023c00011a000088000042000020800010000004800002200000c000003800001800000b000005000002000000c000004000001c00000c0000050000020000008000002000000
|1=>0x8020004000001800000a8600054200028800014080008000003af80018f0000c7000063000030000012200007be0003dd0001cf8000e740006be00035e0001ab8000c7c00062e00030c0001500000a6000050c0002840001410000a000004ae000215
|2=>0x1440000a00000480000221800110800082000040600020140010060008020004008001795000a828004f7c00273e00139a0009cb8004c7c00253e00128000090c000485c0024240012060008a1000423c00211600104e0008230004054002010001006
|3=>0x8b4e8044e7c02253a011297008922004485c021e6a010f15008788804083c02002a010002008000003885c01a72e00d39500614e8024e7c01253e00929700490b802083c01020a008101004046002001001000200425d00202f0010040008000003210
|4=>0x4410f8218af410352e08128404016a82004000c000004e21502700e01188f008803c04400002002d00c481005a72a02131f010842008411804208802100e01080300840000404aa020044010003006287c0302020180050099180047e7c023e2e011f15
|5=>0x20894a901eaf4808c3a40421d20155810000688000304000101509420a80a5451c52a28029512315e89088c044050820629d100101080000033842e18c217084282841001013b62a09d31704e98a8270c5412352a08e21504594a8228a5c11073e08829f
|6=>0x84c38ac020015400488a0024244335da206a4d10152e88039f40334ea004e6d00250480039f400140200091900040c46421d23000a111485484a42a41321d
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x3000000001500030003000000000300000e00033403000000000503000300000700000700000003130000030318000006000000000000000000000000001e0000030300000303000000000007111b0007000000000000030000
|6,0=>0x9031c1c3e0303033d009700081a00383b5e00000d000002000016000099000001350000940758050456326200031c759c000003040003b833660027000303000000011d001c090303006aae001c09111c00043f000a1c30037400043928000300315e05075f095d00005d420a00000c05389ac51c00110700151c00651c55
|6,1=>0xaa00671407070003001d38055d0300221f118a000300000000008f220500000047000003003e0013030000c73a000007095d5b98001603570100110100000041030305030300122e0309000307000309003e1c191c052f001c09070000008e00090000037603090000100003121c000f04030003777b00005a7861000900
|6,2=>0x32655d001c5905154600730303091c110900881c005d4503004503070017
|7,0=>0x26b18e4d64b7d0d291c444b071b5696b5163b64b7a87215143b3522b4f90b2364a86cf22bc0bb4256c7da849ab35ac689b2fd18023246e729284a35cafcb2fce5cbac22a81a2434ac8bfbda9406f2fcab9bb249dad53a6ce4ec078544c319693be8385c12cc626512d7f9f3ca14eb48da670958b507c48c9cd6051c8a089c38c
|7,1=>0x886d
|8,0=>0x7d2a51a6a4374ad382b49e79a77e29a570cc
|9,0=>0x20
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 25 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_121 7 roots_121 ops++addP pm 1 dom_124 6 roots_124 ops++addP pm 2 dom_61 7 roots_61 ops++addP pm 3 dom_108 5 roots_108 ops++addP pm 4 dom_109 7 roots_109 ops++addP pm 5 dom_73 4 roots_73 ops++addP pm 6 dom_60 4 roots_60 ops++addP pm 7 dom_85 5 roots_85 ops++addP pm 8 dom_120 5 roots_120 ops++addP pm 9 dom_93 7 roots_93 ops++addP pm 10 dom_104 4 roots_104 ops++addP pm 11 dom_81 4 roots_81 ops++addP pm 12 dom_117 6 roots_117 ops++addP pm 13 dzo_73_4 4 roots_73 ops++addP pm 14 dzo_105_4 5 roots_105 ops++addP pm 15 dzo_121_4 6 roots_121 ops++addP pm 16 dom_113 5 roots_113 ops++addP pm 17 dom_53 4 roots_53 ops++addP pm 18 dom_45 4 roots_45 ops++addP pm 19 dzo_89_4 5 roots_89 ops++addP pm 20 dom_57 4 roots_57 ops++addP pm 21 dom_29 4 roots_29 ops++addP pm 22 dom_101 4 roots_101 ops++addP pm 23 dom_92 4 roots_92 ops++addP pm 24 dom_105 5 roots_105 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_125 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_108 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_60 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_120 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_104 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_73_4_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_105_4_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_121_4_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_53 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_zo_89_4_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_29 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_101 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_92 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_105 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_121 7 s (0,roots_121.map (·&&&dom_121)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_125 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_121 h
def symsG:List (List (Nat×Nat)):=[[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_125==dom_125)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_125 gM v ys):RunD true dom_125 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_125 gM mpG SD SS NN hAt idxH ori 0 mkPools s
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
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_125 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_217_4:=0x30303030000000003030303000000000303030300000000030303030
def gzo_217_4:=0x30303030000000003030302000000000303030200000000030302000
def gsh_217_4:=0x3030303000000000303030200000000030303020000000003030200
theorem lowS_zo_217_4_201:Lower true dzo_217_4 roots_217 gzo_217_4 8:=lower_iso_b (d1:=dom_217) (r1:=roots_217) (T1:=gsh_217_4) [(dom_217,4)] (by decide +kernel) (lower_slice_b (T:=gsh_217_4) [(0x3030000000000000303000000000000030300000000000003030000,0,16)] (by decide +kernel) lowS_201)
namespace S_221
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(1,129),(4,20),(5,13),(5,21),(5,69),(5,133),(8,9),(8,72),(8,136),(12,13),(12,28),(12,76),(12,140),(16,17),(16,20),(16,80),(16,144),(24,25),(24,28),(24,88),(24,152),(64,65),(64,72),(64,80),(64,192),(68,69),(68,76),(68,84),(68,196),(128,129),(128,136),(128,144),(128,192),(132,133),(132,140),(132,148),(132,196)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_221.map (·&&&dom_221)
def gM:=goal_221&&&dom_221
def NN:Nat→Nat
|6=>4
|7=>4
|8=>1
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0xc6af1999462a6f01bca3
|7,0=>0xf134176be234f4b06f7c
|8,0=>0x125d8
|9,0=>0x7369e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x444444440000000044444444000000004444444400000000000000033333333000000003333333300000000333333330000000000000000cccccccc000000008888888800000000cccccccc000000008888888b3003300000000003300330000000000330033000000000033003300cccccccc00000000cccccccc00000000cccccccc000000008888888b3333333000000003333333300000000222222220000000022222222cccc000000000000cccc000000000000cccc000000000000cccc00030303030000000003030303000000000303030300000000030303030888888880000000088888888000000008888888800000000888888880330033000000000033003300000000003300330000000000220022cccccccc000000000000000000000000cccccccc00000000000000033333333000000003333333300000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x5843105846310584731058473a1058431b058493a058496a54732105493210543210
|_=>0
def sO:Nat→Nat→Nat
|6,0=>0x28c35c33806
|7,0=>0x60ea210b9a7
|8,0=>0x377
|9,0=>0x3e6
|_,_=>0
def wAt:=mkWire dB 12 222 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xc1614c1a3441a3c41014c5304053161e614c187a411361e614c1
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x4998c6603
|7,0=>0x91409c4c2
|8,0=>0x141
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 9
def pmP:Nat→Nat
|0=>0xfff9f9fdff3fc7f1140d01c00
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x4123
|7,0=>0x9856
|8,0=>7
|9,0=>4
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 10 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_217 8 roots_217 ops++addP pm 1 dom_213 8 roots_213 ops++addP pm 2 dzo_217_4 8 roots_217 ops++addP pm 3 dom_220 7 roots_220 ops++addP pm 4 dom_157 7 roots_157 ops++addP pm 5 dom_93 7 roots_93 ops++addP pm 6 dom_201 7 roots_201 ops++addP pm 7 dom_29 4 roots_29 ops++addP pm 8 dom_156 4 roots_156 ops++addP pm 9 dom_92 4 roots_92 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_221 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_217_4_201 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_201 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_29 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_156 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_92 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_217 8 s (0,roots_217.map (·&&&dom_217)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_221 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_217 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xffffffffffffffff0000000000000000,64),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xffffffffffffffff0000000000000000,64),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_221==dom_221)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_221 gM v ys):RunD true dom_221 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_221 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 4 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 4 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_221 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_221 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_221 roots_221 goal_221 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_221
theorem lowS_221:Lower true dom_221 roots_221 goal_221 10:=S_221.noCircuit
theorem lowS_222:Lower true dom_222 roots_222 goal_222 9:=lower_slice_b [(0x50505050000000005050505000000000505050500000000050505050,16,20)] (by decide +kernel) lowS_218
theorem lowS_245:Lower true dom_245 roots_245 goal_245 9:=lower_slice_b [(0x30003000300030003000300030003000300030003000300030003000300030,16,20)] (by decide +kernel) lowS_241
theorem lowS_246:Lower true dom_246 roots_246 goal_246 9:=lower_slice_b [(0x50005000500050005000500050005000500050005000500050005000500050,16,20)] (by decide +kernel) lowS_242
def isoMvS_111:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_111:Lower true dom_111 roots_111 goal_111 9:=lower_iso_b isoMvS_111 (by decide +kernel) lowS_95
def isoMvS_126:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_126:Lower true dom_126 roots_126 goal_126 8:=lower_iso_b isoMvS_126 (by decide +kernel) lowS_119
def isoMvS_159:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_159:Lower true dom_159 roots_159 goal_159 9:=lower_iso_b isoMvS_159 (by decide +kernel) lowS_95
def isoMvS_175:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_175:Lower true dom_175 roots_175 goal_175 9:=lower_iso_b isoMvS_175 (by decide +kernel) lowS_95
def isoMvS_183:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_183:Lower true dom_183 roots_183 goal_183 8:=lower_iso_b isoMvS_183 (by decide +kernel) lowS_119
def isoMvS_187:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_187:Lower true dom_187 roots_187 goal_187 10:=lower_iso_b isoMvS_187 (by decide +kernel) lowS_123
def isoMvS_189:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_189:Lower true dom_189 roots_189 goal_189 10:=lower_iso_b isoMvS_189 (by decide +kernel) lowS_125
def isoMvS_190:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_190:Lower true dom_190 roots_190 goal_190 8:=lower_iso_b isoMvS_190 (by decide +kernel) lowS_119
def isoMvS_231:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_231:Lower true dom_231 roots_231 goal_231 9:=lower_iso_b isoMvS_231 (by decide +kernel) lowS_222
def isoMvS_235:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_235:Lower true dom_235 roots_235 goal_235 10:=lower_iso_b isoMvS_235 (by decide +kernel) lowS_219
def isoMvS_237:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_237:Lower true dom_237 roots_237 goal_237 10:=lower_iso_b isoMvS_237 (by decide +kernel) lowS_221
def isoMvS_238:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_238:Lower true dom_238 roots_238 goal_238 9:=lower_iso_b isoMvS_238 (by decide +kernel) lowS_215
def isoMvS_243:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_243:Lower true dom_243 roots_243 goal_243 10:=lower_iso_b isoMvS_243 (by decide +kernel) lowS_219
def isoMvS_249:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_249:Lower true dom_249 roots_249 goal_249 10:=lower_iso_b isoMvS_249 (by decide +kernel) lowS_219
def isoMvS_250:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_250:Lower true dom_250 roots_250 goal_250 10:=lower_iso_b isoMvS_250 (by decide +kernel) lowS_219
def isoMvS_252:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_252:Lower true dom_252 roots_252 goal_252 9:=lower_iso_b isoMvS_252 (by decide +kernel) lowS_245
theorem lowS_127:Lower true dom_127 roots_127 goal_127 11:=lower_slice_b [(0xcccccccccccccccccccccccccccccccc,16,18)] (by decide +kernel) lowS_125
theorem lowS_223:Lower true dom_223 roots_223 goal_223 11:=lower_slice_b [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,16,18)] (by decide +kernel) lowS_221
theorem lowS_247:Lower true dom_247 roots_247 goal_247 11:=lower_slice_b [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,16,20)] (by decide +kernel) lowS_243
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
namespace S_253
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(1,129),(4,20),(4,36),(5,13),(5,21),(5,37),(5,69),(5,133),(8,9),(8,40),(8,72),(8,136),(12,13),(12,28),(12,44),(12,76),(12,140),(16,17),(16,20),(16,80),(16,144),(24,25),(24,28),(24,56),(24,88),(24,152),(32,36),(32,40),(32,96),(32,160),(33,37),(33,41),(33,49),(33,97),(33,161),(48,49),(48,52),(48,56),(48,112),(48,176),(64,65),(64,72),(64,80),(64,96),(64,192),(68,69),(68,76),(68,84),(68,100),(68,196),(128,129),(128,136),(128,144),(128,160),(128,192),(132,133),(132,140),(132,148),(132,164),(132,196)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffffffffffffff
def xsM:=roots_253.map (·&&&dom_253)
def gM:=goal_253&&&dom_253
def NN:Nat→Nat
|10=>1
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|10,0=>0xdfc1b
|11,0=>0x1e31b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000003333000033330000333300003333000033330000333300003333000033330000cc88cc88cc88cc88cc88cc88cc88cc88cc88cc88cc88cc88cc88cc88cc88cc8b300330033003300330033003300330033003300330033003300330033003300c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c2222222222222222222222222222222222222222222222222222222222222222cccccccccccccccc0000000000000000cccccccccccccccc0000000000000003333333333333333333333333333333300000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x1f4688fac688
|_=>0
def sO:Nat→Nat→Nat
|10,0=>8
|11,0=>0x87
|_,_=>0
def wAt:=mkWire dB 8 254 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 8
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x89
|_=>0
def oO:Nat→Nat→Nat
|10,0=>1
|_,_=>0
def PO:=mkPO wAt oP oO 8 3 7 5
def pmP:Nat→Nat
|0=>0x3f80
|_=>0
def pmB:Nat→Nat→Nat
|10,0=>1
|11,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 1 (j%128);fld (pmP (k/32)) 7 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_249 10 roots_249 ops++addP pm 1 dom_189 10 roots_189 ops++addP pm 2 dom_125 10 roots_125 ops++addP pm 3 dom_237 10 roots_237 ops++addP pm 4 dom_221 10 roots_221 ops++addP pm 5 dom_252 9 roots_252 ops++addP pm 6 dom_245 9 roots_245 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_253 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_189 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_237 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_221 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_245 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_249 10 s (0,roots_249.map (·&&&dom_249)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_253 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_249 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_253==dom_253)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_253 gM v ys):RunD true dom_253 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_253 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_253 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_191:Lower true dom_191 roots_191 goal_191 11:=lower_iso_b isoMvS_191 (by decide +kernel) lowS_127
def isoMvS_239:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_239:Lower true dom_239 roots_239 goal_239 11:=lower_iso_b isoMvS_239 (by decide +kernel) lowS_223
def isoMvS_254:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_254:Lower true dom_254 roots_254 goal_254 11:=lower_iso_b isoMvS_254 (by decide +kernel) lowS_247
def dzo_203_4:=0xf0f0000000000000f0f0000000000000f0f0000000000000f0f0
def gzo_203_4:=0xf0f0000000000000f0e0000000000000f0e0000000000000a000
def gsh_203_4:=0xf0f0000000000000f0e0000000000000f0e0000000000000a00
theorem lowS_zo_203_4_203:Lower true dzo_203_4 roots_203 gzo_203_4 8:=lower_iso_b (d1:=dom_203) (r1:=roots_203) (T1:=gsh_203_4) [(dom_203,4)] (by decide +kernel) (lower_slice_b (T:=gsh_203_4) [] (by decide +kernel) lowS_203)
def dzo_171_4:=0xf0f00000f0f000000000000000000000f0f00000f0f0
def gzo_171_4:=0xf0f00000f0e000000000000000000000f0f00000a000
def gsh_171_4:=0xf0f00000f0e000000000000000000000f0f00000a00
theorem lowS_zo_171_4_139:Lower true dzo_171_4 roots_171 gzo_171_4 6:=lower_iso_b (d1:=dom_171) (r1:=roots_171) (T1:=gsh_171_4) [(dom_171,4)] (by decide +kernel) (lower_slice_b (T:=gsh_171_4) [(0xf0f00000000000000000000000000000f0f00000000,0,32)] (by decide +kernel) lowS_139)
def dzo_251_4:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def gzo_251_4:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0f0f0f0f0f0f0f0e0f0f0f0f0f0f0a000
def gsh_251_4:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0f0f0f0f0f0f0f0e0f0f0f0f0f0f0a00
theorem lowS_zo_251_4_203:Lower true dzo_251_4 roots_251 gzo_251_4 10:=lower_iso_b (d1:=dom_251) (r1:=roots_251) (T1:=gsh_251_4) [(dom_251,4)] (by decide +kernel) (lower_slice_b (T:=gsh_251_4) [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000,0,16),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000,0,32)] (by decide +kernel) lowS_203)
def dzo_235_4:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0
def gzo_235_4:=0xf0f00000f0f00000f0f00000f0e00000f0f00000f0e00000f0f00000a000
def gsh_235_4:=0xf0f00000f0f00000f0f00000f0e00000f0f00000f0e00000f0f00000a00
theorem lowS_zo_235_4_203:Lower true dzo_235_4 roots_235 gzo_235_4 9:=lower_iso_b (d1:=dom_235) (r1:=roots_235) (T1:=gsh_235_4) [(dom_235,4)] (by decide +kernel) (lower_slice_b (T:=gsh_235_4) [(0xf0f0000000000000f0f0000000000000f0f0000000000000f0f00000000,0,32)] (by decide +kernel) lowS_203)
def dzo_107_4:=0xf0f00000f0f00000f0f00000f0f0
def gzo_107_4:=0xf0f00000f0e00000f0f00000a000
def gsh_107_4:=0xf0f00000f0e00000f0f00000a00
theorem lowS_zo_107_4_75:Lower true dzo_107_4 roots_107 gzo_107_4 6:=lower_iso_b (d1:=dom_107) (r1:=roots_107) (T1:=gsh_107_4) [(dom_107,4)] (by decide +kernel) (lower_slice_b (T:=gsh_107_4) [(0xf0f0000000000000f0f00000000,0,32)] (by decide +kernel) lowS_75)
def dzo_219_4:=0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0
def gzo_219_4:=0xf0f0f0f000000000f0f0f0e000000000f0f0f0e000000000f0f0a000
def gsh_219_4:=0xf0f0f0f000000000f0f0f0e000000000f0f0f0e000000000f0f0a00
theorem lowS_zo_219_4_203:Lower true dzo_219_4 roots_219 gzo_219_4 9:=lower_iso_b (d1:=dom_219) (r1:=roots_219) (T1:=gsh_219_4) [(dom_219,4)] (by decide +kernel) (lower_slice_b (T:=gsh_219_4) [(0xf0f0000000000000f0f0000000000000f0f0000000000000f0f0000,0,16)] (by decide +kernel) lowS_203)
def dzo_227_4:=0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f0
def gzo_227_4:=0xf0000000f0000000f0000000e0000000f0000000e0000000f000000000
def gsh_227_4:=0xf0000000f0000000f0000000e0000000f0000000e0000000f00000000
theorem lowS_zo_227_4_195:Lower true dzo_227_4 roots_227 gzo_227_4 6:=lower_iso_b (d1:=dom_227) (r1:=roots_227) (T1:=gsh_227_4) [(dom_227,4)] (by decide +kernel) (lower_slice_b (T:=gsh_227_4) [(0xf000000000000000f000000000000000f000000000000000f00000000,0,32)] (by decide +kernel) lowS_195)
def dzo_234_4:=0x505000005050000050500000505000005050000050500000505000005050
def gzo_234_4:=0x505000005050000050500000504000005050000050400000505000000000
def gsh_234_4:=0x50500000505000005050000050400000505000005040000050500000000
theorem lowS_zo_234_4_202:Lower true dzo_234_4 roots_234 gzo_234_4 6:=lower_iso_b (d1:=dom_234) (r1:=roots_234) (T1:=gsh_234_4) [(dom_234,4)] (by decide +kernel) (lower_slice_b (T:=gsh_234_4) [(0x50500000000000005050000000000000505000000000000050500000000,0,32)] (by decide +kernel) lowS_202)
def dzo_123_4:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def gzo_123_4:=0xf0f0f0f0f0f0f0e0f0f0f0f0f0f0a000
def gsh_123_4:=0xf0f0f0f0f0f0f0e0f0f0f0f0f0f0a00
theorem lowS_zo_123_4_75:Lower true dzo_123_4 roots_123 gzo_123_4 7:=lower_iso_b (d1:=dom_123) (r1:=roots_123) (T1:=gsh_123_4) [(dom_123,4)] (by decide +kernel) (lower_slice_b (T:=gsh_123_4) [(0xf0f00000f0f00000f0f00000f0f0000,0,16),(0xf0f0f0f000000000f0f0f0f00000000,0,32)] (by decide +kernel) lowS_75)
def dzo_187_4:=0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0
def gzo_187_4:=0xf0f0f0f0f0f0f0e00000000000000000f0f0f0f0f0f0a000
def gsh_187_4:=0xf0f0f0f0f0f0f0e00000000000000000f0f0f0f0f0f0a00
theorem lowS_zo_187_4_139:Lower true dzo_187_4 roots_187 gzo_187_4 7:=lower_iso_b (d1:=dom_187) (r1:=roots_187) (T1:=gsh_187_4) [(dom_187,4)] (by decide +kernel) (lower_slice_b (T:=gsh_187_4) [(0xf0f00000f0f000000000000000000000f0f00000f0f0000,0,16),(0xf0f0f0f0000000000000000000000000f0f0f0f00000000,0,32)] (by decide +kernel) lowS_139)
namespace S_255
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(1,129),(2,18),(2,34),(2,66),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(4,20),(4,36),(5,13),(5,21),(5,37),(5,69),(5,133),(6,22),(6,38),(6,70),(6,134),(7,15),(7,23),(7,39),(7,71),(7,135),(8,9),(8,40),(8,72),(8,136),(10,11),(10,26),(10,42),(10,74),(10,138),(12,13),(12,28),(12,44),(12,76),(12,140),(14,15),(14,30),(14,46),(14,78),(14,142),(16,17),(16,18),(16,20),(16,80),(16,144),(24,25),(24,26),(24,28),(24,56),(24,88),(24,152),(32,34),(32,36),(32,40),(32,96),(32,160),(33,35),(33,37),(33,41),(33,49),(33,97),(33,161),(48,49),(48,50),(48,52),(48,56),(48,112),(48,176),(64,65),(64,66),(64,72),(64,80),(64,96),(64,192),(68,69),(68,70),(68,76),(68,84),(68,100),(68,196),(128,129),(128,130),(128,136),(128,144),(128,160),(128,192),(132,133),(132,134),(132,140),(132,148),(132,164),(132,196)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffffffffffffffffff
def xsM:=roots_255.map (·&&&dom_255)
def gM:=goal_255&&&dom_255
def NN:Nat→Nat
|6=>5
|7=>108
|8=>582
|9=>625
|10=>265
|11=>52
|12=>8
|13=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0xcef6a5688435c3b1440507863
|7,0=>0xe6a99d4effc4d97c2488ae7a5abd279e9d280f887ca947b0c9798b777836775ca774ca771e073f767324e70c996fbff6e8c76abbf6870f63f9c615346093c606775e0f15b93e5aba459346567c04f2f14ca344c06a44a9042c0b4184f3e5c93db973d8f13d8283cdd63a1e639ad535f3832b4a3282430b68306c22ba212b5a12a12d296ce2937c28d2728c17259632529c2515b24bdb2447e2340e230f822814224e021f53207801f0011dec71d3761ad851947216e7014d9314c3614b8214886139c11389b11b9a1167611002109671005f0ec140def20bf680bec40ae1e0910c08437082a40822707bf60716706d380580a0529203aff03476030700223b01e8c01dfd00f5900ede00dc00042e
|8,0=>0x1531d148ca14720146531451814416143391430c13f8413c5e13bed1373f1365e1364f131661311e12c8c12a18128971220811cbd119c91193e1178a113e7113e5105d2102dc10215100510fdb50fd230fb670f80a0f2960efd80ea8b0e8da0e5570e4ff0df660df1a0dd4b0dcb60dc100da210d64b0d2e50ce080c8ce0be130bd170b85f0af960ae140ab930a97b0a8ef0a8ad0a6410a4570a2fe0a14e09bb809ba0098f1098de098a70955c0930308f3208df808d6308b2408aaa089900888d0884f085270839d082d3081d107d5d07b3307a4a078df0745306fac06e6506db906c2806ae406a440653f05ed805e1c05a050590a057ae05437053da04f6504b2c046e4046b7045c603edd03c0703b730377b036e5034b3032da031c802cf402a2b0253001df5018a60174e016c2014d90146300cf800c8f00a79005ba0043f
|8,1=>0x2c9de2c3af2be192bbe72bbaa2b2222b1d62adfb2aabb2aaac2a6e22a43c2a27828d2728c58284a42834527d9527a532764e27633275c1274e2273292720c26d6d2683b26660265b42649625a8f25862257f92579b2566824eb724e5a24d5124c0824b9f23c3e23b1e23a68239d723940234e823479233f3232d823229230c72275f22542224bb21f5321e3921dff2156321208210c120fc720d4320cf220b112085e20743206e42048c200fa1f7cf1f7541f5151f41d1f3821eea81eb6f1e8ce1e7c81e34e1dede1dcd81dc9b1db601d9b91d8b81d8751d8711d8361d0321cc431c6231bc941baf01b9fb1b9161b6c91b65d1b4b21ae111a80d1a13c19ff719e2319ae019abc1989f193d31931d1912418f4118d4e18cad187291823c17dcf17c9f17c2e179d4176e3174c1173ef16bc3168c615f8015e1b155f3155d3153c1
|8,2=>0x47e3b469d6460c745d5244b9c44a5b449ea44976443a74429643dbb4362c435b34347242e9a42c6e42b2042a4b427414268b422fd41f2241877415db415984147c411ea40e5440cad4092040389401bd3fb323faa83f9433f77d3f44c3f4043efbb3ef573e8f63e5923e10d3dc893d9f83d93a3d60e3cfc23c94d3c8fc3c5ea3b98b3b5c43b1ac3af093a9f13a78e3a01639d3a3994c3963b38d6f388d838841387f437f8237f7b37c9e37b32379ee3794b375133723f361753601335ff035e7c35c2235ae1350a334f7f34ed234d13349c83480d347543447a341ec33aea33a8a33906334d8331cb3310132d7432a4d32444322d43228c3228031d5d31bae319f6316b330c5630ba030b78308283047e3012a300af2fdde2fca12fc4f2fc162f1932ecfc2e98f2e9492dfbf2dbcc2dae62da402d8352d7c32d4e42cd462cc3c
|8,3=>0x7e0887db357ce907bb357b59d7ac057ab057a61c78729783bf76604764d8760d975c5775c467559474e92748c07446173a2e72caf72bf772736718c4707476fb406f3156ebae6e4126e0c16dbfa6c5c36ba5c6b9cc6b8866b83f6b8036b3886b3166adca69da0686de6775266f34646f563eef6371862feb62b206253861ec261dd761d3e6171b6137e60e8660d4b60c7e5fe365fdd95f2aa5e8175e6c05e4075df785c6675bec45b62d5b5af5b40f5a2aa59f595990359051587cb584d657a9e571a4571785706756f5256c5f55b7355a13555a75535254749546845402353de253b1c539b65376f5318752b2f52a5c523d351db251b9f51401507954f9df4f7c84ec734eb094e8f64e8214e7634e28c4e0fb4dbbe4db784d5e14c37e4bce74b95b4b9454b52a4adee4acd44aa974a3e44a16249c3d493c84935248c794890b
|8,4=>0xff253f11a6f0f57eb2b8e4fd0e0276dad8cd748bd6d88d2fa9d25e3cfa63c9963c70f7c5c57c5002c35a0c146ec07cbbd57abc413b7e09b5b1db4ffeb47aab1af2b01e4af3e5ac134a950ba6feca65f8a5f6aa5f5ca28999eabb9e4689c9199c3e29b4f9974db9345691c399118d90f7f8fb858fb7f8d6438ce888c9ae8c8d38b04788dc48893586860864c785ef085e90842d58349583250827e481f2681a2381277802b87ffc37f7727ed7a7e416
|9,0=>0x114cb1133b112b3105e910517101d910117100360fd950fd040f8e80f7980f7640f7040ef6b0ec600ebd20e9440e8e90e63d0e5340e19d0de540dc7d0db460d92e0d6770d2730ce6b0cc3e0cc060cb640c9410c8050c3b90c39c0c0db0bea60bddb0b9840b9630b9120b7cc0b7be0b6f00b0b80a9a60a8de0a6080a5740a5680a5460a1b30a1060a08609f4709e1109cdb09c9109b2c09ac6097860950e093b3092b908d5208b7b08863087f60870e082de081fd080420791007861078140738c06fbb06a4906a40068af068ae0682b067750667606618065fa064a105dbc05cdc05884057ce05399050530501304e0304dbb04c3504b30047c3045310451304501042850406803e0b03bd503bb603ac303a4303715033b9033490329002ebe02b38027eb0226f01f5601d88018d70101000d8400b7500afc007fa0060b0002c
|9,1=>0x290c3290c028ff228daf28c4128c242863027e0e278ac275c12743426f7d26dda26c9b26a1826625261f026131260e625f1625db625d5e25b9825a382524a249922469c245612444923ded23a33237a323302227e52241b2202721eb32141b21206211bf2100220dad20c6e208e0208d82087d204bd202262002c1fe611fe071fdab1fa891f9651f6eb1f5791f2421ed971eb841ea5e1e3811e1ad1e1301de581dda61dda21dcfb1dbed1cfa11c3e01bdac1bc941b2cb1afd01ae7a1a9851a4ad1a4851a3241a2a31a1f519d6119cab19bc319899196f019660195f118623183551833f1832e1818b17eea170f21705716ea416a1b167b616724160a315f6115ecf15c97159d91555514f0014ec214afe14a44149771491b146fa13c3d13af413a6f13589134511317712c1b12b65129e011dfb119d3119c9118151178e11594
|9,2=>0x498af48fab48d2a48c2a489bd46bbe461ed45d0645c2f45766452f744f9344f4c43f41439f4435fc4359f43260431ee430cf42f4142c25420c041804416104146e40ee240e5d40a1e405ff404be401d13feb43fcd63f7703f2773f1f53eed93e8203e34c3dfdf3dfd33df143dc5a3d0133cf593cf553ca933c9783c67e3c6233b9803b4ab3b3233b2073ae3c3ac3d3abed3a2da3a0283a00c39e1e39b1d3950f38a9b386a33837c37a23379013787c3749336df036b2b36ae536095359ae358f835731351cd350d534da8344cf341c433c9c3368e32fb232ac631d9431cdc31b1b31873315e4310e330b4b30ab830086300832fcfd2f90d2f7932f7402f0b22f0422efc92e7962e0342de722dd2a2dbe52d2ea2d28c2d1d52cd0a2cc362ca952c4902c31f2c04f2bcce2ba4b2b6092b5e92ad3b2aa052a7e22a5e02a2df294bd
|9,3=>0x7d93f7d7547cdfb7c7fe7bdda7ae6279e7d79958797e37864378409780c77742a772e976b827568d754fa7514c7510674fc0745fb744fe743bc73a94728157248872105719e16f2936ed196e6dc6e1246d6e16d11b6d1066c2836c1ea6c1cd6bed06bdae6b3706affd6a28169e8169c49691486901067ce867b77678826767f66580655ff64c5763f9c634ae620db61814615ff614a46136d611ce6045e5fcab5f3685e9ae5e97a5de755d8625d7de5d6605d4595cbe95c8a95c8525c06a5bd535a28b59a26596b55881c587b3570c0566c7563e055e7255d2954d3c547ca53fe253ec2539db5347d5332452baa52452522175142e513b5510d550f5d50ee550ec550c9e50a0a507d5504595013b4ffc44fe6f4f6304f0ab4ec0c4ea734d8d84d8b14d60e4cd8d4c8704bc1d4b7424b5be4b29a4acc64a7874a4c84a4164a2a4
|9,4=>0xed1caea6e7e7f94e2045db659d97c3d81c6d69b1d526fd1a3fd19ead0ce9cead6cdb6ec9e14c834fc5fa7c51acc42ebc29b1c265ec026dbf8d7be80abe7e3bd81ebc65abab8cb8e6ab8563b851eb6dbbb6939b64d8b6322b4c06b497fafb27aebfdadfa2acaacaa3b6a7f8fa666da465da368ea2f75a2de3a27b1a143b9fce39ec459de5c9dc2b9bb719b4049a6ae9a10e998859904f98e9398b459863a9850397dd1958139532a949d49479093f3c93d6192f3592c799264a918e890bc78ff5b8fd3b8fa5c8e1968d4d98d3778b3d38a2578a10989f5e89cd3884248831387b068789287795876a387640861738606884f2b84d6884a89847bf845e984414838fc838d583310826bf81fde81f9b816e8808947e5fa7dd5e7d969
|10,0=>0x3a64e3a44039d173902d3854537ba7372e336a873676c366fe3640334c6e347e4345e6341003349632cd032a97326cf324df3235f30d7030af3306b52f1912e2ad2dac62d9152d33c2cf2b2cc702bc4b2bafe2b3932aae12a69929b102868c2823a2772327531270b426b3825d412576824dbb225e221d8c210f3207c3204171ff771fce51f2ba1ec451cefa1c7801c4e91b8c31b3781acd11acb2193031897d186891827b173a91653e15c6a152ea14f02147b213f06137f6132061287d12442121eb11cc91174a1149510bb4109dd0ffd00f77f0f53a0f2d20e3fd0e39e0e3750d2ec0cc6d0cb900ca540bc760b6360a7ba09ed609e1f08cf4081ef07cbc071b90710306e7906dc506515061c90612d060bc05e6205791050aa047a504544043a9032c403168028640285e027c10269c025e20204b0199e0141700d8500b7d
|10,1=>0xd01f2cf759ce4c5c8f5ec5ee3c3e0db6bdbb2d8fb0db7af630aca87aad91a9a3ca91b2a6910a67aea62c2a368ea3513a31f5a152e9d4439b3d59993698e88986c99645d937b592c1a9211d8f3f28e8368ca008b1c089d6e8887a8653d860f185621855048530782c6b82446806587dcea7d1847bc8e7aeff7ac1278e8978684752067426b71cfb71389706af7061d6c0a06bfe16b9856a3e068e24673ef66ded659496570d640a26339b632aa605e76039d5fc765c6975ac3b5a5b559527594395910d57f9a57ad657a8e5758356cb456231542b25407453b4b532b05261e51b32514c1514595140e4fb5d4f1b54ed2f4dc5a4d0af4caf04b66c4b1b44a19048c0f489c54821247ee247e6f4395642f7642d3242be542b0a41a0040cc93df453dce93d96a3d7f13d5ec3ccd83ca553c6593bdf03b45e3b3cc3b0b23a99a3a69d
|10,2=>0xf4fe6f3378f0517ecac3dd3b2dce5fdb513db202d7c1a
|11,0=>0xe07d0d6bf3cf95fccec0cc1c6c41c8c255abc94abb2cbb32cda7f2f9fd4b85631790ad74a38706da665bd5d9114697f40718405923dd1c3d8d83902f32ff02f5542ee582cae32c48c2aa252a9b329a99287fb2848e283b7260392558c24abe1ac8f0e7be0dd190ceb50c7af0c11306dd3067c006147056690403202a4d02901006e7
|12,0=>0xf9c0790bd459a3b4da8f1641b1045a0e41d06b9f
|13,0=>0x43e5c
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffffffffff00ffffffffffffff00ffffffffffffff000000000000000000ffffffffffffff00ffffffffffffff00ffffffffffffff00ffffffffffffff00ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ffffffffffffffccffffffffffffffccffffffffffffffccccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0055555555555555555555555555555555555555555555555555055505550555003333333333333333333333333333333333333333333333330303030303030000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000
|0,1=>0xff000000ff000000ff000000ff000000ff000000ff000000ff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff00003333333333333333333333333333333333333333333333333333333333330000ffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa5511551155115511551155115511551155115511551155115501550155015500ffffffffffffaaaaffffffffffffaaaaffffffffffffaaaa0000000000000000ffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffaaffffffffffffffaaffffffffffffffaaff00ff00ff00ff00ffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaacccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
|0,2=>0xff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff0000ffffffffffffffffff0fff0fff0fff00ffffffffffffffffff0fff0fff0fff00ffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaa0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff00000000ffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff0000000000ffffffff00000000ffffffff00000000ff00ff0000000000ff00ff0000000000000000000000000000000000ffffffffffffffffff0fff0fff0fff00ffffffffffffffff0f0f0f0f0f0f0000ffffffffffffffff0f0f0f0f0f0f0000ffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff000000000000ffffffff00000000ffffffff00000000ffffffff00000000ff00ff00ffffffffffffffffffffffffffffffffffffffffffffffffff00ff00ff00ff00ffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffff0000ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffffffffffffffffffffffffff0000ff00ff00ff00ff00ff00ff00ff000000ffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00
|0,3=>0xffffffff00000000ffffffff00000000ffffffff00000000ffffff00ffffffffffffffffffffffffffff0000aaaaaaaaaaaaaaaaaaaaaaaaaaaa000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff000000000000000000ffffffffffffffff0000000000000000ff0fff0fff0fff00ffffffffffffffffaaaaaaaaaaaaaaaaff00ff00ff00ff00aa00aa00aa00aa00ffffffffffffffffffffffffaaaaaaaaffffffffff00ff00ffffffffaa00aa00fffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0000000000000ffff000000000000ffff000000000000ffff000000000000aaaa00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff0000ffffffffffffffffffffffffffffffff0f0f0f0f0f0f00000f0f0f0f0f0f0000ffffffffffffffffffffffffaaaaaaaaffffffffffffffffffffffffaaaaaaaaffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000333333333333333333333333333333333333333333333333232323232323222255555555555555555555555555555555555555555555555555555500555555003333333333333333333333333333333333333333333333333333333333333300
|0,4=>0xffffffffffffffff0000000000000000ffffffffffffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00aaffffffffffffffffffffffffffffffffffffffffffffffffff0fff0fff0fff0000000000ffffffff00000000ffffffff00000000ffffffff00000000ffff0000ffffffffffffffffff00ff00ff00ff00aaaaaaaaaaaaaaaaaa00aa00aa00aa00ffffffffffffffffffccffccffccffcceeeeeeeeeeeeeeeeeecceecceecceecc00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00aa00aa00000000ffffffff00000000ffffffff00000000ffffffff00000000aaaaaaaa00000000000000000000000000000000ffffffffffffffffffffffffffffff00000000000000ffff000000000000ffff000000000000ffff000000000000ff003333333311111111333333331111111133333333111111113333333311110000fffffffffffffffff0f0f0f0f0f0fffffffffffffffffffff000f000f000ff00555555555555555555555555555555555555555555555555555555550000000000000000000000000000000000000000ffffffffffffffffafafafafafafaaaa0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00000000555500005555000055550000555500005555000055550000555500000000
|0,5=>0xffffffffffffffffffffffffffffaaaa0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000aaaa0000aaaa55555555555555555555555555555555555555555555555555555555555555000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000aaaa55550000555555555555000055555555555500005555555555550000555555003333333333333333333333333333333333333333333333333333333333332222ffffffffffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaa5555555555555555555555555555555555555555555555555555000055550000ffffffffffffffffffffffffffffffffffffff00ffffff00ffffff00ffffff0033333333333333333333333333333333333333333333333333033303330333003333333311111111333333331111111133333333111111113333333311111100ffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000aaaa00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000aa5f5f5f5f5f5f55555f5f5f5f5f5f55555f5f5f5f5f5f55550f0f0f0f0f0f000055555555555555555555555555555555555555555555555500000000000000001313131313131111131313131313111113131313131311110303030303030000
|0,6=>0x555555555555555555555555555555555555555555555555555555555555000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000f000f000f0000ffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaafffffffffffffffffffcfffcfffcfffcfefefefefefefefefefcfefcfefcfefc0000ffff0000ffff0000ffff0000ffff0000aaaa0000aaaa0000aaaa0000aaaaffffffffffffffffffffffffffffffffffffffffffffffffffffff00ffffff00bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbababababababaaaaffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffaaaaffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff00000000ffff000055550000ffff000055550000ffff000055550000ffff00000000ffffffffffffffaaffffffffffffffaaffffffffffffffaaaaaaaaaaaaaaaaaaff33ff33ff33ff33ff33ff33ff33ff33ff33ff33ff33ff33ff33ff33ff33ff0055115511551155115511551155115511551155115511551155115511551155000000000000000000ffffffffffffffff0000000000000000ffffffffffffaaaa0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff000000ff003333003333330033333300333333003333330033333300333333003333330000
|0,7=>0xffffffffffffffffffff0000ffffffffffffffffffffffffffff0000ffffff00ffff0000ffffffffffff0000ffffffffffff0000ffffff00ffff0000ffffff005555555555555555555500005555555555555555555555555555000055555500ffffffff0000ffffffffffff0000ffffffffffff0000aaaaffffffff0000aaaaffffffffffffffffffffffffffffaaaaffffffffffffffffffffffffffffaaaaffffffffffffffffffffaaaaffffaaaaffffffffffffffffffffaaaaffffaaaaffffffffffffffffffffffffffffff00ffffffffffffffffffffffffffffff00ffffffffffffffffffffffffffffffffffffffffffffff00ffffffffffffff0000000000000000000000000000000000000000000000ffff000000000000ff00ffff0000ffff0000ffff0000ffff0000ffff0000ffffffffffff0000ffffff00ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ffffffffffffffffffffffffffffffffffffffffff00ff00ffffffffff00ff000000ffff0000ffff0000ff000000ff000000ffff0000ffff0000ff000000ff000fff0fff0fff00ff0fff0fff0fff00ff0fff0fff0fff00ff0f0f0f0f0f0f000003330333033300330333033303330033033303330333003303030303030300000033003300330033003300330033003300330033003300330003000300030000
|0,8=>0xffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaaaaa0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff000000000000000000ff00ff00aa00ff00ff00ff00aa00ff00ff00ff00aa00ff00ff00ff00aa00aa5555555555555555555555555555555555555555555500005555555555550000ffffffffffffffffffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaa00000000000000000000000000000000ffffffffffffff00ffffffffffffff00ffffffffffffffffffffffffffffffffffffffffffffaaaaffffffffffffaaaaffffffffffffffff00000000ffffffffffffffffffffffff00000000ff00ff00ffffffffffffffffffffffffffffffffffffffffffffffffffffaaaaffffaaaa000000000000ffff000000000000aaaa000000000000ffff000000000000aaaaffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ff000000ffff0000ffff0000ffff0000ffff0000ff000000ff000000ff000000ff00ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffaaaaffffffffffffffffffffff00ffffff00ffffffffffffffffffffff00ffffff00
|0,9=>0xf0f0f0f0f0f0fffff000f000f000ff0055555555000055555555555500005555555555550000555555555555000000000000000033333333000000003333333300000000333333330000000033330000ff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffff00ffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00aaffffffffffffffffffffffffffffffffffffaaaaffffaaaaffffaaaaffffaaaa00000000ffffffff00000000ffffaaaa00000000ffffffff00000000ffffaaaaffff5555ffff5555ffff5555ffff5555ffff5555ffff5555ffff5555ffff00005555555555555555555555555555000055555555555555555555555555550000ffffffffffffffffffffffffff00ff00ffffffffffffffffffffffffff00ff00ffffffff0000ffffffffffff0000ffffffffffff0000ff00ffffffff0000ff00ffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00000000000000000000ffffffffffffffff0000000000000000aaaaaaaaaaaaaaaaaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffaaaa00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffaaaa00ff00ff00ff00ff00ff00ff00ff00ff00aa00aa00aa00aa00aa00aa00aa00aa
|0,10=>0xaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaaaaaff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ff000000000000005555000000000000555500000000000055550000000000000000aaaaaaaaaaaaffffaaaaaaaaaaaaffffaaaaaaaaaaaaffffaaaaaaaaaaaaaaaa5555000055555555555500005555555555550000555555555555000055550000ffffffff55555555ffffffff55555555ffffffff55555555ffffffff55550000ffffffffffffffffffaaffaaffaaffaaffffffffffffffffffaaffaaffaaffaa0055005500550055005500550055005500550055005500550055000000550000aaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaaaaaaaaaaaaaffffffffffffffffffffffffffffffffffaaffaaffaaffaaffaaffaaffaaffaa0000aaaa0000ffff0000aaaa0000ffff0000aaaa0000ffff0000aaaa0000aaaa000000000000000000000000000000000000000000000000ffffffffffffff0000000000000000ff00000000000000ff00000000000000ff0000000000000000ffff0000ffff00ffffff0000ffff00ffffff0000ffff00ffffff0000ffff0000ffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ff0000ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff00000000
|0,11=>0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00aa00aa00aa00aa00000000ffffffff00000000ff00ff0000000000ffffffff00000000ff00ff00ffffffffffffffffffffffff0000ffffffffffffffffffffffffffff0000ff00ffffffffffffffffffffffffff00ff00ffffffffaaaaaaaaffffffffaa00aa0000ff00ff00ff00ff00ff00ff000000ff00ff00ff00ff00ff00ff00ff00000000ffffffffffffffff0000ffff0000ffffffffffffffffffff0000ff000000ff00005500550055005500550055005500550055005500550055005500550000000000000000ffffffff00000000ffffffff00000000aaaaaaaa00000000aaaaaaaa0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000aa00aa00000000ffffffff00000000ffffff0000000000ffffffff00000000ffffff00ffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff0000ffff0000333333333333003333333333333300333333333333330033333333333333000000003333000033330000333300003333000033330000333300003333000000000000000000000000000000000000ffff0000000000000000000000000000aaaaffffffffffffffff000000000000ffffffffffffffffffff000000000000aaaaffffffffffffffffffffffffffffffffff0fff0fff0fff00ff0fff0fff0fff00
|0,12=>0xffffffff00000000aaaaaaaa00000000ffffffff00000000aaaaaaaaffff0000ffffffffffff0000ffffaaaaffff0000ffffffffffff0000ffffaaaaffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff00000000111111111111111111111111111111111111111111111111111111111111000000000000ffff555500000000ffff555500000000ffff555500000000ffff0000ffffffff000000ffffffffff000000ffffffffff000000ffffffffff000000000000555500005555000055550000555500005555000055550000550000005500ffffffffffff5555ffffffffffff5555ffffffffffff5555ffffffffffff000033333333333311113333333333331111333333333333111133333333333300000000000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000ffff000000000000aaaaffff0000ffff0000ffff0000ffff0000ffff0000ffffffffffff0000ffffaaaa0000000055555555000000005555555500000000555555550000000055550000ffffffffffffffffffffffffffffffffffffffffffffffffffaaffaaffaaffaa5555555555555555555555555555555555555555555555555500550055005500
|0,13=>0xffffffffffffffff0000000000000000ff00ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000ffffffffffff00ffffffffffffff00ffffffffffffff00ffffffffffffff000000000000ff00ffff00000000ff00ffff00000000ff00ffff00000000ff00ff0000000000ffffffff00000000ffffffff00000000ffffffff0000000000000000ffffff00ffffffffffffff00ffffffffffffff00ffffffffffffff00ffffff005555550055555555555555005555555555555500555555555555550055555500ffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff0000000000000000aaaaffff00000000aaaaffff00000000aaaaffff00000000aaaaaaaa00000000ffff00ff00000000ffff00ff00000000ffff00ff00000000ffff0000ffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff000000000000ffffffff00000000ffffffff00000000ffffaaaa00000000ffffaaaa0000000055555555000000005555555500000000555555550000000055555500f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f0f0f0f0f0f0f0f0000000000000000000000000000000000000000000000000ffffffffffffaaaaffffffffffffffffffffffffffffffff0000000000000000ffffffffffffaaaa
|0,14=>0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0f0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fff0f0f0fff00000000000000000000000000000000055555555555555555555555555550000ffffffffffffffffffffffffffffffff555555555555555555555555555500000000000000000000ffffffffffffffff0000000000000000ffffffffffff0000ff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ffffffffffffff00ffffffffffffffffffffffffffffffff00000000ffffffff00000000ff00ff00ffffffff55555555ffffffff55555555ffffffff55555555ffffffff00000000ffffffffffffffff0000ffff0000ffffffffffffffffffff0000aaaa0000aaaafffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fafafafa0000000000000000000000000000ffff0000000000000000000000000000ff0000000000000000000000000000000000ffffffffffffffffff00ff00ff00ff00ffff0000ffffffffffff0000ffffff00ffff0000ffffffffffff0000ffffff00ffffffffffffffffffffffffffffffffffff0000ffffffffffff0000ffffff00fffffffffffffffff0f0fffff0f0fffffffffffffffffffff0f0fff0f0f0fff0
|0,15=>0xffff0000ffff0000ffff0000ffff000000000000ffff000000000000ff00ffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff0000ffffffffffffffffffffffffffffffffffff0000ffffffffffff0000ffffaaaaffffffffffffffffffffffffffffffff00000000ffffffff00000000aaaaaaaaaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaa0000000000000000000000000000000000ff00ff00ff00ff00aa00aa00aa00aaff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffffffffaaffaaffaaffaa0000000000000000ffffffffffffffff0000000000000000ffffaaaaffffaaaaffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffaaaa0000000000000000555555555555555500000000000000005555555555550000ffffffffffffffffffffffffffffffff0000ffff0000ffff0000ff000000ff0000000000ffffffff00000000ffffffff000000000000ffff000000000000ff000000ffff0000ffff0000ffff0000ffff0000ffff0000aaaa0000ffff0000aaaaffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000aaaa00000000000000000000ffff0000ffff00000000000000000000aaaa0000aaaaffffffff00000000ffffffff0000ffffffffffff00000000ffffffff0000aaaa
|1,0=>0xffffffff00005555ffffffff00005555ffffffff00005555ffffffff00000000ffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffff000000000000000000000000000000000000ffffffffffffffff0f0f0f0f0f0f000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff0000000000000000000000000000000000000000ffff0000ffff0000ffff0000ff00ffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffaaaa00000000000000000000000000000000ffffffffffffaaaaffffffffffffaaaaffffffffffffffff0000000000000000ffffffffffffffffffffffffffffaaaaffffffff00000000ffffffff00000000ffffffffffffffffffffffffaaaaaaaa00000000000000000000000000000000ffffffffffffffffaaaaaaaaaaaaaaaaf0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0f0f0f0f0f0f0f00000555500005555000055550000555500005555000055550000000000000000f0f0f5f5f0f0f5f5f0f0f5f5f0f0f5f5f0f0f5f5f0f0f5f5f0f0f0f0f0f0f0f000000000000000000000000000000000ffffffffffffffffffffffffaaaaaaaaffff0000ffff0000ffff0000ffff0000ffffffffffffffffffffffffffffaaaafffffffffffffffffffffffffffffffff0f0fffff0f0fffff0f0fff0f0f0fff0
|1,1=>0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fffff0f0fffff0f0fff0f0f0fff0000000ff000000ff000000ff000000ff000000ff000000ff000000000000000000000000ffffffff00000000ffffffff00000000ffffff0000000000ffffff00ffff5555ffff5555ffff5555ffff5555ffff5555ffff5555ffff0000ffff0000ffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffaaaaff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ff00ff0000000000000000000000000000000000ffffffffffffffffffffff00ffffff00000000000000000000000000ffffffff000000000000000000000000ffffff00000000000000ffff000000000000ffff000000000000ffff0000000000000000ffffffffffff0000ffffffffffff0000ffffffffffffffffffffffffffffaaaaffffffffffffffffffffffffffffffffafafafafafafaaaaafafafafafafaaaa0000000000000000000000000000000000000000ffffffff00000000aaaaaaaaffffffffffffffffffffffffffffffff000000000000ffff000000000000aaaa0000000055555555000000005555555500000000555555550000000000000000f0f0f0f0f5f5f5f5f0f0f0f0f5f5f5f5f0f0f0f0f5f5f5f5f0f0f0f0f0f0f0f00000000000000000ffffffffffffaaaa0000000000000000ffffffffffffaaaa
|1,2=>0xf0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fafafafaf0f0f0f0fafafafa00000000000000000000000000000000ffffffffffffffffffaaffaaffaaffaa00000000000000005555555555555555000000000000000055005500550055000000ffff0000ffff0000ffff0000ff000000ffff0000ffff0000ffff0000ff00ffffffffffffffff00000000ffffffffffffffffffffffff00000000aaaaaaaa0000000000000000ffffffffffffff000000000000000000ffffffffffffff00ffffffff0000ffffffffffff0000ff00ffffffff0000ffffffffffff0000ff0000000000000000000000000000000000ffffffffffffffffffffaaaaffffaaaa0000000000000000ffffffffffffffff0000000000000000ffffffffaaaaaaaa55555555555555555555555555555555550055005500550055005500550055000000ff000000ffff0000ff000000ffff0000ff000000ffff0000ff000000ff000055005500550055005500550055005500550055005500550000000000000000f0f5f0f5f0f5f0f5f0f5f0f5f0f5f0f5f0f5f0f5f0f5f0f5f0f0f0f0f0f0f0f0fffffffffffffffffff0fff0fff0fff0fafafafafafafafafaf0faf0faf0faf0ffffffffffffffffffffffffffffffff00ff00ff00ff00ff00aa00aa00aa00aa000000000000000000000000000000000000ffff0000ffff0000ff000000ff00
|1,3=>0xffffffffffffffff00ff00ff00ff00ffffffffffffffffff00aa00aa00aa00aa5555555555555555550055005500550055555555555555555500550055005500f0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0f0f0f0f0f0f0ff55ff55ff55ff55ff55ff55ff55ff55ff55ff55ff55ff55ff00ff00ff00ff00000000000000ffff000000000000ffff000000000000ff00000000000000ff000000ffff0000ffff0000ffff0000aaaa0000ffff0000ffff0000ffff0000aaaaffffffff00000000ffffffffffffffffffffffff00000000ffffffffff00ff00ff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ffaaffaaffaaffaa
|_,_=>0
def sP:Nat→Nat
|0=>0x581440090801c5e010982c441d12024200703014082c038080200030145c04038080200168980809080b056010c87454090801c520d0301450040801c4e0d1189808090801c4a0d0702c1424048400e0d0308842090801c1a060508012100387c1a060e81408090c0443806028103011010340c050205c04010004c0a1204840220b050101208038180a04018080200
|1=>0x1f0040c090801c7a3c008000c051d81020070d80032331502420071b0002a331301012100c03426260202420070b0e40a041c0400e0d0a8cc4c040484058010989808090801c6e0d0982c0a24048400e36030140810018d402000c8d03a0404840220d0c8cc40090801c3e010301408071909c0200030140818038081a0016898080908060560d030140809188c00200
|2=>0x48400e460011c0c04048400e3c008180a040481c60010002c4424048400e46008180a04048b08a01000180a0408060221b068180a04220400e27000641404048405843000180a04081080e35008180a2e100400e270682c0a04048200e010309854090801c1e130289012100390400060e81012100c1000019198740809080602204048400e3c1f804002d130101210
|3=>0x28100e560d80400060281012312a804000605024200729834004f028101210038fc000e1982848090801c0006028100e50008009e060282420071e8000c05048400e4e00800321d020242018089300c05268100e02008006622150242007260000c05020e094070681412102192490010004c0a24048400e2f00054261d020242011068180a04048608a0d0004c442a
|4=>0xc84c40090801c6c0d0581454090801c820d070cc3a2a048400e002f81808090801cbc0103074080908060222b0301408092e87002000302812101601ca6000301012102c17002000282420071e894020005814400404840b6010301412072d13802002393c0c050202420070302808090806080001a02c0a0404840b00d0302808090401c00191995c5420048400e06
|5=>0x38040067168280809080b01a190501012100c10c00060509812101601c92060e8101210089980213028481210038000c05100242065008306605100240e1c008180a040498c380100018280a048405849001880c05020242058000184c04048403016030284c090801c920d0982c4424048400e610307412100394c0200198180a200481cc0010301408100186c0200
|6=>0x801ce60d1182c0a04048405807068180a04039c8e201000180a0403808e001000180809081bcb801000180a0403808dc010001012070e0ac980100030660a130901210038180a6d1c040960d0301408090c044380d03014086c2501c1a06028240e1c2480400191a01012100c1ac1a0c058144009080c4020602810d207010040006028101218228040054340101210
|7=>0x28101210038340c051001012102e804005f031e80a040484022012a0181404048400e0d000cc0c2205080121003834f2780301408090801c1a4f0f0180a04048400e000301440090801c3e0d0082c0a04048400e41068042a06130101210160340267031d808090801c0200070cc3a04048400e01001d48e0602810121003804ea06028101210188040074030144009
|8=>0x1f80400810301408090816002000202420071593002003d88c1605020242007068cc0c051502420074103466064001440090801c1a74098740a04048400e0d3c8190005100242007068780c05020240e5a00800ce064001012100383432341301012100c01c1a780315c1404048400e0d0f0183a05020242018089d00c05048400e3d008000c0502024207d00800f813
|9=>0x3800321302024200735834c4063d01408090801c00061108412100380400790581408090801c1a060e814121003924020003014540404840b601000180a040481c3884008006606028801210038f4022316898080908044020e0981448090801c0023058144804048400e0d0c81854090801c6c0d001e4160510024200700a0c0c05020240e1c00800e805020242007
|10=>0x28801210038041c060508012100383432060e81012100c0441a060501012100387c1a00448542605020242007068180a04080b00e35068040c800281012071800400131301408090801c4a0d0301450040801c4e010008c0c22048400e3d0080066051001012100393002193f810121003a2002000982d0e05020242007068180a04048402286069d02680028a81210
|11=>0x6800260502024200746034f2470301408090801c1a0b428144004048400e01058180a20048400e36008641622120242007008b4d005020242011008002a060282420072700400194587408090801c1a011188808090801c9801000cc0c14050101210160002606028900809080c400670301012070e0ac02004504c0a2a048400e00168140809080446e01001e48e06
|12=>0xc84cae04048400e0d03074080903870560100018fc051502420070697c460b028101210038040c05020240e5a0680400191689808090824c02190e81012104901c02003a0180a040481c60010019c0a0404841240700800b2050202420074880400783a0180a2a048400e0d03014083808061200d03014121003a3402000c81900040484062010013c0c05020242007
|13=>0x48408649008000c05020400e1b3700400670308848090801c1a010c8cc08090801c3e0100019300502024202c00800320b2b8a840090801c020613010121003a5c1a96032004c04048400e0d05818281d02024202c008180a041c0406201000180a20020400e2706a542605020242007068cc0c94028a81210038000c2602024202c039700206028242007248ac0200
|14=>0xc0341c4f0981408090801c00230281012070e2740200031e80a041c040220d058153804048400e0d00818440a120e02007000640c24048400e360080066050202420920380400064d81412100392402000315c0a2a100e02007068183a050202422070e0042605120101210039180033032680a0404840300d1682cf405020242018068180a0404840229906a2c0c05
|15=>0xe8101210088043c050202420071280400890301412100392402002a01814040484058070013c0c0515080121003800ea060202420071e004007b059e80a04048400e0d070cc0a20048400e010301440090801c8201000642604048400e5e068000c05020242018088ac1a74030140809080c40200032600a0404840300d0006516050202420180682c0c140e8101210
|16=>0xb44c04048400e2b06804320b350101210038340206028113e10038d402001a0180a0404840301147064161d150101210038340c0510024200720834020c09a004c2a048400e000307408090801c6e0100054260502024202c06800322d1301012100c0340c050202420114f004003402810121003a4402000c8b4080908060bc01000b42605020e02011068cc0c14
|17=>0x816002000f01808090801cb801000184c0502024202c2180512060281012100c0441a5f458180a04048400e010308854090801c980d0022c0c0502024205800800328b0501012100c0002a620981408090801c000e0328808090801c020033819002a020242007069ecbe061301012100380432330501012101601c0033030284c040484058070301440090801d4001
|18=>0x309808090801cc20d0c81454090801c520d3c8180a20048400e0d030154c041c040301106a2c0c05020242058068041c33028a81210038340006028b840100389c0200311640c05020242007001e41605150101210038340c1d02024200752804000e09814482a048400e003a8180a04048400e01002040c05048400e4e00800f20b028a840090801c021e168140809
|19=>0x801c1a0602890121018aa002000c82c4424150242007008180a040389c04010002c0a04108242007008184c0502024201821834f20e0581408090801c1a33030284c240202420070c82c3a04048405807008180a2e020400e27068000c05048414e074680400190595c4804048400e010602c3a0515024200706830160510024200730804f20e0581440090801c0213
|20=>0x20242043240040013030504c0404840580d030295c04048400e0d000180a040481c6001000546626020242007068042a0602810121056004002d050140809080b09000031a00a0404841560100018fe0502024207d0080154060281012100c00400740981440041c0400e0d0982c44051202420070301552a610024202c008180a04048b00e5a0080116130e8140809
|21=>0xa240c9a0501012100c0000c0554a984009080601a060e81012105781c0200278180a240202420070022c0c05020e02018068180a0404840fa880080026061107448090801c001e0308808090387002002388c160502024200700864161d020242018038340c05020242018089301a790301408090387002001981412100392490010017c680602810121008804b205
|22=>0x2810121003ac40039028101210038340c052681020071a80400780301408090817402000c8cc442a048400e000307408090801c8001000184424048400e3c00800260b2b8145420048400e5f118180a04048400e0d030280809080440e2b069ec0c05020240e5a0080032330e81012100881c0259030140809081bc02000581408090801c020f0602cae05120242007
|23=>0x30004000e1981448090801c02000301412100c10c9201000184c04048400eb6068196a05020240eb400800f20b0289008090801c0206028242007270040006028242007421840200030101210039792201000780c221002420070680432062b8a840090801c1a061109012100393002000f01808090387166010022426050202420070682c0a04048400e3f068044606
|24=>0x48400e495b804001e02810121003a4402000301454380801c520d032000a2a048400e2906818440a048400e8406800680502024204324004001919a6008090801c0200168cc0a0404840de01000180a090801ca60d008001c0510024200712804007803014121003a1002000c8cc08090801cd60d008640c80048400e36008000c140e8101210089300206028101207
|25=>0x418180a090801c7a010022c0c05048400e4e0080112064d02808090801c1a0e030141210038f40200168140809080b06e01000180a04080440e1b0680468060281012103780400060281012102c2e01a010982cd405020242007068b40c0a130101210160440c6a0281012070e0040019030745420048400e0d2f8190e05020242007008180a2a048400e3d008006605
|26=>0x2600400060282420075dae802000309808380801cbc014181408090801c7e01000300a2a048400e3f008001c050202420071f8040006028102007139b80200458180a0908125720100064262602024202c03834a8060e8101210038040019059a84804048400e0119818441d100242007008641404048400e43068000c0a1301012100390c1a2d340140809080b00200
|27=>0x1301454090801d080d030883a2a1c0400e002f818f405020242007068180a040481c8a0d00800260b2b8144804048400e1919888121003a1002000c9640a090801c920100038262602024200706818f405020e020180883516063d0140809080441a1903074080908044b0010c84cd42a0202420070019c0c04048400e1f008000c05020241007008000c04048400ea5
|28=>0x48400ebb008005a064d0280809080441a0c059a80a24048400e010307408090801c3e01000302605100e02007068180a2a020240e30008005a06050101210161780062030140809080440e0d030140821048400e0d198180a20048400e3600af00a20048400e01338101210038ac98010002c0c05020242031068040c05020e020185c034f20e0301440090801c1a06
|29=>0x391802003d81808090801cb801000184c041c0400e61008182805048402249008000c051002420070083c0c050201c040100019280510024200706804321d020242011039300283030140809038c002000604cd405150242007000180a090801d40610080016061102848090801c1a15030140809039680200118b44c04048400e0d0f0b408090801c5601002f40c05
|30=>0x8001605120101210039300206028101210089bc1a01030154c09083017e01000183a051002420075f03466060281070100c0440c0504840580729804000e0581454090801c1a0602810124a0383416050202420072303402060e8140838080602206028101210162780200058140809080600e4c0697c680b028101210038041813028901210039840006400101210
|31=>0x130101210160342605150101210038fc0019199a808090801c020003015822a100242018088380c1d15024200706800ea05020242007128040083030140809080c4020031019340a020242007000182826020e0202c008180a040481d8e01003140c0510024200700800ce06618101210038040078030284004048400e0d030140809080458401000180ac10484180bf
|32=>0x8000c1d0281070101880400060281012073021002000c95c08090801c7e01001640c051c0400e4900800be670301408090801c02060202420582f00400064381412100393802000302808090801c780d000190026020e02007068181405048403007248000c0a02024200707800f6060202420072f00400062b810121018b2402000c8b4140404840580d000b40c0a
|33=>0x801c7e01002040c05020240e5a0080032330202420071e00400064001012101898402002c9a00a04048400e010017c660602810121003804b2050202420071b804001e168740a04048402201508184c04048400e0d0097c0c1d02810121003804260b350144804048400e0e6501408090801c0200058880a20048400e25008540c26020242093008780c0502024205d
|34=>0x168740809080441a010c88848090801c4a01000380c1d120242007008003c061102420071e80400060281012102e83402003c8180a090801c7a01000180a090801c925c008000c05020240e430e00400670308854090801c1a19400101210038940200168140809080612201002580c0502024205d008000c050484030495c80400190e8101210038fc0200338140809
|35=>0x8000c0a020242018038dc00060281012070e3300200060cc1426020242007068640c1d0202420180899c0c05020240e30008000c050204058070d8040006028b808100386c02003c19c0c05150242007068b466260281012100c0346605020242007658040033028101210038fc02001a02c2805020242018068d00c7a13010121008804f605020242007488040019
|36=>0x481c600100064d404048400e3f008000c1d0281012071800400193501012100393002000ca6008090801c86010017d1206028101210038040cce028101210088340c6a0202420316480400192a01012100397802000701808090801c78010017c68060281012100383468680281012100380400cd03014121003a34020016aa80a0404840b001000180a090801c925e
|37=>0xe81408090806022064381012102c1780200680180a04048400e0d008183a05048400e4e008000c220e8242007420040006050101210039181a000301440040481c380d008b40c9a050101210160001606110801210039840219030a81210038d802000c8183a040484062010019c0c05048400e4e008000c80130a808380801c1a0e1989808090801c1a01198180a04
|38=>0x8005a330509808090801c1a33030881424048400e00030140809080b0de010001828050484058490080102060202420072e00400060289012100387c02000702c0a24150242007008cc0c05020240e60008000c0a130101210039201a950981454090801c0006028102018088681a060299008090387002000c87408090801c8601000cc0c05048400e4e008011606
|39=>0x1981440090801c02060281012073787002000a9880c05020242018000181426020242007128340c850281012102d80400960581408380801c1a9605a000a04048400e0d278180a2a020242007000181426023482007032600a04048403001000180aa6150801210160600c051201012102e8040023458980809080440e01550180a040481c8a0100018d405020240e30
|40=>0x8012c062b81454090801c1a06050980809080b00e4803028080908061a8000301408090819402000307408090801c7801000645a1d02024202c0080018330281012070e004000602810121018b4c02000f014080903870980100018d405048406236008000c140e8101210378040067030101210038f002003c88c1605020242007069e4460b028801210038043c0c
|41=>0x48400e25068000c055301070100c0340c220ea70121003804000602a985438080440e0d338b40a040481c3801001640a090801c9248008000c051202420072080400060282420072980400060288008090801daa014b014121003a104a01000386605048400e84008000c050201c3635010040019058884820048400e013d97c1605020242007008180a4d020400e1b
|42=>0x88340c05021b09407008000c090801c6c610080032330202420072f00400330301440090801c3e014b0190005100242007068180a38080b00e4900800323402024201835804002d1981408090387002000604cae05100242007068780c22048400e36008003c0602824200724804000605010121003b501a13058500a0404840580d0301448090801d40010008c0a04
|43=>0x29b44038080601a0e0289012100389402001981408090801dac01000cc0c1d0281012100c0440c053688070101600502060281012103780400060281012102d89402000307408090801c8c01000780a04048412407008003c061109012100380400894581814040484030000704c4c2a048400e000301408100394802000c818d4090801c6c01000780c05020242018
|44=>0x6e0040019350101210038940200033680a0404841b201000306605100e020070081408090801c5625008000c1d0281012100c04498d803014080903ad002002c8180a0404840b001000d00c140e81012100c0000c051002420075b0340c9402890121003804003302810121003b5c0200031a80a09080c55001002251606050101210038340c224e0242007260040006
|45=>0x1d40c05020240e1c008000c05100242018258b43a04048400e2b00801ba060281012075a00400060281070100392c1a1945828080908060220003014da090812c1a0602810122c0387002000301408070d8081a01001640c05048400e4e008003c04048400e2b2600400060e81012070e2cc02000f01808090801c3e0100064681d020242018038000aae020242007
|46=>0x301408070d8080200508183a04048400e01000180a04038081a01000300a24048400e3f00800260b028101210039601a060282420c05f804008b0305014040484058000301448041c04030110c82d002402024200700818d004048400e37008000c050484058432480400060509848041c0400e06050980838080b00e54028101210038dc0200030140809081612201
|47=>0x198184405100242007068043c2d0281012100383402003a819000502024200700800ce06110101210038340206130101210039781a010301408e00801c0200030140809080458001000181426020e020073d818f40502024201100800180b02b7c1210038040c05020400e1b1a804002d0301408090829c02000c8184c04048405818038043c23030140809038700200
|48=>0x2024200700801027b0301408090801c02003c018ae05020242007068040c220e8a812100383400190588854090801c02000308840090801cc201000306605020242007158040006050980809080b030070301408380801ce60d000380c05718242007008002606028101210039601a002a0180a04048400e0d008000c053689070100380400067081408090801c0200
|49=>0x3868020003014482a020242018088180a04048400e01568006606028101210039840200098180a041c0405807000190e7a0202420072f00400060a010121016178020003014080908045800d0088c0c050202420077200400061102808380801c0019030101210038d80200060181405100242007069640c1d0281012100380400150989808090801c02003a04cae05
|50=>0x801d080100018441d048400e36008000c0a13011cc100c01cb2060281012102180400753a0180a04048400e01001d00c0510024200739804000602811ca100383402003c19c0c05020242007068040c140e81012100c0000c22028a870100383400191982808090801c1a001981814260202420070684c1605120101210038b40c0a028101210160000c05120800810
|51=>0x68042a060e8101210038040019198144004048400e010301408090801c3e0d0080032e802810121003804001903010121003b9c0200338180a04048400e3d008003c830301408090801c020003014da09080457e01000b4260502024202c06800f2780301408090801c0200031e84c04048405807008cc0c05048400e49008000c05020242092038340200030144009
|52=>0x3c8190005100242007008000c053689012100c000ce064001012100380400191a0980809080600e01001e00c57050101210038040033030881404048400e0d000cc0c1402810121016004000602880121003af81a1e0301408090801d0801000180ac15482420075f804000c0581454e60801c0206028a81210038d81a003e04c0a04048400e01000380c05100242007
|53=>0x4001408090801c1a000c84c442a048400e00031e84c0404840300706818f426023982007008301605120a8121003804b206028101210038ac0200168cc3a0502024200700800f6230581408090801c0200098180a24020e02007003a80c05020242007008002606400144804048400e000309808090801cc20d008180a20048400e84068040ce102810121003ba40200
|54=>0x38340023030144004048400e0d19818280502024201806800321302024200735804003303014080908060220d3c82c0a04048400e01000190e05020e0202c0380400062b81408090801c4a01000183a050202420071e804002d098980a0404840220103014482a020242031008000c1d0281012100c0441a1e3381808090801c5601002840c05020242007008006606
|55=>0x30883a04048400e0d008180a2a10024202c038180a24020e02018038000c141301012101603402dd032d40a04048400e01000380c0a100242007008000c05020242007760040006400140809080c40200448542605020242007008000c22028a812100389402002ca2c0c05020242043008006606028101210038f40200030140809080450c01000640c0a02024202c
|56=>0x8003233028a808090801c1a00198184c05150101210038345a060e81408090804402340301408090810c02000321c0a04048400e91008003213028905404048400e000981408090801d1801000180a20020242007230040079238180a04048400e0100018441d120242007008001c0605010121003834001e0307408090801c5601000180ac13688012100c004000b
|57=>0xe8140809080440e010c84cae04048400e01000180a20048400e73068184c040484058072f00432060509008090801c1a003384c0a04048400e0d031f80a2a048400e01000183a050202420071280400060e8140809080c41a01000184405120e02007008000c0502024201103bb402002c8180a090801c920d008005a33028101210038ac0200449640c05020242007
|58=>0x100107010038040c050202420114c80400060281012100c01d2201000180a04048400ef2008000c051202420071b00400f00301408090801c02000315c1404778400e000309808090801d2e01002580c8013010121003804000b0301408090801c6c0d009500c0502024202c0380400060288008ee0801c02000301440040801c4e01002542605020242007008003c06
|59=>0x1606000060a02808380801c000602810121003bd80200168183a050202420580080032330281012101601c0200198184c0502024202c038040c050202420077a00400740301408380801c1a010308808090801c9801000cc0c05100107010038040c0502394202c038040074030880a24048400e01002042a0602810121003804002d059e80a04048403001000183a05
|60=>0x6800ce060281012070e0040033030980a04048403007068180a24020242011600040c05020e0200748034021503028080908060000602a984004048405818008640c2215024200706800ea0602810121003804007b059e80a04048400e01000300c0a0289012100383400064d01012100397802000ca2c0a040484030010004c1622028a81210038000c05368a81210
|61=>0x28101210039041a01000cc0c260289008090801c0233030501404048400e0d000180a04048400eb2008000c0510024201103afc02fe0301408090801c0200033f40a04048400efc008000c140281012107d8040023030140809080b00e0d000180af910024200700801ee060281012100380400060281012100890c020003014da2a7304030000c8cc0a04048403007
|62=>0x8804008a0302808090801c02003a04c0a2a048400e000c8144004048400e25008000c050202420077f80400591981408090801c900100018d405020242007128040006050140838080440e0d060cc0a090801d08010020c0c05100242007420040067032005404048400e01002a80c050202420072c004000e0301448090801c1a01000646605120101210038040006
|63=>0x2c0c140e81012100383402060281012100c2401a1903014080908060220d0c81454090801c5201001e40c05100242007008000c056082420075f804000602a98121003afc02003c82c0a2a0202420070080066064d01408090801c1a010301409000801dea01002840c051501012100380400060e81408090387002000301408380801cb001002240c05020242018
|64=>0x801c020016818140502024202c0c0020206028101210038040067098145404048400e000581408090801c980d0084c0c870281012100383400790f0180a04048400e01000180a040484022071583402590301412101601c92010001930050202420070680400790702c0a04048400e01000d00c1d0281012100c01c00194581408090801c1a013c8180a04048400e0d
|65=>0x501012100c0440034030980a04048402201058180a04828400e010cb600a04048400e01000645a26020242007068045a06438140809080600200032140a200202420070080032061109012100380400060281020070d005bc00030140809080c40200550180a04048400e01001640c050202420182180400060281012101630002000c82c1404048400e0d030140903
|66=>0x81600200448180a04048402207068040c7a13011cc100c01c021916814080908418020003014482a048400e36008000c7a02810121008834be230301408090801c0200030740a04048400e9100800f6064381408090801c02000315c0a2a1002420070682c0a20020242007128040c0554a98400908060020005818440a02024200706bac5a05020242007008003206
|67=>0x801c1a2d031e80a0404840300d000b4260502024201106c200c05020242007008000c055301070100881c1a010c8b40a04048405811008000c0536824202c5f804008b0981408ef080440e000cc1c0a04048400e01000640c571508012100380400890981408090801c0200030880a090801d080d0080072050202420070080016064001408090801c1a06438140809
|68=>0x150242007148040019058145404048400e0d0301408090801c6e01000180a04048400f0b008000d0a02810121003804000602a7008090801c1a01000780c6a02810121003804008f668180a04048400e01001d40c051501012100380400190281012100390c1a01000184c04048400eb6008000c1d028101210038a41a01448193405020242007068041813130140809
|69=>0x778400e010301408090801e180d008640c6a02024200706804000602a98080908060220d44819340a020242007008000c05023b8200730804008b030280a0404840301100064661d02024200700801160602810701003834020b030501404048403000030140809080440e4c068040c057181020070d0040006028a81210038e80075418180a04048400e01000190005
|70=>0x1301408090801df801031a80a24020e020070080116063d0140809080440200058184405120242007068040c05608a8121003afc02000c8183a04048400e36008000d0a8701408090801c020003014081003c3402002c8182805020242011008012c063501408090801c02000301408090801d4a01000b40c0502024202c2f00400060e814080908044b0010602c0a20
|71=>0x48400e01030140821048400e01001e41c060281012100383400190315c4804048400e01000646604048400e2b0080116060281012100c03418060288012100398402000c9646805020242007008001c060281012100380546003c8380c0510024200700800be063d01408090801c0200458182826020242011008180a20020400e1a068061e06028101210038040006
|72=>0x6800b206050140809080600e00030140809082bc0e01000380c1d020242007008000c05020400e35068040c05020400e1b06804000c0981408380801c1a00118b44c04048400e01000cc0c050202420071b004002d032681404048402201000641605020242018038340c05150101210188040062030140809080440e01000b40c0502024201100a3816062b8284004
|73=>0x28101210038040006028101210038041e0006018ae05120242007008010606028107010038040083032000a04048400e01000645a0502024202c0680400064a01408090801c1a01000184c05020242011678040c050202420072000400061109808380801c1a014b0180a04048400e3c008011606050140809080440e0d0c82c0a24020242007008180a04048400e86
|74=>0x30140809080b00e2b0080032590281012100881c0200030140809080b030c000800f2060289008090801c02003c0181420020242007008000d0a0281012107d81c02000301408090801c7e0d008000c0a0281012100c01c9000418184405120242007008001c0b028a8121003804000602810124a038040019058280809080600e000301408090801c780d008014806
|75=>0x2024201808834a80602810121003804001e1681408090801c02003a99c0c05020242007008000c0a028101210038a41a590301408090801cb801000180a04080b00e1a0680400190581408df048400e010ca2c4c0404840220700818f4050202420072400400670281012100393002000301408090801d320d00019c405020242007068000c05608a80809080602200
|76=>0x780c0502024200721804000602811ca1003804000b032000a2402024200700a580c05048400e84008000c050484058072483402000c818d424020242007008000cda0281012100380400330281012100393002000f0180a040481c380d008000c05120101210038ac020019818281d0202420070080016060281070100c01c1a13031a80a04048400e0d00018f405
|77=>0xe81408090801c020033818442a048400e01000180a04888400e01000180a04048400e1f008006606028101210039cc1a00880184c04048400e01000180ac1020e0202c0380400060281012104901c02003a8cc0c05020242007008000c05530a84009080600034030140809080600e8e00030260510024200706818d480028101210188040075030740a04048400e01
|78=>0x23034020003014da2004840580d0097c68060281012100380400060a0980809080b002064281408090801c4a01000180a04048400eab008000c6a028901210038d802003c19c0c05150242007008000c1d0281012100c04418063501448090801c02001a02c2805020242018008000c05020e020073583402340301408090801cb801000180a04048400f1300801fc06
|79=>0x8180a04084540e35008000cc302810121003804000602a984804048403000278180a04048400e01000180a240202420071f804001e030144004048400e0d00aa80c1d0281012100380400060a01012100c17802002c8180a090801c9201000199c0502024201100800ea063501408090801c0200030144804048400e3c008000c80130101210038340c05020242007
|80=>0x20242007008184424048400e61008002a060281012101604402000301408100c04434010004c0c6a0289008090801c0006400101210039840200030500a04048405848008022c06028101210038040033030880a24048400e01000180a040484022072e00400061301408090801c900d008540c2602024200706804180b0289040090801c02740315c0a04048400e0d
|81=>0x3d0140838080600e0d000640a04048400e250680400063501408380801c0200030980a04048400e25068040c05020e020075f804000602890121003a1002000c81808090801cd60d00864660502024200742004000e0301448090801c020005818140502024202c0383432831981408090801c0200030140809082b00e010020d2c06028242007420040033030740a20
|82=>0x48400e010002c0c05020242007398340c260281012101601c90010f0306605020242007008012a06028101210038340206400985404048400e0d03014da041c040220d008cc0c050202420072c0040033030144004048400e2b008780c0502024200737804000602810121003c6002001a0182805020242018068000c2205081de10038011406028a81210038040006
|83=>0x301408090801c5e010020c66060281070100380400330301408090801c8001000180a04048400e6f06804000611014121003a1002000713c0c050202420070080016061101454090801c1a33030140809082bc0e01000180a6d1208012100c0000c05120101210039180200060cc0a20048400e0d008640d1902024200700801ba060281012100380400791182c0a04
|84=>0x801c02004181408090801c4a01000640c6a02024200700800b2340281012100392002002c8180a09080600e49008000c0502024201808b783c671681408090801c02000c8d00a04048403007068000c0502024202c089600200030140809082bc0e2b008017a060281012100380400d10301408090801c1a01002580c57028a81210038040096030980a04048400e0d
|85=>0x2b040809080b180010003026570288012100380400066d0163404048400e01000640a240202420071280400190309808090801c02510302808090801da80100258160502024200706a0c0c051202420074200400dd6c0180a04048400e01000d00c0a1301012100c01c00064d02808090806022000f0b46605020242007008000c0502024201808a383c2d0e8140809
|86=>0x48400e3c0080068060281070100c01c1a00030154c041c0400e0d008180a041c0400e43008000c056081070100380400060281020070d80400330301408090801c3e010002c0c57028a840090801c0296032000a20048400e01000181426020242007288180a090801c920d008005a061301408090824c02191687408090801c1a01000183a05020242092038040006
|87=>0x1601c3401000cc0a04048400e48008000c055301012100c034320602024200778804000602a985409080440e0d2c8cc0c05048400e490080018060509808090801c1a2d028101210038ac1a01000180a04048400f1d0680506060e81408090801c02000301408090801d9601000180a04048400e3f008000c050202420078d8040096030980a2a020242007068180a04
|88=>0x383506063501408090801c0200030140809082480e4c008002a330281012100383402000301552200484022010301412101601c92010002c0c220289054090801c021e03014080903870020003014da2a048420c00418180a04048400e2b008000c0a1301012101601c1a89458181404048400e01002840c050202420073080400060a0140838080441a01030140810
|89=>0x1c0403007068180a2002024200790804183302810701003804000602810701003978020003014da2004840300d03014091f0801c020003014480404840301106b280c05020242007008000c056081012100380400060281012070e03402000301440090801d6c01000b40c0a130101210038340c6a0e81408380801c02001981408090801c4a01000181426120101210
|90=>0x3014da090812c020003014083808060220d168cc0a041c0400e01000180a6d12024202c008000c1402810701016004001e030140809080b00e0100018281d02024202c008010633028101210038940200030284c041c0400e0d0c818d41d020242007008003205020242007128040006028107010039840200030284c040484030110301409220801c0200030144004
|91=>0x48400e0d00800322d0e81012100380400064c01408090801c8601000780c1d0281012070e004000602810121003c9402000301409230801c02003a8780c05020242007008003c050202420072600400060e81408090801c7e01000180a04048400e660080142060281012100383402000301408090801cde0100018d404048400e61008002a060e8101210038340200
|92=>0x394400061301408380801c022d030740a04048400e0d00800f0062b81408090801c02000321c0a04048402207008000c05020240e1c00800ea060289008090801c0200418180a04048400e61008000c051508012100c04542060289008090801c0200063340a04048400e01000183a05020240e1c0680400060281012100392c1a061143808090801c02003a8180a04
|93=>0x301408090801c0200030880a041c0400e01000640c0a10010121003804002d058280a04048400e01000184c0502024202c0c01c020643a680a04048400e01001e0ce060281012100380400061107408090801c02000301582a6020242007008001c1302810121003804000602811de1003ae00200030144804048402207008181405100101210038340c0a028101210
|94=>0x380400060a02808e60801c0200031a80a24020242007068040006028101210038d80200030980a04730403007008300c05150242007068003233028101210038340200198184c0502024200706804462d0281012100380401270301408090801c0200070180a20048400e01000180a04048400f260680426064d01408090801c0200030154c2002024201800800b233
|95=>0x20242007008025206028101210038040006029b454090801c1a000c8180a0404840580706804000602b040809080b0220700800260b02811cc10038040c056088008090801c02000301408090801dce01000300c0a028101210038340006400145404730400e01000180a046f8242011038040c05548a808e60801c0200060181405100242007008000d28028101210
|96=>0x300c05120242007008000c0502024200700c48008b030140809080b00e01000180a04048400e840680400063d0980809080600e0100018140502024202c0383400830301408090801c1a01000180a04048400ebe068001c060281012100383402003d8180a04048400e01000180aa610010121003834020602880121003af802000301408ef0801cd601004a80c05
|97=>0x29b448090801c0200168181405020242007068000c051002420073980400670981408090801c0200030145420048403007000182805020e02007008000c05020242007960040006050144804048400e0d00018281d020242007008000c05120a80809080440e010315c0a04778400e010004c0c05150801210038000c05020242007958040023030144004048400e01
|98=>0x800322d13010121003804001e030740a04048400e010004c0c0512010121003800328b02810121003804000602b040809080b00e0d008003c670301408090801c0200058184405100242007008cc0c14028101210038340200198180a04048402207068040c22028a8121003834000c03015be090801c0200030740a04048402207068040c05020242007398340006
|99=>0x28901210038040006029b408ef08044020003014080908061200100018280a020242018000640c0502024201808804000c03014482a048400e01000180a200202420077d0040089030140809080440e01000300c0515398200700800320b0281012100383402060281012100881d7e01002580c22028a81210038040006438140809080b00e01000180a6d6f8242007
|100=>0x804402003a0180a04048400e0d008cc0c05100101210038040c57028a840090801c0200740180a04048400e01000180a6d120a812100380400064d01408ef080440e01000181405020e02007068000c05024bc2007008000c05608800809080600e0100064160a020242007008000c0597010121003804000602810121003cb40200448193405020242007008000c22
|101=>0x30280a04048402207068180a2a02024202c0c01c0013030145404730400e000301440040801c34010001844056f82420070080018131301408090801c02000c8180a04048402207068045a13028101210088040006028101210038ac1a01000b40c05023bc20110080016062b8144004048400e01058190005020242007008000c050202420078600400063d0140809
|102=>0x8000c055301012100c04402000c81408090801d7c01000180a2a023982018038000c05020400e35008003206400a808090801c0200060183a05020242007008000c050202420072c00400063501408090801c1a01000180a04048400ebf06804001303014482a020242007000641605150101210038040059030140809080b02207008000c05100101210039840200
|103=>0x801c1a01000302605023bc2007000180aa6023bc2007008011606050140809080440e010022c0c05020242018008003213028a808090801c0033030140809080b00e01000300c80028a8121003804000611014482a048400e01000183a0502024202c03804008303014482a020242007008000c1d028101210038d80200030144004048400e016d8180b30020242007
|104=>0x180a04048400e018b8000c050202420079980400191981408090801c02001a018f405020242007008005a0b02811de1003804008b0301408090801c1a01030140809080b00ebf008000c0502024200700c90000602810121003cc80200168183a05020242007008000d0e0281012100380400060288008090801c4a01004c40c05020242007008010633030140809
|105=>0x30158204048400e0d0080018130281012100383401070301408090801c02000604c0a20048400e01000b42605023bc2007000180a0404841f607008000c050202420a70380400230301408090801c1a00031e80a04048403011008000c6a0289008090801c02000c8180a04048400e9300801b0060281012100380400060501408090801c5201000180a6d150242018
|106=>0x801c028e000645a0502024201100800b2340301408090801c0200070181404048400e01000180a6d02024202c06804007c0301408090801c0200032004c04048400e010002c0c0a0288008090801c02061101408090801c02db000183a05020e020070080106060281012100380400061109808090801c1a010301408090801c860d0080032060281012101601c0200
|107=>0x48400e01000180a04048400f14008003206028905404048400e010002c0c050237c121003804b2060281012100881c0200030166804048400e01000183a050202420072c0040006350740a04048400e0d008005a06028101210160340200030158204048405807008000c055301012101601c0200030144004048400e0128a242a0602810121003804000c030140809
|108=>0x281012100c01c1a00031e80a04730400e0100018d405020242007008000c050202420073083402000301408090801d7e01000180a040801c340d008000c7a0281012101601c02000301408090801c56010002c0c22028a8121003804000c1981408090801c1a01000180a04048400e5e06804000b0301408090801ce601000180a2002024202c038340206400985404
|109=>0x80600200060181426020242007008000c0510010701003834020602810121003bc402004b0184c0515010121003804000602811a410038040083198180a04048400e01000180a04730400f36008000c05024d42007008000c0502024202c039780200168cc0a04048400e0d008012c0b0281012100380400060a0140809080b01a010002c0c05023982018038040c7a
|110=>0xe81408090801c02000982c0a20020242007008180a6d020e020070680400060281012100380608001681814260202420070080068060281012100c01c1a00030154c04048400e0d008780c0502024200706804000602b0408090801c0200060180a041c0400e0d00800322d028101210038340200058181405020242007068180a0404840580724004000602a980809
|111=>0x392c02000321c0a0404840580706804001e030740a04048400e0d008000c051201012101601c020003014080908060220d030284c04048400e0d0301408090801cc201003ac0c05020242007008000c051001012100c01c1a060281012100397802000301408090801e6e01000cc0c0502024200715804002d0301408380801c1a01000180a6d100242018008006606
|112=>0x1601c0200098180a04048400e0d000180a04048400e93008000c053681012100c004000b030144004048400e01030145404048400e0d000180a2a100242007008000c05020242007930040013030140809080440e01000182805023982007008000c053681070100380400060281070101601c02000f0180a04048400e01000640c0502024200700b780006028101210
|113=>0xc00400060281070100380400064001408090801c0200030155204048400e010002c0c22028101210038040006028905404048400e0100018440a020242007008000c0515011cc100380400150301408090801c02000c82c0a04048400e01000640c22020242007008005a060281012100c004000602a984004048400e01002580c05150101210038040006028101210
|114=>0x30145404048403007000180a04048400ebe008000c050202420075c00400190301408090801c1a01000181405020242011038040006400145404048400e010002c0c140281012100380400060a02808090801c0200030280a04778400e000c8180a0404840220700800e8060281012100380400060e81408090801c1a010004c0c05023982007008000c14028101210
|115=>0x20242007008000c051001012100c01c0200030140810038680200168180a04048400e0d008000c05368101210038340200030140809080b00e0d008001806028101210038340200168180a04778400e01000180a6d023bc20070080016060501408090801c02000301408090801c02de000180a04048400e016d8000c1d0281012100380400670301408090801c0200
|116=>0x180a04048400e01000180a04048400e0d008003206028101210038040006028a808090801c0200058180a04048400e01000b40c05020242007008000c05023982007008000c0536810121003804000c0301408090801c02000301408380801c1a01000181426
|_=>0
def sO:Nat→Nat→Nat
|6,0=>0x1a7004dc00d6001d80007
|7,0=>0x84202097080601f9807c601e98078601d980749c1ca8070a01ba806ca01aa8068dc19b8064e018b8060e017b805ce016b8058e015b8054e014b8050e013b804ce012c70495c11d80456010d8041600fe703da00ee8039a00de8035dc0d07032200c0802e200b0802a200a0802620090802220080801e20070801a20060801620050801220040800e20031700a600218
|7,1=>0xdae036380d6e035380d2e034380cf1c33480cb5c32580c76031580c36030580bf602f580bb602e580b7602d670b3dc2c780afe02b780abe02a870a82029880a42028880a020278809c20268809820258809420248809020238808c202288088202188
|8,0=>0x16764594916320583915ea4572815a645609155e454e91516453c914ce452a9148645189143e4507813fa44f6813b644e58137604d49132e44c2912e644b1812a604a09125e448f8121a447d911d2446c8118e445a911464448910fe4436910ba04259107244139102a440280fea03f190fa243df90f5a43cd90f1243bb90eca43a990e82439790e3a438590df243739
|8,1=>0x1f3647c491ef207b391eaa47a191e62478f91e1e077e91dd6476c91d92075b91d4e074a91d06473891cbe472691c76471491c2e470381bea46f191ba246df91b5a46cd91b1606bc91ace46ab81a8e069b81a4a468991a024678819be46678197a4655919360644918ee4632918a646209186206108181e45fe917da05ed9179245db9174e05ca9170645b8916be45a69
|8,2=>0x281a49fd927d249eb9278e09db8274a49c99270249b7926ba49a59267249939262a4981925e24970825a2095f9255a494d92512493b924ca49299248249179243a4905923f248f3923aa48e19236248cf9231a48be822d648ac9228e489a922464888921fe4876921b648649216e4852921264840920de482e9209a081d92052480b9200e07fa91fc647e891f7e47d69
|8,3=>0x30ee4c32930a64c209305e4c0e930164bfd82fd24beb92f8e0bda92f464bc982f024bb792eba4ba592e724b9392e2e0b8292de64b7272da64b6092d620b4f92d1a4b3d92cd24b2b92c8a4b1992c424b0882bfe4af692bb64ae492b6e4ad382b2a4ac192ae24aaf92a9a4a9d92a524a8b92a0a4a79929c24a679297e0a56929364a44928ee4a32928a64a20928620a0f9
|8,4=>0x39c64e689397e4e578393a4e45938f24e34838ae4e247386e4e129382a0e01937e24df08379e4dde937564dcc9370e4dbb836ca4da9936824d979363a4d86835f64d74935b20d639356a4d51935224d3f934da4d2d934924d1b9344a4d09934024cf7933ba4ce5933724cd39332a4cc1932e24caf9329a4c9d932524c8b9320a4c79931c24c688317e4c56931364c449
|8,5=>0x428650989423e5087841fa5075941b250639416a5051941261040940de502f8409a501e84056500c9400e4ffa93fc64fe893f7e4fd693f364fc493eee4fb383eae0fa293e664f9093e1e4f7e93dd64f6c93d8e4f5a93d4a0f4993d060f3a73cc64f2983c824f1793c3a4f0593bf24ef393bae0ee293b6a0ed373b2a4ec193ae24eaf93a9a4e9d93a524e8c83a0e4e7a9
|8,6=>0x4b7a52d594b3252c394aea52b194aa2529f94a5a528d94a12527b949ca52699498252579493a5246848f65234948ae52229486652109481e51fe947d651ec9478e51db8474a51c99470251b7946ba51a59467251939462a5181945e2516f9459a515d94552514b9450a5139944c611289447e5116944365104943ee50f2943a650e09435e50ce9431650bc942ce50aa9
|8,7=>0x5456150c9540e54fa953ca14e99538254d79533a54c5952f614b4952ae54a29526654909521e547e951d6546c95192145c8514e544a951065438950be54269507654149502e540294fe653f094f9e53de94f5653cd84f1253bb94ed1d3ab94e8a539994e42538794dfa537594db2536394d6a535194d22533f94cda532d94c96131d84c52530b94c0a52f994bc252e79
|8,8=>0x5d12573c85cce572a95c86571985c46170895bfe56f695bbdd6e695b7656d585b3256c575af256b395aaa56a195a62568f95a1a567d959d2566b9598e165a959465648958fe5636958ba16259587256139582a5601957e615f09579e55de9575a15cd9571255bb956ca55a9956825598856421587955fa5576855ba15659557255539552a5541954e2552f9549a551d9
|8,9=>0x5de2176f95d9e175e95d56574d8
|9,0=>0x671a99bca66ce59aa9668299979663a5984a65ee5972965aa19619655e994da6512593aa64ca19299648259179643e1906963f298f3963aa58e0a635e58cda631258bb962c698a9862825897962369884961ea9870a619a985d96152584b961069838960be5826960729812a6026580095fda97eca5f8a97d995f4257c885efe57b875eba97a685e76579495e2a9780a
|9,1=>0x707a5c159702e9c01a6fde9bef86f9a5bdd96f4e9bca96f065bb896eba9ba4a6e6a9b90a6e1e5b7da6dd25b6aa6d865b5896d3e5b45a6cee9b31a6ca25b1ea6c565b0ba6c0a5af8a6bc21ae796b7e1ad696b329ac2a6ae29aaf96a9a5a9ca6a4e5a8a96a029a76a69ba1a659696e9a51a691e9a3da68d61a2ba68869a19868425a07967fa59f5967b259e2a676659d09
|9,2=>0x79d65e6ba798a5e59979461e47a78fa5e35978ae9e21a78625e0f9781a5dfd977d61dec9778a9dd8a773a9dc5976f25db3976aa5da19765e9d8da760e9d7a975c65d67a757a5d55975325d44874ee5d31a749e9d1da74525d0b9740a5cf8a73be5ce78737a5cd4a73321cc3972e69cafa729a5c9ca724a9c88a71fa9c74a71aa9c61971625c4ea71129c3b970c69c27a
|9,3=>0x8332a0c2a82e660b0982a2209f98256a08c98212207c881caa06998182605798136a043a80e6a02fa8096a01ba8046a00897ffe5ff5a7fb61fe497f6e5fd297f265fc097eda9faca7e8e5f99a7e425f8797df69f7497db21f62a7d665f4fa7d169f3c97cce5f29a7c7e9f15a7c2e9f01a7bde9eeda7b8e9eda97b465ec897afa9eb597aae9ea297a665e9097a221e7ea
|9,4=>0x8c82a31798c36a30498bf222f398ba6a2e098b5aa2cd98b0ea2ba98ac662a898a7aa29598a362283a89e6a2709899e625e98956624ba8906a237a88b6a223a886a6210a881aa1fd987cea1eb8878a61d8a873aa1c5986f261b3986a6a1a09865aa18e88616617c985caa169985826156a853a2144a84eaa130a849e611e98452a10b9840a60f9983c260e88837e60d69
|9,5=>0x9602a576a95b2a562a9562a54ea9512a53aa94c2a526a94766515894326502a93e664f09939aa4dd9934ea4c9a92fea4b6992b664a49926aa490a921e647e991d2a46b9918a645a891466448990fe6435a90aea42299066640fa901a63fca8fce63e9a8f7ea3d698f3a23c4a8eeaa3b0a8e9aa39ca8e4e638a98e06637898dbaa364a8d6aa350a8d1aa33ca8cd2232aa
|9,6=>0x9f6e67d1a9f1ea7bda9ed267ab99e8a6798a9e3aa78689df2a77399da6a76189d5ea74e99d12a73aa9cca2728a9c7aa71599c2ea70299be2a6ef99b9e26de99b52a6cb99b06a6b899abaa6a599a6ea69389a26a67fa99d6a66d8998ea65a99942a646a98f66634998aaa620a985aa60d9980ea5fa997c665e89977aa5d59972ea5c1a96e265af99696a59c9964e658a9
|9,7=>0xa8eaaa30aa89aaa1d9a84eaa09aa80269f79a7b6a9e3aa766a9d09a71aa9bd9a6cea9aa9a682a9979a63a69859a5eea9729a5a2a95eaa556694c9a50e6939aa4bea925aa4726912aa42a29019a3dea8edaa39268daaa34668c89a2fe68b5aa2b268a2aa262a88f9a216a87baa1ca6868aa17e6855aa1326842aa0e6682faa096a81baa04a680999ffea7f699fb667e49
|9,8=>0xb242ac879b1fa6c74ab1aaac60ab1622c4f9b116ac3c9b0d22c2aab0866c17ab036ac049afee6bf29afaa2be19af626bceaaf166bbbaaeca6ba8aae7e6b969ae366b83aadea6b70aad9e6b5e9ad566b4d8ad0eab39aacbeab278ac7a6b159ac2eab01aabdeaaedaab8eaad9aab426ac79aafe2ab5aaaaeaaa1aaa626a8eaaa1a2a7caa9ce6a6a9a982aa56aa93a2a44a
|9,9=>0x2e4e8b912ae3aab8ca2e28ab87e6e15ab8362e049b7eaadf19b79eadddab7526dcc8b70aadb99b6beada69b672ad939b62a6d80ab5e22d708b59e6d5e9b5566d4bab50a6d38ab4c22d26ab4766d149b4322d048b3ee6cf29b3a66ce09b3622cd08b31e6cbe9b2d66cac9b28e6c9a9
|10,0=>0xc2ba70a4ac26e70929c226707fac1da706d9c18eb059ac13eb045ac0eeb0329c0a2b01f9c056b00c9c00e6ffa9bfc66fe89bf76efd2bbf2a2fc0abede6fadabe8eaf9a9be42af86abdf66f749bda6ef609bd5e6f4e9bd12af3aabcc66f289bc7e6f169bc32af02abbe2aeef9bb96aedbabb46aec7abaf6aeb49baaaaea19ba626e8f9ba1a6e7d9b9d62e6abb982ae56a
|10,1=>0xcc2af300acbde72edacb9272db9cb4a72c8acafab2b59caaeb2a29ca62b28eaca16727c9c9ce726a9c982b2579c936b243ac8ea72328c89ef21e9c856720c9c80ab1f99c7c271e79c77e31d5ac72eb1c1ac6deb1ae9c696719bac646b187ac5fa71759c5aeb1629c566714ebc512b13b9c4c2f126ac47671149c42ab1019c3e270eeac39670dc9c34e70ca9c30670b7a
|10,2=>0xd5a2b55f9d556b54c9d50e7539ad4beb5269d47675149d42ab500ad3dab4ed9d39274db9d34e34ca9d30674b89d2bab4a4ad26ab4919d21eb47f8d1da746d9d192745aad14674489d0fab4359d0b27422ad066740fad01a73fbbcfce33ea9cf7ef3d69cf3673c3acee6b3aface96b39abce42b3879cdfa7374acdae73629cd6a3350acd1ab33d9ccceb329acc7eb315a
|10,3=>0xdf3237c39deea77b19dea2779f9de56b78bade0a7778addbe7765add727752add22b73f9dcd6b72c9dc8ab718adc3e7705adbf276f2adba676e09db56f6cd8db0eb6ba9daca36a8ada7ab6959da2eb6829d9e2b66f9d99a765cad94e764a9d902b6379d8b6b623ad866b60fad816b5fbad7ca75e7bd77a75d4ad72e75c1ad6daf5acad68ab598ad63e7585ad5eeb5729
|10,4=>0x38219e062780f9e016b7fc9dfc6f7e6bdf72b7d48
|11,0=>0xe80e79fa9e7c2b9e88e77ab9d4ae72ab9c0ae6de79ae9e692b99b9e64a79899e60279779e5ba79659e56eb951ae51eb93dae4d2792c8e48ab9199e43eb9069e3f678f58e3b278e39e366b8cfae31a78bd9e2d278ab9e28a78999e23eb885ae1f278739e1aa78619e162784f9e11a783d9e0ceb82a9
|12,0=>0xe92a7a419e8e27a2f9e89a7a1e8e8567a0c9
|13,0=>0x3a538
|_,_=>0
def wAt:=mkWire dB 312 256 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 9 18
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 11 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 3000009 zs)
def oP:Nat→Nat
|0=>0x50580503001038050806e0d035000050c82703015038050080103001030921000502835028110203503001030050000503035008010200502001008010203500801110190281102035028050000500801118800200109815028110300503035008010f043030750283500801038010806e0d035000050c827030150380103005020590a8340a0190281d000050803d030010280507034060150301100005
|1=>0xc82702819030010803d07034060150301100801070341101900005028010281102005020350e83302835000050f053030751300502801038050380102835028190303500801028011184403801050190301d028050283500005038050c81d02819030350080102801030050a8340a0190281d0000504835030e90c080020010380500005038350c81d030350080103835008010981d03801030050301502835
|2=>0x30010280503805028050803d07034060150301100005028190980103005028810206d1a8050d0010c827028192a013038350000502831030350203500005028050814a0d1450c8270281903836008010e81b0283502819008010806e1a8050d0010c827048350812d150440380102005000050c81d038010300503015028350000515001020050203500801038010d035008010c82703015020010209d0d005
|3=>0x3001020010806e1a8050d0010c827030150c80103835000050301d05861030012c813030b1088050380103005020590a8340a0190281d00005020010383d070340601503011008010f043028cd09801030053201f020710f043008012c813030b1038350000502801038050a8340a0190281d000052c813030b1038350280100005028920203502811000050283500005030350301502835000050a16605861
|4=>0x801029dd338aa0282d0300102005110190283503035008013a803051d1060010301102805350193501f0289102035008010080103081028aa02005020010284d038350300503001008010806e1a8050d0010c827028190280503035020350080103011028010483515044038010201d02005000050f0430c835028190380100801049290812d150440380102005000050284603061038013501f0508102805
|5=>0x380502805008010315d028810200103805038010307502835008013a813051d10600103011028053f81f3f005028a503082020010080103005031ad02846038013a81f2b84d02881030053d8033d0190286103805028b2038350000502805020010281103035008010700100005070050c811028193a8070f011028cd03035000051988b0281103035008010e8330283503011008010c81d030150383502801
|6=>0x20010c805028190203503001008010e8130c8a902001028190300102005030813501b028911000502001168750e81f02835008010f01703131030760283500801030011181d09815030050000502882030350200102005000050303500005028a9020050200102835058110300103005000054001900005028a90200502001408430f01d0307502835008011100502811130190280100801030150306102801
|7=>0x170030209d0d0050c827028190f013118010501902805148050308202001028b103835030010300500005008010c862028190380503801028a903081030050200502001030050284602819038010080140807059e90a0050281d03001118800200109815028110300506029030010000503011028054281f0289503092150010f013028cd03035008010c8050301d02801028190380102831030111000503005
|8=>0x2921088050380140813448050a8010c81d030150581d03001030150283500801118010383503035000053501f0289102035000050f0430f017338050581503001070030c81103005030150200508805038013c803050310301102805110190080102805028110200102835038050281903801008011988b02811030350000503005008010a8010c81d03015008010d0010c8270301502801030920203500005
|9=>0x1181d098150300540843168750301d0283500801088070301d028010281903801030150307602835008010393133805030b10321e028b10383500801020053a01503081020010080104835008010380508813038014781316a390301d02836008013501f40001028a9020053a807110cd02811030350000500801030053381f05815030013c80305031030110280505081028050203500801030150281103001
|10=>0xc827028191301902811020350280100801058050300102881020010281903001020051181f03029028050280100801030a900801028a902801020050283503835008010281d03001048353501f0e811028350080100801020010d0050c8270281903209028820300502001008011981302966030b10c0010380513011028190300502801008010f0170307502835008010080102005028a503082020013d803
|11=>0x30013c007070010308902811030720f0431180105019028050a00503801048350281d00801021310307602835008010483502811020350280500005029252c813030b1038350080102005028810483502001008010f0430307502835008010c89202819020350000502845038050303503801008010300100801028610301d0380500801038013d01b02861038052c8132c81f4580503045038011a8050d001
|12=>0x38050301d030050483503801008010283503035008010309202035030350080102a2d2c813458050304503801028b23c0070c88103015020013a817051d10600103011028053d0190a0050281d030010283109801030110300502001020fe3501b028911000502001028b203015038350000519817038050303503801008010290d1981f030350000503015008010304503801038050283503805008010281d
|13=>0x383503035000050303503835028010280500005508130318502892100050200119817008010e81103001028350080103801030610283603805000050200502835008010e833028350301100801028a9020050300503011028010c8b2038350283500801168150301d0383503005000050380500801028190301d028012a01f03179028b208805038014381b1306103061028010380502819028b20c0010301d
|14=>0xc811030150200552035070370601503011008014081309a690a0010281d030054001903001028a9020050283500801028cd2c8171981d0303500801038050c845028190380100801408034480502a2d0304503801020050e81b000054381f0504502805038010304503805030150280503801448070a801030510281d0300502a8d070360601503011008010282d028a903001020053d8030c8610301503805
|15=>0x288103015020010283500005030110300102005028921000502001030110300102001070050308902811030010300502892020350080102005030820301502001008014001900005028a902005020010380508811048350380100801030450e81f0308902005028110303500005020010209d0d0050c82702819458054480702a2d030450380140019028a9030010200502a4a0393102835008010300515001
|16=>0x30820200104835030810300502001008010203502811030010300500005038810c0010c011020010380503005168010301d02835008013501f028910080103015028111500103001020050806e138010d0050c8270301503001118800284d0300502001028011981f008010700503089028110300103035020350280102805000050300103835030150283500801000050209d0d0050c827028190300110005
|17=>0xf0430307502835008013c803118110c80503015038050300103015028350080103805038010307602835008010f043118111180105019028052c8132c81b1981d03035008013d803028d10306103805008010383502801000050281d03005020ad028ce000053a843051d10600103011028050c81d02819030350080103ab50a8360a0190281d008010301d030b2038350000502921030b2008013f005028a5
|18=>0x3091020350080103001030050288102001020053d8031181d098150300503801028ce00801408433d801098510281d0300503801028350281903035008010f01f198151981d0303500801030010703406015030110080103011030010288110005020014d019028450280503805038011001d0c01102001038053a8070c8910281902035000050581d030010483503805000050281103005020350283500005
|19=>0x28a903001020054081309a690a0010281d030051981502001030350080100801030150288102001020050283500801028720f0430307502835008014d019008010a0010281d03005031aa0e81102835008015900511846030290280503801030e90c08002001038050000558005020d50d0010c827028193a81f3c0051303103011028010980102811030050301502005028351985303035008010281102a0e
|20=>0x80103082028a902005020011981302811000052c81b2c81f0306103805028190290d1981f0303500801028cd03035008012a01303179028b2038350080103092100050c8110301502001418133a005030810200102846038010080103076050010281d02805038014a04302a111981303035008010c811020350281903035008012c8132c81f030b10c00103805008010280103202028a9020050320115001
|21=>0x1301d0280102805000053a8133c005070010c811028190383500801038010d035008010c827030154081f3d801028d10306103805030460e81f0289102035030010300500005028010301d0880502805038010f043030750080102819020050283502001008013d803031e93d00102861038053a8134002d028a903001020052c8131981d008014081b0f01d0307502835008010200503082048350200100801
|22=>0xf08b3380513019028010803d0703406015030110080104835028b2038350280100801031aa028910309102035008013501b0289115001020053a81b3c005070010c81102819138010d0050c827028192c81345805030450383503015028010300500005030010289102035008010283503035008011981f000051981f030350280102805000050301d030b203835008010f013198151981103035008014d019
|23=>0x3805030460483503801008010200100005070050c81102819028011981302005028350281104835000053d8033d019028610380555043031610e81f0283500801030050288110005020010281902811198130303500801030152c813030b10383500801060150300500801030110280103801028610483503805000050501d00801030450280503801030150e81f028350080102819130a9028010300502005
|24=>0xa8010c81d030150c80500801028190301d02801032e941005028820280500005028450301d038010289103011150010300102005110ce02835030350080103005020010483503011008013a8434002d028a9030010301d028b20383500005448070c845028190380100801118800284d030050200102835008010312d150440200102005038010f01b0f017338050581503001030013501f0e8110283500801
|25=>0x483503801008012a01f0317903835008010380503076000053d803028d103061038050289203011100050300502001028a90c89215001020051a0152c8171a001030610380504835028920203502801008012c81309845038010281d0300502001070340601503011008010806e1a8050d0010c82703015198130e81b028350281900801130a902801030050200503001028110203502805000054084344805
|26=>0x48350281d00801640430c94502819038360080102319118830284d030050200102b11338620309902801038050315d0000502881028050200116a1e0301d05045028050380102835008010f01f0c83502819008016081f608130881103801030aa0200102835020050000504835038050303503801008010c811030010301502005000050812d150440380102005000050c8920281902035008010380502835
|27=>0x80141817060350301100005028a9028010483502005000052c813058610300102805038050280507034060150301100005438173d00102861038053501f2b805020010383500005028190301d028050301d038350280102805000050289115001020050289102035028190303500801038010200502001038050c81102835030150200500005030920c8910203500801448074d01902845038010383502801
|28=>0x408030a0cd058050281d030010c8b2030b1038350080103075028350080102892020350080140803438190e81d028350080103001028911000503005020010328d07036060150301100801030921000502811020010a01908807038010281d028013a81f0f011028cd03035008013501f048350e811028352b8050288102001168350301d0483500801408030f01d3380505815030010e81f028b20383502835
|29=>0x2819038010301d028350080102819028110309202035008010c811020350283500801028cd03035008013a81f110cd0281103035008010f0131181111801050190280513019000050280102811020051500102005130610280103805039262c813030b10c0010e81102835008013a81b0f0113380513019028014084309a690a0010281d030054181719811058050301503001350173501f40001028a902005
|30=>0x8010c8b20c0010281903805038720f043030750283500801028050303500801030110280105001038050301502805038013a8430f011338051301902801138010209d0d0050c8270281900801338110282d030010200503805028010301d03035008014c01b0290d030350080103035031aa0e81102835008010281d0080103061030010380502861028010306103805038010321e031e93d0010286103805
|31=>0x301d0380103001028110289210005020013501f0e8110283500801408130f01d338050581503001028a9028010483502005000050c81102801028190303500801031aa0508102805020010307613005028011981f03035008013d8030a8050a8010c81d03015038010080102b3d03062038053501f020350080103179028b203835008013a8173c005070010c811028193d803028d103061038050e81f02835
|32=>0x2c813030b103835008014081709a690a0010281d03005020f203091020350080103001150010c8110301502005030b2038350280102805000050320902882030050200502001008010c827028190380103805020710f043028cd030350080103035008010500102805030450380103805688010a8370a0190281d0080103035008010c8920301502035000050f0430c835030150200100801088050280502845
|33=>0x28190309202035028010280500005028950309202035008010483509811030050300100801030a900005028a903001020053a8074002d028a9030010200502805028010494503836008010290d030b10c0010c0011001d03805020010284d03045030050380155043031610e81f02835008013a843031a90080102805028010301d030350080103035028110203502805000050f01f03075038350283500801
|34=>0x38054d01b02845038010383d0703406015030110080102835418170603503011008010301d038350301502835008010f043028cd03035008013501f028910203500801030760f043030750283500801350133501f0289102035008010f01f0307502835008013a8170f01133805130190280100801118110c805030150300103001118110284d0300502001028cd09801030110300502001448070a8010c81d
|35=>0x4835038010f0433380505815030012c81b2c813030b10383500801020350e83302835008012a01303179028b2038350080163001118830284d0300502001418134181b030a90200511019028111981303035008010806e1a8050d0010c8270301510005028110300103015020013d803098510281d030050206d1a8050d0010c827028191100100801030a902811020050280502801030b2038350080102805
|36=>0xe813028920203502835008010383500801110ce0580502811030010200100801030a9028a9020050284603061038010f043028cd030350080103011008010288103005020010283500801198152c8131981d03035008014d01b1301d0280102805000050300103835000050281d03005508130318502035008010284d0309202035000050483536801038110380500005021310307602835008010200508811
|37=>0x28350080104835038050201d020010080111019028110309202035008014a01b02a110303500801028350380503035038010080103811020010383504835008014081f09a690a0010281d030050c89202035028350080102811028cd020350303500801028054581503045038010c811028010300503015020050d1450c8270281903836008011981503805030350380100801049290812d150440380102005
|38=>0xf017030750283500801028720f043030750283500801028f6028cd030350080103061028350281900005032ba020ad03035008010309202035008011136d028110303600801030350200104835030110080103076050010280503805038010e81f16835028350080103061130050281d02801038054001b00005028a90200502001032be038ad03035008013501f028910080102a2d0581d028050300103076
|39=>0xc8b20301503835008012c81f2c813030b1038350080104835020350280102805000050483503835028010280500005030dd0c8b20301503835008010f0430f011028cd030350080115044038010200502001038056e8430cb7903015020360080104835150440380102005000050301502805030450380115044038010201d02005000050806e0d035008010c827030154081302965030b1038350080103076
|40=>0x5031e9028610380503801100070200103011030011a8050d0010c8270301503a390301d02836008010c0010301502801038050f0431180109815030050806e1a8050d0010c827030150806e0d035008010c82703015031aa0289102035008010e81f02835030010300500005020b26081f020b103835008010880503045028050380103801038050203504835000050300115001028a90301502005028dd
|41=>0x2001028ce030350301100801028050c0010280103805028aa048350200500005030890281115003020050e81f02835030050000503179028b20383500801038110203504835008017100102af9030aa0200502001028110303500801030750301d02835008013c80103201028a90200502811130190280100801028b203835028010080104ae94100502882020016081f150450380102005048350280102805
|42=>0x80103005038350483500005438173d00102861038050281d028b2038350080103892020350380100801118820284d030050200102811048350280500005030150e813028350080102001000050301102805168350301d02835008010a019028010281d03005030810288103005020013d801098510281d03005008010315d02881020010200502811028350000502811028190300102005028110289210005
|43=>0x801048010280502801038052c81f030b10383500801051d106001030110280503081028aa020050200104921030b2038350080133811130190280100801130050281d0280103805020050281104835000050280502819030350000503035028010280500005020350300103005000050301d0880502805038010c827100050301502001038011500102005038050a8360a0190281d00801028920203503035
|44=>0x38010c8110301502001008010c81d13005028190280103035030150200100801110ce02811030350080103145028190383600801358050284602819038010f01333805130190280119815198110303500801160130880503811038010301d03835030050000507005070010c8110281902801028610c001038052c8131981d030350080103931030760283500801418130988103005020010e8130281102835
|45=>0x28a9150010200502892020350280100801198130303502001008015f001030aa0200540019028a90200502001020350381103805000050c801028a9030150200503061030150280103805028050315d028810200102805028110303500005038350303500801030aa020050200100801028cd19813030350080160813548010c0110380503001020050301104801020050e813028350000503005031ad02846
|46=>0xf01303075028350080103005038010301d028013501f028911500102005028350380103805000050f01733805058150300103185028920203500801110050281103035000050281103005030150200502861028010380500005028010501d0480102805150010301103001020051981d0303500801030350301d02835008011181d0c8050301503001030050203504835000057581133807130190280103005
|47=>0xc8110280503015020014b8011181f09815030053501f40001028a9020050a801030510281d03005030921500102811020052c81f4580503045038010f013028cd03035008010c862028190380503801030150383502805000050c8050301502001008010281d03035038050000502846030050281903801038050303503801008010c8a9028190300102005028b103835048350080103092028811000502001
|48=>0x20050000513005038010301d028012c81f1a001030610380505045028050380115001030050301502005030053381f05815030010c8921000503015020013c80305031030110280502035028110283500801060150000503011028050f017030750283500801100610380502001030010281102835008010c001020050200103805038050203504835000050281d0383502801008015a81902b790203600801
|49=>0x32090288202001038010307502835008010288102819030050200100801028aa0200502001028b20c0010280103805030150203502805000050282d03001030050000502005028a50308202001030920203502835008013501f0e8110283500801020350281104835008011184703029028052c8131981d0303500801028ce0301d03035008014580502a2d0304503801030350301502005000050303502801
|50=>0x30811000502001448050a8010c81d030150301d02861030010380502835048350200100801038013d01b02861038050321e1306102801038057980502a2e03045038010e813020350283500801033c505046028050380102881020010480502805028011181f0981503005030a9028a90280102005030010e813028350080103179028b2038350080104985028921000502001020010d0050c8270281903005
|51=>0xa0050281d0300102035000050301102805028b20284508805038010581d030010281903805020050300102811030050201d0c00103805020050281d048350280500005338630309902801038050301d0e81f02835008010383502819030350080102801038350303500801033d639801028aa0200506001048350301100801028110307602835008010303504835020010080104921030b2038350080102811
|52=>0x67801030620380503b6d030360281d0080103835098150300500005023e9100620380502001033e14d00702845038012c81f030b108805038010201d048010380502005030350281903805000050f0433380505815030010280103035038050000503801038920203500801088130483503801008010c81d0280502819038050c0011001d038050200102811030150200500005051d1060010301102805031e9
|53=>0x5f001030aa020052c81b1981d0303500801028910309202035008010280504835038010080103011198130303500801418130988103005020010282d028a90300102005031610e81f028350080102831020350301100801020350281903035008010e8330283503011008010303502035028010080102805030350281d0000511846030290280503801020b2088050380102001030d90e813028350080102bf1
|54=>0x38050881303801038050281903801008010200503082030150200102001050310301102805020b2020b10383500801608135300508811038010c8a90281903001020050303502845038010080104bd539801028aa02005031850289215001020050f0430307502835008010e81f04835028350080102a2d03045038010380507003028310301102805030810300502005020010309210005030150200102ba6
|55=>0x2805030010080104c110a0360281d008010c001038050301d02805810151a00303061038050c801030050301502005030010307602835008010a035000050281d030051181111801050190280503801028ce03035008012c813030b103835008010290d1981f03035008010700503089028110300113005030610280103805030450281903801008010c8a903015020050000502835008010281d0300100801
|56=>0x1001d0380502001028110300102805000050301d33807058150300103805030150280503801030610280103801038050300104b7902036008010337903015020360080100801028190301d028010301d13061028010380502895030921000502001028110281902035008010c8270301502036008013501f028910203500801031610e81f02835008012c81f030b10c001038056081f020b1038350080103015
|57=>0x28810200102005032690a0010281d0300519813028110303500801030e90c0800200103805050110300102805000054381f0504502805038010c84502819038010080104801028610280103805028190301d0c0030380535013028911500102005038010286103805000053d8031181d09815030054381b0e81d0283500801031e93d0010286103805008010288102001020050309210005030010200102061
|58=>0xe8190e81102835008010323902836008014002d028a903001020051981f0281903035008010280103202028a902005030820283502001008014d0190284503801008010300500801030110280100801028610301d0380500801030050301d03801848050a8030c81d03015088110483503801008010301d0880502819038010201d020b203835008010304503801048050300503419030150c0030380503015
|59=>0x4d019028450280503801049850289202035008010280503045038010380502835028190303500801168010301d048350080103805028050281d03001038010307602835008010c827028191500302005100600200502001038054181509881030050200103082028a90200502001030010301502005000050c8b20301503835008011325a0600503011028010a36d030360281d0080102131030760283500801
|60=>0x380504835028910203500801028610304503801038050203500801028110300160813088a902005038010e81313005028190280102b6d0303600801138030d0050c8270301509845038010281d0300502891030a9150010200502bee03b6d03036008010301d028b20383500801038010e81f028350080103001020010301104805338131301902801008010e81103015028350080102045038010380500005
|61=>0x38010301d02836038010080103001028810280502001118800284d030050200100005070050c81102819100050288103015020011981705805030150300100801030450380103805030110289210005020011a00103061028190380507036060150301100801070050c81103015020013d8033d019028610380502801030450281d038010c827030150200100801034110a0360281d00801028016780103062
|62=>0x80102a0e4b001030a90200500801030450280503801150010281903001020050c86202819038050000505861030010280503805038ad028ce030350080103089028110283500801008010d0010c827030150d035008010c82703015030050483503011000050c805028190301d02801030350e813028350080102805028450301d03801030010281903805000053501f028911500102005448070c84502819
|63=>0x80102805030b20c00103805028110309102035008010c8110281903001020050812d150440380102005030010280502819038054181706035030110080107037060150301100801070340601503011008011000502881030110200106035048350301100801058a9028a903001020050301d03015038350080102a1119813030350080103062028010380103805038ae028ce0303500801028010281104835
|64=>0x28050200100801030b103835008010c8270301503835008011000703001030150200103045028010281903801030b2028610c001038050f01b338051301902801008013d01b028610380502af9030aa0200500005088a903805038010200519817038350303500801098450300502819038016081f160110c0010380502a59030a915001020050c88102805030150200103b6d0303600801031aa0e81102835
|65=>0x4921030b2038350080115001028a90300102005418134b001030a9020052c813030b10383500801028910281902035008011136d028110303600801030350307602835008010f043030750283500801028ce02035030350080103035028350080103001048350380500005030050e81102835000050286103805038010080103179028b20383500801028cd0301d03035008010f01133805130190280103082
|66=>0x3805430010c8620281903805030d90e81302835008010200505815028110300104c49168360301d00801020ae028ce030350080103035028aa02005000050a807028b50301d028010383504835008010393103076028350080141815198110303500801020051001d038050200103061028360380500005008010301103005020013501f40001028a902005060751300503011028011981f028cd0303500801
|67=>0x380503801031a902891020350080102a0e030910203500801050110280502801008010c892028190203500801038350201d02001008013d803028d103061038050281d0c00102801038050309202035008018701f02b6d030360080135013028910203500801338110282d0300102005050010280503805038010301102891020350080103061038050281d03001028460483503801008012c8171a00103061
|68=>0xc00303805020350281103035008012c817030b10880503801030b203835028010080116815008010301d028011000502001030110300100005030810288102001038d50d0010c8270301502c51058620300103805100051001d03805020013c007130310301102801031aa0289102035008010c835030150200100801031610e81f0283500801028b20c0010281d038052c813030b1038350080102b3d03062
|69=>0x483500801198130203503035008010284602819038010080102819198130303500801100050c8110301502001038350280503001008011981105805030150300103c5d0c8360301500801418134b001030a9020050303502835020010080102811028920203500801088050c81d02819038010c8270281903801038050289110005030050200102892028a915001020050281d030b203835008010cc1903015
|70=>0x383500801028cd0303503011008010000503209028820200100801028a90280102005048350381103801008010e81f03035028350080102001028ce03035008010f01f0307502835008010995e02881030050200100801030610281d0380502811020010480502805070030c811030150200502861048350380500005030920281902035008011103502811048350080103092020350280100801020b203835
|71=>0x3011028018701302b6d0303600801198110483503035008010a0ce058050281d030010f01f030750283500801028111981303035008013c007070010c8110281902005008010281103001038ad028ce030350080103805100050201d020010c892028190203500801020010303503011008010281940003028a9020050cb79030150203600801118110c8050301503001028aa03001020050000502801030b2
|72=>0x28050380503801028cd0301d03035008010380502836038010080103075130050301d028014181b098810300502001050810280503015020012c81b1a00103061038052c813030b10c00103805038050203603801008010301d338050581503001030610281903805000054381f028b10880503801028ce0303500801032e94100502882020010a8370a0190281d00801030a90288102001020050000506005
|73=>0x30a9028a90200502001038360280102805000052c8131981d0303500801028010301d0880703801030150301d0283500801039310307602835008016081f020b10383500801030110288103005020010236d03036008010281903092020350080102801028190383600801028054d01b028450380109811030050300100801418130309102035008016c0150337902036008010280503061028010380502845
|74=>0x3011028010280500005198170301d03035008012b81b028810200100801028350603503011008018e01b029450383600801031aa0289102035008014c8013d01b028610380500801030a902801020054181709881030050200103061048350380500005048351001d0200100801048351981f0303500801020b10383504835008011a8050d0010c82703015110ce05805028110300103001028810200102005
|75=>0x303500801020011501d03801020052c813030b10383500801028111500103001020050f043030750283500801020050c00303811038050303500801038350280102805000050280502a2d03045038010318502892020350080103801048350281d008010c827030150383500801030b20383503035008013680103811038050000505046030150280503801008010881102005038012c8131981d0303500801
|76=>0x38050200103035048350301100801028b2038350483500801038050201d020010080104c81130aa02801020050380502035038010080103479110360281100801103e91006203805020010f0430307502835008014001b028a902005020010301d028010280500005048350e811028350080103092020350303500801020350280102805000050289103091020350080103931030760283500801168150301d
|77=>0x283500801150440201d038010200503805048350380100801030350301d048350080102035038350201d0080103835048350281d00801030750383502835008010281d0383502835008014181b198110303500801048350280102805000050e8111300502819028010309202819020350080102892020350483500801028010280503805038010492d150440380102005038050483502001008017d00110062
|78=>0x307502835008011504403801020050000502b6d028110303600801110cd02811030350080113005028190301d028011981f03035008010f04303075028350080102c6a0236d030360080104c91368360201d008010f011028cd0303500801031310307602835008013501b0e811028350080174017031450383600801031850289202035008010f01f03075028350080102891028920203500801168150301d
|79=>0x4d0050284503801338111301902801028110283500801530051001d020010308902811030050304604805038010203503801008010280502001008010383602805000050483502801008010301d02835008010315d02881020010504502805038010f0430307502835008010c891028190203500801030910289202035008010380102005020010380503185028920203500801032390283603011008010f043
|80=>0x2001048011501d020050200103011028053d00302861038050281d04801028050289102035008010e8130283500801048010280103805030110200500005028190303500801030350280100801050190301d028054580703045038010c81103015020011001f02001008010a0010281d030051001d03805020011981d0303500801028110483500801028050301502001030010301d028050c0010280103805
|81=>0x880503801198130303500801028610280103805038350280500005060350301100801030aa0200500005060150301100801098510281d030051001d0200100801030aa0200502001048050284603801070070c81102819031cd028aa020050201d02005000050301503835008011601108805038010300504801030010c0810200103805358050284603801000050301102805028a904801020050380110007
|82=>0x30350380100801028110200500005030111000702001028350380100801028aa0200500005150010201d02005000050301d02805028aa02005020010c8010301503005020050200103805048350281d008014b017030a902005020350280500005028350281d008011500102005038011301104805028010300502005020015c00503046038010284d0300502001030110203500801168360301d0080103045
|83=>0x801048050381103801038050881303801038050281d028050281903801038051500103011020051006203805020010c8450281903801020050301104801008010301503001160130880503801030a90281102005028b10383500801100070201d02001028190301d02801030750283500801100050300502001030450281903801020b10383500801338050581503001020010281103001030350281d00801
|84=>0x380100801030050301d03801028ce0303500801038010301d04805028810300102001028a90300102005338131301902801028610380503801030810200100801030350200100801028810200102005031450383600801150010201d0200502845048050380104835028050000504ae10304603801100610380502001028050301503001548031501d020050c08202001038054d01902845038010281102035
|85=>0x303602001008010224d0880703801088110380103805030aa03015020050480103805020050d0010c82703015028a903015020051300503011028010e81f02835008010e8110283500801020b20383500801150010300502005028190300102005030b108805038010289210005020010280503801008010c00103805020050200504801030050c827030150200102811100070200103005030110280102819
|86=>0x38050301d0480503001030450380100801020b20383500801368360201d00801028d20306103805130050301d0280102b6d03036008010309210005020010337d1000702001198110303500801030110480503005048051001d02001030450280503801030450380103805030050301502005038350303500801028a903011020051500102811020050383502835008010309115001020050e8130283500801
|87=>0x3005020010281102801008011981f0303500801030150383500801368350201d00801030050301100005034190c003038050301103005020010301d048050300503b6d030360080103a3902836008010981503005000050286103805038010289102035008010301508807038010337902036008010280503082020010200503811038050c83603015008010c88203015020010580503015030010286103061
|88=>0x150010301502005030011000702001030b108805038010214503836008010e81f02835008010e81102835008010301d0383500801020b103835008010880508811038010383602001008010a8010c81d030150283603011008010301d02819038011a0010306103805028310301102805038350201d00801031ad028460380102801028a90200502805030010200102811030360080104835028350080109881
|89=>0x200504a390283600801028b203835008010301d0303500801030a90300102005038350281d008010380504801030010286103805000050501d0480102805028910203500801028920203500801020b20383500801008010c82703015028610c00103805028ce0303500801028110300102005030350301100801028b20383500801028aa0300102005038350200100801028a90280102005058620300103805
|90=>0x3805020010303502835008010300103005020010201d04835008010a0360281d00801028050301d028010306103805000051001d0200100801030750283500801100610380502001048350301100801008010301d03015028050300100801030b203835008011001d0380502001028050301102801048350200100801050460280503801030a90280102005049450383600801198110303500801048011501f
|91=>0x300102001020050000502001020051001f0200103005038010281d04801778010201d04805038350483500801030750283500801030150203600801150440380102005028b10383500801030750283500801020350383500801038010380500005028010280500005028920203500801338070581503001038050200100801028b20383500801480050881303801028ce03035008010301d04835008010201d
|92=>0x5815030010380502005030aa02005030460380103015008010280503801028a9020050281d030010281d02805048050280502819038010308102001028350080104801030050281d038050483500801028a9020051501d0200502811030011500102005028110280504801020050c81d03015030150300102811028190301d038051001d02001030a9020050383500801030050000508807038010381103805
|93=>0x8010301502005030010301d048010201d030110483500801028050280103805020010c827030150301d008010201d00801038350080103011008010301d048050201d048050280503001020360080103036008010283500801
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0xe60000001dc000e0000
|7,0=>0x2dd816680ae5000002acc00000a65050300000000009c404c200000124c0000000002318000008a200000000011040000041a800000000000003f281e180e4c06e4035201918000005e60000000000b840575028b012d808e8045200000000007ec03d2000000dd806a40000019180b18000000000151009cc0000025201028069803040144
|7,1=>0x4754000000000000045d8222c10c508330000020660fe507ca8000000000f54079903bd000000e96071b037d01b680d74000003458198a0c8400000000000000000063103090000000000000000000000000000000000000000bd5
|8,0=>0x115a08994442a21f210da08594422a20d4104288110000020040fda87dd000001f430f7a87a943caa1e050eda875943a2a00000e6a0000039281c450dfa86e9437221b45000006bd435681a650d0a8671432ea19250c6a86214306a17f40bd285d542e0a16b50b32858902bc815b30ab285454298a14840a2204fd4274a1364098a84b1424ea1225
|8,1=>0x19228c810636a316518920c3540000309418228bfd45f682f65178a8bb505d0a000000000b8d45bca2da416b20b454598a2c7516128af90572a2b7200000ac9455aa2a85151a8a794532a294514988a3d0000028a514320a0544fa82785139a89bd0000026d21342898d44bca259512aa09414496a2474000009148480a23d311c288cd4464222f3
|8,2=>0x10a9484e6422520ea9061482c441152062901d4804a00001fea8fe147e6a3ee51f520f9547c0a3db51ec90f51479ea3ca51e320f09077aa3b851d9a8ebd075a43a8500000e8d473ca39b31cba0e49471aa38851c220e0106fa637851b9a8dc486da800001b428d94c6c2835c51ac20d4d469ca34951a228cfd4674a3373199a0cb9465a23294
|8,3=>0x2961949d4a44a51e428d980000a2ca51152862941d4a04a000027ea93e140000000027a213bd49da44e85271a937d09b4a4d552682932d498ca4c2425ea92e1496884b132562929d4944a49d524c2924d491e800002452921540000480523e211e108e6a46e5234a919148c0845f122d2915cc8a4a44e4224a91150884643e4000010e54868a42f5
|8,4=>0x318298ad4c4e8622530f218690c2c86115307918294c0aa60052fda97d94be845ef52f5a17994bc485dd52ec2974d4b9ca5c952e2a17014b7885b75000000000b64a5ad52d4a16914b40859d32cc280000b28859132c7916294b0c85815000015f14aeea57522b8295ad4ad2456452afa9570caaea55252a6a9528ca8aa540529da94e0ca68852f5
|8,5=>0x393a9c894e3c8719538a29c410000070d3384a1c114dfea000037da1bd94de2a6ec537421b94cdc0a6db536c19b4d4d9e86ca5363200000d8486bd535c29acd4d5ca6a95352280000d44469e434d21a554d20a0000345a9a194d04867d533ca19d8cce4866d5334a19914cbea65a532aa99414c9e264b40000191d00000642531ea98e1400006353
|8,6=>0x20309010880353ff29fe5400007f543f829fad4fcca00003f1200000fbe67dc33eba9f494f9e67cb43e329f090000000003df980000f7687b653d8a9eb14f4ea00003d129e754f30a79443c7a9e294f0aa78053bda9dd94ee4876f33b529d954000000003b029d788eb6600003aba1d50ce9ea74a53a2a9d014000073b539ba1cd0ce62672c5
|8,7=>0x48c2a44d521e890b44832a40911fc88fa447aaa3c511d8a8e75471a237951b2a8d454682232d518ca8c1545e2a2dd5164a8ad5454a22951140a89b544ba2249511aa8885441a800010fe887a543b221c550d8a86754312a17cd0b68000042ba2149509e684a5422aa101507888375419a20b94000082954122a07d5034a81820000204d4000080e5
|8,8=>0x505a28195402a9fc54fbaa7c953daa9e850000278d53bca00004ecaa75153a089cb5000027195382a9bc54dbaa6cd135e89ab44d41a691133ea00004cd28000132c899154c6280001310898534c0a25f8d2f2a97454b8225ad52cca9615000025750000095854aa2253d5294a00004a2aa5015276a939249aa24c14000092d3494a24915244491d5
|8,9=>0x1444a000050eaa8651428aa0f5
|9,0=>0x591a2c7d16368b174589a2c3d16168b074581a2bfd15f68af74579a2bbd15d68ae74571a2b7d15b68ad74569a2b3d15968ac74561a2afd15768ab74559a2abd15568aa74551a2a7d15368a974549a2a3d15168a874541a29fd14f68a774539a29bd14d68a674531a297d14b68a574529a293d14968a474521a28fd14768a374519a28bd14568a274
|9,1=>0x60fa306d182e8c1436082303118108c04460022ff117f08bf445f822fb117d08be445f022f7117b08bd445e822f3117908bc445e022ef117708bb445d822eb117508ba445d022e7117308b9445c89ae3517128b8545c0a2df516f28b7545b91adb916d48b6645b122d7916b48b5735a9a2d3d16968b4745a1a2cfd16768b374599a2cbd16568b274
|9,2=>0x68ea34651a2a8d114686a34251a0a8d01467ea33e519ea8cf14676a33a519ca8ce1466ea336519aa8cd14666a3325198a8cc1465ea32e5196a8cb14656a32a5194a8ca1464ea3265192a8c914646a3225190a8c81463ea31e518ea8c714636a31a518ca8c61462ea316518aa8c52362723129188c8c42461f230e9186c8c333617a30ad184e8c234
|9,3=>0x70ea38651c2a8e114706a38251c0a8e0146fea37e51bea8df146f6a37a51bca8de146eea37651baa8dd146e6a37251b8a8dc146dea36e51b6a8db146d6a36a51b4a8da146cea36651b2a8d9146c6a36251b0a8d8146bea35e51aea8d7146b6a35a51aca8d6146aea35651aaa8d5146a6a35251a8a8d41469ea34e51a6a8d314696a34a51a4a8d214
|9,4=>0x78e23c611e288f10478623c211e088f00477e23be11de88ef0477623ba11dc88ee0476e23b611da88ed0476623b211d888ec0475e23ae4dd6a8eb14756a3aa51d4a8ea1474ea3a651d2a8e914746a3a251d0a8e81473ea39e51cea8e714736a39a51cca8e61472ea39651caa8e514726a39251c8a8e41471ea38e51c6a8e314716a38a51c4a8e214
|9,5=>0x80d240592024900e48052401920066fff47fda3fdd1fe68fef47f5a3f9d1fc68fdf47eda3f5d1fa68fcf47e5a3f1d1f868fbf47dda3edd1f668faf47d5a3e9d1f468f9f47cda3e5d1f268f8f47c5a3e1d1f068f7f47bda3ddd1ee68f6f47b5a3d9d1ec68f5f47ada3d5d1ea68f4f47a5a3d1d1e868f3f479da3cdd1e668f2f4795a3ca0de488f204
|9,6=>0x88b24449221c910a48832440921fc90fa487b243c921dc90ea48732438921be70db486ba434d219e90cb4863a430d217e90bb485ba42cd215e90ab4853a428d2140709c484c242512120908c4844242112100907c483c241d120e0906c48342419120c0905c482c9c15520a2904d4824a41152082903d481d1c0d92064902e4815240992044901e4
|9,7=>0x90aa4845241c720a49032480923fc91fa48fb247c923dc91ea48f32478923bc91da48eb24749239c91ca48e324709237c91ba48db246c9235c91aa48d324689233c919a48cb24649231c918a48c32460922fc917a48bb245c922dc916a48b32458922bc915a48ab24549229c914a48a324509227c913a489b244c9225c912a489324489223c911a4
|9,8=>0x98924c3926149306498124bf925f492f6497924bb925d492e8297224b8125b892d8496a24b41259892c8496224b01257892b8495a24ac1255892a8495224a8125389298494a24a4125189288494224a0124f89278493a249c124d8926849322498124ba7259492aa4945249a92494922a4905247a9239491aa48c5245a92294912a4885243a92194
|9,9=>0x13d549e8a4f35279293c549e0a4ef5277293b549d8a4eb5275473a649d124e792734939649c924e392714938649c124df926f4937649b924db926d4936649b124d7926b4935649a924d392694934649a124cf926749336499924cb926549326499124c79263493164
|10,0=>0xa4b1d24ce920748d3a451d21ce90874813a3f1d1ece8f074753a391d1bce8d874693a331d18ce8c0745d3a2d1d15ce8a874513a271d12ce89074453a211d0fce87874393a1b1d0cce860742d3a151d09ce84874213a0f1d06ce83074153a091d03ce81874093a031d00ce80073fd39fd1cfdce7e873f139f71cface7d073e539f11cf7ce7b873d93
|10,1=>0xaab1d54ceaa0754d3aa51d51cea8875413a9f1d4ecea7075353a991d4bcea5875293a931d48cea40751d3a8d1d45cea2875113a871d42cea1075053a811d3fce9f874f93a7b1d3cce9e074ed3a751d39ce9c874e13a6f1d36ce9b074d53a691d33ce99874c93a631d30ce98074bd3a5d1d2dce96874b13a571d2ace95074a53a511d27ce93874993
|10,2=>0xb0b1d84cec20760d3b051d81cec0876013aff1d7ecebf075f53af91d7bcebd875e93af31d78cebc075dd3aed1d75ceba875d13ae71d72ceb9075c53ae11d6fceb7875b93adb1d6cceb6075ad3ad51d69ceb4875a13acf1d66ceb3075953ac91d63ceb1875893ac31d60ceb00757d3abd1d5dceae875713ab71d5acead075653ab11d57ceab875593
|10,3=>0xb6b1db4ceda076cd3b651db1ced8876c13b5f1daeced7076b53b591dabced5876a93b531da8ced40769d3b4d1da5ced2876913b471da2ced1076853b411d9fcecf876793b3b1d9ccece0766d3b351d99cecc876613b2f1d96cecb076553b291d93cec9876493b231d90cec80763d3b1d1d8dcec6876313b171d8acec5076253b111d87cec3876193
|10,4=>0x16f13b771dbacedd076e53b711db7cedb876d93
|11,0=>0xbad15d60aeac57542ba915d40ae9c574c2ba515d20ae8c57442ba115d00ae7c573c2b9d15ce0ae6c57342b9915cc0ae5c572c2b9515ca0ae4c57242b9115c80ae3c571c2b8d15c60ae2c57142b8915c40ae1c570c2b8515c20ae0c57042b8115c00adfc56fc2b7d15be0adec56f42
|12,0=>0xbb18dd886ec237601baf8dd786eba375c1
|_,_=>0
def PO:=mkPO wAt oP oO 20 9 511 17
def pmP:Nat→Nat
|0=>0x206000000000000002020000000000000020000000000000000180000000000000001180000000000000011600000000000000112000000000000001080000000000000010700000000000000100000000000000000e20000000000000008f0000000000000008800000000000000080000000000000000400000000000000001e0000000000000001a000000000000000180000000000000001600000000000000011000000000000000100000000000000000f0000000000000000e0000000000000000a0000000000000000900000000000000008000000000000000070000000000000000600000000000000003000000000000000020000000000000000100000000000000000
|1=>0x110800000000000001100000000000000010da000000000000010a8000000000000010a00000000000000108a00000000000001048000000000000010120000000000000100000000000000000c1500000000000000a180000000000000084e0000000000000084a0000000000000082a0000000000000080a000000000000008070000000000000080000000000000000606000000000000005150000000000000050d000000000000005000000000000000041e0000000000000041900000000000000418000000000000004160000000000000041500000000000000408000000000000003800000000000000030f000000000000003020000000000000030000000000000000220
|2=>0x30400000000000000300700000000000003000000000000000029080000000000000240700000000000002200000000000000021800000000000000211600000000000002107000000000000021000000000000000202f00000000000002008000000000000020070000000000000200100000000000002000000000000000019360000000000000190800000000000001808000000000000014150000000000000140600000000000001400000000000000013080000000000000123e0000000000000122a0000000000000122200000000000001208000000000000011a600000000000001192000000000000011820000000000000112e0000000000000112800000000000001115
|3=>0x940600000000000009400000000000000091100000000000000910000000000000009010000000000000090000000000000000841600000000000008410000000000000084070000000000000840000000000000008336000000000000083260000000000000831000000000000008116000000000000081070000000000000810000000000000008016000000000000080100000000000000800700000000000008006000000000000080020000000000000800100000000000008000000000000000074750000000000000640700000000000005122000000000000051200000000000000402000000000000004000000000000000034f50000000000000320700000000000003100
|4=>0xf53f0000000000000f5150000000000000f4150000000000000e0070000000000000d1100000000000000d1000000000000000c2100000000000000c2000000000000000c1200000000000000c0000000000000000bf5f0000000000000bf1f0000000000000b7ff0000000000000b73f0000000000000b71f0000000000000b71d0000000000000b53f0000000000000b53d0000000000000b51f0000000000000b51d0000000000000b5190000000000000b0070000000000000b0000000000000000a51d0000000000000a0070000000000000a0060000000000000a001000000000000096060000000000000953d0000000000000951d0000000000000951600000000000009515
|5=>0x2925200000000000023eff0000000000002200700000000000021d7e0000000000002197e0000000000002195a00000000000021852000000000000218480000000000002095e0000000000002091a00000000000020176000000000000201740000000000002011000000000000020002000000000000200000000000000001f73f0000000000001c0000000000000001b71d0000000000001b53f00000000000019126000000000000181120000000000001200700000000000012000000000000000115260000000000001120000000000000011126000000000000101000000000000001004200000000000010040000000000000100000000000000000f71f0000000000000f57d
|6=>0x20953d00000000000060800000000000000600000000000000004b51f00000000000042500000000000000414000000000000004040000000000000040002000000000000400000000000000003f6770000000000003b57f0000000000003b57d0000000000003b55f0000000000003b53f0000000000003955600000000000030112000000000000300220000000000002f6350000000000002f57d0000000000002f51d0000000000002d4420000000000002bf5d0000000000002bd7f0000000000002bd7d0000000000002bd5f0000000000002bd3f0000000000002b5fd0000000000002b5bd0000000000002b59d0000000000002b57d0000000000002b55d0000000000002b36d
|7=>0x20115020000000000200f7170000000000200f53d0000000000200b71f0000000000200b57d00000000002009300000000000020092020000000000200200700000000002001000000000000020002020000000000200000200000000001282004000000000008404000000000000080b51d000000000008081520000000000080002800000000000800002000000000008000000000000000040b531000000000004004000000000000038a02c0000000000021b53d0000000000021b51d0000000000020bd3d0000000000020bd1d0000000000020b53d0000000000020b51d0000000000020a92d0000000000020a51d0000000000020a41d0000000000020a41c0000000000020a02d
|8=>0x802d0020000000000801b5770000000000801b55f000000000080110100000000000800d0020000000000800c1260000000000800b5270000000000800b51d00000000008008726000000000080040020000000000800267d000000000080018080000000000800109200000000008001082000000000080010100000000000800084a00000000008000808000000000080000020000000000620b53d0000000000620b51d0000000000620311d0000000000620201d0000000000420b53d0000000000420b51d00000000004040000000000000040084100000000000320a43d0000000000221b53d0000000000220b53d0000000000220b51d0000000000202e57500000000002028440
|9=>0x102414150000000001024040100000000010240011000000000102400000000000001020b51d0000000001005000000000000010049d3d0000000001004951d00000000010049000000000000100488140000000001004800800000000010042916000000000100425000000000001004000100000000010022e0d000000000100201000000000001000b51d000000000100021080000000001000010000000000010000010000000000100000010000000000a00f71f0000000000882bf1f0000000000882b73f0000000000882375f0000000000882364f0000000000880355f0000000000821b53d0000000000820953d000000000080414080000000000804104200000000008040108
|10=>0x20808100000000000208080170000000002080351f000000000208019080000000002080100f00000000020801007000000000208004070000000002080033e0000000002080021e000000000208002170000000002080010f0000000002080001f0000000002080001700000000020800008000000000208000070000000002080000300000000020800001000000000208000000000000002000b51f0000000002000b51d0000000002000a00700000000020008102000000000200080020000000002000800000000000020003d1f00000000020000808000000000200000160000000002000001200000000020000010000000000200000080000000002000000300000000020000000
|11=>0x440004100000000004220b51d0000000004024b51d00000000040241c1d0000000004020bd1d0000000004020b51d0000000004004b71d0000000004002b5fd0000000004002b59d000000000400205980000000004000b59d0000000004000b51f0000000004000b51d0000000004000801000000000040003f1d0000000004000353f0000000004000224700000000040000410000000000400003220000000004000030600000000040000002000000000280094020000000002800351f0000000002200f7570000000002200b717000000000220030470000000002082957f0000000002080b51f0000000002080973f0000000002080951f0000000002080821700000000020808107
|12=>0x10020b51d0000000010002b5bd0000000010002b51d00000000100023d7d00000000100023d5d0000000010002225d00000000100021100000000001000208000000000010000bf5f0000000010000b73f0000000010000b71f0000000010000b71d0000000010000b51f0000000010000b51d00000000100003dbd0000000010000259d000000001000013260000000010000070a00000000100000100000000001000000080000000006800230f00000000058249d1d00000000048249d3d00000000048041d8000000000048040f0800000000048001c4a0000000004800030a000000000480000400000000004620b51d0000000004620351d0000000004420b51d0000000004420a41d
|13=>0x14002112a0000000014000b73f0000000014000b73d0000000014000b71d0000000014000b5fd0000000014000b5bd0000000014000351d0000000014000313f0000000014000259d00000000140001d28000000001400017680000000014000173e0000000014000132e000000001400007300000000014000070a0000000014000031e000000001400003100000000014000003c0000000011800351f000000001100219000000000011000b51f0000000010880324f0000000010820bd3d0000000010820bd1d0000000010820b51d000000001080421080000000010802291f0000000010800b71f0000000010800b71d00000000108003d5f0000000010800320f0000000010080235f
|14=>0x200021c00000000002000214000000000020001a735000000002000101020000000020000f51f0000000020000c0220000000020000b71f0000000020000b59f000000002000092000000000020000810000000000200004000000000002000020070000000020000124200000000200000100000000002000000a200000000200000002000000001c220a40d0000000015004953d00000000148201d3d0000000014420b53d000000001440080100000000014220b50d0000000014020b53d0000000014020b51d0000000014020a41d00000000140043d5d0000000014002b71d0000000014002b57d0000000014002b55d00000000140023d3d000000001400225fd0000000014002115e
|15=>0x20800851500000000208008000000000002080015be000000002080011be0000000020800114a0000000020800111e000000002080010920000000020800070a0000000020800019a000000002028004000000000020220b53d0000000020202f6570000000020202c1020000000020202b047000000002020200000000000020200f7170000000020200f5370000000020200f51f0000000020200b73f0000000020200b71f0000000020200b5770000000020200b51f00000000200809002000000002008000020000000020020951d0000000020002f5370000000020002d0520000000020002bd1f0000000020002b73f0000000020002b71f0000000020002b53f0000000020002b51f
|16=>0x310003f1f000000003000200020000000024002b59f0000000024002351d000000002400231870000000024000373f0000000022a00b7170000000022800b77f0000000022800b75f0000000022080975f0000000022000f7570000000022000b75f0000000021804953d000000002100080080000000020a00f517000000002082184150000000020820953d00000000208040d12000000002080405000000000020802977d000000002080297370000000020802957f000000002080225150000000020802095a0000000020801e1370000000020800e6050000000020800d5160000000020800d4020000000020800d1260000000020800d1160000000020800b73d00000000208009162
|17=>0x608000100000000004080101000000000040800f75f0000000040800f5170000000040800a24700000000408004102000000004080010000000000040200955d0000000040002d0520000000040000b51d0000000040000b000000000004000093000000000040000920000000000400009110000000004000032000000000040000300200000000400002100000000004000015100000000040000102200000000400001002000000004000010000000000035020bd3d0000000035020bd1d00000000350003f1d00000000350003b170000000034000355d0000000031020bd3d00000000310021d1a000000003100211000000000031000bf4f0000000031000bf1f0000000031000bddf
|18=>0x183000211f0000000183000041e000000018100200100000000114002b5dd0000000110800b5df00000001030020010000000010080234050000000100802308f0000000100002351f000000010000215d2000000010000210500000000100000b51f000000010000025dd0000000100000105000000001000000510000000009200005160000000092000011e000000009000234df0000000084002bf9f0000000083000001e0000000082000021e000000008200000120000000080084151e00000000800800402000000008000404000000000080000bf9f0000000080000b51f00000000800003fdf00000000800003d5f000000008000037ff0000000080000040200000000800000400
|19=>0x400a00b51f0000000400a0011400000000400221941d0000000400000b51f0000000400000b51d000000040000004000000000400000010200000004000000002000000022028086020000000220201f71700000002202012127000000022020004000000000200a0067070000000200801f71f0000000200801f7170000000200800a2270000000200201f5170000000200200b7170000000200003f71f0000000200003b5170000000200002f7370000000200001f73f0000000200000b51f0000000200000201700000002000000402000000020000000100000000193000b71f0000000193000b5df00000001930001056000000018300201120000000183000bf9f0000000183000351f
|20=>0x84000004080000000840000008000000008400000001000000084000000000000000820202f51f0000000820202b5370000000820200f5170000000820002b515000000082000271070000000820000f0470000000820000b71d000000082000090000000000800a02f71f00000008008004510000000080080005000000000800203f51f0000000800202f57d0000000800202f55d0000000800202f51d0000000800002b0000000000800000b55700000008000009500000000080000000800000000800000000100000008000000000000000060008004060000000420a21b53d0000000420a21b51d0000000400a21b51d0000000400a01f51f0000000400a0191420000000400a00b577
|21=>0x1000040b5190000000e20080b5170000000e20080a5070000000e2008025170000000e00080b5170000000e0008095160000000e0008084160000000e0008084060000000e0008035070000000e0008014160000000e0008014060000000e0000004060000000c2080005000000000c0080015000000000c0080005420000000c0080005400000000c0008004000000000a000000400000000084040000000000000840202d51d0000000840000d0360000000840000b71d0000000840000b51d0000000840000b3000000000840000b00000000008400009100000000084000070160000000840000501600000008400003402000000084000031000000000840000301200000008400001000
|22=>0x8000a20b51f0000008000420b51d0000008000221b51f0000008000220b51f0000008000220b51d0000008000202f51f0000008000202e5770000008000002b5df0000008000000951f0000006000202e4630000006000200e5370000006000002b51f00000040308209d1b0000004030020183f0000004010420b51d0000004010020bd1f0000004010000b5df0000004010000b51f00000040048041c080000004000420b51d0000004000002f55f0000003014000b5390000003000200b5190000003000000b53d0000003000000b5390000003000000b51f0000003000000b51d0000003000000b51b00000020140003519000000201400000380000002008200b51f00000020000003519
|23=>0xf000002b59b000000f000002b57f000000f000002b55d000000f000002b55b000000f000002b53f000000f000000f51b000000f000000b59b000000f000000b55b000000e014002b16f000000e010002253f000000e000002257f000000d000520b53d000000c0310201c3f000000c004002b55f000000c0000000513000000b000000f57f000000a01400021ff000000a010002253f000000a01000025bf000000a000002b59f000000a000000b59f0000008024020b51f0000008020a2194370000008018220a41d0000008014520a0310000008010520a43d0000008004620b51d0000008004220b51d0000008004002b5db0000008004002b59f000000800400225af0000008004000b55f
|24=>0x10000200b17d00000100002009724000001000020097200000010000200971600000100002009630000001000020096020000010000200933600000100002009300000001000020084200000010000200831600000100002008030000001000020010000000010000021b53d0000010000021b51d0000010000020b51d0000010000020a43d0000010000020a03d0000010000020291d0000010000003b5370000010000003b51f0000010000002f53d0000010000002b71f0000010000002b51f000001000000175350000010000000f51d0000010000000d2500000010000000c1500000010000000b51f000001000000051360000010000000120200000100000000202000000f000002f51b
|25=>0x10004620b53d0000010004620b10d000001000452020250000010004420b53d0000010004420b51d0000010004220b51d0000010004020b51d000001000200010100000010000a20b53d0000010000a20b51d0000010000a0137270000010000882b71f0000010000882b5370000010000821b53d0000010000821b51d0000010000802b5370000010000800b71d000001000080071070000010000800370f0000010000620b53d0000010000420b51d0000010000221b53d0000010000220b53d0000010000220b51d0000010000202f5750000010000202b57d00000100002020152000001000020177370000010000200f7150000010000200f53d0000010000200d2100000010000200b55d
|26=>0x1004000056500000010020a20b53d0000010020a00f1250000010020821a51d0000010020821953d0000010020820b53d0000010020820b51d0000010020803a1170000010020800b71d000001002080080100000010020221953d0000010020220b51d0000010020220b13d0000010020200b73d0000010020200321500000100202001200000001002020011100000010020020b51d0000010020002b51f0000010020000f51f0000010014620b51d0000010014620a43d0000010014420b53d0000010014220b53d0000010014220b51d000001001420000000000010010620b53d0000010010620a43d0000010010420b51d000001001040080180000010010020a43d00000100100000010
|27=>0x40000000b51d000004000000081200000040000000800000000400000001188000004000000001a8000004000000001080000040000000010000000400000000008000004000000000000000020000028b12c000001e000202b16f000001c004120a43d000001c000320a02d0000016000202f5270000016000000b51b0000014020021b51f0000014010420b51d0000014010420a0150000014000000f55f0000013000000b51d0000012000000b531000001020200092120000010200001f71f0000010200001f7170000010200001f537000001020000070270000010060000f55f0000010060000d150000001006000092400000010040800b5150000010040200f55d0000010040000f55d
|28=>0x800000001908000008000000011080000080000000100f000008000000010000000080000000010800000800000000068000008000000000420000080000000000800000800000000000000005002002094350000050000020941d0000040030820953d0000040021824953d0000040020821953d00000400208209d3d0000040020820953d0000040020802977f0000040020800c1200000040020800957f0000040020800953f0000040020800953d0000040020800871d0000040020800019a0000040001024000900000400008000002000004000080000000000040000020b53d0000040000020141d0000040000001b5350000040000000d0000000040000000c1070000040000000b73d
|29=>0x100000000010000000c0020802957d00000c0020800051500000c0002082137700000c0002080973f00000c0000000b51f00000c0000000100700000c00000000107000009e000002a577000008f000002b57f00000800220001717000008002000015770000080010002b57d0000080002082957f0000080002080100f00000800020801007000008000208005170000080000202a535000008000000390520000080000002b57d0000080000002b45500000800000021c4a0000080000002195a0000080000001910000000800000019020000008000000100000000080000000f5350000080000000b53d0000080000000b51f0000080000000b51d000008000000090000000080000000217d
|30=>0x110000220b53d0000110000220953d0000110000202b53d0000110000200f53d0000110000200b53d0000110000200b51500001100002008501000011000020011520000110000000b53d0000110000000a57500001100000005130000011000000000020000100840000a415000010084000021010000100800002e5150000100800000b51d0000100800000210000001000200209435000010000020000020000100000000f5150000100000000b51f0000100000000b51d00001000000009300000010000000092060000100000000910000001000000009006000010000000090000000100000000330000001000000002415000010000000021000000100000000131000001000000001020
|31=>0x200010000257d0000200010000213d0000200004000355f0000200004000012000002000010240009000020000100431080000200000020b53d0000200000000b53d0000200000000b51d00002000000003d3d000020000000035bd0000200000000112e000020000000001000000190840200e134000019084020021000000190000200a515000018d840000b51f0000180840002e1740000180840000f53d0000180840000a0100000180000000b51d000018000000021000000150000220941d00001400208208415000011e000200f537000011c000720a439000011c000320a43d0000110840200b53d0000110010620b53d0000110000a20953d0000110000620b53d0000110000221953d
|32=>0x400000000151000004000000001010000040000000000020000310014220b53d0000280014002b57d0000280000000b51d00002800000000100000028000000000080000240034820953d0000240020820041d000024000000020080000210014020b53d000020e01400025bf00002000350209d3d000020001582410380000200014420b53d0000200014220b53d0000200014020b53d0000200014020a51d00002000140209d3d0000200014020953d0000200014002b5fd0000200014002b53d0000200014000b5bd0000200014000b53d00002000140008409000020001400019200000200014000115e000020001400001190000200011824951d0000200010020b51d0000200010000b51d
|33=>0x540400021953d000054040000080100000510420200942000005004000008001000050040000010010000500000000b51d0000440420820953d00004404000008001000041c0200219437000041026200001160000410242000f55f0000410020a21b51d0000410020800b5170000410020021b53d0000410020021b51d0000410020003b5170000410000020b51d0000400400020b51d0000400400020841500004004000018116000040040000101160000400400000810000004004000001100000040040000004010000400262000b75f00004002420008016000040024200010160000400060800111200004000600001110000040004200095160000400042000001600004000000011010
|34=>0x400c020820143f0004008000820951f0004007020020b51f0004005000821953f0004004020020bd1f0004004010020b51f0004004000020bd1f0004003000120b51f0004003000000b51d0004003000000b5190004000014020953f00040000108201c2f0001210014420b53d0001100000020b51d000101c010420a41d000101801040080180001010014420b51d0001010010420b53d0001010010420b51d0001010000420b41d00010000000000010000080100004095390000801000040951d000080100004000100000801000000b53d0000801000000b51d0000800000040b51d0000800000040951d0000800000040001100008000000000018000054d400020951f00005404208019034
|35=>0x1120000000080010011100004020b51d001110000000080010011010010420b51d001101000440080280011000000020b51d0011000000020341d0011000000000040100110000000000000001021001020000180010000004620b51d0010000000020b51d000800000000020060006000010820142f000420f014120b53f000420c014820953f000411c000a20953f000405c0208209437000404d0208219433000404d0208201d3b000401f000120b53f000401802082180330004010000821942700040100008209427000400f014120b53f000400f000400951d000400f000100953f000400f000100951b000400d000021953f000400d0000209d3f000400c024020143f000400c020820951f
|36=>0x40000080080151e0040000080004151e004000002408604000040000020002351d004000002000231870040000020000359f00400000200000900004000002000001820040000014002b5bd0040000014002b59d004000001400225fd0040000004806bd9f0040000004002b5fd0040000004002b5dd0040000004002b5bd0040000004002b59d00400000040021d80004000000008004000040000000004b51f00400000000040540004000000000404000040000000000b51d00200000000408400002000000004004000020000000000801000113100044008418001130d000020b51d0011300014400803c0011300000420b53d00113000000008000001120001420080380011200014020b53d
|37=>0x200020d000020b5192000014000002f51f2000008020221b51f1c04000000020953b1004004000820bd1f100008c000000b51b100004c000020951b0804003000020b51f0300801000000b51d0200801000040951d008020c014000b51b008011c000200b51b0080018000000a1130080008010000215b004028011400001bc004028011400001000040200114000b53d0040200110002b51d0040200014002b5bd0040200000000010e004000400400205880040000110000b5dd0040000100000a515004000010000014020040000100000119600400001000001012004000010000004010040000100000000000400000a40861402004000008408614060040000080084b51f0040000080084040e
|38=>0x8000006000200a5774000000000040b5192004004000821b51f
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0xe00000402000
|7,0=>0x1a4000000001ec8500e1d60006e87a0a8000000220240580002c0801a4010160001880c837000000000001442bc0000000000000000000000000180001fc4b00100000800098050000000060a20007a0000000c80001d0000000e80001c000000001d81c83403700c0fc000360000005101522a3801201e00000018863000094010000c61f0000000243bc0000208e19c31806
|8,0=>0x32750384b2d67dc000f044e0e8a21415c28b5b900000005d8280604044e4cc9b2561a581063000d8cd52b0036bc476b581dc4b40023b002cb92080d334018000020030d8e782d06e030c5aaf000e99a88370120cc7781c06e5053981d55cd9824916498630003cd90e1adcba2f94c6e0599a10022755e8000d2000a41a066ac6858abc0000042e8269407a5020d056a014f918484a56c0084d34a1a5238d823e1e0009d514863c018af0020c20f18e
|8,1=>0xc0687b8163d0a1c1e07913201d4b0000fc09800000292c18511504be8b0018e40a40110300607c8fe45b870080fc291dd46498cb7000002b480007c0d299c240ba0080052013c0869e0139d100efcc03006000d59ae9060002d956b508927fdc32860fa11a44800466770562b97a8cb55bb4202246a440013ece718d8530da9d0178016ee93c008b206e4c40786a3e29201083f056741180001b474c518cb06e5b4b782b0026362a01302c0106ba66
|8,2=>0x5441a9e024e00a02c000370d200c130004f2b640c0ce06ea24b605006e225a30cf02c001252ef0541a801b380971ddd314289652a2f8004eadd980af57e6e65208a606e0065982b61022ca03980008d400066012498a70694aaa8834c690d2ff0a191974cc38a28388e4ad1c32d61e60411c9fe0e09c0bb1de73422435881000002590014561a83490730a0011889621c7dc0b00100098c3501d88400408aa13321445f8010d44e800c685224386c818
|8,3=>0x4b0111df8f56dc1c1a00082640dc1686a4f47fa21b21482214888424b2200008350d20dca7a9d2a400d5c2862c00009632500cba55986a5fa018b900043c01428a081340040b00102cd40001c0412b004301200013a5200c00018c7b06e4a2f1400037008400ed0000ba0005481600286d4f05d0d52380000006e00010008156300020000ed0848837800283646001068c505386901a004000002cc0741b8002580dc018530e0a200000102c51a0e801
|8,4=>0x222000894a805c826260dcceb801002dd57b8010011cd9f00000a414cc10b001120381512a01a4878160b401a350000820002e84e52e001bcaad4b41a59eb146fa0fd738520000dc0007a4ba9c414a9c2a8385e181d0c8ac8000de00c8f851005
|9,0=>0x64e9add847b3ca725f29bb772da0792ac4bcf549e95f3726cd9991234883d5f4b07821e8d131718454de520425524d6c3550b213e5046f29aa29eb39679ead5961f430d0948d81c6a6e063c4bd75c6b5b38be402815c01a30de1c4c01cd0f325509ca772aead7913f17b0825e4262f0b5505a0a6bc7098ab4811ef22384a536ed040230015cc342e24484816e129013e0f304b9c49849bdd51347ccf41019573a8855ffac41c6bf25135c96cfd8da959
|9,1=>0x4a4a3191ac7104e8dfdc0d3c6b14db0dc432ed2540777124dcac2b922887d5d83d3946f997abb8f31313b9f9582758b2cba4a09b21a0fa796e21e22f64210f0f9b9d6321cc6887d22464d883a2958fd4d88e24a8e116f1f842c7ed87ae849a72c7f08d9463fd29a284227317f94c1701281fbcb86e27a3745583e1564c3b79380e497bf0324b2c92ab175afe9b8abf86656d1eb1f7fc3e50c3627922d1f380626cdec2c117400670be03763a5a43aaba
|9,2=>0x8ecdf0d3406108daa0caa47e90a53b0e53c50ad348b045d104e91b02c2899bfaf005688da917025cdfc6b44789517093ba84ac8691c24b3228dc8c2b9468e29150a82661b15b249440dac473fd7e277d81c7d74f062608db0befde02ba06e059d52b434c6f2cd620c5e6875d4ac92fc15d491ed11a9ee0d2ab115054a59fa5163c53191e91e6a522c5035e71d699796be981010885352a527ae32e2f664bc9e07e131b03ce2fe798a39c538d175c0095
|9,3=>0x30f00dbc43a01a471403a287c0ecab88c8447bdbd33f0e8d6d4abba5707adfa160860a3d7339f6fc0291b18897c9ba55b167def625fbe932ae39921bf85423a1407c7b46c961aa27a21164689b241011213558472dcb9b4411aa98af3b13204e10e05e0f8a3d8e34993e6ede13a27a5098e22a241cbb8159747425a22bb7f2d490e413a2138d2c9133253e2a80a4575289f4d72a87d6ef4ab38202718551c907ee5747c3300acb09aba2205ced64d299
|9,4=>0x8d0c207da3bc77062d481ba54d0329bc95a79715c43baf0f8dfe1608c7a62ec864678d8d2a098233830e17f2a71212d0e1c566e838a36cb5678b159488e8a458d4c0c97d8fa1930607367f0c19ce69e588c1063388989e32ed595059a199468a4d46a9fa478295d108c9149f8462cd8a32e642c450cad91590c527266c5bb9e8fe8e9f531812695d42c3b7704852e15537457216aaa27c84884954
|10,0=>0x822f5ccf40f5bedb18391d32c6a1c62d06caa6ca6c96864d69b0b857c2b3d7dcb890c78a3a3114c8c89689c82ee6f1f03394cab74f1c0e5052bd95895764cdd10c8442cd30feb941fac49d98fb65831990217674be53e3dd18af8db6b36802cd1950e6824e424940987e7d5354a189cd51672694fe434da4818c11fa000d25b4ce572b0c914bb1f93a25c0411c7b8d2524edb4b394b713dc9afa614792054aa84e3363e2728b4ca5858c45f02f21acae
|10,1=>0x184f28a6b3c7ee67dc5c62676ef9acaf411c31cc4c4d7771ea318943c302e268d38d664940c58872b6d63407722a12042ea922b8954bdb1cab2256b7f3dce4a039ea828a38bd31e6b3008733ac7dd03240453212984569973149b6081ab51cd344fbb685c281c81bd906490beb31976fe5fc12892cf90ca38561260c47b044032522da2581c3986e0c8748f7a17c40980dbd1222925505d483dc8370f5d631333f13c7e2e488ca4c6a3a27db039f11ec
|10,2=>0x4668e259049102962ef20e1c9
|11,0=>0x8ca3059cac51d0426070ea8b2b30f00e61be3090a17e20467c4919d51a76061ad432b0c5d645e2eb19146c753b6f7c662dc48c7645097b89aa0ce492333e605a7103650c44d3aeb
|12,0=>0x106244811e71ceb5c840e9
|13,0=>0x82
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 11 (j%128);fld (pmP (k/32)) 68 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_253 12 roots_253 ops++addP pm 1 dzo_203_4 8 roots_203 ops++addP pm 2 dom_251 12 roots_251 ops++addP pm 3 dom_254 11 roots_254 ops++addP pm 4 dom_191 11 roots_191 ops++addP pm 5 dom_63 8 roots_63 ops++addP pm 6 dom_111 9 roots_111 ops++addP pm 7 dom_238 9 roots_238 ops++addP pm 8 dom_239 11 roots_239 ops++addP pm 9 dom_203 8 roots_203 ops++addP pm 10 dom_127 11 roots_127 ops++addP pm 11 dom_222 9 roots_222 ops++addP pm 12 dom_223 11 roots_223 ops++addP pm 13 dom_230 8 roots_230 ops++addP pm 14 dom_231 9 roots_231 ops++addP pm 15 dom_247 11 roots_247 ops++addP pm 16 dom_215 9 roots_215 ops++addP pm 17 dom_175 9 roots_175 ops++addP pm 18 dom_158 6 roots_158 ops++addP pm 19 dom_60 4 roots_60 ops++addP pm 20 dom_248 8 roots_248 ops++addP pm 21 dom_214 8 roots_214 ops++addP pm 22 dzo_171_4 6 roots_171 ops++addP pm 23 dom_139 5 roots_139 ops++addP pm 24 dom_59 7 roots_59 ops++addP pm 25 dom_183 8 roots_183 ops++addP pm 26 dom_246 9 roots_246 ops++addP pm 27 dom_159 9 roots_159 ops++addP pm 28 dom_94 6 roots_94 ops++addP pm 29 dom_75 5 roots_75 ops++addP pm 30 dom_190 8 roots_190 ops++addP pm 31 dom_179 7 roots_179 ops++addP pm 32 dom_126 8 roots_126 ops++addP pm 33 dom_95 9 roots_95 ops++addP pm 34 dom_103 6 roots_103 ops++addP pm 35 dom_202 5 roots_202 ops++addP pm 36 dom_110 6 roots_110 ops++addP pm 37 dom_195 5 roots_195 ops++addP pm 38 dom_151 6 roots_151 ops++addP pm 39 dom_167 6 roots_167 ops++addP pm 40 dzo_251_4 10 roots_251 ops++addP pm 41 dzo_235_4 9 roots_235 ops++addP pm 42 dom_187 10 roots_187 ops++addP pm 43 dom_123 10 roots_123 ops++addP pm 44 dom_119 8 roots_119 ops++addP pm 45 dom_252 9 roots_252 ops++addP pm 46 dom_31 5 roots_31 ops++addP pm 47 dom_47 5 roots_47 ops++addP pm 48 dom_55 5 roots_55 ops++addP pm 49 dom_62 5 roots_62 ops++addP pm 50 dom_87 6 roots_87 ops++addP pm 51 dzo_107_4 6 roots_107 ops++addP pm 52 dom_118 6 roots_118 ops++addP pm 53 dom_155 7 roots_155 ops++addP pm 54 dzo_219_4 9 roots_219 ops++addP pm 55 dom_245 9 roots_245 ops++addP pm 56 dom_182 6 roots_182 ops++addP pm 57 dzo_227_4 6 roots_227 ops++addP pm 58 dom_174 6 roots_174 ops++addP pm 59 dom_235 10 roots_235 ops++addP pm 60 dzo_234_4 6 roots_234 ops++addP pm 61 dzo_123_4 7 roots_123 ops++addP pm 62 dom_186 7 roots_186 ops++addP pm 63 dom_122 7 roots_122 ops++addP pm 64 dom_250 10 roots_250 ops++addP pm 65 dom_243 10 roots_243 ops++addP pm 66 dzo_187_4 7 roots_187 ops++addP pm 67 dom_107 7 roots_107 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_255 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45|h46|h47|h48|h49|h50|h51|h52|h53|h54|h55|h56|h57|h58|h59|h60|h61|h62|h63|h64|h65|h66|h67
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_203_4_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_191 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_238 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_127 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_223 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_247 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_175 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_60 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_zo_171_4_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_195 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_zo_251_4_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_zo_235_4_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h45;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h46;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h47;exact cpcs (by decide +kernel) lowS_47 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h48;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h49;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h50;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h51;exact cpcs (by decide +kernel) lowS_zo_107_4_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h52;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h53;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h54;exact cpcs (by decide +kernel) lowS_zo_219_4_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h55;exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h56;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h57;exact cpcs (by decide +kernel) lowS_zo_227_4_195 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h58;exact cpcs (by decide +kernel) lowS_174 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h59;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h60;exact cpcs (by decide +kernel) lowS_zo_234_4_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h61;exact cpcs (by decide +kernel) lowS_zo_123_4_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h62;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h63;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h64;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h65;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h66;exact cpcs (by decide +kernel) lowS_zo_187_4_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h67;exact cpcs (by decide +kernel) lowS_107 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_253 12 s (0,roots_253.map (·&&&dom_253)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_253 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_255==dom_255)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 3000009 zs symsG zs (hk 3000009 zs)
theorem ori_ok {v ys} (h:RunD true dom_255 gM v ys):RunD true dom_255 gM v (ori ys):=pickMin_runD 3000009 ys h symsG ys (hk 3000009 ys) symsG_ok h
def Z (s:Nat):=barP dom_255 gM mpG SD SS NN hAt idxH ori 3000009 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 5 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 108 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 108 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 256 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_256 : ∀ i, 256 ≤ i → i < 384 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 256 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_384 : ∀ i, 384 ≤ i → i < 512 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 384 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_512 : ∀ i, 512 ≤ i → i < 582 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 70 512 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 582 → Z 8 i = true := (range_split (range_split z8_0 z8_128) (range_split z8_256 (range_split z8_384 z8_512)))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_0 : ∀ i, 0 ≤ i → i < 128 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_128 : ∀ i, 128 ≤ i → i < 256 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_256 : ∀ i, 256 ≤ i → i < 384 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 256 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_384 : ∀ i, 384 ≤ i → i < 512 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 384 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_512 : ∀ i, 512 ≤ i → i < 625 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 113 512 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 625 → Z 9 i = true := (range_split (range_split z9_0 z9_128) (range_split z9_256 (range_split z9_384 z9_512)))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_0 : ∀ i, 0 ≤ i → i < 128 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_128 : ∀ i, 128 ≤ i → i < 256 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_256 : ∀ i, 256 ≤ i → i < 265 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 9 256 = true)
private theorem z10 : ∀ i, 0 ≤ i → i < 265 → Z 10 i = true := (range_split z10_0 (range_split z10_128 z10_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 52 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 52 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z12 : ∀ i, 0 ≤ i → i < 8 → Z 12 i = true := span_ok (by decide +kernel : span (Z 12) 8 0 = true)
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
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [7, 6] }, { op := GateOp.or, inputs := [2, 1] }, { op := GateOp.or, inputs := [5, 4] }, { op := GateOp.or, inputs := [4, 3] }, { op := GateOp.or, inputs := [11, 8] }, { op := GateOp.or, inputs := [8, 9] }, { op := GateOp.or, inputs := [3, 1] }, { op := GateOp.or, inputs := [5, 8] }, { op := GateOp.and, inputs := [0, 12] }, { op := GateOp.and, inputs := [14, 15] }, { op := GateOp.and, inputs := [13, 10] }, { op := GateOp.and, inputs := [6, 7] }, { op := GateOp.or, inputs := [16, 17] }, { op := GateOp.or, inputs := [20, 18] }, { op := GateOp.or, inputs := [21, 19] }]

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 22⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
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

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_52182_aux

theorem PEqualNP.Outside.L_meta_52182 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_52182_aux.main
