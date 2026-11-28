import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_52276_aux
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
def goal_43 : Nat := 0xffeeffeeaa00aa00ffeeffeeaa00aa00ffeeffeeaa00aa00ffeeffeeaa00aa00
def roots_43 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_45 : Nat := 0x333300003333
def goal_45 : Nat := 0xffaaffaaaa00aa00ffaaffaaaa00aa00ffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_45 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_47 : Nat := 0xffff0000ffff
def goal_47 : Nat := 0xffeeffeeaa00aa00ffeeffeeaa00aa00ffeeffeeaa00aa00ffeeffeeaa00aa00
def roots_47 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_51 : Nat := 0xf000f000f000f
def goal_51 : Nat := 0xeeeeeeeecccc0000eeeeeeeecccc0000eeeeeeeecccc0000eeeeeeeecccc0000
def roots_51 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_54 : Nat := 0x55005500550055
def goal_54 : Nat := 0xfcfcccccfcfc0000fcfcccccfcfc0000fcfcccccfcfc0000fcfcccccfcfc0000
def roots_54 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xfefeeeeefcfc0000fefeeeeefcfc0000fefeeeeefcfc0000fefeeeeefcfc0000
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_57 : Nat := 0x303030303030303
def goal_57 : Nat := 0xffaaffaaaa00aa00ffaaffaaaa00aa00ffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_57 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_58 : Nat := 0x505050505050505
def goal_58 : Nat := 0xffccffcccccc0000ffccffcccccc0000ffccffcccccc0000ffccffcccccc0000
def roots_58 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xffeeffeeeeccaa00ffeeffeeeeccaa00ffeeffeeeeccaa00ffeeffeeeeccaa00
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xfffaffaafaf0aa00fffaffaafaf0aa00fffaffaafaf0aa00fffaffaafaf0aa00
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfffeffeefefcaa00fffeffeefefcaa00fffeffeefefcaa00fffeffeefefcaa00
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_82 : Nat := 0x500050000000000050005
def goal_82 : Nat := 0xffffccccffffcccccccc0000cccc0000ffffccccffffcccccccc0000cccc0000
def roots_82 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_83 : Nat := 0xf000f00000000000f000f
def goal_83 : Nat := 0xffffccccffffcccccccc0000cccc0000ffffccccffffcccccccc0000cccc0000
def roots_83 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_84 : Nat := 0x1100110000000000110011
def goal_84 : Nat := 0xfffff0f0fffff0f0f0f00000f0f00000fffff0f0fffff0f0f0f00000f0f00000
def roots_84 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_85 : Nat := 0x3300330000000000330033
def goal_85 : Nat := 0xfffff0f0fffff0f0f0f00000f0f00000fffff0f0fffff0f0f0f00000f0f00000
def roots_85 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_86 : Nat := 0x5500550000000000550055
def goal_86 : Nat := 0xfffffcfcfffffcfcfcfc0000fcfc0000fffffcfcfffffcfcfcfc0000fcfc0000
def roots_86 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_87 : Nat := 0xff00ff0000000000ff00ff
def goal_87 : Nat := 0xfffffcfcfffffcfcfcfc0000fcfc0000fffffcfcfffffcfcfcfc0000fcfc0000
def roots_87 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_90 : Nat := 0x50505050000000005050505
def goal_90 : Nat := 0xffffccccffffcccccccc0000cccc0000ffffccccffffcccccccc0000cccc0000
def roots_90 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f
def goal_91 : Nat := 0xffffeeccffffeecceeccaa00eeccaa00ffffeeccffffeecceeccaa00eeccaa00
def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_92 : Nat := 0x111111110000000011111111
def goal_92 : Nat := 0xfffff0f0fffff0f0f0f00000f0f00000fffff0f0fffff0f0f0f00000f0f00000
def roots_92 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_93 : Nat := 0x333333330000000033333333
def goal_93 : Nat := 0xfffffaf0fffffaf0faf0aa00faf0aa00fffffaf0fffffaf0faf0aa00faf0aa00
def roots_93 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_94 : Nat := 0x555555550000000055555555
def goal_94 : Nat := 0xfffffcfcfffffcfcfcfc0000fcfc0000fffffcfcfffffcfcfcfc0000fcfc0000
def roots_94 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_95 : Nat := 0xffffffff00000000ffffffff
def goal_95 : Nat := 0xfffffefcfffffefcfefcaa00fefcaa00fffffefcfffffefcfefcaa00fefcaa00
def roots_95 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_98 : Nat := 0x5000000050000000500000005
def goal_98 : Nat := 0xffffffffcccccccccccccccc00000000ffffffffcccccccccccccccc00000000
def roots_98 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_99 : Nat := 0xf0000000f0000000f0000000f
def goal_99 : Nat := 0xffffffffcccccccceeeeeeee00000000ffffffffcccccccceeeeeeee00000000
def roots_99 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_101 : Nat := 0x33000000330000003300000033
def goal_101 : Nat := 0xfffffffff0f0f0f0aaaaaaaa00000000fffffffff0f0f0f0aaaaaaaa00000000
def roots_101 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_102 : Nat := 0x55000000550000005500000055
def goal_102 : Nat := 0xfffffffffcfcfcfccccccccc00000000fffffffffcfcfcfccccccccc00000000
def roots_102 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_103 : Nat := 0xff000000ff000000ff000000ff
def goal_103 : Nat := 0xfffffffffcfcfcfceeeeeeee00000000fffffffffcfcfcfceeeeeeee00000000
def roots_103 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_105 : Nat := 0x303000003030000030300000303
def goal_105 : Nat := 0xffffffffaa00aa00ffaaffaaaa00aa00ffffffffaa00aa00ffaaffaaaa00aa00
def roots_105 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_106 : Nat := 0x505000005050000050500000505
def goal_106 : Nat := 0xffffffffccccccccffccffcc00000000ffffffffccccccccffccffcc00000000
def roots_106 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffffffffeecceeccffeeffeeaa00aa00ffffffffeecceeccffeeffeeaa00aa00
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_108 : Nat := 0x1111000011110000111100001111
def goal_108 : Nat := 0xfffffffff0f0f0f0ff00ff0000000000fffffffff0f0f0f0ff00ff0000000000
def roots_108 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_109 : Nat := 0x3333000033330000333300003333
def goal_109 : Nat := 0xfffffffffaf0faf0ffaaffaaaa00aa00fffffffffaf0faf0ffaaffaaaa00aa00
def roots_109 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_110 : Nat := 0x5555000055550000555500005555
def goal_110 : Nat := 0xfffffffffcfcfcfcffccffcc00000000fffffffffcfcfcfcffccffcc00000000
def roots_110 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xfffffffffefcfefcffeeffeeaa00aa00fffffffffefcfefcffeeffeeaa00aa00
def roots_111 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_113 : Nat := 0x30003000300030003000300030003
def goal_113 : Nat := 0xffffffffffff0000aaaaaaaa00000000ffffffffffff0000aaaaaaaa00000000
def roots_113 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_114 : Nat := 0x50005000500050005000500050005
def goal_114 : Nat := 0xffffffffffffcccccccccccccccc0000ffffffffffffcccccccccccccccc0000
def roots_114 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def goal_115 : Nat := 0xffffffffffffcccceeeeeeeecccc0000ffffffffffffcccceeeeeeeecccc0000
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_116 : Nat := 0x110011001100110011001100110011
def goal_116 : Nat := 0xfffffffffffff0f0f0f00000f0f00000fffffffffffff0f0f0f00000f0f00000
def roots_116 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_117 : Nat := 0x330033003300330033003300330033
def goal_117 : Nat := 0xfffffffffffff0f0fafaaaaaf0f00000fffffffffffff0f0fafaaaaaf0f00000
def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xfffffffffffffcfcfcfcccccfcfc0000fffffffffffffcfcfcfcccccfcfc0000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xfffffffffffffcfcfefeeeeefcfc0000fffffffffffffcfcfefeeeeefcfc0000
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_121 : Nat := 0x3030303030303030303030303030303
def goal_121 : Nat := 0xffffffffffffaa00ffaaffaaaa00aa00ffffffffffffaa00ffaaffaaaa00aa00
def roots_121 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_122 : Nat := 0x5050505050505050505050505050505
def goal_122 : Nat := 0xffffffffffffccccffccffcccccc0000ffffffffffffccccffccffcccccc0000
def roots_122 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffffffffffffeeccffeeffeeeeccaa00ffffffffffffeeccffeeffeeeeccaa00
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_124 : Nat := 0x11111111111111111111111111111111
def goal_124 : Nat := 0xfffffffffffff0f0fff0ff00f0f00000fffffffffffff0f0fff0ff00f0f00000
def roots_124 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xfffffffffffffaf0fffaffaafaf0aa00fffffffffffffaf0fffaffaafaf0aa00
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_126 : Nat := 0x55555555555555555555555555555555
def goal_126 : Nat := 0xfffffffffffffcfcfffcffccfcfc0000fffffffffffffcfcfffcffccfcfc0000
def roots_126 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xfffffffffffffefcfffeffeefefcaa00fffffffffffffefcfffeffeefefcaa00
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_137 : Nat := 0x30300000000000000000000000000000303
def goal_137 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_137 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_141 : Nat := 0x333300000000000000000000000000003333
def goal_141 : Nat := 0xfffafffafffafffafffafffafffafffaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_141 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_146 : Nat := 0x5000500000000000000000000000000050005
def goal_146 : Nat := 0xffffccccffffccccffffccccffffcccccccc0000cccc0000cccc0000cccc0000
def roots_146 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_147 : Nat := 0xf000f000000000000000000000000000f000f
def goal_147 : Nat := 0xffffeeeeffffeeeeffffeeeeffffeeeecccc0000cccc0000cccc0000cccc0000
def roots_147 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_148 : Nat := 0x11001100000000000000000000000000110011
def goal_148 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0f0f00000f0f00000f0f00000f0f00000
def roots_148 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_149 : Nat := 0x33003300000000000000000000000000330033
def goal_149 : Nat := 0xfffffafafffffafafffffafafffffafaf0f00000f0f00000f0f00000f0f00000
def roots_149 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_150 : Nat := 0x55005500000000000000000000000000550055
def goal_150 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfcfcfc0000fcfc0000fcfc0000fcfc0000
def roots_150 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_151 : Nat := 0xff00ff00000000000000000000000000ff00ff
def goal_151 : Nat := 0xfffffefefffffefefffffefefffffefefcfc0000fcfc0000fcfc0000fcfc0000
def roots_151 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def goal_155 : Nat := 0xffffffeeffffffeeffffffeeffffffeeeeccaa00eeccaa00eeccaa00eeccaa00
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_157 : Nat := 0x3333333300000000000000000000000033333333
def goal_157 : Nat := 0xfffffffafffffffafffffffafffffffafaf0aa00faf0aa00faf0aa00faf0aa00
def roots_157 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_159 : Nat := 0xffffffff000000000000000000000000ffffffff
def goal_159 : Nat := 0xfffffffefffffffefffffffefffffffefefcaa00fefcaa00fefcaa00fefcaa00
def roots_159 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_165 : Nat := 0x330000003300000000000000000000003300000033
def goal_165 : Nat := 0xfafafafafafafafafafafafafafafafaaaaaaaaa00000000aaaaaaaa00000000
def roots_165 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_166 : Nat := 0x550000005500000000000000000000005500000055
def goal_166 : Nat := 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfccccccccc00000000cccccccc00000000
def roots_166 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_167 : Nat := 0xff000000ff0000000000000000000000ff000000ff
def goal_167 : Nat := 0xfefefefefefefefefefefefefefefefeeeeeeeee00000000eeeeeeee00000000
def roots_167 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_169 : Nat := 0x3030000030300000000000000000000030300000303
def goal_169 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_169 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_172 : Nat := 0x11110000111100000000000000000000111100001111
def goal_172 : Nat := 0xfff0fff0fff0fff0fff0fff0fff0fff0ff00ff0000000000ff00ff0000000000
def roots_172 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_173 : Nat := 0x33330000333300000000000000000000333300003333
def goal_173 : Nat := 0xfffafffafffafffafffafffafffafffaffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_173 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_175 : Nat := 0xffff0000ffff00000000000000000000ffff0000ffff
def goal_175 : Nat := 0xfffefffefffefffefffefffefffefffeffeeffeeaa00aa00ffeeffeeaa00aa00
def roots_175 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_177 : Nat := 0x300030003000300000000000000000003000300030003
def goal_177 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaaaaaaaaaa00000000aaaaaaaa00000000
def roots_177 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_178 : Nat := 0x500050005000500000000000000000005000500050005
def goal_178 : Nat := 0xffffccccffffccccffffccccffffcccccccccccccccc0000cccccccccccc0000
def roots_178 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_179 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f
def goal_179 : Nat := 0xffffeeeeffffeeeeffffeeeeffffeeeeeeeeeeeecccc0000eeeeeeeecccc0000
def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_181 : Nat := 0x3300330033003300000000000000000033003300330033
def goal_181 : Nat := 0xfffffafafffffafafffffafafffffafafafaaaaaf0f00000fafaaaaaf0f00000
def roots_181 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_182 : Nat := 0x5500550055005500000000000000000055005500550055
def goal_182 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfcfcfcccccfcfc0000fcfcccccfcfc0000
def roots_182 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_183 : Nat := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
def goal_183 : Nat := 0xfffffefefffffefefffffefefffffefefefeeeeefcfc0000fefeeeeefcfc0000
def roots_183 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffeeffffffeeffffffeeffffffeeffeeffeeeeccaa00ffeeffeeeeccaa00
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_189 : Nat := 0x333333333333333300000000000000003333333333333333
def goal_189 : Nat := 0xfffffffafffffffafffffffafffffffafffaffaafaf0aa00fffaffaafaf0aa00
def roots_189 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xfffffffefffffffefffffffefffffffefffeffeefefcaa00fffeffeefefcaa00
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_195 : Nat := 0xf000000000000000f000000000000000f000000000000000f
def goal_195 : Nat := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeecccccccccccccccc0000000000000000
def roots_195 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_197 : Nat := 0x33000000000000003300000000000000330000000000000033
def goal_197 : Nat := 0xfafafafafafafafafafafafafafafafaf0f0f0f0f0f0f0f00000000000000000
def roots_197 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_199 : Nat := 0xff00000000000000ff00000000000000ff00000000000000ff
def goal_199 : Nat := 0xfefefefefefefefefefefefefefefefefcfcfcfcfcfcfcfc0000000000000000
def roots_199 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_204 : Nat := 0x1111000000000000111100000000000011110000000000001111
def goal_204 : Nat := 0xfff0fff0fff0fff0fff0fff0fff0fff0f0f0f0f0f0f0f0f00000000000000000
def roots_204 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_205 : Nat := 0x3333000000000000333300000000000033330000000000003333
def goal_205 : Nat := 0xfffafffafffafffafffafffafffafffafaf0faf0faf0faf0aa00aa00aa00aa00
def roots_205 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_207 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def goal_207 : Nat := 0xfffefffefffefffefffefffefffefffefefcfefcfefcfefcaa00aa00aa00aa00
def roots_207 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_209 : Nat := 0x30003000000000003000300000000000300030000000000030003
def goal_209 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaaffff0000ffff00000000000000000000
def roots_209 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_210 : Nat := 0x50005000000000005000500000000000500050000000000050005
def goal_210 : Nat := 0xffffccccffffccccffffccccffffccccffffccccffffcccccccc0000cccc0000
def roots_210 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffeeeeffffeeeeffffeeeeffffeeeeffffccccffffcccccccc0000cccc0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_212 : Nat := 0x110011000000000011001100000000001100110000000000110011
def goal_212 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0f0f00000f0f00000
def roots_212 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_213 : Nat := 0x330033000000000033003300000000003300330000000000330033
def goal_213 : Nat := 0xfffffafafffffafafffffafafffffafafffff0f0fffff0f0f0f00000f0f00000
def roots_213 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfcfffffcfcfffffcfcfcfc0000fcfc0000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xfffffefefffffefefffffefefffffefefffffcfcfffffcfcfcfc0000fcfc0000
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffffeeffffffeeffffffeeffffffeeffffeeccffffeecceeccaa00eeccaa00
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def goal_221 : Nat := 0xfffffffafffffffafffffffafffffffafffffaf0fffffaf0faf0aa00faf0aa00
def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffefffffffefffffffefffffffefffffefcfffffefcfefcaa00fefcaa00
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_225 : Nat := 0x300000003000000030000000300000003000000030000000300000003
def goal_225 : Nat := 0xffffffffaaaaaaaaaaaaaaaaaaaaaaaaffffffff00000000aaaaaaaa00000000
def roots_225 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_226 : Nat := 0x500000005000000050000000500000005000000050000000500000005
def goal_226 : Nat := 0xffffffffccccccccccccccccccccccccffffffffcccccccccccccccc00000000
def roots_226 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def goal_227 : Nat := 0xffffffffeeeeeeeeeeeeeeeeeeeeeeeeffffffffcccccccceeeeeeee00000000
def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_228 : Nat := 0x1100000011000000110000001100000011000000110000001100000011
def goal_228 : Nat := 0xfffffffff0f0f0f0f0f0f0f0f0f0f0f0fffffffff0f0f0f00000000000000000
def roots_228 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_229 : Nat := 0x3300000033000000330000003300000033000000330000003300000033
def goal_229 : Nat := 0xfffffffffafafafafafafafafafafafafffffffff0f0f0f0aaaaaaaa00000000
def roots_229 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def goal_230 : Nat := 0xfffffffffcfcfcfcfcfcfcfcfcfcfcfcfffffffffcfcfcfccccccccc00000000
def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def goal_231 : Nat := 0xfffffffffefefefefefefefefefefefefffffffffcfcfcfceeeeeeee00000000
def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_232 : Nat := 0x10100000101000001010000010100000101000001010000010100000101
def goal_232 : Nat := 0xffffffffff00ff00ff00ff00ff00ff00ffffffff00000000ff00ff0000000000
def roots_232 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffaaffaaffaaffaaffaaffaaffffffffaa00aa00ffaaffaaaa00aa00
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffeeffeeffeeffeeffeeffeeffffffffeecceeccffeeffeeaa00aa00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_236 : Nat := 0x111100001111000011110000111100001111000011110000111100001111
def goal_236 : Nat := 0xfffffffffff0fff0fff0fff0fff0fff0fffffffff0f0f0f0ff00ff0000000000
def roots_236 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xfffffffffffafffafffafffafffafffafffffffffaf0faf0ffaaffaaaa00aa00
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffefffefffefffefffefffefffffffffefcfefcffeeffeeaa00aa00
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_240 : Nat := 0x1000100010001000100010001000100010001000100010001000100010001
def goal_240 : Nat := 0xffffffffffff0000ffff0000ffff0000ffffffffffff00000000000000000000
def roots_240 : List Nat := [xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_241 : Nat := 0x3000300030003000300030003000300030003000300030003000300030003
def goal_241 : Nat := 0xffffffffffffaaaaffffaaaaffffaaaaffffffffffff0000aaaaaaaa00000000
def roots_241 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def goal_242 : Nat := 0xffffffffffffccccffffccccffffccccffffffffffffcccccccccccccccc0000
def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffffeeeeffffeeeeffffeeeeffffffffffffcccceeeeeeeecccc0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_244 : Nat := 0x11001100110011001100110011001100110011001100110011001100110011
def goal_244 : Nat := 0xfffffffffffff0f0fffff0f0fffff0f0fffffffffffff0f0f0f00000f0f00000
def roots_244 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_245 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
def goal_245 : Nat := 0xfffffffffffffafafffffafafffffafafffffffffffff0f0fafaaaaaf0f00000
def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffffffcfcfffffcfcfffffcfcfffffffffffffcfcfcfcccccfcfc0000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffefefffffefefffffefefffffffffffffcfcfefeeeeefcfc0000
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffaaffffffaaffffffaaffffffffffffaa00ffaaffaaaa00aa00
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffccffffffccffffffccffffffffffffccccffccffcccccc0000
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffeeffffffeeffffffeeffffffffffffeeccffeeffeeeeccaa00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_252 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
def goal_252 : Nat := 0xfffffffffffffff0fffffff0fffffff0fffffffffffff0f0fff0ff00f0f00000
def roots_252 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffafffffffafffffffafffffffffffffaf0fffaffaafaf0aa00
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffcfffffffcfffffffcfffffffffffffcfcfffcffccfcfc0000
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffefffffffefffffffefffffffffffffefcfffeffeefefcaa00
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
def isoMvS_82:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_82:Lower true dom_82 roots_82 goal_82 4:=lower_iso_b isoMvS_82 (by decide +kernel) lowS_41
def isoMvS_84:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_84:Lower true dom_84 roots_84 goal_84 4:=lower_iso_b isoMvS_84 (by decide +kernel) lowS_41
def isoMvS_98:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_98:Lower true dom_98 roots_98 goal_98 4:=lower_iso_b isoMvS_98 (by decide +kernel) lowS_41
def isoMvS_137:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_137:Lower true dom_137 roots_137 goal_137 4:=lower_iso_b isoMvS_137 (by decide +kernel) lowS_41
def isoMvS_146:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_146:Lower true dom_146 roots_146 goal_146 4:=lower_iso_b isoMvS_146 (by decide +kernel) lowS_41
def isoMvS_148:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_148:Lower true dom_148 roots_148 goal_148 4:=lower_iso_b isoMvS_148 (by decide +kernel) lowS_41
theorem lowS_43:Lower true dom_43 roots_43 goal_43 5:=lower_slice_b [(0xc0c00000c0c,32,34)] (by decide +kernel) lowS_41
namespace S_51
def pG:List (Nat×Nat):=[(1,33),(2,18),(2,34),(3,19),(3,35),(16,18),(17,19),(17,49),(32,33),(32,34),(48,49),(48,50)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfff
def xsM:=roots_51.map (·&&&dom_51)
def gM:=goal_51&&&dom_51
def NN:Nat→Nat
|3=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0xc1dd9
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf000f00000000f0000000f0000c000c000c000ca000a000a000a
|_,_=>0
def sP:Nat→Nat
|0=>0xe4
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|_,_=>0
def wAt:=mkWire dB 4 52 0xfffffffffffff
def SS:=mkSS wAt sP sO 2 7
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def mkPools (_ _:Nat):List (Nat×Nat×(Nat×List Nat)):=[]
def mkCut (_ _:Nat) (_:Nat×Nat×Nat) (_:List Nat):Bool:=false
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_51 gM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_51 gM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat×Nat)):=[[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_51==dom_51)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_51 gM v ys):RunD true dom_51 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_51 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s:Nat) (hs:s≤3):∀ i<NN s,bar dom_51 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 1 3=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤3) (h:RunD true dom_51 gM s xsM):False:=by
  have hmin:3≤s:=by have hl:=run_len h;change 4≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_51 roots_51 goal_51 4:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_51
theorem lowS_51:Lower true dom_51 roots_51 goal_51 4:=S_51.noCircuit
theorem lowS_86:Lower true dom_86 roots_86 goal_86 5:=lower_slice_b [(0x4400440000000000440044,16,18)] (by decide +kernel) lowS_84
def isoMvS_54:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_54:Lower true dom_54 roots_54 goal_54 4:=lower_iso_b isoMvS_54 (by decide +kernel) lowS_51
def isoMvS_58:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_58:Lower true dom_58 roots_58 goal_58 4:=lower_iso_b isoMvS_58 (by decide +kernel) lowS_51
def isoMvS_99:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_99:Lower true dom_99 roots_99 goal_99 5:=lower_iso_b isoMvS_99 (by decide +kernel) lowS_43
def isoMvS_101:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_101:Lower true dom_101 roots_101 goal_101 4:=lower_iso_b isoMvS_101 (by decide +kernel) lowS_51
def isoMvS_102:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_102:Lower true dom_102 roots_102 goal_102 5:=lower_iso_b isoMvS_102 (by decide +kernel) lowS_43
def isoMvS_105:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_105:Lower true dom_105 roots_105 goal_105 5:=lower_iso_b isoMvS_105 (by decide +kernel) lowS_43
def isoMvS_106:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_106:Lower true dom_106 roots_106 goal_106 5:=lower_iso_b isoMvS_106 (by decide +kernel) lowS_43
def isoMvS_108:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_108:Lower true dom_108 roots_108 goal_108 4:=lower_iso_b isoMvS_108 (by decide +kernel) lowS_51
def isoMvS_113:List (Nat×Nat):=[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_113:Lower true dom_113 roots_113 goal_113 4:=lower_iso_b isoMvS_113 (by decide +kernel) lowS_51
def isoMvS_114:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]
theorem lowS_114:Lower true dom_114 roots_114 goal_114 5:=lower_iso_b isoMvS_114 (by decide +kernel) lowS_86
def isoMvS_116:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_116:Lower true dom_116 roots_116 goal_116 5:=lower_iso_b isoMvS_116 (by decide +kernel) lowS_43
def isoMvS_141:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_141:Lower true dom_141 roots_141 goal_141 5:=lower_iso_b isoMvS_141 (by decide +kernel) lowS_43
def isoMvS_147:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_147:Lower true dom_147 roots_147 goal_147 5:=lower_iso_b isoMvS_147 (by decide +kernel) lowS_43
def isoMvS_150:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_150:Lower true dom_150 roots_150 goal_150 5:=lower_iso_b isoMvS_150 (by decide +kernel) lowS_86
def isoMvS_165:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_165:Lower true dom_165 roots_165 goal_165 4:=lower_iso_b isoMvS_165 (by decide +kernel) lowS_51
def isoMvS_166:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_166:Lower true dom_166 roots_166 goal_166 4:=lower_iso_b isoMvS_166 (by decide +kernel) lowS_51
def isoMvS_169:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_169:Lower true dom_169 roots_169 goal_169 5:=lower_iso_b isoMvS_169 (by decide +kernel) lowS_86
def isoMvS_172:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_172:Lower true dom_172 roots_172 goal_172 4:=lower_iso_b isoMvS_172 (by decide +kernel) lowS_51
def isoMvS_177:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_177:Lower true dom_177 roots_177 goal_177 4:=lower_iso_b isoMvS_177 (by decide +kernel) lowS_51
def isoMvS_178:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_178:Lower true dom_178 roots_178 goal_178 5:=lower_iso_b isoMvS_178 (by decide +kernel) lowS_43
def isoMvS_195:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)]
theorem lowS_195:Lower true dom_195 roots_195 goal_195 4:=lower_iso_b isoMvS_195 (by decide +kernel) lowS_51
def isoMvS_197:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_197:Lower true dom_197 roots_197 goal_197 4:=lower_iso_b isoMvS_197 (by decide +kernel) lowS_51
def isoMvS_204:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_204:Lower true dom_204 roots_204 goal_204 4:=lower_iso_b isoMvS_204 (by decide +kernel) lowS_51
def isoMvS_209:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_209:Lower true dom_209 roots_209 goal_209 4:=lower_iso_b isoMvS_209 (by decide +kernel) lowS_51
def isoMvS_212:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_212:Lower true dom_212 roots_212 goal_212 5:=lower_iso_b isoMvS_212 (by decide +kernel) lowS_86
def isoMvS_225:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_225:Lower true dom_225 roots_225 goal_225 4:=lower_iso_b isoMvS_225 (by decide +kernel) lowS_51
def isoMvS_226:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_226:Lower true dom_226 roots_226 goal_226 5:=lower_iso_b isoMvS_226 (by decide +kernel) lowS_43
def isoMvS_228:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_228:Lower true dom_228 roots_228 goal_228 4:=lower_iso_b isoMvS_228 (by decide +kernel) lowS_51
def isoMvS_232:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_232:Lower true dom_232 roots_232 goal_232 4:=lower_iso_b isoMvS_232 (by decide +kernel) lowS_51
def isoMvS_240:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_240:Lower true dom_240 roots_240 goal_240 4:=lower_iso_b isoMvS_240 (by decide +kernel) lowS_51
theorem lowS_55:Lower true dom_55 roots_55 goal_55 5:=lower_slice_b [(0xaa00aa00aa00aa,32,33)] (by decide +kernel) lowS_54
def dzo_43_16:=0xf0f00000f0f0000
def gzo_43_16:=0xf0e00000e0c0000
def gsh_43_16:=0xf0e00000e0c
theorem lowS_zo_43_16_41:Lower true dzo_43_16 roots_43 gzo_43_16 5:=lower_iso_b (d1:=dom_43) (r1:=roots_43) (T1:=gsh_43_16) [(dom_43,16)] (by decide +kernel) (lower_slice_b (T:=gsh_43_16) [(0xc0c00000c0c,0,2)] (by decide +kernel) lowS_41)
namespace S_59
def pG:List (Nat×Nat):=[(1,9),(1,33),(2,18),(2,34),(3,11),(3,19),(3,35),(8,9),(8,40),(10,11),(10,26),(10,42),(16,18),(17,19),(17,25),(17,49),(24,25),(24,26),(24,56),(32,33),(32,34),(32,40),(48,49),(48,50),(48,56)]
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
|4,0=>0xb120e1f10d
|5,0=>0xdeb70a6f001a42
|6,0=>0x9abd7
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0a0f0a0f0a0f0af0f0f0f0f000f0000f000f00000000f000f000f000f00505050505000500f0f0f0f00000000f0f00000f0f0000f000f000a000a00c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a
|_,_=>0
def sP:Nat→Nat
|0=>0x436104396108436104361074361543210
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x15405
|5,0=>0x166418a6
|6,0=>0x1c5
|_,_=>0
def wAt:=mkWire dB 10 60 0xfffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x11b
|_=>0
def oO:Nat→Nat→Nat
|5,0=>1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 5
def pmP:Nat→Nat
|0=>0x1f6a040
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x53
|6,0=>4
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_43 5 roots_43 ops++addP pm 1 dom_58 4 roots_58 ops++addP pm 2 dzo_43_16 5 roots_43 ops++addP pm 3 dom_51 4 roots_51 ops++addP pm 4 dom_41 4 roots_41 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_59 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_43_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_41 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_43 5 s (0,roots_43.map (·&&&dom_43)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_59 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_43 h
def symsG:List (List (Nat×Nat)):=[[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
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
theorem lowS_61:Lower true dom_61 roots_61 goal_61 6:=lower_slice_b [(0x3030303030303030,16,20),(0x3333000033330000,4,20)] (by decide +kernel) lowS_41
theorem lowS_103:Lower true dom_103 roots_103 goal_103 6:=lower_slice_b [(0xaa000000aa000000aa000000aa,32,33)] (by decide +kernel) lowS_102
namespace S_107
def pG:List (Nat×Nat):=[(1,9),(1,33),(2,34),(2,66),(3,11),(3,35),(3,67),(8,9),(8,40),(10,11),(10,42),(10,74),(32,33),(32,34),(32,40),(32,96),(64,66),(64,96),(65,67),(65,73),(65,97),(72,73),(72,74),(72,104)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_107.map (·&&&dom_107)
def gM:=goal_107&&&dom_107
def NN:Nat→Nat
|3=>1
|4=>4
|5=>10
|6=>4
|7=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0xe2d1
|4,0=>0x4eba71f4b81033305105
|5,0=>0x7c22774f80492ce3856a23a040da900ca210c32408ad601d56
|6,0=>0xb40cf7ad9f734c404510
|7,0=>0xb40cf
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0c00000f0c00000f0c00000f0c000000000000000050500000000f0f00000f0f0000000f00000000f0f00000c0c00000f0f00000c0cf0f00000e0e00000f0f00000e0ef0f00000f0000000f0f00000f00f0c0000000000000f0c0000000000f0000000f0000000f0000000af0f0000000000000f0f00000000f0000000f0000000f0000000f000000000000000000d0d00000c0ca0a00000a0a00000a0a00000a0af0f00000a0a00000f0f00000a0af0f00000f0000000f0a00000f00c0c00000c0c00000c0c00000c0cf0f00000f0f0000000000000000
|0,1=>0xf0f00000000f0f00000f0f00000f0000000f00f0f0000000000000f000000000000f0000000a0000000f0000000a00000000f0c0000000000000f0c505000000000000050500000000303000002020000030300000202
|_,_=>0
def sP:Nat→Nat
|0=>0x1cc1200e60900c3982401ec6090077982401cd4090070926019c24980e60924019cc1880e60920061de6200e6091c03982468167304803882402921200e1220073142418820
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|4,0=>0x26a3944a845
|5,0=>0x26b48584cf19b330654c918f3186
|6,0=>0xcab7dacb536
|7,0=>0x6a5
|_,_=>0
def wAt:=mkWire dB 23 108 0xfffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x3853830993d419b39138539b611385
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x61004200000031002102
|6,0=>0x918171
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 8
def pmP:Nat→Nat
|0=>0xff7d5e289185080
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x6020403015
|6,0=>0x7889
|7,0=>9
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 6 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_106 5 roots_106 ops++addP pm 1 dom_41 4 roots_41 ops++addP pm 2 dom_99 5 roots_99 ops++addP pm 3 dom_98 4 roots_98 ops++addP pm 4 dom_43 5 roots_43 ops++addP pm 5 dom_105 5 roots_105 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_107 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_98 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_105 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_106 5 s (0,roots_106.map (·&&&dom_106)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_107 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_106 h
def symsG:List (List (Nat×Nat)):=[[(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0x2222222222222222222222222222222222222222222222222222222222222222,1)],[(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_107==dom_107)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_107 gM v ys):RunD true dom_107 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_107 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 4 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
theorem checked (s:Nat) (hs:s≤7):∀ i<NN s,bar dom_107 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤7) (h:RunD true dom_107 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_107 roots_107 goal_107 8:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_107
theorem lowS_107:Lower true dom_107 roots_107 goal_107 8:=S_107.noCircuit
def dzo_114_1:=0xa000a000a000a000a000a000a000a
def gzo_114_1:=0xa000a000a0008000a000a00080000
def gsh_114_1:=0x50005000500040005000500040000
theorem lowS_zo_114_1_82:Lower true dzo_114_1 roots_114 gzo_114_1 5:=lower_iso_b (d1:=dom_114) (r1:=roots_114) (T1:=gsh_114_1) [(dom_114,1)] (by decide +kernel) (lower_slice_b (T:=gsh_114_1) [(0x50005000000000005000500000000,0,32)] (by decide +kernel) lowS_82)
namespace S_115
def pG:List (Nat×Nat):=[(1,33),(2,18),(2,34),(2,66),(3,19),(3,35),(3,67),(16,18),(16,80),(17,19),(17,49),(17,81),(32,33),(32,34),(32,96),(48,49),(48,50),(48,112),(64,66),(64,80),(64,96),(65,67),(65,81),(65,97)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_115.map (·&&&dom_115)
def gM:=goal_115&&&dom_115
def NN:Nat→Nat
|4=>1
|5=>1
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xc3387
|5,0=>0xf31a
|6,0=>0x88c8c
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0000000f0000000f0000000f0000f000f000f000f000c000c000c000cf000f00000000000f000f00000000c000c000c000c000c000c000c000ca000a000a000a000a000a000a000a0000f0000000f0000000c0000000cf000f000f000f0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x99a135684688
|_=>0
def sO:Nat→Nat→Nat
|4,0=>5
|5,0=>0x56
|6,0=>0xb5
|_,_=>0
def wAt:=mkWire dB 7 116 0xfffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 9
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x61
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
addP pm 0 dom_114 5 roots_114 ops++addP pm 1 dom_113 4 roots_113 ops++addP pm 2 dzo_114_1 5 roots_114 ops++addP pm 3 dom_99 5 roots_99 ops++addP pm 4 dom_51 4 roots_51 ops++addP pm 5 dom_82 4 roots_82 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_115 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_114_1_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_82 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_114 5 s (0,roots_114.map (·&&&dom_114)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_115 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_114 h
def symsG:List (List (Nat×Nat)):=[[(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_115==dom_115)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_115 gM v ys):RunD true dom_115 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_115 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_115 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_115 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_115 roots_115 goal_115 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_115
theorem lowS_115:Lower true dom_115 roots_115 goal_115 7:=S_115.noCircuit
namespace S_118
def pG:List (Nat×Nat):=[(2,18),(2,34),(2,66),(4,20),(4,68),(6,22),(6,38),(6,70),(16,18),(16,20),(16,80),(32,34),(32,96),(36,38),(36,52),(36,100),(48,50),(48,52),(48,112),(64,66),(64,68),(64,80),(64,96)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffff
def xsM:=roots_118.map (·&&&dom_118)
def gM:=goal_118&&&dom_118
def NN:Nat→Nat
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x93d49
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x550055000000000055005500000000aa000000aa000000aa000000aa000140014001400140014001400140014220022002200220022002200220022550055005500550000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x4688
|_=>0
def sO:Nat→Nat→Nat
|6,0=>5
|_,_=>0
def wAt:=mkWire dB 5 119 0x7fffffffffffffffffffffffffffff
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
addP pm 0 dom_116 5 roots_116 ops++addP pm 1 dom_114 5 roots_114 ops++addP pm 2 dom_102 5 roots_102 ops++addP pm 3 dom_86 5 roots_86 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_118 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_86 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_116 5 s (0,roots_116.map (·&&&dom_116)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_118 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_116 h
def symsG:List (List (Nat×Nat)):=[[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_118==dom_118)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_118 gM v ys):RunD true dom_118 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_118 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_118 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_151:Lower true dom_151 roots_151 goal_151 6:=lower_slice_b [(0xaa00aa00000000000000000000000000aa00aa,128,129)] (by decide +kernel) lowS_150
theorem lowS_167:Lower true dom_167 roots_167 goal_167 5:=lower_slice_b [(0xaa000000aa0000000000000000000000aa000000aa,32,33)] (by decide +kernel) lowS_166
theorem lowS_179:Lower true dom_179 roots_179 goal_179 6:=lower_slice_b [(0xa000a000a000a0000000000000000000a000a000a000a,32,33)] (by decide +kernel) lowS_178
theorem lowS_214:Lower true dom_214 roots_214 goal_214 6:=lower_slice_b [(0x440044000000000044004400000000004400440000000000440044,16,18)] (by decide +kernel) lowS_212
namespace S_229
def pG:List (Nat×Nat):=[(1,33),(1,129),(4,68),(4,132),(5,37),(5,69),(5,133),(32,33),(32,96),(36,37),(36,100),(36,164),(64,68),(64,96),(65,69),(65,97),(65,193),(128,129),(128,132),(160,161),(160,164),(160,224),(192,193),(192,196),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1ffffff
def xsM:=roots_229.map (·&&&dom_229)
def gM:=goal_229&&&dom_229
def NN:Nat→Nat
|4=>2
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x40121330d8
|5,0=>0x60d97305ba23834
|6,0=>0x23834
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x3300000033000000330000003300000030000000300000003000000030cc000000cc0000008800000088000000cc000000cc000000880000008b000000030000000300000003000000030000000300000003000000030cc000000c00000000000000000000000cc000000c00000000000000003300000000000000330000000000000033000000000000003300000000880000008800000088000000880000008800000088000000880000008b3000000330000000000000000000000330000003300000000000000000c0000000c0000000c0000000c0000000c0000000c0000000000000003300000033000000330000003300000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x46320486320467320463204635043210
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x15405
|5,0=>0x1563d8a5
|6,0=>0x1b5
|_,_=>0
def wAt:=mkWire dB 9 230 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffff
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
|5,0=>0x24
|6,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 2 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_228 4 roots_228 ops++addP pm 1 dom_225 4 roots_225 ops++addP pm 2 dom_165 4 roots_165 ops++addP pm 3 dom_101 4 roots_101 ops++addP pm 4 dom_197 4 roots_197 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_229 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_228 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_225 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_165 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_101 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_197 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_228 4 s (0,roots_228.map (·&&&dom_228)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_229 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_228 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff00000000ffffffff00000000,96),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xffffffffffffffff0000000000000000,64),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_229==dom_229)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_229 gM v ys):RunD true dom_229 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_229 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_229 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_229 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_229 roots_229 goal_229 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_229
theorem lowS_229:Lower true dom_229 roots_229 goal_229 7:=S_229.noCircuit
def isoMvS_91:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_91:Lower true dom_91 roots_91 goal_91 6:=lower_iso_b isoMvS_91 (by decide +kernel) lowS_61
def isoMvS_93:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_93:Lower true dom_93 roots_93 goal_93 6:=lower_iso_b isoMvS_93 (by decide +kernel) lowS_61
def isoMvS_109:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_109:Lower true dom_109 roots_109 goal_109 7:=lower_iso_b isoMvS_109 (by decide +kernel) lowS_59
def isoMvS_110:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_110:Lower true dom_110 roots_110 goal_110 6:=lower_iso_b isoMvS_110 (by decide +kernel) lowS_103
def isoMvS_117:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_117:Lower true dom_117 roots_117 goal_117 7:=lower_iso_b isoMvS_117 (by decide +kernel) lowS_59
def isoMvS_121:List (Nat×Nat):=[(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_121:Lower true dom_121 roots_121 goal_121 7:=lower_iso_b isoMvS_121 (by decide +kernel) lowS_59
def isoMvS_122:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_122:Lower true dom_122 roots_122 goal_122 7:=lower_iso_b isoMvS_122 (by decide +kernel) lowS_115
def isoMvS_124:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_124:Lower true dom_124 roots_124 goal_124 7:=lower_iso_b isoMvS_124 (by decide +kernel) lowS_59
def isoMvS_155:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)]
theorem lowS_155:Lower true dom_155 roots_155 goal_155 8:=lower_iso_b isoMvS_155 (by decide +kernel) lowS_107
def isoMvS_157:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_157:Lower true dom_157 roots_157 goal_157 8:=lower_iso_b isoMvS_157 (by decide +kernel) lowS_107
def isoMvS_173:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_173:Lower true dom_173 roots_173 goal_173 7:=lower_iso_b isoMvS_173 (by decide +kernel) lowS_115
def isoMvS_181:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_181:Lower true dom_181 roots_181 goal_181 7:=lower_iso_b isoMvS_181 (by decide +kernel) lowS_59
def isoMvS_182:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_182:Lower true dom_182 roots_182 goal_182 7:=lower_iso_b isoMvS_182 (by decide +kernel) lowS_115
def isoMvS_199:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_199:Lower true dom_199 roots_199 goal_199 5:=lower_iso_b isoMvS_199 (by decide +kernel) lowS_167
def isoMvS_205:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_205:Lower true dom_205 roots_205 goal_205 7:=lower_iso_b isoMvS_205 (by decide +kernel) lowS_59
def isoMvS_211:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)]
theorem lowS_211:Lower true dom_211 roots_211 goal_211 7:=lower_iso_b isoMvS_211 (by decide +kernel) lowS_115
def isoMvS_213:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_213:Lower true dom_213 roots_213 goal_213 7:=lower_iso_b isoMvS_213 (by decide +kernel) lowS_115
def isoMvS_227:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)]
theorem lowS_227:Lower true dom_227 roots_227 goal_227 6:=lower_iso_b isoMvS_227 (by decide +kernel) lowS_179
def isoMvS_230:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_230:Lower true dom_230 roots_230 goal_230 6:=lower_iso_b isoMvS_230 (by decide +kernel) lowS_179
def isoMvS_233:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_233:Lower true dom_233 roots_233 goal_233 7:=lower_iso_b isoMvS_233 (by decide +kernel) lowS_115
def isoMvS_236:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_236:Lower true dom_236 roots_236 goal_236 7:=lower_iso_b isoMvS_236 (by decide +kernel) lowS_229
def isoMvS_241:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_241:Lower true dom_241 roots_241 goal_241 7:=lower_iso_b isoMvS_241 (by decide +kernel) lowS_229
def isoMvS_242:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)]
theorem lowS_242:Lower true dom_242 roots_242 goal_242 7:=lower_iso_b isoMvS_242 (by decide +kernel) lowS_118
def isoMvS_244:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_244:Lower true dom_244 roots_244 goal_244 7:=lower_iso_b isoMvS_244 (by decide +kernel) lowS_115
theorem lowS_63:Lower true dom_63 roots_63 goal_63 8:=lower_slice_b [(0xf0f0f0f0f0f0f0f0,16,20)] (by decide +kernel) lowS_59
theorem lowS_95:Lower true dom_95 roots_95 goal_95 7:=lower_slice_b [(0xaaaaaaaa00000000aaaaaaaa,8,9),(0xff00ff0000000000ff00ff00,1,9)] (by decide +kernel) lowS_86
theorem lowS_111:Lower true dom_111 roots_111 goal_111 9:=lower_slice_b [(0xf0f00000f0f00000f0f00000f0f0,64,68)] (by decide +kernel) lowS_107
def dzo_86_1:=0xaa00aa0000000000aa00aa
def gzo_86_1:=0xaa00a80000000000a80000
def gsh_86_1:=0x5500540000000000540000
theorem lowS_zo_86_1_86:Lower true dzo_86_1 roots_86 gzo_86_1 5:=lower_iso_b (d1:=dom_86) (r1:=roots_86) (T1:=gsh_86_1) [(dom_86,1)] (by decide +kernel) (lower_slice_b (T:=gsh_86_1) [] (by decide +kernel) lowS_86)
def dzo_118_1:=0xaa00aa00aa00aa00aa00aa00aa00aa
def gzo_118_1:=0xaa00aa00aa00a800aa00aa00a80000
def gsh_118_1:=0x550055005500540055005500540000
theorem lowS_zo_118_1_86:Lower true dzo_118_1 roots_118 gzo_118_1 6:=lower_iso_b (d1:=dom_118) (r1:=roots_118) (T1:=gsh_118_1) [(dom_118,1)] (by decide +kernel) (lower_slice_b (T:=gsh_118_1) [(0x550055000000000055005500000000,0,32)] (by decide +kernel) lowS_86)
namespace S_119
def pG:List (Nat×Nat):=[(1,33),(2,18),(2,34),(2,66),(3,19),(3,35),(3,67),(4,20),(4,68),(5,21),(5,37),(5,69),(6,22),(6,38),(6,70),(7,23),(7,39),(7,71),(16,18),(16,20),(16,80),(17,19),(17,21),(17,49),(17,81),(32,33),(32,34),(32,96),(36,37),(36,38),(36,52),(36,100),(48,49),(48,50),(48,52),(48,112),(64,66),(64,68),(64,80),(64,96),(65,67),(65,69),(65,81),(65,97)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_119.map (·&&&dom_119)
def gM:=goal_119&&&dom_119
def NN:Nat→Nat
|4=>3
|5=>10
|6=>17
|7=>7
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x9991e69d932ef8d
|5,0=>0xac77f9f53794c388dd538542b81527572904a62530a9716b96
|6,0=>0xec6d6de44bd8383c23d5b1c91a8e48a4e71a0b88873f760cc153a794872e3875a361f73222e2b7ce0b8f3
|7,0=>0xe8d9fde33bd6a41d10f384cb0721ca5d38a
|8,0=>0xdaa04
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf000f000f000f000f0000000f00005500ff000000ff00550055000000003300330033003300330033003300000f000f000f000f000f000f000f00000f0000000f000f000f0000000f0000ff00ff00ff00ff0000000000000000ff00ff00ff00000000000000000000ff00ff00ff00ff00ff00ff00000000ff000000ff000000ff000000ff0000ff00ff00ff00f000f000f000f000f0cc00cc00cc00cc00cc00cc00cc00ccff00ff0000000000ff00ff00000000ff00ff00ff00ff00ff000000ff0000f000f000f000f000f000f000f000f0ff00ff00ff00cc00cc00cc00cc00ccaa00aa00aa00aa00aa00aa00aa00aa
|0,1=>0xff000000ff000000ff0000000000000000ff00ff0000000000ff0000aa00ff00aa00ff00aa00aa00aa00aa00000000ff00ff0000000000000000ff000000ff00ff00ff000000ff0000ff00ff00ff00ff00550055000000000000000000000000ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00000000ff000000ff0000000000000000ff00ff000000ff00ff00ff00000000ff00ff00ff000000ff00ff00ff0000000000000000ff0000000000000000550055000000000055005500000000ff00ff00ff00ff00aa00aa00aa00aa
|_,_=>0
def sP:Nat→Nat
|0=>0x1162a20ce22c15621c4502a84388a054c831140a21c450292419ca07a8871140a910e58bd443960f510e22b9443880d510e628148388a0490e50314438820510e502d44188a04a0e2080833140418820
|1=>0x21c45028871140aa90e22c544388a0568871160a410e22815321c4502883388a0510e22c55521c4507544388a0e28871176a264e2281443940f510e22e15341c4502ae4388a051067
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0xa5055005
|5,0=>0x4563f63963362d62762161b61560f6
|6,0=>0xb87b17aa7a469d79769168a78377c77576e76776075975274b7
|7,0=>0xe77e16da7d46cd7c67bf7
|8,0=>0xee6
|_,_=>0
def wAt:=mkWire dB 30 120 0xffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x3aa20322a02922921d3a93aa20320e3a90553aa3e922a18b3a98a920321d2299ab21d2033a90293a920d3a92553aa21d3a99a821d18b3a99aa21d
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x1e2001c2689825894248902388c2288821884208802
|7,0=>0x261946418c62184601
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 10
def pmP:Nat→Nat
|0=>0xffbfbd7d71443f3d2b21190c08070300
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0xa01b36b2144715941
|7,0=>0xdcefe9d
|8,0=>8
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 8 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_118 7 roots_118 ops++addP pm 1 dzo_86_1 5 roots_86 ops++addP pm 2 dom_103 6 roots_103 ops++addP pm 3 dom_115 7 roots_115 ops++addP pm 4 dom_86 5 roots_86 ops++addP pm 5 dom_117 7 roots_117 ops++addP pm 6 dzo_118_1 6 roots_118 ops++addP pm 7 dom_55 5 roots_55 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_119 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_86_1_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_118_1_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_55 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_118 7 s (0,roots_118.map (·&&&dom_118)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_119 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_118 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_119 gM v ys):RunD true dom_119 gM v (ori ys):=h
def Z (s:Nat):=barP dom_119 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 17 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 17 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 7 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 7 0 = true)
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
def dzo_41_16:=0x303000003030000
def gzo_41_16:=0x302000002000000
def gsh_41_16:=0x30200000200
theorem lowS_zo_41_16_41:Lower true dzo_41_16 roots_41 gzo_41_16 4:=lower_iso_b (d1:=dom_41) (r1:=roots_41) (T1:=gsh_41_16) [(dom_41,16)] (by decide +kernel) (lower_slice_b (T:=gsh_41_16) [] (by decide +kernel) lowS_41)
def dzo_107_16:=0xf0f00000f0f00000f0f00000f0f0000
def gzo_107_16:=0xf0f00000f0f00000f0e00000e0c0000
def gsh_107_16:=0xf0f00000f0f00000f0e00000e0c
theorem lowS_zo_107_16_41:Lower true dzo_107_16 roots_107 gzo_107_16 6:=lower_iso_b (d1:=dom_107) (r1:=roots_107) (T1:=gsh_107_16) [(dom_107,16)] (by decide +kernel) (lower_slice_b (T:=gsh_107_16) [(0xc0c00000c0c00000c0c00000c0c,0,2),(0xf0f00000f0f0000000000000000,0,64)] (by decide +kernel) lowS_41)
def dzo_105_16:=0x3030000030300000303000003030000
def gzo_105_16:=0x3030000030300000302000002000000
def gsh_105_16:=0x303000003030000030200000200
theorem lowS_zo_105_16_41:Lower true dzo_105_16 roots_105 gzo_105_16 5:=lower_iso_b (d1:=dom_105) (r1:=roots_105) (T1:=gsh_105_16) [(dom_105,16)] (by decide +kernel) (lower_slice_b (T:=gsh_105_16) [(0x303000003030000000000000000,0,64)] (by decide +kernel) lowS_41)
def dzo_90_1:=0xa0a0a0a000000000a0a0a0a
def gzo_90_1:=0xa0a0a08000000000a080a00
def gsh_90_1:=0x50505040000000005040500
theorem lowS_zo_90_1_82:Lower true dzo_90_1 roots_90 gzo_90_1 5:=lower_iso_b (d1:=dom_90) (r1:=roots_90) (T1:=gsh_90_1) [(dom_90,1)] (by decide +kernel) (lower_slice_b (T:=gsh_90_1) [(0x50005000000000005000500,0,8)] (by decide +kernel) lowS_82)
def dzo_83_8:=0xf000f00000000000f000f00
def gzo_83_8:=0xf000e00000000000e000a00
def gsh_83_8:=0xf000e00000000000e000a
theorem lowS_zo_83_8_82:Lower true dzo_83_8 roots_83 gzo_83_8 5:=lower_iso_b (d1:=dom_83) (r1:=roots_83) (T1:=gsh_83_8) [(dom_83,8)] (by decide +kernel) (lower_slice_b (T:=gsh_83_8) [(0xa000a00000000000a000a,0,1)] (by decide +kernel) lowS_82)
def dzo_122_1:=0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a
def gzo_122_1:=0xa0a0a0a0a0a0a080a0a0a0a0a080a00
def gsh_122_1:=0x5050505050505040505050505040500
theorem lowS_zo_122_1_82:Lower true dzo_122_1 roots_122 gzo_122_1 6:=lower_iso_b (d1:=dom_122) (r1:=roots_122) (T1:=gsh_122_1) [(dom_122,1)] (by decide +kernel) (lower_slice_b (T:=gsh_122_1) [(0x5000500050005000500050005000500,0,8),(0x5050505000000000505050500000000,0,32)] (by decide +kernel) lowS_82)
def dzo_115_8:=0xf000f000f000f000f000f000f000f00
def gzo_115_8:=0xf000f000f000e000f000f000e000a00
def gsh_115_8:=0xf000f000f000e000f000f000e000a
theorem lowS_zo_115_8_82:Lower true dzo_115_8 roots_115 gzo_115_8 6:=lower_iso_b (d1:=dom_115) (r1:=roots_115) (T1:=gsh_115_8) [(dom_115,8)] (by decide +kernel) (lower_slice_b (T:=gsh_115_8) [(0xa000a000a000a000a000a000a000a,0,1),(0xf000f00000000000f000f00000000,0,32)] (by decide +kernel) lowS_82)
namespace S_123
def pG:List (Nat×Nat):=[(1,9),(1,33),(2,18),(2,34),(2,66),(3,11),(3,19),(3,35),(3,67),(8,9),(8,40),(10,11),(10,26),(10,42),(10,74),(16,18),(16,80),(17,19),(17,25),(17,49),(17,81),(24,25),(24,26),(24,56),(24,88),(32,33),(32,34),(32,40),(32,96),(48,49),(48,50),(48,56),(48,112),(64,66),(64,80),(64,96),(65,67),(65,73),(65,81),(65,97),(72,73),(72,74),(72,88),(72,104)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_123.map (·&&&dom_123)
def gM:=goal_123&&&dom_123
def NN:Nat→Nat
|5=>4
|6=>15
|7=>24
|8=>8
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0x4edfa43e2138fd11f4ee
|6,0=>0xbf80ab81618e642823cf775e273010531e74f5bf4ea6b499173543a352da33abc0fc1d0d0a1
|7,0=>0xe7fb0a7d1b872ff80af17b99d768f3756366b8185d3245b4b1599c34f929449a9388c92e5222df802a039205631d0481ac5e1861b150fc0cc9507550
|8,0=>0xe3f54cdd92ad2d25459947c683cae432d0c07721
|9,0=>0x62b5b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f0f0f0f0f0f0f0f0f0000000000f000f00000000000f000f00000000c0f0c0f0c0c0c0c0c0f0c0f0c0c0c0cf0f0f0f0f0f0f0f0c0c0c0c0c0c0c0ca0a0a0a0a000a000a0a0a0a0a000a0000f000f000a000a000f000f000a000a0000f0f00000f0f00000c0c00000c0c0000000000000000f0f0f0f0c0c0c0cf0f00000f0f00000f0f00000f0f00003030303030303030303030300000000f0f0f0f000000000f0f0f0f00000000f000f000f000f000f000f000f000f00c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a00f0f0f00000f0f000f0c0f00000c0cf0f0f0f0f0f0f0f0000000000000000
|0,1=>0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0000000000000000e0e0e0e0e0e0e0ef0f0f0f0f0f0f0f0f0c0f0c0f0c0f0cf0f0f0f0f0f00000f0f0f0f0f0f000000000000000000003030303000000005050505000000000505050500000000f0f0f0f0f0f0f0f0d0d0d0d0c0c0c0cf0a0f0a0f0a0f0a0f0a0f0a0f0a0f0af0f0f0f0f000f000f0f0f0f0f000f005050505050005000505050505000500f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0cf0f0f0f0a0a0a0a0f0f0f0f0a0a0a0af000f000a000a000f000f000a000a000000000000000000c0f0c0f0c0c0c0cf0f0f0f00000f0f0f0f0f0f00000c0cf0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c
|0,2=>0xf0f0f0f0f0f0f0f0a0a0a0a0a0a0a0af0f05050f0f00000f0f05050f0f0000f0f0f0f0f0f0f0f03030303000000000000000000000000f0f0f0f000000003030303000000000303030300000000f0f03030f0f00000f0f03030f0f0000
|_,_=>0
def sP:Nat→Nat
|0=>0x103c710c0941440c224040814710c08510308e24040f14710c0851c46430801581030890051c430358040f1c40860151471021801474cc0c20051c448308044510308020f1471030851c434c0801440cb24014308a2402051c40861440c2040
|1=>0x8401471035801471030a301c4040c20051d30c201088710308040814710308016010308040f14710308014710c0c26803c51c43030851c478308054f1471030801477440c20051c434308014710308601c4051030805051c430308014710309b
|2=>0x51c40c201c1440c20051d81030801471030a10051c40c26801471039420051c43030805051c40c200f1471030801440c224014760430308016410308040f1c40c20151471030807040c2
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x9303180cc006
|6,0=>0x1e58e4e6b7323975cace4f7243905c74e33716389983ee187
|7,0=>0x903462224d0b7823bf99f0cf1775b3959bced686833221810b97593aaa146e9c74aba39d0d07f7
|8,0=>0xabb541e92f4279dbcd1e5af267
|9,0=>0x15d6
|_,_=>0
def wAt:=mkWire dB 38 124 0xfffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x142450314350031434785143c50d1404301142c301140407e0834f0d1404c110c04e0d144cf0f140451d14345090c045330c0430114345011cc8301400c50d1cc8301144c301143450131a4301142c7320c0570b14443013c3c501543d001143541014243010c0500314345013834513
|1=>0x51d102450f142c2010c0450914047320c043011024769142c50d1404f0d140450f147570b1446101143c51d1435410
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x80cf11c232658c999121c63084986300014411802
|7,0=>0xa253ca694b29251ca29432824fc9e93b2724dc9a9332624bc9692b25249c929232
|8,0=>0xb43646c0d71ac3546a0d31
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0xa11209ffc09f48108901f8603f0407d5809cb013560260c0401807ff00ff601fac03f4807c100f560070c00e1001bd00352006080081801000018000204001800008000080000c000100000
|1=>0x613a982112a16acc0ff907ff1a7d224fa449d4881e9
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x40
|6,0=>0x1a10a14e08418755c003248
|7,0=>0x32795065e89251d6cd50e61b8569a03d37d2
|8,0=>0x9284608578d1
|9,0=>0xb
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 19 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_107 8 roots_107 ops++addP pm 1 dzo_41_16 4 roots_41 ops++addP pm 2 dzo_107_16 6 roots_107 ops++addP pm 3 dom_122 7 roots_122 ops++addP pm 4 dzo_105_16 5 roots_105 ops++addP pm 5 dom_115 7 roots_115 ops++addP pm 6 dom_91 6 roots_91 ops++addP pm 7 dom_121 7 roots_121 ops++addP pm 8 dom_59 7 roots_59 ops++addP pm 9 dzo_90_1 5 roots_90 ops++addP pm 10 dzo_83_8 5 roots_83 ops++addP pm 11 dom_41 4 roots_41 ops++addP pm 12 dzo_122_1 6 roots_122 ops++addP pm 13 dom_105 5 roots_105 ops++addP pm 14 dom_82 4 roots_82 ops++addP pm 15 dzo_114_1 5 roots_114 ops++addP pm 16 dzo_43_16 5 roots_43 ops++addP pm 17 dzo_115_8 6 roots_115 ops++addP pm 18 dom_114 5 roots_114 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_123 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_41_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_107_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_zo_105_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_90_1_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_83_8_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_122_1_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_114_1_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_43_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_115_8_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_114 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_107 8 s (0,roots_107.map (·&&&dom_107)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_123 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_107 h
def symsG:List (List (Nat×Nat)):=[[(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_123==dom_123)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_123 gM v ys):RunD true dom_123 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_123 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 4 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 15 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 24 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 24 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 8 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 0 = true)
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
def dzo_124_1:=0x22222222222222222222222222222222
def gzo_124_1:=0x22222222222222202222222222202200
def gsh_124_1:=0x11111111111111101111111111101100
theorem lowS_zo_124_1_84:Lower true dzo_124_1 roots_124 gzo_124_1 6:=lower_iso_b (d1:=dom_124) (r1:=roots_124) (T1:=gsh_124_1) [(dom_124,1)] (by decide +kernel) (lower_slice_b (T:=gsh_124_1) [(0x11001100110011001100110011001100,0,8),(0x11111111000000001111111100000000,0,32)] (by decide +kernel) lowS_84)
def dzo_92_1:=0x222222220000000022222222
def gzo_92_1:=0x222222200000000022202200
def gsh_92_1:=0x111111100000000011101100
theorem lowS_zo_92_1_84:Lower true dzo_92_1 roots_92 gzo_92_1 5:=lower_iso_b (d1:=dom_92) (r1:=roots_92) (T1:=gsh_92_1) [(dom_92,1)] (by decide +kernel) (lower_slice_b (T:=gsh_92_1) [(0x110011000000000011001100,0,8)] (by decide +kernel) lowS_84)
def dzo_57_4:=0x3030303030303030
def gzo_57_4:=0x3030302030302000
def gsh_57_4:=0x303030203030200
theorem lowS_zo_57_4_41:Lower true dzo_57_4 roots_57 gzo_57_4 5:=lower_iso_b (d1:=dom_57) (r1:=roots_57) (T1:=gsh_57_4) [(dom_57,4)] (by decide +kernel) (lower_slice_b (T:=gsh_57_4) [(0x303000003030000,0,16)] (by decide +kernel) lowS_41)
def dzo_85_8:=0x330033000000000033003300
def gzo_85_8:=0x330032000000000032002200
def gsh_85_8:=0x3300320000000000320022
theorem lowS_zo_85_8_84:Lower true dzo_85_8 roots_85 gzo_85_8 5:=lower_iso_b (d1:=dom_85) (r1:=roots_85) (T1:=gsh_85_8) [(dom_85,8)] (by decide +kernel) (lower_slice_b (T:=gsh_85_8) [(0x2200220000000000220022,0,1)] (by decide +kernel) lowS_84)
def dzo_45_16:=0x3333000033330000
def gzo_45_16:=0x3332000032300000
def gsh_45_16:=0x333200003230
theorem lowS_zo_45_16_41:Lower true dzo_45_16 roots_45 gzo_45_16 5:=lower_iso_b (d1:=dom_45) (r1:=roots_45) (T1:=gsh_45_16) [(dom_45,16)] (by decide +kernel) (lower_slice_b (T:=gsh_45_16) [(0x303000003030,0,4)] (by decide +kernel) lowS_41)
def dzo_116_1:=0x220022002200220022002200220022
def gzo_116_1:=0x220022002200200022002200200000
def gsh_116_1:=0x110011001100100011001100100000
theorem lowS_zo_116_1_84:Lower true dzo_116_1 roots_116 gzo_116_1 5:=lower_iso_b (d1:=dom_116) (r1:=roots_116) (T1:=gsh_116_1) [(dom_116,1)] (by decide +kernel) (lower_slice_b (T:=gsh_116_1) [(0x110011000000000011001100000000,0,32)] (by decide +kernel) lowS_84)
def dzo_105_4:=0x3030000030300000303000003030
def gzo_105_4:=0x3030000030300000302000002000
def gsh_105_4:=0x303000003030000030200000200
theorem lowS_zo_105_4_41:Lower true dzo_105_4 roots_105 gzo_105_4 5:=lower_iso_b (d1:=dom_105) (r1:=roots_105) (T1:=gsh_105_4) [(dom_105,4)] (by decide +kernel) (lower_slice_b (T:=gsh_105_4) [(0x303000003030000000000000000,0,64)] (by decide +kernel) lowS_41)
def dzo_121_4:=0x30303030303030303030303030303030
def gzo_121_4:=0x30303030303030303030302030302000
def gsh_121_4:=0x3030303030303030303030203030200
theorem lowS_zo_121_4_41:Lower true dzo_121_4 roots_121 gzo_121_4 6:=lower_iso_b (d1:=dom_121) (r1:=roots_121) (T1:=gsh_121_4) [(dom_121,4)] (by decide +kernel) (lower_slice_b (T:=gsh_121_4) [(0x3030000030300000303000003030000,0,16),(0x3030303030303030000000000000000,0,64)] (by decide +kernel) lowS_41)
def dzo_109_16:=0x33330000333300003333000033330000
def gzo_109_16:=0x33330000333300003332000032300000
def gsh_109_16:=0x3333000033330000333200003230
theorem lowS_zo_109_16_41:Lower true dzo_109_16 roots_109 gzo_109_16 6:=lower_iso_b (d1:=dom_109) (r1:=roots_109) (T1:=gsh_109_16) [(dom_109,16)] (by decide +kernel) (lower_slice_b (T:=gsh_109_16) [(0x3030000030300000303000003030,0,4),(0x3333000033330000000000000000,0,64)] (by decide +kernel) lowS_41)
def dzo_117_8:=0x33003300330033003300330033003300
def gzo_117_8:=0x33003300330032003300330032002200
def gsh_117_8:=0x330033003300320033003300320022
theorem lowS_zo_117_8_84:Lower true dzo_117_8 roots_117 gzo_117_8 6:=lower_iso_b (d1:=dom_117) (r1:=roots_117) (T1:=gsh_117_8) [(dom_117,8)] (by decide +kernel) (lower_slice_b (T:=gsh_117_8) [(0x220022002200220022002200220022,0,1),(0x330033000000000033003300000000,0,32)] (by decide +kernel) lowS_84)
namespace S_125
def pG:List (Nat×Nat):=[(1,9),(1,33),(4,20),(4,68),(5,13),(5,21),(5,37),(5,69),(8,9),(8,40),(12,13),(12,28),(12,44),(12,76),(16,20),(16,80),(17,21),(17,25),(17,49),(17,81),(24,25),(24,28),(24,56),(24,88),(32,33),(32,40),(32,96),(36,37),(36,44),(36,52),(36,100),(48,49),(48,52),(48,56),(48,112),(64,68),(64,80),(64,96),(65,69),(65,73),(65,81),(65,97),(72,73),(72,76),(72,88),(72,104)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffffff
def xsM:=roots_125.map (·&&&dom_125)
def gM:=goal_125&&&dom_125
def NN:Nat→Nat
|4=>1
|5=>3
|6=>9
|7=>18
|8=>10
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x2851c
|5,0=>0x5fe035d09911ca6
|6,0=>0xe5c58db4ae4cdbb446b93cbb937d1f30f8917350016f9
|7,0=>0x74b3a70b7d5cbc75c4af43d003efe83e9c23e6342bd652a6d01f1a212a730dd3f0bc0f08ea508a8d02f71002ab
|8,0=>0x95de87f2e47749274b3a6951e642d24624f1d4c00f7ba067c2
|9,0=>0x7f2e4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcccccccc88888888cccccccc8888888b3223322332233223322332233223322cccccccccc00cc00cccccccccc00cc033333333333333333333000033330000cc00cc0088008800cc00cc008800880333300003333000030300000303000000c0c0c0c0c0c0c0c0c0c00000c0c00033330000333300003333000033330000cc00cc00cc00cc00cc00cc00cc00cc030303030303030303030000030300000444444444400440044444444440044033333333000000003333333300000000cccccc00cccc8800ccc0cc00c8c0880303030303030303030303030303030308888888888888888888888888888888b3333333333333330000000000000000
|0,1=>0xcc00cc0000000000cc00cc00000001111111100000000111111110000000088888888cccccccc0000000000000003333333303030303333333330000000000000000cccc0000cccc0000cccc000232323232323232322222222222222220000cccc000000000000cccc000000030300000303030303030000030303030cccccccc000000000000000000000003333333333333333333333330000000000000000cccccccccccccccc0000000111133330000333311111111000000000c0c0c0c0c0c0c0c00000000000000000003333000033330000000000000000ccccc0c0ccccc0c0ccccc0c0ccccc0c33333333333333333030303030303030
|0,2=>0x33333333333300003333333333330000ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc333333332222222222222222222222220000000000000000cccccccc0000000000000003333333300000000000000000c0c0c0c000000000c0c0c0c000000033330303333300003333030333330000
|_,_=>0
def sP:Nat→Nat
|0=>0x1c20403c420708101211b1c20403c44481c20405881c20571081c26810042076010152070815952070811081c20540042070850131082c20404844482c20403c41c228100420e1c124010c2070850042c22810042071490042071850040c2040
|1=>0x5842070810261081c20401081c20408842251c20401081c205900f1081c20401081c20404d61081c204011120e1c20401081c29008c81c20623c42074020401112070817801201c20401082c20401081c205f0131081c204074420704901c108
|2=>0x1081c20401081c20405c420708100420e1c2040
|_=>0
def sO:Nat→Nat→Nat
|4,0=>5
|5,0=>0x45816c056
|6,0=>0x4e5243105c74e337163895c3ce177
|7,0=>0x190ec085d32d19590a484f3261921089741b1f1ce906e63341818b2e536
|8,0=>0x21af076803be5de4eeb7723b75dacecf7
|9,0=>0x1146
|_,_=>0
def wAt:=mkWire dB 39 126 0x3fffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x10007051004811100821d2048111080848910088091c1415d10004031008201044411220248850848f1c044441f080807b0448c0b200444d0808405200885f00401112024401100014d0808267204965f1004400597c4011000d071074f1c10148023c701112100201302c80104d8711
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x1031a6000590830c410811002
|7,0=>0x1a9332624bc9692b25249c9292324247c8e91b23245c8a9132
|8,0=>0x1f88007c2f45e0bb1742e45c0b71
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0xc00bf163ad2003913db224f63001c452f8840d0c4061801c2a3581c5f02db60596c0a25813db01ed603bfc03fd806fb00c960190801fd802db004be007ec00258000d0001000008000080000
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x64804410423
|7,0=>0x1bd73357d9d4facf12b2688
|8,0=>0x1abfb78df4331
|9,0=>5
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 19 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_124 7 roots_124 ops++addP pm 1 dom_121 7 roots_121 ops++addP pm 2 dzo_124_1 6 roots_124 ops++addP pm 3 dom_109 7 roots_109 ops++addP pm 4 dzo_92_1 5 roots_92 ops++addP pm 5 dzo_57_4 5 roots_57 ops++addP pm 6 dom_117 7 roots_117 ops++addP pm 7 dzo_85_8 5 roots_85 ops++addP pm 8 dzo_45_16 5 roots_45 ops++addP pm 9 dom_93 6 roots_93 ops++addP pm 10 dom_61 6 roots_61 ops++addP pm 11 dzo_116_1 5 roots_116 ops++addP pm 12 dzo_105_4 5 roots_105 ops++addP pm 13 dom_105 5 roots_105 ops++addP pm 14 dzo_121_4 6 roots_121 ops++addP pm 15 dom_84 4 roots_84 ops++addP pm 16 dzo_109_16 6 roots_109 ops++addP pm 17 dom_116 5 roots_116 ops++addP pm 18 dzo_117_8 6 roots_117 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_125 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_124_1_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_zo_92_1_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_zo_57_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_85_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_45_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_116_1_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_105_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_121_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_109_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_117_8_84 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_124 7 s (0,roots_124.map (·&&&dom_124)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_125 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_124 h
def symsG:List (List (Nat×Nat)):=[[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_125==dom_125)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_125 gM v ys):RunD true dom_125 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_125 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 9 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 18 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 18 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 10 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 10 0 = true)
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
theorem lowS_159:Lower true dom_159 roots_159 goal_159 9:=lower_slice_b [(0xcccccccc000000000000000000000000cccccccc,16,18)] (by decide +kernel) lowS_157
theorem lowS_175:Lower true dom_175 roots_175 goal_175 8:=lower_slice_b [(0xcccc0000cccc00000000000000000000cccc0000cccc,32,34)] (by decide +kernel) lowS_173
def dzo_151_32:=0xff00ff00000000000000000000000000ff00ff00000000
def gzo_151_32:=0xff00fe00000000000000000000000000fe00ee00000000
def gsh_151_32:=0xff00fe00000000000000000000000000fe00ee
theorem lowS_zo_151_32_148:Lower true dzo_151_32 roots_151 gzo_151_32 6:=lower_iso_b (d1:=dom_151) (r1:=roots_151) (T1:=gsh_151_32) [(dom_151,32)] (by decide +kernel) (lower_slice_b (T:=gsh_151_32) [(0xaa00aa00000000000000000000000000aa00aa,0,1),(0xcc00cc00000000000000000000000000cc00cc,0,2)] (by decide +kernel) lowS_148)
namespace S_183
def pG:List (Nat×Nat):=[(1,33),(1,129),(2,18),(2,34),(2,130),(3,19),(3,35),(3,131),(4,20),(4,132),(5,21),(5,37),(5,133),(6,22),(6,38),(6,134),(7,23),(7,39),(7,135),(16,18),(16,20),(16,144),(17,19),(17,21),(17,49),(17,145),(32,33),(32,34),(36,37),(36,38),(36,52),(36,164),(48,49),(48,50),(48,52),(48,176),(128,129),(128,130),(128,132),(128,144),(160,161),(160,162),(160,164),(160,176)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_183.map (·&&&dom_183)
def gM:=goal_183&&&dom_183
def NN:Nat→Nat
|4=>5
|5=>15
|6=>37
|7=>10
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xe4bbfd57328e2585c3454b346
|5,0=>0xfcb6efb964e65a2c4dabb980ba531e9c9da961a18657878c52644cc1acdd19ad30adf10494b
|6,0=>0xfed70f4680e30b0da542d49a5cb550ca919c9042c4d7cc2de9bab12b58a3b34a2aab8aa886d9e7789b7128263b71534662c0652a364b44646c4644cc5b6f25b34757a833c7733678f3386e2d7bd27c20246ea2048f189eb156ff0df13
|7,0=>0xcf017bc3d3ac7aaa886da2cd06b2e960448490a5329ef04aba
|8,0=>0x8a6fe
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xff000000ff000000000000000000000000000000000000ff00ff00ff00ff000000000000000000ff00ff0000000000000000000000000000000000000000ff00f000ff00f0f000f000f000f0000000000000000000f000f000f000f0ff00cc00ff00cc000000000000000000cc00cc00cc00cc0f000f000f000f0000000000000000000f0000000f0000ff000000ff0000000000000000000000ff000000ff0000fe00fe00fe00fe000000000000000000fe00ee00fe00eefc00fc00fc00fc000000000000000000fc00cc00fc00ccff00ff00ff00ff000000000000000000000000000000000000ff000000ff000000000000000000ff000000ff0000ff00ff00000000000000000000000000ff00ff00000000ff00ff00ff00ff000000000000000000ff000000ff0000cc00cc00cc00cc000000000000000000cc00cc00cc00ccaa00aa00aa00aa000000000000000000aa00aa00aa00aa00000f0000000f0000000000000000000f0000000f0000
|0,1=>0xf0000000f0000ff00ff00ff00ff000000000000000000ff00f000ff00f0ff00ff00ff0000000000000000000000ff00ff000000000000f0000000f0000000000000000000f000f000f000f0ff00ff000000ff000000000000000000ff00ff00000000f000f000f000f0000000000000000000f0000000f0000000000000000000000000000000000000ff000000ff00000000ff000000ff00000000000000000000000000000000ff00ff00ff00ff0000000000000000000f0000000f0000ff00f000ff00f0000000000000000000ff00f000ff00f0ff00ff00ff00ff000000000000000000f000f000f000f0ff000f00ff000f000000000000000000ff000000ff0000ff00f000ff00f0000000000000000000f000f000f000f000000000000000000000000000000000ff00ff000000000f0000000f00000000000000000000000f0000000f00000f000f000f000f00000000000000000000000000000000
|0,2=>0xff00ff000f000f000000000000000000ff00ff00000000ff000000000000000000000000000000ff00ff00000000f000f000f000f0000000000000000000ff00f000ff00f0ff00aa00ff00aa000000000000000000aa00aa00aa00aaf0000000f00000000000000000000000ff000000ff00000000ff00000000000000000000000000ff00ff00000000
|_,_=>0
def sP:Nat→Nat
|0=>0x8144640425a08119b24c0811842470461053020442420574045835420445020511840c204a3c40d308138908128648908128610308145010908128610324704610314c08110330b04e3493020440cb04a1050812842481c61050810040c2040
|1=>0x25530204434930204610324204a1a024c08118424c0817c611424c08118458954204638930205118424204a1840cc08144611e24c08119d24c08118425308118e58930204610325a08118458330204611664c0811840c9302050109702046109
|2=>0x24c08119810954c08118424c08144611624c0811a524c0811a424c0811848c930204638324c08118e25930204610330204f48324c08118424c0815c648964c08118424c08128611930205810930288610984c08118424c2c11840c9302046103
|3=>0x424c08118424c08119038930204648930204610324c0811842593020461093020463c4
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x14507a82940aa005
|5,0=>0x1a94caa5f62cb14d89ac4852130f186cc30615309183ea196
|6,0=>0x15f6acb549e96f4479f34dde60f297913c71a2cd0f784b409df6ef4776bb9d9c0ed97693b2dd8acbe75bbac5956ca474eba59d1ee8874131edceac6f6
|7,0=>0x344f9c6cb363df10f817bd3dcded8f657
|8,0=>0x1a96
|_,_=>0
def wAt:=mkWire dB 38 184 0xffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xc1a106441b246491b246091a306493324c4441306846324689182464919246c91a04f4918250c23d2460919246443f24604190ccc919246443d2460c3d2460419246491b2464c3f246033024644612469a090cc0919658491b24689192464c3d246091908f4918
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0xa31cc00184000003300000000000000000c00
|6,0=>0x2f2b480000000acaa1000000028298a518c80088400845f200000001e1709b1001925c9610015150531448003c8d2
|7,0=>0xe8791e0771d8751d0731c8711
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 10
def pmP:Nat→Nat
|0=>0xf5fd5edf77dd757c5705324c53109021c8219460140421003708c120400b01c0500800
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x1c60300030000008480
|6,0=>0x15a01497b00904a2b9b8c02d0000945005246098ab68114
|7,0=>0x2f6beb5bde339
|8,0=>0x15
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 10 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_182 7 roots_182 ops++addP pm 1 dom_51 4 roots_51 ops++addP pm 2 dom_181 7 roots_181 ops++addP pm 3 dom_165 4 roots_165 ops++addP pm 4 dom_179 6 roots_179 ops++addP pm 5 dom_147 5 roots_147 ops++addP pm 6 dom_55 5 roots_55 ops++addP pm 7 dom_167 5 roots_167 ops++addP pm 8 dzo_151_32 6 roots_151 ops++addP pm 9 dom_151 6 roots_151 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_183 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_165 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_151_32_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_151 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_182 7 s (0,roots_182.map (·&&&dom_182)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_183 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_182 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_183 gM v ys):RunD true dom_183 gM v (ori ys):=h
def Z (s:Nat):=barP dom_183 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 5 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 15 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 37 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 37 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 10 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_183 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_183 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_183 roots_183 goal_183 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_183
theorem lowS_183:Lower true dom_183 roots_183 goal_183 9:=S_183.noCircuit
theorem lowS_187:Lower true dom_187 roots_187 goal_187 9:=lower_slice_b [(0xf0f0f0f0000000000000000000000000f0f0f0f00000000,1,33)] (by decide +kernel) lowS_155
theorem lowS_207:Lower true dom_207 roots_207 goal_207 8:=lower_slice_b [(0xcccc000000000000cccc000000000000cccc000000000000cccc,64,66)] (by decide +kernel) lowS_205
theorem lowS_215:Lower true dom_215 roots_215 goal_215 8:=lower_slice_b [(0xcc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc,16,18)] (by decide +kernel) lowS_213
namespace S_231
def pG:List (Nat×Nat):=[(1,33),(1,129),(2,34),(2,66),(2,130),(3,35),(3,67),(3,131),(4,68),(4,132),(5,37),(5,69),(5,133),(6,38),(6,70),(6,134),(7,39),(7,71),(7,135),(32,33),(32,34),(32,96),(36,37),(36,38),(36,100),(36,164),(64,66),(64,68),(64,96),(65,67),(65,69),(65,97),(65,193),(128,129),(128,130),(128,132),(160,161),(160,162),(160,164),(160,224),(192,193),(192,194),(192,196),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_231.map (·&&&dom_231)
def gM:=goal_231&&&dom_231
def NN:Nat→Nat
|4=>5
|5=>16
|6=>36
|7=>9
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xfd74a637f154e6441612266a7
|5,0=>0xf51f7b6f31a754e8877482674733a56d3df6c0705f8175d52558d8045c3a24c9c1dc140e60108208
|6,0=>0xe576fde89eda142d5472cf4accd1f4b806b9ea379c02e90dbe8d9f6790ee75ada707566daf5669a0621f7615fb60e3657787565d95518e52b0645c3a449453989537d0335fa82fbdd2667220ed11d1410ae4c04e9c040ab02837
|7,0=>0xe576fa938b8cb8877bca4b9034096b34ab92d26919f5b
|8,0=>0x9aff0
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xff000000000000000000000000000000ff000000000000000000000000ff000000ff0000000000000000000000ff000000ff00000000ff00000000000000ff00000000000000ff00000000000000ff00000000aa000000aa000000aa000000aa000000aa000000ff000000aa000000aaff000000ff0000000000000000000000ff000000ff0000000000000000ff000000ff000000ff000000ff000000ff00000000000000ff00000000ff000000f0000000f0000000f0000000ff000000f0000000f0000000f0ff000000ff000000ff000000ff000000ff000000ff0000000000000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000000000000000ff000000ff000000ff00000000000000ff000000ff00000000cc000000cc000000cc000000cc000000cc000000cc000000cc000000cc00000000000000000000000000000000ff000000ff000000ff00000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000f0ff000000cc000000cc000000cc000000ff000000cc000000cc000000ccaa000000aa000000aa000000aa000000aa000000aa000000aa000000aaff000000ff000000ff000000ff00000000000000000000000000000000
|0,1=>0xff00000000000000ff00000000000000ff00000000000000000000000000000000000000000000000000000000ff00000000000000ff00000000ff000000ff0000000000000000000000ff000000ff000000ff000000005500000055000000000000000000000055000000550000000000000000aa00000000000000ff00000000000000aa00000000000000ff00000000ff000000f0000000ff000000f0000000ff000000f0000000ff000000f0330000003300000033000000330000003300000033000000330000000000000000ff00000000000000ff00000000000000ff0000000000000000ff000000aa000000aa000000aa000000ff000000aa000000aa000000aaff000000000000000000000000000000ff0000000000000000000000000f0000000f0000000f0000000f000000000000000f0000000000000000ff000000ff000000ff00000000000000ff000000ff000000ff00000000ff000000ff000000ff000000ff000000ff000000000000000000000000ff000000ff0000000000000000000000ff00000000000000000000000055000000550000005500000055000000550000005500000055000000000000000000000000ff000000000000000000000000000000ff00000000
|0,2=>0xff0000000f000000ff00000000000000ff0000000f000000ff00000000aa000000aa000000ff000000aa000000aa000000aa000000ff000000aaff00000055000000ff00000000000000ff00000055000000ff00000000000000000000000000000000000000000000000000000000ff000000000000000000000000ff000000aa0000000000000000000000ff000000aaff00000000000000ff000000000000000000000000000000ff00000000000000000f0000000000000000000000000000000f0000000000000000f0000000f0000000f0000000f0000000ff000000f0000000ff000000f00000000000000000ff000000ff0000000000000000000000ff00000000ff000000ff000000ff000000f0000000ff000000ff000000ff000000f0ff000000ff000000ff000000ff0000000f000000000000000f0000000055000000550000005500000000000000550000005500000055000000005500000055000000550000005500000055000000000000005500000000ff000000ff000000ff000000ff00000000000000ff00000000000000000f000000000000000f000000000000000f000000000000000f0000000000000000f0000000f0000000f000000000000000f0000000f0000000f0
|0,3=>0xff000000ff00000000000000000f0000000f00000000000000000000000f0000000f0000000000000000ff000000ff000000f0000000f0000000ff000000ff000000f0000000f000000000ff000000ff000000ff00000000000000000000000000000000ff000000aa000000ff000000aa000000ff000000aa000000ff000000aaff000000ff000000aa000000aa000000ff000000ff000000aa000000aa
|_,_=>0
def sP:Nat→Nat
|0=>0x2c06940c504b00d0c164b0070c50560100c50580040c505600d0c55c800a0c204b0140c20402831572c028314121634504b54050e0c50403431412d33431412123431512c038314100d0c530b00a0c20482891412070c20401831410040c2040
|1=>0x2d300db031412c0acd0c504b00da831412c03431412e902834504b00d9c31412c098d0c504b00d0c504b4cd24504b00a3431632c034314194b34314190b00d0c58cb00d0c504b88050314184b00d80504b00d0c504b7c074d0c504b00d6c3141
|2=>0x5803500c504b01a3431412c03730c504b0143431412c03430812c04031413c02831412d60140c50560073431412c03431412f210d0c504b01e0c504b3c02831412cf0313431702c0bcd0c504b00a34314120bb8d0c504b02d3431412c0343141
|3=>0x3431412c050d0c504b00d0c504bd4034314120b00d0c504bd0034314184b00d0c504b
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x14507a82940aa005
|5,0=>0x38b1ad8cac5f62cb14d89ca4862130f186cc30615309183ea196
|6,0=>0xb13d71aacd4f7a4b509e78d357973c9de40f197893c2de08efd77b3bbddd0ee176db351d9aec7660b2e9d68cad753b281d32e936463a15cfce777
|7,0=>0x1a17cd3e4df18f857bf3dddee0f697
|8,0=>0x1a86
|_,_=>0
def wAt:=mkWire dB 54 232 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x34b4b032c0432e0cd8d2c2cd83350cb4d2e2cd8b3434b4d2c3484b015808d2c34b8d230de4d032ca960134b03592cd012a34061010cd812a3404d2e0d6cb342de5c3634b503d34b8b36
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0xc00
|6,0=>0x7c9e1709a26080000171000000000000000584000000050931001123c8d22c80024881000620005110431
|7,0=>0x291a0671986519063188611
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 10
def pmP:Nat→Nat
|0=>0xecdeadccdc9d7e56e56004e54bd1000a0084062061044041040019018008005004002001000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x400000000020
|6,0=>0x4316349c8000de0300002800008c015b42009401029d2
|7,0=>0x11842f6a4f17
|8,0=>0x15
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 12 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_229 7 roots_229 ops++addP pm 1 dom_197 4 roots_197 ops++addP pm 2 dom_103 6 roots_103 ops++addP pm 3 dom_99 5 roots_99 ops++addP pm 4 dom_102 5 roots_102 ops++addP pm 5 dom_167 5 roots_167 ops++addP pm 6 dom_199 5 roots_199 ops++addP pm 7 dom_230 6 roots_230 ops++addP pm 8 dom_166 4 roots_166 ops++addP pm 9 dom_195 4 roots_195 ops++addP pm 10 dom_227 6 roots_227 ops++addP pm 11 dom_226 5 roots_226 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_231 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_229 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_197 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_166 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_195 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_226 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_229 7 s (0,roots_229.map (·&&&dom_229)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_231 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_229 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_231==dom_231)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_231 gM v ys):RunD true dom_231 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_231 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 5 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 36 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 36 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 9 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_231 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_231 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_231 roots_231 goal_231 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_231
theorem lowS_231:Lower true dom_231 roots_231 goal_231 9:=S_231.noCircuit
def dzo_173_64:=0x333300003333000000000000000000003333000033330000000000000000
def gzo_173_64:=0x333300003332000000000000000000003333000032300000000000000000
def gsh_173_64:=0x33330000333200000000000000000000333300003230
theorem lowS_zo_173_64_137:Lower true dzo_173_64 roots_173 gzo_173_64 6:=lower_iso_b (d1:=dom_173) (r1:=roots_173) (T1:=gsh_173_64) [(dom_173,64)] (by decide +kernel) (lower_slice_b (T:=gsh_173_64) [(0x30300000303000000000000000000000303000003030,0,4),(0x33330000000000000000000000000000333300000000,0,32)] (by decide +kernel) lowS_137)
def dzo_137_64:=0x303000000000000000000000000000003030000000000000000
def gzo_137_64:=0x302000000000000000000000000000002000000000000000000
def gsh_137_64:=0x30200000000000000000000000000000200
theorem lowS_zo_137_64_137:Lower true dzo_137_64 roots_137 gzo_137_64 4:=lower_iso_b (d1:=dom_137) (r1:=roots_137) (T1:=gsh_137_64) [(dom_137,64)] (by decide +kernel) (lower_slice_b (T:=gsh_137_64) [] (by decide +kernel) lowS_137)
def dzo_233_4:=0x303000003030000030300000303000003030000030300000303000003030
def gzo_233_4:=0x303000003030000030300000303000003030000030300000302000002000
def gsh_233_4:=0x30300000303000003030000030300000303000003030000030200000200
theorem lowS_zo_233_4_41:Lower true dzo_233_4 roots_233 gzo_233_4 6:=lower_iso_b (d1:=dom_233) (r1:=roots_233) (T1:=gsh_233_4) [(dom_233,4)] (by decide +kernel) (lower_slice_b (T:=gsh_233_4) [(0x30300000303000000000000000000000303000003030000000000000000,0,64),(0x30300000303000003030000030300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_41)
def dzo_141_64:=0x3333000000000000000000000000000033330000000000000000
def gzo_141_64:=0x3332000000000000000000000000000032300000000000000000
def gsh_141_64:=0x333200000000000000000000000000003230
theorem lowS_zo_141_64_137:Lower true dzo_141_64 roots_141 gzo_141_64 5:=lower_iso_b (d1:=dom_141) (r1:=roots_141) (T1:=gsh_141_64) [(dom_141,64)] (by decide +kernel) (lower_slice_b (T:=gsh_141_64) [(0x303000000000000000000000000000003030,0,4)] (by decide +kernel) lowS_137)
def dzo_169_4:=0x30300000303000000000000000000000303000003030
def gzo_169_4:=0x30300000303000000000000000000000302000002000
def gsh_169_4:=0x3030000030300000000000000000000030200000200
theorem lowS_zo_169_4_41:Lower true dzo_169_4 roots_169 gzo_169_4 5:=lower_iso_b (d1:=dom_169) (r1:=roots_169) (T1:=gsh_169_4) [(dom_169,4)] (by decide +kernel) (lower_slice_b (T:=gsh_169_4) [(0x3030000030300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_41)
def dzo_41_4:=0x303000003030
def gzo_41_4:=0x302000002000
def gsh_41_4:=0x30200000200
theorem lowS_zo_41_4_41:Lower true dzo_41_4 roots_41 gzo_41_4 4:=lower_iso_b (d1:=dom_41) (r1:=roots_41) (T1:=gsh_41_4) [(dom_41,4)] (by decide +kernel) (lower_slice_b (T:=gsh_41_4) [] (by decide +kernel) lowS_41)
namespace S_237
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,129),(4,68),(4,132),(5,13),(5,37),(5,69),(5,133),(8,9),(8,40),(8,136),(12,13),(12,44),(12,76),(12,140),(32,33),(32,40),(32,96),(36,37),(36,44),(36,100),(36,164),(64,68),(64,96),(65,69),(65,73),(65,97),(65,193),(72,73),(72,76),(72,104),(72,200),(128,129),(128,132),(128,136),(160,161),(160,164),(160,168),(160,224),(192,193),(192,196),(192,200),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_237.map (·&&&dom_237)
def gM:=goal_237&&&dom_237
def NN:Nat→Nat
|4=>2
|5=>15
|6=>56
|7=>31
|8=>8
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x9f22a25fa7
|5,0=>0xaa0e583414804cd6b1d76448f561715149a475e846c7f43a8b19845176d91520f1084d0297a
|6,0=>0xdc46ed0f47cc0b0b86beafa72a7a439e4fe9957f992f28a633745ae6ab516869f6370460e575b03b52d75516704f3c14e8e24bf7f4b9ef46ee64634b43a8b4372a3a35b32cd32ed422d3c82cbd32cb812b902258a5251e32278f2211e21bd61f5ed1de3d1b4b21b0a618b06178a81764012c9b104a10b6a00ac7509523077fc049cd03a6a019820158600af0
|7,0=>0xb618fac38b8d1868c725866bd81cde7ebd77811758b0b58798508204e6714c28046821455fc40d2c3e8e7369d6343353378a317053161c2ec622ea752625a24c36161771574c12bf512af606308
|8,0=>0xf0cadd9f3dc30fbbad38743d35a8794e2f643d29
|9,0=>0xf0cad
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcc000000cc000000cc000000cc000000cc00000000000000cc0000000001100000011000000000000000000000011000033330000000000000000cccc000000000000cccc000000000000cccc000000000000cccc0000000000000003333000000000000333300000000000033000000000000003300cc000000cc000000cc000000cc000000cc000000cc000000cc000000cc022220000222200002222000022220000222200002222000022220000222200000000cccc000000000000cccc000000000000cccc000000000000cc8b33300003333000033330000333300000000000000000000000000000000cccc0000cccc0000cccc0000cccc0000cccc000000000000cccc0000000332200003322000033220000332200003322000033220000332200003322cccc000088880000cccc000088880000cc00000088000000cc000000880333300003300000033330000330000003333000033000000333300003300cc880000cc880000cc880000cc880000cc88000000000000cc880000000303000003030000030300000303000003030000030300000303000003030cccc0000cccc0000cccc0000cccc0000888800008888000088880000888b33300003333000000000000000000003333000033330000000000000000
|0,1=>0xcc880000cc8800000000000000000000cc880000cc8b03000003030000000100000001000003030000030300000001000000010cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000000000000002222000022220000222200002222000033330000332200003333000033224444000044440000444400004444000044440000000000004444000000033330000333300003322000033220000333300003333000033220000000000000000000000000000000000000000c0c00000ccc80000c0c00000cccb33300000000000033330000000000003333000000000000332200000000cccc0000cccc0000cccc0000cccc0000cc000000cc000000cc000000cc030300000333200003030000033320000000000000000000000000000000000000000000000000000000000000000cc880000cc880000cc880000cc8b0300000303000003030000030300000303000003030000000000000000044440000444400004444000044440000444400004400000044440000440333300003333000033330000333300003333000033000000333300003300cccc000088880000cccc000088880000cccc000088880000cccc0000888a22200002222000022220000222200002222000022000000222200002200
|0,2=>0xcccc000000cc0000cccc000000cc0000cccc000000880000cccc0000008b3330000303000003333000030300000333300003030000033330000303000000000cc88000000000000cc88000000000000cc88000000000000cc8800000000000000000000000000000003333000033000000333300003300ccc80000ccc80000ccc80000ccc80000ccc80000ccc80000ccc80000cccb33200003332000033320000333200000000000000000000000000000000cccc0000cccc0000cccc0000cccc0000cc880000cc880000cc880000cc8b30300003302000033030000330200003303000033020000330300003302cccc0000cccc00008888000088880000cccc0000cccc00008888000088891110000111100001111000011110000110000001100000011000000110000440000004400000044000000440000004400000000000000440000000333300003333000033330000333300000000000033220000000000003322cccc0000cccc0000cccc0000cccc0000cccc000088880000cccc000088880330000003300000033000000330000003300000022000000330000002244440000440000004444000044000000444400004400000044440000440333300003333000033330000333300001111000011110000110000001100
|0,3=>0xcccc0000cccc0000cccc0000cccc00000000000000000000cc880000cc8b300000033000000330000003300000033000000220000003300000022000000000000000000000000000000000000000000cc88000000000000cc8b330000033300000333000003330000033300000333000003330000033300000000044400000000000004440000000000000444000000000000044400000000000000003333000033330000000000000000000033220000332244440000444000004444000044400000444400004440000044440000444000000003332000000000000333200000000000033320000000000003332cccc0000cccc00008888000088880000cc000000cc00000088000000880303000003030000033320000333200003030000030300000333200003332cc000000ccc80000cc000000ccc80000cc000000ccc80000cc000000ccc8000000033330000000000003333000000000000332200000000000033220000000000000000cccc0000c0c000000000000000000000cccc0000c0c000000000000000000000000000000001111000011000000111100001100cc440000cc440000cc440000cc440000cc440000cc000000cc440000cc0000000003333000000000000333300000000000022220000000000002222
|0,4=>0xc0800000c0800000c0800000c0800000c0800000c0800000c0800000c0830300000202000003030000020200000303000002020000030300000202cccc0000cc880000cccc0000cc880000cccc0000cc880000cccc0000cc8b2320000323200003232000032320000323200003232000032320000323200c8000000c8000000c8000000c8000000c8000000c8000000c8000000cb33300003330000033330000333000003333000033300000333300003330cccc0000cccc0000cccc000000000000cccc0000cccc0000cccc000000000000000000000000000000000000000333300003333000022220000222200cc000000cc000000cc000000cc0000008800000088000000880000008b333000033330000333300003333000033330000333300003300000033000c0c00000c0c00000c0c00000c0c00000c0c00000c0c000000000000000333300003333000033330000333300003333000033220000333300003322c0c00000ccc80000c0c00000ccc80000c0c00000ccc80000c0c00000cccb0330000303200003033000030320000303300003032000030330000303200000000000000000000000000000000ccc80000ccc80000ccc80000cccb33300003332000033330000333200003333000033320000333300003332
|0,5=>0x333300003333000033000000330000003333000033330000330000003300cccc0000cccc0000cc880000cc880000cccc0000cccc0000cc880000cc8b33300003333000030300000303000003333000033330000303000003030
|_,_=>0
def sP:Nat→Nat
|0=>0x1a1858a005041c1a2c10a002068b0404d80101c68b04400081a68582142038b0a085001a2cc8214002070c08080302c10a00206860a08008220c582002068b04280161a5458a005068b044c00824443020020682203c0081a2c10a1c206860404600160850900203860a080040608080
|1=>0x600040d1608522002178d1608500101068604040085c2c10a5a0042c222c10a00206861608500541c6a916085001aa0582140040d16093a6002068b04292801034b8b04400081a2c10a48004071a08522002038d0c5c10a001c69704287800e2c10a420040d1608520002068b1478008
|2=>0x1035d0b0428008082c10a360040d16085390020207160808a001068b044c0081a2c10a700040d1608500543458214dc0081ad858a002068b044c0081ad4582140040d161410a002068b0429a00108c6821488008663430b042840d1608532002090d160808a003588b04280081a18582
|3=>0x4287801034a8b0428008221c58214004041a2c10114004231af810a00206831608500103608b04280441a2c10a002068b860850010345c204280081b0430b04280401a2c10a002090d0c085001035f8b04280081a18b8202006be04280084634582360040d160853d002068b0429d80
|4=>0x140160d16085001034582152c008941068b0428008923430b04280081a2c10a36004111a1858200206a92e2c10a002068b05205001034582151c0081b1858214004111af0582140040d1628014104868b0428008464468b04280081aac582140040d1628045101c6861608500101c68b
|5=>0x160850010345d004280081a18582140040d160851d002248d16085001034b8b04280081b4858214004071a2c10a00206d10c2c10a0020686174010a0020686160851d002068b042a780113468b0428008241c68b0428008923458202280081a2c10a9c0044d1a18582140040d2e2c101
|6=>0x34582140040d
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x154005
|5,0=>0x5e61618526131846610183a60d182e60a18226071816604180a6
|6,0=>0x779dd777459ca770ddbc76d5dae769dda076699946635d8675fdd7875c5d6a758dd5c7555d4f6521d4264f193574b9d277481d197449d0b7411cfd73d9cef73a1ce17369cd37331cc572f9cb772c1ca97289c9b7251c8d7219c8061e5c7271adc647
|7,0=>0x2c28aea2b28aadea47a722948a35e8589f9e7779c1e6889822597949e4a890de3c78d5e2d889da207862211782da0387ee1f477b5de58
|8,0=>0xbedaf47bb5ee67b7ded87b45eca7
|9,0=>0x3016
|_,_=>0
def wAt:=mkWire dB 83 238 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 14
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x462c0e291a211a2122f214350e2b1035242b101156200c0916292e9c1621225c1a2916210e291a2100ba043508211a2d0e2b1a211a061421022f14210c37162910ac0c092e2916212e2b16210e1b1a2124281a5d462f0e291a21082b16353e0a0c0316290474162900211a0524280e2d1a21225c1a2916210e1810350e2d1035
|1=>0xe2d1a2114210035220b14350c3516291421162110121635982f140908091635162900350e2b1a21142d14352e2916214e231401022f14212e01162114351609047400210e2d1a21104514350c0916290476002116291a210e2f1a210c231629143510351a2d14210e1816291a21222f10ae0c0908290e2d1a21162914211621
|2=>0x401162900210035162116011a210c01162916290401162900210c0b162908291635
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x43022000000000002000000000000
|6,0=>0x4930000000004814624514320004033d33c10003a20003820000003620003333120000000002e30002c22a20002822622420002220002020001e21c20001a21821620001420001311120000e30b30000a1073
|7,0=>0x8828628428228027e27c27a27827627427227026e26c26a26826626426226025e25c25a25825625425225024e24c2
|8,0=>0x9018f18e18d18c18b18a1
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 12
def pmP:Nat→Nat
|0=>0x391bc00c441002910c00906f00201bc00706f000d1b400306f00081fc00186f000402c000c09000300400080100008bc000207000060000006f000019c00004b000012800004200001000000390000080000008000001c000004000000c0000020000004000000
|1=>0x8000e19080031200c9fc80020511881fc24126f05001fc10007104001440c207f01881fc04226f01081fc04126f00800e4018803005c1bc014042004602c01106f
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0xc1000001000000
|6,0=>0xc00000f04f0405434c01000800020110400000c00810010820090040012401c108024008600520048a
|7,0=>0x32c2599f8ab99e85abb3b18764a96bd05e3526a0c2dc64c
|8,0=>0x3716e9b609d8
|9,0=>0xe
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 26 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_236 7 roots_236 ops++addP pm 1 dom_229 7 roots_229 ops++addP pm 2 dom_233 7 roots_233 ops++addP pm 3 dom_109 7 roots_109 ops++addP pm 4 dzo_173_64 6 roots_173 ops++addP pm 5 dom_173 7 roots_173 ops++addP pm 6 dom_205 7 roots_205 ops++addP pm 7 dom_137 4 roots_137 ops++addP pm 8 dzo_137_64 4 roots_137 ops++addP pm 9 dzo_233_4 6 roots_233 ops++addP pm 10 dom_204 4 roots_204 ops++addP pm 11 dom_108 4 roots_108 ops++addP pm 12 dzo_105_4 5 roots_105 ops++addP pm 13 dzo_141_64 5 roots_141 ops++addP pm 14 dom_197 4 roots_197 ops++addP pm 15 dom_228 4 roots_228 ops++addP pm 16 dom_101 4 roots_101 ops++addP pm 17 dom_41 4 roots_41 ops++addP pm 18 dzo_169_4 5 roots_169 ops++addP pm 19 dom_172 4 roots_172 ops++addP pm 20 dom_141 5 roots_141 ops++addP pm 21 dom_232 4 roots_232 ops++addP pm 22 dzo_41_4 4 roots_41 ops++addP pm 23 dom_169 5 roots_169 ops++addP pm 24 dom_165 4 roots_165 ops++addP pm 25 dom_225 4 roots_225 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_237 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_229 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_zo_173_64_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_137_64_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_233_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_204 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_108 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_105_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_141_64_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_197 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_228 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_101 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_169_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_172 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_141 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_zo_41_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_169 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_165 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_225 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_236 7 s (0,roots_236.map (·&&&dom_236)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_237 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_236 h
def symsG:List (List (Nat×Nat)):=[[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xffffffff00000000ffffffff00000000,96),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60)],[(0xffffffff00000000ffffffff00000000,96),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_237==dom_237)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_237 gM v ys):RunD true dom_237 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_237 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 15 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 56 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 56 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 31 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 31 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 8 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_237 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_82_1:=0xa000a00000000000a000a
def gzo_82_1:=0xa00080000000000080000
def gsh_82_1:=0x500040000000000040000
theorem lowS_zo_82_1_82:Lower true dzo_82_1 roots_82 gzo_82_1 4:=lower_iso_b (d1:=dom_82) (r1:=roots_82) (T1:=gsh_82_1) [(dom_82,1)] (by decide +kernel) (lower_slice_b (T:=gsh_82_1) [] (by decide +kernel) lowS_82)
def dzo_210_1:=0xa000a00000000000a000a00000000000a000a00000000000a000a
def gzo_210_1:=0xa000a00000000000a000a00000000000a00080000000000080000
def gsh_210_1:=0x50005000000000005000500000000000500040000000000040000
theorem lowS_zo_210_1_82:Lower true dzo_210_1 roots_210 gzo_210_1 5:=lower_iso_b (d1:=dom_210) (r1:=roots_210) (T1:=gsh_210_1) [(dom_210,1)] (by decide +kernel) (lower_slice_b (T:=gsh_210_1) [(0x50005000000000005000500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_82)
def dzo_242_1:=0xa000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a
def gzo_242_1:=0xa000a000a000a000a000a000a000a000a000a000a0008000a000a00080000
def gsh_242_1:=0x5000500050005000500050005000500050005000500040005000500040000
theorem lowS_zo_242_1_82:Lower true dzo_242_1 roots_242 gzo_242_1 6:=lower_iso_b (d1:=dom_242) (r1:=roots_242) (T1:=gsh_242_1) [(dom_242,1)] (by decide +kernel) (lower_slice_b (T:=gsh_242_1) [(0x5000500000000000500050000000000050005000000000005000500000000,0,32),(0x5000500050005000500050005000500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_82)
namespace S_243
def pG:List (Nat×Nat):=[(1,33),(1,129),(2,18),(2,34),(2,66),(2,130),(3,19),(3,35),(3,67),(3,131),(16,18),(16,80),(16,144),(17,19),(17,49),(17,81),(17,145),(32,33),(32,34),(32,96),(48,49),(48,50),(48,112),(48,176),(64,66),(64,80),(64,96),(65,67),(65,81),(65,97),(65,193),(128,129),(128,130),(128,144),(160,161),(160,162),(160,176),(160,224),(192,193),(192,194),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_243.map (·&&&dom_243)
def gM:=goal_243&&&dom_243
def NN:Nat→Nat
|4=>11
|5=>96
|6=>287
|7=>130
|8=>18
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xfb85eaa2938b87b4bd5d4a8014690434f892a9da1fab9172df0c971
|5,0=>0xfce77f9ae2e8a73e2626e0601d915bcf668c53c4bd3d4bd359bbdfdb7d09b5c68b495ab360fb004eaf0d8a82fca5d58a16639f8b7980e197ae396bd4968fc926388f16d8c2908aeb18a069876e8837b68225a7ccbe7a9157967c78144717c1708f865b28658d064a1162acb5e9a05d14357f2b57d81568414fa52481a745524447be4295b41e0c3f1783eaa837c8b379d336d1933cbe32b253125f2cbe729bc0299c5278ba23cef20b0120aa12085b1fd411fc711aa9619fe118e83189ef137d513578108b30f7e40d6e90d5730cdb60b2b309ce108f390872207164052c0046e103c07035fa02980027ea023de01a0c
|6,0=>0x40c3b3fc2e3e7603cde63b8c63ae8b3adb33ad843a6d53919438e9c38c4d38bd7386d137b2a377e3375bc36aa2367303618e35e8735ac535a1135091334523214231a5f3102330c182ff572fd412fbcc2ed9d2e86e2e10d2d8142d2f92b8042b55a2a00b29f2f29b84291ca28e5b28cef28c4d276b62759127525271d12715725f56259fd254d82491722973226182232d2143b20d9720aa1206a31fa9c1f0a71e9a91ce171cb851cb831c5371bbbb1b2331acfd1a71319f1b193b1185ef1735416798164d71547c14ddd14a2713f8b1397f135b512d6c12c89115af1143e10eb3107ed0ff2c0f2050ed980df6e0dd400dcb70d4800c9e30c8aa0c78f0bc3b09fe909e2909b6108dc908cd1079b2078650716406f2006b3b069090678a065fb0636b05d4a05b9004ca004b5d0421f03d0a02d1802bda0197d012b1009d800769
|6,1=>0xb4172b2dadb26aeaf64eaf0d8ac1e1ab308aa04ca967ea8ed1a8691a8315a41219f89a9f8309cdbb9c3f29bdbf9b9c699cb9994c2993ce97770968fc95b1295a51953de9535393f1493e3f92a5592491920fd915ba912d28ed0e8ec078e0828db338c7058b3ee8a9cc8a8f189feb86cdb841e98399f81bdc80de08041f7fd017f9207ef657ea247d86a7d6177ba1d79a537912f787157829b77c1d7750476d3e76af4748db74644745a971bbd709126ffec6f45b6f43c6d6e66cca56bbd76b0de6ac0869488689cc684c5642c062638608455fccc5d5a45d1fd5b5585ab72599f05916158ef258477581bf57eab56cc3563e955e8c5577e54d4054b7254335542f953da952fe451a6a5115b510554fa4f4f5094f3314e7954da314d6be4c1e64c1834b98e4ae2e497a545b054560c44d42437d0428a441e7a412ae4128c40f4f
|6,2=>0xfc912f9ae2f8f9bf72e9f1ddee8a73e850fe1ff6dc2f7d7500d72a5d6ce5d600dd40c7d3d8fd1c29d083dcff9cc8b87c851fc7f72c5b04c501dbd354bcecebb0deb9942b5d2fb4eb2b4de6b4a62
|7,0=>0xe9822dd0a5d3d8fd08b1bbc98baaf9b93e3b65bcb2ae4adfb5ac380ab356a3b8ba308fa2ab99ee349b9019a7c69923a98eb9905648eb198cc608ac2b8573084f7b8354181893817dd801c87f8977e4717c7d97bf007bc2c7980278d6c76ef176d1b7494d74644743946fc6c6f8906d4696cd996c8926b1c76b0de6a44d6741d66fc265428644b463926628e962108606896063d5fc665ece35c8445c4965be635b1795a65f59d365866b57d6e5577e554c9538f652ea85191450f264f5864de8348d4a450bc3d8cd3d80e3936238aa737d4736c0f36bfc35c4f3586e34f3634131322cd306e8303da2f07d2e68f2e2d52bf342af7d2adc2274ed274c424eb62232d20b561df5c1d5551c7761634c150311143e10e2c100220ef800d9880cee70cae20c0150b55c0691105d4a059aa0599d0467f0360703495023300108400d7c
|7,1=>0xfa83eec62b
|8,0=>0xcdcdec4aa8bbc98ad320a8580a25797a9f6762ce712a96c50a6340b3d1cf22ce7227e01972117c56127920fc84
|9,0=>0x7a9f6
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf000f000f000f000f000f000f000f000f0000000f0000000f0000000f0000f000f000f000f000c000c000c000c000f000f000f000f000c000c000c000cf000c000f000c000f000c000f000c000f000c000f000c0000000000000000f000f000f0000000f000f000f0000000f000f000f0000000f000f000f0000f000f000c000c000f0000000c0000000f000f000c000c000f0000000c0000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000ef000f000f000f0000000000000000000f000f000f000f0000000000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000f000c000f000c000f000c000f000c000f000c000f000c000f000c000f000cf000f000f000f000f0000000f0000000c000c000c000c000c0000000c0000f000f000f000f000f000f000f000f000f000f000f000f0000000000000000f000f000c000c000f000f000c000c000f000f000c000c000f000f000c000cf000f000f000f000f0000000f0000000f000f000f000f000f0000000f0000f000f000f0000000c000c000c0000000f000f000f0000000c000c000c0000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a000af000f000f000f000f000f000f000f00000000000000000000000000000000
|0,1=>0xf0000000f000f000c000f000c0000000f0000000f000f000c000f000cf000f000f000c000f000f000f000c000f000f000f000c000f000f000f000cf000f000f000f000f000f00000000000f000f000f000f000f000f000000003000300030003000300030003000300030003000300030003000300030000e000e000e000e000e000e000e000e000e0000000e0000000e000e000e000ef0000000f0000000f0000000f0000000f0000000f0000000f0000000f0000f000f000c000c0000000000000000000f000f000f000c0000000000000000f000e000f000e000e000e000e000e000f000e000f000e000e000e000e000ef000f000f000f000f000f000f000f000f000f000f0000000c000c000c000030003000300030003000000030000000300030003000300030000000300000000f0000000f000f0000000f00000000000f0000000f000f0000000f00000000300000003000300000003000000000003000000030003000000030000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000cf000f000f0000000f000f000f0000000f000f000f00000000000000000000f000f000f000f000f000f000f000f000f000f00000000000f000f00000000f000f000f0000000f000f000f0000000c000c000c0000000c000c000c0000
|0,2=>0xf000f000f000f000f000f000f000f000c000c000c000c000c000c000c000c0000f0000000f0000000f0000000f0000000c0000000c0000000c0000000c0000f0000000f00000000000000000000000f0000000f0000000000000000f000f000f000f000f000f000f000f000f000f000f000f000f0000000f0000f000f000f000c0000000000000000000f000f000f000c0000000000000000a000a000a000a000a000a000f000e000a000a000a000a000a000a000f000e00000000f000c00000000000f000c00000000000f000c00000000000f000c00000000f000f00000000000f000e00000000000f000f00000000000f000ef000f000f000c000f000f00000000000f000f000f000c000f000f00000000f0000000f0000000f0000000f0000000f000f000f000f000f0000000f000000000000f000f00000000000f000000000000000f000f00000000000f0000f0000000f0000000f0000000f0000000f0000000f0000000c0000000c000000000000a000f00000000000a000e00000000000a000f00000000000a000ec000c000c000c000c000c000c000c000f000f000f000f000c000c000c000cf000f000f000f000f000c000f000c000f000f000f000f000f000c000f000cf0000000f00000000000000000000000f0000000f00000000000000000000
|0,3=>0xf000f000f000f000f000f000f000f000f000f000f0000000f000f000f0000a000a000a000a000a000a000b000a000a000a000a000a000a000a000b000af000f00030000000f000f00030000000f000f00030000000f000f00030000f000f000f000f000f0000000f0000000f000c000f000c000f0000000f0000f000c000f000c000c000c000c000c000f000c000f000c000c000c000c000c0000f0000000f0000000f0000000f0000000c0000000f0000000c0000000cf0000000f0000000f0000000c0000000f0000000f0000000f0000000c0000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c00000000000000000000f000f000f00000000000000000000000f000f000f00000000f0000000f0000000f0000000f0000000f0000000f0000000000000000f000f000f000f000f000f000f000f0000000f0000000f00000000000000000000f0000000f0000000f0000000f0000000f0000000f0000000c0000000cf0000000f0000000f000f000f000c000f0000000f0000000f000f000f000c0000000000000000f0000000f00000000000000000000000f0000000f0000e000e000e000e000e000e000f000e000e000e000e000e000e000e000f000e3000300030003000000000003000000030003000300030000000000030000
|0,4=>0xf000f00030003000f000f00030000000f000f00030003000f000f00030000f000f00000000000f000f000f000f000c000c00000000000c000c000c000cf000d000f000d000c000c000c000c000f000d000f000d000c000c000c000cf000a000f000a000a000a000b000a000f000a000f000a000a000a000b000ac000f000c000f000f000c000f000c000c000f000c000f000f000c000f000cf0000000f0000000f0000000f000000000000000f000000000000000c0000f000f000f000f000f000f000f0000000f000f000f000f000f000f000f000030003000300030003000300030000000300030003000300030003000300000000f0000000f00030000000300000000000f0000000f000300000003000000000000f000000000000000f000000000000000f000000000000000f00000000f0000000c0000000f0000000c0000000f0000000c0000000f0000000cf000f000f000a000e000e000e000a000f000f000f000a000e000e000e000a300000003000300030000000300000003000000030003000300000003000000000000f000f0000000000000000000f0000000f000f000f0000000f00000000000000000000f000f000f000f0000000000000000000f000f000f000cf000f000f0000000f000f00010000000f000f000f0000000f000f00010000
|0,5=>0xf000c000f000c00000000000000000000000000000000f000f000f000f0000000000000000f000f000c000c000f000f000c000c000f000f000f000c000f000f000f000cc000c000f000f000c000c000c000c000c000c000f000f000c000c000c000c0000000000000000f000f000c000c0000000000000000000f000f000c000ce000e000e000e000e000e000e000e000c000c000c000c000e000e000e000ec000c000c000c000c000e000c000e000c000c000c000c000c000e000c000e00000000f000f000000000000000000000000000f000f0000000000000000f0000000f000f000f0000000f0000000f0000000f000f000f0000000f0000f000f000f000f0000000000000000000f000f000f000c0000000000000000f000f000f000f000f000f000f000f000f000c000f000c00000000000000000000f0000000f0000000f0000000f000000000000000f000000000000000ce000e000f000e000e000e000f000e000e000e000f000e000e000e000f000e0000000030003000000000003000000000000000300030000000000030000f000f000f000c000f000f000f000c000f000f000f000c000f000f00000000000000000000f000300030003000f00000000000000000000000000000000
|0,6=>0x30003000300030003000300030003000300030003000300030003000000000000000000000000e000e000e000e0000000000000000000e000e000e000ef0000000f00000001000000010000000f0000000f00000001000000010000a000a0000000a000a000a0000000a000a000a0000000a000a000a0000000ae000e000c000e000e000e000c000e000e000e000c000e000e000e000c000ec000c000f000f000c000c000f000f000c000c000f000f000c000c000c000cf000f00000000000f000f000f0000000f000f00000000000f000f000f00000000f0000000f0000000f0000000f0000000f0000000c0000000f0000000cf000f000f000f000c000c000c000c0000000f0000000f0000000c0000000c00000000000000000000000000000000f000f000c000c000f000f000c000cf000f000f000f0000000000000000000f000f000f000f000f000f000c000cf000f000f000f000f000f000f000f000f000f000f000f000c000c000c000cf000f0000000f000f000f0000000f000f000f0000000f000f000f000000005000000050000000500000005000000050000000500000005000000050000d000c000d000c000d000c000d000c000d000c000d000c000d000c000d000cf000f000f000f000000000000000000000003000000030000000000000000
|0,7=>0xf000c000f000c000f000c000f000c000f000f000f000f000f000c000f000c00000000000000000000000000000000f000f000f000f000f0000000f00000000000000000000f000e000f000e0000000000000000000f000e000f000ef000f000f000f00000000000000000000000f0000000f000000000000000000000000000000000000000000000000f0000000f0000000f0000000f0000f000f000f000f0000000000000000000f000f000f000f000f0000000f0000f000f000f000f000f000f000c000c000f000f000f000f000f000f000c000cf000f000f000f000f000f000f000f00000000000f000f0000000000000000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0000f000f000f000f0003000000030000000f000f000f000f000300000003000000000000f000f00000000000f000f00000000000f000f0000000000000000f0000000f000f000f0000000f000f000f0000000f000f000f0000000f0000c000f000c000f000c000c000c000c000c000f000c000f000c000c000c000cc000c000f000c000c000c000f000c000c000c000f000c000c000c000f000cf0000000f0000000f0000000f0000000f000f000f000c000f000f000f000cf000f000f000f000f000f000f000f000f000f000f000f000f000f00000000
|0,8=>0x30003000300000003000300030000000300030003000000030003000300003000300030003000000000000000000030003000300030003000000030000000000000000f000000000000000f000000000000000f000000000000000000000000f000f00000000000f000f00000000000c000c00000000000c000c00000000000000000000000000000000f000f000f000f000c000c000c000ca000a000a000a000a000a000a000a00000000000000000002000200020002000000000000000000000000000000000000f0000000f000000000000000000000000000000000000e0000000e00000000000000000000000e0000000e0000000000000000f000c000f000c0000000000000000000f000c000f000c3000300030003000100000001000000030003000300030001000000010000f000f000f000f000f000f000f000f000f0003000f0003000f0000000f000000000000000000000000000000000000f0003000f0003000f0000000f000050005000500050005000400050004000500050005000500050004000500040000000000000000000000000000000000000000f000f00000000000c000cf000f00000000000f000f00000000000f000f000f000f000f000f000f0000b000b000b000b000b000a000b000a000b000b000b000b000b000a000b000a
|0,9=>0xf000f000f000f000f000f000f000f0000000000000000000f000c000f000c0000f0000000f0000000f0000000f0000000f0000000f0000000f00000000f000f000f000f0003000300030000000f000f000f000f0003000300030000f0000000f00000000000000000000000f0003000f00030000000000000000f000f000f000f0000000000000000000f000c000f000c0000000000000000f000f000c000c0000000f0000000c000f000f000c000c0000000f0000000cf000f000f000f000e000e000e000e000f000f000f000f000e000e000e000e00000000f000f00000000000e000e00000000000f000f00000000000e000e000000000000000000000000f0000000000000000000000000000000f000030000000300000003000000030000000300000003000000030000000300000000300000003000000000000000000000003000000030000000000000000f0003000f0003000f0000000f0000000f0003000f0003000f0000000f00000000000000000000300030003000000000000000000000003000300030000f000f00050000000f000f00050000000f000f00050000000f000f0005000000000000000000000000f0000000f00000000000000000000000c0000000c3000300030003000300030003000300030003000300030003000000030000
|0,10=>0xf0000000f0000000f0000000f0000000f000f000f000f000f000c000f000cf000f000f000f000f000f00000000000f000f000f000f000f000f000f0000e000e000e000e000e0000000e0000000e000e000e000e000e0000000e0000f000f000f000f000f000f000f000f0000000000000000000f000f000c000cf000f000f000f000f000f000f000f000f000f000c000c000f000f000c000c00000000000000000000000000000000f000c000f000c000f000c000f000ca000a000a000a000a000a000a000a000a000a00000000000a000a00000000e000e000e000e000e000e000e000e000e000e000c000c000e000e000c000cf000f000f000f000f000f000f000f00030003000300030000000000000000a000f000a000f000a000e000a000e000a000f000a000f000a000e000a000e0000000030000000000000003000000000000000300000000000000030000a000a000b000a000a000a000b000a000a000a000b000a000a000a000b000a0000f0000000f0000000c0000000c0000000f0000000f0000000c0000000ca000a000a000a000a000a000f000a000a000a000a000a000a000a000f000a00000000000000000000000000000000f000f000f000f000f000c000f000c000000000000000000000000f000c000000000000000000000000000f000c
|0,11=>0xf0000000f0000000f000e000f000e000f0000000f0000000f000e000f000e0000a0000000a0002000a0002000a0000000a0000000a0002000a0002000af0000000f0000000c0000000c0000000f0000000f0000000c0000000c0000f000f000f0000000f000f00000000000f000f000f0000000f000f00000000f000c000f000c0000000000000000000f000c000f000c0000000000000000f000f000f000f0005000400050004000f000f000f000f000500040005000400000000000000003000000030000000000000000000000030000000300001000100010001000100000001000000010001000100010001000000010000f000f000f000f000a000a000a000a000f000f000f000f000a000a000a000af000f000f000f0000000000030000000f000f000f000f0000000000030000c000c000c000c000f000f000f000c000c000c000c000c000f000f000f000cf000f000f000f000f000a000f000a000f000f000f000f000f000a000f000a3000300030003000300020003000200030003000300030003000200030002f000f000f000f000c000c000c000c000f000f000f000f000f000c000f000ce000e000e000e000e000e000e000e0000000000000000000e000e000e000e000000000000f000000000000000f000000000000000c000000000000000c
|0,12=>0x3000000030000000000000000f0000000f000f000f0000000f000c000f0000000f000f000f0000000f000cf000f000f000f000f000f000f000f000f000f000f000f000f000f000c000cf000f000f000f000f000f000f000f0000000300000003000000000000000000000000000000000000000000000000f000f000f0000000f000f000f00000000300000003000f000f000f000f00000000000000000000000000000000e000e000e000e0000000000000000000e000e000e000e0000000000000000f000e000f000e000f0000000f0000000f000e000f000e000f0000000f0000f000f000f000f000f0000000c0000000f000f000f000f000f0000000c0000c000c000c000c000c000c000f000c000c000c000c000c000c000c000f000c00000000f000f00000000000f000f00000000000f000f00000000000f000000000000000000000000000000000000f0000000f000f000f0000000f0000c000c000c000c000f000c000f000c000c000c000c000c000f000c000f000ce000e000e000e0000000e0000000e000e000e000e000e0000000e0000000ef000f000f000f000f000f000f000c000f000f000f000f000f000f000f000cf000c000f000c000f000c000f000c0000000000000000000f000c000f000c
|0,13=>0xc000c000c000c000c000c000c000c000f000f000f000f000f000c000f000c3000000000000000300000003000000030000000000000003000000030000000000000000000000000000000000003000300030003000000000000000050005000500050005000500050005000500050000000000050005000000000000a0000000a000a000a000a000a0000000a0000000a000a000a000a000ac000e000c000e000e000e000e000e000c000e000c000e000e000e000e000ea000a000a000a000a000a000a000a000f000f000f000f000e000e000e000ef000f00000000000f000f00000000000f000f000f000f000f000f000c000c00000000000000000000000000000000f000f000f000f000f000f000c000c3000300030003000300030003000300030003000300030000000000000000f000f000f000f0005000000050000000f000f000f000f0005000000050000f000f000c000c000f000f000f000c000f000f000c000c000f000f000f000ca000f000a000f0008000c0008000c000a000f000a000f0008000c0008000c0000000000000000f000f000f000c0000000000000000000f000f000f000c0000300000000000f000f000000000000000300000000000f000f00000000f000f000f000f000f000f000f000f000f000c000f000c000f000c000f000c
|0,14=>0xf000d000f000d000f000c000f000c000f000d000f000d000f000c000f000c0000000000000000f000f000f000f0000000000000000000c000c000c000c00000000000000000000000000000000f000f000f000c000f000f000f000c0000000030003000000000003000300000000000300030000000000000000f000f000f000f000f000f000f000f000f0000000f0000000c0000000c0000f000f000f000f00000000000f0000000f000f000f000f00000000000f0000000000000000000000000000000000000000f0000000c0000000f0000000c0000e0000000e000e000e000e000e0000000e0000000e000e000e000e000e5000500050005000500000005000000050005000500050005000000050000d000d000d000d000d000c000d000c000d000d000d000d000d000c000d000ce000e000e000e000e000e000e000e000f000f000f000f000e000e000e000ef000c000c000c000f000c000f000c000f000c000c000c000f000c000f000ca000a000a000a000a000a000a000a000b000b000b000b000a000a000a000af000f000f000f000f000f000f000f00000000000f000f00000000000c000ca000a0008000a000a000a0008000a000a000a0008000a000a000a0008000af000a000f000a000e000a000e000a000f000a000f000a000e000a000e000a
|0,15=>0xf000f000f000f000f000e000f000e000f000f000f000f000f000e000f000ea000a000f000a000a000a000f000a000a000a000f000a000a000a000f000ad000d000d000d000d000d000d000d000d000d000c000c000d000d000c000c30003000300030000000000000000000f0003000f0003000f0000000f0000f000f000f000f000f000f000f000f0000000f0000000f0000000c0000000cf000f00000000000f000f000f000f000f000f00000000000f000f000c000c0000f0000000f000f000f000f000f00000000000000000000000000000000f000f000f000f0000000f0000000c000f000f000f000f0000000f0000000c1000000010000000f0000000f00000001000000010000000f0000000f00000000000000000000000000000000000000000000f000f00000000000f0000f000f000f000f0000000000000000000c000c000c000c0000000000000000a000a000a000a000a000a000a000a0008000800080008000a000a000a000af000f000f000f000f000f000f000f000300030003000000030003000300003000300030003000000000000000000030003000300030000000000000000d000d000d000d000c000c000c000c000d000d000d000d000c000c000c000c5000500050005000000000000000000050005000500050000000000000000
|1,0=>0xf000f000f000f000f000f000f000f00050005000500050000000000000000c000c000c000c000c000c000c000c000f000c000f000c000f000c000f000ca000f00000000000a000f00000000000a000f00000000000a000f00000000f000a000f000a000a000a000a000a000f000a000f000a000a000a000a000a5000400050004000500040005000400050004000500040005000400050004f000e000f000e000f000e000f000e000f000e000f000e000f000e000f000ef000a000f000a000f000a000f000a000f000a000f000a000f000a000f000af000f000f000f000f000f000f000f000a000a000a000a000a000a000a000a2000200020002000200020002000200020002000200020002000200020002f000f00000000000f000f00000000000f000f000f0000000f000f000f0000f000000000000000f0000000f0000000f000000000000000f0000000f0000f0005000f0005000f0000000f0000000f0005000f0005000f0000000f00000000c0000000c000c000c000c000c0000000c0000000c000c000c000c000cc0000000c0000000f0000000f0000000c0000000c0000000f0000000f00000000000000000000f000f000f000f0000000000000000000f000c000f000c
|_,_=>0
def sP:Nat→Nat
|0=>0x200e26070040008038380225000201e13008241a0809890020900068260111824000c0200c1409000200e031100400080f80c2601000783a1a0700400080d004380900020341b0982400080d04c02190002006180a00010070b80412080a8282c000400c1414000202a0a0a00022030980424110384002090403c1c0106830160a048001007030040a04018080200
|1=>0x98041200040687001048006e08098046c0008820262400824101a050580a0004068142f048d41013008d012000406814060480066081904c02000401c040104800101a1884c120004068260600814102c0d0285e09040681430048001811038bc02090404c022e028b4100716038020002020340a15800101a098a812000400c1c01148003413008a01200138681c01
|2=>0x23800101a050bc0a2d04068142f048d8100a0b11812000e8681c0122800101a2204c12000406814430480010150504c0011210682601048302203098040a4104068260100100340a09824001e0400c1c010002042031d804003f0401c5e010482034131f02400110d04c2001048200e03178040a041e868140900020781a098040a080182876000404c023a048001839
|3=>0xd14c12000406814520480010031d80428000400c2a0a09800a21a0980412000401c060e00800101a09804125027820340a04800100309804240008868264e00824101a05134120004068264c04800104b0184c02000412c2a130080010130092812000401c200104800081a01004120024810340e00800101a0583802000406814480480010210a84c02000400c2601
|4=>0x616c341300824004f040682601048001015098042c000406814160480010031d80400080186076000401c1e0e0081410031d8042c000404c022e048d4101a2d0bc12000406814590480010030980428000405426010a00010072b83802000400c260200800100305058400008868260104848101a09804ac00040682601049541013009501200040285e34048000808
|5=>0x980412000401c34640082400080989002090018c101a09804120004068c20e00824000801868441300800101a0980412600004410030d04c020506010340a0480010030d028260900020be1a09804120006010340e0082400080380c26012f00010070d04c022b00174101a0980412000406814010b024000803868b801048001007018380209000303a1a0704c0200
|6=>0x4800101a09804a40900020e81a0980412000401c347300824000404068e40104800e2080d04c0209000203413009bc120008820340e098040a080d028266d04800101a3584c120004098340e0980400080d1a826010480010150980400080d038260112800d2080d028260900020340e00914120004068260134024000810868021604800101a09804ce0900194101a
|7=>0x98046a0008868f61300824b0080d04c02820480102080d04c0209000203413400041200041fc34130082400081784c023404800107e0d028260900030221a1784c0209041f434130082400080d02826093e000180819028260900044107a0d04c02093c810101a050240008160681c13008001808098042c0900020342f0980412783b82034130082400080d04c0276
|8=>0xcc101a0980412000406826014601412080d04d140900020341301004120004068141304a24001e0406826010480092080d038260100020340a09a2012000404c0234048003c080184c020900044342f09804125808868b81300824000c0421c260104800101a098050c09000210a1a0980412001b820340a09824000842068260104800101a09805060900020340e
|9=>0xa6812000d04c02980480010070d0380205000200e1300a5c12000607426014b024000803a50260104800101a09805260900248340e09804120002020343205024001e02020340a04800101a09805220900020341300a4012000886826014782400080d04c028e0480018700d04c0209000301013008246c0004068260104a3400082b8681413048001003098042c20
|10=>0x480158080d04c020900031561a09804120008821541a0980412080d2a012000404c029612824000801868260153800101a09a98020900010101a09a9012000404c02625182400080d04d440900021421a0980412000406826015002400084f868260104800101a098053c0900020061a0504c0a000406826014e82400080d04c02094e000101a09804129b000203413
|11=>0x40685e130082410070d22c02090003010030704c02000400c340a1782400080d04c02b604800081d0d02812005a82034130082400080d04c02b30480010b20d04c02090007434130091412000406962130480010030d0282c0900020061a1784c020504068c813008b400080d04c02b0048001021098048c09000215e1a0980412005702034130082400080d2b42601
|12=>0x406814136102400080d04c02092a80182080d04c0209000201e1a0504c0a090406816130082400080d060760900021801a0980412000400c2a130080010bf0d04c02090002034135f02400080184d7a0100124101300a5812005e068141304800101a0700576000406826015d02400110401cf61300824180809805720900020341300ae012000421c34135b804003f
|13=>0x98046c000433834130082400cd04068260104800101a0980412cc000301007178041200658200e130082400080383c1c0104800101a0980412ca04320340a0982400080d31c2601048000808018681c0100124081a09804120004068760104800101a6304c020900020341300b14120004310341300824003d0e86826010480010640989002090003010c3098041200
|14=>0x360101a0980412000401c34220082400d70406826010480010030d04c02d600020340e09805aa000419026011a02400d404068260104800101a09805a6090002034130085812000400c14132302400080704c0234048001007190380209000200e0e0091812000401c1e2f00825a4080d04c020900020342f09804127568868260104800101a0980412cf00020340e
|15=>0x15800e0080d038260100020581a0504c12000400c141310000101a09805c40900078221a0980412000406826e104800101a09840020900030102109804120004069c0130480010260d028260900021be1a0980412000406826016f02400080d0285e096e80010070d04db8090002034da09824001a0704c029804800101a6c84c12000401c06130082400080d0602609
|16=>0x40681c1300ba800080d04c02e904800101a1784c02091a830f21a0980412002486826011282400080d3a0260900020420309804400004069cc1300824000c0400c26010280010070d0380258000202601170245a0008868260112824001d0d04c028f04800101a0980460090002034e509824000872068260104800101a09b8c12000406814ad098240004040682601
|17=>0x20f43413008240008018ec260100020341300bcc120004068143b0480010940d04c0205000202624008141200040681c13009e0000819028262d00021de1a09804120008820341377004120c0404c022e0480010bf0d0282609000200e03070040008019f834130081410072b84c020900020841a0980412007682034130082400080d04c020976000101a09bac0209
|18=>0xd190260104820061a09b701200041e8341300bc800080d02826097c82026011a01412000604434130081412080d04c02f804800101a7b8282609000201e1a0980412780606826011282400080d04c02f604800101a098040af50406826010495410073d04c0209000200e1a008581200041f8340e0980400080380c021604800101a1784de80900020340e09804f800
|19=>0x98240008018ec0200043fc34130082400080d029d01304800181d0384c020900020340e09bf812000400c348b0980400080d04c028804800101a1784c020516820342f0980412360408434130082400110401c342f00824101a0993802090002026010b11812000400c341300b7400080d3f4260900021f81a0980412000406826017d82400fa04068260104800100f
|20=>0x4068260104800f2080d04c020900020341300824ea000401c34130081412000403c341300824b0000400c340a0982400080d04db609000201e1a098040a090400c340e0980412000401c340e0082400080d028dc1304800101a8084c020900020348b0980412005e06826010480011000d04c020900020340a0b02400080d04c020909000e0080d0bc26010482034a8
|21=>0x480156040406826010480011030d04c020900020341300825760004068260104bd40008039ec2601048003c080d04c0209000200613009181200060200e130082400080d408020900020421a0704c020900021541a09804120004084061a0980412000406826013b02400080d0ec260104800101a3203826010480010030d02826010480010033f0682601048003c0c
|22=>0x40682601048d400080d04e0c05048020a080d04c02090004410070d04c0209001c0101a098040a0900074100f0d04c020900020340a098259200040b034130082400080184c022000020340e098045a0002020061a0980412000406826014602400080d08826010480022080d04c0205048204c1a09804120024830101a0980412000406826011282400080d4102601
|23=>0x203413008252a0006020342f0980412000403c340e0980412000406826017382400080d028260504800101a0704c02050480010070d04c02094a800101a1d80412003c820340e098041200040681c13009780008038682601048b400081904c022d00020061a098040a0900010221a098041200040685e13008245a0002020341300a9412000403c341300825e400
|24=>0xa58120004068640a0982400080d028264604800101a0704c024604800101a098042c09000200e1a098041258000203413548240008078685e1300824101a1784c02092c000101a1784c0205048301003098041200042d03413008240008840681c130082400080d1ec26010496000080d03827070082400080d04c02095380010070d04c020978000100f0d0282609
|25=>0x186826017900008080d0281200040682601028b40004040681c0104800101a0980412360004410030d04c020900074101a0704c02002d82034130082400080d04db8090002034610980412000406826ee0082400081600c341300824000843868260104800101a098052e09000200e030980412000442434130082400088481c34130082400080d04c02097c8301013
|26=>0xd04c0209000221a1a0980412000400c34130085812000430c34130082400085a00c34130082400080d04cd809001c0101a09804120004068f61300825e4000400c341300b9c12000f010101a09804120004068260104b58001a09c3002090002034138582400080d04dfc0900044101a3d84c0209020201e1a098041200040682601850240079020203413008240008
|27=>0x4068260104bc0001104068260104800101a1904c02090002034130091812000442034130082400080d04e0e0104800100f0d04c02090002034130081412000602034130081412000406814130488000080186827060480010570d04c020900020421a09804120004068260152824000801868260104800101a09804130e04068dc130082400080d1ec1413048015608
|28=>0x80d04c020900020340a0980412000406814130480010030d04c020900020341300825e40004068270604800101a09804122000020341300824000803868260104800101a1784c020900020347b098041200
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x32502d50285023501e50195014500f500a500550005
|5,0=>0x1ae61a861a2619c61966190618a6184617e61786172616c61666160615a6155514f61496143613d61376131612b6125611f61196113610d6108510260fc60f660f060ea60e460de60d860d260cc60c660c060ba60b460ae60a860a2609c60966090608a6084607f50796073606d60676061605b6055604f60496043603d60376
|5,1=>0x26c62666261525c52566250624a6244623e62386232622c62266220621a6214620e6208620261fc61f661f061ea61e461de61d861d261cc61c661c061ba61b46
|6,0=>0x426741f74187411740a740373fc73f573ee73e773e073d973d273cb73c473bd73b673af73a873a1739a7393738c7385737e7377737073697362735b7354734d7346734063397332732d5326731f73187311730a730372fc72f572ef62e872e172da72d372cc72c662bf72b872b172aa72a3729c7295728e72877280727972727
|6,1=>0x5de75d865d175ca75c375bc75b665af75a875a1759a7593758c7585757e7577757075697564555d7556754f75487541753b6534752d7526751f75187511750a750374fc74f664ef74e874e174da74d374cc74c574be74b774b074a974a2749b7494748d7486747f74787471746b6464745d7456744f74487442643b7434742d7
|6,2=>0x792778c6785777f67787771776a7763775c7755774e7747774077397732772b7724771e67177710770a670376fc76f576ee76e776e076d976d276cc66c576be76b776b076aa66a3769c7695768e7687768076797672766b7664765d76576650764a6643763d66376630762a6624661d7616760f7608760175fa75f375ec75e57
|6,3=>0x944793d79367930692a6923791c7915790e7907790078f978f368ec78e668df78d878d178cb68c478bd78b678af78a968a2789b7894788d7886788068797872786b7864785d7857685078497842783b7834782d7826781f78196812780c680577fe77f777f077ea67e377dc77d667cf77c877c267bb77b477ad77a6779f77996
|6,4=>0xa177a116a0a7a0379fd69f859f179ea79e379dc79d579ce79c779c079b979b279ab79a4799d7997699079897982797b7974796d7967696079597952794b7
|7,0=>0xbe88be17bda7bd28bca8bc46bbc8bb57bad8ba76b9f8b987b908b888b808b797b727b6b7b638b5b8b538b4c7b457b3f6b387b308b297b227b1b7b147b0c8b057afe7af68aef7ae87ae17ada7ad37acc7ac57abf6ab78ab07aa88aa17a9a7a928a8a8a828a7a8a737a6c7a648a5c8a557a4f6a487a408a397a327a2b7a247a1e6
|7,1=>0xdb27dab7da47d9d7d967d906d897d827d7b7d747d6c8d657d5d8d576d507d488d408d388d317d2b6d256d1f6d187d108d097d018cfa7cf46ced7ce67cdf7cd78cd07cc97cc36cbc7cb57cad8ca67c9f7c987c917c898c836c7c7c757c6e7c668c5f7c578c516c4a7c428c3b7c347c2d7c258c1d8c158c0e7c068bff7bf87bf08
|7,2=>0xdc08db97
|8,0=>0xe3c7e366e2f7e287e226e1b7e156e0e7e077e007df97df27deb7de47ddd7dd67dcf7dc87
|9,0=>0xe436
|_,_=>0
def wAt:=mkWire dB 271 244 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 9 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x18ef0d0250d024190b50d0260486a2c0690482307030018ef0d0250d024018830d0250d02419025098250486a018830d0250d024190b50d0260486a060bc0d021070300d021048310d0210200c04869018830d0250d0240980504069048010d0250604d0d0250d024060010d0210d04d098810d0250d024098051780c0d025070300d021078250d0010d0210d04d0d015048010281c108830d0240d0250604d
|1=>0xd025098050486a3d8250d003098050d015048010184f0486900161048230e83d0d0010d1d504801098690d0260206a098213804f00025098250d1bb05027099b10091b0d023190b50d0260486a01823048690206b0d02504999000121782532068178250d0160982509989048010d025098050d02109821190250486a09805048780401d0184f0d025098690d02509869098251d8050d025098810d0240484d
|2=>0x4001098260706b00a950206a0e86a04821098690d02509805170260d0be098214c8230700509825048210d2550382609869310210086a098050486a098320d021048210d0160480106016040692c069048230d0240d02509801458060003a09825070300d0210982507826048310d0210182a0d0253206b178250604d048232c04d048230382709869168010d0260883a098253f0210d0253206b1782501803
|3=>0x38240d325050240e86904821038240986904821048210986a098c90486a098050200c048691d805098810d0240397b09869018830d0250d02400af7070680982504869070680982510021048680980503824098690706a0982503827098690403d0d001098250486909805098050482109821048320d0215a04f0d0250517b04803098050d02509815018280d0252d8010481209821038030986909aa508804
|4=>0xd0250d024098050401d0986900a970206a09821060bc04069070690982500af5070682f0690480317826088070002109b6d008830d0244c82307005458050003a0d0b5098690d026050810d024098050422d0982509979098690284f0484d049890086a178250d1920003909869098250486a000690d04d098010480109801042ef03824680260d0160480108839098250d0210d04d000320d021098255d802
|5=>0xd02409832098810d024098050d3c90982632068098150016104823098050d0260486a7886909bc117827098010d0be098010d02509825098690d0252c069048230281309821002f50706809825230250d023168010d02604831050830d024098050d0240d02509b9d0d02504801048690d0210986901823048690983211005099790480300b7517826018280d0250f024020690882509825040010d01504801
|6=>0x982510021048680184f0d0250601408825040010980109aa508804040010d025098810d0240382509869050830d02409869009190d0230182a0d025098010d016048010d04d08807040010706b098251782508807100020d024098053206b0981500069048230486912803048691782404801098015d80103824098693d8250d003038250184f0486900b77178263d8260d003042950206a098210d02509881
|7=>0x4803048310d02101823048692c06a0482300011098210d3c100826038240986917824098010d04d0d00302069098210d023048690406909869098830d024070690982503803098690d02504a590986a098810d02400039098250d025018030d025098310d02104811098210401604801048010986900069048230d02509805008830d0240d001048010486909825098250986905027098050d3cb098260003a
|8=>0xd00109805038260986904069098010006909825018070d025048010980500025098250382609869098810d02407021098250002609825098690d0260d0260486a0d0250480100021098210d026098010206a098210d00109826000b50d0260480109806041ed0d00309869000210401504801040250d00105024098050d015048010d0250d0240484d0d02604869040be09801099790480304801040012f069
|9=>0x250d0260484d098210d016048010d025048210982504812098210880704001099890086a17827098010d02503827098690e86a048210d0250986903805098690380509869100020d0240d0210986a0486a098050d023098050d023098250184f0d025098690482308804040010d0010980104026098010480109801048690d021018050d0250982500869040260d003098250080179001098260d04d00826
|10=>0x486a0d02300869008010d0010480104069048010d024098050d025098062c0690482303825098690206a09821190250486a78001008260502709805098050d003040bd098013d84d0d0030184f0d0251904d0486a0d0250091b0d02308825040010d003098260d02502069098210981604801310220086a008810d024009190d023040010d0030006909821038070986904811098210d025098260980509821
|11=>0x9805098050d02509826098060d02409869098010d0030082604001
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0xa0c00009882420888202000000000000000000000000000000001c400001930000000060416204cc0000000000000000003d000000000000000000000000000000d200000b20000000024800001c8000014800000000000000000000000001040000000000000001300040000000000
|5,1=>0x11444141004000000000000003d30e8c3820dc400000000000000000000000000003430c4c0000b8c0000000000000000000002b3
|6,0=>0x22480000000000000000021c80002148832000000020487f2000000000007d21ec87a11e087621d0872200000001c086e21b080001ac469219c86430000000184c5f200005e100005d100005b2168458215c4552000000014c8503134c000000000012c8000124848111880000000000
|6,1=>0xd233408ce2000000032ccca10000c910000000000000031c8c523104c222fcc0002f84bd12ec80002e480002e040000000b620000b420000b312c0c0000000af12b0c0002a88a8200000000000a620000a5128c8a1227c89d200009c1264c963254400024c891223c88e123448b2
|6,2=>0x4a0926248cd20347891c200011b1460d17100000000000000454912300010f300010d242c90a14208000418800041090224044ff23f480000000fb23e48f8100000003d880003d0800000000003cc4f123b8cec23a4c000398ce330000e0337880000000dc20000da23608d710000d52
|6,3=>0x65c99616509913638d8c262c4000624987261498235fcd7e15ecd7925dc97525c8d7025b896c200016935a056620000000590961357c80005748000570559355c9552548d51100014f2538400052cc0005249472514942350093d300013b24e0d3624d093224c0800000012f14b492a3
|6,4=>0x6ec9ba16dcdb436c4daf26b49ac16a880006a09a716948000690400000000006888000680800067c59e100019b366480000000000
|7,0=>0x8e0a3628d0a3228c0a2e28b0a2a28a0a262890a222880a1e2870a1a2860a162850a122840a0e2830a0a2820a071814a0328049ff27f49fb27e49f727d49f327c49ef27b49eb27a49e727949e327885e027789dc276c5d9275c9d5274c9d1273c9cd272c9c9271c9c5270c9c126fc9bd2
|7,1=>0xad0ab22ac0aae2ab0aaa2aa0aa62a90aa22a80a9e2a7469b2a64a972a586942a48a902a38a8c2a28a882a18a842a08a8029f8a7c29e8a7919dca7529cca7129bca6e19b0a6a29a0a662990a622980a5e2970a5a2960a562950a522940a4e2930a4a2920a462910a422900a3e28f0a3a2
|7,2=>0xae0ab62
|8,0=>0xb286c91b206c71b186c510002c41b0c6c21b046c01afc6be1af46bc1aec6ba1
|_,_=>0
def PO:=mkPO wAt oP oO 20 9 511 14
def pmP:Nat→Nat
|0=>0x1678000a3000041600020800010300008100004040002000000c2000040000014a000098000045000022000010e00008400004100002000000c0000042000020000008800003000000f000005000002000000c0000040000018000008000002000000
|1=>0x6010002a2000140400088a00044000020880010040008000003e78001c18000dde0006eb0003678001b2c000cd600064b000315800180c0009100004870002350001128000808000403000201000100000073000031c00018c0000c4000060c0002ef
|2=>0x1145000880800440000210000104100082000040300020040010010007098003844001c02000c03000600000284400122b0008110004010001dde000ecf0007660003b2c001d1e000e4f000705800382000190e000c850006300003098001844000c0a
|3=>0xc5a58060d6c03069601834900904000480000210860106eb00814d004080002020001000a0080000026a3c01341c008e8f004717802382c01151e008a220045078021e2c010d06008400004007002002c00b40c004f0f0020200010008005414002658
|4=>0x840208411b3c208d1e10428f0807678403a3c201d16100e0b08040784002182000861000410800010400004120d9608629f0409458201228100556080000022001009887804b40c02520f012107808601804240c0204020100100080000031f9e018f4b
|5=>0x1445478a1ae74500516208e8f1047468822a3c40d73e20638f10118e0806028401910200802100044071292c38941619c64b0c6725863192c31849618620b0c15458609a2c304c16180e4f0c0527860283c2a008612620f0931058498818218d5610878b
|6=>0x447092e200006a80a0b500805220122910051688000041314fa08806900c51e42422f2103659081088840444404f0d202315900993c8014084002042001000a43a24520d1629028b
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0xd150e0000000002020204000000000000000002020027000000000000020200020202050000000000000000001100230000040207000000000028000000000000000002000200000200090002000000000000000e000000000204000000
|6,0=>0xa2029200009702000e00000000025c7b767c000e16620063001600001200740026030000263900021a83000006001718060202005866218c0002020204590618000000000002005c06000002025a000018184e0218575c0000183927005c228b6900001f020004004f00180e135c68000025a3270000000200015239008200
|6,1=>0x3bc35cb46c020a0027020227357a4406060245011818005506020000062a02000200c41102921c3800060400670002030219022c00062e0f1802020000d0021102023996063b000e270e00000000023f008e005d027302005c0006020e020c000002430b00002900180000000e0544063300032700455300001800015b0e0012
|6,2=>0x1105e7d2075030402000338020014000000930006000e04000806170000
|7,0=>0x806e50334ca7b2a9cf313f349f6ab94094cabda09b9e605fad8642a4bb89c12465879ca1d1b32f3741b0a548cb999d36473d7dd261d4c8ad9546d5ba79aa6b5f13afabb63a4c8571414cb58a3c843cbc7fc677b71ea6c033561bcd72be70c5644acea86f6d2bcc4bc748518d4f324dd3952dc988b8133e9849c25455b14c8f4c
|7,1=>0x1e9a
|8,0=>0xadac816b7e4c4778d130a7904c33aed691bf
|9,0=>0x1d
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 25 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_242 7 roots_242 ops++addP pm 1 dom_241 7 roots_241 ops++addP pm 2 dom_147 5 roots_147 ops++addP pm 3 dom_115 7 roots_115 ops++addP pm 4 dom_82 4 roots_82 ops++addP pm 5 dom_225 4 roots_225 ops++addP pm 6 dom_226 5 roots_226 ops++addP pm 7 dom_99 5 roots_99 ops++addP pm 8 dom_146 4 roots_146 ops++addP pm 9 dom_211 7 roots_211 ops++addP pm 10 dom_227 6 roots_227 ops++addP pm 11 dom_179 6 roots_179 ops++addP pm 12 dom_177 4 roots_177 ops++addP pm 13 dzo_82_1 4 roots_82 ops++addP pm 14 dzo_210_1 5 roots_210 ops++addP pm 15 dom_178 5 roots_178 ops++addP pm 16 dom_98 4 roots_98 ops++addP pm 17 dom_209 4 roots_209 ops++addP pm 18 dom_240 4 roots_240 ops++addP pm 19 dzo_114_1 5 roots_114 ops++addP pm 20 dzo_242_1 6 roots_242 ops++addP pm 21 dom_51 4 roots_51 ops++addP pm 22 dom_195 4 roots_195 ops++addP pm 23 dom_113 4 roots_113 ops++addP pm 24 dom_114 5 roots_114 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_243 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_225 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_226 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_146 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_177 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_82_1_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_210_1_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_178 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_98 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_209 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_240 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_zo_114_1_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_zo_242_1_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_195 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_114 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_242 7 s (0,roots_242.map (·&&&dom_242)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_243 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_242 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_243==dom_243)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_243 gM v ys):RunD true dom_243 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_243 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 11 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 11 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 96 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 96 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 256 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_256 : ∀ i, 256 ≤ i → i < 287 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 31 256 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 287 → Z 6 i = true := (range_split z6_0 (range_split z6_128 z6_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 130 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 2 128 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 130 → Z 7 i = true := (range_split z7_0 z7_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 18 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 18 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_243 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_243 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_243 roots_243 goal_243 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_243
theorem lowS_243:Lower true dom_243 roots_243 goal_243 10:=S_243.noCircuit
def dzo_214_32:=0x55005500000000005500550000000000550055000000000055005500000000
def gzo_214_32:=0x55005500000000005500540000000000550055000000000054004400000000
def gsh_214_32:=0x550055000000000055005400000000005500550000000000540044
theorem lowS_zo_214_32_148:Lower true dzo_214_32 roots_214 gzo_214_32 6:=lower_iso_b (d1:=dom_214) (r1:=roots_214) (T1:=gsh_214_32) [(dom_214,32)] (by decide +kernel) (lower_slice_b (T:=gsh_214_32) [(0x440044000000000044004400000000004400440000000000440044,0,2),(0x550055000000000000000000000000005500550000000000000000,0,64)] (by decide +kernel) lowS_148)
namespace S_246
def pG:List (Nat×Nat):=[(2,18),(2,34),(2,66),(2,130),(4,20),(4,68),(4,132),(6,22),(6,38),(6,70),(6,134),(16,18),(16,20),(16,80),(16,144),(32,34),(32,96),(36,38),(36,52),(36,100),(36,164),(48,50),(48,52),(48,112),(48,176),(64,66),(64,68),(64,80),(64,96),(128,130),(128,132),(128,144),(160,162),(160,164),(160,176),(160,224),(192,194),(192,196),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_246.map (·&&&dom_246)
def gM:=goal_246&&&dom_246
def NN:Nat→Nat
|7=>2
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|7,0=>0xeb5db65c6b
|8,0=>0x3f43d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaa00aa00aa000000aa00aa00aa000000aa00aa00aa000000aa00aa00aa000154015400000000015401540000000001540154000000000154015400000002a8000002a8000002a8000002a8000002a8000002a8000002a8000002a8000500050005000500050005000500050005000500050005000500050005000508800880088008800880088008800880088008800880088008800880088008800015400000000000001540000000000000154000000000000015400000002a802a802a802a8000000000000000002a802a802a802a800000000000000055005500550055005500550055005500000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x358c8f6322c688
|_=>0
def sO:Nat→Nat→Nat
|7,0=>0xcc06
|8,0=>0xc6
|_,_=>0
def wAt:=mkWire dB 8 247 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 9
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xd5d7
|_=>0
def oO:Nat→Nat→Nat
|7,0=>0x441
|_,_=>0
def PO:=mkPO wAt oP oO 8 3 7 6
def pmP:Nat→Nat
|0=>0x1fdf80
|_=>0
def pmB:Nat→Nat→Nat
|7,0=>5
|8,0=>2
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 2 (j%128);fld (pmP (k/32)) 7 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_244 7 roots_244 ops++addP pm 1 dom_182 7 roots_182 ops++addP pm 2 dom_118 7 roots_118 ops++addP pm 3 dom_242 7 roots_242 ops++addP pm 4 dom_214 6 roots_214 ops++addP pm 5 dom_230 6 roots_230 ops++addP pm 6 dzo_214_32 6 roots_214 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_246 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_214_32_148 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_244 7 s (0,roots_244.map (·&&&dom_244)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_246 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_244 h
def symsG:List (List (Nat×Nat)):=[[(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_246==dom_246)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_246 gM v ys):RunD true dom_246 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_246 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 2 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_246 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z7 i (Nat.zero_le i) hi
  · exact z8 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 4 5=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_246 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_246 roots_246 goal_246 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_246
theorem lowS_246:Lower true dom_246 roots_246 goal_246 9:=S_246.noCircuit
def isoMvS_126:List (Nat×Nat):=[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_126:Lower true dom_126 roots_126 goal_126 9:=lower_iso_b isoMvS_126 (by decide +kernel) lowS_119
def isoMvS_189:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_189:Lower true dom_189 roots_189 goal_189 10:=lower_iso_b isoMvS_189 (by decide +kernel) lowS_123
def isoMvS_219:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)]
theorem lowS_219:Lower true dom_219 roots_219 goal_219 10:=lower_iso_b isoMvS_219 (by decide +kernel) lowS_123
def isoMvS_221:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_221:Lower true dom_221 roots_221 goal_221 10:=lower_iso_b isoMvS_221 (by decide +kernel) lowS_123
def isoMvS_235:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)]
theorem lowS_235:Lower true dom_235 roots_235 goal_235 9:=lower_iso_b isoMvS_235 (by decide +kernel) lowS_187
def isoMvS_245:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_245:Lower true dom_245 roots_245 goal_245 10:=lower_iso_b isoMvS_245 (by decide +kernel) lowS_237
def isoMvS_249:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)]
theorem lowS_249:Lower true dom_249 roots_249 goal_249 10:=lower_iso_b isoMvS_249 (by decide +kernel) lowS_237
def isoMvS_250:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_250:Lower true dom_250 roots_250 goal_250 10:=lower_iso_b isoMvS_250 (by decide +kernel) lowS_243
def isoMvS_252:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_252:Lower true dom_252 roots_252 goal_252 10:=lower_iso_b isoMvS_252 (by decide +kernel) lowS_237
def dzo_43_4:=0xf0f00000f0f0
def gzo_43_4:=0xf0e00000a000
def gsh_43_4:=0xf0e00000a00
theorem lowS_zo_43_4_43:Lower true dzo_43_4 roots_43 gzo_43_4 5:=lower_iso_b (d1:=dom_43) (r1:=roots_43) (T1:=gsh_43_4) [(dom_43,4)] (by decide +kernel) (lower_slice_b (T:=gsh_43_4) [] (by decide +kernel) lowS_43)
def dzo_111_16:=0xffff0000ffff0000ffff0000ffff0000
def gzo_111_16:=0xffff0000ffff0000fffe0000fefc0000
def gsh_111_16:=0xffff0000ffff0000fffe0000fefc
theorem lowS_zo_111_16_41:Lower true dzo_111_16 roots_111 gzo_111_16 7:=lower_iso_b (d1:=dom_111) (r1:=roots_111) (T1:=gsh_111_16) [(dom_111,16)] (by decide +kernel) (lower_slice_b (T:=gsh_111_16) [(0xcccc0000cccc0000cccc0000cccc,0,2),(0xf0f00000f0f00000f0f00000f0f0,0,4),(0xffff0000ffff0000000000000000,0,64)] (by decide +kernel) lowS_41)
def dzo_126_1:=0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
def gzo_126_1:=0xaaaaaaaaaaaaaaa8aaaaaaaaaaa8aa00
def gsh_126_1:=0x55555555555555545555555555545500
theorem lowS_zo_126_1_86:Lower true dzo_126_1 roots_126 gzo_126_1 7:=lower_iso_b (d1:=dom_126) (r1:=roots_126) (T1:=gsh_126_1) [(dom_126,1)] (by decide +kernel) (lower_slice_b (T:=gsh_126_1) [(0x55005500550055005500550055005500,0,8),(0x55555555000000005555555500000000,0,32)] (by decide +kernel) lowS_86)
def dzo_94_1:=0xaaaaaaaa00000000aaaaaaaa
def gzo_94_1:=0xaaaaaaa800000000aaa8aa00
def gsh_94_1:=0x555555540000000055545500
theorem lowS_zo_94_1_86:Lower true dzo_94_1 roots_94 gzo_94_1 6:=lower_iso_b (d1:=dom_94) (r1:=roots_94) (T1:=gsh_94_1) [(dom_94,1)] (by decide +kernel) (lower_slice_b (T:=gsh_94_1) [(0x550055000000000055005500,0,8)] (by decide +kernel) lowS_86)
def dzo_87_8:=0xff00ff0000000000ff00ff00
def gzo_87_8:=0xff00fe0000000000fe00aa00
def gsh_87_8:=0xff00fe0000000000fe00aa
theorem lowS_zo_87_8_86:Lower true dzo_87_8 roots_87 gzo_87_8 6:=lower_iso_b (d1:=dom_87) (r1:=roots_87) (T1:=gsh_87_8) [(dom_87,8)] (by decide +kernel) (lower_slice_b (T:=gsh_87_8) [(0xaa00aa0000000000aa00aa,0,1)] (by decide +kernel) lowS_86)
def dzo_47_16:=0xffff0000ffff0000
def gzo_47_16:=0xfffe0000fefc0000
def gsh_47_16:=0xfffe0000fefc
theorem lowS_zo_47_16_41:Lower true dzo_47_16 roots_47 gzo_47_16 6:=lower_iso_b (d1:=dom_47) (r1:=roots_47) (T1:=gsh_47_16) [(dom_47,16)] (by decide +kernel) (lower_slice_b (T:=gsh_47_16) [(0xcccc0000cccc,0,2),(0xf0f00000f0f0,0,4)] (by decide +kernel) lowS_41)
def dzo_59_4:=0xf0f0f0f0f0f0f0f0
def gzo_59_4:=0xf0f0f0e0f0f0a000
def gsh_59_4:=0xf0f0f0e0f0f0a00
theorem lowS_zo_59_4_43:Lower true dzo_59_4 roots_59 gzo_59_4 6:=lower_iso_b (d1:=dom_59) (r1:=roots_59) (T1:=gsh_59_4) [(dom_59,4)] (by decide +kernel) (lower_slice_b (T:=gsh_59_4) [(0xf0f00000f0f0000,0,16)] (by decide +kernel) lowS_43)
def dzo_119_8:=0xff00ff00ff00ff00ff00ff00ff00ff00
def gzo_119_8:=0xff00ff00ff00fe00ff00ff00fe00aa00
def gsh_119_8:=0xff00ff00ff00fe00ff00ff00fe00aa
theorem lowS_zo_119_8_86:Lower true dzo_119_8 roots_119 gzo_119_8 7:=lower_iso_b (d1:=dom_119) (r1:=roots_119) (T1:=gsh_119_8) [(dom_119,8)] (by decide +kernel) (lower_slice_b (T:=gsh_119_8) [(0xaa00aa00aa00aa00aa00aa00aa00aa,0,1),(0xff00ff0000000000ff00ff00000000,0,32)] (by decide +kernel) lowS_86)
def dzo_118_8:=0x55005500550055005500550055005500
def gzo_118_8:=0x55005500550054005500550054000000
def gsh_118_8:=0x550055005500540055005500540000
theorem lowS_zo_118_8_86:Lower true dzo_118_8 roots_118 gzo_118_8 6:=lower_iso_b (d1:=dom_118) (r1:=roots_118) (T1:=gsh_118_8) [(dom_118,8)] (by decide +kernel) (lower_slice_b (T:=gsh_118_8) [(0x550055000000000055005500000000,0,32)] (by decide +kernel) lowS_86)
def dzo_86_8:=0x550055000000000055005500
def gzo_86_8:=0x550054000000000054000000
def gsh_86_8:=0x5500540000000000540000
theorem lowS_zo_86_8_86:Lower true dzo_86_8 roots_86 gzo_86_8 5:=lower_iso_b (d1:=dom_86) (r1:=roots_86) (T1:=gsh_86_8) [(dom_86,8)] (by decide +kernel) (lower_slice_b (T:=gsh_86_8) [] (by decide +kernel) lowS_86)
def dzo_107_4:=0xf0f00000f0f00000f0f00000f0f0
def gzo_107_4:=0xf0f00000f0f00000f0e00000a000
def gsh_107_4:=0xf0f00000f0f00000f0e00000a00
theorem lowS_zo_107_4_43:Lower true dzo_107_4 roots_107 gzo_107_4 6:=lower_iso_b (d1:=dom_107) (r1:=roots_107) (T1:=gsh_107_4) [(dom_107,4)] (by decide +kernel) (lower_slice_b (T:=gsh_107_4) [(0xf0f00000f0f0000000000000000,0,64)] (by decide +kernel) lowS_43)
namespace S_127
def pG:List (Nat×Nat):=[(1,9),(1,33),(2,18),(2,34),(2,66),(3,11),(3,19),(3,35),(3,67),(4,20),(4,68),(5,13),(5,21),(5,37),(5,69),(6,22),(6,38),(6,70),(7,15),(7,23),(7,39),(7,71),(8,9),(8,40),(10,11),(10,26),(10,42),(10,74),(12,13),(12,28),(12,44),(12,76),(14,15),(14,30),(14,46),(14,78),(16,18),(16,20),(16,80),(17,19),(17,21),(17,25),(17,49),(17,81),(24,25),(24,26),(24,28),(24,56),(24,88),(32,33),(32,34),(32,40),(32,96),(36,37),(36,38),(36,44),(36,52),(36,100),(48,49),(48,50),(48,52),(48,56),(48,112),(64,66),(64,68),(64,80),(64,96),(65,67),(65,69),(65,73),(65,81),(65,97),(72,73),(72,74),(72,76),(72,88),(72,104)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1fffffffffffffffffff
def xsM:=roots_127.map (·&&&dom_127)
def gM:=goal_127&&&dom_127
def NN:Nat→Nat
|5=>17
|6=>73
|7=>188
|8=>265
|9=>138
|10=>14
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0xf7412c0df1b1540993368411a82d1f813805d68d456d73c7ff2f93f1cda31932811f9c0bdff0593301118
|6,0=>0xf955df8c83ecdf1e9750e656bde900d5fcbcff54cf0c7b290ab16d0af53eae69aaa8c2a71f8a344d9f9ad9bf689b0b99971a98227963878e71388b8285951854dc817f07e47f7a49c75a47724937179a6f8fa687ff680f066e0b65fdf602bf5e15e5d148577e45755a574165610b556ba47cd945b4743db9405243f33c38abe36d393409b3350b316c22f61c2b676252b619a40194b217ba012e251161a0f7ac0ec9f0e11207da305f0304c9903c95027cf020be01f7a
|7,0=>0x8cee086ef285cf382c088248980c4b803eb7ed867e1b07da587ca937bdfa7bb957a36377cc4743cc736877252c7200b6d1996c2dc6b29f6a0a86990a68d3268889687ff67a586730366b426582e62ffe629526264861b3960fce5fd7a5d8a95b8b45b4fc59b99598b058479552f153c9f515a451237509cf4fbc24f3314eb994e9f64d2e84ca2f49758488214770445fd54386743654417ae40e343e83a3d6503b6f03b4be399a53918538fb33841c380b2380623563632f282fdf52e9482ba7c2b9802b6202b3482b1bf2aa6b29aa628dc728c7e282232703926d0426208251e1234e92112120b822032e1f0f21ec0e1c4711a9a91a62d1a1911a03d17fb615a7514c28145241315b12c2b10d8b1071f0f5d10e3600dc050c8070bff90bfd90b6a80af240a98b0a8bc096cf07d0a07c73065b80358102b910162b0107e00f8e
|7,1=>0xfe905fc773f5de5f52fef3135ee18deb980eb0a8e94c0e8ba2e82eee7840e6dc9df7b5de096dd624db258d43b2d3ad8d21f6d19d7c8babc4ef3c0df1be9cfbe696bd92abcb2fbc7f6b8d28b7d47b755ab56bab54abb4302b41ccb232cb2170af17dae1b8ac840a9a08a6aada1aa9a1a599f02d9dceb9a99399b8a9811996916947ff937bf927e39258c906ec8ed1f8dde18d7098d499
|8,0=>0x4b2c24a86e4a45a490be4883f481cb47ab0468784537244ea744ca8447d843fbe43b87436544301342003405bd400103ec2d3c9ce3c1153b9aa3b3713ae0c39c0e395ed394e2386fe3740a36709364263623135f7b359b234b5833e1632d143254f311912fdf52e02c2da292d9d92d8be2d0152c7672afad2984b292f128932282b627884266cd258c5255cf24af324373241ca22546217e121414212e820e2a201071f8081f42b1efe81ec0c1ce3c1c8211c6b61c6031bb9d1acb91a4621a177197fc1949818e6018537179041765416c9e16a721606714fb614e3414dfe13c891281912563123e41212811def114a2111d80f9e60f7620cfb30c8070c23b0ade60acb30a8bc0956f0889d084d8084ba07925076cc068d1068220656f061b305f5d05e0905c2405b6c04db804c680402a03c1c01abc01a3b017350120300e28
|8,1=>0xee191ecf7eec262eb597eb261e65a3ddfc2dbed3da115d9849d7edfd58bad4e28d1b90d0cf6d0c3acdf8acc03fc7b25c7929c73a5c3f6bbc515bb95ab98e2b8eebb586db51c4b4538b3c51b1624b0dcfad04bab49eaa9d4a991ca83b2a7ad8a70b9a46dba468ba2675a1c5f9e54f9e46c9945f98a2496ff7942799189790bbb906eb8fb128dd078c80689b5889298880f5872e2842a5835778233c80d3b80c5d7fd637e4c47dcd77981b78f9c781357744c761fa73f9072e4b720297200b7195c711e06a55d6a31669f356855e682ee675af672ff66e0b669496638464aa96410f640ac63934630a362b7b6295262648623a361d476125d6114d5fda25e1765d5b95c5975bc9a5a1b9585745854f57a495735f56bd4551b854a4253e695118350e7350cf2507b64f2f44ef404ee2f4e4dc4e4884dede4de7a4d9914c7834b42b
|8,2=>0xfe233fcf9afb75af7783f2e0befc2eefa7deecdeeec8e
|9,0=>0xd89b2d3928cec71cdf47cdd70cb389cae58c7760c6e0bc3a7dbf087bdd15bb383ba0a2b6ac8b51c4b16d2b0480afed3afc7daded7aa9a7a991ca8a85a8201a6636a4c3aa36faa24cba21faa1f8aa11819bd299b7a09b2b798001934af912d68dc818ceeb8c1808b3068104b80e3c7e3a47a7e379dde776fa761fa721876d2926a3f7688a56765b64cd36309f5e22c5d2755d1915cc7658cab57fbf4c7834a45a49cb6489a04816946fad46f5d46aaa4454a445313fd7a3d5ff3d36c3c55e3c2ee3a6793933b38fcb363a335d47350f0348ea33f6c3254f323e43119130ed6308f72d79b2bc422a4cf292d4291b824b852479722dec2258c224dc2150d1df2b1ab8a1927417b871765416ab6156f1155f210c780dece0c8070c6fe0bb3f0baf90a7090a4e309fe00973f0969708cad07bf806d14053570398a037ed016a400f9b
|9,1=>0xfd84bfa280f7decf673bf4ebdf1cfbeb784de17cdd06ad8c87
|10,0=>0xe74f2ce280bbe948d3bf83c7d761fa715435254f43a533b65b31191150280cfcb05c14
|11,0=>0x2654f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xfffffffffffff0f0f0f0f0f0f0f0f0f0cccccccccccccccccccccccccccccccc00ff00ff00aa00aa00ff00ff00aa00aaffffffffcccccccceeeeeeeecccccccc0f0f0f0f0f0f0f0f0f0f00000f0f000055555555550055005555555555005500ffffffffffffffffffffffff00000000ffff0000ffff0000ffff0000ffff0000ffffffffffffcccccccccccccccccccc00ff00ff00ff00ff00ff00ff00aa00aaffffffff00000000ffffffff00000000ffffffffffffffffffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ffffccddffffccccccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
|0,1=>0xffff0000ffff0000ffff00000000ffffffff00000000ff00ff0000000000ffffffffffffffffffffffffffff0000ffffffffccccccccffccffccccccccccffffffffffffffffff00ff00ff00ff00aaaaaaaaaa00aa00aaaaaaaaaa00aa0055005500550055005555555555005500fffff0f5fffff0f0f0f0f0f0f0f0f0f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0000ff00ff00ff00ff00ff00ff00aa00aa00ff00ff00aa00aa00ff00ff00aa00aa00ffffffffffffaa00ff00ff00aa00aa0000000000333333330033003333330000ffffffffaaaaaaaaffffffffaaaaaaaaffffffffff00ff00ffaaffaaff00ff00ffffffffffffffff0000000000000000
|0,2=>0xf0f0f0f0f0f0f0f0f0f00050f0f0000ffff5555ffff00000000000000000000ffff5555ffff0000ffff5555ffff0000ffffddddffffccccccccccccccccccccffffffffffffffff5555555500000000ffff00ffffff00000000000000000000ffff00ffffff0000ffff00ffffff000000ff00ff0000000000ff00ff00000000ffffccffffffcccccccccccccccccccc000000000000ffffffffffffff00ff00ffffffffffff0000ffffffffffff000055555555000000005555555500000000ffffffffffff0000000000000000000033333333333333333333333333330000ffffffff00000000aaaaaaaa00000000ffffffffffffffffaaaaaaaaaaaaaaaa
|0,3=>0xffffff0000ffff00ff00ff00000000ffffffffccccccccccccccccccccccccffffffff000000000000000000000000fffffffffcfcfcfcfcfcfcfcfcfcfcfc00000000333333333333333300000000fffff0fffffff0f0f0f0f0f0f0f0f0f0ffaaffaaffaaffaaffaaffaaffaaffaaffffffffffffffff00ff00ff00000000ffffffffffffffffffffffffff00ff0000000000ffffffff00ff00ffffff000000000000aaaaaaaa00aa00aaaaaaaaaaffffffffff00ff00ffffffffff00ff00ffffffffaaaaaaaaffaaffaaaaaaaaaa0f0f00000f0f0f0f0f0f00000f0f0000000000000000ffff00ff00ff0000000000330033333333330033003333330000
|0,4=>0xaaaaaaaaffffffffaaaaaaaaffff0000ff55ff55ff00ff00ff55ff55ff00ff005555555555555555555555555500550000000000ffffffff00000000ff00ff00ff00ffffff00ffffff00ff00ff00ff00aa00aa00aa00aa00aaaaaaaaaa00aa000f0f0f000f0f0f0f0f0f0f000f0f000033333333333333333333001133330000aaaaffff00000000aaaaaaaa00000000aaaaffffaaaaffffaaaaaaaaaaaaaaaa0000ffff0000ffff0000000000000000ffaaffffff00ff00ffaaffaaff00ff000f0f0f0a0f0f0f0f0f0f00000f0f0000fffff5f5fffff0f0f0f0f0f0f0f0f0f055555555555555555555555500000000ffff0055ffff00000000000000000000
|0,5=>0xffff0055ffff0000ffff0055ffff0000ffffff55ffffff00ff00ff00ff00ff00aaaaaaaaaaaaaaaaffffffffaaaaaaaa00aa00aa00aa00aa00ff00ff00aa00aa0000000000000000ffffffff00000000ffffffffffffffffffffffaaffffffaa0f0f0f0f0f0f0f0f0f0f0f0a0f0f0f0affffffffffffffffffffffffaaaaaaaaff00ff00ffffffffff00ff0000000000ffffff00ffffffffffffff00ffff0000ffffffff0000ffffffffffff0000000000000000ffffffff00000000ffff0000ffffffffffffffff005500550000000000550055000000000055005500000000ffffffffffffffffffff0055ffff0000ffff5555ffff0000ffff0000ffff0000
|0,6=>0xff00ff00aa00aa00ff00ff00aa00ff00ffffffffffffffffffffffffffffff00aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa000f0f0f0f0f0f0f0f0f0f000f0f0f0000ffffffffffffffffffff00ffffff0000333333333333333333330033333300000000000000000000ffffffffaaaaaaaaffffaaaaaaaaaaaaffffffffaaaaaaaaffff000000000000ffffffff00000000ff00aa00aa00aa00ff00ff00aa00aa00ffffff00ffffffffffff0000ffff0000ff00ff00ffffffff00000000000000000f0f0f000f0f0f0f0f0f00000f0f0000ff00ffff00000000ff00ff0000000000ffccffffccccccccffccffcccccccccc00000000ffffffff00ff00ff00000000
|0,7=>0xffff00ffffff0000ffffffffffffffffffffffffffffaaaa33333333333333333333333333332222fffffffff0f0f0f0fff0fff0f0f0f0f000ff00ff00aa00ff00ff00ff00aa00aaffaaffaaffffffffffaa0000ffff000000ff00aa00aa00aa00ff00ff00aa00aaffffffffffff0000ff00ff00ff000000ffffffffffaaffaaffffffffffaaffaa00ff00ff00ff00ff00aa00aa00aa00aa00000000ffffffff0000000000000000ffff0000ffffffffffff0000ffff00000000000000000000ffffffffffff0000000000000000ffff00000000000000000000aa000000ff00ff00ff00ff00ff0000000000555555550000000055550000
|0,8=>0xffffffffffff00005555555500000000ffffffffaaaaffffffffffffaaaaaaaaffaaffaaffffffff0000000000000000ffffffaaffffffffffff0000ffff0000ffffffff00000000ffff00000000000000000000ffff00000000ffffffff0000000000000000000000ff00ff00ff0000ffffffffffff0000ffffff00ffff0000ffffffffffffaaaaaaaaaaaaaaaaaaaa0000000000000000000000ff00000000f0f0f0f0f0f0f0f0f0f0f0fff0f0f0f0ffffaaaaffffffffffff0000ffff0000aaaaaaaaffffffff00000000000000000f0f0a0a0f0f0f0f0f0f00000f0f0000ff00ff00ff00ff00ffffffffff00ff0000000000000000005555555500000000
|0,9=>0xff00ffffffffff00ff00ffffff0000ff00ff00ff55ff55ff00ff00ff55ff000000000000000000ffff5555ffff0000ffaaffffaaaaaaaaffaaffaaaaaaaaaa0000ffff0000ffff0000005500000000ffffffffffffff00ff00ff00ff00ff000000ffaa0000ffff0000000000000000ffffffffff00ffffffffffffff00ff00aaaaaaaaaa00aaaaaaaaaaaaaa00aa000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0055000000ff00ff0055005500ff00ff00ff00ffffff00ffffff00ffffff00ff0000000000ff00ffff00000000ff00ff00ffffffffffffffffffaaffaaffaaffaaffffffffffff0000ffffaaaaffff00000055ffff0000ffff0055005500000000
|0,10=>0xffff000000000000ffff00000000f0f0fffff0f0f0f0f0f0f0f0f0f0f0f0ffffffffffffffffffff5555ffff000055555555555500005555555555550000ffffffffffffffff55555555555500000000aaaa0000ffff0000000000000000ffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa0000000000000000fafafffff0f0f0f0fafafafaf0f0f0f00000000000000000ffff0055ffff0000000000000000ffffffffffff0000000000ff00ff0000ffff00ff00ff0000000000000000000000000000ffff0000aaaaf0f0f0f0f0f0f0f0f0f0fffff0f0fafa00000000ffffffff555555550000000000ff00ff00ff00ff00ff00ff00ff00aa
|0,11=>0xffff0000ffff0000ffff0000aaaa5555555555555555555555555555000055555555555555555555000055550000aaaaaaaa00000000aaaaffff0000000000000000ffffffff00000000aaaaaaaa0000000000ff00ff0000000000000000aaaaaaaaaa00aa00aaaaaaaaaaaaaaaa55555555000000000000000000000000ffffffffaaaaaaaaffffaaaaaaaaaaaa00ff00ff00ff00ff00ff00ff00000000aaaaaaaaffffffffaaaa0000ffff0000ffffffffffffaaaaffffffffffffaaaa00ff00ff00ff00aa00ff00ff00ff00aa00005555000000000000555500000000f0f0f5f5f0f0f0f0f0f0f5f5f0f0f0f00000ffff000000000000000000000000
|0,12=>0xffaaffffffaaffffffaaffaaffaaffaaffff0000aaaa0000ffffffffaaaaaaaaccccffffccccccccccccccccccccccccff55ff55ff55ff55ff55ff00ff55ff00ff00ff00ffffffffff000000ffff000000000000555555550000000000000000ff00ff00ff55ff55ff00ff00ff00ff00aaffaaffaaaaaaaaaaffaaffaaaaaaaa00000000000000000000ffff00000000aaaaaaaaaaaaaaaaaaaaffffaaaaaaaa0000000000000000ffffffffff00ff00ffff0000ffff0000ffffffffffffff00aa00aa00ff00ff00ff00ff00ff00ff0000000000ffffffffffffffff00000000aaaaffffaaaaffffaaaaffffaaaaaaaaffffffffff00ff000000000000000000
|0,13=>0x55005555550055555500550055005500000000000000000000ff00ff00000000ffff0000ffff0000ffff00ffffff0000000000000000000000000000ffffff00ffffffffffffff00ffff0000ffff0000ff00ff00ff00ffffff00ff00ff00ff00ffffffffffff0000aaaaaaaaaaaa00000000ffff0000ff000000ffff0000ff0000000000000000000000ffff0000ff00ff55ff55ff00ff00ff00ff00ff00ff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff0000000000aaaa0000ffff0000ffff0000ffff00000000ffff0000ffff000000ff00000000f0f0fffff0f0f0f0f0f0fffff0f0f0f000000000000000005555555555550000
|0,14=>0xff00ffffff00ffffff00ffaaff00ffaa00550055005500550000000000000000ffff0055ffff0055ffff0000ffff0000ffffffffaaaaaaaaaaaaaaaaaaaaaaaaffffffff55555555ffffffff55550000ffffff0000000000ffffff0000000000ffffffffffffffffffffff000000000000ff00ff00ff00ff0000000000000000aaffaaffaaffaaffaaaaaaaaaaaaaaaaaaaaffffaaaaaaaaaaaaaaaaaaaaaaaaffff00ffffff00ffffff00ffffff0000ddddddddccccccccccccccccccccccccffffaaaa00000000ffffaaaa00000000ff00ff00ffffffffff00ff00ffffff0000005555000055550000000000000000ff00aa00ff00aa00ff00ff00ff00ff00
|0,15=>0xffff0000aaaa0000ffff0000aaaaffff0000ffff5555000000000000000000ff00ff000000ff00ff00ff00000000ffff0000ffff00ffffff0000ffff0000ffffffffff00ff00ffff0000ff000000ffffffffffffaaaaffffffff0000000055555555000000005555000000000000000000ff000000ff0000000000000000aaaaaaffaaaaaaffaaaaaaaaaaaaaaaa0000ffff0000ffff0000ffaa0000ffaa0000ffff0000ffff0000ff000000ff00ffffffff0000ffffffffffff0000ff00f5f5f5f5f0f0f0f0f0f0f0f0f0f0f0f00000ffff0000ffff0000555500000000aaaaaaaaffffffffaaaaaaaa000000000000ffff0000ffff0000aaaa0000aaaa
|1,0=>0xffff0000ffffffff000000000000000000000000ff00ff0055005500ff00ff00ffffffffffff0000ffff0000ffff00005555ffff0000ffff5555555500000000ffff5555ffff5555ffff5555ffff0000ff000000ff00ff00ff00ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff000000550055005500550055000000550000ff00ff00ff00aa00ff00ff00ff00aa0000ff00ffffffffff00ff00ff00000000fffffffff0f0f0f0fafafafaf0f0f0f0f0f0f0f0f0f0f0f0f0f0fffff0f0f0f000ff00000000000000ff00ff00000000ffffffffff00ff00ff00ff00ff00ff00000000000000ffff000000000000aaaaffffffffffffffff0000ffff0000ff00
|1,1=>0xff00ff0000000000ffffffff000000005555550055555500555555005555550000ff00ff00ff000000ff00ff00ff0000ff55ff55ff55ff55ff00ff00ff00ff00ffffffffaaaaaaaa0000000000000000ff00ff00ffffffffff00ff00ff00ff000000000000000000ffffaaaaffffaaaa55555555555555550000000000000000aa00aa00aa00aa00ff00ff00ff00ff00ffffffaaffffffaaffffffaaffffffaaffffffffffffffffffffff00ffffff00000000000000aaaaaaaaaaaaaaaaaaaa00000000ffff000000ff0000ffff000000000000000000000000555500000000ffffffffffffffffffffaaaaffffaaaa0f0f0f0f0f0f0f0f0f0f0a0a0f0f0a0a
|1,2=>0xfffffffff0f0f0f0f0f0f0f0f0f0f0f0ffff0000ffff0000ffffffffffff000000000000ffff0000ffff0000ffff0000ffffffff55555555ffffffff000000005555555555555555550055005500550000000000ff00ff00ff00ff00ff00ff00ffffffffffffffff0000ffff00000000aaaaffffaaaaaaaaaaaaffffaaaaaaaa00000000ffffff0000000000ffffff00ffff00ffffff00ffffff0000ffff0000
|_,_=>0
def sP:Nat→Nat
|0=>0x4070060200014101107000161002820360e0d02c20050400c1c19058400a04018601c00048200602060001208018300017028102a020380012080b0080e00028102a0f070000a040a0081c00048202a020380012080a0081c000482006020004c0a040101c000d09020220e058400a0407838000d04820060c0002c1208018080e0a048200407000180a04018080200
|1=>0x80241003010380031028200602000c020090400c1c001082c0a0807838000d080141003070005e100282006021600056050200c0407000900a08070002e060801410030100400100282004001101820050200c0427000981208018081c000282006180700020050200c1e0e000900a04018081c1a11814100e0005c1a100282004001103420090400c040c0007c3a09
|2=>0x88200504038000b068400a08018080e001c02410030f0081c0002820060c0002c20340482006020380068080f038000b080dc1208018080e0004820040e0001846090400c3c0e0005c12050400c042c00024100301038003604820061e010004405040080e0006840120801038000d1181410030702c6a101a0101033010382005040541c24058400a080a8380032
|3=>0x281006420700048090400c0407001040a04018081c00200d00a04018080e00028202a0f07000200504050040e000400a080b0380017080141016010004410028100602138005005040081c1a1f84068050200c1e0e0002410031e0007605020081c000688c1208018080e0014014100e0002c0c1002810063a070006812040e41c0b080141015070002e10028202a02
|4=>0x808c1208018080e0002820060e0002c981002820360307080000b0282096020706820050400c1c4a058400a080b038000b08024080801808180002820060e001242005020e40602038000a08018080048080241016010380023028107203078380005040380032068402408220081c10028202a0203800200904054040e0008c0a08018380043080241039018080e00
|5=>0x8820052b02006020700020050400c040e000ac46090202006020700042050400c040e000ac5c550282006020700020050400c3c0e0002c20050200c040e000a046050400c040e0d15020120281006020700046052882006020700020052800c040e000400a08018e81c00140400a08018081c4f000400a082700c1c00058404a090400c040e268400a080a8081c00
|6=>0x2810100307068161004820060207000c0120282072030702c200902820060e100001605020200602070d420052f810060207000200504178040e000400a04040081c002e0400a0404054040e120403a090400c040e000840a0801838004105840aa050400c040e0504012052d820060e0002c6808198081c1002820060e00164205802820060e0005c2058028200602
|7=>0x140a80a08018081c001f8400a08388081c00080d00a0807000162808014106f010380010028202a02070ac20050400c040e368400a08018084e0008014100307000d82808014100301000d428081a40a0801838000b08014106601038001002810060f070000a080183c1c00120400a080183800630802410030103800210f8141061018080010128140802070001a10
|8=>0x70001638080d01062010380010028101002070001a1002820060e0002cec10028101003010300010028100602038000a08018080e001204068050400c1c00190401208018081c001208c12050400c040e000b80a080a8081c2408114680404078040e000400a041c80c040e0008c0a74040081c0006840e605040081c00068400a0801038000d081c80a04018081c00
|9=>0x1c0141003070006428081cc0a08018081c001c014080801038000608014100301000fa1004820f803070002025048202a0207000205804820060207000465502820040e001ec201d02820040e000342005041e806020700020050400c1c00059482034090101039010382012028202a0e0002c2005040081c003c8400a0404054040e100401208019e0040e000141003
|10=>0x400c1c00058406805040081c001f8400a0807000160d080151808018081c00081540a080a8081c0008014060207001141004814100301038008904a2006020700020050400c040e438400a0801038000d081140a0801a141c00080740a08010380006080141003070004882082040a0801838000b08014100307001000b080141002070001a1f08014fe08018081c00
|11=>0x2a040120801808180008014100307000d83808014100301000d438080141002070012a100482006020700126100282124030700016101282410160103800101a0141003070002e102c01410030700016101a014100301000441002a440602070002005040081c000307c2034090207202070408a050400c040e0024020050400c040e0023c2005040081c003d8406812
|12=>0x20201c00058342005042700602070400a08018081c004d8400a08018380017140400a08018080022140400a04018081c001701410031d038001009014100307080161002820060e0002c1a1012814081501038001009020060e0002c501002820720307000641004814109a0103800050400c040e0004132550282006020725c20050400c1c004b0400a0801038000d
|13=>0x101c001004814b60801838001704814b6080180800221a024100301038002302820060e001b020050400c0400350400a080103800a008014100301038009f0801410030109c002808014e8080a8081c00081cc0a080a8081c00080141015010380010390d00a080183c1c00080141003010392e1002820040e000342023028213c0207000200902a741003010380005
|14=>0x28101016010380010028202a0e0002c200902a9410030103800050400c040e00290200504054040e0007c20090400c040c000141039018380017080240a080183840000b81410035103800100282072030100044100481410030108000220e814101501038001002820060207000204002820060e001042e100282006020010444100482006020700142101a0141003
|15=>0x1c80c040e0008cee050400c1c00058401208018081c002088c100307000480b140401208018087c001d814101601038001f080254a08018081c000481410030101c00050400d4e0e000400a081c80c1e0e000404a09040081c00068401208018f07c000e81410160103800101a014100307028161002810101101038001002a981003010380010028101003010389410
|16=>0x2cc20340282006020700020230e8141039018081c000801410035883800100e8240a08018081c2000014100357038001002ab4100301038002b080241003010f800054e8200602070002069028101003010380010028209c030103800102281410030103800ab080141003010380024082a80a08018081c20540d00a040400c1c00058400a081c80c0407000401208
|17=>0x202006020700176101a0203c020700020550282006020700020050400c040e5c8404a050400c040e0d0400a08018081c002087c20052800c040e000400a08018081c001415020055b820060207000201d028200602070016c10090141003010380054080240a5b0400c040e0007d3055028200602070002034028101002070005010028200602070016a1002820040e
|18=>0x2820040e0003420050400c1c000b84012050202036030103800050400c040e001c020050426806020700020050400c040c000400a0801808002208014100301039820008014100301038009308014101b0103800c0128140602070017a1002820720301038001f080240a08018081c200007c0a08018081c005f84012050400c040e002f820050400c040e5e0002005
|19=>0x40e4060e0002c200502020060e0002c50100282198030103800100282006cb01038002808014101501038401002821920207000200502020060207000ec10028101003010399000080141003010380010550141003010398c00080480a081c80c040e081141208018081c002604188050400c040e000404a050200c040e0009020050430c040e000418408018081c00
|20=>0x1b441c00080240a2d0400c040e000402405020202a020700020050400c040e00340203402820040e000a02045028219e030103800106701410030103800100282006020700050101182410030f0081c0008308b608018081c00028200602668002098028200602070002034090207202070400a040400c040e000e020052d0200602070002005148100602070002005
|21=>0x2a0400a0801038000d081d40a086b0081c00080d00a04040e4040e000400a080195c040e000400a5b0400c040e000400a08018081c001f8400ad40400c040e000400a740400c040e0009020730282006020700048101a014100207000701002b4c06020700020050400c040e000a1a410028200602070004810390140808018081c00290400a08010380006080240a08
|22=>0x801410e2018081c00081a00a08018081c000801410e001038001002820060207001be1004814100301038002302820063c1f00020056e82006020700020050400c040e0037020056d820060207000208102810100301038001002821b4030103800100281010030103800800801410030103800d908014101b0103800d80801410030103800d7080141039018081c00
|23=>0x28a41003010380038080141003010380052081140ae90400c040e0004012050400c040e738480a080a8081c00081140a08018081ce6080240ae50400c040e000403a050400c040e0009020050400c04e4000404a092d820060207000681202020060207000200502020040e0003420054202006020700048100482006d10700020050400c1e0e000404ae3018081c00
|24=>0x903e10128dc1208018081c00080141039018081c000808c0a0801bcc1c000801410030103800f2080240a08018081c0078840b00502020060207000202504820060207080000902b081003010380005043bc06020700020057682006020700020050400c040e760400a04040e4060e0002c20050400c040e000a0202a758141003010380010028200602070005610
|25=>0x5f8400a08018081c007c8400a08018380024058400a08018081c00082340a840400c040e000404a050400c040e000e0201d2c0141003010380010028200602073dc207e0282006020700020050400c040e003d820053582006020700020050400c0407000400a040424806020700020090400c040e0008c4a340482006020700020f40282006020700020050400c040e
|26=>0x1038000d0802410030f0081c00048141003070002e102c014100301038001f080240a080180800220801410fb018081c00080145a04018081c001204012050400c040e6080020050400c040e0011c20340902006020700020450282006020721c2005040081c00068408a05020200602070004210090101003010380028083e80a08018081c00080240a08018081c00
|27=>0x3040120504408040e00014be08018081c00080240a08018081c0008014100301038010108014100301038002b790404a090400c040e000a020054880c040e000400a08018081c00800400a08018081c00083f8aa050400c040e003f420057e02006020700020342a8141003010380010090140808018081c20080140808018081c000684012c20400c040e000240a08
|28=>0x28220e020700020050400c1c200002c20050400c040e00418200902820060207001b8102a814100301038002808014100301038000d081140a08018081c007e8400a0801c141c0008014b60801838000b080481003010380028081140a880400c040e000400a0801c101c00080940a0801038000d080240ad40400c040e000400a08018081c00818401205040081c00
|29=>0x700020050400c040e000405c34029d01003010380010398d00a08018081c0008014100301038010c1204068050400c040e00040e40504054040e00040ea2504820720301038001002c2c10030103800100282214020700020250482006020700082100282006020700212100294010030103800100282006020700210100281006020700046251a0140803010380010
|30=>0x8014fe08018081c00140400a030103801130807468050400c040e000400a08018081c002984068050202006020702820050400c040e0044820050400c040e73840aa05040e406020700020050400c1c00880400a08088081c000801410030103832100281010150103800102d8200602070021e05040081c00870400b0d018081c00080141003010389410028202c02
|31=>0x745020050400c1c00190400a040406c0602070800025028107203010380010398240a08018081c001a0141003010381410228480a08018081c46080d00a0801838000b080940a8b018081c00080240a080a8081c00081dc0a040400c040e000400808018081c00120a0200504054040e000408a34028200602070003e1002ab41003010380024080240a0801838000b
|32=>0x801410030103800b2080158408018081c002d82006d107000201d04814b608018081c00048141016010380010028101003010380041081dc0a08018081c000811412052d81010030103800053a0207203010380010398141039018081c000801410150103848100400c040e000905010228141039018081c00081c812050400c043e000951603010380010028200602
|33=>0x18081c00082040a08018081c00080240aa90400c040e000400ad50400c040e1000020050400c040e0020020050440806020700020058b02006020700020050400c040e0004170058a8200602070002025028200602070005010128480a08018081c00080d00a081c8081c0008015aaa9018081c0008015aa080d8081c000801410030103800ff080d00a08018081c1a
|34=>0x70023a100282238030103800100282006020700020a80282006020700020ba2c01410030103800105a0141003010380010048141039018081c000801410030103800108d8141039018081c000811468120400c040e000400a0801038000d080240a08018081c00208400a088d00c040e000400b190400c040e000400a088b8081c00080480a08018081c24081540a08
|35=>0x28200602070004210090200602070005010128141039018081c000801410030103800107c01410030103800c70801410030103800bd080940a04018081c0008014b608018081c0008014100301038002b120400b0d0400c040e000400b1f0400c040e000400a080d80c040e004600a08018081c0012040ea050400c040e004782005042480602070002025028200602
|36=>0x282006020700230050400c040e0048c20050400c040e003c020053a02006020700020730282006020700020057182006020700020050400c040e000421e050400c040e00040e4050400c040e9100020c50282006020700020050400c040e0048420120282006020708020050400c040e00034200590020060207000205b0400c040e002bc2005020200602070004810
|37=>0x816012050400c040e000400a080d80c040e1000020050400c040e0007c200504490040e000400a040400c040e100002009028200602070015e10028200602070005010320740a08018081c00080141003010384000780400a5b0202006020700020090282006020700048100282006021f00020050400c040e000902045028200602073b020050400c040e000ac2009
|38=>0x801410030103840003a8141003010380010770940a5b0400c040e000401208018081c001e814b608018081c003a8141003010380054080d00a08018081c0a080141003010380125080240a08018081c20000400a080a8081c00080240a5b0400c040e000401208018081c00578400a290400c040e0004012050400c040e000f40a0801838000b080240a08018081c00
|39=>0x18081c00260400a080d80c040e10000680502020060207000201d0481410030103800102d820060207000ea058680c040e000400a08018081c000808c0a082580c040e000400a08018081c000820cee050400c040e000400a040400c1c00058404a050400c040e1000020090281010030103800100400c040e0009050101a01410030103800103a8940aa9018081c00
|40=>0x18081c00080d00a08018081c000811412050400c040e1000250050400c040e000400a08018081c00082c00b27018081c000801410036883800af080141003010380041080240a5b0400c040e000145a08018081c00120400a08018081c008e8424c050400c040e0004012050400c040e0007c20050413806020700020050400c040e738404a5b0400c040e000400a08
|41=>0x400a5b0400c040e000400a08018081c00578400a08018081c00120400a08018081c00083a00a08018081c00290400a04040e406020700020053382006020700020250482006020700020250280c040e002bc20050422c0602070002005040e406020700020750282007290700020250481410030103800100282006d10700021280296c10030103800101a0240a08
|42=>0x50400c040e000400a08018081c00080f40a081c80c040e000400aa90400c040e000404a050400c040e0004068050400c040e0004012050400c040e000400a08018081c00081140a040400c040e000400a08018081c00081d40a08018081c20
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x60602d30151809cc0486021300f1806cc030601530091803cc018600930031800cc0006
|6,0=>0x10e30855c41ce2077100387e5c3e4e1eb70f238775c3ace1cf70e438705c374e1b370d6b0699c33ee19870c93062dc308e17d70bb385bdc2d0e16170ad3854dc298e145709f384ddc260e12970913846dc228e10d7083383fdc1f0e0f170753838dc1b8e0d570673831dc180e0b97059b02b1c14ae09e704bb8241c112e082703db81d1c0dae0667
|6,1=>0x25a7129b8931c48ae23e711bb88c1c452e2227
|7,0=>0x223410fa086d042e82134107a082d040e820340ffa07ed03ef71f3c0f81c7b2e3d271e5b8f0e077703b381d638e99873d039771c7c0e21c701037881b8b8da606c3035981a8c0d29c685033a819940caa0645031a818a30c35c60b02fd817ac0bb605cb02dd816ac0b36058b02bd815ac0ab6054ce29e814b40a3a050d027e813c309c204d102617
|7,1=>0x31a418b20c49061d730ac18360c0ce5fe82fbb97be0bcf05e072ec417420b9105c082dc416c20b52e5a182ccc16460b13058272bd415ca0ad6e56382adc1551ca990545729f394da0a5ee527828fc145e0a1f0507827fc13de09df04e7827039365c9a304c98260c12e6096304a98250c12660924e48a8241b91ee08e8e46c82324117208acc44e8
|7,2=>0x40141fea0fe507ea83f141f6dcfa707cc73e2b9ef9cf6d07ae83d431e820f31079083c441e020ef1077173b4c1d860eb3075363a5c1d0e0e78e734839641c920e390714838641c120df906f4837641b920dbae6d67367b9b1e0d7f06b78357c1a9e0d3f0698734841a25cd0306798339399aa0cc5065a8329b9931cc89063c8
|8,0=>0x504c280613f309f094f44277e53b0e9d174e44a6fe536f09af84d34a67a132d098d94c33a60192f2e97274b4ca58612b3095274a5ba50e1277093474964248e523529128484ca40611f128f17474c2389d1b508d194653a306517308b09453ca27a512b288c9442421f5d0e9286b94323a16e50a8e84b9422b20f61069282b9411c206a5026e80a9
|8,1=>0x6084b02218010bf795f74af9a17beebd695e7baf1a577b2bb675d742e96573b0b9495c6bae19d6feeb7785b7c2da1d6c10b5885a8bad2616830b3985984aca2163f2b178587c2c1e15fd2af68577bab9a55bd0ad6856742b1a157b2ab4955642a95d5392a9395454aa0dd4f70a729534ca98614b12a508524428fe546f0a307514ba8861434ea119
|8,2=>0x70fbb85e1c1d2e0686ff437dddbdf0de786efc375a5b9b2dc676df436da1b5b2da586ce4b64e5b152d8376bdc35d1dad90d6396adc354e1a952d41969cc34c25a52ed21868c4b43e5a0f0cfe967b433ba19cd0cde866acb332598aecbd865ac32b6194cec9d964b3b236590b0c7c9639cb1aa58c6ec5b86294b12658830c398618c30a61844ec199
|8,3=>0x8123c06e6025300b78023bff5dfecefed97f24bf721fa72fcb87e1c3eee1f670faa97d0cbe661f212f8797bfc3dda5edeef6697af43d565e9b0f46779ecbcd9de5eef28779043c65de24ef0b77823bbf5ddeb0eec9771cbb6a5da32ec987604bae21d62eea8975043a621d210e8977404b9e5dce30e6987304b95e5c9d2e46871fbb8de1c5d2e268
|8,4=>0x10707834bc18260b1104f98234c0f66069302b9
|9,0=>0x93cc49c624d31261892cc494624931241891cc48c624531221890cc48462413120098fc447c223cf31df88ebc473e238f11bf88db4c6ba234d119e88cacc636230b117c98ba445b222c9115c88aa4452e6287113a9899444ade245311a88894442de20710fb8879c43aa61c330d98868c4326218310b988584c29e613f10978847c421e20ff10778
|9,1=>0xa424d1ee68e5346a8a314516a28a6f44b8a21c50ee2865342a8a11450666823140a7a0144fea27e513e999f04cf65e7a4f3ca89e144eea276513aa89d0cce626721138799bfc4dde26df136699afbcd5e269f1347899fc4cda665ef326998f44c5a261d1307797fc4bda65db32e5896f3cb56659932c3995dc4aca655332a0994cbca426512f2818
|9,2=>0x29ad14cd9a62c52f6296b14ad8a524d275e929348d7
|10,0=>0x2a8d153e8a9b454ba2a4d151e8a8b4543a2a0d14fe8a7b453ba29cd14de8
|11,0=>0x154e7
|_,_=>0
def wAt:=mkWire dB 298 128 0xffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 9 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x40411284002821070a91484004041040a1040410108d1284002821010f9048fb070f5028400284104041010a914840040a10280f0200b028010280d04041140410708d12840028210708d0284112840028210f0010280d0286c0404101841070b9168400409112041040410708d128400282104041070a914840040a10280f040410108d128400282110839028800284100041048210f0390286c0284101841
|1=>0x414d29041028e70180116810040910280304041010a914840040a1028030200b040411b8030480d028410900c028011284002821028410708d12840028210200b01841040410004101915040421a0000280d04041108390288002841000410708d040411284002821040410108d1284002821028010191d029180011504042028410708d1284002821010b9168400404104091028410708d12840028210708d
|2=>0x4041040410007b0286c018410404104149028e701801018b9168400409102803040412e80f2d801028430900c0280302801040410482102880028410004102843028410200b040410280d000790286c018412d00b020e501801040410415d048a30280f02841120411284002821040410288002841000411684004091120410200b0286c040410184104041128400282102812040411a000040411284002821
|3=>0x280f0200b04041019c30901202801040410900c000911204102803370001a0110280d04041070a914840040a10280f3580b040e1140413583b040e1140413400c338010291704042040410108d12840028210108d12840028213280b04191140420280f028800284100041071890292c0191504042040410900f02801028210200b040411a0000280d0487b0286c02841018410200b0280104041028410200b
|4=>0x40413400f338010291704042040410900c02801000411286c0284102821018410280d0292c01915040423b80f028e50000d040410200b0404100041040410708502880000410708d0404112840028210708d0280312840028213a00b041d502842128401684002803040420900c028010280d0286c04041018410404112840028210900f041d502801028421484004041040a1018bb168400409102803018a1
|5=>0x286c0284101841000b9168400409102803090570900c0280101219020a20280f040412c00f0480104821028414200b0420d120421404114843040a10280f3a00b041d5028421404112843028210280f2c00f0904102801040413f03b0901102801040410f0090286c02841018410900c028010282102841028411284002821128410900f0280102821018920200b04041028010280d0000d040410900c0200b
|6=>0x2841000410191f02918001150404202a520187d04823028411c8410200b04041028212c00c04801028410e80b04821028410e83b02811040410411d0291800115040420280d02801040420180129115028e7040421208d12840028214700f0911502801040420200b028010280d040410200b0900f02801040410423529042028e70180102915040420900c12a2f0282102810040410e843048210284104079
|7=>0x4c0001a1150280d040420900f028011284002821019c1090120280104041168430409102803028410200b0900f0280104041001890292c01915040420e80b04821028410e83b048210284116840040910280304041010a914840040a10280f0200b028010900c028210280104041028010280f0200b040413a00b041d502842028410188d12840028214c00002915040423700b1a0110280d040411083902880
|8=>0x4821028410e83b048210284112841028210900c028012f84004149028e701801048870288002841000410708d1284002821028430e80b0482102841028430e83b0482102841028410280d128403580b020a10280f040413583b020a10280f040413f00f09011028010404114151028120280f04041070a914840040a10280f041d5028420900c0280112843028210900c0900c12842028210108d1284002821
|9=>0x28411284002821028410708d12840028210111d0291800115040420108d1284002821028410900f02801010f9070f502840028412c00c0480104821028410200b1a0030280d040410404101885028800004104041408002d80d02843040412c00c02881000410900c028010200b040410488f028411284002821108390288002841000410e80b04821028410e80b04821028410128d0901302801040410e83b
|10=>0x2803040415a00f02aa5040010280d1284002821028110180104041012c902aa704001000410482102841012c15784002823040ad1204102803070f5028400284116843040910280309043028010404101891028030404256041128030282116842040915484004001000410200b0280d040410708d12840028210284112840028211284002821028410280f028030200b04041048fb070f502840028410488f
|11=>0x292e01915040421a0400280d0184102821020030404104823028410482302841000412c02302881000410e803048210284102af702003040410288204041000410286c0280d01841029c91284202821002eb1a0420280d028211a0000280d048230480302841042e1120400280302812040414580102810040410480f048210284102812028010404104823028430284102915040420280f0280d0404102093
|12=>0x4041020a30280f040410900c028010004101b290904202801040410188200041000a10280f040411684204091028030031d02813040410280104042018010286e0284101841628211a0430280d02821028030404101ae31204002803048f70284002841090570900c028010e80b04821028410404102841018410901202801040410188d12840028210708502880000410e83b04821028410007d0482302841
|13=>0x1284202821028e701801040412c00f0288100041012bd0282302841040910280302841040410900c028013980312843028210280f0280d040421c91504042018010911702801040420280f12840028210286c02841018412d9d50284202843072c157840028231a1150280d0404201801028010280d140410280f04041020e50180104041040a10280f04041018010200b040410280f0200b0404101af502003
|14=>0x286f0184104b560400d02841043011a0400280d040412d80d02843019c912842028210288304041000411288002821000411a0230280d018411a0130280d0404102812040410900f028010284201ae112040028030280d0000d04041048a30280f028410288f1284002821141150280f0404204b540400d02841041d50280302842128430282102803018a1140410280f042e31204002803040e2140410280f
|15=>0x28e704042018017504102b540400d003a10184202841040420900c02801002c15784002823042d90480f02841048210280302841072e11204002803028430282102841028010280d040410900f02801040410420d120420280302841012bd028230108d128400282102aa4028210400101951028120404133801029170404201b875484204001258030191504042028411284002821010f9070f50284004379
|16=>0x28211c84101801040410284112840028210280d028210284102bd50406e018410482302803028410480d0282102841018011284002821012e11204002803040ae1204102803048930280302841090410280104041028410282100041048f7028400284101bc10408200041043b91c842018010908002801000410200b018010404114840040a10280f02af502003040411220d1204202803040a1140410280f
|17=>0x280d040410404104091028030007d0482302841029180011504042028010280d040420008d12840028210900f02801040420288004041000410280f028010404102aa154840040012c0230480102841020900280304041028030200b0404129042028e7018010420d120420280302821140410280f048010482102841003e16a8420400d0901102801040410424a0188100041020a10280f040410708d12840
|18=>0x282102841141170280f040422c00f0480102841018f5028400284104149028e70180102a0d1204202803042ee028820004112041028030280f028410408502880000416c0411a0230280d7f84209023028010291504042042e91a0420280d029150280d040420404102801000410900f0280104041048f702840028410900f02801028410286c02841018410e80b0482102841028410e83b04821028411a010
|19=>0x900c0280102841028210180104105048030284101ac357840028230282104803028410e80f0482102841042e11204002803020e70180104041040411284002821028210280d040415a00c02aa504001000410200b04041141d50280f028420284102915040420900f02801040422a80f0291504042010850288000041028430200b040410280f0280104042040790286c018410131d02813040410900f02801
|20=>0x40a10280f0407b0286c01841028110280d0404129041028e7018011a0030280d04041020920280304041003b91c8420180102915040428880b0408100041018850288000041408032d80d02843040410900c02801578420282302843018870288000041042c15784002823408002d80d028432c00c0288100041168400409102803041d50280d02842128430280d02821121150280304042128420282102842
|21=>0x28030900c02801040420280f02803128420282101801070f502840028410282102810040410008f12840028213a00b041d5028420184104041000410282101801040410e84304821028411a0030280d040420011502801040420280d0200b04041028210281004041028410900c02801028e50180104041040410280f02803040420900c02801048230280d02841040ad1204102803028410200b0404114843
|22=>0x1c6300042000910280302915040422d80d0284304001028410400d000410288300041018f502840040e50180112040028030406d01841028210280f02801028210280d0000d0400d040010400d0184109023028011a0000280d02aa704001048f7028400284102843012bd028230284304821028412c00c0480102841040410480302841028e50404201801028430404102841041d501801028421284302821
|23=>0x43a101842028230284302803040410288000041028010280f02821018016a8420400d02813040410200304041028210404104843028411204102803040f50284002ba301842000420184102803028426a8030400d01881000411280f0282101c610004254840040011a0420280d028810004102aa504001018010284109040028010404201801028010280d0900f028010480302841019d5028425484304001
|24=>0x40a10280f02840028410200b040412d84102843048010284101841000410482302841018f70284004041000410282302841140420280f0482102841040820004102843040410280302841070f5028400280304042000f5028401204102803000420284157841028230408200041041d502842128430282102aa40400157842028231284202821002bd028231a0430280d02b560400d02801000410900f02801
|25=>0x4823028410189102803003a10184202821028430286e0184101841000410280d0404104821028410284202843040f502840128400282101915040421204202803028e5018010200b04041028210004104041028410280f028030280d02842028210400102842000411c8420180102821028430284002841028420284302812040411a0030280d0006e0184102841000410900c0280102843028410282302841
|26=>0x28400180104001028210280d028410404204041028420004102843028230280301842028e701801018010404102917040420282102841028230282102810040410180102842010f5028400282102841012bd028232d821028430280d028410280d0404202841000412d821028435784002823040f702840012bd028230480302841028430284104091028031280f0282102c6100042
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x9aa000000000000928115020a000007a80000000000000000e500000354060a00000000000056a09d00000000000008d00000000000000000fa00000000000000000000000000000001a500000000000000000000000000016402480000000000001aa00000000094000000000000054000a00000000000
|6,1=>0x16940000564000000002920000
|7,0=>0x232646048b8913421e8430c84200000000414c00010141fa83e507aa0f141da83a8c73980001c6837d06e18d841aa6345066a0c9418a8308c5f98bb416e82cd057a0ab414e800000000a3413e826d0000000012e8250c48208d300002250431883310061f103c2075300001c8c37986b40ce8000031a05f4
|7,1=>0x3a887410e699c940000718ce12000037c800000001ba436c86cccd7a1ac300006a4cd2a00003428678ccd9997432680000c7a18b431066110c0997d42f285d8cb9216e42d66000000000002ce8590cb0215c42b085510a8214d300005250000146328484fcc9da13742668000097a12b42506491090211c4
|7,2=>0x51e6a30c000289350a8a05000027d44f289d51391a6f34d6899d131a25f4000096d12ba253449e8000000024b44906914d20a23e347668dd119a000000008bd1161a2844488884d0ea219442a8845106a209440c680cd0019fc43f087d10f821ec43d080000f299e233bc87690ec10000
|8,0=>0x6966d20da29b42367e6cf0d9c9b3636666cc0d969b2a364e6c90d909b1e36366c60d8a9b12361e6c30d849b0636066c00d7e9afa35ee6bd49791aef35d86ba4d731ae335c06b74d6d1ad735a86b489679acc35926b18d6212c1357c6aecd5c1ab535646abcd561aa9354c6a8cd501a9d35346a6094a9a923
|8,1=>0x8127018e019c0037fa6fe8dfb9bf437e26fb8df59be837ca6f88def9bdc37b26f58de99bd0379a6f28de39bc437826ef8ddd9bb8376a6ec8dd79bac37526e98dd213a1373c6e6cdcc1b9537246e3cdc61b89370c6e0cdc01b7e26f66de0dba9b7236de6db0db49b6636c66d80dae9b5a36ae6d50da89b4e3
|8,2=>0x98472fce5f0cbb397072d4e591caf395872a8a5414a53944727ce4e949a392e7250e489c8e39167220e429c84190271f8e3d9c7838ea71c8e379c6c38d27198e319c6038ba7168e2b9c5438a27138e259c48388a7108e1f9c3c387270d8e199c30385a70a8e139c2438427078e0d9c18382a7048e079c0c3
|8,3=>0xafa75e8ebb9d743ae275b8eb59d683aca7588eaf9d5c3ab27558ea99d503a9a7528ea39d443a8274f8e9d9d383a6a74c8e979d2c3a54549ce921d213a3c746ce8c1d153a24743ce861d093a0c740ce8094fe39f673e0e7a9cf239de73b0e749ce639c67380e6e9cda39b2335ca6a1cd1399c732ce641cc53
|8,4=>0x5973b287644ec71d8b3b107614ec11d802
|9,0=>0xc305858b0a16122c205838b06160a2c105818b0216022c0057f8afe15fa2bf057d8afa15f22be057b8af615ea2bd05798af215e22bc05778aee15da2bb05758aea15d22ba05738ae615ca2b905718ae215c22b8056f8ade15ba2b7056d8ada15b22b6056b8ad615aa2b505698ad215a22b405678ace159a2
|9,1=>0xd305a58b4a16922d205a38b46168a2d105a18b4216822d0059f8b3e167a2cf059d8b3a16722ce059b8b36166a2cd05998b3216622cc05978b2e165a2cb05958b2a16522ca05938b26164a2c905918b2216422c8058f8b1e163a2c7058d8b1a16322c6058b8b16162a2c505898b1216222c405878b0e161a2
|9,2=>0x35616aa2d505a98b5216a22d405a78b4e169a2
|10,0=>0x35d8eba1d723ae075b8eb61d6a3ad07598eb21d623ac07578eae1
|_,_=>0
def PO:=mkPO wAt oP oO 20 9 511 15
def pmP:Nat→Nat
|0=>0x10a000000001080000000010600000000102000000000cb0000000008e000000000880000000008100000000060000000000590000000004f0000000004e0000000004d000000000460000000004300000000042000000000410000000004000000000038000000000290000000001a0000000000d0000000000c0000000000b0000000000900000000008000000000060000000000400000000003000000000020000000000100000000000
|1=>0x1002000000010010000000100000000000f090000000074f00000000644000000005ef0000000050f0000000050e000000005060000000048c0000000046f0000000040e0000000040d0000000040c000000004060000000040400000000401000000003020000000030000000000282000000002490000000024700000000241000000002400000000020400000000200000000001cf0000000014f00000000143000000001220000000010b
|2=>0x404f0000000404b000000040450000000400e0000000400400000004003000000040020000000174f0000000154f000000015060000000146f0000000144f000000014440000000140d000000014050000000134f0000000126f0000000124f0000000124000000001201000000011cf0000000114f00000001101000000010860000000106f0000000104f000000010400000000102f0000000101c0000000100d0000000100500000001004
|3=>0x201cf000000200040000001824f00000015f4f0000001574f0000001514f00000010f4f0000001074f000000071510000000576f0000000574f0000000564f0000000554f000000055490000000534f0000000524f0000000516f0000000516d0000000514f0000000504f0000000504b0000000476f0000000474f0000000466f0000000456f0000000454f0000000440c00000004406000000044020000000436f0000000434f0000000424f
|4=>0x200102000002000c6000002000c4000002000400000020000e0000018106f0000018104f0000008574f0000008514f0000006124f0000006066f0000004574f00000044143000000411cf000000406000000004024b000000400cf00000021649000000215ef000000215cf0000002154f0000002124f000000211cf0000002114f000000205ef000000205cf0000002056f0000002054f0000002052f0000002046f0000002030f0000002026f
|5=>0x400015cf000400011cf0004000114f000400005cf000400000460002000124a000100000080000801d34f0000800d24f0000700107f0000700105f0000300005f00000801c4500000400008000002450cf000002441cf0000024014f000002400cf0000020514f0000020404f0000020134f000002011cf0000020114f00000201102000002005cf0000020040e0000020016f0000020014f0000020012b0000020012a0000020010a00000200106
|6=>0x8002024d0008000574f000800053cf0008000534f0008000534d0008000474f0008000154f000800011cf00080001086000800010840008000104f0008000066f00080000644000800005ef0008000046f00080000444000800002680008000008e0008000008c000402041cf0004008504f0004004010f000400215cf000400211cf0004001504f0004000544f000400051cf0004000514f0004000504f0004000444f0004000424f000400040cf
|7=>0x14000164f0014000110f0014000104f001400010440014000014f0014000004e0014000004c001400000460014000000e0010026154f0010022016f0010006164f0010006066f0010004534f0010004514d0010004124f001000412490010000124f0010000114f000c024104f000c00047cf000c00011cf000802001cf0008006124f0008004574f0008004534f0008004124f000800410460008004024f0008004004e0008002154f0008002114f
|8=>0x5400605cf005400201cf0050004124f0048004164f0048000164f0040002126f0040002124f0040000574f004000054440040000454f00400001640004000006480040000060c0040000004e004000000090030004124f0028000104f0020000164f0020000120d001c004034f0018020514f0018006024f0014006154f001400611cf0014004424f0014004104f001400403cf001400401cf0014002174f0014000510f0014000410f0014000174f
|9=>0x200000144f0100010574f0100000534f0100000474f00a0000166f0088006126f0088000106f008800001df008400211ef0080140144f0080100144f0080020116f0080020002e0080000576f0080000574f0080000570d0080000564f0080000540d0080000536f0080000526f0080000154f0080000146f0080000144f0080000141f0080000108c0080000106f0080000100d0080000064c0080000056f0080000010f0080000006c0080000000b
|10=>0x800000215cf800000205cf800000054028000000534f8000000466b8000000400a8000000050c800000000004200000104741000005b5f205400617cf2040004164f2040004064f2040000024f201400405ef200002001cf2000000114f1000004124f1000000514f10000000240100000000400904000414f0680000146f060002010470600000144f0600000104f060000010470300010534f0300000574f0300000474f0200000184f02000001847
|11=>0xa00000047cfa00000015cf8804000114f800400045ef800400005ef8004000014f
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x1800020000004000c000000001008040007000000000038000e1e0000000060400000000380000000001c00000000000000000009000000000000000002010000000068000002000000004050000000
|7,0=>0xf840050d0009c02005b8000001130080a0e000387c004f00804010800002060e1081c72248100207010000000170385c095c9dc3a020001c00020a008020914801de09070256c3f07094585b048080c000003800010786cbc01218381c0035a680401022e83c091127004090c930120905000003e760040000030b4162b002cc1c270101c020e0003808235a0002090
|7,1=>0x10080002081e0000a5a8f804043c880200900024121120000007d010080202010811e00001641c3e1f1f802b2008588a060e0701c0340804c609140001c0e221047a00
|8,0=>0x789fd8c53241d600d7368e810c798051fc33a2266b71a3891a0c713e19aa51b89a28628c783513f0261a6e9a7125550675d499b0a6020d2f67a6467210ba926ab6cea693d3c15c651c9ba91218f05c96bd893dc9c624ea3a395a360ed9547922fa32b89b2169cf041a7cacbc0ece06ef228138c0366183ab91110946981327d81bea3a54892e323c1a06afc3f8097d21
|8,1=>0x2f849507b96b5682fa51149c8bea29d8dacd0a12a2b20a014ce22a58b89844b4fd8e16c4251b4da6f38128e1141d0fc4e6d50218d81d4030c964767892ae7348d2df88aab5017718a1c05226d769d55874458bcb67568c3c4eee26c9df23b811867f589ace4b8366c3e110fe940529e3661d155b2f8b8e1fabc53c8d6aa62334d0430682ad96742d0c51a757a9298b33
|8,2=>0x759f49495596b4b9429f
|9,0=>0x3ab71d0c83b1c4e33c641c584f3459520eff9925a113a949d4ea46881d1d34946ca8bee743b2495312c1d64d0c8423046759899ceb463ab82065539cae6273952fe64703d9c0ea70709d51b2a2ad94e24675b96a6be82ceceb2c6eb314aee994dcaa75619d9bcf63a47d549584d3ddceab0aa5b2a9823ed12f4b215d80467357eaac54a541871d8b3695f5178349c762
|9,1=>0x1613438954d52d54a60eb42
|10,0=>0xeaa4af0d2144623498a8c8389a5830e
|11,0=>0x15
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 44 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_125 10 roots_125 ops++addP pm 1 dom_126 9 roots_126 ops++addP pm 2 dom_111 9 roots_111 ops++addP pm 3 dom_123 10 roots_123 ops++addP pm 4 dzo_43_4 5 roots_43 ops++addP pm 5 dzo_111_16 7 roots_111 ops++addP pm 6 dom_119 9 roots_119 ops++addP pm 7 dzo_126_1 7 roots_126 ops++addP pm 8 dzo_94_1 6 roots_94 ops++addP pm 9 dzo_87_8 6 roots_87 ops++addP pm 10 dzo_47_16 6 roots_47 ops++addP pm 11 dzo_59_4 6 roots_59 ops++addP pm 12 dom_63 8 roots_63 ops++addP pm 13 dom_115 7 roots_115 ops++addP pm 14 dom_95 7 roots_95 ops++addP pm 15 dzo_92_1 5 roots_92 ops++addP pm 16 dom_93 6 roots_93 ops++addP pm 17 dzo_86_1 5 roots_86 ops++addP pm 18 dzo_119_8 7 roots_119 ops++addP pm 19 dom_59 7 roots_59 ops++addP pm 20 dom_107 8 roots_107 ops++addP pm 21 dom_118 7 roots_118 ops++addP pm 22 dzo_109_16 6 roots_109 ops++addP pm 23 dzo_43_16 5 roots_43 ops++addP pm 24 dzo_45_16 5 roots_45 ops++addP pm 25 dom_61 6 roots_61 ops++addP pm 26 dom_109 7 roots_109 ops++addP pm 27 dom_124 7 roots_124 ops++addP pm 28 dzo_124_1 6 roots_124 ops++addP pm 29 dzo_85_8 5 roots_85 ops++addP pm 30 dzo_118_1 6 roots_118 ops++addP pm 31 dom_86 5 roots_86 ops++addP pm 32 dzo_118_8 6 roots_118 ops++addP pm 33 dzo_86_8 5 roots_86 ops++addP pm 34 dom_103 6 roots_103 ops++addP pm 35 dom_43 5 roots_43 ops++addP pm 36 dom_91 6 roots_91 ops++addP pm 37 dzo_107_4 6 roots_107 ops++addP pm 38 dzo_107_16 6 roots_107 ops++addP pm 39 dzo_122_1 6 roots_122 ops++addP pm 40 dom_55 5 roots_55 ops++addP pm 41 dom_102 5 roots_102 ops++addP pm 42 dom_122 7 roots_122 ops++addP pm 43 dom_110 6 roots_110 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_127 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_zo_43_4_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_zo_111_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_126_1_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_94_1_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_87_8_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_47_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_59_4_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_92_1_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_86_1_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_119_8_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_zo_109_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_zo_43_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_zo_45_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_zo_124_1_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_zo_85_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_zo_118_1_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_zo_118_8_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_zo_86_8_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_zo_107_4_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_zo_107_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_zo_122_1_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_110 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_125 10 s (0,roots_125.map (·&&&dom_125)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_127 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_125 h
def symsG:List (List (Nat×Nat)):=[[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_127==dom_127)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_127 gM v ys):RunD true dom_127 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_127 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 17 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 17 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 73 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 73 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 188 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 60 128 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 188 → Z 7 i = true := (range_split z7_0 z7_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 256 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_256 : ∀ i, 256 ≤ i → i < 265 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 9 256 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 265 → Z 8 i = true := (range_split z8_0 (range_split z8_128 z8_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_0 : ∀ i, 0 ≤ i → i < 128 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_128 : ∀ i, 128 ≤ i → i < 138 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 10 128 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 138 → Z 9 i = true := (range_split z9_0 z9_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 14 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 14 0 = true)
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
theorem lowS_191:Lower true dom_191 roots_191 goal_191 11:=lower_slice_b [(0xcccccccccccccccc0000000000000000cccccccccccccccc,16,18)] (by decide +kernel) lowS_189
theorem lowS_223:Lower true dom_223 roots_223 goal_223 11:=lower_slice_b [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,16,18)] (by decide +kernel) lowS_221
theorem lowS_239:Lower true dom_239 roots_239 goal_239 11:=lower_slice_b [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,32,34)] (by decide +kernel) lowS_237
def dzo_215_32:=0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000
def gzo_215_32:=0xff00ff0000000000ff00fe0000000000ff00ff0000000000fe00ee00000000
def gsh_215_32:=0xff00ff0000000000ff00fe0000000000ff00ff0000000000fe00ee
theorem lowS_zo_215_32_148:Lower true dzo_215_32 roots_215 gzo_215_32 7:=lower_iso_b (d1:=dom_215) (r1:=roots_215) (T1:=gsh_215_32) [(dom_215,32)] (by decide +kernel) (lower_slice_b (T:=gsh_215_32) [(0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa,0,1),(0xcc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc,0,2),(0xff00ff00000000000000000000000000ff00ff0000000000000000,0,64)] (by decide +kernel) lowS_148)
def dzo_212_32:=0x11001100000000001100110000000000110011000000000011001100000000
def gzo_212_32:=0x11001100000000001100100000000000110011000000000010000000000000
def gsh_212_32:=0x110011000000000011001000000000001100110000000000100000
theorem lowS_zo_212_32_148:Lower true dzo_212_32 roots_212 gzo_212_32 5:=lower_iso_b (d1:=dom_212) (r1:=roots_212) (T1:=gsh_212_32) [(dom_212,32)] (by decide +kernel) (lower_slice_b (T:=gsh_212_32) [(0x110011000000000000000000000000001100110000000000000000,0,64)] (by decide +kernel) lowS_148)
def dzo_150_32:=0x5500550000000000000000000000000055005500000000
def gzo_150_32:=0x5500540000000000000000000000000054004400000000
def gsh_150_32:=0x55005400000000000000000000000000540044
theorem lowS_zo_150_32_148:Lower true dzo_150_32 roots_150 gzo_150_32 5:=lower_iso_b (d1:=dom_150) (r1:=roots_150) (T1:=gsh_150_32) [(dom_150,32)] (by decide +kernel) (lower_slice_b (T:=gsh_150_32) [(0x44004400000000000000000000000000440044,0,2)] (by decide +kernel) lowS_148)
def dzo_149_32:=0x3300330000000000000000000000000033003300000000
def gzo_149_32:=0x3300320000000000000000000000000032002200000000
def gsh_149_32:=0x33003200000000000000000000000000320022
theorem lowS_zo_149_32_148:Lower true dzo_149_32 roots_149 gzo_149_32 5:=lower_iso_b (d1:=dom_149) (r1:=roots_149) (T1:=gsh_149_32) [(dom_149,32)] (by decide +kernel) (lower_slice_b (T:=gsh_149_32) [(0x22002200000000000000000000000000220022,0,1)] (by decide +kernel) lowS_148)
def dzo_214_1:=0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa
def gzo_214_1:=0xaa00aa0000000000aa00aa0000000000aa00a80000000000a80000
def gsh_214_1:=0x550055000000000055005500000000005500540000000000540000
theorem lowS_zo_214_1_86:Lower true dzo_214_1 roots_214 gzo_214_1 6:=lower_iso_b (d1:=dom_214) (r1:=roots_214) (T1:=gsh_214_1) [(dom_214,1)] (by decide +kernel) (lower_slice_b (T:=gsh_214_1) [(0x550055000000000055005500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_86)
def dzo_246_1:=0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa
def gzo_246_1:=0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00a800aa00aa00a80000
def gsh_246_1:=0x55005500550055005500550055005500550055005500540055005500540000
theorem lowS_zo_246_1_86:Lower true dzo_246_1 roots_246 gzo_246_1 7:=lower_iso_b (d1:=dom_246) (r1:=roots_246) (T1:=gsh_246_1) [(dom_246,1)] (by decide +kernel) (lower_slice_b (T:=gsh_246_1) [(0x55005500000000005500550000000000550055000000000055005500000000,0,32),(0x55005500550055005500550055005500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_86)
namespace S_247
def pG:List (Nat×Nat):=[(1,33),(1,129),(2,18),(2,34),(2,66),(2,130),(3,19),(3,35),(3,67),(3,131),(4,20),(4,68),(4,132),(5,21),(5,37),(5,69),(5,133),(6,22),(6,38),(6,70),(6,134),(7,23),(7,39),(7,71),(7,135),(16,18),(16,20),(16,80),(16,144),(17,19),(17,21),(17,49),(17,81),(17,145),(32,33),(32,34),(32,96),(36,37),(36,38),(36,52),(36,100),(36,164),(48,49),(48,50),(48,52),(48,112),(48,176),(64,66),(64,68),(64,80),(64,96),(65,67),(65,69),(65,81),(65,97),(65,193),(128,129),(128,130),(128,132),(128,144),(160,161),(160,162),(160,164),(160,176),(160,224),(192,193),(192,194),(192,196),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffffffffffff
def xsM:=roots_247.map (·&&&dom_247)
def gM:=goal_247&&&dom_247
def NN:Nat→Nat
|5=>9
|6=>46
|7=>239
|8=>260
|9=>121
|10=>14
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0xb447da5ec4a179f8caac6534756c3e33bb21201f00156
|6,0=>0xffeadfc653f9d51f812ff3079eac30e1c5adec5cdea9ddd003d5d00ce551cc063c560cc542dc3a77bf743bc7d3b5bdfa2148a15119c1ba9a7bd991ce91da88e7108e3c9880fd8523781d36784ef73d20675cc6428d506f74e5a047b2943b2a3e3fd32f372f4e31e98a1bbc90f7590557501f42
|7,0=>0x86a528623185f7785bdb855cf840e98338e830e18203980eaa7ea627e1a87dd777da167d3f47ba9679d2177f0376f2c76051754c07487772422721a7719ab715f2709b8705366eb136dc196cdec6c6256ae2b6a05968b81687e1685ad676cd664e5642ca606545f5955eeef5e85f5ba775ad8f5aaa85a6785a64f5a5df5a2b358996582295620f55908544e252c055271d51ebf5024c502074dce048d2048bea477864737146ec64544744dbb43b82418873f3d23f30c3e7313e4223e23e3979036aca3615635f2e3435b3249431b4e317d72fa942f8482f2ea2ed162de602d7e22cbfd2c7f02a18529f862877c286622620723c3b237ac235992110720d89208991f4841ad141983b18a341825a162eb15fbc15a76142c513a5412dbf11f28111370ba480a6180a2cd0a22c07775068f10639c062fd05ac70561e045a303cc7
|7,1=>0xff9a1fecfafe62efe3e3fcd11fa194f79b6f6bebf6809f47a3f1491ef755eeb62eeaa4ee864ed2eaeb970eb41ceaae6ea35cea134e8579e81afe795de786ae4edee4a71e3c40e2b20e1e3dde9c1dd54adb4b7da908d996ad9542d7c90d78e5d77ddd61cfd5a08d48afd4497d3990d370dd1768cf824cde2ccd920cd79acbe65cb2adc9a1bc7d55c5fdec4e5bc40f8c40adc0175c0048bef4cbe805bc51bbb149b8fc0b844bb7e24b78e3b6515b5e81b36d1b2f4bb2bc1adb44ad0e5aaa57aa678aa317a8e94a49a5a3e17a347fa2a779c9a29bf719ac469aa2a9a7349a61798cd89865f95f1f95cda94c5f9402a92c639274f8fb398e6138e53d8c7948bdf88b3d08aebd8acf789ac4887bc8859e880ae8804d877b5
|8,0=>0x7384a7359971fa3717b671181700c56f4c96e51b6df7c6d6506c8b86ab4468ded6725c65ae16512b650b86362f630a461e096179e61395607375fc3d5f9ba5f2315dc015c7425c2435ba225b4135b3cc598da587de58119568d5566f355b045580253f3751aa850a874f0d44eec14cf9d4b0a84a8d949c6147a42475f546f284644c45f3e43972429c44294142326419cd41688404db3fd093f0cb3e7b63dac23d6443d5d23d4f03cab53c8fc3c2c83bf8c3b81239ebf39dca3905637f28350c034df534d86345ec31cdb30f862fecb2fe402fcab2ed802e0de2ceb62c7802a99d2a24f286b0270582288b223002146c20c961fbff1f85f1e18f1c5e11b75d1a62b19b33193fc18bf018b361788b168d71653715b3113f22134840fabc0cf400cf3c0c9860c1140b56009e5c094330914308da308a03061840503904fd6001d7
|8,1=>0xf82b2f7fc0f7879f638af5ecaf5e70f5e27f4aa4f3fe2f2e0cf0a5df0794ef09cee225edfdceda4bed1d4ecfacebb47eb970eb62feac6be9512e832ce1e3de141ee1004e06c8dfb10dfa1ddf7fadd285dcfaedc582db547daf8fdacb9d7917d69b3d6718d5793d4186d4026d3427d317ed2a56d0438cf993ced18cd550cce06cbd4ac9ab1c8d3ec7fffc71f4c6cc1c5d42c5bbec4ac8c4295c41fdc365bc2ee1c1661c0e5bc095cbb63fba7d8b7cd0b6bf5b6a1fb5461b3d00affebafef6afcb9af571aedd9adae4ad481acca7ab17baa38aa9ec7a95e9a67d3a075e9f5f79e9a59cf029c33b9b8189acbe9a43b9a1eb990ef9840f97f5397f4d94291919a490d4590b298ebef8ddcd8d6158b51189d63887e68859f8800487ab786c15859b28449482cdd82be4808fd7c91b7c5de7bed97a8bc78501771f376f2c7613575e64
|8,2=>0xfa86ffa248f911bf8d8a
|9,0=>0xfe37efb60ff4666f110fed702e9545e9229e4fa2e39e1e2e9fe2731e1a1be031adf8dcdb0c8da888d8de6d8a46d7415d6743d5d6ad4c44d2c18d18a2ccf5dc6b3ac671ac5b6dc53e3c4747c1903bfd54bf61cbd9e8b7fe6b58c7b2322b18edaf571af3ecac1a4a9ef4a8078a63bba6193a5de6a26f99ea7f9d010989e19646c93ea093ab9926ef9159d90afe903338c79a8c05f89f84896fc88237872b485d96848828218f7f9fc7c050785fa7620172a547244b6fc786fc066f2da6e6486acea687556713a608ac5ff145f7495d0ec5be6d5b3205affb55a5c54d1c54c6c53ea54fa5d4e01948c35460d34503340daa403353c4e63b0dd34a6b31eb330b15303da303192fde6273eb231a122bd32288b217f21fe9c197ea1627915a1d0fdb30acbe0ac8f054eb026a702040019af
|10,0=>0xff591f9dd7ba86bb6bdab47c3b412e9ac028064d7fd216aad465042346ae1a57c0428f
|11,0=>0x3ef7d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xff00ff00ff00ff00ff00ff0000000000ff00ff00ff00ff000000000300030003000300030003000300030003003300030003000300330003000003000300030003000300030003000300030003000300030003003300030000ff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00cc00cc00ee00ee00cc00cc0f000f000f000f000f000f000f000f000f000f000f000f000f0000000f0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0ff00cc00ff00cc00ff00cc00ff00cc00ff00ff00ff00cc00cc00cc00cc00ccff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff000000ff0000ff00f000ff00f000ff00f000ff00f000ff00ff00ff00f000f000f000f000f0cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00ccaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aaff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000
|0,1=>0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00ff00000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff000000ff0000ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff0000f000f00000000000f000f00000000000f000f00000000000f000ff00000000000000000f000f00000000000f000f00000000000f000f00000000000f000000000000ff00ff0000000000ff00ff0000000000ff00ff000000ff00ff0000ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff00ff00ff00ff00ff0000ff00ff0000000000ff00000000000000ff00ff0000000000ff000000000000ff00ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff000000ff000000000000ff00ff000000ff00ff00000000000000ff00ff000000ff00ff0000aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa0000f000f0000f000f00f000f0000f000f00f000f0000f000f00f000ff000f0000ff00ee00ff00ee00ff00ee00ff00ee00ff00ee00ff00cc00ff00ee00ff00cc0000fe000000fe000000fe000000fe000000fe000000fc000000fe000000fc00000000000000000000000000000000ff00fe00ff00fc00ff00fe00ff00fcfe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fc00fc00fe00fe00fc00fc
|0,2=>0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa0000000000aa00aa00000000ff000000ff000000ff000000ff000000ff00ff00ff00000000000000000000ff00ff000f000f00ff00ff000f000f00ff00ff000f000f00ff00ff000f00000f000f00000000000f000f00000000000f000f00000000000f00000000000000000000000000000000ff000000ff0000000000ff00ff000000000000000000000000000000000000000000000000ff00ff00ff00ff00ff000000ff00000000ff000000ff000000ff000000ff000000ff000000ff0000000000000000aa00aa000a000a00aa00aa000a000a00aa00aa000a000a00aa00aa000a00000000000000000000ff00ff00000000000000000000000000ff00ff0000000000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff0000ff00ff00ff00ff000000000000000000ff00ff00ff00ff00ff00ff00000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff00000000000000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000ff00ff0000000000ff00ff0000000000ff00ff00ff00ff00000000ff00ff0000000000ff00ff0000000000ff00ff000000000000000000000000
|0,3=>0x55005500550055005500550055005500550055005500550055005500000000550055000500050055005500050005005500550005000500550055000500000000000000000000ff00ff0000000000ff00ff00ff00ff00ff00ff00ff000000000000000000000000ff0000000000ff00ff00ff00ff00ff00ff00ff0000000000000000000000000000000000000f000f000f000f000f0000000f000000000f0000000f0000000f0000000f0000000f0000000f000000000000000000000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff00000f000f000f000f000f000f000f000f000f000f000f000f000f00ff000f0000aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00000000aa00aa00aa00aa00aa00aa00aa00aa00aa00aa0000000000aa00aa000000aa0000000000000000000000000000000000000000ff00ff0000000000ff0000ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00cc00cc00ee00ee00cc00ee5500550055005500550055005500550055005500550055005500550055000000000000ff00ff000000ff00ff00ff0000000000ff00ff0000000000000000ff00fe00ff00fe00ff00fe00ff00fe00ff00fe00ff00fc00ff00fe00ff00fc000000000000000000000000000000000000000000000000ff00ff00000000
|0,4=>0xff000000ff00ff00ff000000ff00ff00ff000000ff00ff0000000000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0000ff000000ff000000ff000000ff000000ff000000ff000000ff00ff00ff00000000000000000000000000000000000000000000000000000000ff00000000ff00ff00ff00ff000000000000000000ff00ff00ff00ff000000ff000000000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000000f000f000f000f000f000f000f000f000f00ff000f000f000f00ff000f00005500550055005500550055005500550055005500550000005500550055000000000000ff00ff0000000000ff00000000000000ff00ff000000ff00ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000ff000000000000000000000000ff000000000000000000000000000000ff00ff000000ff000033003300330033003300330033003300330033003300330033003300330000330033000300030033003300030003003300330003000300330033000300000f000f000f000f000f000f000f000f000f0000000f000f000f0000000f000000000000ff00ff000000ff00ff00ff0000000000ff00ff000000ff00ff0000
|0,5=>0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00aa00aa00aa00aa5500550000005500550055000000550055005500000055005500550000000000000000ff00ff0000000000ff00000000000000ff00ff0000000000ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00aa00ff00aa0f000f000f000f000f000f000f000f000f000f000f000f000f000a000f000aff00ff00ff00ff00ff000000ff000000ff00ff0000000000ff00000000000000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00000000ff000000ff000000ff000000ff000000ff000000ff00ff00ff00000000ff00ff00ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff00000000ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff0000ff00ff00ff00ff00ff000000ff00ff00ff00ff00ff00ff00ff000000ff0000ff00ff00ff00ff000000000000000000ff00ff00ff00ff00ff00ff00ff00000000000000000000ff00ff00ff00ff000000000000000000ff00ff00ff0000000000000000000000000000000000000000ff00000000000000ff00000000ff00ff00ff00ff00ff00ff00ff00ff000000ff00000000000000ff000000000000ff00000000000000ff00000000000000ff00000000000000ff00000000
|0,6=>0xff00ff00ff0000aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00ff00ff00aa00aa00ff00aaf000f000f000f000f000f000f000f000f000f000f000f000f000ff00f000f0ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff00000000ff000000ff000000ff000000ff000000ff000000ff000000ff00ff00000000ff000000ff000000ff000000ff000000ff00ff00ff000000ff00ff00ff0000f000f000f000f000f000f000f000f000f000ff00f000f000f000ff00f000f00000000000000000ff00ff00ff0000000000000000000000ff00ff00ff0000ff00ff0000000000ff00ff0000000000ff00ff00ff00ff00ff00ff00ff0000ff00ff0000000000ff00000000000000ff00ff0000000000ff000000ff0000ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff00000000ff00ff00ff00ff00aa00aa00aa00aa00ff00ff00ff00ff00aa00aa00aa00aaff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff0000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00000000000000000000000000000000ff000000000000000000000000000000ff00000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff0000
|0,7=>0xee00ee00ee00ee00ee00ee00ee00ee00cc00cc00cc00cc00ee00ee00cc00ccff00ff00ff00ff0000000000ff00ff00ff000000ff00000000000000ff000055005500550055005500000055000000550055005500550055000000550000ff00ff00ff00ff00ff00ff00ff00ff00550055005500550055000000550000af00af00af00af00af00af00af00af00af00af00af00af00af00aa00af00aaff00ff00000000000000000000000000ff00ff00000000000000ff000000000000000000000000ff00ff00ff00ff000000000000000000ff000000ff0000ff00ff00f000f000f000f000f000f000ff00ff00f000f000f000ff00f000f0ff00ff0000000000ff00ff0000000000ff00ff0000000000ff000000ff000000000000000000000000000000000000ff00ff00ff000000ff00ff00ff0000aa00aa000000aa00aa00aa000000aa00aa00aa000000aa00aa00aa00000000ff00ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00ff0000000000000000000000ff0000000055005500550055005500550055005500550055005500550000000000000000ff00ff00ff00ff00ff00aa00ff00aa00ff00ff00ff00ff00ff00aa00ff00aa00000000ff00ff000000ff00ff00ff0000000000ff00ff0000000000ff0000
|0,8=>0xff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff0000000000ff000000000000000000000000ff000000ff0000000000000000000000ff00000000ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff000000ff00000000aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa000000aa00aa00aa000055005500550055005500550055005500550055005500550055000000550000ff00ff00ff00ff000000ff0000000000ff00ff00ff00ff000000ff000000000000000000000000ff00ff00000000000000000000000000ff00ff00ff000000000000000000000000000000000000ff000000ff00ff00ff000000ff00005500550000000000550055000000000055005500000000005500550000000000000000ff00ff0000000000ff00ff0000000000ff00ff00ff000000ff0000ff00ff00aa00aa00ff00ff00aa00aa00ff00ff00aa00aa00ff00ff00aa00aaff00ff00ff00ff00ff000000ff00000000000000ff00ff0000000000ff0000000000000000000000000000000000000000ff000000ff000000ff00000000ff000000ff000000ff000000ff000000ff00ff00ff00ff00ff00ff00ff0000aa00aa00aa00aa00aa00aa00aa00aa000000000000000000aa00aa00000000ff00ff00ff00ff00ff00ff00ff00ff000000000000000000ff00ff00000000
|0,9=>0xff000000ff000000ff00ff00ff000000ff000000ff000000ff00ff00ff00000000ff000000ff000000ff000000ff000000ff00000000000000ff00000000ff000000ff000000ff000000ff000000ff000000ff00ff000000000000000000000000ff00aa0000000000ff00aa0000000000ff00aa0000000000ff00aaff00aa00ff00aa00ff00aa00ff00aa00ff00aa00ff00aa00ff00aa00ff00aa55005500ff00aa0055005500ff00aa0055005500ff00aa0055005500ff00aaff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff000000ff00000000ff00000000000000ff00000000000000ff00000000000000ff00ff00000000ff00ff00ff00ff00ff00000000000000ff00ff00ff00ff00ff00ff0000000000000000ff00ff0000000000ff00ff0000000000ff000000ff000000ff00000500050005000500050005000500050005000500050005000500000005000000000000000000000000000000000000ff00ff0000000000ff00ff00000000ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00ff0000000000ff00000000ff000000ff000000ff000000ff00000000000000ff0000000000000000ff00ff0000000000ff00ff000000000000000000000000000000ff00000000ff00ff00ff00ff00ff00ff0000000000ff00ff00ff00ff000000ff00000000
|0,10=>0xff005500ff005500ff005500ff005500ff005500ff005500ff000000ff0000ff005500ff000000ff005500ff000000ff005500ff000000ff005500ff000000000000000000000000000000000000ff005500ff000000ff005500ff0000ff00aa0000000000ff00aa0000000000ff00aa0000000000ff00aa000000000000000000000000ff000000ff0000000000000000000000ff00ff00ff0000000000000000ff00000000000000ff00000000000000ff0000000000000000aa00aa00aa00aa00aa00aa00aa00aa00ff00ff00ff00ff00ff00aa00ff00aaff00ff00ff00ff00ff00ff00ff00ff00ff005500ff000000ff005500ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff00ff00ff0000ff00ff0000000000ff00ff00ff00ff00ff00ff0000000000ff00ff00ff000000005500000055000000550000005500000055000000550000000000000000ff00ff00ff00ff005500550000000000ff00ff00ff00ff0055005500000000ff00ff00ff00ff00ff00ff0000000000ff000000ff000000ff00000000000055005500550055005500550055005500550055000000000055005500000000aa00ff00aa00ff00aa00ff00aa00ff00aa00ff00aa00ff00aa00aa00aa00aa55005500550055005500550055005500000000000000000055005500000000
|0,11=>0xff00ff0000000000ff000000000000ff00ff0000000000ff00ff0000000000ff00000000000000ff000000000000ff00ff00ff00ff00ff00ff0000000000ff00ff00ff00ff00ff000000000000000000000000000000000000ff00ff00000000000000000000000000ff000000000000000000000000000000000000550055000000000055005500000000ff00ff00ff00ff00ff00ff00ff00ff00aa00aa00aa00aa00aa00aa00aa00aaff000000ff000000ff000000ff000000ff005500ff000000ff005500ff000055005500550055005500550055005500550000005500000055000000550000ff00ff00ff00ff005500550055005500ff00ff00ff00ff005500000055000000000000000000000000000000000000ff000000ff000000ff00ff00ff00000000ff000000ff000000ff000000ff000000ff000000ff000000aa000000aa0000ff00000000000000ff00000000000000ff0000000000000000000000000000000000000000000000000000000055005500550055005500000055000000000000000000000000000000000000ff00ff00ff00ff00ff00ff000000000000ff000000ff000000ff00000000000000ff000000ff000000ff0000000000000000ff00ff0000000000ff00ff0000000000ff00000000000000ff0000
|0,12=>0x550055005500000055005500550000005500550055000000550055005500000000000000000000ff00ff00ff00ff000000000000000000ff00ff00000000aa00aa00aa00aa00aa00aa00aa00aa00ff00ff00aa00aa00ff00ff00aa00aaff00ff00ff00ff00ff00ff00ff00ff00ff00aa00ff00aa00ff00aa00ff00aa55005500550055005500550000000000550055005500550055005500000000ff00ff00ff00ff00ff00ff00aa00aa00ff00ff00ff00ff00ff00ff00aa00aaaa00aa00aa00aa00ff00ff00aa00aa00aa00aa00aa00aa00ff00ff00aa00aa0000000000000000ff00ff00aa00aa000000000000000000ff00ff00aa00aaaa00ff00aa00aa00aa00ff00aa00aa00aa00ff00aa00aa00aa00ff00aa00aa0000000000000000ff00aa00ff00aa000000000000000000ff00aa00ff00aa00000000000000005500550000000000000000000000000055005500000000ff00ff00ff00ff00ff00ff00ff00ff0055005500000000005500550000000000000000000000000000000000000000ff00ff00aa00aa00ff00ff00aa00aa00005500000000000000550000000000000055000000000000005500000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00aa00aa00ff00ff00aa00aa00000000000000000000000000000000ff00aa00ff00aa00ff00aa00ff00aa
|0,13=>0xff000000aa000000ff000000aa000000ff000000aa000000ff000000aaff00ff00ff00aa00ff00ff00ff00aa00ff00ff00ff00aa00ff00ff00ff00aa
|_,_=>0
def sP:Nat→Nat
|0=>0x1090029050b022809000c0f250b0702010c240b070201230c21170b0702010c1f171e070201081d18020109000c0b1c02011b000c0b0702011a000c0b07020116080c050b021509000c0b140201000c05131012000c05110b100a000f0b0201090c050b010e000c050b010d000c050b0a090800050407060100050403020100
|1=>0x108052502013b003a3c050b0702010805130b10000c050402013b003a390b1807020108050b020138000c050b023709000c050b0734000c050b100a12000c050b023309000c1f0b070201083205310b100a000c3017070201230c05170b070a080504070201002e2d0b02012c000c050b070201082b270b020109260c052a02
|2=>0x14a0c0504070201490800050b020148000c050b024709000c0b07020146000c1d1745070201080517440702010c05250b070a0800050b014309000c050b022f090800050b014209000c050b020141000c0b07020140000c1f0b0201090020050b023f09000c21040b07020100050b023e09000c3d050b070201080f040b0702
|3=>0x5259000c05580b070201000c3905040b0702010005550b070201080c5405040b0702010022040b07020100200517070201230c05250b0702014a0c4c0517070201080c5305040b0702010827250b070201260c05250b07020151001f0b07020108004f050b02014d08000c4c0504070201000c05252a070201002905170b0702
|4=>0xb025f0109000c050b07025e00290c1f050b0201090800050b0201095d000c30170b070201260c05170b07022f0805171e070201080c4c0525070201000c19050b020109000c050b0702014a080c4c0517070201000c050b02015b000c05170b5a070201083905170b07020108220b070201004f0c0b07020116000c0b070201
|5=>0x50b020109000c050b02640109080c05630b070201080005300b020109000c05171e070201000c270b07020159080c0b070201615d080c1f170b180702010805040b07024708003905250b07020100050b07023f00290c05272a0b070201081d240b070201080c1f0517070201082905040b070233000c4e050b020109000c05
|6=>0xc050b6d0201000c05040b0702016c00056b0b070201000c6a0b0702015d000c05040b690201080005250b070233000c190b18070201080c39050b07020108006805250b0702010c05170b070233000c60050b020109000c6705170b0702010805660b070201080c1d1762070201000c05170b070237080c050b07025e000c22
|7=>0x40b0702017300050b100a000c220b18070201080c05170b450702010805170b02015b000c050b07023308000c0f0b070201080c6a170702015d000c2d050b020109000c050b02010900720c05710b020109000c050b07020170000c6f05040b07020100050b070143000c05250b070237000c050b07026e000c05170b070a00
|8=>0x200b0702014b5d000c050407020149000c05170b07023f080c7605040b0702470067050b0702010800050b02010900260c050b02010961000c050b070275000c051707020108230c74050b070201080c300b07020159000c05250b02015b000c05170b07020173084e0b18070201000c210b070201000c0b070201735d000c05
|9=>0x59000c05040b070143000c68052a0b0702010c050b027b0109000c050b07020108320c050b780201000c74050b070201000c05250b0702017300050b02015b08000c05040b6d0201000c6a05040702010800050b070215000c390b18070201000c051707020149080c05770b070201000c1d3017070201080c1f170b07020108
|10=>0xb0702010c052507020149000c055c0b020109000c05040b0201093b00050b0702017e0805040b0702014a08050b450702010800052a0b07020161081f250b070201002005170b0702017c0827040b070201082605250b07023f000c051707020149000c050b18020109000c22170b070201200c1d18070201080c050b020109
|11=>0x29050b0201094b000c05250b07022f08000b070a50000c85050b020109000c05170b070143000c050b07025e08000c05250b6d0201000c5305250b0702010c1d1707020184000c820504070201000c050b077f000c3c050b070201000c050b0702017308001f1e0b070201080005170b6d0201000c050b0201092c000c530517
|12=>0x2010800270b07020108230c050b02014d000c050b02018709000c050b0201091b000c050b6d020108000c050b070a080053050b070201080c05250b0201093b004c05040702010800050b86070201000c221e0b070201000c1d0517020109000c54050b070201080c0b0702016159000c05250b070143000c05270407020108
|13=>0x2010900200c6f05170b0702010c1d1718070201080c052a0702010029050402010900290c050b070236000c05250b070215000c052a040b020109001d05172a07020108050b0201093b080005170b0702016c0c30040b070201002605250b070247000c05170b070215000c8905170b0702010c050b07014308000c05880b07
|14=>0x517070201080c050b07028c080005252a0b02010900051702010900290c0504020109003a0c050b07021508000c1d1745070201000c4e0b62070201000c05040b070237080005250b690201000c1f0b6207020108000b0702014b59000c2405040b07020108050b02018b09000c27560b070201080c190b62070201000c050b
|15=>0xc0517020109003a0c050b02010952000c600b62070201000c050b0702016c000c740b0702015d000c300b07020100230c051707020100920c1d0b070a000c220b62070201000c05170b070201900c050b5a07020108050b0702018f080c052502010900290c05040b02014d000c1d2518070201000c05170b0702018d0c65
|16=>0x702010c05250b02014d000c050b62020109000c05172a07020108291f0b180702010805040b070201990097050b070201080c6f050b070201000c05170b02014d000c0525020109003a0c052a040702010029050b1c020109000c052a0b0201090800050b960702010800050b02010995000c05130b070a000c650517070201
|17=>0x7020108260c05170b07020161080c6005040b070247000c050b0702014b000c1f170b18070201000c9f050b070201080c050b0702018d000c05270b020109080c05040b07023f0800050b070233000c050b02017d09000c0f0b0702010c050b07020108009d0b07029a000c30560b070201000c6a0525070201000c89052a0b
|18=>0x50b0702017c000c746a050b070201000c05040b07020152080005170b07020191000c05250b020109000c6705170b070201000c19052a0b070201000c05170b020109000c05040b0702640108050b070a000c05250b07020100720c050b0702018700290c0571250b070201000c4c050b070201000c050b070237000c05170b
|19=>0x70201000c052a040b0702010005980b070201000c050b0702a2000c940b0702015d000c05170b18070201080c051e0b070201000c05250b07020100260c05250b07020161000c1f0b070201500800270b07020108260c050b070201510800050b0702a101000c05040b07020159000c050b0702a0000c05980b07020100290c
|20=>0x18070201000c050b0702018b000c05250b07020159000c05170b07020173000c8505170b070201080c05040b0702014b000c051707020108290c050b0702014a000c05170b45070201000c65050b07020108000c05170b07020159000c220b07020150000c05172a0b07020108050407020100290c050b02010908000c050ba3
|21=>0x1615d000c0b07022f50000c055c250b070201000c1f0b0702010020050b0702016c08000c1d240b070201000c1d270b070201080c7605040b07020100050b07028c000c050b07020135000c050b07023f000c050b07020100a50c6805170b0702010c05170b0702018e000c059b0b0702a4000c055c170b070201000c05250b
|22=>0xb0702014b000c8505250b070201000c05170b07020187080c050b0702015908000c052507020100290c6f050b07020108000c05170b0702014b000c60050b0702010800a6050b070201000c05252a0b07020100050b07020183000c5476050b070201000c0b0702879c000c051707020100290c0525040b020109000c0b0702
|23=>0xb0702014a000c05040b07025f010800052a0b07020161000c05170b0702017c000c052a0b0702010800052a0b07020191000c0525170b020109000c68050b070201080c67052a0b070201000c190b18070201000c055c0b07020108000c1d052517070201000ca7050b070201000c300b07020100260c050b07022f08000525
|24=>0x50b07020108000c0530040b0702010800050b07023708000c05170b0702a2000c94170b0702015d000c050b0702014b08000c05270b07020108290c05250b07020187000c05170b07020108200c05a90b070201000c050b62070201000c24050b070201080c050b0702017d080c05a80b070201000c050b0702017e000c0504
|25=>0xc05170b0702018b000c1dac070201000c05250407020100290c6005040b070201080005250b02010908000c050b07020149000c1d300b070201000c05252a040b0702010005040b07020183000cab050b070201000c050b07020100aa0c050b070247000c1f05170b070201082205040b0702010800050b07020100230c4c
|26=>0x70201080029050b07020199000c85052a0b070201000c1d0b07022f000c050b690201000c05980b07020108000c05710b07027d000c05560b070201000c051e0b07020108000ca705040b070201000c05250b0702018b000c050b070201b0080005af0b070201000c05250b07020100200c74050b070201000c05ad0b070201
|27=>0x9417070201000c05040b070247000c22050b07020100290c050b07023f08000c05300b07020100290c050b070281000c050b0702018b08000c82050b070201000c1d18070201000c050b0702017a000c1d05172a070201000c05040b62070201000c220b0702015008000c05251707020100290c05040b0702010800721f050b
|28=>0x39050b070201000c54050b070201000c220b07020100200c050b07020193000c050b070201b3000c05250b62070201000c05170b62070201000c05252a0b070201080005170b0702017d080c052a0b07020187000c050b070201004f0c05040b07020108002605250b07020152000c1f0b0702010800204e050b070201000c1d
|29=>0x201080c270b070201260c050b6207020108000cb6050b070201000c7405170b070201000c1db20b070201000c0527250b070201080c05250b0702017d000c05710b070201080c05040b690201000c050b070201b5000c050b07020184000c60050b070201000c050b07020100b40c607605040b07020100050b5a070201000c
|30=>0x4908000c1d300b07020108000c050b070201bc000c05170b07025f01080c050b07020161080c059b0407020108008505040b07020108004e05040b070201000c65050b07020100290c05b90b070201000c1f0b18070201000c05170b0702015d080c0504070201080029050b0702010800230c050b070201b7000c1905170b07
|31=>0x5170b070201000c05250b0702015d000c1905250b070201000c0527040b070201082205170b070201080c050b07020191000c05af0b07020108000c65050b070201000c050bbf070201000c67050b070201000c0530170b070201080c050bbd070201000c1d1718070201000c050b020109000c1f050b070a000c050b070201
|32=>0xb070201510005170b07020193000c0530250b070201000c050b0702018f000c050b0702016c000c05040b070201a4000c4e05250b070201000c050b18070201080c050b0702019e08005305040b070201000c05250b07025f01000c1f05250b070201080005040b07020187080005560b07020108000c6a0504070201000c4e
|33=>0x7020108000c85050b07020100290c0571170b070201080c050b07020173000c05040b07020108002005170b07020184000c6a0517070201000c050b45070201000c05170b5a070201000c050b07020159000c3905170b070201000c2205250b070201000c05250b07026401080c05c00b07020108006f050b070201000c0504
|34=>0x50b070264000c1d0517070201000c0571170b070201000c05172a0b070201000c22050b07020108000c05040b070201080005040b020109000c1d0517070201080c050b0702018e000c05170b07022f000c055c0b070201000c050b07020108004f0c05170b0702018a0c6005250b070201000c05170b07020108720c4e050b
|35=>0x260c05170b18070201000c050b07020100290c050b07020100200c059b04070201000c8505040b070201000cc1050b070201000c050b0702018a000c05ae0b070201000c050b0702a2000c050b0702010800720c1d050b0702ba01000c05170b07020161000c050b070201bb000c9f050b070201000c050b0702015008000c85
|36=>0x20187000c050b070201c4000c1d050b07020108000cc3050b070201000c05c00b070201000c050b07020152000c050bbe070201000c1d270b070201000c050b0702019e000c05040b07020187000c8505170b070201000c050b070201c2000c1f05170b070201000c570b07020150000c059b0b070264000c050b0702010800
|37=>0xc050b0702018708000cca050b070201000cc9050b070201000c24050b070201000c05270b070201080c05170b070201080c050b0702017d000cc8050b070201000c050b0702c701000c68050b070201000c1f050b0702ba010085050b07020108000c05c60b070201000c050b79070201000c050b070201c5000c05170b07
|38=>0x70201000c1d76050b070201000c19050b070201000c059b0b07020108000c050b0702010800290c050b0702010800200c05cc0b070201000c050b070201b1000c1d940b070201000c1f0b07020150000c05250b070201000c050b07020151000c1d570b070201000c05040b07020152000c050b070201cb000c1f050b07022f
|39=>0xc60050b070201000c05170b0702017d000c0527040b070201000c57059b0b070201000c05800b070201000c22050b070201000c050b07026401080c05170b0702ba01000c05300b070201000c059b0b070287000ccd050b070201000c050b07025f01000c1f050b0702010800050b0702015d000c050b070201a2000c85940b
|40=>0x50b070201000c1905170b070201000c1d1f0b070201000c0525170b070201000c050b070201cf000c050b07020100720c050b0702019c000c05710b070201000c052a0b070201000c57050b070264010c1d059b070201000c050b070201b8000c050b07022f000c050b070201a4000c05ce0b070201000c0525040b07020100
|41=>0xc050b070201d1000c050b070201b0000c1f050b0702a2000c05040b07026401000c05250b07020108000c5705040b070201000c6a050b070201000c6005040b070201000c57050b0702ba01000c050b07020100260c050b07020161000c851f0b070201000c76050b070201000c05ac0b070201000c05170b0702015d000cd0
|42=>0x7020150000c050b07020108000c05270b070201000c05170b070201000c05040b070201000c050b0702ba01000c059b0b070201000c050b07020187000c85050b070201000c05300b07020108000c0594170b070201000c050b07025f0108000c050b18070201000c1f0b07020187000c059b0b0702ba000cb2050b07020100
|43=>0x50b070201000c1f050b070201000c1d050b070201000c05940b070201000c050b07026401000c57050b070201000c050b
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x30601530091803cc018600930031800cc0006
|6,0=>0x2dce16770b038565c2a4e14b70a2384f5c26ce12f709438485c234e113708638415c1fce0f77078383a981c6e0dc706ab8339c190c0c1705d382cdc158e0a5704fb0261c122e08a7041b81f1c0eae06e7033b8181c0b2e0527025b8111c07ae0367
|7,0=>0x1b440d8206b1035081a440d0206710330819440c8206310310818440c05c5f302f18174c0b8605b302d18164c0b06057302b18154c0a86053302918144c0a0604f302718134c098604b3025271254090a0475023281154088dc43702138105c0811c3f901f480f64079203b901d480e6b8716037b01b580d6c0696033b019580c6c061602fb01758
|7,1=>0x2ae395520a990544829e414d20a590524828e414520a190505727ec13d609db04e5826ec1359c99d04c6825f412da095d04a7724fc125e091f0487823fc11de08df0467822fc115e089f04478220390e208610428821041062082104097200c0fe607e6c3eb81f1c0f6e07a703cc71e240ef2076903ac81d240e72072ae38d81c338dfdc6f0e3708
|7,2=>0x3a941d2a0e85073a839941caa0e45071a838941c2a0e0506fa837941baa0dc6e6db836a39b320d8906bc835a41ab20d49069c834a41a320d09067c833a419b5cccb065d832ac193d8c8f063f831bc18be0c4f061f830bc183e0c0f05ff82fbc17be0bd2c5e182ecc17460b9305c182dcc16c60b56c5a382cdc164e0b17058382bdc15ce0ad705638
|7,3=>0x22fe116f08b07454422899135089464464221210f9087484364219210bae8558426c2116107b08358416c2096103b08158406c2019cffd07f683f741f9a0fbd07d683e741f1a0f80c7b883d841ea5cf43079983c8c1e260f03077983b939daa0ec5075a8
|8,0=>0x569c2b2e15870abc755a42ab5d54b0a9d854a4aa3215072a7a9539429a654c12a5795274a91a147d0a3595164a88e54370a138505c280e13f709f384f5c2791d3b909d394e5c270a537329b184d4c26861333099094c4ba60252f1096f94b34a57652ab094c94a1ca4ee1267092d64924a46e5225290a8481ba3ea51e328e894704235e519f08c78
|8,1=>0x6773b39659b92cd39665c330e19752cb19654c32861934ec928644cb20618f12c6f9633c317e18ad2c4d96224b0ee58652c2a86114306a18250c0a860142fe657e12be795ef4af5a179b2bc495de42ece57570ba295cccae4617130b8275bccadc256cf2b5e95ab42d3656892b3c859a42cb216490b1b958a3ac3216072afb857a3abae55c8eadb9
|8,2=>0x782c3bf25deaeeec977243b6e5da70eca9760cbae61d630ea98750c3a661d230e889740439e21ce10e688730439621c9f2e46971ecb8d25c572e23870d4b8465c130e0186fcc37c61bd12de086ebcb741db8f2dbf86dc3b6c21b4f2d9e96cacb6325b072d7a96b9435a65ac4ed5b76a94b52a1a850d3996984b49e5a3f0d1786874b41a19fd0cf59
|8,3=>0x89344476622b110c9881cc3ea61e330e898704435e619d30c6885f442d6615b10a4984dcc24a61151082883d441c660d13060882c4413e608d303e881b440b66049301b98094c02660030ff897f7cbf9a5fbd0fd597e6c3f125f790fb487d643e8e5f370f9387c63be15def92f7397b5c3d8a5eb50f5287a4cbd025e6f2f2f8793c3c7a5e2d0f0d9
|8,4=>0x8a3444fa226d112e8
|9,0=>0x9ac4cd3e668f133f899bc4cbe264f131f898bc4c3a660d12fe897accbb625cb12dd896ac4b36258b12bd895ac4ab6254b129c994a44a322509127b9939c49aa64c5125a89294492a2485123a8918cc8a2644112179907c481e23fd31f598f6c479623bb11d498e644712237911b578d64c68e6335319288c54460662f3117188b44c57e62ad314e8
|9,1=>0x15319a944d47e6a2f150f8a83c53fe29ef14ef8a73c537a69ab34cc9a62452ee696534aa8a514526a2925148a8a40cd1e628e134688a2fcd15e289f14478a1fc50de285f14278a0fc5061e821140889ffccfde27dd33e599ee4cf52279913c489ddccece275713a389cdc4e4e2717138389bdc4dca66d513619
|10,0=>0x2b45159a8ac94562a2b05157a8ab9455aa2ac5155a8aa94552a2a85153a8
|11,0=>0x15aa7
|_,_=>0
def wAt:=mkWire dB 210 248 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xc40031050b46031051702c01022f42c21000c47c04050c4c0990b0c414220508c9c99050881403000c41c290b0a408bd1f0101431090cc941f0400408d90135c14aa170cc2c010b1081c29022f47c04050c42c41070a408bd1f0101431000c42c01022f47c04050c49c990508814030b08400312220c2c01050841420050c42c810508000311918c145c051740031
|1=>0x51742c01050854022000c4646305170145d0b004c0a50508c2c22000c53833570442c310500558010b2641422000c41421050802c311d08000310b004142d520041413040042c310b0041423000c414110b0c414220500c2c21000c548310504c10010b0c4143150088142f4e07c14950b0842d2d0525c10010b0c4942f170c45c330b0052c010525c5c310b0041421
|2=>0x508000310b6241494170c414960500c0031000c4145f0517814310517000316001c14110b0c45c31190cc145d0b004142d0508c2c224e01d5c110500414952507c2c21000c4941f0b0840031050c4941f0b08414220b00414230b00400311f01014310b0042c810508000310b084c02d0508c00314b00414970b08400310b4b41497170c42c015c07c94050b0840031
|3=>0x170cc2c010b00408bd1f0101431074b414970b0840031520841413000c488a70508400310752414130b0c400314e01c14950b084003105170145d000c53833052542c21000c45c311900c145d0b0053807052545c312507c14a90b0045c9b050882c01050b414940b0042c01220101421000c59407052942c22000c414212507c2c2101004941f0b08400311e0c42c81
|4=>0xc4c05d0b0041423000c494050b08400310517c2c01000c4c099050881423000c52c310525c10010b0c41c29022f47c04050c41421051700031000c46031051702c015c07dc431170153807052542c212726414220500c00310b00414252507c2c21000c4941f0b08400312518c145c0b00580230504400314e02c14950b08400310b08488040508400310135414aa
|5=>0xb004142d4e02d5c1105004941f0b084003118088145c0b0040031077a415e70400c2c31174b414970b00584310517c5c310b005701f250142c21074b41497040053804052542c21000c41421000c4142d0508c2c01050c41420000c5382f570442c31050042c012201c1421000c58007600cc14110b0c414a9250cc2c2105088941f0b0859404052942c22000c47420
|6=>0x270c414034b0c414970b08400310b2041431050800031074b41497170c53803052545c310b004882f050842c21000c42c21000c424332507c10010b0c400312704814030b0c414130b0c47c94050c42c21000c42c21050c41420000c5f4311701c2c01000c414220500c00310b08488070508400314e0bc1495170c42c012507c145c170c42c01050841420051700031
|7=>0xc4941f0b0840031074b414970b08408bd000c47c04050c53803052542c21000c424330b08400310508c0031050842c8105080142d2507c5c316f0047423050b400314e02c14950b08400310b08400311f0101431022f47c04050bc14312507c2c21000c5380b052545c316501c14a50b08814970b08400316000c1001050442c310b8355c130b0c41401028160004
|8=>0x5088003105080941f0b08464230517400310517000310b004142d250bc5c31170cc2c012507c942f040042c310135c14aa170cc2c014e01014950b08400312507c9433040042c31170cc142d090cc941f0b08400318a0c584010517c2c010b0c414220508c10016001c14110b0c53804052545c316700c14a9170cd380b052542c21560cc2c9905089381f052542c21
|9=>0x50842c219100414ab170cc2c01000c47c5c0b00414312725814030b0840031250bc941f0b08400314e07d5c1105004142d051705c310b00638011f17c2c01050c58004050442c31000c4941f170c45c330b004942f2507c5c310b0042c262507c10010b0c53804052542c21050b4145c0b0042c31220101421000c410010b0c41494050c42c21000c42c310508c1403
|10=>0xc40031170cc1431051702c01000c60c315704c2c310500660010529c2c22000c5381f052545c310b098941f0b0840031250bc9433040042c31250cc941f0b08400310420c14200b0c4941f0b08400310b0a408bd1f01014310b098941f170c42c012507c14130b0c414940400414110517a505d0b00474200508c00310b93974310517808bd1f010142d050c41494
|11=>0x50c404220b08400310b0880031170c45c050b004c02d0508c0031220115c310500414220b00400310517c2c01000c58007050442c310525c2c21000c4145c0b0041431270b41403000c678011f0bc14312507c14030b0842c312201c1421000c53807052542c21000c49c99050881403000c678221f0bc1431879c4166e0501c2c050b5241413040042c31052542c21
|12=>0x1f0101431051782c01050cc145c0b00400310b2041420000c414220b08400310517c5c310b0040031050bc1431050881403000c40031500c4142f012942c22000c41496040042c318001c9c310500c2c22000c5f4311701c2c016a006502d050cc14130b0c40031052ac5c330b004941f0b0840031052a45c330b0042c012507c5c310b00404010b0c40031022f47c04
|13=>0x1f17c2c01050c61c010501c2c05710c45c050b004145c170c42c012501c2c21000c414960b0840031610c4145f0b00400310b00414050525c10010b0c42c010b08800315200414130b0c46031051702c01052942c22000c41496170c42c011f004142f050c40031170cc2c01250bc10010b0c4941f0b0840031570402c31050049433040042c310529c2c22000c47cbf
|14=>0xb00414110b0c400310579410030b0c45c31170cc2c015704c2c3105005d8011d0cc142d059b814070b014942f170c42c012507c10010b0c4145f051782c011f010142f050c494050b0840031050c41420000c54021050bc003194004142d050cc1403050b40031600cc14110b0c580041f0b41431052a85c330b0048807570c41401012982c22000c46403051742c01
|15=>0xb0c548010504c2c31010842c31000c4145f170cdf4311701c2c01250cc2c21000c45c330b004941f170c42c01000c47403050b414a9170cc2c0105170145d0b00494050b0840031170c42c01050b49c110500c2c31050881423000c400311f01014310525c2c21000c41001050142c310b00400310501c14960b08400310b0842c22000c47423050b400310525c5c31
|16=>0xb0c414016a00e502d050cc14a60b08800316001c7c2d050c414310b0040031050842c31000c47420050b40031300b41423000c42c310508c0031220101421000c42c011f01c1431051782c01050cc14970b08400310500c2c22000c42c21000c414070b0041420000c4a805170cc2c01052502c21000c4c0010508c0031000c45c070b004121d0b0c41407270481403
|17=>0x1f010142d050c41d490504c2c310529c2c22000c45c07170142c010b2641422000c42c810508000312704414030b0c494070b0840031050482c31000c42dc9010880031050802c21000c6505d0b0041433ae0cc2e1d0501c9407170c42c01059b0142d0b014942f040042c31050442c31000c4941f0b0840031220bd5c3105004142d0508c0031250cc10010b0c55c13
|18=>0xc414220b0c400310504c10010b0c41431050800031052542c21000c414330b004142d6001c14110b0c414210b08888070508400310b0880031800109c310500c94070b0840031b20b55c3305004145c0b004142d0579c10030b0c45c330b004142d0525010010b0c41421050bc0031250bc5c310b00404220b0c40031050c42c22000c6c431570bc1401170cc2c01
|19=>0x570cc142d0500414030b08400311701c5c310b0045c050b00400310752414130b0c42d7e640c40401941782c01050cc16c1050482c31052902c22000c58033050442c311f1702c01050c46433570b41401760047433050b414210508000315d0c4145e0b005f4331701c2c01052502c21000c41494170c42c01250cc2c21000c45c070b0040031170cc2c0150088142f
|20=>0xb0840031022f47c04050c4882f050840031050b41423000c55c120b0c41401010842c01000c4145f0b00400310b0142c31000c414050b0c40031570442c31050042c22000c42eed05bac0431050c4145c0b004145e0b00400310b0c42c22000c47420050b40031b800410070b0c4145d0b0040031050881403000c414940b08400319f0cc9c2d0500e505d0b0041433
|21=>0x51702c01000c47c2f050c400316000c14110b0c404210b0840031050c42c21000c414070b0c400310b2641422000c42d490504c2c31052545c310b004145e170c42c01051745c310b00414030b0c40031050842c01000c414ab170cc2c010b7240422000c414a50b0880031052a05c330b00414a9170cc2c010b0041423000c6f801050402c31051702c01050b4941f
|22=>0xb08400310b0880031000c45c050b00584310517c2c01050802c31000c6505e0b0041433940b42c01050cc6031051702c011f1702c01050c414960b0840031190cc145d0b00414210b0840031010042c21000c66c33000c42c05680cc7403050b548310504c2c315d0c4145e0b0042c210508c0031b000414120b0c54401500c4142f870042c310501c14950b0840031
|23=>0xb0c42c05050142c311f014143150004142f0b87414071f01c1431010880031050b404310517c2c0105bac0431270b41403050bc00310501404010b004142d170142c01170cc2c010508400310b0c400312507c10010b0c400310b004142d1f17c2c01050c47c040b0041431250142c21000c54022050bc003161004145f0b0041001050442c31010882c01000c41495
|24=>0x2701414039400414330500c00310b00400311701c2c018500c140501504142f1d00c142d010c414310501400319b00c2c050400c2c310564c04010b0041407870c41407050b40031850cc14059b0cc2c050504c2c31050402c31050b414031f0bc14310b0c414070b0041405059bc2c050b0041431050bc14010b0140401050880031051702c010b0880031050800031
|25=>0x1701c2c010500c2c31050042c05270c41403570c41401000c404010b00404310508c00310501c2c05940141433640c40401050c40031051782c011f01c14310501414331d0cc142d570b41401000c42c050b08800310508000319b0c42c05570bc1401050b41433050bc14310b0840031500c4142f050b414010504c2c315701c14011f0101431000c41407056440401
|26=>0x850bc1405050482c311f01c14310b0c404010b08400310b0c41401940b41433050442c31010c414010508800310517c2c010501414311d0cc142d059b02c05051782c01059b42c05051742c01050b41431170c42c011d01c142d010880031059b82c050b6440401170cc2c01050040401050b42c050401c2c311f01014318700414071f00c1431040042c311f0b41431
|27=>0x50c4142d050cc040105004142f000c414030b0042c31010c42c050501c14050508c00310b0041433010840031051702c01050c41407010c42c05570cc1401
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0xe9400003550000000000000000000000000003140000000016a000000000a1412980000000000010281b5000000000b28000022a000000000000000000000000c5000002100220000000000000020000
|7,0=>0x1e0600007620e841ca638506ea0da31b2235c86a18d1319a832506318c2417c800005d98b8316a62cc857a0ab4000000005490a8114a628504f18000136600004c189441208231000008841088201000007e20f661dd000007340de81ad000006830c8818102e985b20ae814d028184d30928115020a03f2
|7,1=>0x342867c8cda000032e864d0c8198c43108614cc1197e400005ecc00017832e885c10b6996942cc658cc00015f40000574800015b22ae80000a9a14f42968520ca29800028284fc89da000027064d4c000131400004b5094a1263244847cc8e1918422e244d0881800021a6428c83210241fc83e907b20f33
|7,2=>0x4a06934c000249448e490d0000241200008f8c00023b347068d1118222c44508891110221e243488591099a0f44186824d031a03300007fd0fe180003f267d50f8a1ee33d840000f499e633c480000ef2000000007690eb21d333a06734ce519c6400007090df2000037486d90d99800035e86ad0d491a54
|7,3=>0xb64d6aa2d140000b351651ac640000b0900002bf30000af495ca2b5456280001571aaa454c8000151229f35386a61000029445226a38c00028b35106a14d40a27e34f489d9139226e44d6699d131a00004be896d12ba2534
|8,0=>0x72a6e48dc79b8c37126e18dc19b8036fa6de8dbb9b7436e26db8db59b6836ca6d88daf9b5c36b26d58da99b50369a6d28da39b4436826cf8d9d9b38366a6cc8d979b2c36526c98d919b20363a6c6c98c1b1536246c3cd861b0936102c14d811aff35f86be897b9af435e26bb8d759ae835ca6b88d6f9adc3
|8,1=>0x8a67140e269c4a388e7110e209c3e387670e0e1a9c32385e70b0e149c2638467080e0e9c1a382e7050e089c0e38167020e029c0237fe6ff0dfc9bf727e86fc4df793ec37d26f98df19be037ba6f68deb9bd437a26f38de59bc8378a6f08ddf9bbc37726ed8dd99bb0375a6ea8dd39ba437426e78dcd9b983
|8,2=>0xa1e7430e849d063a067400e7e9cfa39ee73d0e789cee39d673a0e729ce239be7370e6c9cd639a67340e669cca398e7310e6114bf397872e4e5b1cb3396072b4e5594a8394c528ce501c9d3934725ce4a1c91391c722ce441c8539047200a3e9c7a38ee71d0e389c6e38d671a0e329c6238be7170e2c9c563
|8,3=>0xb9a7728ee39dc43b8276f8ede15b93b6c76cced81dad3b54769ced21da13b3c766cecc1d953b24763cec61d893b0c760cec01d7d3af475dceba1d713adc75aceb41d653ac4757ceae1d593aac754cea81d4d3a94751cea21d413a7c74ece9c1d353a6474bce961d293a4c748ce90951e3a367460e8a9d123
|8,4=>0xbb27758ee99dd03
|9,0=>0xcb45960b2b16542ca45940b27164c2c945920b2316442c845900b1f163c2c7458e0b1b16342c6458c0b17162c2c5458a0b1316242c445880b0f161c2c345860b0b16142c245840b07160c2c145820b0316042c045800aff15fc2bf457e0afb15f42be457c0af715ec2bd457a0af315e42bc45780aef15dc2
|9,1=>0x6cc2d945b20b6316c42d845b00b5f16bc2d745ae0b5b16b42d645ac0b5716ac2d545aa0b5316a42d445a80b4f169c2d345a60b4b16942d245a40b47168c2d145a20b4316842d045a00b3f167c2cf459e0b3b16742ce459c0b37166c2cd459a0b3316642cc45980b2f165c2
|10,0=>0x36d8eda1db23b6076b8ed61daa3b507698ed21da23b407678ece1
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 15
def pmP:Nat→Nat
|0=>0x81800000040800000020200000010000000005300000000f400000006e00000003600000001a00000000c80000000540000000290000000128000000090000000044000000021000000010000000007800000002c000000014000000009800000004400000001800000000a000000004000000001800000000a0000000040000000018000000008000000002000000000
|1=>0x282800000141000000086400000042a000000214000000109000000084400000040e000000204000000101800000080a000000403000000201000000100400000080000000032f0000001950000000c8000000060e000000302000000101800000080800000028000000013c00000009b00000004a80000002500000001220000000900000000428000000210000000106
|2=>0x400b500002005800001000fe00008003700004001000001800100000300040000097ee000004293800001dcbc00000864400000430a0000020838000010410000008040000004003000002000000000dcb8000006d5c00000368e000000bd70000005abc0000010140000007ee000000295000000149c000000a4c0000005240000002910000001430000000a14000000506
|3=>0x1080978000821dbc000410c5e00020842f0001040850000811cbc000408c5e0002046120001003b78000801cbc000400e5a00020062f00010029780008010bc00040007e00020002f0001000138000800028000400010000200003000100001000080000000021285c0001036af000080a978000201500000100a7400008052a0000402910000201400000100854000080400
|4=>0x40021500020004a800100024000080010a000400010000200007c00100001400080000800030421780018118fc000c00c7e00060032f00030009f80018000fc00080842600040403200020029300010000fc00080006e0004000000001483978000a001bc00050007e00028002f0001183978000881cbc00044085e00022040a00010839780008414fc00042065e00021022f
|5=>0x200020f800a881cbc004c00a7e00240000700114a39780088418fc004410c5e00220842f00110411780088018bc004108ac400200c4200010022110008011080004008214002004022001002001000800149c004000814002000027001000011000800008000200000200100000000051039780028000fc00140001400088002f0004002950002001480001000a14000800500
|6=>0x300000380148010fc00a40085e004a2802f0025042978012801cbc008c2065e00460043f0023002178010a21cbc008510a5e00428052f00210a2978010821c9c008410c5e00420853f0021042178010811cfc008408a5e00420443f0021022178010801cfc008400e5e00420053f00210029780108014b400840087e00420042f00210021680100214bc00800883e00400052f
|7=>0x2010839781008218b4080400e5e04020062f02010011780d08000bc02853005e010a0000a00831021100418010fc02050006401022042f008110202004088100002043005e01020c022008104217804082001002041000001020004600810001900408000280204000080080000000034002138018a010b400c50025e00620442f00310031780188014b400c40085e00620012f
|8=>0x8910021784408810bc220408e5e11020042f0821080178410801cbc20840005e10020842f06011021782188010bc10840085e08400042f04100020502080000a010082880408040021f04010839782008418bc10042065e08000032804000019381488000080a044085e04420472f02210031f81108018bc088000c5e04220042f0201183978100881cbc08044085e04021472f
|9=>0x20054001790028000bc68c430c5e34423062f18a30c0178c518400fc628440c5e31421002f18a1000178c118800bc608c00c5e30421002f10810031788408000a840040000814621062f0a211031785108418bc260c08c7e13020c72f09810431784908310bc24841085e12420442f0901063178480821cbc240408e5e12020062f08a11c01784508600bc22842807e11421002f
|10=>0xc82100017e0508601bf0204000c580020004aa02114017c4908210be208c0005f10420002f880102397c1408818be08c410c5f04422062f80810c017c0108000be00080008d00000000670810000538128a00bd62800004ea1021802f48a104317a4508000bd220410c5e84621862f40a30801fa0508401bd020c200fe80423002f300200012104180011082040003c41020000e
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x20000d00000000000000000f00000040000130040000000360600000921c2400000000000000040001c2200000000400
|7,0=>0x6f83c2200021ac04040f83c0e7500008006a1d8500e350780800010000800230400006081583c0e00360781000020dc00c30000cd0ab040081ee518804d40003808b4040092c0202010002204010404202462604a07110041e6d088001e020103c221d000001e29012a4d400078000e770a8d400101a004380757ab0005901820000f180c8660f020e81e0f018306802
|7,1=>0x1c220100380a2fa000e8000400008ae031e000040c0b000200f3513400170780800070f26c9c0f198b4100a01010a0003902806090781c00115404400aa00008000f012640a0b37810169d090cc1e04010781e5b00004d400079602004010001e0f0a000080000034d26a0103c081d0000cce000804404000f875d006
|8,0=>0x7f06520187db1c322a8a9fe0c875820c48243f414721230bcc2af13e39aa70962892ba0252cfd400e40a895d431434d8c7e1f3b908470d0b86c8249865710c99a9030463e509a4b26432620763fc19e30b2a47ea23a788f88e7b10221c29c5a905a33e469c5708e3e469809f6202484d06a32de2436218a411213a8ce2a3279c68a4a98bca80c43e89882783e1559079
|8,1=>0x788f1ce8f3704ddb4f620f07314620b0fe4722d066f0f60a848094724287e7c3c8e5d8277b9917e532910998b13e3d4fe7c3f905c2da38159662e7dd70f93a782f0cc7c6111cba2f8dab5924763c4df838a8531bd1962364f8913d3ee1ae2404647c412e3e1e4c40a911ac7f6441cbd06301cdd6b7649f13c3d5a26a645f5bbb4ecdd31d35006588ba57b200945a2eea
|8,2=>0x4920cf476
|9,0=>0xd567d799f56ac2e64e958451d12ba8aa5aaaff67c761c9753ce57cfd534ba4535a54fa913c909d2087a493f5b8cc9eb35f946adb3e3929afc0e052fad3f5f93b45356b2b965338e2cb7e362607a7a52650e1659c247259521aa92c9b24a3c8584a0e573865b5d92797b499de8771d2916db4533e752dabb8603067cd51b71863b3e9702a74f97692
|10,0=>0x20102625116cc438310e092a94d0e524
|11,0=>0x70
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 37 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_245 10 roots_245 ops++addP pm 1 dom_231 9 roots_231 ops++addP pm 2 dom_243 10 roots_243 ops++addP pm 3 dom_119 9 roots_119 ops++addP pm 4 dom_103 6 roots_103 ops++addP pm 5 dom_183 9 roots_183 ops++addP pm 6 dom_54 4 roots_54 ops++addP pm 7 dom_148 4 roots_148 ops++addP pm 8 dzo_151_32 6 roots_151 ops++addP pm 9 dzo_215_32 7 roots_215 ops++addP pm 10 dom_215 8 roots_215 ops++addP pm 11 dom_226 5 roots_226 ops++addP pm 12 dom_244 7 roots_244 ops++addP pm 13 dzo_212_32 5 roots_212 ops++addP pm 14 dom_86 5 roots_86 ops++addP pm 15 dom_150 5 roots_150 ops++addP pm 16 dzo_86_1 5 roots_86 ops++addP pm 17 dzo_150_32 5 roots_150 ops++addP pm 18 dzo_149_32 5 roots_149 ops++addP pm 19 dom_55 5 roots_55 ops++addP pm 20 dom_212 5 roots_212 ops++addP pm 21 dom_246 9 roots_246 ops++addP pm 22 dom_102 5 roots_102 ops++addP pm 23 dom_167 5 roots_167 ops++addP pm 24 dom_211 7 roots_211 ops++addP pm 25 dom_151 6 roots_151 ops++addP pm 26 dzo_214_1 6 roots_214 ops++addP pm 27 dom_242 7 roots_242 ops++addP pm 28 dzo_118_1 6 roots_118 ops++addP pm 29 dom_214 6 roots_214 ops++addP pm 30 dzo_214_32 6 roots_214 ops++addP pm 31 dom_199 5 roots_199 ops++addP pm 32 dzo_246_1 7 roots_246 ops++addP pm 33 dom_230 6 roots_230 ops++addP pm 34 dom_166 4 roots_166 ops++addP pm 35 dom_182 7 roots_182 ops++addP pm 36 dom_118 7 roots_118 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_247 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_151_32_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_215_32_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_226 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_212_32_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_150 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_86_1_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_150_32_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_149_32_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_212 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_zo_214_1_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_zo_118_1_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_zo_214_32_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_zo_246_1_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_166 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_118 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_245 10 s (0,roots_245.map (·&&&dom_245)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_247 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_245 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_247 gM v ys):RunD true dom_247 gM v (ori ys):=h
def Z (s:Nat):=barP dom_247 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 9 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 46 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 46 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 239 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 111 128 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 239 → Z 7 i = true := (range_split z7_0 z7_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 256 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_256 : ∀ i, 256 ≤ i → i < 260 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 4 256 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 260 → Z 8 i = true := (range_split z8_0 (range_split z8_128 z8_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 121 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 121 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 14 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 14 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_247 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤11) (h:RunD true dom_247 gM s xsM):False:=by
  have hmin:6≤s:=by have hl:=run_len h;change 7≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_247 roots_247 goal_247 12:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_247
theorem lowS_247:Lower true dom_247 roots_247 goal_247 12:=S_247.noCircuit
namespace S_251
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,129),(2,18),(2,34),(2,66),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(8,9),(8,40),(8,136),(10,11),(10,26),(10,42),(10,74),(10,138),(16,18),(16,80),(16,144),(17,19),(17,25),(17,49),(17,81),(17,145),(24,25),(24,26),(24,56),(24,88),(24,152),(32,33),(32,34),(32,40),(32,96),(48,49),(48,50),(48,56),(48,112),(48,176),(64,66),(64,80),(64,96),(65,67),(65,73),(65,81),(65,97),(65,193),(72,73),(72,74),(72,88),(72,104),(72,200),(128,129),(128,130),(128,136),(128,144),(160,161),(160,162),(160,168),(160,176),(160,224),(192,193),(192,194),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1fffffffffffffffff
def xsM:=roots_251.map (·&&&dom_251)
def gM:=goal_251&&&dom_251
def NN:Nat→Nat
|10=>1
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|10,0=>0x294df
|11,0=>0xff75e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000f0f0f0f0f0f0f0f0f0f00000f0f00000f0f0f0f0f0f0f0f0f0f00000f0f0000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x1ec688fac688
|_=>0
def sO:Nat→Nat→Nat
|10,0=>8
|11,0=>0x87
|_,_=>0
def wAt:=mkWire dB 8 252 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 8
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xa5
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
addP pm 0 dom_250 10 roots_250 ops++addP pm 1 dom_123 10 roots_123 ops++addP pm 2 dom_249 10 roots_249 ops++addP pm 3 dom_243 10 roots_243 ops++addP pm 4 dom_219 10 roots_219 ops++addP pm 5 dom_235 9 roots_235 ops++addP pm 6 dom_187 9 roots_187 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_251 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_187 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_250 10 s (0,roots_250.map (·&&&dom_250)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_251 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_250 h
def symsG:List (List (Nat×Nat)):=[[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)],[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_251==dom_251)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_251 gM v ys):RunD true dom_251 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_251 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
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
namespace S_253
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,129),(4,20),(4,68),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(8,9),(8,40),(8,136),(12,13),(12,28),(12,44),(12,76),(12,140),(16,20),(16,80),(16,144),(17,21),(17,25),(17,49),(17,81),(17,145),(24,25),(24,28),(24,56),(24,88),(24,152),(32,33),(32,40),(32,96),(36,37),(36,44),(36,52),(36,100),(36,164),(48,49),(48,52),(48,56),(48,112),(48,176),(64,68),(64,80),(64,96),(65,69),(65,73),(65,81),(65,97),(65,193),(72,73),(72,76),(72,88),(72,104),(72,200),(128,129),(128,132),(128,136),(128,144),(160,161),(160,164),(160,168),(160,176),(160,224),(192,193),(192,196),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffffffffffff
def xsM:=roots_253.map (·&&&dom_253)
def gM:=goal_253&&&dom_253
def NN:Nat→Nat
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|11,0=>0x1e31b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x3333333300000000333333330000000033333333000000003333333300000000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0003300330033003300330033003300330033003300330033003300330033003300c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c2222222222222222222222222222222222222222222222222222222222222222cccccccccccccccc0000000000000000cccccccccccccccc0000000000000003333333333333333333333333333333300000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x1ac688
|_=>0
def sO:Nat→Nat→Nat
|11,0=>7
|_,_=>0
def wAt:=mkWire dB 7 254 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
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
addP pm 0 dom_252 10 roots_252 ops++addP pm 1 dom_189 10 roots_189 ops++addP pm 2 dom_249 10 roots_249 ops++addP pm 3 dom_245 10 roots_245 ops++addP pm 4 dom_237 10 roots_237 ops++addP pm 5 dom_221 10 roots_221 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_253 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_189 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_237 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_221 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_252 10 s (0,roots_252.map (·&&&dom_252)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_253 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_252 h
def symsG:List (List (Nat×Nat)):=[[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_253==dom_253)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_253 gM v ys):RunD true dom_253 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_253 gM mpG SD SS NN hAt idxH ori 0 mkPools s
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
  · simp [NN] at hi
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
def isoMvS_254:List (Nat×Nat):=[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_254:Lower true dom_254 roots_254 goal_254 12:=lower_iso_b isoMvS_254 (by decide +kernel) lowS_247
namespace S_255
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,129),(2,18),(2,34),(2,66),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(4,20),(4,68),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(6,22),(6,38),(6,70),(6,134),(7,15),(7,23),(7,39),(7,71),(7,135),(8,9),(8,40),(8,136),(10,11),(10,26),(10,42),(10,74),(10,138),(12,13),(12,28),(12,44),(12,76),(12,140),(14,15),(14,30),(14,46),(14,78),(14,142),(16,18),(16,20),(16,80),(16,144),(17,19),(17,21),(17,25),(17,49),(17,81),(17,145),(24,25),(24,26),(24,28),(24,56),(24,88),(24,152),(32,33),(32,34),(32,40),(32,96),(36,37),(36,38),(36,44),(36,52),(36,100),(36,164),(48,49),(48,50),(48,52),(48,56),(48,112),(48,176),(64,66),(64,68),(64,80),(64,96),(65,67),(65,69),(65,73),(65,81),(65,97),(65,193),(72,73),(72,74),(72,76),(72,88),(72,104),(72,200),(128,129),(128,130),(128,132),(128,136),(128,144),(160,161),(160,162),(160,164),(160,168),(160,176),(160,224),(192,193),(192,194),(192,196),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffffffffffffffffffffff
def xsM:=roots_255.map (·&&&dom_255)
def gM:=goal_255&&&dom_255
def NN:Nat→Nat
|11=>7
|12=>3
|13=>1
|_=>0
def HT:Nat→Nat→Nat
|11,0=>0xfd2f7fd1ddfb8e7ecb3258c994ba7e18457
|12,0=>0xc33a38fd7c0eef7
|13,0=>0x64457
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffffffff00000000000000000000ffffffffffff000000000000ffffffff00000000ffff000000000000ffffffff00000000ffff0000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffff0000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x86543210a86543210876543210b86543210d86543210a87543210865432c10986543210ab65432109a865432109876543210
|_=>0
def sO:Nat→Nat→Nat
|11,0=>0xe257ca693b25245500a
|12,0=>0x14e654c19
|13,0=>0x5c8
|_,_=>0
def wAt:=mkWire dB 14 256 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x21961605a1e196161987985a161981619a161987585
|_=>0
def oO:Nat→Nat→Nat
|11,0=>0x3094482311084402
|12,0=>0x405e2e1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 9
def pmP:Nat→Nat
|0=>0xfff7fe7fbff5fe7fc7f800
|_=>0
def pmB:Nat→Nat→Nat
|11,0=>0xb5f3f
|12,0=>0xab
|13,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 11 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_254 12 roots_254 ops++addP pm 1 dom_127 12 roots_127 ops++addP pm 2 dom_253 12 roots_253 ops++addP pm 3 dom_251 12 roots_251 ops++addP pm 4 dom_247 12 roots_247 ops++addP pm 5 dom_239 11 roots_239 ops++addP pm 6 dom_191 11 roots_191 ops++addP pm 7 dom_223 11 roots_223 ops++addP pm 8 dom_207 8 roots_207 ops++addP pm 9 dom_159 9 roots_159 ops++addP pm 10 dom_175 8 roots_175 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_255 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_127 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_247 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_191 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_223 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_207 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_175 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_254 12 s (0,roots_254.map (·&&&dom_254)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_254 h
def symsG:List (List (Nat×Nat)):=[[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_255==dom_255)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_255 gM v ys):RunD true dom_255 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_255 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 7 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z12 : ∀ i, 0 ≤ i → i < 3 → Z 12 i = true := span_ok (by decide +kernel : span (Z 12) 3 0 = true)
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
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [4, 8] }, { op := GateOp.or, inputs := [0, 3] }, { op := GateOp.or, inputs := [9, 10] }, { op := GateOp.and, inputs := [7, 11] }, { op := GateOp.or, inputs := [1, 6] }, { op := GateOp.or, inputs := [13, 10] }, { op := GateOp.and, inputs := [5, 14] }, { op := GateOp.and, inputs := [6, 9] }, { op := GateOp.and, inputs := [4, 8] }, { op := GateOp.and, inputs := [0, 3] }, { op := GateOp.or, inputs := [12, 15] }, { op := GateOp.or, inputs := [19, 16] }, { op := GateOp.or, inputs := [20, 17] }, { op := GateOp.or, inputs := [21, 18] }]

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 22⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
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

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_52276_aux

theorem PEqualNP.Outside.L_meta_52276 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_52276_aux.main
