import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_52674_aux
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
def dom_29 : Nat := 0x33333333
def goal_29 : Nat := 0xfafaaa00fafaaa00fafaaa00fafaaa00fafaaa00fafaaa00fafaaa00fafaaa00
def roots_29 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_30 : Nat := 0x55555555
def goal_30 : Nat := 0xfcfccc00fcfccc00fcfccc00fcfccc00fcfccc00fcfccc00fcfccc00fcfccc00
def roots_30 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_31 : Nat := 0xffffffff
def goal_31 : Nat := 0xfefeee00fefeee00fefeee00fefeee00fefeee00fefeee00fefeee00fefeee00
def roots_31 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

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

def dom_54 : Nat := 0x55005500550055
def goal_54 : Nat := 0xfcfcf0f0fcfc0000fcfcf0f0fcfc0000fcfcf0f0fcfc0000fcfcf0f0fcfc0000
def roots_54 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xfefefafafefe0000fefefafafefe0000fefefafafefe0000fefefafafefe0000
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

def dom_60 : Nat := 0x1111111111111111
def goal_60 : Nat := 0xfff0fff0f0f00000fff0fff0f0f00000fff0fff0f0f00000fff0fff0f0f00000
def roots_60 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xfffafffafafaaa00fffafffafafaaa00fffafffafafaaa00fffafffafafaaa00
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_62 : Nat := 0x5555555555555555
def goal_62 : Nat := 0xfffcfff0fcfccc00fffcfff0fcfccc00fffcfff0fcfccc00fffcfff0fcfccc00
def roots_62 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfffefffafefeee00fffefffafefeee00fffefffafefeee00fffefffafefeee00
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_77 : Nat := 0x33330000000000003333
def goal_77 : Nat := 0xfafafafafafafafaaa00aa00aa00aa00fafafafafafafafaaa00aa00aa00aa00
def roots_77 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_78 : Nat := 0x55550000000000005555
def goal_78 : Nat := 0xfcfcfcfcfcfcfcfccc00cc00cc00cc00fcfcfcfcfcfcfcfccc00cc00cc00cc00
def roots_78 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_79 : Nat := 0xffff000000000000ffff
def goal_79 : Nat := 0xfefefefefefefefeee00ee00ee00ee00fefefefefefefefeee00ee00ee00ee00
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
def goal_85 : Nat := 0xfffffafafffffafafafa0000fafa0000fffffafafffffafafafa0000fafa0000
def roots_85 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_86 : Nat := 0x5500550000000000550055
def goal_86 : Nat := 0xfffffcfcfffffcfcfcfc0000fcfc0000fffffcfcfffffcfcfcfc0000fcfc0000
def roots_86 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_87 : Nat := 0xff00ff0000000000ff00ff
def goal_87 : Nat := 0xfffffefefffffefefefe0000fefe0000fffffefefffffefefefe0000fefe0000
def roots_87 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_89 : Nat := 0x30303030000000003030303
def goal_89 : Nat := 0xffffaaaaffffaaaaaaaaaa00aaaaaa00ffffaaaaffffaaaaaaaaaa00aaaaaa00
def roots_89 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_90 : Nat := 0x50505050000000005050505
def goal_90 : Nat := 0xffffccccffffcccccccccc00cccccc00ffffccccffffcccccccccc00cccccc00
def roots_90 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f
def goal_91 : Nat := 0xffffeeeeffffeeeeeeeeee00eeeeee00ffffeeeeffffeeeeeeeeee00eeeeee00
def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_93 : Nat := 0x333333330000000033333333
def goal_93 : Nat := 0xfffffafafffffafafafaaa00fafaaa00fffffafafffffafafafaaa00fafaaa00
def roots_93 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_94 : Nat := 0x555555550000000055555555
def goal_94 : Nat := 0xfffffcfcfffffcfcfcfccc00fcfccc00fffffcfcfffffcfcfcfccc00fcfccc00
def roots_94 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_95 : Nat := 0xffffffff00000000ffffffff
def goal_95 : Nat := 0xfffffefefffffefefefeee00fefeee00fffffefefffffefefefeee00fefeee00
def roots_95 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_99 : Nat := 0xf0000000f0000000f0000000f
def goal_99 : Nat := 0xeeeeeeeeeeeeeeeeaaaaaaaa00000000eeeeeeeeeeeeeeeeaaaaaaaa00000000
def roots_99 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_102 : Nat := 0x55000000550000005500000055
def goal_102 : Nat := 0xfcfcfcfcfcfcfcfcf0f0f0f000000000fcfcfcfcfcfcfcfcf0f0f0f000000000
def roots_102 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_103 : Nat := 0xff000000ff000000ff000000ff
def goal_103 : Nat := 0xfefefefefefefefefafafafa00000000fefefefefefefefefafafafa00000000
def roots_103 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_105 : Nat := 0x303000003030000030300000303
def goal_105 : Nat := 0xffaaffaaaaaaaaaaffaaffaaaa00aa00ffaaffaaaaaaaaaaffaaffaaaa00aa00
def roots_105 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_106 : Nat := 0x505000005050000050500000505
def goal_106 : Nat := 0xffccffccccccccccff00ff00cc00cc00ffccffccccccccccff00ff00cc00cc00
def roots_106 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffeeffeeeeeeeeeeffaaffaaee00ee00ffeeffeeeeeeeeeeffaaffaaee00ee00
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_108 : Nat := 0x1111000011110000111100001111
def goal_108 : Nat := 0xfff0fff0f0f0f0f0fff0fff000000000fff0fff0f0f0f0f0fff0fff000000000
def roots_108 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_109 : Nat := 0x3333000033330000333300003333
def goal_109 : Nat := 0xfffafffafafafafafffafffaaa00aa00fffafffafafafafafffafffaaa00aa00
def roots_109 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_110 : Nat := 0x5555000055550000555500005555
def goal_110 : Nat := 0xfffcfffcfcfcfcfcfff0fff0cc00cc00fffcfffcfcfcfcfcfff0fff0cc00cc00
def roots_110 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xfffefffefefefefefffafffaee00ee00fffefffefefefefefffafffaee00ee00
def roots_111 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_113 : Nat := 0x30003000300030003000300030003
def goal_113 : Nat := 0xffffaaaaffffaaaaaaaaaaaaaaaa0000ffffaaaaffffaaaaaaaaaaaaaaaa0000
def roots_113 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def goal_115 : Nat := 0xffffeeeeffffeeeeeeeeaaaaeeee0000ffffeeeeffffeeeeeeeeaaaaeeee0000
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_116 : Nat := 0x110011001100110011001100110011
def goal_116 : Nat := 0xfffff0f0fffff0f0f0f0f0f0f0f00000fffff0f0fffff0f0f0f0f0f0f0f00000
def roots_116 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_117 : Nat := 0x330033003300330033003300330033
def goal_117 : Nat := 0xfffffafafffffafafafafafafafa0000fffffafafffffafafafafafafafa0000
def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xfffffcfcfffffcfcfcfcf0f0fcfc0000fffffcfcfffffcfcfcfcf0f0fcfc0000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xfffffefefffffefefefefafafefe0000fffffefefffffefefefefafafefe0000
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_121 : Nat := 0x3030303030303030303030303030303
def goal_121 : Nat := 0xffffffaaffffaaaaffaaffaaaaaaaa00ffffffaaffffaaaaffaaffaaaaaaaa00
def roots_121 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_122 : Nat := 0x5050505050505050505050505050505
def goal_122 : Nat := 0xffffffccffffccccffccff00cccccc00ffffffccffffccccffccff00cccccc00
def roots_122 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffffffeeffffeeeeffeeffaaeeeeee00ffffffeeffffeeeeffeeffaaeeeeee00
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_124 : Nat := 0x11111111111111111111111111111111
def goal_124 : Nat := 0xfffffff0fffff0f0fff0fff0f0f00000fffffff0fffff0f0fff0fff0f0f00000
def roots_124 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xfffffffafffffafafffafffafafaaa00fffffffafffffafafffafffafafaaa00
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_126 : Nat := 0x55555555555555555555555555555555
def goal_126 : Nat := 0xfffffffcfffffcfcfffcfff0fcfccc00fffffffcfffffcfcfffcfff0fcfccc00
def roots_126 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xfffffffefffffefefffefffafefeee00fffffffefffffefefffefffafefeee00
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_137 : Nat := 0x30300000000000000000000000000000303
def goal_137 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_137 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_138 : Nat := 0x50500000000000000000000000000000505
def goal_138 : Nat := 0xffccffccffccffccffccffccffccffcccc00cc00cc00cc00cc00cc00cc00cc00
def roots_138 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_141 : Nat := 0x333300000000000000000000000000003333
def goal_141 : Nat := 0xfffafffafffafffafffafffafffafffaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_141 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

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

def dom_148 : Nat := 0x11001100000000000000000000000000110011
def goal_148 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0f0f00000f0f00000f0f00000f0f00000
def roots_148 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_149 : Nat := 0x33003300000000000000000000000000330033
def goal_149 : Nat := 0xfffffafafffffafafffffafafffffafafafa0000fafa0000fafa0000fafa0000
def roots_149 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_150 : Nat := 0x55005500000000000000000000000000550055
def goal_150 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfcfcfc0000fcfc0000fcfc0000fcfc0000
def roots_150 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_151 : Nat := 0xff00ff00000000000000000000000000ff00ff
def goal_151 : Nat := 0xfffffefefffffefefffffefefffffefefefe0000fefe0000fefe0000fefe0000
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

def dom_156 : Nat := 0x1111111100000000000000000000000011111111
def goal_156 : Nat := 0xfffffff0fffffff0fffffff0fffffff0f0f00000f0f00000f0f00000f0f00000
def roots_156 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_157 : Nat := 0x3333333300000000000000000000000033333333
def goal_157 : Nat := 0xfffffffafffffffafffffffafffffffafafaaa00fafaaa00fafaaa00fafaaa00
def roots_157 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_158 : Nat := 0x5555555500000000000000000000000055555555
def goal_158 : Nat := 0xfffffffcfffffffcfffffffcfffffffcfcfccc00fcfccc00fcfccc00fcfccc00
def roots_158 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_159 : Nat := 0xffffffff000000000000000000000000ffffffff
def goal_159 : Nat := 0xfffffffefffffffefffffffefffffffefefeee00fefeee00fefeee00fefeee00
def roots_159 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_161 : Nat := 0x30000000300000000000000000000000300000003
def goal_161 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaa00000000aaaaaaaa00000000
def roots_161 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_163 : Nat := 0xf0000000f00000000000000000000000f0000000f
def goal_163 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeeeaaaaaaaa00000000aaaaaaaa00000000
def roots_163 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_164 : Nat := 0x110000001100000000000000000000001100000011
def goal_164 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0f0f0f0f000000000f0f0f0f000000000
def roots_164 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

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
def goal_180 : Nat := 0xfffffffffffff0f0fffffffffffff0f0f0f0f0f0f0f00000f0f0f0f0f0f00000
def roots_180 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_182 : Nat := 0x5500550055005500000000000000000055005500550055
def goal_182 : Nat := 0xfffffffffffffcfcfffffffffffffcfcfcfcf0f0fcfc0000fcfcf0f0fcfc0000
def roots_182 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_183 : Nat := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
def goal_183 : Nat := 0xfffffffffffffefefffffffffffffefefefefafafefe0000fefefafafefe0000
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
def goal_188 : Nat := 0xfffffffffffffff0fffffffffffffff0fff0fff0f0f00000fff0fff0f0f00000
def roots_188 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_190 : Nat := 0x555555555555555500000000000000005555555555555555
def goal_190 : Nat := 0xfffffffffffffffcfffffffffffffffcfffcfff0fcfccc00fffcfff0fcfccc00
def roots_190 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xfffffffffffffffefffffffffffffffefffefffafefeee00fffefffafefeee00
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_202 : Nat := 0x505000000000000050500000000000005050000000000000505
def goal_202 : Nat := 0xffccffccffccffccffccffccffccffcccccccccccccccccccc00cc00cc00cc00
def roots_202 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffeeeeeeeeeeeeeeeeeeee00ee00ee00ee00
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_204 : Nat := 0x1111000000000000111100000000000011110000000000001111
def goal_204 : Nat := 0xfff0fff0fff0fff0fff0fff0fff0fff0f0f0f0f0f0f0f0f00000000000000000
def roots_204 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_205 : Nat := 0x3333000000000000333300000000000033330000000000003333
def goal_205 : Nat := 0xfffafffafffafffafffafffafffafffafafafafafafafafaaa00aa00aa00aa00
def roots_205 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_206 : Nat := 0x5555000000000000555500000000000055550000000000005555
def goal_206 : Nat := 0xfffcfffcfffcfffcfffcfffcfffcfffcfcfcfcfcfcfcfcfccc00cc00cc00cc00
def roots_206 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_207 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def goal_207 : Nat := 0xfffefffefffefffefffefffefffefffefefefefefefefefeee00ee00ee00ee00
def roots_207 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_209 : Nat := 0x30003000000000003000300000000000300030000000000030003
def goal_209 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaaaaa0000aaaa0000
def roots_209 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_210 : Nat := 0x50005000000000005000500000000000500050000000000050005
def goal_210 : Nat := 0xffffccccffffccccffffccccffffccccffffccccffffcccccccc0000cccc0000
def roots_210 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffeeeeffffeeeeffffeeeeffffeeeeffffeeeeffffeeeeeeee0000eeee0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_213 : Nat := 0x330033000000000033003300000000003300330000000000330033
def goal_213 : Nat := 0xfffffafafffffafafffffafafffffafafffffafafffffafafafa0000fafa0000
def roots_213 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfcfffffcfcfffffcfcfcfc0000fcfc0000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xfffffefefffffefefffffefefffffefefffffefefffffefefefe0000fefe0000
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_216 : Nat := 0x1010101000000000101010100000000010101010000000001010101
def goal_216 : Nat := 0xffffff00ffffff00ffffff00ffffff00ffff0000ffff00000000000000000000
def roots_216 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_217 : Nat := 0x3030303000000000303030300000000030303030000000003030303
def goal_217 : Nat := 0xffffffaaffffffaaffffffaaffffffaaffffaaaaffffaaaaaaaaaa00aaaaaa00
def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def goal_218 : Nat := 0xffffffccffffffccffffffccffffffccffffccccffffcccccccccc00cccccc00
def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffffeeffffffeeffffffeeffffffeeffffeeeeffffeeeeeeeeee00eeeeee00
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_220 : Nat := 0x11111111000000001111111100000000111111110000000011111111
def goal_220 : Nat := 0xfffffff0fffffff0fffffff0fffffff0fffff0f0fffff0f0f0f00000f0f00000
def roots_220 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def goal_221 : Nat := 0xfffffffafffffffafffffffafffffffafffffafafffffafafafaaa00fafaaa00
def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xfffffffcfffffffcfffffffcfffffffcfffffcfcfffffcfcfcfccc00fcfccc00
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffefffffffefffffffefffffffefffffefefffffefefefeee00fefeee00
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_226 : Nat := 0x500000005000000050000000500000005000000050000000500000005
def goal_226 : Nat := 0xffffffffccccccccffffffffcccccccccccccccccccccccc0000000000000000
def roots_226 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def goal_227 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeeeeeeeeeeeeeeeeeeeaaaaaaaa00000000
def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_228 : Nat := 0x1100000011000000110000001100000011000000110000001100000011
def goal_228 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000
def roots_228 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def goal_230 : Nat := 0xfffffffffcfcfcfcfffffffffcfcfcfcfcfcfcfcfcfcfcfcf0f0f0f000000000
def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def goal_231 : Nat := 0xfffffffffefefefefffffffffefefefefefefefefefefefefafafafa00000000
def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffaaffaaffffffffffaaffaaffaaffaaaaaaaaaaffaaffaaaa00aa00
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffccffccffffffffffccffccffccffccccccccccff00ff00cc00cc00
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffeeffeeffffffffffeeffeeffeeffeeeeeeeeeeffaaffaaee00ee00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_236 : Nat := 0x111100001111000011110000111100001111000011110000111100001111
def goal_236 : Nat := 0xfffffffffff0fff0fffffffffff0fff0fff0fff0f0f0f0f0fff0fff000000000
def roots_236 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xfffffffffffafffafffffffffffafffafffafffafafafafafffafffaaa00aa00
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_238 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def goal_238 : Nat := 0xfffffffffffcfffcfffffffffffcfffcfffcfffcfcfcfcfcfff0fff0cc00cc00
def roots_238 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffefffefffffffffffefffefffefffefefefefefffafffaee00ee00
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_240 : Nat := 0x1000100010001000100010001000100010001000100010001000100010001
def goal_240 : Nat := 0xffffffffffff0000ffffffffffff0000ffff0000ffff00000000000000000000
def roots_240 : List Nat := [xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_241 : Nat := 0x3000300030003000300030003000300030003000300030003000300030003
def goal_241 : Nat := 0xffffffffffffaaaaffffffffffffaaaaffffaaaaffffaaaaaaaaaaaaaaaa0000
def roots_241 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def goal_242 : Nat := 0xffffffffffffccccffffffffffffccccffffccccffffcccccccc0000cccc0000
def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffffeeeeffffffffffffeeeeffffeeeeffffeeeeeeeeaaaaeeee0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffffffcfcfffffffffffffcfcfffffcfcfffffcfcfcfcf0f0fcfc0000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffefefffffffffffffefefffffefefffffefefefefafafefe0000
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_248 : Nat := 0x101010101010101010101010101010101010101010101010101010101010101
def goal_248 : Nat := 0xffffffffffffff00ffffffffffffff00ffffff00ffff0000ff00ff0000000000
def roots_248 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffaaffffffffffffffaaffffffaaffffaaaaffaaffaaaaaaaa00
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffccffffffffffffffccffffffccffffccccffccff00cccccc00
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffeeffffffffffffffeeffffffeeffffeeeeffeeffaaeeeeee00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_252 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
def goal_252 : Nat := 0xfffffffffffffff0fffffffffffffff0fffffff0fffff0f0fff0fff0f0f00000
def roots_252 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffafffffffffffffffafffffffafffffafafffafffafafaaa00
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffcfffffffffffffffcfffffffcfffffcfcfffcfff0fcfccc00
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffefffffffffffffffefffffffefffffefefffefffafefeee00
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
def isoMvS_82:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_82:Lower true dom_82 roots_82 goal_82 4:=lower_iso_b isoMvS_82 (by decide +kernel) lowS_41
def isoMvS_84:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_84:Lower true dom_84 roots_84 goal_84 4:=lower_iso_b isoMvS_84 (by decide +kernel) lowS_41
def isoMvS_137:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_137:Lower true dom_137 roots_137 goal_137 4:=lower_iso_b isoMvS_137 (by decide +kernel) lowS_41
def isoMvS_138:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_138:Lower true dom_138 roots_138 goal_138 4:=lower_iso_b isoMvS_138 (by decide +kernel) lowS_41
def isoMvS_146:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_146:Lower true dom_146 roots_146 goal_146 4:=lower_iso_b isoMvS_146 (by decide +kernel) lowS_41
def isoMvS_148:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_148:Lower true dom_148 roots_148 goal_148 4:=lower_iso_b isoMvS_148 (by decide +kernel) lowS_41
def isoMvS_161:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_161:Lower true dom_161 roots_161 goal_161 4:=lower_iso_b isoMvS_161 (by decide +kernel) lowS_41
def isoMvS_164:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_164:Lower true dom_164 roots_164 goal_164 4:=lower_iso_b isoMvS_164 (by decide +kernel) lowS_41
def isoMvS_168:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_168:Lower true dom_168 roots_168 goal_168 4:=lower_iso_b isoMvS_168 (by decide +kernel) lowS_41
namespace S_29
def pG:List (Nat×Nat):=[(1,9),(1,17),(4,20),(5,13),(5,21),(8,9),(12,13),(12,28),(16,17),(16,20),(24,25),(24,28)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfff
def xsM:=roots_29.map (·&&&dom_29)
def gM:=goal_29&&&dom_29
def NN:Nat→Nat
|3=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x36cd4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcccc00033003300c0c0c0c22222222
|_,_=>0
def sP:Nat→Nat
|0=>0xe4
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|_,_=>0
def wAt:=mkWire dB 4 30 0x3fffffff
def SS:=mkSS wAt sP sO 2 7
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def mkPools (_ _:Nat):List (Nat×Nat×(Nat×List Nat)):=[]
def mkCut (_ _:Nat) (_:Nat×Nat×Nat) (_:List Nat):Bool:=false
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_29 gM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_29 gM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat×Nat)):=[[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_29==dom_29)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_29 gM v ys):RunD true dom_29 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_29 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s:Nat) (hs:s≤3):∀ i<NN s,bar dom_29 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 1 3=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤3) (h:RunD true dom_29 gM s xsM):False:=by
  have hmin:3≤s:=by have hl:=run_len h;change 4≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_29 roots_29 goal_29 4:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_29
theorem lowS_29:Lower true dom_29 roots_29 goal_29 4:=S_29.noCircuit
theorem lowS_43:Lower true dom_43 roots_43 goal_43 5:=lower_slice_b [(0xc0c00000c0c,8,10)] (by decide +kernel) lowS_41
theorem lowS_83:Lower true dom_83 roots_83 goal_83 5:=lower_slice_b [(0xa000a00000000000a000a,16,17)] (by decide +kernel) lowS_82
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
def isoMvS_30:List (Nat×Nat):=[(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_30:Lower true dom_30 roots_30 goal_30 4:=lower_iso_b isoMvS_30 (by decide +kernel) lowS_29
def isoMvS_45:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_45:Lower true dom_45 roots_45 goal_45 5:=lower_iso_b isoMvS_45 (by decide +kernel) lowS_43
def isoMvS_46:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_46:Lower true dom_46 roots_46 goal_46 4:=lower_iso_b isoMvS_46 (by decide +kernel) lowS_29
def isoMvS_51:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_51:Lower true dom_51 roots_51 goal_51 4:=lower_iso_b isoMvS_51 (by decide +kernel) lowS_29
def isoMvS_54:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_54:Lower true dom_54 roots_54 goal_54 4:=lower_iso_b isoMvS_54 (by decide +kernel) lowS_29
def isoMvS_57:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_57:Lower true dom_57 roots_57 goal_57 5:=lower_iso_b isoMvS_57 (by decide +kernel) lowS_43
def isoMvS_58:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_58:Lower true dom_58 roots_58 goal_58 4:=lower_iso_b isoMvS_58 (by decide +kernel) lowS_29
def isoMvS_60:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_60:Lower true dom_60 roots_60 goal_60 4:=lower_iso_b isoMvS_60 (by decide +kernel) lowS_29
def isoMvS_77:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_77:Lower true dom_77 roots_77 goal_77 4:=lower_iso_b isoMvS_77 (by decide +kernel) lowS_29
def isoMvS_78:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_78:Lower true dom_78 roots_78 goal_78 4:=lower_iso_b isoMvS_78 (by decide +kernel) lowS_29
def isoMvS_85:List (Nat×Nat):=[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_85:Lower true dom_85 roots_85 goal_85 5:=lower_iso_b isoMvS_85 (by decide +kernel) lowS_83
def isoMvS_86:List (Nat×Nat):=[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_86:Lower true dom_86 roots_86 goal_86 5:=lower_iso_b isoMvS_86 (by decide +kernel) lowS_83
def isoMvS_89:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_89:Lower true dom_89 roots_89 goal_89 5:=lower_iso_b isoMvS_89 (by decide +kernel) lowS_43
def isoMvS_90:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_90:Lower true dom_90 roots_90 goal_90 5:=lower_iso_b isoMvS_90 (by decide +kernel) lowS_43
def isoMvS_99:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_99:Lower true dom_99 roots_99 goal_99 4:=lower_iso_b isoMvS_99 (by decide +kernel) lowS_29
def isoMvS_102:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_102:Lower true dom_102 roots_102 goal_102 4:=lower_iso_b isoMvS_102 (by decide +kernel) lowS_29
def isoMvS_105:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_105:Lower true dom_105 roots_105 goal_105 5:=lower_iso_b isoMvS_105 (by decide +kernel) lowS_43
def isoMvS_106:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_106:Lower true dom_106 roots_106 goal_106 4:=lower_iso_b isoMvS_106 (by decide +kernel) lowS_29
def isoMvS_108:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_108:Lower true dom_108 roots_108 goal_108 4:=lower_iso_b isoMvS_108 (by decide +kernel) lowS_29
def isoMvS_113:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_113:Lower true dom_113 roots_113 goal_113 5:=lower_iso_b isoMvS_113 (by decide +kernel) lowS_43
def isoMvS_116:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_116:Lower true dom_116 roots_116 goal_116 5:=lower_iso_b isoMvS_116 (by decide +kernel) lowS_43
def isoMvS_141:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_141:Lower true dom_141 roots_141 goal_141 5:=lower_iso_b isoMvS_141 (by decide +kernel) lowS_43
def isoMvS_142:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_142:Lower true dom_142 roots_142 goal_142 5:=lower_iso_b isoMvS_142 (by decide +kernel) lowS_43
def isoMvS_147:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_147:Lower true dom_147 roots_147 goal_147 5:=lower_iso_b isoMvS_147 (by decide +kernel) lowS_83
def isoMvS_149:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_149:Lower true dom_149 roots_149 goal_149 5:=lower_iso_b isoMvS_149 (by decide +kernel) lowS_83
def isoMvS_150:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_150:Lower true dom_150 roots_150 goal_150 5:=lower_iso_b isoMvS_150 (by decide +kernel) lowS_83
def isoMvS_153:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_153:Lower true dom_153 roots_153 goal_153 5:=lower_iso_b isoMvS_153 (by decide +kernel) lowS_83
def isoMvS_154:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_154:Lower true dom_154 roots_154 goal_154 5:=lower_iso_b isoMvS_154 (by decide +kernel) lowS_83
def isoMvS_156:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_156:Lower true dom_156 roots_156 goal_156 5:=lower_iso_b isoMvS_156 (by decide +kernel) lowS_43
def isoMvS_163:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_163:Lower true dom_163 roots_163 goal_163 5:=lower_iso_b isoMvS_163 (by decide +kernel) lowS_43
def isoMvS_166:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_166:Lower true dom_166 roots_166 goal_166 5:=lower_iso_b isoMvS_166 (by decide +kernel) lowS_43
def isoMvS_170:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_170:Lower true dom_170 roots_170 goal_170 5:=lower_iso_b isoMvS_170 (by decide +kernel) lowS_83
def isoMvS_172:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_172:Lower true dom_172 roots_172 goal_172 5:=lower_iso_b isoMvS_172 (by decide +kernel) lowS_83
def isoMvS_177:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_177:Lower true dom_177 roots_177 goal_177 5:=lower_iso_b isoMvS_177 (by decide +kernel) lowS_83
def isoMvS_178:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_178:Lower true dom_178 roots_178 goal_178 5:=lower_iso_b isoMvS_178 (by decide +kernel) lowS_43
def isoMvS_180:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_180:Lower true dom_180 roots_180 goal_180 5:=lower_iso_b isoMvS_180 (by decide +kernel) lowS_83
def isoMvS_184:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_184:Lower true dom_184 roots_184 goal_184 5:=lower_iso_b isoMvS_184 (by decide +kernel) lowS_43
def isoMvS_202:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_202:Lower true dom_202 roots_202 goal_202 5:=lower_iso_b isoMvS_202 (by decide +kernel) lowS_43
def isoMvS_204:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_204:Lower true dom_204 roots_204 goal_204 4:=lower_iso_b isoMvS_204 (by decide +kernel) lowS_29
def isoMvS_209:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_209:Lower true dom_209 roots_209 goal_209 5:=lower_iso_b isoMvS_209 (by decide +kernel) lowS_83
def isoMvS_216:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_216:Lower true dom_216 roots_216 goal_216 4:=lower_iso_b isoMvS_216 (by decide +kernel) lowS_29
def isoMvS_226:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_226:Lower true dom_226 roots_226 goal_226 4:=lower_iso_b isoMvS_226 (by decide +kernel) lowS_29
def isoMvS_228:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_228:Lower true dom_228 roots_228 goal_228 5:=lower_iso_b isoMvS_228 (by decide +kernel) lowS_43
def isoMvS_240:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_240:Lower true dom_240 roots_240 goal_240 4:=lower_iso_b isoMvS_240 (by decide +kernel) lowS_29
theorem lowS_31:Lower true dom_31 roots_31 goal_31 5:=lower_slice_b [(0xaaaaaaaa,8,9)] (by decide +kernel) lowS_30
theorem lowS_47:Lower true dom_47 roots_47 goal_47 6:=lower_slice_b [(0xcccc0000cccc,8,10)] (by decide +kernel) lowS_45
theorem lowS_59:Lower true dom_59 roots_59 goal_59 6:=lower_slice_b [(0xc0c0c0c0c0c0c0c,8,10)] (by decide +kernel) lowS_57
namespace S_62
def pG:List (Nat×Nat):=[(2,10),(2,18),(4,20),(4,36),(6,14),(6,22),(6,38),(8,10),(8,40),(12,14),(12,28),(12,44),(16,18),(16,20),(24,26),(24,28),(24,56),(32,36),(32,40),(34,38),(34,42),(34,50),(48,50),(48,52),(48,56)]
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
|4,0=>0x1a4f618e85
|5,0=>0xaaa4e38f8b0600b
|6,0=>0xaaa4e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x5454545454545454aaaaaaaaa0a0a0a111111111111111100002a2a00002a2a5555555500000000aaaa0000aaaa000154015401540154028282828282828284444440044444400
|_,_=>0
def sP:Nat→Nat
|0=>0x43216432164328167432164216543210
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x15405
|5,0=>0x165418a6
|6,0=>0x1b5
|_,_=>0
def wAt:=mkWire dB 9 63 0x7fffffffffffffff
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
|5,0=>6
|6,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 2 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_60 4 roots_60 ops++addP pm 1 dom_58 4 roots_58 ops++addP pm 2 dom_54 4 roots_54 ops++addP pm 3 dom_46 4 roots_46 ops++addP pm 4 dom_30 4 roots_30 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_62 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_60 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_46 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_30 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_60 4 s (0,roots_60.map (·&&&dom_60)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_62 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_60 h
def symsG:List (List (Nat×Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]]
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
theorem lowS_87:Lower true dom_87 roots_87 goal_87 6:=lower_slice_b [(0xaa00aa0000000000aa00aa,16,17)] (by decide +kernel) lowS_86
theorem lowS_91:Lower true dom_91 roots_91 goal_91 6:=lower_slice_b [(0xa0a0a0a000000000a0a0a0a,8,9)] (by decide +kernel) lowS_90
def dzo_85_8:=0x330033000000000033003300
def gzo_85_8:=0x330032000000000032002200
def gsh_85_8:=0x3300320000000000320022
theorem lowS_zo_85_8_84:Lower true dzo_85_8 roots_85 gzo_85_8 5:=lower_iso_b (d1:=dom_85) (r1:=roots_85) (T1:=gsh_85_8) [(dom_85,8)] (by decide +kernel) (lower_slice_b (T:=gsh_85_8) [(0x2200220000000000220022,0,1)] (by decide +kernel) lowS_84)
namespace S_93
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(4,20),(4,68),(5,13),(5,21),(5,69),(8,9),(12,13),(12,28),(12,76),(16,17),(16,20),(16,80),(24,25),(24,28),(24,88),(64,65),(64,68),(64,80),(72,73),(72,76),(72,88)]
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
|4,0=>0xabd2d
|5,0=>0x8c59d
|6,0=>0x4011c
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x333333330000000033330000c0c0c0c000000000c0c0c0c333300000000000033330000cc00cc0000000000cc00cc02222222200000000222222220c0c0c0c000000000c0c000333333330000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x8ea1a3a84688
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
addP pm 0 dom_89 5 roots_89 ops++addP pm 1 dom_77 4 roots_77 ops++addP pm 2 dzo_85_8 5 roots_85 ops++addP pm 3 dom_85 5 roots_85 ops++addP pm 4 dom_84 4 roots_84 ops++addP pm 5 dom_29 4 roots_29 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_93 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_85_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_29 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_89 5 s (0,roots_89.map (·&&&dom_89)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_93 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_89 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)]]
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
|0,1=>0x80800000808000008080000080b030303030303030302030203020302c0c0c0c0c0c0c0c0c0c0c0c00000001010101010101010101010100000000000000000000808000000000000080b030303020202020303030302020202000000008080808000000000808080b030000030302020303000003030202
|_,_=>0
def sP:Nat→Nat
|0=>0xce1310670989519c262486709883384d724867338833d82625467080c3384d420ce134c92384d120e0709883384cf20ce6710670998459c2620cea4906132087098a418820
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|4,0=>0x26a3944a845
|5,0=>0x26b47682ced9ab2f652c8d8f2986
|6,0=>0xcab7dacb536
|7,0=>0x6a5
|_,_=>0
def wAt:=mkWire dB 24 122 0x3ffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x19130d31f90730d51130531130f698
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x52322100000011000001
|6,0=>0x918171
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
def dzo_90_32:=0x5050505000000000505050500000000
def gzo_90_32:=0x5050504000000000504050000000000
def gsh_90_32:=0x50505040000000005040500
theorem lowS_zo_90_32_82:Lower true dzo_90_32 roots_90 gzo_90_32 5:=lower_iso_b (d1:=dom_90) (r1:=roots_90) (T1:=gsh_90_32) [(dom_90,32)] (by decide +kernel) (lower_slice_b (T:=gsh_90_32) [(0x50005000000000005000500,0,8)] (by decide +kernel) lowS_82)
namespace S_122
def pG:List (Nat×Nat):=[(2,10),(2,18),(2,66),(8,10),(8,40),(16,18),(16,80),(24,26),(24,56),(24,88),(32,40),(34,42),(34,50),(34,98),(48,50),(48,56),(48,112),(64,66),(64,80),(72,74),(72,88),(72,104),(96,98),(96,104),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1ffffff
def xsM:=roots_122.map (·&&&dom_122)
def gM:=goal_122&&&dom_122
def NN:Nat→Nat
|4=>2
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x8d6485c377
|5,0=>0xb657f4097b05b3e
|6,0=>0xc00bf
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x28282828282828282828000028280000000000000000000404040404040404a0a0a0a0a0a0a0a080808080808080800000000000000014141010141410128280000282800002828000028280005050505000000000505050500000000a000a000a000a000a000a000a000a0101010101010101010101010101010128280000282800002020000020200005050505050505050000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x453204953204532804537204653243210
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x15405
|5,0=>0x166418a6
|6,0=>0x1c5
|_,_=>0
def wAt:=mkWire dB 10 123 0x7ffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x83
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x20
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 5
def pmP:Nat→Nat
|0=>0x1f41c40
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0xd1
|6,0=>4
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_90 5 roots_90 ops++addP pm 1 dom_58 4 roots_58 ops++addP pm 2 dzo_90_32 5 roots_90 ops++addP pm 3 dom_106 4 roots_106 ops++addP pm 4 dom_82 4 roots_82 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_122 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_90_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_82 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_90 5 s (0,roots_90.map (·&&&dom_90)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_122 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_90 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_122==dom_122)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_122 gM v ys):RunD true dom_122 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_122 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_122 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_122 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_122 roots_122 goal_122 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_122
theorem lowS_122:Lower true dom_122 roots_122 goal_122 7:=S_122.noCircuit
theorem lowS_143:Lower true dom_143 roots_143 goal_143 6:=lower_slice_b [(0xaaaa0000000000000000000000000000aaaa,8,9)] (by decide +kernel) lowS_142
theorem lowS_155:Lower true dom_155 roots_155 goal_155 6:=lower_slice_b [(0xa0a0a0a0000000000000000000000000a0a0a0a,8,9)] (by decide +kernel) lowS_154
namespace S_157
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,129),(4,20),(4,132),(5,13),(5,21),(5,133),(8,9),(8,136),(12,13),(12,28),(12,140),(16,17),(16,20),(16,144),(24,25),(24,28),(24,152),(128,129),(128,132),(128,136),(128,144)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffff
def xsM:=roots_157.map (·&&&dom_157)
def gM:=goal_157&&&dom_157
def NN:Nat→Nat
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x1df45
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x3333000000000000000000000000000033330000cc00cc00000000000000000000000000cc00cc03030303000000000000000000000000030303030888888880000000000000000000000008888888b333333300000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x4688
|_=>0
def sO:Nat→Nat→Nat
|6,0=>5
|_,_=>0
def wAt:=mkWire dB 5 158 0x3fffffffffffffffffffffffffffffffffffffff
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
addP pm 0 dom_156 5 roots_156 ops++addP pm 1 dom_153 5 roots_153 ops++addP pm 2 dom_149 5 roots_149 ops++addP pm 3 dom_141 5 roots_141 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_157 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_156 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_153 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_149 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_141 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_156 5 s (0,roots_156.map (·&&&dom_156)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_157 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_156 h
def symsG:List (List (Nat×Nat)):=[[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_157==dom_157)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_157 gM v ys):RunD true dom_157 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_157 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_157 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_157 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_157 roots_157 goal_157 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_157
theorem lowS_157:Lower true dom_157 roots_157 goal_157 7:=S_157.noCircuit
theorem lowS_171:Lower true dom_171 roots_171 goal_171 8:=lower_slice_b [(0xc0c00000c0c000000000000000000000c0c00000c0c,8,10)] (by decide +kernel) lowS_169
theorem lowS_233:Lower true dom_233 roots_233 goal_233 8:=lower_slice_b [(0x30300000303000000000000000000000303000003030000000000000000,1,65)] (by decide +kernel) lowS_169
def isoMvS_55:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_55:Lower true dom_55 roots_55 goal_55 5:=lower_iso_b isoMvS_55 (by decide +kernel) lowS_31
def isoMvS_61:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_61:Lower true dom_61 roots_61 goal_61 6:=lower_iso_b isoMvS_61 (by decide +kernel) lowS_59
def isoMvS_79:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_79:Lower true dom_79 roots_79 goal_79 5:=lower_iso_b isoMvS_79 (by decide +kernel) lowS_31
def isoMvS_94:List (Nat×Nat):=[(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_94:Lower true dom_94 roots_94 goal_94 7:=lower_iso_b isoMvS_94 (by decide +kernel) lowS_93
def isoMvS_103:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_103:Lower true dom_103 roots_103 goal_103 5:=lower_iso_b isoMvS_103 (by decide +kernel) lowS_31
def isoMvS_107:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)]
theorem lowS_107:Lower true dom_107 roots_107 goal_107 6:=lower_iso_b isoMvS_107 (by decide +kernel) lowS_59
def isoMvS_109:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_109:Lower true dom_109 roots_109 goal_109 6:=lower_iso_b isoMvS_109 (by decide +kernel) lowS_59
def isoMvS_110:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)]
theorem lowS_110:Lower true dom_110 roots_110 goal_110 7:=lower_iso_b isoMvS_110 (by decide +kernel) lowS_62
def isoMvS_115:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_115:Lower true dom_115 roots_115 goal_115 7:=lower_iso_b isoMvS_115 (by decide +kernel) lowS_93
def isoMvS_117:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_117:Lower true dom_117 roots_117 goal_117 6:=lower_iso_b isoMvS_117 (by decide +kernel) lowS_91
def isoMvS_118:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_118:Lower true dom_118 roots_118 goal_118 7:=lower_iso_b isoMvS_118 (by decide +kernel) lowS_93
def isoMvS_124:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_124:Lower true dom_124 roots_124 goal_124 7:=lower_iso_b isoMvS_124 (by decide +kernel) lowS_122
def isoMvS_151:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_151:Lower true dom_151 roots_151 goal_151 6:=lower_iso_b isoMvS_151 (by decide +kernel) lowS_87
def isoMvS_158:List (Nat×Nat):=[(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_158:Lower true dom_158 roots_158 goal_158 7:=lower_iso_b isoMvS_158 (by decide +kernel) lowS_157
def isoMvS_167:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_167:Lower true dom_167 roots_167 goal_167 6:=lower_iso_b isoMvS_167 (by decide +kernel) lowS_143
def isoMvS_173:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_173:Lower true dom_173 roots_173 goal_173 8:=lower_iso_b isoMvS_173 (by decide +kernel) lowS_171
def isoMvS_174:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_174:Lower true dom_174 roots_174 goal_174 7:=lower_iso_b isoMvS_174 (by decide +kernel) lowS_157
def isoMvS_179:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_179:Lower true dom_179 roots_179 goal_179 7:=lower_iso_b isoMvS_179 (by decide +kernel) lowS_157
def isoMvS_182:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_182:Lower true dom_182 roots_182 goal_182 7:=lower_iso_b isoMvS_182 (by decide +kernel) lowS_157
def isoMvS_185:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_185:Lower true dom_185 roots_185 goal_185 8:=lower_iso_b isoMvS_185 (by decide +kernel) lowS_171
def isoMvS_186:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_186:Lower true dom_186 roots_186 goal_186 7:=lower_iso_b isoMvS_186 (by decide +kernel) lowS_157
def isoMvS_188:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_188:Lower true dom_188 roots_188 goal_188 7:=lower_iso_b isoMvS_188 (by decide +kernel) lowS_157
def isoMvS_203:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_203:Lower true dom_203 roots_203 goal_203 6:=lower_iso_b isoMvS_203 (by decide +kernel) lowS_91
def isoMvS_205:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_205:Lower true dom_205 roots_205 goal_205 6:=lower_iso_b isoMvS_205 (by decide +kernel) lowS_59
def isoMvS_206:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_206:Lower true dom_206 roots_206 goal_206 6:=lower_iso_b isoMvS_206 (by decide +kernel) lowS_59
def isoMvS_211:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_211:Lower true dom_211 roots_211 goal_211 6:=lower_iso_b isoMvS_211 (by decide +kernel) lowS_155
def isoMvS_213:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_213:Lower true dom_213 roots_213 goal_213 6:=lower_iso_b isoMvS_213 (by decide +kernel) lowS_155
def isoMvS_214:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_214:Lower true dom_214 roots_214 goal_214 6:=lower_iso_b isoMvS_214 (by decide +kernel) lowS_155
def isoMvS_217:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]
theorem lowS_217:Lower true dom_217 roots_217 goal_217 7:=lower_iso_b isoMvS_217 (by decide +kernel) lowS_157
def isoMvS_218:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccccccccccccccccccccccccccc,126),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_218:Lower true dom_218 roots_218 goal_218 7:=lower_iso_b isoMvS_218 (by decide +kernel) lowS_157
def isoMvS_220:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_220:Lower true dom_220 roots_220 goal_220 7:=lower_iso_b isoMvS_220 (by decide +kernel) lowS_93
def isoMvS_227:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)]
theorem lowS_227:Lower true dom_227 roots_227 goal_227 6:=lower_iso_b isoMvS_227 (by decide +kernel) lowS_59
def isoMvS_230:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_230:Lower true dom_230 roots_230 goal_230 6:=lower_iso_b isoMvS_230 (by decide +kernel) lowS_59
def isoMvS_234:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_234:Lower true dom_234 roots_234 goal_234 7:=lower_iso_b isoMvS_234 (by decide +kernel) lowS_93
def isoMvS_236:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_236:Lower true dom_236 roots_236 goal_236 7:=lower_iso_b isoMvS_236 (by decide +kernel) lowS_93
def isoMvS_241:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]
theorem lowS_241:Lower true dom_241 roots_241 goal_241 7:=lower_iso_b isoMvS_241 (by decide +kernel) lowS_157
def isoMvS_242:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_242:Lower true dom_242 roots_242 goal_242 7:=lower_iso_b isoMvS_242 (by decide +kernel) lowS_93
def isoMvS_248:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_248:Lower true dom_248 roots_248 goal_248 7:=lower_iso_b isoMvS_248 (by decide +kernel) lowS_122
namespace S_63
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(2,10),(2,18),(3,11),(3,19),(3,35),(4,20),(4,36),(5,13),(5,21),(5,37),(6,14),(6,22),(6,38),(7,15),(7,23),(7,39),(8,9),(8,10),(8,40),(12,13),(12,14),(12,28),(12,44),(16,17),(16,18),(16,20),(24,25),(24,26),(24,28),(24,56),(32,33),(32,36),(32,40),(34,35),(34,38),(34,42),(34,50),(48,49),(48,50),(48,52),(48,56)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_63.map (·&&&dom_63)
def gM:=goal_63&&&dom_63
def NN:Nat→Nat
|4=>5
|5=>16
|6=>36
|7=>9
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xf4716c32efbb27373fbb5be7f
|5,0=>0xca973ca592c802ebffb2b08c8ae63f9be199981895e6384f7c7079e60bbe34cda2a5990cd48086b9
|6,0=>0xf131fe3250dd808d6184cf6b2ce108b40d5a9467a33d79d4fa9c2ed908be8d95f8ad1584f7c81958785bc78555754dd7314b72b0e6ed14692a46324a5a9d257b684d9543a92e39e34362712b4e324193077970481104701028d7
|7,0=>0xdd808ba6a9b12a65f7114017b2a68d29ed4297201fb9e
|8,0=>0xc6758
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f0f0f0fff0fff0fff0f0f0f0f0ffffffff00000000ff00ff00ff00ff00555555555555550000ff00ffffffff000000ffff0000ff00ffffffffffffff00ffff0000ffff0000ffccffccccccccccaaaaaaaaaaaaaaaaffffffffffff0000ffffff00ffffff00ffaaffaaaaaaaaaaf0f0f0f0f0f0f0f0cccccccccccccccc
|0,1=>0x3333333300000000cc00cc00ff00ff0000000000ffccffcc0000000033003300ff000000ff00ff00ffffffffccccccccf0fff0fff0f0f0f03333000033333300ffffff0000000000ffffffffff00ff0000ff00ffff00ff0000ff00ff0000000000000000ffffff00ffffff00ffff0000ff00ff00000000000f0f0f0f0f0f0f00
|0,2=>0xfffffffffff0fff0333333003333330000cc00cccccccccc00000000ff00ff00000000ff000000000f0f0f0f0f0f0000ffffffff330033000000ff000000ff0000ff00ff00ff0000ffccffccffccffccff33ff33ff00ff000000ffff00000000ccccffffccccccccffff0000ffffff00ffff3333ffff00000f0f0f0f0f000f00
|0,3=>0xf000f000f000f003300330033003300fff0fff0fff0fff0ff00ff00ff00000000ff0000ffff0000ff00ffffff00ff00
|_,_=>0
def sP:Nat→Nat
|0=>0x53473190401561c20403431c60451d10401492074410055870401553473011581173010051c10055470401544cd48c0401441c23010040d104014d1cc00540d1cc3c014d0c738014d1cc0402c704014a1c20402481c20401031811440c2040
|1=>0x529347301005347040154a041cc4410053473010059cd1c630114434330100568d1e630114d1e530100534708c0403473018c55873010057cd88730100536130100534730100580d1cc04078534730100574d1cc04015c34731b040156687301
|2=>0x17534730100550d1cc040174347ccc04014d4873010053473320401563473010053473010052561d104014834730100534c040171347c0c04016f3473010053431cc045b8d1cc045b47040154b0d1cc04016b34730016a3523010053431c1005
|3=>0x34730100558d1cc04014d0c7301005347301005a0d1cc44100534798c04014d1cc040
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x14507a82940aa005
|5,0=>0x3929b18ccc6062d315189cc49521b0f586ec31615b09583ec196
|6,0=>0xb13d6dea8f4d7a3b501e74d337963c95e3ed196893c31a0ccff77c3bc5dd4ee376eb359d9eec876132f196aeae7543285d34e937463a15cfce777
|7,0=>0x1a17cd3e4df18f857bf3dddee0f697
|8,0=>0x1a86
|_,_=>0
def wAt:=mkWire dB 54 64 0xffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x34c47311cc8d303004c0730d8c033014d3034c561d34c474734c0c910c0c7314408d3034c8c36343c4071cd474534c0c3630d0c124404d30024473634c877d340cc7f34c564734c0d31
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x300000000000000000000
|6,0=>0x7c9d26c9a100182589424c5123c8e100000344c1288000000000082000711480010400000000c400
|7,0=>0x291a0671986519063188611
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 10
def pmP:Nat→Nat
|0=>0xeb5d3d7756f16b553d4f543d1101000c10c004003002802102001800e00d005004002001000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x10000000010000000000
|6,0=>0x602392a02c2560428001082b5e03040c080e000200
|7,0=>0x1194af6a4ed8
|8,0=>0x15
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 12 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_62 7 roots_62 ops++addP pm 1 dom_54 4 roots_54 ops++addP pm 2 dom_55 5 roots_55 ops++addP pm 3 dom_31 5 roots_31 ops++addP pm 4 dom_61 6 roots_61 ops++addP pm 5 dom_47 6 roots_47 ops++addP pm 6 dom_45 5 roots_45 ops++addP pm 7 dom_43 5 roots_43 ops++addP pm 8 dom_29 4 roots_29 ops++addP pm 9 dom_57 5 roots_57 ops++addP pm 10 dom_59 6 roots_59 ops++addP pm 11 dom_51 4 roots_51 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_63 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_47 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_29 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_51 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_62 7 s (0,roots_62.map (·&&&dom_62)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_63 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_62 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_63==dom_63)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_63 gM v ys):RunD true dom_63 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_63 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 5 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 36 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 36 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 9 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 9 0 = true)
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
theorem lowS_95:Lower true dom_95 roots_95 goal_95 8:=lower_slice_b [(0xaaaaaaaa00000000aaaaaaaa,8,9)] (by decide +kernel) lowS_94
theorem lowS_123:Lower true dom_123 roots_123 goal_123 9:=lower_slice_b [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,8,10)] (by decide +kernel) lowS_121
def dzo_82_32:=0x50005000000000005000500000000
def gzo_82_32:=0x50004000000000004000000000000
def gsh_82_32:=0x500040000000000040000
theorem lowS_zo_82_32_82:Lower true dzo_82_32 roots_82 gzo_82_32 4:=lower_iso_b (d1:=dom_82) (r1:=roots_82) (T1:=gsh_82_32) [(dom_82,32)] (by decide +kernel) (lower_slice_b (T:=gsh_82_32) [] (by decide +kernel) lowS_82)
def dzo_84_8:=0x110011000000000011001100
def gzo_84_8:=0x110010000000000010000000
def gsh_84_8:=0x1100100000000000100000
theorem lowS_zo_84_8_84:Lower true dzo_84_8 roots_84 gzo_84_8 4:=lower_iso_b (d1:=dom_84) (r1:=roots_84) (T1:=gsh_84_8) [(dom_84,8)] (by decide +kernel) (lower_slice_b (T:=gsh_84_8) [] (by decide +kernel) lowS_84)
def dzo_118_8:=0x55005500550055005500550055005500
def gzo_118_8:=0x55005500550054005500550054004400
def gsh_118_8:=0x550055005500540055005500540044
theorem lowS_zo_118_8_84:Lower true dzo_118_8 roots_118 gzo_118_8 6:=lower_iso_b (d1:=dom_118) (r1:=roots_118) (T1:=gsh_118_8) [(dom_118,8)] (by decide +kernel) (lower_slice_b (T:=gsh_118_8) [(0x440044004400440044004400440044,0,2),(0x550055000000000055005500000000,0,32)] (by decide +kernel) lowS_84)
def dzo_116_8:=0x11001100110011001100110011001100
def gzo_116_8:=0x11001100110010001100110010000000
def gsh_116_8:=0x110011001100100011001100100000
theorem lowS_zo_116_8_84:Lower true dzo_116_8 roots_116 gzo_116_8 5:=lower_iso_b (d1:=dom_116) (r1:=roots_116) (T1:=gsh_116_8) [(dom_116,8)] (by decide +kernel) (lower_slice_b (T:=gsh_116_8) [(0x110011000000000011001100000000,0,32)] (by decide +kernel) lowS_84)
def dzo_86_8:=0x550055000000000055005500
def gzo_86_8:=0x550054000000000054004400
def gsh_86_8:=0x5500540000000000540044
theorem lowS_zo_86_8_84:Lower true dzo_86_8 roots_86 gzo_86_8 5:=lower_iso_b (d1:=dom_86) (r1:=roots_86) (T1:=gsh_86_8) [(dom_86,8)] (by decide +kernel) (lower_slice_b (T:=gsh_86_8) [(0x4400440000000000440044,0,2)] (by decide +kernel) lowS_84)
def dzo_94_32:=0x55555555000000005555555500000000
def gzo_94_32:=0x55555554000000005554555000000000
def gsh_94_32:=0x555555540000000055545550
theorem lowS_zo_94_32_82:Lower true dzo_94_32 roots_94 gzo_94_32 6:=lower_iso_b (d1:=dom_94) (r1:=roots_94) (T1:=gsh_94_32) [(dom_94,32)] (by decide +kernel) (lower_slice_b (T:=gsh_94_32) [(0x505050500000000050505050,0,4),(0x550055000000000055005500,0,8)] (by decide +kernel) lowS_82)
namespace S_126
def pG:List (Nat×Nat):=[(2,10),(2,18),(2,66),(4,20),(4,36),(4,68),(6,14),(6,22),(6,38),(6,70),(8,10),(8,40),(12,14),(12,28),(12,44),(12,76),(16,18),(16,20),(16,80),(24,26),(24,28),(24,56),(24,88),(32,36),(32,40),(34,38),(34,42),(34,50),(34,98),(48,50),(48,52),(48,56),(48,112),(64,66),(64,68),(64,80),(72,74),(72,76),(72,88),(72,104),(96,98),(96,100),(96,104),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_126.map (·&&&dom_126)
def gM:=goal_126&&&dom_126
def NN:Nat→Nat
|4=>2
|5=>15
|6=>56
|7=>31
|8=>8
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x5d88e38c7c
|5,0=>0xe291dc215da302184f13820cf593754d201445593dccf3be3b377e72096712fce0902b02636
|6,0=>0xf7ea9e53b0de404d0a48c4a489eb089dd0580cdc7d2707d0ee7beb57aa05754937377a6429a62dc060e4957a5b5296b48e7b44559425e241c3f3d50f3d04c3b653385673432c30c9b2fc482af07280b02751925e0a2362b219be1ea341d01c1a4f119c37180b6178f31609015115131f9110bc0f9c00a0900898907339070f80337502dbd02c5e0272301e03
|7,0=>0xe14d2d5098d4a31a38afa19388bf7382d2d6a43f51bab466723d88f3c9b43600c318fa24c0823b971ed7c1a6b218c08166b91415b139e412ebf10ea90e4f10dc370c93508e8b06b3c048a3007f0
|8,0=>0xf47f0c9098524f449279464f43188f25b0e00935
|9,0=>0x464f4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaaaaaaaaaaaaaaaaa8a8a8a8a8a8a8a955551111555511115555111155551110282828282828282820202020202020255550000555500005555000055550000a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a11111111111111111111111111111111008000800080008000802a8000802a8055555555555555550000000000000000aaaaaaaaaaaaaaaaaaaa0000aaaa000151515151515151515151515151515152aaaa2222aaaa222282820202828202055555555000000005555555500000000aaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a154015401540154015401540154015402a2a2a2a2a2a2a2a2a2a00002a2a000055555555555555554444444444444444
|0,1=>0xaaaaa0a0aaaaa0a155555555555555555555414155554142aaaaa2a2aaaaa2a2aaaaa2a2aaaaa2a00000000000000005555545455555454aaaaaaaa22222222aaaaaaaa2222000141414140404040414141414040400000880888088808880888088800880888044444444444444444444444044444440aaaaaaaaaaaaaaaaa0a0a0a0a0a0a0a1555555555151515155555555515000000002aaa80002aaa80002a2a00002a2a111111111111111111111110111111100000a8a80000a8a80000a8a80000a8a955555151555551500000000000000002aa82aa8000000002aa82aa80000000005050505050505050505000005050000
|0,2=>0x8888aaaa8888aaaa8888a8a88888a8a8000000000000000000015150000151528a8a8a8a8a8a8a8a8a8a82828a8a828505050505050505055555550555555500000000000000000a8a8a8a8a8a8a8a95555555555555554141414001414140000000000000000008888808088888085555555544444444555555554444444400aa00aa0088008800aa00aa0088008844444444444444444040404040404042aaa8282aaaa8282aaaa82022aaa820255505550555055505550555055505550aaaa0000aaaa0000a8a80000a8a8000154015401540154015555554155555542aaaaaaaaaaaaaaaaaaaaa802aaaaa8044444444444444444444440044444400
|0,3=>0xaaaaaaaaaaaaaaaaaaaaa8a8aaaaa8a955540155555401555554014155540142aaa80002aaa80002aaaaa2a2aaaaa2a0000000000000000050505000505050088888888aaaaaaaa88888888aaaa888801540154015401540154000001540002a802a80000000002a802aaa8000000055555555555500005555555555550000aaaaaaaaaaaa000088888888888800000001555400015554000155400001554002a802a802a802a802a8028002a8028050505050505050505050404050504042222222222222222222222222222000155555555555555555555555555551112aaaaa802aaaaa802aaaaa802aaaaa8000005555000055550000505000005050
|0,4=>0x555555555500550055555555550055000000000000000000aaaaaaaaaaaa000000000001555555540000000155540002aaaaaaaaaaaaaaaaaaaa2222aaaa222050505000505050005050500050505000000aaaa0000aaaa000088880000888955555555414141415555555541414142aaaaaa82aaaaaa82aaaaaa82aaaaaa8000000005555444400000000555544440202020202020202020200000202000155555555555555555555555555540000282828282828282828282828282800055005500555555555500550055555500
|_,_=>0
def sP:Nat→Nat
|0=>0x8746022e284043a70602162820e0e0830b106c20c042c50808301060a2020c046850808383820c5c20c042cc88083010b3020207042c28a2c3010b14202021628a88083010b28202021628992184410a202020e0e0878b0830101160020e0e0858d083058a122020704182840608080
|1=>0xc2c504180832b2e2820c042c52a101038c043c58a083010b14a44040e3058a4e2038c220858a101018c0429308087460216289040e3010b4020225180858a1010624042880808083231628404443010b142020c042d008087060216284043e301061420207180858a1a10f0c0418508
|2=>0x80918b1420202465c58a10106021629b08083010b14d4404180808b14202021628a880808b8b14544041809597162820c042c5341010602162998864106021628404620858a602020c042d78a10106021629708083012d1628404583010b142020e180831710106022e289880870602
|3=>0x42c508083010b1510404421c60216284040e301061628404180858a86202030e08b8a083010b0a284040e3010a822020c042a08808383822e2c504190058a1010e82162898808fc60216284047c3010b142023d180858a10106021629e08083010b762840c720858a10106021629b88
|4=>0x8c1038c042c508083010b1440404180858a942020e0e0858a1012487180858a101070c045c58a10e020c042c00a101018c0418508092460216284048a3010b142021e063010b142020c042c5481010602162a3888c1070c042c508083058a4e20611042c508501038c042c508091418c
|5=>0x180830b1422604180858a101038c042c50808c46021628404180858a111820c042c50808386021628428083010b1422104180858a1130207180858a1010602562c508083010f162840418087971628404180858a1a2020c041958b14202031808b8a10106021e1858a112c20c042c508
|6=>0x106021628404
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x154005
|5,0=>0x5e61618526131846610183a60d182e60a18226071816604180a6
|6,0=>0x779dd86745dca77119bd76dd9b076a5da2766dd947635d876601d7a65cdd6c7595d5e75619517529d4374f1d3574b9d277481d197449d0b7411cfd73d9cef73a1ce17369cd37331cc572f9cb772c1ca97289c9c6255c8e721dc8071e5c7271adc647
|7,0=>0x2c37aee2b47ab5ea58a79e968a3de878a01e7889c5e6a798de5b894e24b8911e3d78d9e2e889de2078622126831a0487f21f577b61e58
|8,0=>0xbe9ef37bb1ee57b7dad87b45eca7
|9,0=>0x3016
|_,_=>0
def wAt:=mkWire dB 77 127 0x7fffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 14
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xe0b182170001421183c0c211629183c2e290e1816291821183e2e291e232e29162118212e3316212e3316210c2316290c33142d10760c31142d0c211629500b08294810042d182142280e090e2f1821183c0c211629062342280e09182106231631002f142106211631062916310c3116291c5c162114310c2116290e181629
|1=>0x1629162116310c211629702308311821082d0e2f18210e131821143110310e29182116211431083114211631142d0e291821040d163106211631622f0431003314211431082d500b08294810042d08291821040d1631083a14310e091821162918211821162116311c5c16211431842f0e1126310c330c231629625f162108eb
|2=>0x1629080918210431082d143108290e111821080918210c2316290c2116292e291621002f14210c23
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x43000000000000000022002000000
|6,0=>0x4c34934720000000004520000004324120003e33c23933720000003430003222f30000002e12c22a22820000000002622422310002120001f21c30000001a20001821531411130000f20d20b2092072000000
|7,0=>0x8b28928728528328127f27d27b27927727527327126f26d26b26926726526326125f25d25b25925725525325124f2
|8,0=>0x9319219119010008f18e18d1
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 12
def pmP:Nat→Nat
|0=>0x12c13808709c04314e018083009010804801401b04e00a064004c13801819800804c002021000e00800609c00304600180600061100020000006000000c10000138000094000046000021000010000006000000c0000050000020000008000002000000
|1=>0x440300918304e881022440010931609c54b84e200c020b0e1384030e01cb24e0c5827052c13820440c102006061c3f030e1380e629c06f04e035827018c1380a021c04b84e025863
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x140000000083000
|6,0=>0x1514200000c00008e0100891c000b00750000d3810800000c10c008008f0000803841930010810c3000
|7,0=>0x2cc1f95b90a59acb466c89c229826a18be3ce17aababd8b
|8,0=>0x7f15e747576d
|9,0=>0x12
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 25 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_124 7 roots_124 ops++addP pm 1 dom_110 7 roots_110 ops++addP pm 2 dom_62 7 roots_62 ops++addP pm 3 dom_82 4 roots_82 ops++addP pm 4 dzo_82_32 4 roots_82 ops++addP pm 5 dom_122 7 roots_122 ops++addP pm 6 dom_106 4 roots_106 ops++addP pm 7 dom_108 4 roots_108 ops++addP pm 8 dom_84 4 roots_84 ops++addP pm 9 dzo_84_8 4 roots_84 ops++addP pm 10 dzo_118_8 6 roots_118 ops++addP pm 11 dom_118 7 roots_118 ops++addP pm 12 dom_94 7 roots_94 ops++addP pm 13 dom_58 4 roots_58 ops++addP pm 14 dzo_90_32 5 roots_90 ops++addP pm 15 dom_46 4 roots_46 ops++addP pm 16 dom_60 4 roots_60 ops++addP pm 17 dzo_116_8 5 roots_116 ops++addP pm 18 dzo_86_8 5 roots_86 ops++addP pm 19 dzo_94_32 6 roots_94 ops++addP pm 20 dom_102 4 roots_102 ops++addP pm 21 dom_86 5 roots_86 ops++addP pm 22 dom_78 4 roots_78 ops++addP pm 23 dom_90 5 roots_90 ops++addP pm 24 dom_54 4 roots_54 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_126 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_zo_82_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_108 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_84_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_118_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_90_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_46 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_60 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_116_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_86_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_zo_94_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_78 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_54 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_124 7 s (0,roots_124.map (·&&&dom_124)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_126 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_124 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_126==dom_126)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_126 gM v ys):RunD true dom_126 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_126 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 15 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 56 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 56 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 31 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 31 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 8 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 0 = true)
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
theorem lowS_159:Lower true dom_159 roots_159 goal_159 8:=lower_slice_b [(0xaaaaaaaa000000000000000000000000aaaaaaaa,8,9)] (by decide +kernel) lowS_158
theorem lowS_175:Lower true dom_175 roots_175 goal_175 9:=lower_slice_b [(0xcccc0000cccc00000000000000000000cccc0000cccc,8,10)] (by decide +kernel) lowS_173
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
|0,1=>0xf0f0f0f0f0e0f0e00000000000000000f0f0f0f00000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f00000000f0f0f0f0f0f0f0a00000000000000000f0f0f0f00000000f0f0f0f0f0f0f0c00000000000000000c0c0c0c0c0c0c0c00000000000000000000000000000000f0f0f0a0f0f0f0af0f0f0f0f0f0f0f00000000000000000e0e0e0e0e0e0e0ef0a0f0a0f0a0f0a00000000000000000f0a0f0a0f0a0f0a10101010101010100000000000000000101010001010100f0a0f0f0f0a0f0f00000000000000000f0a0f0a0f0a0f0af0f0f0a0f0f0f0a00000000000000000f0f0f0a0f0f0f0ae0e0e0e0e0e0e0e00000000000000000e0e0e000e0e0e0050505050505050500000000000000000504050405040504f0f00000f0f000000000000000000000f0f00000f0f0000f0f0f0f0f0f0f0f00000000000000000f0a0f0a0f0a0f0a00000000f0f0f0f0000000000000000000000000f0a0f0af0f0f0f0f0f0e0e00000000000000000f0f00000f0f0000
|0,2=>0xf0f00000f0f000000000000000000000e0e00000e0ef000f0f0f000f0f00000000000000000f000f0e0f000f0e00000000000000000000000000000000f0e0f0e0f0e0f0e0000f0f00000f0f000000000000000000000f0f00000e0e00f000f000000000000000000000000000f000f0000000000000000f0f0f0f0000000000000000000000000f0f0f00f0b0f0b0f0b0f0b00000000000000000f0a0f0a0f0a0f0a10101010101010100000000000000000000000000000000f0f0f0f0e0e0e0e00000000000000000f0f0f0f0e0e0e0e5050505050505050000000000000000050505000505050010101010101010100000000000000000100010001000100f0e0f0e0f0e0f0e00000000000000000f0e0f0e0f0e0f0ef0e0f0e0f0e0f0e00000000000000000000000000000000a0a0a0f0a0a0a0f00000000000000000a0a0a0a0a0a0a0a00f000f000f000f0000000000000000000f000f000f0000f0f0f0f0e0e0e0e00000000000000000a0a0a0a0a0a0a0a
|0,3=>0xf0f0f0f0f0f0f0f00000000000000000f0e0f0e0f0e0f0ea0b0a0b0a0b0a0b00000000000000000a0a0a0a0a0a0a0aa0a0a0a0f0f0f0f00000000000000000a0a0a0a0e0e0e0ef0f0f0f0f0f0f0000000000000000000000000000000000f0f0f0f0000000f00000000000000000f0f0f0f00000000000000f0000000f00000000000000000000000000000000f0f0f0f0e0e0e0e0000000000000000000000000000000000f000f000f000f0000000000000000000f000f000e000e0000e0e00000f0f000000000000000000000e0e00000e0e00000000000000000000000000000000f0f0f0f0e0e0e0ef010f010f010f0100000000000000000f000f000f000f00a0a0a0a0b0b0b0b00000000000000000a0a0a0a0a0a0a0a00f000f0000000f0000000000000000000f000f00000000000000f0000000f00000000000000000000000f00000000f000f0f0f000f0f00000000000000000f000f0f0f000f0050505050000000000000000000000000505050500000000
|0,4=>0xa0f0a0f0a0f0a0f00000000000000000a0a0a0a0a0a0a0af0f0f0f0a0a0a0a00000000000000000f0f0f0f0a0a0a0a00000000f0f0f0f00000000000000000000000000000000f000f000f0f0f0f00000000000000000f000f000f000f0050505050505050500000000000000000500050005000500f0f0f0f0f0f0f0f0000000000000000000f000f00000000f0f0f0a0f0f0f0a0000000000000000000000000000000000f000f000f000f00000000000000000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f000f00101010101010101000000000000000001010101000000005050505050505050000000000000000050505050000000030303030303030300000000000000000303030003030300f0f0f0e0f0f0f0e00000000000000000c0c0c0c0c0c0c0c0000e0f00000e0f000000000000000000000e0e00000e0e3030303030303030000000000000000030303020303030200000000f0f0f0f0000000000000000000000000f0e0f0e
|0,5=>0x5050505050505050000000000000000000000000000000000100010001000100000000000000000000000000000000f0f0f0f0f0f0f0000000000000000000f0f0f0f0f0f0f00e0f0e0f0e0f0e0f00000000000000000e0e0e0e0e0e0e0e000000f0000000f00000000000000000000000a0000000a0000000010101010000000000000000000000000000000000000000000000000000000000000000f0f0f0f00000000f0f0f000f0f0f0f00000000000000000f0f0f000f0f0f00f0f0f0f0f000f0000000000000000000f0f0f0f0f000f00f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f00f0f0f0e0f0f0f0e00000000000000000f0f0f0e0f0f0f0e00000000f0f0f0f0000000000000000000000000e0e0e0ef0f0f0f0a0a0a0a00000000000000000a0a0a0a0a0a0a0af0f0f0f000000000000000000000000000000000000000000000000f0f0f0f00000000000000000f0f0f0f0000000000f000f000f000f0000000000000000000f000f00000000
|0,6=>0x50005000500050000000000000000000000000000000000000000f0f0f0f0000000000000000000000000a0a0a0aa0a0a0a0f0f0f0f00000000000000000a0a0a0a0a0a0a0a00000000f000f0000000000000000000f000f000f000f00f0f0f0f000f000f00000000000000000f0f0f0f00000000f0f0f0f0c0c0c0c00000000000000000c0c0c0c0c0c0c0cf0f0f0f0f0f0f0f00000000000000000f0f0f0f0a0a0a0aa0a0a0a0f0f0f0f00000000000000000000000000000000f0f0f0f0f000f0000000000000000000f000f000f000f00f0f0f0f0f0f0f0f0000000000000000050505050000000000000000505050500000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x12080a21a10486168468914185911a10488022c6841264a8d3c4c101407c98a022cf09041829d122830b081c11c1610d89140420304685841264c0d0824b811a10b022a342090250689240488d0840101001048f0c002091c04684140460b08245060a10488020020704182840608080
|1=>0xc0022e040458d084d6820200202022d60d084c101008c209326808d0840101163448616ad50d084d482023421332280a808241151634209041828d08249011a1048f0c2c6a73c4c101001048e0c2c68412643261a104811694684262808b461098202506841220300164c9020244684
|2=>0x26080bd1a104ad022c69e120830b78ec48616ac68412280801a109a4146858412280800824c811ae82130404039084c08b7034202022db8d08252010034213040500d6c10982020021332d408d082451a022c2130405a0d082490a02342090c2d98d0825886163420202c178d081c499
|3=>0x163421304045c61a109a4040400d3c109820c02293240830b2234202022d78d0824106442c68412645c41a10482862c6840e0830b7810101170868412085c11a10b09141801d120830b1a4c10117006842c1c1011a104bf022c684122808b5010482166068426080be1a10982342d184
|4=>0x26080cf1b38f13041a28d082660616342090c2e58d76104820c2c693041800b2234213320808d50104990234207126430b1a10982020240426b4101163421314080801a104861728684262810100104920c2c6842608d016034209041858d929cf13040458d084c11a022e4470824506
|5=>0x141858d08244061634f13041a984122830b9a1048a022c684260808b1ae4f04122830b3d449820c2c209046808b1a109bf040458d082430b5635d0426080c51a1098a04045a83c104861740684262830ba035b04260808b1a104a4022c684120830b4c34209321800d082490a0c2c684
|6=>0xb80458d0824906002c6d73c4c506163420904185db1a10982022c6daa24c106167898202c0684b0241061636b9e262830bac104820c2c684120808b1ae8255120808b1a10389042e20d4e10982020069304185911a109a4046858d081c4820c005c7084c30ba03421304045d41a78209
|7=>0x84c101163641e084c106172021314083001634213040580d084f106163421304185e11a78213140830b1a1098a041800b084c5020c2e684260830b1b80213140808b1a78213140830b084c5020c2ef8426645060034213322830008584820c00684260808b1b7ae840e0830b1a10982
|8=>0x41b40b1a9c213040458d084c9020c0058d0824106163669e08241061634213ce1858d08241011634f1304185ab1b98213041858d084c10617146d9260830b9a10982ca2c6e4084c1061634213041a78b1a109820c2c6e3084c10116354473c109820c2c684126430b1b5c213141858d
|9=>0x84c106163640426281061636b84260830b1a109820c2c6d2084c10616c069e084c106171469e084c106163421304185cb1a10999141858d081c4820c2c68426481061634209141858dae789820c2c6842c24106163638426281061634f1304185d2084c1061637504260830bd234213
|10=>0x84c1061634213041858d9a78213041858d084cc820c2c684120830b1a12c93041858d
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
|0=>0x16350235082f0c2d2c34122d2609080508350c2d2609043516350c2d3c2f08350435344f02350c2d123626091635140504350c2d4834483704352609043502350c2d123626090c2d4e3416352609260904c93c270835123516352609483426090236021c123526090435260908050835002748340c2d04351236043526090027
|1=>0x26093c2f0c2d083502360c2d3c0b260908358e0b082904354e370805020926090c2d0e2f123526091635042d2609260904350c2d172104363c2f0835053508362609142f2609043508e91236084a000902360c2d0c2d042d26091235042d260904360c2d16354837020904350c2d16355635080b26090c2d1635043526090009
|2=>0x82f08351335083626090835043508093c2526090835123626090c2d120526090e1b123526091635084a142d043502350c2d1635123526093c0b3c090835086a023508352609043504e912362609174908340835043508362609043526090c2d4e3408050c2d2609083504353d4b0834083502350c2d2609483502090c2d1236
|3=>0x8370d4908349c35082d172104366036082f02360c2d0835042d2609043508090c2d04360835043616350435082f0c2d054908346035082f0835043516350435083604359c36082d0c2d043508350435043516361635042d0435042d16350435163512350825260903210c2d043626090009163508350809b335083608370c2d
|4=>0x8360835042d260908370436043508090834082f3c2f0835b2350837142f0435042d043512352609142d04352609043508350809122d260908290435083408353236042d080216351735083608050c2d000916350836260926090835054b08340c2d2609080b0835092104363c2f08350836
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
|0=>0x2074008100018240043000102000400000e7c00395000c5400300000a7c002400008b800220000864002000004000008600021000070000180000400000c0000200000400000c000020000050000100000200000400000
|1=>0xe8640390500e0740381000c8e40321f00c86c0321900c0400300000a87c02a1b00a8080220f00880002113008400020290068fc01a1d004cfc0131f004c740121b00404400c00002a7400a3b00287c00a10002800008bc
|2=>0x5287414a10050a7c1429404c0a01221f0428f010a1004087c0c317020c7c0810001e4540781d01e0400701001a06c05b1d0168740591901404005001012a7404294010a3c0428401087c0401100ec7403a1f00e87403a1b
|3=>0xe000808137f200efc41b19100c04403001008044010110000423a1b0888fc2022008080020022
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x60000200001800000000
|5,0=>0x1e000000c00000100050000404802c20000160000034006800a00b00000040800001800200700240c0000e000020000000
|6,0=>0x1125a80139b9078000516f2bd085b6e6c0443e89441e4c50f9513a6a0e065ec83b7898766731191b13f5839013af4a029618598eb8be24cd800c4208e90
|7,0=>0x3381164eabb39ed5a0e51da6b8ee4386d15cf82d6064ae8dfa4966692d7b79dc07146fbd46b6925
|8,0=>0x21422aa602c9aea038
|9,0=>0x11
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 7 (j%128);fld (pmP (k/32)) 22 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_185 8 roots_185 ops++addP pm 1 dom_154 5 roots_154 ops++addP pm 2 dom_146 4 roots_146 ops++addP pm 3 dom_171 8 roots_171 ops++addP pm 4 dom_179 7 roots_179 ops++addP pm 5 dom_184 5 roots_184 ops++addP pm 6 dom_177 5 roots_177 ops++addP pm 7 dom_178 5 roots_178 ops++addP pm 8 dom_163 5 roots_163 ops++addP pm 9 dom_186 7 roots_186 ops++addP pm 10 dom_57 5 roots_57 ops++addP pm 11 dom_59 6 roots_59 ops++addP pm 12 dom_147 5 roots_147 ops++addP pm 13 dom_155 6 roots_155 ops++addP pm 14 dom_51 4 roots_51 ops++addP pm 15 dom_170 5 roots_170 ops++addP pm 16 dom_58 4 roots_58 ops++addP pm 17 dom_153 5 roots_153 ops++addP pm 18 dom_43 5 roots_43 ops++addP pm 19 dom_169 7 roots_169 ops++addP pm 20 dom_161 4 roots_161 ops++addP pm 21 dom_168 4 roots_168 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_187 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_146 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_184 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_177 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_178 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_153 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_169 _ g hchk
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
namespace S_190
def pG:List (Nat×Nat):=[(2,10),(2,18),(2,130),(4,20),(4,36),(4,132),(6,14),(6,22),(6,38),(6,134),(8,10),(8,40),(8,136),(12,14),(12,28),(12,44),(12,140),(16,18),(16,20),(16,144),(24,26),(24,28),(24,56),(24,152),(32,36),(32,40),(32,160),(34,38),(34,42),(34,50),(34,162),(48,50),(48,52),(48,56),(48,176),(128,130),(128,132),(128,136),(128,144),(128,160)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_190.map (·&&&dom_190)
def gM:=goal_190&&&dom_190
def NN:Nat→Nat
|5=>4
|6=>24
|7=>18
|8=>4
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0x4453622a961752006a22
|6,0=>0x7d72151f4f516e34dc0e349ed2a4592627524acc216a5199ea157b114d3e14bb1143b2133fe1294710ec50a9d308bf6065eb05d00038e70288801e73
|7,0=>0x732825aa97516df2ef432ea112788223b05225c0141e41095d0ddc0094af074ea0724b0691a0485c044eb01cc4
|8,0=>0xf79e076607277151b6a7
|9,0=>0xf79e0
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaaaaaa00aaaaaa000000000000000000aaaaaa00aaaaaa01555555555555555400000000000000015401540154015402aaaa2222aaaa22200000000000000002aaaa2222aaaa22255555555555544440000000000000000555555555555444400000000aa00aaaa000000000000000000000000aa00aaa000015554000155540000000000000000000155540001515222222222222222200000000000000002222222222222222555555555555555500000000000000000000000000000000aaaa0000aaaa00000000000000000000aaaa0000aaaa0001555555540000000000000000000000015555555400000002aaaaaaaaaaa800000000000000000002aaaaaaaaaaa8000555555554444444400000000000000005555555544444444aaaaaaaaaaaaaaaa0000000000000000aaaa0000aaaa000154015401540154000000000000000001540154015401540282828282828282800000000000000002828282828282828555555555555555500000000000000004444444444444444
|0,1=>0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaa000000000154015401540154000000000000000001540154011001100002aaa80002aaa800000000000000000002aaa80002222050505050505050500000000000000000500050005000500000000000a0a0a0a0000000000000000000000000808080800000000000155540000000000000000000000000001540000000000000000000000000000000002aaa2aaa2aaa2aaa05050505050505050000000000000000050500000505000000aa00aa00aa00aa000000000000000000aa00a000aa00a155555555555555540000000000000001414141414141414002a802a802a802a8000000000000000002a8000002a8000505550555055505500000000000000005055505050555050aaaaaaaaaaaaaaaa0000000000000000aaaaaaaa88888889515151515151515000000000000000015151515151515152aa82aa82aa82aa800000000000000002aa82aa82aa82aa8555555555454545400000000000000005555555554545454
|0,2=>0xaaaaa0a0aaaaa0a00000000000000000aaaaa0a0aaaaa0a155555555555555540000000000000001555541415555414002a802a802a802a80000000000000000028002800280028050505050505050500000000000000000505050500000000aaaaaaaaaaaaaaaa0000000000000000aaaaaa00aaaaaa01555555555555555400000000000000015511551155115512aaa2aaa2aaa2aaa00000000000000002aaa2aaa2aaa2aaa111111111111111100000000000000001111111100000000aaaaaaaaaa00aa000000000000000000aaaaaaaaaa00aa0155555555555555540000000000000001555555555554000028282828282828280000000000000000282828282828000555555550055005500000000000000005555555500550000aaaaaaa0aaaaaaa00000000000000000aaaaaaa0aaaaaaa155555555555555540000000000000001555155515551555002a802a802a802a8000000000000000002a802a80000000555500555555005500000000000000005555005555550000
|0,3=>0x2aaaaaaaaaaaaaaa80000000000000002aa82aa82aa82aa8000000005555555500000000000000000000000055005500
|_,_=>0
def sP:Nat→Nat
|0=>0x18704978818708125d2063c704970818708125b2061c20496881876420492061d108960818708125720c1870810081831d10962461c25012484c61c24812063c34412484061c204020518f3812483060c20401c20492c81820492881440c2040
|1=>0x1c2049b489df1c20492061c2049b081ab1ce081248187a8e0812487c63c7081248187a420492041870920487c61c24812481470812682277c738125f1870899489061c20492061c125e2068c308124818788204920680708124815f1ce081253
|2=>0x187081248187081248187382049206bc708124818709204922718738124818d1c20402061f108124815f1c204921f1870960491870812702271831c2049206b87081248187442589206
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x9303180cc006
|6,0=>0x5bbac5954ea374eb259d1ee88740b9e9ce6e6c732b979caee50724b909c76e34716b899c3ee187
|7,0=>0x274f337963c95e3cf17787c421e02efa779bbb1dc90dc86a4335d8cebe8
|8,0=>0xab353de90f417
|9,0=>0x15c6
|_,_=>0
def wAt:=mkWire dB 50 191 0x7fffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x42560b04846211825f071884e1d0884e25088421d1884249049462504946212415f2718846210864221981df1d1d141091c84e490884785187422118844212464e0708843071c8471124849191c8412104241551c8401924847211c2440524849190874221346472124749211c84719
|1=>0x88411d0494221182491d248512104246211c64121188463a08847211826f210474121
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x6600000003
|6,0=>0x564a0d310000008cd092013a66c8001920000000017200050c898f21a42c841862
|7,0=>0x2794d296524a39452865049f93d2764e49b9352664c49792d2
|8,0=>0x14c690d11
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0x2003e40722800211eb2102f390807ac8401f20081c00039809002f2c8017954008822002f1900159c8004100001c32000e1100054000020c00010100008000003e4000100800080000020200010000004000000a000003000000c000002400000e000000
|1=>0x4a0f866403e32920201402f3c9809460c01e32600e0b
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x80001
|6,0=>0x30b24000348620700c00000700d3871440ca
|7,0=>0x69872089b3e64d47e17a4663595
|8,0=>0x41d957
|9,0=>0x11
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 25 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_188 7 roots_188 ops++addP pm 1 dom_142 5 roots_142 ops++addP pm 2 dom_156 5 roots_156 ops++addP pm 3 dom_62 7 roots_62 ops++addP pm 4 dom_186 7 roots_186 ops++addP pm 5 dom_178 5 roots_178 ops++addP pm 6 dom_148 4 roots_148 ops++addP pm 7 dom_150 5 roots_150 ops++addP pm 8 dom_146 4 roots_146 ops++addP pm 9 dom_182 7 roots_182 ops++addP pm 10 dom_158 7 roots_158 ops++addP pm 11 dom_174 7 roots_174 ops++addP pm 12 dom_168 4 roots_168 ops++addP pm 13 dom_58 4 roots_58 ops++addP pm 14 dom_184 5 roots_184 ops++addP pm 15 dom_164 4 roots_164 ops++addP pm 16 dom_172 5 roots_172 ops++addP pm 17 dom_60 4 roots_60 ops++addP pm 18 dom_166 5 roots_166 ops++addP pm 19 dom_46 4 roots_46 ops++addP pm 20 dom_54 4 roots_54 ops++addP pm 21 dom_138 4 roots_138 ops++addP pm 22 dom_30 4 roots_30 ops++addP pm 23 dom_180 5 roots_180 ops++addP pm 24 dom_170 5 roots_170 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_190 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_188 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_142 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_156 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_178 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_150 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_146 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_174 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_184 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_172 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_60 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_166 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_46 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_138 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_30 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_180 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_170 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_188 7 s (0,roots_188.map (·&&&dom_188)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_190 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_188 h
def symsG:List (List (Nat×Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_190==dom_190)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_190 gM v ys):RunD true dom_190 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_190 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 4 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 24 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 24 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 18 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 18 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 4 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_190 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_207:Lower true dom_207 roots_207 goal_207 7:=lower_slice_b [(0xaaaa000000000000aaaa000000000000aaaa000000000000aaaa,8,9)] (by decide +kernel) lowS_206
theorem lowS_215:Lower true dom_215 roots_215 goal_215 7:=lower_slice_b [(0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa,16,17)] (by decide +kernel) lowS_214
theorem lowS_219:Lower true dom_219 roots_219 goal_219 8:=lower_slice_b [(0xa0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0a,8,9)] (by decide +kernel) lowS_218
def dzo_213_8:=0x33003300000000003300330000000000330033000000000033003300
def gzo_213_8:=0x33003300000000003300330000000000330032000000000032002200
def gsh_213_8:=0x330033000000000033003300000000003300320000000000320022
theorem lowS_zo_213_8_84:Lower true dzo_213_8 roots_213 gzo_213_8 6:=lower_iso_b (d1:=dom_213) (r1:=roots_213) (T1:=gsh_213_8) [(dom_213,8)] (by decide +kernel) (lower_slice_b (T:=gsh_213_8) [(0x220022000000000022002200000000002200220000000000220022,0,1),(0x330033000000000033003300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_84)
namespace S_221
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(1,129),(4,20),(4,68),(4,132),(5,13),(5,21),(5,69),(5,133),(8,9),(8,136),(12,13),(12,28),(12,76),(12,140),(16,17),(16,20),(16,80),(16,144),(24,25),(24,28),(24,88),(24,152),(64,65),(64,68),(64,80),(72,73),(72,76),(72,88),(72,200),(128,129),(128,132),(128,136),(128,144),(192,193),(192,196),(192,200),(192,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_221.map (·&&&dom_221)
def gM:=goal_221&&&dom_221
def NN:Nat→Nat
|7=>2
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|7,0=>0x668333ab6a
|8,0=>0x7369e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcccccc0000000000cccccc0000000000cccccc0000000000cccccc033003300000000003300330000000000330033000000000033003300cccc000000000000cccc000000000000cccc000000000000cccc00030303030000000003030303000000000303030300000000030303030888888880000000088888888000000008888888800000000888888880003300000000000000330000000000000033000000000000003300cccccccc000000000000000000000000cccccccc00000000000000033333333000000003333333300000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x2e8c8f6322c688
|_=>0
def sO:Nat→Nat→Nat
|7,0=>0xcc06
|8,0=>0xc6
|_,_=>0
def wAt:=mkWire dB 8 222 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 9
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xb9ba
|_=>0
def oO:Nat→Nat→Nat
|7,0=>0x441
|_,_=>0
def PO:=mkPO wAt oP oO 8 3 7 6
def pmP:Nat→Nat
|0=>0xfefcf80
|_=>0
def pmB:Nat→Nat→Nat
|7,0=>6
|8,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 2 (j%128);fld (pmP (k/32)) 7 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_220 7 roots_220 ops++addP pm 1 dom_157 7 roots_157 ops++addP pm 2 dom_93 7 roots_93 ops++addP pm 3 dom_217 7 roots_217 ops++addP pm 4 dom_213 6 roots_213 ops++addP pm 5 dom_205 6 roots_205 ops++addP pm 6 dzo_213_8 6 roots_213 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_221 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_213_8_84 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_220 7 s (0,roots_220.map (·&&&dom_220)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_221 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_220 h
def symsG:List (List (Nat×Nat)):=[[(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_221==dom_221)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_221 gM v ys):RunD true dom_221 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_221 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 2 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_221 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_235:Lower true dom_235 roots_235 goal_235 9:=lower_slice_b [(0xc0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c,8,10)] (by decide +kernel) lowS_233
def dzo_174_64:=0x555500005555000000000000000000005555000055550000000000000000
def gzo_174_64:=0x555500005554000000000000000000005554000054540000000000000000
def gsh_174_64:=0x55550000555400000000000000000000555400005454
theorem lowS_zo_174_64_168:Lower true dzo_174_64 roots_174 gzo_174_64 6:=lower_iso_b (d1:=dom_174) (r1:=roots_174) (T1:=gsh_174_64) [(dom_174,64)] (by decide +kernel) (lower_slice_b (T:=gsh_174_64) [(0x44440000444400000000000000000000444400004444,0,2),(0x50500000505000000000000000000000505000005050,0,4)] (by decide +kernel) lowS_168)
def dzo_168_64:=0x10100000101000000000000000000000101000001010000000000000000
def gzo_168_64:=0x10100000100000000000000000000000100000000000000000000000000
def gsh_168_64:=0x1010000010000000000000000000000010000000000
theorem lowS_zo_168_64_168:Lower true dzo_168_64 roots_168 gzo_168_64 4:=lower_iso_b (d1:=dom_168) (r1:=roots_168) (T1:=gsh_168_64) [(dom_168,64)] (by decide +kernel) (lower_slice_b (T:=gsh_168_64) [] (by decide +kernel) lowS_168)
def dzo_172_64:=0x111100001111000000000000000000001111000011110000000000000000
def gzo_172_64:=0x111100001110000000000000000000001110000010100000000000000000
def gsh_172_64:=0x11110000111000000000000000000000111000001010
theorem lowS_zo_172_64_168:Lower true dzo_172_64 roots_172 gzo_172_64 5:=lower_iso_b (d1:=dom_172) (r1:=roots_172) (T1:=gsh_172_64) [(dom_172,64)] (by decide +kernel) (lower_slice_b (T:=gsh_172_64) [(0x10100000101000000000000000000000101000001010,0,4)] (by decide +kernel) lowS_168)
def dzo_170_64:=0x50500000505000000000000000000000505000005050000000000000000
def gzo_170_64:=0x50500000504000000000000000000000504000004040000000000000000
def gsh_170_64:=0x5050000050400000000000000000000050400000404
theorem lowS_zo_170_64_168:Lower true dzo_170_64 roots_170 gzo_170_64 5:=lower_iso_b (d1:=dom_170) (r1:=roots_170) (T1:=gsh_170_64) [(dom_170,64)] (by decide +kernel) (lower_slice_b (T:=gsh_170_64) [(0x4040000040400000000000000000000040400000404,0,2)] (by decide +kernel) lowS_168)
namespace S_238
def pG:List (Nat×Nat):=[(2,10),(2,66),(2,130),(4,36),(4,68),(4,132),(6,14),(6,38),(6,70),(6,134),(8,10),(8,40),(8,136),(12,14),(12,44),(12,76),(12,140),(32,36),(32,40),(32,160),(34,38),(34,42),(34,98),(34,162),(64,66),(64,68),(72,74),(72,76),(72,104),(72,200),(96,98),(96,100),(96,104),(96,224),(128,130),(128,132),(128,136),(128,160),(192,194),(192,196),(192,200),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_238.map (·&&&dom_238)
def gM:=goal_238&&&dom_238
def NN:Nat→Nat
|4=>11
|5=>96
|6=>287
|7=>130
|8=>18
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xeba8ad6660cdfc583b455673d4b13c283f024bd11d895142a303d01
|5,0=>0xe7bf3de601d93bad7f27d4b8ed35c5cfe67cf807c903ac32fcc15d0c14e6be689bc791b91b6ab9ffa33649cf1d9aa21978579458692fa591bc490ad88c5ad855d3853ca83b537a3897998e785e373725726a26b7df6b1496a2fd67a025b3a357709567195631253c604cb364c8be49ed349b2147975477874159240f3b40cb63f0ec3e28c3ca363c7253a8f938d793783d36bd4368993640e359ea338f33166430d71301512fa0d2dfb32d4cd2915b2718724554241bb22ec61f9021f5f71d37514df6149cc11fcb11c780d5ea0d3fc0c6690baf80abbe0a99f099ea0930e082ef0669305223044ab03527010a400e46
|6,0=>0x42036419e14139940dca3fdc03e8e03e8d83e6393db553d5e23ced13cbd03be6b3b50a3b1943b1173a8f939690385b337813374bd36c643673235e1e357c834efc3400f33f7d33bbb33506334a0330cd31419308122ebf72e4fb2e0462c9b52c4782c15f2bb552a8a42a5d02a59d2a41f2a2dd2a0b1296ea293022902a289232730f2683425d5225b6f2403423c8b2366a225a72146c20ed020ccf20c041f8451e8fe1dea61ddf31d4821d10f1ced81cb531c9f71c6f51c4481c1f61bd221a73b195131920f18feb1818e17c2714322141661396913967135c612f9f12a131133d1105610a0f0ff9f0fd080fbe40f7bb0ede50e10b0d7d40d2140c8410c5ca0b3970ad720ad5e0a99f0a96e0946d094390934f08fe20897e084bf078d4078500739a0673b064890585404d63044f603d1f032ca028010205b01def00e630045a
|6,1=>0xb7758b6d72b6a95b5b88b5915b46b3b2d95b12a1adb5daaf5baaafba9ea0a966aa8d2ba8207a4fe2a2be3a278ba13879fe669e2fc9b17395ed094e589395291d3c90ad8907788d61a8ca6f8c59f8c27e8b1d48aad78a1868436a8320582990828ea824557ffbc7f9537ef8e7e5b47c6547bac67baa278f95785f377770770a375b12755d2753947479373a1e7340e7300271ec4707896ff5c6f9ee6ee036e7826d7006d2776ca326c9aa6bab36b5eb6a97867686664de6641464383640d163bdb63b48604db6047d600155fcea5f63a5e6aa5e66a5e09f5d16c5cf095c4d05b98e5b8f65b3dd5a13a5a07359a75581a757acd572a0571cd56941552bd54aef526365142c513c04f7284f67a4ef814eddc4dd194d08c4cb364c27b4917248f0d488b848504477ff453f644fdb44f0044d9643840437964349f430ec4247a42042
|6,2=>0xfe363f892cf40cbeaab5e9ca5e9b0ce8576e698ae21bde1d93e1cdddd398d903fd899bd75b3d6681d320ecdd90cb572c903ac7c70c5278c4e92c32fcc0355c027dbf7dabcd44bcb95bb5f8bb3aa
|7,0=>0xde5c7d15a4cf791caa7ac99f8c92e4c9045c2093bebe6bb97ebb932bb92cb640cb4967acab5abca8a01079cc569b19f9abd09ab8695ed0936709261a8fdcd8f7fe8ef1a8bb9a8b8628a9c2836078204a7d7647bac67b3ea7939d7855f782347319372c6c7116b6b24568b39689ed6768f667676604c65f0565a7d645d7644db5dddf5b4b45abac5a9275a52a578a3526d44f9754f4564e4bf4d5e64a3a149f564669144e7d448ae4433543947431c0430ec4221f41cbd3fcd03fa343dfd53df243d3c23c8ad3b1633a1123969036d3a33139309a52ffb72e0462ccb829f582995f2887f27e91264a72520a24ae9217da1f4d61f4171eee41cd491be441bd6e1b3ae182aa17cdb170ce12c3011b4d106dc101421006a0ffab0ff9f0c8410beea0bd4c080e60763a063540571f045eb0319b0301202b6d02b6201a200196e01263
|7,1=>0xf2734eb2ec
|8,0=>0xeedd0b6d63ab7859859a80de16910868b395ee8958f444db723cb3c354382533d17c7616c9614e881305b090cc
|9,0=>0x1305b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaaaa0000aaaa0000aaaa0000aaaa00000000000000000000000000000001554000015540000155400001554000015540000000000001554000000002aaa80002aaa80002aaa80002aaa80002828000028280000282800002828555500005555000055550000555500005555000000000000555500000000aa880000aa880000aa880000aa880000aa880000aa880000aa880000aa89555400011110000155540001111000015400000110000001540000011002aaa80002aaa80002aaa80002aaa80002aaa80002aaa80002a8000000000555500005500000055550000550000005555000055000000555500005500888800008888000088880000888800008888000088880000888800008888000000000000000000000000000000000154000154000000015400015402aaa80002aaa80002aaa80002aaa80002aaa80002aaa8000000000000000555500000000000055550000000000005555000000000000555500000000aaa80000aaa80000aaa80000aaa80000aaa8000088880000aaa80000888955540001555400015554000155540001540000015400000154000001540282800002828000028280000282800002828000028280000282800002828555500005555000000000000000000005555000055550000000000000000
|0,1=>0xaaaa0000aa880000aaaa0000aa8800000001540000000000000154000000015400015400000001540001540222a8000222a8000222a8000222a80002028000020280000202800002028000000005500000000000000550000000000000055000000000000005500aa88000088880000aa88000088880000aa88000088880000aaaa00008889555400015554000000000000000000015554000155540000004400000002a8000002a8000002a8000002a8000002a8000002a8000002a8000002a8055550000444400005555000044440000505000004040000050500000404000000000000000000000000000000000aaaa0000aa000000aaaa0000aa00015400015400000001540001540000000154000154000000015400015402aaa8000222200002aaa8000222200002aaa8000222200002aaa80002222555500005500000055550000550000004444000044000000444400004400aaa00000aaa00000aaa00000aaa00000aaa00000aaa00000aaa00000aaa1555400015400000155540001540000014140000140000001414000014002aa80000222000002aa80000222000002aa80000222000002aa800002220545400005454000054540000545400005454000054540000545400005454
|0,2=>0xaaaa0000aaaa0000aaaa0000aaaa000088880000aaaa000000000000000155540001414000015554000141400001555400014140000155540001414002a8000002a8000002a8000002a8000002800000028000000280000002800550000004400000055000000440000005500000044000000550000004400000000aaa0000000000000aaa0000000000000aaa0000000000000aaa0000000000000000000000000000000015554000155500001555400015552a8000002aaa80002a8000002aaa80002a8000002aa800002a8000002aa8444400004444000044440000444400005555000044440000555500004444aa000000aa000000aa000000aa000000aa000000a0000000aa000000a00155540001555400015554000155540001111000011110000111100001111000000002aaa8000000000002aaa8000000000002aaa0000000000002aaa050500000000000005050000000000000505000000000000050500000000aa0a0000aa000000aa0a0000aa000000aa0a0000aa000000aa0a0000aa01555400015150000155540001515000015540000151400001554000015142aaa8000000000002aaa80000000000028a800000000000028a800000000050500000505000005050000050500000505000005050000050500000500
|0,3=>0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aa000000aaaa0000aa01555400015554000155540001555400015400000000000001540000000002a8000002a8000002a8000002a8000002a8000002a0000002a8000002a00555500005555000055550000555500005555000044440000555500004444aa220000aa000000aa220000aa000000aa220000aa000000aa220000aa0155540001515000015554000151500001555400015150000155540001515028000000280000002800000028000000280000002800000028000000280004500000045000000450000004500000045000000440000004500000044aaaa0000aaaa0000aaaa0000aaaa00000000000000aa000000000000000001540000000000000154000000000000015400000000000001540000000002a8000002a8000002a8000002a80000022000000220000002200000022550000005500000055000000550000005500000044000000550000004400aaaa0000aaaa0000aaaa0000aaaa0000aa00000000000000aa000000aa0111100001111000011110000111100001555400015510000155540001551000000000000000000000000000000000282800002800000028280000280050500000500000005050000050000000505000005000000050500000500
|0,4=>0xaa0000aaaa000000aa0000aaaa000000aa0000aa00000000aa0000aa00000000000000000000000000000000015444000154000001544400015402aa200002aa200002aa200002aa200002aa20000222200002aa200002222555500005544000055550000554400005555000055440000555500005544a0a00000aaa00000a0a00000aaa00000a0a00000aaa00000a0a00000aaa0000000015554000000000001555400000000000155400000000000015542aaa8000282a80002aaa8000282a80002aaa8000282a8000000000000000555500005555000055550000555500001111000000000000111100000000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa00000a0000000a01540000000000000154000000000000015400000000000001540000000002aaa80002aa800002aaa80002aa800002aaa80002aa800002aaa80002aa8555500005500000055550000550000005544000055000000554400005500aaaa0000aaaa0000aa00000000000000aaaa0000aaaa0000aa0000000a00000000004040000000000000404000000140000041400000014000004142aaa80002aaa00002aaa80002aaa00000000000000000000000000000000005500000055000000550000005500000055000000440000005500000044
|0,5=>0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000a0a00000aaaa0000a0a000000000000000000000000000000000000000001400000000000000140000000002aaa0000000000002aaa0000000000002aaa0000000000002aaa5555000055550000555500005555000055550000555500000000000005002a0a0000220000002a0a0000220000002a0a0000220000002a0a00002201555400011110000155540001111000015510000111100001551000011112aa800002aa800002aa800002aa800002220000022200000222000002220555500005555000055500000555000005555000055550000555000000000aaaa0000aaaa0000000000000a0a0000aaaa0000aaaa0000000000000a000000000155540000000000015554000000000001414000000000000141428a880000000000028a880000000000028a800000000000028a80000000000000000000000000000000000000000555500001100000055550000110022220000222200000000000022220000222200002222000000000000220155540001555400015554000155540000015400015400000001540001540000000002aaa8000000000002aaa80000000000028a800000000000028a8050500000505000005050000050500000500000005000000050000000500
|0,6=>0x222200000000000022220000000000002222000000000000222200000001414000014140000141400001414000015540000155400001554000015542a8000002a8000002aaa80002a8000002a8000002a8000002aaa80002a80000000000000000055550000000000000000000000000000555500000000aaaa0000aaaa0000aaaa0000aaaa0000aa000000aa000000aaaa0000aa0000000000000000000000000000000000000000015400000000000001540000000000000000000000000000000002aaa8000000000002aaa80000000550000005500000055000000550000005555000055000000555500005500aaaa0000aa000000aaaa0000aa000000aaaa0000aa000000000000000000000000001414000000000000141400000000000014000000000000001402aaa8000000000002aaa8000000000002a800000000000002a8000000000111100001111000011110000111100001110000011100000111000001110222200002200000022220000220000002222000022000000222200002201555000015550000155500001555000015550000155500001555000015552aaa8000282800002aaa8000282800002aaa80002aa800002aaa80002aa8555500005555000055550000555500000055000000000000005500000000
|0,7=>0xa2a20000a2a00000a2a20000a2a00000a2a20000a2a00000a2a20000a2a155540001555400000154000001540001555400000000000001540000000000000000000000000000000000000002aaa8000222200002aaa80002222000000000000000000000000000000000000000055500000000000005550000000000000000000000000000000000a0000000a0000000a0000000a01555400015554000000000000000000015554000155540000140000001402aaa80002aaa80002aaa80002aaa80002aaa80002aaa80002aaa80002a805555000055550000555500005555000055550000050000005555000005000000000000000000aa000000aa0000000000000000000000aa000000aa01414000014140000155400001554000014140000141400001554000015542a8000002a8000002a8000002a8000002aaa80002aa200002aaa80002aa2550000005555000055000000555500005500000055550000550000005500000000000a0a0000000000000a0a000000000000080800000000000008084444000044440000444400004444000044440000000000004444000000028a8800028a8800028a8800028a8800028a880002828000028a880002828550000005500000055550000555500005500000055000000555500005500
|0,8=>0x202000002000000020200000200000002020000020000000202000002000000000155540000000000015554000000000001515000000000000151528000000280000002800000028000000280000002a800000280000002a80110000001100000011000000110000005555000011000000555500001100aaaa0000aaaa0000000000000000000088880000aaaa0000000000000000000000015554000000000001555400000000000111100000000000011110880000008800000088000000880000008800000088000000880000008805555000055550000000000000500000055550000555500000000000005000a0a00000a0a00000a0a00000a0a00000a0a0000000000000a0a0000000155540001555400015554000155540000015400000110000001540000011000000002aaa80000000000000000000002a80002aaa800000000000000000000000000000000000000000000000111000001110000011100000111000000000000000000000000000000000222200000000000022220000000000000001414000000000000141400000014000014140000001400001414000000000000000000000000000000002aa800002aa800002aa800002aa8000000000000000000000000000000000000000000000000555500005500
|0,9=>0xaaaa0000aaaa0000aaaa000000000000aaaa0000aaaa0000aa000000000155540000015400015554000001540001414000000140000141400000014000000000000000000000000000000002aaa80002aa800002aaa80002aa8505500005055000050550000505500005054000050540000505400005054aaaa000000000000aaaa000000000000aaaa0000aa000000aaaa0000aa014140000141400001414000014140000155540001554000015554000155422a280002222000022a280002222000022a280002222000022a280002222001100000000000000110000000000000011000000000000001100000000a0aa0000a0aa0000a0aa0000a0aa0000a0aa0000a0a00000a0aa0000a0a1115400000000000111540000000000011154000000000001115400000002aaa80002aaa80002aaa80002aaa80000282800002800000028280000280555500005555000055550000555500005550000055500000555000005550aaaa000000000000aaaa000000000000aaa0000000000000aaa000000000141400001414000014140000141400001010000010100000101000001012a8280002a8280002a8280002a8280002a8200002a8200002a8200002a82010100000101000001010000010100000100000001000000010000000100
|0,10=>0xaaaa0000aa0000000000000000000000aaaa0000aa01555400015554000155540001555400000000000000000001555400015402a8000002a8000002a8000002a8000002a800000000000002a8000000000505000005555000050500000555500005050000054540000505000005454000000002222000000000000222200000000000020200000000000002021555400015554000155540001555400000000000000000001515000015152aaa80002aaa80002aaa80002aaa8000222a800000000000222a8000000005050000000000000505000000000000050500000500000005050000050000000000000000000000000000000000aaaa000000000000aaaa0000aa01541400015414000154140001541400015414000154000001541400015402a8880002a8880002a8880002a8880002a8800002a8800002a8800002a88444400005555000044440000555500004444000055550000000000000000aaaa0000aaaa0000aaaa0000aaaa00008a8a0000888800008a8a00008889555400015554000155540001555400000000000014000000000000001402aaa8000000000002aaa8000000000002aaa800000000000000000000000555500005500000055550000550000005555000055000000550000005500
|0,11=>0xaaaa0000aaaa0000aaaa0000aaaa00000000000000000000aaaa0000000001540000015400000154000001540000015400000154000001540000000000000000000000000000000000000000888800008800000088880000880555500000055000055550000005500005555000000440000555500000044a0a00000a0a000000000000000000000a0aa0000a0aa0000000000000000000000000000000155540001555400000000000000000001555400015402aaa80002aaa80002aaa80002aaa8000000000002a800000000000002a805555000055550000555500005555000055550000555500005555000000000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a0000000155540001555400015554000155540001555400015540000155540001554002a80002aaa8000002a80002aaa8000002a80002aaa8000000000000000555500005555000055550000555500005050000055500000505000005550222000002220000022200000222000002220000022200000222000002220000000015554000000000001555400000000000154000000000000015402a800000000000002a800000000000002a800000028000002a8000000280000000000000000054540000545400000000000000000000545400005454
|0,12=>0xaaaa0000aaaa00000000000000000000aaaa0000aaaa0000222200000000015400000154000001540000015400000154000001540000000000000002a800000000000002a800000000000002a800000000000002aaa80000000000000000000000000000000000000005555000005000000555500000500aaaa0000aaaa0000aaaa0000aaaa000022000000220000002200000022014000000154000001400000015400000140000001540000014000000154022220000222200002222000022220000222a800022220000222a8000222255550000555500005555000055550000550500005500000055050000550000000000000000000000000000000000aaaa0000a8a80000aaaa0000a8a954000001555400015400000155540001540000015554000000000000000282a8000282a80000000000000000000282a8000282a8000000000000000555500005555000055550000555500005055000050550000000000000000aaaa0000aaaa00002222000000000000aaaa0000aaaa0000222200000001115400011110000111540001111000011154000111100001115400011112aaa80002aaa80002aaa80002aaa80002aaa00002aaa00002aaa00002aaa005500000055000000550000005500000055000000000000005500000000
|0,13=>0xa8a80000a8a800000000000000000000a8a80000a8a8000000000000000155540001555400015554000155540001515000015150000000000000000282800002aaa8000282800002aaa8000282800002aa80000282800002aa8000000000500000000000000050000000000000005000000000000000500222200002220000022220000222000002222000022200000222200002221415400014150000141540001415000014154000141500001415400014152aaa80002aaa80002aaa80002aaa80002aaa80002aaa800008888000000000000000005500000000000000550000000000000050000000000000005088880000aaaa000088880000aaaa000088000000aa00000088000000aa01551000011110000155100001111000015510000111100001551000011112a8880002a8880002a8880002a8880002a8880002a8000002a8880002a80111100001111000011110000111100001111000010100000111100001010aaaa0000aaaa0000aaaa0000aaaa00000a0a0000000000000a0a00000001555400015554000001540000015400015554000155540000015400000002aaa80002aaa800002828000028280002aaa80002aaa8000028000000280555500001100000055550000110000005555000011000000555500001100
|0,14=>0x222200002222000022220000222200002222000022000000222200002200000000004444000000000000444400000000000044000000000000004402a8000002aaa80002a8000002aaa80002a8000002aa200002a8000002aa2555500005555000055550000555500001110000011100000111000001110aa000000aa000000aa000000aa000000a0000000a0000000a0000000a00155540001555000015554000155500001555400015550000155540001555000000002aaa8000000000002aaa8000000000002aa20000000000002aa21101000011000000110100001100000011010000110000001101000011000088000088880000008800008888000000880000888800000088000088880000000000000000000000000000000154000001540000015400000154000000000002a800000000000002a800000000000002a8000000000000000005500000000000000550000000000000055000000000000555500000000000000002220000000000000222000000000000022200000000000002221555400015554000155540000000000015554000155540001555400000002aaa80002aaa80002aaa80002aaa80002a2a00002a2a00002a2a00002a2a454500004545000045450000454500004545000044440000454500004444
|0,15=>0xa00000a0a0000000a00000a0a0000000a00000a0a0000000a00000a0a0000000000000000000000000000000015554000155540000000000000002aaa80002aaa80002aaa80002a8000002aaa80002aaa80002aaa80002a8000000000000000000000000000000000555500005555000055550000550088aa000088aa000088aa000088aa000088aa00000000000088aa00000000141400001010000014140000101000001414000010100000141400001012aaa80002aaa800000000000000000002aaa80002aaa80002aaa80002a8051500000515000005150000051500000515000005150000051500000515088880000888800008888000088880000aaa80000aaa80000aaa80000aaa8015400015554000000000000000000000154000155540000000000000002aaa80002aaa80002aaa80002aaa8000002a80002aaa8000000000000000000000004444000000000000444400000044000044440000004400004444aaaa000022200000aaaa000022200000aaaa000022200000aaaa000022215554000000000001555400000000000155540000140000015554000014000000000000000000000000000000000222a800000000000222a80000000555500005150000055550000515000005555000051500000555500005150
|1,0=>0x155540001555400011110000111100001555400015554000111100001111002a80002aaa8000002a80002aaa80000000000000000000000000000000550000005500000055000000550000000000000055000000000000005500aaaa0000aaaa0000a0a00000a0a00000aaaa0000aaaa0000a0a00000a0a1111000011110000155540001111000011110000111100001555400011112aaa80002aaa80002a800000000000002aaa80002aaa80002a80000000004444000055550000000000000000000044440000555500000000000000000000000000000000aaaa0000aaaa00000000000000000000aaaa000000015554000155540001555400015554000155540001555400015400000154000000000000000000000000000000000002a800000000000002a8000000055550000050000005555000005000000555500000500000055550000050000000000aaaa000000000000aaaa000000000000aaaa0000000000000001111000011110000000000001111000011110000111100000000000011112aaa80002aaa80002a8000002a8000002aaa80002aaa80002a8000002a80555500005555000055550000555500005544000055440000554400005544
|_,_=>0
def sP:Nat→Nat
|0=>0x78104419038001e19108040e000785c08190081c0a040c8042407028103207100001e1f0206402070282002070f0001e040c8403a0007810260d038700a1b0206402050785418190803400040c8040e1a0783032100c00002070b0180a170081c2c050a8080214000102612038141011080001e08070340e000602c1401000201201038181001038180a04018080200
|1=>0xc01c0017020040e390281002071c0001e040c8040e051b85402361a8001e041a04002000781032330081c0a32020640207028101c190681c00040c8040e31028300401038c000040c8044c07178b81819038b40001038b05600078a808190081c00290081c3800078a00819008980a040989c0e00078202a020089800190081c4a000783046020081c0004058280200
|2=>0x200802070a000320103928000f0206402072483c08110c840000f040080207240000819068040e470081c2c060003c8a0c010040e000a91032010003c0819218040e0f0b8040e160003c081903908000f0b81026010381408190081c0041040f80207000100226039000a3f040f80207000107a01038001e3c0202c04010003076020081c003a060641a07000303201
|3=>0xc8040e050206402530003c10110081c000f0081ca4160003c08340081c000f0c8040e510003c103c010040e00040040e060003c100c0081ca0000081c2c05078202e460081c0a080081c9e00078202a19008980a0c0c82802070001068011301c0a04270640207028109a020080008190089858050402802070003c9804010044c000a86402140003c0819258340e05
|4=>0x206402072f0001e040c8040e5d0003c10091f0040e081f0040e050206402072e03c5c0c098080e0002064205b0003c7e0103858000f040040e160283c100103948000f0216832010003c100c010040e000206420590003c101509840000f0216032010383c08190081cae0f26010320113014103e0081c0c000405c7c0103800324b03958000f0c95402070003ca804
|5=>0x8001e040c8040e590003c1015098040e000783076190081c000f2a0103201038001e680a86402070003c085a0c8040e0007810320103814ce0f170103207168001e040c8040e660003c2a190081cac0007820ca01038001e040c8040e640003c78190081c6c00078201804010040e00060640207318001e04310641a070003cc2040c8040e0007854320103980000f
|6=>0x3c0103201038001e042206402070003c2a04010640226000fc08190081c000f06010ec19038001e750206402070003c08740c8040e05078103201039cc000f02064e201038001e700206402070003c2a040081c80000782008190081c0a0f060083201039bc0001038d8380507810dc190681c000f358103201038001e17020640207028102601039a8000f1e0101619
|7=>0x328040e000206402072d8001e080c8040e480003c08190081d0c0007810320103a141e040c8040e840003c0819008980e83028202a020081c000f020640e820003c1004408040e000781004010398c000f400103201038001e040c9fc02070003c8a0c0c8040e00078103201039f8000f3e8101619008001e040c8040e7c0003c0819068040e7a079e408190081c000f
|8=>0x1b0141e040c8040e140003c10460081c0a0f020640207480001e080204c1a070003c08190081d1e0007810320103a38000f0a9a41619008001e2e0204c32070283c081900a340e0007a3008190081c000f0206402074583c08020c8040e8a00010321044890000f020ec0401038001e3c0206402260381474040c8340e0007810320103a201e040c8400e870003c1819
|9=>0x60083201038013a040c8040e0007810329c0081c000f4d8103201038001e9a0206402070003c081900a644c000782002070b0001e040c8040e980283c08194b8040e000781032014b01c0a0f0204c3207180001e040c8040e950003c98040c8044c00078543201038ac000f4a24c3201038001e040c8404c240003c8a04010040e000781122190081c000f0a8640207
|10=>0x781032aa0081c1e040c80552070003c103e0081c00040c8f8020700010320103aa0000f538103201038001e045306402070003c7e040081c72000797c08130c81c000f022943201038001e040c8040ea4078b808190681c0a040c80546070003c08190081d440007810041000a24000f0401002071c8141e045006402070283c08194f8040e0f02064029e038001e15
|11=>0x81d6a0f020656801038001e3c0206402070003c08190681d660007810260103ac8000f1f8102601038001e040cac402070003c08020cac00207078200819580040e0f570103201038001e280202c32010003c1004098040e050781032011301c900009a4c3201038001e0401064200113000084d0c804000f020655801038001e040c8040eab0003c08940c8400e00
|12=>0xc8040e00040f802070003c08190081d7c0007810320103af4000f5e0103201038001e930106402070003c08190081c3a00078640207250001e0c0c80532070003c08190081d760f0a830320d0081c00040106402072400174040c8040e000783008190081d7200368100401038001e040c81d6e0007ad808190081c000f020641a07158001e08020640226038140819
|13=>0x781032016481c000f0204c3210130001e046406402070003d8e040c8040e00078202a190098c000f4d8303201038001e040c82802070003c08190081c0ac607810320103b101e081e06402070003c08020c8040ec307810320161098000f023043201038001e041186402070283c1804010040e1c00020320103a0c000f0202c04011300008770081d8000078117e02
|14=>0x6a86402070003c08740c8040e0007820080103940000f0206402076a0001e040c8400ed30003c08190081da40007a4c320d0081c000f0206402076883da00c0c8040e00078fc2e040c8040e000206402070019c1e040c8040ecf078202e040c8040e05023343201038141ecc0206402070003c08190081c56050783008190081d96000a810320113014080200b280e00
|15=>0xb800e0007810320103b78181900b080e000781032dd0081c000f0204c1a070e0001e04010040edc0003c10150c840020007810320103b6c000f020642001318001e040cb6802070003c08190081c800007810320103b641e690c8040e630003c08190081db00007810320103b5c000f0235832010283c08190081c6005078103201038156a0f02064022603a2c1e04
|16=>0x7810320103b781e040c8040e057283c5c0c0106402070011408190081c0a0f023903201038141e3c0200832010380008190081dc60007b88320103ac8000f0601032010394000150206402350003c08130cb840e000781076190081c0a0f1f8208c01038001e940c8040e4a0003c2a040c80524000785c08190081c000f020642001450001ed00200802070003c0819
|17=>0x8980e400003c08230c8400e0007810320103bb0000f0204dd6070003dd4040c8040e0007808320103928000f0b81002071c8001e4c0206402630003c08190081dd20007810320103ba0000f0206402e70283c100c0c8040e000781046e60081c000f0600832010389000040886402070003c08340081c000f0b81032010381400081406402070003c2a0c0c8400200
|18=>0x38000819048040e0f0a8102619080001ef30206402070003c2e04010640207000201801038e4000f021880401038001ef20206402070003c0819068040e1c02930d2190081c000f0206402f1038001ef00206402070003c2a0c05864020007810320103bbc000f0601032075b8001e040c8040eee0003c2e04098040e0007811da190081c000f170302619038001e04
|19=>0x310640200078202e0c0c8040e00020640207003941e040c8247c010381032017d81c000f0401004011301c00040c92c02070283c08191f0040e050606402077d0001ef90206402070003c5c040cbe00e00078040e160003cbe040c83402070281102190801c000f023dc3201038001e042d064020007810320103bd41e040c89c02070003c081900bd0000f040300401
|20=>0x42bc08190081c000f020640207490001e150204c3201038001e040c8040e480003c18048086402070003c08190081d96000781032650081c000f368103201038001e048006402070003c081903bfc000f041a43201038001e040c8040ec307810320103bd81e080206402077f03c320103870ac00078303201038b0000f7e0103201038001e080b91802070003c2a04
|21=>0x20640207180001e040cb8402070003c081900a640e000793008190081c000f0206402ca038001e040c8400e240003c0819730040e240003c2a040106402070003c10150206402070003c081900c08000f1701032e60081c000f0206402071a8001e040c8340207028117e190081c000f020640207003381e040c8040eb20003c7e040c8040e000782008190081c0a0f
|22=>0x3c0813730040e0007810320103816060f020647c0103801a0040c8040e0007810320103b70000f0a810320d0081c000f0a83008190081c000f4d8103201038001e450204c3201038001e04058640207120001e040c8040e500003c0819068040e1c0003c18040c8040e1c0003c08190081d0e0007810161900898000f020648c01038141e2e0202c3201038001e08
|23=>0x81c000f020640207828001e2e0606402070003c18040c8040e6a0003c08020c84002070003c10040c84002070003cbe040c83402070003cbe0c0206402070003c74150206402070003c78040c8040e00078303201038d8000f020640207378141e040c8040edf07810320103a0c000f020649601038001f040206402070003c086c0106402070003c8a08020640207
|24=>0x8980e00078040e360e0001e040c8040e89120001e3f020083201038001e150206402070283c7e080206402070003c08190081c0aa10781033090081c1e040c8040e1c0283c081900bac0e0007810320103c201e150206402077f03c09070c8040e0007ae018040c8040e0007830320103890000f0204c3210038001e048306402070003c08191f0040e00079f40819
|25=>0x1e01032011301c000f02008330b0081c000f02064022603a0c000f0225026190081c000f0a86402071b0001e08230040e00078b808130c81c000f0b8103201038001e04010640207120001e043106402070003c50040c8040e000781032100681c000f8501032010003c5c040106402070003c0819008980e240003c0819708044c070003c10040c8040e00078b80819
|26=>0xc8040e000781016190081c0a0f020640207158001e0c0206402071c8001eaf0206402070003c10040c8044c070003c08190081e180007810320103be8000f0200832011301c00fd0206402070003c0813010040e000782008130081c000f0225004190081c000f040303201038001e040c8040e600003c10040c8040e050003c08020081c7200078200801038e4000f
|27=>0x7810320103814000f02064030e038001e040c8040e240003c080b0c8040e000781032770081c000f0206402071b0001e040c8040e000781032e60081c000f7e82008190081c000f0206560010383c08190081d1400078202e040c8040e0007854081900898000f0235832010003c08190081c6000078103201038021a040c8040e240283c1804010640207000200802
|28=>0x40c8040e000781032100081c000f0206402070283c08190081dfc0f024043201038001e040c91802070003c08020c8040e000782008190081c000f020640226038001e040986402070003c08190081c7200
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x32502d50285023501e50195014500f500a500550005
|5,0=>0x1af61a961a3619e51986192618c61866180617a6174616e61686162615c61566150614a6144613e61386132612c61275121611b6115610f6109610360fd60f760f160eb60e560df60d960d360cd60c760c160bb60b560af60a960a3609d60976091608b6085607f60796073606d60676061605b6055604f60496043603d60376
|5,1=>0x26d52685262625c62566250624a6244623e62386232622c62266220621a6214620e6208620261fc61f661f061ea61e461de61d861d261cc61c751c161bb61b56
|6,0=>0x424741d7416740f7409640273fc63f573ee73e773e163da73d373cc73c663bf73b873b173aa73a3739c7395738e7387738073797372736b7364735d7356734f73487341733a7333732c7325731f63187311730b630472fd72f672ef72e872e172da72d372cc72c572be72b772b162aa72a3729c7295728e72877280727972727
|6,1=>0x5d975d275cb75c475bd75b675af75a875a1759a7594658d7586757f75796572756d5567656075597552754b7544753d75376531652a7523751c7515750e7508650174fa74f374ec74e574de74d774d164ca74c374bc74b574ae74a774a074997492748b7484747d7476747064697462745b7454744d7446743f74387432642b7
|6,2=>0x78f77887781777a7773776c7765775e77577750774a6743773c7735772f67287721771a7713770c770666ff76f876f176ea76e376dc76d576ce76c776c166ba76b376ac76a5769e76977690768a6683767c7676666f76687661765a7653764d6646764066397632762b7624761d761766107609760275fc65f575ee75e775e07
|6,3=>0x947794079397932792b7924791d7916790f7908790178fa78f378ec78e668df78d878d178ca78c378bc78b668af78a878a1789a7894688d7886787f78796872786b7864785d7856784f78487841783a7833782c7825781e781778107809780277fb77f657ef77e877e177da77d377cc77c577be77b777b167aa77a3779c77966
|6,4=>0xa177a107a097a0279fb79f479ed79e769e079d979d279cc69c579be79b779b259ab79a4799d79976991698a7984697e69786971796a7963795c7955794e7
|7,0=>0xbe68bde8bd68bce8bc68bbe8bb77bb07ba97ba36b9c7b957b8e7b868b7e8b777b707b6a6b637b5c7b548b4c8b457b3d8b358b2e7b268b1e8b177b107b097b018af98af27aeb7ae47add7ad67ace8ac68abe8ab86ab08aa97aa36a9c7a957a8e7a877a807a788a717a698a627a5a8a537a4c7a457a3e7a386a317a2b6a256a1e7
|7,1=>0xdb37dab8da47d9e6d977d916d8a7d837d7b8d747d6d7d658d5e7d568d4f7d487d417d3a7d337d2c7d248d1d7d167d0e8d077d007cf88cf08ce88ce08cd97cd36ccc7cc57cbd8cb67caf7ca87ca26c9a8c928c8a8c837c7b8c756c6d8c658c5e7c568c4f7c496c427c3b7c356c2e7c277c1f8c187c117c0a7c037bfc7bf57bee7
|7,2=>0xdc08dba6
|8,0=>0xe3c7e366e306e297e227e1b7e147e0d7e067dff7df87df17dea7de37ddc7dd57dcf6dc87
|9,0=>0xe436
|_,_=>0
def wAt:=mkWire dB 271 239 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 9 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x3d020640c83d0411b02064020650411b0206402065020710c8130203d0c8050201d02065058110c81d040fb02064020650411b02064020650203d0b91b02064020651b07102067020660003d1f91b02064020650a8080201d0a8080a8650201d04098020650411b0206402065040050c8110203d02064020650203d0203d02041038050a8340201d098300c8050c891020070a80804034020650203d0201d
|1=>0x32806020080983f0401f020650098d02065040050c8110a83f3d8010c8370403d3b8050c803009c90203d0c8f20a83d02071020660003d02067020660003d0c8370083d3683d0c9b10403f020650c8330203d0203d098980c8050201d0c8050c8110c9a50203f04014020650c83d020360083d02065020080c83d0203d0c83d0c811058050c81d0083d1b03d0c8120c97f020651f0012303d02064020652303d
|2=>0x203d0c83d378160003d0201f020050003d0083d020050ca850201432801020080083d0c89a03891020070411b02064020650202f0204d0401d020650204e0c80502007040050c8110ca490089a0c8120003d04098020650003d02064020650c83d0c8110c81d0003d418020209b0383d0209a0c9bd0201f02041038050c8bb02005060070203d010100c83d0c8560201d32802020080c83d0989b0383d0209b
|3=>0x2303d020640206502250010054a0130c835038910200728002010070c83d0203d0201d3783d0c83d0c8330203d0c83d0c9b1020035c007060010203d0204e0c8050c8110003d230160003d020640083d0c8050200a0c83d0403d0c8110c95b02036080030081d080035783d020650c81d0203f0003d0c8114183d0209b0383d022500983d0c83d5681d0c8300203d010050c83d080030081d2303d0206402065
|4=>0x3783d0201f011bf0c83d2301d0003d02064040070c8112301602064418020209b1203d020070c8324a0100c83528001010070c83d022250c81f020650401402065418010209b020650233b0c8160203d0201d0003d0383d0c893020071d03f02065021a90c8330203d0a8080201d0c83d6283d1c8020c8070a83d378010201f038d90c812058350c891020070c83d0c8130203d0c83d0c81d0383d0c83d3603d
|5=>0x1e067020990c891020070c8050c8340083d020650225201005020652301e0003d02064020710c8130203d0c83d0a84c1e064020990403f020650203f0201d0203d6f83d080000081d04016020650c83d040050c8110203d0a84e0201d010130c83d0c83d130050c9bd0201f02064020650c8350383d0209a0383d022250c81f6f83d08000038d90c8120200a0c83d0083d0201d020650401f020650c85624001
|6=>0xc8100c8110203f378010201f2300202064020650003f0c8560201d7e83f0206502064020650c8410403f0c81104016020651f0012303d020642303d0003d020640a8070201d020050c81f0411b02064020650003d0983f0c8050983f3281d020080c83d7b03d23002020643281e02008020650203d0c83d230150003d02064022cd0c805020650c83d0c8410081d020660003d0203d5c007060010403f0c811
|7=>0xc8130203d060070203d0c81d0383d0003d02064020050c81d040070c8110803d0081d03891020070401d020650c893020070081d02007020070c83f0201d0c83d0201d020653601e02003020050c83f0c89a0383d0003d0083d3603d020030c8160003d0200a0c83d0403d020650003d02065020650089a0383d0201d0c8053783d0201f0203d0c8014483d0c81f020080c83d0c9b1020030c8990383d23006
|8=>0xc80503805010010c83d2303d020640a83f0201d0200b0c83d0203d020050c8330203d0c83d0081d02065020350083d060050203d0a8050201d020990383d0c8120203d0003d0201f080000081d0209b0383d0087102066020e50c8070c83d020030c8110c8050c83f020160003d2303d02064022250c81f0c8bb020050201d0083d0201d0203d023990c83f0204d0c8050c81d02007010070c83d0c8130083d
|9=>0xc807020990383d0c83d008010209b0383d0983d0c8050201d0c81202064020650c805020050403f020650c83d020070c8410081d3481d0203f0083d038053601d020030c83d020050383d02007008990383d0c8d90c812020050383d020660c8120c81f02007020090c83d0201d0003d02065020140003d2300102064020660003d0c8340083d378020201f0201d0003f060030203d060010203d0203d02007
|10=>0xc83d020650383d0c8050c8070003d03801020070c81d0c8030c8120c83f02065080030081d0209a0383d0403f020650201d0383d2301d02064040070c8112303e020640003d020070203d0c83d0c83d020650c81d0003d0204e0c8050203d0c8070400302065020650c9a70203f0a8070201d0c83d0383d04001020650c8050c83d0c8050c811010050c83d0203d0c8111b03d0c812020650c83d0c80702065
|11=>0x81d0003d0003f0c80102064
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x708000000000000001b106480000000172000000000000000000143048800000000000000000000011100000f200000e100000b3024800000000000000000000000001c8000000000000000000000000000000000000000148041000000000000220000000000000000000000008000
|5,1=>0x10903e400003d100000000e8c3730000343000031300000000bc82c30000000000000000000000a4c0000000281094c0000850000078c000
|6,0=>0x90200008e223088a22208000000086220cc81220040001f887d11ec80001e48772000076100007421cc400000000000000712000000000006f200006d21a8c00019cc65218c861217c85e11708593000000015c80001548000150452213cc00013844c2000049300004721184000
|6,1=>0x36c8d9235c8d613508d223408cd332c8ca131cc0000000c5230c8000300cbe20000000000000000000002eccb830000b7100000002d48b322c840000000b1100000002bc8ac32ac40000000aa10000a8229880002944a3228489f227489a32644000260400025c4961000000024cc921
|6,2=>0x4dc93524cc8000000000000013124c052e24acd2924a05262490923148480000001201474d1b2000000000011a1464516344cc000440d0f143490b24285082414c000408c0004008fd300000000000fb20000f923dc8f433c88f020000ee23acce830000e623908e13000000037c8dd2
|6,3=>0x6148000000000061040006088000600800000017e25f080005e4d7815d880005d4400000017235bcc0005b856d15ac96925a0566258cd61258055e200015d156c9592560400055c555254c9521544400053c94d200014b2524947251840005108000508941100013e300000004f09393
|6,4=>0x6d49b326c49b016b89ac26a4c0000000000698da420001a2267cd9e167099b1660d9530001932640d8d300018b2628400061cc000
|7,0=>0x8c8a3028bc62d28aca29289ca25288ca21287ca1d286ca1928606162850a122840a0e2830a0a2820a062810a0228009fe27f09fa27e09f627d09f227c09ee27b09ea27a09e627909e227809de27709da27609d627509d227445cf27349cb27249c727149c327049bf26f49bb26e49b72
|7,1=>0xabcaad2aacaa92a9caa52a8caa12a7ca9d2a6ca992a5ca961a50a922a40a8e2a30a8a2a20a862a10a831a04a7f29f4a7b29e4a7729d4a7329c4a6f29b4a6b29a4a672994a632984a5f2974a5b2964a572954a5329486502938a4c2928a482918a442908a4028f8a3c28e8a3828d8a342
|7,2=>0xacc6b12
|8,0=>0xb106c31b086c11b006bf1af86bd1af06bb1ae86b91ae06b71ad86b510002b41
|_,_=>0
def PO:=mkPO wAt oP oO 20 9 511 14
def pmP:Nat→Nat
|0=>0x500000123000043800010c00004280001080000410000100000036c0000d9000030c00009900001440000430000108000041000010000002b00000980000220000080000018000003000000a00000240000080000018000004000000c0000020000004000000
|1=>0x402800100600040080010010004000000a2b0002808000900000201800076f0001dac0006ef00018bc00060000015bc00056b00011bc00042f00010a800040700010080004000000d8000022f0000810000202000070000016e00005980001620000540000149
|2=>0x872400210e000820000201800080280020010008000001b060006818001a0200064080018060005dbc00160400055bc00154d000528800146f000500000130600048180011eb00045bc0011660004590001108000412400104000040bc001023000403800100d
|3=>0x40044010010004000c010002004000400c42000255bc0091eb00245bc00912300241bc00902f0021088008420002050800802000200080075ef001d2bc0064bb00165ac00592f00155bc00532f001482800516b00144ac0050fb00140ac00410300095bc0021eb
|4=>0x1c05ec06d42f01b12bc06c46f01b10ac05902b01301bc04312f010642804092b010100004032b010002003906b00e01bc02d16b00a74ac02952f00a54ac02916b00a44ac02814b00803bc0200470080000015019004402401010900404080101000040140010040
|5=>0x100000023017b08803ac22006b08541ac21011908145b420516b080600c201045080010418020a05c07f414312d05084bc14056f05008bc13017f040442010056f04011bc100108040003810000803e04ac0f011b036042808500a020642008090a020193c07802b
|6=>0x81303ad00800a21b00bc86902b208000880e02218840ac62086b18060044b017b124006443802b10c05ac42026b108091c42006b108011c4200001004004400800
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x290d00180000020200050014000002020000000000000200000f02002200020002000000000f0200001100000000000202000000000000320002000f00080200000000000000020000000000000000000000020f000000020000000000000a00
|6,0=>0x65b020f70441a3c06132c0000016f00355200000000000076a5002a00002b020400007e00007c31870000a8000201007f02010111237e007e003b180000420f0002c083955a550000020c06c200021802000102000f00935d0000000002000000010001050048090b0b060f1107000001000c0059013d000f3d007d00015900
|6,1=>0x1a0000000f000200060000010100a97e0200b500001e05003b1f120b0f5c60021802000f060b18bf8102021882000602005f020604001600067e006200000123020c0100000000015906080239020202cf000027c8020080007e01051500240f02027e023e0088004d36000000020002022d064400053d0c0002102200007b06
|6,2=>0x27002213d0c47000000470200193038017e672200025771250126000300
|7,0=>0xc43ecd5198499a574b91b15e9e1051bec59bafb2b4546a73a150cbd2c1b4b931b2433faeb8a68d1b85c9518451405692398b7975314a649bcea4b39d53bc6597371716a3a2bacc588c6066ac314faaabd0512e6184b72fad45941c5496c3772046cabbbd4e864112b6781dc4a78fd1283a7472c7206b7333688ec64e4c90496d
|7,1=>0x7a8a
|8,0=>0x9fa06c9c51346ec4b0319bd363899969432f
|9,0=>0xe
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 26 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_236 7 roots_236 ops++addP pm 1 dom_110 7 roots_110 ops++addP pm 2 dom_230 6 roots_230 ops++addP pm 3 dom_234 7 roots_234 ops++addP pm 4 dom_168 4 roots_168 ops++addP pm 5 dom_174 7 roots_174 ops++addP pm 6 dom_228 5 roots_228 ops++addP pm 7 dom_164 4 roots_164 ops++addP pm 8 dom_202 5 roots_202 ops++addP pm 9 dom_102 4 roots_102 ops++addP pm 10 dom_166 5 roots_166 ops++addP pm 11 dom_78 4 roots_78 ops++addP pm 12 dom_206 6 roots_206 ops++addP pm 13 dom_138 4 roots_138 ops++addP pm 14 dom_142 5 roots_142 ops++addP pm 15 dzo_174_64 6 roots_174 ops++addP pm 16 dzo_168_64 4 roots_168 ops++addP pm 17 dzo_172_64 5 roots_172 ops++addP pm 18 dzo_170_64 5 roots_170 ops++addP pm 19 dom_106 4 roots_106 ops++addP pm 20 dom_226 4 roots_226 ops++addP pm 21 dom_204 4 roots_204 ops++addP pm 22 dom_108 4 roots_108 ops++addP pm 23 dom_46 4 roots_46 ops++addP pm 24 dom_170 5 roots_170 ops++addP pm 25 dom_172 5 roots_172 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_238 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_174 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_228 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_166 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_78 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_138 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_142 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_174_64_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_168_64_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_172_64_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_170_64_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_226 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_204 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_108 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_46 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_172 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_236 7 s (0,roots_236.map (·&&&dom_236)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_238 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_236 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_238==dom_238)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_238 gM v ys):RunD true dom_238 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_238 gM mpG SD SS NN hAt idxH ori 0 mkPools s
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
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_238 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_238 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_238 roots_238 goal_238 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_238
theorem lowS_238:Lower true dom_238 roots_238 goal_238 10:=S_238.noCircuit
namespace S_249
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(1,129),(8,9),(8,40),(8,136),(16,17),(16,80),(16,144),(24,25),(24,56),(24,88),(24,152),(32,33),(32,40),(32,160),(48,49),(48,56),(48,112),(48,176),(64,65),(64,80),(72,73),(72,88),(72,104),(72,200),(96,97),(96,104),(96,112),(96,224),(128,129),(128,136),(128,144),(128,160),(192,193),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_249.map (·&&&dom_249)
def gM:=goal_249&&&dom_249
def NN:Nat→Nat
|6=>1
|7=>5
|8=>2
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x8c72
|7,0=>0xa32f1661252bbac25e6824b3a
|8,0=>0xb3f6f262dc
|9,0=>0x2c020
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x3020302000000000302030200000000030203020000000003020302c0c0c0c0c080c080c0c0c0c0c080c080c0c0c0c0c080c080c0c0c0c0c080c0b00030003000300030003000300030003000300030003000300030003000300c0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c0000000202020202020202020202020202020202020202020202020202020202020202c0c0c0c0c000c000c0c0c0c0c000c000c0c0c0c0c000c000c0c0c0c0c000c0303030302020202030303030202020203030303020202020303030302020202c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c000302030203020302030203020302030203020302030203020302030203020302c0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0c0c000000000000000303030303030303030303030303030300000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x738610573861047386107386a1047328109738610947386105732610543210
|_=>0
def sO:Nat→Nat→Nat
|6,0=>6
|7,0=>0x23771d5736067
|8,0=>0xc5ea7
|9,0=>0x386
|_,_=>0
def wAt:=mkWire dB 11 250 0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1e17649f8661976521765217661d865e1865d9
|_=>0
def oO:Nat→Nat→Nat
|6,0=>3
|7,0=>0xb292725232
|8,0=>0xe1d1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0x1fff46fe7eff5f9fc7e00
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>1
|7,0=>0x34876
|8,0=>0x52
|9,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 9 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_233 8 roots_233 ops++addP pm 1 dom_121 8 roots_121 ops++addP pm 2 dom_185 8 roots_185 ops++addP pm 3 dom_241 7 roots_241 ops++addP pm 4 dom_217 7 roots_217 ops++addP pm 5 dom_248 7 roots_248 ops++addP pm 6 dom_216 4 roots_216 ops++addP pm 7 dom_240 4 roots_240 ops++addP pm 8 dom_209 5 roots_209 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_249 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_216 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_240 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_209 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_233 8 s (0,roots_233.map (·&&&dom_233)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_249 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_233 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_249==dom_249)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_249 gM v ys):RunD true dom_249 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_249 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 5 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 2 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_249 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_184_64:=0x101010101010101000000000000000001010101010101010000000000000000
def gzo_184_64:=0x101010101010100000000000000000001010100010100000000000000000000
def gsh_184_64:=0x10101010101010000000000000000000101010001010000
theorem lowS_zo_184_64_168:Lower true dzo_184_64 roots_184 gzo_184_64 5:=lower_iso_b (d1:=dom_184) (r1:=roots_184) (T1:=gsh_184_64) [(dom_184,64)] (by decide +kernel) (lower_slice_b (T:=gsh_184_64) [(0x10100000101000000000000000000000101000001010000,0,16)] (by decide +kernel) lowS_168)
def dzo_218_32:=0x505050500000000050505050000000005050505000000000505050500000000
def gzo_218_32:=0x505050500000000050505050000000005050504000000000504050000000000
def gsh_218_32:=0x5050505000000000505050500000000050505040000000005040500
theorem lowS_zo_218_32_82:Lower true dzo_218_32 roots_218 gzo_218_32 6:=lower_iso_b (d1:=dom_218) (r1:=roots_218) (T1:=gsh_218_32) [(dom_218,32)] (by decide +kernel) (lower_slice_b (T:=gsh_218_32) [(0x5000500000000000500050000000000050005000000000005000500,0,8),(0x5050505000000000505050500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_82)
def dzo_210_32:=0x5000500000000000500050000000000050005000000000005000500000000
def gzo_210_32:=0x5000500000000000500050000000000050004000000000004000000000000
def gsh_210_32:=0x50005000000000005000500000000000500040000000000040000
theorem lowS_zo_210_32_82:Lower true dzo_210_32 roots_210 gzo_210_32 5:=lower_iso_b (d1:=dom_210) (r1:=roots_210) (T1:=gsh_210_32) [(dom_210,32)] (by decide +kernel) (lower_slice_b (T:=gsh_210_32) [(0x50005000000000005000500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_82)
def dzo_186_64:=0x505050505050505000000000000000005050505050505050000000000000000
def gzo_186_64:=0x505050505050504000000000000000005050504050504040000000000000000
def gsh_186_64:=0x50505050505050400000000000000000505050405050404
theorem lowS_zo_186_64_168:Lower true dzo_186_64 roots_186 gzo_186_64 6:=lower_iso_b (d1:=dom_186) (r1:=roots_186) (T1:=gsh_186_64) [(dom_186,64)] (by decide +kernel) (lower_slice_b (T:=gsh_186_64) [(0x40404040404040400000000000000000404040404040404,0,2),(0x50500000505000000000000000000000505000005050000,0,16)] (by decide +kernel) lowS_168)
namespace S_250
def pG:List (Nat×Nat):=[(2,10),(2,18),(2,66),(2,130),(8,10),(8,40),(8,136),(16,18),(16,80),(16,144),(24,26),(24,56),(24,88),(24,152),(32,40),(32,160),(34,42),(34,50),(34,98),(34,162),(48,50),(48,56),(48,112),(48,176),(64,66),(64,80),(72,74),(72,88),(72,104),(72,200),(96,98),(96,104),(96,112),(96,224),(128,130),(128,136),(128,144),(128,160),(192,194),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_250.map (·&&&dom_250)
def gM:=goal_250&&&dom_250
def NN:Nat→Nat
|4=>7
|5=>18
|6=>46
|7=>36
|8=>12
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xc7bf2b29084c53628c0526ead0f3b308e17
|5,0=>0xe35d7da108d8c03bd37bb2dada820286de68431c761757151a6cea166dab5865a5550253b5b178f6104680a54d
|6,0=>0xef8d0eb259d8bebc6baaa7930a6e44a6c67a63caa50e09c8d39c47097a7a933c0924208710b84b0f849898261779aa5719c2705d66f21a672506345f625725ebed5ea505d6ea5cef25b14458d7d4f35f4eeb94addd47b89435103d5f43b2ab387bf33bfa2a61822c9022a721eb8a16947132dd
|7,0=>0xfdc38fc02ce6b7ad0879c7a46bc7d1b799c97ddf973be8f03e8d08e85d9e79c83772f1763707412972b916f0b96939d63def613c85b2e7594955531b50a734756339f5b38e2c36aba2d38620ffc182211786e166af1188a09cd9
|8,0=>0xef2e1df606a480673b1266ea96234939dad39127309b61cf321991212b8d
|9,0=>0xef2e1
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xa0a0a0a0a0a080800000000000000000a0a0a080a0a080940014001400140014001400140014001400140014001400140014001400140000000002828282800000000282828280000000028002800000000002800280505050505050505050505050505050505050404050504040000000000000000a0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0a000000014141414141414141414141414141414141400001414000014140000141400028202820282028202820282028202820282028202820282028202820282028250505000505050005050500050505000404040004040400040404000404040080808080808080808080808080808080808080808080808080808080808080941410101414101014141010141410101414101014141010141410101414101282800002828000028280000282800002828000028280000282800002828000505050505050404050505050505040405050504050504040505050405050404a0a0a000a0a0a000a0a0a000a0a0a000a0a0a000a0a0a000a0a0a000a0a0a0141414141010101014141414101010101410141010101010141014101010101282828282828282800000000000000002828282828282828000000000000000505050505050505050505050505050500000000000000000000000000000000
|0,1=>0x20202020202020202020202020202020202000002020000020200000202000141414141010101014141414101010101414141410101010141414141010101282828282828282828282828282828280000282000002820000028200000282005000500050005000500050005000500040004000400040004000400040004a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a000000000000000141414141414141414141414141414141414140014141400141414001414140282828280000000028282828000000002800280000000000280028000000000000050500000404000005050000040400000504000004040000050400000404a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a080a0a0a080a000a000a000a01414101014141010000000000000000014141010141410100000000000000002828282028282820282828202828282028282820282828202828282028282820000000000000000505040405050404000000000000000005050404050504040000a0800000a0800000a0800000a0800000a0800000a0800000a0800000a0941414141414141414141414141414141400140014001400140014001400140282028202820282028202820282028202820000028200000282000002820000505050505050505050505050505050504040404040404040404040404040404
|0,2=>0xa000a000a000a000a000a000a000a000a0008000a0008000a0008000a0008000000000000000000000000000000004040400040404000404040004040400000000000000000000000000000000028282820282828202828282028282825050000050500000505000005050000050505040505050405050504050505042020200020202000202020002020200020202000202020002020200020202014141414141414141414141414141414141410101414101014141010141410100002828000028280000282800002828000020200000202000002020000020250500050505000505050005050500050505000405050004050500040505000400a000a000a000a000a000a000a000a000a0000000a0000000a0000000a000141414141414141414141414141414140404040004040400040404000404040282828282800280028282828280028002828282828002800282828282800280000000000000000000000000000000005050500050505000505050005050500a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a080a080a080a080a080a080a080a0941414141414141410101010101010101414141414141414101010101010101000800080008000800080008000800080008000000080000000800000008000404040405050505040404040505050504040404050405040404040405040504
|0,3=>0x14141414141414141400140014001400141414141414141414001400140014028282828282828282828282800000000282828282828282828282828000000000000000000000000000000000000000505050505050505000000000000000000a000a000a000a000a000a000a000a000a000a000a000a000000000000000040404040000000004040404000000000404040400000000040404040000000282828282828202028282828282820202828282828282020282828282828202505050505050505050505050505050505050505000000000505050500000000a0a0a0a0a0a0a0a0a0a00000a0a00000a0a0a0a0a0a0a0a0a0a00000a0a000000000000000000000000000000000001410141014101410141014101410141282828282828282828282828282828282828282028282820282828202828282000000500000005000000050000000500000004000000040000000400000004
|_,_=>0
def sP:Nat→Nat
|0=>0x4875802ca3872012da18e4011423980402c63880402c31924012c544e4012c548e1cc2c33873002c34470402c338730b15738730538735600b54a39005414e1cd00b15241304b1922012c345004f14238014e1cd30b2892010c60810040c2040
|1=>0x1c80402d415238700b18e1e70402c53879810252d414e1c02c615239004b0c63900402e418e1c100b1633901db2c31921c10053a21cd0402c544e1c100b14e1e104014e8070402c33877c101e0c524100b14e1dd0402c32894012c525071b2c3
|2=>0x48e1d600b0ca24704079514938100b14e1cc2da14e40704b0c58c70407853906cb1493906cb0ca3901c12ed14e1c100b14e40771b2c53901e704b6863870402ec14e1c100ba8e1e90402ca387ac100b28e1e90400c56470402e814e1c100b14e
|3=>0x2c524e1db01e14938100b0c52470402f31523870402c314e4070402ea14e1c100b1723870402da2853870402c525070100bc453870402c52524012c54901dc04b14e1f00402ca14939004b14e1cc00b14e1ef0402da1491c100b14e1ee0402c5
|4=>0x2c52521c100b14e40770100b50538700b14e1c1dc02c53876f70053991c1005387d9b00b1523901c12c53874c10352c53870402c314e1db00b28524e1c100b68314e1c100b5453870402c58ce407040d0b1853870402ea2853870407853876c0
|5=>0xd810392c53870402c314e1c101e14e1c100bcc538704078b14e1c100b185387040d0b14e1c100b28538704014e1f6e002c61523870400c5387d8100b14e1dc040d0b14e8870402e414e1c100b0c54870402c524e40100a14e1f60402c53901db
|6=>0xb14e1c100b14e1c100b17a3870402c53901c1005387
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x1e5065414503d40a50154005
|5,0=>0x22188261f187661c186a619185e61618526131846610543b60d582f60a58236
|6,0=>0x6fddb876c99ab7691d9d765d9907625d8275edd7475b5d685585d5a755554f6521d4174e9d3374b1d257479d177441d0a640dcfc73d5cee739dce07365cd2732dcc472f5cb672bdca8728989b725588e7
|7,0=>0xb01ab88ac5eaa7a8a29b7a51e8d7a19e8069e5e7189ada647975e576945a4a790de3c78d5e2d889621e785a20e881a20067e5df367b1de487721d57739dc68
|8,0=>0xc45b0a7c0defd6bd9eef7ba5ae27b6ded47b35ec67
|9,0=>0x3176
|_,_=>0
def wAt:=mkWire dB 59 251 0x7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 14
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x3856a17287450114e522c3804e420d0070114e4607147431f181c51d380430314e401d0404e0148bce012890e1d1404d1d48bce01287c50138745392c7451d0d005390c04e15647522c38043403854e012890501387451d5804604147560138546041475601181051d2454e1d1474509
|1=>0x2c0451d28745010404b1d38741013874b1d3874e1538045051c04539150401d240ce1d28e450139087012894e1d3804701390870158046041474a3914046041474b1d3875601181051d1524e0139047011c041012c74e1d0074101540ce42007410138a85014854e01240c5a5150831f
|2=>0xe051c04b1f2c145392c745052c7451d2c04501040cb1f380451d2c7ce1539087011c14b010c0c5393804539387401d1404b1f00741013874e013908701181c51d6cec1016cec10148b0e012c7c1013804701245ce1d2c6451d385410138745010c045390c74e153904701
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x11001
|5,0=>0x1c11a21821531321210f30e10b3000074043000022000000
|6,0=>0x6826716436220000005f30005d20005b20005925635425224f34c30004b14834624424314123f23c33933813533320003213022f10002d22b22a12822530002232021d3000
|7,0=>0xb02ae2ac2aa2a82a62a42a22a029e29c29a29829629429229028e28c28a28828628428228027e27c27a27827627427227026e26c26a2
|8,0=>0xbc1bb1ba1b91b81b71b61b51b41b31b21
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 12
def pmP:Nat→Nat
|0=>0x117400045c0000fb40003a00000c200003040000c0000022d000073400018d0000600000145000051000010100004000000c000002a00000a00000210000081000020000004100001000000200000074000008000001800000500000100000020000004000000
|1=>0x19b774060cdd01233f4046d5d011b3f4046c5d0112d14040c5d00937740248c50083b7402085d004117401001f00202a40080a10020224007d5d001f4f4005d5d00173f4005b450016114004d5d00129140020410004c14000edd00039f4000e5d00011f400045f
|2=>0x819b175124c5d2088044430c5f108003821645d084804418475d0611d7018445d0521174124c5d0491f74100cfd0220d1008830c02173f4085cbd
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x102
|5,0=>0x424086182050206003850024000
|6,0=>0x21c4e4c00066009000a547b2246dfb62238a1202398105e7871d0600c83102c09a10045004c35680
|7,0=>0x42611a89f2a4a948f9514691a3206ae55bb8a5a1c14b2d8bf6eba04d2ef5642
|8,0=>0x3f41c22a321e4e7512647
|9,0=>0x1f
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 7 (j%128);fld (pmP (k/32)) 26 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_248 7 roots_248 ops++addP pm 1 dom_146 4 roots_146 ops++addP pm 2 dom_242 7 roots_242 ops++addP pm 3 dom_234 7 roots_234 ops++addP pm 4 dom_218 7 roots_218 ops++addP pm 5 dom_168 4 roots_168 ops++addP pm 6 dom_122 7 roots_122 ops++addP pm 7 dzo_168_64 4 roots_168 ops++addP pm 8 dzo_82_32 4 roots_82 ops++addP pm 9 dom_82 4 roots_82 ops++addP pm 10 dom_186 7 roots_186 ops++addP pm 11 dzo_184_64 5 roots_184 ops++addP pm 12 dom_240 4 roots_240 ops++addP pm 13 dzo_218_32 6 roots_218 ops++addP pm 14 dzo_210_32 5 roots_210 ops++addP pm 15 dom_106 4 roots_106 ops++addP pm 16 dom_138 4 roots_138 ops++addP pm 17 dzo_186_64 6 roots_186 ops++addP pm 18 dzo_90_32 5 roots_90 ops++addP pm 19 dom_226 4 roots_226 ops++addP pm 20 dzo_170_64 5 roots_170 ops++addP pm 21 dom_90 5 roots_90 ops++addP pm 22 dom_170 5 roots_170 ops++addP pm 23 dom_184 5 roots_184 ops++addP pm 24 dom_178 5 roots_178 ops++addP pm 25 dom_154 5 roots_154 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_250 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_146 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_168_64_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_82_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_184_64_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_240 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_218_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_210_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_138 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_186_64_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_90_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_226 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_zo_170_64_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_184 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_178 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_154 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_248 7 s (0,roots_248.map (·&&&dom_248)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_250 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_248 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccccccccccccccccccccccccccccccc,126)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_250==dom_250)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_250 gM v ys):RunD true dom_250 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_250 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 7 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 18 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 18 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 46 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 46 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 36 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 36 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 12 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 0 = true)
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
def isoMvS_111:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)]
theorem lowS_111:Lower true dom_111 roots_111 goal_111 9:=lower_iso_b isoMvS_111 (by decide +kernel) lowS_63
def isoMvS_119:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_119:Lower true dom_119 roots_119 goal_119 8:=lower_iso_b isoMvS_119 (by decide +kernel) lowS_95
def isoMvS_125:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_125:Lower true dom_125 roots_125 goal_125 9:=lower_iso_b isoMvS_125 (by decide +kernel) lowS_123
def isoMvS_183:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_183:Lower true dom_183 roots_183 goal_183 8:=lower_iso_b isoMvS_183 (by decide +kernel) lowS_159
def isoMvS_222:List (Nat×Nat):=[(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_222:Lower true dom_222 roots_222 goal_222 9:=lower_iso_b isoMvS_222 (by decide +kernel) lowS_221
def isoMvS_231:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_231:Lower true dom_231 roots_231 goal_231 7:=lower_iso_b isoMvS_231 (by decide +kernel) lowS_207
def isoMvS_237:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_237:Lower true dom_237 roots_237 goal_237 9:=lower_iso_b isoMvS_237 (by decide +kernel) lowS_235
def isoMvS_243:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_243:Lower true dom_243 roots_243 goal_243 9:=lower_iso_b isoMvS_243 (by decide +kernel) lowS_221
def isoMvS_246:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_246:Lower true dom_246 roots_246 goal_246 9:=lower_iso_b isoMvS_246 (by decide +kernel) lowS_221
def isoMvS_252:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_252:Lower true dom_252 roots_252 goal_252 10:=lower_iso_b isoMvS_252 (by decide +kernel) lowS_250
def dzo_119_8:=0xff00ff00ff00ff00ff00ff00ff00ff00
def gzo_119_8:=0xff00ff00ff00fe00ff00ff00fe00ee00
def gsh_119_8:=0xff00ff00ff00fe00ff00ff00fe00ee
theorem lowS_zo_119_8_84:Lower true dzo_119_8 roots_119 gzo_119_8 7:=lower_iso_b (d1:=dom_119) (r1:=roots_119) (T1:=gsh_119_8) [(dom_119,8)] (by decide +kernel) (lower_slice_b (T:=gsh_119_8) [(0xaa00aa00aa00aa00aa00aa00aa00aa,0,1),(0xcc00cc00cc00cc00cc00cc00cc00cc,0,2),(0xff00ff0000000000ff00ff00000000,0,32)] (by decide +kernel) lowS_84)
def dzo_87_8:=0xff00ff0000000000ff00ff00
def gzo_87_8:=0xff00fe0000000000fe00ee00
def gsh_87_8:=0xff00fe0000000000fe00ee
theorem lowS_zo_87_8_84:Lower true dzo_87_8 roots_87 gzo_87_8 6:=lower_iso_b (d1:=dom_87) (r1:=roots_87) (T1:=gsh_87_8) [(dom_87,8)] (by decide +kernel) (lower_slice_b (T:=gsh_87_8) [(0xaa00aa0000000000aa00aa,0,1),(0xcc00cc0000000000cc00cc,0,2)] (by decide +kernel) lowS_84)
def dzo_95_32:=0xffffffff00000000ffffffff00000000
def gzo_95_32:=0xfffffffe00000000fffefffa00000000
def gsh_95_32:=0xfffffffe00000000fffefffa
theorem lowS_zo_95_32_82:Lower true dzo_95_32 roots_95 gzo_95_32 7:=lower_iso_b (d1:=dom_95) (r1:=roots_95) (T1:=gsh_95_32) [(dom_95,32)] (by decide +kernel) (lower_slice_b (T:=gsh_95_32) [(0xaaaaaaaa00000000aaaaaaaa,0,1),(0xf0f0f0f000000000f0f0f0f0,0,4),(0xff00ff0000000000ff00ff00,0,8)] (by decide +kernel) lowS_82)
def dzo_87_32:=0xff00ff0000000000ff00ff00000000
def gzo_87_32:=0xff00fe0000000000fe00fa00000000
def gsh_87_32:=0xff00fe0000000000fe00fa
theorem lowS_zo_87_32_82:Lower true dzo_87_32 roots_87 gzo_87_32 6:=lower_iso_b (d1:=dom_87) (r1:=roots_87) (T1:=gsh_87_32) [(dom_87,32)] (by decide +kernel) (lower_slice_b (T:=gsh_87_32) [(0xaa00aa0000000000aa00aa,0,1),(0xf000f00000000000f000f0,0,4)] (by decide +kernel) lowS_82)
def dzo_91_32:=0xf0f0f0f000000000f0f0f0f00000000
def gzo_91_32:=0xf0f0f0e000000000f0e0f0a00000000
def gsh_91_32:=0xf0f0f0e000000000f0e0f0a
theorem lowS_zo_91_32_82:Lower true dzo_91_32 roots_91 gzo_91_32 6:=lower_iso_b (d1:=dom_91) (r1:=roots_91) (T1:=gsh_91_32) [(dom_91,32)] (by decide +kernel) (lower_slice_b (T:=gsh_91_32) [(0xa0a0a0a000000000a0a0a0a,0,1),(0xf000f00000000000f000f00,0,8)] (by decide +kernel) lowS_82)
def dzo_83_32:=0xf000f00000000000f000f00000000
def gzo_83_32:=0xf000e00000000000e000a00000000
def gsh_83_32:=0xf000e00000000000e000a
theorem lowS_zo_83_32_82:Lower true dzo_83_32 roots_83 gzo_83_32 5:=lower_iso_b (d1:=dom_83) (r1:=roots_83) (T1:=gsh_83_32) [(dom_83,32)] (by decide +kernel) (lower_slice_b (T:=gsh_83_32) [(0xa000a00000000000a000a,0,1)] (by decide +kernel) lowS_82)
def dzo_117_8:=0x33003300330033003300330033003300
def gzo_117_8:=0x33003300330032003300330032002200
def gsh_117_8:=0x330033003300320033003300320022
theorem lowS_zo_117_8_84:Lower true dzo_117_8 roots_117 gzo_117_8 6:=lower_iso_b (d1:=dom_117) (r1:=roots_117) (T1:=gsh_117_8) [(dom_117,8)] (by decide +kernel) (lower_slice_b (T:=gsh_117_8) [(0x220022002200220022002200220022,0,1),(0x330033000000000033003300000000,0,32)] (by decide +kernel) lowS_84)
namespace S_127
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(2,10),(2,18),(2,66),(3,11),(3,19),(3,35),(3,67),(4,20),(4,36),(4,68),(5,13),(5,21),(5,37),(5,69),(6,14),(6,22),(6,38),(6,70),(7,15),(7,23),(7,39),(7,71),(8,9),(8,10),(8,40),(12,13),(12,14),(12,28),(12,44),(12,76),(16,17),(16,18),(16,20),(16,80),(24,25),(24,26),(24,28),(24,56),(24,88),(32,33),(32,36),(32,40),(34,35),(34,38),(34,42),(34,50),(34,98),(48,49),(48,50),(48,52),(48,56),(48,112),(64,65),(64,66),(64,68),(64,80),(72,73),(72,74),(72,76),(72,88),(72,104),(96,97),(96,98),(96,100),(96,104),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffffffffffff
def xsM:=roots_127.map (·&&&dom_127)
def gM:=goal_127&&&dom_127
def NN:Nat→Nat
|5=>2
|6=>18
|7=>77
|8=>171
|9=>84
|10=>11
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0x644e942b6c
|6,0=>0xea252e73a0dbfa7d3f2bbf1b394fcb5f4543e1a7382c035b242359b2038f1798816252121a70bfe807fa704bcf
|7,0=>0xfa04def39eea9e5e2585d9733cf2c0ce04dc5b77c3e4dbe9e5be4bdbd3f3b844fadc04a32469cb4097e4d8fdd18fc488ccb6816c37f84e7f4777c8ae7b36a793767721a76ebc741476e6df6d1da6bc2a687de6639865dbb6502261c0557c6a55ca9556c354ef2534e849a3d4683b4537944cbb426df3e4e43e17f3bd3d36e6136198352382c24f28ef22857126b3226b2e237cc207b21eeaf1e5cf19f93193791935d16c9e1272311c2311b191170f0f4bb0e0a60d6a50c56f08b52015df00683
|8,0=>0x62ca161f7b613b1602eb5d8c85d5925b6045b51d5a5ff58e92588cd584bd579325735f56cb954be753d2c51e98511164fe554ef9c4b7764a96249cb6495e24906f48d964867d481cb4535d42c9e41fe34137440ec040e6340d80404d83ed003ec2d3df433c7b73b6e73a2fd3999e394413875437be835f7b353d034edd32d8d31c6831a7b2fc982fa352f6d52e02c2deff2c24f2a00729f9629ca92804c27e9926fa4250f924f4b245282403623ece2329b21d5220ec81fe951fd701ee651d6ac1a87b1a4201a13319f9319ae319a28199561979019756194981935d1840616c9e1658f16506157401557f14fea131c711db211c6511b4f10d980fb970f41c0e4fc0dc310cf8c0cc730c0b00c0af0bcad0ae610a70e0a00b096970957508e56088ea0711d06d7c05fce05a7b04d2404c52047720419503b4402f9201fd800840
|8,1=>0xf4ab7e397fdc8eac8658c0279b3c68afc7dad733a8c36a27b0a00fc9817b95baa93cf193bc490d0c8f17a8c2eb8c2498b16686d7683fc4839998335f80d697e1557d00d7bbf878cac789c675ff8757bf7509c710f46eb126d6286d47f6c63a6c17b68ca367cf1654416410f
|9,0=>0xee133e5b4fe33a5d7b44d6882c8ab7bf9eaafc7daddcda9e0ea3c688dc818866587c6883c7d80b068056c7cc367a7e372b516d9546ba506aa6d69d1967bc464d0c6317a5c0a45bbbe5ad76567d45099b4fbf84d641476a34669841f6f4147f3e9633d36c3d09d3b9083a9023944138d693569734c36348752f0e62e31e292942924028381271b32689622f9c215431d8871cd961a4a01967017eb213f2b12b12113e41109d10fcf107891070f103020f8b00edcf0c6fe0b27d0a7920a6c70a32b09697093d00913f0888c06aad04ebc0398a
|10,0=>0xd8ebcaeb36939ea83c7d7de0e6c3bf581865456c5254f2fbbe15028
|11,0=>0x2654f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffffff00ff00ffffffffff00ff00ff00ff0000000000ff00ff0000000000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000000000000000ffff0000ff0000000000ff00ff0000000000ff00ff00ffffffff00000000ffffffff00000000ff00ff00ff00ff00ff00ff00ff00ff00eeeeeeeeeeeeeeeeeeeeaaaaeeeeeeaaffff0000ffff0000ffffffffffffff00ffffffffffffffff00000000000000000000000000000000ffffffffffffff00ffffffffffffffffffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffaaffaaaaaaaaaaffaaffaaaaaaaaaaf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0cccccccccccccccccccccccccccccccc
|0,1=>0x333333333333333333333300333333000f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000ffff0000ffff0000ffff0000ff000000000000000000ffffffffffff0000ffffffffffff0000ffffffffffff0000ff00ff00ff00ff00ffffffffffffff000000ffff0000ff000000ffff0000ff00ffffffffffffffff0000ffff0000ff0000ff00ff00ff00ff00ff00ff00ff0000ffffffffffffffffffffffffffff000000ff00ffffffffff00ff00ffffffff00ffffffffffffffffffffffffffffff00f0f0f0f0f0f0f0f0f0f000f0f0f000f000000000000000000000ff000000ff00fefefefefefefefefefeeefefefeeefefafafafafafafafafafaaafafafaaafa
|0,2=>0xffffffffffffffffffffffff00000000ffffffffffffffffff00ff00ff00ff00fff0fff0f0f0f0f0fff0fff0f0f0f0f0ffffffffffffffffcccccccccccccccc0000ffff0000ffff0000cccc0000cccc00ff00ff0000000000ff00ff0000000000000000ffffffff00000000ffffff00ffffffffffffff00ffffffffffffff0000000000000000000f0f0f0f0f0f000000000f0f00000f0f00000f0f00000000ff00ff0000000000ff00ff000000ff0000000000ffffffff00000000ffff0000ffffff00ffff0000ffffff00ffffff00ffffffffffffffffff00ff000000ff00ffffffffffffffffffffff00ffffff00ffccffccccccccccffccffcccccccccc
|0,3=>0xf0fff0fff0f0f0f0f0fff0fff0f0f0f00000ffff0000ffff0000ff000000ff00ff00ff00ffffffffff00ff00ffffff00ffffffffffffffffffff0000ffffff0033333333333333333333000033333300ffffffffffffffffffffff00ffff0000fffffffffffffffffffffffffffff0f0fffffffff0f0f0f0fffffffff0f0f0f0ffffffffffffffffffffffffff00ff0000ff00ffffffffff00ff00ffff00ff000f0f0f0f0f0f0f0f0f0f00000f0f0000000f000f00000000000f000f00000000ff00ff00ff00ff00ff00ff00ff000000ffffffff33333333ffffffff33330000333333333333333333330000333300000f0f0f0f030303030f0f0f0f03030000
|0,4=>0xfffff0f0fffff0f0fffff0f0fffff0f0fffffffffffffffff0f0f0f0f0f0f0f0ffccffccffccffccffccffccffccffccffffffff0f0f0f0fffffffff0f0f00000f0f0f0f000000000f0f0f0f00000000ffffffffffffffffff00ff000000000000ff00ffff00ff0000ff00ffff00ff00ffffffffccccccccffffffffccccccccff00ff00ff000000ff00ff00ff000000ffffff00ffff0000ffffff00ffff0000ffffffffffffffff0000ffff00000000ff0fff0fff00ff00ff0fff0fff00ff00cccccccccccccccccccccc00cccccc00eeeeeeeeeeeeeeeeeeeeeeaaeeeeeeaaffffff00ffffff00ffffff00ffffff000000000000000000ffffff00ffffff00
|0,5=>0xfcf0fcf0fcf0fcf0fcf0fff0fcf0fff00000000000000000000000000000ff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0fff0ccccccccffccffccccccccccffccffcccccccccccccccccccccccccccccccc000000000000000000ffffffffff00ff000000ffff0000ffff0000ffff00000000ff00ffffff00ffffff00ffffff00ff000f0f0f0f0f000f000f0f0f0f0f000f000000000000000000000000ff00000000ffffffffffffffff000000ff00000000ffffccccffffccccffffccccffffccccffffffffffffffffffff00ffffff0000f0f0f0f0f0f0f0f0f0f000f0f0f0000033333333333333333333333333333300fff0fff0f0f0f0f0fff0fff0f0f0fff0
|0,6=>0xf0f0f0f0f0f00000f0f0f0f0f0f00000000000000000000ff00ff00ff00ff00ccccccccccccccccffccffccffccffcc00000000000000003300330033003300ffff0000ffff0000ffff3300ffff3300fffffffffffffffffffffff0fffffff0fff0fff0fff0fff0fff0fff0fff0fff033333333333333333333333033333330cccccccccccccccccccc0000cccccccc00000000000000000000ffff00000000eeeeeeeeeeeeeeeeeeeeaaaaeeeeeeee5555555555555555555555555555550000000000000000000000330000003300ffffffffffffffffffffccccffffccccf0f0f0f0f0f0f0f0f0f0f3f0f0f0f3f0cc00cc00cc00cc00cc00ff00cc00ff00
|0,7=>0xff00ff00ff00ff00ff000000ff00000000ff00ff0000000000ffffff00000000f0f0f0f0f0f0f0f0f0f0f0f0f0f00000ffffffffffffffffffff3333ffff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff00ff00ff000000ff0000ccccffffccccffffccccffccccccffccff00ff00ff00ff00ff000000ff00ff000000ff000000ff000000ff000000ff00ffffffffffffffff0000ff000000ff00ffff3333ffff0000ffff3333ffff0000333333330000000033333333000000000000000000000000ffff3333ffff0000ffffffff00000000ffffffff0000ff00330033003300330033003300330033000000000000000000ffffffff00000000
|0,8=>0xffffffffffffffffffffffffcccccccc0000000000ff00ff0000000000ff0000ff00ff00ff00ff00ff00ff0000000000ffffffffffffffffffccffccffccffcc0000ffff0000ffff0000ffcc0000ffccccccccccccccccccccccffffcccccccc000000000000000000000000ff00ff00ffff0000ffff0000ffff0000ffffff000f0f0f0f0f0f0f0f0f0f0f000f0f0f000000ffff000000000000ffff000000000f0f0f0f0f0f0f0f00000f0f00000000000000000000000033333300333333000f000f000f000f000f000f000f000f00ffffffffffffffffffff0f00ffff0f00ffff0f00ffff0f00ffff0f00ffff0f00ccccccccccccccccccccffccccccffcc
|0,9=>0xfffffffffffffffffffff0f0fffff0f000000000000000000000ffcc0000ffcc0000000000000000ffffccccffffcccc0000ffff0000ffff0000f0f00000f0f0ffff000000000000ffff0f0f00000000ffffff00ffffff00ffffff00000000000f0f0f000f0f0f000f0f0f000f0f0f0000000000000000000f0f0f000f0f0f00000000ff000000ff000000ff0000000033333333333300003333333333330000ffffffffffffffff333333333333000033333333333333333300330033003300f0f0f0f0f0f0f0f0f0f0fff0f0f0fff0ffffffff00000000ffff000000000000ffffffffff00ff00ffffff00ff00ff0000000000000000000f0f0f0f00000000
|0,10=>0xffffffffffffffff33003300330033000000ffff0000ffff0000330000003300ffffffffffffffffffff3300ffff3300ffff00ffffff0000ffff00ffffff00000000000000000000ffff00ffffff0000ffffff0000000000ffffff0000000000ffffffffffffffffffffff0000000000ffffffccffffffccffffffccffffffccf0f0f0f000000000f0f0ffff00000000ccccccccccccccccffffffffffffccccffff0000ffff0000ffffff00ffffff00ffffccccffffccccffffffccffffffccffff0000ffff0000ffffffffffff0000ffffffffffffccccffffffffffffccccfffffffffffffffffff0fff0fff0fff00000ffff0000ffff0000fff00000fff0
|0,11=>0xff33ff33ff00ff00ff33ff33ff00ff00cc00cc00ff00ff00cc00cc00ff00ff00ff33ff33ff33ff33ff33ff00ff33ff00ff00ff00ff00ff00fffffff0fffffff0fffffffffff0fff0fffffffffff0fff0ffffffffff00ff00ffff0000ff0000000000000000000000fffff0f0fffff0f0ffffffff00000000fffffffffffff0f00000ffff0000ffff0000ff0000000000f0f0f0f0f0f0f0f0fffffffffffff0f0fffff0f000000000fffff0f000000000ffff0000ffffff00ffff0000ffffff000000000000000000ffffff00ffff0000ffff3333ffff3333ffff3333ffff0000333333333333333333333333000000000000000000000000ffccffccffccffcc
|0,12=>0xff00ff00ff00ff00cc00cc00cc00cc00f0f0fffff0f0f0f0f0f0fffff0f0f0f000ff00f000ff00f000ff00f000ff00f0fffffffffffffffffffffffff0f0f0f0ffffffffffffffff0f0f0f0f00000000ff00ff00ff00ff00ffffffffff00ff00fffffff0fffffff0fffffff0fffffff000ff00cc00ff00cc00ff00cc00ff00cc00000000ffccffcc00000000ffccffcc00ff00ffffffffff00ff0000ffff0000ffffffff33003300ffffffff330033000000ffcc0000ffcc0000ffcc0000ffccffffffffffffffff0000ffcc0000ffccffffffff00ff00ffffff000000ff00000000000033003300000000003300330000cc00cccccccccc00cc00cccccccccc
|0,13=>0xff00ffffffffff000000000000000000003300000033000000330000003300fffffffffffff0f0fffffffffffff0f00000000000000000fffffffff0f0f0f000000000ffffff0000000000ffffff0033333300333333003333330033333300000000000000ff00000000000000ff00ff00ff00ff00ff0000000000ff00ff00
|_,_=>0
def sP:Nat→Nat
|0=>0x1000d150616210302010006030201000c060503020100060a0409000d27260a232201000d16210320010d06140403020100060a03090d1f1e06040e01000d1d061a030201000607040e01000d06030201001806040301000d15061403020100060a030911100604030201000c060a0309010806070402010006050403020100
|1=>0x142060a400320010d060a033f01000d3e060a033d01000d060a0309010d3b060a3a030901000d060a0309000d1e060301000d36061c0302090100060a0309000d3534061b032d2e000d060a21033301000d060a210320010d060a0309000d3006040301000d170b062f03202e010d1604032d09000d061b0901000d2b0b0603
|2=>0x35009000d06160a4f094e000d0a040309010d3b060a034d09000d1e060a21032d000d064c0309000d4b061b414a01000d320a0309000d30060f040301000d49060301000d2a29060f480309010d31060a3a460901000d061603020901000604030901000d450b3703020100061c04030901000d0b0a034409000d35060a0309
|3=>0x2f46032e01000d0a035025000d0603580e01000d060a0309000d5735060a2104032d000d060a40040901000d3e0f0a540409012c0d0a04030901000d550a03222501000d0a540409012c0d0b1b03022e0100060a030952000d060a0409010d1f3e060f0403020100060a0309010d510616040302090100060a40032d000d060a
|4=>0x604030e01000d0c060a030901006406070a040901000d060a030961000d060a03095f000d060a0403095d000d061621030e01000d06050a04030901000d030e01000d0c0605030e01000d060a0409000d1e2606160309015c000d060a040309010d5106160a0309010d1f060a0309015b0d061b410201000607030e01000d06
|5=>0x720a030901000d060a0309010d31710670030901000d6f061b032d09000d060a0403093f01000d060a040302090100060a41036d01000d060a41034a01000d060a6b030901000d061404030e01000d060a0309010d68060a040309010064060a0309016506040301000d490603020100190614030e01000d0632030901000d0b
|6=>0x41034e01000d2a060f0a030901000d2b060a03090180000d060a030901000d7e06030901000d7459060a03097d000d060f0301000d49060a7c030901000d060301000d7b0b060a21030901000d061638030901000d060a03090179000d060a0403097801000d060a030901000d2b0b060a034d01000d76060a73030901000d06
|7=>0x3a030901000d061c030901000d4b060a0309000d1e06390a030901000d060a030901000d870638030901000d59060a030901000d85060a03580901000d060a0309012c000d760a030901000d84060a036d09012c0d060f04030e01000d06160403090e01000d060a8281030901000d060a040901000d59060a540409012c0d0a
|8=>0x38d01000d061b032e0e01000d060a032e012c000d770a030901000d8b060a210309012c000d0a81032e01000d060a040309018a0d060a034d01000d1206040301000d2a0b060a033d01000d060a88030901000d060f0a030901000d35061b03094a01000d0a21040901000d3e060a04030901000d5606070a030901000d060a
|9=>0x30901000d4b060a9a030901000d06050a030901000d060a3a460901000d060a030901000d98060a030901000d97060f03020100061b0a030901000d95060a0309012c0d94060a030993000d060a91030901000d060a6a030901000d061b030901000d90061b8f030901000d060a030901000d8e06380a030901000d3e060a41
|10=>0x540309010d960628030e01000d060a030901000da0060f0a9f030901000d060a032e01000d99060a460901000d061b410e01000d060a030901000d352a060a030901000d0c060f4804030901000d060a030901000d9e061b0a4f094e000d062f0a9d030901000d720a04030901000d060a9b030901000d060a41032d000d0616
|11=>0xd060a3a03094a01000d060aa4a5030901000d060f0a040301000d83060aab030901000d060aa9030901000d060a3a04030901000d060a040309000d1e060aa8036e01000d06160a21030901000d062f0302090100060a0309a701000d06a60a030901000d060aa4030901000d06a3030901000d0b060a033d0901000d060a
|12=>0xab2030901000d060a03580901000d59061bb50901000d060a9f030901000d2a062fb4030901000d060a53030901000d060a21040309010d1f06320a030901000d060a032501000d060a21030e01000d060ab3030901000d060ab2030901000db1060a04030901000d57060a4103b001000d060a030901000dae060aad030901
|13=>0x4e01000d59bb0a04030901000d060a04030901000d76140a030901000d060a54040901000d0b060a0301000d2a12060a46040901000d060a03ba0901000d060a40030e01000d060a04030901000d0c06b80a030901000d060a210301000d2a060a03094a01000db70a414701000d06b61c0a030901000d060a030901000d6306
|14=>0xa0403090100be0d060f0a540309012c0d060a41033f01000d060a5304030901000d060a036909000d35060a540309012c0d0b060a0403093301000d060a04032009010d060a030901670d060a03092501000d060a036901000d3e060a03bd0901000d060abc030901000d060a400301000d2a060f0a54040901000d060a0309
|15=>0x1706c50a04030901000d060f0a04030901000d060301000d4906380a04036909000d060a210301000d83060a030901000dc306140a04030901000d060a03c20901000d060a040301000d2a12060a04030901000dc1060a040309010dc0060a0403bf0901000d060a21040301000d2a06160a034d0901000d06030e01000d1906
|16=>0xd9c060ac94f030901000d060a032e01000d77060a030901000dc8060a21030901000d060f48030901000d060a4f032e0901000d060a5403096e01000d060a034d01000d77060a04030901000d71060a41032e01000d060a04030901000dc7061648030901000d060a03097801000d060a030901000dc6060a04030901000d
|17=>0xd060f0a0301000d83060a40030901000d060a036e01000d2a062f030901000d74061b03090e01000d061b48030901000d060a54040901000d060a030901000d12060a030901000dcd060a030901000d96060a81030901000d060a04030901000d8306cc0a03094e01000d060a030901000dcb06ca0a030901000d060a030901
|18=>0xa03a10901000d060a460901000d060a03094701000d060a2104030901000d060f0a4f030901000d060a030901000dd2060aa5030901000d060a030901000dd1060a030901000d19060a030901000dd0060a03090100cf0d062f0a4f030901000d060a540309012c0d060a030901000d5706382f030901000d060a0309ce0100
|19=>0x1000d060a0309012c000d6c060a0403690901000d060a03090100be0d060a03094a01000d060a0309012c000d0b060a032009010d060a410301000d2a062f030901000d4b062f0a41030901000d06d50a030901000d06bb0a030901000d06d40a030901000d060a030901000dd3060a04030901000d12060a0309015c000d06
|20=>0xd060a030901000d2406380a41030901000d06c50a030901000d060f0a030901000d06370a030901000d060a04034d0901000d06380a036909000d060aac030901000d060a030901000dd6060a032e09012c000d2f0a030901000db1060a030901000d31060a62030901000d060a030901000dc1060a0309010dc0060a03bf09
|21=>0xd060a032e0901000d060a034d0901000d060a04030901000d060a03690901000d060a030901000d86060301000d2a0b060f030e01000d060a030901000dd70a0302090100061b0a410901000d060a030901000dc7060a0403090e01000d060f0a04030901000d061b1c0a030901000d060a04030901000d0b060a03097f0100
|22=>0xa030901000d060a030901000d71060a030901000d74060a03090e01000d060f0a030901000d060a030901000d0b060a5403090100
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x660006
|6,0=>0x7b6074706e60686061705b6054704d7046703f70396032702c6025701f60196012700c6
|7,0=>0x252824a8242823b7234722c8224821c8214820d7207620071f971f271eb71e381db81d381cb81c381bc71b481ad71a6719e8197719071888181717a7173716b8163815c7155714f6147813f813871308128812171198113610b810380fd60f670ee80e770e070d880d170cb60c470bc80b570ad80a6709f70978091608980818
|7,1=>0x2b082a972a1829b6294728e6287727f8277827072688261725a7
|8,0=>0x4b374ab84a3849b8493848b8482947a8472846a8462845a8452844a8442843a8433742b8422941b74129409940183f983f183ea73e283da83d283ca83c283ba83b283aa83a283999390938883817378936f9367835f8357835073497341833a7332832a8322831993109308830082f882f082e882e172d892d082c882c082b88
|8,1=>0x6b986b096a886a086988691768896808678866f9668765f9657864f8646963e8637762f8627861e9615960d860585fd85f495eb95e295da85d285c995c185b985b095a975a1859985918589858185798572756a856195598552754b7542953a853195298521851985109508850174f984f184e984e184d984d184cb64c294ba8
|8,2=>0x81f9817880f880787fe97f597ec97e667dd97d587cd87c497bc87b397aa97a287999790978797807777976e9766875d9755874c9743973b8734772c8724871c8714870c870396fb86f296ea86e286d996d186c986c18
|9,0=>0xa2c8a239a1b8a138a0b8a0479fc89f399ea99e289da89d199ca79c289ba89b199a989a1899989918988998089788971796989609957994f8947893f8937892f8927891e9916890e890688fe88f688ee88e688de88d688ce88c688be88b688ae88a6889d9894988c8884887c8873986b8863885b8853884a98419839883098288
|9,1=>0xacf7ac87ac17aba7ab28aaa8aa19a989a8f9a869a7e8a768a6d9a658a5d8a558a4c9a448a3c8a348
|10,0=>0xb268b1e8b168b0e8b068afe8af68aee8ae68ade8ad68
|11,0=>0xb2e7
|_,_=>0
def wAt:=mkWire dB 216 128 0xffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xe0d428240a0441025030643c130e0d40c190a09428240e0d4a01b0f03428250a090781b1601c10290325494190924c102b0306438010a0902811040943c110e0d40c190a09428240e0d42471090a0186e0a0343835190643c0f0a0942824170b428260916810290f04438350306428250a0900041130d4044b040980c190f04c38350306428250a090102d030642826
|1=>0x430d48400032e424190e004282406418240d212ac241103064242a3c00c102d03064282616210281104094e407043840c190a014dc3b0f06428250a0903835090a0186e0a0340c190e014242809064280d16090281104094380104094282403064c8070a31410030306428260916810290e00428240a06424190e0141029090a00c19032c8a8a50a218241103064242a
|2=>0xa09050030f0442825030643835040a424280306438050a09019060903494050924c102b030641029010640c1901034f003040b428261601c28110306438050409428240306428d50401c28070306438190a090280d0903428c50400c0c190f0ec0c190a09428240a218241103064242a090a40c1903474246c0a0343835040a4242803064242b0e0d43c190a0942824
|3=>0xf04428252100c50000f04428250306438350a090280d09035680d0f06c28250a090380d0a09028190906494050924c102b030642565090a00cbe0a0640c190e01410250a0900c192106c1025060340c190a0940019560642887040940c19250642493040ac0c190a09800190306438350a090280d090654c04042a40c19090a884032103c1025060343835030642825
|4=>0x46940c190901450370f0442825670d4019b040a80c19030643c3b0a09428240f03c38350a09428240a21410250a0900c190306428260f04c0c190a094282403064300d0f04c282506034058d6209950190003580050931c10030306405790916c10290a0902811040940c191406c3c110a0940c190f04c0c190a09428242806c3c0d0a09428241e03c5807040a45003
|5=>0x32f428190f0ec28250a09011d10a00c0c19090ac246e0a03425e90409c0c19040a40c190a014f801032e824190966c102a03064242b2c03c001909005dc190903dd41b7403428030a12410260306410030900c0c191b01c280d0a06c280d0e01424280306404a9090a80c190e0d428240903401b90906c0c250e06428246c034b026000643c110306428250a091a803
|6=>0xa0940d290e06428240a01c186e0a0345807032f42819043840c190a0148407032e424192f03c28050a065140786064280f095940cbe0a064180177064240f4000c19060903401b12c09800190306428250a0901029090a00c19810660c0d0901c580f040a4180d000640c1900034282706014240d090a4b00f0012410260306429ff040900c190a00c0cbe0a0645804
|7=>0x30642649040a00c19046940c1909014293b06014280d2c0a418010a0343c120a0940c19032e824190903424bc0a06428240a034241903098001909066300f2e004241904094180d000640e0d0901c241900664102a030642401040980c190a09c0c190a0982491040ac0c198903424bf0a064242903064280d0e06424282103c1025060342887040940c195a0343c1b
|8=>0x4101c240d03474246c0a03428240a034240d0401c0c19090a83c130a0940c19090a40c190a004113603064240106014040d0a03418295406c000d0a1241026030642a734e03c0419090343805090a010290a01c0c192f410281909034a01b0a414240d46064380d0a092641b4101c240d095980cbe0a06438350a0942824069646c030a03630032c0940019011241026
|9=>0x4d06c2401090340ebe710642403047142403030640d290e06428246e034241b0a094240703066b01b2a034242aaa06429040903410390a0900c191601c102903064241b41004240d0a04410250306428190e0d424280a35c1007030647001061b8280da5005b80d0906c0dc10a098281b09244102b0306688030a544000d0f03428250a0900e862e01424194f0642419
|10=>0xa0940c190a0901906090343c130a0940c190ab953c1b01034241103064242a4a03c38190a0900c25091b0280d1c014186e0a035882654064000db1034bc030a0642565032f828190a4f0040d0a034100503064242a0a0642c0d0a09810a903064242a2100c10250306428c50400c0c190924c102b0306410250a0900c1906468380d0a090bc030a0640c190f01c2429
|11=>0xa094001900034240d012a4242a042a40c19090a810070306424050300400190a0982458040a40c190306438010a090019b040a80c190924c102b030642405032e824190931410030306426e54f06c040d0a09c190609034282503064000d032f804190a06429a5030642405120641026030643c110a0940c190a0980c19000342827040980c1906034380d0a0903c10
|12=>0x309424190a4d80c190900410290306428010966c102a03064103b0a0900c19091681029030640c190a71424030a0b40c190a0983c3b0a09428240a0140c19090142407032e42419c4065340f090043c110a0940c19040bc0c190a098241303064242a0948c0c190a00438020a0900c1909744280303064241103064242a0a0440c190f03c28250a0900c190974c2803
|13=>0x970c281b2c090001903014281900064000d0f01c24290a014281901864280f0901c242906418240d090a8241b0a00c2819090a0280d0a004280d03064000d040980c19094f8040d1b00c280d8303424070901c0c194e0a404194b064280709704281b4e03c0419094f4040d09064240f5409c000d032e42419090a4280103014241900034241b09004240f0900c0c19
|14=>0x54098000d0006424192f00c28190400c0c1954064000d0948c28010e00828240974428032c09800190306424050974c28030e06428240006428260e00428240a09c240d0a01c28190a064240d1b014280d0938428053806c28050a418240d040980c19000b428262e01424190e0342824091b0280d040940c19090a4040d4100c240d6e034241b091bc280d0f03c2825
|15=>0x24030a00c28240a0942826000342419090040c1909014280f0a09c28260a09428240e06828240e0d428240a034240d0a4d824010a0900c190a0940c19061b8280d030642826040900c19040ac0c190a014240d0a71424030a0b428260a2e424190306424010901428052a034242a
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x10143b50d943150b8c2950950205000000006d40000594124035408500d4003
|7,0=>0x450d104431108441110130000fe33f44f943d50f143b50e943950e413810dd3368cd643490cf332d0c7430d0bf42ed0b742cd0af42ad0a83294ca142750994258c92423908c2224c854210480400000001f1078400007441c106d31a50654185060117105931550514138c4a41190451
|7,1=>0x14144f513a34d913244b912a44a0924448c51f446d1174
|8,0=>0x7fcdfc37e4df637ccdf037b89eb37a0de53788ddf3770dd93758dd33740dcd372c9c83714dc236fcdbc36e4db636ccdb036b4daa369cda43684d9e366cd983654d92363cd8c36289873610d8135f8d7b35e0d7535c8d6f35b0d693598d633580d5d3568d573550d513538d4b3520d453
|8,1=>0xaeceb83ad4eb23abceac3aa4ea63a8cea03a74e9a3a5ce943a44e8e3a2ce883a14e832a00e7d39e8e7739d0e7229bce6c39a4e66398ce603974e5a395ce543944e4e392ce483914e42390463e38ece3838d4e3238bce2c38a4e26388ce203874e1a385ce143844e0e382ce083814e023
|8,2=>0x33b3ce0f353cc8f2f3cb0f293c98f233c80f1d3c68f173c50f113c38f0b3c20f062c0cf003bf4efa3bdcef43bc4eee3bacee83b94ee23b7cedc3b64ed63b4ced03b34eca3b1cec43b04ebe3
|9,0=>0xef0bba2ee0bb62ed0bb22ec0bae2eb0baa2ea0ba62e90ba22e80b9e2e70b9a2e60b962e50b922e40b8e2e30b8a2e20b862e10b822e00b7e2df0b7a2de0b762dd0b722dc0b6e2db0b6a2da0b662d90b622d80b5e2d70b5a2d60b562d50b522d40b4e2d30b4a2d20b462d10b422d00b3e2
|9,1=>0xf90be22f80bde2f70bda2f60bd62f50bd22f40bce2f30bca2f20bc62f10bc22f00bbe2
|10,0=>0x3f01fbc7ee1fb47ec1fac7ea1fa47e81f9c7e61
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 14
def pmP:Nat→Nat
|0=>0x100000000001042800000020000000000213b0000000423e0000000600000000009dd8000000133b00000000cd400000000c20000000018100000000201000000004000000000062c0000000085000000000ab000000000f0000000001ac000000002c0000000004e00000000090000000000ec00000000140000000001e00000000032000000000600000000007000000000090000000001000000000008000000000080000000000
|1=>0x84656000001086ec00000210958000004019b00000080316000001004ec000002008d8000004008100000076416000000e8ee400000190170000002b26b000000544d6000000a4cac000000c0158000000b3cb000000166f60000002cd7c00000059af0000000b35b000000166760000002cc7c000000595d8000000b29b0000001617600000028f2c00000051bd8000000a35e000000127360000002482c000000485d80000008001
|2=>0xf2716000001e4c2c000003c155800000721bb000000e2616000001c4a2c00000359d58000006b32b000000d44d6000001a4aac00000301540000005d32b000000b66f60000016ccac000002d9058000005b00b000000ac156000001486f800000290958000004b37b0000009665e0000012ccac00000251dd8000004a32e00000094656000001284ac00000249e58000004933b00000092596000001248ac0000024905800000483eb
|3=>0x8c01d0000011802a0000022d1158000045827b00000894656000011000a0000022000c0000040930b00000808000000010048ac000020011c000004000a800000800050000010000600000200000000003091bb00000492196000003aceac0000065195800000ca323000001842760000030046c0000055935800000a926b000000f677e000001eceec000003d9978000007b32b000000f6416000001ec02c000003d1dd8000007a32b
|4=>0x8096516000100b4c2c000201005400004000008000040fa61600008124b2c0001016985800020180000000402405c000080408280000c149958000140d30b000020f66d6000041c82ac000082d9b58000105a22b000020b2676000040a4cac00008109c0000010103080000201265600004000c00000080001580000c5a22b00001854056000030a4cac000060000c8000082b26b0000104001000002050ca0000040218400000804302
|5=>0x4100009200081120f2c001021493580020000000000240d06760004112800000082058158001008b2ab000200fe776000401f0aec000803e1558001006b33b000200d067600040120020000800595580010000000000118f04160002102c004000403c1858000805b283000100b64f60002012ca2c00040258458000804b00b00010080002000200201200004000024000080000000000c88005000018124b2c00030200140000407930b
|6=>0x4000000900042102800000840010000010105b37b002020b04f60040016c8ec00800259fd8010004b20b00200090676004000a820000800110440010000001800100194656002003000a000400400150008008000a0010009665600200128cac00400149958008000d31b00080000000000c102caac001802100000026040008000498200160008416ccac001082d11580020c7930b000418544d60008302482c001060415d800208600a8
|7=>0x100005265602000084cac04000100c40080000933b00d01002436018060a4cac03008000800060080d33b00c00842656010101e4b2c020002699580400004120004300fe776008401eceec010803c11d8020805823b00410030436008041ecfec010040517d8020042b2fb0040084265600801034cac01002009858020008d33b004000b26d6008001249ec01000149958020000f2bb0040001a6760080002caec010000495d80200000248
|8=>0x100100b24f6200001ecaac400003481c8800004b28b1000004401011003024c2c22004049858420080d33b0800500a612100060a4cac20006049858400080930b0800008a6160c0a006c02c180200d8058213000b2bb042200164160842016c9ec101c02d9058201800b20b021000520d60402016ca2c080000590580c008212230100201265602004024c6c040060499d808000a932b01000100400020001e4eec04000249d58080002933b
|9=>0x1000281e082d109800595d9213000b2ab2000011e576240e016c82c408003d95d8810005b20b
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x24090602006010182c00000280018030d85c0c1a
|7,0=>0xb0080cde2616870ee0665810020101824080e0500800035e050ce0e1b0c420a4691c82c0444a049c200389002a11c8c55c03098ed4e660f834708a010d4e22a00000e06a000040203008c12eb02680c780101985421d
|8,0=>0x3581a183a673b9308b4f27558c927accea94630f8da9c53065cae56840d4abb6bb455e1860195b099820fcbb17158a1ba213719974db4641e25133fb6092a85b3c4d8b85a8b92cfb1990050a92dbbdac922e3dc46e985af9fc472fa41bc6442a0db6d3282b46e283127d6acd744204aa36831e34b27cbfc8e5a288b144e47698998747a3fd34573b140c11b243ac9232
|8,1=>0x3f4b6473d9f9c00f1835443065fa20f2822137cf48d17954231d642e43c73231058a277543c741588b510ef0400f4dadb
|9,0=>0x250bc944b79c08f67c931f508c490b9c98f282c79688e7c280f11a2a109ccfa651599ef52391214b631b6a40b761c04524a49b061ce334a45b8594ac3632ab31c723f232c3d8c85e8a8d2209b342f644aa6cc2648ec8c3891f258b4010ce1
|10,0=>0xc8864a2994a28e47e3096245
|11,0=>0x22
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 43 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_126 10 roots_126 ops++addP pm 1 dom_63 9 roots_63 ops++addP pm 2 dom_118 7 roots_118 ops++addP pm 3 dom_111 9 roots_111 ops++addP pm 4 dzo_119_8 7 roots_119 ops++addP pm 5 dom_119 8 roots_119 ops++addP pm 6 dom_87 6 roots_87 ops++addP pm 7 dzo_87_8 6 roots_87 ops++addP pm 8 dom_93 7 roots_93 ops++addP pm 9 dom_125 9 roots_125 ops++addP pm 10 dom_122 7 roots_122 ops++addP pm 11 dom_116 5 roots_116 ops++addP pm 12 dom_121 8 roots_121 ops++addP pm 13 dom_115 7 roots_115 ops++addP pm 14 dzo_85_8 5 roots_85 ops++addP pm 15 dom_123 9 roots_123 ops++addP pm 16 dzo_95_32 7 roots_95 ops++addP pm 17 dzo_87_32 6 roots_87 ops++addP pm 18 dom_95 8 roots_95 ops++addP pm 19 dom_103 5 roots_103 ops++addP pm 20 dzo_116_8 5 roots_116 ops++addP pm 21 dom_124 7 roots_124 ops++addP pm 22 dom_47 6 roots_47 ops++addP pm 23 dom_45 5 roots_45 ops++addP pm 24 dom_85 5 roots_85 ops++addP pm 25 dom_79 5 roots_79 ops++addP pm 26 dom_31 5 roots_31 ops++addP pm 27 dzo_91_32 6 roots_91 ops++addP pm 28 dzo_83_32 5 roots_83 ops++addP pm 29 dom_43 5 roots_43 ops++addP pm 30 dzo_118_8 6 roots_118 ops++addP pm 31 dom_55 5 roots_55 ops++addP pm 32 dom_83 5 roots_83 ops++addP pm 33 dzo_117_8 6 roots_117 ops++addP pm 34 dom_61 6 roots_61 ops++addP pm 35 dom_117 6 roots_117 ops++addP pm 36 dom_59 6 roots_59 ops++addP pm 37 dom_107 6 roots_107 ops++addP pm 38 dom_109 6 roots_109 ops++addP pm 39 dom_91 6 roots_91 ops++addP pm 40 dom_99 4 roots_99 ops++addP pm 41 dom_51 4 roots_51 ops++addP pm 42 dom_77 4 roots_77 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_127 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_zo_119_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_87_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_85_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_95_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_87_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_zo_116_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_47 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_79 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_zo_91_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_zo_83_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_zo_118_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_zo_117_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_77 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_126 10 s (0,roots_126.map (·&&&dom_126)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_127 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_126 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_127==dom_127)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_127 gM v ys):RunD true dom_127 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_127 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 2 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 18 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 18 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 77 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 77 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 171 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 43 128 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 171 → Z 8 i = true := (range_split z8_0 z8_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 84 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 84 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 11 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 11 0 = true)
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
theorem lowS_191:Lower true dom_191 roots_191 goal_191 11:=lower_slice_b [(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,8,9)] (by decide +kernel) lowS_190
theorem lowS_223:Lower true dom_223 roots_223 goal_223 10:=lower_slice_b [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,8,9)] (by decide +kernel) lowS_222
theorem lowS_239:Lower true dom_239 roots_239 goal_239 11:=lower_slice_b [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,8,9)] (by decide +kernel) lowS_238
def dzo_171_64:=0xf0f00000f0f000000000000000000000f0f00000f0f0000000000000000
def gzo_171_64:=0xf0f00000f0e000000000000000000000f0e00000e0e0000000000000000
def gsh_171_64:=0xf0f00000f0e000000000000000000000f0e00000e0e
theorem lowS_zo_171_64_168:Lower true dzo_171_64 roots_171 gzo_171_64 6:=lower_iso_b (d1:=dom_171) (r1:=roots_171) (T1:=gsh_171_64) [(dom_171,64)] (by decide +kernel) (lower_slice_b (T:=gsh_171_64) [(0xa0a00000a0a000000000000000000000a0a00000a0a,0,1),(0xc0c00000c0c000000000000000000000c0c00000c0c,0,2)] (by decide +kernel) lowS_168)
def dzo_211_32:=0xf000f00000000000f000f00000000000f000f00000000000f000f00000000
def gzo_211_32:=0xf000f00000000000f000f00000000000f000e00000000000e000a00000000
def gsh_211_32:=0xf000f00000000000f000f00000000000f000e00000000000e000a
theorem lowS_zo_211_32_82:Lower true dzo_211_32 roots_211 gzo_211_32 6:=lower_iso_b (d1:=dom_211) (r1:=roots_211) (T1:=gsh_211_32) [(dom_211,32)] (by decide +kernel) (lower_slice_b (T:=gsh_211_32) [(0xa000a00000000000a000a00000000000a000a00000000000a000a,0,1),(0xf000f00000000000f000f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_82)
def dzo_187_64:=0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000
def gzo_187_64:=0xf0f0f0f0f0f0f0e00000000000000000f0f0f0e0f0f0e0e0000000000000000
def gsh_187_64:=0xf0f0f0f0f0f0f0e00000000000000000f0f0f0e0f0f0e0e
theorem lowS_zo_187_64_168:Lower true dzo_187_64 roots_187 gzo_187_64 7:=lower_iso_b (d1:=dom_187) (r1:=roots_187) (T1:=gsh_187_64) [(dom_187,64)] (by decide +kernel) (lower_slice_b (T:=gsh_187_64) [(0xa0a0a0a0a0a0a0a00000000000000000a0a0a0a0a0a0a0a,0,1),(0xc0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0c0c,0,2),(0xf0f00000f0f000000000000000000000f0f00000f0f0000,0,16)] (by decide +kernel) lowS_168)
def dzo_219_32:=0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000
def gzo_219_32:=0xf0f0f0f000000000f0f0f0f000000000f0f0f0e000000000f0e0f0a00000000
def gsh_219_32:=0xf0f0f0f000000000f0f0f0f000000000f0f0f0e000000000f0e0f0a
theorem lowS_zo_219_32_82:Lower true dzo_219_32 roots_219 gzo_219_32 7:=lower_iso_b (d1:=dom_219) (r1:=roots_219) (T1:=gsh_219_32) [(dom_219,32)] (by decide +kernel) (lower_slice_b (T:=gsh_219_32) [(0xa0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0a,0,1),(0xf000f00000000000f000f00000000000f000f00000000000f000f00,0,8),(0xf0f0f0f000000000f0f0f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_82)
namespace S_251
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(1,129),(2,10),(2,18),(2,66),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(8,9),(8,10),(8,40),(8,136),(16,17),(16,18),(16,80),(16,144),(24,25),(24,26),(24,56),(24,88),(24,152),(32,33),(32,40),(32,160),(34,35),(34,42),(34,50),(34,98),(34,162),(48,49),(48,50),(48,56),(48,112),(48,176),(64,65),(64,66),(64,80),(72,73),(72,74),(72,88),(72,104),(72,200),(96,97),(96,98),(96,104),(96,112),(96,224),(128,129),(128,130),(128,136),(128,144),(128,160),(192,193),(192,194),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffffffffffffff
def xsM:=roots_251.map (·&&&dom_251)
def gM:=goal_251&&&dom_251
def NN:Nat→Nat
|7=>8
|8=>32
|9=>62
|10=>10
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|7,0=>0xf5c4ee2f95d1749cef3896a4059d245346610aa9
|8,0=>0xf2025efcdaed384ed0bfe7418e6801deb4dc7920b9184b2009a30ef9db7694fda90b27817637f2db7c35f6c90b6a964679186712860fe960a7c6086a558dc524e3503fc4f01e44bf63f6810916205127
|9,0=>0xfc1abfa788f8f4df1a88f0a9eed213ea318ea1e0e8f3cdff56dfdb8d4598d1ac6c91fbc882bc8760c1f37bff33b9b4eb9675b7668b0daab0071ab7fca78349af1999b7d97a1e974fa93710935e39202e8e7548c6df8b2758a86a8a54c8976388354855fe8071f7eb06715936ca956580b638125b4184d1cb4985e3cbc139b7537255347c73019c2ebe925770247401a49d1752105c1004e7b0385d
|10,0=>0xe3d59b7536840fe7dc916c0fe658404acc8411753ecf23e1f9
|11,0=>0xff75e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f000000000f0f0f0f000000000f0f0f0f00000000000000000000000000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0f0f0f0f00000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000f0f00000f0f000000f000f00000000000f000f00000000000f000f00000000000f000f00000000f0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f00f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000000000000000000000000000000000000000000000000000000000f0f0f0f0f000f000f0f0f0f0f000f00f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000000000000000
|0,1=>0xf0f0f00000000000f0f0f00000000000f0f0f00000000000f0f0f0000000000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f00000000000f000f00000000000000000000000000000000000000000000000000000000f0f0f0f0000000000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0000000000000000000000f000000000000000f000000000000000f000000000000000f00000000f000f0f0f000f000f000f0f0f000f000f000f0f0f000f000f000f0f0f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f0f0f000f0f0f000f0f0f0000000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f00000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f00000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f000f000f000f000f000f0000000000f0f0f00000000000f0f0f00000000000f0f0f00000000000f0f0f0000f000f0f0f0f00000f000f0f0f0f00000f000f0f0f0f00000f000f0f0f0f00f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000
|0,2=>0xf0f000f0f0f00000f0f000f0f0f00000f0f000f0f0f00000f0f000f0f0f00000000f0f00000f0000000f0f00000f0000000f0f00000f0000000f0f00000f00f000f000f000f000f000f000f000f000f0f0f0f0f000f000f0f0f0f0f000f0000000000000000000000000000000000f0f0f0f000000000f0f0f0f00000000f0f0f0f0f0f0f000f0f0f0f0f0f0f000f0f0f0f0f0f0f000f0f0f0f0f0f0f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f0f0f0f0f000f0000000000f0f0f0f000000000f0f0f0f000000000f0f0000000000000f0f000000000000000000000000000000000000f0f0f000f0f0f000f0f0f000f0f0f000000f0f0000000000000f0f0000000000000f0f0000000000000f0f000000000000f0f00000f0f00000f0f00000f0f00000f0f0000000000000f0f00000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000f0f0f0f0000000000f000f000f000f000f000f000f000f000f000f00000000000f000f000000000000000000000000000000000000000000f000f00000000000f000f00000000000000000000000000000000000000000000f0f0000000000000f0f00000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0000000000000f0f00000000f0f0f0f000000000f0f0f0f000000000f0f0000000000000f0f000000000000
|0,3=>0xf000f000f0000000f000f000f0000000f000f000f0000000f000f000f000000f000f000f000f000f000f000f000f000f000f000f000f000000000000000000000000000000000000000000000000f0f0f0f0f0f00000f0f0f0f0f0f0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f000f0000f000f000f000f000f000f000f000f000f0000000f0000000f0000000f0000f0f00000f0f00000f0f00000f0f00000f0f0f0f0f0f00000f0f0f0f0f0f0000
|_,_=>0
def sP:Nat→Nat
|0=>0x10308b04020a18c1440c20464456430892050c22d324818c1440c22c16063051030811974450c22c92161851030812951540c22450c248920644308b04020644c0c22c13851030881c63451030812863040c204018c10308b0401c61440c2040
|1=>0x8b0481911430a324840510308f2063051030a20463051030a125e8040c224819730510308119110308100879f10308920644c1030817863040c204644c0c22c92151911540c22464450c274920a1851030810081c61440c205c1440c26c8185
|2=>0x2481973051030892061440c204f2151911440c22481856440c22481913040c22487863040c22481a81440c22481851030a12481851030a62481a51440c20464450c29092063040c20402863451030812154450c22c920634510308b048191143
|3=>0x21e1851030812061440c2b8922d1851030892063451030812067c51030892061440c205b20644550308921eb051030892101851030812181851030892063051030a2248ac61440c224854615410308918510309d248a861440c22481851030a9
|4=>0x18510308b04818510309a2481971440c2248185c840c20481858040c22481851030a32482861540c22481851030b12482ac1440c224819114308b2487951440c22481851030932481911440c2048ac6445103089230185103089206bc5103089
|5=>0x4451030892061440c2d4920630510308b24818c1440c20461440c207421818c1440c22487864440c22485451030a72481851030a70481851030a224819c1440c20481851030a42482951440c2248cc61440c224854510308b2482861440c2048
|6=>0xc22485461440c22481ac1440c224818c1440c22481851030a72482861440c224818510308b24818510308120644510308920615410308921e1851030892071851030892061440c2040206b111440c22481911440c268920a18c1440c2248197
|7=>0x6144
|_=>0
def sO:Nat→Nat→Nat
|7,0=>0xd582d8099c20606201080220008
|8,0=>0x4b5d258479d15943610493f20f483b5ce583760d6733a0c682fdcb872c5ca9828609982424897209c7991c60698189c5a814a0499109c3b7
|9,0=>0xc9631d8c5270b9c0a6f99bc62e89b85ed98b426c88b022b88ac22a88a822988a422888a0227889c226889822588942248890223888c22288882218883e60787fe1f787be1e7877e1d7873e1c786fe1b786be1a6967a196863a18685fa17595b61649572154853214484f21348
|10,0=>0xdd236c8d9235c8d5234c8d15f3d8cd632d8
|11,0=>0x37c7
|_,_=>0
def wAt:=mkWire dB 54 252 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 14
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1844a23248461118186072484506248461314849211844469191c511184c6461444921184c52118c492114846134484511408c605248442118446212d3461319185111418511184c5211444921184d03f18146042484a2324846111484506248461114845062484613288c5062484611
|1=>0x545c621708460724855131444621141892114845052484611184c511188461314149211444921184c511194c4211814604248463324845218884633148461518c052130449211484511141892118546441444511248452118549211484511184c521108451118845112c846131418921
|2=>0x184462314446131884615191851124845111914511b05462314b46132484615285c611b0446231414921191051118189211444421188c6151814921788461518cc521784461518844212c84613194442118c8521304452118109211444621127461714445211484615448c5119c84617
|3=>0x184461324845111084615288c61114189211444623191c51118445214484511784c615184c5212484521101892118c452114446151884617248461718cc521181c921544c6211844621788c615188461324846112484613191c5113044521101492118c0521194c4211844421304c521
|4=>0x18846231484617
|_=>0
def oO:Nat→Nat→Nat
|7,0=>0xd205cc2680f40618210088004
|8,0=>0x3d99e0cea67233799b0cd26663319980cba65a32b9950ca264e3259920c8a64231f98f0c7263631998c0c5a62a3139890c4261e3
|9,0=>0x1f04f627a13c89e04ee27613a89d04e627213889c04de26e13689b04d626a13489a04ce26613289904c626213089804be25e12e89704b625a12c89604ae25612a89504a6252128894049e24e126893049624a124892048e2461228910486242120890047e2
|10,0=>0x2063021808c005fe2fe17e8bf05f62fa1
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 13
def pmP:Nat→Nat
|0=>0x111a200683740305ba0162dd00947e8048fe40247b20121f900906e804836c0240fa00e1d900546e800e3280047fa0023df0011ee8008b740045b20021fd0010ee80083e40041ba0020d9000c4000043380021040004400001ff8000120000014000000
|1=>0xc106e86083642873be1420df09d46e84c83742551ba1222dd08d47f846a3f42351ba11a0dd08906e842a3742141ba1063dd08306e840c37c2053fa1028dd0811ee830837c1241ba0860dd04116e814b3000a41be0432db02186d80c8fe40647b20321d9
|2=>0x2c14fe9448274a1c7ba5063dd2830ee940a7f4a053ba5021dd28106e90187748053ba3431dd1298ec894c3744849b22410fb12026208c8fe44251fe2123fb1091ed884837c4043fe2020fb0df06e86d8b7436c1ba1a60dd0cb16e86483f43241ba1860dd
|3=>0x10521db4a146f9c0a7fce053be6829fd
|_=>0
def pmB:Nat→Nat→Nat
|7,0=>0x2804196081c282
|8,0=>0x54fa826713c8097934ad79c92f4cc44632724c97066e755c9c07f1ba
|9,0=>0x19231e71b22b632453bf7214a2e96033b311a8b2e8b21716ecc391cbd84bbb56b61684e897a886cbd5e6d645511d6a2a50cf1ab4654c1
|10,0=>0x1f89145d8891035058
|11,0=>8
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 7 (j%128);fld (pmP (k/32)) 25 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_250 10 roots_250 ops++addP pm 1 dzo_171_64 6 roots_171 ops++addP pm 2 dom_219 8 roots_219 ops++addP pm 3 dom_187 10 roots_187 ops++addP pm 4 dom_249 10 roots_249 ops++addP pm 5 dom_107 6 roots_107 ops++addP pm 6 dom_235 9 roots_235 ops++addP pm 7 dom_243 9 roots_243 ops++addP pm 8 dzo_83_32 5 roots_83 ops++addP pm 9 dom_227 6 roots_227 ops++addP pm 10 dom_171 8 roots_171 ops++addP pm 11 dzo_91_32 6 roots_91 ops++addP pm 12 dom_59 6 roots_59 ops++addP pm 13 dom_123 9 roots_123 ops++addP pm 14 dzo_211_32 6 roots_211 ops++addP pm 15 dom_211 6 roots_211 ops++addP pm 16 dom_83 5 roots_83 ops++addP pm 17 dom_115 7 roots_115 ops++addP pm 18 dzo_187_64 7 roots_187 ops++addP pm 19 dom_91 6 roots_91 ops++addP pm 20 dzo_219_32 7 roots_219 ops++addP pm 21 dom_43 5 roots_43 ops++addP pm 22 dom_203 6 roots_203 ops++addP pm 23 dom_155 6 roots_155 ops++addP pm 24 dom_179 7 roots_179 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_251 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_171_64_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_83_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_91_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_211_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_187_64_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_zo_219_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_179 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_250 10 s (0,roots_250.map (·&&&dom_250)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_251 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_250 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_251 gM v ys):RunD true dom_251 gM v (ori ys):=h
def Z (s:Nat):=barP dom_251 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 8 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 32 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 32 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 62 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 62 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 10 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 10 0 = true)
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
namespace S_254
def pG:List (Nat×Nat):=[(2,10),(2,18),(2,66),(2,130),(4,20),(4,36),(4,68),(4,132),(6,14),(6,22),(6,38),(6,70),(6,134),(8,10),(8,40),(8,136),(12,14),(12,28),(12,44),(12,76),(12,140),(16,18),(16,20),(16,80),(16,144),(24,26),(24,28),(24,56),(24,88),(24,152),(32,36),(32,40),(32,160),(34,38),(34,42),(34,50),(34,98),(34,162),(48,50),(48,52),(48,56),(48,112),(48,176),(64,66),(64,68),(64,80),(72,74),(72,76),(72,88),(72,104),(72,200),(96,98),(96,100),(96,104),(96,112),(96,224),(128,130),(128,132),(128,136),(128,144),(128,160),(192,194),(192,196),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffffffffff
def xsM:=roots_254.map (·&&&dom_254)
def gM:=goal_254&&&dom_254
def NN:Nat→Nat
|10=>1
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|10,0=>0x6f64d
|11,0=>0xba90f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaaaaaaaaaa00aa00aaaaaaaaaa00aa00aaaaaaaaaa00aa00aaaaaaaaaa00aa015555555400000001555555540000000155555554000000015555555400000002aaa80002aaa80002aaa80002aaa80002aaa80002aaa80002aaa80002aaa80005500550055005500550055005500550055005500550055005500550055005500a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a11111111111111111111111111111111111111111111111111111111111111112aaaaaaaaaaaaaaa80000000000000002aaaaaaaaaaaaaaa80000000000000005555555555555555555555555555555500000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x1ac688fac688
|_=>0
def sO:Nat→Nat→Nat
|10,0=>8
|11,0=>0x87
|_,_=>0
def wAt:=mkWire dB 8 255 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 8
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xd1
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
addP pm 0 dom_252 10 roots_252 ops++addP pm 1 dom_190 10 roots_190 ops++addP pm 2 dom_126 10 roots_126 ops++addP pm 3 dom_250 10 roots_250 ops++addP pm 4 dom_238 10 roots_238 ops++addP pm 5 dom_246 9 roots_246 ops++addP pm 6 dom_222 9 roots_222 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_254 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_238 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_222 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_252 10 s (0,roots_252.map (·&&&dom_252)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_254 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_252 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_254==dom_254)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_254 gM v ys):RunD true dom_254 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_254 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
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
  · simp [NN] at hi
  · simp [NN] at hi
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
def isoMvS_247:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_247:Lower true dom_247 roots_247 goal_247 10:=lower_iso_b isoMvS_247 (by decide +kernel) lowS_223
def isoMvS_253:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_253:Lower true dom_253 roots_253 goal_253 12:=lower_iso_b isoMvS_253 (by decide +kernel) lowS_251
def dzo_247_8:=0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00
def gzo_247_8:=0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00fe00ff00ff00fe00ee00
def gsh_247_8:=0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00fe00ff00ff00fe00ee
theorem lowS_zo_247_8_84:Lower true dzo_247_8 roots_247 gzo_247_8 8:=lower_iso_b (d1:=dom_247) (r1:=roots_247) (T1:=gsh_247_8) [(dom_247,8)] (by decide +kernel) (lower_slice_b (T:=gsh_247_8) [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,0,1),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,0,2),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000,0,32),(0xff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_84)
def dzo_215_8:=0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00
def gzo_215_8:=0xff00ff0000000000ff00ff0000000000ff00fe0000000000fe00ee00
def gsh_215_8:=0xff00ff0000000000ff00ff0000000000ff00fe0000000000fe00ee
theorem lowS_zo_215_8_84:Lower true dzo_215_8 roots_215 gzo_215_8 7:=lower_iso_b (d1:=dom_215) (r1:=roots_215) (T1:=gsh_215_8) [(dom_215,8)] (by decide +kernel) (lower_slice_b (T:=gsh_215_8) [(0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa,0,1),(0xcc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc,0,2),(0xff00ff0000000000ff00ff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_84)
def dzo_223_32:=0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000
def gzo_223_32:=0xffffffff00000000ffffffff00000000fffffffe00000000fffefffa00000000
def gsh_223_32:=0xffffffff00000000ffffffff00000000fffffffe00000000fffefffa
theorem lowS_zo_223_32_82:Lower true dzo_223_32 roots_223 gzo_223_32 8:=lower_iso_b (d1:=dom_223) (r1:=roots_223) (T1:=gsh_223_32) [(dom_223,32)] (by decide +kernel) (lower_slice_b (T:=gsh_223_32) [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,0,1),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,0,4),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,0,8),(0xffffffff00000000ffffffff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_82)
def dzo_215_32:=0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000
def gzo_215_32:=0xff00ff0000000000ff00ff0000000000ff00fe0000000000fe00fa00000000
def gsh_215_32:=0xff00ff0000000000ff00ff0000000000ff00fe0000000000fe00fa
theorem lowS_zo_215_32_82:Lower true dzo_215_32 roots_215 gzo_215_32 7:=lower_iso_b (d1:=dom_215) (r1:=roots_215) (T1:=gsh_215_32) [(dom_215,32)] (by decide +kernel) (lower_slice_b (T:=gsh_215_32) [(0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa,0,1),(0xf000f00000000000f000f00000000000f000f00000000000f000f0,0,4),(0xff00ff0000000000ff00ff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_82)
def dzo_175_64:=0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000
def gzo_175_64:=0xffff0000fffe00000000000000000000fffe0000fefe0000000000000000
def gsh_175_64:=0xffff0000fffe00000000000000000000fffe0000fefe
theorem lowS_zo_175_64_168:Lower true dzo_175_64 roots_175 gzo_175_64 7:=lower_iso_b (d1:=dom_175) (r1:=roots_175) (T1:=gsh_175_64) [(dom_175,64)] (by decide +kernel) (lower_slice_b (T:=gsh_175_64) [(0xaaaa0000aaaa00000000000000000000aaaa0000aaaa,0,1),(0xcccc0000cccc00000000000000000000cccc0000cccc,0,2),(0xf0f00000f0f000000000000000000000f0f00000f0f0,0,4)] (by decide +kernel) lowS_168)
def dzo_191_64:=0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
def gzo_191_64:=0xfffffffffffffffe0000000000000000fffffffefffffefe0000000000000000
def gsh_191_64:=0xfffffffffffffffe0000000000000000fffffffefffffefe
theorem lowS_zo_191_64_168:Lower true dzo_191_64 roots_191 gzo_191_64 8:=lower_iso_b (d1:=dom_191) (r1:=roots_191) (T1:=gsh_191_64) [(dom_191,64)] (by decide +kernel) (lower_slice_b (T:=gsh_191_64) [(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,0,1),(0xcccccccccccccccc0000000000000000cccccccccccccccc,0,2),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,0,4),(0xffff0000ffff00000000000000000000ffff0000ffff0000,0,16)] (by decide +kernel) lowS_168)
namespace S_255
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(1,129),(2,10),(2,18),(2,66),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(4,20),(4,36),(4,68),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(6,14),(6,22),(6,38),(6,70),(6,134),(7,15),(7,23),(7,39),(7,71),(7,135),(8,9),(8,10),(8,40),(8,136),(12,13),(12,14),(12,28),(12,44),(12,76),(12,140),(16,17),(16,18),(16,20),(16,80),(16,144),(24,25),(24,26),(24,28),(24,56),(24,88),(24,152),(32,33),(32,36),(32,40),(32,160),(34,35),(34,38),(34,42),(34,50),(34,98),(34,162),(48,49),(48,50),(48,52),(48,56),(48,112),(48,176),(64,65),(64,66),(64,68),(64,80),(72,73),(72,74),(72,76),(72,88),(72,104),(72,200),(96,97),(96,98),(96,100),(96,104),(96,112),(96,224),(128,129),(128,130),(128,132),(128,136),(128,144),(128,160),(192,193),(192,194),(192,196),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffffffffffffffffff
def xsM:=roots_255.map (·&&&dom_255)
def gM:=goal_255&&&dom_255
def NN:Nat→Nat
|7=>6
|8=>56
|9=>89
|10=>153
|11=>67
|12=>8
|13=>1
|_=>0
def HT:Nat→Nat→Nat
|7,0=>0xfb305958c276b845b3e741d2716c3f
|8,0=>0xfa94cf8ffdf7fdef670ef4df3f1243e15e5dff3edc2d1d2b55d2505d09c5cdae3c4b18b5228ad67eacdbfa44a1a235f99b5698ce598b0b97baa961c895c3395a3394a148e02584c2e7cf117bef27b58b751a174965725c070a807024c6a590654f960952583bd451b542bdc3b7d539c11398f437c652696024a5d20c742058d1a081193b117ce400d1a00a0d
|9,0=>0xfcd6ff8bd1f7cfaf670eebd4be8d77e7e66e718add3a7d53ccd2b55cc401cb3b3ca7e8c1cebb52a6b4276b3813af966adf84a7d0ba49f89d9e59d2219c7849bc4c99edf9222b921c28800887dca86dab84ec384e297d00f7ccb178e5b7870e77df373a447386e6a8a367de96534563631624e1619ca612bb600c95ec7c5cf715565a4fa214f2c74aea148dbf4541b44e81429bb3f7f03e71c3c2f33a7b239c5739499380ea32a9a32a912f8ff2c3462890c2560e211351d8f11c8d21a25c19a9a18870187c917e2e15891116f20b8b809b2308fff0799105ed90407f00faf
|10,0=>0x9d74f9d31b9cc7f9bcc698dab96ec2960ce958a18fbaf8d94e8b62a8adb98ab428a05987dca879ef86dab8578b855ba82c3e827988265f7cff27cde07582f720c06f3286beb06b52568119670a96704266f8d661e76605665c286534564b6f6380860be7605f85ba395a1805a0765959e587f55810e541f353e50527d2505974d6114ae0e4936f46ec8451b144fb844d8e4179440dbf3eed53e3403d1643b8183b46d3aef739f74396b438a0c37405371e8365c33459532b7632a912e7002e43c2bfee2babe2b8302b59b2b52f2b0532a37029a0326e2f26d7f258a324a1b243bc2425b2387e2285f2074c1fdb41f2b11d3071cd7c1c69f1b7701b5a31b3ab1b1c31928f18d6b14a1612a1b10884107eb105c7103dc0f28f0dc0f0db740be660b62009e8a08eae07ebb07c280659e0658904e2202d6701c9b018d20048900355
|10,1=>0xf7ef6f6021efca7ed499ec30de718ae4b87e42dee25a4e24fbd568ad1dbec92ecc528ac2818c2136c1b15bdfafbb0fcba2ddb9a71b3b16a763da2367a0ac8
|11,0=>0xfff0bf9f7ef5c34ed446e9a3ae64d9e469adc596da8bfcf279c7aa2c6a49c2818be10dbc5a2b0be0b04cfa763da36dca03ff975d287a9a832007e1fd7d20a7b4e87135a6e3d66de436649d616d65ee575badc5b1195a1805925758c995631b53cdc509124d4184c32c4ba7e468fc430f13e5753d65f3ce9438fe6389f6355f32bfee2b83028a2e1f2b11d3071c2011b5a312a1b10f3d0f41b0c8b807c28055e90450602fee018c4
|12,0=>0xfff0b8fd7c8758d61e18518e52fee011d3a0eef7
|13,0=>0x64457
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffffffffffffffffffffffffffffffffffffffffffffffffff00ffff00000000000000000000000000000000000000ff00ffff00ff0000ff00ffff00ff00ffffffffffffffffffffffffffffffffff00ff0000000000ff00ff0000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffff00ffffffffffffff00ffffffffffffff00ffffffffffffff00ffffffffffffffffffffffffffffffffffffff00ffff0000ffffff00ffff0000ffffffffffffffffffffffffffffffffffffffffffffffffff00ff0000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
|0,1=>0xffff0000ffff0000ffffffffffffff00ffff0000ffff0000ffffffffffffff000000000000000000000000000000000000ff00ffffffffff00000000000000000000ffff0000ff000000ffff0000ff000000ffff0000ff000000ffff0000ff000000000000000000ffffffffff00ff000000000000000000ffffffffff00ff0000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000000000ffffff0000000000ffffff0000000000ffffff0000000000ffffff0000ff00ffffffff0000ff00ffffffff0000ff00ffffffff0000ff00ffffffff00000000000000000000ff00ffffffff00000000000000000000ff00ffffffff00ffffffffffffffffffffffffffffff00ffffffffffffffffffffffffffffff00ffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff000000ff00ffffffffff00ff00ffffffff0000ff00ffffffffff00ff00ffffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff000000000000000000ffffffffffffff000000000000000000ffffffffffffff00ffaaffaaaaaaaaaaffaaffaaaaaaaaaaffaaffaaaaaaaaaaffaaffaaaaaaaaaa0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff0000000000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000
|0,2=>0xff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff0000ffffffff00000000ff00ff0000000000ffffffff00000000ff00ff0000000000ffffffffffffffffff00ff0000000000ffffffffffffffffff00ff0000000000000000ff0000ff00000000ff0000ff00000000ff0000ff00000000ff0000ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00ffffffffffffffffffff00ffffffff00ffffffffffffffffffff00ffffffff00ffff0000ffff0000ffff00ffffffff00ffff0000ffff0000ffff00ffffffff00000000000000000000ff00ffff00ff00000000000000000000ff00ffff00ff00ffff00ffffffff00ffff00ffffffff00ffff00ffffffff00ffff00ffffffff000000000000000000ffff00ffffffff000000000000000000ffff00ffffffff0000ff00ffff00ff0000ff00ffff00ff0000ff00ffff00ff0000ff00ffff00ff00ffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffff0000ff00ff00ff000000ffffffffffff0000ff00ff00ff0000000000000000000000ffffffffffffffff0000000000000000ffffff00ffff0000ffccffccccccccccffccffccccccccccffccffccccccccccffccffcccccccccc
|0,3=>0xff000000ff000000ff00ff00ff000000ff000000ff000000ff00ff00ff0000000000000000000000ffffffffffff00000000000000000000ffffffffffff000000000000ff00ff00ffffffffffffff0000000000ff00ff00ffffffffffffff000000000000000000000000ff000000000000000000000000000000ff00000000ffffffffffffffffffffff00ffffff00ffffffffffffffffffffff00ffffff00ccccccccccccccccccccccffccccccccccccccccccccccccccccccffcccccccc0000000000000000ffff00ffffff00000000000000000000ffff00ffffff0000ffff00ffffff0000ffff00ffffff0000ffff00ffffff0000ffff00ffffff0000ff00ff00ff00ff00ffffffffffffff00ff00ff00ff00ff00ffffffffffffff00ffffffffffffffffffffffffff00ff00ffffffffffffffffffffffffff00ff00ffffffff0000ff00ffffffff0000ff00ffffffff0000ff00ffffffff0000ff00000000000000ff00000000000000ff00000000000000ff00000000000000ff000000000000000000ffffffff0000ff000000000000000000ffffffff0000ff00ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff00000000ff00ff0000ff0000ff00ff0000ff0000ff00ff0000ff0000ff00ff0000ff00ff00ff00ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff0000000000
|0,4=>0xffff00000000ff00ffffff00ff000000ffff00000000ff00ffffff00ff000000000000000000ffffff00ffffff000000000000000000ffffff00ffffff00ffffffffffffffff00ff00ffff00ff00ffffffffffffffff00ff00ffff00ff00000000000000ff00ffffffffffffff00000000000000ff00ffffffffffffff00fff0fff0f0f0f0f0fff0fff0f0f0f0f0fff0fff0f0f0f0f0fff0fff0f0f0f0f00000000000000000ff00ff00ff0000000000000000000000ff00ff00ff000000ffff0000ffff0000ffffff00ffff0000ffff0000ffff0000ffffff00ffff00000000000000000000ff00ff00ff00ff000000000000000000ff00ff00ff00ff00000000ff00000000ff00ffffff00ff00000000ff00000000ff00ffffff00ff0000ff00ffffff000000ff00ffffff000000ff00ffffff000000ff00ffffff000000ff00ffffffffff00ff00ffff00ff0000ff00ffffffffff00ff00ffff00ff00000000ff00000000000000ff00000000000000ff00000000000000ff00000000000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff0000ff000000ffff0000ff000000ffff0000ff000000ffff0000ff000000ffff00ffff0000ffff0000ffffffffffff0000ffff0000ffff0000ffffffffffff00000000000000000000ffffffff000000000000000000000000ffffffff00000000
|0,5=>0xff000000ff00ff000000000000000000ff000000ff00ff00ffffffffffffffff00ff00ff00000000ffffffffffffffff00ff00ff000000000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00ffffffffffffffff0000ffff00000000ffffffffffffffff0000ffff00000000ffffffffffffffffff00ffffff00ff00ffffffffffffffffff00ffffff00ff0000000000000000000000ff000000ff0000000000000000000000ff000000ff00ffffffff00000000ffff00ff00000000ffffffff00000000ffff00ff00000000ffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffff0000ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff00ff00ff00ff00ff00000000000000ffffffff00000000ff00ff0000000000ffffffff00000000ff00ff00ffffff00ffffff00ffffffffffffff00ffffff00ffffff00ffffffffffffff00ffffff00ffff0000ffffff00ffff0000ffffff00ffff0000ffffff00ffff0000ffff0000ffff0000ffff00ffffff0000ffff0000ffff0000ffff00ffffff0000000000000000000000ff00ff00000000000000000000000000ff00ff000000000000ff000000ff00000000000000ff000000ff000000ff00000000000000ff000000ffff000000000000ffff000000000000ffff000000000000ffff00000000
|0,6=>0xffffffff00000000ffffffffffffff00ffffffff00000000ffffffffffffff00ff00ff00ff00ff00ffffffffff00ff00ff00ff00ff00ff00ffffffffff00ff000000ff000000ff000000ffff0000ff000000ff000000ff000000ffff0000ff000000000000000000ffffff00ffff00000000000000000000ffffff00ffff0000ffffffffffffffff0000ff000000ff00ffffffffffffffff0000ff000000ff00ffffff0000000000ffffff0000000000ffffff0000000000ffffff0000000000ffffffffffffffff00000000ff00ff00ffffffffffffffff00000000ff00ff00ffff0000ffffff00ffff0000ffffff00ffff0000ffffff00ffff0000ffffff00ffffffffffffffff000000000000ff00ffffffffffffffff000000000000ff00ffffffffffff0000ffffffffffffff00ffffffffffff0000ffffffffffffff00ffffff00ffffff0000000000ffffff00ffffff00ffffff0000000000ffffff00ffff0000ffff0000ffffff00ffffff00ffff0000ffff0000ffffff00ffffff00ffff000000000000ffffff0000000000ffff000000000000ffffff0000000000ff00ffffff00ff00ff00ffffff00ff00ff00ffffff00ff00ff00ffffff00ff000000000000000000ff00ffffff00ff000000000000000000ff00ffffff00ff00000000000000000000000000ff00ff00000000000000000000000000ff00ff00
|0,7=>0xffffff00ffffff00ffffff0000000000ffffff00ffffff00ffffff0000000000ff00ff00ff00ff00000000000000ff00ff00ff00ff00ff00000000000000ff000000ffff0000ffff0000ff000000ff000000ffff0000ffff0000ff000000ff00ffff000000000000ffff00ff00000000ffff000000000000ffff00ff000000000000000000000000000000000000ff000000000000000000000000000000ff00ffffffff00000000ffffffffff00ff00ffffffff00000000ffffffffff00ff00000000000000ffff000000000000ff00000000000000ffff000000000000ff000000ffff0000ffff0000ffff000000000000ffff0000ffff0000ffff00000000ff00ffffff00ffffff00ffffff00ff00ff00ffffff00ffffff00ffffff00ff00ffff0000ffffffffff000000ff00ff00ffff0000ffffffffff000000ff00ff00ffffffffffffffff000000ff00000000ffffffffffffffff000000ff00000000ffffffffffffffff0000ffff0000ff00ffffffffffffffff0000ffff0000ff00ffffffffffffffffffffff00ffff0000ffffffffffffffffffffff00ffff0000ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ffffffffffffffffff000000ff00ff00ffffffffffffffffff000000ff00ff0000ff000000ff000000ff00ff00ff000000ff000000ff000000ff00ff00ff0000
|0,8=>0xffffffff00000000000000ff00000000ffffffff00000000000000ff00000000ffffffffffffffffffff00ffffff0000ffffffffffffffffffff00ffffff00000000000000000000ffff0000ffffff000000000000000000ffff0000ffffff00ffffffff0000000000ff00ff00000000ffffffff0000000000ff00ff00000000ffffffffffff0000ffff00ffffff0000ffffffffffff0000ffff00ffffff0000ffffffffffffffff00000000ffffff00ffffffffffffffff00000000ffffff000000ffff0000ffff0000ffff0000ff000000ffff0000ffff0000ffff0000ff0000000000ffffffff00000000ffffff0000000000ffffffff00000000ffffff00ffff0000ffffffffffff0000ffffff00ffff0000ffffffffffff0000ffffff00ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff0000000000ff00ff00ffffffffffff0000ffffff00ffff0000ffffffffffff0000ffffff00ffff0000ffffffffffffffffff00ff00ff000000ffffffffffffffffff00ff00ff00000000ff00ff00ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff0000000000ff0000ffffff0000ff0000ffffff0000ff0000ffffff0000ff0000ffffff00000000000000000000000000ffffff00000000000000000000000000ffffff00ffffffff00000000ffffffff0000ff00ffffffff00000000ffffffff0000ff00
|0,9=>0xff00ffffffffff000000000000000000ff00ffffffffff000000000000000000ff0000ffff000000ff0000ffff000000ff0000ffff000000ff0000ffff000000000000000000000000ffff0000ff0000000000000000000000ffff0000ff00f0f0f0f0f0f0f0f0f0f0fff0f0f0fff0f0f0f0f0f0f0f0f0f0f0fff0f0f0fff0
|_,_=>0
def sP:Nat→Nat
|0=>0x20100190c080b0f0a030d0201000b0f0a0d0201000c0a030d0201001d0c100d0201001d0c051c0a1202010c08130a020100190c080a02010019180c080b0a020100150c0805130a1202010c080b040a030201000b0a030201000e110b0403020100110504030201000c050f040d0201000c0b0f0a030201000e050403020100
|1=>0x130a0d0201000c130b0a0d0201000c170b0a0d0201000c050a0d0201001e231422020100080b0a030201000e050a030d020100100406030201000b210a0d0201000c142002001d0c08050d0201001d0c0b040a030201000c1f0b0a1202010c080b0f040a0d0201000c10140d0201001e141202011d0c081014030d0201001c0a
|2=>0xc0a0d0201001d1e0a030d0201001d100f04060d0201000c0704060302010011020100192c0c08051c0a0d0201000c2a0a020100250c081014030d0201000c290a020100250c08270a020100280c080b0f0a030d0201000c0b160a030d020100260a020100250c08130a020100250c08170a020100250c0805040d0201000c05
|3=>0xd02010011230a06220201000805090201001d0c08100a2430020100080b160a1202010c08020100191d0c08130b0a1202010c08170b0a1202010c080a020100190c081f0a020100250c080b0a030d02010011051202011d0c080b0a0d020100110c1f0b0a0d0201000c10142d02010008050a030d0201000c10040603020100
|4=>0x100a06030d0201000c10140d0201000c05130a090201000c08360b0a0d0201000c130b0a090201000c08170b0a090201000c080a020100252c0c0810330a060201000c080b1c0a1202010c0807040a0603020100270a020100250c08050a020100250c08070a020100310c08070a020100190c0805140a2002000c08070a0603
|5=>0x1001d0c0a06020100430c080714020100420c0807143f0201000c08051c0a090201000c083d070a060201000c080714220201000c08070f0a060d0201000c05100a1202010c081014300201000c08360a020100250c080b160a020100250c08070a06023a000c0810142d0201000c0837070a060201000c080a1202011d0c08
|6=>0x1000c0b040a0d0201000c0a020100191a0c080b0a0d0201001e0b0a030d0201000a020100251d0c08100a062d0201000807140a470201000c081014020100460c080b0a020100450c08050a0d0201000c14090201001d0c0805140a0d0201000c070f040a060d0201000c100a020100190c08070f0a06030d0201000b0a0d02
|7=>0xa020100250c08360b0a1202010c080b1c0a0d0201000c1023142402010008050a020100190c0810144b01000c080b0a020100190c0807210a060d0201000c13070a060201000c0817070a060201000c080b160a0d0201000c070201002f1d0c080749060201000c081f0b0a090201000c08050b0a1202010c0807040a060302
|8=>0xd0201000c1f070a060201000c08050a1202010c08100a060d0201001e10142d02010008100a06030d0201000b0a1202011d0c080b0a030d0201000c4c070a060201000c081c0a020100250c080a02010025280c080a0d0201001d0c070f0a06030d0201000c07160a06030d020100100714020100420c0810141202010c0816
|9=>0x201000c0807160a4b0601000c08101c070a060201000c0807140a020100520c08070a06020100510c08050a090201000c0807140a2e0201000c08070a4f060201000c08073b4e0a0602010008050b0a0d0201000c0a0201004d250c08070a060d020100110c0a020100190c080b0a0d0201000e0c0a0201002f1a0c08100406
|10=>0x7590a060201000c080754060201000c08070a06570201000c08100a06020100560c0855070a060201000c08071454060201000c08361c070a06020100080714320201000c080b0a020100250c080507060201001d0c0807530a060201000c080b073b0a060201000c08100a0201002f2b0c08160a0201001b2b0c0805070a06
|11=>0xc08130b070a060201000c08170b070a060201000c0807630a060201000c08070a61060201000c08070a060201002f0c0835070a060201000c080a0602010050600c080b070a0201002f0c08070a065f0201000c08070a062d020100080a0201001b1a0c08070a0201005e5d0c08070a5b060201000c0807160a120602010c08
|12=>0x70a060201000c08074e0a2406020100080b07160a060201000c080513070a060201000c08100a060201001a0c0858070a060201002b0c081f1c070a060201000c08100768060201000c0810070a06020100670c086607640a060201000c080b160a090201000c08100a4b0601000c0805070a0201002f0c08070a0602010065
|13=>0x3e070a060201002b0c08070a06710201000c08070a06020100700c0807140a4b01000c086f074e0a060201000c08070a060201006d0c081014060201001a0c08100a120602010c08076c0a060201000c0823070a060201006b0810146a060201000c0837070a060201000c0841070a06020100510c0810230a24060201000836
|14=>0x4014060201000c08070a77060201000c08070a24060201005e08051c070a060201000c083e070a06020100340c0807160a062d020100086f07140a060201000c08070a06760201000c08070a06020100750c080a06020100441a0c08070a06020100740c0807730a060201000c08075416060201000c080b1c0a090201000c08
|15=>0x1d0c08077f0a060201000c08100a062d02010008102314060201000c080b6a0a060201000c0805100a090201000c08070a060201007e0c0807140a48020100440c08070a060201001d0c08077c0a060201000c080b0a0d0201000c070a060201007b0c087a230a060201000c080a090201001d0c08070a06020100790c0810
|16=>0x100690c08070a06030d020100070a020100835d0c081c070a24060201000807140a060201005e0c080a020100250c0810071454060201000c0807140a020100820c08056a0a060201000c08103e0714060201000c0810350a060201000c082307680a060201000c08070a06020100810c0880070a060201000c080714060201
|17=>0x860c0807850a060201000c0807040a060d0201000c070a06840201000c08070a060d0201001e07144e0a2402010008070a064a0201000c080507140a480201000c0813070a060201000c0823070a240201005d0817070a060201000c081307140a060201000c08103e0a060201002b0c081f0b070a060201000c08100a0602
|18=>0x60201000c08100a060d0201000c070a2430020100080a060201001b1a0c08070a060201008a0c081c070a060201000c08070a06020100890c08053e070a060201000c08050b0a090201000c08070a06020100880c0807160a060d0201000c410714060201000c083e0b070a060201000c0807870a060201000c08100a060201
|19=>0xc08077354060201000c08070a069001000c081f070a060201000c0807546c060201000c08074e0a060201008f0c08070a06030d0201000c07140a300201000c080b0a1202010c08078e0a060201000c081014090201000c08100a062d0201000c087a070a060201000c08078d0a060201000c08360b0a090201000c08078b0a
|20=>0xc08070a200602000c08070a062d020100080754060201000c0823070a06020100600c0810070a06020100340c082307140a060201000c0805070a060201000c080507140a060201000c0807540a060201000c080706020100920c0810070a060201002b0c08070a06020100910c0807730a062d020100080b0a090201001d
|21=>0x10070a060201000c0810400a060201000c080b1c070a060201000c0807400a060201005d0c0807160a06090201000c08070a240201005d0c08070a06720201000c08070a06020100690c080b070a24060201000c0836070a060201000c080b07160a060201000c08070a06020100780c08070a060201002f0c0835070a060201
|22=>0x201000c08070a06020100600c0836070a24060201000c08100b070a060201000c08100a06090201000c0807640a060201000c08070a060201001d0c080a06020100502b0c0810230a060201000c08074e0a060201000c0807144e0a060201000c0823070a060201005d0c0823070a060201002b0c08070a06020100860c0858
|23=>0xc0807140a0201001b0c08070a06020100340c081c070a060201000c08050b070a060201000c08070a06320201000c085823070a060201000c08070a060201005a0c08070a06300201000c0810070a060201002f0c0807160a060201001b0c08070a062d0201000c08070a060d0201000c073b0a060201000c081023070a06
|24=>0x201000c080b0a090201000c080b070a060201001d0c08070a120602010c08070a060201006b0c0810070a06480201000c0823070a2406020100080a0201001b2b0c0807146a0a060201000c08100714060201000c08360b070a060201000c08070a06020100560c087a070a060201000c08070a06020100930807680a060201
|25=>0x70a060201000c080b070a060201000c0807160a060201000c08070a06480201000c0807140a060201000c08070a060201001b0c08070a06020100500c08070a06090201000c0823070a060201000c080b070a06
|_=>0
def sO:Nat→Nat→Nat
|7,0=>0x24801d7016700e800680006
|8,0=>0x1d471cc81c481bd71b581ad81a6719e8196818f7187817f817871717168916081597151814981418139813181289120811881108108810170f980f180e980e270db70d470cd70c670be80b770b070a880a08097909070897082707a8072806a8062805b7053804b8043803b8033802c7
|9,0=>0x3e183d983d273ca83c193b893af93a7839f8397838e9386837d9375836d8366735f7357834f8346933e8336832f7327831f8315a30d830492fc82f482ec82e482db92d292ca82c192b982b182a982a09298829082879280727792707267925f8256924d9245823c9234822c8224821c8214820c820481fb91f381eb81e381db8
|9,1=>0x4ab84a3849a9493748b8483847b8472946b7463845c7454844c8444843b9433842b8424741aa4119408940173f983f183e98
|10,0=>0x6ed96e496dc86d2a6c996c096b886af96a6969d9694968aa6819678966f9665a65ba6529648a63ea635962ba621a6189610860795fe95f4a5eaa5e195d895cf95c695bd95b495ab95a3859b8592958995809577956f8566955d9554954b9542953a8532852995209516a50d950494fb94f294e8a4df94d694ce84c594bc94b39
|10,1=>0x933992a99219918990ea90598fc98f398ea98e198d988d098c798bda8b498ab98a29898a88ea884a87b9873886a98619857a8507846a83d9834982aa8219817a80e980597fc97f397eb87e297d997d097c797bda7b497ab97a4779b9792978a87819778976f9766975ca752a749973fa736972d9724971b97129709970096f6a
|10,2=>0xa109a0799fe99f599ed89e499db99d1a9c899bf99b879af99a7899e9995998c9983997a9972896a89619958994f9946993ca
|11,0=>0xc618c589c4eac459c3d8c33ac2a9c20ac179c0e9c068bfd9bf49beb9be29bd8abcf9bc5abbc9bb39ba9ab9fab969b8e8b859b7bab729b68ab5eab559b4c9b439b3a9b319b289b1eab14ab0aab019af7aaee9ae4aadaaad0aac79abe9ab59aabaaa29a98aa8f9a869a7d9a758a6d8a658a5baa51aa47aa3e9a34aa2b9a238a19a
|11,1=>0xc7b9c738c69a
|12,0=>0xcc39cba9cb19ca89c9f9c969c8d9c849
|13,0=>0xccc8
|_,_=>0
def wAt:=mkWire dB 148 256 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xb0cc1c19070601427050cc1c18071442819190cc6c69060781c520a0645c27070602c590a0c41c19090041433070601c510a0643431070642835090841c180b0dc1c190a0383431090841c180a0d41c190a0383431090841c180d0c428350b0a42421070641c1810064281d040c4283509084181c0b0dc1c190a0343431090841c180a0d434310b0a42421070641c18
|1=>0x70602819050ac2c29090841c19070601c190d0c42835090841c181c0a424010b0cc1c19070601c19040c42835090841c180a064281d0d0c8242106070142b09004501d0706028190d0c424210a064181c0a0741427070602c330b0a41c1907064280d0d0c4242107060280d070643431090841c180d0c42c2b090841c1907060142b10064242106070281d0b0a42401
|2=>0x70602c270706014330b0a41c190b09c1c180b16428310706428350b0a42421070641c18050cc2c29090841c190706024210706014330b0a41c19090841c180b16428310706434320b0a42421070641c180a0644090060c41c310a07434310b0dc2421070641c180d0c42c29090841c190706034310a074283509084181c040cc1c190a0d4242107060142b09014501d
|3=>0xd0c82c2b090841c190706034310b0ac2421070641c180a07410310a0d424210607028350a0383431090841c180a1986c69060781c520a0642c330b0a42421070641c18162546cad0a0c41c1a0607828190a074343109084181c0a28494330b09c1c190706094330a2542c27070641c180a0341c190d0c42421070602831070643431090841c18270cc28950b09c1c19
|4=>0xa0c41c19090041c180509c1c180a1d42c2b0706424010706014330b0a41c19090041c180b164283107064bc691006c141f06104281d1c0a42c270b0cc1c19070601c190a0383431090841c180a1d42c2b070642401070601c190a0383431090841c181c0a42c33090841c190706028192e0c4281d2407018310d0c42c29090841c1907060281d0d0c4283509084181c
|5=>0x90842c31070641c180706014330b0a41c19070602c590a0c41c190a2582c27070641c18350cc1cd10610c281d090042c33070641c180d0c42835090841c180a2542c27070641c180b0a42c27070641c180b32c1c1906100281d2b2f4401b0607c281d09014501d0706028190a0383431090841c18102401831070c4281d0706028750b0ac1c19230601831070c4281d
|6=>0x60a419040a4041c33070602c330b0a41c193e2b4181f100cc281d060a49040060c4281d040c42835090841c1809004401906070281d070a42819230601c310b09c2c31070641c180b09c2831070641c18013c41cef140c42819090c4281906070281d06394e0330a1b4181e0b0ac1c19090041c180a074343109084181c09084281906070281d050cc1c18071442819
|7=>0xd0c82421070641c18070643431090841c180b0ac2c27070641c182e0c4281d24070183148444501e060cc28191009c281d0706028193609c2c31070641c180b0a42421070641c18050ac501d070602819140742421070602819040c42835090841c182f2b418420607c281d0a0343431090841c180b0ac2421070641c18441a4501f0714c28191432c281906100281d
|8=>0xb0cc2421070641c180a0641831070c4281d0509c1c1807144281909024281d0706028190509c2c29070641c18040cc2835090841c18050cc40ad0607c281d0b1642831061b4181e0a0c42421070641c180506c28750b0ac1c190a4a418f8100cc281d1c0a42c33070641c180b0a41c19090041c180d0c42835090841c18070642835090841c181b1a4181e071482819
|9=>0x90041c180714428190a074343209084181c0a064281d090c4181c0a074343109084181c0b0ac1c19090041c18070643431090841c183e3441843100cc281d0b09c2c33070641c18250cc2c27070641c180b0ac2421070641c180a0343431090841c180a0c43431090841c181432c4018070a4281909004281906070281d1b2b4283107068181e090042c31070641c18
|10=>0x607c281d0a0c41c1a0607840ad0607c281d0a0c4240906070281d0b0cc181d2407818310a06419070a4041c33070601c510a064901c060c428194850418330a078ec33140c428190b0a42421070641c18250c42c27070641c180a0383431090841c181b1a4181e0714828190b0dc2421070641c181006c141f06104281d0a074283509084181c1c0a42c33061b4181e
|11=>0x734418430a0741c2b230681c310706418420a0741973500c4281e300c48c18070c4181e071482819060ac6c31060781971500c4281e0a0c42401070601d6b1606828310a32418400a0741960100c4281d2407c18310a07419050a4041c33101401c290a064d8330b0c41c190a06418400a0742c27070641c180a1d42c2b070642949240781831160642831070641842
|12=>0xa07419070a4041c33060c41c310a0741da52b0c41c1a140cc18310a0642831061b4181e050cc1c510a064141f06104281d160741c1a0a0c470290b0cc1c190a2b4181f0a074d0310610c281d076442921060cc2831070641c180a074240906070141b0714428191440c1c330a06414330b0a41c190b1642831070641d900a4841833620cc19410a078141b071442819
|13=>0x100cc281d090c42831070601d39140cc28192450c18310a07910310714c28191407c1c530a06474310b0ac1c191609428310706028250a0c41c180b0cc1c1907060181f100cc281d720c419430a07819060a4041c33060a42409060701d39140cc28196e0ac1901070cc501f060a4281d0a07424010607150330a0941c18070c574310a068501c060a4281d063e44033
|14=>0x231481c310a0641d691606828310a0642c2b070648c50070c428190a0742431060702819070c4281d060741c500a064401906070281d063ec40330a074501e060cc28190b0ac186d060781df7240ac1831090841c19070601963100c4281d076048c1a070c41c180b0ac1c192410c18310a0742819070cc281d067848c2b070c418311b0c4181e0b0cc2c29070641843
|15=>0x70601831140cc2819063e040330a074501d060cc2819050cc1c510a064281a060c41c31360a42c310706414330714428190607c40330a07470290b0cc1c19070a4ac31070683431090841c18060ac8c1b070c418310b0cc1c19060a46c31060782c27070641c18101401c290a0645027070602819071441c500a0641829100cc281d0734418430a07428ad070681c31
|16=>0x230681c31680cc28ad070682c31070641c180a8c41d23060cc242106070281d060c48c18070c4501f0706c28191a0c41c520a0642c33061b4181e360ac2c31070641841100cc281d0b0a41c19070601cee140c428190a0c424210706018290a4041c330607440330a07429592407c1831400681c330a07428b92407018310a0d4242107060c83106100281d0d0c82421
|17=>0x70602431070602825070608c1a070c418430a0741c310a0641c510a0641c510a064282507060282707060181f0a074702b0b0cc1c190a2d42431070601c180b0ac1c19540c428250706009691606828311c0a42c330706550330a0941c18074ec50330a0643431090841c180a0648c18070c41c19090041c180a5e46c3106078281906070281d090c4181c0a0741d81
|18=>0xa0c424310706024210706050310a0641c310a0748c1a070c4901d060c4181d0a074181c0a0742921060cc2c2b070641c1a0a0781c310a07450330a06450330a0641c310a0681c1a070c41903070cc40310a0741c330a0742c33070641c330a06828310706018310a06819430a078ac31070681831070642c31070642831070648c2b070c418420a0741d750a0682405
|19=>0x1c190a0c418330a064181e0a0781c18070c4186d060781c19070602c2b0706424010706174310a06818330a0741831070c41c1a060781c500a0641c290a0642c3107064901f060c41d21060cc24320706028ad070681c1b0a06418430a0742c33070642c290706418400a0748c29070c4581a0a0c48c18070c418420a074181e
|_=>0
def oO:Nat→Nat→Nat
|7,0=>0xf30186024c03180330006
|8,0=>0x26ea4c9496a9285246a47948ca914521ea429482a90051f6a3d9478a8ec51cea38946ea8d851a6a339464a8c4517ea2e945aa8b05156a299450a89c512ea249446a8885106a1f943ca87450dea1a9432a86050b6a159428a84c508ea10941ea8385066a0b9414a8245
|9,0=>0x47088d1118222c44508891110221c44308851108220c4410881110021fc43f087d10f821ec43d087910f021dc43b087510e821cc439087110e021bc437086d10d821ac435086910d0219c433086510c8218c431086110c0217c42f085d10b8216c42d085910b0215c42b085510a8214c429085110a0213c4
|9,1=>0x29c45308a51148228c45108a11140227c44f089d1138226c44d08991130225c44b08951128224c44908911120223c4
|10,0=>0x6ba6d68dab9b5436a26d38da59b48368a6d08d9f9b3c36726cd8d999b30365a6ca8d939b2436426c78d8d9b18362a6c48d879b0c36126c18d819b0035fa6be8d7b9af435e26bb8d759ae835ca6b88d6f9adc35b26b58d699ad0359a6b28d639ac435826af8d5d9ab8356a6ac8d579aac35526a98d519aa03
|10,1=>0x83a7068e0b9c1438227038e059c08380a7008dff9bfc37f26fd8df99bf037da6fa8df39be437c26f78ded9bd837aa6f48de79bcc37926f18de19bc0377a6ee8ddb9bb437626eb8dd59ba8374a6e88dcf9b9c37326e58dc99b90371a6e28dc39b8437026df8dbd9b7836ea6dc8db79b6c36d26d98db19b603
|10,2=>0x46838ca7188e2f9c5c38b27158e299c50389a7128e239c44388270f8e1d9c38386a70c8e179c2c38527098e119c203
|11,0=>0x9d2539ca7294e329c2537ca6e94db29b2535ca6a94d329a2533ca6694cb2992531ca6294c3298252fca5e94bb297252dca5a94b3296252bca5694ab2952529ca5294a32942527ca4e949b2932525ca4a94932922523ca46948b2912521ca429483290251fca3e947b28f251dca3a947328e251bca36946b2
|11,1=>0x13bca7694eb2
|12,0=>0x9f033dc67b0cf519e833cc6790cf11
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 15
def pmP:Nat→Nat
|0=>0x247c80000123ac0000091d2000002fed0000016f6800000b3b40000053da000001fed000000efe80000077b40000039f20000019ed000000cf580000067a40000031f20000018eb0000008fc80000037b40000019fa000000cf900000067780000033ac0000013d20000008fb00000047c80000023ac0000011d200000009c00000004500000001b400000003c000000000
|1=>0x2067480001023a40000673da0000311ed0000116fd800008b7e40000453f2000021ded0000106f6800004cfb40000253da0000128ef000008cf78000044bbc00002051400000c8eb000004e7c80000273a40000131f20000098eb00000467d80000233e40000119d6000008ce900000447c80000223a400000b9f6000005cf9000002c7c80000133e40000099d6000004ce9
|2=>0x404e7d80020273e40010131f20008098eb00040467c80020233ac0010119d2000808be90004044f580020227a40010111f60008088f900040447580020223a40010107d20008081e900040403480020023a4000e011d60005088e900020447480008223a40002199d60001088eb00008447480003033e40001819d60000c0ce900006047c80001073a40000831d6000040ceb
|3=>0x68447480030323a40018119d6000c08ce900060447480030023a40016111d2000a0cce900050647c80028323a40014139f2000a08cf900050467580028233a40014111f6000a088f900050447580028223a400121b9d200090c8eb00048447580024223a40012091d20008488e900040c4f48002060fa40010305d60008181eb00040c0f480020603ac0010199d200080c8e9
|4=>0x1786674800b8323a4005c011d6002e008e9001604474800a4223a40050199d200280c8e9001404674800a0223e40050111d60028088e9000d844758006c223a40034911d2001a08ce9000d0447480060323ac0030191d20018088f9000c0447580060223a40030011d6001200ce9000784e748003c233a4001c139d2000e088eb00070447480034233a4001a111f2000d088eb
|5=>0x5c064f4802e0323a40164191d200b0241e1005506674802a0323a40150119d6008a0c8e900448447480220333e40110199d200880c8eb00440647480220233a40110111f20088088e900440247480208123a40100199d20080088e9003c045f4801e0227a400f0111d2003b0c8e9001d06474800e4223a40070911d200380c8eb001c06474800e0233a40070113d20038088e9
|6=>0x105c06474882e0223a44114111d220880cce91044046f688220223a4405c191d2202c0c8e910048667584220233ec2070503d21030083e908070447584020227a41800119f2048808ce902040447480801233e40400839f20200418f8010020678804082e7e4020007bf2010003df10080018fc804000afb40200043f20100021ed0080009f680400047a40172191d200b84c8e9
|7=>0x60034333a60110111d300810cce9804086474c0204233ae0078111d7002f0c8e9801700475c00b4323a6001e119f3000908cf980040447cac020223e50050111d2800e088e9400604474902e0323a48110191d24038088e920040447490000223a46014119d620b80cce9
|_=>0
def pmB:Nat→Nat→Nat
|7,0=>0x4021803011a
|8,0=>0x1f44401f0835cb3c396a38d4c2c5034f1f3b1ebc070831331d210a1c37370b124d0d1ba9c3d1c836433156cebf2b34320fca45201d3044c4
|9,0=>0xe23631d1788ab543fd2c1aacd3d6e0c07c73164dec010423a9f20e62251595a137452273f66c6ae1419156a59bd240e2adb31a762c9b6b5602952696591e92425cfc152ccd5bf28162829116f46501f227077d0634c2a6b41
|10,0=>0x285a578a936c8b6b589556f452d6978072b58f746b564bec7d05dfb5b2a86e849e265b7ea6d9598f94b95e6a094ae82d9a8e8082738f6ab5527cb281b7b02a8f528de5f554bba5b07fe0a48df085f35f78ddd3ebb879b12ce4905272e15254a2705290526aaf52816826da6f6a8cb5edba227459d78f5272e3715252286152f2
|10,1=>0x556a2fb0e2eab0f567e73ef1bea670ac2e52a17fb2b45b8692
|11,0=>0x5b2675684794ee52dc98879a9652b3596e547294ef267ba7536a56499c6ef676a0ac5d529cacad9b83529d8974525348526a6d875c7aa396cf6a52e86ed899b5da526e
|12,0=>0x52062626524e527a
|13,0=>5
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 37 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_254 12 roots_254 ops++addP pm 1 dom_175 9 roots_175 ops++addP pm 2 dzo_87_8 6 roots_87 ops++addP pm 3 dom_239 11 roots_239 ops++addP pm 4 dom_215 7 roots_215 ops++addP pm 5 dom_253 12 roots_253 ops++addP pm 6 dom_251 12 roots_251 ops++addP pm 7 dom_191 11 roots_191 ops++addP pm 8 dom_119 8 roots_119 ops++addP pm 9 dom_103 5 roots_103 ops++addP pm 10 dzo_247_8 8 roots_247 ops++addP pm 11 dom_127 12 roots_127 ops++addP pm 12 dom_151 6 roots_151 ops++addP pm 13 dom_87 6 roots_87 ops++addP pm 14 dzo_215_8 7 roots_215 ops++addP pm 15 dom_247 10 roots_247 ops++addP pm 16 dom_55 5 roots_55 ops++addP pm 17 dom_63 9 roots_63 ops++addP pm 18 dom_246 9 roots_246 ops++addP pm 19 dom_190 10 roots_190 ops++addP pm 20 dom_183 8 roots_183 ops++addP pm 21 dzo_223_32 8 roots_223 ops++addP pm 22 dom_159 8 roots_159 ops++addP pm 23 dom_223 10 roots_223 ops++addP pm 24 dom_207 7 roots_207 ops++addP pm 25 dzo_215_32 7 roots_215 ops++addP pm 26 dzo_87_32 6 roots_87 ops++addP pm 27 dom_231 7 roots_231 ops++addP pm 28 dom_111 9 roots_111 ops++addP pm 29 dom_238 10 roots_238 ops++addP pm 30 dom_221 9 roots_221 ops++addP pm 31 dom_237 9 roots_237 ops++addP pm 32 dom_143 6 roots_143 ops++addP pm 33 dom_167 6 roots_167 ops++addP pm 34 dom_243 9 roots_243 ops++addP pm 35 dzo_175_64 7 roots_175 ops++addP pm 36 dzo_191_64 8 roots_191 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_255 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_175 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_87_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_191 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_247_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_127 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_215_8_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_247 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_zo_223_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_223 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_207 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_zo_215_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_zo_87_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_238 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_221 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_237 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_143 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_zo_175_64_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_zo_191_64_168 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_254 12 s (0,roots_254.map (·&&&dom_254)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_254 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_255==dom_255)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_255 gM v ys):RunD true dom_255 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_255 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 6 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 56 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 56 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 89 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 89 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_0 : ∀ i, 0 ≤ i → i < 128 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_128 : ∀ i, 128 ≤ i → i < 153 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 25 128 = true)
private theorem z10 : ∀ i, 0 ≤ i → i < 153 → Z 10 i = true := (range_split z10_0 z10_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 67 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 67 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z12 : ∀ i, 0 ≤ i → i < 8 → Z 12 i = true := span_ok (by decide +kernel : span (Z 12) 8 0 = true)
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
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [0, 7] }, { op := GateOp.or, inputs := [6, 7] }, { op := GateOp.or, inputs := [4, 9] }, { op := GateOp.or, inputs := [0, 1] }, { op := GateOp.or, inputs := [11, 2] }, { op := GateOp.and, inputs := [10, 12] }, { op := GateOp.or, inputs := [2, 3] }, { op := GateOp.or, inputs := [14, 8] }, { op := GateOp.and, inputs := [5, 15] }, { op := GateOp.or, inputs := [1, 8] }, { op := GateOp.and, inputs := [3, 17] }, { op := GateOp.and, inputs := [4, 9] }, { op := GateOp.or, inputs := [13, 16] }, { op := GateOp.or, inputs := [20, 18] }, { op := GateOp.or, inputs := [21, 19] }]

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 22⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
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

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_52674_aux

theorem PEqualNP.Outside.L_meta_52674 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_52674_aux.main
