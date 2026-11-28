import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_51568_aux
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

def dom_51 : Nat := 0xf000f000f000f
def goal_51 : Nat := 0xeeeeeeeecccc0000eeeeeeeecccc0000eeeeeeeecccc0000eeeeeeeecccc0000
def roots_51 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_54 : Nat := 0x55005500550055
def goal_54 : Nat := 0xfcfcccccfcfc0000fcfcccccfcfc0000fcfcccccfcfc0000fcfcccccfcfc0000
def roots_54 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xfefeeeeefcfc0000fefeeeeefcfc0000fefeeeeefcfc0000fefeeeeefcfc0000
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_58 : Nat := 0x505050505050505
def goal_58 : Nat := 0xffccffcccccc0000ffccffcccccc0000ffccffcccccc0000ffccffcccccc0000
def roots_58 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xffeeffeeeeccaa00ffeeffeeeeccaa00ffeeffeeeeccaa00ffeeffeeeeccaa00
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xfffaffaafaf0aa00fffaffaafaf0aa00fffaffaafaf0aa00fffaffaafaf0aa00
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_62 : Nat := 0x5555555555555555
def goal_62 : Nat := 0xfffcffccfcfc0000fffcffccfcfc0000fffcffccfcfc0000fffcffccfcfc0000
def roots_62 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfffeffeefefcaa00fffeffeefefcaa00fffeffeefefcaa00fffeffeefefcaa00
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_73 : Nat := 0x3030000000000000303
def goal_73 : Nat := 0xffaaffaaffaaffaaaa00aa00aa00aa00ffaaffaaffaaffaaaa00aa00aa00aa00
def roots_73 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_83 : Nat := 0xf000f00000000000f000f
def goal_83 : Nat := 0xeeeeeeeeeeeeeeeecccc0000cccc0000eeeeeeeeeeeeeeeecccc0000cccc0000
def roots_83 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_86 : Nat := 0x5500550000000000550055
def goal_86 : Nat := 0xfcfcccccfcfcccccfcfc0000fcfc0000fcfcccccfcfcccccfcfc0000fcfc0000
def roots_86 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_87 : Nat := 0xff00ff0000000000ff00ff
def goal_87 : Nat := 0xfefeeeeefefeeeeefcfc0000fcfc0000fefeeeeefefeeeeefcfc0000fcfc0000
def roots_87 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_90 : Nat := 0x50505050000000005050505
def goal_90 : Nat := 0xffccffccffccffcccccc0000cccc0000ffccffccffccffcccccc0000cccc0000
def roots_90 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f
def goal_91 : Nat := 0xffeeffeeffeeffeeeeccaa00eeccaa00ffeeffeeffeeffeeeeccaa00eeccaa00
def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_93 : Nat := 0x333333330000000033333333
def goal_93 : Nat := 0xfffaffaafffaffaafaf0aa00faf0aa00fffaffaafffaffaafaf0aa00faf0aa00
def roots_93 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_94 : Nat := 0x555555550000000055555555
def goal_94 : Nat := 0xfffcffccfffcffccfcfc0000fcfc0000fffcffccfffcffccfcfc0000fcfc0000
def roots_94 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_95 : Nat := 0xffffffff00000000ffffffff
def goal_95 : Nat := 0xfffeffeefffeffeefefcaa00fefcaa00fffeffeefffeffeefefcaa00fefcaa00
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

def dom_104 : Nat := 0x101000001010000010100000101
def goal_104 : Nat := 0xffffffffff00ff00ff00ff0000000000ffffffffff00ff00ff00ff0000000000
def roots_104 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_105 : Nat := 0x303000003030000030300000303
def goal_105 : Nat := 0xffffffffffaaffaaffaaffaaaa00aa00ffffffffffaaffaaffaaffaaaa00aa00
def roots_105 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffffffffffeeffeeffeeffeeaa00aa00ffffffffffeeffeeffeeffeeaa00aa00
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_109 : Nat := 0x3333000033330000333300003333
def goal_109 : Nat := 0xffffffffffaaffaaffaaffaaaa00aa00ffffffffffaaffaaffaaffaaaa00aa00
def roots_109 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xffffffffffeeffeeffeeffeeaa00aa00ffffffffffeeffeeffeeffeeaa00aa00
def roots_111 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_114 : Nat := 0x50005000500050005000500050005
def goal_114 : Nat := 0xffffffffcccccccccccccccccccc0000ffffffffcccccccccccccccccccc0000
def roots_114 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def goal_115 : Nat := 0xffffffffeeeeeeeeeeeeeeeecccc0000ffffffffeeeeeeeeeeeeeeeecccc0000
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_117 : Nat := 0x330033003300330033003300330033
def goal_117 : Nat := 0xfffffffffafaaaaafafaaaaaf0f00000fffffffffafaaaaafafaaaaaf0f00000
def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xfffffffffcfcccccfcfcccccfcfc0000fffffffffcfcccccfcfcccccfcfc0000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xfffffffffefeeeeefefeeeeefcfc0000fffffffffefeeeeefefeeeeefcfc0000
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_122 : Nat := 0x5050505050505050505050505050505
def goal_122 : Nat := 0xffffffffffccffccffccffcccccc0000ffffffffffccffccffccffcccccc0000
def roots_122 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffffffffffeeffeeffeeffeeeeccaa00ffffffffffeeffeeffeeffeeeeccaa00
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_124 : Nat := 0x11111111111111111111111111111111
def goal_124 : Nat := 0xfffffffffff0ff00fff0ff00f0f00000fffffffffff0ff00fff0ff00f0f00000
def roots_124 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xfffffffffffaffaafffaffaafaf0aa00fffffffffffaffaafffaffaafaf0aa00
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_126 : Nat := 0x55555555555555555555555555555555
def goal_126 : Nat := 0xfffffffffffcffccfffcffccfcfc0000fffffffffffcffccfffcffccfcfc0000
def roots_126 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xfffffffffffeffeefffeffeefefcaa00fffffffffffeffeefffeffeefefcaa00
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_137 : Nat := 0x30300000000000000000000000000000303
def goal_137 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_137 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_141 : Nat := 0x333300000000000000000000000000003333
def goal_141 : Nat := 0xfffafffafffafffafffafffafffafffaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_141 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_147 : Nat := 0xf000f000000000000000000000000000f000f
def goal_147 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaacccc0000cccc0000cccc0000cccc0000
def roots_147 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_148 : Nat := 0x11001100000000000000000000000000110011
def goal_148 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0f0f00000f0f00000f0f00000f0f00000
def roots_148 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_149 : Nat := 0x33003300000000000000000000000000330033
def goal_149 : Nat := 0xfffffafafffffafafffffafafffffafaf0f00000f0f00000f0f00000f0f00000
def roots_149 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_150 : Nat := 0x55005500000000000000000000000000550055
def goal_150 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0fcfc0000fcfc0000fcfc0000fcfc0000
def roots_150 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_151 : Nat := 0xff00ff00000000000000000000000000ff00ff
def goal_151 : Nat := 0xfffffafafffffafafffffafafffffafafcfc0000fcfc0000fcfc0000fcfc0000
def roots_151 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_153 : Nat := 0x303030300000000000000000000000003030303
def goal_153 : Nat := 0xffffffaaffffffaaffffffaaffffffaaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_153 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_154 : Nat := 0x505050500000000000000000000000005050505
def goal_154 : Nat := 0xffffff00ffffff00ffffff00ffffff00cccc0000cccc0000cccc0000cccc0000
def roots_154 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def goal_155 : Nat := 0xffffffaaffffffaaffffffaaffffffaaeeccaa00eeccaa00eeccaa00eeccaa00
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_156 : Nat := 0x1111111100000000000000000000000011111111
def goal_156 : Nat := 0xfffffff0fffffff0fffffff0fffffff0f0f00000f0f00000f0f00000f0f00000
def roots_156 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_157 : Nat := 0x3333333300000000000000000000000033333333
def goal_157 : Nat := 0xfffffffafffffffafffffffafffffffafaf0aa00faf0aa00faf0aa00faf0aa00
def roots_157 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_158 : Nat := 0x5555555500000000000000000000000055555555
def goal_158 : Nat := 0xfffffff0fffffff0fffffff0fffffff0fcfc0000fcfc0000fcfc0000fcfc0000
def roots_158 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_159 : Nat := 0xffffffff000000000000000000000000ffffffff
def goal_159 : Nat := 0xfffffffafffffffafffffffafffffffafefcaa00fefcaa00fefcaa00fefcaa00
def roots_159 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_167 : Nat := 0xff000000ff0000000000000000000000ff000000ff
def goal_167 : Nat := 0xfffffffffafafafafffffffffafafafaeeeeeeee00000000eeeeeeee00000000
def roots_167 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_169 : Nat := 0x3030000030300000000000000000000030300000303
def goal_169 : Nat := 0xffffffffffaaffaaffffffffffaaffaaffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_169 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_171 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
def goal_171 : Nat := 0xffffffffffaaffaaffffffffffaaffaaffeeffeeaa00aa00ffeeffeeaa00aa00
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_173 : Nat := 0x33330000333300000000000000000000333300003333
def goal_173 : Nat := 0xfffffffffffafffafffffffffffafffaffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_173 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_174 : Nat := 0x55550000555500000000000000000000555500005555
def goal_174 : Nat := 0xfffffffffff0fff0fffffffffff0fff0ffccffcc00000000ffccffcc00000000
def roots_174 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_175 : Nat := 0xffff0000ffff00000000000000000000ffff0000ffff
def goal_175 : Nat := 0xfffffffffffafffafffffffffffafffaffeeffeeaa00aa00ffeeffeeaa00aa00
def roots_175 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_177 : Nat := 0x300030003000300000000000000000003000300030003
def goal_177 : Nat := 0xffffffffffffaaaaffffffffffffaaaaaaaaaaaa00000000aaaaaaaa00000000
def roots_177 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_179 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f
def goal_179 : Nat := 0xffffffffffffaaaaffffffffffffaaaaeeeeeeeecccc0000eeeeeeeecccc0000
def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_180 : Nat := 0x1100110011001100000000000000000011001100110011
def goal_180 : Nat := 0xfffffffffffff0f0fffffffffffff0f0f0f00000f0f00000f0f00000f0f00000
def roots_180 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_181 : Nat := 0x3300330033003300000000000000000033003300330033
def goal_181 : Nat := 0xfffffffffffffafafffffffffffffafafafaaaaaf0f00000fafaaaaaf0f00000
def roots_181 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_182 : Nat := 0x5500550055005500000000000000000055005500550055
def goal_182 : Nat := 0xfffffffffffff0f0fffffffffffff0f0fcfcccccfcfc0000fcfcccccfcfc0000
def roots_182 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_183 : Nat := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
def goal_183 : Nat := 0xfffffffffffffafafffffffffffffafafefeeeeefcfc0000fefeeeeefcfc0000
def roots_183 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_185 : Nat := 0x30303030303030300000000000000000303030303030303
def goal_185 : Nat := 0xffffffffffffffaaffffffffffffffaaffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_185 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_186 : Nat := 0x50505050505050500000000000000000505050505050505
def goal_186 : Nat := 0xffffffffffffff00ffffffffffffff00ffccffcccccc0000ffccffcccccc0000
def roots_186 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffffffffffaaffffffffffffffaaffeeffeeeeccaa00ffeeffeeeeccaa00
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_188 : Nat := 0x111111111111111100000000000000001111111111111111
def goal_188 : Nat := 0xfffffffffffffff0fffffffffffffff0fff0ff00f0f00000fff0ff00f0f00000
def roots_188 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_189 : Nat := 0x333333333333333300000000000000003333333333333333
def goal_189 : Nat := 0xfffffffffffffffafffffffffffffffafffaffaafaf0aa00fffaffaafaf0aa00
def roots_189 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_190 : Nat := 0x555555555555555500000000000000005555555555555555
def goal_190 : Nat := 0xfffffffffffffff0fffffffffffffff0fffcffccfcfc0000fffcffccfcfc0000
def roots_190 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xfffffffffffffffafffffffffffffffafffeffeefefcaa00fffeffeefefcaa00
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_199 : Nat := 0xff00000000000000ff00000000000000ff00000000000000ff
def goal_199 : Nat := 0xfffffffffffffffffafafafafafafafaeeeeeeeeeeeeeeee0000000000000000
def roots_199 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_201 : Nat := 0x303000000000000030300000000000003030000000000000303
def goal_201 : Nat := 0xffffffffffffffffffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00aa00aa00
def roots_201 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_206 : Nat := 0x5555000000000000555500000000000055550000000000005555
def goal_206 : Nat := 0xfffffffffffffffffff0fff0fff0fff0ffccffccffccffcc0000000000000000
def roots_206 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_207 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def goal_207 : Nat := 0xfffffffffffffffffffafffafffafffaffeeffeeffeeffeeaa00aa00aa00aa00
def roots_207 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffffffffffffffffffaaaaffffaaaaeeeeeeeeeeeeeeeecccc0000cccc0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xfffffffffffffffffffff0f0fffff0f0fcfcccccfcfcccccfcfc0000fcfc0000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xfffffffffffffffffffffafafffffafafefeeeeefefeeeeefcfc0000fcfc0000
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def goal_218 : Nat := 0xffffffffffffffffffffff00ffffff00ffccffccffccffcccccc0000cccc0000
def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffffffffffffffffffffaaffffffaaffeeffeeffeeffeeeeccaa00eeccaa00
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_220 : Nat := 0x11111111000000001111111100000000111111110000000011111111
def goal_220 : Nat := 0xfffffffffffffffffffffff0fffffff0fff0ff00fff0ff00f0f00000f0f00000
def roots_220 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def goal_221 : Nat := 0xfffffffffffffffffffffffafffffffafffaffaafffaffaafaf0aa00faf0aa00
def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xfffffffffffffffffffffff0fffffff0fffcffccfffcffccfcfc0000fcfc0000
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffffffffffffffffffafffffffafffeffeefffeffeefefcaa00fefcaa00
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_225 : Nat := 0x300000003000000030000000300000003000000030000000300000003
def goal_225 : Nat := 0xffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaa00000000
def roots_225 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_229 : Nat := 0x3300000033000000330000003300000033000000330000003300000033
def goal_229 : Nat := 0xfffffffffffffffffffffffffafafafaffffffffaaaaaaaaaaaaaaaa00000000
def roots_229 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def goal_230 : Nat := 0xfffffffffffffffffffffffff0f0f0f0ffffffffcccccccccccccccc00000000
def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def goal_231 : Nat := 0xfffffffffffffffffffffffffafafafaffffffffeeeeeeeeeeeeeeee00000000
def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_232 : Nat := 0x10100000101000001010000010100000101000001010000010100000101
def goal_232 : Nat := 0xffffffffffffffffffffffffff00ff00ffffffffff00ff00ff00ff0000000000
def roots_232 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffffffffffffffffffaaffaaffffffffffaaffaaffaaffaaaa00aa00
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffffffffffffffffffaaffaaffffffffffeeffeeffeeffeeaa00aa00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xfffffffffffffffffffffffffffafffaffffffffffaaffaaffaaffaaaa00aa00
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_238 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def goal_238 : Nat := 0xfffffffffffffffffffffffffff0fff0ffffffffffccffccffccffcc00000000
def roots_238 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffffffffffffffffffafffaffffffffffeeffeeffeeffeeaa00aa00
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_240 : Nat := 0x1000100010001000100010001000100010001000100010001000100010001
def goal_240 : Nat := 0xffffffffffffffffffffffffffff0000ffffffff000000000000000000000000
def roots_240 : List Nat := [xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_241 : Nat := 0x3000300030003000300030003000300030003000300030003000300030003
def goal_241 : Nat := 0xffffffffffffffffffffffffffffaaaaffffffffaaaaaaaaaaaaaaaa00000000
def roots_241 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def goal_242 : Nat := 0xffffffffffffffffffffffffffff0000ffffffffcccccccccccccccccccc0000
def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffffffffffffffffffffaaaaffffffffeeeeeeeeeeeeeeeecccc0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_244 : Nat := 0x11001100110011001100110011001100110011001100110011001100110011
def goal_244 : Nat := 0xfffffffffffffffffffffffffffff0f0fffffffff0f00000f0f00000f0f00000
def roots_244 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_245 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
def goal_245 : Nat := 0xfffffffffffffffffffffffffffffafafffffffffafaaaaafafaaaaaf0f00000
def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffffffffffffffffffffff0f0fffffffffcfcccccfcfcccccfcfc0000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffffffffffffffffffafafffffffffefeeeeefefeeeeefcfc0000
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffffffffffffffffffaaffffffffffaaffaaffaaffaaaa00aa00
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffffffffffffffffff00ffffffffffccffccffccffcccccc0000
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffffffffffffffffffaaffffffffffeeffeeffeeffeeeeccaa00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_252 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
def goal_252 : Nat := 0xfffffffffffffffffffffffffffffff0fffffffffff0ff00fff0ff00f0f00000
def roots_252 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffffffffffffffffffafffffffffffaffaafffaffaafaf0aa00
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffffffffffffffffff0fffffffffffcffccfffcffccfcfc0000
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffffffffffffffffffafffffffffffeffeefffeffeefefcaa00
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
def isoMvS_98:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_98:Lower true dom_98 roots_98 goal_98 4:=lower_iso_b isoMvS_98 (by decide +kernel) lowS_41
def isoMvS_104:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_104:Lower true dom_104 roots_104 goal_104 4:=lower_iso_b isoMvS_104 (by decide +kernel) lowS_41
def isoMvS_137:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_137:Lower true dom_137 roots_137 goal_137 4:=lower_iso_b isoMvS_137 (by decide +kernel) lowS_41
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
theorem lowS_99:Lower true dom_99 roots_99 goal_99 5:=lower_slice_b [(0xa0000000a0000000a0000000a,32,33)] (by decide +kernel) lowS_98
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
def isoMvS_54:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_54:Lower true dom_54 roots_54 goal_54 4:=lower_iso_b isoMvS_54 (by decide +kernel) lowS_51
def isoMvS_58:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_58:Lower true dom_58 roots_58 goal_58 4:=lower_iso_b isoMvS_58 (by decide +kernel) lowS_51
def isoMvS_83:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_83:Lower true dom_83 roots_83 goal_83 4:=lower_iso_b isoMvS_83 (by decide +kernel) lowS_51
def isoMvS_86:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_86:Lower true dom_86 roots_86 goal_86 4:=lower_iso_b isoMvS_86 (by decide +kernel) lowS_51
def isoMvS_90:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_90:Lower true dom_90 roots_90 goal_90 4:=lower_iso_b isoMvS_90 (by decide +kernel) lowS_51
def isoMvS_114:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_114:Lower true dom_114 roots_114 goal_114 5:=lower_iso_b isoMvS_114 (by decide +kernel) lowS_43
def isoMvS_141:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_141:Lower true dom_141 roots_141 goal_141 5:=lower_iso_b isoMvS_141 (by decide +kernel) lowS_43
def isoMvS_147:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]
theorem lowS_147:Lower true dom_147 roots_147 goal_147 4:=lower_iso_b isoMvS_147 (by decide +kernel) lowS_51
def isoMvS_149:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_149:Lower true dom_149 roots_149 goal_149 5:=lower_iso_b isoMvS_149 (by decide +kernel) lowS_43
def isoMvS_150:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_150:Lower true dom_150 roots_150 goal_150 5:=lower_iso_b isoMvS_150 (by decide +kernel) lowS_43
def isoMvS_153:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_153:Lower true dom_153 roots_153 goal_153 5:=lower_iso_b isoMvS_153 (by decide +kernel) lowS_43
def isoMvS_154:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_154:Lower true dom_154 roots_154 goal_154 4:=lower_iso_b isoMvS_154 (by decide +kernel) lowS_51
def isoMvS_156:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_156:Lower true dom_156 roots_156 goal_156 5:=lower_iso_b isoMvS_156 (by decide +kernel) lowS_43
def isoMvS_169:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_169:Lower true dom_169 roots_169 goal_169 7:=lower_iso_b isoMvS_169 (by decide +kernel) lowS_105
def isoMvS_177:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_177:Lower true dom_177 roots_177 goal_177 5:=lower_iso_b isoMvS_177 (by decide +kernel) lowS_43
def isoMvS_180:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_180:Lower true dom_180 roots_180 goal_180 5:=lower_iso_b isoMvS_180 (by decide +kernel) lowS_43
def isoMvS_201:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96)]
theorem lowS_201:Lower true dom_201 roots_201 goal_201 7:=lower_iso_b isoMvS_201 (by decide +kernel) lowS_105
def isoMvS_225:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_225:Lower true dom_225 roots_225 goal_225 7:=lower_iso_b isoMvS_225 (by decide +kernel) lowS_105
def isoMvS_232:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_232:Lower true dom_232 roots_232 goal_232 7:=lower_iso_b isoMvS_232 (by decide +kernel) lowS_105
def isoMvS_240:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_240:Lower true dom_240 roots_240 goal_240 5:=lower_iso_b isoMvS_240 (by decide +kernel) lowS_43
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
|0=>0x1f59040
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x8b
|6,0=>4
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_43 5 roots_43 ops++addP pm 1 dom_51 4 roots_51 ops++addP pm 2 dom_58 4 roots_58 ops++addP pm 3 dzo_43_16 5 roots_43 ops++addP pm 4 dom_41 4 roots_41 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_59 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_zo_43_16_41 _ g hchk
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
theorem lowS_107:Lower true dom_107 roots_107 goal_107 8:=lower_slice_b [(0xc0c00000c0c00000c0c00000c0c,32,34)] (by decide +kernel) lowS_105
def dzo_99_16:=0xf0000000f0000000f0000000f0000
def gzo_99_16:=0xf0000000e0000000e0000000c0000
def gsh_99_16:=0xf0000000e0000000e0000000c
theorem lowS_zo_99_16_97:Lower true dzo_99_16 roots_99 gzo_99_16 5:=lower_iso_b (d1:=dom_99) (r1:=roots_99) (T1:=gsh_99_16) [(dom_99,16)] (by decide +kernel) (lower_slice_b (T:=gsh_99_16) [(0xc0000000c0000000c0000000c,0,2)] (by decide +kernel) lowS_97)
namespace S_115
def pG:List (Nat×Nat):=[(1,33),(1,65),(2,18),(2,34),(2,66),(3,19),(3,35),(3,67),(16,18),(17,19),(17,49),(17,81),(32,33),(32,34),(32,96),(48,49),(48,50),(48,112),(64,65),(64,66),(64,96),(80,81),(80,82),(80,112)]
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
|4,0=>0x948d4
|5,0=>0x6134d
|6,0=>0x88c8c
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf000f000f000f000f000f00000000a000a000a000a000a000a000a000af000f00000000000f000f00000000f0000000f0000000f0000000f0000c000c000c000c000c000c000c000c50005000500050005000500000000f000f000f000f0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x8d51a3544688
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
addP pm 0 dom_114 5 roots_114 ops++addP pm 1 dom_83 4 roots_83 ops++addP pm 2 dzo_99_16 5 roots_99 ops++addP pm 3 dom_99 5 roots_99 ops++addP pm 4 dom_97 4 roots_97 ops++addP pm 5 dom_51 4 roots_51 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_115 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_99_16_97 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_97 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_51 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_114 5 s (0,roots_114.map (·&&&dom_114)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_115 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_114 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32)]]
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
theorem lowS_151:Lower true dom_151 roots_151 goal_151 6:=lower_slice_b [(0xaa00aa00000000000000000000000000aa00aa,128,129)] (by decide +kernel) lowS_150
namespace S_157
def pG:List (Nat×Nat):=[(1,9),(1,129),(4,20),(4,132),(5,13),(5,21),(5,133),(8,9),(8,136),(12,13),(12,28),(12,140),(16,20),(16,144),(17,21),(17,25),(17,145),(24,25),(24,28),(24,152),(128,129),(128,132),(128,136),(128,144)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_157.map (·&&&dom_157)
def gM:=goal_157&&&dom_157
def NN:Nat→Nat
|3=>1
|4=>4
|5=>10
|6=>4
|7=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0xf5ca
|4,0=>0x43e23193380082200636
|5,0=>0xcf1564b7643d97c3443a296342345e1824b0f5280f491021a8
|6,0=>0x41a28404ed1df4509bfd
|7,0=>0x1df45
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x4444444400000000000000000000000044440000000000000000000000000000000000033303330cccccc00000000000000000000000000cccccc03333333300000000000000000000000033003300cccccccc000000000000000000000000cccc00033333300000000000000000000000000000000000c0c0c0c0000000000000000000000000c0c080b333323200000000000000000000000030303030cccc0000000000000000000000000000cccc0003030303000000000000000000000000030303030008800cc0000000000000000000000000088008b333333300000000000000000000000000000000ccccc8c8000000000000000000000000cccc0003300330000000000000000000000000033003300cccccccc000000000000000000000000c0c0c0c2222222200000000000000000000000022222222
|0,1=>0xc000c00000000000000000000000000000003232323200000000000000000000000032323232c8c8c8c8000000000000000000000000000000022223333000000000000000000000000222222220000cccc0000000000000000000000000000c0c33333333000000000000000000000000222222224444444400000000000000000000000000000003333333300000000000000000000000032323232
|_,_=>0
def sP:Nat→Nat
|0=>0x1c46010e2b1804388c0244e230087104c021c46012e711804a88c0990e235004104c0990e23489138a06010e2301e43b846011a761804588c051c40490e240087300a418820
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|4,0=>0x26a3944a845
|5,0=>0x26b47684af19b330654c918f3186
|6,0=>0xc8d79acad36
|7,0=>0x6a5
|_,_=>0
def wAt:=mkWire dB 24 158 0x3fffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x301012311b10392386311081311111
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x610051320012000001
|6,0=>0x91810071
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 8
def pmP:Nat→Nat
|0=>0x3ff7be5848f183080
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x401623005
|6,0=>0xa879
|7,0=>0xa
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 6 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_156 5 roots_156 ops++addP pm 1 dom_148 4 roots_148 ops++addP pm 2 dom_137 4 roots_137 ops++addP pm 3 dom_153 5 roots_153 ops++addP pm 4 dom_141 5 roots_141 ops++addP pm 5 dom_149 5 roots_149 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_157 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_156 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_153 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_141 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_149 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_156 5 s (0,roots_156.map (·&&&dom_156)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_157 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_156 h
def symsG:List (List (Nat×Nat)):=[[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_157==dom_157)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_157 gM v ys):RunD true dom_157 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_157 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 4 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
theorem checked (s:Nat) (hs:s≤7):∀ i<NN s,bar dom_157 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤7) (h:RunD true dom_157 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_157 roots_157 goal_157 8:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_157
theorem lowS_157:Lower true dom_157 roots_157 goal_157 8:=S_157.noCircuit
theorem lowS_171:Lower true dom_171 roots_171 goal_171 8:=lower_slice_b [(0xc0c00000c0c000000000000000000000c0c00000c0c,32,34)] (by decide +kernel) lowS_169
theorem lowS_179:Lower true dom_179 roots_179 goal_179 6:=lower_slice_b [(0xc000c000c000c0000000000000000000c000c000c000c,16,18)] (by decide +kernel) lowS_177
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
theorem lowS_242:Lower true dom_242 roots_242 goal_242 6:=lower_slice_b [(0x4000400040004000400040004000400040004000400040004000400040004,16,18)] (by decide +kernel) lowS_240
def isoMvS_62:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_62:Lower true dom_62 roots_62 goal_62 5:=lower_iso_b isoMvS_62 (by decide +kernel) lowS_55
def isoMvS_87:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_87:Lower true dom_87 roots_87 goal_87 5:=lower_iso_b isoMvS_87 (by decide +kernel) lowS_55
def isoMvS_91:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_91:Lower true dom_91 roots_91 goal_91 7:=lower_iso_b isoMvS_91 (by decide +kernel) lowS_59
def isoMvS_93:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_93:Lower true dom_93 roots_93 goal_93 6:=lower_iso_b isoMvS_93 (by decide +kernel) lowS_61
def isoMvS_94:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_94:Lower true dom_94 roots_94 goal_94 5:=lower_iso_b isoMvS_94 (by decide +kernel) lowS_55
def isoMvS_117:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)]
theorem lowS_117:Lower true dom_117 roots_117 goal_117 6:=lower_iso_b isoMvS_117 (by decide +kernel) lowS_61
def isoMvS_118:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_118:Lower true dom_118 roots_118 goal_118 7:=lower_iso_b isoMvS_118 (by decide +kernel) lowS_59
def isoMvS_122:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_122:Lower true dom_122 roots_122 goal_122 7:=lower_iso_b isoMvS_122 (by decide +kernel) lowS_115
def isoMvS_124:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_124:Lower true dom_124 roots_124 goal_124 6:=lower_iso_b isoMvS_124 (by decide +kernel) lowS_61
def isoMvS_155:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]
theorem lowS_155:Lower true dom_155 roots_155 goal_155 7:=lower_iso_b isoMvS_155 (by decide +kernel) lowS_59
def isoMvS_158:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_158:Lower true dom_158 roots_158 goal_158 6:=lower_iso_b isoMvS_158 (by decide +kernel) lowS_151
def isoMvS_167:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_167:Lower true dom_167 roots_167 goal_167 6:=lower_iso_b isoMvS_167 (by decide +kernel) lowS_151
def isoMvS_173:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_173:Lower true dom_173 roots_173 goal_173 8:=lower_iso_b isoMvS_173 (by decide +kernel) lowS_171
def isoMvS_174:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_174:Lower true dom_174 roots_174 goal_174 6:=lower_iso_b isoMvS_174 (by decide +kernel) lowS_151
def isoMvS_181:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_181:Lower true dom_181 roots_181 goal_181 8:=lower_iso_b isoMvS_181 (by decide +kernel) lowS_157
def isoMvS_182:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_182:Lower true dom_182 roots_182 goal_182 6:=lower_iso_b isoMvS_182 (by decide +kernel) lowS_179
def isoMvS_185:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_185:Lower true dom_185 roots_185 goal_185 8:=lower_iso_b isoMvS_185 (by decide +kernel) lowS_171
def isoMvS_186:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_186:Lower true dom_186 roots_186 goal_186 6:=lower_iso_b isoMvS_186 (by decide +kernel) lowS_179
def isoMvS_188:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_188:Lower true dom_188 roots_188 goal_188 8:=lower_iso_b isoMvS_188 (by decide +kernel) lowS_157
def isoMvS_199:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_199:Lower true dom_199 roots_199 goal_199 6:=lower_iso_b isoMvS_199 (by decide +kernel) lowS_151
def isoMvS_206:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_206:Lower true dom_206 roots_206 goal_206 6:=lower_iso_b isoMvS_206 (by decide +kernel) lowS_151
def isoMvS_211:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_211:Lower true dom_211 roots_211 goal_211 6:=lower_iso_b isoMvS_211 (by decide +kernel) lowS_179
def isoMvS_214:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_214:Lower true dom_214 roots_214 goal_214 6:=lower_iso_b isoMvS_214 (by decide +kernel) lowS_179
def isoMvS_218:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_218:Lower true dom_218 roots_218 goal_218 6:=lower_iso_b isoMvS_218 (by decide +kernel) lowS_179
def isoMvS_220:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_220:Lower true dom_220 roots_220 goal_220 8:=lower_iso_b isoMvS_220 (by decide +kernel) lowS_157
def isoMvS_229:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_229:Lower true dom_229 roots_229 goal_229 8:=lower_iso_b isoMvS_229 (by decide +kernel) lowS_171
def isoMvS_230:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_230:Lower true dom_230 roots_230 goal_230 7:=lower_iso_b isoMvS_230 (by decide +kernel) lowS_115
def isoMvS_241:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_241:Lower true dom_241 roots_241 goal_241 8:=lower_iso_b isoMvS_241 (by decide +kernel) lowS_171
def isoMvS_244:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_244:Lower true dom_244 roots_244 goal_244 8:=lower_iso_b isoMvS_244 (by decide +kernel) lowS_157
theorem lowS_63:Lower true dom_63 roots_63 goal_63 8:=lower_slice_b [(0xf0f0f0f0f0f0f0f0,16,20)] (by decide +kernel) lowS_59
theorem lowS_119:Lower true dom_119 roots_119 goal_119 8:=lower_slice_b [(0xaa00aa00aa00aa00aa00aa00aa00aa,32,33)] (by decide +kernel) lowS_118
def dzo_107_16:=0xf0f00000f0f00000f0f00000f0f0000
def gzo_107_16:=0xf0f00000f0e00000f0e00000e0c0000
def gsh_107_16:=0xf0f00000f0e00000f0e00000e0c
theorem lowS_zo_107_16_105:Lower true dzo_107_16 roots_107 gzo_107_16 8:=lower_iso_b (d1:=dom_107) (r1:=roots_107) (T1:=gsh_107_16) [(dom_107,16)] (by decide +kernel) (lower_slice_b (T:=gsh_107_16) [(0xc0c00000c0c00000c0c00000c0c,0,2)] (by decide +kernel) lowS_105)
namespace S_123
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(2,18),(2,34),(2,66),(3,11),(3,19),(3,35),(3,67),(8,9),(8,40),(8,72),(10,11),(10,26),(10,42),(10,74),(16,18),(17,19),(17,25),(17,49),(17,81),(24,25),(24,26),(24,56),(24,88),(32,33),(32,34),(32,40),(32,96),(48,49),(48,50),(48,56),(48,112),(64,65),(64,66),(64,72),(64,96),(80,81),(80,82),(80,88),(80,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_123.map (·&&&dom_123)
def gM:=goal_123&&&dom_123
def NN:Nat→Nat
|4=>3
|5=>15
|6=>35
|7=>15
|8=>3
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x24ddd114b105230
|5,0=>0xef180a9579940397cd966c26f5dde55b1e25964f3a798265e82576d12494117ce0ea2d07073
|6,0=>0xec765d8dd0b179da73fca326d9132b7dd79767bc74c90749e961a7e5964f5097a48b23476a0465d543d25436d23cf8f3cd20387743833423eb7231ca21b1e1ddb31afdf174020d1770c48a0c09c0909d05eae05d3a024bd
|7,0=>0xbe12d8532077981729586a42d6240e5f86f446b53c00a3b21c2cd92297df1fafa1489e0ca2c
|8,0=>0xcdd9232d0c07721
|9,0=>0x62b5b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f0f0f0f0f0a0a0a0a0a0a0a0af0f0f0f000000000f0f0f0f00000000a0a0a0a0a0a0a0a0a0a0a0a0a000a0000f000f000f000f000f000f00000000f0f0f0f0f0f0f0f0000000000000000f0f0f0f0a0a0a0a0f0f0f0f0a0a0a0af0f0f0f0f0f0f0f0f000f000f000f00f0f0f0f0f000f000a0a0a0a0a000a00f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0af0f0f0f0a0a0a0a0f000f000a000a00c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0cf0f0f0f0f0f0f0f0f0f0f0f00000000f0f00000f0f00000f0f00000f0f0000f0f0f0f0e0e0e0e0f0c0f0c0e0c0e0cf000f000f000f000f000f000f000f00a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a
|0,1=>0xf0f0f0f0f0f0f0f0f0a0f0a0f0a0f0a00000000f0f0f0f000000000f0a0f0af0f0f0f0f0f0f0f0f0f0f0f0f0a0f0a505050505050505050505050500050000000000f0f0f0f000000000a0a0a0a000000000000000050505050500050050505050505050505000500050005005050505050505050505050500000000f0f0f0f0f0c0f0c0e0e0e0e0e0c0e0cf0f0f0f0f0f0f0f0f0f0f0f0a0a0a0af0f0f0f0f0f0f0f0f0f0f0f0f000f0000f000f000f000f000f000f000a000af0f0f0f0f0a0f0a0f0f0f0f0f0a0f0a505050505000500050505050500050000000000f0f0f0f000000000f000f00f0f0f0f0f000f000f0f0f0f0f000f00
|0,2=>0xf0f0f0f0a0a0a0aa0f0a0f0a0f0a0f0a0f0a0f0a0a0a0a0050005000500050005000500000000f000f000f000f000f000f000a000a0000f000f000a000a000f000f000a000af0f0f0f0f0f0f0f0505050505000500a0a0a0a0a0a0a0a0f0f0f0f0f0a0f0a
|_,_=>0
def sP:Nat→Nat
|0=>0x34b38304501a2c43830450194030450182d02832453ce0c15c02d05831c52c40c118500a0c114f3152830453d310324500e0c50142d33832453c40c914048e0c91402101031c53ce0c714f44e0c71482ce0c534c2ca0c91481031c61440c2040
|1=>0xc114f88b54e0c500c2ce0c114084b40a0c114f2ce0c118500b80e0c11402ce0c114078b2840c114f74e0c11402d63832411403832411406d338324500b10e0c724500e0c904570b3830450142d63831c114b3831c115b2d02831c52ce0c9045
|2=>0x30b54e0c11402d540e0c11402ca10304500b3830450192d03831c500b38304534b40e0c714f2d638314050b3830459402c438304570b10e0c114d2d01030453c010e0df04500a38304560b3830450242ca10304560b38314050b58e0e31402ce
|3=>0x38304500b3831c11402ca38304500b10e0c11402d038324500b3837c11402d028304500b10e0c704500b3837c114f00b10e0c114060b58438304500b40e0c114f00b98e0c11402ce0c1140
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x2940aa005
|5,0=>0x18d8bac57628b12d88ac3f61cb0cd85ac27610b06d82ac0f6
|6,0=>0x551a9af4679fbce1e62f2a791bc71e2af0e7843405df4ef37763b95dbced77683b29986ebc75abab9d4eea074cba49d16e8563f39ddce0e697
|7,0=>0x709f76fb47d646923391948c64615efcf777b7c5a1ec2f5a7
|8,0=>0x75dfa0fc97
|9,0=>0x1de6
|_,_=>0
def wAt:=mkWire dB 39 124 0xfffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x107c10138b44032ce560728b4039281c039541d02d04e500304e492804b403939f8f0500b4e2d00b403928b40393cec02d40041392ce550324e4a2d00e4f3b00b4e0100141395400939240c12d100cb391004e2d24a012d00e502d04e4e1d001412900e4f4000b413938b503c00b4139
|1=>0x10100e4e2d04b41393c1402d38140390404e2d3c1402d100ce2d1004e2d04e402d28bc039101ce2d40b413940b413938b4039240c12d0014139540102d04e4a2d00e440738b55031014e2d540040538b4f0500b560328b4039
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x1021a6000590920001c80004306200001800
|6,0=>0x13cc004d296520e2980086500de9bb2706001b133362400171800566a0c00262484889089f2000748d91832c4000a1122
|7,0=>0x1b8b616a2d0598b21622c0578ae15a2b0558aa1522
|8,0=>0x1c8788f01
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0x4f74e74213f73d73143012f71fb0ff0fb0f70e70e107f067061053043041040036030022020014010008006004002000
|1=>0xc63affa385f3
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x50c01c2002006100240
|6,0=>0x120051cd38005d3c83000990805002d3005142105005155140045
|7,0=>0x1b8a046142329f51c69e617
|8,0=>0x167d4
|9,0=>0x14
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 12 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_107 8 roots_107 ops++addP pm 1 dom_91 7 roots_91 ops++addP pm 2 dom_59 7 roots_59 ops++addP pm 3 dom_114 5 roots_114 ops++addP pm 4 dom_115 7 roots_115 ops++addP pm 5 dom_122 7 roots_122 ops++addP pm 6 dzo_107_16 8 roots_107 ops++addP pm 7 dom_105 7 roots_105 ops++addP pm 8 dom_83 4 roots_83 ops++addP pm 9 dom_51 4 roots_51 ops++addP pm 10 dom_90 4 roots_90 ops++addP pm 11 dom_58 4 roots_58 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_123 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_107_16_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_58 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_107 8 s (0,roots_107.map (·&&&dom_107)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_123 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_107 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_123==dom_123)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_123 gM v ys):RunD true dom_123 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_123 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 15 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 35 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 35 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 15 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 15 0 = true)
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
theorem lowS_125:Lower true dom_125 roots_125 goal_125 9:=lower_slice_b [(0x30303030303030303030303030303030,16,20),(0x33330000333300003333000033330000,4,20)] (by decide +kernel) lowS_105
theorem lowS_159:Lower true dom_159 roots_159 goal_159 9:=lower_slice_b [(0xcccccccc000000000000000000000000cccccccc,16,18)] (by decide +kernel) lowS_157
theorem lowS_175:Lower true dom_175 roots_175 goal_175 9:=lower_slice_b [(0xcccc0000cccc00000000000000000000cccc0000cccc,32,34)] (by decide +kernel) lowS_173
theorem lowS_183:Lower true dom_183 roots_183 goal_183 9:=lower_slice_b [(0xcc00cc00cc00cc000000000000000000cc00cc00cc00cc,16,18)] (by decide +kernel) lowS_181
theorem lowS_187:Lower true dom_187 roots_187 goal_187 9:=lower_slice_b [(0xc0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0c0c,16,18)] (by decide +kernel) lowS_185
namespace S_189
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,129),(4,20),(4,132),(5,13),(5,21),(5,37),(5,133),(8,9),(8,40),(8,136),(12,13),(12,28),(12,44),(12,140),(16,20),(16,144),(17,21),(17,25),(17,49),(17,145),(24,25),(24,28),(24,56),(24,152),(32,33),(32,40),(32,160),(36,37),(36,44),(36,52),(36,164),(48,49),(48,52),(48,56),(48,176),(128,129),(128,132),(128,136),(128,144),(128,160)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_189.map (·&&&dom_189)
def gM:=goal_189&&&dom_189
def NN:Nat→Nat
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|9,0=>0x3abd3
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcccccccc000000000000000000000000cccccccc0000000333300003333000000000000000000003333000033330000cc00cc00cc00cc000000000000000000cc00cc00cc00cc030303030303030300000000000000000303030303030303088888888888888880000000000000000888888888888888b33333333333333300000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x2c688
|_=>0
def sO:Nat→Nat→Nat
|9,0=>6
|_,_=>0
def wAt:=mkWire dB 6 190 0x3fffffffffffffffffffffffffffffffffffffffffffffff
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
addP pm 0 dom_188 8 roots_188 ops++addP pm 1 dom_185 8 roots_185 ops++addP pm 2 dom_181 8 roots_181 ops++addP pm 3 dom_173 8 roots_173 ops++addP pm 4 dom_157 8 roots_157 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_189 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_188 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_157 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_188 8 s (0,roots_188.map (·&&&dom_188)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_189 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_188 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_189==dom_189)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_189 gM v ys):RunD true dom_189 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_189 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_189 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_189 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_189 roots_189 goal_189 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_189
theorem lowS_189:Lower true dom_189 roots_189 goal_189 10:=S_189.noCircuit
theorem lowS_231:Lower true dom_231 roots_231 goal_231 9:=lower_slice_b [(0xcc000000cc000000cc000000cc000000cc000000cc000000cc000000cc,32,34)] (by decide +kernel) lowS_229
theorem lowS_235:Lower true dom_235 roots_235 goal_235 10:=lower_slice_b [(0xc0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c,32,34)] (by decide +kernel) lowS_233
theorem lowS_237:Lower true dom_237 roots_237 goal_237 10:=lower_slice_b [(0x303000003030000030300000303000003030000030300000303000003030,128,132)] (by decide +kernel) lowS_233
theorem lowS_243:Lower true dom_243 roots_243 goal_243 9:=lower_slice_b [(0xc000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c,16,18)] (by decide +kernel) lowS_241
theorem lowS_246:Lower true dom_246 roots_246 goal_246 9:=lower_slice_b [(0x44004400440044004400440044004400440044004400440044004400440044,16,18)] (by decide +kernel) lowS_244
def isoMvS_95:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_95:Lower true dom_95 roots_95 goal_95 8:=lower_iso_b isoMvS_95 (by decide +kernel) lowS_63
def isoMvS_126:List (Nat×Nat):=[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_126:Lower true dom_126 roots_126 goal_126 8:=lower_iso_b isoMvS_126 (by decide +kernel) lowS_119
def isoMvS_190:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_190:Lower true dom_190 roots_190 goal_190 9:=lower_iso_b isoMvS_190 (by decide +kernel) lowS_183
def isoMvS_207:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_207:Lower true dom_207 roots_207 goal_207 9:=lower_iso_b isoMvS_207 (by decide +kernel) lowS_175
def isoMvS_215:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_215:Lower true dom_215 roots_215 goal_215 9:=lower_iso_b isoMvS_215 (by decide +kernel) lowS_183
def isoMvS_219:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_219:Lower true dom_219 roots_219 goal_219 9:=lower_iso_b isoMvS_219 (by decide +kernel) lowS_187
def isoMvS_221:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_221:Lower true dom_221 roots_221 goal_221 10:=lower_iso_b isoMvS_221 (by decide +kernel) lowS_189
def isoMvS_222:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_222:Lower true dom_222 roots_222 goal_222 9:=lower_iso_b isoMvS_222 (by decide +kernel) lowS_183
def isoMvS_238:List (Nat×Nat):=[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_238:Lower true dom_238 roots_238 goal_238 9:=lower_iso_b isoMvS_238 (by decide +kernel) lowS_231
def isoMvS_245:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)]
theorem lowS_245:Lower true dom_245 roots_245 goal_245 10:=lower_iso_b isoMvS_245 (by decide +kernel) lowS_189
def isoMvS_249:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)]
theorem lowS_249:Lower true dom_249 roots_249 goal_249 10:=lower_iso_b isoMvS_249 (by decide +kernel) lowS_237
def isoMvS_250:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_250:Lower true dom_250 roots_250 goal_250 9:=lower_iso_b isoMvS_250 (by decide +kernel) lowS_243
def isoMvS_252:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_252:Lower true dom_252 roots_252 goal_252 10:=lower_iso_b isoMvS_252 (by decide +kernel) lowS_189
theorem lowS_127:Lower true dom_127 roots_127 goal_127 11:=lower_slice_b [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,16,20)] (by decide +kernel) lowS_123
theorem lowS_191:Lower true dom_191 roots_191 goal_191 11:=lower_slice_b [(0xcccccccccccccccc0000000000000000cccccccccccccccc,16,18)] (by decide +kernel) lowS_189
theorem lowS_239:Lower true dom_239 roots_239 goal_239 11:=lower_slice_b [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,32,34)] (by decide +kernel) lowS_237
theorem lowS_247:Lower true dom_247 roots_247 goal_247 11:=lower_slice_b [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,16,18)] (by decide +kernel) lowS_245
def dzo_235_16:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000
def gzo_235_16:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0e00000f0e00000e0c0000
def gsh_235_16:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0e00000f0e00000e0c
theorem lowS_zo_235_16_105:Lower true dzo_235_16 roots_235 gzo_235_16 9:=lower_iso_b (d1:=dom_235) (r1:=roots_235) (T1:=gsh_235_16) [(dom_235,16)] (by decide +kernel) (lower_slice_b (T:=gsh_235_16) [(0xc0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c,0,2),(0xf0f00000f0f00000f0f00000f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_105)
namespace S_251
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(1,129),(2,18),(2,34),(2,66),(3,11),(3,19),(3,35),(3,67),(3,131),(8,9),(8,40),(8,72),(8,136),(10,11),(10,26),(10,42),(10,74),(10,138),(16,18),(16,144),(17,19),(17,25),(17,49),(17,81),(17,145),(24,25),(24,26),(24,56),(24,88),(24,152),(32,33),(32,34),(32,40),(32,96),(32,160),(48,49),(48,50),(48,56),(48,112),(48,176),(64,65),(64,66),(64,72),(64,96),(64,192),(80,81),(80,82),(80,88),(80,112),(80,208),(128,129),(128,136),(128,144),(128,160),(128,192),(130,131),(130,138),(130,146),(130,162),(130,194)]
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
|4,0=>0xa918a2760d
|5,0=>0xd34f4ac61192dec5507101c69
|6,0=>0xa75d896273584f83ee053ecd31aff30c0340b082
|7,0=>0xc4933bf75baaa5f9423592d199123a852857bc8479edb6ceea68ddc5b416596a658c7e4f00b488c2456b04215a3fa053f5773a47733a0f32c2332580306842f10d2d6cc2b3d428e9928a67269bc215e7206bb1d4271afa414d30126b80e48d0e40b0ae460630a0461c
|8,0=>0xb50f4a7cc2976bc961a0946c1905f8823637de977701d713e66eee76ceea658e65cf2752a3e4efc14be644ab0f4a15248e03487bf460e443932428e0422663252430c6b2eb252a11729e432966726ed82676f2495c23b421c63a1a7ca163bb1503613f531302e1154f0fb130c9530b2490ac0f0979107aa3078a506d4d
|9,0=>0xb329c96cf48131e5fa06568824df96479684699941be83636834d1b2e76c2d5b71c8c21c20b10b3a03c5a
|10,0=>0xc34df7de6758b411497e
|11,0=>0xff75e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f0f000f000a0a0a0a0a000a000f0f0f0f0f000f000a0a0a0a0a000a00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000f0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f00f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0af0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0ac0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0cf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f00000000f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0af0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a0f0f0f0f0a0a0a0af0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000f0f0f0f0f0f0f0f0f000f000f000f000f0f0f0f0f0f0f0f0f000f000f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0f0c0e0e0e0e0e0c0e0cf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000a0a0a0a0a000a00
|0,1=>0xf0f0f0f0f0f0f0f0f0f0f0f0f0a0f0a0f0f0f0f0f0f0f0f0f0f0f0f0f0a0f0af0f0f0f0f0f0f000f0f0a0a0f0f0a000f0f0f0f0f0f0f000f0f0a0a0f0f0a00000000005050505000000000500050000000000050505050000000005000500f0f0f0f050505050f0f0f0f050005000f0f0f0f050505050f0f0f0f05000500f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f0000f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a0f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0af0f0f0f0f0a0f0a0f0f0f0f0f0a0f0a0f0f0f0f0f0a0f0a0f0f0f0f0f0a0f0af0f0f0f0f0f0f0f0f0f0f0f0f000f000f0f0f0f0f0f0f0f0f0f0f0f0f000f00f0f0f0f0f0f0f0f0f0a0f0a0f0a0f0a0f0f0f0f0f0f0f0f0f0a0f0a0f0a0f0af0f0f0f0f0f0f0f0f0f00000f0f00000f0f0f0f0f0f0f0f0f0f00000f0f00000000000000000000f0f0f0f0f000f0000000000000000000f0f0f0f0f000f00f0f0f0f0f0c0f0c0e0e0e0e0e0c0e0c0f0f0f0f0f0c0f0c0e0e0e0e0e0c0e0c0000000000000000f0f0f0f0f0a0f0a00000000000000000f0f0f0f0f0a0f0a00000000f0f0f0f000000000f0a0f0a000000000f0f0f0f000000000f0a0f0af0f0f0f0a0a0a0a0f000f000a000a000f0f0f0f0a0a0a0a0f000f000a000a00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a0f000f000a000a00
|0,2=>0xf0f0f0f000000000f0f0f0f0f0a0f0a0f0f0f0f000000000f0f0f0f0f0a0f0af0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000000000000005050505050005000000000000000000050505050500050050505050500050005050505050005000505050505000500050505050500050000000000f0f0f0f000000000a0a0a0a000000000f0f0f0f000000000a0a0a0af000f000f0f0f0f0f000f000f0a0f0a0f000f000f0f0f0f0f000f000f0a0f0a00000000f0a0f0a000000000f0a0f0a000000000f0a0f0a000000000f0a0f0a505050505050505050505050500050005050505050505050505050505000500000000000000000000000000f0a0f0a0000000000000000000000000f0a0f0a00f000f000a000a000f000f000a000a000f000f000a000a000f000f000a000a00000000f0f0f0f000000000f000f00000000000f0f0f0f000000000f000f00f0f0f0f000f000f0f0f0f0f000a000a0f0f0f0f000f000f0f0f0f0f000a000a0000000000000000f0a0f0a0f0a0f0a00000000000000000f0a0f0a0f0a0f0a00f000f000f000f000a000a000a000a000f000f000f000f000a000a000a000a000000000000000000f000f000a000a0000000000000000000f000f000a000af000f000f000f000f0f0f0f0f0a0f0a0f000f000f000f000f0f0f0f0f0a0f0a
|_,_=>0
def sP:Nat→Nat
|0=>0x30e6832092921ce6582c320930e3430892921ce3445852473951031491ce18315124e2c32012801c60c824a0060c850a38b0c52401d30c824a48e34344930e2c321024c1030890060c804a00b0c50401c60c52401032010071831410040c2040
|1=>0x3840c824f1ce7c32092921ce3432092921ce2de20928738470320928738d1035c91ce1035c82521ce64418320930e6040c824c38b0c850a1ce60d2c314930e65318320928e35a0c524739b14824a48738d1035c224739810308824c38d103089
|2=>0x3460c524c39a2c314224c38b0c54491ce6460d720928e6460c824c3932c314824c39f2c32092873841835c220938d1038c91ce6c824a4873860c22092923992c314224c38418320988e80b0c224a1ce2c32092801d918314824c39334b58824a
|3=>0x24a98739910b0c824c1ce2c32092a11ce6cb5c824c2873862c35c824a38b0c524a9473a42c32092873994cb0c824a1ce60b0c524a1ce34458824a1ce5440c824a1ce6842c31482473932c320928739b5c824a4873932c35c824a3860c844928e
|4=>0xc824aa0738b0c22092921ce18b0c508928e10b0c82621ce7cb0c520928739b2c508928739b2e320928739834b0c824c28e64b0c520930738418320930e18b0d720930a38b0c824a9c738d68320928739f10b0c824a1ce2c314824a4873860c8
|5=>0x1ce34b0c524c1ceb8b14824a1ce7d92c32092873992c35c824a1ce7cb0c824a1ce64b0c824c1ce2c320930ab473842c35c22091ce2d62092ac1ce65a2c320928738b0c508930e10b0c220930e2c3a8824a1ce2c32093291ce64b58520928738b
|6=>0x20928738b0c824a88738d18320928738b0d714824a1ce10b58824a1ce18b0c520928738d2c31492873842c32093073992c320928739f68b0c824a1cebcb0c824a1ce3460c824c28e68b0c220930a38b0c844928739918314824a1ce64b58824a
|7=>0xb0c824a1ce2c314824a1ce2d62092873862c320928738b0c824c2873ae2c824a1ce2c38c824a1ce34b0c824c28738b0c824a94738b0d708824a1ce2c308824c28e68b0c824a1ce60b0c220928738b585
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x154005
|5,0=>0x21506d815604140a6
|6,0=>0x14984b711583f60e583270b18266
|7,0=>0x63e1878601d7975c616a758a15b754e14b850e13c74d5d2d849611e745a10f741e0ff83e1cf083a20e173660d2732a0c282edcb472b20a48275c95823608581f9c7681ba066817dc587
|8,0=>0xcc27288c823179c3e3069bfa2f68bba2e59b726d48b322c39aea6b28aa66a27a6a2928a2a28199e627099a2260895e64f891e23e98d662e789661d885620c980e5fb87ca5ea87865d987461c987025b886c21a8867e5978
|9,0=>0x3be7eda3ad9e9639c9e5238c8e0e77b8dce36b8d8a75a8d467498d063398
|10,0=>0xf723d57f363c58
|11,0=>0x3e47
|_,_=>0
def wAt:=mkWire dB 48 252 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 14
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x2ca481d2874b312d78831287473534a4b212874b5e282481d20a470d20b4a2d1cd8a2128b482d20a42101cb472128b4b1d3ce4d302c84a1d3c94d302c74b2128748293ce4d302c84a1d20b44082ca481d28751391020b292074a1d1c84f3930d072920b4a2d3ce482934c0b1d2c84a1d
|1=>0x20a472d1c3476628d4c341ca482d28b572d5cbc51d20a5f2f30d472920b433d34c0b212875d2d1028b29207471520a482d28b572f14748291ca472d2044a2d2874a2d188472d3c94d302c84a1d2874d1d20b591f14b482920a482d18a472d2c34b5e14742291c84a2d08b472128b4b21
|2=>0x14748291c5476614b4829084072d1c84a2d20a4b1d2c84a1d2cc48292074a1d20a42101c84a2d147452d20a472d1ca452d20a472d1d9852d20a4b29282481d1c5882920b4a2d0cb572f14748292d78a092074b1520a481d2874a2d2c748322874885084872128b4f3934c0b21287452d
|3=>0x20a4d1d2c84a1d14b4a1d20a4b1d2ca4a1d2c74831287461620a4b1d20b46291cb42111c84a2d2d7851d20a472d2048a2d204472928b42121c84a2d2c34831287451d20a4b1d08bc81d2884b8920c8a1d647c52d20a4a211884b1d1c3482d28b473628b482d1074a2d20a591f14b4829
|4=>0x20a48292c84a1d18348292c7452d20a4b15147482968846292c74d292c84a1d30d882d08a472128b470d28d882d1c4481128b48292074a1d2ca481d28748ad2cc8a1d1ca452f20a470d14b482960ac6212c74b5e282481d2074a212c74b2920c8a1d18548292c7432d2074a212c3451f
|5=>0x8290c74b1d287460d2c7451f20a4b212874b0a2074a09207481d28746292c74b09207431d20a4832287482d1cb451d20a4b290c748292c7482d2884b29287452d20a46292c74b8d147c8292c74b212874b312074a1d084072128b452d20a472d0c7452d
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x66000000000c000
|6,0=>0x12a800040a1b50b2800022a0c5
|7,0=>0x17c4ba45b22c915c8aa453228913e60004e1a61128891346a22510a88143f19eccee873437a1ad0ce86343019710b08544289938c948473221904c7a83941aa0c8c5c82a4
|8,0=>0x2a254e3a59d20e8a74239f9cf0e7273729a1cc4e5c72c2949c98e4672038e9c68e2e7143889c38e167083829c08dfe6fc37c9bd8de66f03769ba8dce6e43709b78db66d836a9b48d9e6cc3649b18d866c03
|9,0=>0x1732b895bcada56b2b4959caca5632b0957caba55b2ac955caaa5532
|10,0=>0xbc0ddc6ec3751
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 13
def pmP:Nat→Nat
|0=>0x1ff80ff407da03df01cf80bc8044001ff00fe807bc03da01ec00f28070002c00129009280440021a00dd00638029401020080003f801040080002000070001c00020000
|1=>0xaf6856f42b60159f0ab9055c027de13ed08fe847bc22200fef07f683cb41dc00def06f68308017fa0bed05f00288013da08420370018800bfa05ef02f68173c0a240420
|2=>0xc2f6e07b52bfa91ed42f6a07f503d261ed308018200c08460012cf79210083da23ff11d908bc8438020010d0c86708319618400bf68583c2bfa15f0
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x10000100
|6,0=>0xe005831e0060a
|7,0=>0x2013108d2522f0700548869980704934221bd012403324d0229488d4d855ca23c82480abe
|8,0=>0x29237328bbbb30ead3235208563624b35a7523a9a9d81ea2bebc67a7d8a399395987a5d8b45e7604f6ede595
|9,0=>0x5546e14b359327db3ad99d648fcf41
|10,0=>0x4768b1d
|11,0=>0x15
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 7 (j%128);fld (pmP (k/32)) 17 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_249 10 roots_249 ops++addP pm 1 dom_155 7 roots_155 ops++addP pm 2 dom_235 10 roots_235 ops++addP pm 3 dom_123 10 roots_123 ops++addP pm 4 dom_218 6 roots_218 ops++addP pm 5 dom_219 9 roots_219 ops++addP pm 6 dom_250 9 roots_250 ops++addP pm 7 dom_243 9 roots_243 ops++addP pm 8 dom_187 9 roots_187 ops++addP pm 9 dom_186 6 roots_186 ops++addP pm 10 dom_242 6 roots_242 ops++addP pm 11 dom_179 6 roots_179 ops++addP pm 12 dom_211 6 roots_211 ops++addP pm 13 dom_154 4 roots_154 ops++addP pm 14 dom_147 4 roots_147 ops++addP pm 15 dzo_235_16 9 roots_235 ops++addP pm 16 dom_171 8 roots_171 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_251 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_235_16_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_171 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_249 10 s (0,roots_249.map (·&&&dom_249)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_251 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_249 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
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
namespace S_253
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(1,129),(4,20),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(8,9),(8,40),(8,72),(8,136),(12,13),(12,28),(12,44),(12,76),(12,140),(16,20),(16,144),(17,21),(17,25),(17,49),(17,81),(17,145),(24,25),(24,28),(24,56),(24,88),(24,152),(32,33),(32,40),(32,96),(32,160),(36,37),(36,44),(36,52),(36,100),(36,164),(48,49),(48,52),(48,56),(48,112),(48,176),(64,65),(64,72),(64,96),(64,192),(68,69),(68,76),(68,84),(68,100),(68,196),(80,81),(80,84),(80,88),(80,112),(80,208),(128,129),(128,132),(128,136),(128,144),(128,160),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffffffffff
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
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]]
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
def isoMvS_223:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_223:Lower true dom_223 roots_223 goal_223 11:=lower_iso_b isoMvS_223 (by decide +kernel) lowS_191
def isoMvS_254:List (Nat×Nat):=[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_254:Lower true dom_254 roots_254 goal_254 11:=lower_iso_b isoMvS_254 (by decide +kernel) lowS_247
def dzo_157_2:=0xcccccccc000000000000000000000000cccccccc
def gzo_157_2:=0xccccccc8000000000000000000000000cccc8800
def gsh_157_2:=0x3333333200000000000000000000000033332200
theorem lowS_zo_157_2_141:Lower true dzo_157_2 roots_157 gzo_157_2 6:=lower_iso_b (d1:=dom_157) (r1:=roots_157) (T1:=gsh_157_2) [(dom_157,2)] (by decide +kernel) (lower_slice_b (T:=gsh_157_2) [(0x3333000000000000000000000000000033330000,0,16)] (by decide +kernel) lowS_141)
def dzo_111_16:=0xffff0000ffff0000ffff0000ffff0000
def gzo_111_16:=0xffff0000fffe0000fffe0000fefc0000
def gsh_111_16:=0xffff0000fffe0000fffe0000fefc
theorem lowS_zo_111_16_105:Lower true dzo_111_16 roots_111 gzo_111_16 9:=lower_iso_b (d1:=dom_111) (r1:=roots_111) (T1:=gsh_111_16) [(dom_111,16)] (by decide +kernel) (lower_slice_b (T:=gsh_111_16) [(0xcccc0000cccc0000cccc0000cccc,0,2),(0xf0f00000f0f00000f0f00000f0f0,0,4)] (by decide +kernel) lowS_105)
def dzo_253_2:=0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
def gzo_253_2:=0xccccccccccccccccccccccccccccccc8cccccccccccccccccccccccccccc8800
def gsh_253_2:=0x3333333333333333333333333333333233333333333333333333333333332200
theorem lowS_zo_253_2_141:Lower true dzo_253_2 roots_253 gzo_253_2 8:=lower_iso_b (d1:=dom_253) (r1:=roots_253) (T1:=gsh_253_2) [(dom_253,2)] (by decide +kernel) (lower_slice_b (T:=gsh_253_2) [(0x3333000033330000333300003333000033330000333300003333000033330000,0,16),(0x3333333300000000333333330000000033333333000000003333333300000000,0,32),(0x3333333333333333000000000000000033333333333333330000000000000000,0,64)] (by decide +kernel) lowS_141)
def dzo_221_2:=0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc
def gzo_221_2:=0xcccccccc00000000ccccccc800000000cccccccc00000000cccc8800
def gsh_221_2:=0x33333333000000003333333200000000333333330000000033332200
theorem lowS_zo_221_2_141:Lower true dzo_221_2 roots_221 gzo_221_2 7:=lower_iso_b (d1:=dom_221) (r1:=roots_221) (T1:=gsh_221_2) [(dom_221,2)] (by decide +kernel) (lower_slice_b (T:=gsh_221_2) [(0x33330000000000003333000000000000333300000000000033330000,0,16),(0x33333333000000000000000000000000333333330000000000000000,0,64)] (by decide +kernel) lowS_141)
def dzo_189_2:=0xcccccccccccccccc0000000000000000cccccccccccccccc
def gzo_189_2:=0xccccccccccccccc80000000000000000cccccccccccc8800
def gsh_189_2:=0x333333333333333200000000000000003333333333332200
theorem lowS_zo_189_2_141:Lower true dzo_189_2 roots_189 gzo_189_2 7:=lower_iso_b (d1:=dom_189) (r1:=roots_189) (T1:=gsh_189_2) [(dom_189,2)] (by decide +kernel) (lower_slice_b (T:=gsh_189_2) [(0x333300003333000000000000000000003333000033330000,0,16),(0x333333330000000000000000000000003333333300000000,0,32)] (by decide +kernel) lowS_141)
def dzo_109_16:=0x33330000333300003333000033330000
def gzo_109_16:=0x33330000333200003332000032300000
def gsh_109_16:=0x3333000033320000333200003230
theorem lowS_zo_109_16_105:Lower true dzo_109_16 roots_109 gzo_109_16 8:=lower_iso_b (d1:=dom_109) (r1:=roots_109) (T1:=gsh_109_16) [(dom_109,16)] (by decide +kernel) (lower_slice_b (T:=gsh_109_16) [(0x3030000030300000303000003030,0,4)] (by decide +kernel) lowS_105)
def dzo_239_16:=0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
def gzo_239_16:=0xffff0000ffff0000ffff0000ffff0000ffff0000fffe0000fffe0000fefc0000
def gsh_239_16:=0xffff0000ffff0000ffff0000ffff0000ffff0000fffe0000fffe0000fefc
theorem lowS_zo_239_16_105:Lower true dzo_239_16 roots_239 gzo_239_16 10:=lower_iso_b (d1:=dom_239) (r1:=roots_239) (T1:=gsh_239_16) [(dom_239,16)] (by decide +kernel) (lower_slice_b (T:=gsh_239_16) [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,0,2),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,0,4),(0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_105)
def dzo_237_16:=0x3333000033330000333300003333000033330000333300003333000033330000
def gzo_237_16:=0x3333000033330000333300003333000033330000333200003332000032300000
def gsh_237_16:=0x333300003333000033330000333300003333000033320000333200003230
theorem lowS_zo_237_16_105:Lower true dzo_237_16 roots_237 gzo_237_16 9:=lower_iso_b (d1:=dom_237) (r1:=roots_237) (T1:=gsh_237_16) [(dom_237,16)] (by decide +kernel) (lower_slice_b (T:=gsh_237_16) [(0x303000003030000030300000303000003030000030300000303000003030,0,4),(0x333300003333000033330000333300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_105)
def dzo_251_4:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def gzo_251_4:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0f0f0f0e0f0f0a000
def gsh_251_4:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0f0f0f0e0f0f0a00
theorem lowS_zo_251_4_107:Lower true dzo_251_4 roots_251 gzo_251_4 10:=lower_iso_b (d1:=dom_251) (r1:=roots_251) (T1:=gsh_251_4) [(dom_251,4)] (by decide +kernel) (lower_slice_b (T:=gsh_251_4) [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000,0,16),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_107)
def dzo_235_4:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0
def gzo_235_4:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0e00000f0e00000a000
def gsh_235_4:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0e00000f0e00000a00
theorem lowS_zo_235_4_107:Lower true dzo_235_4 roots_235 gzo_235_4 9:=lower_iso_b (d1:=dom_235) (r1:=roots_235) (T1:=gsh_235_4) [(dom_235,4)] (by decide +kernel) (lower_slice_b (T:=gsh_235_4) [(0xf0f00000f0f00000f0f00000f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_107)
def dzo_231_16:=0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000
def gzo_231_16:=0xff000000ff000000ff000000ff000000ff000000fe000000fe000000fc0000
def gsh_231_16:=0xff000000ff000000ff000000ff000000ff000000fe000000fe000000fc
theorem lowS_zo_231_16_97:Lower true dzo_231_16 roots_231 gzo_231_16 7:=lower_iso_b (d1:=dom_231) (r1:=roots_231) (T1:=gsh_231_16) [(dom_231,16)] (by decide +kernel) (lower_slice_b (T:=gsh_231_16) [(0xcc000000cc000000cc000000cc000000cc000000cc000000cc000000cc,0,2),(0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f0,0,4),(0xff000000ff000000ff000000ff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_97)
def dzo_207_16:=0xffff000000000000ffff000000000000ffff000000000000ffff0000
def gzo_207_16:=0xffff000000000000ffff000000000000fffe000000000000fefc0000
def gsh_207_16:=0xffff000000000000ffff000000000000fffe000000000000fefc
theorem lowS_zo_207_16_73:Lower true dzo_207_16 roots_207 gzo_207_16 7:=lower_iso_b (d1:=dom_207) (r1:=roots_207) (T1:=gsh_207_16) [(dom_207,16)] (by decide +kernel) (lower_slice_b (T:=gsh_207_16) [(0xcccc000000000000cccc000000000000cccc000000000000cccc,0,2),(0xf0f0000000000000f0f0000000000000f0f0000000000000f0f0,0,4),(0xffff000000000000ffff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_73)
def dzo_238_16:=0x5555000055550000555500005555000055550000555500005555000055550000
def gzo_238_16:=0x5555000055550000555500005555000055550000555400005554000054540000
def gsh_238_16:=0x555500005555000055550000555500005555000055540000555400005454
theorem lowS_zo_238_16_104:Lower true dzo_238_16 roots_238 gzo_238_16 7:=lower_iso_b (d1:=dom_238) (r1:=roots_238) (T1:=gsh_238_16) [(dom_238,16)] (by decide +kernel) (lower_slice_b (T:=gsh_238_16) [(0x444400004444000044440000444400004444000044440000444400004444,0,2),(0x505000005050000050500000505000005050000050500000505000005050,0,4),(0x555500005555000055550000555500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_104)
def dzo_175_16:=0xffff0000ffff00000000000000000000ffff0000ffff0000
def gzo_175_16:=0xffff0000ffff00000000000000000000fffe0000fefc0000
def gsh_175_16:=0xffff0000ffff00000000000000000000fffe0000fefc
theorem lowS_zo_175_16_41:Lower true dzo_175_16 roots_175 gzo_175_16 7:=lower_iso_b (d1:=dom_175) (r1:=roots_175) (T1:=gsh_175_16) [(dom_175,16)] (by decide +kernel) (lower_slice_b (T:=gsh_175_16) [(0xcccc0000cccc00000000000000000000cccc0000cccc,0,2),(0xf0f00000f0f000000000000000000000f0f00000f0f0,0,4),(0xffff0000ffff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_41)
namespace S_255
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(1,129),(2,18),(2,34),(2,66),(3,11),(3,19),(3,35),(3,67),(3,131),(4,20),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(6,22),(6,38),(6,70),(6,134),(7,15),(7,23),(7,39),(7,71),(7,135),(8,9),(8,40),(8,72),(8,136),(10,11),(10,26),(10,42),(10,74),(10,138),(12,13),(12,28),(12,44),(12,76),(12,140),(14,15),(14,30),(14,46),(14,78),(14,142),(16,18),(16,20),(16,144),(17,19),(17,21),(17,25),(17,49),(17,81),(17,145),(24,25),(24,26),(24,28),(24,56),(24,88),(24,152),(32,33),(32,34),(32,40),(32,96),(32,160),(36,37),(36,38),(36,44),(36,52),(36,100),(36,164),(48,49),(48,50),(48,52),(48,56),(48,112),(48,176),(64,65),(64,66),(64,72),(64,96),(64,192),(68,69),(68,70),(68,76),(68,84),(68,100),(68,196),(80,81),(80,82),(80,84),(80,88),(80,112),(80,208),(128,129),(128,132),(128,136),(128,144),(128,160),(128,192),(130,131),(130,134),(130,138),(130,146),(130,162),(130,194)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffffffffffffffffffff
def xsM:=roots_255.map (·&&&dom_255)
def gM:=goal_255&&&dom_255
def NN:Nat→Nat
|6=>8
|7=>167
|8=>511
|9=>479
|10=>188
|11=>47
|12=>9
|13=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x4b7aa4974f420bb3e60e19b28184340d95d0d68f
|7,0=>0x6688d6655262a68622c9605af5fb80582965731754d3d54cb4548e95385451db84e40b4d2654ae5f498bd48e6748dd74877645f7c458724577a44f46423d8406cf400483bbbe3b93a3b07339c7c38c32366c73590f33fbc33d8a33732333ce32c7c31b5a3106730db230c783091f305632fcd72ee132e71c2d15a2b8f32b2df29aae295522930c288d02884e282ef2807f27589272ba271c32654e2466623e972379b234b3230532143a1fb721f52c1eebb1ee281e94b1e8141cb521c3611b4ac1aa2619aad1991f192891921117c371795616ced15d4e159ed15885156c3150c51478e13cf1132a712fc912977125761234011aff10bf7109d50fe6d0fb220f74c0ef830de700bb8a0b2c20b21509d780956008f2808c53089c9087550822e074b805a9005a37034400284b0270d01eb801e2601aec0186b00bc5008e7003a1
|7,1=>0xe9a03e495fdcc36dafdacb389c0ad9c0186bc3cbb76c8b42d3b1278affd0ac6eda04499ffc69d9939bd749ad9a9847091df98e7968ca7b85981833ed82bbe80349801537e5e6796587815e7810575611718246ff7f6dae36b5c969ce369c5567c6f
|8,0=>0x181ee1814a17dff17b7a17ae817758174121737816d69164d5161a7161a6160f715fe715f8b15a66159781589c1586c157a91562c14f6c14eff1441a142831416c13b9112f0d12eee12561124111227d1225711ca211c2b11b9711483111cc1112c110ae10ee810eb910e1d10d71109c0104510fcbf0f1940eebc0edca0ea920e9990e8790e7100e4ff0e3950e1d50df0a0da2a0d76d0d5f50d0cb0cdf00c7ff0c5c30c4ea0c4b30c4af0c1dc0c1140aebf0a53009e43097c4095af09590092050916b08c4108b6108a86089870893f0802507f4707b7f0727306e85069ff065cc0658b05e6a05e3a05bcc05a37059ee058ea057d80554c052c6051f404e9e044fd042f60401c03cd203b0203a4c0395f02d5e02d390278e024ff024970230a020b901f6601dbf01bca01599013d100f9900d8d00ceb007df00710001f100113
|8,1=>0x33cbe33b4f33753336ef32db232aa532685323f3323c631c17317e8311a930f79305e8302e2301e22fefe2f4402f2fb2f2772eff62e7e22e13c2dee82d78d2d7492d1ac2cea92c3842c1b62be102bd3c2baf32b63a2b26d2b22a2af7e2a7fd2a7442a71e2a6012a4e32a35829cc72980629327292642904e28af228620284ba282bc2820f280122792b278b92725e27098266ea25d5625c41259a8259072508a24c0f24762246fd242bc24230240bd239a6236502363b2329e22ac7227932264c220e321eb021c5d21aea218d52188c20fd320cc2206be205af200281fbca1f8351f7701f2fd1ee841eda01e8071e6f21e3091e1fa1cc421c9971c6c61c0e21be0f1bc3b1b7401b6d11ab4b1aa211a9ce1a7a01a5551a3a81a28a1a0c119e1919cf61962718ff918eef18e381895f18836188221877b1873b18689183a1182b7
|8,2=>0x5b7985b4225b3805ab8e5a7cc5a2495a1e859f3659b07589f458901588dd587565845f5756c5743356f2156bcc563dd55a4d559c055906557665535654e60548e75473b53f7953d625396c538935370a535ee52c9d52c4d5272c51f0b51e6250f67508a450622501b64fac84f4ff4f39f4f0f44ec714e5fb4e4694dc724db214ce174cc424c6434c49f4c0bf4b5574b0714acf049fdf49f1349d8b49b78497084964849614494db4908c4881e480c547f2d47964473bd47361472c64708d46b92466e145bba44f9d44ab0446a7443df44032438644306e42c91428874282b427c3423f44212f4130240f5640e00402c43fc493fb933f8c73f3503e6c83e47d3e3e93e3ad3dff43daa63d2133d08e3cd713cc723b7263b2473a4ec3a28839c64399e739926398c138d1837f3537a70370343644635f71346f3340df33e2a33cf0
|8,3=>0xf83c4eb3c1d9326d757bd5b04d46c2d3489d0c96cd092c9f93c97cbc25d9beb51bc1f2bb0a9b6ed9b6ab5b69c7b48fdb485cb2d81b1a75b08d4b081fafc5ca9c41a8bc8a863fa5fd3a5118a4c45a2a7ba21119cd969b50f987ec983ca954d09517692d929270d90ac48fd408e3598dfaf8d18989ef489df587d4887ca685a848562b84a6084880837ef822fa8220581cb5816b880ecb7e63a7d4bc7c7bd7c2057bc737bbc27b8d37b00d795477829a7810576c6576bcb7684976461757c2741ce7352d7303071f3971c90715d9708ba703587021e7018a6f6156edf46d33f6c6846bfa26ba586b46c69edf69da969cae69c8467fb7675da66af3664b86610465e3f6561864ee164cb264c106417663f606376d6334962757625b66209d61ec661aab61849612dd611405fadf5f80a5ee755ea005e2515e22e5e1755bff5
|9,0=>0x19bbf194bd18e3318b5518ade18a5417b261766a1763a1762b1730516f80167c3165b9162611608215f35158a1153bb1516d1516b14d1a14c6514b12147451447214244141261388b1362212cd512c0b129e81253f120c511aab1199a1163a1140d113f4113e610f3110e4410d0810cd910ad110828102761022f0fdb80fbe10f7f70f56c0f3bb0ed980ed3d0e97c0ddc70d9d60d8a60d54a0d5100d1380cd090cb790c9ce0c6350c58a0c49a0c2040bafe0b7ce0b78e0b09d0b0540b0400aebf0ad2b0abf70abcd0a74e09f8b09e1e0976e09603094e40949708f4408f1308b1c089960896208605085c40821107eb20791f0736e0728f06db906b9004d0304c9704b6904a4a04a3d049fe048f80461103930033db032690311202f77029870269d024140210b01f1e01de701cd8014f0013ed013d700e8d00b7d00a4b0080d
|9,1=>0x337f83370b335ef334b132ee232d4f3264932507324b83221431c5f31c2a31b003186a31818318173139c312ed30eb030cf030aed304e32fda02fb762f8302ee8a2e9492e2a22d7bc2d7962d4b42d3872d0a12cf0c2ce312ce232cc572c2802c00d2be7f2bbaf2b9902aeca2a9312a8682989929849297d829744292b6292aa28cb9285ff285952839828314281f227c8727b08278ab2781f277e7277d826fde266b3265e325d77259cf254c72522a2494d2482f24225241a02410b2404b23de423650231c922afa22ac7227e8227702229f218502152e214fe2143f204481ff481fed91fd911fcd71fc361fbc11f6091f2571e8821e3501e2c01e0c01dbc31d17d1d11b1cfcc1ccae1c8731c6521c3af1c0711c0521bf7c1bb221b8aa1b85d1b7571b5b61b32f1b1c21abc31ab021aa601a8961a7031a3a81a2fd1a2f819cc6
|9,2=>0x6aac16a3356979368fb768b43688be6807d658ca6565a6538e63d7d62b46620f061d556147d6072060695605755f4ca5f1b05ea2a5e9e65e9245e87e5e2ff5df985db575d5a25c1bf5b2fb5ad265a5f95a55a5906458c5f580a257e4c572ea56de255f6155986543dc5403253dc353c4853b7753959534cb53441532d9528f45288050ff350c13502795026e4fea54fe154f2134dd934dab74d2d34d06a4bdfc4bd874bcac4b98b4b2704a6b84975b491bf48c32487574857d4856d481b64811446d404634c461254607845e5e45d0945cdf45b3b447214409043b574368e4133f40e2b40da440d3b407203fe263f8843f6d53e0923da9b3d9603c9393c82e3c7de3bd9a3bc963b9823b65a3b31e3adb739e8b399263973e38b243814f380bd37ebe374863740b36cb5367cb3638635ec8347a03410c3406b33ff133dcb339f3
|9,3=>0xf6527eef3ce098cde311db52cd944bd7b71cff9acfec5cf629cecd3cd092c6aaac36c1c3520c2f9cc0f28bf0fcbd3bbbcf44bbaeebb274b9a03b86aab814cb4c6ab4970afda3ac872ab5dca9741a34cea300da2504a1753a1633a132aa1240a05d59e96a9e8099cd6b9b79f9974e97043969d595f81946a592c30921f89057f8fca68f3568d5fd8bba38b93a8a28b8911788c7d8898f881a88766686a9c84d9384730842888235f80bfc80a5c7e9a37d9357ce137a96678ced77b167775376e5c74fc17461e73d4d72d1572b3271b30719c9714956eef26e6536e4506e1846d6196d42a6c2816c2586c0036ba4e
|10,0=>0x5873a572d15714655c7c534c8522ef521ec511af50c654f7d04dd454dcef4c3f14a3f74705446f4546adf461c345a9f449f644468443054334941c5d411f63e3963c4fb3a11839e92397a938903382cb37a42363c835dc73574734e2632f5132286315d53114e2fb0b2eed72ec272eadd2e63d2dbcf2c5082ba5229b092949d28c2e278c827634275c62740e2544222f5122cae2200d21f9320e2c2072b2035b1f91d1f8001f7f61eff41e7a91e4861dc651d7911d4201d3531bed11bb5d1b6da1b11e1a5731a3b51a208199ef194a41946c18bb118134177bd174ea16b7b15cd514dc71377012d011223e1034e0fbad0fb3a0ed170e8920db5e0d9400d2920c88b0bfed0bf670b4320869307d7b07ab50790f07206067c905f8005d32058c60546503d7003ba203a9a03885028f3028b3027190266d0265401ff900e2000878
|10,1=>0xf26dff0e50daf70d3381d2d37c93aabec7ebbaefb586db1dcaaef35ad8c3a810aa6829a5c5da3fe4a3d0d9c9529b8129b37e9977098d65988e095c368f7198f4ad8c5be8bfc18bb7289516893178906c86e92868b083b4a8384c7e6237ab8e79eea79eba750877460f73746725c07212a711fc6e6786c64b672ca6658764224632cb61a8d61a5e6118a607f9600c85ef735cf2358fdc
|11,0=>0xe8b3de6de6e3c11df1abcfa0dcf97cb34e5ac34597b9c8b27288dc58714c85499767f86e56e5e4dc5e3dd5d93e5997d58c2f5365d50f2450cfe50bf850a9f4c55345f5142cf836ac7367e235ccc2a1bc214fe211461e3c01d2801a8bb19c4c1931911d8f089aa0648604ee4045b003c6101c3201913
|12,0=>0xd709bc9f4ea0cfc9736a8f4ad7ec636450412dcb11ebd
|13,0=>0x4766c
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffffffffffffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaaffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffffffffffffffaaffaaffaaffaaffffffffffffffffffaaffaaffaaffaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ffffffffffffffffffffffffffffffffccccccccccccccccccccccccccccccccffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaa00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00000000
|0,1=>0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffffffffffffffffffffffffffffffff00ff00ffffffffff00ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00aa00aa00ff00ff00aa00aa0055005500550055005500550055005500550055005500550055005500000000000000000000000000ff00ff00ff00ff000000000000000000ff00ff00aa00aa0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000aa00aa5555555555555555555555555555555555555555555555555555555500000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffaaffaaffffffffffaaffaaffffffffffaaffaaffffffffffaaffaaffffffffffffffffffffffffffffffffffffffffffffffffff00ff00ff00ff00ffffffffffffffffffffffff00000000ffffffffffffffffffffffff0000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00aa00aa00aa00aaffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa5555555555555555555555555555555555555555555555555500550055005500ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
|0,2=>0x5555555555555555555555555555555555555555550055005555555555005500ffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff00000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000f0f00000f0f0000ffffffffffffffffffffffffffffffffffffffffffffffffffaaffaaffaaffaaffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ff0055555555555555555555555555555555550055005500550055005500550055000000000000000000555555555555555500000000000000005555555555005500ffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa555555555555555555555555555555555555555555555555555555555500550000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000ffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00aa0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00aa00aaffffffffffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaffffffffffffffffffffffffaaaaaaaaffffffffffffffffffffffffaaaaaaaaffffffffffffffffffffffffffffffffffffffffffaaffaaffffffffffaaffaa
|0,3=>0xffffffffffffffff0000000000000000ffffffffaaaaaaaa00000000ffffffff00000000ffffffff00000000ffffffff00000000aaaaaaaaffffffffffffffff5555555555555555ffffffffffffffff555555555500550000000000ffffffff00000000ffffffff00000000ffffffff00000000ff00ff00ff55ff55ff55ff55ff55ff55ff55ff55ff55ff55ff55ff55ff55ff55ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00aa00aa005555555555555555555555555555555555555555000000005555555500000000ffffffffffffffffffffffffffffffffffaaffaaffaaffaaffaaffaaffaaffaa00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00cc00cc00ff00ff00cc00ccaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaeeaaeeaaffaaffaaeeaaee0000000000000000ffffffffffffffff0000000000000000eeeeeeeeeeeeeeeeffffffffffffffffffffffffff00ff00ffffffffffffffffffffffffff00ff000000000000000000ff55ff55ff55ff550000000000000000ff55ff55ff44ff440000000055555555000000005555555500000000555555550000000055005500ffffffffffffffffffffffffffffffffffffffffccccccccffffffffcccccccc0055005500550055005500550055005500550055005500550044004400440044
|0,4=>0xffffffffffffffff0000000000000000ffccffccffccffccffffffffffffffffffffffffffffffffffffffffffeeffeeffffffffffeeffee0000000000000000ffffffffffffffff0000000000000000ffffffffffeeffee555555555555555555555555555555555555555555555555000000000000000000550055005500550055005500550055005500550044004400550055004400440000000000000000005500550055005500000000000000000055005500440044ff55ff55ff55ff55ff55ff55ff55ff55ff55ff55ff44ff44ff55ff55ff44ff44aaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaeeaaeeaaeeaaeeffffffffffffffffffffffffffffffffffffffffffffffffccccccccccccccccff55ff55ff55ff55ff55ff55ff55ff55ff55ff55ff55ff55ff44ff44ff44ff44ffffffff55555555ffffffff55555555ffffffff55555555ffffffff5500550000ff00ff0055005500ff00ff0055005500ff00ff0055005500ff00ff00000000aaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaaaaaaaff00ff00ff55ff55ff00ff00ff55ff55ff00ff00ff55ff55ff00ff00ff44ff44555555555555555555555555555555555555555555555555444444444444444400ff00ff00ff00ff00ff00ff00ff00ff00aa00aa00aa00aa00aa00aa00aa00aa
|0,5=>0xaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaaaaaaaaaffaaffaaaaaaaaffffffff00ff00ffffffffff00ff00ffffffffff00aa00aaffffffff00aa00aa0000000000000000ffffffffffffffff0000000000000000ffffffffccccccccffffffffff55ff55ffffffffff55ff55ffffffffff55ff55ffffffffff00ff00ffffffffffffffff0000000000000000ffffffffffeeffee0000000000000000ffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00aa00aa5555555500550055555555550055005555555555005500555555555500000000ffffffff55555555ffffffff55555555ffffffff55555555ffffffff0000000000000000ffffffff00000000ffaaffaa00000000ffffffff00000000ffaaffaa0000000000000000ffffffffffaaffaa0000000000000000ffffffffffaaffaa0000000000000000ffffffffffffffff0000000000000000ffffffffff00ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00ff00000000ffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff000000005555555555555555005500550055005555555555555555550055005500000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffaaffaaffffffffffffffffffffffffffffffffffccffccffccffccffccffccffccffcc
|0,6=>0xaaaaaaaaaaaaaaaaaaffaaffaaffaaffaaaaaaaaaaaaaaaaaaffaaffaaeeaaee5555555555555555555555555555555555555555444444445555555544444444ffffffffaaffaaffffffffffaaffaaffffffffffaaffaaffffffffffaaeeaaee3333333333333333333333333333332233333333333333333333333333333322ffffffff00550055ffffffff00550055ffffffff00550055ffffffff0044004400000000ffffffff00000000ffffffff00000000ffffffff000000000000000000ff00ff00ff00ff00ff00ff00aa00aa00ff00ff00ff00ff00ff00ff00aa00aaff55ff55ff55ff55ff55ff55ff55ff55ff55ff55ff55ff55ff00ff00ff00ff005555555555555555555555555500550055555555555555555555555555005500ffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00aa00aaffffffffffffffffffffffffffffffffffffffffffffffffffeeffeeffeeffee00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ee00ee00ee00eeffffffffffffffffffffffffffaaffaaffffffffffffffffffffffffffaaffaa0000000055555555000000005555555500000000555555550000000044444444ffffffffffffffffffffffffffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee000000000000000000ff00ff00ff00ff000000000000000000ee00ee00ee00ee
|0,7=>0xffffffffffffffffffffffffffffffff33333333332233223333333333223322ff55ff55ff55ff55ff55ff55ff55ff55ff55ff55ff00ff00ff55ff55ff00ff00ffffffffffffffffffffffffffffffffffffffffffffffffffffffffcccccccc005500550055005500550055005500550055005500550055005500550044004400ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00cc00cc00cc00cc00000000555555550000000055555555000000005555555500000000000000000000000000000000ffffffffffffffff0000000000000000ffeeffeeffeeffeeffffffff55555555ffffffff55555555ffffffff55005500ffffffff550055000000000000000000ffffffffffffffff0000000000000000ffffffff0000000000000000aaffaaff00000000aaffaaff00000000aaffaaff00000000aaeeaaeeff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ff00ff00ffffffffffffffffffffffffffffffffffeeffeeffeeffeeffeeffeeffeeffee33331111333311113333111133331100333311113333111133331111333311005555555555555555555555555555555555445544554455445544554455445544ffffffffffffffff5555555555555555ffffffffffffffff55555555000000005555555555555555005500550055005555555555555555550055005500440044
|0,8=>0xffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffffffffff00ff00ff00ff00aaffffffffffffffff00ff00ff00ff00aaaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffaaffaaffffffffffffffffffffffffffffaaaaffffffffffffffffffffffffffffaaaa3333333333333333333333333333222233333333333333333333333333332222ffffffffffffffffffffffff00ff00ffffffffffffffffffffffffff00aa00aa0000000000000000ff55ff55ff55ff550000000000000000ff55ff55ff00ff00555555555555555555555555555555555555555555555555555555554444444400000000ffffffff00000000ffffffff00000000ffccffcc00000000ffccffcc00ff00ff00ff00ff00ff00ff00ff00ff00ee00ee00ee00ee00ee00ee00ee00eeffffffff00ff00ffffffffff00ff00ffffffffff00ee00eeffffffff00ee00ee000000000000000000ff00ff00ff00ff000000000000000000ff00ff00000000aaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaeeaaee000000000055005500000000005500550000000000550055000000000044004400550055005500550055005500550055005500550055005500000000000000000000000000000000000000000000000033333333332233223333333333223322
|0,9=>0x555555555555555555555555555555555555555555555555554455445544554400000000555555550000000055555555000000005544554400000000554455440000ffff0000ffff0000ffaa0000ffaa0000ffff0000ffff0000ffaa0000ffaaf0f0fffff0f0fffff0f0fffaf0f0fffaf0f0fffff0f0fffff0f0fffaf0f0fffaff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ffffffffff00ff00ffaaffaaffaaffaaffffffffffffffffffaaffaaffaaffaaffffffffffaaffaa0000000000000000ffffffffffffffff0000000000000000ff00ff00ff00ff00ffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00000000ffffffffffffffffaaffaaffaaffaaffffffffffffffffffaaffaaffaaaaaaaaffffffffffffffffffffffffffffffaaffffffffffffffffffffffffffffffaaffff0000ffff0000ffffffffffffffaaffff0000ffff0000ffffffffffffffaaaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaa00ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff00ff00ff00ff00ff0000ffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffff0000aaffaaffaaffaaffaaffaaffaaffaaaaaaffaaffaaffaaffaaffaaffaaffaaaa00ff00ff00ff00aa00ff00ff00ff00aa00ff00ff00ff00aa00ff00ff00ff00aa
|0,10=>0xffffffffffffffffffffffffffffffff55555555555555555555555555005500ffffffffffffffff0055005500550055ffffffffffffffff0055005500000000000000000000000000ff00ff00ff00aa000000000000000000ff00ff00ff00aaffffffffffffffffffffffff55555555ffffffffffffffffffffffff55005500ffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff00000000000000000000005500550055005500000000000000000055005500000000ffffffffffffffffffffffffffffffff0000000000000000ffffffffffaaffaa00000000ffffffff00000000ffffffff00000000ffffffff00000000cccccccc0055005500550055005500550055005500550055000000000055005500000000ffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa00000000ffffffff00000000ffffaaaa00000000ffffffff00000000ffffaaaaffffffffffffffffffffaaaaffffaaaaffffffffffffffffffffaaaaffffaaaaff00ff00ffffffffff00ff00ffffffaaff00ff00ffffffffff00ff00ffffffaa55005500555555555500550055555555550055005555555555005500550055003333333333333333333333333333000033333333333333333333333333330000ffffffffffffffffffffffffffffffffffffffffffffffffffccffccffccffcc
|0,11=>0xffffffffffffffffffffffffffffffffffffffffeeeeeeeeffffffffeeeeeeeeaaaaaaaaaaaaaaaaaaffaaffaaffaaffaaaaaaaaaaaaaaaaaaffaaffaaaaaaaaffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff000055005500550055005500550055000000550055005500550055005500550000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff00000000ffff0000ffff0000ffff0000ff000000ffff0000ffff0000ffff0000ff00f0f0fffff0f0fffff0f0fffff0f0fff0f0f0fffff0f0fffff0f0fffff0f0fff00000000000000000ffffffff555555550000000000000000ffffffff55005500ffffffffffffffff5555555555555555ffffffffffffffff5555555544444444ffffffffffffffffffffffaaffffffaaffffffffffffffffffffffaaffffffaa00000000ffffffff00000000ffffffaa00000000ffffffff00000000ffffffaaffffffffaaffaaffffffffffaaffaaffffffffffaaffaaffffffffffaaaaaaaaaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaaaaaaaaaaaaaaa00ff00ff00ff00ff00ff00ff00ff00aa00ff00ff00ff00ff00ff00ff00ff00aa0000000000000000ffffffffffffffff0000000000000000ffffffffffaaffaaffff00ffffff00ffffff00ffffff00aaffff00ffffff00ffffff00ffffff00aa
|0,12=>0xffffffffffffff00ffffffffffffff00ffffffffffffff00ffffffffffffff0000000000000000000000000000000000ffffffffffffffffffffffffaaaaaaaaffffffffffffffffffffff00ffffff00ffffffffffffffffffffff00ffffff005555555555555555555555005555550055555555555555555555550055555500ffffffffffffffaaffffffffffffffaaffffffffffffffaaffffffffffffffaaffffffffffffffffffffffffffffff00ffffffffffffffffffffffffffffff000000ffff0000ffff0000ffff0000aaaa0000ffff0000ffff0000ffff0000aaaa0000ffff0000ffaa0000ffff0000ffaa0000ffff0000ffaa0000ffff0000ffaaffffffff00000000ffffffffffffffffffffffff00000000ffffffffff00ff00000000000000000000000000ffffffff000000000000000000000000ff00ff00ffffffaaffffffaaffffffaaffffffaaffffffaaffffffaaffffffaaffffffaa00000000000000000000000000000000ffffffffffffffffffaaffaaffaaffaa00000000ffffffff00000000ffffffff00000000aaaaaaaa00000000aaaaaaaa
|_,_=>0
def sP:Nat→Nat
|0=>0xa090805180302120a0515030f251910080c0503020d231b0a090e0515030f120c05030224001710210c05030f1b1c0b080c051f030f121c0a08050302120d001e1405030f0d1d170608050403021c080503020d1b1a0605040302190016140515030201140e05030f11130a0805030212110a09080507030206050403020100
|1=>0x1716080504030f010b0a1405070f0d2d0b0614052c030f130b2b06052803021710080c0504030f192a0a210515030f250c0515030f291c0b20140e050403020d06080518030213101e0914050403020d160c051503020110060e0515030f13100a140515030f25110a0e0504030f25190e0c051803022710091405030f0d1d26
|2=>0x1706080518030227100a0e050403020d190c05331803020d172b05030f1c32100b0a0805030f121d0b090c051f030f1c100a090503020d0010060e051803021c1031140518030d300b0a051503020d1910060e0504030f0113060e0504030f2f1709080c05071803021e220c050403020d0a05030f1219000b2b0c0528030212
|3=>0x2060805041f030f010a0515030f3911100a0e050302121d100a080538030f12171614051803020117080c0518030212110c051803023612170c051803350211170a1405030f2511170c0504030f251c170a0805030f121c0b0a090805280302100a05030f25190010340605180302011706142e050718030216140515030f25
|4=>0x30217200e0c05040302121e090c05040302121e140e05280302120a0503020d190010201405030f0d1d171614051f030f01340605180f122d0b200c0504030f2f171e140528030f2f170a080e0507030f251e060e0507030f1709140504030f2f0b0a142e052803021234090e051f030f120a090507030f17210c2e05280403
|5=>0x40f2d0b34090528030f170a08052c03020d100a05030f391117100a080503020d1c100c0503020d231b17340c052803020117140e052815030f01080c053a0302191022080c05280403021608051f030f01100a0905030f1c100b1e140e0528030f01220c050403020d000a140503020d11170a0605070f2d100b0608050718
|6=>0x53b18030210160c051503021217220c0504030f1c0b2b220c05280302101e0c05030f1225001e0605030f250010340605280f2d100b1e060805180302120c0504030f192a17080518030f29320b0a090515030f121e09140507030f0b0a080528030212171e0605030f12000b060805071f030f0a080e050703020d06140528
|7=>0x5421803020d103f08051803020d3e140518030d41370b06080518030212001e080c0528030212060805041f030f190c05030f2f1d17100a220e050403020d0805180302273c100a210538030f170605030f004017103f05030f0d233e0b060e051803023d100c0518030212271705030f27003c100b0a05180302121917060e
|8=>0x2544100a080504030f2519080c0518030227100608053804030f0c0515030f12440b160c2e05040302120c053b030f43100b080503020d003c10140518030f3911170c05030f2723100b0a08050703020d0a090e05040302123f0518030f193e0b0e0503020d233e100a210528030217220c051f030f1c101e140528030f010e
|9=>0x7030f17060504030f01000b060805071f030f170c051803020d4a171e210e0528030f171405491803470d0b0a062e05040302120c0504030f43190b140e05180302480d060805280403020a14054603020d0b140c052815030201080c05040302430d0608051f030f13100e05180302193e100a0e05030f1225000c0515030f
|10=>0xf0d2d0b340e0538030f0d100a060515030f12170b340e0528030f120b160e05040302120a0605040f122d0b2b0518030f29320b1405030f2f1d100b14051803020d4b170a2208050403020d2b0605030f12000b2105030f0d1b1a0b220c05041f030f191e220c05280302100a212e050403020d0c051f030f4319101e090c05
|11=>0xb160c2e0504030f120b340e05180302120d080c05041f030f0d190e0c053a03020d1006140518030f13170b4d160c051803020d0b140e051803020d1d101e0c0504030f0d4c31140528180302120b0a210504030f250b2b0e0c0528030f120b0c05151803022717101e0c0518030f2519100c051f030f0d231710210c050418
|12=>0x30f010d0a22051f030f010d101e140e05180347020d0a0e050703020d10220e051803020d3e100c054f180302010d17090e0c051518030f12060e051f030f0d00100a08051f030f010d100a0515030f0d391710080e051803020d3e10080c05281503020d102b0e0c05180302120d080c05180302120d000a1405180f120d2d
|13=>0x17100e0c051f030f120d00510e0c051803020d100a060515030f251710340e0528030f25100a22090504030f0d0b0c055003020d131710080e0c05280403020d1e0c0507030f0d170c0518030f431c100b0a09080504030f0d0b0c05041f030f0d3e060805041f030f0d172b0e0c0503020d00100e0c051803022710340e0518
|14=>0xc0518030f27100b0a0c0515030f122517080c0518030f252f100c051f030f255710080c0518030f27100b140c051518030f25112b0c05030f2400100b560e051803020d100a220518030f19100b550518030f0d3c0b2b0e0c0528030f251006080e05281f030f10060518030f5352100b3406051f030f0d170a0e05030f0d1d
|15=>0x51803020117101e080c050403020d060518030f1900100b0c0518030f011c100b0a0e052c030f0d17101614051f030f0d17550c051803020d17140e052818030f011709140e0518030212080e0c05281f030f120c0518030f1253520b210c051518030f25090c0528030f23100b580c05041f030f0d201e140518030f0d1722
|16=>0x51803020d0a21050403020d0b2b080c0518030224100a090e050403020d10140c0507180f0d2d0b09140518030f121d0b080c0504030f0d130b0c051803020d5b0b1e0c051803020d19101e060518030f01100c0518030f0159100b0a0c052c030f11100b140e05280403020d140518030f1225540c052c18030f27100b0a06
|17=>0x4180302120c0518030f255352100a090518030f1217550c051518030f270b1608051f030f0d17105c0c05030f0d44100b0e0518030f193e100b060e053804030f101e090c0504030f0d17220c0504030f0d130b0608050418030f250614052c18030f0b0a140507030f250b210e052818030f173f0c05180302010d173f080c
|18=>0x1803020d170e0c053804030f12080c0518030f121d0b060518030f1200170b140c052815030f010b060c051f030f011310210c0518030f401755080c05030f0d000b1e05030f0d003c100b0a220504030f0d0b080c0504030f430d0b090c05041f030f1206080e0518030219100614053818030f17140e05281f030f12060e05
|19=>0x101e0c0518030f2f104c220c05030f231c100b140c0515180302010d16080518030f120b0e0c05041803020d190a080e0518030f12251e060e0518030f12170a14052c15030f0d0b0608052c18030f100b0a1405280f0d2d100b06080518030f1c100b340e052803020d10140c052815030f110b160c0504030f25175d0c0515
|20=>0x51803020d60170a080504030f0d190b060e051f18030f19100c0518030f25190010160c2e050403020d1006080e050718030f0b210c052815030f0b090e0c052815030f10140518030f5f0d170914051518030f0d080e0c0518030212195e0c0518030f12170a210515030f0d170b310c05071803020d172b0e0c052803020d
|21=>0x30f25100c051503020d0017100c0518030d4137100b140518030f121d0b1e140e0504030f250d14051803020d4b100b060518030f250017100a0605180f122d100b630e0518030f0d17140c0518030f251117080e0c0504030f0d2a0a0c05150302120d17080c051803020d2f100e051803020d62100608053818030f17100c
|22=>0xf122500170e051803020d6710090c0528030f66100b060805041803020d140518030f010d540c050703020d64100b0a14050703020d0b0e0c05180302121d100a0e05030f120d000b213f0c05030f0d230b3f0c0518030f190b16080518030f251006142e052818030210080c053818030f12170608052804030f0b0a21051f
|23=>0x30f120b090e0c05071f030f10340c05030f271c100b0c0568030f0d44100b0a580504030f0d0b0a0908051f030f0d10140e0504030f0d2a080c053804030f0d2b060518030f2510080c0518030f251c100c05180f0d2d57100b220c05030f0d23100b0a0605280f2d100b160e0518030212101e0c0518030f27100b0c051803
|24=>0x1226450c0518030f01100b6b0c051803020d100b0c05030f010d231b0b0608051f18030f12080c050403020d000a080e05180302120d0a0c052803020117100c05030f2400100b2b0c05030f430d100b0a1405040f0d2d0b0c053818030f126a0c05180f0d2d69100b550c0518030f27170b0a2209051f030f0d100a080e0528
|25=>0x12170e0c052c18030f1110080c052804030f250c05041803020d6e176d0c051803020d100b0a062e0504030f120b0c0528030f123c0b1e09140518030f120b0a080504030f250d170a14052c030f0d170b0c051803020d1900100c0518030d6c100b060e0528040302101e0c0528030f01100a090528030f1710060e0518030f
|26=>0x10140e0518030f010d130a0905030f0d1d1710080c0518030224100614053804030f0b140e0518030f0d2f170e0c05280403021214051803020d3c170a090504030f120b1e060e0528030f1710220c0528030f1d100b1e060e0518036102100c051f030f0d6717060c0507180f2d100b0c051803026f0d100b201e0c0518030f
|27=>0xc051f030f430d100a06052c15030f100b0a0e05030f0d11100c0528030f253c100c05030f25231c100b140e0528180347020d0c05041f030f0d710c05180302120d00171e0e0c0528030f12172b060528030f100b1e210e0518030f0d170a060528034702100b220c051f030f0d13100c051803020d70100b1608051803020d
|28=>0xf0d23100b0c0518030f5f12170c0518030f2717100b0a0e0503020d72100e0c051f030f0d1c1034060538030f100b0a0c05280f122d100b080c05281803021217080e0c05071803020d060e0518030f27100b140e051803020d41080c052c1803020d100c0518030f39111710080c051803020d1c10060c0515180302011008
|29=>0x5180302120c0528180302126a140e05071803020d0c0518030d73100b213f0c0518030f190b0a090e0507030f100b2b0c0528030f251034060518030f010b340c051f030f010d170a0605070302100b1e140e0518030f0d4c080c05280403020d22080c05041f030f0d0608050418030f010b5a0c0504030f0d170b1e0c0503
|30=>0x22710210518030f2554100a062e050403020d1016140518030f010b06080e0518030f401020140e051803020d10223f0c05030f0d230b210e0518030f0d260c053b18030f01100b0614051518030f25173f080c05030f0d230b080e0c053a03020d100a060504030f25172b0c051803022417105d0c05281803020d1706142e
|31=>0xb0c0504030f010d230b09140e052804030f0b55080518030f0d3c0b200c0504030f0d17140e052c18030f0d171e220c0528030f100b1e140528030f0d17061405280403020b0a06052c030f17100b0a0e0507030f0d17080c0518030f192a100c057418030212170c0504030f430d170b0a212e0504030f0d0b080e0c051803
|32=>0x9051f030f12100c052815030201101e080c0504030f250d0c0518030f121c170b09140e05041803020d0c051803021211170e0c05180302430d101e0c0504030f0d2f171e220c051803020d10060518030f001c100b0c057518030f1225140518030f0d3926080c0518030f27290b16080518030f01100b140c052c18030f11
|33=>0x528030f100b78140518030f0d170a0c054603020d100b0e0c053a030f19100b340605280302100b0c0504030f010d000b080c05071f030f0d1716770518030f25101405180302360d100b0c051803020d76100b060e052818034702100a080e050403020d1e060518030f12172b060518030f27100b2b060518030f01100b0a
|34=>0xd100a142e0507030f0d0b31140518030d410b080c052804030f010b340c05030f2700100b0a22080504030f0d0b1e1405030f0d1d100b450c051518030f120b34090e051803020d102b0c05030f2700100b0614051f18030f01311405281803470d0b0e0c051803020d2710080c0504030f0d2a223f080c051803020d34090e
|35=>0xc05180302480d10210c2e0528180302105a0c051f030f0d17100c05041f030f0d7a0e0c05030f0d0040100c050403020d00170c052875030f120b080c0504180302010d0c053a030f0119100b510c0518030f27100b0c0518030f25001c100c0579071803020d0b220c052804030f010b16080e0504030f0d0b630e051f030f
|36=>0x18030f0d131677051803020d100c0574040302120b220e0c0503020d23100c051f030f0d5717450c051518030f25101e140e0507030f0d0b080c051803020d2310140c052815030f2517090c05071f030f100e0518030f2732100b2b080c051803022710220c0528030f23100b06080504030f0d000b2b0c0518030f2527100e
|37=>0x100b630c2e051803020d10220c051803020d00100c051803020d1c17100c051f030f430d17100e0518030f0d671714057e04030f0d0b0a0c052c03020d17101e140518030f010d170e0c0518030f121d17140c05281803020117223f0c0518030f190b0c053b030f0d00100b0c051803020d7c100b0c052875030f2510140e05
|38=>0x60e052804030f17220c05041f030f0d1778140504030f0d0b22080c0528180302100c051803020d7f10080c053b1803020d101e0c0528030f12170c051f030f010d2310080c05030f2400100b0c050418030f01190b0c05491803470d100b080c0504030f250d000e0c0528030f011310060c05071f030f17060e0504030f2f
|39=>0xc05281f030f01102b0608051803020d10340518030f2732100b2b0518030f2732100b630c051803020d170e0c0504030f252f100c05030f011923100b2b06080528030f100b0a21051f030f0d17140e0518030f0d810614052c1518030f0b140c05281f030f01067705281f030f10160c0515030f120b1e0c0504030f0d190b
|40=>0x100b06142e05041803020d2b080c0528030f251051080c051803020d1006142e052804030f0b2b080c0503020d0010080c0518030227102b0c05030f250d00100608051f030f0d001009080c05041803020d200c05030f0d66100b22090c052804030f0b09080c052804030f0b220c05281f030f01101e0c05030f121d100b08
|41=>0xc050418030f190b0a220e0528030f100b060e050418030f011734062e051803020d100c051f18030f0119100a220504030f0d170b34062e0528030f100b1e09140518030f0d170a08050403020d2b060518030f19100b080c05180302011910450c051803020d1710160e0504030f120b0914052804030f0b220c0518030f1c
|42=>0xf271c100b630c051f030f25100c051803020d4b17100c05030f2f1d100b160e0518030f0117101e0e0c050703020d102b060518030f251710560c2e051803020d100c051803470d4b100b0c051803020d82100b2b0c0518030f25191016142e051803020d100c05791803020d170c052815030212170a220e051803020d1009
|43=>0x212060518030f250010060c2e052804030210061405041f030f25630c05180f0d2d100b060518030f12000b0c2e051803020d671006080518030f27100b090c051518030f121706770518030f4010210c0528180f2d100b0c05180302830d100b311405071803020d0b201e0c0504030f0d17160c0515030f01100b1e0c0503
|44=>0x2b220c0528030f100b0c051f030f2700100b0c0518030f27100b213f0518030f0d3e0b0a0c0515030f12110b4d0c051803020d0b1614051f030f25102b06052c18030f100b1e090c0504030f120b0e0c0515030f0d131020140518030f0d171e090c0528030f1710080c0518030f2527101405041803020d6e0b0c2e05280403
|45=>0xf0d100b0c05651803020d100b0c0518030f0d661d100b0c052875030f0d100b140c051f18030f010d0677051f18030f0d10080c05180302120d17060518030f0d84100b0a06051f030f0d17100a0605040302120b2b550518030f0d3c0b0a06052c030f100b080c05071803020d172b220c051803020d100614051518030f25
|46=>0xd0b060e0518030f40102b1e0c0518030f27100b210c050418030f250b140c05281f030f251020220c0518030f0d100b060c051518030f12170b630c0518030f0d170b2b0c051803020d1710850c051803020d100b0e0518030f250d3e10220e0c051f18030f0d100c051803020d62100b210c05030f0d23100b20080c051803
|47=>0x10d100c05180302360d100b0e0c05071803020d100c05180302120d6a0c051f030f0d001710080c053a030f0d100b080c051f18030f010d105a0c0518030f0d100b1e0e0c0518030f0d104c0a140518030f12250b0a080528030f0d100b0a0c051f030f120d170c051803020d80100b2b06080518030f0d100b0a140507030f
|48=>0x100b22090c050418030f0d0b140c0504030f0d2a0b22080518030f0d3e100b060e05501803020d1020140518030f0d100b160c0518030212100b09080c050418030f0d0b1e1405041f030f0d0b060c2e0518030212100e051803020d8710220c053a030f0d100b0c051803020d67100b0c05740403020d100b220c051f18030f
|49=>0xc0518030d8b100b160c0518030f01100b1e140518030f0d2f100b1e0e0c05030f0d00100b220e0c0518030f19100b0c05041f030f0d4c0e0c0518030f0d1d17108a0c0518030f0d100b0c058918030f0d100b060c051518030f2517102b080c05030f0d00100b0c0518030f0d32100b080c0518030f27100b0c051803020d88
|50=>0x30f910d100b060c0518030f12260b0c05030f01250d23100b51220c0518030f0d100b06140518030f01170b2b0c051f18030f27100b06142e050418030f0d0b51080c0518030f0d100b0c0518030f0d8e100b1e0c05030f0d1d100b0c051518030f122517160e0518030f0d17100c0518030f8d0d100b0c0518030f250d8410
|51=>0xf0d100b0914050418030f0d0b0e0c052c18030f0d1710080c0518030f0119100b0c0518030f430d100b1e060504030f0d100b0c05071f030f0d172b080c0518030f250d101e0c0528030f0d17103f080c0518030f0d170b060c0528040302100b450c0518030f0d17100b0c052c18030f11100b0c0518030f1219170b0c0518
|52=>0x101e0c0518030f0d3d100b0a140538030f0d100b0a080504030f0d0b210c05041803020d0b090e0c05041803020d10340c05030f0d2a100b0c0518030f0d3910260c0528040302120b0e0c0504030f0d2f100b220c0518030f0119100b0c057e18030f0d1710223f0c0518030f0d170b090e0c052804030f100b510c052c1803
|53=>0x30f0d100b060c0518030f251026090e0c0518030f121734550c0518030f0d0b0a1405180302120d0b0a0518030f0d19100b2b550c0518030f0d0b060c0518030212170c052804030f010b0e0518030f0d3e17101e0c0504030f120d0b0c051f18030f940d10093f0c0518030f0d17140c050718030f250b0a142e051803020d
|54=>0x18030f12100c7705281f030f0d100a0e05151f030f0d10780c0518030f0d171034090518030f0d100b950c0518030f0d100b0a0c05030f0d11100b0c0518030f0d27100b0e0c0518030f124010140c0528180347020d0b220c050418030f0d0b0e0c052804030f0d171e060518030f2f100b060e05180347020d1034062e0518
|55=>0x51518030f0d170b310c05281803470d100b0a140528030f25100b960c0518030f0d100b1e140e051803020d1020090c0518030f12100b2b0c0518030f2717100b2b090c0518030f0d100b140c052c1518030f0d0b140c0528180f0d2d100b140c051803020d410b0c052815030f12170b0a220e0518030f0d100b090e0c051f
|56=>0xf19100b210c0518030f25170a0c2e0507030f0d100b980c0518030f0d59100b2b080c0528030f0d100b310c0518030d41100b080c050418030f0d190b0c0515180302120d1734060518030f120b0c0518030f970d100b16142e0518030f0d100b060c051f18030f01102b1e060518030f0d100b0c0518030f0d2317100b210c
|57=>0xc051f18030f25100c05030f010d2317100b210c2e051803020d100a14051803020d170c050418030f0d3e0b0608050418030f0d170b0a0e0599030f0d101e0c0504030f0d170c0518030f0d52100b0a060507030f100b0a0c0503020d72100b090e0c05281f030f100a060538030f100b060e0518030f0d00100b210c051803
|58=>0x30f0d100b1e0e0c0507030f0d100b3f0c0518030f12250b140c05071803020d0b06080e052818030f100b34060518030f0d170b0e0c051803020d7b10060518030f0d5417100e0c0518030f120d000b1e0c0518030f252f10220c05030f0d23100b310c05281803020d1710560c2e0518030f0d100b1e0c0518030f27100b21
|59=>0x54170e0c0518030f0d13100c053b18030f0d17100b140c2e052804030f0d0b580c050418030f0d0b080c0504030f0d00170b310c0504180302120d0b0c051803020d1917100a08051803020d17100c0518030f2557100b160e0504030f0d100b060c0528180f2d100b3f0c051f18030f0d10080c0518030f0d4010511e0c0518
|60=>0x100a14052803020d100b1e0c0518030f010d17100c0518030f2569100b140c0504180f0d2d0b210c0518030d8b100b16140518030f0d170b0614052804030f0b220c052818030f17100b200c0518030f12100b080e0c053818030f0d100c0528180302011710080e0c052818030f120b210c0518030f0d260b0c0518030f120d
|61=>0x18030f2417100b060c2e050418030f120b080c050418030f250d17140c052c18030f0d170b080e0c051803020d00101e14051518030f0d0b2b0c051f030f0d00100b0c051f18030f27100b0c05189c0f0d100b9a0c0518030f0d100b0c0518030f012519100b09140518030f0d170c057e04030f0d100b0e0c0518030f250d00
|62=>0xd10060c0518030f0113100b2b0e0c0518030f24100b7d0c05281803020d100b1e0c0528030f2f100b140e053818030f0d10340c2e0528030f0d100b140e052818030f120b080e0c052818030f2510340c0518030f250d17210c05281f030f100b2b0c0518030f0d19100b16080518030f0d17100b210c051803020d17080c05
|63=>0xb061405180347020d0b0e0c051f030f0d1d100e0c050418030f010d17340c05180f0d2d100b2b060518030f0d17100b0a090e0518030f12100b0a770528030f0d100b0a08051f030f0d1034060528030f100b090c0518030f0d1d1710220c05180302010d17100a060518030212100b140518030f0d3e170b22080c05180302
|64=>0x100c052818030da1100b3f0c0518030f010d0b0c051803020d9f100b0e0c0518030f0d10810c051803020d57100b220c051f18030f0d10060c052c1518030f100b0c053a030f0d17100b2b1e0c0528030f0d100b0c051803020d9e100b0c05281f030f01100a0c0538030f12100b060c052818034702100b780c0504030f0d10
|65=>0xb1e0e0518030f0d3c100b0e0c051803020d7210510c0518030f0d17100b060e053818030f10080c051f18030f0d19100c0518030f0da2100b0c2e0518030f0d67100b1e0c0518030f0d104c0a14050403020d0b630c051f030f0d100b0a0e0518030f120d170c0518030f2717100b0614051f18030f0d17140e052818030f25
|66=>0x18030f0d130b160c2e051803020d1006080e0518030f120b060c2e052804030f100b22210c05030f0d23100b1e0c05030f0d00100b2b080c051803020d1710220c0518030f19100b080e0c05281803020d100a09080518030f0d100b0c0504030f0d13170b0608051f18030f0d17100c05a318030f0d100b340c0528030f0d17
|67=>0x30f17100b140e05281803020d10140518030f0da7100b0c0518030f0d67170b0c2e0504180302120d1e080c051803020d1022080c053a030f0d100b090c052804030f100b060c051803020117100ca60518030f67100b580c051f18030f0d10060c2e05041803020d10080c051f030f0d0017100c2e052804030f120b140c05
|68=>0x1225080c0518030f430d100b0e0c05741803020d100c050418030f0d710ba90c0518030f0d100b5e140518030f0d100b1e090c0518030f0d17100e051803020da810220c0518030f0d13100b06080e0518030f25100c051f030f0d00100b080c0518030f0d13100b06080518030f1917100b160c0518030f12170b060c052c18
|69=>0x4010060e052818030210090e0c050418030f0d170a0e0504030f120d0b0c0518030f0dad100bac780c0518030f0d100b140e05151f18030f0d060c05041803020d17560cab0518030f0d0b160c0518030f2517100e0c053818030f1210060c052804030f170b1e140e0518030f120d0b0c0518030f0daa100b080e0c0518030f
|70=>0x17060e051518030f0d10080518030f0d3c100b0c052804030f2517060c051f18030f12170e0518030f0d3e100b1e140e0518030f250d10140e0518030f1225080c0518030f0d27100b0c050718030f11100b080e0c0518030f0d2a10060c05180f122d100b0e0c0518030f0d1c100b2b1e0518030f0d3c100b0c770518030f0d
|71=>0xd00100a77051f030f0d101e550c0504030f0d0b140c05041f030f250d0e0c051518030f120d22210c0518030f19100b0a0e0504030f0d17090e0c05501803020d100c0518030f0daf100b0c0518030f0dae100b140e0518030f0d2a10080c053818030f0d100c2e05280403020d10310c0518030d72100b1e140e0518030f0d
|72=>0x170b0a0e055003020d100c051803020d3e17109b060518030f0d100b2b220c0518030f0d100b0e0c052818030212101e090c0504030f0d100b1e140e0528030f0d100b080c052818030f25100cb00518030f0d100b0c052c1803020d17100c050418036102120b080c051803020d001022080c05030f0d23100b0c0518030f25
|73=>0xc050718030f0d6a0bb40c0518030fb30d100b1e0c0518030f0d27100b0c0518030f0db2100b060c05281f030f17100a142e0504030f0d0b310c057418030d100b140518030f5f0d100b140e0518030f0d26310c05071803020d100b090e0c05180347020d10b10c0518030f0d100b160c0504030f25100b080c050718030f0d
|74=>0xb0c05041803020d6e100b140c051f18030f0d4c0c05041f030f1225060c05041f030f2510160c051f030f25100a140504030f250d0b080c0518030f2717100b0c0518030f0d57170b080c05281803020d100c051803020db7100b0c0518030f0db5100b20090c0518030f0d1710060c05041f030f120b0a0e051f030f120d10
|75=>0x10210c05041f030f0d0b0c0565071803020d100b0a06051803020d17100c0518030f0d1c100b0c0518030f010d00100b140e052818030f0d17140c052818030f010b0a060528030f17100b0c055018030d6e100b080c05041803020d0c0518030f24100b140e0518030f0d2f100b200c0518030f0d17100c0518030f430d0010
|76=>0x10b80c0518030f0d100b0c053a030f010d100b0c05071803020d17140518030f010d3e0b060c051518030f120b0a140518030f0d4c0b0c0504180f120d2d0b5d0c05281803020d100b060c0504180f0d2d100b160c05180f0d2d100b0c05041f030f010d0c0518030f0d191c100b080c052818030f01100b0c77053818030f0d
|77=>0x970d53100b140e05180347020d3f0c052818030f100b140c051518030f010d0b0e0c051803020d2f10bb0c052804030f120b0c7705281803020d1006140518030f010b0a060518030f0117100b1e080c0504030f0d0b0c051803020d30100b210c053818030f100b340e0518030f0d170c0518b90f0d100b060c051518030f25
|78=>0x1c100b630c051803020d100b22213f0c0518030f0d0b16080518030f0d100b080c050418030f250d1e0c0518030f010d100c0518030f0d1900100b220c052818030f100b2b1e0c0518030f24100b080c0504030f0d000b0614bd0518030f120b210c0528180302100b0c0518030f0dbc100b0608050418030f0d0b0c0518030f
|79=>0xd100a0c05151f030f0d100b630c2e0518030f0d100b220c0518030f0d23100b0c0515180302010d100c052815030f01100b0a060504030f120b080c051f030f0d00100e0c052818030f011710510c0518030f0d100b0c0518030fbe0d100b3114051803470d0b140c2e05281803020d100c0518030f27100b080c0518030f0d
|80=>0xb0c051f18030f120d17140e0518030f0d170a0c050403020d100b0cb60518030f0d100bbf0c051803020d100b20160c0518030f0d100b060c051f18030f0d17100e0c05281803020d100c0550180302120d100b0c0518030f0da7100b140e0518030f250d100c05180f120d2d100b0a090518030f0d100b080e0c051f18030f
|81=>0xe0518030f25100c05501803020d17100a0c0515030f0d17100b0c0518030f0d13100b2b340c0518030f0d100b0c0518030f0dc01710090c0518030f010d100b0c051803020d7b100b080c052818030f0d100b140c050718030f0d0b0a0c0599030f0d100b5e0c0518030f0d100b0c05501803470d100b1e060e0518030f0d10
|82=>0xf0d2a10140c053818030f0d100b080c050418030f0d0b160cab0518030f0d100b060e0518030f12100b0a060518030f12100b0a0c2e0518030f120d100b0c05501803610d100b1e0e0c0518030f250d105d0c051803020d100b140518030f0d54100b550e0c0518030f0d100b0a140528030f0d100b0c0518030f0da5100b06
|83=>0x5151f18030f0d10060c05041f030f0d100b0a060518030f0d17100b0c05c118030f0d100b160c051f030f0d100b0c05281f030f0d17100c0518030f0d57100b1e0e0c0518030f120d100b0a060528030f100b201e0c0518030f0d100b0e0c0518030f0d19100b0a080e0518030f0d100b0a0c2e0528030f0d100b0e0c051803
|84=>0xc053818030f100b0e0c05041803020d100e0c0518030f1225100c051803020d72100b0c77051803020d100a0c0518030f120d170b0c2e050718030f0d100b0c05041f030f120d0b1e0e0c0528030f0d100b140c052818030f25100b0c0518030f0d3c100b0a140504030f0d0b0c0518030f0d69100b060e051803020d100e0c
|85=>0x518030f0d100b0a0c0528030f12100b0a210518030f0d100b0c050718030f0d170b140cc20518030f0d100b3114051803020d100b2b0c0518030f0d100b0a0c05180347020d100b0c050418030f0d4c0b0c05041f030f250d100c0518030f5f0d100b0c05500403020d100b1e0e0c0518030f0d1710060c050718030f100b06
|86=>0x120d0b0a0c2e0504030f0d100b0c0518030f0dc6100b0e0c0518030f0d10260c77052818030f0d100b0a0c0528030f0d17100b0e0c0518030f010d100c0518030f0dc5100b0c05741803020d100bc40c0518030f0d100b22080c0518030f0d17100b0c0518030f0dc3100b080c0518030f250d10140c05281803020d100b210e
|87=>0xf0d170b0c051f18030f0d104cc8160c0518030f0d100b140c0518030f0d2a100b22090e0c0518030f0d100bc7340c0518030f0d100b0a0c0504030f250d100b060c051518030f0d100b140c05041803020d0b0e0c0518030f0d2f100b060c0528180302100b06140518030f25100b140c05151f18030f0d0bbb0c050418030f
|88=>0xb8f0c050418030f0d100b0e0c052818030f0d1710220e0c0518030f0d100b140c0518030f010d0b06770518030f0d100b0c052818030f01100b0c0518030f0d19100bbb0c052804030f0d100b140c2e051803020d100c057518030f0d100b340c051803020d100b0c0518030f0d93100b1e0c0518030f250d10140c05151803
|89=>0x30f0d100b0c0518030f0d84100b140c2e052818030f0d100b0e0c050418030f0d170c0518030f010d3e100bc70c0518030f0d100b0a0c0518030f0d104c0b080c051803020d17100c770518030f250d10140c051803020d17220c0518030f010d100b080e0c0518030f0d19100b080c0518030f010d100b0c0518030f0dc910
|90=>0x18030f250d0b0e0c05180347020d10340c2e0518030f0d100b0c051518030f0d11100b080c052818030f0d17100b0c051518030f010d100b210c0518030f25100b090e0c051803020d10140c2e050418030f0d0b140c052818030f0d170b060c0518030f01100b2b080c0518030f0d100b310c05281803020d100b0614bd0518
|91=>0x200e0c0518030f0d100b06080518030f0d17100b0c053818030f0d17100c052818030f12170b080c0518030f0d19100b06140518030f0d170b2b0c051f18030f0d100b0c052c18030f0d100b0c2e05281803020d100c054f1803020d100b060cbd0518030f12100b340c0518030f250d100b0c051f18030f0d3c100b140c0504
|92=>0x51803020d100b0c052804030f25100b0c0504180302120d0b630c0518030f0d100b060c05041803020d100b160c051803020d100b060c2e051803020d10210cbd0518030f0d100b210c052818030f100b0e0c050718030f0d100b310c051803470d100b140c051f18030f250d10140c05180f0d2d100b580c0518030f0d100b
|93=>0x2e051803020d10060c051803020d100bcc0c0518030f0d100b0c05151f18030f0d100b080c051803020d10920c052818030f0d100b0c2e050418030f120d0b0c0528180f0d2d100b0c0504030f0d2a100bcb0c0518030f0d100b0614050418030f0d0b0c05281f030f25100c0518030da1100b220c0518030f01250d100b7d0c
|94=>0x30f0d17100b140ca60518030f0d100b340c0518030f0d100b140c050418030f0d0b0c051803020d1710060cbd0518030f0d100b060c052818030f100b0c0518030f0d10260b0c2e052818030f0d100b0c0518030f010d100b140c052818030f0d100b0c051899030f0d100b0c0518030f1225100b090e0c0518030f0d100b0c
|95=>0xd100b0c05180347020d100b0c0518030f250d17100cab052818030f0d100b140e0518030f0d100b060c0518030f0d17100b0c051f18030f250d100c05501803020d100b080e0c0518030f0d100b0c05180f0d2d100b060c0518030f12100b0c050418030f0d170b0c050418030f250d100b060c2e0518030f0d100b0c052818
|96=>0x100b0cc20518030f0d100b140c2e0518030f0d100b0e0c0518030f0d17100c053818030f0d100b0c770518030f0d100b140c051803020d100b0c0518030f0d40100b0c050418030f120d0b060c050418030f0d100b160c0518030f0d100b080c0518030f0d100b060cab0518030f0d100b920c0518030f0d100b0c05281f030f
|97=>0xc0518030f0d100b0cab0518030f0d100b0c052818030f0d100b0c0518030f250d100b0c2e0518030f0d100b140c0518030f0d100b0cbd0518030f0d100b0c051803020d100b0e0c0518030f0d100b0a0c0518030f0d100b140c0518030f250d100b0c05281803020d
|_=>0
def sO:Nat→Nat→Nat
|6,0=>0xc5c02a7008dc01c70055c00e7001dc0007
|7,0=>0x8ba02268087a02168083a0207707fe01f7807be01e78077e01d78073e01c7806fe01b7806be01a78067e01978063e0187805fe0177805be01678057e01578053e0147804fe0137804be01278047e01178043e0107803fe00f7803be00e78037e00d780341c0c88030200b8802c200a8802820098802420088802020078801c200688018200588014200488010200388
|7,1=>0x109e041f8105e041071022040170fe603f180fa603e180f6603d180f2603c180ee603b270eaa03a280e6a039280e2a038280dea037280daa036280d6a035280d2a034280cea033280cadc32380c6e031380c31c30480bf202f570bb602e580b7602d580b3602c580af602b580ab602a580a76029580a360285809f60275809b6026580976025580939c246808fa02368
|7,2=>0x55c71552054c81512053c814d2052c81492051c81452050c8141204fc813d204ec8139204dc8135204cc8131204bc812d5c4ad81296049d81256048d81216047d811d6046d81199c45e8115a044e8111a043e810da042f7
|8,0=>0x1e2a078191de2476f91d9a475e81d56474c91d0e473b81cca472a81c86471891c3e470781bfa46f591bb246e391b6e06d291b2646c091ae206af91a9a469e81a56468c91a12067c819ce466a9198a0659919424647918fa4635918b246239186a46119182245ff917da45ee8179645dd8175245cb9170a45ba816c645a98168245979163a4585915f24574815ae45638
|8,1=>0x26be49a6926764995826324984825ee4973825aa496192562494f9251e093e924d6492d82492491c8244e490b8240e08fb823ca48ea8238648d89233e48c6922fa08b5922b248a4822720894822320883921ee0873821aa486192162484f9211a483e820d6482d82092481b9204e080b8200a47f991fc607e891f7e47d691f3a07c681ef647b581eb247a391e6e07929
|8,2=>0x2f660bd092f220bc082ee20baf92e9a4b9d92e560b8d82e124b7b92dce0b6a92d8a0b5a82d464b4982d024b3792cba4b2682c7a0b1592c324b0482bf20af392baa4ae282b664ad092b1e4abe92ada0aad92a924a9b92a4a4a8a82a064a79829c24a679297a4a55929324a44828ee4a33828ae0a229286a0a119282249ff927da49ed9279249dc8274e49ca9270649b89
|8,3=>0x38064df8937be4de78377e0dd6937364dc5836f24db3936ae0da2936664d909361e4d7f835da4d6d935960d5d835524d4c835120d3c834ce4d2a934864d19834424d07933fa4cf5933b60ce49336e4cd29332a0cc1932e24caf9329a4c9e8325a0c8e8321a0c7e831d64c6c9318e4c5b8314e0c4a931064c39830c24c28830820c179303a4c0592ff24bf392faa4be19
|8,4=>0x40aa50228406a1011940224fff93fda4fed93f924fdc83f4e4fca93f0a0fba83ec64fa983e824f9883e3e4f8693df64f7583db24f6483d6e4f5293d264f4183ce24f2f93c9a4f1d93c560f0c93c0e4efb83bce0eeb83b8e0eda93b464ec983b060eb893ac20ea793a7e0e9693a364e84939ee4e73839aa4e62839664e51839224e3f938da4e2d938960e1c9384e4e0a9
|8,5=>0x496a125194922523f948da522e84896521c9484e520a9480651f8947be51e69477a11d59473611c5846f251b3946aa51a194662518f9461a517e845d6516d84592515b9454a5149945025137944ba5126844765114944321103943ea50f2843a650e09436210cf9431a50be842d650ac9428e509b8424e108a942065079841c610689417e50569413a1045940f250339
|8,6=>0x521e147e951d6546c9518e545a951465449851025437950ba54259507254139502a540194fe253ef94f9a53dd94f5613cc94f0e53ba94eca13aa84e86539984e46138984e02537884dbe536784d7a535684d36534584cf2533394caa532194c62530f94c1e12fe94bd652ec94b8e52da94b4a12ca84b0652b894abe52a694a76529494a2e5283849ee1273849ae12629
|8,7=>0x16ab85a8a569a85a46568895a021677959ba5666859765654959321644858ee5632958a6562185862560f9581a55fe857da15ed9579615dc9575215cb9570a55b9956c615a89567e5596956365584955ee5573855aa55628556655509551e553e954d6552c9548e551a9544a150a8540654f8953be54e69537654d49532e54c2952e654b2752a654a09525e548f8
|9,0=>0x63e218ef9639698dba634698c9862fe98b6962b658a3a626698909621e587e961d2986b9618698589613e5846960f29833960aa58228606658109601e57fda5fd257eb95f8e17da95f4657c7a5efa57b4a5eae57a295e66579095e1a977e85dda176ca5d8e575a95d429746a5cf6573495cae572295c62970f95c1a56fca5bce56e9a5b8256d795b3a56c595af256b39
|9,1=>0x6d165b3c96cce5b29a6c825b1796c3a5b0596bee9af296ba65ae096b5e5ace96b165abd86ad61aac96a8e5a9a96a465a88969fe5a75a69b25a648696e5a51a69225a3f968de1a2da688e9a1a968429a06a67f299f3967a699dfa675a59cd9671619bba66ca59a8a667e5995a66325983965ea59719659e995da6552594aa65029936a64b659249646e59129642659009
|9,2=>0x765e5d8e976165d7ba75c69d689757e5d55a75325d43974ea5d30a749e5d1e974529d0aa74065cf8973ba9ce5973761cd49732a9cc2872ea1cb1972a61ca09725e5c8f872169c7c971d21c6aa71829c56a71365c43a70ea5c32870a65c1fa705a5c0ca700a9bf8a6fba9be596f725bd396f269bbfa6ed69baba6e869b9896e3e5b85a6dee9b7296da65b6096d5e5b4e9
|9,3=>0x7fb65fe3a7f6a5fd0a7f1a9fbd97ed61fad87e8e9f99a7e425f8797dfa5f74a7daa9f60a7d5e5f4e97d129f3b97cc69f2897c7e5f15a7c2e9f0387be69eefa7b969edba7b469ec897afa9eb597ab61ea497a6a9e9287a265e7fa79da5e6ca798e5e5a979465e48979021e36a78b65e23a786a5e10a781e5dfe977d65deba77869dd89773a9dc4a76ee5db2976a65da09
|9,4=>0x88fa2234a88ae622298862a20ea881661fba87ca61e99878261d79873a61c4a86ee61b2986a661a09865aa18ca860e617a985c661689857aa154a852e6141a84e2612ea8492a11b98446a108983fe60f5a83b260e2a836a20d0a831e60bda82d260ac8828e609a982466088981fe6076981b660649816e605298126603fa80da602ca808e601b8804a6008a7ffe5ff69
|9,5=>0x9222647ea91da246d99192645aa91466447a90f6a434990ae64229906664109901aa3fd98fd623ec98f8e63da98f42a3c888efaa3b598eb263a398e6a639198e22637f98dda636d98d96235c98d4e6349a8d062337a8cba6324a8c6e6311a8c1ea2fe98bda22eca8b8e62da98b42a2c798afa62b598ab262a398a6a6290a8a1e627e989d2a26b9898a6259989426246a
|9,6=>0x9b3a66c599af626b3a9aaa66a199a62669089a22267f999da666d99996265c9994e664a999066637a98b6a624998722612a9822a5ff997da65eca978e65da99742a5c7996fa65b5996b265a4896722592a9626657fa95d6a56c99592255b9954e254a99502a537994ba6525994726512a94266500993de64eda938ea4da9934664c8992fe64b6992ba24a4a926aa4919
|9,7=>0x27eaa9f82a7d799f3a67c689ef667b3a9eaa67a199e66278fa9e1e277da9dd2676aa9d86675899d3e6745a9cf26732a9ca6672099c5e670e99c1666fba9bce26ea99b82a6d79
|10,0=>0xa906aa389a8baaa24aa86e6a138a82a6a028a7e2a9eeaa792a9db9a74a69c99a70269b5ba6b629a3aa666a98faa616a97c9a5caa9699a57ea9569a5366942ba4e6692faa49a691d9a44ea90a9a40668f98a3c268e6aa37668d3aa32a68c0aa2de68adaa292689b9a24a68899a1fea8769a1ba28659a17268539a126a83faa0da682caa08e681a9a046680899ffaa7f4a
|10,1=>0xb276ac92bb222ac7f9b1d6ac6bab186ac589b13e6c469b0f66c33ab0aa6c219b0626c0f9b01a6bfcaafce6be9aaf7eabd4baf2aabc0aaedaabad9ae8eab9a9ae466b87aadf6ab73aadaa6b619ad5eab4daad126b3b9acca6b299ac7aeb159ac326b02aabe66af09ab9e6ade9ab52aacb9ab0a6ab8aaabe6aa69aa766a949aa2aaa819a9e26a6f9a99a6a5d9a9562a4ba
|10,2=>0xbb562ecbabb06aeb89babe6ea69ba766e958ba362e82bb9e66e709b99e6e5e9b952ae4b9b90a6e38ab8be6e25ab8726e12ab8266e009b7daadecab78e6dda9b742adc79b6f6adb49b6ae6da29b662ad8eab612ad7aab5c66d67ab576ad52bb522ad3f9b4da6d2cab48aad199b43ead05ab3eeacf29b39eecde9b352accb9b306acb89b2be6ca78
|11,0=>0x3087ac1fa70759c1aeb0629c16670509c11e703e9c0d6702bac08a70199c03eb0069bff66ff49bfae6fe1abf626fceabf166fbc9becaafaa8be866f989be3aaf84abdeaaf70abd9e6f5e9bd5a2f4cabd0e6f3a9bcc2af279bc76af149bc2e6f01abbe62ef09bb9e6edda
|12,0=>0x30d89c33e70c69c2f670b49c2ae70a38c26a70919
|13,0=>0x30e18
|_,_=>0
def wAt:=mkWire dB 205 256 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 18
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 1000003 zs)
def oP:Nat→Nat
|0=>0xd044b80f050b46041181346006120b434410f0b42061170c4402d1817418410c0d4402d182783055040b438a10f0b4302d0d1843c2d0e0d4302d0f0b45c3517184402d171840463100b43061100c454370c18440390f0b438350c0b4102d181048c432218c842d0d00820630c174402d0d10420632018c34790c1f4602d181745c350f0b4402d100e43c2d0e0d4302d
|1=>0x100b460350d374c463020c43c2d0d0b42037170c4402d0828c502d0c1046035100e43c2d0e0d4302d0d1743c2d100b4142d0f0b410351810430a1181746035100b43061101843c2d080dc38410c0b4609e08184502d0e0d420370e104302d0d0e43c2d0e104302d0d0c4302d0118c40390f0b438350c0b43c2d080d438410c0b430550f0b45c61100b45c31170d4402d
|2=>0xe0d4302d0f0b460390e0d4302d0e1843c2d0c0b4602518098182d0d0c41861120b434410d0c4b80f14184142d0c10478351e0dc307d180b4402d0d1e84031181243841100d4302d0e184a041180d4302d200dc182d0d0c44031100d4142d0f0b434390c0b4a0410c254342d180d418410c0d4142d0f0b434310c17440610d174602d100b4305d100b430a1170d43c2d
|3=>0xc0b4502d0d0443041181043841040d430610f0b4302d1810440312e03c142d18104182d040c460410d0c454350f0b45c61100b420a3180d45c350f0b4402d100c4605d0d1746035100b4302d0f0b42035140b43041170d45c31100b43439080dc38410c0b440950d0b420350f0b4502d0c1043c2d150dc5c61100b460492e03c142d0d1043c2d170c4402d091843c2d
|4=>0xc10420630c17440350f0b4402d0d0c438410f0b438610c0b4602d1810420370f0b420350e104302d100647c350d0c43061180b4402d1718418610f0b4402d0d0c4348e080d4502d0c1043c2d080d42061140b430410818c38610c0b42063100e460390c0b4b80f050b41031181043c2d0e184302d040b494310d0b460410e0d438610c0b43c2d0c174402d0818c3861
|5=>0x140b44031180d46105470dc08410f0b4605d170d43c2d100b43041184583045040b46041181042037180c4a02d0d0c4502d100c46035181051463110c4102d1810430a10d184142d0f0b460650818c502d0c1043c2d170c4402d1218460310d10434390f0b4302d140d460310f0b4402d0d18430410828c2035140b430410c1f49441180b4342d220cc3c2d2210c502d
|6=>0x170c4402d0c124b80f050b43441280b450610c0b43461100c4343117184402d100d450610c0b43461100c460411806430350f0b4302d0d1046041100d4b80f050b43c2d181046031080d4502d100c460010818c502d100c48837120e434410c0b43c2d0e124302d0d1043c2d140d4142d0c10438610e0d4302d0c174402d180e4302d0f0b43441050b460410818c3c2d
|7=>0x140b43041100d4b80f050b418610d104142d181043431100a43c2d0c0b43441180c46041180b42037140b430410f0b48860080d438410c0b460060c0d44031170d4402d104e858090f0b430410918c38350c0b46041170dc307d180b4402d0d10460350c18440190d0b43431181047841180e4302d0d18434410f0b4ac37150c4402d0e18440390c0b4602d2218c2035
|8=>0xe104302d2b0dc3c2d0818438410c0b4482d0c0b42841180c434410c014482d0d104386110024302d100c43c2d040d430610f0b4302d181048833080d438410c0b45c35100b54043021843c2d040b46041180b430350818c3841170d45c310c184602d100b45c610d0e8402d0f0b48833080d438410c0b43c2d170c45c61100b43c2d0818438410c0b420630d1043c2d
|9=>0x100e4602d0c0b54c371054438630c0b428410d0c43061180b4402d100b424630e0d420630d0c45c61100b4342d14184302d0d18440311009494310d0b408610118c5c35100b43c2d100e4302d180d46041180e4a0410d184402d0c0b434010d0082063140b430411810438410c18438350c0b44061180b43006120b43441180b4305d100b434311810460010f0b42063
|10=>0xc0b4605d0d0b4402d140d430412218c4025060b434310c4c4602d0d178402d1810430410d1e4307d180b4402d510dc8861080d4502d0c1043061100d4605d0d0b4402d0e18440390c0b4602d0d0b41c33040d46041100c454370818cac3408184502d0c1043c2d0c0b458430a0d460310d1942037140b440310c158407d101e87c31180b410390c0b460410d1843035
|11=>0xd10434550d158102d1810460410f0b4302d0d18440310e18c3441100c4342d0c0b544370c2c46005120b434410f0b46031170d4402d100e460410f0b438610c0b42063140b440310828c5c31170d4402d011845c35100b43429180c43041180b4402d0f0b4ac43081845c31100b430410d1746035100b4302d0f0b440350c10438350c0b440390c0b43461105443863
|12=>0x1812430410d0b43441180c4302d140d4402d180d430410f0b48843010c45c35100b43c2d2210c2035140b430410c1843c2d061043431181043c2d2b0d0502d0c10434390c1843c2d0c0b4604128104b80f050b4603518098182d100c434310d1045c31170d4402d104e058090f0b42835180c460390f0b420370e104302d180e4303510254342d0c0b4356a0c134482d
|13=>0x180b4302d0c0d43c2d080dc38410c0b460950d0c430410d0b4402d1018430350f0b4302d0d1054c371054438630c0b43061100d430950d0b4402d2b0dcac430c154102d181043429170c43061180b4402d5c18d60610c4c45c37100b4302d1f0d4602d1810434310e184402d1810438350c0b40431120b43441140b440310d0b43431181046005120b430410d1043431
|14=>0x828c502d0c10434610f0b450610c0b43461100c434560c104402d0d0b41861181043431103185c61100b408310f0b47c350d1044061180b4302d0e10434410918c38350c0b420630d1043431170c4402d170d4605d100b434610c104303518018402d0c12460960d0b434412b0ccac630a0b460310c01494410d0b46041180c434010818c502d0c10434390d1044061
|15=>0xd0c43c2d080dc38410c0b43441400c460960d0b4402d140d45c61100b4402d0f0b410351810440790f0b438610c0b4348e2218c2035140b430410f0b4345d100c45c61100b438410c0b428350d1046031101843c2d080dc38410c0b4342d100e4302d0d10460310c0d4402d0d10438610c0b43455040b4304118104603117284305d100b434610d0c4b80f050b44031
|16=>0xc104342d0d1f838410c0b4605d0f0b4402d180c434410f0b438411e0dc38610c0b4302d064783035021043c2d0c174402d0d184118618104402d020d43c2d0c1846041080dc502d0c104602d080dc38410818c502d0c10430a10d184142d0f0b41035100e4302d181043431181745035100b460350c104102d181043041100b435510e18c302d040b44061100c4182d
|17=>0x140d43041080dc8843080d4502d0c1044039280c460350d0b4302d100c4142d0f0b4347d100d4305d180b4402d0d0c4502d100c4603518104602d0c124342d0d10460310f0b4ac63150c45c61100b46026060b440310d0c434410d0b440610c10438610c0b4c4a3180d408310f0b434310d0b42063170c4402d100d4b80f050b45841280c460350c0b4402d150dc5c61
|18=>0x100b4285d180c430350d0b4402d0d0082063140b43041080d4502d0c1046035180c4b80f050b434311806430350f0b4302d0d10440350d0b42063170c4402d0c0b4d0370f0b45061100c4407518098182d0d0c4305d0f0b4402d0d0c46041100c4386310254342d0c0b594630702448610d1043061100c43c2d1218434410f0b424630e0d4302d0818c88632210c842d
|19=>0x2b0d02061140b43041180042063140b430410c184b80f050b460410c104a02d100d4305e100b460352b0dcac43081845c31100b440250c1843439180b4302d180d440390c0b4a0410d0e43461180b4302d18278d02d1418430415c18da031184c45c37100b431310c184345e100b46041100e430610d0e4602d0c0b4347e181044031180b4302d18104347d0c174602d
|20=>0x1810460390c10438350c0b4342d181046031170c4402d0d1545c61100b43c2d0818c2037140b430410604434311810434610f0b4302d1810434310d17434610c1f4602d100b430950d0b4402d180d460311817830350d104402d0c0b488630c014482d0c0d434410c174602d100b42063181043c2d140b430410f0b440390c0b43441180c43c2d0d174402d180c42063
|21=>0x1018434610d104543318174402d0c1043c2d100d494310d0b46031181043431180e434610c0b4402d09104182d0d0c408350c0d43c2d0e184302d340dc602d100b450610c10460492e03c142d0d10434790c1f4602d150dc3455101f4602d100e4342d0c0b4603518104402d10184c437020c43c2d4718c08410f0b430610d104142d181043431100d460350c158102d
|22=>0x10024302d100c43c2d10394383710184602d0c0b434410f0b42063170c4402d180e4302d0d104285d100b43035180d46031180e45035100c4302d100b430610d0c46035021043c2d010c4345d100b4502d0c1043c2d0a0d460310c0b460060c104482d0d104402d0918c3c2d2b0d02061140b430411825440310d0b4343118104402d0c10478370e184302d0f0b4302d
|23=>0xe104302d040c47c35180b460410d0c4b80f050b434410f0b4305d100b434610d10438410c0b43c2d040d460410d0c4ac370818438410c0b51c3710024302d100c43c2d1728460350f0b4402d0f0b46066080dc502d0c1043c2d17184402d0d004502d0c1043455040b46041150dc3061101f4602d0c0b4342d180d43056040b460410d23888630c01494410d0b46035
|24=>0xd0b4402d180d4603114184482d0c10434410d0c4301110184345d180b4402d102843c2d0c18434610d0c4345e180e440310c0b4402d140b43c2d100c460351810420350e1044061180b4302d0d174305d100b4343118104304d0118c5c35100b544632010434790a0b460310d104402d0d54438630c0b4ac932b0d02061170c4302d180c54037021843c2d181982037
|25=>0x100c488432218c2035140b430411817850350c104402d0c0b45c610d0c430410d0b4402d2218c8843080d4502d0c1043c2d2218020350e104302d1810460310c0d4342d100b4c443180d4402d020c43c2d0f0b4142d0c10434410d0c440350f0b4305e100b460350c0b440310f0b4103518104d037141843041220dc8843140d43041040d430611810438350c0b4285d
|26=>0x180e4302d0d1843441100b460390c0b43461100c460350c1043c2d0d0c46041180143431180c45c35100b46031281043461100b4302d100b4a0090f0b434610d10434010818c5c31100b45035050b430411810460310f0b4ac3708184302d180e8342d0c0b45035100c43c2d050b4604106184482d0c10434410d0c438410c0d460960d0b4302d0e2843c2d0c0b46035
|27=>0xf0b45c61100b434010f0b420630e104302d1e0dc40610c1f4602d100b438490d1043c2d0c0b42063140b440310d104342d6a1845c33100b430410e0dc605e100b4302d2b0dc2061140b430a1170c46035170d4402d0d1143456040b460412218c3005120b434410d0e4302d18104ac432b0cc502d100c4783510184307d180b4402d0c0b4a05d100b460350c1043849
|28=>0xc174a0410d184602d100b4403a280c460350d0b4302d0d374c463020c43c2d0c0b43431180d408410f0b440390c1843c2d0c0b46041100b47c31180b434310d104ac3708184502d100c4285d0d0c46031170d4402d100d430610d0e4602d0c0b4605d180d43c2d170d4402d101843861100e4342d0c0b434020818c5c31100b43c2d0c10460410e0d4302d150dc4035
|29=>0xc0b44431150dc102d1810440290c1843c2d0e0d4302d2b18cac3708184502d0c104602d120b430410d1043431180d40841100c408310f0b4ac370f0b420610e104302d170c440610d1f8602d100b43c2d2210c2035140b430410d0e450610c0b430412a0c4347e180b4402d184151c37021043c2d221802035080dc3841141843c2d0c10434610d0c45c31170d4402d
|30=>0x100b460350f0b45c31101845c35100b48837221803005120b434412b0d4ac3708184502d0c1042063140b430416510c1c09040d460410c014482d1018434610d1041861100e4302d10164a0310d184602d0c0b41035050b43041181046031470dc0841100c408310f0b45c31101845c35100b4ac372b18cd02d141843041181046031080d4502d100c438610918c3835
|31=>0x40b46041040d440610c10438610c0b43c2d2218c2035140b43041100c4605d180d4342d100b4182d180b410350d0c46041270ccac370818438410f0b4ac3708184502d0c1048863080d4502d0c10434310818c2061140b430410d7b51c63021043c2d0c1243441050b43c2d130c45c35100b4602d06178402d0d0c46041181043c2d0818c5c31100b5a861100d4305e
|32=>0xc0b460e5100c4343a0c0b46041011843c2d170d4402d0c1045c350c1f4602d100b4402d0d10424630e0d4302d170d43c2d100b460350c1046065080dc2063140b430417d28c311d021043c2d0d184342d6a1845c33100b4302d180183041120b434410c2843c2d100e8302d180d43441280243c2d180d460410f0b420350e104302d0c078a0410d184602d100b43045
|33=>0xc2a4347e180b460410f0b42035140b43041800b4580b0f0b42835180c43c2d181942037140b430410d10434610c1f4602d100b43005120b434412b0d0502d0c1042037170c45c35100b420630d0b404630c0b4a041180b4402d0d18434311e0dc50a1180d430410f0b43c2d080d42063140b43041181983c2d080dc5c31100b43401170c4402d340dc50610c104402d
|34=>0x140b44031340b450612b0dc2061140b418110f0b4402d0d0c460411e0dc8863220dc3005120b4344108184502d100c45035180c43041180b4402d0c104a05e180d4402d0c0b43455040b4604125104602d180d4342d0c104602d0c0d4403a0c0b460351f104602d0a0d43441180c440610e18420370e104302d0c0d4302d100b460351810430050d174602d100b43041
|35=>0x828c2035140b430410f0b4142d181042061140b43041180d44031050b43431181043c2d180042063140b430410f0b4ac3708184502d0c10420610818c502d0c10420630d0c438410f0b438350c0b46075101d46026060b4343110094182d0d0c438410d0e4302d180d460410c01434610d174602d100b438610918c38350c0b45c310d174602d100b420610d0c43c2d
|36=>0xf0b4302d0d1043835080dc38410c0b42035100e4302d0c0b4345d100b434311810410310f0b4142d181045c35080dc5c31100b42035170c4402d050b43461040c460410d0c4402d0d0e430410e184302d0c17440610f0b4402d180c42061140b44031170d43c2d080dc5c31100b444310f0b4543717184402d0d104302d0618460410d0c440610d0e4302d180d44031
|37=>0x1e0d440610c1f4602d100b45c3518064343117184402d18278ac37101e4282d180c450a1180b460350d0b430413128c6035020c43c2d2018c803718094182d0d0c4345d280c460350c0b4402d1028434610f0b438610c0b4285d180c4402d0f0b4405a0a0d4603108184502d0c104142d0f0b42835180c441d2280243c2d100b46035180d440350f0b45c61100b44839
|38=>0x180b4187d0d0c43041180b4402d180e43439180d4302d100b42061140b43041310dc08310f0b434410d1846041050b43c2d0d0b434310818c502d100c46041050b43c2d0d10434310818c502d100c4d0370f0b450610c104ac3708184502d100c43095100d4605d0d0b4402d0e10c303518258342d0c0b430492e03c142d0d105f4630c47408410f0b43c2d040d46041
|39=>0xd1046031381043061280b434610d0c43c2d040d44061170c4402d0f0b4203508184502d0c1045c610d0c430410d0b4402d080d42061140b430412b18cac370c1547c41180b544373425450610d0b43041220cc8843140d43041180c45437104e858090f0b42835180c4a031180b460350d0b44031150c43455040b46041180e434411810438350c0b4b0630d154407d
|40=>0xc1043c2d081845c31100b618316118c08350f0b4302d0c01894410d0b4602d080d438410c0b4191e0c0d408410f0b48863210b450350c10438410918438350c0b41c090f0b4103518104407518098182d0d0c460356a1845c33100b440310d174602d100b4602d100e8302d0d0c434410f0b45c31100b4103a0c0b460410d0c434310c184602d100b460410d0c43c2d
|41=>0xc1045c350c174602d100b4304d18018482d0d10438610d178402d0c0b430410d0b43441180c4502d0c1046035180c4402d180b460310d104580b0f0b42835180c4343108184502d100c410350c1046041180c4303518258342d0c0b4ac37101e4282d180c440190d0b4343118104602d180d4342d0c104244118094182d0d0c440350d0c45c61100b450a1100b46035
|42=>0x100c434310c0b408610f0b4a0390c0b46035100c434410f0b42835180c434391810438410c0b44031101847c31180b434410d0c4142d0f0b4302d500cc08610f0b48860080d4502d0c104d0370f0b450610c104a0090f0b460351810404310d174602d100b434dd3118c08310f0b4302d0f0b41035181043c2d0c178402d0d104602d0818c5c31100b48860080d4502d
|43=>0x140d43041120b428350d10460310d1e840310a0b460312b18c78410e184302d080d420370e104302d180b4345e100b46041100b424630e0d4302d5e105003118258342d7e10c60e50e0dc302d1718430350d0b4402d180042063140b430410d3c83056040b460412b0dc2061140b430417d0dc311d021043c2d10094182d0d0c4347e18104602d0c1048833080d4502d
|44=>0x100b4b03718014482d0d1044035080dc5c31100b4364d9218c50150c104303518178402d0d10488630c01494410d0b42035140b430410c0d44031170d4402d2b0dc30551f104602d100c4142d0d0c46041140b43041109063c630605434310e18424630e0d4302d100d4605d0d0b4402d280c460350c0b4402d0d3c43056040b460410d0b4103a0c0b460418c0fc8415
|45=>0xe184302d220dc3005120b43441100b460e50e0dc302d2210c2035170c4402d0d0e4302d180d4604118014482d0d1044061100c4182d0d0c4a05d180d4402d0c0b45c35080dc5c31100b434010818c502d0c104307d180b460410d0c4a0410d184602d100b420610c174342d100b434610c1f4602d100b48843080d45c31100b460350f0b43431181044431150dc5c61
|46=>0x100b43431120b440610d18434410c0b40433170d4402d0c1f43441180b46041180b5a835170cc402d1009830950d0b4402d2810460350d0b43041180c44031050b43c2d102f4347a0a0b46031280b43041180d46031140b430411810460310f0b418410d0c46041181043c2d0e0d4302d0c044347e180b460410e0dc605e100b4302d0f0b440610d1843441181047837
|47=>0xa0d460310d1583061040b460412b0dc2061140b430411825840350d0b4302d180d43041021043c2d210b418410d0c460410c0b4402d180d460411e0dc34310a0b460310c0d4302d021043c2d050b410311810434311718c30350d0b4402d0e0d43441100b4302d2b10cd02d141843041100c43c2d0d1046031180c42037140b4403110554407a0a0b46031100d43c2d
|48=>0xd0b440316305418110d0c46041180e4302d100c43c2d0d1046025060b434312b0dc2061170c4402d0e0d420610e104302d0d1543041040b460412e03c142d180d430410c1051c37021043c2d18174402d0d18434410c18420350e104302d0d1043439180b4302d180b4403a0c0b434610c0b430611f104602d2a0c4347e180b4402d250c450610d0b44031055645843
|49=>0x210b450350c104342d100b450350c104142d1218460310d10660370c2645c63100b42061140b430410c0251c37021043c2d181042037140b43041100d43c2d17184402d1418430410d1043431530d441510e18c302d100c4142d0a0d460310d0c4345d180b4402d1e10434310a0b460312218c2035170c4402d17184402d140d43041180d43009021043c2d180c46035
|50=>0x50b42835180c4ac37101e4282d180c4342d140d4602d0c1048863010c45c35100b450350c104142d0f0b43061100b430410f0b460410c018482d0d104305d100b43431181046031101f8602d0c0b440610c1f4602d100b54c371054438630c0b43061040d43431181046031500dc08610f0b434390d184602d0c0b43061280b434610d0c430350818c38410c0b48837
|51=>0x18104302d0618460410d0c4b80f050b434610d0c4602d10098182d0d0c460960c174342d100b4282d180c460490d10438610c0b44026100d494310d0b440310f0b410351810440390c0b434610d0c4402d040c460410d0c4302d4718c08410f0b4402d180e8302d0d0c434410818c38410c0b47837180e4342d0c0b48863080d4502d0c1046035100b408310f0b4405a
|52=>0x181046035080d45c31100b4582d0a0d43441180c4403918254342d0c0b460350f0b45c35100b440390c0b434610d1045c63100b450350c104402d180e8302d0d104600610254342d0c0b46065080dc5c31100b4142d100c460351810460410c4c45c37100b440610818c5c31100b430091018434410f0b43c2d080dc5c31100b43c2d180c45c31100b4342d070cc1035
|53=>0xc0b430410c1f47c41180b4ac630c1547c41180b4ac370c1547c41180b40e750705c1035181066c357718438430c0b488370c01494410d0b43439100c4302d100b460411839438370c0b4342d0818c38410c0b43c2d0c1046035180c45c350c1f4602d100b4342d2118c50350c104b80f050b460410c106303f2105450350c10430a1100b460350c1043431100c46035
|54=>0xc0b460350c47408410f0b4347a0d184282d180c4a02d0c0b46035100c45061050b434610c10440350c0b46035100c43461100e4342d0c0b4402d14184342d0c1043461140d4602d0c1042061080dc502d0c10418610d0c45c31100b43c2d100b450350c104ac34081845c31100b43441050b460410d0c440610c174342d100b4a05d100b460350c1043c2d0818c3841
|55=>0x1810434310c10408410f0b4602d0918c38350c0b4345d18104402d0c0b430112e03c142d181043431081845c31100b434390c0b43441180c43061100e8302d0d1845c310c184602d100b43461040c460410d0c460260c254342d100b43c2d010c45c35100b434310f0b43441180c43006100c45c35100b420350f0b4502d0c104303518018482d0d104ac34081843841
|56=>0x170c4402d0d0c43041180b4402d0d0b4302d180d44031920fc5015180d43041102544026250c4342da00dd1c61021043c2d281786035100b4302d070cc3c2d040d46041210b45035180b430410d154102d181048860080d45c31100b440790d184282d180c5401b0d0c408610f0b434610d174602d100b47c35180b460310d1043431180d408410f0b430a90d1f8602d
|57=>0xe0d4302d101840463170d4402d0d0c4305d180b4402d18a56903312054344114184402d0d18430412b0cc78410e184302d500dc302d021843c2d221842035170c4402d0c0b4a02d0d1843431180b42037140b43041750dda861170cc402d050b4d037141843041170dc307d180b4402d0f0b43041181046031211845035180b430410c0b4402d180c434412b0dc2061
|58=>0x60b434310d0c43c2d170d4402d340dc50610c1041435180b43131170dc402d0f0b4142d0d0c46041180b42063170c4402d050b440610d1843441180183041120b43441050b43c2d0a0d460310d0c434410e104302d180d4142d0d0c460412218c842d140d430410e18420630e104302d0f0b42061170c4402d080d42037140b43041180d43c2d0e104302d0e1043061
|59=>0x400c460960d0b4402d0e18438350c0b4302d0c47808410f0b460060c014482d0d1043035100e4342d0c0b4ac630c1547c41180b45c310118c5c35100b43431080dc5c31100b4402d0a0d43441180c4a05d100b434610d0c43c2d0c0b46035100c4a03a0c0b46035100c4d037100b450610c10440610d104142d0f0b438410f0b438610c0b48860140b43041101846035
|60=>0xc0b43441180c63c130506460410d0c5e0412a0c4347e180b47c41100c4602d0c0b43c2d100b434311810458430618414410d0c460190c0d4342d100b4302d280b434610d1043461100b434311810430410d10438610c0b4381f0c0b41035181043841100d4342d0c0b434010818c502d0c104a0090f0b4302d180d440611039438370c0b5582d1610c2835180c43041
|61=>0x101f4602d0c0b4ac3308184502d100c4342d100b4603518104402d180b434410d0c48833080d438410c0b43861100c4342d0c0b43441100c4342d0c0b4ac3708184502d0c104b037070b41035181047c37100e4602d0c0b430352e03c142d0d1046066080dc38410c0b4ac33101e4282d180c4384318258342d0c0b43c2d0c0b434610d0c4402d1810438350c0b44061
|62=>0x80d4502d0c10420630c174342d100b43843180c4602d0c0b44061101e8282d180c460410d0b4602d0c1043441101f4602d0c0b48837210b450350c104306118104402d0c0b434390c0b408610f0b59c2d340dc50610c1069c41280e8302d180d4347e100c4602d0c0b460950c174342d100b4346118104142d0f0b40831500dc08610f0b46039100c4302d100b43035
|63=>0xc0b408410f0b4408218094182d0d0c4342d0618460410d0c41035101845c31100b460310c0b408610f0b404330f0b45c35100b434317718438430c0b4203508184502d0c1043c2d0c0b434610d10438611810438350c0b460390c0b43461100c4502d180d4342d0c10415a52118c50350c10404610f0b45c35100b408351018434410f0b420630f0b4502d0c1048863
|64=>0x180d43c2d140b43041106e4c437020c43c2d0cb681c15040d460411809430950d0b4402d0d104602d1810434310c0b4602d180c4344110284305e100b46035b30c434991718c402d2b0dc40790a0b460318c18c8415140d43041180b4402d0d1843431050b43041181046031280246035020c43c2d0c10435510e18c302d181783041100b4302d0f0b41035181043835
|65=>0xc0b4345d100b460350c104402d0c18434610d0c40861310dc08310f0b460410f0b4502d0c104ac3408184502d0c10430411e0dc38610c0b460250c254342d100b42063140b4304110184c437020c43c2d170dc3041180b4402d0d0b43441180b460410d0b4602d181043431280c4342d180b434610d0b430411810460312b0dc2061170c4402d100b41c33040d46041
|66=>0xd1047c41180b434410d0c430410d178402d180c460412e03c142d0d10460351031808310f0b4b80f050b4343118104b80f050b42835180c440610d174602d100b46066080dc502d0c1045c31180d45c35100b4a02d100e8302d180d46041140d4602d0c1041c090f0b410351810434310f0b4402d180c46066080dc502d0c1045c350818c5c31100b460350c104402d
|67=>0xd0c4345d100c45c61100b43c2d1e0dc38610c0b434410d1841431181043c2d100e8302d180d4482d0c10434410d0c43431180c45c35100b460391810438410c0b51ca3180d408410f0b4347d140d4602d0c10450610c104402d0c0b40ee93405c50610c104102d0d0b4343118105e0432a0c4347e180b488600c014482d0d104402d0f0b410351810430060c104482d
|68=>0x140b43041161043c2d0a0d460312210c842d140d43041280c46035140b4403118104305d0d0b4402d2510460390d0b4302d0818c2037140b430411425460350d0b430412b0d0282d180c460410818c502d0c10414610c10434410d0c43c2d0610434610d0c648a31405460350c10440390c0b460410d0c54c351054438630c0b440090c0b440310f0b4346110098182d
|69=>0xd0b4302d2e03c142d0d1046031060b43431100e4602d0c0b430611f104602d0c074142d040d460412218c2035140b43041171843c2d170d4402d180d45c61170d4402d1810434310d1046031180b42063140b430410d1746035100b4302d3425450610d0b430410d844103a0c0b46041021044031020c43c2d180d43041050b43c2d2b0dc2061140b43041181982037
|70=>0x18018482d0d104d02d1418430410c258342d100b4309525104342d4718c08410f0b46035140b43041100c410351810430611f10c602d400c460960d0b40861021043c2d0c0d438610c0b43441180b4402d0c104402d0c0b43c2d18104603107054103518104c435020c43c2d160b42835180c43035180b4402d0f0b4302d180d43441021843c2d280e8302d180d44031
|71=>0xd0c434790a0b46031080dc38410c0b430610e104302d050b46035180c4347e180b4302d18254342d0c1046041140b430410618414410d0c434310c0b434410d0c43441180c4142d0d1046031020d408610f0b460390d0b4302d1031808310f0b438630c0b440311e10c38610c0b43041180d46031a40cc48150d10434310d0b4302d100b408610f0b4603117184402d
|72=>0xc0b46041100d4342d0c0b54037021843c2d0f0b438430c0b4402d180c43441050b41035181043441180b460410d18438610c0b460350d0b430410c158102d1810430411810460312118c50350c1043c2d0c0b43431101f4602d0c0b4602d1810434310c184402d0d0c41c2f040d46041180b418610d0c43461180b4402d070cc10351810434410e184302d0c1843461
|73=>0x500d408610f0b432651f10c602d080d45c31100b4507e180b430410c174342d100b43c2d180d430410c0b45035100c460350d1046031120c43441180c4402d040d460410528460350c1044031020c43c2d08184502d0c1043061021043c2d0d178402d1810460410d0b4602d0d54438630c0b46041021843c2d180e4302d100b410350d0c46041280b434610d0c43c2d
|74=>0xc0b4403117184402d0d178602d100b458150a0d460310d1f8602d0c10424410e0d4302d3405450610c104342d181046031040b434311810460410c1043c2d1e0dc38610c0b43c2d0d18434310d0c4342d100c430411f104602d1018414310d104142d1810460312105c50350c104605e100b4302d100e8302d180d4402d180d4603110254342d0c0b458170a0d46031
|75=>0x1418430410d178402d180c43c2d170c4402d100e8342d0c0b4402d0c1043c2d0c014482d0d10420370e104302d170d45c31100b728370405460410506460410d0c46035100b4302d080d438410c0b43041120b43441100e8302d0d0c46035120b43441080dc502d0c1043461050c460410c104142d0f0b5a861170cc402d0f0b450610c1064863140543041180e4342d
|76=>0xd10434310518450610d0b430410c1587c41180b460410d0b430410c0b408410f0b4142d1418430410d158102d181046035170c4402d171845c35100b450350d0b430410f0b438350c0b4142d181043041100b460350c1043035120b4344108184502d0c1046035020c43c2d0d0c4403105184103a0c0b46041050b460350c1046041100b4302d0c018482d0d104d015
|77=>0xf0b418110d0c460410f0b43431181043c2d0a0d460310d0c4142d0f0b450350c10414610610434610d0c4302d040d460410c02408410f0b4602d0d0b430410c104b80f050b43131170dc402d0918438350c0b43431170c4402d18254342d100b4402d0d1843441080dc502d0c1043041100b434310c1547c41180b46005120b43441180d4142d0f0b54043021843c2d
|78=>0xd0c414610d18434311718c402d180d4142d120b43441180d430411f10c602d0d0b434410e0d4302d050b43c2d0d0c43c2d0a05460311f104602d0f0b4502d0c1045015180d4304110184142d0d104b80f180d4142d0d1f8602d18104842f140d430410c104343118104342d180b43461920fc50150c104300525104342d0c47408410f0b4342d180d46041101843441
|79=>0x52846035050b43041100b4302d280b460350e10c302d0c1043c2d18258342d100d460410d0c460410a0d46031140b43041051043431140543041180b43461021043c2d0d0b4402d0510460350c0b44031100b43431180b4342d021843c2d0e104302d2e03c142d0d1043431100b460410d0b46041050b43431100b460350c1041435141843041181043041100b43c2d
|80=>0x1441180d4342d050b43041051843c2d0c0b460310d0b43041180d43c2d
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x4400000000000080000
|7,0=>0x50202710132609540499023d011680856000000000106407e5000001e900000000003b201c900dc800000359819d00c68000002eb000000b46000002b201490000000000000013cc000004b4023a000000868040301e200e1006880000018200b4c0528000001318089003e601c30000000000000017500000000002a4000000918039001840084
|7,1=>0xa9180000000014c60a4205110000013f5000004e5826a81323000004b9000001286000000000000000000000000000000123508fa0469422e61134087a0430c0000000008420414c20460ff307da03d581e280ed4074a000001ce4000007218379800000da406b9834d01a240cd4064a0315018460be405d202dcc00000b34057a02ad014e80a43
|7,2=>0x69d83468000000000000033ac1994000006550322818d400000628c00001882000006188000018240c08800002fa817940ba28000000000000000005c102da600000b3b058d02be815b400000000000001556
|8,0=>0x158a8ab1454ea2a2514f98a69400002982149a8a39451482855141189f544f282745138989c04000026d313428994c4c2825c512ba8949449aa2485121a88f94472a2345118988b1444ea223410f288708430821351081882d440e820340ff287ecc3eca1f150f62879d43c4a1e020eda875943a841cf50e528719038661be50dd206d5436461ad5
|8,1=>0x1e1a8f00c77883b751da90ec14756a3a651d0a8e71472ea39521c8280000718838751c1a0df946f2a374500000dbd46d6836651b0a8d7146aea00001a928d354694634551a028ced466ca331519628c9d4646831e518d20c554624630d518428c0d45fe82fb417b28bc545d8a2e84171a8b80c5b882d9316a28b3d4594a2c5516118afcc574a2b64
|8,2=>0x267293254988a4bf525d292d9000004b33257292a5400004a4524fa926d092ca4915246a122149088483123f291e548e8a47132362919d48c4a45d50000116148a6a44f42252911cc884a43e421d990d94862a42c521499091483ea41c320c990550820a40b52049101147fea3fb41fb28fccc7de83eb400000f9947c2a3dc51eba8f49479aa3c85
|8,3=>0x2eb1974ccba065cb52e3297054b78a5b752d9296bccb54a5a552d029674c000059852c9a96448b18a58752c1295f54af0a57352b7295accacca56152aea00000ab4655642a8a95314a926544529fa94ed0a6ca5333297294acca4ca521528e2945d40000000028a1943d4a14a5055280a13f149f084f352772800009d2a4e452709937149b084d35
|8,4=>0x37619b9d4dc4a6df336d29b590da486cf3365a1b194d82a6bc535ba9ac94d5aa6a8500001a8d4d3e869a534b21a454d1c66895342299fd4cf4a6755000019c14cd6a6665330a80000cb8a6575329299354c9466464320a98f14c6ea6325316a98a14c46a61e530ca98550c20a60b5303a18094bfc85f952fb197c54bd8a5e752f129779000005d95
|8,5=>0x400a9ff8cff2a7f453f7a9fa94fcc87e153eea1f6c8fb067d443e821f34cf90a00003e1a9ef94f72a7b453d7a9eb0cf5087a353d019e6d4f2ca79153c6a1e214f06a77f43bda1dd94ee2a76c53b3a9d894ebaa75853aa99d414e98874843a1a9d00ce76a7365399200000e5aa7285391a9c7d0e34a715538829c2d4e0e8702537ea9be14de6a6ef4
|8,6=>0x4802a3f111f268f63000023c551d8a8e75471a238491ba88d8546a9a3415196a8c74461a22f9517848b9345a2a2cc515ca8ab34532a285513c6899544a2a23d5114a8855440a21f150f0887354372a1a550cc6863342fa000010ba485b242b2a15450a2884c5423aa110d07ea83a541b220c55058a827500002089503c8819540a2a03d5014a8064
|8,7=>0x27f9400009f954fa2a7bd53d4a9e644f0aa77153b089d624e8aa731539089c354dfa26e9536aa9b234d79a6a9534aa9a2300000000133aa99944caa26415316a98744c1a2600d2f6a97654b8aa5b152d0896354af2a56552ac6952400000000129e694b44a32a505527a8939449b1a4c5525a892944931a4855238a917548a1a43d5214a9055
|9,0=>0x57f22be915ec8af2457722ba915cc8ae2456f22b6915ac8ad2456722b29158e6ac3455fa2aed156e8ab34557a2aad154e8aa3454fa2a6d152e8a934547a2a2d150e8a83453fa29ed14ee8a734537a29ad14ce8a63452fa296d14ae8a534527a292d148e8a43451fa28ed146e8a334517a28ad144e8a23450fa286d142e8a134507a282d140e8a034
|9,1=>0x5fd22fd917e48bee45f522f9917c48bde45ed22f5917a48bce45e522f1917848bbe45dd22ed917648bae45d522e9917448b9e45cd22e5917248b8e45c522e1917048b7e45bd22dd916e48b6e45b59ad9d16c68b5f45ada2d5d16a68b4f45a5a2d1d16868b3f459da2cdd16668b2f4595a2ca0d6488b20458e22c68962c8b12458722c29160c8b024
|9,2=>0x67ba33cd19de8ced2674a339519c28cdd466ca335519a28ccd4664a331519828cbd465ca32d519628cad4654a329519428c9d464ca325519228c8d4644a321519028c7d463ca31d518e28c6e36352319918c48c5e462d2315918a48c4e46252311918848c3e461d230d918648c2e46152309918448c1e460d2305918248c0e46052301918048bfe4
|9,3=>0x6fba37cd1bde8deb46f3a378d1bbe8ddb46eba374d1b9e8dcb46e3a370d1b7e8dbb46dba36cd1b5e8dab46d3a368d1b3e8d9b46cba364d1b1e8d8b46c3a360d1afe8d7b46bba35cd1ade8d6b46b3a358d1abe8d5b46aba354d1a9e8d4b46a3a350d1a7e8d3b469ba34cd1a5e8d2b4693a348d1a3e8d1b468ba344d1a1e8d0b4683a340d19fe8cfb4
|9,4=>0x77aa3bc51dda8ee94772a3b851dba8ed9476aa3b451d9a8ec94762a3b08dd7c8eba475b23ac91d5c8eaa475323a891d3c8e9a474b23a491d1c8e8a474323a091cfc8e7a473b239c91cdc8e6a4733239891cbc8e5a472b239491c9c8e4a4723239091c7c8e3a471b238c91c5c8e2a4713238891c3c8e1b370ba384d1c1e8e0b4703a380d1bfe8dfb4
|9,5=>0x7faa3fc51fda8fe947f2a3f851fba8fd947eaa3f451f9a8fc947e2a3f051f7a8fb947daa3ec51f5a8fa947d2a3e851f3a8f9947caa3e451f1a8f8947c2a3e051efa8f7947baa3dc51eda8f6947b2a3d851eba8f5947aaa3d451e9a8f4947a2a3d051e7a8f39479aa3cc51e5a8f294792a3c851e3a8f19478aa3c451e1a8f094782a3c051dfa8ef94
|9,6=>0x879a43bd21d690e74871a437d21b690d74869a433d219690c74861a42fd217690b74859a42bd215690a74851a427d213690974849a423d211690874841a41fd20f690774839a41bd20d690674831a4180e0b89058482a241412098904848222410120789038481a240c12058902848122408120389018480a2404120189008480224004dffa8ff94
|9,7=>0x45b922d4916648b12457922b4915648a9245392294914648a1244f9227491364899244b92254912648912447ce23691174889a443d221691074881a43fd21f690f74
|10,0=>0x9179c8b0e452722639119c880e43a721a390b9c850e422720e39059c820e40a720238ff9c7f0e3f271f638f99c7c0e3da71ea38f39c790e3c271de38ed9c760e3aa71d238e79c730e39271c638e19c700e37a71ba38db9c6d0e36271ae38d59c6a0e34a71a238cf9c670e332719638c99c640e31a718a38c39c610e302717e38bd9c5e0e2ea71723
|10,1=>0x9779cbb0e5d272e639719cb80e5ba72da396b9cb50e5a272ce39659cb20e58a72c2395f9caf0e57272b639599cac0e55a72aa39539ca90e542729e394d9ca60e52a729239479ca30e512728639419ca00e4fa727a393b9c9d0e4e2726e39359c9a0e4ca7262392f9c970e4b2725639299c940e49a724a39239c910e482723e391d9c8e0e46a72323
|10,2=>0x9d19ce80e73a739a39cb9ce50e722738e39c59ce20e70a738239bf9cdf0e6f2737639b99cdc0e6da736a39b39cd90e6c2735e39ad9cd60e6aa735239a79cd30e692734639a19cd00e67a733a399b9ccd0e662732e39959cca0e64a7322398f9cc70e632731639899cc40e61a730a39839cc10e60272fe397d9cbe0e5ea72f23
|11,0=>0x5008a80053fe29fe14fe8a7f053f629fa14fc8a7e053ee29f614fa8a7d053e629f214f88a7c053de29ee14f68a7b053d629ea14f48a7a053ce29e614f28a79053c629e214f08a78053be29de14ee8a77053b629da14ec8a76053ae29d614ea8a75053a62
|12,0=>0x140c1a058d028681234081a038d018680a34041
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 17
def pmP:Nat→Nat
|0=>0x2200000000000000020000000000000000110000000000000001030000000000000010200000000000000100000000000000000e4000000000000000e0000000000000000a6000000000000000a4000000000000000a00000000000000008800000000000000080000000000000000480000000000000004400000000000000042000000000000000400000000000000002a000000000000000220000000000000002100000000000000020000000000000000180000000000000001400000000000000012000000000000000100000000000000000a000000000000000080000000000000000600000000000000004000000000000000020000000000000000100000000000000000
|1=>0xc8000000000000000c2000000000000000c0000000000000000a8200000000000000a6000000000000000a24000000000000008a000000000000000884000000000000008800000000000000084000000000000000820000000000000008180000000000000080a0000000000000080100000000000000800000000000000006a000000000000000624000000000000006040000000000000060200000000000000600000000000000005680000000000000054200000000000000480000000000000004220000000000000042000000000000000404000000000000004020000000000000040100000000000000400000000000000002a00000000000000024000000000000000221
|2=>0x200000000000000001e8000000000000001ca000000000000001c220000000000000189200000000000001620000000000000016080000000000000160200000000000001600000000000000014a00000000000000142800000000000001422000000000000014200000000000000140200000000000001400000000000000012220000000000000122000000000000001200000000000000010a8000000000000010a0000000000000010810000000000000108000000000000001022000000000000010200000000000000100000000000000000ea400000000000000ea000000000000000e0000000000000000da200000000000000cb400000000000000cb200000000000000ca0
|3=>0x8002000000000000050900000000000000408000000000000003510000000000000034940000000000000341000000000000002da000000000000002d8200000000000002cb000000000000002c14000000000000029a1000000000000029820000000000000286800000000000002821000000000000028200000000000000258000000000000002528000000000000024900000000000000248200000000000002420000000000000024100000000000000240000000000000002100000000000000020a20000000000000208200000000000002040000000000000020220000000000000202100000000000002020000000000000020100000000000000200800000000000002002
|4=>0x1082100000000000010820000000000000108140000000000001081200000000000010802000000000000106680000000000001065000000000000010640000000000000106240000000000001052900000000000010502000000000000104a600000000000010440000000000000104350000000000001040200000000000010110000000000000101020000000000001010000000000000010068000000000000100400000000000001002600000000000010022000000000000100200000000000001000400000000000010002000000000000100000000000000000ace20000000000000aca600000000000008d2600000000000008c7400000000000008c3600000000000008542
|5=>0x1298200000000000012980000000000000128a00000000000001282000000000000012800000000000000125a4000000000000125a20000000000001252e000000000000125260000000000001252200000000000012480000000000000124620000000000001246000000000000012452000000000000124340000000000001242200000000000012420000000000000120220000000000001201000000000000012002000000000000120000000000000001140000000000000010d6200000000000010d0200000000000010cf500000000000010c3800000000000010aaa00000000000010a24000000000000109a0000000000000108a0000000000000108390000000000001082c
|6=>0x230a2000000000000228ac000000000000224d0000000000000221a3000000000000220880000000000002200000000000000020d6900000000000020ca8000000000000209e800000000000020400000000000000202c0000000000000201210000000000002010100000000000020080000000000000200400000000000002001000000000000020008000000000000200000000000000001acb4000000000000188a6000000000000184e4000000000000164a000000000000012da200000000000012d8000000000000012d3000000000000012ca200000000000012ca000000000000012c3a00000000000012c1200000000000012c0200000000000012c00000000000000129a0
|7=>0x80a280000000000008082800000000000080820000000000000805200000000000008040100000000000080222000000000000802200000000000008020000000000000080040000000000000800220000000000008002100000000000080020000000000000800100000000000008000100000000000052d3100000000000050a0000000000000047880000000000000450b0000000000000450a000000000000045090000000000000448820000000000004488000000000000040a40000000000000408000000000000004008000000000000030f2800000000000030d2800000000000030ce80000000000003086c000000000000300e40000000000003004000000000000023490
|8=>0x200010000000000002000080000000000020000400000000000180020000000000001440800000000000014008000000000000122100000000000001220000000000000012040100000000000120004000000000001124880000000000010408000000000000102004000000000001002200000000000010002100000000000100020000000000001000010000000000010000000000000000090c2000000000000088d2a00000000000088d2800000000000081e2000000000000081aa000000000000081a2000000000000081a00000000000000816220000000000008162000000000000081201000000000000810a40000000000008108400000000000080e2800000000000080aa8
|9=>0x232da300000000000232ce800000000000220929000000000002208c800000000000210ea400000000000210d5400000000000210cd100000000000210cd000000000000210ca100000000000210c4800000000000210c0100000000000210886000000000002108040000000000021062400000000000203cc2000000000002034e40000000000020340200000000000202cc20000000000020286800000000000202860000000000002025e800000000000202529000000000002024900000000000020240800000000000200c6800000000000200c12000000000002008b400000000000200800000000000002004d5000000000002004300000000000020028400000000000200024
|10=>0x460121000000000004224a100000000000412ca00000000000041148000000000000401e0400000000000401e00000000000004016800000000000040162000000000000401604000000000004016000000000000040140000000000000401220000000000004010210000000000040100000000000000400e1000000000000400e000000000000040060400000000000400600000000000004004200000000000040040200000000000400400000000000004002000000000000040000400000000000400001000000000002c080800000000000292ca100000000000270ca100000000000260c9300000000000250e3800000000000243cc300000000000242c8100000000000240501
|11=>0x20014a0000000000020014200000000000200109300000000002000e2000000000002000de300000000002000d8d00000000002000d8500000000002000ced00000000002000cb700000000002000cab00000000002000c65000000000020008f100000000002000545000000000020004bb000000000020004b300000000002000453000000000020002810000000000200021500000000002000103000000000020000a0000000000020000810000000000200005d0000000000200000100000000001aa21a800000000001a9242c00000000001a248c4000000000018340e200000000001812ca100000000001812c8100000000001012c81000000000010084a100000000000460810
|12=>0x20121820000000000201208200000000002010fb500000000002010dab00000000002010da100000000002010cb100000000002010cab00000000002010ca5000000000020108650000000000200cde700000000002008de900000000002008dab00000000002008cf900000000002008cb70000000000200892f000000000020088c700000000002008571000000000020081e700000000002008117000000000020041ef00000000002003cf500000000002002db900000000002002da200000000002002cf300000000002002ca3000000000020029e10000000000200258100000000002002513000000000020024b1000000000020024590000000000200242b00000000002002097
|13=>0x2080dbd00000000002080daf000000000020801ef000000000020800200000000000208000000000000002060dab00000000002047080000000000020458810000000000204548100000000002044de7000000000020440e600000000002040de900000000002040dab00000000002040cf5000000000020404010000000000204010300000000002030ee800000000002030ebd00000000002030a2a00000000002030440000000000020228a40000000000202241400000000002020eed00000000002020de500000000002020961000000000020200d500000000002012db500000000002012da200000000002012d3b00000000002012d210000000000201253200000000002012530
|14=>0x2414c100000000000241140000000000002408df300000000002408df100000000002401ea100000000002401ea00000000000240162100000000002400e1000000000002400c810000000000240057d00000000002400571000000000024004000000000000240000000000000002260ceb000000000022408f100000000002220dd300000000002210d3d00000000002210c5000000000002203de300000000002202cdb0000000000220202800000000002200eb70000000000220090b0000000000220054900000000002145c8100000000002111d0100000000002102ca100000000002100cb9000000000020c01ad00000000002081ea000000000002081ca000000000002081a21
|15=>0x3872d8d00000000003862ce900000000003860da500000000003860cb900000000003860cb200000000003852da500000000003850cb100000000003842db100000000003842da100000000003842cf100000000003840ca100000000003833cb100000000003832d8d00000000003832c8100000000003830eaa00000000003830db100000000003830ca600000000003823ce500000000003814ca300000000003812ce900000000003812ce500000000003812ca10000000000381257100000000003810cb100000000003802ca700000000003802ca2000000000032109710000000000302346300000000002800021000000000026004c1000000000024a0cad00000000002440df5
|16=>0x4210cb000000000004210c30000000000042109040000000000401001800000000004010010000000000040022a10000000000400100100000000004000c0000000000004000800000000000040004600000000000400040400000000003e00da100000000003c01ea000000000003a82ca900000000003a70da100000000003a60ce300000000003a60cb400000000003a608c700000000003a528a100000000003a50da300000000003a43de100000000003a43cf000000000003a23cb000000000003a23c6700000000003a12ca200000000003a10e1a00000000003a10ca000000000003a04ca500000000003a02cb200000000003a025d000000000003a00ce100000000003a00ca2
|17=>0xa800da50000000000a800da30000000000a800da10000000000a800cfd0000000000a800cf90000000000a800cf10000000000a800ceb0000000000a800ce50000000000a800cbb0000000000a800cb50000000000a800cb30000000000a800ca90000000000a800ca30000000000a800ca100000000009c12ca1000000000088008000000000000880040000000000008800080000000000088000200000000000880001800000000008800012000000000088000100000000000880000200000000007a304a100000000007800eb400000000006200da100000000006010ca500000000006000ea300000000005a10aa100000000004610af000000000004401400000000000044000c1
|18=>0xb812da10000000000b812cad0000000000b812ca90000000000b812ca30000000000b812ca10000000000b810da50000000000b810da10000000000b810cf10000000000b810cb10000000000b810ca30000000000b810ca10000000000b802db10000000000b802da30000000000b802ce90000000000b802ce30000000000b802cb10000000000b802ca90000000000b802ca70000000000b802ca50000000000b802ca30000000000b802ca10000000000b800ea10000000000b800df10000000000b800cbb0000000000b800cb90000000000b800cab0000000000b800ca10000000000ac00ca10000000000a804ca10000000000a800db70000000000a800dad0000000000a800dab
|19=>0xb870d290000000000b870ce90000000000b870cad0000000000b863ce50000000000b862ce30000000000b862cb10000000000b862cad0000000000b862ca70000000000b862ca30000000000b860ce50000000000b860cb50000000000b860ca90000000000b860ca30000000000b860ca10000000000b845ca10000000000b840dad0000000000b840da50000000000b840cad0000000000b832da10000000000b832cad0000000000b830da90000000000b830cb10000000000b823ce70000000000b823cb50000000000b820da10000000000b820ce50000000000b812df10000000000b812db10000000000b812dad0000000000b812da90000000000b812da50000000000b812da3
|20=>0xba40ca10000000000ba12de10000000000ba12db10000000000ba12cf10000000000ba12ce10000000000ba10eb90000000000ba10c390000000000ba03ce70000000000ba03ce30000000000ba02df10000000000ba02de10000000000ba02cf10000000000ba02ce10000000000ba00ca10000000000b972ca50000000000b962dad0000000000b962cad0000000000b962ca50000000000b922da50000000000b922cad0000000000b922ca50000000000b903ca10000000000b901ca10000000000b900ca10000000000b8b0ca90000000000b892da10000000000b880da10000000000b880ca90000000000b880ca10000000000b872da90000000000b872da50000000000b870dad
|21=>0xfa10eb10000000000fa00ca10000000000f810ca10000000000f800ce10000000000bc01ea10000000000bc00ca10000000000ba70eb30000000000ba70ea90000000000ba70cb30000000000ba63ce50000000000ba63ce30000000000ba62ca30000000000ba60da30000000000ba60da10000000000ba60ce50000000000ba60cbb0000000000ba60cb30000000000ba60ca30000000000ba60ca10000000000ba52da10000000000ba50de10000000000ba50ce10000000000ba50cb10000000000ba42da10000000000ba42ca70000000000ba42ca10000000000ba40db10000000000ba40da30000000000ba40da10000000000ba40ce10000000000ba40ca70000000000ba40ca5
|22=>0x101a90c2400000000101a23c2200000000101832c8d0000000010000008000000000040000802000000000200008a00000000001b800ca100000000013c8488000000000013c8482000000000013c8442000000000013840ea100000000012402de10000000001240252100000000012040ea100000000012040cbf0000000001204089b00000000012010c1000000000012008cbb00000000012002ce500000000012000cbf000000000120008df00000000010040e0000000000010040c2100000000010040aa100000000010040a200000000001004082000000000010032ca000000000010030ca0000000000100228a000000000010010c2000000000010000c380000000000fc10ce1
|23=>0x10b923ce50000000010b888ca10000000010b81ade10000000010b81ada10000000010b81aca90000000010b818da20000000010b818ca50000000010b810ca30000000010b80cca10000000010b80acb40000000010b808dad0000000010b808da50000000010b808da30000000010b808da10000000010b808cb50000000010b808cad0000000010b802ca10000000010b800ce70000000010b800ce50000000010b800cb30000000010b800cb10000000010b800ca30000000010b800ca10000000010981ada50000000010981ada10000000010981aca300000000103c844a000000000103808ce700000000103808ce300000000103808cb900000000103800ca100000000103800c81
|24=>0x20b804ca10000000020b801ea10000000020ac00df90000000020ac00df30000000020a880dfd0000000020a880dbf0000000020a880dad0000000020a804def0000000020a804de70000000020a804cff0000000020a804cf700000000203e60cf000000000203ac2da500000000202460de500000000202460cf300000000202400cf10000000020240000100000000202080d8500000000202004ce3000000002000140240000000020000160000000000200001280000000002000012020000000020000120100000000200001040000000001cb810ca1000000001c3800830000000001400001a00000000011bc8cca100000000111810c220000000010fa10eb10000000010b982ca9
|25=>0xd0000040400000000d000000200000000090000080000000000501808c21000000004000000040000000031b800cbb0000000030b888dad0000000030b818ce7000000003000000800000000021ba60cbb0000000021b860cbb0000000021b840ebb0000000021ac84ca10000000021a800cbb00000000213c84ca100000000213a02cb200000000213812cb900000000212002db900000000212002cf3000000002100020820000000021000202800000000210000a000000000020be42df10000000020be40df10000000020bc10df10000000020bc00ca10000000020bac0dad0000000020b892dad0000000020b880dad0000000020b866ce70000000020b814ce70000000020b806ce7
|26=>0x500a8008f10000000420b800ca10000000400b800ca50000000400b800ca30000000400b800ca100000004009800ca100000004008000cb400000004008000000000000031eb800ca10000000316b800ca9000000021eb800ca9000000021e00008310000000216b810da10000000216b810ca1000000021400001a000000002109818ca200000002109818ca1000000021002008b100000002040000c8200000002040000c220000000200000058900000001d0b800da10000000190b800cb1000000011cb800cb1000000011ab800ca10000000118b800ca30000000116b800ca50000000114b808ca10000000112b800da100000001002800ca10000000100200808100000000d00000424
|27=>0x1152b8004a30000001056b80aca10000001016b818ca90000001010981adad000000101002004b10000001010020000100000010009812da100000010000002581000000100000004200000000b52b800da10000000b1620009b10000000b12b800da00000000b12b800ca100000009d2b800ca10000000992b800ca30000000952b8004b1000000091e20008b1000000091a30008b1000000090a200083000000008d000008220000000870000008000000008600000000000000085000008a2000000084000004a0000000084000000000000000810b80ada90000000810b80ada100000008000103485000000080000004000000000510a800df10000000500a800d890000000500a8009f1
|28=>0x2000b832ca90000002000b830eb90000002000b830eab0000002000b830ea90000002000b830ca90000002000b800ca1000000200060208a900000020003820ce900000020003810ce9000000200020806810000002000203096800000020002020e8900000020002020ce100000020002020ca9000000200020200a900000020002010cb100000020002010ca500000020002010429000000200018304a1000000200001c0401000000200001009200000002000008182000000020000081801000000200000309680000002000002048900000020000010c890000002000000082000000020000000060000000200000000050000001316b800ca10000001156b808ca50000001152b808ce1
|29=>0x40003810ca900000040003802ca8000000400038018a1000000400020420e1000000400020039e1000000400020030e100000040002002c6500000040002001ca900000040002000da9000000400004129b000000040000400a0100000040000400081000000400002024d000000040000202000000000400002010b0000000400002008e10000004000020004000000040000000cb8000000400000004a8000000400000004900000004000000040800000040000000400000000400000000a10000004000000008000000022001800e810000002010b830da900000020109832ca90000002001f850ea30000002001b870ea90000002000f800ca10000002000ba70ea90000002000b9e0da1
|30=>0x10810b80acf00000010216b810cb10000010152a808c650000010010b812da10000010010b810cb30000010010b810cb10000010010b80acf100000100000102425000001000000204b90000008952b8004a30000008156b800ca30000008150a808c270000008150a80884700000080508808c43000000804000000010000008030b806ce70000008014b808ca3000000800000000000000004810ba03ce10000004010b947ca300000040103a03c2300000040103a028f100000040101b23c210000004000fa52cf10000004000f800da10000004000be02ce10000004000bb23ce50000004000ba12de10000004000ba03ce10000004000b800ca1000000400046429e000000040003a138a1
|31=>0x100400a800dad0000100400a800da50000100400a800da10000100400a800ce70000100400a800ce50000100400a800cb10000100400a800cad0000100400a800cab0000100400a800ca30000100400a800ca100001004008800da200001004008800ce8000010040088000200000100400880000000001004008000da20000081156b808ca10000081152b808ca10000081016b808cb1000008101688084390000080116a8084b90000080114b808cb10000080112b808ca10000080014b818ca10000040114b808cb1000004005038084240000020020bc00df10000020000b800ca20000020000b800ca1000002000010000000000012010b830ca90000011156b800ca10000011016b818cb1
|32=>0x80000400b800ca70040800400b800ca10020800400b800ca1001000807000000000010000150b808ca10008000400bc00df10008000400b800df10008000400b800db10008000400b800cf10008000400b800cb10008000400b800ca10004000152b800cb10004000030bc0adf10002000112b800da1000200001200000220001000400b800ca10000800400b800ca10000600000b800ca10000600000a800da10000600000a800ce10000600000a800ca30000600000a800ca10000600000a000dad0000600000a000cbb0000100510a800da10000100510a800cbb0000100510a800cb10000100510a800ca30000100510a800ca10000100500a800c670000100500a800c650000100500a800c27
|33=>0x8000000400b800da15400000420b880dad4000800400b800ca13100000421b800cbb0801000400b800ca10420000400b800ca10200000401b800cbb0200000400b800cb10200000400b800ca30200000400b800ca10100000400b800da10100000400b800ca10080000400b800ce70080000400b800ce5
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0xa00000002000
|7,0=>0x6000000800460480000b0002c80808e00008c000d3000000000000000000006204609c0781f016084000000120440100f10e2280411d0260004300000a0f80005200c08c0282303a04c010e802203c000310c202c740cf10e23001806006220118390000000106121c0d80000000806c1680000a04c3101e01c0000380004608c0000000019800004046000058060261f40f8001a003c18800006028038da000000000350000000380000e18043031
|7,1=>0xd0050000000002d0f40001441182309c0440000200003c0000a2a40003f8140a611c00000000440558000384401880b0000000008b
|8,0=>0x6e0084790c22ccb1b1a0e0300a8bf3b23c4000189d92aa4844f140000208449390022b8888002880e9d58f136e630eaba943463c2b8a40264e9d5b4204e4d9d511b10624c2591e5ba02c118e7656e9c971e50c002c6e9550d0b18120de70859800118208c08a71b1090270449c343817c238d028e53dbd0651c40301784d18ee0d7012a0b2d2c662196ee47c568551a427c248481680151810b16eb8415bce43ab0db39d6206358068440464f4049bd
|8,1=>0xe15c760a10b675182094168344e01ac698eac000c425686cb21b01aeb91b216e14a855eb9680260007491a0cecfc03a2c2fa0ec3787d04ef8c4093c40c1ac000002927a5bc0b323c78c0597a2820001915a0364cc0690f3021146a0dc2142b0000232e4b04000a95be884668ca7a26389201a2905bc618020e85b4b01170005cc500311220156b1190d436dc2b0510ef9c5c0900160c44a9a623e248588712460259b848000530299840d82cc4c8ed
|8,2=>0x2ca4484685e1be4d0dd8272ac1a427adc0460b0d58006f060c2b04b61002de8959036b5d1736d0a83c8ac2172384807aa025b4130af0200123640a013322094cf2cf0620016da5e1303e41a9435bc0fc0d8977b014c718230161b8578f7066450a5809046b20750291ca63475b0c000f48a5a2f17677c0398221a3c0a42d30001f0008bc0020799f36010a32df19d313a424e41cb320b08421582d852c008a7062fb4301c900a1b4581bc6a8128000bd
|8,3=>0x5a87c1b833c09c3d0270485a4e9913682b400a819750b241804f67700893007000000b83581f21d89a823016da9638341ecb619e96b2503840fb5800000006831678790550262964a4058512968b42037c01a190112cb2dc08c0385009c8ac1216209e2ac1703d2ae05cac8360a8168038f35ca338008fa2be6883f1421366001c0012a069c2c1610b4354160230a200034baf36a015ac0271440b0b39971ce1cc9112f2944100587712c299e9823
|9,0=>0x38891500b513b679dc73de45a80d4e30e32a5d9cb3d9530f00d4bbe4466d9b0b8a37498cee13b3c2315770d8768e5dda9256146747787248a6b9911053e21d4c910038e61a07988258c2d4b0fc454c2607b994f8cbd442057c8731c43874409e10fbc77343807da8850cd0cad9a82a6f81692ce08ca01afbe9576bf9ea159692ce1ef9f24be175e12c4368670ff34420ac614c8fd3c0acc2207b662c01f420d2b8d212483c836860e2a0b3f2bf4cd1fc
|9,1=>0x4504c2048ff39c6654131a43cec4c9bbb462ecc814117228451697b184c4d8882819304c6422a1746e4609ff718a16073a2760a75c78b93284b50a1797cccb9211515a42fde58785a87addf90145261c383687b8bed022cc2e289ca33071c8744cb0a837ed54f407971aae9b4bf250ec50963626ccee0d027f4d89158b3ec572ac0d0b106528b8319066dc2dd7fb1b5788c1051083b06a96d1b36b6e99650fe02c3b421b6f4d27789c1ef4f2e60e7b5b
|9,2=>0x5a267dbebcd72009d7184635a81dadbcc7bade4a6a004fae50fe9ee61e979bda834aa7c09fc006e09acfa1c654e7d9de8e65567098695d2e8625c49377b64c8bc41e716a057b35a660840bb89a4aaa78ac3cf330b651304560ceb5321f575c28d968eb5f466d0940174a550e53ca6b6799ac8b57f8ede03265454751c91153ae318be3b918f040df3867dcca95b8b6510fcd62af56627b1421f8418f95de3453d4bdd098ee48a421f5ab53a4d35c9b75
|9,3=>0xfc8ed3c94108f0b193163c955ba3f148a69181b0f3467e89f0273b641cc2c193bb074d2a166a6890bfbe2842d414b1273e6d18e832481c825cd2937a0ee8c598a2eadb02140856c09c2e14562507171245082980e6a486feba1193955aa02da01f756283d9b27017c7b57334a6b6b28d927e59aeb0e0b5b3f6ffdeb2254c4dada724a
|10,0=>0x78c301e24286ba971602954aea5d22c1f80ea299cc2b570a353bc2a4ce88a1626e4d0bd1cdaec54aa42103f96bc9752b246536d79eaa7276c9c9562f364e8e58eb20846dd941b5649cac55eb8173ec5557af9554fa9a7a527f89d9ceaa4512905223da5229d523b1f66a9dd219af46ee8d2fa627f09a959a6184e9611dbf47c2e85b925a73890214aa96fca31e1323550f21a3a6062e9d15f38273c9ed2faf06b70519a27a5f0e012aaab818a6936a8f
|10,1=>0x5ced71fdc0b4ccc99212ae7c8f06092a15daccd78b3a80b0698e3216e6aca06a4b7489915a2514be951d0271808fbe0bb2551c9bda93ff516691e2b28602ff929a9450cdc60c2557ea979e1b5b49ebf155365
|11,0=>0xa8d754227fa96d572555e4a491c23666497e1335b4e6d5d534254b294156bf04bf0291d24d540fe92642d6328fd77c1646a92dfba9347c9c9512bf806badada8e
|12,0=>0x424466a7dfb23d82aba52aa34
|13,0=>0x232
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 11 (j%128);fld (pmP (k/32)) 68 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_253 12 roots_253 ops++addP pm 1 dom_246 9 roots_246 ops++addP pm 2 dom_183 9 roots_183 ops++addP pm 3 dom_215 9 roots_215 ops++addP pm 4 dom_222 9 roots_222 ops++addP pm 5 dom_254 11 roots_254 ops++addP pm 6 dom_190 9 roots_190 ops++addP pm 7 dom_223 11 roots_223 ops++addP pm 8 dom_159 9 roots_159 ops++addP pm 9 dom_86 4 roots_86 ops++addP pm 10 dom_247 11 roots_247 ops++addP pm 11 dom_191 11 roots_191 ops++addP pm 12 dom_54 4 roots_54 ops++addP pm 13 dom_63 8 roots_63 ops++addP pm 14 dom_182 6 roots_182 ops++addP pm 15 dzo_157_2 6 roots_157 ops++addP pm 16 dom_95 8 roots_95 ops++addP pm 17 dom_119 8 roots_119 ops++addP pm 18 dom_118 7 roots_118 ops++addP pm 19 dom_151 6 roots_151 ops++addP pm 20 dom_55 5 roots_55 ops++addP pm 21 dom_126 8 roots_126 ops++addP pm 22 dom_158 6 roots_158 ops++addP pm 23 dom_251 12 roots_251 ops++addP pm 24 dzo_111_16 9 roots_111 ops++addP pm 25 dom_127 11 roots_127 ops++addP pm 26 dom_94 5 roots_94 ops++addP pm 27 dom_239 11 roots_239 ops++addP pm 28 dom_214 6 roots_214 ops++addP pm 29 dzo_253_2 8 roots_253 ops++addP pm 30 dzo_221_2 7 roots_221 ops++addP pm 31 dom_61 6 roots_61 ops++addP pm 32 dom_125 9 roots_125 ops++addP pm 33 dom_150 5 roots_150 ops++addP pm 34 dzo_189_2 7 roots_189 ops++addP pm 35 dom_93 6 roots_93 ops++addP pm 36 dzo_109_16 8 roots_109 ops++addP pm 37 dom_189 10 roots_189 ops++addP pm 38 dzo_239_16 10 roots_239 ops++addP pm 39 dom_221 10 roots_221 ops++addP pm 40 dom_245 10 roots_245 ops++addP pm 41 dom_87 5 roots_87 ops++addP pm 42 dom_62 5 roots_62 ops++addP pm 43 dom_244 8 roots_244 ops++addP pm 44 dom_252 10 roots_252 ops++addP pm 45 dzo_237_16 9 roots_237 ops++addP pm 46 dom_124 6 roots_124 ops++addP pm 47 dom_117 6 roots_117 ops++addP pm 48 dom_107 8 roots_107 ops++addP pm 49 dzo_251_4 10 roots_251 ops++addP pm 50 dzo_235_4 9 roots_235 ops++addP pm 51 dzo_231_16 7 roots_231 ops++addP pm 52 dzo_207_16 7 roots_207 ops++addP pm 53 dom_157 8 roots_157 ops++addP pm 54 dom_220 8 roots_220 ops++addP pm 55 dom_231 9 roots_231 ops++addP pm 56 dom_180 5 roots_180 ops++addP pm 57 dzo_238_16 7 roots_238 ops++addP pm 58 dzo_175_16 7 roots_175 ops++addP pm 59 dom_207 9 roots_207 ops++addP pm 60 dom_230 7 roots_230 ops++addP pm 61 dom_175 9 roots_175 ops++addP pm 62 dom_167 6 roots_167 ops++addP pm 63 dom_174 6 roots_174 ops++addP pm 64 dom_199 6 roots_199 ops++addP pm 65 dom_206 6 roots_206 ops++addP pm 66 dom_141 5 roots_141 ops++addP pm 67 dom_238 9 roots_238 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_255 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45|h46|h47|h48|h49|h50|h51|h52|h53|h54|h55|h56|h57|h58|h59|h60|h61|h62|h63|h64|h65|h66|h67
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_223 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_247 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_191 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_157_2_141 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_zo_111_16_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_127 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_zo_253_2_141 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_zo_221_2_141 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_150 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_zo_189_2_141 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_zo_109_16_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_189 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_zo_239_16_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_221 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h45;exact cpcs (by decide +kernel) lowS_zo_237_16_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h46;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h47;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h48;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h49;exact cpcs (by decide +kernel) lowS_zo_251_4_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h50;exact cpcs (by decide +kernel) lowS_zo_235_4_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h51;exact cpcs (by decide +kernel) lowS_zo_231_16_97 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h52;exact cpcs (by decide +kernel) lowS_zo_207_16_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h53;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h54;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h55;exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h56;exact cpcs (by decide +kernel) lowS_180 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h57;exact cpcs (by decide +kernel) lowS_zo_238_16_104 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h58;exact cpcs (by decide +kernel) lowS_zo_175_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h59;exact cpcs (by decide +kernel) lowS_207 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h60;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h61;exact cpcs (by decide +kernel) lowS_175 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h62;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h63;exact cpcs (by decide +kernel) lowS_174 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h64;exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h65;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h66;exact cpcs (by decide +kernel) lowS_141 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h67;exact cpcs (by decide +kernel) lowS_238 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_253 12 s (0,roots_253.map (·&&&dom_253)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_253 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_255==dom_255)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 1000003 zs symsG zs (hk 1000003 zs)
theorem ori_ok {v ys} (h:RunD true dom_255 gM v ys):RunD true dom_255 gM v (ori ys):=pickMin_runD 1000003 ys h symsG ys (hk 1000003 ys) symsG_ok h
def Z (s:Nat):=barP dom_255 gM mpG SD SS NN hAt idxH ori 1000003 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 8 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 167 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 39 128 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 167 → Z 7 i = true := (range_split z7_0 z7_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 256 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_256 : ∀ i, 256 ≤ i → i < 384 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 256 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_384 : ∀ i, 384 ≤ i → i < 511 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 127 384 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 511 → Z 8 i = true := (range_split (range_split z8_0 z8_128) (range_split z8_256 z8_384))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_0 : ∀ i, 0 ≤ i → i < 128 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_128 : ∀ i, 128 ≤ i → i < 256 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_256 : ∀ i, 256 ≤ i → i < 384 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 256 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_384 : ∀ i, 384 ≤ i → i < 479 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 95 384 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 479 → Z 9 i = true := (range_split (range_split z9_0 z9_128) (range_split z9_256 z9_384))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_0 : ∀ i, 0 ≤ i → i < 128 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_128 : ∀ i, 128 ≤ i → i < 188 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 60 128 = true)
private theorem z10 : ∀ i, 0 ≤ i → i < 188 → Z 10 i = true := (range_split z10_0 z10_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 47 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 47 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z12 : ∀ i, 0 ≤ i → i < 9 → Z 12 i = true := span_ok (by decide +kernel : span (Z 12) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z13 : ∀ i, 0 ≤ i → i < 1 → Z 13 i = true := span_ok (by decide +kernel : span (Z 13) 1 0 = true)
theorem checked (s:Nat) (hs:s≤13):∀ i<NN s,bar dom_255 gM mpG SD SS NN hAt idxH ori 1000003 mkCut s i=true:=by
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
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [3, 0] }, { op := GateOp.or, inputs := [7, 1] }, { op := GateOp.or, inputs := [8, 9] }, { op := GateOp.or, inputs := [2, 8] }, { op := GateOp.or, inputs := [9, 2] }, { op := GateOp.or, inputs := [5, 6] }, { op := GateOp.and, inputs := [13, 10] }, { op := GateOp.and, inputs := [6, 5] }, { op := GateOp.and, inputs := [12, 4] }, { op := GateOp.and, inputs := [11, 7] }, { op := GateOp.and, inputs := [3, 0] }, { op := GateOp.or, inputs := [14, 15] }, { op := GateOp.or, inputs := [19, 16] }, { op := GateOp.or, inputs := [20, 17] }, { op := GateOp.or, inputs := [21, 18] }]

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 22⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
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

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_51568_aux

theorem PEqualNP.Outside.L_meta_51568 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_51568_aux.main
