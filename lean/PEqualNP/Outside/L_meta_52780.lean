import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_52780_aux
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

def dom_42 : Nat := 0x50500000505
def goal_42 : Nat := 0xffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00
def roots_42 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_43 : Nat := 0xf0f00000f0f
def goal_43 : Nat := 0xffccffccee00ee00ffccffccee00ee00ffccffccee00ee00ffccffccee00ee00
def roots_43 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_45 : Nat := 0x333300003333
def goal_45 : Nat := 0xfff0fff0aa00aa00fff0fff0aa00aa00fff0fff0aa00aa00fff0fff0aa00aa00
def roots_45 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_46 : Nat := 0x555500005555
def goal_46 : Nat := 0xfffcfffccc00cc00fffcfffccc00cc00fffcfffccc00cc00fffcfffccc00cc00
def roots_46 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_47 : Nat := 0xffff0000ffff
def goal_47 : Nat := 0xfffcfffcee00ee00fffcfffcee00ee00fffcfffcee00ee00fffcfffcee00ee00
def roots_47 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_53 : Nat := 0x33003300330033
def goal_53 : Nat := 0xfafaf0f0fafa0000fafaf0f0fafa0000fafaf0f0fafa0000fafaf0f0fafa0000
def roots_53 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_54 : Nat := 0x55005500550055
def goal_54 : Nat := 0xfcfcfcfcf0f00000fcfcfcfcf0f00000fcfcfcfcf0f00000fcfcfcfcf0f00000
def roots_54 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xfefefcfcfafa0000fefefcfcfafa0000fefefcfcfafa0000fefefcfcfafa0000
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_57 : Nat := 0x303030303030303
def goal_57 : Nat := 0xffaaff00aaaaaa00ffaaff00aaaaaa00ffaaff00aaaaaa00ffaaff00aaaaaa00
def roots_57 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xffeeffcceeaaee00ffeeffcceeaaee00ffeeffcceeaaee00ffeeffcceeaaee00
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_60 : Nat := 0x1111111111111111
def goal_60 : Nat := 0xfff0fff0f0f00000fff0fff0f0f00000fff0fff0f0f00000fff0fff0f0f00000
def roots_60 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xfffafff0fafaaa00fffafff0fafaaa00fffafff0fafaaa00fffafff0fafaaa00
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_62 : Nat := 0x5555555555555555
def goal_62 : Nat := 0xfffcfffcfcf0cc00fffcfffcfcf0cc00fffcfffcfcf0cc00fffcfffcfcf0cc00
def roots_62 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfffefffcfefaee00fffefffcfefaee00fffefffcfefaee00fffefffcfefaee00
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_73 : Nat := 0x3030000000000000303
def goal_73 : Nat := 0xffaaffaaffaaffaaaa00aa00aa00aa00ffaaffaaffaaffaaaa00aa00aa00aa00
def roots_73 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_74 : Nat := 0x5050000000000000505
def goal_74 : Nat := 0xffccffccffccffcccc00cc00cc00cc00ffccffccffccffcccc00cc00cc00cc00
def roots_74 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_75 : Nat := 0xf0f0000000000000f0f
def goal_75 : Nat := 0xffeeffeeffeeffeeee00ee00ee00ee00ffeeffeeffeeffeeee00ee00ee00ee00
def roots_75 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_77 : Nat := 0x33330000000000003333
def goal_77 : Nat := 0xfffafffafffafffaaa00aa00aa00aa00fffafffafffafffaaa00aa00aa00aa00
def roots_77 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_78 : Nat := 0x55550000000000005555
def goal_78 : Nat := 0xfffcfffcfffcfffccc00cc00cc00cc00fffcfffcfffcfffccc00cc00cc00cc00
def roots_78 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_79 : Nat := 0xffff000000000000ffff
def goal_79 : Nat := 0xfffefffefffefffeee00ee00ee00ee00fffefffefffefffeee00ee00ee00ee00
def roots_79 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_81 : Nat := 0x300030000000000030003
def goal_81 : Nat := 0xffffaaaaffffaaaaaaaa0000aaaa0000ffffaaaaffffaaaaaaaa0000aaaa0000
def roots_81 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_83 : Nat := 0xf000f00000000000f000f
def goal_83 : Nat := 0xffffeeeeffffeeeeaaaa0000aaaa0000ffffeeeeffffeeeeaaaa0000aaaa0000
def roots_83 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_84 : Nat := 0x1100110000000000110011
def goal_84 : Nat := 0xfffff0f0fffff0f0f0f00000f0f00000fffff0f0fffff0f0f0f00000f0f00000
def roots_84 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_85 : Nat := 0x3300330000000000330033
def goal_85 : Nat := 0xfffffafafffffafafafa0000fafa0000fffffafafffffafafafa0000fafa0000
def roots_85 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_86 : Nat := 0x5500550000000000550055
def goal_86 : Nat := 0xfffffcfcfffffcfcf0f00000f0f00000fffffcfcfffffcfcf0f00000f0f00000
def roots_86 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_87 : Nat := 0xff00ff0000000000ff00ff
def goal_87 : Nat := 0xfffffefefffffefefafa0000fafa0000fffffefefffffefefafa0000fafa0000
def roots_87 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_89 : Nat := 0x30303030000000003030303
def goal_89 : Nat := 0xffffffaaffffffaaaaaaaa00aaaaaa00ffffffaaffffffaaaaaaaa00aaaaaa00
def roots_89 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_90 : Nat := 0x50505050000000005050505
def goal_90 : Nat := 0xffffffccffffffcccc00cc00cc00cc00ffffffccffffffcccc00cc00cc00cc00
def roots_90 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f
def goal_91 : Nat := 0xffffffeeffffffeeeeaaee00eeaaee00ffffffeeffffffeeeeaaee00eeaaee00
def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_92 : Nat := 0x111111110000000011111111
def goal_92 : Nat := 0xfffffff0fffffff0f0f00000f0f00000fffffff0fffffff0f0f00000f0f00000
def roots_92 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_93 : Nat := 0x333333330000000033333333
def goal_93 : Nat := 0xfffffffafffffffafafaaa00fafaaa00fffffffafffffffafafaaa00fafaaa00
def roots_93 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_94 : Nat := 0x555555550000000055555555
def goal_94 : Nat := 0xfffffffcfffffffcfcf0cc00fcf0cc00fffffffcfffffffcfcf0cc00fcf0cc00
def roots_94 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_95 : Nat := 0xffffffff00000000ffffffff
def goal_95 : Nat := 0xfffffffefffffffefefaee00fefaee00fffffffefffffffefefaee00fefaee00
def roots_95 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_99 : Nat := 0xf0000000f0000000f0000000f
def goal_99 : Nat := 0xeeeeeeeeeeeeeeeecccccccc00000000eeeeeeeeeeeeeeeecccccccc00000000
def roots_99 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_101 : Nat := 0x33000000330000003300000033
def goal_101 : Nat := 0xfafafafafafafafaf0f0f0f000000000fafafafafafafafaf0f0f0f000000000
def roots_101 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_103 : Nat := 0xff000000ff000000ff000000ff
def goal_103 : Nat := 0xfefefefefefefefefcfcfcfc00000000fefefefefefefefefcfcfcfc00000000
def roots_103 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_105 : Nat := 0x303000003030000030300000303
def goal_105 : Nat := 0xffaaffaaffaaffaaff00ff00aa00aa00ffaaffaaffaaffaaff00ff00aa00aa00
def roots_105 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_106 : Nat := 0x505000005050000050500000505
def goal_106 : Nat := 0xffccffccffccffccffccffcccc00cc00ffccffccffccffccffccffcccc00cc00
def roots_106 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffeeffeeffeeffeeffccffccee00ee00ffeeffeeffeeffeeffccffccee00ee00
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_109 : Nat := 0x3333000033330000333300003333
def goal_109 : Nat := 0xfffafffafffafffafff0fff0aa00aa00fffafffafffafffafff0fff0aa00aa00
def roots_109 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_110 : Nat := 0x5555000055550000555500005555
def goal_110 : Nat := 0xfffcfffcfffcfffcfffcfffccc00cc00fffcfffcfffcfffcfffcfffccc00cc00
def roots_110 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xfffefffefffefffefffcfffcee00ee00fffefffefffefffefffcfffcee00ee00
def roots_111 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_114 : Nat := 0x50005000500050005000500050005
def goal_114 : Nat := 0xffffccccffffcccccccccccc00000000ffffccccffffcccccccccccc00000000
def roots_114 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def goal_115 : Nat := 0xffffeeeeffffeeeeeeeeccccaaaa0000ffffeeeeffffeeeeeeeeccccaaaa0000
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_116 : Nat := 0x110011001100110011001100110011
def goal_116 : Nat := 0xfffff0f0fffff0f0f0f0f0f0f0f00000fffff0f0fffff0f0f0f0f0f0f0f00000
def roots_116 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_117 : Nat := 0x330033003300330033003300330033
def goal_117 : Nat := 0xfffffafafffffafafafaf0f0fafa0000fffffafafffffafafafaf0f0fafa0000
def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xfffffcfcfffffcfcfcfcfcfcf0f00000fffffcfcfffffcfcfcfcfcfcf0f00000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xfffffefefffffefefefefcfcfafa0000fffffefefffffefefefefcfcfafa0000
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_120 : Nat := 0x1010101010101010101010101010101
def goal_120 : Nat := 0xffffff00ffffff00ff00ff0000000000ffffff00ffffff00ff00ff0000000000
def roots_120 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_121 : Nat := 0x3030303030303030303030303030303
def goal_121 : Nat := 0xffffffaaffffffaaffaaff00aaaaaa00ffffffaaffffffaaffaaff00aaaaaa00
def roots_121 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_122 : Nat := 0x5050505050505050505050505050505
def goal_122 : Nat := 0xffffffccffffffccffccffcccc00cc00ffffffccffffffccffccffcccc00cc00
def roots_122 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffffffeeffffffeeffeeffcceeaaee00ffffffeeffffffeeffeeffcceeaaee00
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_124 : Nat := 0x11111111111111111111111111111111
def goal_124 : Nat := 0xfffffff0fffffff0fff0fff0f0f00000fffffff0fffffff0fff0fff0f0f00000
def roots_124 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xfffffffafffffffafffafff0fafaaa00fffffffafffffffafffafff0fafaaa00
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_126 : Nat := 0x55555555555555555555555555555555
def goal_126 : Nat := 0xfffffffcfffffffcfffcfffcfcf0cc00fffffffcfffffffcfffcfffcfcf0cc00
def roots_126 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xfffffffefffffffefffefffcfefaee00fffffffefffffffefffefffcfefaee00
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_141 : Nat := 0x333300000000000000000000000000003333
def goal_141 : Nat := 0xfafafafafafafafafafafafafafafafaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_141 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_142 : Nat := 0x555500000000000000000000000000005555
def goal_142 : Nat := 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfccc00cc00cc00cc00cc00cc00cc00cc00
def roots_142 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_143 : Nat := 0xffff0000000000000000000000000000ffff
def goal_143 : Nat := 0xfefefefefefefefefefefefefefefefeee00ee00ee00ee00ee00ee00ee00ee00
def roots_143 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_145 : Nat := 0x3000300000000000000000000000000030003
def goal_145 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaaaaaa0000aaaa0000aaaa0000aaaa0000
def roots_145 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_147 : Nat := 0xf000f000000000000000000000000000f000f
def goal_147 : Nat := 0xffffeeeeffffeeeeffffeeeeffffeeeeaaaa0000aaaa0000aaaa0000aaaa0000
def roots_147 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_148 : Nat := 0x11001100000000000000000000000000110011
def goal_148 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0f0f00000f0f00000f0f00000f0f00000
def roots_148 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_149 : Nat := 0x33003300000000000000000000000000330033
def goal_149 : Nat := 0xfffffafafffffafafffffafafffffafafafa0000fafa0000fafa0000fafa0000
def roots_149 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_151 : Nat := 0xff00ff00000000000000000000000000ff00ff
def goal_151 : Nat := 0xfffffefefffffefefffffefefffffefefafa0000fafa0000fafa0000fafa0000
def roots_151 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_153 : Nat := 0x303030300000000000000000000000003030303
def goal_153 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaaaaaaaa00aaaaaa00aaaaaa00aaaaaa00
def roots_153 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_154 : Nat := 0x505050500000000000000000000000005050505
def goal_154 : Nat := 0xffffccccffffccccffffccccffffcccccc00cc00cc00cc00cc00cc00cc00cc00
def roots_154 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def goal_155 : Nat := 0xffffeeeeffffeeeeffffeeeeffffeeeeeeaaee00eeaaee00eeaaee00eeaaee00
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_157 : Nat := 0x3333333300000000000000000000000033333333
def goal_157 : Nat := 0xfffffafafffffafafffffafafffffafafafaaa00fafaaa00fafaaa00fafaaa00
def roots_157 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_158 : Nat := 0x5555555500000000000000000000000055555555
def goal_158 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfcfcf0cc00fcf0cc00fcf0cc00fcf0cc00
def roots_158 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_159 : Nat := 0xffffffff000000000000000000000000ffffffff
def goal_159 : Nat := 0xfffffefefffffefefffffefefffffefefefaee00fefaee00fefaee00fefaee00
def roots_159 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_170 : Nat := 0x5050000050500000000000000000000050500000505
def goal_170 : Nat := 0xffffffffccccccccffffffffccccccccffccffcccc00cc00ffccffcccc00cc00
def roots_170 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_171 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
def goal_171 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeeeffccffccee00ee00ffccffccee00ee00
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_172 : Nat := 0x11110000111100000000000000000000111100001111
def goal_172 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0fff0fff000000000fff0fff000000000
def roots_172 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_173 : Nat := 0x33330000333300000000000000000000333300003333
def goal_173 : Nat := 0xfffffffffafafafafffffffffafafafafff0fff0aa00aa00fff0fff0aa00aa00
def roots_173 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_185 : Nat := 0x30303030303030300000000000000000303030303030303
def goal_185 : Nat := 0xffffffffffffaaaaffffffffffffaaaaffaaff00aaaaaa00ffaaff00aaaaaa00
def roots_185 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_186 : Nat := 0x50505050505050500000000000000000505050505050505
def goal_186 : Nat := 0xffffffffffffccccffffffffffffccccffccffcccc00cc00ffccffcccc00cc00
def roots_186 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffffffffeeeeffffffffffffeeeeffeeffcceeaaee00ffeeffcceeaaee00
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_189 : Nat := 0x333333333333333300000000000000003333333333333333
def goal_189 : Nat := 0xfffffffffffffafafffffffffffffafafffafff0fafaaa00fffafff0fafaaa00
def roots_189 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xfffffffffffffefefffffffffffffefefffefffcfefaee00fffefffcfefaee00
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_193 : Nat := 0x3000000000000000300000000000000030000000000000003
def goal_193 : Nat := 0xffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000000000000000
def roots_193 : List Nat := [xs256.getD 0 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_195 : Nat := 0xf000000000000000f000000000000000f000000000000000f
def goal_195 : Nat := 0xffffffffffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0000000000000000
def roots_195 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_197 : Nat := 0x33000000000000003300000000000000330000000000000033
def goal_197 : Nat := 0xfffffffffffffffffafafafafafafafafafafafafafafafa0000000000000000
def roots_197 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_198 : Nat := 0x55000000000000005500000000000000550000000000000055
def goal_198 : Nat := 0xfffffffffffffffffcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc0000000000000000
def roots_198 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_199 : Nat := 0xff00000000000000ff00000000000000ff00000000000000ff
def goal_199 : Nat := 0xfffffffffffffffffefefefefefefefefefefefefefefefe0000000000000000
def roots_199 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_201 : Nat := 0x303000000000000030300000000000003030000000000000303
def goal_201 : Nat := 0xffffffffffffffffaaaaaaaaaaaaaaaaffaaffaaffaaffaaaa00aa00aa00aa00
def roots_201 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_202 : Nat := 0x505000000000000050500000000000005050000000000000505
def goal_202 : Nat := 0xffffffffffffffffccccccccccccccccffccffccffccffcccc00cc00cc00cc00
def roots_202 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffffffffffffffffeeeeeeeeeeeeeeeeffeeffeeffeeffeeee00ee00ee00ee00
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_205 : Nat := 0x3333000000000000333300000000000033330000000000003333
def goal_205 : Nat := 0xfffffffffffffffffafafafafafafafafffafffafffafffaaa00aa00aa00aa00
def roots_205 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_206 : Nat := 0x5555000000000000555500000000000055550000000000005555
def goal_206 : Nat := 0xfffffffffffffffffcfcfcfcfcfcfcfcfffcfffcfffcfffccc00cc00cc00cc00
def roots_206 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_207 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def goal_207 : Nat := 0xfffffffffffffffffefefefefefefefefffefffefffefffeee00ee00ee00ee00
def roots_207 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_208 : Nat := 0x10001000000000001000100000000000100010000000000010001
def goal_208 : Nat := 0xffffffffffffffffffff0000ffff0000ffff0000ffff00000000000000000000
def roots_208 : List Nat := [xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_209 : Nat := 0x30003000000000003000300000000000300030000000000030003
def goal_209 : Nat := 0xffffffffffffffffffffaaaaffffaaaaffffaaaaffffaaaaaaaa0000aaaa0000
def roots_209 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_210 : Nat := 0x50005000000000005000500000000000500050000000000050005
def goal_210 : Nat := 0xffffffffffffffffffffccccffffccccffffccccffffcccc0000000000000000
def roots_210 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffffffffffffffffffeeeeffffeeeeffffeeeeffffeeeeaaaa0000aaaa0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_212 : Nat := 0x110011000000000011001100000000001100110000000000110011
def goal_212 : Nat := 0xfffffffffffffffffffff0f0fffff0f0fffff0f0fffff0f0f0f00000f0f00000
def roots_212 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_213 : Nat := 0x330033000000000033003300000000003300330000000000330033
def goal_213 : Nat := 0xfffffffffffffffffffffafafffffafafffffafafffffafafafa0000fafa0000
def roots_213 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xfffffffffffffffffffffcfcfffffcfcfffffcfcfffffcfcf0f00000f0f00000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xfffffffffffffffffffffefefffffefefffffefefffffefefafa0000fafa0000
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_216 : Nat := 0x1010101000000000101010100000000010101010000000001010101
def goal_216 : Nat := 0xffffffffffffffffffff0000ffff0000ffffff00ffffff000000000000000000
def roots_216 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_217 : Nat := 0x3030303000000000303030300000000030303030000000003030303
def goal_217 : Nat := 0xffffffffffffffffffffaaaaffffaaaaffffffaaffffffaaaaaaaa00aaaaaa00
def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def goal_218 : Nat := 0xffffffffffffffffffffccccffffccccffffffccffffffcccc00cc00cc00cc00
def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffffffffffffffffffeeeeffffeeeeffffffeeffffffeeeeaaee00eeaaee00
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_220 : Nat := 0x11111111000000001111111100000000111111110000000011111111
def goal_220 : Nat := 0xfffffffffffffffffffff0f0fffff0f0fffffff0fffffff0f0f00000f0f00000
def roots_220 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def goal_221 : Nat := 0xfffffffffffffffffffffafafffffafafffffffafffffffafafaaa00fafaaa00
def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xfffffffffffffffffffffcfcfffffcfcfffffffcfffffffcfcf0cc00fcf0cc00
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffffffffffffffffefefffffefefffffffefffffffefefaee00fefaee00
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def goal_227 : Nat := 0xffffffffffffffffffffffffeeeeeeeeeeeeeeeeeeeeeeeecccccccc00000000
def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_229 : Nat := 0x3300000033000000330000003300000033000000330000003300000033
def goal_229 : Nat := 0xfffffffffffffffffffffffffafafafafafafafafafafafaf0f0f0f000000000
def roots_229 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffffffffffffffffaaaaaaaaffaaffaaffaaffaaff00ff00aa00aa00
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffffffffffffffffccccccccffccffccffccffccffccffcccc00cc00
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffffffffffffffffeeeeeeeeffeeffeeffeeffeeffccffccee00ee00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_236 : Nat := 0x111100001111000011110000111100001111000011110000111100001111
def goal_236 : Nat := 0xfffffffffffffffffffffffff0f0f0f0fff0fff0fff0fff0fff0fff000000000
def roots_236 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xfffffffffffffffffffffffffafafafafffafffafffafffafff0fff0aa00aa00
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_241 : Nat := 0x3000300030003000300030003000300030003000300030003000300030003
def goal_241 : Nat := 0xffffffffffffffffffffffffffffaaaaffffaaaaffffaaaaaaaa0000aaaa0000
def roots_241 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def goal_242 : Nat := 0xffffffffffffffffffffffffffffccccffffccccffffcccccccccccc00000000
def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffffffffffffffffffffeeeeffffeeeeffffeeeeeeeeccccaaaa0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_245 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
def goal_245 : Nat := 0xfffffffffffffffffffffffffffffafafffffafafffffafafafaf0f0fafa0000
def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffffffffffffffffffefefffffefefffffefefefefcfcfafa0000
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_248 : Nat := 0x101010101010101010101010101010101010101010101010101010101010101
def goal_248 : Nat := 0xffffffffffffffffffffffffffff0000ffffff00ffffff00ff00ff0000000000
def roots_248 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffffffffffffffffaaaaffffffaaffffffaaffaaff00aaaaaa00
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffffffffffffffffccccffffffccffffffccffccffcccc00cc00
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffffffffffffffffeeeeffffffeeffffffeeffeeffcceeaaee00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_252 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
def goal_252 : Nat := 0xfffffffffffffffffffffffffffff0f0fffffff0fffffff0fff0fff0f0f00000
def roots_252 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffffffffffffffffafafffffffafffffffafffafff0fafaaa00
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffffffffffffffffcfcfffffffcfffffffcfffcfffcfcf0cc00
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffffffffffffffffefefffffffefffffffefffefffcfefaee00
def roots_255 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

namespace S_42
def pG:List (Nat×Nat):=[(2,10),(2,34),(8,10),(8,40),(32,34),(32,40)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3f
def xsM:=roots_42.map (·&&&dom_42)
def gM:=goal_42&&&dom_42
def NN:Nat→Nat
|2=>1
|3=>1
|_=>0
def HT:Nat→Nat→Nat
|2,0=>0xe7802
|3,0=>0xe7802
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x141400000002800000028040400000404
|_,_=>0
def sP:Nat→Nat
|0=>0x924
|_=>0
def sO:Nat→Nat→Nat
|2,0=>3
|3,0=>0x33
|_,_=>0
def wAt:=mkWire dB 3 43 0x7ffffffffff
def SS:=mkSS wAt sP sO 2 7
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def mkPools (_ _:Nat):List (Nat×Nat×(Nat×List Nat)):=[]
def mkCut (_ _:Nat) (_:Nat×Nat×Nat) (_:List Nat):Bool:=false
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_42 gM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_42 gM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_42==dom_42)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_42 gM v ys):RunD true dom_42 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_42 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s:Nat) (hs:s≤3):∀ i<NN s,bar dom_42 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 2 2=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤3) (h:RunD true dom_42 gM s xsM):False:=by
  have hmin:2≤s:=by have hl:=run_len h;change 3≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_42 roots_42 goal_42 4:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_42
theorem lowS_42:Lower true dom_42 roots_42 goal_42 4:=S_42.noCircuit
def isoMvS_73:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_73:Lower true dom_73 roots_73 goal_73 4:=lower_iso_b isoMvS_73 (by decide +kernel) lowS_42
def isoMvS_74:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_74:Lower true dom_74 roots_74 goal_74 4:=lower_iso_b isoMvS_74 (by decide +kernel) lowS_42
def isoMvS_81:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_81:Lower true dom_81 roots_81 goal_81 4:=lower_iso_b isoMvS_81 (by decide +kernel) lowS_42
def isoMvS_84:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_84:Lower true dom_84 roots_84 goal_84 4:=lower_iso_b isoMvS_84 (by decide +kernel) lowS_42
def isoMvS_145:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_145:Lower true dom_145 roots_145 goal_145 4:=lower_iso_b isoMvS_145 (by decide +kernel) lowS_42
def isoMvS_148:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_148:Lower true dom_148 roots_148 goal_148 4:=lower_iso_b isoMvS_148 (by decide +kernel) lowS_42
def isoMvS_193:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_193:Lower true dom_193 roots_193 goal_193 4:=lower_iso_b isoMvS_193 (by decide +kernel) lowS_42
def isoMvS_208:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_208:Lower true dom_208 roots_208 goal_208 4:=lower_iso_b isoMvS_208 (by decide +kernel) lowS_42
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
theorem lowS_75:Lower true dom_75 roots_75 goal_75 5:=lower_slice_b [(0xa0a0000000000000a0a,8,9)] (by decide +kernel) lowS_74
namespace S_209
def pG:List (Nat×Nat):=[(1,17),(1,65),(1,129),(16,17),(16,80),(16,144),(64,65),(64,80),(64,192),(128,129),(128,144),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfff
def xsM:=roots_209.map (·&&&dom_209)
def gM:=goal_209&&&dom_209
def NN:Nat→Nat
|3=>3
|4=>6
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x76c5d74ede03f89
|4,0=>0x594054087f3b7e0397dc38d5d27c4e
|5,0=>0x8b70744f2b21bc4
|6,0=>0x8b707
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xc000c00000000000c000000000000000c000c00000000000c00030003000000000003000300000000000300000000000000030000400040000000000040004000000000004000400000000000000000000000000000000000000000000000300030000000000030000c000c00000000000c000c00000000000c000c00000000000800090001000000000001000100000000000100010000000000010000c000c000000000000000000000000000c000800000000000000020002000000000002000200000000000200020000000000020002c000c000000000000000000000000000c000c00000000000000030003000000000003000300000000000000000000000000000000c000000000000000c000000000000000c000000000000000c00030003000000000002000200000000000300030000000000020002c000c00000000000c000c0000000000080008000000000008000b0003000000000003000300000000000300030000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x36543654c3654d3654c3165c3605365b4a36543260439654385436743210
|_=>0
def sO:Nat→Nat→Nat
|3,0=>0x8411004
|4,0=>0x956056d565454c5
|5,0=>0x344bd6a5
|6,0=>0x384
|_,_=>0
def wAt:=mkWire dB 14 210 0x3ffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x3454d464d1435515455946551
|_=>0
def oO:Nat→Nat→Nat
|3,0=>2
|4,0=>0x624200002200
|5,0=>0x9181
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0xf976530
|_=>0
def pmB:Nat→Nat→Nat
|3,0=>1
|4,0=>0x13028
|5,0=>0x136
|6,0=>6
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 4 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_208 4 roots_208 ops++addP pm 1 dom_145 4 roots_145 ops++addP pm 2 dom_193 4 roots_193 ops++addP pm 3 dom_81 4 roots_81 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_209 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_145 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_193 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_81 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_208 4 s (0,roots_208.map (·&&&dom_208)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_209 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_208 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)],[(0xffff0000ffff0000ffff0000ffff0000,112)],[(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_209==dom_209)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_209 gM v ys):RunD true dom_209 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_209 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 3 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 6 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 6 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_209 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_209 gM s xsM):False:=by
  have hmin:3≤s:=by have hl:=run_len h;change 4≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_209 roots_209 goal_209 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_209
theorem lowS_209:Lower true dom_209 roots_209 goal_209 7:=S_209.noCircuit
def isoMvS_29:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_29:Lower true dom_29 roots_29 goal_29 4:=lower_iso_b isoMvS_29 (by decide +kernel) lowS_27
def isoMvS_45:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_45:Lower true dom_45 roots_45 goal_45 4:=lower_iso_b isoMvS_45 (by decide +kernel) lowS_27
def isoMvS_46:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_46:Lower true dom_46 roots_46 goal_46 5:=lower_iso_b isoMvS_46 (by decide +kernel) lowS_43
def isoMvS_53:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_53:Lower true dom_53 roots_53 goal_53 4:=lower_iso_b isoMvS_53 (by decide +kernel) lowS_27
def isoMvS_54:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_54:Lower true dom_54 roots_54 goal_54 4:=lower_iso_b isoMvS_54 (by decide +kernel) lowS_27
def isoMvS_57:List (Nat×Nat):=[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_57:Lower true dom_57 roots_57 goal_57 4:=lower_iso_b isoMvS_57 (by decide +kernel) lowS_27
def isoMvS_60:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_60:Lower true dom_60 roots_60 goal_60 4:=lower_iso_b isoMvS_60 (by decide +kernel) lowS_27
def isoMvS_77:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_77:Lower true dom_77 roots_77 goal_77 5:=lower_iso_b isoMvS_77 (by decide +kernel) lowS_43
def isoMvS_78:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_78:Lower true dom_78 roots_78 goal_78 5:=lower_iso_b isoMvS_78 (by decide +kernel) lowS_43
def isoMvS_83:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_83:Lower true dom_83 roots_83 goal_83 5:=lower_iso_b isoMvS_83 (by decide +kernel) lowS_43
def isoMvS_85:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_85:Lower true dom_85 roots_85 goal_85 5:=lower_iso_b isoMvS_85 (by decide +kernel) lowS_75
def isoMvS_86:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_86:Lower true dom_86 roots_86 goal_86 5:=lower_iso_b isoMvS_86 (by decide +kernel) lowS_43
def isoMvS_89:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_89:Lower true dom_89 roots_89 goal_89 5:=lower_iso_b isoMvS_89 (by decide +kernel) lowS_75
def isoMvS_90:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_90:Lower true dom_90 roots_90 goal_90 5:=lower_iso_b isoMvS_90 (by decide +kernel) lowS_43
def isoMvS_92:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_92:Lower true dom_92 roots_92 goal_92 5:=lower_iso_b isoMvS_92 (by decide +kernel) lowS_43
def isoMvS_99:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_99:Lower true dom_99 roots_99 goal_99 4:=lower_iso_b isoMvS_99 (by decide +kernel) lowS_27
def isoMvS_101:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_101:Lower true dom_101 roots_101 goal_101 4:=lower_iso_b isoMvS_101 (by decide +kernel) lowS_27
def isoMvS_105:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_105:Lower true dom_105 roots_105 goal_105 5:=lower_iso_b isoMvS_105 (by decide +kernel) lowS_43
def isoMvS_106:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_106:Lower true dom_106 roots_106 goal_106 5:=lower_iso_b isoMvS_106 (by decide +kernel) lowS_75
def isoMvS_114:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_114:Lower true dom_114 roots_114 goal_114 4:=lower_iso_b isoMvS_114 (by decide +kernel) lowS_27
def isoMvS_116:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_116:Lower true dom_116 roots_116 goal_116 5:=lower_iso_b isoMvS_116 (by decide +kernel) lowS_43
def isoMvS_120:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_120:Lower true dom_120 roots_120 goal_120 4:=lower_iso_b isoMvS_120 (by decide +kernel) lowS_27
def isoMvS_141:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_141:Lower true dom_141 roots_141 goal_141 4:=lower_iso_b isoMvS_141 (by decide +kernel) lowS_27
def isoMvS_142:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_142:Lower true dom_142 roots_142 goal_142 4:=lower_iso_b isoMvS_142 (by decide +kernel) lowS_27
def isoMvS_147:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_147:Lower true dom_147 roots_147 goal_147 5:=lower_iso_b isoMvS_147 (by decide +kernel) lowS_43
def isoMvS_153:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_153:Lower true dom_153 roots_153 goal_153 5:=lower_iso_b isoMvS_153 (by decide +kernel) lowS_43
def isoMvS_154:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_154:Lower true dom_154 roots_154 goal_154 4:=lower_iso_b isoMvS_154 (by decide +kernel) lowS_27
def isoMvS_170:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_170:Lower true dom_170 roots_170 goal_170 5:=lower_iso_b isoMvS_170 (by decide +kernel) lowS_75
def isoMvS_172:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_172:Lower true dom_172 roots_172 goal_172 5:=lower_iso_b isoMvS_172 (by decide +kernel) lowS_43
def isoMvS_195:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_195:Lower true dom_195 roots_195 goal_195 5:=lower_iso_b isoMvS_195 (by decide +kernel) lowS_75
def isoMvS_197:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_197:Lower true dom_197 roots_197 goal_197 5:=lower_iso_b isoMvS_197 (by decide +kernel) lowS_75
def isoMvS_198:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_198:Lower true dom_198 roots_198 goal_198 5:=lower_iso_b isoMvS_198 (by decide +kernel) lowS_75
def isoMvS_201:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_201:Lower true dom_201 roots_201 goal_201 5:=lower_iso_b isoMvS_201 (by decide +kernel) lowS_75
def isoMvS_202:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_202:Lower true dom_202 roots_202 goal_202 5:=lower_iso_b isoMvS_202 (by decide +kernel) lowS_75
def isoMvS_210:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_210:Lower true dom_210 roots_210 goal_210 5:=lower_iso_b isoMvS_210 (by decide +kernel) lowS_75
def isoMvS_212:List (Nat×Nat):=[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_212:Lower true dom_212 roots_212 goal_212 7:=lower_iso_b isoMvS_212 (by decide +kernel) lowS_209
def isoMvS_216:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_216:Lower true dom_216 roots_216 goal_216 5:=lower_iso_b isoMvS_216 (by decide +kernel) lowS_43
theorem lowS_31:Lower true dom_31 roots_31 goal_31 5:=lower_slice_b [(0xcccccccc,8,10)] (by decide +kernel) lowS_29
theorem lowS_47:Lower true dom_47 roots_47 goal_47 6:=lower_slice_b [(0xaaaa0000aaaa,8,9)] (by decide +kernel) lowS_46
def dzo_43_16:=0xf0f00000f0f0000
def gzo_43_16:=0xf0e00000e0a0000
def gsh_43_16:=0xf0e00000e0a
theorem lowS_zo_43_16_42:Lower true dzo_43_16 roots_43 gzo_43_16 5:=lower_iso_b (d1:=dom_43) (r1:=roots_43) (T1:=gsh_43_16) [(dom_43,16)] (by decide +kernel) (lower_slice_b (T:=gsh_43_16) [(0xa0a00000a0a,0,1)] (by decide +kernel) lowS_42)
namespace S_59
def pG:List (Nat×Nat):=[(1,9),(1,17),(2,10),(2,34),(3,11),(3,19),(3,35),(8,9),(8,10),(8,40),(16,17),(18,19),(18,26),(18,50),(24,25),(24,26),(24,56),(32,34),(32,40),(33,35),(33,41),(33,49),(48,49),(48,50),(48,56)]
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
|4,0=>0x116aa1150d
|5,0=>0x706e0567fd0a6f0
|6,0=>0x9abd7
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf000f00f0f0f0f0c0c0c0cf0f0f0f0f000f00f0f0f0f00000000303030303000300f0f00000f0f0000f0c0f0c00000000f000f000f000f00c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a
|_,_=>0
def sP:Nat→Nat
|0=>0x642106421098642107642106420543210
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
|0=>0x9b
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x400
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 5
def pmP:Nat→Nat
|0=>0x1f41c40
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x99
|6,0=>4
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_43 5 roots_43 ops++addP pm 1 dom_27 4 roots_27 ops++addP pm 2 dzo_43_16 5 roots_43 ops++addP pm 3 dom_57 4 roots_57 ops++addP pm 4 dom_42 4 roots_42 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_59 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_43_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_42 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_43 5 s (0,roots_43.map (·&&&dom_43)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_59 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_43 h
def symsG:List (List (Nat×Nat)):=[[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)]]
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
namespace S_61
def pG:List (Nat×Nat):=[(1,9),(1,17),(4,20),(4,36),(5,13),(5,21),(5,37),(8,9),(8,40),(12,13),(12,28),(12,44),(16,17),(16,20),(24,25),(24,28),(24,56),(32,36),(32,40),(33,37),(33,41),(33,49),(48,49),(48,52),(48,56)]
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
|4,0=>0x17b4f078e1
|5,0=>0xd596d410471adda
|6,0=>0xd596d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x3333303033333030ccc0ccc0ccc0ccc30303030303030300c0c0c0c0c0c0003333333300000000cccc0000cccc0003300330033003300c0c0c0c0c0c00002222222222222222
|_,_=>0
def sP:Nat→Nat
|0=>0x43260432604832604372604320543210
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x15405
|5,0=>0x165418a6
|6,0=>0x1b5
|_,_=>0
def wAt:=mkWire dB 9 62 0x3fffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def pmP:Nat→Nat
|0=>0x7c40
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>5
|6,0=>2
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 2 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_60 4 roots_60 ops++addP pm 1 dom_57 4 roots_57 ops++addP pm 2 dom_53 4 roots_53 ops++addP pm 3 dom_45 4 roots_45 ops++addP pm 4 dom_29 4 roots_29 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_61 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_60 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_53 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_29 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_60 4 s (0,roots_60.map (·&&&dom_60)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_61 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_60 h
def symsG:List (List (Nat×Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
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
theorem lowS_79:Lower true dom_79 roots_79 goal_79 6:=lower_slice_b [(0xaaaa000000000000aaaa,8,9)] (by decide +kernel) lowS_78
namespace S_91
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(2,10),(2,66),(3,11),(3,19),(3,67),(8,9),(8,10),(8,72),(16,17),(16,80),(18,19),(18,26),(18,82),(24,25),(24,26),(24,88),(64,65),(64,66),(64,72),(64,80)]
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
namespace S_94
def pG:List (Nat×Nat):=[(2,10),(2,66),(4,20),(4,68),(6,14),(6,22),(6,70),(8,10),(8,72),(12,14),(12,28),(12,76),(16,20),(16,80),(18,22),(18,26),(18,82),(24,26),(24,28),(24,88),(64,66),(64,68),(64,72),(64,80)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_94.map (·&&&dom_94)
def gM:=goal_94&&&dom_94
def NN:Nat→Nat
|3=>1
|4=>4
|5=>10
|6=>4
|7=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x70d60
|4,0=>0x4f6c5225a70cf2e0088a
|5,0=>0x673e262b523b1dc23fa8132c70cbad0aa4009f9b03866020d5
|6,0=>0x4f7614c25d3432f0c8a5
|7,0=>0x4c25d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaaaa000000000000a0a00001555400000000000154022a2a2a280000000222222220000000000000000545454540000a0aa000000000000a0a0000155540000000000015152aaaaaaa800000002aaa8000444444440000000044444444aaaa88880000000000000001540154000000000154015402aaaaaa20000000022222222555555550000000000000000aaaa000000000000aaaa000155555554000000015401540282828280000000028282828555455540000000044444444
|0,1=>0x2aaa8000000000000000555555550000000050505050222222220000000000000000141414140000000014140000000002a8000000000000000555555000000000000000000aaaa888800000000aaaa8889555555540000000111111112aaaaa80000000002aaaaa80555555550000000055555500
|_,_=>0
def sP:Nat→Nat
|0=>0xcc1410660a0991982820cd80a0931982820cc1912e91991620cc1412a330504a4c660c8901982821828790660a1c41982d41066605043050b21828511260a0e3304a418820
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|4,0=>0x26a3944a845
|5,0=>0x26b47682ced9ab2f654a918f3186
|6,0=>0xc8d7d6cb536
|7,0=>0x6a5
|_,_=>0
def wAt:=mkWire dB 26 95 0x7fffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1920911a10a6191890411891092
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x420031211100000100
|6,0=>0x81007161
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 8
def pmP:Nat→Nat
|0=>0xffdd6e50a183080
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x2506340010
|6,0=>0x8789
|7,0=>9
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 6 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_92 5 roots_92 ops++addP pm 1 dom_84 4 roots_84 ops++addP pm 2 dom_78 5 roots_78 ops++addP pm 3 dom_74 4 roots_74 ops++addP pm 4 dom_90 5 roots_90 ops++addP pm 5 dom_86 5 roots_86 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_94 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_92 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_78 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_86 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_92 5 s (0,roots_92.map (·&&&dom_92)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_94 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_92 h
def symsG:List (List (Nat×Nat)):=[[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_94==dom_94)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_94 gM v ys):RunD true dom_94 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_94 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 4 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
theorem checked (s:Nat) (hs:s≤7):∀ i<NN s,bar dom_94 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤7) (h:RunD true dom_94 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_94 roots_94 goal_94 8:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_94
theorem lowS_94:Lower true dom_94 roots_94 goal_94 8:=S_94.noCircuit
theorem lowS_103:Lower true dom_103 roots_103 goal_103 5:=lower_slice_b [(0xcc000000cc000000cc000000cc,32,34)] (by decide +kernel) lowS_101
theorem lowS_109:Lower true dom_109 roots_109 goal_109 6:=lower_slice_b [(0x3030000030300000303000003030,32,36)] (by decide +kernel) lowS_105
theorem lowS_110:Lower true dom_110 roots_110 goal_110 6:=lower_slice_b [(0x5050000050500000505000005050,32,36)] (by decide +kernel) lowS_106
def dzo_85_32:=0x330033000000000033003300000000
def gzo_85_32:=0x330032000000000032003000000000
def gsh_85_32:=0x3300320000000000320030
theorem lowS_zo_85_32_81:Lower true dzo_85_32 roots_85 gzo_85_32 5:=lower_iso_b (d1:=dom_85) (r1:=roots_85) (T1:=gsh_85_32) [(dom_85,32)] (by decide +kernel) (lower_slice_b (T:=gsh_85_32) [(0x3000300000000000300030,0,4)] (by decide +kernel) lowS_81)
namespace S_117
def pG:List (Nat×Nat):=[(1,17),(1,65),(4,20),(4,36),(4,68),(5,21),(5,37),(5,69),(16,17),(16,20),(16,80),(32,36),(33,37),(33,49),(33,97),(48,49),(48,52),(48,112),(64,65),(64,68),(64,80),(96,97),(96,100),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_117.map (·&&&dom_117)
def gM:=goal_117&&&dom_117
def NN:Nat→Nat
|4=>1
|5=>1
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x5e1c0
|5,0=>0xb5342
|6,0=>0x96c74
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x33003300330033003300000033000088008800880088008800880088008b30033000000000033003300000000cc000000cc000000cc000000cc00030003000300030003000300030003044004400440044004400000044000330033003300330000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x8d5133544688
|_=>0
def sO:Nat→Nat→Nat
|4,0=>5
|5,0=>0x56
|6,0=>0xb5
|_,_=>0
def wAt:=mkWire dB 7 118 0x3fffffffffffffffffffffffffffff
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
addP pm 0 dom_116 5 roots_116 ops++addP pm 1 dom_101 4 roots_101 ops++addP pm 2 dzo_85_32 5 roots_85 ops++addP pm 3 dom_85 5 roots_85 ops++addP pm 4 dom_81 4 roots_81 ops++addP pm 5 dom_53 4 roots_53 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_117 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_101 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_85_32_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_53 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_116 5 s (0,roots_116.map (·&&&dom_116)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_117 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_116 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_117==dom_117)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_117 gM v ys):RunD true dom_117 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_117 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_117 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_117 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_117 roots_117 goal_117 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_117
theorem lowS_117:Lower true dom_117 roots_117 goal_117 7:=S_117.noCircuit
theorem lowS_199:Lower true dom_199 roots_199 goal_199 6:=lower_slice_b [(0xaa00000000000000aa00000000000000aa00000000000000aa,64,65)] (by decide +kernel) lowS_198
theorem lowS_203:Lower true dom_203 roots_203 goal_203 6:=lower_slice_b [(0xa0a0000000000000a0a0000000000000a0a0000000000000a0a,8,9)] (by decide +kernel) lowS_202
theorem lowS_211:Lower true dom_211 roots_211 goal_211 8:=lower_slice_b [(0xc000c00000000000c000c00000000000c000c00000000000c000c,64,66)] (by decide +kernel) lowS_209
theorem lowS_213:Lower true dom_213 roots_213 goal_213 8:=lower_slice_b [(0x220022000000000022002200000000002200220000000000220022,16,17)] (by decide +kernel) lowS_212
theorem lowS_220:Lower true dom_220 roots_220 goal_220 8:=lower_slice_b [(0x11001100000000001100110000000000110011000000000011001100,64,72)] (by decide +kernel) lowS_212
def isoMvS_55:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_55:Lower true dom_55 roots_55 goal_55 5:=lower_iso_b isoMvS_55 (by decide +kernel) lowS_31
def isoMvS_62:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_62:Lower true dom_62 roots_62 goal_62 7:=lower_iso_b isoMvS_62 (by decide +kernel) lowS_59
def isoMvS_87:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_87:Lower true dom_87 roots_87 goal_87 6:=lower_iso_b isoMvS_87 (by decide +kernel) lowS_79
def isoMvS_93:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_93:Lower true dom_93 roots_93 goal_93 7:=lower_iso_b isoMvS_93 (by decide +kernel) lowS_91
def isoMvS_107:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_107:Lower true dom_107 roots_107 goal_107 7:=lower_iso_b isoMvS_107 (by decide +kernel) lowS_91
def isoMvS_115:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_115:Lower true dom_115 roots_115 goal_115 7:=lower_iso_b isoMvS_115 (by decide +kernel) lowS_59
def isoMvS_118:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_118:Lower true dom_118 roots_118 goal_118 6:=lower_iso_b isoMvS_118 (by decide +kernel) lowS_109
def isoMvS_121:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_121:Lower true dom_121 roots_121 goal_121 7:=lower_iso_b isoMvS_121 (by decide +kernel) lowS_117
def isoMvS_122:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_122:Lower true dom_122 roots_122 goal_122 7:=lower_iso_b isoMvS_122 (by decide +kernel) lowS_117
def isoMvS_124:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_124:Lower true dom_124 roots_124 goal_124 6:=lower_iso_b isoMvS_124 (by decide +kernel) lowS_109
def isoMvS_143:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_143:Lower true dom_143 roots_143 goal_143 5:=lower_iso_b isoMvS_143 (by decide +kernel) lowS_103
def isoMvS_151:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_151:Lower true dom_151 roots_151 goal_151 6:=lower_iso_b isoMvS_151 (by decide +kernel) lowS_79
def isoMvS_155:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_155:Lower true dom_155 roots_155 goal_155 6:=lower_iso_b isoMvS_155 (by decide +kernel) lowS_109
def isoMvS_157:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_157:Lower true dom_157 roots_157 goal_157 7:=lower_iso_b isoMvS_157 (by decide +kernel) lowS_117
def isoMvS_158:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_158:Lower true dom_158 roots_158 goal_158 7:=lower_iso_b isoMvS_158 (by decide +kernel) lowS_59
def isoMvS_171:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_171:Lower true dom_171 roots_171 goal_171 6:=lower_iso_b isoMvS_171 (by decide +kernel) lowS_110
def isoMvS_173:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_173:Lower true dom_173 roots_173 goal_173 6:=lower_iso_b isoMvS_173 (by decide +kernel) lowS_109
def isoMvS_185:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_185:Lower true dom_185 roots_185 goal_185 6:=lower_iso_b isoMvS_185 (by decide +kernel) lowS_109
def isoMvS_186:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_186:Lower true dom_186 roots_186 goal_186 7:=lower_iso_b isoMvS_186 (by decide +kernel) lowS_117
def isoMvS_205:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_205:Lower true dom_205 roots_205 goal_205 7:=lower_iso_b isoMvS_205 (by decide +kernel) lowS_91
def isoMvS_206:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_206:Lower true dom_206 roots_206 goal_206 7:=lower_iso_b isoMvS_206 (by decide +kernel) lowS_91
def isoMvS_214:List (Nat×Nat):=[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_214:Lower true dom_214 roots_214 goal_214 8:=lower_iso_b isoMvS_214 (by decide +kernel) lowS_211
def isoMvS_217:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_217:Lower true dom_217 roots_217 goal_217 8:=lower_iso_b isoMvS_217 (by decide +kernel) lowS_211
def isoMvS_218:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_218:Lower true dom_218 roots_218 goal_218 7:=lower_iso_b isoMvS_218 (by decide +kernel) lowS_91
def isoMvS_227:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_227:Lower true dom_227 roots_227 goal_227 7:=lower_iso_b isoMvS_227 (by decide +kernel) lowS_91
def isoMvS_229:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_229:Lower true dom_229 roots_229 goal_229 7:=lower_iso_b isoMvS_229 (by decide +kernel) lowS_91
def isoMvS_233:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_233:Lower true dom_233 roots_233 goal_233 6:=lower_iso_b isoMvS_233 (by decide +kernel) lowS_110
def isoMvS_234:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_234:Lower true dom_234 roots_234 goal_234 6:=lower_iso_b isoMvS_234 (by decide +kernel) lowS_203
def isoMvS_236:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]
theorem lowS_236:Lower true dom_236 roots_236 goal_236 6:=lower_iso_b isoMvS_236 (by decide +kernel) lowS_110
def isoMvS_241:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_241:Lower true dom_241 roots_241 goal_241 8:=lower_iso_b isoMvS_241 (by decide +kernel) lowS_220
def isoMvS_242:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_242:Lower true dom_242 roots_242 goal_242 7:=lower_iso_b isoMvS_242 (by decide +kernel) lowS_91
def isoMvS_248:List (Nat×Nat):=[(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_248:Lower true dom_248 roots_248 goal_248 6:=lower_iso_b isoMvS_248 (by decide +kernel) lowS_109
def dzo_47_16:=0xffff0000ffff0000
def gzo_47_16:=0xfffe0000fefa0000
def gsh_47_16:=0xfffe0000fefa
theorem lowS_zo_47_16_42:Lower true dzo_47_16 roots_47 gzo_47_16 6:=lower_iso_b (d1:=dom_47) (r1:=roots_47) (T1:=gsh_47_16) [(dom_47,16)] (by decide +kernel) (lower_slice_b (T:=gsh_47_16) [(0xaaaa0000aaaa,0,1),(0xf0f00000f0f0,0,4)] (by decide +kernel) lowS_42)
namespace S_63
def pG:List (Nat×Nat):=[(1,9),(1,17),(2,10),(2,34),(3,11),(3,19),(3,35),(4,20),(4,36),(5,13),(5,21),(5,37),(6,14),(6,22),(6,38),(7,15),(7,23),(7,39),(8,9),(8,10),(8,40),(12,13),(12,14),(12,28),(12,44),(16,17),(16,20),(18,19),(18,22),(18,26),(18,50),(24,25),(24,26),(24,28),(24,56),(32,34),(32,36),(32,40),(33,35),(33,37),(33,41),(33,49),(48,49),(48,50),(48,52),(48,56)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffffff
def xsM:=roots_63.map (·&&&dom_63)
def gM:=goal_63&&&dom_63
def NN:Nat→Nat
|4=>3
|5=>5
|6=>9
|7=>3
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x9089f6129a2d780
|5,0=>0xe2aafb08c899818971348e1da
|6,0=>0xdd808cf6b2b40d5a528a908be8e1da84f7c72b0e5a9d2
|7,0=>0xdd8085f71129ed4
|8,0=>0xc6758
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xff00ff0000000000000000ff00ff00ffffff00ffff0000ffaaffaaaaaaaaaaffccffccccccccccccccccccccccccccff00ff0000000000ffffffff00000000ff00ff00ff00ff00333333333300330000ff00ffff00ff00ffffffffff00ff00ffff0000ffff0000f0f0f0f0f0f0f0f0aaaaaaaaaaaaaaaa0033003333003300
|0,1=>0xff0000ffff0000
|_,_=>0
def sP:Nat→Nat
|0=>0x10338941220671282819d225050338941791033894120d22505071283022067104c31282f72067104c869c4a0a06b388281b0e25106b10483128251894129069104c819c4130c4128062098a418820
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x2942a805
|5,0=>0x26540c6d4ab0f6
|6,0=>0x5c7acd41a4bc367acdd98b2b6
|7,0=>0x1c5f53e37
|8,0=>0x786
|_,_=>0
def wAt:=mkWire dB 17 64 0xffffffffffffffff
def SS:=mkSS wAt sP sO 5 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x41d41c3a23bd3a241c41d41d41c41d22741c41d22741c41d
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x621980c0000
|6,0=>0xb2490010200000000000
|7,0=>0x3c5c2d1
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 9
def pmP:Nat→Nat
|0=>0xffaca0f0c10100
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x1240
|6,0=>0x380d02a
|7,0=>0x1ff
|8,0=>6
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 7 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_62 7 roots_62 ops++addP pm 1 dom_61 7 roots_61 ops++addP pm 2 dom_55 5 roots_55 ops++addP pm 3 dom_59 7 roots_59 ops++addP pm 4 dom_31 5 roots_31 ops++addP pm 5 dom_47 6 roots_47 ops++addP pm 6 dzo_47_16 6 roots_47 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_63 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_47 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_47_16_42 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_62 7 s (0,roots_62.map (·&&&dom_62)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_63 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_62 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_63==dom_63)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_63 gM v ys):RunD true dom_63 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_63 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 5 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 9 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 3 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 3 0 = true)
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
theorem lowS_95:Lower true dom_95 roots_95 goal_95 9:=lower_slice_b [(0xaaaaaaaa00000000aaaaaaaa,8,9)] (by decide +kernel) lowS_94
theorem lowS_111:Lower true dom_111 roots_111 goal_111 8:=lower_slice_b [(0xf0f00000f0f00000f0f00000f0f0,32,36)] (by decide +kernel) lowS_107
def dzo_87_32:=0xff00ff0000000000ff00ff00000000
def gzo_87_32:=0xff00fe0000000000fe00fc00000000
def gsh_87_32:=0xff00fe0000000000fe00fc
theorem lowS_zo_87_32_81:Lower true dzo_87_32 roots_87 gzo_87_32 6:=lower_iso_b (d1:=dom_87) (r1:=roots_87) (T1:=gsh_87_32) [(dom_87,32)] (by decide +kernel) (lower_slice_b (T:=gsh_87_32) [(0xcc00cc0000000000cc00cc,0,2),(0xf000f00000000000f000f0,0,4)] (by decide +kernel) lowS_81)
namespace S_119
def pG:List (Nat×Nat):=[(1,17),(1,65),(2,34),(2,66),(3,19),(3,35),(3,67),(4,20),(4,36),(4,68),(5,21),(5,37),(5,69),(6,22),(6,38),(6,70),(7,23),(7,39),(7,71),(16,17),(16,20),(16,80),(18,19),(18,22),(18,50),(18,82),(32,34),(32,36),(33,35),(33,37),(33,49),(33,97),(48,49),(48,50),(48,52),(48,112),(64,65),(64,66),(64,68),(64,80),(96,97),(96,98),(96,100),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_119.map (·&&&dom_119)
def gM:=goal_119&&&dom_119
def NN:Nat→Nat
|4=>5
|5=>15
|6=>37
|7=>10
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xe8d6978b936ee3a6d9af54b88
|5,0=>0xef258e64eee3448e1eecd8193cb74ac9270c39fba0069716ab5ab19595394107540a78001ac
|6,0=>0xfeae0fd584f89ecf4031f2a2de972be6de2e6930dae64bce6cb4720b23e2b0eb3a4524a120d9cf2d9ccfd9b1e396e998bd487ed9a749c973eed716ab633535d38a5c1104f8474a36c47d7945218450703eb1e219941f8b31f0b107592
|7,0=>0xf2fd6f06f3e8d9fc2892bad6da4ab86aedf5d38a4f76c093c2
|8,0=>0xdaa04
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x550055005500550000000000000000ff00ff00ff00ff00ff00ff000000000000000000000000ff00aa00ff00aaaa00aa00aa00aa00aa00aa00aa00aaff000000ff000000ff000000ff0000fe00fe00fe00fe00fe00fc00fe00fcfa00fa00fa00fa00fa00f000fa00f0ff00ff00ff00ff0000000000000000ff00f000ff00f000f000f000f000f05500550055005500550000005500000000ff000000ff00ff000000ff0000ff00ff0000000000ff00ff00000000ff00ff00ff00ff00ff000000ff0000f000f000f000f000f000f000f000f0cc00cc00cc00cc00cc00cc00cc00cc000055000000550055000000550000
|0,1=>0xaa000000aa000000ff000000ff0000ff00ff00ff00ff00ff00aa00ff00aaaa00aa00aa00aa00ff00aa00ff00aaff00cc00ff00cc00cc00cc00cc00ccff00ff00ff000000ff00ff00000000ff005500ff005500ff000000ff0000ff00aa00ff00aa00aa00aa00aa00aaff000000ff000000000000000000000000000000000000ff000000ff00000000ff000000ff0000000000000000ff00aa00ff00aa00ff00aa00ff00aaff00ff00ff00ff00aa00aa00aa00aaff00ff00ff00ff00550000005500000000000000000000ff00ff00000000aa00aa00aa00aa00aa000000aa0000550000005500000055000000550000
|0,2=>0xff0000000000ff00ff000000000000aa000000aa00aa00aa00aa00aaff00ff000000ff00ff00ff00000000ff00000000000000ff00ff00000000000000000000000055000000550000ff00ff0055005500ff00ff00000000
|_,_=>0
def sP:Nat→Nat
|0=>0x5120e54b08130810b0813132046820502040c20466040c20591031c130414204c1150c205410b0814cf1032c904838b08118810b08118810314204c48b08118810b2412040c20503ce34b0813042ca2481031c11841420461050810040c2040
|1=>0x8144880b08130810b7c204c20478b0813083832c204c2040c204c40811d2c204c2042c270c2042c20462045c204c5840cb08130810b0814083c40c204c6045570813081032c20543120cb08130810b08130621b2c204c20e2d70813081032c2
|2=>0x10b0813086040cb08130810b0813083ce2c204c2042c20592042c704c2252c204c2040cb0811881032c204c3ce2c204c4081152c20542042c20642122d70813088cb0813081150c204c2222c204c20434b08130810b08132120468b08130810b
|3=>0x42c204c2042d70813081152c204c2042c204c21648b08130810b0813102042c2054308
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x14507a82940aa005
|5,0=>0x1a58c6c5e52ca95149cc4862130f186cc30615309543ec196
|6,0=>0x15f6acb54da98f4579f3cdde62d2a7923475e2ed10784bc09df8cf6677bba1dc2eda769bb3598ecc165d3acdd5aca674fba61d22e8b64239f5cece6f7
|7,0=>0x344f9b7ca3e39b0ef807bcbdc9ed6f656
|8,0=>0x1a96
|_,_=>0
def wAt:=mkWire dB 38 120 0xffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xb232cc4b22108cb333084b202c84c221084c612c802612c804632c80b212c84421318cb201164b222c8445b2c883302c8443d3088b3f2c841612c803332c84b232c88b212c80b232c84b211184b201084b213184b200984b212c817592c8cb222c842450cc0b21
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0xa31cc430c40000000000000000300000
|6,0=>0x2f2b4ab2a8691a04009880090a3184800000007c9d270400001b1001925c952000004c92144501000e20000034400
|7,0=>0xe8791e0771d8751d0731c8711
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 10
def pmP:Nat→Nat
|0=>0xf9fe3edf77dcf67c8f03324c3308a021c84180531404410037090200540d01c0400c00
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x320ce01000201400
|6,0=>0x129d0cd30989a1e80001156815004432701e63ac14488e0
|7,0=>0x359ddf38deaf6
|8,0=>0x15
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 10 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_117 7 roots_117 ops++addP pm 1 dom_115 7 roots_115 ops++addP pm 2 dom_54 4 roots_54 ops++addP pm 3 dom_99 4 roots_99 ops++addP pm 4 dom_86 5 roots_86 ops++addP pm 5 dom_118 6 roots_118 ops++addP pm 6 dom_55 5 roots_55 ops++addP pm 7 dom_103 5 roots_103 ops++addP pm 8 dzo_87_32 6 roots_87 ops++addP pm 9 dom_87 6 roots_87 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_119 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_87_32_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_87 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_117 7 s (0,roots_117.map (·&&&dom_117)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_119 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_117 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_119 gM v ys):RunD true dom_119 gM v (ori ys):=h
def Z (s:Nat):=barP dom_119 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 5 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 15 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 37 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 37 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 10 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 10 0 = true)
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
def dzo_81_32:=0x30003000000000003000300000000
def gzo_81_32:=0x30002000000000002000000000000
def gsh_81_32:=0x300020000000000020000
theorem lowS_zo_81_32_81:Lower true dzo_81_32 roots_81 gzo_81_32 4:=lower_iso_b (d1:=dom_81) (r1:=roots_81) (T1:=gsh_81_32) [(dom_81,32)] (by decide +kernel) (lower_slice_b (T:=gsh_81_32) [] (by decide +kernel) lowS_81)
def dzo_42_16:=0x505000005050000
def gzo_42_16:=0x504000004000000
def gsh_42_16:=0x50400000400
theorem lowS_zo_42_16_42:Lower true dzo_42_16 roots_42 gzo_42_16 4:=lower_iso_b (d1:=dom_42) (r1:=roots_42) (T1:=gsh_42_16) [(dom_42,16)] (by decide +kernel) (lower_slice_b (T:=gsh_42_16) [] (by decide +kernel) lowS_42)
def dzo_91_32:=0xf0f0f0f000000000f0f0f0f00000000
def gzo_91_32:=0xf0f0f0e000000000f0e0f0c00000000
def gsh_91_32:=0xf0f0f0e000000000f0e0f0c
theorem lowS_zo_91_32_81:Lower true dzo_91_32 roots_91 gzo_91_32 6:=lower_iso_b (d1:=dom_91) (r1:=roots_91) (T1:=gsh_91_32) [(dom_91,32)] (by decide +kernel) (lower_slice_b (T:=gsh_91_32) [(0xc0c0c0c000000000c0c0c0c,0,2),(0xf000f00000000000f000f00,0,8)] (by decide +kernel) lowS_81)
def dzo_106_16:=0x5050000050500000505000005050000
def gzo_106_16:=0x5050000050500000504000004000000
def gsh_106_16:=0x505000005050000050400000400
theorem lowS_zo_106_16_42:Lower true dzo_106_16 roots_106 gzo_106_16 5:=lower_iso_b (d1:=dom_106) (r1:=roots_106) (T1:=gsh_106_16) [(dom_106,16)] (by decide +kernel) (lower_slice_b (T:=gsh_106_16) [(0x505000005050000000000000000,0,64)] (by decide +kernel) lowS_42)
def dzo_83_32:=0xf000f00000000000f000f00000000
def gzo_83_32:=0xf000e00000000000e000c00000000
def gsh_83_32:=0xf000e00000000000e000c
theorem lowS_zo_83_32_81:Lower true dzo_83_32 roots_83 gzo_83_32 5:=lower_iso_b (d1:=dom_83) (r1:=roots_83) (T1:=gsh_83_32) [(dom_83,32)] (by decide +kernel) (lower_slice_b (T:=gsh_83_32) [(0xc000c00000000000c000c,0,2)] (by decide +kernel) lowS_81)
def dzo_89_32:=0x3030303000000000303030300000000
def gzo_89_32:=0x3030302000000000302030000000000
def gsh_89_32:=0x30303020000000003020300
theorem lowS_zo_89_32_81:Lower true dzo_89_32 roots_89 gzo_89_32 5:=lower_iso_b (d1:=dom_89) (r1:=roots_89) (T1:=gsh_89_32) [(dom_89,32)] (by decide +kernel) (lower_slice_b (T:=gsh_89_32) [(0x30003000000000003000300,0,8)] (by decide +kernel) lowS_81)
def dzo_107_16:=0xf0f00000f0f00000f0f00000f0f0000
def gzo_107_16:=0xf0f00000f0f00000f0e00000e0a0000
def gsh_107_16:=0xf0f00000f0f00000f0e00000e0a
theorem lowS_zo_107_16_42:Lower true dzo_107_16 roots_107 gzo_107_16 6:=lower_iso_b (d1:=dom_107) (r1:=roots_107) (T1:=gsh_107_16) [(dom_107,16)] (by decide +kernel) (lower_slice_b (T:=gsh_107_16) [(0xa0a00000a0a00000a0a00000a0a,0,1),(0xf0f00000f0f0000000000000000,0,64)] (by decide +kernel) lowS_42)
namespace S_123
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(2,10),(2,34),(2,66),(3,11),(3,19),(3,35),(3,67),(8,9),(8,10),(8,40),(8,72),(16,17),(16,80),(18,19),(18,26),(18,50),(18,82),(24,25),(24,26),(24,56),(24,88),(32,34),(32,40),(33,35),(33,41),(33,49),(33,97),(48,49),(48,50),(48,56),(48,112),(64,65),(64,66),(64,72),(64,80),(96,97),(96,98),(96,104),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_123.map (·&&&dom_123)
def gM:=goal_123&&&dom_123
def NN:Nat→Nat
|4=>7
|5=>18
|6=>46
|7=>36
|8=>12
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xf5570bfbbe89e877444856cf04555013407
|5,0=>0xe6053d48b3ba802a898f9bbd58d3ef626934a1153fb3e39646340fa2cce12c8d6282701943417fd716ba404831
|6,0=>0xd8d71d8338c8c8ec825fb7238b00b39dfad9928797d449676c91b89838bc7ce157cca16dfd969c7667aeb65fdb58beb5317652938519385085e4908845591419d6401d23abf8300792d93f2c8992b8992a19a2945821dee1c5741a7121827b15dc2117e8105dd0f3a70c3150593a03588007ba
|7,0=>0xf5353f0557e1338d5e3bc37a2baca9aee04a7d1b9a1369657b93a528eb9b78e10761a866b9c5d0b44938f487b5446b53df5c3998035605353c1311d62c9172a9472a0391d0481ce041489e12c1f0fff30b41709f9f08466048d0
|8,0=>0xf62e77f49378ef062b5b5f5a847c683cae432d0c300161cf4b1b67807721
|9,0=>0x62b5b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf000f000f000f000f000f000f000f0000000000f0f0f0c000000000f0e0f0cf0f0f0c0f0f0f0c0f0e0f0c0f0e0f0ce0e0e0e0e0e0e0e0e0e0e0e0e0e0e0ef0a0f0a0f0a0f0a0f0a0f0a0f0a0f0af0f0f0f0f0f0f0f0c0c0c0c0c0c0c0cf0f0f0f000000000f0f0f0f00000000f0f00000f0f00000f0f00000f0f0000f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0ce0e0e0e0e0e0e0e0e000e000e000e00f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0af0f0f000f0f0f000f0a0f000f0a0f00c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a00000000f0c0f0c000000000f0c0f0cf0f0f0f0f0f0f0f0000000000000000
|0,1=>0xa0f0a0f0a0f0a0f0a0e0a0e0a0e0a0ef0f0f0f0f0f0f0f0f0c0f0c0f0c0f0c00500050005000500040004000400045050505050505050404040404040404f0f0f000f0f0f000f0f0f000f0f0f00303030303030303030003000300030050505050505050505040504000000000000f0f00000f0f00000a0a00000a0af0f0f0f0f0f0f0f0f0e0f0e0a0a0a0af0f0f0f0f0f0f0f0e0e0e0e0e0e0e0ef0e0f0e0f0e0f0e0f0e0f0e0f0e0f0ef0f00000f0f00000a0a00000a0a0000f0c0f0c000000000f0c0f0c00000000f0f0f0f0f0f0f0f0f0c0f0c00000000f0f0f0f0f0f0f0f0f000f000f000f00f0a0f0a0f0a0f0a0c080c080c080c08
|0,2=>0x303030003030300030303000303030000f0000000f0000000f0000000f0000d0d0d0d0d0d0d0d0d0c0d0c0d0c0d0c00f000f000f000f000e000e000e000e1010101010101010100010001000100f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0cf000f000f000f000f0e0f0e0f0e0f0ef0f0f0f0f0f0f0f0f0e0f0e0f0e0f0ef000f0f0f000f0f0f000f0a0f000f0a0000000000000000f0a0f0a0f0a0f0af050f050f050f050f040f040f040f04f0f0f0f0f0f0f0f0f0f00000f0f000000e000e000e000e000e000e000e000e3030303030303030302030203020302f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000e000e000e000e
|0,3=>0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0af0f0f0f0a0a0a0a0f0f0f0f0a0a0a0af0f0f0f0f0f00000f0f0f0f0f0f0000f0f0f0f0f0f0f0f0f0a0f0a0f0a0f0af0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a0000000000000000f0f0f0f000000003020302030203020302030203020302f0f0f0f0f000f000f0f0f0f0f000f000000000000000000e0e0e0e0e0e0e0e5050505050505050500050005000500
|_,_=>0
def sP:Nat→Nat
|0=>0x1d109c25b44a09a3c30980402123c30992484434022483cc4002473cc5004cf0c260021748f0c22471030802481c60802482d15832485510c52482c60c02443cc0c02123cc08921131024710c0040c238024d10c00920b18a2481c61440c2040
|1=>0xc20402483c31630092113cc0c52483c30a20092073cc1408483cc28225b54b0c20084cf0c50802483c30a000920f0df08024844f0c270921e3c26802481cf09c00848f0c200920f0c27402481d109a0092154430802482d130a2481d1305248
|2=>0x3c30802483c60c200920b3d60c020f0c50810092153c314025b44309a0099cf0c202120b44308848f0c22482d128308920f2828c024844f30a0892263cc0c025b7910c200920b44314920744314224894f0c200920b3cc2802483ca09a02420f
|3=>0x8085b3c30802483c30b00092113cc0c200920744308025b3c30af0096cf28308084f0c2b802483d628308024f3035002483ed0c200921e3cc08085b44308920f0d00802483c30ac00920f0c2ac024844f2826aa24f0c2600248a4f0c2009228
|4=>0x14203420b3c308025b443080a8920f0c50808483ca0c224f0c26002481cf30200920f0c2cc02482cf3030322483c314200920f0c2bc02487913c30802133c308024854f30308024844f0c2c002482d10c200920f5830802483f10c200921e3c3
|5=>0x3c3080c8920f0c200920f0c50802483ca0c20382483c308025b3c3080dc920f0c20093c30ae0212483c3080c899083c3080248d8b3c3080d0f0c2b8024898f0c20096cf303080d4920f0c20093cc0c2b802482cf2830802482cf0c50092073c3
|6=>0x920f0c200920f30308024844f0c2009e483c3080248
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x1e5065414503d40a50154005
|5,0=>0x22188261f187661c186a619185e61618526131846610183a60d182e60a18235
|6,0=>0x7019b976c9dad5699d9f7661d917629d8375f1d7575b9d677581d59754d94d652154174e9d3374b1d25747d9187445d0a740dcfc73d5cee739dce073698d37331cc572f9cb772c1ca9728d89c7255c8e7
|7,0=>0xafa2b68ac1aa97a89e9b7a51e8c8a15e7d89d9e7069a22626971a557939e4778fe23878c222a688a21a884de0c7815dfe77e19f177a61e2776ddd477399c68
|8,0=>0xc41f097c09efc6bd5eee7b9dee07b69ad37b35ac67
|9,0=>0x3176
|_,_=>0
def wAt:=mkWire dB 58 124 0xfffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 14
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xcf4c3f083402e08f483d00f4f01002423d0804f29247833d30fc20d080400d240430920f423d247033d3ca8a0b0c0403d4c0491c0cf510f00f4b0d08f42014c0491c0cf4b283c243013c35301247033d0cf51300834a090c04f310c251300834f5120502010c25301247033d3c3440d
|1=>0xf423d2824301300c3093ca4301240483d442cf010c24f010cf403d6c3c83d20f4301240483f28243010834814080510b3ca4301240483d00f4b283c243013d6910f00f48160804c033d64a0944c03093c04a090c0491e0cf4b0d08f483d443c03d3d84816080403d240423d4c0491c
|2=>0x3093c0480924f42010c0490920f492120fc901200493d00b423d240c83f00b823d20f420d24542010c2483f3c24301002423d3c34201240c23d20f403d002490d240430120582010cf420d2c3c23d083423d080493d6c3c83d443403d247033d30f420d442cf01
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x11000001000000000
|5,0=>0x1c10000000001931630001510001231110f20d20b2092063024
|6,0=>0x6536416225f35c35b10005925725615425134f24d24b24834534233f30003d20003b23923633510000003413223020000002f12c32a22820002712522410002130001f21d2
|7,0=>0xae2ac2aa2a82a62a42a22a029e29c29a29829629429229028e28c28a28828628428228027e27c27a27827627427227026e26c26a2682
|8,0=>0xba1b91b81000b71b61b51b41b31b21b11b01
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 12
def pmP:Nat→Nat
|0=>0x8180001c35000685400037d0000ca00003000000924000175000058400014000004800001150000410000100000031400008000001a0000064000014000004000000c000002900000a000002400000500000100000020000004000000c0000020000004000000
|1=>0x206c540818150200c4406ddf501b235406c1f5019675404e4f501383f404e0d5013535404907c0114354044bd500b27740248d500800500140d700503540100c7003bfc400ddd70035bd400c2dd00167540052d500127740040dd00103540040d100081b0002068
|2=>0x819035d00dcd521b3354400443088121020c4d7081101c18c8ed06000b410ebd50432f5410c8ed043235410234102323f40859d5
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x1000400000
|5,0=>0x500000010e0010006084040c10611
|6,0=>0x110914f039a003460936709810c3979e58005922c3ce850054f900c48005563c180344d0005a0070b
|7,0=>0x96f524062a94177e652b998e184483224bb42ba3947d1a2b7789cc3476e94c2
|8,0=>0x86ce7a394c9b4e7335335
|9,0=>0x23
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 7 (j%128);fld (pmP (k/32)) 26 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_122 7 roots_122 ops++addP pm 1 dom_74 4 roots_74 ops++addP pm 2 dom_115 7 roots_115 ops++addP pm 3 dom_81 4 roots_81 ops++addP pm 4 dom_59 7 roots_59 ops++addP pm 5 dzo_81_32 4 roots_81 ops++addP pm 6 dom_121 7 roots_121 ops++addP pm 7 dom_107 7 roots_107 ops++addP pm 8 dzo_42_16 4 roots_42 ops++addP pm 9 dom_42 4 roots_42 ops++addP pm 10 dzo_91_32 6 roots_91 ops++addP pm 11 dzo_106_16 5 roots_106 ops++addP pm 12 dzo_83_32 5 roots_83 ops++addP pm 13 dom_57 4 roots_57 ops++addP pm 14 dom_91 7 roots_91 ops++addP pm 15 dzo_89_32 5 roots_89 ops++addP pm 16 dom_73 4 roots_73 ops++addP pm 17 dzo_107_16 6 roots_107 ops++addP pm 18 dzo_43_16 5 roots_43 ops++addP pm 19 dom_114 4 roots_114 ops++addP pm 20 dom_120 4 roots_120 ops++addP pm 21 dom_83 5 roots_83 ops++addP pm 22 dom_89 5 roots_89 ops++addP pm 23 dom_75 5 roots_75 ops++addP pm 24 dom_90 5 roots_90 ops++addP pm 25 dom_106 5 roots_106 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_123 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_zo_81_32_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_42_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_91_32_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_106_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_83_32_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_89_32_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_107_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_43_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_120 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_106 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_122 7 s (0,roots_122.map (·&&&dom_122)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_123 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_122 h
def symsG:List (List (Nat×Nat)):=[[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_123==dom_123)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_123 gM v ys):RunD true dom_123 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_123 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 7 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 18 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 18 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 46 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 46 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 36 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 36 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 12 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 0 = true)
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
def dzo_93_32:=0x33333333000000003333333300000000
def gzo_93_32:=0x33333332000000003332333000000000
def gsh_93_32:=0x333333320000000033323330
theorem lowS_zo_93_32_81:Lower true dzo_93_32 roots_93 gzo_93_32 6:=lower_iso_b (d1:=dom_93) (r1:=roots_93) (T1:=gsh_93_32) [(dom_93,32)] (by decide +kernel) (lower_slice_b (T:=gsh_93_32) [(0x303030300000000030303030,0,4),(0x330033000000000033003300,0,8)] (by decide +kernel) lowS_81)
namespace S_125
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(4,20),(4,36),(4,68),(5,13),(5,21),(5,37),(5,69),(8,9),(8,40),(8,72),(12,13),(12,28),(12,44),(12,76),(16,17),(16,20),(16,80),(24,25),(24,28),(24,56),(24,88),(32,36),(32,40),(33,37),(33,41),(33,49),(33,97),(48,49),(48,52),(48,56),(48,112),(64,65),(64,68),(64,72),(64,80),(96,97),(96,100),(96,104),(96,112)]
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
|4,0=>0xc9263c71afa377b6a595648ba5ec435ebfb44f49325072318601a30
|5,0=>0xfe867f2b06e8db2e5f62def52dc7c5d6b3dd425dcfb27ca57bbfbebbd62bbcd2abcce2b9872b78e7b04e1a815b9f9ac969c195581922e88e74b7629e75e2a74bc173d767268e700f56fddb6fb566b1996a7e36892b67e4b64c25637bd611b45f3f55c80a5bf7057f6757271565be54852528f0520ae51d90511dc5035949ff549acd44baf4284842571413f640b763d96d3d1ba369bd3519b33e5d339cf31c25313d930ad62b6f429d72297cd2908028a2927582261dd246b824190210d420ad0203891bbb01a94d183721816a1529714dcd115ac10e5e0e20d0bd7309a2b0984c08c9408bbb087230780604f1d04898
|6,0=>0x4b1894a9ba4a0af49c7548a7e4880747bcf477d24768f46e4046945465ed45c124589c4568e450a4449c642b234250f41f5d400eb3fabb3f6b23f22e3d57a3d1ba3b83f3b2c13918d38ec838874386a9380983786b377cd36eb43661632fe1316e730c993031b2d8882d3cd2cd072cae72c8d62c7a82c4b92b0232a2e529eed29d72297c628d9a288262879227b8f2720626a932516c24d0223bce23a66233f52337c221ce2198d2171a2127e20337201201ff9e1fc791eb441e8e01db671d9a51c18a1bb9f1b48a19ba71977a1976d194ac1821e18168174cc1716015ce315c7b15279150b214b2813840131fb12b0312230119170fa670ecbe0e2e50e2860e20d0d8560d52b0c9db0bd1f0b1a00aaf90a5570a2b40a24208c9608bbb085f50635605d0805b1b03f1f0369c03185030100291c01d35018e50187f01541000ba
|6,1=>0xbee66be4d8bd62bbc176bbb73b8f6eb7257b673ab5f76b38e5b012cabff6a8164a6ebaa6e66a5a16a1e31a01329f1cb9da3d9d3479acba99b029762f950e69370b932b991bb49175a916508f8d68e29e8d28e89c548875e87f12871f185d1983e6d81c0881631815797fe617e3bf7e2337dc2e7d5787d3157a7467a36a79f21781f7774b17735976d9475e3c75bcf74f3874a1c7409773cfd73977730d4715607154f71381711e57114a710056fd2d6e2906d9266d8bb6c1646bb876949e65c716567e6509963b7e63a4a638b2637c1637bd633d362eb762e05620f161eff617b46111560988600085fbaa5f8615f2fe5eb0f5e56d5dfc65d4145c7355c6ff5c0915c04b5ac2b5a85d5a4385840457d315747b567f35588654ac6548145407453ae951d485190150fe54f7bd4f6204f3514e9ac4de904d9b84befa4b80d4b4e0
|6,2=>0xfce3ff7409ef4c6ea7e7ea49fe9135e8d06e8733e4e3fdf054dadb7d5b71d2c3ecf200ce8d4cca9dcbc2ec9d35c8fa1c637dc50eac3819c340fc13d5c11b8c0d2ac0b7ac0682bf415befb7
|7,0=>0xe4701df054db0cfd817ace613ca767c9c45c500dc3469c2dc7c284dc1b50c0682bf1a8b993eb5f76b3183aca81ac938ab9d89c54c9c30596ef693b4291ba590aac8feb18de6988d2c87959879118624985cb082dc181f3e7fdb17d5787bec67a1b8794bb77b427687971f3670b7d6df03698916926e68b0e67bf766dd36590f63c4662a2b6241c6235561739616655f5a35d3c55b6115abdb5a6e557de756dfb5606d5519153cd853ae9534134ddf74d14f4c7704a98648ece48c6947f7145bba44f974487d4329141de4410d93eb0c3d0e239c4b399bd3553532e122fbab2ec392c2242afe42a36028252264cf239672357222110217962102f2047c1eab51d3481bd1d1a37e1670d1580d15248149991402212fe412c3b12360109bf1099d0e4b00dd7a0d8560bf9806b1206708052fd04a5802abe01a5b00ab40042f0005b
|7,1=>0xf6bcce71a7
|8,0=>0xec553d6022b382aa859e8e2268d60a7f2e47749274b3a71a8b62a2d534134c6cf4624f228b5213f113d2e0f7ba
|9,0=>0x7f2e4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xccccc0c0ccccc0c0ccccc0c0ccccc0c32323232323232323232000032320000ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc32323232323232323200320032003200cccccccccccccccccccc0000cccc00032323232323232323232323232323232cccc8888cccc8888c0c08080c0c0808333333333333333333333333000000000000000000000000cccc8888cccc888b30033003300330033003300330033004444888844448888444488884444888b3333333000000003333333300000000cccc0000cccc0000cccc0000cccc00033323332333233323332330033323300c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c33333333333333332222222222222222
|0,1=>0xcccccccccccccccc888800008888000332233223322332233223322332233220000cccc0000cccc0000cc000000cc033003300330033003333330033333300cccccccccccccccccc00cc00cc00cc0333330303333303032323030323230300000000000000000cccccc88cccccc8b33333333333333333333333222200000000000000000000444488884444888b2323200323232003232320032323200cccccccccccccccc00000000000000033333300333333003333330033333300cccc8888cccc8888cc008800cc0088022222222222222222222222222222222cccc8888cccc8888cccc8888cccc888b3333333333333333030303030303030
|0,2=>0xcccc0808cccc080b3333333333333333333333300330000cccc8888cccc8888cccc8080cccc80800330033000000330033003300000022cccccccc00000000cccccccc004400033330000333300003332000033320000444444004444440044444400444444033333300333333002222220022222200ccc8ccc8ccc8ccc8ccc8ccc8ccc8cccb33300003333000032320000323200000088008800880088008800880088008b3330022333300223333002233330022cccccc00cccccc00cc88cc00cc88cc0333333333333333332323232323232320000000000000000ccccccc8cccccccb3333333333333330033000000330000
|0,3=>0xccccccccccccccccc4c4c4c400000000000333300003333000032320000323200cc00cc00cc00cc00cc000000cc00022222222222222222222220022222200c0c0c8c8c0c0c8c8c0c0c8c8c0c0c8cb0330000303300003032000030320000cccc0808cccc0808cccc0808cccc08091110000111100001111000011110000cccccccccccccccc44448888444488891111111111111111111110011111100cccccccc88880000cccccccc88cc000333333333333333333333333000002028888cccc8888cccc8888c8c88888c8c80002222000022220000222200002222888800008888000088880000888800033333322333333223333332233333322
|0,4=>0xccccccccc8c8c8c8ccccccccc8c800033113300331133003311330033113300444444444444444444004400440044030303030303030303333323233333232cccccccccccccccc88880000888888880003333000033330000303200003032cccc0000cccc0000c0c80000c0c80002222222222222222222220202222202000cc000000cc000000cc000000cc0000000323200003232000032320000323200000000000000000c0c08080c0c08080330033003300330033003300330022000000c0000000c0404040c0404040c00000000000000003333002233330022cccccccccccccccccccc8888cccc888b3333333000003033333333300000202
|0,5=>0xccccc8c8ccccc8c8ccccc8c8ccccc8cb33333333333333333110000331100004444cccc4444cccc444488884444888b3333333333333330000111100000000cccccc00cccccc00c0c0c000c0c0c0011011101110111011101110011011100c0c0ccccc0c0ccccc000cc00c000cc0000033330000333300003030000030300c8c00880c8c00880c8c00880c8c008b3333332333333320000000000000000c8c8c0c0c8c8c0c0c8c8c0c0c8c8c8cb32233333322333333223333000000004444000044440000444488884444888b3333330333333303232323032323230444444444444444444444440444444403030202030302020303020203030202
|0,6=>0xc0c0c000c0c0c000000000000000002222222222222222cccccccc44444444cccccccc444400033332222333322223333222200000000c0c0ccccc0c0ccccc0c0ccc0c0c0ccc313131310000000031313131000000000808080808080808080808080808080b3333333333333333303330033033300c4c4c4c4c4c4c4c4c4c0c4c0c4c0c4c000033330000333300003322000033228c8c8c8c8c8c8c8c8c8c88888c8c888b3333333333333333333330033333300cccccccc0000cccc888888880000888b33300003333333333330000333322220000000000000000ccc8ccc8ccc8cccb0323032303230323032303230323032
|0,7=>0xcccc0000cccc0000ccccc8c8ccccc8c80110011001100110010001000100010000000000000000000cc000000cc000333333330000000033003333000000000c0c0c000c0c0c000c0c0c000c0c0c0002200220022002233330022333300224444cccc4444cccc4444cccc000000000320032003200320032003200320032cccc00c8cccc00c8cccc00c8cccc00cb3333333333333330011000000110000c0c0c0c0c0c0c0c0c8c8c8c8c8c8c8c80330022003300220033002200330022008c0088008c0088008c0088008c008b3330000333300002222000022220000c0ccc0ccc0ccc0ccc0ccc0c0c0ccc0c33333333333333330202020202020202
|0,8=>0xcccc4444cccc4444c0c04040c0c04040303030303030303020202020202020244444444444444444040404040404043333333333333333111111001111110044444444444444444444444400000002222000022220000222200003333000000000000ccc0ccc000000000ccc0ccc33333333333333333333332233333322cccc0c0ccccc0c0ccccc0c00cccc0c0330033000000000033003333000000008c8c88888c8c88888c8c88888c8c888803300330033003300330030003300300c0c00000c0c00000c0c00000c0c00011110000111100001111000033330000888888888888888888880000888800010101010101010101010303010103030
|0,9=>0xcc000000cc000000cc440000cc44000333333333333333333333333333300000c0c0c0c0c0c0c0c0c0c0c0c0c0c00001010100010101000101010001010100cccc0000cccc0000cccc8888cccc88880000000000000003333000033330000000000cc000000cc000000c0000000c33233322332333223323332233233322888888888888888888888888000000033332222333322223333222233330000004400440044004400440000004400033003332330033323300333233003332ccccccc8ccccccc8ccccccc8ccccccc80030003000300030002000200020002cccccccccccc0000cccccccccccc00000003333000033330000222200002222
|0,10=>0x4444444444444444444044404440444333300003333000033330202333302020000000000000000ccccc8c8ccccc8c80000000000000000033002200330022cc0ccc00cc0ccc00cc0ccc00cc0ccc0313131313131313131313030313130300000000000000000cc440000cc4400000000000333322220000000033332222cccccccccccccccc00000000cccc888b3333333333333331111000011110000cccccccc00440000cccccccc004400000000000000000002323222223232222444444404444444044444440444444401010101010101010101000001010000cccccccccccccccc00880088008800880000000000000003232323232323232
|0,11=>0x8888cccc8888cccc8888cccc888888880000000000000002233222222332222ccccc0c0ccccc0c0ccccc8c8ccccc8ca2220000222200002233000022330000ccccccc0ccccccc0ccccccc0ccccccc31313131313131313131000031310000cccccccc00cc00cccccccccc00cc00033333333333333333322332233223322000000000000000000440000004400000030002000300020003000200030002ccccccccccccccccccc8ccc8ccc8ccc800002020000020200000202000002020000000088888888000000008888888b3330000333322223333000033332222000000000000000044440000444400022222222222222223333222233332222
|0,12=>0xc0c0c0c0c0c0c0c0c000c000c000c023232323232323232322232223222322c4c4c4c4c4c4c4c4c4c4c4c4000000033333333333333330303020203030202000000000000000044444400444444011001100110011001100330011003300444444444444444444440000444400011111111000000001111333300000000000044440000444400004444000000022222222222222222020202020202020c0c0c0c0c8c8c8c8c0c0c0c0c8c8c8cb3003300330033003333332233333322c0c0c0c0c0c0c0c0c0c0c8c8c0c0c8c803300320033003200330032003300328888cccc8888cccc8888cccc000000030303030303030303333333033333330
|0,13=>0xcccccccccccccccccccc0088cccc00880000000000000003333000033332222cc44cc44cc44cc44cc440000cc4400011111111111111111111111111110000000000000000000000000000cccc888a0202222202022222020222220202222cccccccccccccccc0c0c0c000c0c0c033110000331100003311000033110000000044440000444400004400000044033333333333333333330333033303330cccccccccccccccc0000000088888888303030303030303030303000303030000cc00cc00cc00cc00c000c000c000c333333333333333330303232303032320c0c0c0c0c0c0c0c0c0c08080c0c080b3033303330333033303330033033300
|0,14=>0xc0ccc0c8c0ccc0c8c0ccc0c8c0ccc0cb33300003333000033220000332200000000000000000000080808080808080b3333333000000003333333302020202cccccccccccccccccccc0808cccc08091113333000000001111333300000000cccccccccccccccc4444cccc00000003030333330303333303032323030323200000000cccc000000000000cccc00033333333333333332222222233332222cccccccccccccccc00000000ccc0ccc0303000003030000030302020303020288cc888888cc888888cc888888cc888b3223300332233003322330033223300cccccccccccc8888cccccccccccc88880000000000000003333333333332222
|0,15=>0xc0c0c0c0c0c0c0c0c0c00000c0c00000003333000033330000333300000000ccc0ccc000000000ccc0ccc00000000333333333333333333303330000000004040c0c04040c0c04040c0c04040c0c3333333300000000333333333333222288cc88cc88cc88cc88cc888888cc88880000000333333330000000033332222cccccccccccccccccccccccccccc888b33333333333333333333333020202028888cccc8888cccc8888cc888888cc8b3333333222222223333333322220000cccccccc08080808cccccccc0808080b3333333000000003131313100000000cccc8888cccc8888cc888888cc8888880330033003300330022002200220022
|1,0=>0x4444cccc4444cccc00000000000000000110000001100000011000000110000cccccccccccccccc000088880000888b3003300000033003300330000003300cccccccc88880000cccccccc888800022222222222222220000222200002222cccccccccc00cc00cccccccccc00cc0000000003333333300000000222222220000000000000000000088880000888b33333332222222233333333222222220000000000000000cccccccc000000022222222333322222222222233332222
|_,_=>0
def sP:Nat→Nat
|0=>0xd8040004068184c120a810480b0300400040188c02120a8101e0b0308824041080c0c01090102206008004004078181c120a81022060087c08030f004001d04070061b00848080b0306824080c80c0c010902022060085c3011030042e08030040a17020441a160a8202813008480811030382004078181c000200c1a0c000101606050241007030040a04018080200
|1=>0xa06c02121c01006060600400041c82c0c01000100c010285c2a04030046e050a8100606008d82a350181802120a810220b0308802340181802120a8100c01198c82a080881802050a81060030d80400040186c0212140205e0303004242e0186c0c01090105a03030282a0401804242c0a8ac0606008482a041501802120a820061b0084852040881802280a8100627
|2=>0x230541003030042445020440c16008540811030042e15020440c010f85c08030084888150401802050a81006060910c2a040881802370a82084030300424041802c0c010001016060084850042081802050a9000606008482a03030fc20010902060030d80424080304002121f0102206008007a0401818023c0a82006061d8402404030e802120a8200e03030280208
|3=>0x200c0c5209054080303004a2150202c0c01001409e030300424150200c0c13008001011030043e0401938024d0a86022060087c080303028121504130060600848100303004121204044060605040100303004244b02018021225054084108818021f0201892010905408030686c14000204416060080008140883414150200c0c0a240541007030042447020180229
|4=>0x217c1606008482a04019780c0109054081103004ba15040184c1000848100303004245c0200c1a5b0905408030685824150200c0c012d0540803069642415020440e060087c08060516064150200c1a122b85408030300424560401c06060084808110581814100203c1606050001003031542415019500c01090540807030040a15020440c01298541011038180231
|5=>0x1818021237854080303004dc500a8100e0303004d215368100606008482a043600c0c01090540803031ac02120a81022060087c06061f80424150400c0c0a008c82a04019a00c010905408030319c02120a810060600848cc150200c0c01328482a0408818021f0a810c8110300424150200c0c010918c2a043100c0c010905408033081802120a8100606300402415
|6=>0x9054080303004247e0a80cf81b03004241502090060d008482a040581802123d854087a0181802120a820060600848f215021dc0606008482a040181802123b054080b018780c010001006063a84024150200c1a1b050482a040181802003a05408030300424730a8100623008482a040882c0c010905410110186c0c010901006063880424150202c060600848e004
|7=>0x905408061109802120a81110030300424150221c0606008482a0401818c00100054100f01818201201a180c0109054060600848f2150200c0c01428002a0401818021242054080b030040012418201e030302824150200c1a06110482a040a00c02123a05408110300502150400c0c01092082a040a00c0212268540803030490015021fc0606008482a08019380c01
|8=>0x30046c15042580606008482a040181802124a85408034a01802120a8112603030042415020502206008002a0401818021249054080303004704d0aa4408060084920150200c0c01478482a040880c0c0147054080303004243e0a8101e03030491a1502050061e008002a040882c0c0100048080303004248c0a82006060084914150880c0c01092242a04018182601
|9=>0x1b0554a030300424150200c0c01520482a080880c0c0a0085408030300424a30a8100606050049a150202c06060504024040181802125105408030680424a10a810060d0328024150200d3e06008482a040881c0c01188540803030493a150200c0c01092702a044d80c0c0a0085408144d07802120a820060600848e8150200c0c01092642a0401a600c01090540803
|10=>0x5800c0c010005408030306824150200c0c01092bc2a040881802002385408ae0181802120a810060d0920c4a15022b40606008482a040181802125605408030f2ac02120a81006065500424150200c9c1b008482a0401818023c0a81006060500520150200d5206008482a04018180212538541003030050a120a8102806008494c150200c0c22008c82a040a00c0c01
|11=>0x85408030300578120a8101e03030882415022ec061b008482a040a00c0c011e0540803032e802120aae40606008482a040e0440c010905408030300424b70a810be0303048a0150200c0c01092d82a04018340c122805408110581820010901006b50300424150200c0c01002d02a045902c0c010905408030304024460a820080701818021202070061e008482a04
|12=>0x1300400120a82006060504024040580c0c010923808c40181802120a81006066180424150200c0c01093082a042080c0c0a0085410030300582120a810060600a14dc15023000606008482a04018184401090540803030057e120a810061b030280200020900606008002a040181802be0905408bd0181802120a810220600848fa150202c06060500400040a0440c0a
|13=>0x181802ce0905410030d81802121c010061e0d80400030333402120a81006060084998150200c0c010932c2a040780c0ca009054080b030042472040440c010911c2a040380c0c010004808030084994150200c0c0164acc2a030300424c80a81028035c00424150400c0c010931c2a040181814c60a80c0c0100049121502050160d008482a040580c0cc5090540806
|14=>0x8482a040580c0c124e8541006008e064150202c0606008d82a0401b580c0a09054080b0181802126a81028110d80424150200c0c01093502a0401818141269854080b0181802125081006066900424150200c0c01093442a080181802125a05408640181802360a8100606008008c15020502201091d02a040882c0c010001006d00300424150202c9c06008482a04
|15=>0x181820120a81006dd0300424150202c0c01091d02a083600c0c0109054080b0300400122381016060080024380200c0c01093702a040181802126d854080b0181802124681022070181802000200c0c01003682a040181802126c85410036c01802120a820c8030d8180212020e40606008002a040a01802125885408030300424d70a810061b030046c15022ec1606
|16=>0x30282a081c80c0c010905408140587802120a81006060084850150181802127285408030300424e40a8100606050045215020500627008482a040181802e3000541003710042415700100606008482a040183402120e85408061304002120a811be03030042415021040c010911c2a0801818021214854080303004241f020440606500042a046f00c0c0109054085f
|17=>0xabcc1603030042415040c00606008482a040183436124185406067900424150200de206008482a04018340212780540803033bc02120a81016030308802120200ddc06008482aec0181802120a811d6030300424150217c0606008002a030300424e90a8100606740042415020c13406008482a040181802e60905410110380c0c0109010060608048f01502044060d
|18=>0x21042206008c42a040380c0c0a0085408140d80424380a8100623030042415040440606008482a080186c0c01091f41003030057e120a81006270d80424157b00c0c010905410070181802120200c0c017a8482a0801ae03606008480811030040a150200c0c010915c2a040186c0c0109080089b0181802120a8102206008484015021040e030300424f4018180212
|19=>0xf8600606008482a080181824fb0abe808030300424150c00c0c010907c0806008142a042080c0c0109054080303005f2120a81028030682824150200c0c012d8482aec0181820010905410110300462150200c0c01198482a04018182c010905408030300424f80a81006060080024a60200c1a01000942af70200c0c0109054080303004b2120a8101603068182012
|20=>0x300424290a81006b80300400120a8100606008491c15020c02203030042415020441606008482a0401878360109054080b0300424830a81006d80300424150200c0c01091f42a04018181401000540806008e064150200d7006008482a041200c0c010905408640186c0c0109054081c0181802120a80df8060084806fc0300424150200c0c010931c2a08018180212
|21=>0x849aa1502104160303004241502050061b008482a080181814010905408390181802120a810060600849fe15020440e030300424150400c0c01093f82a04018180212508540811018340c010905408030331424150400c0c010911c2a080181802121c05408037100424150202c0606008496615020440606009a42a040880c0c01092a02a04018340c12418540803
|22=>0x8484a150200c3c060084906150400c0c01090c42a040580c0c01091a42a040181802122c05408030300424a80a810060605004dc15020c00606008482a0401b580c010905408030300424d30a8101e0b0300424150200c0c01800482a04018180212418942a040a01802121c054080303004248d0a81006270300424150400c0c010925c2a08018182001090100606
|23=>0xf01802120a810060600848f6150200c0c010940c2a04018182001090c82a040880c0c01091402a04018340c01000482b020202c0606008482a040181844010905408110181802120a810060600800d2150181802124485408030d81802123e85408070181802120a81006b80d81802120a82008110181802120a81060140181802120ac0422030300424150200d3406
|24=>0x780c3c06008482a0401b580c10008482a0401818021210054080303004248b0a81006060084a0c150200c0ca0008482a040580c0c01090c82b050202c0606008482af30181802120a81006061100400120a8101606008487015020440606008002415020502203030042415020440c011885408031381814010905408030300425040a81006060080024830a810069a
|25=>0x93a82a0401818760109054080303004250a0a81006060084902150200c0c220500424150204406060800424150203c06060080024154f0100606008482a040181802128485408038400424150200c0c01091402b010a00c0c0109054080303004241f0200c0c127d85408030681814120a810060d0304024150200c0c010907c2a03031a802120ac1c0606008482a04
|26=>0x300424900a81006060500400120ab840803030042415020500606050042415020500606080042415040440606008482a037e81802120a82006060084906150226c0606008482a04208440606008482a0408a680c0109054080f0181814120a810061e0304002120a81028030300400120a81016030300425030ab8408110181802120a810061b0300424830a80c0c01
|27=>0xac040606008482a0401a680c010905408110181802120a81006060084906150200c1a06008482a04018180212190560a040181802120a810060600849ce15810100606008482a04018180212858100606008498c150400c3c06008482a042080c0c010905408030d81802000901016030300400120200c0c60008482a9e0202c0606008482a040880c0c0a008540803
|28=>0x8030300424150400c0c010905408030300424310a81006060800424150200c0c010911c2a040181802000905408140181802120a8100606008482a04018780c01090541004018180212
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x32502d50285023501e50195014500f500a500550005
|5,0=>0x1ae61a861a2619c61966190618a6184617e61786172616c61666160615b5155614f61496143613d61376131612b6125611f61196113610d6107610160fb60f560ef60e960e360dd60d760d160cb60c560bf60b960b360ad60a760a1609b6095608f60896083607d60776071606b6065605f60596053604e50486042603d50376
|5,1=>0x26c62666260625a6254624e62486242623c62366230622a6224621e62186212620c6206620061fa61f461ee61e861e261dd51d761d251cc61c661c061ba61b46
|6,0=>0x421741a7413740c740573fe73f773f073e973e273dc63d663d063c973c273bb73b473ad73a673a063997392738c6385737e7377737073697362735b7354734d7346733f73387331732a7323731d6316730f7308730172fa72f372ec72e572de72d772d252cc62c572be72b772b072a972a3629c7295728e72877280727972727
|6,1=>0x5db75d565ce75c775c075b975b275ab75a4759d7596758f75887581757a7574656d7566755f75587551754a7543753c7535752f65287521751a7513750c750574fe74f864f174ea74e374dc74d574ce74c774c074b974b274ac64a5749e7497749074897482747c6475746e7467746074597452744b7444743d7436742f74287
|6,2=>0x792778b7784777d7776777067697762775b7754774d7746773f77387731772a7723771c7715770f6708770176fa76f376ed66e766e076d976d276cc66c576be76b866b176ab66a4769d7697669076897682767b7675666e7667766076597652764b7644763d7636762f76287621761a7613760c760575fe75f775f075e975e27
|6,3=>0x9487942693c6935792e79286921791a7913790c790578ff68f878f178ea78e468dd78d678cf78c878c178bb68b478ad78a768a078997892788b7884787d7876786f78687862685b7854784d7846784068397832782b7824781d781678106809780277fb77f477ed77e677df77d877d177ca77c377bc77b577ae77a777a077997
|6,4=>0xa125a0c6a0579ff69f969f369ec79e669e159da79d379cc79c579be79b869b179aa79a3799c7995798e7987798079797972796b7964795d7956794f7
|7,0=>0xbdd8bd58bcd8bc67bbf7bb87bb26baa8ba37b9b8b938b8b8b847b7c8b748b6d7b658b5e7b577b507b497b427b3b7b347b2d7b258b1e7b177b107b097b036afc7af48aed7ae67adf7ad87ad08ac97ac27aba8ab46aad7aa67aa06a988a917a898a827a7b7a738a6c7a648a5d7a567a4f7a487a417a3a7a346a2d7a267a1e8a177
|7,1=>0xdad7da67d9f7d987d917d898d827d7b7d738d6c7d648d5c8d557d4f6d487d417d398d327d2b7d238d1b8d138d0b8d038cfd6cf67cef7ce87ce08cd88cd08cc97cc27cbc6cb57cae7ca86ca26c9b7c947c8d7c876c816c798c718c6a7c637c5c7c557c4d8c458c3f6c378c307c288c208c1a6c128c0b7c038bfb8bf47bed7be58
|7,2=>0xdbb6db47
|8,0=>0xe366e2f7e287e217e1a7e137e0d6e067dff7df96df27deb7de47ddd7dd67dcf7dc87dc17
|9,0=>0xe3c6
|_,_=>0
def wAt:=mkWire dB 268 126 0x3fffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 9 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x20550184918855018480207d018491885501848088400184901849018480905500849090e1018550184b018190900d008490887f01849018480887f01849018481c0c90184a0900e02055088c70184901848088190900d000500300d090510300d0506c090051c0c90184b0184a1c0c90184b0184a09055088c701849018480881901849000500300d0a0000f0050304909055018950304a090410502c01855
|1=>0x905501849058480900d0185500a070902c021f70d80e018950304a0a0070300d040c701848019e10501b03049018550804a008550881b0900d031c90180009055018c90900f018550900d02055008f50185501855348550a043008550902e040440184901849188550184835055021a70084a020550900f0906e0184918855018480a05513857008950304a0500d00849208c70184901848090550886c01849
|2=>0x80e1c0550184b05055091920a0550187b03049020550900d0906e03055128550304a050570084901848018494f0070202d0185505052008493700d09057030490881b0900d091920d80d01a5d04048018550500f0a0490905501802090550085501855018490a04b0300d01a2f0404b020360886c0900d008950304a00855020550080d020f70302e01855040c702055018480920d0080e090550205500801
|3=>0xacd0204a018880080102055008490085509055088550900d0a0570084909055018950304a018190900d00849019370906e050550a0050300d03055091900a055059a701855020f50302e018550185701ae30500d0184908807018490905501acd0204a018550500f0084908857018490304901857092c50180309055009c90180009055090190080e030e10900e091900d80d018020905554055018490920d
|4=>0x18550184b0804b08857018490920f0080e01803090553204b0d80d0680d00819018554f0070202d0184a0900e02055091920302d00855598550185500855018550903f0d80d0500f0084901849018490185509055030e10900e0933d030550900e02055030490905503055041a70084a02055050570000c0905501849032070902c022070902c01855040470184909040008490085502036030050300d01855
|5=>0xd80e0305501849022050902c021a50084a01879030490080e023b70804a008550300209055009d10900d09041023b50804a0500d0084975055020c70184801802090550039d09055018490501b00849008550900d00849019a50084a018550a000018190905502036030050a04b0300d030490911d0300e02055030c50900c70857018490d80f030551100c080490185509055050570500d008490404401849
|6=>0x184a0906d03055018950304a0d80d030554d019018577e855020347e855020340300504047018490205518855018480207d01848008c702055018480207d18855018481c0c90184b0184a0a04001819023b50804a0205501849018480a0280184b090550180109055018550184901848088570900d03055090e10900e020550d80e0501900849021c1348550084a088570184902055088c701849018483e855
|7=>0x184b0300d0804b00855050190084904048020550205500855598550204a0902d018550300d030550205500849019a50084a0082e0185508857018490400f02055128550304a0184900acd0204a0300e020550900e02055030c50900c0204a018550084a0184901849030050080e0a04b0300d030010905500802090550900d0900d0185509019030550080e01855018970304a0d80e0305500849090550184b
|8=>0x5019008490200209055018070905501857030490a0070300d0902f018550184a008550880701849030050905502049018550804900855018490084a0905502036030050d80e0305508857018490906d03055018490a0490300d0184902057018570304a030490080e020550184809007018550184200855020460184909057008490a0490300d030410085503042008550080d018550939d0200e0304a0080e
|9=>0x1848008c90184a0187b030490902c0185505055008490184901805090550202d01855190550184a0339f0200e08807018490300d020571885501848008c701848008190084903005008551885501848021a70084a020c50184801805030490304100855238550300e0404b020554d04a0185705057008490900f018550201901855021a50084a00801090550900e018550184909055018490300d0184901848
|10=>0x90550300d03049020550205701857018490080e030050184a020190200e02049188560184808048008550205503049018010905509055030550185509055008950304a0202d018550900d00849018020905500849090550204501849008490300d018190085502055018490203403005020550080e3700d0905701849018570900d0080d00849030490085501819090550902f01855018490080e03055020c7
|11=>0x205501848008550300e
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x34200003220bcc2c3000000000000000000293098c000089000007cc00007481b20000000000019200000000000000000000000001720000143044c00000001010000000034c0b202480000000000000000000000000204053000003200000210000000004400100000000000000
|5,1=>0x10cc000000000000000000000000000000000000000000421000000000000000000000000000000004020f100000e1000000003620000000
|6,0=>0x97225489322484902000000000008e222cc883214c832000082120447f21f847b300000001e4800000000001dc87521cc80001c486f21b846d11ac80001a48000198c63318485f217485b2000000016845820000553148c50200004f10000000130c4b1000000012844821188000
|6,1=>0x3908e133804df13784dd136c8000368400035ccd5234c8d12338ccb3000000000000000000000324800031c8c5230c80003048bf22f48bc12e88b820000b620000b4200000002c88b020000ae22acca9229c8a6129080000000a2228089f127849d100009c100009a226440000000000
|6,2=>0x4dc80004d493234c092d34ac92a14a08000000127149840000001251490522248451e300011c24689182454d123000000044450f200010e14308000424c00041c904340890023f88fc23e4cf8100000000000f6200000003d440000000f323c4800000000000000ee33b08eb13a0ce62
|6,3=>0x62898736148000610581300017e300000005f457b25e497725d8573300017125bc96e100016c200016a259cd652000163258855f357495b25685573554800054c952154094d352c949251c8000000000051494410001422000000050080004f8800000013d14ec939200000000000000
|6,4=>0x6d49b236c09ad36ac9a830001a53688c000000000068099e266cc0006684000660800065880006545932644990100018d36304000
|7,0=>0x8c0a2e28b0a2a28a46272894a232884a1f287861c2868a182858a142848a102838a0c2828a082818a042808a0027f89fc27e89f827d89f427c89f027b89ec27a89e827989e4278c5e1277c9dd276c9d9275c9d617509d227409ce27345cb27249c727149c327049bf26f49bb26e49b72
|7,1=>0xab4aab2aa4aa72a94aa32a84a9f2a74a9b2a64a972a54a932a44a8f2a3868c2a28a882a18a842a0c68129fca7d29eca7929dca7619d0a7229c0a6e29b0a6a29a0a662990a622980a5e2970a5a2960a562950a522940a4e2930a4a2920a462910a422900a3e28f0a3a28e0a3628d0a322
|7,2=>0xac4aaf2
|8,0=>0xb0c6c21b046c01afc6be10002bd1af06bb1ae86b91ae06b71ad86b51ad06b31
|_,_=>0
def PO:=mkPO wAt oP oO 20 9 511 14
def pmP:Nat→Nat
|0=>0x8000003cc0001e40000c300006100002440001200000840000410000204000100000074000039000018c00008400004000001d00000c0000056000024000011000008000002600001200000880000400000180000060000018000008000002000000
|1=>0x410000200c0010040007230003908001c44000e020005ef00029100014080008600004010002000000c000004600002110000ff80007ec0003de0001eb0000e7800072c00038e0001af0000bf80005ec0002860001310000910000480000204000101
|2=>0x9ca1804a78c0233a60111fb0088f180444cc0201c601004a0080240040100020004009b13004cb9802454c00c0000041420020400010008008000003b730012f180086880022ae0010010008000002c00001440000a000004908002444001202000822
|3=>0x200ed810070c0803720401820200c0810048808024204010002007901003c008012c04008c020043010020808004004001102000181000080800000211530100a3808021804010402000600cca9806650c0330260171eb00b8a5805479c02a3c6014048
|4=>0x4000001905cc0c20260601eb03004b01802180c010406001202b8e5814876c0a42e605215b028ca181415cc0a03f60501f30280e9814070c098006044b010223b181115cc0882e60441530220a1811001c0880060409010200ff81007ec0803e60401eb
|5=>0x1220f889105cc4803402025e31012b18806dcc4003402001201000800500400240000109b730845808408698204344102167081000040069020024c10000006b8a583117ec188b960c11d30423a58210308100ae608053104020002008041003e6080093
|6=>0x405558e0202048940424298a1a05c70d0040044c11d12048ab902001c803fe2401bf32008e3900454c8016424009db2000fd90007ac80010e4000832000088d80400684286246173
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x2000000000000000000000000060000000000000000000b1b0014000002000000020032173900000000000202001300020002020000000200000000000000020002020000060000020202000000000000000a21000200060000060500000000
|6,0=>0x1210a33c3441f004400170210716e8500000000000071000223010056021f061f51000700010000011f0002111f016d020000024e3344440044001015000000001702d10a0b0000000265501302006d061fb71700ac020000001f01020011014d0a163f02008617221f191f00009f0200271e01004400002f0a0000443d0200
|6,1=>0x400d10000c2e0078000068020202461c00341f06000200021301001002413a020a3755000131021d56010100000074060002000011001700000617020000b5001f001f03027702454f00003f180000470a021f9a000201224a590000069800040200110002c402a2020266060000000100004400001f02000000002036063e1f
|6,2=>0xa4a511760f1200762600003508481d000e006e00a3003002016d0017af00
|7,0=>0x5e6bb29ac8d4d029c56324428ea5932c6875d0432369608481c78a9cce0709ab2d92a88b8280cd5483a19124b39ed282ca99d55cce9b73bd2ec9636f7aba2c1a703c58cf7e285ab67eae58b9a97c7990a05297c6bbb4539d967bbf52cc5b67626ac15d2e6c72d32b3b61958f82a67d578cbcad49b899b18d7f89cb82b02ac2be
|7,1=>0x812e
|8,0=>0x5f82528938c07e4b63a788aa874c82d69464
|9,0=>0x25
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 25 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_121 7 roots_121 ops++addP pm 1 dom_61 7 roots_61 ops++addP pm 2 dom_60 4 roots_60 ops++addP pm 3 dom_92 5 roots_92 ops++addP pm 4 dom_105 5 roots_105 ops++addP pm 5 dom_116 5 roots_116 ops++addP pm 6 dom_93 7 roots_93 ops++addP pm 7 dom_124 6 roots_124 ops++addP pm 8 dom_117 7 roots_117 ops++addP pm 9 dom_81 4 roots_81 ops++addP pm 10 dom_84 4 roots_84 ops++addP pm 11 dzo_81_32 4 roots_81 ops++addP pm 12 dzo_89_32 5 roots_89 ops++addP pm 13 dzo_85_32 5 roots_85 ops++addP pm 14 dom_77 5 roots_77 ops++addP pm 15 dom_57 4 roots_57 ops++addP pm 16 dzo_93_32 6 roots_93 ops++addP pm 17 dom_45 4 roots_45 ops++addP pm 18 dom_109 6 roots_109 ops++addP pm 19 dom_73 4 roots_73 ops++addP pm 20 dom_53 4 roots_53 ops++addP pm 21 dom_101 4 roots_101 ops++addP pm 22 dom_120 4 roots_120 ops++addP pm 23 dom_29 4 roots_29 ops++addP pm 24 dom_85 5 roots_85 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_125 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_60 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_92 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_81_32_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_89_32_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_85_32_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_93_32_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_53 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_101 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_120 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_29 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_85 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_121 7 s (0,roots_121.map (·&&&dom_121)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_125 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_121 h
def symsG:List (List (Nat×Nat)):=[[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
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
theorem lowS_126:Lower true dom_126 roots_126 goal_126 9:=lower_slice_b [(0x55555555000000005555555500000000,2,34)] (by decide +kernel) lowS_94
theorem lowS_207:Lower true dom_207 roots_207 goal_207 8:=lower_slice_b [(0xaaaa000000000000aaaa000000000000aaaa000000000000aaaa,8,9)] (by decide +kernel) lowS_206
theorem lowS_215:Lower true dom_215 roots_215 goal_215 9:=lower_slice_b [(0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa,16,17)] (by decide +kernel) lowS_214
namespace S_219
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(1,129),(2,10),(2,66),(2,130),(3,11),(3,19),(3,67),(3,131),(8,9),(8,10),(8,72),(16,17),(16,80),(16,144),(18,19),(18,26),(18,82),(18,146),(24,25),(24,26),(24,88),(24,152),(64,65),(64,66),(64,72),(64,80),(64,192),(128,129),(128,130),(128,144),(128,192),(136,137),(136,138),(136,152),(136,200)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffff
def xsM:=roots_219.map (·&&&dom_219)
def gM:=goal_219&&&dom_219
def NN:Nat→Nat
|4=>21
|5=>61
|6=>70
|7=>45
|8=>10
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xe062ac6326c2438b4021b2ee68d9ce8d7518bb80670cf576c84b5004b39b446f03f7743dcac3c6782e1ea117d2114fd0a238090c0
|5,0=>0xd7805d4bb9cbdb2c7c6dc7b11c31b8c134abe80abce4abb6bcbac24b2e9daf931a60dc9f28296c7d93e308d667860328291d7cd277c5037892a76d796f6786954366d38665f25e7455e25d5dd9c5b3f65a31e5626f502754e3c04af0e428c140dd33f8273c3413ac5235c5531a572fc272b7952b694257d92385822fc3225111b9ab156b4103e20e9e20d2e70bd3f0a70b06e6b0656005af9
|6,0=>0xb984eb1140aef4ba5fa2a5e1da5898a2c4c9f9449d3129926f8ea818778583fb68151280ace7ec767ace178ee478860756d27546e7409f727587263e6db166cbbd6c9816378d53bf5514b350c644f1794e4d44adfc4a596495714919446627430af3efc83c91f3b54336c2c3599234c3034685328842c62b2a7bf25d7e243002332322c0520e4e1fabc1cf8a18fa11687115e7f15b681552d0e1bc0deca0a7140a3d407a9703ce80384601f220070b
|7,0=>0xf2ecae4333e14bec5e7bb3f50a36749a33597cb0879207d86177767741046fe986f1af69795640dd5cb1453788504004cdf4434a03f1233d4bb3bd40396cd35420318202b8cc29e8d29b351f2951c5671819b1421713d021370d128611285f114830f4a90d49a0abfe0500104e6c013f6
|8,0=>0xe4333dadac9352a4c501488e42c94d1060d0af550698d036ef
|9,0=>0x798d4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0e000000000f000f00000000000f0f0f0e000000000f000f00e0e0e0e000000000e0e0e0e000000000e0e0e0e000000000e0e0e0e0000000000000000f0f0f0f0000000000000000000000000e0e0e0ef0f0f0f000000000f0f0000000000000f0f0f0a000000000f0f0000c0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0cf0f0f0f000000000a0a0a0a000000000f0f0f0a000000000a0a0a0ae0e0e0e000000000e0e0e0e000000000e0e0e0e000000000e000e00f0f0f0f000000000a0a0a0a000000000f0f0f0f000000000a0a0a0af0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f000f00f0f0f0f000000000c0c0c0c000000000f0f0f0c000000000c0c0c0cf0f0f0f000000000f0f0f0f00000000000000000000000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000f0f0f0f000000000f0f0f0f000000000f000f00000000000f000f00f0f0f0f000000000c0c0c0c000000000f0e0f0e000000000c0c0c0ca0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0af0f0f0f000000000f0f0f0f000000000f0f0f0f0000000000000000
|0,1=>0xf0f0f0f000000000f0f0f0f000000000a0f0a0f000000000a0a0a0af0f0f0f000000000f0f0f0f000000000e0e0e0e000000000e0e0e0ef0f0f0f000000000f0f0000000000000f0f0f0f000000000f0f0000f0f0e0e000000000a0a0a0a000000000f0f0e0e000000000a0a0a0af0f0f0f000000000e0e0e0e000000000f0f0f0f000000000e0e0e0ef0f0f0f000000000f0f0f0f000000000f0f0e0e0000000000000000f0f0f0f000000000e0e0e0e000000000f000f00000000000e000e00f0f0f0f000000000a0a0a0a000000000e0e0e0e000000000a0a0a0af0f0f0f000000000f0f0f0f000000000a0a0a0a000000000a0a0a0a1010101000000000101010100000000010101010000000001000100b0b0b0b000000000a0a0a0a000000000b0b0b0b000000000a0a0a0af0f0f0f000000000f0f0000000000000f0f0e0e000000000f0f0000f000f00000000000f000f00000000000f000f00000000000f000f005050505000000000505050500000000050505050000000004040404f0f0f0f000000000f0f0f0f00000000000f000f00000000000a000af0f0f0f0000000000000000000000000f0f0f0f0000000000000000
|0,2=>0x3030303000000000303030300000000030103010000000003000300f0f0e0e000000000f0f0e0e000000000f0f0e0e000000000f0f0e0ef0f0e0e0000000000000000000000000f0f0e0e0000000000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000e0e0e0e0000000000000000f0f0f0f0000000000000000000000000f0a0f0a5050101000000000505000000000000050501010000000005050000f0f0f0f000000000f0f0f0f000000000f0f0f00000000000f0f0f0000000000000000000000000000000000f0f0f0f000000000f0f0f0000000000000000000000000000000000f0f0000000000000f0f000030303030000000003030303000000000303030300000000030003001010101000000000000000000000000010101010000000000000000f0f0f0f000000000f0f0f0f000000000f0a0f0a000000000f0a0f0a0000000000000000000000000000000000f000f00000000000000003030303000000000303030300000000030303030000000003020302f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000a0a0a0a0000f0f0000000000000f0f0000000000000f0f0000000000000a0a
|0,3=>0xf000f00000000000f000e00000000000f000f00000000000f000e0000000000000000000000000000000000f000f00000000000f0000f0f0f0f000000000f0f0f0f00000000000f000f00000000000f0000f0f0000000000000f0f0000000000000f0f000f000000000f0f000000000000000000000000000000000000f0f0f0f000000000e0e0e0ef0f0f0f000000000f0f0f0f0000000000000f0f0000000000000f00f0f0f0f000000000f0f0f0f0000000001010101000000000000000000e000f00000000000e000e00000000000e000f00000000000e000ef0f0f0f000000000f0f0f0f000000000b0b0b0b000000000a0a0a0a0000f0f0000000000000f0f0000000000000f0f0000000000000f00f0f0f0f0000000000000000000000000f0f0f000000000000000000f0f0f0f0000000000000000000000000f0a0f0a0000000000000000f0f0f0f000000000f0f0f0f000000000000000f0000000000000000f0f0f0f000000000f000f00000000000f0e0f0e000000000f000f00f0f0f0f0000000000000000000000000e0e0e0e0000000000000000b0b0b0b000000000b0b0b0b000000000b0b0b0b000000000b0a0b0a
|0,4=>0xf0f0000000000000e0e0000000000000f0f0000000000000e0e000000000000000000000000000000001010101000000000000000050500000000000005050000000000000505000000000000050500000000000000000000f0f00000000000000000000000000000f0f00000000f0f00000000000000000000000000000f0f00000000000000000000f0f000000000f0f00000000000000000f0f000000000f0f0000f0f0f0f000000000f0f0f0f000000000f0f0000000000000f0f00000000000000000000f0f0e0e0000000000000000000000000f0f0e0ef0f0f0f000000000f0f0f0f00000000000f000f000000000000000000000000000000000000000000000000f0f0f0f000000000f0a0f0a00000000000000000000000000000000f0f0f0f000000000f0f0e0e00f000f00000000000e000e00000000000f000f00000000000e000ea0a0a0a000000000a0a0a0a000000000a0f0a0f000000000a0a0a0a0000f0f0000000000000f0f0000000000000f0f0000000000000e0ef0f0f0f000000000f0f0f0f000000000005000500000000000000000000000000000000000000000000000000f000f00000000000a000a
|0,5=>0xf0f0f0f000000000f0f0f0f00000000050505050000000000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0000f0f0f0f000000000f0f0f0f000000000f0e0f0e000000000f0e0f0e10101010000000001010101000000000101010100000000000000000000101000000000000000000000000000001010000000000000000f0f0f0f000000000f0f0f0f000000000f050f05000000000f000f005050505000000000000000000000000050505050000000000000000a0a0f0f000000000a0a0a0a000000000a0a0f0f000000000a0a0a0a5050505000000000505000000000000050505050000000005050000f0f0f0f000000000f0f0e0e000000000f0f0f0f000000000f0f0e0ee0e0f0f000000000e0e0e0e000000000e0e0f0f000000000e0e0e0ef0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0a0f0af0f00000000000000000000000000000f0f00000000000000000000f0f0a0a000000000a0a0a0a000000000f0f0a0a000000000a0a0a0a00000000000000000000000000000000f0f0f0f000000000f0f000000000000000000000000000000000000f0f0f0f0000000000000000
|0,6=>0x505050500000000000000000000505000000000000000000000000000005050000000000000000f0f0f0f0000000000000000000000000f0f0f0f000000000f0f0000f0f0505000000000f0f0000000000000f0f0505000000000f0f00000000f0f0000000000000a0a0000000000000f0f0000000000000a0a0000f0f000000000f0f0f0f00000000000000000000000000000000a0a0f0f0000000000000000000000000a0a0f0f0000000000000000f0f0f00000000000f000f00000000000f0f0f00000000000f000f00f0f0f0f000000000f0f0a0a000000000f0f0f0f000000000f0f0a0af0f0f0f0000000005050000000000000f0f0f0f0000000005050000f0f0a0a000000000f0f0a0a000000000f0f0a0a000000000f0f0a0a5050505000000000505050500000000050505050000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x63868120101814440284066c717201018b144029d062c505081c1010a0c72140402031c7c8043c640903a4c71c0a1099b026820e325c8042638c00080cb96201018e2a00a131c040040638910080c711201078e10142031c3440c062c080080c58a001018910142070c042840608080
|1=>0xa103831c202840604b100a101815e402840638a900a1098e10b428406b070120103831620b84560c581001098e54402a93a0c58100a020316048044e0c0a6201120716202840638b904a3018b0240284481c7100a1018b024480406384230a0c58140008040638400201078e0240284
|2=>0x2f4804063908820f1383160480426ec717201018b02e88042638b907210701704028426384310a7418b02d42841c640900a1098e6e402a7062c0b6201038b02d4284480c58800112031c008040e2c0b40a1018b02419842638c100a1190e0240284263808062101b002402931c85010
|3=>0x2f8805084c70120b428426380909c14207062cb81207498e9a402ca262c0853b2498b02008040638400901098e101420316200c7080c72120123031604845084c70120107178840284063a1900a4c7018440284062c090821098e2e012842638e100a1018e80402841c05f900a1018b
|4=>0x1604804480c58100402031604847089c38316048042754701201422b062c0900a4c5a10280805095018b024028426390882014207062c4010aa4e831604805089018e201420706380900a7498ba416884262c080201099b1c06805084c7019e4028406380904a154840e2c0900a1018b
|5=>0x80c5a1100481d944c5810a1098e100028426390900a12d031604805521018b0200804062c080b21098b105c01da21098b02002131c048310af020316048053a1018b02002131c5c010262c4014040284267870100402131d60805084c7572016b0426380900a1038302988053b46493
|6=>0x200848084c7012016f04062c080201098e9a41285084c70800402e13a4c5880a1018b0243004262c4170040203160485f080c0a62014e84062c080217a884262c090080c71720109bb1c04805097418e0240284062c080964c58140402842638090b8142131c0485b0a1098e0241c85
|7=>0x201320b0240284062c08020753931604805084c58121802e33a1098b0240284262ec0120142131606b900aa42031604805084c581217c29d084c58100402de084c58120142131c5c805084c581012c284266cf0120142131d88805084c717209429d084c75720142131c040250a1018e
|8=>0x40284062c09096142031c04805c27498b0240284262c0e720142131684080201420316048230a1018b0242c853b4421316048053a1018b0240284262e9100a1098b1004005084c58121982131c040100b7821316040100a1098b0243285084c5a1024029d084c581b214213165c080
|9=>0xa1098b0242805084c581212c28426380900a1098b0242985089c98b0240284480c5812014e84262c0900a7498b034c284262c401a017084262c4100a1098b0243585984c5819614213160486a0a1038316048053a1098b10042844e0c58121a42131604805d01098b0240284262c401
|10=>0x84c5812014e84262c0900a1098b2e04805093098b02402e1084c58120142131620090
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x6450bea16942aa8505096a119420a83c506ea0c9416a8285046a07940ca814501ea029402a8005
|5,0=>0x1d05394c7118dfa9b96366c6b58d3b1a16336c6558c7b1896306c5f58bbb17162d6c5958afb15962a6c5358a3b1416276c4d5897b1296246c47588bb1116216c41587fb0f961e6c3b5873b0e161b6c355867b0c96186c2f585bb0b16156c29584fb0996126c235843b08160f6c1d5837b0696
|6,0=>0x6ecedbddb43b6176b6cd559a73b486684ccedd9a3b2f5650ec85d8db315661cec1dd803af975e6cbb5973b2e075b2eb4d966b2c6757eeae1d5932ac654aea79d4c32926516ea11d3eba7674e0c9a5d313a5b74a8e935d233a3f7470e8c9915ba26543ee861d08ba0a7406e7f1cfab9ee73cee7858ee29d57
|6,1=>0x1cf3b986722ee29dc1bb7d6
|7,0=>0x4d6799ef325a613cbb7968f2b9a53bca07932f24da463c8578fb11d9e38346978c4f16a229bc4c788910f5e1bb4307854d08de0dc414781af019dffbbf967e6cfb1df2bbdd87acef3dde43bc177730ec9dd633a57
|8,0=>0x28dbd147a1af419e7fbcf879e2f3ada723cdd7
|9,0=>0x5226
|_,_=>0
def wAt:=mkWire dB 108 220 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 15
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 8 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x86e1c4126151c4216050641080d26155c4008391605021506412615084108071605992d0843084208150841261520157c153a0f08413c40360c1c4116051c4220051605201548403c4016052e4116055c401c01201516050641200526150841080d20050641261526151c4216050622261520153c43261526152e4106420622
|1=>0x1c151605088d064220150841261502152015160508861015201596051605084216053a0708415c41083916050e2f064126153a170841201526154615064226150641081726151d2d16050842484306052e41062120052615160520050641200526150841080d1605060526151605064126150841a60508400a413a1708411605
|2=>0x2015160502410805084102020a41261502412015021526150b6520070e2f064126152015084126153a153a17084126150215160536171c4116050639261520152615084208862e4102150a951c420a21200526153b4f08400841160520052015020120151605076520072615201526150a4120070215201520053a1708413c40
|3=>0x84020152005a616084020151605080120159a4208072e4102150841200720150215274d08400a41261508410817000720150841960508423a070841080d26150b652007084120150801201502151605201508421c41160516059a4108071c42160516053a0708411c4216052615201516055c4308390a4126151c4216050241
|4=>0x84102150843080520052017084216050840081706052615092d08420840084102412017080520052e42021508430842c24208050641261508412005081726154e4108170965200720152005261508422615160508050841082220050005201506422615200726153a17084108412615a605
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x880220000000000000000000000000000000080000000000000000000000
|5,0=>0x50400000000000000000000000000000000094c0000000000000000000120800042620100000003e21d20e080000000000d1000032218100000000001710a1844c00000007900000000c3049800000008100000000c40000288000082000
|6,0=>0x62930c9824be35d9ae0d6a6b23579ab0d526a63519a8493c69b30000001324963499a40d1a68a3448a18d0668123f19f08f267633a11cc4e066d335199ccca4632301974cb465822b8950ca444f3269128c8e644320990047c43b31c180006a60001918bcc5862a2
|6,1=>0x1a84d13679330d944c73
|7,0=>0x12d29594a4a4e5252919484a3e51d28d9464a2e5152899444a1e50d2859424a0e50528194049fe4fd27d93e49ee4f527993c49de4ed27593a49ce4e617213889c04de26e13689b04d62
|8,0=>0x27033719b0cd46683331990cc466032f1
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 13
def pmP:Nat→Nat
|0=>0xcbe0019700032b800577000a000013040022f80045c0008a20010800020400040000040c000810000980001200001620002c000050800081000100000178000220000400000600000800000800000800000a00001000001000000
|1=>0x100802104000200280400400700100219fc042bf80745500e82001995c0330a005655008c280114dc0222b804401006caa00d17001a2b8034100060aa00991c01302002012002caa0051dc00a2b8014100028000048d400404000800
|2=>0x30288a605000c08129804533000b060000082a219034572060ae40915c80a2b9014532020ae4011cc8022b9004532008004001848002b9000122000102151d442a308844551080022053c440a3888145f1028aa2011fc4023b880453
|3=>0x4000107028a6e011d54001020042030a84a615000c22001820483028ea60515cc0a29981451
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x41000000000000000004000000000000
|5,0=>0x9800000000000000000209000000000080040200003100c00000280008b0000004121c0002c000072a0000200002804000200
|6,0=>0xa5b2b30a41d96a5aca6c9225357a3ba7aeee9700002b380b950cd2893a3305339e0a855cd12367919339e1b020d48ed0e474060f82957e005001f92023
|7,0=>0x1cc3717d74b852c6af4a8556f8e153acd62a6bd8f0b8a9132e06d4da6b95658a8b157525cd20fdf
|8,0=>0x311dc3456c3c4670d0
|9,0=>0x17
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 7 (j%128);fld (pmP (k/32)) 23 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_217 8 roots_217 ops++addP pm 1 dom_202 5 roots_202 ops++addP pm 2 dom_74 4 roots_74 ops++addP pm 3 dom_216 5 roots_216 ops++addP pm 4 dom_218 7 roots_218 ops++addP pm 5 dom_83 5 roots_83 ops++addP pm 6 dom_211 8 roots_211 ops++addP pm 7 dom_147 5 roots_147 ops++addP pm 8 dom_210 5 roots_210 ops++addP pm 9 dom_90 5 roots_90 ops++addP pm 10 dom_91 7 roots_91 ops++addP pm 11 dom_89 5 roots_89 ops++addP pm 12 dom_155 6 roots_155 ops++addP pm 13 dom_154 4 roots_154 ops++addP pm 14 dom_27 4 roots_27 ops++addP pm 15 dom_209 7 roots_209 ops++addP pm 16 dom_208 4 roots_208 ops++addP pm 17 dom_81 4 roots_81 ops++addP pm 18 dom_153 5 roots_153 ops++addP pm 19 dom_75 5 roots_75 ops++addP pm 20 dom_203 6 roots_203 ops++addP pm 21 dom_195 5 roots_195 ops++addP pm 22 dom_201 5 roots_201 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_219 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_216 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_209 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_153 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_195 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_201 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_217 8 s (0,roots_217.map (·&&&dom_217)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_219 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_217 h
def symsG:List (List (Nat×Nat)):=[[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_219==dom_219)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_219 gM v ys):RunD true dom_219 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_219 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 21 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 21 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 61 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 61 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 70 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 70 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 45 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 45 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 10 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_219 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_213_8:=0x33003300000000003300330000000000330033000000000033003300
def gzo_213_8:=0x33003300000000003300320000000000330033000000000032002200
def gsh_213_8:=0x330033000000000033003200000000003300330000000000320022
theorem lowS_zo_213_8_148:Lower true dzo_213_8 roots_213 gzo_213_8 6:=lower_iso_b (d1:=dom_213) (r1:=roots_213) (T1:=gsh_213_8) [(dom_213,8)] (by decide +kernel) (lower_slice_b (T:=gsh_213_8) [(0x220022000000000022002200000000002200220000000000220022,0,1),(0x330033000000000000000000000000003300330000000000000000,0,64)] (by decide +kernel) lowS_148)
def dzo_149_8:=0x3300330000000000000000000000000033003300
def gzo_149_8:=0x3300320000000000000000000000000032002200
def gsh_149_8:=0x33003200000000000000000000000000320022
theorem lowS_zo_149_8_148:Lower true dzo_149_8 roots_149 gzo_149_8 5:=lower_iso_b (d1:=dom_149) (r1:=roots_149) (T1:=gsh_149_8) [(dom_149,8)] (by decide +kernel) (lower_slice_b (T:=gsh_149_8) [(0x22002200000000000000000000000000220022,0,1)] (by decide +kernel) lowS_148)
namespace S_221
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(1,129),(4,20),(4,68),(4,132),(5,13),(5,21),(5,69),(5,133),(8,9),(8,72),(12,13),(12,28),(12,76),(12,140),(16,17),(16,20),(16,80),(16,144),(24,25),(24,28),(24,88),(24,152),(64,65),(64,68),(64,72),(64,80),(64,192),(128,129),(128,132),(128,144),(128,192),(136,137),(136,140),(136,152),(136,200)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffff
def xsM:=roots_221.map (·&&&dom_221)
def gM:=goal_221&&&dom_221
def NN:Nat→Nat
|5=>2
|6=>8
|7=>9
|8=>3
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0xb4c337f405
|6,0=>0x8851580bab6a6ba4cff2303a92015c1d5f30ddb6
|7,0=>0xeb830a7dc86a58e62801525b44421035c2218f6a0877c
|8,0=>0xcd7236683340187
|9,0=>0x7369e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcccc000000000000cccc000000000000cccc00000000000000000000000000000000000000000000000333333000000000033333300cccccc0000000000cccccc0000000000cccccc0000000000cccccc033333333000000003333333300000000333333330000000033330000cccccccc00000000cccccccc00000000cccc000000000000cccc00033003300000000003300330000000000330033000000000033003300cccccccc00000000cccccccc000000000000000000000000000000033333333000000003333333300000000333333000000000033333300cccccccc00000000cccc000000000000cccccccc00000000cccc00030303030000000003030303000000000303030300000000030303030cccc000000000000cccc000000000000cccc000000000000cccc00033333333000000003333333300000000330033000000000033003300888888880000000088888888000000008888888800000000888888883030303000000000303030300000000030303030000000003030000cccccccc00000000cccccccc00000000cccccccc00000000000000033333333000000000000000000000000333333330000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0xa63097546309856309546310c75a630975a63195a630f9e56309b5a6310c5a63095a3209856310e763097ba631dc76309d76319c5a32095a3210987631543210
|1=>0x5a630975a6309d56309b5
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x65006
|6,0=>0x3863262c62661f71961270b7
|7,0=>0x7476e66866085975274c64573e7
|8,0=>0x8878267b7
|9,0=>0x8f6
|_,_=>0
def wAt:=mkWire dB 16 222 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x15a5565a9415d96959a425794150941515c25d9e959542579415c6de5056e9954259d969055650941597569056415a41579415c6c55ba56509415
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x1000
|6,0=>0x5cd4344ce32cc8318842
|7,0=>0x2a2a0a6290a22809e2709a2
|8,0=>0x2e1b46c1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 10
def pmP:Nat→Nat
|0=>0x19f3cb863cedf71f3879b9dd1e66fb37991fc5ee2770f985401e60e1008003c004000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x40
|6,0=>0x2290733861
|7,0=>0xc5c6727a614
|8,0=>0x3527
|9,0=>5
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 13 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_220 8 roots_220 ops++addP pm 1 dom_157 7 roots_157 ops++addP pm 2 dom_197 5 roots_197 ops++addP pm 3 dom_85 5 roots_85 ops++addP pm 4 dom_217 8 roots_217 ops++addP pm 5 dom_205 7 roots_205 ops++addP pm 6 dom_93 7 roots_93 ops++addP pm 7 dom_213 8 roots_213 ops++addP pm 8 dom_77 5 roots_77 ops++addP pm 9 dzo_213_8 6 roots_213 ops++addP pm 10 dzo_149_8 5 roots_149 ops++addP pm 11 dom_141 4 roots_141 ops++addP pm 12 dom_29 4 roots_29 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_221 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_197 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_213_8_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_149_8_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_141 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_29 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_220 8 s (0,roots_220.map (·&&&dom_220)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_221 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_220 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff0000ffff0000ffff0000,112)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_221==dom_221)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_221 gM v ys):RunD true dom_221 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_221 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 2 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 8 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 9 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 3 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_221 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
namespace S_222
def pG:List (Nat×Nat):=[(2,10),(2,66),(2,130),(4,20),(4,68),(4,132),(6,14),(6,22),(6,70),(6,134),(8,10),(8,72),(12,14),(12,28),(12,76),(12,140),(16,20),(16,80),(16,144),(18,22),(18,26),(18,82),(18,146),(24,26),(24,28),(24,88),(24,152),(64,66),(64,68),(64,72),(64,80),(64,192),(128,130),(128,132),(128,144),(128,192),(136,138),(136,140),(136,152),(136,200)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_222.map (·&&&dom_222)
def gM:=goal_222&&&dom_222
def NN:Nat→Nat
|6=>1
|7=>5
|8=>2
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x6eb8c
|7,0=>0x98a795290d515fb4bec715d81
|8,0=>0x68c4462fd6
|9,0=>0xbad5e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x14141414000000001414000000000000141414140000000014140002aaaaaaa800000002aaaa828000000002aaaaaaa800000002aaaa82855555555000000000000000000000000555555550000000000000000a0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0a155540000000000015554000000000001555400000000000155540002aaaa828000000002aaaa828000000002aaaa828000000002aaaa82855555555000000005555000000000000555555550000000055550000aa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa0155555554000000014141414000000001555555540000000141414142222222200000000222222220000000022222222000000002222222255555555000000005555555500000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x6371805637180632718046327106371a809463718096371805437180543210
|_=>0
def sO:Nat→Nat→Nat
|6,0=>6
|7,0=>0x23771d4835c67
|8,0=>0xc5ea7
|9,0=>0x386
|_,_=>0
def wAt:=mkWire dB 11 223 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x19d785a1785d2685d168561675a1765e1685d9
|_=>0
def oO:Nat→Nat→Nat
|6,0=>3
|7,0=>0xb292725232
|8,0=>0xe1d1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0x1ffec5fe7eff5f9fc7e00
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>1
|7,0=>0x42786
|8,0=>0x53
|9,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 9 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_220 8 roots_220 ops++addP pm 1 dom_94 8 roots_94 ops++addP pm 2 dom_214 8 roots_214 ops++addP pm 3 dom_218 7 roots_218 ops++addP pm 4 dom_206 7 roots_206 ops++addP pm 5 dom_158 7 roots_158 ops++addP pm 6 dom_142 4 roots_142 ops++addP pm 7 dom_154 4 roots_154 ops++addP pm 8 dom_202 5 roots_202 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_222 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_142 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_202 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_220 8 s (0,roots_220.map (·&&&dom_220)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_222 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_220 h
def symsG:List (List (Nat×Nat)):=[[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_222==dom_222)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_222 gM v ys):RunD true dom_222 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_222 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 5 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 2 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_222 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_222 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_222 roots_222 goal_222 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_222
theorem lowS_222:Lower true dom_222 roots_222 goal_222 10:=S_222.noCircuit
theorem lowS_235:Lower true dom_235 roots_235 goal_235 8:=lower_slice_b [(0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f00,1,9)] (by decide +kernel) lowS_227
namespace S_237
def pG:List (Nat×Nat):=[(1,9),(1,65),(1,129),(4,36),(4,68),(4,132),(5,13),(5,37),(5,69),(5,133),(8,9),(8,40),(8,72),(12,13),(12,44),(12,76),(12,140),(32,36),(32,40),(32,160),(33,37),(33,41),(33,97),(33,161),(64,65),(64,68),(64,72),(64,192),(96,97),(96,100),(96,104),(96,224),(128,129),(128,132),(128,160),(128,192),(136,137),(136,140),(136,168),(136,200)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_237.map (·&&&dom_237)
def gM:=goal_237&&&dom_237
def NN:Nat→Nat
|5=>3
|6=>5
|7=>4
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0xa551d58cd018159
|6,0=>0xcf1f9c216bafff478b0322c30
|7,0=>0xd9f3dbad388193d76cf5
|8,0=>0xf0cad
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xc8c80000c8c80000c8c80000c8c80000c8c80000c8c80000c8c80000c8cb33300003333000030300000303000003333000033330000303000003030cccc0000cccc0000cccc0000c0c00000cccc0000cccc0000cccc0000c0c333300003333000033330000333300003333000033330000000000000000cc000000cc000000cc000000cc000000cc000000cc000000cc000000cc0030300000303000003030000030300000303000003030000030300000000cccc0000cccc0000cccc0000cccc0000000000000000000000000000000333300000000000033330000000000003333000000000000333300000000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000000333300003333000033330000000000003333000033330000333300000000cccc0000cccc0000cccc0000cccc0000cc000000cc000000cc000000cc030300000303000003030000030300000303000003030000030300000303088880000888800008888000088880000888800008888000088880000888b33300003333000000000000000000003333000033330000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x69210769c21076921a0769d210749210749c217b4921074921a743210754921074321a491807543210
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x31433006
|6,0=>0x2b648e798c3117
|7,0=>0x8aef9dbbb16
|8,0=>0x4c6
|_,_=>0
def wAt:=mkWire dB 14 238 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x81074856048160581605c19758160581
|_=>0
def oO:Nat→Nat→Nat
|5,0=>1
|6,0=>0x7261422211
|7,0=>0xc1b1a191
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0xfebf97eabf504c06003000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>1
|6,0=>0x55a3
|7,0=>0x927
|8,0=>4
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 11 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_229 7 roots_229 ops++addP pm 1 dom_77 5 roots_77 ops++addP pm 2 dom_105 5 roots_105 ops++addP pm 3 dom_201 5 roots_201 ops++addP pm 4 dom_233 6 roots_233 ops++addP pm 5 dom_109 6 roots_109 ops++addP pm 6 dom_173 6 roots_173 ops++addP pm 7 dom_172 5 roots_172 ops++addP pm 8 dom_236 6 roots_236 ops++addP pm 9 dom_205 7 roots_205 ops++addP pm 10 dom_141 4 roots_141 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_237 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_229 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_201 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_172 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_141 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_229 7 s (0,roots_229.map (·&&&dom_229)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_237 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_229 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_237==dom_237)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_237 gM v ys):RunD true dom_237 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_237 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 5 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 4 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_237 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_237 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_237 roots_237 goal_237 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_237
theorem lowS_237:Lower true dom_237 roots_237 goal_237 9:=S_237.noCircuit
theorem lowS_249:Lower true dom_249 roots_249 goal_249 9:=lower_slice_b [(0x300030003000300030003000300030003000300030003000300030003000300,1,9)] (by decide +kernel) lowS_241
def dzo_234_16:=0x505000005050000050500000505000005050000050500000505000005050000
def gzo_234_16:=0x505000005050000050500000505000005050000050500000504000004000000
def gsh_234_16:=0x50500000505000005050000050500000505000005050000050400000400
theorem lowS_zo_234_16_42:Lower true dzo_234_16 roots_234 gzo_234_16 6:=lower_iso_b (d1:=dom_234) (r1:=roots_234) (T1:=gsh_234_16) [(dom_234,16)] (by decide +kernel) (lower_slice_b (T:=gsh_234_16) [(0x50500000505000000000000000000000505000005050000000000000000,0,64),(0x50500000505000005050000050500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
namespace S_250
def pG:List (Nat×Nat):=[(2,10),(2,34),(2,66),(2,130),(8,10),(8,40),(8,72),(16,80),(16,144),(18,26),(18,50),(18,82),(18,146),(24,26),(24,56),(24,88),(24,152),(32,34),(32,40),(32,160),(48,50),(48,56),(48,112),(48,176),(64,66),(64,72),(64,80),(64,192),(96,98),(96,104),(96,112),(96,224),(128,130),(128,144),(128,160),(128,192),(136,138),(136,152),(136,168),(136,200)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_250.map (·&&&dom_250)
def gM:=goal_250&&&dom_250
def NN:Nat→Nat
|7=>2
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|7,0=>0x7010459a6b
|8,0=>0xef2e1
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xa0a08080a0a08080a0a08080a0a08080a0a08080a0a08080a0a08080a0a08094140000141400001414000014140000141400001414000014140000141400028282828000000002828282800000000282828280000000028282828000000050005000500050005000500050005000500050005000500050005000500050080808080808080808080808080808080808080808080808080808080808080840400000404000004040000040400000404000004040000040400000404000282828282828282800000000000000002828282828282828000000000000000505050505050505050505050505050500000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x2e8c8be322c688
|_=>0
def sO:Nat→Nat→Nat
|7,0=>0xcc06
|8,0=>0xc6
|_,_=>0
def wAt:=mkWire dB 8 251 0x7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 9
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xcdcf
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
addP pm 0 dom_242 7 roots_242 ops++addP pm 1 dom_186 7 roots_186 ops++addP pm 2 dom_122 7 roots_122 ops++addP pm 3 dom_218 7 roots_218 ops++addP pm 4 dom_248 6 roots_248 ops++addP pm 5 dom_234 6 roots_234 ops++addP pm 6 dzo_234_16 6 roots_234 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_250 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_234_16_42 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_242 7 s (0,roots_242.map (·&&&dom_242)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_250 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_242 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_250==dom_250)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_250 gM v ys):RunD true dom_250 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_250 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 2 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_250 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_250 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_250 roots_250 goal_250 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_250
theorem lowS_250:Lower true dom_250 roots_250 goal_250 9:=S_250.noCircuit
def isoMvS_159:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_159:Lower true dom_159 roots_159 goal_159 9:=lower_iso_b isoMvS_159 (by decide +kernel) lowS_119
def isoMvS_187:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_187:Lower true dom_187 roots_187 goal_187 9:=lower_iso_b isoMvS_187 (by decide +kernel) lowS_126
def isoMvS_189:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_189:Lower true dom_189 roots_189 goal_189 10:=lower_iso_b isoMvS_189 (by decide +kernel) lowS_125
def isoMvS_243:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_243:Lower true dom_243 roots_243 goal_243 10:=lower_iso_b isoMvS_243 (by decide +kernel) lowS_222
def isoMvS_245:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_245:Lower true dom_245 roots_245 goal_245 10:=lower_iso_b isoMvS_245 (by decide +kernel) lowS_221
def isoMvS_252:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_252:Lower true dom_252 roots_252 goal_252 9:=lower_iso_b isoMvS_252 (by decide +kernel) lowS_249
def dzo_46_16:=0x5555000055550000
def gzo_46_16:=0x5554000054500000
def gsh_46_16:=0x555400005450
theorem lowS_zo_46_16_42:Lower true dzo_46_16 roots_46 gzo_46_16 5:=lower_iso_b (d1:=dom_46) (r1:=roots_46) (T1:=gsh_46_16) [(dom_46,16)] (by decide +kernel) (lower_slice_b (T:=gsh_46_16) [(0x505000005050,0,4)] (by decide +kernel) lowS_42)
def dzo_95_32:=0xffffffff00000000ffffffff00000000
def gzo_95_32:=0xfffffffe00000000fffefffc00000000
def gsh_95_32:=0xfffffffe00000000fffefffc
theorem lowS_zo_95_32_81:Lower true dzo_95_32 roots_95 gzo_95_32 7:=lower_iso_b (d1:=dom_95) (r1:=roots_95) (T1:=gsh_95_32) [(dom_95,32)] (by decide +kernel) (lower_slice_b (T:=gsh_95_32) [(0xcccccccc00000000cccccccc,0,2),(0xf0f0f0f000000000f0f0f0f0,0,4),(0xff00ff0000000000ff00ff00,0,8)] (by decide +kernel) lowS_81)
def dzo_111_16:=0xffff0000ffff0000ffff0000ffff0000
def gzo_111_16:=0xffff0000ffff0000fffe0000fefa0000
def gsh_111_16:=0xffff0000ffff0000fffe0000fefa
theorem lowS_zo_111_16_42:Lower true dzo_111_16 roots_111 gzo_111_16 7:=lower_iso_b (d1:=dom_111) (r1:=roots_111) (T1:=gsh_111_16) [(dom_111,16)] (by decide +kernel) (lower_slice_b (T:=gsh_111_16) [(0xaaaa0000aaaa0000aaaa0000aaaa,0,1),(0xf0f00000f0f00000f0f00000f0f0,0,4),(0xffff0000ffff0000000000000000,0,64)] (by decide +kernel) lowS_42)
def dzo_110_16:=0x55550000555500005555000055550000
def gzo_110_16:=0x55550000555500005554000054500000
def gsh_110_16:=0x5555000055550000555400005450
theorem lowS_zo_110_16_42:Lower true dzo_110_16 roots_110 gzo_110_16 6:=lower_iso_b (d1:=dom_110) (r1:=roots_110) (T1:=gsh_110_16) [(dom_110,16)] (by decide +kernel) (lower_slice_b (T:=gsh_110_16) [(0x5050000050500000505000005050,0,4),(0x5555000055550000000000000000,0,64)] (by decide +kernel) lowS_42)
namespace S_127
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(2,10),(2,34),(2,66),(3,11),(3,19),(3,35),(3,67),(4,20),(4,36),(4,68),(5,13),(5,21),(5,37),(5,69),(6,14),(6,22),(6,38),(6,70),(7,15),(7,23),(7,39),(7,71),(8,9),(8,10),(8,40),(8,72),(12,13),(12,14),(12,28),(12,44),(12,76),(16,17),(16,20),(16,80),(18,19),(18,22),(18,26),(18,50),(18,82),(24,25),(24,26),(24,28),(24,56),(24,88),(32,34),(32,36),(32,40),(33,35),(33,37),(33,41),(33,49),(33,97),(48,49),(48,50),(48,52),(48,56),(48,112),(64,65),(64,66),(64,68),(64,72),(64,80),(96,97),(96,98),(96,100),(96,104),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffffffffffff
def xsM:=roots_127.map (·&&&dom_127)
def gM:=goal_127&&&dom_127
def NN:Nat→Nat
|5=>4
|6=>16
|7=>67
|8=>139
|9=>108
|10=>15
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0xd370cca0261e241184a7
|6,0=>0xe3f5bc21cec0a0da7f40a7ae392e958c09e797c45e4265b726541e94da1044c763e7671e06d0dce6
|7,0=>0xfef89f4829f0652ef386e8ef9e6f86e6ed8e2ef0da366d944ed1b8ecebd7cb641c83fec5138c4460c3f00c345fc26f1c0accc0224bf732be9e5bd170b957fb5506aed2dab57aa9020a586da24c8a1d279f95c9124290a818ef3d8c3be89dd789969886d486eda803eb7dc0a734d56c89d6b85b6ae5056737556c3529f84babb3f0b43df7f3cbbc31b0825dbf25bd12466e234eb234da1f09a1bb66106a40ef9d08af502de8002e1
|8,0=>0xea096e95bce728be4afde1f2add798dc717da760d92d4d8697d7144d641ed2f42d1fa1cf4bccdbbacd37ecbee2ca1e8c8a52c7518c5e73c15afba57bb9634b8789af947aac99aaae0a8b29a640fa49ff9f6d79dec89c1ce9b74799a88990d89806597fa9973a89627695baa935c8933129261090bff8ed298ed188d8bb8d60d8aa9d8a788899ca89755871da857dd847f782dba81fb0810448001a7f7c77e3667bd117727c74d5971de97195c6f2176daa06c17b6b8ad69d746410f63c4e61824612ce608645efc85df41576cf575e456ae155b46528c0511834fbe84f40d47feb446954177c3f2d03ec2d3aa933a1f939d8b395ed35f7b30f192ece92ec2d2e02c2dec929f96259ad23ece22c1a20c892064e1fad61c7151c4411a88b194981907e18c3416c9e16734154b314fea12a5e0c1cd0805506dac04b790435703044
|8,1=>0xff2e2fd8e0fbeddf7aaaf4c1bf3fe7f2f1af1a9aefbbfede9febbda
|9,0=>0xfeee3fcb54fa280f673bf3812f1f0bf0020edacbecff9eaa72e9e82e7c7ee20b7de2afdddd2dbdb5db21dda8e5d6882d3773d0ee9d07fbd03f2cb788c75a8c4d3dc325ac02d4beff6bddb7bdd15ba0a2b273db1d11b0480afed3afc7dae5e9acea9aab24aa29ca8ed5a125ca124e9fc329ba12916238fadf8dc818c1808b85889ecd8487880b067cf2279a8471a0e707586ff586fc266a3f769a5660eb95fd695f3995e9105e22c5adef5839a5766a559704e22446f5d46698426593eb213d5ff3d36c3c23e3b2ce3a62339b77375fc34b533254f30187292d429294291b82521024f8b1cf531b4fc1ad001a4a01914a1685b16225155f20d80a09fe009697091bb07b37068b805357041430398a
|10,0=>0xf69ede4ea8ce280bbe949e7bb928f28f8cb8d3bf83c7d761fa581865254f4a8623b65b26763
|11,0=>0x2654f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffff00ffffff00ffffff00ffffff00ffffffff00000000ffffffff00000000ffffffffffffffff0000000000000000ffffff00ffffff00ff00ff0000000000aaaaaaaaaaaaaaaaaaaaaa00aaaaaa00ffffffaaffffffaaffaaffaaaaaaaaaaffffffccffffffccffccffccccccccccffff0000ffff0000ffff0000ffff0000fffffff0fffffff0fff0fff0f0f0f0f0ffffffffffffffffff00ff00ff00ff00ffffffffffffffffffffffff00000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ccccccccccccccccccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000ffff0000ffff00ffff0000ffff0000ff00ff00ff00ff00ff00ff00000000
|0,1=>0xffffffffffffffffffffffffff00ff00ffff0000ffff0000ffff00ff000000000000000000000000ffffaaaaffffaaaa000000ff000000ff00ff00ff00000000ffffffffffffffffff00ffff00000000ff00ff00ff00ff00ff00ff00ff00ff005555555555555555555555005555550033333333333333333333333333003300ffffffffffffffffffffff0000000000000000000000000000ff000000ff0000ffffffffffffffffffffff00ffffff00ffff0000ffff0000ff000000ff0000000000ffff0000ffff0000ff000000ff00ffffff00ffffff00ffffffffff00ff00000000ff000000ff00000000ff00ff00ffffff00ffffff00ffffff0000000000
|0,2=>0xffffffffffffffffffffffffffffff00ffffffffff00ff00ffffffffff00ff00ffffffffffffffffffff0000ffff000033333333333333333333333333333300ffff0000ffff0000ffff0000000000000000ffff0000ffff0000ff00ff00ff00ffaaffaaffaaffaaffaaffaa00000000ffff0000ffff0000ffff0000ff000000ffffff00ffffff00ffffff00ff00ff00ffffaaaaffffaaaaffffaaaaffffaaaa00550055005500550055005500000000ffaaffaaffaaffaaffaaffaaffaaffaaff55ff55ff55ff55ff55ff55ff00ff00ffff0000ffffffffffff0000ffffff0000000000ffffffff00000000ff00ff000000000000000000ffff0000ffffff00
|0,3=>0xffff0000ffff0000ff000000ff00ff000000ffff0000ffff0000ffff0000ff0055555555555555555555555555555500ffffffffffffffffffffff00ff00ff00ffff000000000000ffff000000ff0000ffffffffffffffffffff000000ff000055555555555555555555555555005500ffffffff0000ffffffffffff0000ff0000ff00ff000000ff00ff00ff00000000ffffffffffffffffffaaffaaffaaffaa55555555555555555555555500000000555500005555000055550000555500000000ffff0000ffff00ffffff000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f005555555555555555550055005500550000000000ffffffff00ff0000ffffff00
|0,4=>0xffffffff00000000ffffffff00ff0000ffffffffffff0000ffffffffffff0000000000000000000000ff00ff00ff0000ffffffff0000ffffff00ff000000ff00000000ff000000ff000000ff00000000ffffffffffffffffffffffffffff00000000ffff0000ffff0000ffffffff0000ffffffffffffffffff00ffffff00ff00ffff0000ffff00000000000000ff00000000000000000000ffffffffff00ff00ffffccccffffccccccccccccccffccccffffffffffffffff00ff000000ff0000ffffffffffffffffffffffff00ff0000ffffffffffff0000ffffffffff0000000000ffff0000ffff00ffffff0000ff000000ffff0000ffff0000ffff00000000
|0,5=>0xff00ff00ffffffffff00ff00ffffff000000000000000000ffffff00ffffff00000000000000000000000000ffffff0000000000000000000000ffff0000ff0000ff000000ff000000ff0000000000000000000000ff00ff0000000000ff000000ff000000ff000000ff000000ff0000ff00ffffff00ffffff00ffff0000000000000000ffff000000000000ffff0000ffffffffffffffffff00ff00ffffff00ffff0000ffff0000ffffffffffffff000f0f0f0f0f0f0f0f0f0f0f0f0f0f0000ffffffffffffffffaaaaaaaaaaaaaaaaff00ffffff00ffffff00ffffff00ff0000550000005500000055000000550000aaffaaaaaaffaaaaaaffaaaaaaffaaaa
|0,6=>0xff00000000000000ff0000ccccccccccffccccccccccccccffccccffff0000ff000000ffff0000ff000000ffffffffffffffffffff0000ff0000000000ffff0000ff000000ffff0000ff00ffffffffffffffff0000ffff0000ff00ff00ff00ffffff00ff00ff00ffffff00ffffffffff00ff00ffff0000ff000000ffffffffff00ff000000ffff0000ff000000000000000000ffff0000ffff0000ffffffffff00ff00ffffffffffffff00ffffffaaffffffaaffffffaaffffffaa55555500555555005555550055555500ffffffffffffffff00000000ffff0000ffaa0000ffaa0000ffaa0000ffaa000000000000ffffffff00000000ffff0000
|0,7=>0x55555555555555555555000055550000ff55ff00ff55ff00ff55ff00ff55ff000000000000000000ffaaffaaffaaffaa0000ffaa0000ffaa0000ffaa0000ffaa0000000000000000ffffffff000000000000000000000000ffffffffffff0000000000000000000000000000ffff000000000000ffffff0000000000ffffff00ffffffffffffffff00000000ffffff00ffffffffffffffff0000000000ff000000000000ffffffff00000000ffffff0000ff00ff00ff00ff00ff000000ff0000ffffffff00ff00ffffffffff00ff0000ffffffffffff0000ff00ff00ff000000ff00ff00ff00ff00ffffff00ffffff0000000000ff00ff0000000000ffffff00
|0,8=>0xffffffffffffffffffffaaaaffffaaaaffffffffffffff00ffffffffffffff0000ff00ff00ff000000ff00ff00ff000000000000000000005555000055550000ffffffff00000000ffffffffffff0000ffffffffffffffffffffffffaaaaaaaaffffffff00ff0000ffffffff00ff0000ffffffffffffffff5555000055550000aaaaaaaaaaaaaaaaffffaaaaffffaaaa00ff00aa00ff00aa00ff00aa00ff00aa
|_,_=>0
def sP:Nat→Nat
|0=>0x5080604031900051d081a0402180508060403021c05080604030211051a04030201081b0604030200050e1a040302010e081a0419180d170806040302000504030200161305151404030200120508060403020e0806040302110508060c04030205080604030b0005080a060403050809060402050807060302050403020100
|1=>0x20d0e081a040218160d0508061a0403190508240604030225051708061a0403020e2708060403020d0526081a0402180d050e08061a040319050806140403020005260806040302001f051d081a040302050824230403020d0e2008061a0403020e15081a0402180d0e0f08060402180d051e08061a0403020e0f140402180d
|2=>0xd05081a040234180d05083606040302000508060403022505080604030234000508061a04030b0508061a040302330e081a0302320d0e100806040302050824060403310515080604030200051d081a040302000e081a040302300d05081b061a0403020e081a04022c0d0508061a0403022a050829060403021f0e0f140403
|3=>0x3020508061a3f0403020e1a040302163e0d0e081a140402180d0e081a04033d0d053c08061a0403021f0e081a0403190d050e1a0403021613050e151a140403020e15281a0403020d050e0f06140403020e0f28060403020d0e083a061a040302050806040302001605081a040339340d0e0806040302370d0e081a04021813
|4=>0x4030200130508061a0403343105080604030231000e081a040319210d051008060403020e1a040302010d0508060403024b080604030235001a040302490d05270806040302051a0403021613050848061a04030205151a140403020e081a0445020d430e08061a040302420e0f060403020d0e081a040302410d050f061404
|5=>0x3020d550e081a0403020d05081a040302390d0e27081a0403020d0e081a0302540d0e0f06140403020d0e08361a0403310d0e08521a0403020d0e081a040334310d0e08241a0403500d4f0e08061a0403020d050836061a0403020e08061a0403024d0d0508061a04030234050e08061a040302160e0f064c0403020d050806
|6=>0xe081a0403025c0d0e2208061a0403020d0e081a0403025b0d0e081a0403023e0d0e10081a0403020d0508231a040302350d0e081a0403024b0d0e081a0402180d0e081a0403025a0d0e1a04030216130d0e083b1a0403020d0e08581a0403020d0e0856061a0403020d0508061a040302160e151a140403020d1f0e081a1404
|7=>0x8061a0402180d05081a04030262050e08061a040302130e083b061a0403020d380e081a0403020d430e081a0403020d0e08281a0403020d0508061a040302400e08061a040334310d0e0f610403020d0e262d1a0403530e085f1a0403020d1f081a040302350d05081a040302250d05081a04030234000d0e081a0403025d0d
|8=>0x30240570d0e086c1a0403020d0e081a0403026a0d0508061a04030213420e081a0403020d2f0e081a0403020d0e0869060403020d0508061a040302310e08681a0403020d1f0e15081a0403020d0e081a040302670d650e081a0403020d0e08061a0403023e0d0e081a0403190d1f0e0f08060403020d0e08241a0403630d0e
|9=>0x8231a0403020d05082b061a040302081a04030235000d0508581a0403020d05080604030200050824060403020e081a040302700d050e08061a14040302380e08061a0403020d0527081a0403020d0e0828061a0403020d05081a0302540d1f0526081a0403020d0508521a0403020d0e081a046e020d4a2b1a0403020d1a04
|10=>0x1a040353310e081a720403020d052608061a0403021f0e081a040302160d05081a0403025b0d05081a0403023e0d0510081a0403020d050e0f08060403024a0e1a040302590d0e15081a040302210d05081a0403024b0d05081a0403026b0d0e08061a0403190d05081a0402180d0e5e08061a0403020e0f0806040302210d05
|11=>0xe08061a040302440e081a04030216210d0e0824060403310d0e081a040302750d051d081a0403020e08241a0403310d0e0824060403530508281a0403020d050f0806040302730e081a0403020d0e081a04030b0d0e081a4c0403020d4e2b1a0403020d0508061a04030235420e08061a0403020d0508061a140403020e0806
|12=>0x1a0403020e0f140403020d0508241a040302250d0e0806040302000d0e08061a04030b0d0e08061a4c0403020d05086d1a0403020d0e2d08241a0403530e0f1a040302600d4f0e081a0403020d0e081a0403024d0d0e081a040302760d0526081a040302000d050e1508061a0403020e08061a720403020d0e2608061a040353
|13=>0x1a0403020d0508061a0403020e0f08060403020d0e22081a0403020d0e081a040302470d0508291a0403020d0e08061a040302750d0e0f06040302570d0e0f1a040302620d7a05081a0403021a04030240790d0e081a040302770d0e08561a0403020d1f0e081a040302130d1f05081a040302340d4605081a04030205150806
|14=>0x403020d0e087e1a0403020d0e08611a0403020d0e081a040302790d7b0f081a0403020d0e5e081a0403020d0e087d1a0403020d0e081a0403027c0d05082b1a0403020d0e1d081a0403020d0e0f081a040302780d0e64081a0403020d0e15081a0403020d7b081a040302590d05081a040302570d0e081a040302510d0e0f26
|15=>0xd0e81081a0403020d0e081a040302160d460e081a0403020d0e081a040302780d0e081a040302800d0e1508061a0403020d0e0866241a0403020d05081a040302000d0508241a0403020d050e081a040302590d0e081a0403027f0d05081a040302350d0e081a040302630d0e081a0403026b0d0e08361a0403020d0526081a
|16=>0x6d1a0403020d0e0f1a040302340d0e081a040302400d0e08241a0403530d0e262d1a0403020d050f081a0403020d0e081a040302820d0e08691a0403020d4a0e081a0403020d0e0836061a0403020d0e08061a040302340d0e26081a0403530d0e081a040302440d05081a040302590d7a0e081a0403020d050e0f081a040302
|17=>0x1a0403020d0e081a040302860d850e081a0403020d0e0f2d1a0403020d0e081a040302130d05081a040302340d0e081a040302600d0e081a040302310d8405081a0403020d0e2d1a040302590d05081a040302790d1f0e081a0403020d830e081a0403020d0e0f08240403020d0e71081a0403020d0e08061a040302160d0e08
|18=>0x1a140403020d4e0e08061a0403020d0e08061a040302310d0e081a040302870d050e081a040302400d1f0e08061a0403020d0e6408241a0403020d0e081a040302210d0e08061a040353022e0e2d081a0403020d0e08241a040302510d0e082b1a0403020d0e081a040302620d0e2d081a040353020e081a040302740d0e2666
|19=>0x570d0e08061a040302210d0e89081a0403020d0e081a040350020d0e0f661a0403020d0e0824060403020d880e081a0403020d4e0e0f1a0403020d05081a040302400d0e0836241a0403020d0e081a040302000d0e08061a040302570d0e2d1a040302340d4a05081a0403020d4e0e1a040302590d0e08061a040302130d0e08
|20=>0x81a0403020d7b081a0403020d0e081a040353020d0e081a040302340d0e081a0403026f0d050e082b1a0403020d0e2d08241a0403020d4e05081a0403020d0e261a040302590d0e08061a140403020d2e0e08661a0403020d0e2608061a0403020d2e05081a0403020d050e08061a0403021f05081a0403020d0e0f1a040302
|21=>0xe081a0403020d0e0f081a0403020d0e081a040302590d0e08241a0403020d0e26081a0403020d0e081a040302570d0e08661a0403020d05081a0403020d4e0e081a0403020d2e0e081a0403020d050e081a0403020d0e08061a0403020d0e2d
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x12600c600660006
|6,0=>0x8070797072706b7064705e6057705070497042703b7034702d7026701f70187
|7,0=>0x26b8263825c7255724e72477241623a7233722b8224721d7215820d820581fe71f681ee81e681df71d781cf81c781bf81b781af81a7819f8197818f8187817f8177816f8168716081597151814a7143713c7134812c8124811c8115710d810670fe80f680ef70e780df80d780cf80c780bf80b780af80a7809f8097808f80878
|7,1=>0x283827b82738
|8,0=>0x4897482747b7473846b8463845b8453844b8443843b8432942a8422841994127409940183f983f273e993e093d883d083c883c083b793b073a973a183998391838893808378836f9367835f8357834e9346833f7337832f8327831f8316930e830682fd92f582ed82e582de72d682ce82c682be82b682ad92a5829c9294828b9
|8,1=>0x68b9684767c8675766c9664865c8653964b8643863b8633862b8623861a96119608960085f885ef95e785df85d875d085c975c185ba75b285ab75a3859c7594858b9583857b8573856b8562955a8552854a8542853a85319529852185198512750a850194f984f184e984e184da74d374cb84c294b994b184a894a1749894908
|8,2=>0x6e486dc86d486cb96c386bb86b476ad76a5869d86949
|9,0=>0x8eb88e388db88d388cb88c388bb88b388ab88a3889b8893888b8882987a8872886a8862885a8852884a8842883a88319828982088188810880887ff97f787ef87e787df87d787ce97c597bd87b587ac97a4879c8794878c8784877c8774876c8764875c8754874c8744873c8734872b9723871b8713870b870386fb86f476ec8
|9,1=>0xa5b8a529a499a418a398a309a279a1e9a168a0e8a0689fe89f599ed89e589dd89d589cd89c589bd89b499ac89a3999b8993898b8982997a8971996899608957994e9945993d8935892c9923991b8913890b890388fb88f38
|10,0=>0xad18ac98ac18ab98ab18aa98aa27a9a8a928a8a8a828a7a8a737a6b8a638
|11,0=>0xad97
|_,_=>0
def wAt:=mkWire dB 138 128 0xffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xe0d468350e0d414540806438351a0d4a0691f08038191a0d47c0f051a4383508024540b0e0d420191a0d42018051ac3835051ac38351a0d49837051a438350802468950524c38351a024883708214381a080647c0f1a0d47c0f081a438190513c201a0e0d4683510068143c081a454530806020190e0d468351514c38350806420180513c201a0e0d44018050f03835
|1=>0x381ac384d080687c0f051a43835051ac38351a0d468d60502c38351a0d4146b0802c38351a0d454080806438351a0d414530e0d420181a0d4bc132e2d420350e1a4143c0e0d46835081a468090602c38351a0d4146b08064146b0e0d4983708024145b0e0d4201b1a0d4bc0f2e2d420350e1a4ac1a0508038350524038351a0246835081a438190806068351502c2019
|2=>0x508038352b1a468350508038350e0d4201a0806c68350806020190e0d468350347518222e0dc38690e44458350806c20690806068350806020690e0d468350640c14230e0d47c0f0e06420182f02cb8b5080d438690e064540b0806468350806838350806c38350806420180806038351a0d42069081a47c200e06468353b0d420870e0686835051ac201b0802c1469
|3=>0xe1a47c0b051a438352b1a414200e0d52813050843835081a420181a0d4d80b1a53408351a40414230e0d4200b0602c68350251420931a02438590806c68350602438351a0d5381b0e08468350802c38351a0d438350806c6835080683835051ac180b0e0d46835050f020690e0d468351514c20190806068351a0d42002051ac3835051ac140b0e0d468354a2bc1421
|4=>0xe2d82035051a4140b0e0d468d60502c38350802c146b0e0d4397a0f0dc20692e2dc20350e1a420850e068683508000146b0e0d47c23051a43835050f03835081a468d50502c383508008146b0e0d47c0f051a438352e2d820350e1a4201a0806c68350821c381a1a0d415670e0d4206b0657468350e08838350806c68350806420181a0d4381908060683546084b837
|5=>0x1a57468350e088180b0e0d468352e2d020350e1a420190e06468352e66c3869080dcb9990e1a420371f08c38191a0d4540b0f0d42069081a438191a0d5900b0824468091f03c38191a0d43835570d438220e0d4201a1a0d420870e06868350e134201a1a0d43911590d4206b1f08014690e0d414230e0d468350802c180b1a0d42069082406809080242035020d46981
|6=>0xe0d46835050803835051ac140b0e0d415670e0d4206b051ac38351a0d438351a02468350e7199869080dc38350806068350e134201a1a0d4ac690508038351f08038191a0d52813050843835051a438350802469010508c3835036f4b8220e1a414210508038350508c38220e0d5b4352e08038696b0d4b8230e1a4201a0e0d468350e14420181a0d4b8b5080d43869
|7=>0x657c68350e08814200e08438350502c38351a0d438510806068350e0d420181a0d408350602c68354e06038211a0d420090e0d468350e064201b1a0d42000051ac38351f08c14690e0d4143c0e0d420690e0d46835081a438b5080d4206b08064683508008146b0e0d438352e08c38691502c20191a0d47c0f051a43835150dc20191a0d4381a1a0d420691a354140b
|8=>0x1a0d4195f1a0d438220e0d4b8200e1a46809080d40835081a438b6080d438590806c68354e06c38211a0d5bc352e088386908024146b0e0d438350806468354e06038211a0d40835080246835160d4201b1a0d4180b1a02468350e1583c35081a43835260dc20093602c90351a02408351a02468351f08014690e0d420690e0d468350e744b46b080d454080f0d42069
|9=>0xe0dc38220e0d420931a0242009081a438351a0d46835081a420850e068683546088b8370e1a414900e0d468090e15820191a0d420691a0d43822081a55c350e08838354e0dc38210508814230e0d5e0350e0f820691a6255c350e088201a0e0646835051a438350802c38352e0dc38690806438351a0d420690806068350524c38351a0247c6b0e0646835150202019
|10=>0x81ac3835081ad38370e0843835081a59809080dc201b1a0d4b8370e1a4383e081a4986b0802420191a0d46809080dc146b0e0d438351a0243835081acb40b080d4140b0e0d43c0b081a4b8230e1a4694d020d438350802468d10802c20901a02414220e0d420690e0dc3c37081a490371a02420921a02414200e0d4983708024383e081a43c09081a43c35081a4206b
|11=>0xe0d55c350e0882035020d4b46b080d42009080dc214f020d43999080dc2035081a4201a1a0d438350802c38b6080d4180b1a0d414090e0d42035081ac14220e0d414690e0d43965081ac6809081a59869080dc201b1a0d4b8200e1a4200b081a414230e0d46809020d42009080d43835081a4d0350802c695d0e08814210e0d418091a0d4200b1a0d42009020d56435
|12=>0x80dc20091a0d438690e0d468350e0d414690e0d43822081a4381a1a0d4214d020d40965081ac2037081a468091a0d4383d081a43821081a414230e0d490351a024146b0e0d468350e08820350802c14210e0d43821081ac201a1a0d420181a0d438211a0d4180b1a0d5386b0e08414230e0d438191a0d420911a024381a1a0d46835020d420350e1a420931a0241420
|13=>0x81a4206b1a02420090e08820370e0d438210e1a438351a0d420350e0dc08350802cb8220e1a414200e0d46809080d438210e0d42009081ac20181a0d43869
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x3cc0a500000640000000000000000cc000000c000
|7,0=>0x34900003390ca43190c242f90ba42d900002c90ae42acca830000a44284c000278c9a4000096424cc90300008c4221084420888021f4c0001e8c7731cd06f41ad067418d05f416d0592155000014504d4128c46410900000f903d10e503540c502d40a8c27308d01f4070c193058c124
|7,1=>0x3588000
|8,0=>0x654d92363cd8c3624d86360cd8035f4d7a35dcd7435c4d6e35acd683594d62357cd5c3564d56354cd503534d4a351cd443504d3e34ecd3834d4d3234bcd2c34a4d26348cd203474d1a345cd143444d0e342cd083414d0233fccfc33e4cf633cccf033b4cea339cce43384cde336ccd83
|8,1=>0x944e4e392ce483914e4238fce3c38e4e3638cce3038b4e2a389ce243884e1e386cc000860e153848e0f3830e093818e033800dfd37e8df737d0df137b8deb37a0de53788ddf3770dd93758dd42744dce372cdc83714dc236fcdbc36e4db636ccdb036b4daa369cda43684d9e366cd983
|8,2=>0x27239bce6c39a4e66398ce603974e5a395ce543
|9,0=>0xbccaf12bbcaed2bacae92b9cae52b8cae12b7cadd2b6cad92b5cad52b4cad12b3cacd2b2cac92b1cac52b0cac12afcabd2aecab92adcab52accab12abcaad2aacaa92a9caa52a8caa12a7ca9d2a6ca992a5ca952a4ca912a3ca8d2a2ca892a1ca852a0ca8129fca7d29eca7929dca752
|9,1=>0xd2cb492d1cb452d0cb412cfcb3d2cecb392cdcb352cccb312cbcb2d2cacb292c9cb252c8cb212c7cb1d2c6cb192c5cb152c4cb112c3cb0d2c2cb092c1cb052c0cb012bfcafd2becaf92bdcaf52
|10,0=>0x35b1d687591d607571d587551d507531d487511d4074f1d3874d1
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 14
def pmP:Nat→Nat
|0=>0x74400000e0800001b1000003420000060000000a0000001310000024600000440000008100000100000001c200000304000004dc0000091000001200000020c00000408000007f800000fb000001040000020000000210000003f000000440000008400000100000001f0000000800000008000000080000000
|1=>0x9e7600012004000210000001df300003a7600006fec0000dbd80001b3300003626000065ec0000c9980001400000023f600003dcc00007a100000e0000001ae6000031cc000062100000baa000016f600002ccc000051d800009730000126600002200000041000000802000010000000100000001e1000003c1
|2=>0x416ee00082dcc00104f9800209b3000412fe000825ec00104bb800209730004126600080f0400101c300020373000402040008000000087fb80010c13000217f6000427ec00081e1000103a2000200fe00037cec0006f1880009fb300013e7600026ccc0004c01000096b10000fe2600017cec0002e9980005a00
|3=>0xc02e6001437dc00286f9800509fb00083fe600107dcc0020ef980041b7300082b26001027ec002014100034c3300061a76000c2ccc0016f9d8002da030005066600093cec00126b980024d3b00049876000924cc001240000021f3b000437e600086ddc0010db980021b33000432e6000864cc00106f980020d73
|4=>0x4433e6008825dc01100000020000100280966003925ec00704fd800e09f3001c12f6003825cc00605fd800c09fb001490b6002827cc00504bd80080083000c37e600186dcc0030d99800619f3000c32ee001865cc0030c99800611a3000c1be600182fcc00304f98006097f000c12f6001825dc00304b980060933
|5=>0x2069a760409b4ec081269d81020d3b02021866040110ec04b2619808e4d73010c9ae6021925fc04306f980860d73010c13f6021825e404304bb8086097301093fe602103fcc04206bb80840bf3010812e6020925ec04106b98082097700803886010062ac0130cf980260bf3004c16e6009827cc01304b980221b73
|6=>0x21010499b002197320041266400064cc60304b98c041b73044c16e6081865dc1030cb982060bf3040c07e6080865cc1010c998202181304041666080826cc10101f9820001a3031c12fe061825fc0c304bb8184483f021c13f6043827cc086045d8106097b
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x50400020000000002000200
|7,0=>0x15022224007708447029330c0a0d07021b00760700051003010202001c0e091a34170023694930280e108850165300131007430100123d0f11250e0726903e0b52070e
|8,0=>0xa7cc51b3406f811963c47f58a3632c5575c14b007480986bbd36ae82585e8a711e4ebb869520393c798f7f9d4862add69b4c473a4639376e5d1d213a14d4a67ad8788558807d588054735856586314abc8b9d9661f4d809e587b2db2c089414a3186804d58628c455cd7630c5863184f0d06ca3b58d57cba802e931ebf753221
|8,1=>0x6258421cc9cfa5ac8d5f9c
|9,0=>0x6367b68f9a4ece99626435d072c791b56c8585afbe645ec57bd37d5aa473a38fcbb864bcd2aa5859c684c2609fb0b52f8b7368843962a0b7614e58b78cbd83aea85e8fbf60c35b2ba28f925acd8e977e6d383f65b147b4d1bd94a95a5e58876cb73a988585b058655a852ab5
|10,0=>0xb55a6a96585827a1cd64578257bc58
|11,0=>0x57
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 31 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_125 10 roots_125 ops++addP pm 1 dom_119 9 roots_119 ops++addP pm 2 dom_47 6 roots_47 ops++addP pm 3 dom_46 5 roots_46 ops++addP pm 4 dom_123 10 roots_123 ops++addP pm 5 dom_63 9 roots_63 ops++addP pm 6 dom_111 8 roots_111 ops++addP pm 7 dzo_47_16 6 roots_47 ops++addP pm 8 dom_95 9 roots_95 ops++addP pm 9 dzo_87_32 6 roots_87 ops++addP pm 10 dzo_46_16 5 roots_46 ops++addP pm 11 dom_126 9 roots_126 ops++addP pm 12 dzo_95_32 7 roots_95 ops++addP pm 13 dom_54 4 roots_54 ops++addP pm 14 dom_118 6 roots_118 ops++addP pm 15 dom_31 5 roots_31 ops++addP pm 16 dom_55 5 roots_55 ops++addP pm 17 dom_94 8 roots_94 ops++addP pm 18 dzo_111_16 7 roots_111 ops++addP pm 19 dom_110 6 roots_110 ops++addP pm 20 dom_103 5 roots_103 ops++addP pm 21 dom_79 6 roots_79 ops++addP pm 22 dom_86 5 roots_86 ops++addP pm 23 dzo_110_16 6 roots_110 ops++addP pm 24 dom_62 7 roots_62 ops++addP pm 25 dom_87 6 roots_87 ops++addP pm 26 dzo_107_16 6 roots_107 ops++addP pm 27 dzo_91_32 6 roots_91 ops++addP pm 28 dzo_93_32 6 roots_93 ops++addP pm 29 dom_109 6 roots_109 ops++addP pm 30 dzo_85_32 5 roots_85 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_127 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_47 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_46 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_47_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_87_32_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_46_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_95_32_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_111_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_79 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_zo_110_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_zo_107_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_zo_91_32_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_zo_93_32_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_zo_85_32_81 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_125 10 s (0,roots_125.map (·&&&dom_125)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_127 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_125 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_127 gM v ys):RunD true dom_127 gM v (ori ys):=h
def Z (s:Nat):=barP dom_127 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 4 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 16 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 67 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 67 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 139 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 11 128 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 139 → Z 8 i = true := (range_split z8_0 z8_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 108 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 108 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 15 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 15 0 = true)
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
def dzo_151_8:=0xff00ff00000000000000000000000000ff00ff00
def gzo_151_8:=0xff00fe00000000000000000000000000fe00ee00
def gsh_151_8:=0xff00fe00000000000000000000000000fe00ee
theorem lowS_zo_151_8_148:Lower true dzo_151_8 roots_151 gzo_151_8 6:=lower_iso_b (d1:=dom_151) (r1:=roots_151) (T1:=gsh_151_8) [(dom_151,8)] (by decide +kernel) (lower_slice_b (T:=gsh_151_8) [(0xaa00aa00000000000000000000000000aa00aa,0,1),(0xcc00cc00000000000000000000000000cc00cc,0,2)] (by decide +kernel) lowS_148)
def dzo_215_8:=0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00
def gzo_215_8:=0xff00ff0000000000ff00fe0000000000ff00ff0000000000fe00ee00
def gsh_215_8:=0xff00ff0000000000ff00fe0000000000ff00ff0000000000fe00ee
theorem lowS_zo_215_8_148:Lower true dzo_215_8 roots_215 gzo_215_8 7:=lower_iso_b (d1:=dom_215) (r1:=roots_215) (T1:=gsh_215_8) [(dom_215,8)] (by decide +kernel) (lower_slice_b (T:=gsh_215_8) [(0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa,0,1),(0xcc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc,0,2),(0xff00ff00000000000000000000000000ff00ff0000000000000000,0,64)] (by decide +kernel) lowS_148)
def dzo_214_8:=0x55005500000000005500550000000000550055000000000055005500
def gzo_214_8:=0x55005500000000005500540000000000550055000000000054004400
def gsh_214_8:=0x550055000000000055005400000000005500550000000000540044
theorem lowS_zo_214_8_148:Lower true dzo_214_8 roots_214 gzo_214_8 6:=lower_iso_b (d1:=dom_214) (r1:=roots_214) (T1:=gsh_214_8) [(dom_214,8)] (by decide +kernel) (lower_slice_b (T:=gsh_214_8) [(0x440044000000000044004400000000004400440000000000440044,0,2),(0x550055000000000000000000000000005500550000000000000000,0,64)] (by decide +kernel) lowS_148)
namespace S_223
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(1,129),(2,10),(2,66),(2,130),(3,11),(3,19),(3,67),(3,131),(4,20),(4,68),(4,132),(5,13),(5,21),(5,69),(5,133),(6,14),(6,22),(6,70),(6,134),(7,15),(7,23),(7,71),(7,135),(8,9),(8,10),(8,72),(12,13),(12,14),(12,28),(12,76),(12,140),(16,17),(16,20),(16,80),(16,144),(18,19),(18,22),(18,26),(18,82),(18,146),(24,25),(24,26),(24,28),(24,88),(24,152),(64,65),(64,66),(64,68),(64,72),(64,80),(64,192),(128,129),(128,130),(128,132),(128,144),(128,192),(136,137),(136,138),(136,140),(136,152),(136,200)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffffffffff
def xsM:=roots_223.map (·&&&dom_223)
def gM:=goal_223&&&dom_223
def NN:Nat→Nat
|5=>12
|6=>69
|7=>201
|8=>216
|9=>74
|10=>11
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0xed08cd272ad1ce9c8faaa55f07114f6b89c6ae5b69f546211c4e0f447e00
|6,0=>0xff6d4fe58cf45e5f2ff9f1cbaeaf69e7a97e1e8ce05bddb5cdd890cd3857d213ccfeaec7c37c48e3c32debb403b9d0cac11caa630a7541a5e16a4f21a13a6a03469fe519f8f19c6899617189e2d890c1804d27cee273f71724096e4d76ddbe69020675d361e25545754e9254d8714d37a488f848513437a242c604221f4059d3e32e3c5a7394e038a6332dfd318683151a2f2e32e952280e828059213d21f5d5160540ee590e3cf0cca400789
|7,0=>0xa4dd5a438aa3fed9fe519f8809f3039cdf29610095bbe9452193d4a8ece48dd8289b26884a984ed78491d834e0804d27fad67f4af7e9057d8117d1da7cf3e7a11379f6077c4576ddb766d273194724096f3656e4d76cf526c6a46ace768b7c66d0265e696459e632ec6129c5d4c55d36a5d1905cbcd5a2a85820057ab7574d85707656774564c1560a8558295526554c2f53d005395e51562510215005d4e3374e2044dede4c5854a8114a2d549e2649ca549c3b4924e4859645dd544dc34313441c01405eb403e43d3c63a6a139724372e13503e34b673479a31e953108d30c932e2ed2dfc62dd6c2cebc2b9392954c274e125d0b25cc12459a22004214682065b1ce591cb491baec1abdb1ab6619db418fb717b87179621750e15e36145fb12bb70fe270c2720ae7b0a8f20a40107e94066a7061a1036060226f01485012ed
|7,1=>0xff237fdaccfd28dfb36bf7fb9f65a8f6490f32c8f130cef73fef716ef690ee99bee07fed418eb731eaf69ea8d4e8e7de77a0e4bf5e49e0e48e0e21c9e1765e173ddeff1dd90edd560db475dac4dd7d99d7d75d6eecd6e07d4941d3de0d3857d1ec7cb176c7cdec732cc636dc5f18c4d25c4af3c37a6c3371c26eabf670bee5bbd626bb39cb7eafb7c20b756db587bb537ab4c5eb2debb2815b22e4b16ddafb99ada63ad76dac9f8ac632abe5dab2cda94a4a8f65a6572
|8,0=>0xa0e36a000a9ddb999cd599bd19833795085933b992f8492031907f68fd7c8dd828dbb98d80f8c0228bf708bdbd8a2db8a2288800486ba6853da8529f84b31834d78344781e6d81e177fc8e7cc157b3b17b32b79fcd779a7724097217a70f3f6f7c36d6b16cbe36ca4c68d44681e366272647606414361898614476129c60df05d7fd5c6c15ba765b0c45975b58ce156ba2567745614953f845395e52b54521fc50d3e50bc14e2044e0c24de6a4da964add248f3c468aa45d64459e1443164357342e1340790401c64014b3f0653d23c3b0113acf537c8034e7c34622315752eb7c2ac7b2a3ac29d5529d0529968283e52804f27e9d2521224c7e249db237a92340022e462276d1f6d21e1a01ba7b1b4fe1b1521a4031a12415b5114c8d14c320c4d80a29809e160989908389063a1061a10428003a9a0359702ac70226f01348
|8,1=>0xfd5c0fd408fc756fbd76f87d1f872cf6729f6467f36a2f315ef2fd6f290bf28cdf2811f2229f0e02ef716eb7e4eb6d2eb1bee9b6ae87fee8637e81cee52fae49e0e42fee2d8ae0e2fe0054dfc23ded84de5a9dcf72db8efda2a3d75dbd64a3d59d8d0cded03becf845cf5b6cf18fce64ccd45fc966dc8532c6588c6525c636dc5d5fc5a0ac4e1dc3fb5c2d41c2ac3bf534bf09fbe6d8bc413bbf9cba4e2b89e2b7904b6c32b673cb5200b435fb23c6b1aa7b0f23ae090adb4cad60eace5cac868ab2a6aaab7aa5b6aa36da9f15a94a4a9208a6124a568ea3f0ca1e42
|9,0=>0xfdbcdfabeaf87e1f1b6cf1a80efca2ef716e8212e7662e75cad969fd6d3cd653cd4b9eccbe4cb6dfc9c91c8599c7b3cc2d80becb9bc6c9bbd72ba66eba5bab8715b608ab1177ad3cca8185a61f2a256fa24b7a123f9e93d9d6319b395962cb8782b8750c802ac7ea407c0997b49b6c231635dd628ed5ad995ad655916d58948518fd501d24ce6e433563d23c3ae6b363012e12b2bad4267b11ddfe1c0f519e4415ed0133dc1073a0c2bb0bbda06d070670c061a1036c100d2c
|10,0=>0xae79e9f4a1946448f57a799007474a6e16e6375a4e3a9306ac25239
|11,0=>0x1730e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffff00000000ffffffff00000000ffff000000000000ffff0000ffffffff00000000ffffffff00000000ffffffff00000000ffff0000ffffcccc00000000ffffcccc00000000ffffcccc00000000ccccccccffffffff00000000ffff000000000000ffffffff00000000ffff0000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00ffffaaaa00000000ffffaaaa00000000ffffaaaa00000000aaaaaaaa33333333000000003333333300000000333333330000000033003300ffffffff00000000ffffffff000000000000000000000000000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0000ffffffff000000000000000000000000ffffffff00000000000000000000ffff000000000000ffff000000000000ffff00000000ffff0000ffffffff00000000ffffffff00000000ff00ff0000000000ff00ff000000000000000000ffffffff000000000000000000000000ff00ff00f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0cccccccc00000000cccccccc00000000cccccccc00000000ccccccccaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa
|0,1=>0xffffffff0000000000000000000000000000ff00000000000000000000000000000000000f0f0f0f000000000f0f000000000f0f0000000000000f0f0000000000000f0f0000000000000000000000000000000000000000000000000000000000000000ffff000033333333000000003333333300000000333333330000000033333300ffffffff00000000ffffffff00000000ffffffff00000000ff00ff000000ffff000000000000ffff000000000000ffff0000000000000000ffffffff00000000ffff000000000000ffffffff00000000ff00ff000000ffff000000000000ff00000000000000ffff00000000ffffff00ffff000000000000ffff000000000000ffff00000000000000000000ffff000000000000ffff000000000000ffff000000000000ffff0000ffffffff00000000ffffffff00000000ffffffff0000000000000000ffffffff00000000ffffff0000000000ffffffff00000000ffffff00ccffcccc00000000ccffcccc00000000ccffcccc00000000ccffccccfffff0f000000000fffff0f000000000fffff0f000000000f0f0f0f000000f0f0000000000000f0f0000000000000f0f000000000f0f0000
|0,2=>0xff000000000000000000000000000000ff00000000ffff0000ffffffff00000000ffffffff00000000ffff000000000000ff00000000000000000000000000000000000000ffffffff00000000ffff0000ffffffff00000000ffff000000000000ff00ff0000000000ff000000ffffffff000000000000000000000000ffffffff00000000ffff0000ffffffff000000000000000000000000ff00ff0000000000ff00000000000000000000000000ffff0000000000ff00ff00000000000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f003300333300000000330033330000000033003333000000003300330000003333000000000000333300000000000033330000000033003300555555550000000055555555000000005555555500000000555555003303330300000000330333030000000033033303000000003303330055055505000000005505550500000000550555050000000055055500ffffffff00000000ffff000000000000ffffffff00000000ff000000ffffff0000000000ffffff0000000000ffffff0000000000ff00ff00ffffffff00000000ffffffff00000000ffffff0000000000ff00ff00
|0,3=>0xff00ff0000000000ff00ff0000000000ff00000000000000ff000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff0000000000000000000000000000000000000000ffff000000000000ff00ffffffff00000000ff00ff0000000000ffffffff00000000ff00ff00ffff000000000000ffff000000000000ffffffff00000000ffffff000000000000000000ffffffff000000000000000000000000ffffff00ffffffff00000000ffffffff00000000ffffff0000000000ffffff0000000000000000000000000000000000ffff000000000000ffff0000ffffffff00000000ffffff00000000000000ffff000000000000ff00ffffffff00000000ffffffff00000000ffffffff00000000ffffff00ff00ffff00000000ff00ffff00000000ff00ffff0000000000000000ff00ffff00000000ff00ffff00000000ff00ffff00000000ff00ff00ff00000000000000ff00000000000000ff00000000000000ffff000000ff00ff0000000000ff00ff0000000000ff00ff000000000000000000ff00000000000000ff00000000000000ff00000000000000ff00000000ffff0000000000000000000000000000ffff00000000ffff0000
|0,4=>0xffff000000000000ffff000000000000ffff00ff00000000000000000000ffff000000000000ffff000000000000ff00000000000000ff0000000000000000000000000000000000ffffff0000000000ffffff00ffffffff00000000ffff000000000000000000ff00000000000000000000ffff000000000000ffff000000000000ffff000000000000ff00ffffffff00000000ffffffff00000000ffffffff00000000ff000000ffffffff00000000ffffffff0000000000ff00000000000000ff0000ffffff0000000000ffffff0000000000ffffff0000000000ffffff00ffffff0000000000ffffff0000000000ffffff000000000000000000ffffffff00000000ffffffff0000000000ff00ff0000000000ff000000ff00ff0000000000ff00000000000000ff00ff0000000000ff00000000ffff000000000000ffff00000000000000ff0000000000000000ffff000000000000ffff000000000000ff00000000000000ff0000000000ffff000000000000ffff0000000000ffffff0000000000000000ff0fff0f00000000ff0fff0f00000000ff0fff0f00000000ff0fff00ff00ffff00000000ff00ffff00000000ff00ffff00000000ff000000
|0,5=>0xffff000000000000ffff000000000000ff00000000000000ff00ff0000ff00000000000000ff00000000000000ff00ff0000000000ff0000ffff000000000000ffff000000000000ffff000000000000ff0000000000ff00000000000000ff00000000000000ff0000000000ff00ff00ffffffff00000000ffffffff000000000000ff0000000000ff00ff00ff00ff0000000000ff00ff0000000000ffffffff00000000ffffff00ffff000000000000ffff000000000000000000000000000000ff000000000000000000000000000000000000ffffffff00000000ff00ff00ffffcccc00000000ffffcccc00000000cccccccc00000000ccffcccc0000ffff000000000000ffff000000000000ffff00000000ff00ff00ffffffff00000000ffffffff00000000ff00ff00000000000000ff0000000000000000000000000000000000ffffffff00000000ffffff0000ff00ff0000000000ff00ff0000000000ff00ff00000000ffff0000ffff00ff00000000ffff00ff00000000ffff00ff00000000ffff0000000f000f00000000000f000f00000000000f000f00000000000f000000000000000000000000ffff0000000000000000000000000000ff00
|0,6=>0xffffffff00000000ffffffff000000000000000000000000ffff0000ffffffff00000000ffffffff00000000ff00ff0000000000ffffff000000ffff000000000000ff00000000000000ffff000000000000ff00ffffffff00000000ffffffff000000000000ffff000000000000ff00ffffffff00000000ff00000000000000ffffffff00000000ffff0000ffffffff00000000ffffff0000000000ff00ffff00000000ff00ff00000000000000000000000000000000000000000000000000ffffff00ffffffff000000000000000000000000ffffffff00000000ffffff00ffffffff00000000ffffffff00000000ff00ff0000000000ff000000ffff000000000000ff00000000000000ffff000000000000ff000000ffffffff00000000ffffffff00000000ffffffff000000000000ff000000ffff000000000000ffff0000000000ffff000000000000ffff00ffffffff00000000ffffffff00000000ff00000000000000ffff0000ffffffff000000000000ffff00000000ffffffff000000000000ff000000ffff000000000000ffff000000000000ff0000000000ff00ff0000000000000000000000000000000000ffff00ff00000000ffff0000
|0,7=>0xffffffff000000000000000000000000ffff0000ff00ff0000000000ffffffff00000000ff00ff0000000000ffffff00ff00ff0000000000ff00ff0000000000ffffff0000000000ffffff00ffffffff00000000ff00ff00000000000000ffff000000000000ff00ffffffff000000000000ffff00000000ff00ff00000000000000ff000000000000000000000000000000000000ff00000000000000ff0000000000ff00000000000000ff00000000000000ff0000000000000000ffffffff0000000000ff000000000000ffffffff0000000000ff0000ffffffff00000000ffffffff00000000ffffffff0000000000ff0000ff00ff0000000000ff00ff0000000000ff00ff0000000000ffffff00ffffffff00000000ff00ff0000000000ffffffff00000000ffffff000000000000000000000000000000000000ff00ff0000000000ff00000000000000000000ffff0000000000000000000000000000ffff0000ffffffff00000000ffff0000000000000000ffff0000000000000000000000000000000000ff000000000000000000000000000000ff0000cccccccc00000000ccffcccc00000000cccccccc00000000ccffcccc
|0,8=>0xff00ff0000000000ff00ff00ff00ff0000000000ffffff0000000000ff00ff0000000000ffffff000000000000000000ffffff00000000000000000000000000ffffff00ffffffff00000000ffffffff00000000000000000000000000ff0000ffffffff0000000000ff00ff00000000ffffffff0000000000ff000000ff00ff00000000000000000000000000ff00ff0000000000ff0000cccccccc00000000cccccccc00000000ccffcccc00000000ccffccccffffffff00000000ff00ff0000000000ffff000000000000ff000000000000000000000000ff00ff00000000000000000000000000ff0000
|_,_=>0
def sP:Nat→Nat
|0=>0x80e0b010010060815180402010014170c0b020100080e0402010a060e04020d00060c040b11010014130c0b110100080c0b12000706080e04010010060f0b110009060e04031101000c0b110009080504010010060e04010a07060f0b020a09060e040302010a0e040d0007060c0b020a0908050401000706050403020100
|1=>0x1100090608150b01230706080e040b020d00060f0b22020100140e04010007061615040302010a140f0b02000906160e0403020100160c200201001415040201001f14150403020d00140c0b02000916080f1a0b02010a060e0b01001e061d0f1a0b020d000605040b020100060c1a0b02010a08150b001b0706080c1a0b020d
|2=>0x706080f0b01001e061d0c040b020d0014150b01002806080f1a0b110100060c0b02002714080c1a0b11010008150b0200260608050b0100070608150b02012506080e0411010006150b0024070608150b0100070608150401000714061c0403020100190c0402010a14150b00090706080c04020d00140e040b02010a06150b
|3=>0xb0200270608150b020a0906080e050402010006050b0100100608150b01250706082d0b0100070619150b02001b06080c0f0b020009140c04110100141504020100142915042a02010014150403010007140e040b11010006150b02010014290e0b010a070608150403110100140c040b02010a14130c0b02010a080e0b0d00
|4=>0x1a0b0201000616150b0100070632080c0b1101001408150b02001b1406080c0b0201001435080c340b02010014080c1a0b02010016080e150b02010006080c300b020100080e15040201001406151c0b02000906080c0b0100073106080c3004020100140c2f0b020100080c0b2e020100140504020100060c0b020027060815
|5=>0x3f14150b020027140608150b0100073e06083b0f0b02010006080e050b02010006083a150b0201001408151a0b11010006080f0b010007061d08150403020100141639150b01000706081c0402010006192b1504020100140c150b02012506080f0b010007061908130c0f0b020100140f0b11010014060c0b0201003706080f
|6=>0x1002806080c0b0201000644080c0b020100144708151a0b01000706080c0f0b02010045143a0f150b020100140f150b02001b0608150b020100064408050b0201000608150402010014064215040b02010a14060e040b020100061615410b0100070608390c0b020100140c0b40020100060815040b020d0014060c0b020100
|7=>0x608150b010007061908150b2c020100140e0b020d0006080c150402010050143a0c0f0b020100081c0b0201004b0608150b02010014064f0c150b0201004e140c0b020100064c080e0b0201004b060815044a020100140615040302010014190c0402010014160c0b02010049140c300b02010014080c2102010014080c150b
|8=>0x2010006190e1504030201001415340b0201000608150402010014064f2b15040b020100141504110100140615530b02010006080c0b010007061d080c15040201004e143b150b02010006080c0b0100070619080e0b02010a06080c0b02120014080c150b020009140852150b0201000608150b010007061d08150b01000751
|9=>0x14060c0b02010a080e2d0b02010006190c150b02001b0608150b0257000608150b5602010006080c040201001419480c2d0b0201001415040201005514060e150b01000706080c340b02010006080e15040100071406151c040302010014540e150b02010006480c0f0b0201001415042c020100140f150b02000914061c040b
|10=>0x140e0b010007061608150b02012506080e2d150b01000706155b02010014060c040b02010014162d0b0201000619130c0b02010016083a0c150b020100085a150b0201001406150b2e02010014060c210b02010014080c0f0b02010014320f0b02010a060e150b0100071e06150b01000706080e150b02012506081504010007
|11=>0x2010014060c040b02010014190c0b02010a1408150b01002806080f0b0201004b14060c0f1a0b020100140c0b020d0014080c0b0201004b14083b150201005e06080e0c0b021200060815040b11010014060e150b010028060836150b0201000608150422020100140e0b5d02010006085a0c150b02010014390c0f0b020100
|12=>0x80c0f0b0201001419151a0b02010a0608156102010014061504020100501460150b02010014060f0b0201004b0608540c150b02010014151a0b020d0006080f0b02010a140615040b01000714060e0b010007061d0815045f020100140613150b0100070608150b0100071406080e0b0100070619080f0b020d00140654150b
|13=>0x100071406150b010007450608150b0201003e060815200201001406020100640608150b2202010014080c15040201006208150b0200270619080e150b02001b06080c2d0b0201001419150b02000906160815630b0201001406150b0100071e14060e0b1101000608390c150b02010014150b0201251406080c150b02010062
|14=>0x6080c150b2c020100140f150b0100071e0668150b02010014080f150b02012506080f0b110100060c0b5d02010014082d0f0b0201000619150467020100140615200201000608150b01002814060815040201006514063a0e150b020100080c0b11010008150b02001b0608540c0f0b02010006540f150b020100062d150b
|15=>0x150b0201006c06150b61020100140648150b0100070608150b0201000619080c15042c02010014150402010a14062d0f150b010007060e0402010006160c0b0201004b0608150b02002706086b150b020100140836150b01000706081504020d0014060f0b5d0201001406150b0201004b0608150b0200090619080c6a0b0201
|16=>0x1c040201001406020100314e06080e150b020100060815040b0201001406160c0b020100067208150b0270000608480c2d0b02010006080e150402010014060f150b0201003d060815046102010014060c0b02010047080f150b01002806080e150b02000906086e150b02010014060c15040201001419480c0b01000706080f
|17=>0x1000608150b020d0014060876150b0201001406080c150402010014150b0201004b1406080c151a0b0201001408752b150b020100060815040200090608150b220201000608480f153c0201000608150b02010074060815040201006d0608150b0200090608390f150b02010014066e150b02010006080c150b010007060815
|18=>0x14190815340b020100061908150b02010078140869150b0201000608150b5d020100060815040b020100140619150b02010a1406080e0b0201000616081504220201000608150b02010077140608360c150b02010006080f151a0b02010014060e2d150b020100060f150b0201003e06085a0c150b0201000608390c0f0b02
|19=>0xc0b0201001408150b0201000679080c0b0201001608150b020009140608150b0201005006080e15040b0201001406390f153c0201000608150b020100460608130e150b02010006080e150b020100140608150b0201004e14060f150b02010014061915045d02010006084d0c0b020100060868150b02010006080c150b0201
|20=>0x1007a4e060815340b0201000608390c150b02010006081c0b0201000619083b150b02010006082b150b02010014084d153c020100060815040201005006080c0b02010031140852150b0201000608540c150b02010006080e0b0201000619080f0b0201000616155c020100060815040201004e1406151c040b020100140648
|21=>0x20100061908484302010006081504030201001415580402010006486602010006080f150b0201006d0608150b0201007b060869150b0201001406080e150b0100070608150b5d0201001406080c150b0201003e06080c15040b020100140e2d150b02010014060e150b020100450608150b1101000608150b02010006350802
|22=>0x608150b020100064708155c0201001406080e2d0f150b020100060c150b2c0201000608360e150b02010006080c0b02010014160815330b0201000608150b0201007c06080c2d150b02010014150b01000706083a150b0201000608153c0201004e060815040201007b06080c0f150b020100142d150b020100140648150b
|23=>0x140608150b0201001406350836150b02010006080c15042c020100060815340b020100140608151a0b0201000616085a150b0201000608150b2e020100060875150b0201000608480e0c0b0201000608152102010006080c150b02010006190839730b020100060852150b0201001406080f0b020100140616480e150b0201
|24=>0x6087d0c0b0201000608151c0b0201000632080c0b0212000608150b0201003d0608150b0201008006080c0b0201001419080e150b0201000632087e150b02010006080c2d0f0b02010006150402010049060e150b0100071406080e0c0b020100310608394302010006082d0f150b02010006130c150b0201001408150b1101
|25=>0x3e0608130c0f0b020100060815330b020100140608151a0b020100061908156f0b02010014060c150b020100451408390e150b0201000608130f150b020100060839150b0201001406150402120006080e0f0b020100061908150b0201006206080f0b020100140619150b020100590608150b0201003f1406150b01000714
|26=>0x390c0b020100060836150b0201001406081504660201000608150b0201004914060c0b0201003f0608150b028200060815210201001406080e0f150b01000706080f0b020100061908150b810201000608150b020100140647081504020100620608132d150b020100060854150b020100060815044302010014060e150b0201
|27=>0x608480c150b0201001408150b021200140608151a0201004e06080c0f0b0201004506080f150b01000706083a0f150b0201000608130c380b0201000608151c1a0b0201000608150402820006080f150b0201004506080e151a0b02010006087d153c020100060815210b0201000608150b0201003e06081504020100140616
|28=>0x100060876150b02010006080c15040201005006080e0c0b020100061908150b0201004b06080c150b0201004e060839153c0201000608150b0201008306084815580201000608480f150b0201001406150b0201006c06080e150b0201000619080c0f0b020100140c0b0201004906080c150b0201005006080c150b02010046
|29=>0x7060815042c02010006080c0b0201000619085a2d150b02010006084d1504020100060c150b02010014320815040201004b0608150b02010a0608150b0201008506080c15040201004e0608150b020100770608150b0201000619081504020100140619150b020d000608360f150b0201000608150b020100840608150b2c02
|30=>0x60815040201001406151a0b020100140608151c0b02010006080c0f150b0201000608150b0201006d060815040302010006080e150b02010006080c150b020100450608150b0201001406160815210b020100140608150b0201003e1406080f150b020100140632482d150b0201000608480c0f0b02010006080e0c150b0100
|31=>0x1001408157f0b020100060815040b020100140613150b0201000608150b0201004e0608151c0b0201001406080e150b0201001406080f730b020100060887150b02010006084d150b0201000608480c150b0201000608150b02010014061908150b020100710608390f150b020100060886150b02010006080c2d150b020100
|32=>0x608150b02120006080e0c150b0201000608480c0b02010006080c380b0201000608153c0402010006081573880201000608150b0201007806082d150b020100060815730402010006080c0f0b0201000608150b0201004506080e0f150b02010006080f150b020100140615040201004e060848730b02010006080c150b02
|33=>0x6080c15880201000608156f0b020100060839150b02010006080c15040201000608150b0201003f0608150b4302010006081573040b020100060848153c0201000608150b660201000608150b02010006320815040201003106082b150b02010006080c0b02010031060848150402010006087d150b020100060815580b0201
|34=>0x60815383c0b0201000608480f150b0201000608150b0201007a0608150b020100061908150b02010014063208130c150b0201000608151a040201000608151a0b02010006080f153c0b0201000608150b02010031140608150b020100490608391504020100060848150b020100140608150b020100061608150443020100
|35=>0x150b02010006080c150b0201000608150b02010031060848150b020100060815380b0201000608153c0b02010006080f150b020100060815730b020100060815040b0201000608150b020100140608158802010006081504020100060815040201007a06080c15040b0201000608150b030201
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x21300f1806cc030601530091803cc018600930031800cc0006
|6,0=>0xfd387cdc3d8e1e570ef3875dc3a0e1c970e1b06f1c36ae1ae70d3b8681c332e19270c5b8611c2fae17670b7b85a1c2c2e15a70a9b8531c28ae13e709c304c5c254e123708e38459821ee1096081383edc1e8e0ed70733837dc1b0e0d1706538311817ae0b67057b82a1c142e09a7049b8231c10ae07e703bb81c1c0d2e063602eb0159c09ee0487
|6,1=>0x21c710ab8839c410c2017
|7,0=>0x2074101a07fd03f681f7b8fa1c7c103d881e840f22078103b881d840ea20741039971c938e2a0706e37b81b9c0dae06c7035b81a9c0d2e0687033c719a40cb20649031c818ab8c36060b02fe717b40bba05cd02de816b40b3a058d02be815b40abdc550e2a0814c40a420512e281813cc09c604d4e262812d4094a04950242811db88ce045702238
|7,1=>0x2fdc17ce0bd8e5e572eec17560b9ce5c682df416da0b5d05a682cf4165dcb1f058782bfc15de0ae0e56882b0b95660aa4e54a82a1414ea0a65052a8291414718a29050d7282c13f9c9f0c4f0827441385c9b304d272654130a097504b282554128a093504928245b920e08f704738235c118e08b7045472264111208790434821641095c83ce4168
|7,2=>0x3f4c1f860fb307d273e541f0dcf7707b473d641e920f3ae79583c6c1e160efb077583b6c1d960ebb075763a7c1d1e0e7f0738739841ca20e41071a6389b9c2e0e0706fb8379c1bae0dc8e6de636b41b3a0d8d06be835b41aba0d4d069e834bb9a3e0d0f067f833bc19be0cd0e661732cc19460c930641831d398ca0c550622830d4184a0c1506037
|7,3=>0x8308414ba086103308118404c20060ff307f18
|8,0=>0x520c28e614630a28951042865d424ea0a8500ca7e613e309ea74f14276a13a329c894e0426de535d29a684ceca656131b098584be4a5ce52d7096384adc254a52950942849d424c65251291f948bc243a520b28fc947a423ae51c8e8db94694a3265184e8ba8458ca2a61143089a7448ca2261103087984393a1aa10c3285984293a126508308389
|8,1=>0x62743116587b0c3586173b09658392c157606c301257f90bf395f5c2f8a57b32bd095e442f0217710baf95d43ae7e572f0b8e95c342df656eb0b6d85b24ad6e56a52b4a85a142cea16650b2b7591c2c6e16270b0b8581c2bea55e6eaec7572bab79d5ab2acd85624aaf215672aaa955142a6655212a897540c29e9d4e50a699530c296614a30a498
|8,2=>0x7314b96a1ca32e498720c38e61c612e28870fcb861dc210e0796ff4b7d65bdb0de586ee4b7521b972dc296dccb6c9db532da096cc436421b110d8086bc435be5acf0d5f86abc3541da910d3f969bc34be1a4d2d1e868acb4361a0b0cfc9679cb3aa59c32cd986684b31e597d2cb68657bb29a593d0c9686474321a18fd0c768636cb199d8bd0c568
|8,3=>0x7954bc865e312f0f97834bbf65deb0eed87724bb75dda92ecc8762bbaf61d692eac875243a721d2aee8c9742439f21ce90e6b9
|9,0=>0x89cc44c2624f311f888bc443a620d10fe887b443ba21cd10de886b4433a218b30bd885ac42b6214b109d884ac4236210b107d883b3c1b660cb105d882ac4136208b103d881ac40b6204b101c980a4403220090ffc87fa43fb21fc90fdc87e9cbf2a5f850fba87d943ea65f412f9887c7cbe1e1efd2f7777b74bd9a1ebb2f5587a6c3d161e792f339
|9,1=>0x231d118598bec45d262d7316388adc454a629331418
|10,0=>0x479223b911d488e644712237911b488d644692233af1967
|11,0=>0x11ec7
|_,_=>0
def wAt:=mkWire dB 137 224 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x16454500c1a054191508418211a01c54500b1445419210842c591514018211514068070b14454210016454500b14418210b14454211514018210b08470651514c5452001645419151402c51060845419151402c51060841c5b0e02c5451151401067151482c210b08454510016454500608454510b0840459151401821150640859151401821021645419151401821
|1=>0x150842c51150640859151402c2106084b0520c04054192b04054530b08454510216454500b084380b15144005915140541900164545006084005915064545006084541e0e02c3c19150840859151402c51060845452021645419151402c5106084385b0e02c54511514008591514454500b0841821150640059151402c210608454190b08404591514018210b0845451
|2=>0x1506454210216454211514018211338c54230c0b45450150842c5106084085915064545006084d8070e0b4545131148542f151485419151402c5106084cc511532c2c5206084305b1506454500608470511514c2c21060842c210c16c5419151403c681506454210b14418210b08470651514c5452060842c210e16c54511514018210502c70651514c54521a01c5419
|3=>0xb0845450151442c210b074380b0f06454210f0b418211506454210b08404591514018210f0bc18211506454213401c2c651514854f50f3c82c1915084385b15144545006084d81b0e0b45451060840859151402c5106084541e0e02c3c191508454500406c2c21060842c211514c54520608470191514c2c2106084d8030e0b430210e02c38570f06454210c0b41821
|4=>0x150482c214d0c92023150b4d8570e0b43c191508454520b0845450150642c2106084541931084542f06084305b1506454500b16454191514018213602c382d0c084551a45084302f150645419481401821150b42c510e02c545106084302f06084541915084e41b0f0b454213601ce4190f0b4551a4508454191c19454531514818214314854100b0840059151401821
|5=>0x1514c545215144101b0b08418210b19438570f06454214e14854120b08454530216454500b084182115078380b0c08454191506454120b0841821153d43cf215084380b0e15c30211506454510016454500608418211506404c5150bc6807150642c510e02c3c191508418210c04054190b08454510116454500608454193906c3c2d150853852150482c21150641821
|6=>0x15194545206084d8030e0b43c19150842c210e02c54510608400591506454500608430230e15c302115064d8070e0b430210159455633c08c2c191a16c54500b14418210b0845419151481821150b430231c04854530b084182115194545206084380b151442c210608454533608c382d0f064542115084182115064542d0c04054190b08418211a01c54210b1442c21
|7=>0x1519454520608418214306454100b08430230608454190f0b454210e02c545115140d8030f3c42c191508438230e02c3c191508570210b16c54500608454500608454190b08438570e08c3c1915084302d1506454500608454193906c3c2d150843c68150842c510608454190b1645450060842c52060845419150845421001645450060841c230e02c3c1915084380b
|8=>0xe02c545106084541e0e02c3c19150841067151482c2106084380b1519454520e15c380b0f06454211508404591514018213608c382d1514418210b08454521506400591514018213602c3cf10b0645421151a82c51060845419150842c5106084541901164545006084546a0b144182115584f0230c084541901314542f021645450060842c210e0b43c1915084382d
|9=>0x1506454521a01c54500b14418213308454cb0b14818210708c380b1514418210216454511514018210f0b418211506454213600c382d1514538191504854190b0845421150645452060840059151402c5106084105b151402c21060843012150642c21060854823153242c5206084d857390643c2d150844c230c0b454190b1445450060840059150845450060842c21
|10=>0x60845419151a02c510608438230e15c3c19150843810151442c21060842cb96608454f00b064d80b0e0b454513606c382d0f06454210216454191514018213601c3cf10b06454211308c302d150644c231508454f10b064380b0e08c54510608484210b164545006084e50f1504054110b0857419151a02c510608540190c04854190b084d8070e0b43c19150843023
|11=>0xb06454210416c54500b084380b0f06454210c04054190b08418210016454500b08418210e02c38230f06454211514454500b08418213615c382d0c08454193401c2c651514818213306454cb0b14818210e02c382d0f06454210b0840459151401821151a054210608430100608454190b0841c230f064542169065205306084542d3600ce4190f0b40859150845450
|12=>0xf0b454216f0b5cc211506c380b0c08454191514c2c2106084542f150482c21151945452060845450060842c210c38c54191508c05c5153cc2c190c08c5419150b454510b08418210f3c82c1915084105b151402c21060852050060845419150b4d80b390643c2d1514468070b14418216f0b470211514c18211514854190b08418210e02c302115064542d6d08454f2
|13=>0x608454511514018214306454100b084c451150bc18210e0b430211506454210b14418210e08c3c1915084382f0f06454212d0b430231506454190f0b4542101164545006084702d1514c1821150642c2106084546a0b1441821150642c5106084e0191508c6807040642c214306454100b084542d0b06454212d0bc30231506454f20b0842c191a01cf0210b0641821
|14=>0x15064542d0b19854520608454191514018211a01c2c51060843012150642c211514418210b0842c190f0b4542145084302f1506430210c0b45419151945452060841821150482c21150845452060845468040642c214808c5419150b534194808c542d150645452060842c6515148182131064542f06085205306084542d151a0f0210b0642c21151481821001645450
|15=>0x608454190b08438231514418210c084302f15064085915140182131148542f0608454121504c2c210b19454520608454190f0b454211514c54520608455613c08c2c191c0645453060852023150b42c190c04854190b0845419150bc1821153242c52060844c230c0b454191514454520608454211514018210b16c54500608454120b08418211514c18210b0841821
|16=>0xf06454211506454500608454cb0b1481821383c854230b06418210c08c54190e02c3c1915084e41b0f0b45421150482c210b065cc121506c2c2106084541915084382315144182115148182115040542d0b084101b0b08418213c08c2c210b06454f0150b42c19153c82c1915085cc121506c2c214814c1821150b4380b0f0645421151a02c5106084382f0c0845419
|17=>0x6084302d15064085915140182131148542f060843cf10b06454210c04054190b0842c65151481821151402c5106084b42d0c08c54196608454f00b065f419380b454230c0845419150b42c591514018210e15c3021150643c2d1506c5421153242c52060845421151401821150b43c1915085205006084542d0b16c54500608438230f06454210c04054190b084382d
|18=>0xb06418210f0b454210b08404c5150bc38570f06454214e06454120b08454211514818211558cf0230b06418210f0bc54210e02c5451060845419380b454231506404c5150bc3cf20b06454210f3cc2c19150845419151481821151442c5206085fc2d0f06c54210c08c541915085e8211504c2c210e02c545106084542f0c08454191504054110b0843023150645421
|19=>0xe0b454510608454f00b0842c1931084542f0608454190f0bc5421017a454130b0842c591514018210e02c3c191508438570f06454210f3c02c1915085205006084542d4e06454120b0843023150644c23153c42c19150402c2106084382f0f064542115084302d1506454cb0b14818210b14454520608470211514c182106084302f150643c190f0b454211508454f1
|20=>0xb064545115148182106084541915084541931084542f0c04854190b08514210c0bc5419060845419150b404c5150bc18211504810190b084302f1506454210e02c3c1915084e41b0f0b454211508c302d1506454530b1441821017a454130b084302f150645421151442c51060842c19380b454230b164545006084382f0f0645421151402c21060843c2d150645421
|21=>0xb1481821151a810190b08400591514018217108454f30b0645412150642c2131144542f0608438570f0645421151482c21060840459151401821390643c2d15084fc190f0bc54210c04054190b084702d1514c18210c04854190b08438570c0845419151a8f0210b0645412150642c210f0b42c1915084ac2f3806454233c08c542d0b064542106084542d6d08454f2
|22=>0x730b4541b4808c542d15064542d151481821153cc2c190f0b454214806c542d0c08c54190b08418210b14418211514c1821150645421153c82c190406c2c210f06454210c0bc54191514018210b164545006084382f151441821150842c5206084302315064542d150b4541915084380b0c08454190c04054190b08438570c08454190c08c54193908c54110b0845419
|23=>0x150b42c19153c02c190b1481821150bc2c21380645423150bc5419150b42c21380b454233c08c2c1901314542f0c084541915064542d1506454230b0842c191506c2c2331064542f0c08c54191506c2c211506454210c0bc54190f0645421060845421150482c211506c542d1506418210f06c5421060842c21153c42c19150482c211514c18211514418211506c5421
|24=>0x5419150bc542d1508c2c1915084541b0b08418210b08c2c211504c2c21150642c210406c2c211508c2c19150b454211504c2c211514818210b14818210c0b45419040642c213c0842c190b0645421150bc182131084542f150442c2106084542d151401821150402c210b08c541973084541b0f0b45421150642c210f0bc5421150402c211506c2c21
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x43288240000000000007e40f2a1d8c39980000de8000035a00000ce818d00000603000000002da85a10aaa000028a0000098a00000000000000011d4000042507c80000000000007480000000037300000c94000000005e60a94000026404480754000019402a8048c00000d5010a01100020000
|6,1=>0x9540000241445a8000
|7,0=>0xa89800029a85250a4094530000508c9f213b326e800009a9131425a84a8c932123323e846d08ba11342206434c851906420663fd07e18f841e8800007820ec41d26000072a0e141ba836506aa0d140000335064a0c6318482f905d20b731668000057a0ac315442a4452a0a1413a826500000000
|7,1=>0x44c8890910221c44326855108a20e34184821102220133fa87e500001f813e887c4cf6a1e943ca87850eea1d943aa80000e8a1cd439287150e0a1bd437286d50d8a1ad435466990d1219e433846610ca9800032286404c6218843088604cbf197a42ec85cccb9096e400005a90b3216332be856d0aba1543
|7,2=>0x5f0600017a22f045d88ba117222e045b88b6116a22d13000000000002cd45946b191619abf45768add159a2af4558600015422a445408a74d4ca29540000000148a28d45128a15000028144fc69e913b227244dc89a91339a6344be896d12ba253449e892d1241a45348288f511ca235400008c8d17222a4
|7,3=>0x319462a8c48d87230a460c8c0917f22fb3
|8,0=>0x7b26f58de99bd0379a6f28de39bc437826ef8ddd9bb8376a6ec8dd79bac37526e98dd19ba0373a6e68dcb9b9437226e38dc59b88370a6e08dbf9b7c36f26dd8db99b7036da6da8db39b6436c26d78dad9b5836aa6d4c9a81b4d36946d1cda21b41367c6cecd9c1b3536646cbcd961b29364c6c8cd901b1d3
|8,1=>0x9307254e491c8f39187224e431c83390071f4e3d1c7738e871c4e371c6b38d07194e311c5f38b87164e2b1c5338a07134e251c4738887104e1f1c3b387070d4e191c2f385870a4e131c2338407078a0d9c18382a7048e079c0c38127018e019c0037fa6fe8dfb9bf437e26fb8df59be837ca6f88def9bdc3
|8,2=>0xaa87544ea71d4b3a907514ea11d3f3a7874e4e9b1d333a6074b4e951d273a487484e8f1d1b3a307454e891d0f3a187424e831d033a0073f4e7d1cf739e873c4e771ceb39d07394e711cdf39ba5368e6b9cd439a27338e659cc8398a7308e5f9cbc397272d8e599cb0395a72a8e539ca430001284e4f1c9b3
|8,3=>0xb367660eca9d923b1e7630ec49d863b085604ebf1d7b3af075d4eb91d6f3ad875a4eb31d633ac07574ead1d573
|9,0=>0xc385868b0c16162c285848b08160e2c185828b0416062c085808b0015fe2bf857e8afc15f62be857c8af815ee2bd857a8af415e62bc85788af015de2bb85768aec15d62ba85748ae815ce2b985728ae415c62b885708ae015be2b7856e8adc15b62b6856c8ad815ae2b5856a8ad415a62b485688ad0159e2
|9,1=>0x318162e2c5858a8b1416262c485888b10161e2
|10,0=>0x18f071d8e3a1c7238e071b8e361c6a38d07198e321
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 15
def pmP:Nat→Nat
|0=>0x24800012000008e000046000022800010800008000003f00001b80000d800006800003300001900000c000004c000025000010800007c000032000014000008800004000001800000a000004000001800000a0000040000018000008000002000000
|1=>0x608000300000108400081f000403000200c00100400080000023b00011c80008be00045900022b00011500008a0000448000223000111000088400044000020f800100c00080400040100020000008ec00037400017b0000af80001fc0000be00004b
|2=>0x1224000911800488800244200121100090180042be00207f00102f800810800407e00203200100f800805000400c001c5f000e2700071280030be00145f000a0000041fc0020fa00105f00080e8004010002000000c5f00062d800314000188c000c40
|3=>0x502f80280fc01406600a01f005003802111801047e0081be0040af80201fc01008400803b00401b80200c801006000801f00322f801915c00c0be003c4e001c23000c1fc006004002c5f001621000a1fc0050be00281f00140000091fc0048be002458
|4=>0x10001007807c0344be01a15f00d02f806807c03006601801f00b02f80580fc0248fe01245f00922100489fc0244be0121ff0090ef80481fc0240be01203f00900f804806c0208be01044600802f804010801c8be00e457005a3f802d17c0148be00a07f
|5=>0x2022301010080800fe04005f02000781000100548be02345f01163f808a1fc0448fe02245f01122200881fc0440cc021446010a2200841180418f602086601043100821180408be020457010224008111804088002041b0100330080108040020020004
|6=>0x60102fb0001ec40001210005c040008018b1fc0c48be06206603102f818219808c8be04605f02183f810c17c0858be042c0202142f810a0080848fe04245f02122301081fc0840be04200602082f810416c0818be040c5b02060e81030080810be04045f
|7=>0x410017e0000bec0805f
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x6001a0e00000012020000000621040200020002001919000400000727070002002600000000230001020000002c0000040020000002070007020700070202002514191900
|7,0=>0x3299c1b634f9e6919151a0a0dd10045ac02dc0f655c0b1a2a001a2e1c2412050a227712021b1e53293d0a00123e28a3c402023f073b45910013ce190378840600001900c0733e9f0002c8022838028d6a06b902752d072f3904190e061a021fad001a49290005722a070c3c008b8a0210ae920209009d29294b080a0e520000
|7,1=>0x3da8040a1a511a05061900c28f10552a1d5ddd972c0000002fdb2a04de2d113dbb293828e01ba005030000612b2f3a000a0635561379562903510764c386054607901a121a00020f96
|8,0=>0x8ba16655cd5415cc18af915abcc26c354c58c937577bb5938e31b45717bf349b57577057c1cfc958982cccc4c6c9bac9be225e2fd19942df616835678b488bd7c582bcb0185821d15cd9357f4d4436d6c0327dd151c9d9a9513061b4c92f8f7ed15b434e742fb0ac972d616b4fa5e261d861bce1abb258946876617cd45e95ba
|8,1=>0x2f5c86a6a316d19a2cd988c959c9d062878d6d47bdcc57c273bccbcf61c9b1c7715883bf7ab36ecf2f58aaa25fd54160c957358db7a4c9586a6fb4165558bfcf40c7d131ae93a78c7a3346b7d517c155574a58b4008548c9
|9,0=>0xccd1c5d2b2618d89b8bcbcd36158d1d957cf5758da61ca57d1c957c0cc7f82ccd7c76d80d97fbc57617f6158cc5858cfd95758c5d2cf8d8e58d9d7b48dc9b6d97f35505780d2c558818d
|10,0=>0x5757d757c75857c1212121
|11,0=>0x21
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 25 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_222 10 roots_222 ops++addP pm 1 dom_159 9 roots_159 ops++addP pm 2 dom_95 9 roots_95 ops++addP pm 3 dom_221 10 roots_221 ops++addP pm 4 dom_219 10 roots_219 ops++addP pm 5 dom_79 6 roots_79 ops++addP pm 6 dom_215 9 roots_215 ops++addP pm 7 dom_94 8 roots_94 ops++addP pm 8 dom_206 7 roots_206 ops++addP pm 9 dom_75 5 roots_75 ops++addP pm 10 dzo_151_8 6 roots_151 ops++addP pm 11 dom_87 6 roots_87 ops++addP pm 12 dom_151 6 roots_151 ops++addP pm 13 dom_207 8 roots_207 ops++addP pm 14 dom_205 7 roots_205 ops++addP pm 15 dom_143 5 roots_143 ops++addP pm 16 dom_31 5 roots_31 ops++addP pm 17 dom_199 6 roots_199 ops++addP pm 18 dzo_215_8 7 roots_215 ops++addP pm 19 dom_91 7 roots_91 ops++addP pm 20 dzo_214_8 6 roots_214 ops++addP pm 21 dom_211 8 roots_211 ops++addP pm 22 dom_195 5 roots_195 ops++addP pm 23 dom_203 6 roots_203 ops++addP pm 24 dzo_213_8 6 roots_213 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_223 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_221 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_79 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_151_8_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_207 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_143 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_215_8_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_zo_214_8_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_195 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_zo_213_8_148 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_222 10 s (0,roots_222.map (·&&&dom_222)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_223 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_222 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_223 gM v ys):RunD true dom_223 gM v (ori ys):=h
def Z (s:Nat):=barP dom_223 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 12 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 69 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 69 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 201 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 73 128 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 201 → Z 7 i = true := (range_split z7_0 z7_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 216 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 88 128 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 216 → Z 8 i = true := (range_split z8_0 z8_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 74 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 74 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 11 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 11 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_223 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_217_32:=0x303030300000000030303030000000003030303000000000303030300000000
def gzo_217_32:=0x303030300000000030303030000000003030302000000000302030000000000
def gsh_217_32:=0x3030303000000000303030300000000030303020000000003020300
theorem lowS_zo_217_32_81:Lower true dzo_217_32 roots_217 gzo_217_32 6:=lower_iso_b (d1:=dom_217) (r1:=roots_217) (T1:=gsh_217_32) [(dom_217,32)] (by decide +kernel) (lower_slice_b (T:=gsh_217_32) [(0x3000300000000000300030000000000030003000000000003000300,0,8),(0x3030303000000000303030300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_81)
def dzo_170_16:=0x50500000505000000000000000000000505000005050000
def gzo_170_16:=0x50500000505000000000000000000000504000004000000
def gsh_170_16:=0x5050000050500000000000000000000050400000400
theorem lowS_zo_170_16_42:Lower true dzo_170_16 roots_170 gzo_170_16 5:=lower_iso_b (d1:=dom_170) (r1:=roots_170) (T1:=gsh_170_16) [(dom_170,16)] (by decide +kernel) (lower_slice_b (T:=gsh_170_16) [(0x5050000050500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
def dzo_171_16:=0xf0f00000f0f000000000000000000000f0f00000f0f0000
def gzo_171_16:=0xf0f00000f0f000000000000000000000f0e00000e0a0000
def gsh_171_16:=0xf0f00000f0f000000000000000000000f0e00000e0a
theorem lowS_zo_171_16_42:Lower true dzo_171_16 roots_171 gzo_171_16 6:=lower_iso_b (d1:=dom_171) (r1:=roots_171) (T1:=gsh_171_16) [(dom_171,16)] (by decide +kernel) (lower_slice_b (T:=gsh_171_16) [(0xa0a00000a0a000000000000000000000a0a00000a0a,0,1),(0xf0f00000f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
def dzo_235_16:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000
def gzo_235_16:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0e00000e0a0000
def gsh_235_16:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0e00000e0a
theorem lowS_zo_235_16_42:Lower true dzo_235_16 roots_235 gzo_235_16 7:=lower_iso_b (d1:=dom_235) (r1:=roots_235) (T1:=gsh_235_16) [(dom_235,16)] (by decide +kernel) (lower_slice_b (T:=gsh_235_16) [(0xa0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a,0,1),(0xf0f00000f0f000000000000000000000f0f00000f0f0000000000000000,0,64),(0xf0f00000f0f00000f0f00000f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_42)
def dzo_219_32:=0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000
def gzo_219_32:=0xf0f0f0f000000000f0f0f0f000000000f0f0f0e000000000f0e0f0c00000000
def gsh_219_32:=0xf0f0f0f000000000f0f0f0f000000000f0f0f0e000000000f0e0f0c
theorem lowS_zo_219_32_81:Lower true dzo_219_32 roots_219 gzo_219_32 7:=lower_iso_b (d1:=dom_219) (r1:=roots_219) (T1:=gsh_219_32) [(dom_219,32)] (by decide +kernel) (lower_slice_b (T:=gsh_219_32) [(0xc0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c,0,2),(0xf000f00000000000f000f00000000000f000f00000000000f000f00,0,8),(0xf0f0f0f000000000f0f0f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_81)
namespace S_251
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(1,129),(2,10),(2,34),(2,66),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(8,9),(8,10),(8,40),(8,72),(16,17),(16,80),(16,144),(18,19),(18,26),(18,50),(18,82),(18,146),(24,25),(24,26),(24,56),(24,88),(24,152),(32,34),(32,40),(32,160),(33,35),(33,41),(33,49),(33,97),(33,161),(48,49),(48,50),(48,56),(48,112),(48,176),(64,65),(64,66),(64,72),(64,80),(64,192),(96,97),(96,98),(96,104),(96,112),(96,224),(128,129),(128,130),(128,144),(128,160),(128,192),(136,137),(136,138),(136,152),(136,168),(136,200)]
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
|7,0=>0xf736ff3195e3d2ad44f7adecbab9435d5783fff0
|8,0=>0xfdad5e676de4414e0fd1d5ed3cf771bc06eb47c3b20a99daec9aca1931c28da368a4a77dddc7948c76e1d74c797324671ee76fba45cb54560a9535d845fde3c907321992ef7d2ba37233e622bad0bbd2
|9,0=>0xf3498f2bedf1210ebeb7e9f97e7737e1fd1e0d5bde917d4ecfd0ee2ce9cfcaf43c8c8bbfb35be3c8bdd97bbad1b1f52ad892ac742a5cd0a4252a19a39fb648be808536b7ec09751a96a3a26671a650f36429160a7f5e8db59806583994a17f495a446098451a03ff433d2c13993f36461322462fd332d7662d3af2ac9528bfc27531265691bdfb1b3f618ee3175c116d161233810585053b601d48
|10,0=>0xdb635c837bac58c8a8436efcd527d9502c6294df2329a1497e
|11,0=>0xff75e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0000000000000000f0f0a0a0f0f0a0a00000000000000000f0f0a0a0f0f0a0a0000e0e00000e0e00000e0e00000e0e00000e0e00000e0e00000e0e00000e0ee0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e5050e0e05050e0e05050e0e05050e0e05050e0e05050e0e05050e0e05050e0ec0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0cf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f00000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a505000005050000050500000505000005050000050500000505000005050000303030303030303030303030000000003030303030303030303030300000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000
|0,1=>0xf0f0f0f0f0f0f0f000000000f0f00000f0f0f0f0f0f0f0f000000000f0f0000505050505050505050500000505000005050505050505050505000005050000f0f0f0f0f0f0f0f0f0f0c0c0f0f0c0c0f0f0f0f0f0f0f0f0f0f0c0c0f0f0c0c000000000000000030300000303000000000000000000000303000003030000f0f0f0f0f0f0f0f03030000030300000f0f0f0f0f0f0f0f0303000003030000101000001010000010100000101000001010000010100000101000001010000b0b0a0a0b0b0a0a0b0b0a0a0b0b0a0a0b0b0a0a0b0b0a0a0b0b0a0a0b0b0a0af0f0f0f0f0f0f0f0f0f00000f0f00000f0f0f0f0f0f0f0f0f0f00000f0f0000f0f00000f0f00000c0c00000c0c00000f0f00000f0f00000c0c00000c0c0000f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0ce0e00000e0e00000e0e00000e0e00000e0e00000e0e00000e0e00000e0e0000f0f0f0f0f0f0f0f0e0e0e0e0e0e0e0e0f0f0f0f0f0f0f0f0e0e0e0e0e0e0e0ef0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0cf0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f0f0f0f0f0f0f0f0f0000f0f00000f0f00000f0f0000000000000f0f00000f0f00000f0f0000000000000000f0f00000f0f00000f0f0f0f000000000f0f00000f0f00000f0f0f0f0000
|0,2=>0xf0f0c0c0f0f0c0c00000000000000000f0f0c0c0f0f0c0cf0f0f0f0f0f0f0f0f0f0a0a0f0f0a0a0f0f0f0f0f0f0f0f0f0f0a0a0f0f0a0ac0c0c0c0c0c0c0c0f0f0c0c0f0f0c0c0c0c0c0c0c0c0c0c0f0f0c0c0f0f0c0c5050505050505050505050500000000050505050505050505050505000000000000000000000000f0f00000f0f000000000000000000000f0f00000f0f0000303000003030000030300000303000003030000030300000303000003030000505040405050404050504040505040405050404050504040505040405050404303030303030303030300000303000003030303030303030303000003030000f0f0e0e0f0f0e0e0f0f0e0e0f0f0e0e0f0f0e0e0f0f0e0e0f0f0e0e0f0f0e0ef0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a0f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0af0f0f0f0f0f0f0f05050000050500000f0f0f0f0f0f0f0f05050000050500000000000000000000f0f0f0f0f0f000000000000000000000f0f0f0f0f0f0000000000000000000050500000505000000000000000000000505000005050000f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0000f0f00000f0f00000f0f0000000000000f0f00000f0f00000f0f00000000000000000000000000000000f0f00000000000000000000000000000f0f0000
|0,3=>0xd0d0c0c0d0d0c0c0d0d0c0c0d0d0c0c0d0d0c0c0d0d0c0c0d0d0c0c0d0d0c0c3030202030302020303020203030202030302020303020203030202030302025050505050505050404040404040404050505050505050504040404040404040000f0f00000f0f00000c0c00000c0c00000f0f00000f0f00000c0c00000c0c0000000000000000e0e0e0e0e0e0e0e00000000000000000e0e0e0e0e0e0e0ea0a0a0a0a0a0a0a0f0f0a0a0f0f0a0a0a0a0a0a0a0a0a0a0f0f0a0a0f0f0a0a
|_,_=>0
def sP:Nat→Nat
|0=>0x25814c2822002561570c800738614a0c01c61442830802452823480131c614a0c220049114a0c800958554320024615430a0880071853040804c738614a0c01cf18510304014a0d02001ce1852830401c614c08120024528b2001c61440c2040
|1=>0x50428300960614c2a200718530304800718530a0880241c614a0c01c61440c100918530a8c80073c614a0c120024f6052a20052838602001c61442837001d61851030071852837c024614c29e2001dd18510a0c02461442836c024614c299200
|2=>0x918510a0c22001d61852832001cf18528320026718528320024614a0da20024615430a0c80261c614a0c800960614c28320024614a5c32001c614c10300718528308120024614c2a520024614c1022001cf18510a0c04c73c614a0c8007185
|3=>0x9bc614a0c8009185283788009b8614a0c8009b4614a0c8007185283b0800918530a88800718528304800918550a0c80095ab14a0c80093eb14a0c80091852990c8009185283a48009605283088009185283a080121c614a0c800938614a0c8
|4=>0x15410a0c800718530a0c8009605283a880091852836c800960614a88300718510a0c04c71852832001c614a0c2200246171283200246ac530a0c80091852838c800718528384800918510a0dc20025618510320025d18510a0c8009c0614a0c8
|5=>0x3040c800718528380800918528334800918554a0c800918530a08800959814a0c80093d814a0c800958614c0c800719114a0c80093c614428320024617528320024614a0f420024614a0e520024f1852a220024614a0f320024614a0f2200246
|6=>0x28320024614c2832001c614a0c80091852830880091ab14a0c800918510a0c800958614a0c80093c614a0c800960614a0c8009185283a880091852a20c80099c614c28320024614c283688009185283708007185283a8800974614a0c8009185
|7=>0x9185
|_=>0
def sO:Nat→Nat→Nat
|7,0=>0xd1c2c809201e605a00e80218008
|8,0=>0x4b5d249472114843210393ee0f383ae0e38371cd573360c492f5cb672ba0a77281c988242088820207881c5c6a718a05b714a44b7111c3b9
|9,0=>0xc9271b9c4e30b8c0e2fb8bce2eb8b8e2db8b4e2cb8b0e2bb8aca6aa8a8a29a8a4a28a8a0a27999c626989862598949e4a890a23a88c66298886218984220797fe1f787be1e7877e1d7873e1c786fe1b786be1a7867e197863e18785fe17695ba166857a156853654584f25348
|10,0=>0xdd236d7d9635d8d5634d8d1633d8cd632d8
|11,0=>0x37c7
|_,_=>0
def wAt:=mkWire dB 54 252 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 14
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x2485c21184ca210da4633283460f1884a0d18a461028849213c8c60d183ca212484632183ca0d183c72924847181c6492118a4630283460f3084a0d183c9212834a212484f23183460d1caca2124852471c60719248472b2484f231834a0d183c72b08d4632183ca0d288460f1cac921
|1=>0x1840a212484a0d288460f1cac9212834221183c60f2834a21248460d288460d1ca49211034a2124843211884a0d1caca0d248460f2834921488c719248472b2884921283468b0c8460d1cac9210c8460d188471b1c68921248461328846292884921808471a248580f1884a0d1844a21
|2=>0x308ca0d188ca0d1a2c3211c6c921184ca2118a4a211844a21ac34623588c629603c6211a24321aca46231c3c92128343211cac9212a2432118a462318346230ea462b583c629183c62160ac6211c649213c8c60d183ca2118a4921183492118c4a0d18cca0d3084a0d1c349211884a0d
|3=>0x2884629183462118ac32118c4a0d18cca0d184ca2118ac9211844a212834a211c6892118c8a0d18c0a0d183ca0d18a4621183462118a4a0d1c609211834a21282460f3cac60d088460f1834321103ca211848a211034a212834921188462ba88462b188432128849211ca4921183c921
|4=>0x2834921183c623
|_=>0
def oO:Nat→Nat→Nat
|7,0=>0xd205cc2680f405a020c088004
|8,0=>0x3d99e0cea67233799b0cd26663319980cba65a32b9950ca264e3259920c8a64231f98f0c7263631998c0c5a62a3139890c4261e3
|9,0=>0x1f04f627a13c89e04ee27613a89d04e627213889c04de26e13689b04d626a13489a04ce26613289904c626213089804be25e12e89704b625a12c89604ae25612a89504a6252128894049e24e126893049624a124892048e2461228910486242120890047e2
|10,0=>0x2063021808c005fe2fe17e8bf05f62fa1
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 13
def pmP:Nat→Nat
|0=>0x100ff80611ec0222f60109eb0080fd80227ec00808000307600181000085980040480013fb0007bd8003dbc001df6000d7f0006bd80033ec0012f600087b0003bd8001bec000af60003db00013d80007ec0002f60000ff00003d800010800000c000000
|1=>0xc00fd86005ec3000f610817b0804bd84007ec1a23f60d117b0604bd83007ec1227fe0913fb0488fd82445ec1203f609017b0446bd82205ec1042fe08177b0406bd82007ec0c1df6040efb0206a801033ec0809f60213ff01077f80833fc040efe02027f
|2=>0x2400bf90905808480f64224fb21113790887ec80a1e040287f20103f90007fc712ef638177b190bbd8a85dfc542afe298d7b1446bd8a215ec502ef628157b1402bd8a006ec5002f620857b100abd87607ec3913f61c81fb0e40bd86227ec3102f61803fb
|3=>0x14004ff6408bf94005fc944af648357f
|_=>0
def pmB:Nat→Nat→Nat
|7,0=>0x2464b840404f15
|8,0=>0x4659d936b654c5b0431db0a61b2d494b13da620e3792c90abbd7e527
|9,0=>0x281a0c7ea91acbc30d5caa7da69218bc72296284501d44417448e1e270949b50ecc831a3dc4d5d44c706e7437f8190ba2ce8065192106
|10,0=>0x6030a143cb60f8325
|11,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 7 (j%128);fld (pmP (k/32)) 25 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_243 10 roots_243 ops++addP pm 1 dom_219 10 roots_219 ops++addP pm 2 dzo_217_32 6 roots_217 ops++addP pm 3 dom_123 10 roots_123 ops++addP pm 4 dom_187 9 roots_187 ops++addP pm 5 dom_250 9 roots_250 ops++addP pm 6 dom_249 9 roots_249 ops++addP pm 7 dom_170 5 roots_170 ops++addP pm 8 dom_235 8 roots_235 ops++addP pm 9 dom_185 6 roots_185 ops++addP pm 10 dzo_170_16 5 roots_170 ops++addP pm 11 dom_248 6 roots_248 ops++addP pm 12 dzo_171_16 6 roots_171 ops++addP pm 13 dom_155 6 roots_155 ops++addP pm 14 dom_217 8 roots_217 ops++addP pm 15 dzo_234_16 6 roots_234 ops++addP pm 16 dom_234 6 roots_234 ops++addP pm 17 dom_153 5 roots_153 ops++addP pm 18 dom_186 7 roots_186 ops++addP pm 19 dzo_235_16 7 roots_235 ops++addP pm 20 dom_171 6 roots_171 ops++addP pm 21 dom_233 6 roots_233 ops++addP pm 22 dzo_219_32 7 roots_219 ops++addP pm 23 dom_203 6 roots_203 ops++addP pm 24 dom_218 7 roots_218 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_251 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_217_32_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_170_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_171_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_234_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_153 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_zo_235_16_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_zo_219_32_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_218 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_243 10 s (0,roots_243.map (·&&&dom_243)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_251 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_243 h
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
namespace S_253
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(1,129),(4,20),(4,36),(4,68),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(8,9),(8,40),(8,72),(12,13),(12,28),(12,44),(12,76),(12,140),(16,17),(16,20),(16,80),(16,144),(24,25),(24,28),(24,56),(24,88),(24,152),(32,36),(32,40),(32,160),(33,37),(33,41),(33,49),(33,97),(33,161),(48,49),(48,52),(48,56),(48,112),(48,176),(64,65),(64,68),(64,72),(64,80),(64,192),(96,97),(96,100),(96,104),(96,112),(96,224),(128,129),(128,132),(128,144),(128,160),(128,192),(136,137),(136,140),(136,152),(136,168),(136,200)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffffffffffffff
def xsM:=roots_253.map (·&&&dom_253)
def gM:=goal_253&&&dom_253
def NN:Nat→Nat
|9=>6
|10=>2
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|9,0=>0xaefab75c1c579084de493a2d40629b
|10,0=>0x460ee0a7a6
|11,0=>0x1e31b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x3232000032320000323200003232000032320000323200003232000032324444404044444040444440404444404044444040444440404444404044444043333323233333232333332323333323233333232333332323333323233333232ccccc0c0ccccc0c0ccccc0c0ccccc0c0ccccc0c0ccccc0c0ccccc0c0ccccc0c2222222222222222222222222222222222222222222222222222222222222222cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000003333222233332222333322223333222233332222333322223333222233332222cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0003300330033003300330033003300330033003300330033003300330033003300c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8cb030303030303030303030303030303030303030303030303030303030303030cccccccccccccccc0000000000000000cccccccccccccccc0000000000000003333333333333333333333333333333300000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x7542810754328107954281075428c107a543281075428b107a5428107a954281076543210
|_=>0
def sO:Nat→Nat→Nat
|9,0=>0x15421933046044808
|10,0=>0x1d4328
|11,0=>0x427
|_,_=>0
def wAt:=mkWire dB 13 254 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x28549538a1534a198d49985499854982561
|_=>0
def oO:Nat→Nat→Nat
|9,0=>0xa28262422202
|10,0=>0xd1c1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0xffe7f7fd7f1fc00
|_=>0
def pmB:Nat→Nat→Nat
|9,0=>0x1596b
|10,0=>0x14
|11,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 10 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_245 10 roots_245 ops++addP pm 1 dom_189 10 roots_189 ops++addP pm 2 dom_125 10 roots_125 ops++addP pm 3 dom_221 10 roots_221 ops++addP pm 4 dom_252 9 roots_252 ops++addP pm 5 dom_249 9 roots_249 ops++addP pm 6 dom_237 9 roots_237 ops++addP pm 7 dom_236 6 roots_236 ops++addP pm 8 dom_248 6 roots_248 ops++addP pm 9 dom_233 6 roots_233 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_253 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_189 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_221 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_237 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_233 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_245 10 s (0,roots_245.map (·&&&dom_245)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_253 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_245 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_253==dom_253)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_253 gM v ys):RunD true dom_253 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_253 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 6 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 6 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 2 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 2 0 = true)
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
def isoMvS_191:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_191:Lower true dom_191 roots_191 goal_191 12:=lower_iso_b isoMvS_191 (by decide +kernel) lowS_127
def isoMvS_247:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_247:Lower true dom_247 roots_247 goal_247 12:=lower_iso_b isoMvS_247 (by decide +kernel) lowS_223
def isoMvS_254:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_254:Lower true dom_254 roots_254 goal_254 12:=lower_iso_b isoMvS_254 (by decide +kernel) lowS_251
namespace S_255
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(1,129),(2,10),(2,34),(2,66),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(4,20),(4,36),(4,68),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(6,14),(6,22),(6,38),(6,70),(6,134),(7,15),(7,23),(7,39),(7,71),(7,135),(8,9),(8,10),(8,40),(8,72),(12,13),(12,14),(12,28),(12,44),(12,76),(12,140),(16,17),(16,20),(16,80),(16,144),(18,19),(18,22),(18,26),(18,50),(18,82),(18,146),(24,25),(24,26),(24,28),(24,56),(24,88),(24,152),(32,34),(32,36),(32,40),(32,160),(33,35),(33,37),(33,41),(33,49),(33,97),(33,161),(48,49),(48,50),(48,52),(48,56),(48,112),(48,176),(64,65),(64,66),(64,68),(64,72),(64,80),(64,192),(96,97),(96,98),(96,100),(96,104),(96,112),(96,224),(128,129),(128,130),(128,132),(128,144),(128,160),(128,192),(136,137),(136,138),(136,140),(136,152),(136,168),(136,200)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffffffffffffffffff
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
addP pm 0 dom_254 12 roots_254 ops++addP pm 1 dom_191 12 roots_191 ops++addP pm 2 dom_253 12 roots_253 ops++addP pm 3 dom_251 12 roots_251 ops++addP pm 4 dom_247 12 roots_247 ops++addP pm 5 dom_127 12 roots_127 ops++addP pm 6 dom_223 12 roots_223 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_255 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_191 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_247 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_127 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_223 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_254 12 s (0,roots_254.map (·&&&dom_254)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_254 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
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
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [0, 2] }, { op := GateOp.or, inputs := [1, 0] }, { op := GateOp.or, inputs := [6, 7] }, { op := GateOp.or, inputs := [8, 10] }, { op := GateOp.or, inputs := [5, 6] }, { op := GateOp.or, inputs := [2, 1] }, { op := GateOp.or, inputs := [3, 7] }, { op := GateOp.or, inputs := [12, 9] }, { op := GateOp.and, inputs := [11, 4] }, { op := GateOp.and, inputs := [13, 12] }, { op := GateOp.and, inputs := [14, 15] }, { op := GateOp.and, inputs := [10, 8] }, { op := GateOp.or, inputs := [16, 17] }, { op := GateOp.or, inputs := [20, 18] }, { op := GateOp.or, inputs := [21, 19] }]

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 22⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
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

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_52780_aux

theorem PEqualNP.Outside.L_meta_52780 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_52780_aux.main
