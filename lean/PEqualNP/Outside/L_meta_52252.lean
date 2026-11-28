import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_52252_aux
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

def dom_45 : Nat := 0x333300003333
def goal_45 : Nat := 0xfafafafaaa00aa00fafafafaaa00aa00fafafafaaa00aa00fafafafaaa00aa00
def roots_45 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_46 : Nat := 0x555500005555
def goal_46 : Nat := 0xfcfcfcfccc00cc00fcfcfcfccc00cc00fcfcfcfccc00cc00fcfcfcfccc00cc00
def roots_46 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_47 : Nat := 0xffff0000ffff
def goal_47 : Nat := 0xfefefefeee00ee00fefefefeee00ee00fefefefeee00ee00fefefefeee00ee00
def roots_47 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_54 : Nat := 0x55005500550055
def goal_54 : Nat := 0xfcfcfcfcf0f00000fcfcfcfcf0f00000fcfcfcfcf0f00000fcfcfcfcf0f00000
def roots_54 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xfefefefefafa0000fefefefefafa0000fefefefefafa0000fefefefefafa0000
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_73 : Nat := 0x3030000000000000303
def goal_73 : Nat := 0xffaaffaaffaaffaaaa00aa00aa00aa00ffaaffaaffaaffaaaa00aa00aa00aa00
def roots_73 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_74 : Nat := 0x5050000000000000505
def goal_74 : Nat := 0xffccffccffccffcccc00cc00cc00cc00ffccffccffccffcccc00cc00cc00cc00
def roots_74 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_75 : Nat := 0xf0f0000000000000f0f
def goal_75 : Nat := 0xffeeffeeffeeffeeee00ee00ee00ee00ffeeffeeffeeffeeee00ee00ee00ee00
def roots_75 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_78 : Nat := 0x55550000000000005555
def goal_78 : Nat := 0xffccffccffccffcccc00cc00cc00cc00ffccffccffccffcccc00cc00cc00cc00
def roots_78 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_79 : Nat := 0xffff000000000000ffff
def goal_79 : Nat := 0xffeeffeeffeeffeeee00ee00ee00ee00ffeeffeeffeeffeeee00ee00ee00ee00
def roots_79 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_83 : Nat := 0xf000f00000000000f000f
def goal_83 : Nat := 0xeeeeeeeeeeeeeeeeaaaa0000aaaa0000eeeeeeeeeeeeeeeeaaaa0000aaaa0000
def roots_83 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_85 : Nat := 0x3300330000000000330033
def goal_85 : Nat := 0xfafaaaaafafaaaaafafa0000fafa0000fafaaaaafafaaaaafafa0000fafa0000
def roots_85 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_87 : Nat := 0xff00ff0000000000ff00ff
def goal_87 : Nat := 0xfefeeeeefefeeeeefafa0000fafa0000fefeeeeefefeeeeefafa0000fafa0000
def roots_87 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_89 : Nat := 0x30303030000000003030303
def goal_89 : Nat := 0xffaaffaaffaaffaaaaaaaa00aaaaaa00ffaaffaaffaaffaaaaaaaa00aaaaaa00
def roots_89 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_90 : Nat := 0x50505050000000005050505
def goal_90 : Nat := 0xffccffccffccffcccc00cc00cc00cc00ffccffccffccffcccc00cc00cc00cc00
def roots_90 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f
def goal_91 : Nat := 0xffeeffeeffeeffeeeeaaee00eeaaee00ffeeffeeffeeffeeeeaaee00eeaaee00
def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_93 : Nat := 0x333333330000000033333333
def goal_93 : Nat := 0xfffaffaafffaffaafafaaa00fafaaa00fffaffaafffaffaafafaaa00fafaaa00
def roots_93 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_94 : Nat := 0x555555550000000055555555
def goal_94 : Nat := 0xfffcffccfffcffccfcf0cc00fcf0cc00fffcffccfffcffccfcf0cc00fcf0cc00
def roots_94 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_95 : Nat := 0xffffffff00000000ffffffff
def goal_95 : Nat := 0xfffeffeefffeffeefefaee00fefaee00fffeffeefffeffeefefaee00fefaee00
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

def dom_101 : Nat := 0x33000000330000003300000033
def goal_101 : Nat := 0xffffffffaaaaaaaafafafafa00000000ffffffffaaaaaaaafafafafa00000000
def roots_101 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_102 : Nat := 0x55000000550000005500000055
def goal_102 : Nat := 0xffffffffccccccccfcfcfcfc00000000ffffffffccccccccfcfcfcfc00000000
def roots_102 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_103 : Nat := 0xff000000ff000000ff000000ff
def goal_103 : Nat := 0xffffffffeeeeeeeefefefefe00000000ffffffffeeeeeeeefefefefe00000000
def roots_103 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_105 : Nat := 0x303000003030000030300000303
def goal_105 : Nat := 0xffffffffffaaffaaaaaaaaaaaa00aa00ffffffffffaaffaaaaaaaaaaaa00aa00
def roots_105 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_106 : Nat := 0x505000005050000050500000505
def goal_106 : Nat := 0xffffffffffccffcccccccccccc00cc00ffffffffffccffcccccccccccc00cc00
def roots_106 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffffffffffeeffeeeeeeeeeeee00ee00ffffffffffeeffeeeeeeeeeeee00ee00
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_108 : Nat := 0x1111000011110000111100001111
def goal_108 : Nat := 0xffffffffff00ff00f0f0f0f000000000ffffffffff00ff00f0f0f0f000000000
def roots_108 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_109 : Nat := 0x3333000033330000333300003333
def goal_109 : Nat := 0xffffffffffaaffaafafafafaaa00aa00ffffffffffaaffaafafafafaaa00aa00
def roots_109 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_110 : Nat := 0x5555000055550000555500005555
def goal_110 : Nat := 0xffffffffffccffccfcfcfcfccc00cc00ffffffffffccffccfcfcfcfccc00cc00
def roots_110 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xffffffffffeeffeefefefefeee00ee00ffffffffffeeffeefefefefeee00ee00
def roots_111 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_113 : Nat := 0x30003000300030003000300030003
def goal_113 : Nat := 0xffffffffaaaaaaaaaaaaaaaaaaaa0000ffffffffaaaaaaaaaaaaaaaaaaaa0000
def roots_113 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def goal_115 : Nat := 0xffffffffeeeeeeeeeeeeeeeeaaaa0000ffffffffeeeeeeeeeeeeeeeeaaaa0000
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_117 : Nat := 0x330033003300330033003300330033
def goal_117 : Nat := 0xfffffffffafaaaaafafafafafafa0000fffffffffafaaaaafafafafafafa0000
def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xfffffffffcfcccccfcfcfcfcf0f00000fffffffffcfcccccfcfcfcfcf0f00000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xfffffffffefeeeeefefefefefafa0000fffffffffefeeeeefefefefefafa0000
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xfffffffffffaffaafafafafafafaaa00fffffffffffaffaafafafafafafaaa00
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xfffffffffffeffeefefefefefefaee00fffffffffffeffeefefefefefefaee00
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

def dom_147 : Nat := 0xf000f000000000000000000000000000f000f
def goal_147 : Nat := 0xffffccccffffccccffffccccffffccccaaaa0000aaaa0000aaaa0000aaaa0000
def roots_147 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

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

def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def goal_155 : Nat := 0xffffffccffffffccffffffccffffffcceeaaee00eeaaee00eeaaee00eeaaee00
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

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
def goal_163 : Nat := 0xeeeeeeeecccccccceeeeeeeecccccccceeeeeeee00000000eeeeeeee00000000
def roots_163 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_165 : Nat := 0x330000003300000000000000000000003300000033
def goal_165 : Nat := 0xfafafafaf0f0f0f0fafafafaf0f0f0f0fafafafa00000000fafafafa00000000
def roots_165 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_167 : Nat := 0xff000000ff0000000000000000000000ff000000ff
def goal_167 : Nat := 0xfefefefefcfcfcfcfefefefefcfcfcfcfefefefe00000000fefefefe00000000
def roots_167 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_169 : Nat := 0x3030000030300000000000000000000030300000303
def goal_169 : Nat := 0xffaaffaaff00ff00ffaaffaaff00ff00aaaaaaaaaa00aa00aaaaaaaaaa00aa00
def roots_169 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_170 : Nat := 0x5050000050500000000000000000000050500000505
def goal_170 : Nat := 0xffccffccffccffccffccffccffccffcccccccccccc00cc00cccccccccc00cc00
def roots_170 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_171 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
def goal_171 : Nat := 0xffeeffeeffccffccffeeffeeffccffcceeeeeeeeee00ee00eeeeeeeeee00ee00
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_172 : Nat := 0x11110000111100000000000000000000111100001111
def goal_172 : Nat := 0xfff0fff0fff0fff0fff0fff0fff0fff0f0f0f0f000000000f0f0f0f000000000
def roots_172 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_173 : Nat := 0x33330000333300000000000000000000333300003333
def goal_173 : Nat := 0xfffafffafff0fff0fffafffafff0fff0fafafafaaa00aa00fafafafaaa00aa00
def roots_173 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_174 : Nat := 0x55550000555500000000000000000000555500005555
def goal_174 : Nat := 0xfffcfffcfffcfffcfffcfffcfffcfffcfcfcfcfccc00cc00fcfcfcfccc00cc00
def roots_174 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_175 : Nat := 0xffff0000ffff00000000000000000000ffff0000ffff
def goal_175 : Nat := 0xfffefffefffcfffcfffefffefffcfffcfefefefeee00ee00fefefefeee00ee00
def roots_175 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_180 : Nat := 0x1100110011001100000000000000000011001100110011
def goal_180 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0f0f0f0f0f0f00000f0f0f0f0f0f00000
def roots_180 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_181 : Nat := 0x3300330033003300000000000000000033003300330033
def goal_181 : Nat := 0xfffffafafffff0f0fffffafafffff0f0fafafafafafa0000fafafafafafa0000
def roots_181 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_182 : Nat := 0x5500550055005500000000000000000055005500550055
def goal_182 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfcfcfcfcfcf0f00000fcfcfcfcf0f00000
def roots_182 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_183 : Nat := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
def goal_183 : Nat := 0xfffffefefffffcfcfffffefefffffcfcfefefefefafa0000fefefefefafa0000
def roots_183 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffeeffffffccffffffeeffffffcceeeeeeeeeeaaee00eeeeeeeeeeaaee00
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_189 : Nat := 0x333333333333333300000000000000003333333333333333
def goal_189 : Nat := 0xfffffffafffffff0fffffffafffffff0fafafafafafaaa00fafafafafafaaa00
def roots_189 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_190 : Nat := 0x555555555555555500000000000000005555555555555555
def goal_190 : Nat := 0xfffffffcfffffffcfffffffcfffffffcfcfcfcfcfcf0cc00fcfcfcfcfcf0cc00
def roots_190 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xfffffffefffffffcfffffffefffffffcfefefefefefaee00fefefefefefaee00
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_195 : Nat := 0xf000000000000000f000000000000000f000000000000000f
def goal_195 : Nat := 0xeeeeeeeeeeeeeeeecccccccccccccccceeeeeeeeeeeeeeee0000000000000000
def roots_195 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_198 : Nat := 0x55000000000000005500000000000000550000000000000055
def goal_198 : Nat := 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfccccccccccccccccc0000000000000000
def roots_198 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_199 : Nat := 0xff00000000000000ff00000000000000ff00000000000000ff
def goal_199 : Nat := 0xfefefefefefefefefcfcfcfcfcfcfcfceeeeeeeeeeeeeeee0000000000000000
def roots_199 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_201 : Nat := 0x303000000000000030300000000000003030000000000000303
def goal_201 : Nat := 0xffaaffaaffaaffaaff00ff00ff00ff00ffaaffaaffaaffaaaa00aa00aa00aa00
def roots_201 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_202 : Nat := 0x505000000000000050500000000000005050000000000000505
def goal_202 : Nat := 0xffccffccffccffccffccffccffccffccffccffccffccffcccc00cc00cc00cc00
def roots_202 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffeeffeeffeeffeeffccffccffccffccffeeffeeffeeffeeee00ee00ee00ee00
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_204 : Nat := 0x1111000000000000111100000000000011110000000000001111
def goal_204 : Nat := 0xfff0fff0fff0fff0fff0fff0fff0fff0ff00ff00ff00ff000000000000000000
def roots_204 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_205 : Nat := 0x3333000000000000333300000000000033330000000000003333
def goal_205 : Nat := 0xfffafffafffafffafff0fff0fff0fff0ffaaffaaffaaffaaaa00aa00aa00aa00
def roots_205 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_206 : Nat := 0x5555000000000000555500000000000055550000000000005555
def goal_206 : Nat := 0xfffcfffcfffcfffcfffcfffcfffcfffcffccffccffccffcccc00cc00cc00cc00
def roots_206 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_207 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def goal_207 : Nat := 0xfffefffefffefffefffcfffcfffcfffcffeeffeeffeeffeeee00ee00ee00ee00
def roots_207 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_209 : Nat := 0x30003000000000003000300000000000300030000000000030003
def goal_209 : Nat := 0xffffaaaaffffaaaaffff0000ffff0000aaaaaaaaaaaaaaaaaaaa0000aaaa0000
def roots_209 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_210 : Nat := 0x50005000000000005000500000000000500050000000000050005
def goal_210 : Nat := 0xffffccccffffccccffffccccffffcccccccccccccccccccc0000000000000000
def roots_210 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffeeeeffffeeeeffffccccffffcccceeeeeeeeeeeeeeeeaaaa0000aaaa0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_213 : Nat := 0x330033000000000033003300000000003300330000000000330033
def goal_213 : Nat := 0xfffffafafffffafafffff0f0fffff0f0fafaaaaafafaaaaafafa0000fafa0000
def roots_213 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfcfcfcccccfcfcccccf0f00000f0f00000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xfffffefefffffefefffffcfcfffffcfcfefeeeeefefeeeeefafa0000fafa0000
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_216 : Nat := 0x1010101000000000101010100000000010101010000000001010101
def goal_216 : Nat := 0xffffff00ffffff00ffffff00ffffff00ff00ff00ff00ff000000000000000000
def roots_216 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_217 : Nat := 0x3030303000000000303030300000000030303030000000003030303
def goal_217 : Nat := 0xffffffaaffffffaaffffff00ffffff00ffaaffaaffaaffaaaaaaaa00aaaaaa00
def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def goal_218 : Nat := 0xffffffccffffffccffffffccffffffccffccffccffccffcccc00cc00cc00cc00
def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffffeeffffffeeffffffccffffffccffeeffeeffeeffeeeeaaee00eeaaee00
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_220 : Nat := 0x11111111000000001111111100000000111111110000000011111111
def goal_220 : Nat := 0xfffffff0fffffff0fffffff0fffffff0fff0ff00fff0ff00f0f00000f0f00000
def roots_220 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def goal_221 : Nat := 0xfffffffafffffffafffffff0fffffff0fffaffaafffaffaafafaaa00fafaaa00
def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xfffffffcfffffffcfffffffcfffffffcfffcffccfffcffccfcf0cc00fcf0cc00
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffefffffffefffffffcfffffffcfffeffeefffeffeefefaee00fefaee00
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def goal_227 : Nat := 0xffffffffeeeeeeeeeeeeeeeeccccccccffffffffeeeeeeeeeeeeeeee00000000
def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_228 : Nat := 0x1100000011000000110000001100000011000000110000001100000011
def goal_228 : Nat := 0xfffffffff0f0f0f0f0f0f0f0f0f0f0f0ffffffff00000000f0f0f0f000000000
def roots_228 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_229 : Nat := 0x3300000033000000330000003300000033000000330000003300000033
def goal_229 : Nat := 0xfffffffffafafafafafafafaf0f0f0f0ffffffffaaaaaaaafafafafa00000000
def roots_229 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def goal_230 : Nat := 0xfffffffffcfcfcfcfcfcfcfcfcfcfcfcffffffffccccccccfcfcfcfc00000000
def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def goal_231 : Nat := 0xfffffffffefefefefefefefefcfcfcfcffffffffeeeeeeeefefefefe00000000
def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_232 : Nat := 0x10100000101000001010000010100000101000001010000010100000101
def goal_232 : Nat := 0xffffffffff00ff00ff00ff00ff00ff00ffffffffff00ff000000000000000000
def roots_232 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffaaffaaffaaffaaff00ff00ffffffffffaaffaaaaaaaaaaaa00aa00
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffccffccffccffccffccffccffffffffffccffcccccccccccc00cc00
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffeeffeeffeeffeeffccffccffffffffffeeffeeeeeeeeeeee00ee00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_236 : Nat := 0x111100001111000011110000111100001111000011110000111100001111
def goal_236 : Nat := 0xfffffffffff0fff0fff0fff0fff0fff0ffffffffff00ff00f0f0f0f000000000
def roots_236 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xfffffffffffafffafffafffafff0fff0ffffffffffaaffaafafafafaaa00aa00
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_238 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def goal_238 : Nat := 0xfffffffffffcfffcfffcfffcfffcfffcffffffffffccffccfcfcfcfccc00cc00
def roots_238 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffefffefffefffefffcfffcffffffffffeeffeefefefefeee00ee00
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffffeeeeffffeeeeffffccccffffffffeeeeeeeeeeeeeeeeaaaa0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_244 : Nat := 0x11001100110011001100110011001100110011001100110011001100110011
def goal_244 : Nat := 0xfffffffffffff0f0fffff0f0fffff0f0fffffffff0f00000f0f0f0f0f0f00000
def roots_244 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_245 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
def goal_245 : Nat := 0xfffffffffffffafafffffafafffff0f0fffffffffafaaaaafafafafafafa0000
def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffffffcfcfffffcfcfffffcfcfffffffffcfcccccfcfcfcfcf0f00000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffefefffffefefffffcfcfffffffffefeeeeefefefefefafa0000
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffeeffffffeeffffffccffffffffffeeffeeeeeeeeeeeeaaee00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffafffffffafffffff0fffffffffffaffaafafafafafafaaa00
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffcfffffffcfffffffcfffffffffffcffccfcfcfcfcfcf0cc00
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffefffffffefffffffcfffffffffffeffeefefefefefefaee00
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
def isoMvS_74:List (Nat×Nat):=[(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_74:Lower true dom_74 roots_74 goal_74 4:=lower_iso_b isoMvS_74 (by decide +kernel) lowS_73
def isoMvS_97:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_97:Lower true dom_97 roots_97 goal_97 4:=lower_iso_b isoMvS_97 (by decide +kernel) lowS_73
def isoMvS_98:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_98:Lower true dom_98 roots_98 goal_98 4:=lower_iso_b isoMvS_98 (by decide +kernel) lowS_73
def isoMvS_138:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_138:Lower true dom_138 roots_138 goal_138 4:=lower_iso_b isoMvS_138 (by decide +kernel) lowS_73
def isoMvS_148:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_148:Lower true dom_148 roots_148 goal_148 4:=lower_iso_b isoMvS_148 (by decide +kernel) lowS_73
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
theorem lowS_75:Lower true dom_75 roots_75 goal_75 5:=lower_slice_b [(0xa0a0000000000000a0a,8,9)] (by decide +kernel) lowS_74
theorem lowS_89:Lower true dom_89 roots_89 goal_89 5:=lower_slice_b [(0x30300000000000003030000,1,17)] (by decide +kernel) lowS_73
def isoMvS_29:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_29:Lower true dom_29 roots_29 goal_29 4:=lower_iso_b isoMvS_29 (by decide +kernel) lowS_27
def isoMvS_45:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_45:Lower true dom_45 roots_45 goal_45 4:=lower_iso_b isoMvS_45 (by decide +kernel) lowS_27
def isoMvS_46:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_46:Lower true dom_46 roots_46 goal_46 4:=lower_iso_b isoMvS_46 (by decide +kernel) lowS_27
def isoMvS_54:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_54:Lower true dom_54 roots_54 goal_54 4:=lower_iso_b isoMvS_54 (by decide +kernel) lowS_27
def isoMvS_83:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_83:Lower true dom_83 roots_83 goal_83 4:=lower_iso_b isoMvS_83 (by decide +kernel) lowS_27
def isoMvS_85:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_85:Lower true dom_85 roots_85 goal_85 4:=lower_iso_b isoMvS_85 (by decide +kernel) lowS_27
def isoMvS_99:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_99:Lower true dom_99 roots_99 goal_99 5:=lower_iso_b isoMvS_99 (by decide +kernel) lowS_75
def isoMvS_101:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_101:Lower true dom_101 roots_101 goal_101 5:=lower_iso_b isoMvS_101 (by decide +kernel) lowS_89
def isoMvS_102:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_102:Lower true dom_102 roots_102 goal_102 5:=lower_iso_b isoMvS_102 (by decide +kernel) lowS_89
def isoMvS_105:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_105:Lower true dom_105 roots_105 goal_105 5:=lower_iso_b isoMvS_105 (by decide +kernel) lowS_75
def isoMvS_106:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_106:Lower true dom_106 roots_106 goal_106 5:=lower_iso_b isoMvS_106 (by decide +kernel) lowS_75
def isoMvS_108:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_108:Lower true dom_108 roots_108 goal_108 4:=lower_iso_b isoMvS_108 (by decide +kernel) lowS_27
def isoMvS_113:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_113:Lower true dom_113 roots_113 goal_113 5:=lower_iso_b isoMvS_113 (by decide +kernel) lowS_89
def isoMvS_139:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_139:Lower true dom_139 roots_139 goal_139 5:=lower_iso_b isoMvS_139 (by decide +kernel) lowS_89
def isoMvS_141:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_141:Lower true dom_141 roots_141 goal_141 4:=lower_iso_b isoMvS_141 (by decide +kernel) lowS_27
def isoMvS_142:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_142:Lower true dom_142 roots_142 goal_142 5:=lower_iso_b isoMvS_142 (by decide +kernel) lowS_89
def isoMvS_147:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_147:Lower true dom_147 roots_147 goal_147 4:=lower_iso_b isoMvS_147 (by decide +kernel) lowS_27
def isoMvS_149:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_149:Lower true dom_149 roots_149 goal_149 5:=lower_iso_b isoMvS_149 (by decide +kernel) lowS_89
def isoMvS_150:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_150:Lower true dom_150 roots_150 goal_150 5:=lower_iso_b isoMvS_150 (by decide +kernel) lowS_89
def isoMvS_154:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_154:Lower true dom_154 roots_154 goal_154 5:=lower_iso_b isoMvS_154 (by decide +kernel) lowS_89
def isoMvS_156:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_156:Lower true dom_156 roots_156 goal_156 5:=lower_iso_b isoMvS_156 (by decide +kernel) lowS_89
def isoMvS_163:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_163:Lower true dom_163 roots_163 goal_163 4:=lower_iso_b isoMvS_163 (by decide +kernel) lowS_27
def isoMvS_165:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_165:Lower true dom_165 roots_165 goal_165 4:=lower_iso_b isoMvS_165 (by decide +kernel) lowS_27
def isoMvS_169:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_169:Lower true dom_169 roots_169 goal_169 4:=lower_iso_b isoMvS_169 (by decide +kernel) lowS_27
def isoMvS_170:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_170:Lower true dom_170 roots_170 goal_170 5:=lower_iso_b isoMvS_170 (by decide +kernel) lowS_89
def isoMvS_172:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_172:Lower true dom_172 roots_172 goal_172 4:=lower_iso_b isoMvS_172 (by decide +kernel) lowS_27
def isoMvS_180:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_180:Lower true dom_180 roots_180 goal_180 5:=lower_iso_b isoMvS_180 (by decide +kernel) lowS_89
def isoMvS_195:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_195:Lower true dom_195 roots_195 goal_195 4:=lower_iso_b isoMvS_195 (by decide +kernel) lowS_27
def isoMvS_198:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_198:Lower true dom_198 roots_198 goal_198 4:=lower_iso_b isoMvS_198 (by decide +kernel) lowS_27
def isoMvS_201:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_201:Lower true dom_201 roots_201 goal_201 5:=lower_iso_b isoMvS_201 (by decide +kernel) lowS_89
def isoMvS_202:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_202:Lower true dom_202 roots_202 goal_202 5:=lower_iso_b isoMvS_202 (by decide +kernel) lowS_75
def isoMvS_204:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_204:Lower true dom_204 roots_204 goal_204 4:=lower_iso_b isoMvS_204 (by decide +kernel) lowS_27
def isoMvS_209:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_209:Lower true dom_209 roots_209 goal_209 4:=lower_iso_b isoMvS_209 (by decide +kernel) lowS_27
def isoMvS_210:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_210:Lower true dom_210 roots_210 goal_210 4:=lower_iso_b isoMvS_210 (by decide +kernel) lowS_27
def isoMvS_216:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_216:Lower true dom_216 roots_216 goal_216 4:=lower_iso_b isoMvS_216 (by decide +kernel) lowS_27
def isoMvS_228:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_228:Lower true dom_228 roots_228 goal_228 4:=lower_iso_b isoMvS_228 (by decide +kernel) lowS_27
def isoMvS_232:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_232:Lower true dom_232 roots_232 goal_232 4:=lower_iso_b isoMvS_232 (by decide +kernel) lowS_27
theorem lowS_31:Lower true dom_31 roots_31 goal_31 5:=lower_slice_b [(0xcccccccc,8,10)] (by decide +kernel) lowS_29
theorem lowS_47:Lower true dom_47 roots_47 goal_47 5:=lower_slice_b [(0xaaaa0000aaaa,8,9)] (by decide +kernel) lowS_46
def dzo_75_16:=0xf0f0000000000000f0f0000
def gzo_75_16:=0xf0e0000000000000e0a0000
def gsh_75_16:=0xf0e0000000000000e0a
theorem lowS_zo_75_16_74:Lower true dzo_75_16 roots_75 gzo_75_16 5:=lower_iso_b (d1:=dom_75) (r1:=roots_75) (T1:=gsh_75_16) [(dom_75,16)] (by decide +kernel) (lower_slice_b (T:=gsh_75_16) [(0xa0a0000000000000a0a,0,1)] (by decide +kernel) lowS_74)
namespace S_91
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(2,10),(2,66),(3,11),(3,19),(3,67),(8,9),(8,10),(8,72),(16,17),(18,19),(18,26),(18,82),(24,25),(24,26),(24,88),(64,65),(64,66),(64,72),(80,81),(80,82),(80,88)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_91.map (·&&&dom_91)
def gM:=goal_91&&&dom_91
def NN:Nat→Nat
|4=>1
|5=>1
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x8a3c4
|5,0=>0x88421
|6,0=>0x9f8ac
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f000000000f000f00c0c0c0c000000000c0c0c0cf0f0000000000000f0f0000f000f00000000000f000f00a0a0a0a000000000a0a0a0a30303030000000003000300f0f0f0f0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x8ea133a84688
|_=>0
def sO:Nat→Nat→Nat
|4,0=>5
|5,0=>0x56
|6,0=>0xb5
|_,_=>0
def wAt:=mkWire dB 7 92 0xfffffffffffffffffffffff
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
addP pm 0 dom_89 5 roots_89 ops++addP pm 1 dom_83 4 roots_83 ops++addP pm 2 dzo_75_16 5 roots_75 ops++addP pm 3 dom_75 5 roots_75 ops++addP pm 4 dom_74 4 roots_74 ops++addP pm 5 dom_27 4 roots_27 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_91 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_75_16_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_27 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_89 5 s (0,roots_89.map (·&&&dom_89)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_91 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_89 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_91==dom_91)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_91 gM v ys):RunD true dom_91 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_91 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_91 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(4,20),(5,13),(5,21),(5,69),(8,9),(8,72),(12,13),(12,28),(12,76),(16,17),(16,20),(24,25),(24,28),(24,88),(64,65),(64,72),(68,69),(68,76),(68,84),(80,81),(80,84),(80,88)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1ffffff
def xsM:=roots_93.map (·&&&dom_93)
def gM:=goal_93&&&dom_93
def NN:Nat→Nat
|4=>2
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xc09ca018c0
|5,0=>0xbbcc81e1fd1d17c
|6,0=>0x4011c
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcccccccc00000000cc00cc0333333330000000022222222cc00cc0000000000cc00cc000000000000000002222222200cc00cc000000000088008b33300000000000033330000c0c0c0c000000000c0c0c0c222222220000000022222222cc00cc00000000008800880333333330000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x473204973204738204732604325043210
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x15405
|5,0=>0x166418a6
|6,0=>0x1c5
|_,_=>0
def wAt:=mkWire dB 10 94 0x3fffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x83
|_=>0
def oO:Nat→Nat→Nat
|5,0=>1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 5
def pmP:Nat→Nat
|0=>0x1f41c40
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0xca
|6,0=>4
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_89 5 roots_89 ops++addP pm 1 dom_29 4 roots_29 ops++addP pm 2 dzo_89_4 5 roots_89 ops++addP pm 3 dom_85 4 roots_85 ops++addP pm 4 dom_73 4 roots_73 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_93 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_29 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_89_4_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_73 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_89 5 s (0,roots_89.map (·&&&dom_89)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_93 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_89 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_93==dom_93)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_93 gM v ys):RunD true dom_93 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_93 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
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
theorem lowS_94:Lower true dom_94 roots_94 goal_94 6:=lower_slice_b [(0x505050500000000050505050,16,20),(0x555500000000000055550000,4,20)] (by decide +kernel) lowS_74
theorem lowS_103:Lower true dom_103 roots_103 goal_103 6:=lower_slice_b [(0xaa000000aa000000aa000000aa,32,33)] (by decide +kernel) lowS_102
theorem lowS_107:Lower true dom_107 roots_107 goal_107 6:=lower_slice_b [(0xa0a00000a0a00000a0a00000a0a,8,9)] (by decide +kernel) lowS_106
theorem lowS_117:Lower true dom_117 roots_117 goal_117 6:=lower_slice_b [(0x300030003000300030003000300030,16,20)] (by decide +kernel) lowS_113
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
|0=>0xfed91f6d8306100
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x7800400321
|6,0=>0x5696
|7,0=>9
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 6 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_156 5 roots_156 ops++addP pm 1 dom_150 5 roots_150 ops++addP pm 2 dom_138 4 roots_138 ops++addP pm 3 dom_154 5 roots_154 ops++addP pm 4 dom_142 5 roots_142 ops++addP pm 5 dom_148 4 roots_148 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_158 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_156 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_150 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_138 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_142 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_148 _ g hchk
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
def pG:List (Nat×Nat):=[(1,9),(1,33),(4,36),(4,132),(5,13),(5,37),(5,133),(8,9),(8,136),(12,13),(12,44),(12,140),(32,33),(32,36),(40,41),(40,44),(40,168),(128,132),(128,136),(129,133),(129,137),(129,161),(160,161),(160,164),(160,168)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1ffffff
def xsM:=roots_173.map (·&&&dom_173)
def gM:=goal_173&&&dom_173
def NN:Nat→Nat
|4=>2
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x2a76a0f070
|5,0=>0x4866c1957e142e4
|6,0=>0x4866c
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x33220000332200000000000000000000332200003322cccc0000cc0000000000000000000000cccc0000cc02222000022220000000000000000000022220000222200000000c8c80000000000000000000000000000c8cb3330000000000000000000000000000333300000000cc000000cc0000000000000000000000cc000000cc030300000303000000000000000000000303000003030888800008800000000000000000000008888000088033330000333300000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x43260432604832607432603265043210
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x15405
|5,0=>0x165418a6
|6,0=>0x1b5
|_,_=>0
def wAt:=mkWire dB 9 174 0x3fffffffffffffffffffffffffffffffffffffffffff
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
addP pm 0 dom_172 4 roots_172 ops++addP pm 1 dom_165 4 roots_165 ops++addP pm 2 dom_45 4 roots_45 ops++addP pm 3 dom_169 4 roots_169 ops++addP pm 4 dom_141 4 roots_141 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_173 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_172 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_165 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_169 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_141 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_172 4 s (0,roots_172.map (·&&&dom_172)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_173 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_172 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124)],[(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xffffffff00000000ffffffff00000000,96),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xffffffff00000000ffffffff00000000,96),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_173==dom_173)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_173 gM v ys):RunD true dom_173 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_173 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_173 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
namespace S_203
def pG:List (Nat×Nat):=[(1,9),(1,65),(2,10),(2,66),(2,130),(3,11),(3,67),(3,131),(8,9),(8,10),(8,72),(8,136),(64,65),(64,66),(64,72),(128,130),(128,136),(129,131),(129,137),(129,193),(192,193),(192,194),(192,200)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffff
def xsM:=roots_203.map (·&&&dom_203)
def gM:=goal_203&&&dom_203
def NN:Nat→Nat
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x8dfbc
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf000000000000000f000000000000000f000000000000000f00c0c0000000000000c0c0000000000000c0c0000000000000c0ca0a0000000000000a0a0000000000000a0a0000000000000a0af0f00000000000000000000000000000f0f0000000000000000f0f0000000000000f0f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x4688
|_=>0
def sO:Nat→Nat→Nat
|6,0=>5
|_,_=>0
def wAt:=mkWire dB 5 204 0xfffffffffffffffffffffffffffffffffffffffffffffffffff
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
addP pm 0 dom_202 5 roots_202 ops++addP pm 1 dom_139 5 roots_139 ops++addP pm 2 dom_201 5 roots_201 ops++addP pm 3 dom_75 5 roots_75 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_203 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_201 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_75 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_202 5 s (0,roots_202.map (·&&&dom_202)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_203 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_202 h
def symsG:List (List (Nat×Nat)):=[[(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_203==dom_203)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_203 gM v ys):RunD true dom_203 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_203 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_203 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_203 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_203 roots_203 goal_203 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_203
theorem lowS_203:Lower true dom_203 roots_203 goal_203 7:=S_203.noCircuit
def isoMvS_55:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_55:Lower true dom_55 roots_55 goal_55 5:=lower_iso_b isoMvS_55 (by decide +kernel) lowS_47
def isoMvS_87:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_87:Lower true dom_87 roots_87 goal_87 5:=lower_iso_b isoMvS_87 (by decide +kernel) lowS_31
def isoMvS_109:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_109:Lower true dom_109 roots_109 goal_109 7:=lower_iso_b isoMvS_109 (by decide +kernel) lowS_91
def isoMvS_110:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_110:Lower true dom_110 roots_110 goal_110 7:=lower_iso_b isoMvS_110 (by decide +kernel) lowS_91
def isoMvS_115:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_115:Lower true dom_115 roots_115 goal_115 7:=lower_iso_b isoMvS_115 (by decide +kernel) lowS_91
def isoMvS_118:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_118:Lower true dom_118 roots_118 goal_118 7:=lower_iso_b isoMvS_118 (by decide +kernel) lowS_93
def isoMvS_151:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_151:Lower true dom_151 roots_151 goal_151 6:=lower_iso_b isoMvS_151 (by decide +kernel) lowS_143
def isoMvS_155:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_155:Lower true dom_155 roots_155 goal_155 6:=lower_iso_b isoMvS_155 (by decide +kernel) lowS_117
def isoMvS_157:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_157:Lower true dom_157 roots_157 goal_157 6:=lower_iso_b isoMvS_157 (by decide +kernel) lowS_117
def isoMvS_167:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_167:Lower true dom_167 roots_167 goal_167 5:=lower_iso_b isoMvS_167 (by decide +kernel) lowS_47
def isoMvS_171:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_171:Lower true dom_171 roots_171 goal_171 6:=lower_iso_b isoMvS_171 (by decide +kernel) lowS_117
def isoMvS_174:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_174:Lower true dom_174 roots_174 goal_174 6:=lower_iso_b isoMvS_174 (by decide +kernel) lowS_117
def isoMvS_181:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_181:Lower true dom_181 roots_181 goal_181 6:=lower_iso_b isoMvS_181 (by decide +kernel) lowS_117
def isoMvS_182:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_182:Lower true dom_182 roots_182 goal_182 6:=lower_iso_b isoMvS_182 (by decide +kernel) lowS_117
def isoMvS_199:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_199:Lower true dom_199 roots_199 goal_199 5:=lower_iso_b isoMvS_199 (by decide +kernel) lowS_31
def isoMvS_205:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_205:Lower true dom_205 roots_205 goal_205 7:=lower_iso_b isoMvS_205 (by decide +kernel) lowS_93
def isoMvS_206:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_206:Lower true dom_206 roots_206 goal_206 7:=lower_iso_b isoMvS_206 (by decide +kernel) lowS_91
def isoMvS_211:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_211:Lower true dom_211 roots_211 goal_211 7:=lower_iso_b isoMvS_211 (by decide +kernel) lowS_173
def isoMvS_213:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_213:Lower true dom_213 roots_213 goal_213 7:=lower_iso_b isoMvS_213 (by decide +kernel) lowS_93
def isoMvS_214:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_214:Lower true dom_214 roots_214 goal_214 7:=lower_iso_b isoMvS_214 (by decide +kernel) lowS_93
def isoMvS_217:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_217:Lower true dom_217 roots_217 goal_217 6:=lower_iso_b isoMvS_217 (by decide +kernel) lowS_117
def isoMvS_218:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_218:Lower true dom_218 roots_218 goal_218 7:=lower_iso_b isoMvS_218 (by decide +kernel) lowS_91
def isoMvS_220:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_220:Lower true dom_220 roots_220 goal_220 7:=lower_iso_b isoMvS_220 (by decide +kernel) lowS_93
def isoMvS_227:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_227:Lower true dom_227 roots_227 goal_227 7:=lower_iso_b isoMvS_227 (by decide +kernel) lowS_91
def isoMvS_229:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_229:Lower true dom_229 roots_229 goal_229 7:=lower_iso_b isoMvS_229 (by decide +kernel) lowS_93
def isoMvS_230:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_230:Lower true dom_230 roots_230 goal_230 6:=lower_iso_b isoMvS_230 (by decide +kernel) lowS_117
def isoMvS_233:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_233:Lower true dom_233 roots_233 goal_233 7:=lower_iso_b isoMvS_233 (by decide +kernel) lowS_91
def isoMvS_234:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_234:Lower true dom_234 roots_234 goal_234 7:=lower_iso_b isoMvS_234 (by decide +kernel) lowS_203
def isoMvS_236:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_236:Lower true dom_236 roots_236 goal_236 7:=lower_iso_b isoMvS_236 (by decide +kernel) lowS_173
def isoMvS_244:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_244:Lower true dom_244 roots_244 goal_244 7:=lower_iso_b isoMvS_244 (by decide +kernel) lowS_93
theorem lowS_95:Lower true dom_95 roots_95 goal_95 8:=lower_slice_b [(0xcccccccc00000000cccccccc,8,10)] (by decide +kernel) lowS_93
theorem lowS_111:Lower true dom_111 roots_111 goal_111 8:=lower_slice_b [(0xaaaa0000aaaa0000aaaa0000aaaa,8,9)] (by decide +kernel) lowS_110
def dzo_103_16:=0xff000000ff000000ff000000ff0000
def gzo_103_16:=0xff000000fe000000fe000000fa0000
def gsh_103_16:=0xff000000fe000000fe000000fa
theorem lowS_zo_103_16_98:Lower true dzo_103_16 roots_103 gzo_103_16 6:=lower_iso_b (d1:=dom_103) (r1:=roots_103) (T1:=gsh_103_16) [(dom_103,16)] (by decide +kernel) (lower_slice_b (T:=gsh_103_16) [(0xaa000000aa000000aa000000aa,0,1),(0xf0000000f0000000f0000000f0,0,4)] (by decide +kernel) lowS_98)
namespace S_119
def pG:List (Nat×Nat):=[(1,17),(1,33),(1,65),(2,34),(2,66),(3,19),(3,35),(3,67),(4,20),(4,36),(5,21),(5,37),(5,69),(6,22),(6,38),(6,70),(7,23),(7,39),(7,71),(16,17),(16,20),(18,19),(18,22),(18,50),(18,82),(32,33),(32,34),(32,36),(32,96),(48,49),(48,50),(48,52),(48,112),(64,65),(64,66),(64,96),(68,69),(68,70),(68,84),(68,100),(80,81),(80,82),(80,84),(80,112)]
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
|4,0=>0xd8f49b710e7df1a1982107d0f
|5,0=>0xdc589d1079b8e2ab2905b0231a40428e3f671f095ba6259670386a226dcd2049d1d7570371c
|6,0=>0xf0a7cdf20ad11a4ce346ca831af8aead9c8ac6049eceb9cbec9790693a7489bed84cb0822b47669d6d5a369b3165c7e60f385db1d46e9846ac3458343f7a63d34f328c4320db30d572e96527ac8221731a8ad1984213eed0a3770371c
|7,0=>0xfffa7f4a3fd6a41b387184cb0650b64ec5b493063e1803a8f4
|8,0=>0xdaa04
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcc00cc00cc00cc00cc00cc00cc00ccff00ff000000000000000000000000ff00ff00cc00cc00cc00cc00cc00cc00000000ff00000000000000ff0000ff00ff00aa00aa00aa00aa00aa00aa33003300330033003300330000000000000000ff00ff00ff00ff00000000ff00ff00ff00ff00ff00ff00000000f000f000f000f000f000f000f000f0aa00aa00aa00aa00aa00aa00aa00aa000000003300330033003300000000ff00ff0000000000ff00ff00000000ff000000ff000000ff000000ff0000fe00fe00fe00fe00fe00fe00fa00faee00ee00ee00ee00ee00ee00aa00aaff00ff00ff00ff0000000000000000
|0,1=>0xff000000ff000000ff0000cc00cc00ff00ff0000000000000000ff003300ff000000ff003300ff0000ff00ff00ff00ff00ff00ff00cc00ccff00ff00f000f000f000f000f000f0ff00ff00cc00cc00ff00ff00cc00ccff00ff00ff00ff00cc00cc00cc00ccff00ff00ff000000ff00ff00ff000000000000ff00ff0000000000cc00cc0000000000000000ff00ff0000000000000000ff00ff0000000000000000ff00ff0033003300ff00ff00000000ff00ff00ff00ff0033003300000000330033000000000033003300000000330033003300330000000000000000cc00cc00cc00cc00cc00cc00000000
|0,2=>0xff000000ff00000000000000ff0000ff00ff00ff000000ff000000ff0000000000003300330000000000000000ff000000ff000000ff00ff00ff000000000000cc00cc00cc00cc00cc00cccc00cc00ff00ff00cc00cc00cc00cc
|_,_=>0
def sP:Nat→Nat
|0=>0x1d93c61031c64804440c718a01810718a0081031c101a2031d91880c718a3880c73cb6073c65c02431cf1940c71920040c71934480c71924482431cf1840c70402031cd1841c628c0040c718a0080c72ca2431c62890c71852031c61440c2040
|1=>0x3c60040c73c62806840c76460040c764f1951031cf2c06081073c60081031d01801031cf1970047c73c60040c73c601e11d1cf1807040c73c60141031cf1801031cf1930080c73c64806041cf18045810764f1801036cf1802040c73c6448103
|2=>0xc73c60111031d93c60045831cf1801031cf1803841cf18c0155831cf1951031cd1801073c69401241cf1806041cf1805481031c62801031cf1808c81073c63001031d01808841cf1806880c73c60080c73c63881031cf1801031e11801031e0
|3=>0x40c73c60040c73c64801073c63001031cf1805581073c60081031cf1806840c73c6004
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x14507a82940aa005
|5,0=>0x1a58c6c5d62bb149498c47520b0ed86ac2f615289543ec196
|6,0=>0x15e7ac3549a98d4669fbce1e62f2a7923479a2ef116853c119faef6777bba1dc4cdb76a3b35d8ecc075d32cdd58ea574f3a5dd20e8a641b9f1ceae6f6
|7,0=>0x344f9c6cabe3db10f817bd3dcded8f657
|8,0=>0x1a96
|_,_=>0
def wAt:=mkWire dB 38 120 0xffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x43f1038402103440110f4f023c044031000402100cf39100160e100c3391000401100483c100560d100c40110044003cec4001008639100033b10012020d2443f100440d10347391000401100483f1004401100463910016551008403406483c1004f391004400
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0xc1000930006300000000000cc0300000
|6,0=>0xbcad2aca92002810027194a3288602001e200000001d16c80000000649815880000000545414c512404f1000d2
|7,0=>0xe8791e0771d8751d0731c8711
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 10
def pmP:Nat→Nat
|0=>0xf3fcde7e6a9060477ddd73d8d625811445012c44108411002a07c1a0180400c0200400
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x45020030000230c00
|6,0=>0x9bde104900e3c4ad5bc001130b1020c90000610aab1401
|7,0=>0x294d4f55ce77b
|8,0=>0x12
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 10 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_118 7 roots_118 ops++addP pm 1 dom_85 4 roots_85 ops++addP pm 2 dom_117 6 roots_117 ops++addP pm 3 dom_115 7 roots_115 ops++addP pm 4 dom_101 5 roots_101 ops++addP pm 5 dom_54 4 roots_54 ops++addP pm 6 dom_87 5 roots_87 ops++addP pm 7 dzo_103_16 6 roots_103 ops++addP pm 8 dom_103 6 roots_103 ops++addP pm 9 dom_55 5 roots_55 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_119 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_101 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_103_16_98 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_55 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_118 7 s (0,roots_118.map (·&&&dom_118)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_119 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_118 h
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
theorem lowS_159:Lower true dom_159 roots_159 goal_159 9:=lower_slice_b [(0xaaaaaaaa000000000000000000000000aaaaaaaa,8,9)] (by decide +kernel) lowS_158
namespace S_175
def pG:List (Nat×Nat):=[(1,9),(1,33),(2,10),(2,34),(2,130),(3,11),(3,35),(3,131),(4,36),(4,132),(5,13),(5,37),(5,133),(6,14),(6,38),(6,134),(7,15),(7,39),(7,135),(8,9),(8,10),(8,136),(12,13),(12,14),(12,44),(12,140),(32,33),(32,34),(32,36),(40,41),(40,42),(40,44),(40,168),(128,130),(128,132),(128,136),(129,131),(129,133),(129,137),(129,161),(160,161),(160,162),(160,164),(160,168)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_175.map (·&&&dom_175)
def gM:=goal_175&&&dom_175
def NN:Nat→Nat
|4=>5
|5=>16
|6=>36
|7=>9
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xc746ebfe21493c723a2201b39
|5,0=>0xb573daf7bda4d9d9337e91b606a6d2671e363085610bc608f24c8134af81262e41060b072a2035e2
|6,0=>0xd6b3fd4100c9008bf0d5ae8caa7fc69c12e95b3293a68931867c4966c7196a24f62a63615ea59907504b84fc6e4ef6c4e1764af8142b1c41e90414873dd7739146371912fb842d7492a2ea28537266e4234f91ab2d1427003b56
|7,0=>0xd21e9c9008bd5114764f423853b062363ea32ae814494
|8,0=>0x3e74a
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffff0000ffff00000000000000000000ff000000ff00ff000000ff0000000000000000000000000000000000ff000000ff0000000000000000000000ff000000ff0000ff000000ff00000000000000000000ff000000ff00ffff0000ffff00000000000000000000000000000000ffff0000ffff00000000000000000000ffff0000ff0000ff000000ff00000000000000000000ffff0000ff00ffff0000ff0000000000000000000000ffff0000ff00ffff0000ffff00000000000000000000ffff00000000fff00000fff000000000000000000000f0f00000f0f0cccc0000cccc00000000000000000000cccc0000ccccffff0000000000000000000000000000ffff00000000f0f00000f0f000000000000000000000f0f00000f0f0ffcc0000ffcc00000000000000000000cccc0000ccccaaaa0000aaaa00000000000000000000aaaa0000aaaa00000000ffff0000000000000000000000000000ff00
|0,1=>0xff000000000000000000000000000000ff00ffff0000ffff0000000000000000000000000000ff00ff000000000000000000000000000000ff000000ff00fff00000fff000000000000000000000fff00000fff0ffff0000ffff00000000000000000000f0f00000f0f000000000000000000000000000000000550000005500ff550000ff5500000000000000000000ff000000ff000f0f00000f0f000000000000000000000f0f000000005555000000000000000000000000000055550000550033330000333300000000000000000000333300003300ffff0000ff000000000000000000000000000000000055550000555500000000000000000000555500005500aaaa0000aaff00000000000000000000aaaa0000aaaaffff0000ff0000000000000000000000ffff0000000000000000000000000000000000000000ff000000ff0000ff000000ff0000000000000000000000ff00000000
|0,2=>0xffff0000ffff00000000000000000000fff00000fff00f0f00000f0f000000000000000000000f0000000f00ffff000000ff00000000000000000000ffff00000000ffaa0000ffaa00000000000000000000aaaa0000aaaa555500005500000000000000000000005555000055000000000000000000000000000000000000000000ff0000ff0000000000000000000000000000ffff00000000aaaa0000aaaa00000000000000000000ffaa0000ffaa00000000ffff00000000000000000000000000000000aaaa0000ffff00000000000000000000aaaa0000aaaa00000000000000000000000000000000ffff0000ff0000ff000000ff0000000000000000000000000000000000000000000000000000000000000000ffaa0000ffaa00aa000000aa00000000000000000000aaaa0000aaaa0f0000000f00000000000000000000000f0000000f00f0ff0000f0ff00000000000000000000000000000000
|0,3=>0xffff0000ffff00000000000000000000aaaa0000aaaa55000000550000000000000000000000550000005500ffff00000f0000000000000000000000ffff00000f00ffff0000ffff00000000000000000000550000005500
|_,_=>0
def sP:Nat→Nat
|0=>0x582c43c31413843431572c43430562c40c50403873431415443cc0c504a1031413881061412c81c31413843431542c43c308110d0c54cb48d0c504b1110c50501c434614110c0c50481030812ca1030812070c20491031412071850440c2040
|1=>0x1412c4a0d0c504b1c43431413843431662e510d0c504b48d0c504b1c43510c50444431419048cd0c504b10d0c588b10d0c504b80434314178b2843431412c435d0c504b11c3c31412c81cd0c504b11c35b1412c434314168b1193431412c4345
|2=>0x4b10d0c504b3843431417cb10d0c504b9043431412d5c4d0c504b10f3431412c4343141c0b10f0c50612d210d0c504b10d4431419c4bcd0c504b10d0c506e2c43430812ed10d0c504b10d0c5b0b10d0c50402c810d0c5acb10d0c506a2e9343
|3=>0x10d0c504b2043431412c43cd0c504b10d0c5cc12c434314184b10d0c50722c435b0c5
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x14507a82940aa005
|5,0=>0x38b1ad8cac5f62cb14d89ac47620b0f146cc30615309183ea196
|6,0=>0xb13d71aaaf4e7a3bd01e72f32795bc95a3cf18688bc29e06efd67b3bbddd2ce276e3355d9ecc876132edd68ead7533a7dd30e917453a0dcfac776
|7,0=>0x1a17cd3e4df18f857bf3dddee0f697
|8,0=>0x1a86
|_,_=>0
def wAt:=mkWire dB 52 176 0xffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x10d4d2d04b433604d832d34b043634b84850cd8d2e04e4d2c201c4351cd843b34b0b34067442e20bc43934b0b3634bcd2e04ecd2c84b9f2d10f4d2d2cd470f10b4d2c34b4f3b34b0d2d
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0xc00
|6,0=>0x1f200000000000000000000785c2001a26457200161509314490138800308b12848200071000000000014832
|7,0=>0x291a0671986519063188611
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 10
def pmP:Nat→Nat
|0=>0xf69f2dbd9b39b1d7cd74d34d33d20818010408004604503103001000c009008005004002001000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x80000020
|6,0=>0x460000000310b0410601425095600b8ea03d2d00024
|7,0=>0x11966b8bd233
|8,0=>0x16
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 12 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_173 7 roots_173 ops++addP pm 1 dom_165 4 roots_165 ops++addP pm 2 dom_167 5 roots_167 ops++addP pm 3 dom_143 6 roots_143 ops++addP pm 4 dom_139 5 roots_139 ops++addP pm 5 dom_142 5 roots_142 ops++addP pm 6 dom_47 5 roots_47 ops++addP pm 7 dom_163 4 roots_163 ops++addP pm 8 dom_171 6 roots_171 ops++addP pm 9 dom_174 6 roots_174 ops++addP pm 10 dom_46 4 roots_46 ops++addP pm 11 dom_170 5 roots_170 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_175 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_165 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_143 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_142 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_47 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_174 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_46 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_170 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_173 7 s (0,roots_173.map (·&&&dom_173)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_175 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_173 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_175==dom_175)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_175 gM v ys):RunD true dom_175 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_175 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 5 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 36 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 36 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 9 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_175 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_175 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_175 roots_175 goal_175 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_175
theorem lowS_175:Lower true dom_175 roots_175 goal_175 9:=S_175.noCircuit
def dzo_75_4:=0xf0f0000000000000f0f0
def gzo_75_4:=0xf0e0000000000000e000
def gsh_75_4:=0xf0e0000000000000e00
theorem lowS_zo_75_4_75:Lower true dzo_75_4 roots_75 gzo_75_4 5:=lower_iso_b (d1:=dom_75) (r1:=roots_75) (T1:=gsh_75_4) [(dom_75,4)] (by decide +kernel) (lower_slice_b (T:=gsh_75_4) [] (by decide +kernel) lowS_75)
def dzo_203_4:=0xf0f0000000000000f0f0000000000000f0f0000000000000f0f0
def gzo_203_4:=0xf0f0000000000000f0f0000000000000f0e0000000000000e000
def gsh_203_4:=0xf0f0000000000000f0f0000000000000f0e0000000000000e00
theorem lowS_zo_203_4_75:Lower true dzo_203_4 roots_203 gzo_203_4 6:=lower_iso_b (d1:=dom_203) (r1:=roots_203) (T1:=gsh_203_4) [(dom_203,4)] (by decide +kernel) (lower_slice_b (T:=gsh_203_4) [(0xf0f0000000000000f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_75)
namespace S_207
def pG:List (Nat×Nat):=[(1,9),(1,65),(2,10),(2,66),(2,130),(3,11),(3,67),(3,131),(4,132),(5,13),(5,69),(5,133),(6,14),(6,70),(6,134),(7,15),(7,71),(7,135),(8,9),(8,10),(8,72),(8,136),(12,13),(12,14),(12,76),(12,140),(64,65),(64,66),(64,72),(68,69),(68,70),(68,76),(68,196),(128,130),(128,132),(128,136),(129,131),(129,133),(129,137),(129,193),(192,193),(192,194),(192,196),(192,200)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_207.map (·&&&dom_207)
def gM:=goal_207&&&dom_207
def NN:Nat→Nat
|4=>3
|5=>10
|6=>17
|7=>7
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x6033d455871f484
|5,0=>0xff874e4199e2dabdce6f9bfb66fd024e5b949bff32c2d0c2b7
|6,0=>0xd50c7ca7f6c6731be6dbba1efb4fd7b21f0af622a69bd904708bacb82d147d822511ef4ac231071b00415
|7,0=>0xc55deb967d9c0d28b8ec77ebb735165bf25
|8,0=>0x83b1d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0000000000000f0f00000000000000000000000000000000ff00000000000000ff00000000000000ff00000000000000000055550000000000005555000000000000555500000000000055000f0f000000000000ff0f0000000000000000000000000000ff00fff0000000000000fff0000000000000fff0000000000000fff0ff00000000000000ff00000000000000ff00000000000000ff005555000000000000550000000000000055550000000000005500ffff000000000000ffff000000000000ff00000000000000ff00ffff0000000000000000000000000000ffff0000000000000000cccc000000000000cccc000000000000cccc000000000000ccccffaa000000000000ffaa000000000000ffaa000000000000aaaaffff000000000000ff00000000000000ffff000000000000ff00f0f0000000000000f0f0000000000000f0f0000000000000f0f0ffcc000000000000ffcc000000000000ffcc000000000000ccccaaaa000000000000aaaa000000000000aaaa000000000000aaaaffff000000000000ffff00000000000000000000000000000000
|0,1=>0xf0f0000000000000fff0000000000000f0f0000000000000fff000ff00000000000000ff00000000000000ff00000000000000000000000000000000ffff0000000000000000000000000000ff00000000000000000000000000000000000000000000000000ff00ff0f000000000000ff0f000000000000ff00000000000000ff00ffff000000000000ffff000000000000ffff0000000000000000ffff000000000000ffff000000000000ffff000000000000ff0000000000000000000000000000000000ff00000000000000ff00ffff0000000000000000000000000000ffff000000000000ff0000000000000000000000000000000000ffff000000000000ff000000000000000000ff000000000000000000000000000000ff00ffff000000000000ffff0000000000000000000000000000ff0033330000000000003333000000000000333300000000000033005555000000000000000000000000000055550000000000005500
|_,_=>0
def sP:Nat→Nat
|0=>0x304e07914609c0fca8c13808a1983805d43304e0aa86609c1450cc138152198270286189c0a19a07028c9381e819827710660b80a198a70286669c0a188270298609c0b519270206209c833140418820
|1=>0x50cc13816a304e04286609c0a304e07aac3304e054c6609c0450cc138143307070754609c0a199270286609dc0428660e0e450cc938164518270286609f8056c6609c0ad0cc138153
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0xa5055005
|5,0=>0x4563f63963362d62762161b61560f6
|6,0=>0xb96b36ac7a579e79779078978277b77476e66776075975274b7
|7,0=>0xe86e17db6d47cd7c67bf7
|8,0=>0xee6
|_,_=>0
def wAt:=mkWire dB 30 208 0xffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x50d50118250351f51d38198d51f20751d56038138150120751d50d51d56238156338151f18218251d53d18238151d20151db1d50320351d98151f
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x1e2709a2609625092200102388c2288821884208802
|7,0=>0x261946418c62184601
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 10
def pmP:Nat→Nat
|0=>0xffbfb77767503f37251c110f0c060100
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0xb29655303a5b74133
|7,0=>0xfecedd9
|8,0=>8
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 8 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_206 7 roots_206 ops++addP pm 1 dom_205 7 roots_205 ops++addP pm 2 dom_203 7 roots_203 ops++addP pm 3 dzo_75_4 5 roots_75 ops++addP pm 4 dom_143 6 roots_143 ops++addP pm 5 dom_75 5 roots_75 ops++addP pm 6 dzo_203_4 6 roots_203 ops++addP pm 7 dom_199 5 roots_199 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_207 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_zo_75_4_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_143 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_203_4_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_199 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_206 7 s (0,roots_206.map (·&&&dom_206)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_207 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_206 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_207 gM v ys):RunD true dom_207 gM v (ori ys):=h
def Z (s:Nat):=barP dom_207 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 17 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 17 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 7 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_207 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_207 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_207 roots_207 goal_207 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_207
theorem lowS_207:Lower true dom_207 roots_207 goal_207 9:=S_207.noCircuit
def dzo_151_64:=0xff00ff00000000000000000000000000ff00ff0000000000000000
def gzo_151_64:=0xff00fe00000000000000000000000000fe00ee0000000000000000
def gsh_151_64:=0xff00fe00000000000000000000000000fe00ee
theorem lowS_zo_151_64_148:Lower true dzo_151_64 roots_151 gzo_151_64 6:=lower_iso_b (d1:=dom_151) (r1:=roots_151) (T1:=gsh_151_64) [(dom_151,64)] (by decide +kernel) (lower_slice_b (T:=gsh_151_64) [(0xaa00aa00000000000000000000000000aa00aa,0,1),(0xcc00cc00000000000000000000000000cc00cc,0,2)] (by decide +kernel) lowS_148)
namespace S_215
def pG:List (Nat×Nat):=[(1,17),(1,65),(2,66),(2,130),(3,19),(3,67),(3,131),(4,20),(4,132),(5,21),(5,69),(5,133),(6,22),(6,70),(6,134),(7,23),(7,71),(7,135),(16,17),(16,20),(16,144),(18,19),(18,22),(18,82),(18,146),(64,65),(64,66),(68,69),(68,70),(68,84),(68,196),(80,81),(80,82),(80,84),(80,208),(128,130),(128,132),(128,144),(129,131),(129,133),(129,145),(129,193),(192,193),(192,194),(192,196),(192,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffffff
def xsM:=roots_215.map (·&&&dom_215)
def gM:=goal_215&&&dom_215
def NN:Nat→Nat
|4=>3
|5=>5
|6=>9
|7=>3
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x9433c895166194a
|5,0=>0xaf81a5ce2d328130adb60ad34
|6,0=>0xd3738ae203935ed8c5d483131767d95ceac5ce2d01891
|7,0=>0xb7061831312d4f9
|8,0=>0xde6cd
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xff00000000000000000000000000ff00ff0000000000000000ff00aa0000000000ff00aa0000000000aa00aa0000000000aa00aaff00f00000000000ff00f00000000000f000f00000000000f000f000000000000000000000000000000000ff00000000000000ff00000000ff00000000000000ff00000000000000000000000000000000ff00ff0000000000ff00ff00000000000000000000000000000000ff00000000000000ff00000000000000ff00000000000000ff0000f000f00000000000f000f00000000000f000f00000000000f000f0ff00000000000000ff000000000000000000000000000000000000ff00ff0000000000ff00ff0000000000ff00000000000000ff00000f000f00000000000f000f00000000000f000000000000000f00000000ff00000000000000ff0000000000ff00000000000000ff0000cc00cc0000000000cc00cc0000000000cc00cc0000000000cc00ccaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa00000f000000000000000f00000000000f000000000000000f0000ff00ff00000000000000000000000000ff00ff0000000000000000
|0,1=>0xff00ff0000000000ff00000000000000ff00ff0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x1281880a4b103101464a062029281880a3a5a31014940c505250313d4640c40399281880a4a06e029881880b48c45028c9188a05188818809188a0519a31008818806188a039862080831140418820
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x2942a805
|5,0=>0x2563ec694aa8f6
|6,0=>0x5d6aed45a5b4477cce19932b7
|7,0=>0x1c5f53e37
|8,0=>0x786
|_,_=>0
def wAt:=mkWire dB 17 216 0xffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x5264a94a84a84a96295264a931f4a84a94a84a962d4aa526
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x53000c80600
|6,0=>0x16492000000081
|7,0=>0x3c5c2d1
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 9
def pmP:Nat→Nat
|0=>0xffccd8c1420100
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x1048
|6,0=>0x402b501
|7,0=>0x1ff
|8,0=>6
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 7 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_214 7 roots_214 ops++addP pm 1 dom_211 7 roots_211 ops++addP pm 2 dom_87 5 roots_87 ops++addP pm 3 dom_199 5 roots_199 ops++addP pm 4 dom_213 7 roots_213 ops++addP pm 5 dom_151 6 roots_151 ops++addP pm 6 dzo_151_64 6 roots_151 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_215 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_151_64_148 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_214 7 s (0,roots_214.map (·&&&dom_214)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_215 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_214 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff0000ffff0000ffff0000,112),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_215==dom_215)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_215 gM v ys):RunD true dom_215 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_215 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 5 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 9 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 3 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_215 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_215 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_215 roots_215 goal_215 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_215
theorem lowS_215:Lower true dom_215 roots_215 goal_215 9:=S_215.noCircuit
def dzo_74_16:=0x50500000000000005050000
def gzo_74_16:=0x50400000000000004000000
def gsh_74_16:=0x5040000000000000400
theorem lowS_zo_74_16_74:Lower true dzo_74_16 roots_74 gzo_74_16 4:=lower_iso_b (d1:=dom_74) (r1:=roots_74) (T1:=gsh_74_16) [(dom_74,16)] (by decide +kernel) (lower_slice_b (T:=gsh_74_16) [] (by decide +kernel) lowS_74)
def dzo_202_16:=0x5050000000000000505000000000000050500000000000005050000
def gzo_202_16:=0x5050000000000000505000000000000050400000000000004000000
def gsh_202_16:=0x505000000000000050500000000000005040000000000000400
theorem lowS_zo_202_16_74:Lower true dzo_202_16 roots_202 gzo_202_16 5:=lower_iso_b (d1:=dom_202) (r1:=roots_202) (T1:=gsh_202_16) [(dom_202,16)] (by decide +kernel) (lower_slice_b (T:=gsh_202_16) [(0x505000000000000050500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_74)
def dzo_203_16:=0xf0f0000000000000f0f0000000000000f0f0000000000000f0f0000
def gzo_203_16:=0xf0f0000000000000f0f0000000000000f0e0000000000000e0a0000
def gsh_203_16:=0xf0f0000000000000f0f0000000000000f0e0000000000000e0a
theorem lowS_zo_203_16_74:Lower true dzo_203_16 roots_203 gzo_203_16 6:=lower_iso_b (d1:=dom_203) (r1:=roots_203) (T1:=gsh_203_16) [(dom_203,16)] (by decide +kernel) (lower_slice_b (T:=gsh_203_16) [(0xa0a0000000000000a0a0000000000000a0a0000000000000a0a,0,1),(0xf0f0000000000000f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_74)
namespace S_219
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(2,10),(2,66),(2,130),(3,11),(3,19),(3,67),(3,131),(8,9),(8,10),(8,72),(8,136),(16,17),(16,144),(18,19),(18,26),(18,82),(18,146),(24,25),(24,26),(24,88),(24,152),(64,65),(64,66),(64,72),(80,81),(80,82),(80,88),(80,208),(128,130),(128,136),(128,144),(129,131),(129,137),(129,145),(129,193),(192,193),(192,194),(192,200),(192,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_219.map (·&&&dom_219)
def gM:=goal_219&&&dom_219
def NN:Nat→Nat
|4=>11
|5=>96
|6=>286
|7=>130
|8=>18
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xfcb51f4967cdf998a99e6537755d2d509f3331f0270d20dd6c0cd00
|5,0=>0xfeb06e9c65e7c4bd69a9d5adbd3758d1af9cd3c0ca9aac908cc5587c4820bf1b5b9192b6ac8b5678b54a9b4409b0b5cab7aba99fa9eb0b9bfe79b2249a2818fc108d5528660c855408202a81df27e49e7dbd17b61c791647891d780f877bc276df46dffa6a95c6a71c69f61698266742e654ae641c15e5f35d02657a22544345420f53722509fb509254e2504c8c74b3c349b064974e44d1a42ca33d71e3c1ac39b3f34c6c345742eeee2ce032a5302845c27a7125a9f258cf252c22442321f571f0bd1e0781d8861d0d81844315f3d1562c14faf12ec8105ed0a36f07cc606d6506c4b04d0f02dc2020930208601549
|6,0=>0x4d9754b9764b3c34b10e4964649544490e948dc148b5d486f64750946792460f445a1d44c4c43cfb43c3f4209c4197f40fc7400653fdbf3ded33d51f3c3463bbf43bafa3ac393a0d039ffc39b3f3909138313379c9378b7377333700b36d49367f63555934bdb345e8333203301732b3532729326103259831716316b13165b313bc304d62fb282f9162f4ea2e7982d34f2d01d2bcd52b4582ad7929fed29be529bb228f3c2802526cac264e3245332381e236db233f922e7822ae92244420f141fb501f93d1f8011eb921ea3b1cd931bd981bcdb19c8b19b9919a5a195f1161b91562c150e61501d1328f131cf12c2f123d6114c8112271108d0ee9d0e9f50d8de0caae0ba680b17a0a3fa098de097cf0977408b4c087320733a070e406f9506e4305963051b50501204b6b03dbc03d8c0335a026ca02614018b400f33008bb
|6,1=>0xc1ba2c0569c0273bf152beb1abe951bc4cabc2e6b9fcdb8381b4947b48a2b1e4eb11e6adcb1ac8e9aa51fa974ea79aba7755a65b8a64e6a580fa4e87a4881a29df9ff879ef7e9eee49a07e98c7e95ba394fe793baf930cd92df29198e8fb9f8f8bb8f8238f7958ed4e8e9cc8df3f8d8b88d5a68aec98a7e389068888a4880a3872bb86bb9865e1865bf85a6a83fee837d88347a7fff97f93a7de877d2a47c6677baf87b8917b61c7b4fc7a2437969178cc4768297597575214742e2741d07328d730be7307a7204371f276ecdb6d48b6d11f6c9996ba1c69f6169e3869b80694ee68dca684cd683cb67b116663d65e8f6525863742632f16110060d856003f5ecf45e20c5db4d5d7825c67a5c5ca5c2595aaef59fea59bf25974a585f4584ee562ea55c35551c354f7154a1f542fb540535253950e284f7454eb8e4e7434e211
|6,2=>0xfeb06fe911f8473f832bf2ccbf0942ec5aeebfa0e914ae8cdce489fdf87addde9d89ffd4e58d3f1ccf7e2cf023cdfa4cd46accdd9ccbf6cc47dc9b06c7482c727cc6101c5698c4758c1e32
|7,0=>0xe422fde625ce72ebe121bae9fba2a9b7f94b04ecae73eab1b7a8f5ba4acfa2903a1df7a0c109e8769adcd9ac389a69899d42988ad96716915578d0d67fab97f8897d48e7a7c176eb4742e273b347349f717da71615715326f1c36c9996afdd666f5640926274e62449614f75e83c5e1735c57a5b8585abc059de557113501e54f27c4ec7a4e3304898c482a84787d44e9843f1b424ea41cff41cbf419403f7383e6e33d9f33d7c73ce323999837171365bf3604f33410327fd3261031a933165b30e67305212fde32f52c2e7982cd9529b352764d26de026b0d264fa232e6216bc2112f204d51eec21edac1c5671c3da1c1f519b9917cb9162101512614ade1370d1356b134a01215911be810d730ebe50ebc70e75c0d49a0cc890be910b4bb0aef30a73b082a80760606f5006cc20545204fb004939042ee02b89013b200447
|7,1=>0xf0ba5efd64
|8,0=>0xe4333dadacc7272ae47eab7b17f320798d46dd594c5014af0f488e43f7382fd772c94d1bf4d1a6d21060d088ca
|9,0=>0x798d4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xc0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0cf0f0f0f000000000f000f00000000000f0f0f0f000000000f000f00f0f0f0f000000000f0f0f0f000000000c0c0c0c000000000c0c0c0cf0c0f0c000000000f0c0f0c000000000f0c0f0c0000000000000000f0f0f0c000000000f0f0f00000000000f0f0f0c000000000f0f0f00f0f0f0f000000000c0c0c0c000000000f0f0f0f000000000c0c0c0c003000300000000000c000c000000000003000300000000000c000cf0f0f0f000000000f0f0f0f00000000000000000000000000000000f0f0f0f000000000c0c0c0c000000000f000f00000000000c000c00a0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0af0f0f0f000000000f0f0f0f000000000f0f0f0f0000000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000f0c0f0c000000000f0c0f0c000000000f0c0f0c000000000f0c0f0ce0e0e0e000000000e0e0e0e000000000e000e00000000000e000e00f0f0f0f000000000f0f0f0f000000000a0a0a0a000000000a0a0a0af0f0f0f0000000000000000000000000f0f0f0f0000000000000000
|0,1=>0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000c0c0c0cf0e0f0e000000000f0e0f0e000000000f0e0f0e000000000a0a0a0af0f0f0f0000000004040404000000000f0f0f0f0000000004040404f0f0c0c000000000f0f0000000000000f0f0c0f000000000f0f0000f0f0f0f000000000f0f0f0f000000000f000f00000000000f000f0050405040000000005040504000000000504050400000000050405040000000000000000f0a0f0a0000000000000000000000000f0a0f0aa0a0a0a000000000e0e0e0e000000000a0a0a0a000000000e0e0e0e00f000f00000000000c000c00000000000f000f00000000000c000cf000f00000000000f000f00000000000f000f00000000000f000f00e0e0e0e000000000e0e0e0e000000000e0e0e0e0000000000000000f0f0f0f000000000f0f0f0f000000000e0e0e0e000000000e000e00f0a0f0a000000000f0a0f0a000000000f0a0f0a000000000f0a0f0ae0e0e0e000000000e000e00000000000e0e0e0e000000000e000e003030303000000000c0c0c0c0000000003030303000000000c0c0c0cf0f0f00000000000f0f0f00000000000f0f0f00000000000f0f0f00
|0,2=>0xf0f0f0f0000000000000000000000000f0e0f0ef000f00000000000f030f00000000000f000f00000000000f030f00f0f0f0f0000000000000000000000000f0c0f0c00000000000000003020302000000000302030200000000030203020000000003020302f0c0f0f000000000f000f00000000000f0c0f0f000000000f000f00f0f0f0f000000000a0a0a0a000000000f0f0f0f000000000a0a0a0ac0c0c0c000000000f0e0f0e000000000c0c0c0c000000000f0e0f0e0000000000000000c0c0c0c0000000000000000000000000c0c0c0cc0c0c0c0000000000000000000000000c0c0c0c0000000000000000f0f0000000000000f0f0000000000000f0f0303000000000f0f0300f0f0f0f000000000f0c0f0c000000000f0f0f0f000000000f0c0f0c0000000000000000f0e0f0e0000000000000000000000000f0e0f0ee0e0e0e000000000e0e0e0e000000000e0e0e0e000000000e0e0e0ef0e0f0e000000000a0a0a0a000000000f0e0f0e000000000a0a0a0ac0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c000c00f0f0000000000000f0f0004000000000f0f0000000000000f0f0004
|0,3=>0x30303030000000000000000000000000303030300000000000000000000000000000000a0a0a0a0000000000000000000000000f0e0f0ef0f0f0f000000000e0e0e0e000000000f0f0f0f000000000e0e0e0ef0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f000f00f0a0f0a000000000f0a0f0a00000000030203020000000003020302f0f0e0e000000000f0f0e00000000000f0f0e0e000000000f0f0e00f0f0f04000000000f0f0f04000000000f0f0f04000000000f0f0f04303030300000000000c000c000000000303030300000000000c000cf0a0f0a000000000f0a0f0a000000000f0a0f0a000000000000000000000000000000000000000000000000f0f0000000000000f0f0f0c4040404000000000404040400000000040404040000000004040404f0e0f0e0000000000000000000000000f0e0f0e0000000000000000f0f0f00000000000f0f0f00000000000c0c0c00000000000f0f0f00a0a0a0a0000000000000000000000000f0e0f0e00000000000000000000000000000000e0e0e0e0000000000000000000000000e0e0e0e3030303000000000303030300000000030303030000000000000000
|0,4=>0xf0f0f0f000000000c080c08000000000f0f0f0f000000000c080c08f0f0f00000000000f0f0f00000000000f000f00000000000f0f0f00c0c0c0c000000000c0c0c0c000000000c040c04000000000c000c0000f000f000000000000000000000000000f000f00000000000c000cf000f00000000000f000f00000000000f000f00000000000e000e003030303000000000f0c0f0c0000000003030303000000000f0c0f0cf0f0f0f000000000f0f0f0f000000000f0c0f0c0000000000000000f030f03000000000f0c0f0c000000000f030f03000000000f0c0f0cc0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c080c08f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000a0a0a0af0e0f0e000000000f0e0f0e000000000f0e0f0e000000000f0e0f0e00f000f00000000000e000e00000000000f000f00000000000e000ee0e0e0e000000000a0a0a0e000000000e0e0e0e000000000a0a0a0ef0f0f0f000000000f0f0f0f00000000000f000f0000000000000000f040f04000000000f040f04000000000f040f04000000000f040f04f0c0f0c000000000f000f00000000000f0c0f0c000000000f000f00
|0,5=>0xf0c0f0c0000000000000000000000000f0c0f0c0000000000000000a0f0a0f000000000a0e0a0e000000000a0f0a0f000000000a0e0a0e3030303000000000303030300000000030103010000000003000300005000500000000000400040000000000050005000000000004000450505050000000000000000000000000d0d0d0d000000000c0c0c0c002000200000000000200020000000000020002000000000a0a0a0af0f0f00000000000f0f0f04000000000f0f0f00000000000f0f0f045050505000000000000000000000000050505050000000000000000d0d0d0d000000000c0c0c0c000000000d0d0d0d000000000c0c0c0c00f000f00000000000f000f00000000000f000f00000000000e000e00c000c00000000000c000c00000000000f000f00000000000c000c3030303000000000303030300000000030303030000000003000300303030300000000030303030000000003000300000000000300030000000000000000000000000000000000f0f0f0f000000000c0c0c0c00000000000000000000000000000000f0f0f0f000000000f0f0f0cf0f0f0f000000000f0f0f0f00000000030303030000000000000000
|0,6=>0xf0f0404000000000f0f0404000000000f0f0404000000000f0f040400400040000000000040004000000000004000400000000000400040000000000000000f0f0f0f0000000000000000000000000f0c0f0cc0c0c0c000000000c0c0c0c000000000c0f0c0f000000000c0c0c0cf0f0f0f0000000000000f0c000000000f0f0f0f0000000000000f0c10101010000000001010101000000000100010000000000010001005050505000000000000000000000000050505050000000004040404f0f0f0f0000000000000000000000000f000f00000000000000000000f000f000000000000000000000000000f000f00000000000000000000000000000000f0f0f0f0000000000000000000000000e0e0e0ef0f0f0f000000000f0f0f0f000000000f0a0f0a000000000f0a0f0a00f000f000000000004000400000000000f000f000000000004000400000000000000000000000000000000c0c0c0c000000000c0c0c0cf0f0f0f000000000000000000000000030303030000000000000000f0f0f0f000000000f0f0f0f00000000000300030000000000000000f0f0f0f000000000f000f0000000000030303030000000003000300
|0,7=>0x505050500000000040404040000000005050505000000000404040400300030000000000000000000000000003000300000000000000005050505000000000505050500000000050505050000000005000500f000f00000000000f0c0f0c000000000f000f00000000000f0c0f0cc0f0c0f000000000c0c0c0c000000000c0f0c0f000000000c0c0c0c00d000d00000000000c000c00000000000d000d00000000000c000cf0c0f0c000000000f0c0f0c000000000f0f0f0f000000000f0c0f0c00000000000000000000000000000000e0e0e0e000000000e0e0e0ef000f00000000000f000f00000000000f0f0f0f000000000f000f00f0f0f0f00000000000000000000000000030003000000000000000000000000000000000000000000000000c0f0c0f000000000c0c0c0c0000000000000000000000000000000000f000f00000000000c000c00c000c00000000000c000c00000000000c000c00000000000c000cb0b0b0b000000000b0b0b0b000000000b0a0b0a000000000b0a0b0a0000000000000000000000000000000000e000e00000000000e000ea0a0a0a000000000a0a0a0a000000000e0e0e0e000000000e0e0e0e
|0,8=>0xf0f0000000000000f0f0000000000000a0a0000000000000a0a0000f0f0f00000000000f0f0f00000000000f0a0f00000000000f0a0f00f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0c0f0cf0f0f0f0000000000000000000000000f0f0f0f000000000c0c0c0c0000f0f00000000000000000000000000000f0f0000000000000000c0c0f0f000000000c0c0c0c000000000c0c0f0f000000000c0c0c0c00000000000000000000000000000000f0a0f0a000000000f0a0f0af0f0f00000000000c0c0c00000000000f0f0f00000000000c0c0c00c0c0c0c000000000c0c0c0c000000000f0f0f0f000000000f0c0f0ce0e0e0e000000000e0a0e0a000000000e0e0e0e000000000e0a0e0a0000000000000000000000000000000050405040000000005040504a0a0a0a000000000f0f0f0f000000000a0a0a0a000000000f0a0f0ac0c0c0c000000000c0c0c0c000000000f0f0f0f000000000c0c0c0c00000000000000000000000000000000f0f0f0f0000000000000000f0f0f00000000000f0f0f00000000000f0f0f0f000000000f0f0f005050505000000000500050000000000050505050000000005000500
|0,9=>0xf0f0f0f0000000003030303000000000f0f0f0f0000000003000300f0f0f0f000000000f0f0f0f00000000050505050000000004040404f0f0000000000000f0f00000000000000000000000000000f0f0000c0f0c0f000000000c0f0c0f000000000c0f0c0f000000000c0c0c0cf0b0000000000000f0b0000000000000f0b0000000000000f0b00005050505000000000505050500000000050505050000000000000000f0f0f0f000000000f0f0f0f000000000e0e0e0e000000000e0e0e0ef0f0004000000000f0f0004000000000f0f0004000000000f0f0004f0f0f0f000000000f0a0f0a000000000f0f0f0f000000000f0a0f0aa0a0a0a000000000f0e0f0e000000000a0a0a0a000000000f0e0f0eb0b0b0b000000000b0b0b0b000000000b0b0b0b000000000a0a0a0a008000800000000000c000c000000000008000800000000000c000cf000f00000000000f000f00000000000f0c0f0c000000000f0c0f0c00000000000000000000000000000000f0f0f0f000000000f000f00f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000e0e0e0e00000000000000000000000000000000f0f0f0f000000000f0c0f0c
|0,10=>0xf0f0f0f0000000005050505000000000f0f0f0f0000000005000500c0c0c0c000000000f0f0f0f000000000c0c0c0c000000000f0c0f0c303030300000000030003000000000003030303000000000300030000f000f00000000000f000f00000000000f000f00000000000a000a0000f0f0000000000000f0f0000000000000a0a0000000000000a0af000f00000000000f040f04000000000f000f00000000000f040f04f050f05000000000f050f05000000000f050f05000000000f000f003030300000000000f0f0f000000000003030300000000000f0f0f00f0f0f0f000000000f0f0f0f0000000000000000000000000f0c0f0cf0f0f0f000000000f0f0f0f000000000c0f0c0f000000000c0c0c0cf000f00000000000f000f00000000000f0f0f0f000000000f0c0f0c5050505000000000505050500000000050405040000000005040504c0c0c00000000000c0c0c00000000000c0c0c00000000000c0c0c00f0f0f0f000000000c0c0c00000000000f0f0f0f000000000c0c0c00f0f0f00000000000f0f0f000000000000000000000000000f0f0f00f0f0f0f000000000f0f0f0f000000000c0c0c0c0000000000000000
|0,11=>0xf0f0f0f0000000000000000000000000f0f0f0f000000000f0a0f0aa0f0a0f000000000a0f0a0f000000000a0f0a0f000000000a0a0a0a00000000000000000000000000000000303030300000000030003000000000000000000302030200000000000000000000000003020302f0f0000000000000f0f0000000000000f0f0f0f000000000f0f0f00f0f0f0f000000000f0f0f0c000000000f0f0f0f000000000f0f0f0ca0a0e0e000000000a0a0e0e000000000a0a0e0e000000000a0a0e0ec0c0c0c000000000c000c00000000000c0c0c0c000000000c000c00303000000000000030f0000000000000303000000000000030f00000000c0c0000000000000c0c0000000000000c0c0000000000000c0cf000f0c000000000f000f0c000000000f000f0c000000000f000f0ca0a0a0a000000000a0a0a0a000000000f0e0f0e000000000f0e0f0e00e000e00000000000e000e00000000000e000e00000000000e000ef0f0f0f000000000f0f0000000000000f0f0f0f000000000f0f00000000000000000000f0c0f0c0000000000000000000000000f0c0f0c1010101000000000100010000000000010101010000000001000100
|0,12=>0xf0f0f0f000000000f000f0c000000000f0f0f0f000000000f000f0c0000000000000000000000000000000000f000f0000000000000000f0d0f0d000000000f0c0f0c000000000f0d0f0d000000000f0c0f0cf0f0000000000000f0f0404000000000f0f0000000000000f0f0404c0c0c0c000000000f0f0f0c000000000c0c0c0c000000000f0f0f0c3030303000000000303030000000000030303030000000003030300f0f0f0f0000000000000000000000000f0f0f0f000000000e0e0e0e0000000000000000505050500000000000000000000000005000500f050f05000000000f000f00000000000f050f05000000000f000f000000000000000000f0f0f0f0000000000000000000000000f000f0000000000000000003030300000000000000000000000000030303000000000000000000f0f0f000000000000000000000000000f0f0f00c0c0c0c000000000000000c000000000c0c0c0c000000000000000c2020202000000000a0a0a0a0000000002020202000000000a0a0a0af0f0f0f000000000f0f0f00000000000f0f0f0f000000000f0f0f005050505000000000505050000000000050505050000000005050500
|0,13=>0xf000f00000000000f0e0f0e000000000f000f00000000000f0e0f0ef0c0f0c000000000f0c0f0c0000000000000000000000000f0c0f0ca0a0a0a000000000a0a0a0a000000000f0f0f0f000000000f0a0f0a00300030000000000030003000000000003000300000000000000000000000000000000404040400000000000000000000000004040404000000000000000000000000000000000000000000000000e0e0e0ef0c0000000000000f0c0f0c000000000f0c0000000000000f0c0f0cf0f0f0f000000000f000f00000000000f030f03000000000f000f00202020200000000020a020a000000000202020200000000020a020af000f0f000000000f000f0f000000000f000f0a000000000f000f0af0f0f0f000000000f0f0f0f000000000f0e0f0e000000000f0e0f0ef0f0f000000000003030300000000000f0f0f00000000000303030000f000f000000000000000c00000000000f000f000000000000000c00f000f00000000000f000f00000000000f000f0000000000000000303030300000000030f030f00000000000000000000000000000000f0f0f0f0000000000000c0c000000000f0f0f0f0000000000000c0c
|0,14=>0xf030f00000000000f0f0f00000000000f030f00000000000f0f0f0000f000f0000000000000000000000000c0f0c0f000000000c0c0c0cf0f000f000000000f0f000c000000000f0f000f000000000f0f000c000000c000000000c0c0c0c000000000000000c000000000c0c0c0cf0f0f0f0000000000000000000000000f0f0f0f000000000f0c0f0cf0f0f0f000000000f0f0f0f000000000f030f03000000000f000f00f0f0000000000000f0f0f0c000000000f0f0000000000000f0f0f0cf0f0f0f000000000f0f0f0f000000000f0c0f0c000000000f0c0f0c0000000000000000000000000000000000300030000000000000000f0a0f0a0000000003020302000000000f0a0f0a0000000003020302a0e0a0e000000000a0e0a0e000000000a0e0a0e000000000a0e0a0ec0c0c0c0000000000040004000000000c0c0c0c0000000000040004f0f0000000000000f0f0000000000000000000000000000000f00005050505000000000505050500000000050505050000000004040404f0f0f0c000000000f0f0f0c000000000f0f0f0c000000000f0f0f0c00000000000000000000000000000000f0f0f0c000000000f0f0f0c
|0,15=>0xf030f03000000000f000f00000000000f030f03000000000f000f00f0f0f0f000000000f0f0f0f00000000050505050000000000000000000000000000000000c000c000000000000000000000000000c000c5050505000000000505050500000000050005000000000005000500000000f000000000000000c000000000000000f000000000000000cf0f0f0f000000000f0f0f0f000000000f050f05000000000f000f0000f000f00000000000f000c00000000000f000f00000000000f000cf000f0f000000000f000f0c000000000f000f0f000000000f000f0c0000000000000000000000000000000050505050000000004040404f0f0f0f000000000a0a0a0a000000000f0f0f0f000000000e0e0e0ef0f0c0c000000000f0f0000000000000f0f0c0c000000000f0f000000000000000000000000000000000000303030300000000000000000000f0f0000000000000f0c0000000000000f0f0000000000000f0cf0f0f0c000000000f0f0000000000000f0f0f0c000000000f0f00000000000000000000f0f0f0f0000000000000000000000000f0a0f0a3030000000000000f0f00000000000003030000000000000f0f0000
|1,0=>0xf0f0a0a000000000f0f0a0a000000000f0f0a0a000000000f0f0a0af0f0000000000000f0f0f0f000000000000000000000000000000008080808000000000c0c0c0c0000000008080808000000000c0c0c0c3000300000000000f000f000000000003000300000000000f000f0000f000000000000000f000000000000000f000000000000000f0000f030f030000000000000000000000000f030f030000000000000000b0b0000000000000b0b0000000000000b0b0000000000000b0b00000000f0f0000000000000f000000000000000f0f0000000000000f00f0f0f0f000000000f0f0c0c000000000f0f0f0f000000000f0f0c0c30303000000000003030300000000000303030000000000030303000000f0f0000000000000c0c0000000000000f0f0000000000000c0cf0f0000000000000f0f0000000000000f0f0f0f000000000f0f0000c080c08000000000c080c08000000000c080c08000000000c080c08f0f0f0f000000000f0f0f0f000000000f0f0000000000000f0f0000
|_,_=>0
def sP:Nat→Nat
|0=>0x302008130903c0008020381e22040102c210081800200b03c0c0004010060e0f81810040b03c3c0004010060e0307410040b0280c0c040702c0f0300010040181c0c00040101c0a0306810040c858300f0404014060482020110305c10040b02802150200c28060001026120502020110302410100781c0c05020381a060602c1406048200803038180a04018080200
|1=>0x1a85c00080803c0c17028200816078186808198581e0600020081607818640802058620618020082f0b03c0c08080b81e06000202013118280008020581e06028b4080e078a85808080ac1e0600020081605018120802058240f15020201b108180008020a42c280302008130708c1408080581411030200816088182e08130581e060002008250b0440c08020902c0f
|2=>0x2020160790c000802100140604010260e078040a100d83c0c0021010820e050181004200280c1704040263d078001004129001406040402c1103020083e0b03c0c080204c1c3d0782008031e0280c08020581e011d8000803070340c051d0581e060002072130781800080803c0c17000200816050187008020381e061b820200f0381800081b0102c0f030002006
|3=>0xd83c0c00280102c23278001010200280c080804c4628000209c1b078180008020589a0600020200a0305c4e080803c0c4c00020084b0781800080806c1e06000c0084a0b0280c08020381e06060200816088181208020581e01000540816078180049020581e070301408480b0280c0802058040f0080008162381800080204c1c0f2302008450703c54080803c0c44
|4=>0x28102c0f031800008020381e062f8200803070280c080803cbc0600020081603174000802058460a00814200f03170000802058b60f0080008480b0440c08020581e5a00020b21607818000805900140604010800a03024100401838ae06040101e062b00010040b0280c15040401e062a80010100d818a800040102c06298147e0401838a406041440816078180010
|5=>0x305c0008020581e063580010040b03c0c6a0002008190b08c1e00040102c0f031a40008020581e06029a0080e0b03c0c30040102c1f07818ce0802038140f0305c10100b08c1406000200816118182e00040102c66078180008020581e6300800b00432858460f00020081607818c80004010063c078180008020382c0f0318810040b03c0c0030820081b0b0281e06
|6=>0x401036161183c0200020902c0f0302008410703c0c00040102c23151cc0008020581e720300010100b0a00c3f040102c0f031c40008020581e5e0300010100b03c0c0018020200a078182e00040100616380180008378382c0f030001004070581e012c020201307818dc00040402c0f03000c408021b42c0f0300010040b08c1e061a02008163603c0c00040104a0f
|7=>0xb03c0c7d00020087c0b08c0c00040102c7b078180a08020582206040102c0f031e800080200c2c0a030141004098581e061a020083c0b0341e0600010f216078180008020382c5207818100409858f00f0002008770d83c0c00040102c0f03000ec08020581e06000b410040b1d41e0600020081b0b07c1e0600010800f030001004018381e061f820081607818e800
|8=>0x20081607804fe000401006164601800080200c2c8a03000100444858460f00020083c0b03c0c00040101c1607818a008080581e88030001004018381e064102008870b03c0c00040102c86078180008020581e064280010100b1481e060002008840b03c0c00040101c164183c0c08408581e06000200816078050000040102c23051fc00080200c2c7b030001004
|9=>0xb03c0c940002008930b03c0206000402c0f03000a0080200d240f0300010040185846010002008162903c0c05000102c910781800080205814060d00010040183814060002020164183c0c00040108a16078040008021142c280300010040b0c41e060282008163d83c0c00040112016078180008020382c3d07818108e0781800080200c2c0a030001004468581e06
|10=>0x300010040b03c0c9f000200816078193c00041382c0f0300010040b2701e060002136130b03c0c00040402c0f030147e080200c1c23030001004070581e064d020081b0b2641e06002602616078180008020581e061d80010100b0f41e060002008970b08c1e00040112c1607818000808058ae0f0300010040b03c0c34040102c0f03014fc08020581e95030001004
|11=>0x781800080229c2c0f0300010040b0281e06210202040078180008020580c540280010040b2981e060002008a50b03c0c00040401e060b8001004120581e06000200816078194800040402c0f510180008020f02c210300010100d83c0c05002842c0f0300010040183c0c17000200824018581e06040402c0f0300140040186c1e060280008160788800080200c1c0d
|12=>0x40104a16078180a08020587a0f3f80010b2022c42c0f03020080e0b0280c35040102c0f032c00008020581e0657800109b0b03c0c00040115c16078180008020581e2a1600010040b03c0cad02820081607819580004010ee160503c0c08018581e065580010980b03c0c0004010260e078180a08020382c0f230181004550581e060002008a90b03c0c00040415016
|13=>0x21001406040102c0f032f40008020581e065e00010bb0b03c0c00040102c0f030002a085d0102c0f03000100407059180f0302008162b818e600040402c0a030d40008020580c350b8001004070581eb9000202c0f032dc000802058040f0300010045a8381e0600020080e0b03c0c7f040116816078180008020942c061a80010040b03c54b30002008130703c0200
|14=>0xb03cc601000102c0f0332000080200d8e0f03000100b2003c0c00040102cc6078040c00020581e066280010100b03c0cc30002020160503c0c0004010060e318180008080581ec200020080e0b07c1e06040102c0f600001004070581e060e8202013078a00c00040117e16078180008020581e070300010040b03d7c060002008250b03c0c00040100616078186808
|15=>0x33500008022c42c0f0322c10040b03c0cd3000200816078040c00690102c70078a8000802058460f0081400040b03c0c00688119e1607818000802058140f0333810040b0280c5f040100616068180a00023342c0f0300010040b03c9e06000219816078180008658102c0f0300010040b0280cb3000200816078199400040102cc9078180008020581e06001240813
|16=>0x300010040b018fe730002008130703c5408021f01c0f0300010040b08c1e46000200816078188800040102c0f03001b8080200c2c066d80010040d8581e060010808190b03c0c05040412e1307818000802059b40f0300010046c8581e06000211c16078180008023602c0f0300010040b03dae00043582c0f0300010046a8581e060002008030d8280c00040402c0f
|17=>0x20581e067300010cb080581e060002008250b0280c2704010361607818003002058140f008180a100b03c0cc500020081607b945400040102c0f0339000080b03c0ce300020081607819c4000438008030b03c0c00080101e060b80010046f8581e060002008030b08c5400040103216078a00c080804c1e2a0002008130b1c01e0004011bc16078180008023742c0f
|18=>0x7818000802059dc0f0300010ed020581e060002008400b0280c08080581a0f0301400100b03dd8060002008130b08c5000042a02c0f0300010040b08c14060282008eb0b03c0c0004011d416078180008748102c0f0300010041e058140f0302008162d83c0c0004040781b078180008020581e060039c10040b2301e01030000816050182e27040102c0f030001808
|19=>0x7818000808058140613820081607819f20004011f0160781800080204c2c990780010160503c0cab000200816050440c08020581e067b80010040b3d81e0600020081b0b018a8000402c2c0f030001004228902c0f03020081b0b03c0c00280402c0f03001e8080200d8c0f0300010040b03c0cf300020201b0503c0c00043c82c0f030001004788581e0600021de16
|20=>0x78186a00040102c0f030147e08020581e0600348100422858460f030001004070581e067e80010100d83c0c00040102c3d078180008020581e067e00010040b15c1e0600020081607ae400080200c360f030001004740581e060002008160781800500401036161183c0c00040101c16078180a0004010060e0501810040b03c0cfb00020081607a200c0004011f416
|21=>0x4010061607818005804010800f0300010100b03d4606000216404018581e0600020081607c040c00040101c1607818b008020581e06002681004070581e280300010c1020581e060002008410b03c0c00040102c0f0300140040b08c140f030001100020382c0f0300010047f8581e060002008160f8281e060002008160781800fe040100616078040c00040101c16
|22=>0x40102c0a078180a08083102c0f0300010e10200c2c0f0300010041e0581e06000200816078190000040102c0f230180008022c42c0f0300010040b03c0d040002008130b0281e0600021ea160781800080b03c0cab0002008160503c0d0300020081b0b0341e06000108a130b03c0c00040402c0f03000b008020581a0f150180008020581e010301401020b03c0c00
|23=>0x7b940c0004010061606818000802058620f0300010040b0281e0600020081607b08000802059140f0300010040b264460f0300010040185846060002008160503c0c170002008130b0341e0600020081607818fe0004010261607818dc00040102c0f03000be08020942c0a07818000802058f60f0300010040b0280c350002008030b0280c00040112e0e0b03c0c00
|24=>0x20810040b03c0c053382008b50b03c0c000441408160503c0c00040102c0f0340c00080204c2c0f008001016078191e00040101c16078190408021943616078180008080581e06000fc10040b03c0c6e0002008160798c540600020081607818a600040102c0f03000fc08020581e060e8001004070581e061f82008160683c0c003382008030b03c0c00458200816
|25=>0xb03c0c00840202016078a80c00040100616078a80c0004010801607818000808058140f0300010040b03c0c170002008160798c0c003382008161183c0c050002008030b0281e0600020081b0b03c0c05000102c1f078180a00040104a160781800080211406160781800080204c2c0f3181800080b03e0e060002008160781a0c00040112416078180008080581e06
|26=>0xb03c0c0086010060e078180008020382c23078180008020581f0b030001004638581e06000202016078180027040102c0a031cc000802058140f008180008020940616078180008024281e060002008160781800f4040102616078a00c0004010ca160781800080b08c1e06848001105020581e060002008160683c0c0500058140f03424000808058460f030001004
|27=>0x2058460f0300010040b03c54060002008160503c0c00040103616078180008020581e060020810040b03c0c7300020081607818003f040102c0f030011608080102c0f0300010040b03c0c2c0002008160798c0c002c0200816078040058040102c28030fc101002058140f0300010040b0280c27040102c0a2903c0c00043c02c0f0300010044b84c2c0f030001004
|28=>0x816078180008590102c0f0300010040b03c0206000202c0f034240008080581e060002008030b03c0c00040102c0f318180008020581e06000200816078180027044340816078180008
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x32502d50285023501e50195014500f500a500550005
|5,0=>0x1ae61a861a2619c61966190618a6184617e61786173516d61676161615b6155614f614a5144613e61386132612c61266120611a6114610e6108610260fc60f660f060ea60e460de60d860d260cc60c660c060ba60b460ae60a860a2609c60966090608a6084607e60786073506d60676061605b6055604f60496043603d60376
|5,1=>0x26c62666260625a6254624e62486242623c62375231622b6225621f62196213620d6207620161fb61f561f051ea61e461de61d861d261cc61c661c061ba61b46
|6,0=>0x423741c7416640f7408740173fa73f373ec73e753e073d973d273cb73c473bd73b673af73a873a1739a7393738d6386737f73787372636b7364735d7357635073497342733b7334732d7326731f73187311730a730372fc72f572ee72e772e072da62d372cc72c572be72b772b072a972a2729b7294728d7286727f727872726
|6,1=>0x5da75d375cd65c675bf75b875b175ab65a5659e75977591658a7584657d7576756f75696562755b7554754d7546753f75387531752a7523751c7515750f6508750174fa74f374ec74e574de74d774d074c974c274bb74b474ad74a6749f74987491748c5485747e7477747074697462745b7454744d7446743f74387431742a7
|6,2=>0x78f77887782677b7774776d7767676077597752774b7744773e67377731672a7723771c7715770e7707770076fb56f476ed76e766e076d976d276cb76c476bd76b676b066a976a2769b7694768d7686767f76787671766a7663765c7655764f66487641763a7633762c7625761f66187611760a760375fc75f575ee75e865e17
|6,3=>0x946793f79387931792a7923791c7915790e7907790078f978f278eb78e478dd78d678cf78c878c268bb78b478ad78a6789f78987892688b7884787d7876787068697862785b7854784d7846783f78387831782a7824681d78176811680a780377fc77f577ee77e777e077d977d367cc77c577bf67b877b177aa77a4679d77967
|6,4=>0xa116a0a7a0379fc79f669ef79e879e179da79d469cd79c679bf79b969b279ab79a4799d7996798f79896982797c6975796e79686961795a7953794d6
|7,0=>0xbe06bd97bd18bca7bc28bba8bb37bab8ba47b9c8b957b8e7b877b7f8b787b717b698b627b5b7b547b4d7b467b3e8b386b326b2a8b237b1b8b147b0c8b057aff6af78af16aea7ae28adb7ad47acd7ac58abe7ab77ab16aa98aa18a9a7a928a8b7a838a7b8a747a6d7a658a5d8a576a507a497a427a3c6a357a2e7a277a1f8a178
|7,1=>0xdab7da56d9d8d976d8f8d896d818d7b6d747d6c8d657d5e7d577d507d488d408d3a6d337d2b8d247d1d7d167d0f7d087d017cfa7cf37ceb8ce47cdd7cd67cce8cc68cbe8cb77caf8ca87ca08c988c926c8b7c847c7d7c767c6f7c678c607c597c536c4c7c448c3d7c367c2e8c277c207c197c127c0a8c028bfb7bf47bed7be67
|7,2=>0xdba7db28
|8,0=>0xe357e2e7e286e226e1b7e147e0e6e077e007df97df27deb7de47ddd7dd67dcf7dc87dc17
|9,0=>0xe3c6
|_,_=>0
def wAt:=mkWire dB 270 220 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 9 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x140fd078030780207801021010b09d078002002a07801078002c03d0001b0b09d0780102059078001289f07800078010181400021140fd07803078020509f0780107800030150b001000210b03d018000b00100021050190003d078000780102059140fd0780307802078a9000190b0010b00109814000210d828078010b89f07800078010708c0509f07801078000708c078190680107821018140d82807801
|1=>0xb0a10003e0799d0b002140fd0780307802228000983d0b0010408e078190b0190d8020b0210003507821018000b03d0b00107802228030983d0b0d50b001030010d83f0205907803078020d88e0b021078013181907823020d50781b0983e228000b08d078010d800000210b0210283f000210b02a0780107801020590b02a078010b0050b0150018f07823018000b03d0b001000a10003e078190780100021
|2=>0x210083d04019021b90983e1180107819018030b03d2c03d0001b228000983d018020b03d0283f0b18d078230b0010b03d078190283d079190b03d0003d07a09000230b08d078190983d1180307819078a9000190b23d0200403021000a10b03d0003e0501b0003d0018d078230b03d07a2d020020b0191f8210780208028078010b03d0502307801021dd0b209000230701b0b0010003d3f03d018020b03d
|3=>0xb2d90501b078010b08e0b0010b0290003d078a9018030b03d021bb0983e0b0190703f0b0010b11a0200604019021b90983e0b001000210b0010080103021000190809f078000b002020590b09d078001e03f0b0150b02a07801518010803c0b02100021020590820b00023020590003d22803018190205913821078000317d018000b03d0b0013f8210003d0b2750220b00023021bb0983e0003f020590281b
|4=>0xb341002d9018000b03d0003d078ab000190b08e001e1118232f821018000b03d0403e0b03d021010b09d078000d8030b0210802b078016203e08003078fd07802020590b0011381a020590003c00035078216081b02039000d50781b020590003e00225098230d828078010b0162280001819078010b09d078000b0010224907023118140b02931801078235b0190203e022e30703c0b0010d88c078190b001
|5=>0x7801018140b03d000210b0190780007801078160002107801000210802b07801030010b03e0c83e098030224b070230b001708230200d0b02a0780111803078190b03d000190b01902059318190403e01a0b0b03d490190b0010b001000190b0190703e0b00100801043390d8020b021098030b019020590288e000210b23d02004030215c01a0703c02006030210b2650b016000210001907823042e30703c
|6=>0xb0210d83d0b0211f82107802078190b0210b001000210b0010b03d0003d080280780107801020590780002029078010202a078010b0190083d04019020060509f078010780005007078011e03f0d8017a8590209d078000983d1f82107802000370d80307801020590217d01800780590209f07800078010b09d07800020590b0190809f0205907800078010002107819018030b001740020018d0782307800
|7=>0x983d0b0190001b020590782100019000210302102209000230b03d0001b0b09d078000803c020590b03d020010983c0b0190b0010001b0281b000210b0010003e020390b0010b0d50781b138210780007801078190b001020210b0fd07802078012c0210001b0b03d040190b0010781b00021078020b016000210b08d078190703e0b0010b02102059078a9000190d81b0b0212c03d0001b5b0190203e0b03d
|8=>0xb001078020403d0b0020b03d02002031cd0b03e0b03d078211180307819078011381a0003c07a2d0200211821078190b03d078190b02a078010403d0b0190501b0003d0983e0b019018000b03d078013383d0b0020003d0781b0b03d0003d070190b0010003d0002108003020590200d0b03d0d8010b0210701b0b0010080103021018030b03d0803f020590003d0209d07800020060302107801078210b021
|9=>0x2059398020b03e00019020590b03d000190b09d0780007801020590b02a078010403e0b00200021078190b03d0003d000210b0210283d000210b02907801018190b03d0403e0b019020d70781b0203a0b001070230b0010002302059000210b0020b2d90203e078010202a078010b0190401902004030210b001000230d8190b02107802020590983e0b01907823000190d83f0b021018020b03d000d50781b
|10=>0xb03d0782307800020190781900019078010b021000230b03e0780202002020590983f0b01903002078230001b04019078030780207801078010780005023078010209f07800098010b01945822020020b0010b03d0b001078192c03e0001b0b1610001b0205907800078010b03e07801018010b03d0b09f0780000037078210003e0b0190b00503021078190205b02029078010002107821078010205b07819
|11=>0x2001030210205b02059
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x2530000000088c211000000008041e2000000000001c20688164000014204c4000048400000000000000102038800000000000000000000000000000000000000000000002cc0a100000000000073000000000000000148000000000000c8000000002100000020000000
|5,1=>0x10cc000000040300000000f4c00000003940d8c3420000000000000000000000000000000030400000000000000000000000002d30ac8283
|6,0=>0x218c84220c480300007e21f0879300000001dc876100000001ccc712000000000006f21b486b200000001a486721984651188c602000000017c45d216c800016840000000582000057100000000000000150c522000050213884c2000000012c4000128448200000000000462
|6,1=>0x37080000000da20000d73350cd313448ce30000cb332840003208c530000c3230480002fc8bd22ec80002e480002dc8b522cc8b122c040002b880002b44ab22a84a910000a722948a322884a02000000027889b3260c0002588942244c90100008e22308000000000022c4892
|6,2=>0x13624ccd32100013114b8d2c24a89282494d241484d1f247491b246491724549141000112243cd0e100010c242c50a14208000000000041890334048ff23f480000000fc13ec4f923e04f6200000000000f3300000003c48f010000ee23b08ea239cce610000e420000e31380cde2
|6,3=>0x618c00000018516104000000183160497f25f0d7b100017925dc97525cc97125bc96c300016a25a096625944000588d60257895c2000159355c9561000000000015335449501538800052cc0005249472518400000000000001442508800050093e200013b3000000000013920001381
|6,4=>0x6d0c0006c880006bcdad26ac9a8369c5a43688800068099d367059a2664598100019626508000644c00000018e363440006305893
|7,0=>0x8c4a2f28b4a2b28a4a272894a232884a201878a1c2868a182858a142848a102838a0c2828a08281c605280ca0218009fe27f09fa27e09f627d09f227c09ee27b09ea27a09e627909e227809de27709da27645d727549d327449cf27349cb27249c727149c327049bf26f49bb26e49b72
|7,1=>0xab4aab2aa86a82a98aa42a88aa02a78a9c2a68a982a58a942a4c6912a3ca8d2a2ca892a1ca852a0ca8129fca7d29eca7929dca7529cca7129bca6d29aca69299ca65298ca61297ca5d296ca59295ca561950a522940a4e2930a4a2920a462910a422900a3e28f0a3a28e0a3628d0a331
|7,2=>0xac4aaf2
|8,0=>0xb0c6c21b046c01afc6be10002bd1af06bb1ae86b91ae06b71ad86b51ad06b31
|_,_=>0
def PO:=mkPO wAt oP oO 20 9 511 14
def pmP:Nat→Nat
|0=>0x90c0002190000820000201000080000015a000050800011100004400001030000408000100000028000008000001e000005a000012c00004200001000000220000060000015000004c000011000004000000a0000020000005000000c0000020000004000000
|1=>0x4d0c0013020004c040012d200048280011a000045680011580004488001102000400c00100200024040008000001f5c00075b000185400060d0001814000600000144c000418000100c0003fb0000f6c0003cb0000f0c0003630000c440003080000bec0002db
|2=>0x20020008005002001000800200143080046d30011a440044000010fac00420f00108280042040010000003811000c4c8003122000c428003102000c088003012000c000002813000898c00210200080880020100004fec0013db0004f4c0013cb0004e6400135b
|3=>0x8200002008000800040192050055f6c0157c3005496c0146c7004cd4c013243004c84c0118030044f6c0113730044d4c011343004496c011253004408c011003004090801021200404000100020021000008301002082c0082090020808008201002003000800a
|4=>0x4a297c12825b042201c10200003103080b036b02c0d2c0a925302a490c0a881302a0d4c0a034b028096c0900c002401080852d30204f6c08135b0204d4c08134302048480800c2020030008001a020000806000200a285c0222530085d4c021653008404c020a53
|5=>0x16a092c5882431400ca850030a14009ac50024b13c0d0c4e124312c5b0c4b13c312c4b4c4b02c312a090c49125b1204f4c4812d3120496c42825f100892c40032a100000031125308a597c22865b086492c21135b0844d6420320208040082003080800820200200
|6=>0x24806d34200108820753208194c8203db2080d8c80820d2004444800921200208c8003db200004470224b1c0490c62965d1814d2460024b
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x1500002d0000020000110202000000000000000000190000000000000002020200000002000003070000130400000002021000020500050000000002020000000000000000000000000002070000000200000000020000000200000500060000
|6,0=>0xd00006800be8b0c021a006c0500013c00011b0002607d0002000102091b670001000554a0670034021b071b0000025934001b02345f00020e0000005d0200006a2c013400011b200000010500006234000000023a15005f0217145d39010000020202007f000001004700003200a302003408010000610005020000004c
|6,1=>0x1c00005305009c53010255140002022e0217296b00020d020700965c1b1b0081152a000000341b4601005a0002875d0000000001172a020d00340000007e000700016d5e004b38010e8615140f020202080106670002215300020b5802000000020e0669020000070a1bc50d0000001600001b67000202010312000e0005381b
|6,2=>0x500002001a8787630727670002880702ab05001d02001000002805001410
|7,0=>0x7c448a2722405290500942768e4f2f4d4379189f31b4c17a95449809458c3f3e1e37c3a249c76630b4adafaa9a92b6855a759d8d2723ba6e27513b5bc6acce3f42b1cacb3664833372477141374ac1b89bc484a924b9088f9389bcc8971ec2b2354494912774a84eb72844c9cf77a1a7562ba5c0c748bfcd9e7099bdbba665a4
|7,1=>0x803d
|8,0=>0xb5ae78b357253f44d0cc827bba6f2673b0b4
|9,0=>0x1f
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 26 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_218 7 roots_218 ops++addP pm 1 dom_211 7 roots_211 ops++addP pm 2 dom_74 4 roots_74 ops++addP pm 3 dom_89 5 roots_89 ops++addP pm 4 dom_154 5 roots_154 ops++addP pm 5 dom_209 4 roots_209 ops++addP pm 6 dom_203 7 roots_203 ops++addP pm 7 dom_201 5 roots_201 ops++addP pm 8 dom_217 6 roots_217 ops++addP pm 9 dom_91 7 roots_91 ops++addP pm 10 dom_138 4 roots_138 ops++addP pm 11 dom_210 4 roots_210 ops++addP pm 12 dom_155 6 roots_155 ops++addP pm 13 dom_147 4 roots_147 ops++addP pm 14 dom_73 4 roots_73 ops++addP pm 15 dzo_74_16 4 roots_74 ops++addP pm 16 dom_139 5 roots_139 ops++addP pm 17 dzo_202_16 5 roots_202 ops++addP pm 18 dom_195 4 roots_195 ops++addP pm 19 dzo_203_16 6 roots_203 ops++addP pm 20 dom_83 4 roots_83 ops++addP pm 21 dom_27 4 roots_27 ops++addP pm 22 dzo_75_16 5 roots_75 ops++addP pm 23 dom_216 4 roots_216 ops++addP pm 24 dom_75 5 roots_75 ops++addP pm 25 dom_202 5 roots_202 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_219 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_209 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_201 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_138 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_74_16_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_202_16_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_195 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_zo_203_16_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_zo_75_16_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_216 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_202 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_218 7 s (0,roots_218.map (·&&&dom_218)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_219 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_218 h
def symsG:List (List (Nat×Nat)):=[[(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_219==dom_219)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_219 gM v ys):RunD true dom_219 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_219 gM mpG SD SS NN hAt idxH ori 0 mkPools s
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
def dzo_217_4:=0x30303030000000003030303000000000303030300000000030303030
def gzo_217_4:=0x30303030000000003030303000000000303030200000000030302000
def gsh_217_4:=0x3030303000000000303030300000000030303020000000003030200
theorem lowS_zo_217_4_73:Lower true dzo_217_4 roots_217 gzo_217_4 6:=lower_iso_b (d1:=dom_217) (r1:=roots_217) (T1:=gsh_217_4) [(dom_217,4)] (by decide +kernel) (lower_slice_b (T:=gsh_217_4) [(0x3030000000000000303000000000000030300000000000003030000,0,16),(0x3030303000000000303030300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_73)
namespace S_221
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(4,20),(4,132),(5,13),(5,21),(5,69),(5,133),(8,9),(8,72),(8,136),(12,13),(12,28),(12,76),(12,140),(16,17),(16,20),(16,144),(24,25),(24,28),(24,88),(24,152),(64,65),(64,72),(68,69),(68,76),(68,84),(68,196),(80,81),(80,84),(80,88),(80,208),(128,132),(128,136),(128,144),(129,133),(129,137),(129,145),(129,193),(192,193),(192,196),(192,200),(192,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_221.map (·&&&dom_221)
def gM:=goal_221&&&dom_221
def NN:Nat→Nat
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|8,0=>0x7369e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcccc000000000000cccc000000000000cccc000000000000cccc00033003300000000003300330000000000330033000000000033003300c0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c22222222000000002222222200000000222222220000000022222222cccccccc000000000000000000000000cccccccc00000000000000033333333000000003333333300000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x2c688
|_=>0
def sO:Nat→Nat→Nat
|8,0=>6
|_,_=>0
def wAt:=mkWire dB 6 222 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 7
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def pmP:Nat→Nat
|0=>0x3f80
|_=>0
def pmB:Nat→Nat→Nat
|8,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 1 (j%128);fld (pmP (k/32)) 7 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_220 7 roots_220 ops++addP pm 1 dom_93 7 roots_93 ops++addP pm 2 dom_213 7 roots_213 ops++addP pm 3 dom_205 7 roots_205 ops++addP pm 4 dom_217 6 roots_217 ops++addP pm 5 dzo_217_4 6 roots_217 ops++addP pm 6 dom_157 6 roots_157 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_221 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_zo_217_4_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_157 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_220 7 s (0,roots_220.map (·&&&dom_220)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_221 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_220 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff0000ffff0000ffff0000,112),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_221==dom_221)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_221 gM v ys):RunD true dom_221 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_221 gM mpG SD SS NN hAt idxH ori 0 mkPools s
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
  · simp [NN] at hi
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
def dzo_148_64:=0x110011000000000000000000000000001100110000000000000000
def gzo_148_64:=0x110010000000000000000000000000001000000000000000000000
def gsh_148_64:=0x11001000000000000000000000000000100000
theorem lowS_zo_148_64_148:Lower true dzo_148_64 roots_148 gzo_148_64 4:=lower_iso_b (d1:=dom_148) (r1:=roots_148) (T1:=gsh_148_64) [(dom_148,64)] (by decide +kernel) (lower_slice_b (T:=gsh_148_64) [] (by decide +kernel) lowS_148)
def dzo_156_64:=0x11111111000000000000000000000000111111110000000000000000
def gzo_156_64:=0x11111110000000000000000000000000111011000000000000000000
def gsh_156_64:=0x1111111000000000000000000000000011101100
theorem lowS_zo_156_64_148:Lower true dzo_156_64 roots_156 gzo_156_64 5:=lower_iso_b (d1:=dom_156) (r1:=roots_156) (T1:=gsh_156_64) [(dom_156,64)] (by decide +kernel) (lower_slice_b (T:=gsh_156_64) [(0x1100110000000000000000000000000011001100,0,8)] (by decide +kernel) lowS_148)
def dzo_158_64:=0x55555555000000000000000000000000555555550000000000000000
def gzo_158_64:=0x55555554000000000000000000000000555455440000000000000000
def gsh_158_64:=0x5555555400000000000000000000000055545544
theorem lowS_zo_158_64_148:Lower true dzo_158_64 roots_158 gzo_158_64 6:=lower_iso_b (d1:=dom_158) (r1:=roots_158) (T1:=gsh_158_64) [(dom_158,64)] (by decide +kernel) (lower_slice_b (T:=gsh_158_64) [(0x4444444400000000000000000000000044444444,0,2),(0x5500550000000000000000000000000055005500,0,8)] (by decide +kernel) lowS_148)
def dzo_218_4:=0x50505050000000005050505000000000505050500000000050505050
def gzo_218_4:=0x50505050000000005050505000000000505050400000000050504000
def gsh_218_4:=0x5050505000000000505050500000000050505040000000005050400
theorem lowS_zo_218_4_74:Lower true dzo_218_4 roots_218 gzo_218_4 6:=lower_iso_b (d1:=dom_218) (r1:=roots_218) (T1:=gsh_218_4) [(dom_218,4)] (by decide +kernel) (lower_slice_b (T:=gsh_218_4) [(0x5050000000000000505000000000000050500000000000005050000,0,16),(0x5050505000000000505050500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_74)
def dzo_90_4:=0x505050500000000050505050
def gzo_90_4:=0x505050400000000050504000
def gsh_90_4:=0x50505040000000005050400
theorem lowS_zo_90_4_74:Lower true dzo_90_4 roots_90 gzo_90_4 5:=lower_iso_b (d1:=dom_90) (r1:=roots_90) (T1:=gsh_90_4) [(dom_90,4)] (by decide +kernel) (lower_slice_b (T:=gsh_90_4) [(0x50500000000000005050000,0,16)] (by decide +kernel) lowS_74)
def dzo_78_16:=0x555500000000000055550000
def gzo_78_16:=0x555400000000000054500000
def gsh_78_16:=0x55540000000000005450
theorem lowS_zo_78_16_74:Lower true dzo_78_16 roots_78 gzo_78_16 5:=lower_iso_b (d1:=dom_78) (r1:=roots_78) (T1:=gsh_78_16) [(dom_78,16)] (by decide +kernel) (lower_slice_b (T:=gsh_78_16) [(0x50500000000000005050,0,4)] (by decide +kernel) lowS_74)
def dzo_202_4:=0x5050000000000000505000000000000050500000000000005050
def gzo_202_4:=0x5050000000000000505000000000000050400000000000004000
def gsh_202_4:=0x505000000000000050500000000000005040000000000000400
theorem lowS_zo_202_4_74:Lower true dzo_202_4 roots_202 gzo_202_4 5:=lower_iso_b (d1:=dom_202) (r1:=roots_202) (T1:=gsh_202_4) [(dom_202,4)] (by decide +kernel) (lower_slice_b (T:=gsh_202_4) [(0x505000000000000050500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_74)
def dzo_206_16:=0x55550000000000005555000000000000555500000000000055550000
def gzo_206_16:=0x55550000000000005555000000000000555400000000000054500000
def gsh_206_16:=0x5555000000000000555500000000000055540000000000005450
theorem lowS_zo_206_16_74:Lower true dzo_206_16 roots_206 gzo_206_16 6:=lower_iso_b (d1:=dom_206) (r1:=roots_206) (T1:=gsh_206_16) [(dom_206,16)] (by decide +kernel) (lower_slice_b (T:=gsh_206_16) [(0x5050000000000000505000000000000050500000000000005050,0,4),(0x5555000000000000555500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_74)
def dzo_150_64:=0x550055000000000000000000000000005500550000000000000000
def gzo_150_64:=0x550054000000000000000000000000005400440000000000000000
def gsh_150_64:=0x55005400000000000000000000000000540044
theorem lowS_zo_150_64_148:Lower true dzo_150_64 roots_150 gzo_150_64 5:=lower_iso_b (d1:=dom_150) (r1:=roots_150) (T1:=gsh_150_64) [(dom_150,64)] (by decide +kernel) (lower_slice_b (T:=gsh_150_64) [(0x44004400000000000000000000000000440044,0,2)] (by decide +kernel) lowS_148)
namespace S_222
def pG:List (Nat×Nat):=[(2,10),(2,66),(2,130),(4,20),(4,132),(6,14),(6,22),(6,70),(6,134),(8,10),(8,72),(8,136),(12,14),(12,28),(12,76),(12,140),(16,20),(16,144),(18,22),(18,26),(18,82),(18,146),(24,26),(24,28),(24,88),(24,152),(64,66),(64,72),(68,70),(68,76),(68,84),(68,196),(80,82),(80,84),(80,88),(80,208),(128,130),(128,132),(128,136),(128,144),(192,194),(192,196),(192,200),(192,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_222.map (·&&&dom_222)
def gM:=goal_222&&&dom_222
def NN:Nat→Nat
|5=>4
|6=>15
|7=>24
|8=>8
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0xf478558f0f1d8081b958
|6,0=>0x8513670afa60b5f5a8fc5a769509224c44b3d55f357881b33619af30a0a50740c0616405821
|7,0=>0xf6239e20ebd2150bf304b2c79aa6759b7cf873f286a0a7afa873f636be6c62224504963b278337993163029be2291a826e2d258ed23a3d159be12950
|8,0=>0x78bdf68c443d86d35cd331c332b37d2426a050df
|9,0=>0xbad5e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaa88aa8800000000aa88aa8800000000aa88aa8800000000aa88aa8801100154000000000110015400000000011001100000000001100112aaaaaaa800000002aaaaaaa800000002a802a80000000002a802a80555555550000000055555555000000004444444400000000444444442222222200000000222222220000000022002200000000002200220001540154000000000154015400000000011001100000000001100112aaaaaaa8000000000000000000000002aaaaaaa800000000000000005050505000000005545554500000000000000000000000055445544a0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0a141414140000000014141414000000001414000000000000141400002aaa8000000000002aaa8000000000002aaa8000000000002aaa800000000000000000005544554400000000000000000000000055445544aa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa0111111110000000011111111000000001111111100000000111111110282828280000000028282828000000002828000000000000282800055555555000000005555555500000000000000000000000000000000
|0,1=>0xaa00aa0000000000aa00aa00000000000000000000000000000001555555540000000001540154000000015555555400000000000000008888888800000000888888880000000000000000000000000000000555555550000000055555555000000005555555500000000000000000a0a0a0a000000000a0a0a0a0000000000000000000000000000000155555554000000015555555400000001555400000000000155540002aaaa828000000002aaaa828000000002aaaa828000000002aaaa82855550000000000005555000000000000505000000000000050500000aaaaaaaa00000000aaaaaaaa000000000000000000000000aa88aa89555555540000000155555554000000014141414000000001414141400002aaa8000000000002aaa8000000000002828000000000000282844445555000000004444555500000000444444440000000044444444aa88aaaa00000000aa88aaaa00000000aa88aa8800000000aa88aa89555555540000000155555554000000015511551000000001551155100002aaa8000000000002aaa8000000000000000000000000000000055005555000000005500555500000000550055000000000055005500
|0,2=>0x151515150000000015151515000000001515151500000000151515150008800880000000000880088000000000000000000000000000000055555555000000000000555500000000555555550000000000000000aaa8aaa800000000aaa8aaa800000000aaa8aaa800000000aaa8aaa95555111000000001555511100000000155551110000000015555111002a802200000000002a802200000000002a802200000000002a802244554455000000004455445500000000444444440000000044444444
|_,_=>0
def sP:Nat→Nat
|0=>0x6c53cd1cb2406851031c20191440c70803c31d80890055c31c200f0c709524014f3473091530c70890051031c20111431cc2c90054831cb24014f4070890053cd1cc2401431c23890053473022891472ca2401480c70801440c60801440c2040
|1=>0x4831c22401520c73022401431c29001630c70890050c70a124014d0c708b2401431cc09c1431c271d1431e00890053431cc0891431c278014d0c70897450c708b2401431d40890050c730270014318224014308124014f0c73090053c31c2240
|2=>0x50c708901a1431c22406450c70890050c70890111431c27001431c22407c50e61c224014f0c70890053431c224014d0c73022406853c31c22406453c31c22401431c22409451031c2005
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x9303180cc006
|6,0=>0x1e1ce2e6a731b9758ace50624b909c76e34716b899c3ee187
|7,0=>0x8f445a21d107780b3e9de50ec672bb79dad0d0665330dd78eb6657baa1d42e9a74a323990ee7f8
|8,0=>0xab3d3de90f4269dbcd1e5af267
|9,0=>0x15d6
|_,_=>0
def wAt:=mkWire dB 39 223 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1424d0b0c042012404901080827d0c082010c0497d0c083010808d0b0c0424514082012405a1c1405a1f14042010c243091c082360c04f270c24f270c256141c043090c256171c043090c042010c2435109145021408f270c24d0b0804301482cf010c2434514083010804309303c201
|1=>0x501147450224043021c243090c042010c045010c243091474f020c24f270c24f010c24c0d08049451408f1d0c2438a
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x848f91d2346644b193320634c518730a408c00002
|7,0=>0xa253ca694b29251ca29432824fc9e93b2724dc9a9332624bc9692b25249c929232
|8,0=>0xb43646c0d71ac3546a0d31
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0x58f2085e40d9981b31034f6067fc0cbf8197b032f2064c40c3d80461006e6009ec01198020300266004c80088000fd00100001e4002000032000460008400100000c000100000c000100000
|1=>0x1087fe0cffb317960452631e4983c91179108c2167fc16bc82c7b
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x40000
|6,0=>0x80c950b19c0841d014f00d
|7,0=>0x3e78d831b46a82539a89859a755799921753
|8,0=>0xa267a95df497
|9,0=>0xa
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 19 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_158 8 roots_158 ops++addP pm 1 dzo_148_64 4 roots_148 ops++addP pm 2 dzo_156_64 5 roots_156 ops++addP pm 3 dom_206 7 roots_206 ops++addP pm 4 dom_214 7 roots_214 ops++addP pm 5 dom_220 7 roots_220 ops++addP pm 6 dom_218 7 roots_218 ops++addP pm 7 dzo_158_64 6 roots_158 ops++addP pm 8 dom_94 6 roots_94 ops++addP pm 9 dom_148 4 roots_148 ops++addP pm 10 dzo_218_4 6 roots_218 ops++addP pm 11 dzo_90_4 5 roots_90 ops++addP pm 12 dzo_78_16 5 roots_78 ops++addP pm 13 dzo_202_4 5 roots_202 ops++addP pm 14 dom_156 5 roots_156 ops++addP pm 15 dom_202 5 roots_202 ops++addP pm 16 dzo_206_16 6 roots_206 ops++addP pm 17 dom_74 4 roots_74 ops++addP pm 18 dzo_150_64 5 roots_150 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_222 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_148_64_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_156_64_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_158_64_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_218_4_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_90_4_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_78_16_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_202_4_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_156 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_206_16_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_150_64_148 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_158 8 s (0,roots_158.map (·&&&dom_158)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_222 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_158 h
def symsG:List (List (Nat×Nat)):=[[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_222==dom_222)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_222 gM v ys):RunD true dom_222 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_222 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 4 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 15 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 24 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 24 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 8 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_222 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_107_128:=0xf0f00000f0f00000f0f00000f0f00000000000000000000000000000000
def gzo_107_128:=0xf0f00000f0e00000f0e00000f0c00000000000000000000000000000000
def gsh_107_128:=0xf0f00000f0e00000f0e00000f0c
theorem lowS_zo_107_128_97:Lower true dzo_107_128 roots_107 gzo_107_128 6:=lower_iso_b (d1:=dom_107) (r1:=roots_107) (T1:=gsh_107_128) [(dom_107,128)] (by decide +kernel) (lower_slice_b (T:=gsh_107_128) [(0xc0c00000c0c00000c0c00000c0c,0,2),(0xf0000000f0000000f0000000f00,0,8)] (by decide +kernel) lowS_97)
namespace S_235
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(2,10),(2,34),(2,66),(2,130),(3,11),(3,35),(3,67),(3,131),(8,9),(8,10),(8,72),(8,136),(32,33),(32,34),(32,96),(40,41),(40,42),(40,104),(40,168),(64,65),(64,66),(64,72),(64,96),(128,130),(128,136),(129,131),(129,137),(129,161),(129,193),(160,161),(160,162),(160,168),(160,224),(192,193),(192,194),(192,200),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_235.map (·&&&dom_235)
def gM:=goal_235&&&dom_235
def NN:Nat→Nat
|7=>2
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|7,0=>0x6c2f12ef6a
|8,0=>0xfffda
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f0000000000000000f0f00000f0f00000f0f00000f0f00000000000000000000000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f00000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000f00c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0ca0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0af0f00000f0f000000000000000000000f0f00000f0f00000000000000000000000000000000f0f00000f0f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x2c68eb1ae6c688
|_=>0
def sO:Nat→Nat→Nat
|7,0=>0xcc06
|8,0=>0xc6
|_,_=>0
def wAt:=mkWire dB 8 236 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 9
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x393a
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
addP pm 0 dom_234 7 roots_234 ops++addP pm 1 dom_171 6 roots_171 ops++addP pm 2 dom_107 6 roots_107 ops++addP pm 3 dom_233 7 roots_233 ops++addP pm 4 dom_227 7 roots_227 ops++addP pm 5 dom_203 7 roots_203 ops++addP pm 6 dzo_107_128 6 roots_107 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_235 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_107_128_97 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_234 7 s (0,roots_234.map (·&&&dom_234)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_235 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_234 h
def symsG:List (List (Nat×Nat)):=[[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_235==dom_235)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_235 gM v ys):RunD true dom_235 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_235 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 2 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_235 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_235 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_235 roots_235 goal_235 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_235
theorem lowS_235:Lower true dom_235 roots_235 goal_235 9:=S_235.noCircuit
def dzo_233_4:=0x303000003030000030300000303000003030000030300000303000003030
def gzo_233_4:=0x303000003030000030300000303000003030000030200000303000002000
def gsh_233_4:=0x30300000303000003030000030300000303000003020000030300000200
theorem lowS_zo_233_4_73:Lower true dzo_233_4 roots_233 gzo_233_4 6:=lower_iso_b (d1:=dom_233) (r1:=roots_233) (T1:=gsh_233_4) [(dom_233,4)] (by decide +kernel) (lower_slice_b (T:=gsh_233_4) [(0x30300000000000003030000000000000303000000000000030300000000,0,32),(0x30300000303000003030000030300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_73)
def dzo_97_128:=0x300000003000000030000000300000000000000000000000000000000
def gzo_97_128:=0x300000002000000020000000000000000000000000000000000000000
def gsh_97_128:=0x3000000020000000200000000
theorem lowS_zo_97_128_97:Lower true dzo_97_128 roots_97 gzo_97_128 4:=lower_iso_b (d1:=dom_97) (r1:=roots_97) (T1:=gsh_97_128) [(dom_97,128)] (by decide +kernel) (lower_slice_b (T:=gsh_97_128) [] (by decide +kernel) lowS_97)
def dzo_201_4:=0x3030000000000000303000000000000030300000000000003030
def gzo_201_4:=0x3030000000000000303000000000000030200000000000002000
def gsh_201_4:=0x303000000000000030300000000000003020000000000000200
theorem lowS_zo_201_4_73:Lower true dzo_201_4 roots_201 gzo_201_4 5:=lower_iso_b (d1:=dom_201) (r1:=roots_201) (T1:=gsh_201_4) [(dom_201,4)] (by decide +kernel) (lower_slice_b (T:=gsh_201_4) [(0x303000000000000030300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_73)
def dzo_109_128:=0x333300003333000033330000333300000000000000000000000000000000
def gzo_109_128:=0x333300003332000033320000333000000000000000000000000000000000
def gsh_109_128:=0x3333000033320000333200003330
theorem lowS_zo_109_128_97:Lower true dzo_109_128 roots_109 gzo_109_128 6:=lower_iso_b (d1:=dom_109) (r1:=roots_109) (T1:=gsh_109_128) [(dom_109,128)] (by decide +kernel) (lower_slice_b (T:=gsh_109_128) [(0x3030000030300000303000003030,0,4),(0x3300000033000000330000003300,0,8)] (by decide +kernel) lowS_97)
def dzo_101_128:=0x3300000033000000330000003300000000000000000000000000000000
def gzo_101_128:=0x3300000032000000320000003000000000000000000000000000000000
def gsh_101_128:=0x33000000320000003200000030
theorem lowS_zo_101_128_97:Lower true dzo_101_128 roots_101 gzo_101_128 5:=lower_iso_b (d1:=dom_101) (r1:=roots_101) (T1:=gsh_101_128) [(dom_101,128)] (by decide +kernel) (lower_slice_b (T:=gsh_101_128) [(0x30000000300000003000000030,0,4)] (by decide +kernel) lowS_97)
def dzo_105_4:=0x3030000030300000303000003030
def gzo_105_4:=0x3030000030200000303000002000
def gsh_105_4:=0x303000003020000030300000200
theorem lowS_zo_105_4_73:Lower true dzo_105_4 roots_105 gzo_105_4 5:=lower_iso_b (d1:=dom_105) (r1:=roots_105) (T1:=gsh_105_4) [(dom_105,4)] (by decide +kernel) (lower_slice_b (T:=gsh_105_4) [(0x303000000000000030300000000,0,32)] (by decide +kernel) lowS_73)
def dzo_73_4:=0x30300000000000003030
def gzo_73_4:=0x30200000000000002000
def gsh_73_4:=0x3020000000000000200
theorem lowS_zo_73_4_73:Lower true dzo_73_4 roots_73 gzo_73_4 4:=lower_iso_b (d1:=dom_73) (r1:=roots_73) (T1:=gsh_73_4) [(dom_73,4)] (by decide +kernel) (lower_slice_b (T:=gsh_73_4) [] (by decide +kernel) lowS_73)
namespace S_237
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(4,36),(4,132),(5,13),(5,37),(5,69),(5,133),(8,9),(8,72),(8,136),(12,13),(12,44),(12,76),(12,140),(32,33),(32,36),(32,96),(40,41),(40,44),(40,104),(40,168),(64,65),(64,72),(64,96),(68,69),(68,76),(68,100),(68,196),(128,132),(128,136),(129,133),(129,137),(129,161),(129,193),(160,161),(160,164),(160,168),(160,224),(192,193),(192,196),(192,200),(192,224)]
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
|4,0=>0xc1d9108c90
|5,0=>0xc795192ed683104632d55930d4447f4183e29f071c8371c69115df00bc740a21b099de0075d
|6,0=>0xe21fedcd3fd9f34c015cb7f7da7429965d3933db78441752d96f6ab6b0b167409668d065b6363ac1609a26096c557284dac2498fc45ad3431b542a7c3fbf83df943801b37fa335dda34c4b34b48317b62c27b2c0a629ea1297882768e273d526fb52606a2582a244df2449c1c8371a9d317c8916d0814ea41472213ed80c7050a5dd0a222073e501ee401a4d
|7,0=>0xf890cc1f7bbe9dcbb175b3b859151488211866bd850197ebd76b6e666194576814e671487c747faf44db7431a040b31369d635a3c318072c9802948726d2421aa22030e1a7a115de61445a02073
|8,0=>0xfbb04f0cadedab5c51738193d5a8794e2f643d29
|9,0=>0xf0cad
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcc000000cc000000cc000000cc000000cc000000cc000000cc000000cc0000000000033000011110000113300000000000000000000000000000000cccc0000cccc0000cccc000000000000cccc0000cccc0000cccc0000000332200003322000033220000332200003322000033220000332200003322cccc000000000000cccc000000000000cccc000000000000cccc000000022220000222200002222000022220000222200002222000022220000222200cc000000cc000000cc000000cc000000cc000000cc000000cc0000008b33300003333000000000000000000003333000033330000000000000000cccc000088880000cccc000088880000cccc000088880000cccc0000888b33300003333000033000000330000003333000033330000330000003300cccc0000cc0000008888000088000000cccc0000cc00000088880000880333300003300000033330000330000003333000033000000333300003300cc880000cc880000cc88000000000000cc880000cc880000cc880000000303000003030000030300000303000003030000030300000303000003030cccc0000cccc00008888000088880000cccc0000cccc000088880000888b33300003333000033330000333300000000000000000000000000000000
|0,1=>0xcccc000000000000c8c8000000000000cccc000000000000c8c80000000000000000000000033330000222200000000000000000000333300002222cccc0000cccc0000cccc0000cccc0000cccc0000cccc00000000000000000000000000000003333000033220000000000000000000033330000332200000000c0cc000000000000c0c8000000000000c0cc000000000000c0cb0300000303000003030000030300000303000000000000030300000000000000000cccc0000000000008888000000000000cccc000000000000888b33300002222000033000000220000003333000022220000330000002200cccc000000000000ccc8000000000000cccc000000000000ccc80000000303300000000000030320000000000003033000000000000303200000000cccc0000cc880000cccc0000cc880000cccc0000cc880000cccc0000cc891110000111100001111000011000000111100001111000011110000110000cc00000088000000cc00000088000000cc00000088000000cc0000008b3330000333000003232000032300000333300003330000032320000323044440000440000004444000044000000444400004400000044440000440333300003322000000000000000000003333000033220000000000000000
|0,2=>0x4444000044000000000000000000000044440000440003300000033000000330000002200000033000000330000003300000022cccc0000cccc00000000000000000000cccc0000cccc0000cccc0000888b33300003333000000320000003200003333000033330000003200000032ccc00000ccc00000ccc00000ccc00000000000000000000000000000000000000000000000033330000330000000000000000000000333300003300cccc0000cccc0000cccc0000cccc000000000000cccc000000000000888b23200003232000032320000323200003232000032320000323200003232c8c80000c8c80000c8000000c8000000c8c80000c8c80000c8000000c80003300000033000000330000000000000033000000330000003300000000cccc0000cccc0000cccc0000cc000000cccc0000cccc0000cccc0000cc022220000222200002222000022000000222200002222000022220000220088880000cccc000088880000cc88000088880000cccc000088880000cc8b3300000333000003330000033300000333000003330000033300000333000cc000000cc0000008800000088000000cc000000cc000000880000008b33300003333000032320000323200003333000033330000323200003232
|0,3=>0xcccc00000000000000000000000000008888000000000330000000000000022000000000000003300000000000000228888000088880000cccc0000cc8800008888000088880000cccc0000cc8800000003333000000000000333300000000000033330000000000002222cccc000000000000cccc000000000000cccc0000cccc0000cccc0000888b31100003311000033110000330000003311000033110000331100003300cccc0000cccc0000ccc80000ccc80000cccc0000cccc0000ccc80000cccb33300003333000033330000222200003333000033330000333300002222c0c00000c0c00000c0c00000c0c00000cccc0000cccc0000c8c80000c8c911100001111000011110000111100001111000011110000111100000000444400004444000044440000000000004444000044440000444400000003333000011110000333300001111000033330000111100003333000000000044000000440000004400000000000000440000004400000044000000031310000313100003130000031300000313100003131000031300000313000000000000000000000000000000000cccc0000cccc000088880000888b03000003030000030300000303000000000000000000000101000001010
|0,4=>0xcccc0000cccc0000cccc0000cccc0000c0c00000c0c00000c0c00000c0c00320000003200000032000000320000003200000032000000320000003200000000cc88000000000000cc88000000000000cc88000000000000cc8b3330000333300003333000033330000330000003300000033000000330000000000000000000000000000000000cccc0000cccc0000cccc0000000333300003333000033330000333300003333000033330000333300000000cccc0000cccc0000ccc00000ccc00000cccc0000cccc0000ccc00000ccc0000000000000000323200003232000000000000000000003232000032320c0c00000c0c00000c0800000c0800000c0c00000c0c00000c0800000c0b33300003333000033330000332200003333000033330000333300003322cccc0000cccc0000cccc0000cccc0000cccc000000000000cccc0000000030300000303000003030000030300000303000000000000030300000000cc000000cccc0000cc000000cc880000cc000000cccc0000cc000000cc8b3330000333300003333000033330000333300003333000022220000222200cc000000cc000000cc000000cc000000cc000000cc000000880000008b33300003333000033330000333300002222000022220000222200002222
|_,_=>0
def sP:Nat→Nat
|0=>0x168810a422000f3e0808a1000f0b1e0851d007058c1e085001e0851b100079a1464400086010a10005831e080802e3c10a10007960428400161810a0a00a8d1e08080163c114100068f0404980163c90a100058f0444800163c10a103820d18080801608509100038604140040608080
|1=>0x1e08508002c78214b0400163c1011421584163c114100058f040498800a858c04284004aa858f0428004163c124100058f0429488002c7a70428400163c114100058f04904000e3c10a4c20025163c114100128b1e09208001058c0404400163c12314200151a3c10a100079f0428400
|2=>0x1420007163c10a200038d1e0808016e47821420004703c10a100058f6e28400163c10a6c2000b063c10a100020f0429a8800d058f0428400163c10a662000b1ec810a100058f14c04000e2c30f040400b1e0852f1000a8b1e08088002c78214b84000e2c7822220004542c302140168b
|3=>0x1e08508002e48f0428400701c58f0428400163e402142000b1e08547100058f0428288011858f0428400081c302142000b1e0454410005c31e08508002c10a822000b0404541100058f0429f88002c78214f84007a2c782142000b1e08514100058f0429e0800ec58f042840016e8782
|4=>0x1c58f0404400082c602142000b983c101142000b1e0854e100128b0c3c10a1001c0b1e0850800e058f0404508001c68f04284008a2c7820228400163c131142000b1e08535100058f0428c88002c782142158b1e0854d100038b983c10a100258b1e08508012868b1e08508001c586
|5=>0x163c10a100058f0428400163c101142000b1f3c10a100058f5008508002e60f042840016187821420045163c10a100020b1e0808a100058f9e0808a100020b1e08511100058f1510400163c10a2220015082c782142000b1e0a10a1000a8b1e08508002c7828404508003458f0500508
|6=>0x2c7821420004
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x154005
|5,0=>0x5e61618526131846610183a60d182e60a18226071816604180a6
|6,0=>0x779dd77741dc97709dbb76d59ae769dda07665d92762dd8475f5d7675c19697589d5c6555d4e751dd4074e5d3274b19257479d177441d097409cfb73d1ced7399cdf7361cd17329cc372f1cb662c18a97289c9b7251c8d7219c8061e5c7271adc647
|7,0=>0x2c28aea2b28ab1aa57a762967a3de8789fe27879c5e698989e5a894de4b8911e3c88d5e2e789de216869e12882de0387ee1f477b21e57
|8,0=>0xbe9ef46bb5ee67b7ded87b45eca7
|9,0=>0x3016
|_,_=>0
def wAt:=mkWire dB 80 238 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 14
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x16212a201e1d14211629162114210e2116291a3016211e291a2b16210c2b04c7020314212223163d0829163d1e1d163d142144001e094a2b08211e1e16290823163d10a908234a280821163d0ca01e210821163d0821163d0e3d16291680020914211e061421168002090e2316292a2316311a3016211e290804163d08291e2d
|1=>0x829163d020114210829163d0201142116211401162910291e29163d14211e011ea2140916191e2116051421160514211629162114211601020314211a2b16211606142144001e0916321e2916291e011a0316211a01162116291e210c091e210e2116295023140908041421163d8a0b16011f0a02011b0216210823163d1a2b
|2=>0x163d1421040114091e011e2116011421163d14210401082b163d8a0b1601082b163d
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x43000000022002000000000000000000000
|6,0=>0x4930000004720000004524320004120000000003f23d23a33913720000003433220000003112e30002c22a20002912810000002532322121f21d21a30001820001620001420000000001220f30d20b2092072
|7,0=>0x8828628428228027e27c27a27827627427227026e26c26a26826626426226025e25c25a25825625425225024e24c2
|8,0=>0x9010008f18e18d18c18b18a1
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 12
def pmP:Nat→Nat
|0=>0x481f8020a8401050600803f00381f80141fc00a07e00413f0010188004a8c00217e00107f00081180030000004020001a40000c200001e400009a00003f000017800009c00004a000010000005800002000000c0000040000018000008000002000000
|1=>0x401c1fe000092c02011381018051c0fc2040620c107f02901f81180fc0838fe04107f01291f80940fc04a07a02020500900a804801401257e009223
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0xc0002080000000000
|6,0=>0xa0000400012000400001014d21000031000121c004201108000d10204f14004004004000008e181201
|7,0=>0xac4969992a9f05e0963b1085e5ada957d49a26ef26976c
|8,0=>0x64b732a2b62e
|9,0=>0xc
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 25 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_236 7 roots_236 ops++addP pm 1 dom_173 7 roots_173 ops++addP pm 2 dom_229 7 roots_229 ops++addP pm 3 dom_233 7 roots_233 ops++addP pm 4 dom_109 7 roots_109 ops++addP pm 5 dom_205 7 roots_205 ops++addP pm 6 dzo_233_4 6 roots_233 ops++addP pm 7 dom_141 4 roots_141 ops++addP pm 8 dom_165 4 roots_165 ops++addP pm 9 dom_204 4 roots_204 ops++addP pm 10 dom_97 4 roots_97 ops++addP pm 11 dzo_97_128 4 roots_97 ops++addP pm 12 dzo_201_4 5 roots_201 ops++addP pm 13 dzo_109_128 6 roots_109 ops++addP pm 14 dzo_101_128 5 roots_101 ops++addP pm 15 dom_172 4 roots_172 ops++addP pm 16 dom_101 5 roots_101 ops++addP pm 17 dom_228 4 roots_228 ops++addP pm 18 dzo_105_4 5 roots_105 ops++addP pm 19 dom_232 4 roots_232 ops++addP pm 20 dom_73 4 roots_73 ops++addP pm 21 dzo_73_4 4 roots_73 ops++addP pm 22 dom_45 4 roots_45 ops++addP pm 23 dom_108 4 roots_108 ops++addP pm 24 dom_105 5 roots_105 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_237 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_229 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_233_4_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_141 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_165 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_204 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_97 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_97_128_97 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_201_4_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_109_128_97 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_101_128_97 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_172 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_101 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_228 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_105_4_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_zo_73_4_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_108 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_105 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_236 7 s (0,roots_236.map (·&&&dom_236)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_237 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_236 h
def symsG:List (List (Nat×Nat)):=[[(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]]
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
def isoMvS_125:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_125:Lower true dom_125 roots_125 goal_125 9:=lower_iso_b isoMvS_125 (by decide +kernel) lowS_119
def isoMvS_183:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_183:Lower true dom_183 roots_183 goal_183 9:=lower_iso_b isoMvS_183 (by decide +kernel) lowS_175
def isoMvS_187:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccccccccccccccccccccccccccc,126),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_187:Lower true dom_187 roots_187 goal_187 9:=lower_iso_b isoMvS_187 (by decide +kernel) lowS_175
def isoMvS_189:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_189:Lower true dom_189 roots_189 goal_189 9:=lower_iso_b isoMvS_189 (by decide +kernel) lowS_175
def isoMvS_190:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_190:Lower true dom_190 roots_190 goal_190 9:=lower_iso_b isoMvS_190 (by decide +kernel) lowS_159
def isoMvS_231:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_231:Lower true dom_231 roots_231 goal_231 9:=lower_iso_b isoMvS_231 (by decide +kernel) lowS_119
def isoMvS_238:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_238:Lower true dom_238 roots_238 goal_238 10:=lower_iso_b isoMvS_238 (by decide +kernel) lowS_219
def isoMvS_243:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_243:Lower true dom_243 roots_243 goal_243 10:=lower_iso_b isoMvS_243 (by decide +kernel) lowS_237
def isoMvS_245:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124)]
theorem lowS_245:Lower true dom_245 roots_245 goal_245 9:=lower_iso_b isoMvS_245 (by decide +kernel) lowS_221
def isoMvS_246:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_246:Lower true dom_246 roots_246 goal_246 9:=lower_iso_b isoMvS_246 (by decide +kernel) lowS_221
theorem lowS_127:Lower true dom_127 roots_127 goal_127 10:=lower_slice_b [(0xcccccccccccccccccccccccccccccccc,8,10)] (by decide +kernel) lowS_125
namespace S_191
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(2,10),(2,34),(2,130),(3,11),(3,19),(3,35),(3,131),(4,20),(4,36),(4,132),(5,13),(5,21),(5,37),(5,133),(6,14),(6,22),(6,38),(6,134),(7,15),(7,23),(7,39),(7,135),(8,9),(8,10),(8,136),(12,13),(12,14),(12,28),(12,44),(12,140),(16,17),(16,20),(16,144),(18,19),(18,22),(18,26),(18,50),(18,146),(24,25),(24,26),(24,28),(24,152),(32,33),(32,34),(32,36),(40,41),(40,42),(40,44),(40,168),(48,49),(48,50),(48,52),(48,176),(56,57),(56,58),(56,60),(56,184),(128,130),(128,132),(128,136),(128,144),(129,131),(129,133),(129,137),(129,145),(129,161),(160,161),(160,162),(160,164),(160,168),(160,176)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffffffffffff
def xsM:=roots_191.map (·&&&dom_191)
def gM:=goal_191&&&dom_191
def NN:Nat→Nat
|10=>1
|_=>0
def HT:Nat→Nat→Nat
|10,0=>0x2bff1
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffff000000000000000000000000ffffffff00000000ffff0000ffff00000000000000000000ffff0000ffff0000ff00ff00ff00ff000000000000000000ff00ff00ff00ff00f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0cccccccccccccccc0000000000000000ccccccccccccccccaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaaffffffffffffffff00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x1ac688
|_=>0
def sO:Nat→Nat→Nat
|10,0=>7
|_,_=>0
def wAt:=mkWire dB 7 192 0xffffffffffffffffffffffffffffffffffffffffffffffff
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
|10,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 1 (j%128);fld (pmP (k/32)) 6 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_190 9 roots_190 ops++addP pm 1 dom_189 9 roots_189 ops++addP pm 2 dom_187 9 roots_187 ops++addP pm 3 dom_183 9 roots_183 ops++addP pm 4 dom_175 9 roots_175 ops++addP pm 5 dom_159 9 roots_159 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_191 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_189 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_175 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_159 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_190 9 s (0,roots_190.map (·&&&dom_190)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_191 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_190 h
def symsG:List (List (Nat×Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_191==dom_191)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_191 gM v ys):RunD true dom_191 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_191 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s:Nat) (hs:s≤10):∀ i<NN s,bar dom_191 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_79_16:=0xffff000000000000ffff0000
def gzo_79_16:=0xfffe000000000000fefa0000
def gsh_79_16:=0xfffe000000000000fefa
theorem lowS_zo_79_16_74:Lower true dzo_79_16 roots_79 gzo_79_16 6:=lower_iso_b (d1:=dom_79) (r1:=roots_79) (T1:=gsh_79_16) [(dom_79,16)] (by decide +kernel) (lower_slice_b (T:=gsh_79_16) [(0xaaaa000000000000aaaa,0,1),(0xf0f0000000000000f0f0,0,4)] (by decide +kernel) lowS_74)
def dzo_149_64:=0x330033000000000000000000000000003300330000000000000000
def gzo_149_64:=0x330032000000000000000000000000003200220000000000000000
def gsh_149_64:=0x33003200000000000000000000000000320022
theorem lowS_zo_149_64_148:Lower true dzo_149_64 roots_149 gzo_149_64 5:=lower_iso_b (d1:=dom_149) (r1:=roots_149) (T1:=gsh_149_64) [(dom_149,64)] (by decide +kernel) (lower_slice_b (T:=gsh_149_64) [(0x22002200000000000000000000000000220022,0,1)] (by decide +kernel) lowS_148)
def dzo_157_64:=0x33333333000000000000000000000000333333330000000000000000
def gzo_157_64:=0x33333332000000000000000000000000333233220000000000000000
def gsh_157_64:=0x3333333200000000000000000000000033323322
theorem lowS_zo_157_64_148:Lower true dzo_157_64 roots_157 gzo_157_64 6:=lower_iso_b (d1:=dom_157) (r1:=roots_157) (T1:=gsh_157_64) [(dom_157,64)] (by decide +kernel) (lower_slice_b (T:=gsh_157_64) [(0x2222222200000000000000000000000022222222,0,1),(0x3300330000000000000000000000000033003300,0,8)] (by decide +kernel) lowS_148)
def dzo_207_16:=0xffff000000000000ffff000000000000ffff000000000000ffff0000
def gzo_207_16:=0xffff000000000000ffff000000000000fffe000000000000fefa0000
def gsh_207_16:=0xffff000000000000ffff000000000000fffe000000000000fefa
theorem lowS_zo_207_16_74:Lower true dzo_207_16 roots_207 gzo_207_16 7:=lower_iso_b (d1:=dom_207) (r1:=roots_207) (T1:=gsh_207_16) [(dom_207,16)] (by decide +kernel) (lower_slice_b (T:=gsh_207_16) [(0xaaaa000000000000aaaa000000000000aaaa000000000000aaaa,0,1),(0xf0f0000000000000f0f0000000000000f0f0000000000000f0f0,0,4),(0xffff000000000000ffff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_74)
def dzo_159_64:=0xffffffff000000000000000000000000ffffffff0000000000000000
def gzo_159_64:=0xfffffffe000000000000000000000000fffeffee0000000000000000
def gsh_159_64:=0xfffffffe000000000000000000000000fffeffee
theorem lowS_zo_159_64_148:Lower true dzo_159_64 roots_159 gzo_159_64 7:=lower_iso_b (d1:=dom_159) (r1:=roots_159) (T1:=gsh_159_64) [(dom_159,64)] (by decide +kernel) (lower_slice_b (T:=gsh_159_64) [(0xaaaaaaaa000000000000000000000000aaaaaaaa,0,1),(0xcccccccc000000000000000000000000cccccccc,0,2),(0xff00ff00000000000000000000000000ff00ff00,0,8)] (by decide +kernel) lowS_148)
def dzo_91_4:=0xf0f0f0f000000000f0f0f0f0
def gzo_91_4:=0xf0f0f0e000000000f0f0e000
def gsh_91_4:=0xf0f0f0e000000000f0f0e00
theorem lowS_zo_91_4_75:Lower true dzo_91_4 roots_91 gzo_91_4 6:=lower_iso_b (d1:=dom_91) (r1:=roots_91) (T1:=gsh_91_4) [(dom_91,4)] (by decide +kernel) (lower_slice_b (T:=gsh_91_4) [(0xf0f0000000000000f0f0000,0,16)] (by decide +kernel) lowS_75)
namespace S_223
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(2,10),(2,66),(2,130),(3,11),(3,19),(3,67),(3,131),(4,20),(4,132),(5,13),(5,21),(5,69),(5,133),(6,14),(6,22),(6,70),(6,134),(7,15),(7,23),(7,71),(7,135),(8,9),(8,10),(8,72),(8,136),(12,13),(12,14),(12,28),(12,76),(12,140),(16,17),(16,20),(16,144),(18,19),(18,22),(18,26),(18,82),(18,146),(24,25),(24,26),(24,28),(24,88),(24,152),(64,65),(64,66),(64,72),(68,69),(68,70),(68,76),(68,84),(68,196),(80,81),(80,82),(80,84),(80,88),(80,208),(128,130),(128,132),(128,136),(128,144),(129,131),(129,133),(129,137),(129,145),(129,193),(192,193),(192,194),(192,196),(192,200),(192,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1ffffffffffffffffff
def xsM:=roots_223.map (·&&&dom_223)
def gM:=goal_223&&&dom_223
def NN:Nat→Nat
|5=>1
|6=>12
|7=>68
|8=>155
|9=>98
|10=>14
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0x40664
|6,0=>0xf33a3d4140a175e731623ad7c26b181e48d188f317c891488e1174910f0f
|7,0=>0xfd218fceeef20d8e5abae275ee0a1ade0d6dbde4db75dd74add3857cf92ccbb67c6796c20a8c061abc4beb9a1db5baeb3e83a5c76a595ea0ec7a03889fe519efb598b6f977399631295a768ca4f8c3ee8c12b8b37a820db804d27f8077ef447772f758ac71f4e706546dc4f6b9456991461d465f48d5dd18563345468f4de9f4847a420383937f35c8f336ba32a08310122b66a28d0620f97204620e43107f4304bfc045dc0458703588
|8,0=>0xce2b1cd3eec95d2c9059c73bbc6654c636dc57c7c3fa5c23f4c0807c01babf0a2be5c6bbf9cb930fb3560b16d6aed39ac3ecaaab7aaa32a8113a60f9a3f0ca1f95a1e42a018c9e33f9ddb99d32e9c72e92d53907128dd828d6688c1c08ab36896348745d8693283a42834478296f827818170b8104a7e337743bb73a56724097217a7111070f1e708986fb756e72b6bfdf6819166b49669bd658a7649006378f61e2c61d26610d960e745e7f25c100589245677455c1d5395e52de0506714e4394a49049f5b49b7e463e945bb2459e1455dc4553f442c243d243e32d36adb35f0c3501134c4a34162327093167f310dd30e2c3085d2fcf02a5962a3ac27fdf259d52372921f3c1d1791cde41b81d1a6fd1945b1901f17428151e514c8d139ec1207211c710f7ff0f1ff0e5b30d9680c4d80b8950b63f06ed5049840050600034
|8,1=>0xff9acfe67bfcadafaa64faa1dfa7e8f92a8f8d8df6f03f34d1edf39ecea4ea6f4e9b6ae87fee7e80e68d1e4c51e49e0e1683dff70ded84db773d2b33d09eed0998d0416
|9,0=>0xfabeaf87e1f3466ef716ebe47e3df7d969fd930cd6d3cd6d26d3db1cca80cb6dfc7320c2ca7c0b96c0783c0465bf4c3becb9be5c8bbd72bbbe3bab3cba37bb389cb1f6fb1177ab7e5a2583a256fa123f9cbaf9b9519b3959a7f5992ba9717a9395e9068c8f4038b3cd87e35866dc8173c80b7f806347f0917ea40791817139370e756c2316bc1d6b59669218672a962ff3613415f52a5916d58948561e553072518fd501d24edaa4d03f4ce6e4ccaa4a17946f3c44c2d43b07430f943026321092e12b27042267b1263be25e9b25aeb242cf23cb31d5ab1bd4519e44177fd0c7390bd410b1050a81c06d07067c7061a102ae201ae9
|10,0=>0xea6b8e5cbdd4b04c3dccb0348ae79e94644799007474a6375a5bfd64e3a9451471f14a
|11,0=>0x1730e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x33333333000000003333333300000000333333000000000033333300ffffffff00000000ffffffff00000000ffffff0000000000ffffff00ffccffcc00000000ffccffcc00000000ffccffcc00000000ffccffcc00000000000000000000000000000000333333000000000033333300000000ff00000000000000ff000000000000000000000000ff00ff00cccccccc00000000cccccccc00000000cccccccc00000000ccccccccff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00333333330000000033333333000000003333333300000000330033000f0f0f0f000000000f0f0f0f000000000f0f0000000000000f0f0000ffffffff00000000ffffffff00000000000000000000000000000000ffff000000000000ffff000000000000ffff000000000000ffff0000ffffffff00000000ffffffff00000000ff00ff0000000000ff00ff00f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000033000000000000003300000000333333330000000033003300ffffffff000000000000000000000000ffffffff0000000000000000
|0,1=>0xffffffff00000000ffffffff00000000ffccffcc00000000ffccffcc00000000000000000000000000000000ffffffcc00000000ffffffccffffff0000000000ffffff0000000000ffffff0000000000ffffff00ffffffff00000000ffffffff00000000ffffffff00000000ff00ff00ffffffcc00000000ffffffcc00000000cccccccc00000000cccccccc000000ff00000000000000ff00000000ffffffff00000000ff00ff000f0f0303000000000f0f0303000000000f0f0300000000000f0f0300ffffffff00000000ffffffff00000000ffff000000000000ffff0000ffffffff00000000ff00ff0000000000ffffffff00000000ff00ff00ffffffff00000000cccccccc00000000ffffffff00000000ccccccccffffff0000000000ffffff0000000000000000000000000000000000cccccccc00000000cccccccc00000000cccccccc00000000cc00cc00ffffffff00000000ffffffff00000000cccccccc00000000cccccccc0f0f0f0f000000000f0f0f0f000000000f0f0f00000000000f0f0f00333333330000000033003300000000003333333300000000330033000f0f0303000000000f0f0303000000000f0f0000000000000f0f0000
|0,2=>0xffffff0000000000ffffff0000000000ffffff0000000000000000000f0f0f0f000000000f0f0f0f000000000f0f0f0c000000000f0f0f0cffffcccc00000000ffffcccc00000000ffffcccc00000000ffffccccffff333300000000ffff333300000000ffff000000000000ffff00003333333300000000333333330000000000000000000000000000000033333333000000003333333300000000333300000000000033330000ffffffff00000000ffffffff00000000ffffffff000000000000000000000000000000000000000000000000ffffff0000000000ffffff00ffffffff000000000000ffff00000000ffffffff000000000000ff000000ffff000000000000ffff000000000000ff00000000000000ff0000ff00ff00000000000000ff0000000000ff00ff00000000000000000000000000000000ffffffff000000000000000000000000ff00ff0033333333000000003333333300000000330033000000000033003300ffffffff00000000ffffffff00000000ffffcccc00000000ffffcccc0f0f0f0f000000000f0f0f0f000000000f0f0c0c000000000f0f0c0cffffffff00000000ffffffff00000000ffffffcc00000000ffffffcc
|0,3=>0xffffffff00000000ff00ff00f0f0f0f000000000f0f0f0f000000000f0f0ffff00000000f0f0fcfc0f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f00f0f0f0f000000000f0f0f0f000000000f0f0ffff00000000f0f0fff0fffffff000000000fffffff000000000f0f0f0f000000000f0f0f0f0ffffffcc00000000ffffffcc00000000ffffffcc00000000ffffffccff00ffff00000000ff00ffff00000000ff00ff0000000000ff00ff0055555555000000005555555500000000555555550000000055555500ffff000000000000ffffffff00000000ffff000000000000ffffff0000000000000000000000000000000000ffff000000000000ffffff00ffffffff00000000ffccffcc00000000ffffffff00000000ffccffccffff333300000000ffff333300000000ffff330000000000ffff330000000000000000000000000000000000ffff330000000000ffff330000ff00ff0000000000cc00cc0000000000ff00ff0000000000cc00cc33333333000000003300333300000000333333330000000033003300cccccccc00000000cccccccc00000000cccccccc00000000cccccc00
|0,4=>0xff00ff0000000000ff0000ffff000000000000ff00000000000000ffffffff00000000ff00ff00ffff00ff00000000ffff00ff00000000ffff000000000000ffff000000ff00ff0000000000ff00ff000000000000000000000000000000000f0f000f000000000f0f000f000000000f0f0000000000000f0f0000ffffffff00000000ffffffff00000000ffffffff00000000cccccccc0000ffff000000000000ffff000000000000ffff000000000000ccccffffffff000000000000ffff00000000ffffffff00000000000000000000ffff000000000000ffff00000000000000000000000000000000ffff000000000000ffff00ff000000000000000000000000000000000000ffff000000000000ff00000000000000ffff000000000000ff00ffffaaaa00000000ffffaaff00000000aaaaaaaa00000000aaaaaaaa0f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0c0c33333333000000003333333300000000333333330000000033333300000000ff00000000000000ff00000000ff00ff0000000000ff00ff0000ff00ff0000000000ff00ff0000000000ff00ff0000000000000000
|0,5=>0xffffffff00000000ffffff0000000000ffff000000000000ffff0000000000ff00000000000000ff00000000000000000000000000000000ffffffff00000000000000ff00000000ffffffff0000000000000000000000ff000000000000000000000000ffffffff00000000000000000000ffff000000000000cccc000000000000ffff000000000000ccccffffffff00000000ffffffff000000000000ffff000000000000ccccffffffff00000000ffff000000000000ff00ff0000000000ff0000000000ffff000000000000ffff000000000000ffcc000000000000ffcc0000ffff000000000000ffff000000000000ffff000000000000ff000000000000000000ffffff00000000000000000000000000ffffff00ffffffff00000000ffffffff000000000000000000000000ffffff00000000000000000000000000000000000000000000000000ffffff00ffffffff00000000ff00ffff00000000ffffffff00000000ff00ff00ffffffff00000000ffff00000000000000000000000000000000000000003333000000000000333300000000000033000000000000003300ffffffff00000000ffff000000000000ffffffff00000000ffff0000
|0,6=>0xffffffff000000003333333300000000ffffffff000000003333000000000000000000000000000000000000333333330000000033330000ffffffff00000000ffffff0000000000ff00ff0000000000ff00ff0000000000000000000000ffff00000000000000000000000000000000aaaaaaaa00000000aaaaffff00000000aaaaaaaa00000000aaaaaaaa333333000000000033333300000000003333330000000000333333000000ffff000000000000ffff000000000000ffff0000000000000000ff00ffff00000000ff00ffff00000000ff00ffff00000000ff00ff00ffff000000000000ffff000000000000ffffffff00000000ffffff00ffffffff00000000ffffff0000000000ffffffff00000000000000000000000000000000ffffffff00000000000000000000000000000000aaaaaaaa00000000ffffffff00000000aaaaaaaa00000000aaaaaaaaffffffff00000000ffffffff00000000ffffffff00000000ffffcccc000000ff00000000000000ff00000000000000ff00000000000000000000000000000000ffffffff000000000000000000000000ffff0000ffffffff00000000ff00ff0000000000000000000000000000000000
|0,7=>0xff00ffff000000000000000000000000ff00ff00000000000000000000000000000000000000ffff000000000000ff00000000000000000000ff00ff00000000000000000000000000ff0000ff00ff0000000000ffffffff00000000ff00ff0000000000ffffff00ffffffff00000000ffffff0000000000ffffffff00000000ffffff0055555555000000005555550000000000555555550000000055555500ffffffaa00000000ffffffaa00000000aaaaaaaa00000000aaaaaaaaffffffff00000000ffffffff00000000ffffffff00000000ffffff00ff33ff3300000000ff33ff3300000000ff33ff0000000000ff33ff00000000000000000000000000000000000000ffff000000000000ccccffffffff00000000ffffffff00000000333333000000000033333300000000000000000000ff00ff00000000000000000000000000000000aaaaaaaa00000000aaffaaff00000000aaaaaaaa00000000aaaaaaaaffffffff00000000ffffffff00000000ffffffff00000000ffff00000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f00000000000000000000ffffffff000000000000000000000000ffffff00
|0,8=>0xffffffff0000000000ff00ff00000000ffffffff0000000000000000ffff000000000000ffffffff00000000ffff000000000000ffff000000ff00ff0000000000ff00ff0000000000ff00000000000000ff0000ffffffff0000000000ff00ff00000000ffffffff0000000000ff00003333333300000000333333330000000033333333000000000000000000003333000000000000333300000000000033330000000000000000ccccffff00000000ccccffff00000000ccccffff00000000ccccccccffffffff00000000ffffffff000000000000ffff000000000000ff00000000cc00000000000000cc00000000cccccccc00000000cccccccc00000000000000000000000000000000ffffffff00000000ccccccccffff000000000000ffff000000000000ffffffff00000000ffffcccc00ff00ff0000000000ff00ff0000000000ff00ff0000000000ff0000ffff000000000000ffff00ff00000000ffff000000000000ffff0000ccccffff00000000ccccffff00000000ccccffcc00000000ccccffccffffffff00000000ff00ff0000000000ffff000000000000ff00000033333333000000003333333300000000333333330000000033330000
|0,9=>0xffffffff00000000ffffcccc00000000ffffffff00000000ffffccccffffffff000000003333333300000000ffffffff000000000000000000000000000000000000000000000000ffffffff00000000ffff00003333333300000000333300000000000033333333000000003333000000ff00ff0000000000ff00000000000000ff00ff0000000000ff0000ff00ff0000000000ffffffff00000000ff00ff0000000000ff00ff00ff33ff3300000000ff33ff3300000000ff00ff0000000000ff00ff00
|_,_=>0
def sP:Nat→Nat
|0=>0x4030a0200150509240a021200061d050403130223000517090a022100061e050409030a0200051c04031b0200051a04030a020005040913021900050d17160207060504030208001505091402120006050d04130212000509020812000605090211100006050d0403020c0005040b030a020005090208070006050403020100
|1=>0x21200060504090a021229000504090a0207290005090302310006050903300200060504030a02002f050903020826000605090a022319000605090a022e00062d180903021100060517090a021000060504031b0200050903022a1100060517090a0207290628050d04030a02001e051f09030a02000504030a02002506051c
|2=>0x90a021200063a05040313020005390903023100062c050903021100060504090a022e00060509030a380006340504090313020036050409030a02001d18030a023200060535090a0207000633050409030a020005090a0207320006050d170a02070006050409130a0212001805090302080006050409030a020c00050d040a
|3=>0x2231200060e05090314020006051709160a020706050441030a02000e050d040313020005090a02070040060e05090302080006053f090a020700061d0504031402000605093e0a02000605090a021107000605090a023d0006051f090a022e000605093c0a0200061d0504030208000605090a0219000618093b0a0200051f
|4=>0x1809030a0200150509030a020025061e0509030a0200060509240a02070006051f0903020f00060509160a02120006051c090a021200060504090a021900060509030a440006051c090a020700060504090313020f00050d09160207000605090a0243000605090302420006050d0403020f000618050d170316020605090a
|5=>0x509030a0200061805170903160a0206340509030a022300062d050903130229000509030a024f0006054e09030a020006050d040313020005093b0a02000605090a024b0006051c09030a02260006180509030a020040060509030a02490006050903020800061d051f04030a020006050903021100062b0e05040903130a02
|6=>0x200064628050409030a02000509030a02580006050409030a02570006550509030a0200061d180903160a0200062d05040903130200540509030a0200060e051f09030a02000605533909030a02000605090a021200060509030a0229520509030a02510006050409030a020f0006050903160a022600060509031402000620
|7=>0x630509030a020006050d090a02070006051709030a022a00060504030a0200150509030a020062061d0504030a022300061d6109030a0200065f0509030a0200060509030a025d00060509030a025b290618051c09030a0200060509030a025c060509030a025a000605040959030a02000618050d0903160200060509030a
|8=>0x1c04030a0200060509030a026e0006056d09030a0200060e0509030a02230006050409030a024f00060509030a6b00060509030a020c00061809030a026a00060504090302080006056809030a02000618050924030a020006670509030a02000605090a02072900060509030a026600062d181709030a020006050409030a64
|9=>0x51c09030a0200060517090a02070006340509030a0200060509030a73000605090a02710006700509030a020006050d1703130200061d050403160a0200060509030a026f00060504090a02120006050d17031602060509031b0200060504090a0207000605040903140200062d0509030211000620050409030a0200061d05
|10=>0x6a00060509030a7a00060509030a7900061d0504030a022900780509030a0200060e050903160a0200063a1809030a020006057709030a0200062d0517090313020006050409030a022629000509030a027600061d050424030a0200060509030a02002f060509030a0275000620051f09030a02000618051709030a0229060e
|11=>0x6050d040302230006370509030a0200060509030a0245290618050409030a0229000509030a028000060509030a022700061d05030a0232000605097f030a0200062c051709030a0200060509030a027e000605090a022100060509030a027d00060e050924030a0200061d050403130a02007c0509030a0200060504030a02
|12=>0xa0210000618053509030a0200063a0504030a020006850509030a020006180509030a023200063a0509031302000618050d17030a0200060509030a0284000605040903130223000509030a026606830509030a02000634050409030a020006050903820a0200060504030a0200400670050409030a020006050981030a0200
|13=>0x9030a0200060509030a0229600509160a020700060509030a028c0006050959030a0200060509030a02008a06051f090302230006050d0403160200060509030a0257000622051709030a020006050903890a0200060509030a02880006180517090a02070006050903870200061d09030a022a00060509030a020f00060509
|14=>0xa02450006050409030a02230006720509030a0200060509030a0200065e8e0509030a02000637050409030a02000618053f09030a02000628050903160a0200060509030a02756a00060e050d04030a0200063a050903026a00060e050409030a022900180509030a02110006050409030a02270006051709030a0248060553
|15=>0x62d050903130200060509030a0229006906051709030a0200062b2d5009030a020006051c0409030a020006051709030a0229060509030a0200066c0509030a0248000605090a02070006560509030a0200060509030a028f00061d0509030a026a00061d2d09030a0200060e050409030a0200060509030a02000674050903
|16=>0x30a02290006050d04030a020006050409030a0229007b0509030a020006053909030a020006050d0903130200060509030a02260006051709030a02000647050903130a0229000509030a64000605040924030a0200062c0509030a02000618050903160a020006059009030a02000605040903160a020006280509030a0200
|17=>0x20006220509030a020006940509030a0200061805090a020700060509030a02930006053509030a0200060509030a029200060509030a023200062d050409030a020006050d17030a020006059109030a0200061d050903160a0200061d1809030a02000605040903130a0200500509030a022906056109030a0200062d0509
|18=>0x3f09030a0200060509030a02008b060509030a021100061d5009030a020006050409030a02290006050409030a022600061d560509030a0200060509030a025b0006050903160a0229060509030a026a00060509030a020006600509034a0a020006050903860a0200062d051709030a0200060509030a02000615051f09030a
|19=>0xa020006960509030a0200060509030a020006523a0509030a0200060e0509030a02000605170903130a0200060509030a028d000605170903160a02060509030a029500060509030a02230006050409030a0200650509030a0229002b0509030a02004006180509030a0229000618050d09030a0200061d0504030a02000605
|20=>0x9030a020006050924030a02000650050903130a0200060509030a020069062d1809030a0200060509030a022a0006051c09030a0200061d050903130a02000618051709030a020006050d0903160200064d0509030a020006051f0409030a0200061d0509030a02290006050409030a02002b0509030a0229004c1805040903
|21=>0x509030a0200060509030a02000647050903160a0200060509030a0200064c0509030a0200062b0509030a02000665500509030a0200061d0509030a020006051709030a020006180509030a020006050409030a020006050903130a0200060509030a02290006050d09030a0200062d0509030a020006500504
|_=>0
def sO:Nat→Nat→Nat
|5,0=>6
|6,0=>0x53704c7045703e7037703070297022701b7014700d70067
|7,0=>0x2408239723182298221821a7213720b820381fb81f381eb81e471dc81d481cc81c481bc81b571ad81a6719e8197718f81887182617a8173716b8163815b8154714c8144813c8134812c8124811c8114810c810480fc80f480ec80e570de70d770cf80c780c070b880b080aa60a2809a8092808a8082807a8072806a8062805a8
|7,1=>0x2608258825082488
|8,0=>0x46984609457945074488440843884308427941f8417840f840693ff73f783ef83e693df73d783ce93c683be83b683ae83a5939e7396838d9384937c8374836c8363935b8352934a83428339933093297322731a83119308930172f982f092e792df82d782cf82c872c172ba72b192a892a0829972909288827f9278727082688
|8,1=>0x672966a86628659965186489640863886317629862096188610860795ff85f785ef85e785de95d685ce85c685be85b595ad85a6759e8595958d8585857d8576756f7567855f8556954e8546853d9534952c8523951b8513850a950194f894f084e884e174da74d284ca84c194b984b184aa74a3749b8493848b8482947994718
|8,2=>0x7519748973f9736972d9725871c9713970a970286fa86f376eb86e386db86d386cb86c386bb86b296aa86a286999692768a8682867b7
|9,0=>0x9618958994f9946993e8936892e8926891e8916890d990588fd88f588ed88e588dd88d588cd88c588bc98b488ac88a3989b8893888b8883887a9872886a8862885a8852884a8841983988327829982188189810880797ff87f787ee97e597dd87d497cc87c487bc87b577ad87a5879c9794878b9783877b8772976a8762875a8
|9,1=>0xa7a9a728a699a618a598a518a498a409a379a2f8a278a1e9a159a0d8a0589fc99f489ec89e489dc89d399cb89c389bb89b389ab89a3899b8992998999818979897189698
|10,0=>0xaeb8ae38adb8ad38acb8ac38abb8ab38aab8aa38a9b8a938a8b8a838
|11,0=>0xaf37
|_,_=>0
def wAt:=mkWire dB 151 224 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1803c14191817424010506424191d290001905094240105064b00f0900414ad0a06828551d06024190509414190900400191803c14190e06c14112006c147d0d06424290927898010504824191d0601425040042419040ac14252203c602905064801b051f410290906428551d06014250400424190a004600f0900414190a064380f0504424190f06c382b050442419
|1=>0x906414111c0ac100109064702805094100109064702b0400424193403c148d040ac2419050640c551d0601425050d424290906428192003c147d040a4102b3706c14910400c245a0a004142505064d01b05234102b09064600f090a4240105064380f0a064141109064702b17064240105064384f0a064141109064380f0504424190e03c0019050442419090640019
|2=>0x1c0ac1001090641029090641425170ac24010a06828190504424191d060142505064252200474141a3a06c1435090a4382b040a4141109064380f1809414193403c148d040ac09194506824011803c24010e0ac14110906428011803c24290506414110906424290a00424010506414111c0a0100109064600f0a00424010506410571d06024190509424290a0641411
|3=>0x50a424190a064a0031d06c1425040a4141109064e40109474141a0e03c602505064001950060140105238102b09064382b0504424190a0041412090647028040042419180d4242905064280109004141905234102b0906400190a06414295004c1401090645d1f09004141a090a424190a0640c551d06014254d03c153109068241909298001905064152a130042819
|4=>0x6860590a00414191803c242905064602b0900414191d0602419050941502092980019040ac2419050946003050941419056045c180900401791d0681425051682801000645c190900414190015c7418050956c19051682801500401401090642801090a4141945068145e09004381b050442419051f83419090a41472040042419560647403050942801050941419
|5=>0x900424290a15474180509424191803c14191c0a01001090645c2b090041429051f410290906414250400424195013c14010a0642549500601401040ac1411090654013050042419026c5401a05004a02b1d06c14251d0ac142505064702b0400424190969414a6000641003090641419053f45c1b0900400191803c1419001547418050941429090041419090640995
|6=>0xa0046025050641435090a41419092a4602b05064142909004281900064141209064605a0a00414190400c24190509474a40006414256a064742b05094147d0d06424290006424010506410010504424191803c240105064148d040ac2419027445c1a09005c80f1800414190e00c60250506428190900424290a004241905094a801180ac14190e03c1411090642801
|7=>0x9064605c090041419090a4102b0906414910400c241900064145e090042419000641419720ac600105064980105048241905094245a0a004e40309474141a0900414ad0a068605e0900414192203c602905064605f0900414190400c141109064142509064281961094600305064742b0906414257b02c74010509408551d060142509064001905094605d090041419
|8=>0x900414190a69414a60006514190517824011803c24010506428571d0601425180ac142505064382b1809414192c03c14ad0a0685c29090041419090641435090a416191606c280105064245a0a0042819050d42429090a4240105065c827180041419040ac24190a06400551d0601425057445c1a09004148d040ac24190a26414120906470270400424190e00c1411
|9=>0x1800414191d068142505654001a052441003090645c1b0900414190a004741b05095a8191d0ac1425090a4141109064e82b050d42429000641411090645c2b09004141926004141209064240100474141a09484011d0506800191706024010a004600f0506634011809c141950040140109064162e0a2980019040a4102b090642801090642429051c81001090646029
|10=>0x906424290006424191d004142509474141a0a064242905048241909004141a00064281902654001a0400c2419052b4281a0a0041419092b4281a0a00424191d06c14250a064142905298001909004281a05004142904004241909004001950068140100474141a1803c14191d00c1425004c4241a1d0ac1425050941429050442419170682401051782401040ac2419
|11=>0x1706c24010a2980019170ac24010500414250006424190504824191d00c14250516828010a00400191d0ac14251706024011300428191606c28010900414291d06014250d0642429180a414195006c14011803c1419500ac14010d00424295009c140109168280109064142909004242909654001a0a00414250509414190906428190500400191800c1419000641429
|12=>0x90a414290500424190400c2419050042819052980019050a41419180ac14190400424190509428190900414190a0042429054c4241a040a424190006414250a068241900064241a0906414192d0041429500601401050d424291809414190900428191809c1419090042801002b4281a040ac241909064001a00064281a092980019000641419090a41419090641425
|13=>0x5068280109068281a0006814010509424010506424190a0640019
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x31400000000840000000011000000000040000000
|7,0=>0x284c9e327089932550000000093223d000022d087420d07f400007b400007740000000000000000007431c106c400006840000000194c00019046131750000165000015505141350494118c4240f900000ecc374000000000003520c502d40b04284098822407901a40000182054c114
|7,1=>0xa74290c000
|8,0=>0x598d633580d5d3568d573550d513538d4b3520d453508d3f34f0d3934d8d3334c0d2d34a8d273490d213478d1b3460d153448d0f3430d093418d033400cfd33e8cf733d0cf133b8ceb33a0ce53388cdf3370cd93358cd33340ccd3328cc733184c33300cbd32e8cb732d0cb132b8cab3
|8,1=>0x898e233880e1d3868e173850e113838e0b3820e053808dff37f0df937d8df337c0ded37a8de73790de13778ddb3760dd53748dcf3730dc93718dc33700dbd36e8db736d0db136b8dab36a0da53688d9f3670d993658d933640d8d3628d873610d8135f8d7b35e0d7535c8d6f35b0d693
|8,2=>0x27739d0e7139b8e6b39a0e653988e5f3970e593958e533940e4d3928e473910e4138f8e3b38e0e3538c8e2f38b0e293
|9,0=>0xbe0af62bd0af22bc0aee2bb0aea2ba0ae62b90ae22b80ade2b70ada2b60ad62b50ad22b40ace2b30aca2b20ac62b10ac22b00abe2af0aba2ae0ab62ad0ab22ac0aae2ab0aaa2aa0aa62a90aa22a80a9e2a70a9a2a60a962a50a922a40a8e2a30a8a2a20a862a10a822a00a7e29f0a7a2
|9,1=>0xcf0b3a2ce0b362cd0b322cc0b2e2cb0b2a2ca0b262c90b222c80b1e2c70b1a2c60b162c50b122c40b0e2c30b0a2c20b062c10b022c00afe2bf0afa2
|10,0=>0xd2c74a1d247481d1c7461d147441d0c7421d047401cfc73e1
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 14
def pmP:Nat→Nat
|0=>0x63f00000062f00000061500000060f00000060c00000060a00000060600000060000000040000000038c0000002d20000002ac00000028c00000021000000020000000015d0000000a000000008600000008400000008100000004200000002400000001800000001300000001000000000c00000000a000000006000000005000000004000000002000000000
|1=>0x468000000461f0000042b6000002f2f000002a8c00000278f0000026bf00000268800000263f00000240000000228c00000228000000220c00000171f000001000000000fef000000faf000000f3f000000e3f000000e1f000000d370000009570000007df0000007bf0000007af00000079f00000077f00000075f0000006bf0000006af000000682000000680
|2=>0x407bf0000407b700004079f00004078f00004075f00004073700004071f0000406bf00004068f00004063f00002063f00001079f00001071f0000106a500001004000000a68c00000a60c00000871f0000086bf0000086af0000086860000086420000086060000082060000080020000080000000050020000047f70000047bf0000047b70000046f10000046bf
|3=>0x20270f00020079f00020078f0002006040002004000001806bf00018063f00018022f0000806af00006041f00005278f0000507b700005079f00005071f0000500300000487570000486bf0000486af00004863f0000486040000450060000447df00004479f0000447770000442c500004278f00004278d00004261f00004241600004208400004171f00004168f
|4=>0x104068f00104061f00100529400100229200100208a00100208200100148600100100600084270f00084078f00080272f00080172f00080160200080142f00080072f0008006bf000800690000800288000600000000400f7f000400eaf00040077f00040073f00040062f0003807bf0002427af00024278f0002417bf00024171f0002407bf00024078f0002027af
|5=>0x280063f00280060f00204378f0020436bf0020427af0020427ad0020407bf0020086240020057bf0020057bb00200373f00200372f0020036af00200273f00200270f00200263f0020026370020017af00200173f00200163f00200162f00200079f00200078f0020006bf00200068000200063f00200063d00200063700180862f00104240200104140400104069f
|6=>0x704261f00704061f00700265f00700263f00700205f00700063f00600263b00600261f00600260f0060017af00600173f00600061f00500069f00400260000384068f00380561f0038016af00380165f00380163f00380068f00380063f00300065f00300061f00300060000284862f00280561f00280373f0028016ad00280161f00280105f00280078f0028006bf
|7=>0x8200006bf40604863f40204b73f4001c86bf40004877f40004863f40004463f40000440440000068020000250d20000201810008023f0c000062f08008063f08008023f04010463f04010027f04010023f03000063f02800063f0208006bf0200006bf00800068f00780165f
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x90000040000040000040000
|7,0=>0xc01000211074706000001190017041d49001700120000000000110876004100000200460d36000e00050418040b060600011600000045042c310a510c3409000f0203
|8,0=>0xc844d3d2441a852b1f1f4b5bee33a32aa9c4506197d737999fe8ab7b5eb174e1e5ba60a2684e9d149e3b2753efb8387826e28766c29c3277ca1fec88c6f08e7e373f62e4545a91967ccce91f6be364e7982d273d651f1fd98f1ea0621b1f522913a963423a21ed7aaf28489b1f591920b67d1f8a55ea8d38aa9415924b56a65d
|8,1=>0x35a79a714a674f9335a5a6a4e67f802810dbc1a1599f6c1e7059eb
|9,0=>0x86b584b9f16dc55fc7dd6f8cbb30c04d691f6a58cdf2c9ae2e90d6b24df358cbadc35c398b75deb0721fd5dad01f8af182f483e085d843ce23df5889bcf5b78ab45c2d2558bfadf73c6ef62fdc5840b3cf6995ac37b079bda873694c1fd12e821f6f
|10,0=>0x1fd42322238157be6d1f1fb5243e
|11,0=>0x1c
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 36 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_222 10 roots_222 ops++addP pm 1 dom_221 9 roots_221 ops++addP pm 2 dom_215 9 roots_215 ops++addP pm 3 dom_159 9 roots_159 ops++addP pm 4 dom_93 7 roots_93 ops++addP pm 5 dom_95 8 roots_95 ops++addP pm 6 dom_213 7 roots_213 ops++addP pm 7 dzo_79_16 6 roots_79 ops++addP pm 8 dzo_149_64 5 roots_149 ops++addP pm 9 dom_207 9 roots_207 ops++addP pm 10 dom_219 10 roots_219 ops++addP pm 11 dom_87 5 roots_87 ops++addP pm 12 dzo_157_64 6 roots_157 ops++addP pm 13 dzo_151_64 6 roots_151 ops++addP pm 14 dom_205 7 roots_205 ops++addP pm 15 dom_75 5 roots_75 ops++addP pm 16 dom_199 5 roots_199 ops++addP pm 17 dom_91 7 roots_91 ops++addP pm 18 dzo_207_16 7 roots_207 ops++addP pm 19 dzo_203_4 6 roots_203 ops++addP pm 20 dzo_203_16 6 roots_203 ops++addP pm 21 dom_143 6 roots_143 ops++addP pm 22 dom_85 4 roots_85 ops++addP pm 23 dom_151 6 roots_151 ops++addP pm 24 dom_149 5 roots_149 ops++addP pm 25 dzo_159_64 7 roots_159 ops++addP pm 26 dom_157 6 roots_157 ops++addP pm 27 dzo_206_16 6 roots_206 ops++addP pm 28 dzo_78_16 5 roots_78 ops++addP pm 29 dom_94 6 roots_94 ops++addP pm 30 dzo_217_4 6 roots_217 ops++addP pm 31 dzo_91_4 6 roots_91 ops++addP pm 32 dom_211 7 roots_211 ops++addP pm 33 dom_31 5 roots_31 ops++addP pm 34 dom_73 4 roots_73 ops++addP pm 35 dzo_150_64 5 roots_150 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_223 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_221 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_79_16_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_149_64_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_207 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_157_64_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_151_64_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_207_16_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_zo_203_4_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_zo_203_16_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_143 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_149 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_zo_159_64_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_zo_206_16_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_zo_78_16_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_zo_217_4_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_zo_91_4_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_zo_150_64_148 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_222 10 s (0,roots_222.map (·&&&dom_222)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_223 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_222 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_223 gM v ys):RunD true dom_223 gM v (ori ys):=h
def Z (s:Nat):=barP dom_223 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 12 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 68 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 68 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 155 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 27 128 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 155 → Z 8 i = true := (range_split z8_0 z8_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 98 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 98 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 14 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 14 0 = true)
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
def dzo_105_128:=0x30300000303000003030000030300000000000000000000000000000000
def gzo_105_128:=0x30300000302000003020000030000000000000000000000000000000000
def gsh_105_128:=0x303000003020000030200000300
theorem lowS_zo_105_128_97:Lower true dzo_105_128 roots_105 gzo_105_128 5:=lower_iso_b (d1:=dom_105) (r1:=roots_105) (T1:=gsh_105_128) [(dom_105,128)] (by decide +kernel) (lower_slice_b (T:=gsh_105_128) [(0x300000003000000030000000300,0,8)] (by decide +kernel) lowS_97)
def dzo_111_128:=0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000
def gzo_111_128:=0xffff0000fffe0000fffe0000fffc00000000000000000000000000000000
def gsh_111_128:=0xffff0000fffe0000fffe0000fffc
theorem lowS_zo_111_128_97:Lower true dzo_111_128 roots_111 gzo_111_128 7:=lower_iso_b (d1:=dom_111) (r1:=roots_111) (T1:=gsh_111_128) [(dom_111,128)] (by decide +kernel) (lower_slice_b (T:=gsh_111_128) [(0xcccc0000cccc0000cccc0000cccc,0,2),(0xf0f00000f0f00000f0f00000f0f0,0,4),(0xff000000ff000000ff000000ff00,0,8)] (by decide +kernel) lowS_97)
def dzo_103_128:=0xff000000ff000000ff000000ff00000000000000000000000000000000
def gzo_103_128:=0xff000000fe000000fe000000fc00000000000000000000000000000000
def gsh_103_128:=0xff000000fe000000fe000000fc
theorem lowS_zo_103_128_97:Lower true dzo_103_128 roots_103 gzo_103_128 6:=lower_iso_b (d1:=dom_103) (r1:=roots_103) (T1:=gsh_103_128) [(dom_103,128)] (by decide +kernel) (lower_slice_b (T:=gsh_103_128) [(0xcc000000cc000000cc000000cc,0,2),(0xf0000000f0000000f0000000f0,0,4)] (by decide +kernel) lowS_97)
def dzo_107_4:=0xf0f00000f0f00000f0f00000f0f0
def gzo_107_4:=0xf0f00000f0e00000f0f00000e000
def gsh_107_4:=0xf0f00000f0e00000f0f00000e00
theorem lowS_zo_107_4_75:Lower true dzo_107_4 roots_107 gzo_107_4 6:=lower_iso_b (d1:=dom_107) (r1:=roots_107) (T1:=gsh_107_4) [(dom_107,4)] (by decide +kernel) (lower_slice_b (T:=gsh_107_4) [(0xf0f0000000000000f0f00000000,0,32)] (by decide +kernel) lowS_75)
def dzo_99_128:=0xf0000000f0000000f0000000f00000000000000000000000000000000
def gzo_99_128:=0xf0000000e0000000e0000000c00000000000000000000000000000000
def gsh_99_128:=0xf0000000e0000000e0000000c
theorem lowS_zo_99_128_97:Lower true dzo_99_128 roots_99 gzo_99_128 5:=lower_iso_b (d1:=dom_99) (r1:=roots_99) (T1:=gsh_99_128) [(dom_99,128)] (by decide +kernel) (lower_slice_b (T:=gsh_99_128) [(0xc0000000c0000000c0000000c,0,2)] (by decide +kernel) lowS_97)
def dzo_235_4:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0
def gzo_235_4:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0e00000f0f00000e000
def gsh_235_4:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0e00000f0f00000e00
theorem lowS_zo_235_4_75:Lower true dzo_235_4 roots_235 gzo_235_4 7:=lower_iso_b (d1:=dom_235) (r1:=roots_235) (T1:=gsh_235_4) [(dom_235,4)] (by decide +kernel) (lower_slice_b (T:=gsh_235_4) [(0xf0f0000000000000f0f0000000000000f0f0000000000000f0f00000000,0,32),(0xf0f00000f0f00000f0f00000f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_75)
namespace S_239
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(2,10),(2,34),(2,66),(2,130),(3,11),(3,35),(3,67),(3,131),(4,36),(4,132),(5,13),(5,37),(5,69),(5,133),(6,14),(6,38),(6,70),(6,134),(7,15),(7,39),(7,71),(7,135),(8,9),(8,10),(8,72),(8,136),(12,13),(12,14),(12,44),(12,76),(12,140),(32,33),(32,34),(32,36),(32,96),(40,41),(40,42),(40,44),(40,104),(40,168),(64,65),(64,66),(64,72),(64,96),(68,69),(68,70),(68,76),(68,100),(68,196),(128,130),(128,132),(128,136),(129,131),(129,133),(129,137),(129,161),(129,193),(160,161),(160,162),(160,164),(160,168),(160,224),(192,193),(192,194),(192,196),(192,200),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffffffffffff
def xsM:=roots_239.map (·&&&dom_239)
def gM:=goal_239&&&dom_239
def NN:Nat→Nat
|5=>9
|6=>46
|7=>239
|8=>261
|9=>121
|10=>14
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0xf639fde847b38f8a682f8156375515754fc5f527159fc
|6,0=>0xff52ff79c0efc49ee1b9e1f7bd7a8dc4c25c2721c06afb17c9aa7f7a9e1ca5cdfa38d696fba93352903d6893cb86d0282c917abbd75539712f962c706273b60e2c5eefc5b43c44d0c3f2e23e5453dea13695c364722a4262a1342837226565160701568813e35108530938006b8a036cd00eff
|7,0=>0x8f22a8e26a8cf638bfed8b7518850f83c3b83b2a7ff1d7f9187f85c7f64f7cde07c9e67c6db7a3eb79ba37996478a6b7807577fa9764ed747ec72c0f723937214a704fb6f6506ed826e7c36baa36b5866b5606ac926a8b46954068444658a165170647f4640ae5f0215ef485e3ef5ae995a48759e6759e1d58f8a585bd5851f56dbd557c753fe353a335376c51b925129c51233507f65060f4ea424e99a4c0bd480e7451dd44ab4429dd41ba141981418af401113defe3c4e63bc933b6a43adaf3ab3c37b7235e71347ff3432a33f3132b5c319bc316c9315292e2332c3832b6622af1a2ad8d2974727b502493d2339f228911f4851ed3c1d84e1beed1bd0019bc8182d517a07174701592913e1f128e6126ec126b411d8d11d640efee0ef870dc55097e00904c087aa0860f07b5a0744d06f6c05f92030ad02da2013d200f76
|7,1=>0xfbd58fa557f9446f8ad4f8606f7ca0f7a91f70fbf671ef476df3ec8f3c8df2c4ef20f8ef5c8ef0bdee125ed6a7ec9e7ec816ebea7eae55ea3c5ea16de8c14e8638e84d9e6e26e6705e5e03e3f27e1cf3df09bdd1c4dca03dc8bbdc4eedbce8dab87da3acd9e9cd877fd84b7d8178d78fad6ebdd5cd7d5042d47dcd3933d1a11d06f6d0423cf7ebcf6a3ce950ce320ca505c9f2fc8ce9c7c41c50fdc4d88c4427c4036c2fefc1f47c1b4bbf9a5be239be0f3bc520bac23b9f4db7bc0b7837b7148b3e1cb26aab1fa2b1ddcb0cc5b0215ae514ae217ada88acbd7ac88aaadefa9e80a9467a8bbba62bda619ea5670a5058a4b62a3080a10729e3719d17d9c80e9c1ca98db3978889778d96b1394c41927e6924aa908fd
|8,0=>0x7256e701b77002f6eead6e4106ca7a6bfce6b5606899267f08665dc66571632e463162627a361289606405fa225e73b5ca615c9585af165a1585729a56b2656258554d254c99542e752e1f5278a50ae75087c4fe114f5994e1344e0b54c8b94b6ac4b39e4a0104577a4556b453b042b3241828410c7408d4406143fc893fbba3e2e93d21a3c6cf3ba093b53b3b4a33b29439efe38aa738178380a93786436844367d935ad93586a3564f3502d34e2534957345a5340123371c3366831b433104a305002f1822ecea2e4492e2c72e1572d9e52d58d2d2c32cf6928cbc25d072573a253d423ff022fec224fd212d42126d2103820c3d1de941db7c1dabc1c9af1bb8a1a4c01894d16ed816ad316966140d5138a5126ff121ea11cd20e41e0dde30b3020aa4f0a55f09b4208428080320741c05797043540399303069025d002218
|8,1=>0xf702bf37b9f21faf189af1449f01deef3b3ee035edd24ed683ed2b5ed125ebaf0e94e2e7140e608ee5e71e50dce45ede4470e2d33e1f7ee0e2cde7bcdda2edd189dc3f7db87cdaa3dda316d9b7fd7bdcd7120d6b55d53dfd5282d36a0d0766cd3f2cb303ca1b5c9a8bc9557c8deec7ed0c7d6bc6ee5c0010be546bddabbd79dbd18abcf13bc100bbf31baedeba8a9b91c2b897ab42fab4260b398ab1593b02fcae906adf97add89aafd5aae6fa9d35a8f16a8a47a7729a59a0a42afa3bb9a3ab2a2ecc9f8889f0149ed0d9ec619ec3f9dbae9d74e9d3bc9b2aa9b2a59a971998e298d4f986c197daf94a369429293f6d91e7291d34907a68e78c8c6598c3688c01f89fc08840a87a5d87742868c7866b8864fd844be83ff08368a8347b817007ff1d7e3677dae27ab1c799d0788377807577b517679c75c4675b6a75a9172edd
|8,2=>0xff305fb9f6fb8acf9ac7f795a
|9,0=>0xff874fbfeef8c90f88c9f6695f341bf0220ee5f2ed4d8ec94deb8d7e90aee564ae003adff84dd9abdb399da3a6da028d8da3d6c07d092cd0318cfe9dcc6c5c774bc6655c5a83c4009c1783c06c4bbeeabbdf8bb7acba993ba954b897ab53f9b22ceafcabaf5c6a7f61a5ae4a2e19a1e17a11b1a0d739b28b93b0b8f2cc89fc08760c8722d80d357f0037ad9d7635f729ed70ac66d9d36cf5f6cdc369ccd686a167bd2661c261d7f5f83e5646f5556753d245310e51dda513845033d4e5974cad04b9364983249559488a146b45465ae44c0d4280940f8c3fbd23f3743d13b3c2d73be09397a5377e2363a0358fb3245e32459322e82ea252c8862b70429a3528661221ca21bbb21ba2210d11e38a1bef41bacf16ed71529512bd711f01117cc10f770de090b0cb0a6b70575204c22
|10,0=>0xf63bce88e8e7c82da982d699ccacf5806367dfda704995dbf3460e032bb61023701464
|11,0=>0x3ce8d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffff0000ffff0000ffff000000000000ffff0000ffff0000ffff00000000ffff0000ffaa0000aaaa0000ffaa0000ffff0000ffaa0000aaaa0000aaaaffff0000ff000000ffff0000ff000000ffff0000ff000000ffff0000ff00fcfc0000fcfc0000fcfc0000fcfc0000fcfc0000cccc0000fcfc0000cccc555500005555000055550000550000005555000055550000555500005500fefe0000fefe0000fefe0000fefe0000fefe0000eeee0000fefe0000eeee0000000000000000fefe0000fefe00000000000000000000fefe0000eeeeffff0000ffff0000fcfc0000fcfc0000ffff0000ffff0000fcfc0000cccccccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000ccccaaaa0000aaaa0000aaaa0000aaff00005555000055550000555500005500ffff000000000000ffff000000000000ffff000000000000ffff00000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0111100001111000011110000113300001111000011110000111100001100ffff0000ffff00000000000000000000ffff0000ffff0000000000000000ffff0000ffff0000ffff0000ffff00000000000000000000000000000000
|0,1=>0x555500005555000055550000550000000000000000000000000000000000000000000000000000ff00000000000000000000ff00000000ff0000ff00ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000ffff0000ffff0000ff000000ff0000000000000000000000000000000000333300003333000033330000333300001111000011110000111100001100555500005555000055550000000000005555000055550000555500005500000000000000000000ff000000000000ffff0000ff000000ffff0000ff0000000000000000000000000000ff0000ffff0000ffff0000ffff0000ff00f0f00000f0f00000f0f00000f0f00000f0f0000000000000f0f000000000ffff0000ffff0000ffff0000ffff0000ffff000000000000ffff00000000ffff0000ffff0000ffff0000ff000000ffff0000ffff0000ffff0000ff0000000000ffff000000000000fefe000000000000ffff000000000000eeee11110000111100001111000033330000111100001111000011110000110000ff000000ff000000ff000000ff0000ffff0000ff000000ffff0000ff00ffff0000ffcc0000cccc0000ffcc0000ffff0000ffcc0000cccc0000ccccaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa
|0,2=>0xffff0000ff0000000000000000000000ffff0000ff0000000000ffff000000000000ff00000000000000ffff000000000000ff000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000000ffff0000ff00000000000000ff000000ffff0000ff000000000000000000f0f00000f0f00000f0f00000f0f00000f0f00000f0000000f0f00000f0000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0000000000000000000000000000000000ffff0000ff000000ffff0000ff0000ff000000ff000000ff000000ff00000000000000000000000000000000555500005555000055550000ffff000055550000555500005555000055000f0f00000f0f00000f0f00000f0f0000050500000505000005050000050055550000555500005555000055ff0000555500005555000055550000550000000000ffff000000ff0000ffff000000000000ffff000000000000ff0000000000ffff000000000000ffff000000000000ffff000000000000ff00000000000000000000000000000000005555000055550000555500005500aaaa0000aaaa0000aaaa0000aaff00000000000000000000000000000000ffff0000ffff0000ffff0000ffff00005555000055550000555500005500
|0,3=>0xffff0000ffff0000ffff0000ff000000ffff0000ffff000000000000000000000000000000000000000000ff0000ffff0000ffff0000ff000000ff00000000000000000000ff000000ff0000ffff0000ffff0000ffff0000ff00ffff0000ff000000ffff0000ff0000000000000000000000000000000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff000000ff00000000000000000000ff000000ff0000ffff0000ffff0000ff000000ff000000000000ff00000000000000ff0000ffff0000ff000000ffff0000ff00ffff0000ff000000ffff0000ff000000ffff0000ff0000000000000000000000000000ff00000000000000ff0000000000000000000000000000000033330000333300003333000033330000333300003333000033330000330000ff0000ffff000000ff0000ffff000000000000ffff000000000000ff00f0f00000f0f00000f0f00000f0f000005050000050500000505000005000000000000000000055550000550000000000000000000000555500005500000000005555000000000000550000000000000055550000000000005500ffff0000ffff0000ffff0000ff000000ffff000000000000ffff00000000ffff0000ffff0000ff000000ff000000ffff0000ffff0000ff000000ff00
|0,4=>0xf0f00000f0f00000f0f00000f0f0000ffff0000ffff0000f0f00000f0f0000000000000000000000000ffff0000000000000000000000000000ff00ffff000000000000ffff0000ffff0000ffff000000000000ffff0000ff00000000000000000000000000ffff00000000000000000000000000000000ffff000000000000ffff0000ffff0000ffff000000000000ffff00000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff00ffff0000ffff0000ffff0000ffff0000ff000000ff000000ff000000ff00ffff0000ffff0000ffff0000ffff0000ffff0000ff000000ffff0000ff00ff000000ffff0000ff000000ffff0000ff000000ff000000ff000000ff00f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f000ffff0000ffff0000fefe0000fefe0000ffff0000ffff0000fefe0000eeeef0f00000f0f00000f0f00000f0f00000f0f0000000000000f0f0000000f00000000000000000000000000000000000000000ffff000000000000ff00fcfc0000fcfc0000fcfc0000fcfc0000fcfc0000cccc0000fcfc0000ccfc0f0f00000f0f00000f0f00000f0f00000f0f00000f0000000f0f00000f000000000000ff000000000000000000000000000000ff0000ff000000ff00
|0,5=>0xffff0000ffff00000000000000000000ffff0000ff0000000000000000000000000000000000ffff0000ffff0000ff000000ff0000ff000000ff000000ff000000ff000000ff000000ff000000ff00000000f0f00000f0f00000f0f00000f0f00000f0f00000ffff0000f0f00000fff0f5f50000f5f50000f5f50000f5f00000f5f50000f5f50000f5f50000f5f0ffff0000ffff0000ffff0000ffff000000000000ffff000000000000ff0000000000000000000000000000000000ffff0000ffff0000ffff0000ff00ffff0000ffff0000ffff0000ff00000000000000000000000000000000000000000000ff00000000000000000000ffff0000ffff0000ffff00000000ff000000ff000000ff000000ff000000ffff0000ffff0000ffff0000ff00ffff0000ffff0000ffff0000ff0000000000000000ff000000000000000000000000000000000000000000ff00000000000000000000000000000000aaaa0000aaaa0000aaaa0000aaff0000aaaa0000aaaa0000aaaa0000aaaa00000000000000000000000000000000ffff0000ffff0000f0f00000f0f00f0f00000f0f00000f0f00000f0f00000000000000000000000000000000ffff0000ffff0000f0f00000f0f00000ffff0000ffff0000f0f00000f0f0
|0,6=>0xff0000ffff0000ffff00000000000000000000ffff0000ff000000000000ff00000000000000ff00000000000000ff0000000000000000ff000000ffff0000ff000000ffff0000ff000000ffff0000ff000000ff00ffff0000ffff0000ff000000ff000000ffff000000000000ff0000000000000000000000000000ff000000000000ffff0000ffff0000ffff0000ff000000000000ff00000000000000000000ffff0000ffff0000ffff0000ff00ffff000000000000ffff000000ff0000ffff000000000000ffff00000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff00000000ffff0000ffff00000000000000ff0000ffff0000ffff0000000000000000ffff0000ffff0000ffff0000ffff00000000000000000000ffff0000ff00fff00000fff00000fff00000fff00000fff00000fff00000fff00000fff0ffff0000ffff00000000000000000000ffff0000ffff0000ffff0000ff0000000000ffff0000000000000000000000000000ffff000000000000ff00ffff0000ffff0000ff000000ffff0000ffff0000ffff0000ff000000ff0000ff000000ff000000ff000000ff000000ff000000ff0000000000000000555500005555000055550000555500005555000055550000555500005500
|0,7=>0xff000000ff000000ff000000ff00000000000000ff0000000000000000ffff0000ffff000000000000ffff0000ffff0000ffff000000000000ff00ffff0000ffff000000000000ffff0000ffff0000ffff0000000000000000ffff0000ffff0000ffff0000ff000000ffff0000ffff0000ffff000000000f0f00000f0f00000f0000000f0000000f0f00000f0f00000f0000000f00ffff00000f0f0000ffff00000f000000ffff00000f0f0000ffff00000f00f0f00000f0f00000f0f00000f0f000000000000000000000f0f00000f000ff000000ff000000ff000000ffff0000ff000000ff000000ff000000ff00ffff0000ffff00000000000000ff00000000000000000000000000000000ffff0000ffff0000ff000000ffff0000ff000000ff000000ff000000ff00f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f000000000ffff0000ffff00000000000000ff0000ffff0000ff000000000000000000f0f0000000f00000f0f0000000f00000f0f0000000000000f0f000000000ffff000000ff0000ffff000000ff0000ffff000000000000ffff00000000fcfc0000ccfc0000fcfc0000ccfc0000fcfc0000cccc0000fcfc0000cccc0f0f00000f0f00000f0f00000f0f000000000000000000000f0f00000f00
|0,8=>0xffff000000000000ff00000000000000ffff0000ffff0000ff000000ff00000000000000000000ff000000ff0000000000000000000000ff00000000ff000000ff000000ffff0000ffff0000ff000000ff000000ffff0000ff0000000000ffff000000000000ffff00000000000000000000000000000000ffff000000000000ffff000000ff00000000000000000000000000000000ffff0000ff000000ffff0000ffff0000ff000000ff000000ff000000ff00aaaa0000aaaa0000aaaa0000ffff0000aaaa0000aaaa0000aaaa0000aaaa0f0f00000f0f00000f0f00000f0000000f0f00000f0f00000f0f00000f00ffff0000ffff0000ff000000ff0000000000000000ff0000000000000000ffff0000ffff0000fff00000fff00000ffff0000ffff0000fff00000fff000000000ffff000000000000ffff000000000000ffff0000000000000000000000000000000000ff000000ff00000000000000000000000000000000ffff0000ffff0000ffff0000fff00000ffff0000ffff0000ffff0000fff0555500005555000055550000555000005555000055550000555500005550ffff0000ff000000ffff0000ffff0000ffff0000ff000000ffff0000ff000f0f00000f0000000f0f00000f0000000f0f00000f0000000f0f00000f00
|0,9=>0xff000000ff00000000000000ff000000ff000000ff0000000000000000ffff0000ffff0000ffff00000f0f0000ffff0000ffff0000ffff00000000ffff0000ffff0000ff000000ff000000ffff0000ffff0000ffff0000ff00ffff0000fff00000ffff0000fff00000ffff0000fff00000ffff0000fff0ffff0000ffff0000ffff0000ffff0000f0f00000f0f00000f0f00000f0f0050500000505000005050000050000000505000005050000050500000500ffff000000000000ffff000000000000ffff0000ffff0000ffff0000ff000000000000000000ffff0000000000000000000000000000ffff0000ff000000000000000000ffff0000ffff00000000000000000000000000000000ffff0000ff0000000000000000000000ffff0000ff000000ffff0000ff00ff000000ff000000ff00000000000000ffff0000ffff0000ffff00000000ff000000ff000000ff000000ffff0000000000000000000000000000000000ff000000ff000000ff00000000000000ff000000ff000000ff00000000ffaa0000ffaa0000ffaa0000ffff0000aaaa0000aaaa0000aaaa0000aaaa0000000000000000ffff0000ffff00000000000000000000ffff00000000ffff0000ff0000000000000000000000ffff0000ff00000000000000ff00
|0,10=>0xff000000ff000000ff0000000000000000ffff000000000000ff00000000000000000000000000000000000f0f00000f0f00000f0f0000000000000f0f00000f0f00000f0f00000000ff0f0000ff0f0000ff0f0000ff000000ff0f0000ff0f0000ff0f0000ff00000000000f0f0000000000000f0f00000000000000000000000000000000ffff0000f0f00000ffff0000f0f00000ffff0000f0f00000ffff0000f0f0ffff0000ffff0000000000000f0f0000ffff0000ffff0000000000000000ffff0000ffff0000ffff0000ffff000000ff000000ff000000ff00000000ffff0000ffff0000ffff0000000000000000000000000000000000000000ffff0000ffff0000ffff0000ff000000ff000000ff000000ff000000ff000f0f0000000f00000f0f0000000f00000f0f0000000000000f0f00000000000000000f0f0000000000000f000000000000000f0f0000000000000f00ff000000ff000000ffff0000ffff0000ff000000ff000000ff000000ff00ffff0000ffff000000ff000000ff0000ffff0000ffff000000000000000000000000ffff000000000000fff0000000000000ffff000000000000fff00000000000000000ffff0000ffff00000000000000000000ff000000ff00
|0,11=>0xffff0000ffff0000ffff000000000000ff000000ff000000ff00000000000000000000000000ffff0000ff00000000000000000000000000000000000000000000000000ffff0000fff000000000000000000000ffff0000fff0ffff0000ffff0000f0f00000f0f000000000000000000000000000000000ffff0000ffff0000ffff0000ffff0000ffff0000f0f00000ffff0000f0f00f0f00000f0f00000f0f00000f0f00000f0f0000000000000f0f00000000ffff0000ffff0000ffff000000ff0000ffff0000ffff0000ffff0000000000000000ffff000000000000f0f0000000000000ffff000000000000f0f0ffff0000ffff00000f0f00000f000000ffff0000ffff00000f0f00000f00ff0f0000ff0f0000ff0f0000ff0f0000ff000000ff000000ff000000ff0000000000ffff00000000000000ff000000000000ffff000000000000000000000000ffff000000000000ffff000000000000ff00000000000000ff00ffff0000ffff00000f0f00000f0f0000ffff0000ffff000000000000000000000000ffff0000000000000f0f000000000000ffff000000000000000000000000000000000000000000000000ffff0000ffff0000ffff00000000000000000000000000000000000000000000000000000000ffff0000ff00
|0,12=>0xf0f00000f0f00000ffff0000ffff0000f0f00000f0f00000f0f00000f0f000ff000000ff000000f0000000f0000000ff000000ff000000f0000000f000000000000000000f0f00000f0f00000000000000000000000000000000ffff00000f0f0000ffff00000f0f0000ffff000000000000ffff000000000f0f00000f0f00000f0f00000f0f00000f0000000f0000000f0000000f00ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000f0f00000f0f0ffff0000ffff0000ffff0000f0f00000ffff0000ffff0000ffff0000f0f0f0ff0000f0ff0000f0ff0000f0ff0000f0f00000f0f00000f0f00000f0f000ff000000ff000000ff000000ff000000ff00000000000000ff000000000000000000000000ffff0000ffff00000000000000000000f0f00000f0f000000000ffff000000000000ffff000000000000f0f0000000000000f0f0000f0000000f0000000f0000000f00000000000000000000000000000000f0f00000ffff0000f0f00000ffff0000f0f00000f0f00000f0f00000f0f0f0f00000f0f00000ffff0000fff00000f0f00000f0f00000ffff0000fff000000000000000000f0f00000f00000000000000000000000f0f00000f00f0f00000ffff0000f0f00000fff00000f0f00000ffff0000f0f00000fff0
|0,13=>0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f0000000000000000ffff0000ffff0000ffff0000ffff0000fff00000fff00000fff00000fff000ff000000ff000000ff000000ff000000f0000000f0000000f0000000f0
|_,_=>0
def sP:Nat→Nat
|0=>0x1023011c050403072201210504030720011f0d0307101e0100050403070b1d1c05040a090c01000504030b1b0100050403071a01000d19160307100118050403071001150d040c100100040a0c140100050403130100120503070b010f04031110000f0403070e000d040c0b010005040a090800050403070601050403020100
|1=>0x53003071038370504030b3601000d0307103501000504070b34010005040a080100150403073332000d31300307101d2f0403070b2e000504070b2d01000f040307102c0005042b070b01000504070b2a0100151205030710010d0417070b0100050403072701000504070b260100050403072501000d0307102401000d0307
|2=>0x710010d0f040710410100054703071001380f0403073332000d120f03071001050446070b01000504450a0c01000504421001000504070b4101000d300c100100053040030710000d16300307103f053e04030710013d050403071001160403070b013c0d053a0307100139053003071001290503070b0128390f0403071001
|3=>0x50403070b33004a0504030710011c050403070b01003c050403070b010021050403070b0100580d57040307100100560d0503071001000d0403070b2e010005040307100155000d050403075301000d0530071041010005044f0710014d0f040307100100154b0403071001000f040307102301002f0f050403070b00120503
|4=>0x1000055e0403071001540d050307105d01000f0403070b32010005300403070b1d0015290503071001280d05300307103f000d0f0307105d010005045c0710010005045b03070b01000d040307105a01000d300307105a01000d050307101d1c0530040310360100590504030710014c0504030753010015050403103601000f
|5=>0x12815050403071067000d0307102e0100280d0403071023010066053004030710000d30030710230100050403070b0100510d05044607100100151604030710013c0d056503070b01000d040307106301000d0562030710010005040307200b010015050307100161005f053004030710000f05040307600100155f05040307
|6=>0x7101d586f050403071001000d056d03071001000d0f4703071001000d300307102e1d000d05470307101d010d6c030710010005040307102401006b05040307100100050403071023011c6a050403071001000f6904030710010068050403070b0100050446071001000d1630030710011c0530040307106700640d05030710
|7=>0x5e0403070b01000d2f0f03071000280d057603071001000d0475071001000d05300307101d1c05040307100174000f050407102a01000504711001000d0403070b32010005300403075301000d2f1630030710002f050407107001006405040307100137150403070b2e01001505040307530100150504071041010005300403
|8=>0x5300307105d0100680504030710015815050307105d01000504030710016e000530030710016e000d0f040307107d000530040307103f000d7c0403071001000d0578030710010005040307600100050403070b01001c0f04030710016e000d7a300307100100050479071001000d0f7803071001000d0504030760010005
|9=>0x1001504030710230100152f050403070b00310530040307101d15050446071001000d05040307820100810f0403071001000562040307100100050403070b800100050307102e017f002f0f040307102e000d1905030710010069055e04030710010f05040307107e000504080c1001000d690403071001000d693003071001
|10=>0x5030710018700050407102a010005860403070b01000f6d04030710010005300403070b330005040c101d014a050403070b010015050403070b33000d3017071001000d050407102a0100050403078201000d306c030710010081050403071001002f05300403070b000f0407102d0185008105300307100100053004460710
|11=>0x53b0403070b010005300403076001002f050407104101000d2f300307102e0005625e040307100105308a030710010015050403076001001505040307101d1c0d05302b071001000d0f0407102d01000d0f040307890100150403070b3201000f05040310360100390504030710010d0f042b07100100050403070b8801000d
|12=>0x2815690403071001000d160403070b01000d050407107001000d31040307100100050403070b01001f0d3130030710010005307803071001002f040307102e00050403070b7b01005f0f05040307100015057803071001000d0403071090010005308f040307101d48050403070b0100050403070b0100548d05300307100100
|13=>0xd04170710010048960504030710010530030710017f00050403070b01008405300403078201000d0503070b010028050444071001000d040c100100590504030710015415050403078201000d9503071001000f05040307106700050407107001004a05040307100158050403079201001505040307107d000d050307100138
|14=>0x10000d5f0f0403071000053b0403071001580f0403070b2e01000f05040307530100480f04030710013c0d961604030710010504031036010005300407102a01000d0530030710380015050407102a0100050403070b22010005040a0c01000d290f03071001280d05300307101d3705040307100138370d0504031036010015
|15=>0x30710000d0f0403071067001505042b071001000d16040307100158290f040307100137480d05030710011c0d053b030710011c0d5f0530030710005905040307100184050307102e016100480530030710013c590d05030710012805300307103800050403070b01003748050403071001580530040c100100980530040307
|16=>0x40c1001970d055e0307100184050403070b9a0100590504030710013729050403070b0100053a04030710010d05300307106700152f040307102e00055e040307107d01290530030710013715050407102d010015050403078901000d0307102e0100844805040307103f0105305e040307107d0d1630030710013c0d660530
|17=>0x50307101d01280504030710019f000d163003071001001505040307108001009e0504030710010005040307102e0100840530040307101d8c050403070b01004c0d16030710011c9d0d0503071001009c050403070b010005049b03070b010083050403070b010059050403070b01000d1205030710010d16040307103f0105
|18=>0x3705860407107b01000d05040307100138002f05040307100100510d05040307101d0137050407104101000504030710a10100160504030710011c4d050403071001000f04030710018500152f053004030710000d0f0307100100280504030710230100590f050403071001000d050407104101000d05300307100100840d
|19=>0xd5f05040307100100150d050403070b01001505040307108801000530a303071001000d05300307101d000f0504030710010058050403071001380015058604030710010005040307101d01370d05300307100100370d05030710a201004a05300403071001000d910403071001004a15050403071001000d0f0403071001
|20=>0x30710a8010005a604030710010005300403070b01000530040307105a0100050475071001000d290f0403071001005f050403071001000530030710016100053b04030710011c0d660504030710010015050403070b01000f05040307104e010005040710a501000504030710a401000530040307108801000f040307102e01
|21=>0x7108e01000d0f0403071001004c66050403071001001605040c10010015480504030710010005049b0307102e01001505040307100100547a050403071001000d29053003071001009c0d0f0403071001000d0f049b030710010015053b0403071001000d05040307106701000504030710a901000f05040307105d01000504
|22=>0x7100100770d96050403071001000504030710af01000f05040307107d0005040307100100ae055e0403071001840504030710670100055e04030710018c05ac0403071001009c0d053003071001000d05309b0307100100830d05040307100100590d050403071001001505040307107b010005300403071001005405300403
|23=>0x7100100581505040307100100842f0f050403071000150d050307100100280d0547030710010005040307102e01008b0d0f0403071001003cb0050403071001000530040307102301009605040307100100480d05040307100197830504030710010059050403071001006905040307100100150d160403071001002f050403
|24=>0xd0504030710016e000d16040307100197050403071001b200050403071001008b05040307100100580530040307102e1d00680f0403071001850005046c030710010005041707101d010d040307102e01000d300307102e010056050403071001000d053003071001003c480504030710019716053004030710011c0d050403
|25=>0x1000f05040307890100056d0403071001850005040307102e0100510d0f040307100100511505300403070b010005040307103f0100050403071001b5000504030710016e0005040307104e01000504030710b41d010d0503071001001c150504030710010037150f040307102e010005040307101d1c0d05040307103f0100
|26=>0x1559050403071001000d2f053003071000810504030710010005305e04030710018c1529050403071001000d2f0f04030710000f05b60403071001000d680f04030710010005620403071001000d0f6503071001007a0530040307100100810d050403071001000f05780403071001000d05300307100100510f050407102d
|27=>0x547040307101d01152f0f0504030710000f4b040307100100482f050403071001000d041707100100680504030710010031050403071001000d0504030710b7010015050403071001004c8305300403071001005905300403071001006905300403071001009c15050403071001001505049b03071001008315050403071001
|28=>0x10005300403071001005815050403071001003c0d05305e030710010099050403071001000530046c0307100100150504030710010058640d0504030710010005040c1001000d2f16040307100100056d040307100100150d040307102e01000d058603071001000d04030710b801000d0f0450030710000504030710b70100
|29=>0x307100100150530040307101d008d0504030710010005042b07100100b90f050403071001000d053003071001001c0d2f050307100100280530040307101d1c64050403071001000d0504030710010077053004170710010005300403071001008b4a0f0504030710010015040307102e0100050452071001510d05042b0710
|30=>0x7d00150d056503071001002f05040307100100370f05040307100100540d0530030710800100058f04030710010005623004030710010005040710ba01000d0f040307108001000d680403071001000f050403070b010005780403071001000d050307107b0100050407102d01000504030789010005040307100100770db104
|31=>0x50403071001004a0d050403071001002f05300403071000662f05040307100100152f05040307100005040307104301003105300403071001000504730710010015680504030710010005040307101dbc0d05030710010084680f050407102d01001505040307100100510d4b04030710010005041707100197053004030710
|32=>0x161000504c00307100100290503071001280504bf030710010005040307105a2e0100480504030710013c99053004030710010005040307100100944a050403071001000d05040307108801002f05049b030710010005b604500710010095050403071001000d290503071001280d058630030710010005040307100100bebd
|33=>0x3071001001c050403070b010005040307105a0100480d053003071001000d050403071001005429050403071001370504030710c101000d053b3003071001000d1604030710013c480d0f040307100100053b040307102e010015055e0403071001000d050403070b01000504030710880100b9050403071001000d05030710
|34=>0xf050403071001004caa050450071001000f05049b030710010005040307101d018c0d16040307100100c20504030710010005308f0403071001000562040307107d01000530040710ba0100050403071001005405040307108e01001604030710013c05040307107e0100150f050403070b01000d05300307107b0100150504
|35=>0x100aa053004030710010005040307100100370f0504030710010028050452030710010005a30403071001000586300403071001000d0504030710010037aa05040307101d010016053004030710010005040307100100bc050403071001850005040307100100840d0503071001002805040307100100ab0504c30307100100
|36=>0x10ba01002905040307100100150f050403071001000530040307107b01009c0d050403071001000d05049b0307100100050403c607100100053b3004030710010016050403071001970d29050403071001000504030710c5010005040307100100c40d05300307100100050403071001610005040307102e01000d0f04030710
|37=>0x300403071001008405040307101d0128054904030710019705300403071001008c0504ca0307100100680f05040307100100c9050403071001000565049b07100100050403071001004c0504c8030710010005040307101d0185000504030710c701009c050403071001000f0504030710010051056549030710010005040307
|38=>0x10010015050403071001000d05040307100100510504030710b40100150d050403071001000530040307102e01000530040307101d000504030710cb01000504030710b801000504030710a201000f050450030710000d05040307101d010005041707100100050403071001003c1605040710ba01000d050403071001003c05
|39=>0x40307100100a705040307100100cd055e0403071001001605049b030710010504500710010051aa0549040307100100054904500307100100cc0504030710010005470403071001004b050403071001000f0565040307100100680504030710010005040307109301000530049b0307100100b1050403071001000d05650307
|40=>0x1d010d05040307100100970504a003071001000d2f0504030710010005040307108001000504cf030710010005300403071001005105040307107d01001505300403071001000504030710ce01000d05040307108001000f0549040307100100aa1604030710010005040710ba010005b6040307100100050403071001001c05
|41=>0x565045007100100050403071001d2000549040307101d0105305e040307100100bb05040307100100160504030710015105860403071001000d050450030710010005049b030710018c05d10403071001000504030710d001000504030710ad01000504500307101d002f050403071001007205040307100100160504030710
|42=>0x30710010051053004030710010005040307101d0100050403071001002805049b03071001000d05040307100100050403071001008c0f05040307100100160504170710010005040307107b01000504030710b301004805040307100100053b04030710010005300403071001001c0591040307100100480d05040307100100
|43=>0x50403071001000549040307100100aa0504030710010005045003071001001605040307100100050403071001009705650403071001000504
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x30601530091803cc018600930031800cc0006
|6,0=>0x2dce16770b038565c2a4e14c60a2b84fd8270e13170953848dc238e11570873841dc200e0f97079383adc1c8e0de606bb8341c192e0c2705db82d1c15ae0a6704fb8261c122e08a7041b81f1c0eae06e7033b8181c0b2e0527025b8111c07ae0367
|7,0=>0x1b240d7206a9034d71a2c0cf6066b032d8192c0c76062ce30e818340bfa05ed02ee817340b7a05ad02ce816340afa056d02ae815340a7a052d028e8143409fa04ed026e81334097a04ad024e8123408fdc46f022f8113c0881c43102108104b880603f301f180f4c078603b301d180e4c0706037301b180d4c068d8337019380c5c060e02fac1758
|7,1=>0x2ad415518a990544829eb94d60a5ce526828f4145a0a1d0506827f413da09dd04e6826f4135a099d04c6825f412da095d04a6824f4125a091ee487823fc11de08df0467822fc115e089f0447821fc10de0860e4288210410620822e4098200c0fe607e303e981f138f6a07a503ca81e230ef2076903ac81d240e720729038c81c240df206e9036c8
|7,2=>0x3a741d1dce7f07378397c1c9e0e42c7198388c1c260e0306f98378c1ba60dc306d98368c1b29cd88c6bc835a41ab5cd4b069e734b41a3dcd0f067f833bc19be0ccf065f832bc193e0c8f0640731c418c20c510620830c418420c11060082fc417c20bd105e082ec417420b9105c082dc416c20b5105a082cc41645cb13058182bcc15c9cad505628
|7,3=>0x22fe1170e8b0845442282113108908444ba20610f6c8738435c218e10b7085474264211210790834841642092103908148406420120ff907f483f641f920fb907d483e641f120f7907b483d641e920f3ae79583c6c1e19cefd077683b741d9a0ebd07568
|8,0=>0x56d4ab4655912ac0855bcaaba554b2a9c9549caa2e15052a7a8539429aa14c32a5a7528ca92614830a3985184a8a2143f2a1875084281e53ff09f694f6ca79253b909d484e5ca70e137529b284d4ca6861331299084c3ca5fa52ed096d94b24a56e52a8e94c84a2424f21269092b9491c246e1225290a8480ca3e611e308e984704a362119f28c78
|8,1=>0x67b433b659c92cdb96694b32a19850cba8659432aa19450c9996484b225d9012c779637c319e18bf0c5786274b116587b0c3676174309a183d0c159606c301257f72bf295f542f8657b30bd095e3caefe176d2bae85d2cae76172b0b8d85c24adee56e52b6a85b142d6a16a50b4a85a142cea16632b28958fcac5a561b2b04957dcabca55d50ae37
|8,2=>0x7893bc2dde070efb87794bbaa1dc6eeda9768cbb225d810eb88757cba9e1d3d2e959746c3a19dcfd0e7597364b98e5cb70e529724cb9025c74ce319714c38825c310e108704438021bf10def96f3c377a5baeedcf86e3c36fa5b6b2dac96d1cb66a5b232d8896bfcb5da5add0d6686aecb5525a990d43969d4b4ca1a550d21968c4b43e5a0d2cfe8
|8,3=>0x89244475e22b110c9881cc3ea61e6f0eb88714c36661a310c988604c2e2215f30a6984ecc256211b1085883ec41d620dcf066882ecc15620993044881e440ce60553022880d4404a2013300187fcc3fc25fd10fdf97ebc3f3e1f8d2fbf77db4bebddf4f0f9e97cacbe361f0cef7e87bacbdb25ec72f5a97a943d265e84ef399798c3ca61e430f198
|8,4=>0x114e88a2cc4f26269112c8
|9,0=>0x9b244d6e66a5334a89a144cea2665132a8990ccc69e625130a8980ccbe265e112e8896fccb5e259d32c6895f44ada255d12a5994ec4a5625193284893e449d224d73262992ccc9426491123f991bc48ba644d121e890b4483a240d11fe88facc7b623c931dc88ea4472e638531b998d84c6a22341119888c8446222301117798b7c459a62bd11568
|9,1=>0x153a8a99454aa2a45151a8a88cd4262a0134f88a78453a229bf34d78a67c531e297d34b68a574529a293d14968a474521a28fd14759a36c519268b914548a25cd10e287534328a14cd082683114117a04c500627f313f189f4c4f8627b313d099e3ccefe276f13af89d34ce7a272d138d99c2c4df626eb136c9
|10,0=>0x2b5515a28acd4564a2b1515828abd455ca2ad515628aad4554a2a9515428
|11,0=>0x15b27
|_,_=>0
def wAt:=mkWire dB 211 240 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x50442c071510c3c112928414050400834030504428050c1045c1d160301401440740d0f2e00c14c204014100517074580c050041411040141401013c4340005044ec7330004c00005044a4dd0d00810050d00c14052937434020d00c30050c1045c1d16030140101004c00004014a4a10d01410020d00c14110a01c304117074580c05004340517074580c050041411
|1=>0x401404014a07c540105304415115008340505045281f150043405050442c071510c3c110501454430d00034050f3cc14050d00054a30400834051510c54170d01414111054454020d01410054803c34010504549455000c0c050300815390f49814050400415310f0443c020501528170f49414050400454431501c3c1105014a4a10400834030504414054803c3401
|2=>0x403454430d01414116405ca4050d00d1c050437434020b00454430d01414113b04cc0010530410054a01c54010530410054a10c3d250400434054801c340105045281315004340505044142e1510c3c110501404011510c14c10d01410020d00c1411013c410050d00014110f004140503434b8030530810051510c340505044b8011505c34052e0041005300001411
|3=>0xd004141101004540004014bcdd0d01c34020504411b90d1d804010504414050d00804010530804010d00858c00401414010504454733000010050554454020f04414051510d280c15004340505044c0000500405511500814c10401410020d00c14110137434050d00814114a05c54010d01414113000410051510c340505045280c1500434050500434000d0141411
|4=>0xd01414114a10c54010d01414111510cc0000530435a2050443c01050141411057b4c00f04015980c2f0043407050443c0205015284315004340504774bc020d01c1411680303c010501414113000010050100520bf0d00414114a03c3d2504005cc1d7203014a104008142e1510c34050504441511500814c10d01c54431505c34050504454020d01414110d015200f
|5=>0x4a03054010d01414118310c540d0d0143531050443c0205014c1511500810051510c34050504454171501c3c1105014347305044c0000401538050f498140504004300517074580c0500415511500834050504414113000810054a04c5401053041005150003c110f005a0130f0443c0105014108e053b8c0010401405611500014c1053f404f10d0001411045445402
|6=>0x4803014050d00414112930810050d00d280f150043405050442c071510c14c1040145c1d01004580c0500454011510c3405050442c071510c340505044580c04014140105045280f1500434058310c16193003410051510c54070530410056803da0170f00414056904416113000810054a03054010530414ee3000414c10401454071510c3405050440401300001005
|7=>0x401434071505c34050504528070f49414050400411511500834050504436471601c14011510c34050d00412391630c14010401528431500414c10d01c10056200d1c05048c4122d2e00814c20401454010d014141105304c0000401404014803010050d004141105045a00f0f0041405104c414110f0081405050b8340505045281f0f49410012937434020d00c1411
|8=>0xd004365f05044116a2e00414c2040160c4305864c00d1510c10020d0140d0f2e00c14c2040145c1d16030140105044540d0d01414110f28c14110501410020154454020f04414056603cbc010d01c1411109464c020f04c1405014c43c110f00814050530416113000810051510c340505005980f2f00434070558454000d0141411051c4c0000401411511500814c1
|9=>0x400814110d1d014110401404010d00454000d0145c1d04014580c050066407055e4c0030d00414111505c54430f04414051054454020f04434000501434010d97c040205005281f15004340505045280f1500414c10d1d014114a03c54010d01414110c1045c1d1603014010501410020d00c14110d00804010d008347405045281f1500434050d014580c050041411
|10=>0x1603014013000cc0020504454430d01414111510c34050d00d7a1130008c0030401410050d00814110d01c54170d01414110d00810050d00c3c116803c3c01050143c11050143401013c4340004014340004014140105044340205045200c0d014340105044140115000340505044340205014340330000340105044c0013000014110d00414110d00410050d0005403
|11=>0x504414050400814ee041d404011500c3c1105015200f0d0041411300081005050440401040081411047d806310500810050500414110d03c3405050443d45050140c023000814c20401414020100454430f008140530000100505004141164044a4050d00c14111510c34050504454430d01414110d01414112928410020d00c14110500404f10d0001411170740402
|12=>0x3000810050504410050100454000f04414050d1d004010504414c13003410050100434020504410050d00814110504404a10400854010530410051601c14010504454010d014141105014340205046180f3003410050d1d004010504434070504404010d00814114803c340105044161a3003410053000014010401416814901c10016805c3c01050145407053041005
|13=>0x1ab6a80205035a0130f0041405930043c1305014129d0f00014051510c14c104014b8010530810056803014750100414050d00c14114801c340105044ec1330004100530000c00104014bc010d01c14111510c3405050443d260501410017203c14a1040080cba0530810051503c14c10401454170f04414054801c34010504454430d01414111503c3405050441211
|14=>0xd008141105008c0030401412b50f03c140504014340d0504410050300414111503434050504454030d014141105304c00f0401454020530410051630c14010401414110f00814052f0043407050445c1d1603014010d01434010504414c20401454020d0141411057b4c00f0401410050d00c141105014340d0504414050300414113000414c10401404dd0d0081411
|15=>0x500410051500034050504414c13000810051501c3c110501410020d01414110437434020504414c20401414050d00014112f00c34070504414ee3000410050d97c04020504404020d004141105864c00d0401454030d014141105844c0020401434050500414110d01c14110d97c0402050443d27050141001014c43c0205014b80005308100530008c0030401404dd
|16=>0xf498140504004040105498100105044c0000401434050d00814111505c3c1105014c000040140401013c434000504434760100414110100814010504416ce015140c022e00814c20401454000d01414110100414c204015a0170f00414051630014010401404011603014011505c3405050441411053081005b10443c030501410050d000141101008340105044c000
|17=>0xd01c14114b044165d0100814023000c10050d01434030504414050d01c14110451414050300814110f0041405470141231050081411040341405057b4c00f04014365d010081411044c43c020501410050300814116803c3c010501441310f00814050485414760100414c20401414050300814111510c14c10401404f10d000141105a2804a1040081216051d80401
|18=>0x100454170d014141105044c00d040141542030141411050140c050504600050d03c1411048c414020100454070f0441405054c43c020501434070d004580c0500414110f4c43c0205014147130000100580014340f050443c110f008140505864c00d04014540305304100505844c00204014340d0d014141103004340505044540d0d01414111500c3405050441005
|19=>0x501410023000010050504410020d01c141130000100501004a4050d00c14112f00834070504410051603014012e00814c2040143d250501410011505c3405050454003030140c024803034010504454000530410050d00034050504414113000c1005055e4c0030401458c005004100515000340505044a4050d00c141117074580c050043407050041411048541476
|20=>0x10080402160301401018c4140204014100d0d01414110d01c1411150083c110501410050d03c1411308cc140204014c231050081005bb03ea8010503414050d03c14110f00414050504454430f0441405044c43c0205014c00f0401414116803c14750100441310f00814052f00834070504414110f00c14050530410050100644111601c1401480303401050443ca1
|21=>0x501454010d01414111503c3405050443407050441145030140c020f28c14050400810020d00c141130034100505044bc000d01c14119c01ea8110503454010d01414111501c14c104014340705044bc050d01c14112e00c14c20401414713000010057203014a1040083c110f0041405500000c050100414113000810056803c3c0105014340503008141105044165d
|22=>0x401454430d01414112e00414c20401410050d00414111500834050504434020d00c14112f03c340705044c0010401414110d00014010504414050d00414110401414c13000c10051510c340505044540f0d01414110f2841405040081411041d80401032e414c20401410020d00c14110f490140504004b8010530810050d00034010504415793000c1005930083c13
|23=>0x497404023003410050d008141101004140d050041005500000c05051d80401300081005040081411aa008140d038c414020f008140503014140d0300414050500804010500414112f034340705044c233050081005047d406310500810051603c14011500834050504458c30500410050d000140105046d0050549810011510c3c110501414113003c10053000014c1
|24=>0x50081005031d404010f0041405aa014140d040340c010f0081405032841002051d804011604c1401aa044140d050140c020403410011603c14010d00c14110f04414053003c10050d03414110300414119b01c0c013000410050100814010d00c1411059b80c0165008100d040141411041d8040105308100505014141104014140d0d00814110501410025000c0c05
|25=>0x3000c1005050040c01030140c0204004140d030141001055140c02048c41402059740402040341405051d404010f04c14050300410050f00c14050403414110d01414110300814110549810010d01414110530810050401404014903c1001055080c050128410020301414050100414111603014010d00014111603c14010d0001411300081005040080401010081001
|26=>0x31d804010400404013000c1005aa004140d050040c02300341005030141411030041402490341001049b80c010f03c14050301404010d01c14110528410020500404010100814114901c10010d01c14110d03c1411039740402040140c02018c41402053041005045080c050d03c141105014100105004140d1603c1401045140c023000010050f0001405500080c05
|27=>0x4004140d03014140101008100d0300810050100410020300414110500814051603014013003c1005015140c020d0041411041d404013000010051601c14010d0041411040340c05
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x3c306ea000019282d500000a1400002350000000000001f4036800000ba0000000000000000125000003cc00000000000000000000a50000000000000000000000000000000000000002a8000000000000000005
|7,0=>0x1e243bc87690e940000398c00000001c4838446ea0db21ae8350c6820000198800006510c73188630105e20b9316c62c905720aa414e628d000009f41368260c4a2090411c42290439884310441f903d980000ee81cd037a00000d86000000006930cc6189000005f30b6815d029a04f4096811d021a03f4
|7,1=>0x36286b50d4a1a543428678ccd2000000006590c9218e4316661d0c1a18032f885e4cbaa17232de60000b5a1674000058d0afa15b42b065510a8994d400005250000146328484f909d2137326684bd095a129224c60000000122423c846cc8c191532228435085190910000000082a10231fc83ecc7ba0f34
|7,2=>0x4c2697512d1a5824a88000128224c4494491cd221a40447a68e50000236346668bd115a00004506891110221c4000086110a200004208834d051a073000080d0ffa1fb400007dd0f9a1f0300007b4c0001e940000798c0001e423c267750ed19d643a487390e521c7338867010de2000037266d500000000
|7,3=>0xb68d6b22d2459e6b30d651000058c8b0915f22bb3570600015a9ab1455c6aa900002a735468a84800029e353a2a65000029725268a3d1461a89350c6a108000000050269f8d3d200004ee69cd1381a6e200009a91339a643
|8,0=>0x72e6e549c91b8f37186e24dc31b8337006df4dbd1b7736e86dc4db71b6b36d06d94db11b5f36b86d64dab1b5336a06d34da51b4736886d04d9f1b3b36706cd4d991b2f36586ca4d931b2336406c74d8d1b17362a4c48d879b0c36126c18d819b0035fa6be8d7b9af435e26bb8d759ae835ca6b88d7012dd3
|8,1=>0x8a87144e27944c38927118e219c40387a70e8e1b9c34386270b8e159c28384a7088e0f9c1c38327058e099c10381a7028e039c0438026ff8dfd9bf837ea6fc8df79bed27d46f9cdf21be137bc6f6cdec1bd537a46f409e69bca378e6f10de09bbe37766ee0dda9bb2375e6eb0dd49ba637466e80dce9b9a3
|8,2=>0xa267440e869d0a3a0e7410e809cfe39f673e0e7a9cf239de73b0e749ce639c67380e6e9cda39ae7350e689cce39967320e629cc2397e72f0e5c9cb6396672c0e569caa394e7294a511c9f39387264e4b1c9339207234e451c8739087204e3f1c7b38f071d4e391c6f38d871a4e331c6338c07174e2d1c573
|8,3=>0xb9c772cee41dc53b8476fcede1db93b6c76cced81dad3b54769ced21da31b407674ecd1d973b287644ec71d8b3b107614ec11d7f3af875e4ebb95743ae275b8eb59d683aca7588eaf9d5d2ab4755ceaa1d513a9c752cea41d453a8474fce9e1d393a6c74d0a989d2e3a5674a0e929d223a3e7470e8c9d163
|8,4=>0x5dd3bb4775ceea1dd13
|9,0=>0xcbc5970b2d16582cac5950b2916502c9c5930b2516482c8c5910b2116402c7c58f0b1d16382c6c58d0b1916302c5c58b0b1516282c4c5890b1116202c3c5870b0d16182c2c5850b0916102c1c5830b0516082c0c5810b0116002bfc57f0afd15f82bec57d0af915f02bdc57b0af515e82bcc5790af115e02
|9,1=>0x6d02d9c5b30b6516c82d8c5b10b6116c02d7c5af0b5d16b82d6c5ad0b5916b02d5c5ab0b5516a82d4c5a90b5116a02d3c5a70b4d16982d2c5a50b4916902d1c5a30b4516882d0c5a10b4116802cfc59f0b3d16782cec59d0b3916702cdc59b0b3516682ccc5990b3116602
|10,0=>0x36f8ede1dba3b7076d8eda1db23b6076b8ed61daa3b507698ed21
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 15
def pmP:Nat→Nat
|0=>0x1808000000bfc0000005ee00000028300000011300000008900000004420000002200000001030000000814000000404000000201000000100000000041400000020600000010100000007f800000009c00000004c000000024000000011000000008400000004000000001500000000a000000001800000000a0000000040000000018000000008000000002000000000
|1=>0x8030000003adc0000018000000007050000003818000001bdc000000cfe000000626000000312000000188c000000c420000006160000003080000001818000000c08000000602000000300800000180000000084c000000425000000211800000108400000080c00000040500000020200000010080000008020000004000000001920000000c14000000608000000303
|2=>0xb112800004b8dc000024c6e0000126350000093138000048c1c00002446e000012227000009103800004880c000024006000010006000008002000004000000001c00e00000a623000004101000002080000001004c000006627000003093800000988c000004c2e0000026130000012108000008c140000046060000022040000011018000008804000004002000002000
|3=>0x413118000203bdc0000acc6e000052307000028102000013888c000080c4c0000406240000203100000101818000080c080000406000000202100000100c1400008044c000040200000020002000008199c0000405fe00001e62500000f30380000788dc00003c44e00001a23700000b39b8000059c9c00002cc6e00001663500000b313800005989400002c64e000016227
|4=>0x1042030000820898000410440000208202000104001000081849c000404cfe00020260100010030a0000801840000400802000200201000100100000080000000022c64e00011622700008100000004000000001acc4e0000a026700004f31380002688dc00013444e00009a21700004b39380002598cc00012c44e000092e3700004931b800024889c00012080c000086627
|5=>0x100b113800804200c0040206040020102040010080008002848cdc001400604000a001150004491138002069c9c00102c64e000816227000409383800204985c00102466e000812327000409183800204889c00101400a000802307000400312800200000000080000000028822000010f1138000859cdc00042cc4e00021632700010b11380008498dc00042446e000210134
|6=>0x800910b802000000400c02060400480230700210471300102598dc00812cc4e00404220700200f303801007889400802cc4e004012a07002009183801004881c00800560e004000e060020007000010003080008000e4c0040006260020002100010000c0c00800044c004000200002000010000c05881c0055204040028123270010491138008240004004120000002050006
|7=>0x49409583824805a81c0c013c46e052092207020400500810005881c08000040203021263701800d31b80c00498dc044424c6e02201800401100919b80880488dc04400446e02089223501000d11380800498dc04002446e02001221700b04b10380508698dc028024c6e01209220700840b31b804085989c02010000401001a33700800939380400498dc020024c2e010012607
|8=>0x202029103900a04200480402040a4020101072000291038a4824881c40402446e202010206100008000864005881c2c402446e16001623709800931b848804889c240024c6e12001222708800931b840a04088820402444e102010021081008010040035881c2000b4c6e10005263708000931b840004889c20002004c0d2096a07061008501030004201816013c46e092816307
|9=>0x44804911ba2082488dd10402c40e84309222742040b103a10005881d06402c46e83001e23740910b183a04825881d02402c40e81001663740800b103a00e848cdd006524c6e803092237401849113a0088498dd00403444e80201222740094b113a004a488dd00242c44e80121263740084931ba0040488dd00012444e8000162073c006b1039a08040018c01000402540096207
|10=>0x224002444f010a0002480800931bc04004985e02002446f000802117800021309c00007889e00002c44f000008224800004102400001889e000000c28b9209620759800b11bac0205881d50400c406a3009e23750940b183a84a05881d42402c40ea1001620750100b103a8020588dd28042446e92201223748904b103a40804889d20002446e8c0016207
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x40a8007e1c000f8001700000000202000262400000000f000100000000000001000000000000000000000000600000000011
|7,0=>0xf8e51e102f04c802400050100d0989420040084c2a0429000421a000143c14060bc08250001800130a85080130a950aa1309800001a2c1bc040437050263d00000200100811ca16271d0264800010000002aa882130c80814000a000085209804a6c8021004e2f0209400140184c021709904a413379702600200040a00098000013020500013033180a1902848d615
|7,1=>0x4cfe062914952006b855180229000084305840000400a38001304818000200854264f010080000020089200098e8e00200048081309b78262600800da151709826114d8a4001302158fc00009440a410011032000504c26130001832410001414930004c00940004c0004020340201148542a010217c2a00189040000
|8,0=>0x48d46170e11180c75b44bb5042b111919a3343d7504823b2e1445d8fc6d641745a58702c6e039ac730db806e6054491c0601db2c36ec25a089460264ce0481908e1f2194b8edc0991b30455351940d8a2c1920834b334968f05d0bb7eae506d9680ebf742f1589e102ecf4e211b8a3a631699930a1238c29a34858cde53540222b072523b06ef216996ab0f8bc482666
|8,1=>0x51219102260064aee04f850c4e826b6938924a969d0e670ba0cab03b9b0f2ae702f5832d30b56448292109b0ce23380ea5b55bc104a08628d05528e31c505430552831871abcd2fc7924104b61e285075c38b24fadf66174f0ad22c6508380a0e1be33153303ad0ad32a3547a5cd4cc224d33d08e7303746afb1c0dd7cc28f0a9a4a70c015a2f45cd59fe7b4e8c60af3
|8,2=>0xe80c54de282
|9,0=>0xa2a1c41eeed46a85d53d9cbb611458ad42953c9fca26f4f6a295dc85453526d2b83554f94e75b9228f277a1568c388cba58fda6448d2a3803b95f2758bf8b50d4534e37119c524c74b711650af56ca34ca6a42cd1753b9f28e52ee515018901a23d95f0a824c65509533a661422bc1e36af90215494634c8db31487adeb28551c965eb59d4c8cf13
|10,0=>0xd0faa43e0c1162c15e22609315cc0af
|11,0=>0x57
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 37 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_238 10 roots_238 ops++addP pm 1 dom_175 9 roots_175 ops++addP pm 2 dom_207 9 roots_207 ops++addP pm 3 dzo_105_128 5 roots_105 ops++addP pm 4 dzo_111_128 7 roots_111 ops++addP pm 5 dom_111 8 roots_111 ops++addP pm 6 dom_233 7 roots_233 ops++addP pm 7 dom_97 4 roots_97 ops++addP pm 8 dom_143 6 roots_143 ops++addP pm 9 dom_231 9 roots_231 ops++addP pm 10 dzo_103_128 6 roots_103 ops++addP pm 11 dom_195 4 roots_195 ops++addP pm 12 dom_170 5 roots_170 ops++addP pm 13 dom_237 10 roots_237 ops++addP pm 14 dzo_107_4 6 roots_107 ops++addP pm 15 dom_103 6 roots_103 ops++addP pm 16 dom_235 9 roots_235 ops++addP pm 17 dom_105 5 roots_105 ops++addP pm 18 dom_167 5 roots_167 ops++addP pm 19 dom_99 5 roots_99 ops++addP pm 20 dom_110 7 roots_110 ops++addP pm 21 dom_75 5 roots_75 ops++addP pm 22 dom_234 7 roots_234 ops++addP pm 23 dom_139 5 roots_139 ops++addP pm 24 dom_107 6 roots_107 ops++addP pm 25 dzo_203_4 6 roots_203 ops++addP pm 26 dom_199 5 roots_199 ops++addP pm 27 dzo_101_128 5 roots_101 ops++addP pm 28 dzo_75_4 5 roots_75 ops++addP pm 29 dzo_107_128 6 roots_107 ops++addP pm 30 dom_203 7 roots_203 ops++addP pm 31 dom_227 7 roots_227 ops++addP pm 32 dzo_99_128 5 roots_99 ops++addP pm 33 dom_171 6 roots_171 ops++addP pm 34 dom_163 4 roots_163 ops++addP pm 35 dzo_235_4 7 roots_235 ops++addP pm 36 dom_47 5 roots_47 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_239 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_238 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_175 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_207 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_zo_105_128_97 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_zo_111_128_97 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_97 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_143 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_103_128_97 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_195 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_237 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_107_4_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_zo_203_4_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_zo_101_128_97 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_zo_75_4_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_zo_107_128_97 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_zo_99_128_97 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_zo_235_4_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_47 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_238 10 s (0,roots_238.map (·&&&dom_238)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_239 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_238 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_239 gM v ys):RunD true dom_239 gM v (ori ys):=h
def Z (s:Nat):=barP dom_239 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 9 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 46 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 46 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 239 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 111 128 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 239 → Z 7 i = true := (range_split z7_0 z7_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 256 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_256 : ∀ i, 256 ≤ i → i < 261 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 5 256 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 261 → Z 8 i = true := (range_split z8_0 (range_split z8_128 z8_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 121 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 121 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 14 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 14 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_239 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤11) (h:RunD true dom_239 gM s xsM):False:=by
  have hmin:6≤s:=by have hl:=run_len h;change 7≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_239 roots_239 goal_239 12:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_239
theorem lowS_239:Lower true dom_239 roots_239 goal_239 12:=S_239.noCircuit
def dzo_181_64:=0x33003300330033000000000000000000330033003300330000000000000000
def gzo_181_64:=0x33003300330032000000000000000000330033003200220000000000000000
def gsh_181_64:=0x3300330033003200000000000000000033003300320022
theorem lowS_zo_181_64_148:Lower true dzo_181_64 roots_181 gzo_181_64 6:=lower_iso_b (d1:=dom_181) (r1:=roots_181) (T1:=gsh_181_64) [(dom_181,64)] (by decide +kernel) (lower_slice_b (T:=gsh_181_64) [(0x2200220022002200000000000000000022002200220022,0,1),(0x3300330000000000000000000000000033003300000000,0,32)] (by decide +kernel) lowS_148)
def dzo_230_16:=0x55000000550000005500000055000000550000005500000055000000550000
def gzo_230_16:=0x55000000550000005500000055000000550000005400000054000000500000
def gsh_230_16:=0x5500000055000000550000005500000055000000540000005400000050
theorem lowS_zo_230_16_98:Lower true dzo_230_16 roots_230 gzo_230_16 6:=lower_iso_b (d1:=dom_230) (r1:=roots_230) (T1:=gsh_230_16) [(dom_230,16)] (by decide +kernel) (lower_slice_b (T:=gsh_230_16) [(0x5000000050000000500000005000000050000000500000005000000050,0,4),(0x5500000055000000550000005500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_98)
def dzo_182_64:=0x55005500550055000000000000000000550055005500550000000000000000
def gzo_182_64:=0x55005500550054000000000000000000550055005400440000000000000000
def gsh_182_64:=0x5500550055005400000000000000000055005500540044
theorem lowS_zo_182_64_148:Lower true dzo_182_64 roots_182 gzo_182_64 6:=lower_iso_b (d1:=dom_182) (r1:=roots_182) (T1:=gsh_182_64) [(dom_182,64)] (by decide +kernel) (lower_slice_b (T:=gsh_182_64) [(0x4400440044004400000000000000000044004400440044,0,2),(0x5500550000000000000000000000000055005500000000,0,32)] (by decide +kernel) lowS_148)
def dzo_119_128:=0xff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000
def gzo_119_128:=0xff00ff00ff00fe00ff00fe00ff00fc00000000000000000000000000000000
def gsh_119_128:=0xff00ff00ff00fe00ff00fe00ff00fc
theorem lowS_zo_119_128_97:Lower true dzo_119_128 roots_119 gzo_119_128 7:=lower_iso_b (d1:=dom_119) (r1:=roots_119) (T1:=gsh_119_128) [(dom_119,128)] (by decide +kernel) (lower_slice_b (T:=gsh_119_128) [(0xcc00cc00cc00cc00cc00cc00cc00cc,0,2),(0xf000f000f000f000f000f000f000f0,0,4),(0xff000000ff000000ff000000ff0000,0,16)] (by decide +kernel) lowS_97)
def dzo_180_64:=0x11001100110011000000000000000000110011001100110000000000000000
def gzo_180_64:=0x11001100110010000000000000000000110011001000000000000000000000
def gsh_180_64:=0x1100110011001000000000000000000011001100100000
theorem lowS_zo_180_64_148:Lower true dzo_180_64 roots_180 gzo_180_64 5:=lower_iso_b (d1:=dom_180) (r1:=roots_180) (T1:=gsh_180_64) [(dom_180,64)] (by decide +kernel) (lower_slice_b (T:=gsh_180_64) [(0x1100110000000000000000000000000011001100000000,0,32)] (by decide +kernel) lowS_148)
def dzo_231_16:=0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000
def gzo_231_16:=0xff000000ff000000ff000000ff000000ff000000fe000000fe000000fa0000
def gsh_231_16:=0xff000000ff000000ff000000ff000000ff000000fe000000fe000000fa
theorem lowS_zo_231_16_98:Lower true dzo_231_16 roots_231 gzo_231_16 7:=lower_iso_b (d1:=dom_231) (r1:=roots_231) (T1:=gsh_231_16) [(dom_231,16)] (by decide +kernel) (lower_slice_b (T:=gsh_231_16) [(0xaa000000aa000000aa000000aa000000aa000000aa000000aa000000aa,0,1),(0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f0,0,4),(0xff000000ff000000ff000000ff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_98)
def dzo_117_128:=0x33003300330033003300330033003300000000000000000000000000000000
def gzo_117_128:=0x33003300330032003300320033003000000000000000000000000000000000
def gsh_117_128:=0x330033003300320033003200330030
theorem lowS_zo_117_128_97:Lower true dzo_117_128 roots_117 gzo_117_128 6:=lower_iso_b (d1:=dom_117) (r1:=roots_117) (T1:=gsh_117_128) [(dom_117,128)] (by decide +kernel) (lower_slice_b (T:=gsh_117_128) [(0x300030003000300030003000300030,0,4),(0x330000003300000033000000330000,0,16)] (by decide +kernel) lowS_97)
def dzo_102_16:=0x550000005500000055000000550000
def gzo_102_16:=0x550000005400000054000000500000
def gsh_102_16:=0x55000000540000005400000050
theorem lowS_zo_102_16_98:Lower true dzo_102_16 roots_102 gzo_102_16 5:=lower_iso_b (d1:=dom_102) (r1:=roots_102) (T1:=gsh_102_16) [(dom_102,16)] (by decide +kernel) (lower_slice_b (T:=gsh_102_16) [(0x50000000500000005000000050,0,4)] (by decide +kernel) lowS_98)
def dzo_183_64:=0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000
def gzo_183_64:=0xff00ff00ff00fe000000000000000000ff00ff00fe00ee0000000000000000
def gsh_183_64:=0xff00ff00ff00fe000000000000000000ff00ff00fe00ee
theorem lowS_zo_183_64_148:Lower true dzo_183_64 roots_183 gzo_183_64 7:=lower_iso_b (d1:=dom_183) (r1:=roots_183) (T1:=gsh_183_64) [(dom_183,64)] (by decide +kernel) (lower_slice_b (T:=gsh_183_64) [(0xaa00aa00aa00aa000000000000000000aa00aa00aa00aa,0,1),(0xcc00cc00cc00cc000000000000000000cc00cc00cc00cc,0,2),(0xff00ff00000000000000000000000000ff00ff00000000,0,32)] (by decide +kernel) lowS_148)
def dzo_227_16:=0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f0000
def gzo_227_16:=0xf0000000f0000000f0000000f0000000f0000000e0000000e0000000a0000
def gsh_227_16:=0xf0000000f0000000f0000000f0000000f0000000e0000000e0000000a
theorem lowS_zo_227_16_98:Lower true dzo_227_16 roots_227 gzo_227_16 6:=lower_iso_b (d1:=dom_227) (r1:=roots_227) (T1:=gsh_227_16) [(dom_227,16)] (by decide +kernel) (lower_slice_b (T:=gsh_227_16) [(0xa0000000a0000000a0000000a0000000a0000000a0000000a0000000a,0,1),(0xf0000000f0000000f0000000f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_98)
namespace S_247
def pG:List (Nat×Nat):=[(1,17),(1,33),(1,65),(2,34),(2,66),(2,130),(3,19),(3,35),(3,67),(3,131),(4,20),(4,36),(4,132),(5,21),(5,37),(5,69),(5,133),(6,22),(6,38),(6,70),(6,134),(7,23),(7,39),(7,71),(7,135),(16,17),(16,20),(16,144),(18,19),(18,22),(18,50),(18,82),(18,146),(32,33),(32,34),(32,36),(32,96),(48,49),(48,50),(48,52),(48,112),(48,176),(64,65),(64,66),(64,96),(68,69),(68,70),(68,84),(68,100),(68,196),(80,81),(80,82),(80,84),(80,112),(80,208),(128,130),(128,132),(128,144),(129,131),(129,133),(129,145),(129,161),(129,193),(160,161),(160,162),(160,164),(160,176),(160,224),(192,193),(192,194),(192,196),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1ffffffffffffffffff
def xsM:=roots_247.map (·&&&dom_247)
def gM:=goal_247&&&dom_247
def NN:Nat→Nat
|7=>9
|8=>50
|9=>69
|10=>9
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|7,0=>0xd534daa67899bd783b22721a75250151ebf19b4807075
|8,0=>0xe832cdff49d4c83c9ab1bce47b3ec6b11fca97f6a7ba7a16a49e5ab9a1eb9882d87ab7867138091e6e0806b45c6725c61e59612585f8eb585de4f7c84bd9a45f3e42bb0429c4416353c8fc3c899368153322e314d92a24f28c25269aa2248a216a1215311473f13bf313745116900be490b40a0a28b0691100f9a0061a
|9,0=>0xe39e1e031ad286bccf5db282daf571aea4f9deff93ea0912f090afe8ed528d25789f84896fc85d967e0bb7c6427c050777a4742f872a5471d126f2da6e6486713a608ac5d0ec5bb10587b55542e54dc754c6c540cd48c35455664535941b304137e403353f9053cdfd3b20633d9430b152fde62efde2a3c427c4a273eb21f94202431e8881b362181911705916736151771327b10d420fb490d1c40d1420c2610acbe0ac8f0903106aa7025bf
|10,0=>0xf9dd7b47c386cd67fd216aad44bc4d1950c17a110428f
|11,0=>0x3ef7d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa0000ff00ff00aa00aa00ff00ff00aa00aa00ff00ff00aa00aa00ff00ff00aa00aaff00ff00ff00ff00aa00aa00aa00aa00ff00ff00ff00ff00aa00aa00aa00aa3300330033003300330033003300330033003300330033003300330033000033003300330033003300330033003300330000003300000033000000330000ff00ff00ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff00000000cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00ccff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000ff00cc00ff00cc00ff00cc00ff00cc00ff00cc00ff00cc00ff00cc00ff00ccff00ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff000000ff0000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa33003300330033003300330000000000330033003300330033003300000000ff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000ff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000
|0,1=>0x11001100110000001100110011000000110011001100000011001100110000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00ff000000003300330033003300330033003300330033003300000000003300330000000000000000ff00ff0000000000ff00ff0000000000cc00cc0000000000cc00ccaa00aa00ff00ff00aa00aa00ff00ff00aa00aa00ee00ee00aa00aa00ee00eeff00ee00ff00ee00ff00ee00ff00ee00ff00ee00ff00ee00ff00ee00ff00ee00000000ff00ee0000000000ff00ee0000000000ff00ee0000000000ff00eeff00ff00ff00ff00ff00ff00ff00ff00ff00ff00cc00cc00ff00ff00cc00ccff00ff00ff00ff00ff00ff00ff00ff00cc00cc00cc00cc00cc00cc00cc00cc550055005500550055005500550055005500550044004400550055004400440000000000000000ff00ff00ee00ee000000000000000000ff00ff00ee00ee0f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0000ff00ff00ee00ee00ff00ff00ee00ee00ff00ff00ee00ee00ff00ff00ee00eeee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00eeff00ff00ee00ee000000000000000000ff00ff00ee00ee00000000000000000000000000000000ff00ff00ff00ff000000000000000000ff00ff00ee00ee
|0,2=>0xff00ff0000000000ff00000000000000ff00ff0000000000ff0000ff00ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff000000ff00000000000000000000000000000000000000000000ff00ff0000000000ff000055005500550055005500550055005500550000005500000055000000550000ff00ff00ff00ff00ff00ff00ff00ff00aa00aa00aa00aa00aa00aa00aa00aaff00ff00ff00ff00ff00ff0000000000ff000000ff000000ff000000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00cc00ff00cc00ff00cc00ff00ccff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc000000000000000000000000ff00ff00ff0000000000000000000000ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00ff000000000000000000ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ee00ee00ff00ff00ee00eeff00ff00cc00cc00ff00ff00cc00cc00ff00ff00cc00cc00ff00ff00cc00ccff00ff00ff00ff00cc00cc00cc00cc00ff00ff00ff00ff00cc00cc00cc00ccff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff0000
|0,3=>0x55005500550055005500550055005500440044004400440044004400440044ff00ff0055005500ff00ff0055005500ff00ff0044004400ff00ff004400440000ff000000ff000000ff00000000000000ff000000ff000000ff00000000ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff000000ff00000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff00000f000f000f000f000f000f000f000f000f000f000f0000000f000f000f0000ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000000000000000000000000055005500000000005500550000000000440044000000000044004400000000ff00ff0000000000cc00cc0000000000ff00ff0000000000cc00ccff00ff00ff00ff00ee00ee00ee00ee00ff00ff00ff00ff00ee00ee00ee00ee0000ff000000ff000000ff000000ff000000cc000000cc000000cc000000cc550055005500550044004400440044005500550055005500440044004400440000000000000000ff00ff00ff00ff000000000000000000ff000000ff0000ff00ff0000000000ff00ff00ff00ff00ff00ff0000000000ff00ff00ff000000000000ff00ff0000000000aa00aa0000000000ff00ff0000000000aa00aa000000000000000000000000000000000000ff000000ff000000ff00000000
|0,4=>0xff00ff00ff00ff00ff00cc00ff00cc00ff00ff00ff00ff00ff00cc00ff00cc00000000000000000000000000000000ff00ff00ff00ff00aa00aa00aa00aa3300330033003300330000003300000033003300330033003300000033000000000000ff00ff0000000000ff00ff0000000000ff00000000000000ff0000ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff0000000000ff0000ff00ff00ff00cc00ff00ff00ff00cc00ff00ff00ff00cc00ff00ff00ff00cc33003300330000003300330033000000330033003300000033003300330000bb00bb00bb00aa00bb00bb00bb00aa00bb00bb00bb00aa00bb00bb00bb00aa000000000000000000000000ff00ff00000000000000000000000000ff00000000000000000000ff00ff00ff00ff000000000000000000ff00ff00ff00003300330033003300330033003300330033003300330033003300330000000055005500550055005500550000000000550055005500550055005500000000ff00aa00ff00aa00ff00aa00ff00aa00ff00aa00ff00aa00ff00aa00ff00aa33002200330022003300220033002200330022003300220033002200330022ff00ff00ff00ff00ff00ff00aa00aa00ff00ff00ff00ff00ff00ff00aa00aaff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000
|0,5=>0xff00ff00ff00ff00ff00ff00ff000000ff00ff00ff00ff00ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00aa00ff00aa00ff00aa00ff00aaff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00cc00cc00cc00cc5500550055005500550000005500000055005500550055005500000055000000000000000000000000000000000000ff00aa00ff00aa00ff00aa00ff00aa550055005500550055005500550055005500550000000000550055000000000000ff000000ff000000ff000000ff000000ff00000000000000ff000000000000ff000000ff000000aa000000aa000000ff000000ff000000aa000000aa0000ff000000ff000000ff000000ff000000ff000000ff00000000000000000000000000000000ff00ff00ff00ff000000000000000000cc00cc00cc00ccff00ff00ff00ff00ff00ff00ff00ff00ff00ff00aa00aa00ff00ff00aa00aa
|_,_=>0
def sP:Nat→Nat
|0=>0x60400710104833e0400710109033a040070c202030404007101049b060400e0e1440424240800e2020906640800e2020906580802a1c28808241800e2048328040070a2020906440100e20209060038808247810038505101048d001c40406300800e20203042c0800e182840608080
|1=>0x1010483600400a0e1440412ac1810e2020906b4080442828808241810038385101048d0200507101048358040220e20212560400710a8209060400a0ea4404120c0801c28404123400710113030201207101048302011871010483020111e10110830200386101090d02005070c20217
|2=>0x60403e0e2020906040071010483780400710241ba02005070a20221120c0071010483220038510109210604007101048302e40071010483700402010104836e040070a20236120c080141c404120da810088f080848181001c28808241b402019071010483020038510104836204007
|3=>0x803ae0824181001c404133818100803880884483020038808241cd020038808241cb0202507101090302003880826403020038808241c702009870a2020906040460e20209060400710101c50200a871010483001c28808241c4020100708241c202020870a2020906040400e20209
|4=>0x101048302010250e202090604007101048368040180e2020906040073420209060400710104833a0400710104836204007101048384040070c14209060401e0e20217120c0a2142020906040079e2020906040070c2021206040078620217120c0803c1c404422418100383880824681
|5=>0x20038808241d402003c35c10483020038808241d30201007101090906040078620221120c0803c1d7080824181001c4042484181001c404120e481001c40442241a7001c4046c24181001c404120c0d2003838510104830200388082688302003865c104830200388082418b0202807
|6=>0x8241c40200385101108906040071012c0906040410e2020906040071011089560c0800eb8404120d3800e20209075c0804a1c404120c0803c1c40412ac1810e21984120c0804478404120c0800eb84042e24181001c404120ce0100283880884483001eb080824181007838808241d5
|7=>0x80f080824181001c28808484830201d871010483020110710104ab06040070c20217060400710104835e040130e20209060405b0e20209060400a0e18404120c080141c4042e24181001ed080824181001c404120de81001ec88082418100883c31010483020110710109030200388
|8=>0xe2020906040200e20209060400a0e202090604007101090906040075c2020906040070a202090604007101108906040070c2020906040071010b89060400e0e2020906040071010483980400a0e14404120c080401c4042e24181
|_=>0
def sO:Nat→Nat→Nat
|7,0=>0x3c806ae0b6013381f702f0041c0440008
|8,0=>0xeb41ce838d06fa0dac9ad834ce67dccb498e830b25f60bac16d82cce5764ab394d928b04f609ac12c9247246e089490a820323e607848e881bf235a466c8c5817b02d2456b8a6713d025a047408680fb21d6036c06580bb015242640448
|9,0=>0x7cd0f765eac3cd878b0ef61da4bab97470e6e1c9c38a97050dea1b8cb6986c30d625a8434886810ce21984328863f2c5e187c30785fd2bda17742e685bb2b52565cac385770ace155c2a385352a4a145428284f509c6534c26184b30946124c241847308c6114c22184330842503c9ff83ef07be0f349de8
|9,1=>0x41188112ffe5fbc3ee9
|10,0=>0x45988a31126220c439886310a6210c4198
|11,0=>0x4617
|_,_=>0
def wAt:=mkWire dB 92 248 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 15
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 8 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x10010c0112210e0506050e0d0e0550240e9d02014a0140070e211c5d0e0d120112050e250e01060512210625120112210e05404b0e2106253c270e01120d122114270e0506710e5e12010e0d1001120d0e6a24210625300f0e5d120126070e49120d26040e49120d14150e0510010e0d002106050e0500211427100112210e05
|1=>0x14230e0576130e151001100112050e0526040e49120d100112050625409c0e2102011c5e0e0d12010e8612050e2124051001120d0e05105e1201120d0e250e011001420f12050ecd0a07100110010e36060514170e051001002106010e055e030eba022110010e250e050e0d060510010e050a0f10010e250601120d14140e05
|2=>0x621122100210e0112010e250e055c25022112210625100d120112050e0106050e0d0e2102210036060512050e215c27022198050e16100144210e250625072540270e2114160e0510010e49120d76070e15100150270e9d020126070e49120d1001140f0e0586270e2106211001140d0e0514150e0510010efd2e0f12017a01
|3=>0x22140070e21000d0e010a0710010e250e01120102210e5e120112050e05010e06213c0f0e013c230e01100d02211a2306050e210625120506210e0102211205062540270e21120502012405120d4e2302010e0d10012e071201102502210a2700213c0d0e0140070e21420f12050e5d1201242106253c270e010e3606058627
|4=>0xe210e05120d022110011205122112010e0d0e1610010e0510010e2112010e010e211001120d0e1510010e250601102512010eba02210e49120d0eb9022112210e050e051201010d062114230e055c0102210e2506210e250625140f0e05120500214e250201140d0e0512050601020102215c0f
|_=>0
def oO:Nat→Nat→Nat
|7,0=>0xf3000030c00009302a0000082004
|8,0=>0x1486a134f1a6cd324963499a40d1a68a3439a10d0267e33d99e0cea67233799b0cd26663319980cba65a32b9950ca264e3259920c8a64231f98f0c7263631998c0c5a62a3139890c4261e30d9860c2a6123
|9,0=>0x92948ca4251f28e946ca3251728a944ca2250f286942ca12507282940ca024ff27e93ec9f24f727a93cc9e24ef27693ac9d24e7272938c9c24df26e936c9b24d726a934c9a24cf266932c9924c7262930c9824bf25e92ec9724b725a92cc9624af25692ac9524a72
|9,1=>0x12f29694aca525272
|10,0=>0x13919c0cdc66c33519a0ccc6643311
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 13
def pmP:Nat→Nat
|0=>0x40024fe0000800437c000080018100000c83477000010262ee000010151dc00001c091100000200302000001a2aee000002455dc00000488bb80000060102000000a22fe000000601200000008abf80000007c770000000e8ee000000089dc000000093f80000001277000000020ee0000000410800000008090000000066200000000744000000001880000000029000000000200000000003800000000020000000000100000000000
|1=>0x20188a0ee004030141dc00804088bb801004111770020002a0ee004000301380041281a3b8008200b4ff00100a028ee0020040c1dc004000202400080001477000801022ee000885041dc001000008100012a31077000254428ee000480643dc0009000081000100090f7000190062ee000308844fc000500587f80008111177000080060ee0000c90415c000180493b800022610770000408acee00008024bdc000100493b800020030f7
|2=>0x44400222ee08080000548100923083b8201200107f032000240ee046804551dc081000983b8100c813177018091040ee020230085dc0401864a2b8080200b0ff0100080a8ee008906445dc011108883b80220141077004402220ee008802441dc01018c883b802020110f7004000220ee0080000058000c4482a3b80180d1547f00301a2a8ee004281445dc00842088bb80102c151770020580a0ee004081449fc00810088bf80100c55477
|3=>0x4a0064224ee9300220c1dd220194093ba40030c9477480060b20ee844000551dd0400240a3ba04200110774020112aaee804020555dd000440083ba0002041277400018260fe800012051dc80802288bb90000803177100010062ee1a01100e1dc3200042a3b86000001077090099048ee1201100c1dc2200042a3b84100c5317f082000260ee1001c8849dc200390093b84004c13177080060020ee1000b14c9fc200062983b84000813177
|4=>0x1100002151ddc00060883ba5800013077
|_=>0
def pmB:Nat→Nat→Nat
|7,0=>0x10001000406000203
|8,0=>0x5056701f31170d0e075b2d11363b33050b193e362618356b1d321415083f090a4a572c125c0c4310552a3a6f1c1e365e1b0f
|9,0=>0x4f4c477752167e49616e412938782e13806a224d235c7d4260626951794837217a82766730647f4065817466445f39454e6d71255358722459281a54462b5a7c5d3c2f7b73
|10,0=>0x3d2027684b6375346c
|11,0=>0xb
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 43 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_243 10 roots_243 ops++addP pm 1 dom_231 9 roots_231 ops++addP pm 2 dom_119 9 roots_119 ops++addP pm 3 dzo_181_64 6 roots_181 ops++addP pm 4 dom_245 9 roots_245 ops++addP pm 5 dom_246 9 roots_246 ops++addP pm 6 dom_215 9 roots_215 ops++addP pm 7 dom_151 6 roots_151 ops++addP pm 8 dzo_230_16 6 roots_230 ops++addP pm 9 dzo_182_64 6 roots_182 ops++addP pm 10 dzo_119_128 7 roots_119 ops++addP pm 11 dom_148 4 roots_148 ops++addP pm 12 dom_183 9 roots_183 ops++addP pm 13 dzo_180_64 5 roots_180 ops++addP pm 14 dzo_103_128 6 roots_103 ops++addP pm 15 dom_149 5 roots_149 ops++addP pm 16 dzo_231_16 7 roots_231 ops++addP pm 17 dom_182 6 roots_182 ops++addP pm 18 dzo_151_64 6 roots_151 ops++addP pm 19 dzo_117_128 6 roots_117 ops++addP pm 20 dom_101 5 roots_101 ops++addP pm 21 dom_180 5 roots_180 ops++addP pm 22 dzo_149_64 5 roots_149 ops++addP pm 23 dzo_102_16 5 roots_102 ops++addP pm 24 dom_181 6 roots_181 ops++addP pm 25 dzo_183_64 7 roots_183 ops++addP pm 26 dom_244 7 roots_244 ops++addP pm 27 dom_229 7 roots_229 ops++addP pm 28 dom_150 5 roots_150 ops++addP pm 29 dom_102 5 roots_102 ops++addP pm 30 dzo_227_16 6 roots_227 ops++addP pm 31 dom_117 6 roots_117 ops++addP pm 32 dzo_103_16 6 roots_103 ops++addP pm 33 dom_103 6 roots_103 ops++addP pm 34 dom_118 7 roots_118 ops++addP pm 35 dom_213 7 roots_213 ops++addP pm 36 dom_230 6 roots_230 ops++addP pm 37 dom_214 7 roots_214 ops++addP pm 38 dzo_150_64 5 roots_150 ops++addP pm 39 dom_198 4 roots_198 ops++addP pm 40 dom_199 5 roots_199 ops++addP pm 41 dzo_101_128 5 roots_101 ops++addP pm 42 dom_87 5 roots_87 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_247 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_zo_181_64_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_230_16_98 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_182_64_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_119_128_97 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_180_64_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_103_128_97 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_149 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_231_16_98 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_151_64_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_zo_117_128_97 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_101 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_180 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_zo_149_64_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_zo_102_16_98 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_zo_183_64_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_229 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_150 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_zo_227_16_98 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_zo_103_16_98 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_zo_150_64_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_198 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_zo_101_128_97 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_87 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_243 10 s (0,roots_243.map (·&&&dom_243)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_247 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_243 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff0000ffff0000ffff0000,112),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_247==dom_247)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_247 gM v ys):RunD true dom_247 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_247 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 9 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 50 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 50 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 69 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 69 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 9 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_247 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def isoMvS_251:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_251:Lower true dom_251 roots_251 goal_251 12:=lower_iso_b isoMvS_251 (by decide +kernel) lowS_239
def isoMvS_253:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_253:Lower true dom_253 roots_253 goal_253 12:=lower_iso_b isoMvS_253 (by decide +kernel) lowS_247
def isoMvS_254:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_254:Lower true dom_254 roots_254 goal_254 12:=lower_iso_b isoMvS_254 (by decide +kernel) lowS_223
namespace S_255
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(2,10),(2,34),(2,66),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(4,20),(4,36),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(6,14),(6,22),(6,38),(6,70),(6,134),(7,15),(7,23),(7,39),(7,71),(7,135),(8,9),(8,10),(8,72),(8,136),(12,13),(12,14),(12,28),(12,44),(12,76),(12,140),(16,17),(16,20),(16,144),(18,19),(18,22),(18,26),(18,50),(18,82),(18,146),(24,25),(24,26),(24,28),(24,88),(24,152),(32,33),(32,34),(32,36),(32,96),(40,41),(40,42),(40,44),(40,104),(40,168),(48,49),(48,50),(48,52),(48,112),(48,176),(56,57),(56,58),(56,60),(56,120),(56,184),(64,65),(64,66),(64,72),(64,96),(68,69),(68,70),(68,76),(68,84),(68,100),(68,196),(80,81),(80,82),(80,84),(80,88),(80,112),(80,208),(128,130),(128,132),(128,136),(128,144),(129,131),(129,133),(129,137),(129,145),(129,161),(129,193),(160,161),(160,162),(160,164),(160,168),(160,176),(160,224),(192,193),(192,194),(192,196),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffffffffffffffffffffff
def xsM:=roots_255.map (·&&&dom_255)
def gM:=goal_255&&&dom_255
def NN:Nat→Nat
|12=>2
|13=>1
|_=>0
def HT:Nat→Nat→Nat
|12,0=>0xe7f85792e4
|13,0=>0x64457
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffffffffffff00000000000000000000000000000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x87654310876543109876543210
|_=>0
def sO:Nat→Nat→Nat
|12,0=>0x13209
|13,0=>0x128
|_,_=>0
def wAt:=mkWire dB 10 256 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 9
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x10841
|_=>0
def oO:Nat→Nat→Nat
|12,0=>0x441
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 6
def pmP:Nat→Nat
|0=>0xfffb00
|_=>0
def pmB:Nat→Nat→Nat
|12,0=>0xa
|13,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 2 (j%128);fld (pmP (k/32)) 8 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_254 12 roots_254 ops++addP pm 1 dom_191 11 roots_191 ops++addP pm 2 dom_127 10 roots_127 ops++addP pm 3 dom_253 12 roots_253 ops++addP pm 4 dom_251 12 roots_251 ops++addP pm 5 dom_247 12 roots_247 ops++addP pm 6 dom_239 12 roots_239 ops++addP pm 7 dom_223 12 roots_223 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_255 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_191 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_127 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_247 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_223 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_254 12 s (0,roots_254.map (·&&&dom_254)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_254 h
def symsG:List (List (Nat×Nat)):=[[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_255==dom_255)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_255 gM v ys):RunD true dom_255 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_255 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z12 : ∀ i, 0 ≤ i → i < 2 → Z 12 i = true := span_ok (by decide +kernel : span (Z 12) 2 0 = true)
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
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [5, 4] }, { op := GateOp.or, inputs := [4, 1] }, { op := GateOp.or, inputs := [0, 2] }, { op := GateOp.or, inputs := [9, 2] }, { op := GateOp.or, inputs := [5, 3] }, { op := GateOp.or, inputs := [0, 1] }, { op := GateOp.or, inputs := [12, 13] }, { op := GateOp.or, inputs := [11, 3] }, { op := GateOp.and, inputs := [7, 15] }, { op := GateOp.and, inputs := [10, 8] }, { op := GateOp.and, inputs := [13, 12] }, { op := GateOp.and, inputs := [6, 14] }, { op := GateOp.or, inputs := [16, 17] }, { op := GateOp.or, inputs := [20, 18] }, { op := GateOp.or, inputs := [21, 19] }]

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 22⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
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

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_52252_aux

theorem PEqualNP.Outside.L_meta_52252 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_52252_aux.main
