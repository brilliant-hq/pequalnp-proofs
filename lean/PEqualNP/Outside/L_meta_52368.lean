import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_52368_aux
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
def dom_25 : Nat := 0x3030303
def goal_25 : Nat := 0xffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00
def roots_25 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_43 : Nat := 0xf0f00000f0f
def goal_43 : Nat := 0xeeeeeeeeaa00aa00eeeeeeeeaa00aa00eeeeeeeeaa00aa00eeeeeeeeaa00aa00
def roots_43 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_45 : Nat := 0x333300003333
def goal_45 : Nat := 0xfafafafaaa00aa00fafafafaaa00aa00fafafafaaa00aa00fafafafaaa00aa00
def roots_45 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_47 : Nat := 0xffff0000ffff
def goal_47 : Nat := 0xfefefefeaa00aa00fefefefeaa00aa00fefefefeaa00aa00fefefefeaa00aa00
def roots_47 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_51 : Nat := 0xf000f000f000f
def goal_51 : Nat := 0xeeeeeeeeaaaa0000eeeeeeeeaaaa0000eeeeeeeeaaaa0000eeeeeeeeaaaa0000
def roots_51 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_53 : Nat := 0x33003300330033
def goal_53 : Nat := 0xfafafafaaaaa0000fafafafaaaaa0000fafafafaaaaa0000fafafafaaaaa0000
def roots_53 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xfefefefeaaaa0000fefefefeaaaa0000fefefefeaaaa0000fefefefeaaaa0000
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_57 : Nat := 0x303030303030303
def goal_57 : Nat := 0xffaaaaaaffaaaa00ffaaaaaaffaaaa00ffaaaaaaffaaaa00ffaaaaaaffaaaa00
def roots_57 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xffeeeeeeffaaaa00ffeeeeeeffaaaa00ffeeeeeeffaaaa00ffeeeeeeffaaaa00
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xfffafafaffaaaa00fffafafaffaaaa00fffafafaffaaaa00fffafafaffaaaa00
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfffefefeffaaaa00fffefefeffaaaa00fffefefeffaaaa00fffefefeffaaaa00
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

def dom_83 : Nat := 0xf000f00000000000f000f
def goal_83 : Nat := 0xffffeeeeffffeeeeaaaa0000aaaa0000ffffeeeeffffeeeeaaaa0000aaaa0000
def roots_83 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_88 : Nat := 0x10101010000000001010101
def goal_88 : Nat := 0xffffff00ffffff00ff000000ff000000ffffff00ffffff00ff000000ff000000
def roots_88 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_89 : Nat := 0x30303030000000003030303
def goal_89 : Nat := 0xffffffaaffffffaaffaaaa00ffaaaa00ffffffaaffffffaaffaaaa00ffaaaa00
def roots_89 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_90 : Nat := 0x50505050000000005050505
def goal_90 : Nat := 0xffffffccffffffccff000000ff000000ffffffccffffffccff000000ff000000
def roots_90 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f
def goal_91 : Nat := 0xffffffeeffffffeeffaaaa00ffaaaa00ffffffeeffffffeeffaaaa00ffaaaa00
def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

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
def goal_106 : Nat := 0xffffffffffccffcccccccccc00000000ffffffffffccffcccccccccc00000000
def roots_106 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffffffffffeeffeeeeeeeeeeaa00aa00ffffffffffeeffeeeeeeeeeeaa00aa00
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_108 : Nat := 0x1111000011110000111100001111
def goal_108 : Nat := 0xffffffffff00ff00f0f0f0f000000000ffffffffff00ff00f0f0f0f000000000
def roots_108 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_109 : Nat := 0x3333000033330000333300003333
def goal_109 : Nat := 0xffffffffffaaffaafafafafaaa00aa00ffffffffffaaffaafafafafaaa00aa00
def roots_109 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_110 : Nat := 0x5555000055550000555500005555
def goal_110 : Nat := 0xffffffffffccffccfcfcfcfc00000000ffffffffffccffccfcfcfcfc00000000
def roots_110 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xffffffffffeeffeefefefefeaa00aa00ffffffffffeeffeefefefefeaa00aa00
def roots_111 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_114 : Nat := 0x50005000500050005000500050005
def goal_114 : Nat := 0xffffffffffffcccccccccccc00000000ffffffffffffcccccccccccc00000000
def roots_114 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def goal_115 : Nat := 0xffffffffffffeeeeeeeeeeeeaaaa0000ffffffffffffeeeeeeeeeeeeaaaa0000
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_116 : Nat := 0x110011001100110011001100110011
def goal_116 : Nat := 0xffffffffffff0000f0f0f0f000000000ffffffffffff0000f0f0f0f000000000
def roots_116 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_117 : Nat := 0x330033003300330033003300330033
def goal_117 : Nat := 0xffffffffffffaaaafafafafaaaaa0000ffffffffffffaaaafafafafaaaaa0000
def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xffffffffffffccccfcfcfcfc00000000ffffffffffffccccfcfcfcfc00000000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xffffffffffffeeeefefefefeaaaa0000ffffffffffffeeeefefefefeaaaa0000
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_120 : Nat := 0x1010101010101010101010101010101
def goal_120 : Nat := 0xffffffffffffff00ff000000ff000000ffffffffffffff00ff000000ff000000
def roots_120 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_121 : Nat := 0x3030303030303030303030303030303
def goal_121 : Nat := 0xffffffffffffffaaffaaaaaaffaaaa00ffffffffffffffaaffaaaaaaffaaaa00
def roots_121 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_122 : Nat := 0x5050505050505050505050505050505
def goal_122 : Nat := 0xffffffffffffffccffccccccff000000ffffffffffffffccffccccccff000000
def roots_122 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffffffffffffffeeffeeeeeeffaaaa00ffffffffffffffeeffeeeeeeffaaaa00
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_124 : Nat := 0x11111111111111111111111111111111
def goal_124 : Nat := 0xffffffffffffff00fff0f0f0ff000000ffffffffffffff00fff0f0f0ff000000
def roots_124 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xffffffffffffffaafffafafaffaaaa00ffffffffffffffaafffafafaffaaaa00
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_126 : Nat := 0x55555555555555555555555555555555
def goal_126 : Nat := 0xffffffffffffffccfffcfcfcff000000ffffffffffffffccfffcfcfcff000000
def roots_126 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xffffffffffffffeefffefefeffaaaa00ffffffffffffffeefffefefeffaaaa00
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_137 : Nat := 0x30300000000000000000000000000000303
def goal_137 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_137 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_141 : Nat := 0x333300000000000000000000000000003333
def goal_141 : Nat := 0xfffafffafffafffafffafffafffafffaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_141 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_149 : Nat := 0x33003300000000000000000000000000330033
def goal_149 : Nat := 0xfffffafafffffafafffffafafffffafaaaaa0000aaaa0000aaaa0000aaaa0000
def roots_149 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_152 : Nat := 0x101010100000000000000000000000001010101
def goal_152 : Nat := 0xffffff00ffffff00ffffff00ffffff00ff000000ff000000ff000000ff000000
def roots_152 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_153 : Nat := 0x303030300000000000000000000000003030303
def goal_153 : Nat := 0xffffffaaffffffaaffffffaaffffffaaffaaaa00ffaaaa00ffaaaa00ffaaaa00
def roots_153 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_156 : Nat := 0x1111111100000000000000000000000011111111
def goal_156 : Nat := 0xfffffff0fffffff0fffffff0fffffff0ff000000ff000000ff000000ff000000
def roots_156 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_157 : Nat := 0x3333333300000000000000000000000033333333
def goal_157 : Nat := 0xfffffffafffffffafffffffafffffffaffaaaa00ffaaaa00ffaaaa00ffaaaa00
def roots_157 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_167 : Nat := 0xff000000ff0000000000000000000000ff000000ff
def goal_167 : Nat := 0xfffffffffafafafafffffffffafafafafefefefe00000000fefefefe00000000
def roots_167 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_171 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
def goal_171 : Nat := 0xffffffffffaaffaaffffffffffaaffaaeeeeeeeeaa00aa00eeeeeeeeaa00aa00
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_174 : Nat := 0x55550000555500000000000000000000555500005555
def goal_174 : Nat := 0xfffffffffff0fff0fffffffffff0fff0fcfcfcfc00000000fcfcfcfc00000000
def roots_174 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_175 : Nat := 0xffff0000ffff00000000000000000000ffff0000ffff
def goal_175 : Nat := 0xfffffffffffafffafffffffffffafffafefefefeaa00aa00fefefefeaa00aa00
def roots_175 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_178 : Nat := 0x500050005000500000000000000000005000500050005
def goal_178 : Nat := 0xffffffffffff0000ffffffffffff0000cccccccc00000000cccccccc00000000
def roots_178 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_182 : Nat := 0x5500550055005500000000000000000055005500550055
def goal_182 : Nat := 0xfffffffffffff0f0fffffffffffff0f0fcfcfcfc00000000fcfcfcfc00000000
def roots_182 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_183 : Nat := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
def goal_183 : Nat := 0xfffffffffffffafafffffffffffffafafefefefeaaaa0000fefefefeaaaa0000
def roots_183 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_186 : Nat := 0x50505050505050500000000000000000505050505050505
def goal_186 : Nat := 0xffffffffffffff00ffffffffffffff00ffccccccff000000ffccccccff000000
def roots_186 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffffffffffaaffffffffffffffaaffeeeeeeffaaaa00ffeeeeeeffaaaa00
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_188 : Nat := 0x111111111111111100000000000000001111111111111111
def goal_188 : Nat := 0xfffffffffffffff0fffffffffffffff0fff0f0f0ff000000fff0f0f0ff000000
def roots_188 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_190 : Nat := 0x555555555555555500000000000000005555555555555555
def goal_190 : Nat := 0xfffffffffffffff0fffffffffffffff0fffcfcfcff000000fffcfcfcff000000
def roots_190 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xfffffffffffffffafffffffffffffffafffefefeffaaaa00fffefefeffaaaa00
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_195 : Nat := 0xf000000000000000f000000000000000f000000000000000f
def goal_195 : Nat := 0xeeeeeeeeeeeeeeeeaaaaaaaaaaaaaaaaeeeeeeeeeeeeeeee0000000000000000
def roots_195 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_197 : Nat := 0x33000000000000003300000000000000330000000000000033
def goal_197 : Nat := 0xfafafafafafafafafafafafafafafafaaaaaaaaaaaaaaaaa0000000000000000
def roots_197 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_199 : Nat := 0xff00000000000000ff00000000000000ff00000000000000ff
def goal_199 : Nat := 0xfefefefefefefefefafafafafafafafaeeeeeeeeeeeeeeee0000000000000000
def roots_199 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_202 : Nat := 0x505000000000000050500000000000005050000000000000505
def goal_202 : Nat := 0xffccffccffccffccff00ff00ff00ff00ffccffccffccffcc0000000000000000
def roots_202 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffeeffeeffeeffeeffaaffaaffaaffaaffeeffeeffeeffeeaa00aa00aa00aa00
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_204 : Nat := 0x1111000000000000111100000000000011110000000000001111
def goal_204 : Nat := 0xfff0fff0fff0fff0fff0fff0fff0fff0ff00ff00ff00ff000000000000000000
def roots_204 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_205 : Nat := 0x3333000000000000333300000000000033330000000000003333
def goal_205 : Nat := 0xfffafffafffafffafffafffafffafffaffaaffaaffaaffaaaa00aa00aa00aa00
def roots_205 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_206 : Nat := 0x5555000000000000555500000000000055550000000000005555
def goal_206 : Nat := 0xfffcfffcfffcfffcfff0fff0fff0fff0ffccffccffccffcc0000000000000000
def roots_206 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_207 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def goal_207 : Nat := 0xfffefffefffefffefffafffafffafffaffeeffeeffeeffeeaa00aa00aa00aa00
def roots_207 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_210 : Nat := 0x50005000000000005000500000000000500050000000000050005
def goal_210 : Nat := 0xffffccccffffccccffff0000ffff0000ffffccccffffcccc0000000000000000
def roots_210 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffeeeeffffeeeeffffaaaaffffaaaaffffeeeeffffeeeeaaaa0000aaaa0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_212 : Nat := 0x110011000000000011001100000000001100110000000000110011
def goal_212 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0ffff0000ffff00000000000000000000
def roots_212 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xfffffcfcfffffcfcfffff0f0fffff0f0ffffccccffffcccc0000000000000000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xfffffefefffffefefffffafafffffafaffffeeeeffffeeeeaaaa0000aaaa0000
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_216 : Nat := 0x1010101000000000101010100000000010101010000000001010101
def goal_216 : Nat := 0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ff000000ff000000
def roots_216 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_217 : Nat := 0x3030303000000000303030300000000030303030000000003030303
def goal_217 : Nat := 0xffffffaaffffffaaffffffaaffffffaaffffffaaffffffaaffaaaa00ffaaaa00
def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def goal_218 : Nat := 0xffffffccffffffccffffff00ffffff00ffffffccffffffccff000000ff000000
def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffffeeffffffeeffffffaaffffffaaffffffeeffffffeeffaaaa00ffaaaa00
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_220 : Nat := 0x11111111000000001111111100000000111111110000000011111111
def goal_220 : Nat := 0xfffffff0fffffff0fffffff0fffffff0ffffff00ffffff00ff000000ff000000
def roots_220 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def goal_221 : Nat := 0xfffffffafffffffafffffffafffffffaffffffaaffffffaaffaaaa00ffaaaa00
def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xfffffffcfffffffcfffffff0fffffff0ffffffccffffffccff000000ff000000
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffefffffffefffffffafffffffaffffffeeffffffeeffaaaa00ffaaaa00
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_225 : Nat := 0x300000003000000030000000300000003000000030000000300000003
def goal_225 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaa00000000
def roots_225 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_226 : Nat := 0x500000005000000050000000500000005000000050000000500000005
def goal_226 : Nat := 0xffffffffccccccccffffffff00000000ffffffffcccccccccccccccc00000000
def roots_226 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def goal_227 : Nat := 0xffffffffeeeeeeeeffffffffaaaaaaaaffffffffeeeeeeeeeeeeeeee00000000
def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def goal_230 : Nat := 0xfffffffffcfcfcfcfffffffff0f0f0f0ffffffffccccccccfcfcfcfc00000000
def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def goal_231 : Nat := 0xfffffffffefefefefffffffffafafafaffffffffeeeeeeeefefefefe00000000
def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffaaffaaffffffffffaaffaaffffffffffaaffaaaaaaaaaaaa00aa00
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffccffccffffffffff00ff00ffffffffffccffcccccccccc00000000
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffeeffeeffffffffffaaffaaffffffffffeeffeeeeeeeeeeaa00aa00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_236 : Nat := 0x111100001111000011110000111100001111000011110000111100001111
def goal_236 : Nat := 0xfffffffffff0fff0fffffffffff0fff0ffffffffff00ff00f0f0f0f000000000
def roots_236 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xfffffffffffafffafffffffffffafffaffffffffffaaffaafafafafaaa00aa00
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_238 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def goal_238 : Nat := 0xfffffffffffcfffcfffffffffff0fff0ffffffffffccffccfcfcfcfc00000000
def roots_238 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffefffefffffffffffafffaffffffffffeeffeefefefefeaa00aa00
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def goal_242 : Nat := 0xffffffffffffccccffffffffffff0000ffffffffffffcccccccccccc00000000
def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffffeeeeffffffffffffaaaaffffffffffffeeeeeeeeeeeeaaaa0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_244 : Nat := 0x11001100110011001100110011001100110011001100110011001100110011
def goal_244 : Nat := 0xfffffffffffff0f0fffffffffffff0f0ffffffffffff0000f0f0f0f000000000
def roots_244 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffffffcfcfffffffffffff0f0ffffffffffffccccfcfcfcfc00000000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffefefffffffffffffafaffffffffffffeeeefefefefeaaaa0000
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_248 : Nat := 0x101010101010101010101010101010101010101010101010101010101010101
def goal_248 : Nat := 0xffffffffffffff00ffffffffffffff00ffffffffffffff00ff000000ff000000
def roots_248 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffaaffffffffffffffaaffffffffffffffaaffaaaaaaffaaaa00
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffccffffffffffffff00ffffffffffffffccffccccccff000000
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffeeffffffffffffffaaffffffffffffffeeffeeeeeeffaaaa00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_252 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
def goal_252 : Nat := 0xfffffffffffffff0fffffffffffffff0ffffffffffffff00fff0f0f0ff000000
def roots_252 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffafffffffffffffffaffffffffffffffaafffafafaffaaaa00
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffcfffffffffffffff0ffffffffffffffccfffcfcfcff000000
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffefffffffffffffffaffffffffffffffeefffefefeffaaaa00
def roots_255 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

namespace S_25
def pG:List (Nat×Nat):=[(1,9),(1,17),(8,9),(8,24),(16,17),(16,24)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3f
def xsM:=roots_25.map (·&&&dom_25)
def gM:=goal_25&&&dom_25
def NN:Nat→Nat
|2=>1
|3=>1
|_=>0
def HT:Nat→Nat→Nat
|2,0=>0x22873
|3,0=>0x22873
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x3030000c000c02020202
|_,_=>0
def sP:Nat→Nat
|0=>0x924
|_=>0
def sO:Nat→Nat→Nat
|2,0=>3
|3,0=>0x33
|_,_=>0
def wAt:=mkWire dB 3 26 0x3ffffff
def SS:=mkSS wAt sP sO 2 7
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def mkPools (_ _:Nat):List (Nat×Nat×(Nat×List Nat)):=[]
def mkCut (_ _:Nat) (_:Nat×Nat×Nat) (_:List Nat):Bool:=false
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_25 gM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_25 gM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat×Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_25==dom_25)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_25 gM v ys):RunD true dom_25 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_25 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s:Nat) (hs:s≤3):∀ i<NN s,bar dom_25 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 2 2=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤3) (h:RunD true dom_25 gM s xsM):False:=by
  have hmin:2≤s:=by have hl:=run_len h;change 3≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_25 roots_25 goal_25 4:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_25
theorem lowS_25:Lower true dom_25 roots_25 goal_25 4:=S_25.noCircuit
def isoMvS_73:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_73:Lower true dom_73 roots_73 goal_73 4:=lower_iso_b isoMvS_73 (by decide +kernel) lowS_25
def isoMvS_81:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_81:Lower true dom_81 roots_81 goal_81 4:=lower_iso_b isoMvS_81 (by decide +kernel) lowS_25
def isoMvS_88:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_88:Lower true dom_88 roots_88 goal_88 4:=lower_iso_b isoMvS_88 (by decide +kernel) lowS_25
def isoMvS_98:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_98:Lower true dom_98 roots_98 goal_98 4:=lower_iso_b isoMvS_98 (by decide +kernel) lowS_25
def isoMvS_137:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_137:Lower true dom_137 roots_137 goal_137 4:=lower_iso_b isoMvS_137 (by decide +kernel) lowS_25
def isoMvS_152:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_152:Lower true dom_152 roots_152 goal_152 4:=lower_iso_b isoMvS_152 (by decide +kernel) lowS_25
namespace S_43
def pG:List (Nat×Nat):=[(1,9),(1,33),(2,34),(3,11),(3,35),(8,9),(10,11),(10,42),(32,33),(32,34),(40,41),(40,42)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfff
def xsM:=roots_43.map (·&&&dom_43)
def gM:=goal_43&&&dom_43
def NN:Nat→Nat
|3=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0xd70c9
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f00000000f0000000f00c0c00000c0ca0a00000a0a
|_,_=>0
def sP:Nat→Nat
|0=>0xe4
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|_,_=>0
def wAt:=mkWire dB 4 44 0xfffffffffff
def SS:=mkSS wAt sP sO 2 7
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def mkPools (_ _:Nat):List (Nat×Nat×(Nat×List Nat)):=[]
def mkCut (_ _:Nat) (_:Nat×Nat×Nat) (_:List Nat):Bool:=false
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_43 gM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_43 gM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat×Nat)):=[[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_43==dom_43)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_43 gM v ys):RunD true dom_43 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_43 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s:Nat) (hs:s≤3):∀ i<NN s,bar dom_43 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 1 3=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤3) (h:RunD true dom_43 gM s xsM):False:=by
  have hmin:3≤s:=by have hl:=run_len h;change 4≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_43 roots_43 goal_43 4:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_43
theorem lowS_43:Lower true dom_43 roots_43 goal_43 4:=S_43.noCircuit
theorem lowS_57:Lower true dom_57 roots_57 goal_57 5:=lower_slice_b [(0x303030300000000,1,33)] (by decide +kernel) lowS_25
namespace S_89
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(8,9),(8,24),(8,72),(16,17),(16,24),(16,80),(64,65),(64,72),(64,80)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfff
def xsM:=roots_89.map (·&&&dom_89)
def gM:=goal_89&&&dom_89
def NN:Nat→Nat
|3=>3
|4=>7
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x922763f74c070e9
|4,0=>0x6ebab310173021e29bbd24a8c18324114e4
|5,0=>0x61e1742a8701a8f
|6,0=>0x1a8f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xc0c0c0c000000000c000c030303000000000003030300c080c08000000000c080c0b03030300000000030203020000c0c00000000000008080000000000000003030300404040000000000040404010101010000000001010100c000c00000000000c00080303000000000000030300008080808000000000808080b0303030000000000000000c0c0808000000000c0c080b0303030000000003030000c000c00000000000c000c030303030000000002020202
|_,_=>0
def sP:Nat→Nat
|0=>0x6154610546d15461546d1046f105e6d546c154615b4a615461594618467543210
|_=>0
def sO:Nat→Nat→Nat
|3,0=>0x21022004
|4,0=>0xa952aa0536a5948a8c5
|5,0=>0xe159aaf4
|6,0=>0x3d4
|_,_=>0
def wAt:=mkWire dB 16 90 0x3ffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x5454515551455051654564551
|_=>0
def oO:Nat→Nat→Nat
|3,0=>2
|4,0=>0x62422200000000
|5,0=>0x918100
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0xfcb930
|_=>0
def pmB:Nat→Nat→Nat
|3,0=>1
|4,0=>0x111000
|5,0=>0x16b
|6,0=>5
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 4 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_88 4 roots_88 ops++addP pm 1 dom_73 4 roots_73 ops++addP pm 2 dom_25 4 roots_25 ops++addP pm 3 dom_81 4 roots_81 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_89 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_88 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_25 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_81 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_88 4 s (0,roots_88.map (·&&&dom_88)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_89 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_88 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_89==dom_89)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_89 gM v ys):RunD true dom_89 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_89 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 3 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 7 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_89 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_89 gM s xsM):False:=by
  have hmin:3≤s:=by have hl:=run_len h;change 4≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_89 roots_89 goal_89 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_89
theorem lowS_89:Lower true dom_89 roots_89 goal_89 7:=S_89.noCircuit
theorem lowS_99:Lower true dom_99 roots_99 goal_99 5:=lower_slice_b [(0xa0000000a0000000a0000000a,32,33)] (by decide +kernel) lowS_98
def isoMvS_45:List (Nat×Nat):=[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_45:Lower true dom_45 roots_45 goal_45 4:=lower_iso_b isoMvS_45 (by decide +kernel) lowS_43
def isoMvS_51:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_51:Lower true dom_51 roots_51 goal_51 4:=lower_iso_b isoMvS_51 (by decide +kernel) lowS_43
def isoMvS_53:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_53:Lower true dom_53 roots_53 goal_53 4:=lower_iso_b isoMvS_53 (by decide +kernel) lowS_43
def isoMvS_75:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_75:Lower true dom_75 roots_75 goal_75 5:=lower_iso_b isoMvS_75 (by decide +kernel) lowS_57
def isoMvS_83:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_83:Lower true dom_83 roots_83 goal_83 5:=lower_iso_b isoMvS_83 (by decide +kernel) lowS_57
def isoMvS_90:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_90:Lower true dom_90 roots_90 goal_90 5:=lower_iso_b isoMvS_90 (by decide +kernel) lowS_57
def isoMvS_101:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_101:Lower true dom_101 roots_101 goal_101 5:=lower_iso_b isoMvS_101 (by decide +kernel) lowS_57
def isoMvS_102:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_102:Lower true dom_102 roots_102 goal_102 5:=lower_iso_b isoMvS_102 (by decide +kernel) lowS_57
def isoMvS_105:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_105:Lower true dom_105 roots_105 goal_105 5:=lower_iso_b isoMvS_105 (by decide +kernel) lowS_99
def isoMvS_106:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_106:Lower true dom_106 roots_106 goal_106 5:=lower_iso_b isoMvS_106 (by decide +kernel) lowS_57
def isoMvS_108:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_108:Lower true dom_108 roots_108 goal_108 4:=lower_iso_b isoMvS_108 (by decide +kernel) lowS_43
def isoMvS_114:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_114:Lower true dom_114 roots_114 goal_114 5:=lower_iso_b isoMvS_114 (by decide +kernel) lowS_57
def isoMvS_116:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_116:Lower true dom_116 roots_116 goal_116 4:=lower_iso_b isoMvS_116 (by decide +kernel) lowS_43
def isoMvS_120:List (Nat×Nat):=[(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_120:Lower true dom_120 roots_120 goal_120 5:=lower_iso_b isoMvS_120 (by decide +kernel) lowS_57
def isoMvS_141:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_141:Lower true dom_141 roots_141 goal_141 5:=lower_iso_b isoMvS_141 (by decide +kernel) lowS_57
def isoMvS_149:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_149:Lower true dom_149 roots_149 goal_149 5:=lower_iso_b isoMvS_149 (by decide +kernel) lowS_57
def isoMvS_153:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_153:Lower true dom_153 roots_153 goal_153 7:=lower_iso_b isoMvS_153 (by decide +kernel) lowS_89
def isoMvS_156:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_156:Lower true dom_156 roots_156 goal_156 5:=lower_iso_b isoMvS_156 (by decide +kernel) lowS_57
def isoMvS_178:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_178:Lower true dom_178 roots_178 goal_178 4:=lower_iso_b isoMvS_178 (by decide +kernel) lowS_43
def isoMvS_195:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_195:Lower true dom_195 roots_195 goal_195 4:=lower_iso_b isoMvS_195 (by decide +kernel) lowS_43
def isoMvS_197:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_197:Lower true dom_197 roots_197 goal_197 4:=lower_iso_b isoMvS_197 (by decide +kernel) lowS_43
def isoMvS_202:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_202:Lower true dom_202 roots_202 goal_202 4:=lower_iso_b isoMvS_202 (by decide +kernel) lowS_43
def isoMvS_204:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_204:Lower true dom_204 roots_204 goal_204 4:=lower_iso_b isoMvS_204 (by decide +kernel) lowS_43
def isoMvS_210:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_210:Lower true dom_210 roots_210 goal_210 4:=lower_iso_b isoMvS_210 (by decide +kernel) lowS_43
def isoMvS_212:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_212:Lower true dom_212 roots_212 goal_212 4:=lower_iso_b isoMvS_212 (by decide +kernel) lowS_43
def isoMvS_216:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_216:Lower true dom_216 roots_216 goal_216 5:=lower_iso_b isoMvS_216 (by decide +kernel) lowS_99
def isoMvS_225:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_225:Lower true dom_225 roots_225 goal_225 5:=lower_iso_b isoMvS_225 (by decide +kernel) lowS_99
def isoMvS_226:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_226:Lower true dom_226 roots_226 goal_226 5:=lower_iso_b isoMvS_226 (by decide +kernel) lowS_57
theorem lowS_47:Lower true dom_47 roots_47 goal_47 5:=lower_slice_b [(0xcccc0000cccc,32,34)] (by decide +kernel) lowS_45
def dzo_57_2:=0xc0c0c0c0c0c0c0c
def gzo_57_2:=0xc0c0c0c0c080800
def gsh_57_2:=0x303030303020200
theorem lowS_zo_57_2_25:Lower true dzo_57_2 roots_57 gzo_57_2 5:=lower_iso_b (d1:=dom_57) (r1:=roots_57) (T1:=gsh_57_2) [(dom_57,2)] (by decide +kernel) (lower_slice_b (T:=gsh_57_2) [(0x303030300000000,0,32)] (by decide +kernel) lowS_25)
namespace S_59
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(2,34),(3,11),(3,19),(3,35),(8,9),(8,24),(10,11),(10,26),(10,42),(16,17),(16,24),(18,19),(18,26),(18,50),(32,33),(32,34),(40,41),(40,42),(40,56),(48,49),(48,50),(48,56)]
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
|4,0=>0xb35c3aa8c3
|5,0=>0xa75f19e68f0deb7
|6,0=>0x9abd7
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xa000a000a000af0f0f000f0f0f00f0a0f0a0f0a0f0af0a00000f0a0000f000f000f000f00f0f0f0f00000000f0f00000f0f0000c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a00f000a000f000a
|_,_=>0
def sP:Nat→Nat
|0=>0x435214352194835214375214652143210
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
|0=>0x146
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x400
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 5
def pmP:Nat→Nat
|0=>0xf9c40
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x25
|6,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 2 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_57 5 roots_57 ops++addP pm 1 dom_51 4 roots_51 ops++addP pm 2 dzo_57_2 5 roots_57 ops++addP pm 3 dom_43 4 roots_43 ops++addP pm 4 dom_25 4 roots_25 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_59 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_57_2_25 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_25 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_57 5 s (0,roots_57.map (·&&&dom_57)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_59 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_57 h
def symsG:List (List (Nat×Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]]
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
theorem lowS_91:Lower true dom_91 roots_91 goal_91 8:=lower_slice_b [(0xc0c0c0c000000000c0c0c0c,64,66)] (by decide +kernel) lowS_89
theorem lowS_103:Lower true dom_103 roots_103 goal_103 6:=lower_slice_b [(0xaa000000aa000000aa000000aa,32,33)] (by decide +kernel) lowS_102
namespace S_107
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(2,34),(2,66),(3,11),(3,35),(3,67),(8,9),(8,72),(10,11),(10,42),(10,74),(32,33),(32,34),(32,96),(40,41),(40,42),(40,104),(64,65),(64,66),(64,72),(64,96)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffff
def xsM:=roots_107.map (·&&&dom_107)
def gM:=goal_107&&&dom_107
def NN:Nat→Nat
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0xb40cf
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0000000000000f0f00000000f0000000f0000000f0000000f00c0c00000c0c00000c0c00000c0ca0a00000a0a00000a0a00000a0af0f00000f0f0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x4688
|_=>0
def sO:Nat→Nat→Nat
|6,0=>5
|_,_=>0
def wAt:=mkWire dB 5 108 0xfffffffffffffffffffffffffff
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
addP pm 0 dom_106 5 roots_106 ops++addP pm 1 dom_105 5 roots_105 ops++addP pm 2 dom_99 5 roots_99 ops++addP pm 3 dom_75 5 roots_75 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_107 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_75 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_106 5 s (0,roots_106.map (·&&&dom_106)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_107 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_106 h
def symsG:List (List (Nat×Nat)):=[[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_107==dom_107)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_107 gM v ys):RunD true dom_107 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_107 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_107 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_107 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_107 roots_107 goal_107 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_107
theorem lowS_107:Lower true dom_107 roots_107 goal_107 7:=S_107.noCircuit
def dzo_105_4:=0x3030000030300000303000003030
def gzo_105_4:=0x3030000030200000303000002000
def gsh_105_4:=0x303000003020000030300000200
theorem lowS_zo_105_4_73:Lower true dzo_105_4 roots_105 gzo_105_4 5:=lower_iso_b (d1:=dom_105) (r1:=roots_105) (T1:=gsh_105_4) [(dom_105,4)] (by decide +kernel) (lower_slice_b (T:=gsh_105_4) [(0x303000000000000030300000000,0,32)] (by decide +kernel) lowS_73)
namespace S_109
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(4,36),(5,13),(5,37),(5,69),(8,9),(8,72),(12,13),(12,44),(12,76),(32,33),(32,36),(32,96),(40,41),(40,44),(40,104),(64,65),(64,72),(64,96),(68,69),(68,76),(68,100)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_109.map (·&&&dom_109)
def gM:=goal_109&&&dom_109
def NN:Nat→Nat
|4=>1
|5=>1
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x7cc9d
|5,0=>0x38010
|6,0=>0xf22e7
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x3300000033000000330000003300cccc0000cccc000088880000888b333000000000000333300000000c0c00000c0c00000c0c00000c0c222200002222000022220000222200cc000000cc000000880000008b333000033330000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x99a133a84688
|_=>0
def sO:Nat→Nat→Nat
|4,0=>5
|5,0=>0x56
|6,0=>0xb5
|_,_=>0
def wAt:=mkWire dB 7 110 0x3fffffffffffffffffffffffffff
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
addP pm 0 dom_105 5 roots_105 ops++addP pm 1 dom_108 4 roots_108 ops++addP pm 2 dzo_105_4 5 roots_105 ops++addP pm 3 dom_101 5 roots_101 ops++addP pm 4 dom_45 4 roots_45 ops++addP pm 5 dom_73 4 roots_73 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_109 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_108 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_105_4_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_101 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_73 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_105 5 s (0,roots_105.map (·&&&dom_105)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_109 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_105 h
def symsG:List (List (Nat×Nat)):=[[(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_109==dom_109)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_109 gM v ys):RunD true dom_109 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_109 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_109 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_109 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_109 roots_109 goal_109 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_109
theorem lowS_109:Lower true dom_109 roots_109 goal_109 7:=S_109.noCircuit
theorem lowS_110:Lower true dom_110 roots_110 goal_110 6:=lower_slice_b [(0x5050000050500000505000005050,32,36)] (by decide +kernel) lowS_106
theorem lowS_121:Lower true dom_121 roots_121 goal_121 8:=lower_slice_b [(0x3030303000000000303030300000000,1,33)] (by decide +kernel) lowS_89
namespace S_122
def pG:List (Nat×Nat):=[(2,34),(2,66),(8,24),(8,72),(10,26),(10,42),(10,74),(16,24),(16,80),(18,26),(18,50),(18,82),(32,34),(32,96),(40,42),(40,56),(40,104),(48,50),(48,56),(48,112),(64,66),(64,72),(64,80),(64,96)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_122.map (·&&&dom_122)
def gM:=goal_122&&&dom_122
def NN:Nat→Nat
|3=>1
|4=>4
|5=>10
|6=>4
|7=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x133c1
|4,0=>0x28d62262a214b890b29b
|5,0=>0x5310e44a1c3b9423964c303ee2aadd28cbd1df1e0af2306eef
|6,0=>0xc00bf19ac114b5b05b3e
|7,0=>0xc00bf
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xa0a0a0a0a0a000141414141414000014141414141400028282828282828282828282828280000000000000500050000000000000000202020200000202020202020000000000014140000141400001414000014028282828000000002828282800000005050505050505050500050005000500a080a080a080a08000000000000000141414141414101014141414000000020202020202020202020202020202025050505050505050000000000000000a0a0a0a0a080a080a0a0a0a0000000141400001414000014140000141400028002800280028002800280028002805050505050505050404040404040404
|0,1=>0x505000005050000000000000000a0a0a0a0a0a0a0a0a0a0a0a000000000000000141414140000000000000002828282800002828282828280000000000050500000505000005050000000000000000a0a0a0a000000000808080941014101410141014101410141014128282828282800000000000000000000000505000005050000050000000500
|_,_=>0
def sP:Nat→Nat
|0=>0x24412912209489104a4c3922094891040525c41292d548825224412d0820966448a4829122094914a025811e9104a46a441291220948c4882b2242551122414e6104a418820
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|4,0=>0x26a3944a845
|5,0=>0x26b47682cf15b330654c918f3186
|6,0=>0xcab7dacb536
|7,0=>0x6a5
|_,_=>0
def wAt:=mkWire dB 25 123 0x7ffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x112489291112091710122091711
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x510000413112000100
|6,0=>0x817161
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 8
def pmP:Nat→Nat
|0=>0x3ff7be7078a185080
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x4100256030
|6,0=>0x79a8
|7,0=>0xa
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 6 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_120 5 roots_120 ops++addP pm 1 dom_88 4 roots_88 ops++addP pm 2 dom_98 4 roots_98 ops++addP pm 3 dom_90 5 roots_90 ops++addP pm 4 dom_106 5 roots_106 ops++addP pm 5 dom_114 5 roots_114 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_122 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_120 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_88 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_98 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_114 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_120 5 s (0,roots_120.map (·&&&dom_120)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_122 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_120 h
def symsG:List (List (Nat×Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)],[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_122==dom_122)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_122 gM v ys):RunD true dom_122 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_122 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 4 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
theorem checked (s:Nat) (hs:s≤7):∀ i<NN s,bar dom_122 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤7) (h:RunD true dom_122 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_122 roots_122 goal_122 8:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_122
theorem lowS_122:Lower true dom_122 roots_122 goal_122 8:=S_122.noCircuit
theorem lowS_199:Lower true dom_199 roots_199 goal_199 5:=lower_slice_b [(0xcc00000000000000cc00000000000000cc00000000000000cc,64,66)] (by decide +kernel) lowS_197
theorem lowS_217:Lower true dom_217 roots_217 goal_217 8:=lower_slice_b [(0x3030303000000000000000000000000030303030000000000000000,1,65)] (by decide +kernel) lowS_153
theorem lowS_233:Lower true dom_233 roots_233 goal_233 6:=lower_slice_b [(0x30000000300000003000000030000000300000003000000030000000300,1,9)] (by decide +kernel) lowS_225
theorem lowS_234:Lower true dom_234 roots_234 goal_234 6:=lower_slice_b [(0x50000000500000005000000050000000500000005000000050000000500,64,72)] (by decide +kernel) lowS_226
theorem lowS_248:Lower true dom_248 roots_248 goal_248 6:=lower_slice_b [(0x101010100000000010101010000000001010101000000000101010100000000,64,96)] (by decide +kernel) lowS_216
def isoMvS_55:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_55:Lower true dom_55 roots_55 goal_55 5:=lower_iso_b isoMvS_55 (by decide +kernel) lowS_47
def isoMvS_61:List (Nat×Nat):=[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_61:Lower true dom_61 roots_61 goal_61 7:=lower_iso_b isoMvS_61 (by decide +kernel) lowS_59
def isoMvS_115:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_115:Lower true dom_115 roots_115 goal_115 7:=lower_iso_b isoMvS_115 (by decide +kernel) lowS_107
def isoMvS_117:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_117:Lower true dom_117 roots_117 goal_117 7:=lower_iso_b isoMvS_117 (by decide +kernel) lowS_109
def isoMvS_118:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_118:Lower true dom_118 roots_118 goal_118 6:=lower_iso_b isoMvS_118 (by decide +kernel) lowS_110
def isoMvS_124:List (Nat×Nat):=[(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_124:Lower true dom_124 roots_124 goal_124 7:=lower_iso_b isoMvS_124 (by decide +kernel) lowS_59
def isoMvS_157:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_157:Lower true dom_157 roots_157 goal_157 8:=lower_iso_b isoMvS_157 (by decide +kernel) lowS_91
def isoMvS_167:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_167:Lower true dom_167 roots_167 goal_167 6:=lower_iso_b isoMvS_167 (by decide +kernel) lowS_103
def isoMvS_171:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_171:Lower true dom_171 roots_171 goal_171 7:=lower_iso_b isoMvS_171 (by decide +kernel) lowS_109
def isoMvS_174:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_174:Lower true dom_174 roots_174 goal_174 6:=lower_iso_b isoMvS_174 (by decide +kernel) lowS_110
def isoMvS_182:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_182:Lower true dom_182 roots_182 goal_182 6:=lower_iso_b isoMvS_182 (by decide +kernel) lowS_110
def isoMvS_186:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_186:Lower true dom_186 roots_186 goal_186 7:=lower_iso_b isoMvS_186 (by decide +kernel) lowS_59
def isoMvS_188:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_188:Lower true dom_188 roots_188 goal_188 8:=lower_iso_b isoMvS_188 (by decide +kernel) lowS_122
def isoMvS_203:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_203:Lower true dom_203 roots_203 goal_203 7:=lower_iso_b isoMvS_203 (by decide +kernel) lowS_109
def isoMvS_205:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)]
theorem lowS_205:Lower true dom_205 roots_205 goal_205 7:=lower_iso_b isoMvS_205 (by decide +kernel) lowS_109
def isoMvS_206:List (Nat×Nat):=[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_206:Lower true dom_206 roots_206 goal_206 5:=lower_iso_b isoMvS_206 (by decide +kernel) lowS_199
def isoMvS_211:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_211:Lower true dom_211 roots_211 goal_211 7:=lower_iso_b isoMvS_211 (by decide +kernel) lowS_109
def isoMvS_214:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_214:Lower true dom_214 roots_214 goal_214 5:=lower_iso_b isoMvS_214 (by decide +kernel) lowS_199
def isoMvS_218:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_218:Lower true dom_218 roots_218 goal_218 7:=lower_iso_b isoMvS_218 (by decide +kernel) lowS_109
def isoMvS_220:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_220:Lower true dom_220 roots_220 goal_220 7:=lower_iso_b isoMvS_220 (by decide +kernel) lowS_109
def isoMvS_227:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_227:Lower true dom_227 roots_227 goal_227 7:=lower_iso_b isoMvS_227 (by decide +kernel) lowS_107
def isoMvS_230:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_230:Lower true dom_230 roots_230 goal_230 8:=lower_iso_b isoMvS_230 (by decide +kernel) lowS_122
def isoMvS_236:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_236:Lower true dom_236 roots_236 goal_236 6:=lower_iso_b isoMvS_236 (by decide +kernel) lowS_234
def isoMvS_242:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_242:Lower true dom_242 roots_242 goal_242 6:=lower_iso_b isoMvS_242 (by decide +kernel) lowS_234
def isoMvS_244:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_244:Lower true dom_244 roots_244 goal_244 6:=lower_iso_b isoMvS_244 (by decide +kernel) lowS_234
theorem lowS_63:Lower true dom_63 roots_63 goal_63 8:=lower_slice_b [(0xcccccccccccccccc,32,34)] (by decide +kernel) lowS_61
def dzo_75_4:=0xf0f0000000000000f0f0
def gzo_75_4:=0xf0e0000000000000a000
def gsh_75_4:=0xf0e0000000000000a00
theorem lowS_zo_75_4_75:Lower true dzo_75_4 roots_75 gzo_75_4 5:=lower_iso_b (d1:=dom_75) (r1:=roots_75) (T1:=gsh_75_4) [(dom_75,4)] (by decide +kernel) (lower_slice_b (T:=gsh_75_4) [] (by decide +kernel) lowS_75)
def dzo_107_4:=0xf0f00000f0f00000f0f00000f0f0
def gzo_107_4:=0xf0f00000f0e00000f0f00000a000
def gsh_107_4:=0xf0f00000f0e00000f0f00000a00
theorem lowS_zo_107_4_75:Lower true dzo_107_4 roots_107 gzo_107_4 6:=lower_iso_b (d1:=dom_107) (r1:=roots_107) (T1:=gsh_107_4) [(dom_107,4)] (by decide +kernel) (lower_slice_b (T:=gsh_107_4) [(0xf0f0000000000000f0f00000000,0,32)] (by decide +kernel) lowS_75)
namespace S_111
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(2,34),(2,66),(3,11),(3,35),(3,67),(4,36),(5,13),(5,37),(5,69),(6,38),(6,70),(7,15),(7,39),(7,71),(8,9),(8,72),(10,11),(10,42),(10,74),(12,13),(12,44),(12,76),(14,15),(14,46),(14,78),(32,33),(32,34),(32,36),(32,96),(40,41),(40,42),(40,44),(40,104),(64,65),(64,66),(64,72),(64,96),(68,69),(68,70),(68,76),(68,100)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_111.map (·&&&dom_111)
def gM:=goal_111&&&dom_111
def NN:Nat→Nat
|3=>1
|4=>30
|5=>85
|6=>62
|7=>14
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x81983
|4,0=>0xf4cebf4a8cf37ddefbf8e62f0e06a7d76cdcf45cc470dbc66cae97cac03498ba3822b477876775a87549374f3a74cd763b085674a4fb424b60941fb837fa33477134263286241863e10222
|5,0=>0xfe925fa06cf66a1f5a84f4ebbf370eec8f0ebeedead30e1289e0c2cda1b2d9fdad925ad8c73d3ce9d3191d29f2d124ac9d53c3010c0aedba332b54e7b2348b2291ad2cba76a2a6edda474ba37c6a36169cc969b3e794cef93ca19035a8e7c88a49888207868b3867de8319c7ff4577ed9773626daca684c96813766f36665cb642e4632705e759576ab5610450e504ea9c4cc984c36f4af764412043144413a13b53b3840237cdb373782c9412a17c29634264711900d175da15ea1156b013d441111c0e2630c14e0a9da09e610610405e47018b3
|6,0=>0xff7baff456fe4aafaf9ff7888ef8b0e7720e5fbce3953e124adda15dbf7cda2ddd02b7cf0bdcb0bfc4822c1894bd12cafc8dac4e4abdd7a74929e95c9cdbf9cb029b512993eb9596190d278ccc28a9148928385f7f835c6819eb8026d778e770e6d6e2c569e4c696ad66735600ba5edaa57a5c52dc552882522df4f25348e1a4445943f863a2d138d69265e22621016c000d1ff0a98106d4101f5b
|7,0=>0xf4fe6d9385ba452932268097a7ff727aee871b6770f986d8816d3605d719520c32c61c
|8,0=>0x4f37e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xeeee0000eeee0000eeee00000000ffff0000aaaa0000ffff0000aaaa0000000000000000fefe0000fefe1111000011110000000000000000ffff000000000000ffff00000000ff000000ff000000ff000000ff000333000000330000030300000000ffff0000ffff0000000000000000cccc0000cccc0000cccc0000ccccaaaa0000aaaa0000aaaa0000aaaaffff0000ff000000ffff0000ff00ffff0000ffff0000aaaa0000aaaaffff0000ffff0000ffff00000000f0f00000f0f00000f0f00000f0f0eeee0000eeee0000eeee0000eeeeffff0000ff000000aaaa0000aa00
|0,1=>0xffff0000ffff00000f0f000000000000000000ff0000ffff0000ff00ffff0000ffff0000ffff0000aaaaffff0000ffff0000ff000000ff00ffff0000ffaa0000ff000000ff00ffff0000eeee0000cccc0000ccccbbbb0000bbbb0000abab0000aaaa111100001111000001010000000055550000555500005454000054540000000000000000ffff0000aaaaffff0000ffff0000ffff0000ff00ffff0000ffaa0000aaaa0000aaaa0fff000000ff00000faf000000aaffff0000ffcc0000cccc0000cccc1313000011110000030300000000ffff0000ffff0000afaf0000aaaa
|0,2=>0xf1f10000f1f10000f0f00000f0f0fefe0000fefe0000fefe0000fefeffff000000ff0000ffff00000000efef0000eeee0000efef0000eeeeffff0000ffff0000fafa0000fafa00000000ffff000000000000ff00ffff0000ff000000000000000000ffff000000ff0000ffff000000aa3333000033330000333300002222ffff0000aaaa0000000000000000ffff0000ff000000ffff00000000555500005500000055550000550000000000ffff000000000000aaaaffff000000000000fefe0000000033330000333300002323000022220000000000000000afaf0000aaaa
|0,3=>0xff00000000000000000000000000ff00000000000000aa5555000055550000555500005500f0ff0000f0ff0000f0fa0000f0fa00ff000000ff000000aa000000aa0f0f0000000000000f0f00000000ffff0000ffff0000fefe0000fefe5f5f0000555500000f0f000000003333000011110000333300000000333300000033000033330000000011110000111100001010000010100000000000000000ffff0000ff0000ff000000ff0000000000000000333300003333000003030000000000ff000000ff000000ff000000aaffff000055550000ffff00000000
|0,4=>0xaaaa0000ffff0000aaaa0000aaaa0000000000aa0000aaaa0000aaaa5555000055550000050500000000aaaa0000aaaa0000aaaa0000aa00bbbb0000bbbb0000bbbb0000aaaa00aa000000ff000000aa000000aaafaf0000aaaa0000afaf0000aaaa33330000333300003333000000000fff000000ff00000f0f0000000000000000ffff0000000000000000bbbb0000bbbb0000aaaa0000aaaa00ff000000ff000000ee000000ee111100001111000011110000000033330000333300003333000033005555000055550000000000000000ffff0000ffff0000f0f00000f0f0
|0,5=>0xff00000000000000ff00fafa0000fafa0000fafa0000fafa5555000055550000505000005050f0ff0000f0ff0000f0f00000f0f0f5f50000f5f50000f0f00000f0f0ffff0000ffaa0000ffff0000ffaaff000000ffff0000ff000000ff0000ff000000ff000000ff000000000000000055550000000000000000ffff0000ffff0000eeee0000eeeeffff0000eeee0000ffff0000eeee5555000055550000555500000000
|_,_=>0
def sP:Nat→Nat
|0=>0x3a080881670107282cd820e10283041ca031408d061628c86102c506302018a041ca0506089061628097102c1010020296040440b14340842a2c107282c386262018a044830e14087881628311102c501202058a043c20e041c0081628686182c50612201820e1800506080840608080
|1=>0xab41070c2058a5804308162810f0c2058a56042080a08386542018a041c329502c1070c2058a041c22616281064e2018a041c32616083860020296041c3080a941070c2028e041d2081628101462028b04042080a0c1010c20522021840b141908816280a0102c501087cf0b041c305
|2=>0xcfc5820e19f0816281077a205bc0e19d8816286810c2058a0211d081629c810c2058a0e19c0816281066e2059c041c32916281066c2058a0219a880a2c101482058a0448308682c1070ccc58a0c7d9080a0c1070ca45820e198880ac01070c20b0b140808816297810c2058a5c04208
|3=>0x1408d06102c502021230b14080c510141820e1030b14199080a0c1070d04e8b1408088160808688205ab0e19d880ad01820e1828b041de881c0c5020e1058a041ca0816283a00c2058a041a18816283840c7c58a041a10816283863f0458a80042080a2c1120c2029d041c308682c107
|4=>0xf3840b801c33b10545820e1948b141c34d10145820f3040e0628101102c5010c7c40b14064881608084762058a052c308161c33a762058a0e403081608386942018b14080840a38101102c5079210405060834810147020e1040b360838610145820e5040b141c34710145820d0840b
|5=>0x1408386a82058a041c308a62c502a4043081608386762058a041a40816705070ce840b14083840d18e8b140838610145820e18429162a0010c2288b1408086102c5400e1030816281070c2148b140433a102c5020e1842616281010c20605041c350102c502033c40b14b83081814582
|6=>0xe184411c2c502022058a041e786100c58a041a4080ad05820e18405160838610cc70b1408384105428b041c3081c0c5020e1840b140838610fc58a0f2430816083840cec40baa281070c2018b14083840c147020e1840316281070d0459c150038610d058a041c3082a2c5020e1840b
|7=>0x1608386482058aae1c30816297010c2058a041c32a102c50202104050608386105858a041c308ac145820e1840316281010c2058a041c350102c52b0e1030816283863e2028b04043080a2c1070c21f8506281070c2058a04043088c2c5020e191880a2c107081840b14ac3861014582
|8=>0x62c5020e1840b1408086102c1070d6c4051608386102c55a0e1840b14083840c2058a041c308822c5020e1844616281070c2198516281070c2070b1408386102c5070d6440b156038610c058a041c30816283840ce840b141c33a110568b1408386102c5070ce84330a2ce020e18405
|9=>0xb1408386102c5400e1840b141c33a102ce0a041c308
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|4,0=>0x4aa8905116a219440a87c50eea1c9436a86850c6a17942ca854509ea129422a8405076a0d9418a82c504ea08940ea8185026a039404a8045
|5,0=>0x426c835903b20163f6c7d58f7b1e963c8a7798ec31d26398c7198e031ba6368c6b98d431a26338c6598c8318a6308c5f98bc317262d8c5998b0315a62a8c5398a431426278c4d9898312a6248c47988c31126218c41988030fa61e8c3b987430e261b8c35986830ca6188c2f985c30b26158c299850309a6
|5,1=>0x28f6512ca0d93eb27764e2c9ad932b25f64b2c95152732486484c8f191b32306456a89590fb2196
|6,0=>0x218b42b6848f075e0b3c0f7810f005dfd3bf467dccf9ddf0b3db67a8ef35de33bbf7770eec99d633a5773cee5ddc83b897706cdf1dbb336f76d0ed85dad3b537698ed15d9f3b386662eca9d91bb1d662cec3dd843b0175f4ebcdd763ae665c0cb65d693acb7588eaf995bbab07552ea8d94e3a957
|7,0=>0x246b4876900f1e5e39b46d68ced185a2d3c537898f115e1f3c377
|8,0=>0x4936
|_,_=>0
def wAt:=mkWire dB 92 112 0xffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 15
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 8 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xc211622061916210a20162904210e1916050e190c2104210a2016290e19160b1c20161902220e19162202220e190e190e19160b0e190c21161916290e19061f0c2102220c210e7e0c22061916210c210a2316210c21042116215c230e19160b0a1b0e190a2004050c210604162104111c201c200a100a1b16120e1916210a10
|1=>0xa19162916210e19061b162104110c217421160b16290e190a221629162116220e1916120c210c21162904110c210c22162916190e190d191622061f16210a231629142216290c210a21162916210a2216290ce9160b14120c210c211621162916190c2204210a2316290a2116291c22161902210e1914120c21061f1621160b
|2=>0x421160b142116210e19162a162904190c210c221622142216291619801b042104cd142217050c220c21160b0c22160b16cd14221422160b14210a1b162905050c2204050e19167214210c210e19162916211c231619
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x11000000000000000000000000000001000000000000000000000000000000000000000000
|5,0=>0x1e11d11c11b11920001811710001520000000000000000001410001310000000000001121010000000000000000000e20000000000d10000000000000b2000000092081000000000071000061051000000041031000021
|5,1=>0x2b12920000000000000002810002622420000000000000002130002011f1
|6,0=>0x9b29929729529329128f28e18c28a28828628428228027e27c27a27827627427227116f26d26b26926726526326125f25d25c15a25915725525320005124f24e14d14b24920004724524324124013e23c23a23823623423223022e22c2
|7,0=>0xaa1a91a81a71a61a51a41a31a21a11a019f19e19d1
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 12
def pmP:Nat→Nat
|0=>0x304818200830040802010100006000297014000870043402140108808340418020b0105008240410020000c180108004000180008000300010000400018000800020000
|1=>0x4587e2c37061d830ba1820ac364252210908a082f3e165f0b0f8585c2c26160f0b008516c202410100802020000d3e0697030f818740c360618030b8183c0c1a060c
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x2000000000000002000000000000000000000
|5,0=>0x8c00000000501b1000000005801450000000000856850c0a8501d0000000000800800000190800000002440000050000002c02412800001c0682000142005
|6,0=>0xe703adb12ada5bdd5162135590ee2f98d1a43e4ba4a4f7e079c38837150076670479000dd937842107f3eb78b2957
|7,0=>0xfb2efca279b4efbf3b9e7
|8,0=>0x23
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 17 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_109 7 roots_109 ops++addP pm 1 dom_102 5 roots_102 ops++addP pm 2 dom_103 6 roots_103 ops++addP pm 3 dzo_75_4 5 roots_75 ops++addP pm 4 dom_110 6 roots_110 ops++addP pm 5 dzo_105_4 5 roots_105 ops++addP pm 6 dom_106 5 roots_106 ops++addP pm 7 dom_108 4 roots_108 ops++addP pm 8 dom_105 5 roots_105 ops++addP pm 9 dom_107 7 roots_107 ops++addP pm 10 dom_75 5 roots_75 ops++addP pm 11 dom_99 5 roots_99 ops++addP pm 12 dzo_107_4 6 roots_107 ops++addP pm 13 dom_45 4 roots_45 ops++addP pm 14 dom_43 4 roots_43 ops++addP pm 15 dom_73 4 roots_73 ops++addP pm 16 dom_47 5 roots_47 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_111 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_zo_75_4_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_zo_105_4_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_108 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_107_4_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_47 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_109 7 s (0,roots_109.map (·&&&dom_109)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_111 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_109 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_111 gM v ys):RunD true dom_111 gM v (ori ys):=h
def Z (s:Nat):=barP dom_111 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 30 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 30 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 85 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 85 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 62 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 62 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 14 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 14 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_111 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_111 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_111 roots_111 goal_111 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_111
theorem lowS_111:Lower true dom_111 roots_111 goal_111 9:=S_111.noCircuit
namespace S_123
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(2,34),(2,66),(3,11),(3,19),(3,35),(3,67),(8,9),(8,24),(8,72),(10,11),(10,26),(10,42),(10,74),(16,17),(16,24),(16,80),(18,19),(18,26),(18,50),(18,82),(32,33),(32,34),(32,96),(40,41),(40,42),(40,56),(40,104),(48,49),(48,50),(48,56),(48,112),(64,65),(64,66),(64,72),(64,80),(64,96)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_123.map (·&&&dom_123)
def gM:=goal_123&&&dom_123
def NN:Nat→Nat
|6=>1
|7=>5
|8=>2
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x7121c
|7,0=>0xc5dc1b484b6f44a61b1452b12
|8,0=>0x7f4936900d
|9,0=>0x62b5b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf000f000f000f000f0000000f0000f0f0f0f0f0f0f0f0f0f0f000f0f0f00f0f00000f0f00000f0f00000f0f0000f000f000f000f000f000f000f000f00f0f0f0f0f0f0f0f0000000000000000f0f0f0f000000000f0f0f0f00000000f0f0f000f0f0f000f0f0f000f0f0f00f0f0f0f0f0f0f0f0f0f00000f0f0000f0f0f0f0f0f0f0f0f000f000f000f00c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a
|_,_=>0
def sP:Nat→Nat
|0=>0x58710658271065487106543710658710a65982710653827105987106543210
|_=>0
def sO:Nat→Nat→Nat
|6,0=>6
|7,0=>0x23771d4835c67
|8,0=>0xc5ea7
|9,0=>0x386
|_,_=>0
def wAt:=mkWire dB 11 124 0xfffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1d9875e1865ce8660976619766097661d865d9
|_=>0
def oO:Nat→Nat→Nat
|6,0=>3
|7,0=>0xb292725232
|8,0=>0xe1d1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0x1ffe65fe7eff5f9fc7e00
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>1
|7,0=>0x62748
|8,0=>0x35
|9,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 9 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_122 8 roots_122 ops++addP pm 1 dom_121 8 roots_121 ops++addP pm 2 dom_115 7 roots_115 ops++addP pm 3 dom_107 7 roots_107 ops++addP pm 4 dom_59 7 roots_59 ops++addP pm 5 dom_91 8 roots_91 ops++addP pm 6 dom_43 4 roots_43 ops++addP pm 7 dom_51 4 roots_51 ops++addP pm 8 dom_99 5 roots_99 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_123 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_99 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_122 8 s (0,roots_122.map (·&&&dom_122)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_123 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_122 h
def symsG:List (List (Nat×Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_123==dom_123)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_123 gM v ys):RunD true dom_123 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_123 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 5 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 2 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_123 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_121_4:=0x30303030303030303030303030303030
def gzo_121_4:=0x30303030303030203030303030202000
def gsh_121_4:=0x3030303030303020303030303020200
theorem lowS_zo_121_4_89:Lower true dzo_121_4 roots_121 gzo_121_4 8:=lower_iso_b (d1:=dom_121) (r1:=roots_121) (T1:=gsh_121_4) [(dom_121,4)] (by decide +kernel) (lower_slice_b (T:=gsh_121_4) [(0x3030303000000000303030300000000,0,32)] (by decide +kernel) lowS_89)
namespace S_125
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(4,36),(5,13),(5,21),(5,37),(5,69),(8,9),(8,24),(8,72),(12,13),(12,28),(12,44),(12,76),(16,17),(16,24),(16,80),(20,21),(20,28),(20,52),(20,84),(32,33),(32,36),(32,96),(40,41),(40,44),(40,56),(40,104),(48,49),(48,52),(48,56),(48,112),(64,65),(64,72),(64,80),(64,96),(68,69),(68,76),(68,84),(68,100)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_125.map (·&&&dom_125)
def gM:=goal_125&&&dom_125
def NN:Nat→Nat
|4=>3
|5=>15
|6=>35
|7=>15
|8=>3
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x66fe047b7c2b8b1
|5,0=>0xe152fc20cbb2d2da716789e407629e6d14f68746610cb34b0f28697246b81d28d155fe08723
|6,0=>0x9487f91bf39003b8a17c806376c16461eff5e48e5d4145b93e57d315629c43a513a6d535d3234b0f28d9a2337c221ae218a6216b6203371ff9e18168171791326c11eb6119170f0610e2e508c3e06703043fa03f1f03010
|7,0=>0xa39449c54c9aa769a8868bb346cf7b4169b39c4b23572221101099d106ab0bf9801a5b0042f
|8,0=>0x8e2268d60a53413
|9,0=>0x7f2e4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcccccccccccccccccc00cc00cc00cc033333333333333333322332233223322cc88cc88cc88cc88cc880000cc8800022222222222222222222222222222222cccccccccccccccc00000000000000000003333000033330000330000003300cccccccccccccccccccc0000cccc00033223322332233223322332233223322cccccccc00000000cccccccc000000033333300333333003333330033333300cccc8888cccc8888cc008800cc0088033333333332233223333333333220000cccc0000cccc0000cccc0000cccc00033003300330033003300330033003300c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c33333333333333332222222222222222
|0,1=>0x44004400440044004400000044000333333333333333333333322333333220000cccc0000cccc000088880000888803300220033002200330022003300224444444444444444440044004400440330033003300330033002200330022000000cccc0000cccc0000cc880000cc8b3333333333333333333222233332222cccccccccccccccccccccc00cccccc033330000333300003322000033220000cccccccccccc8888cccccccccc008800033003300330033002200220022002200cc00cc00cc00cc00cc008800cc008b33322223333222233332222333322220000000000000000cc88cc88cc88cc8b3333322333333223333332233333322
|0,2=>0xcccccc88cccccc8b3333333333333330000332200003322cc00cc00cc00cc00cccccc88cccccc880000033000000330000002200000022cccc00cccccc00cccccc0088cccc00880003322000033220000332200003322
|_,_=>0
def sP:Nat→Nat
|0=>0x31b1d20da04c2c70c204c64b1d748204c2c748920f0471923c100760320f0470c81412c75d22012c70c21410075813142d50c204c2c74890815070c13132c71924412c74033c100718938130718d04c2c70c80402872481411c61410040c2040
|1=>0x84308130b1c33c13202c70c13132c70c204c7cb1c60c80402c758204030b1c32010142c748320f04b1c308504c2c778308130b1c60c131b2c748338204b1d608130b1c33c204c7472432020401d208131d2c70c204070b1d20c13132c7243081
|2=>0x2c70ce08100c2c72433c204c1c320f04c2c70ce08130b1d70cf08130b1d80c13132c794308130b1d80da04c2c740308100b1c30813242c71923c130b1c320f0401c648804b1c60ce04c2c70ce04c50b1e30c204c2c70c204c88b1c30403132c7
|3=>0x1c308130b1c308100c2c718308130b1d20c204c2c748308100b1c60c204030b1c308100c50b1d20cf08130b1c30813142c70c204c28b1c344204c2c740308130b1d824308130b1c60cf04c
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x2940aa005
|5,0=>0x18d8bac57628b12d88ac3f61cb0cd85ac27610b06d82ac0f6
|6,0=>0x54de98f4579f3cdde60f2a6923475e2cf0f7843c05df4ef3776b399dbeed8768bb29d86ebc75abab9d50ca174d3a4dd18e8573f39ddce0e697
|7,0=>0x709f751b28d5468df38f957c73e1a2fef778b83da5ec4f5a8
|8,0=>0x75dfa0fc97
|9,0=>0x1de6
|_,_=>0
def wAt:=mkWire dB 38 126 0x3fffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x808c2d0d4820230b42620c04c2d0808c2d0c88231098830130b4b310ce020130b42022cc523c08b43313ccc22d0804b310ce020130b430230b580f48b4331482c331602d22d3ccc22d602122d089432d2cc522d0cc523c0cc422d18b420d3d2022d0cc432108c4f3108b482408c432d
|1=>0xc2d0c243310cc4b310c24c2d0808c2d08b43310808c2d3c3c22d20bc231482433124c432d083422d0804c2d08b432d08b42310804c2d3c3422d0c04c2d40bd2090cc52090cc480f08c422d08c4b310cc420d08c4f3108b4251
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x888f218628839800000000000000a40c801800
|6,0=>0x140a6980096524800463867049f1800766e0db134262600180ad3564001418004c4909099f200070cd11822c450800122
|7,0=>0x1b8b616a2d0598b21622c0578ae15a2b0558aa1522
|8,0=>0x1c8788f01
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0x4fd4f54113fd3f93593012fd2ef1fd0ff0fd0f90df0dd07f07905905104904104003c03002001801000c008004002000
|1=>0xc14aeda0e5ff
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x431852000000001c2100
|6,0=>0x32801c701348264030d0872c004e18050008244301d1c5085005
|7,0=>0x1e40f2546168235da89b721
|8,0=>0x1455f
|9,0=>0x14
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 12 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_121 8 roots_121 ops++addP pm 1 dom_101 5 roots_101 ops++addP pm 2 dom_109 7 roots_109 ops++addP pm 3 dom_117 7 roots_117 ops++addP pm 4 dom_124 7 roots_124 ops++addP pm 5 dom_61 7 roots_61 ops++addP pm 6 dzo_121_4 8 roots_121 ops++addP pm 7 dom_89 7 roots_89 ops++addP pm 8 dom_116 4 roots_116 ops++addP pm 9 dom_53 4 roots_53 ops++addP pm 10 dom_108 4 roots_108 ops++addP pm 11 dom_45 4 roots_45 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_125 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_101 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_121_4_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_53 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_108 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_45 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_121 8 s (0,roots_121.map (·&&&dom_121)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_125 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_121 h
def symsG:List (List (Nat×Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)],[(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_125==dom_125)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_125 gM v ys):RunD true dom_125 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_125 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 15 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 35 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 35 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 15 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 3 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 0 = true)
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
theorem lowS_126:Lower true dom_126 roots_126 goal_126 9:=lower_slice_b [(0x50505050505050505050505050505050,32,36)] (by decide +kernel) lowS_122
theorem lowS_207:Lower true dom_207 roots_207 goal_207 8:=lower_slice_b [(0xcccc000000000000cccc000000000000cccc000000000000cccc,64,66)] (by decide +kernel) lowS_205
def dzo_217_2:=0xc0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c
def gzo_217_2:=0xc0c0c0c000000000c0c0c08000000000c0c0c0c000000000c080800
def gsh_217_2:=0x3030303000000000303030200000000030303030000000003020200
theorem lowS_zo_217_2_153:Lower true dzo_217_2 roots_217 gzo_217_2 8:=lower_iso_b (d1:=dom_217) (r1:=roots_217) (T1:=gsh_217_2) [(dom_217,2)] (by decide +kernel) (lower_slice_b (T:=gsh_217_2) [(0x3030303000000000000000000000000030303030000000000000000,0,64)] (by decide +kernel) lowS_153)
namespace S_219
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(1,129),(2,66),(3,11),(3,19),(3,67),(3,131),(8,9),(8,24),(8,72),(8,136),(10,11),(10,26),(10,74),(10,138),(16,17),(16,24),(16,80),(16,144),(18,19),(18,26),(18,82),(18,146),(64,65),(64,66),(64,72),(64,80),(128,129),(128,136),(128,144),(130,131),(130,138),(130,146),(130,194),(192,193),(192,194),(192,200),(192,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_219.map (·&&&dom_219)
def gM:=goal_219&&&dom_219
def NN:Nat→Nat
|6=>4
|7=>4
|8=>1
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0xa3ba4857c670d224394f
|7,0=>0x8e378810ab2e6fa1d36e
|8,0=>0x88ca
|9,0=>0x798d4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf000a00000000000f000a00000000000f000a00000000000f000af0a0f0a000000000f0a0f0a000000000f0a0f0a000000000f0a0f0af0f0f00000000000f0f0f00000000000f0f0f00000000000f0f0f00f0f0f0a000000000f0f0f0a000000000f0f0f0a000000000f0f0f0af0f0f0f000000000f0f0f0f0000000000000000000000000000000000000000000000000000000000000000f0f0f0a000000000f0f0f0af0f0a0a000000000f0f0a0a000000000f0f0a0a000000000f0f0a0af0f0000000000000f0f0000000000000f0f0000000000000f0f0000f000f00000000000f000f00000000000f000f00000000000f000f00c0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0ca0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0af0f0f0f0000000000000000000000000f0f0f0f0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x4321079432107843210795321074321b078943210795a20786432106432106543210
|_=>0
def sO:Nat→Nat→Nat
|6,0=>0x28c35c3b007
|7,0=>0x60ea5d139a8
|8,0=>0x377
|9,0=>0x3e6
|_,_=>0
def wAt:=mkWire dB 12 220 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xd1914d14150d53c51914d1315054361f914d187e453461f53451
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x4998c6603
|7,0=>0x91409c4c2
|8,0=>0x141
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 9
def pmP:Nat→Nat
|0=>0xfffd77fd7f3fc7f10c0b01c00
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x4123
|7,0=>0x9768
|8,0=>5
|9,0=>4
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 10 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_217 8 roots_217 ops++addP pm 1 dzo_217_2 8 roots_217 ops++addP pm 2 dom_91 8 roots_91 ops++addP pm 3 dom_153 7 roots_153 ops++addP pm 4 dom_211 7 roots_211 ops++addP pm 5 dom_203 7 roots_203 ops++addP pm 6 dom_218 7 roots_218 ops++addP pm 7 dom_195 4 roots_195 ops++addP pm 8 dom_202 4 roots_202 ops++addP pm 9 dom_210 4 roots_210 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_219 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_217_2_153 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_153 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_195 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_210 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_217 8 s (0,roots_217.map (·&&&dom_217)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_219 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_217 h
def symsG:List (List (Nat×Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_219==dom_219)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_219 gM v ys):RunD true dom_219 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_219 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 4 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 4 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 4 0 = true)
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
theorem lowS_231:Lower true dom_231 roots_231 goal_231 9:=lower_slice_b [(0xaa000000aa000000aa000000aa000000aa000000aa000000aa000000aa,32,33)] (by decide +kernel) lowS_230
def dzo_233_2:=0xc0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c
def gzo_233_2:=0xc0c00000c0c00000c0c00000c0800000c0c00000c0c00000c0c00000800
def gsh_233_2:=0x30300000303000003030000030200000303000003030000030300000200
theorem lowS_zo_233_2_137:Lower true dzo_233_2 roots_233 gzo_233_2 6:=lower_iso_b (d1:=dom_233) (r1:=roots_233) (T1:=gsh_233_2) [(dom_233,2)] (by decide +kernel) (lower_slice_b (T:=gsh_233_2) [(0x30300000000000003030000000000000303000000000000030300000000,0,32),(0x30300000303000000000000000000000303000003030000000000000000,0,64)] (by decide +kernel) lowS_137)
namespace S_235
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(1,129),(2,34),(2,66),(3,11),(3,35),(3,67),(3,131),(8,9),(8,72),(8,136),(10,11),(10,42),(10,74),(10,138),(32,33),(32,34),(32,96),(32,160),(40,41),(40,42),(40,104),(40,168),(64,65),(64,66),(64,72),(64,96),(128,129),(128,136),(128,160),(130,131),(130,138),(130,162),(130,194),(192,193),(192,194),(192,200),(192,224)]
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
|7,0=>0x8c63343456
|8,0=>0xfffda
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x40400000404000004040000040400000404000004040000040400000404c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0cf0f0000000000000f0f0000000000000f0f0000000000000f0f00000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000f00e0e00000e0e00000e0e00000e0e00000e0e00000e0e00000e0e00000e0ea0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0af0f00000f0f000000000000000000000f0f00000f0f0000000000000000f0f00000f0f00000f0f00000f0f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x2cc88b1722c688
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
|0=>0xcbc9
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
addP pm 0 dom_227 7 roots_227 ops++addP pm 1 dom_171 7 roots_171 ops++addP pm 2 dom_107 7 roots_107 ops++addP pm 3 dom_203 7 roots_203 ops++addP pm 4 dom_234 6 roots_234 ops++addP pm 5 dom_233 6 roots_233 ops++addP pm 6 dzo_233_2 6 roots_233 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_235 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_233_2_137 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_227 7 s (0,roots_227.map (·&&&dom_227)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_235 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_227 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff00ff00ff00ff00ff00,120)]]
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
theorem lowS_238:Lower true dom_238 roots_238 goal_238 9:=lower_slice_b [(0x550000005500000055000000550000005500000055000000550000005500,64,72)] (by decide +kernel) lowS_230
theorem lowS_249:Lower true dom_249 roots_249 goal_249 9:=lower_slice_b [(0x303030300000000030303030000000003030303000000000303030300000000,1,33)] (by decide +kernel) lowS_217
theorem lowS_250:Lower true dom_250 roots_250 goal_250 9:=lower_slice_b [(0x505050505050505050505050505050500000000000000000000000000000000,8,136)] (by decide +kernel) lowS_122
def isoMvS_119:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_119:Lower true dom_119 roots_119 goal_119 9:=lower_iso_b isoMvS_119 (by decide +kernel) lowS_111
def isoMvS_175:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_175:Lower true dom_175 roots_175 goal_175 9:=lower_iso_b isoMvS_175 (by decide +kernel) lowS_111
def isoMvS_183:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_183:Lower true dom_183 roots_183 goal_183 9:=lower_iso_b isoMvS_183 (by decide +kernel) lowS_111
def isoMvS_187:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_187:Lower true dom_187 roots_187 goal_187 10:=lower_iso_b isoMvS_187 (by decide +kernel) lowS_125
def isoMvS_190:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_190:Lower true dom_190 roots_190 goal_190 9:=lower_iso_b isoMvS_190 (by decide +kernel) lowS_126
def isoMvS_215:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_215:Lower true dom_215 roots_215 goal_215 8:=lower_iso_b isoMvS_215 (by decide +kernel) lowS_207
def isoMvS_221:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_221:Lower true dom_221 roots_221 goal_221 10:=lower_iso_b isoMvS_221 (by decide +kernel) lowS_219
def isoMvS_222:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_222:Lower true dom_222 roots_222 goal_222 8:=lower_iso_b isoMvS_222 (by decide +kernel) lowS_207
def isoMvS_237:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_237:Lower true dom_237 roots_237 goal_237 9:=lower_iso_b isoMvS_237 (by decide +kernel) lowS_235
def isoMvS_243:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_243:Lower true dom_243 roots_243 goal_243 9:=lower_iso_b isoMvS_243 (by decide +kernel) lowS_235
def isoMvS_246:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_246:Lower true dom_246 roots_246 goal_246 9:=lower_iso_b isoMvS_246 (by decide +kernel) lowS_238
def isoMvS_252:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_252:Lower true dom_252 roots_252 goal_252 9:=lower_iso_b isoMvS_252 (by decide +kernel) lowS_250
theorem lowS_127:Lower true dom_127 roots_127 goal_127 11:=lower_slice_b [(0xcccccccccccccccccccccccccccccccc,32,34)] (by decide +kernel) lowS_125
theorem lowS_223:Lower true dom_223 roots_223 goal_223 11:=lower_slice_b [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,64,66)] (by decide +kernel) lowS_221
namespace S_239
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(1,129),(2,34),(2,66),(3,11),(3,35),(3,67),(3,131),(4,36),(4,132),(5,13),(5,37),(5,69),(5,133),(6,38),(6,70),(6,134),(7,15),(7,39),(7,71),(7,135),(8,9),(8,72),(8,136),(10,11),(10,42),(10,74),(10,138),(12,13),(12,44),(12,76),(12,140),(14,15),(14,46),(14,78),(14,142),(32,33),(32,34),(32,36),(32,96),(32,160),(40,41),(40,42),(40,44),(40,104),(40,168),(64,65),(64,66),(64,72),(64,96),(68,69),(68,70),(68,76),(68,100),(68,196),(128,129),(128,132),(128,136),(128,160),(130,131),(130,134),(130,138),(130,162),(130,194),(192,193),(192,194),(192,196),(192,200),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffffffffffffffff
def xsM:=roots_239.map (·&&&dom_239)
def gM:=goal_239&&&dom_239
def NN:Nat→Nat
|9=>1
|10=>1
|_=>0
def HT:Nat→Nat→Nat
|9,0=>0xf119b
|10,0=>0x3ce8d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00ffff0000ff000000ffff0000ff000000ffff0000ff000000ffff0000ff00ffff000000000000ffff000000000000ffff000000000000ffff00000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000ccccaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaaffff0000ffff00000000000000000000ffff0000ffff0000000000000000ffff0000ffff0000ffff0000ffff00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x2f8d11ac688
|_=>0
def sO:Nat→Nat→Nat
|9,0=>7
|10,0=>0x77
|_,_=>0
def wAt:=mkWire dB 8 240 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 8
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xbd
|_=>0
def oO:Nat→Nat→Nat
|9,0=>1
|_,_=>0
def PO:=mkPO wAt oP oO 8 3 7 5
def pmP:Nat→Nat
|0=>0xfc0
|_=>0
def pmB:Nat→Nat→Nat
|9,0=>1
|10,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 1 (j%128);fld (pmP (k/32)) 6 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_238 9 roots_238 ops++addP pm 1 dom_175 9 roots_175 ops++addP pm 2 dom_237 9 roots_237 ops++addP pm 3 dom_235 9 roots_235 ops++addP pm 4 dom_111 9 roots_111 ops++addP pm 5 dom_231 9 roots_231 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_239 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_238 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_175 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_237 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_231 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_238 9 s (0,roots_238.map (·&&&dom_238)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_239 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_238 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_239==dom_239)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_239 gM v ys):RunD true dom_239 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_239 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s:Nat) (hs:s≤10):∀ i<NN s,bar dom_239 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 5 6=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤10) (h:RunD true dom_239 gM s xsM):False:=by
  have hmin:6≤s:=by have hl:=run_len h;change 7≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_239 roots_239 goal_239 11:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_239
theorem lowS_239:Lower true dom_239 roots_239 goal_239 11:=S_239.noCircuit
def dzo_249_2:=0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
def gzo_249_2:=0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c080c0c0c0c0c0c0c0c0c0c0c0c0c080800
def gsh_249_2:=0x303030303030303030303030303030203030303030303030303030303020200
theorem lowS_zo_249_2_153:Lower true dzo_249_2 roots_249 gzo_249_2 9:=lower_iso_b (d1:=dom_249) (r1:=roots_249) (T1:=gsh_249_2) [(dom_249,2)] (by decide +kernel) (lower_slice_b (T:=gsh_249_2) [(0x303030300000000030303030000000003030303000000000303030300000000,0,32),(0x303030303030303000000000000000003030303030303030000000000000000,0,64)] (by decide +kernel) lowS_153)
namespace S_251
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(1,129),(2,34),(2,66),(3,11),(3,19),(3,35),(3,67),(3,131),(8,9),(8,24),(8,72),(8,136),(10,11),(10,26),(10,42),(10,74),(10,138),(16,17),(16,24),(16,80),(16,144),(18,19),(18,26),(18,50),(18,82),(18,146),(32,33),(32,34),(32,96),(32,160),(40,41),(40,42),(40,56),(40,104),(40,168),(48,49),(48,50),(48,56),(48,112),(48,176),(64,65),(64,66),(64,72),(64,80),(64,96),(128,129),(128,136),(128,144),(128,160),(130,131),(130,138),(130,146),(130,162),(130,194),(192,193),(192,194),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffffffffffffff
def xsM:=roots_251.map (·&&&dom_251)
def gM:=goal_251&&&dom_251
def NN:Nat→Nat
|8=>1
|9=>6
|10=>4
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|8,0=>0xe31de
|9,0=>0xe6665b98df7c46060ab351f5432b89
|10,0=>0xf117277ec8502c641175
|11,0=>0xff75e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0000f0a00000f0a00000f0a00000f0a00000f0a00000f0a00000f0a00000f0af0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a404040404040404040404040404040404040404040404040404040404040404f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0af0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f00f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0af0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0ac0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0cf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x68927106897a10689d7106489271065892710654927106589d71068927c10648392106b89271065897a106543210
|_=>0
def sO:Nat→Nat→Nat
|8,0=>7
|9,0=>0x17c2783f05e07c078
|10,0=>0x9cf1ddfc378
|11,0=>0x557
|_,_=>0
def wAt:=mkWire dB 14 252 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x9f2761d8962587625274e39765d875258762527e5d8961d
|_=>0
def oO:Nat→Nat→Nat
|8,0=>3
|9,0=>0x1a4b2491c8a432
|10,0=>0x90c4602f1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 9
def pmP:Nat→Nat
|0=>0xaff7ff6ff4ff3ff1ff0ff0ef000
|_=>0
def pmB:Nat→Nat→Nat
|8,0=>2
|9,0=>0x425671
|10,0=>0x1283
|11,0=>2
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 12 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_219 10 roots_219 ops++addP pm 1 dom_187 10 roots_187 ops++addP pm 2 dom_123 10 roots_123 ops++addP pm 3 dom_249 9 roots_249 ops++addP pm 4 dzo_249_2 9 roots_249 ops++addP pm 5 dom_243 9 roots_243 ops++addP pm 6 dom_250 9 roots_250 ops++addP pm 7 dom_235 9 roots_235 ops++addP pm 8 dom_227 7 roots_227 ops++addP pm 9 dom_234 6 roots_234 ops++addP pm 10 dom_242 6 roots_242 ops++addP pm 11 dom_226 5 roots_226 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_251 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_zo_249_2_153 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_226 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_219 10 s (0,roots_219.map (·&&&dom_219)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_251 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_219 h
def symsG:List (List (Nat×Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_251==dom_251)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_251 gM v ys):RunD true dom_251 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_251 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 6 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 6 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 4 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 4 0 = true)
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
def dzo_156_2:=0x4444444400000000000000000000000044444444
def gzo_156_2:=0x4444444000000000000000000000000044000000
def gsh_156_2:=0x1111111000000000000000000000000011000000
theorem lowS_zo_156_2_156:Lower true dzo_156_2 roots_156 gzo_156_2 5:=lower_iso_b (d1:=dom_156) (r1:=roots_156) (T1:=gsh_156_2) [(dom_156,2)] (by decide +kernel) (lower_slice_b (T:=gsh_156_2) [] (by decide +kernel) lowS_156)
def dzo_90_4:=0x505050500000000050505050
def gzo_90_4:=0x505050400000000050000000
def gsh_90_4:=0x50505040000000005000000
theorem lowS_zo_90_4_90:Lower true dzo_90_4 roots_90 gzo_90_4 5:=lower_iso_b (d1:=dom_90) (r1:=roots_90) (T1:=gsh_90_4) [(dom_90,4)] (by decide +kernel) (lower_slice_b (T:=gsh_90_4) [] (by decide +kernel) lowS_90)
def dzo_218_4:=0x50505050000000005050505000000000505050500000000050505050
def gzo_218_4:=0x50505050000000005050505000000000505050400000000050000000
def gsh_218_4:=0x5050505000000000505050500000000050505040000000005000000
theorem lowS_zo_218_4_90:Lower true dzo_218_4 roots_218 gzo_218_4 6:=lower_iso_b (d1:=dom_218) (r1:=roots_218) (T1:=gsh_218_4) [(dom_218,4)] (by decide +kernel) (lower_slice_b (T:=gsh_218_4) [(0x5050505000000000505050500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_90)
def dzo_220_2:=0x44444444000000004444444400000000444444440000000044444444
def gzo_220_2:=0x44444444000000004444444000000000444444440000000044000000
def gsh_220_2:=0x11111111000000001111111000000000111111110000000011000000
theorem lowS_zo_220_2_156:Lower true dzo_220_2 roots_220 gzo_220_2 6:=lower_iso_b (d1:=dom_220) (r1:=roots_220) (T1:=gsh_220_2) [(dom_220,2)] (by decide +kernel) (lower_slice_b (T:=gsh_220_2) [(0x11111111000000000000000000000000111111110000000000000000,0,64)] (by decide +kernel) lowS_156)
def dzo_252_2:=0x4444444444444444444444444444444444444444444444444444444444444444
def gzo_252_2:=0x4444444444444444444444444444444044444444444444444444444444000000
def gsh_252_2:=0x1111111111111111111111111111111011111111111111111111111111000000
theorem lowS_zo_252_2_156:Lower true dzo_252_2 roots_252 gzo_252_2 7:=lower_iso_b (d1:=dom_252) (r1:=roots_252) (T1:=gsh_252_2) [(dom_252,2)] (by decide +kernel) (lower_slice_b (T:=gsh_252_2) [(0x1111111100000000111111110000000011111111000000001111111100000000,0,32),(0x1111111111111111000000000000000011111111111111110000000000000000,0,64)] (by decide +kernel) lowS_156)
def dzo_216_2:=0x4040404000000000404040400000000040404040000000004040404
def gzo_216_2:=0x4040404000000000404040000000000040404040000000004000000
def gsh_216_2:=0x1010101000000000101010000000000010101010000000001000000
theorem lowS_zo_216_2_152:Lower true dzo_216_2 roots_216 gzo_216_2 5:=lower_iso_b (d1:=dom_216) (r1:=roots_216) (T1:=gsh_216_2) [(dom_216,2)] (by decide +kernel) (lower_slice_b (T:=gsh_216_2) [(0x1010101000000000000000000000000010101010000000000000000,0,64)] (by decide +kernel) lowS_152)
def dzo_248_4:=0x1010101010101010101010101010101010101010101010101010101010101010
def gzo_248_4:=0x1010101010101010101010101010101010101010101010001010101010000000
def gsh_248_4:=0x101010101010101010101010101010101010101010101000101010101000000
theorem lowS_zo_248_4_88:Lower true dzo_248_4 roots_248 gzo_248_4 6:=lower_iso_b (d1:=dom_248) (r1:=roots_248) (T1:=gsh_248_4) [(dom_248,4)] (by decide +kernel) (lower_slice_b (T:=gsh_248_4) [(0x101010100000000010101010000000001010101000000000101010100000000,0,32),(0x101010101010101010101010101010100000000000000000000000000000000,0,128)] (by decide +kernel) lowS_88)
def dzo_250_4:=0x5050505050505050505050505050505050505050505050505050505050505050
def gzo_250_4:=0x5050505050505050505050505050505050505050505050405050505050000000
def gsh_250_4:=0x505050505050505050505050505050505050505050505040505050505000000
theorem lowS_zo_250_4_90:Lower true dzo_250_4 roots_250 gzo_250_4 7:=lower_iso_b (d1:=dom_250) (r1:=roots_250) (T1:=gsh_250_4) [(dom_250,4)] (by decide +kernel) (lower_slice_b (T:=gsh_250_4) [(0x505050500000000050505050000000005050505000000000505050500000000,0,32),(0x505050505050505050505050505050500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_90)
def dzo_248_2:=0x404040404040404040404040404040404040404040404040404040404040404
def gzo_248_2:=0x404040404040404040404040404040004040404040404040404040404000000
def gsh_248_2:=0x101010101010101010101010101010001010101010101010101010101000000
theorem lowS_zo_248_2_152:Lower true dzo_248_2 roots_248 gzo_248_2 6:=lower_iso_b (d1:=dom_248) (r1:=roots_248) (T1:=gsh_248_2) [(dom_248,2)] (by decide +kernel) (lower_slice_b (T:=gsh_248_2) [(0x101010100000000010101010000000001010101000000000101010100000000,0,32),(0x101010101010101000000000000000001010101010101010000000000000000,0,64)] (by decide +kernel) lowS_152)
def dzo_216_4:=0x10101010000000001010101000000000101010100000000010101010
def gzo_216_4:=0x10101010000000001010101000000000101010000000000010000000
def gsh_216_4:=0x1010101000000000101010100000000010101000000000001000000
theorem lowS_zo_216_4_88:Lower true dzo_216_4 roots_216 gzo_216_4 5:=lower_iso_b (d1:=dom_216) (r1:=roots_216) (T1:=gsh_216_4) [(dom_216,4)] (by decide +kernel) (lower_slice_b (T:=gsh_216_4) [(0x1010101000000000101010100000000000000000000000000000000,0,128)] (by decide +kernel) lowS_88)
namespace S_254
def pG:List (Nat×Nat):=[(2,34),(2,66),(4,36),(4,132),(6,38),(6,70),(6,134),(8,24),(8,72),(8,136),(10,26),(10,42),(10,74),(10,138),(12,28),(12,44),(12,76),(12,140),(14,30),(14,46),(14,78),(14,142),(16,24),(16,80),(16,144),(18,26),(18,50),(18,82),(18,146),(20,28),(20,52),(20,84),(20,148),(22,30),(22,54),(22,86),(22,150),(32,34),(32,36),(32,96),(32,160),(40,42),(40,44),(40,56),(40,104),(40,168),(48,50),(48,52),(48,56),(48,112),(48,176),(64,66),(64,72),(64,80),(64,96),(68,70),(68,76),(68,84),(68,100),(68,196),(128,132),(128,136),(128,144),(128,160),(130,134),(130,138),(130,146),(130,162),(130,194),(192,194),(192,196),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffffffffffff
def xsM:=roots_254.map (·&&&dom_254)
def gM:=goal_254&&&dom_254
def NN:Nat→Nat
|4=>6
|5=>27
|6=>130
|7=>359
|8=>262
|9=>75
|10=>12
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x7b46a6bd8a191b517a0b134a2035db
|5,0=>0xdb59578a5e74b1c7445470a985fc415137642da140cde3be8f359ce339dd319ba31287252e420e82185a517211114fe10eda104560a743099cb07634026c500f1b00a44
|6,0=>0xa50249fb4f9962298ec0955fd949bb944108924b83c5580a377df347cf407bec779a9b77c8274d0e70a986ec016dc9b6d6086951968c6665366641236332162bb861d995fe8a58f6456ae5557e551b504dd674ca054a198475834608b45e3045c7145201451f243a8041f0541e853fe263f2163ed3a3dce63a8863a0423836537b1037705374b136bf5359ce358783574b3502d32b1b316ba300962fa3e2dbeb2d6f92d1902cc6f2c7232c2b12b1092a32429bc628d4b27ff527f1d27102257d6253e023c46239f52289921b042119920e8220e341f9d71eede1ee8c1e2301d2d71bec41a26219f2d188811812c18123176ea1743917280170a41662215a0c1500d14c121473313e2913dd51398e124fb117081136210a0e103510f3b60e5ec0b3910a5b80879f073fb065790628c05e5605623054cc042500278401ab500721
|6,1=>0xc294ec0f55
|7,0=>0x1b6071aa621a9d21a35a19d9f19aef1999418e3c18a661838c1831e1812317b7617b061774316ec416e2516bb716622165871617f15ebd15ccf159ea1594d158ed154951435b13c9c13b3b12fb112ace128e81280d127d512684124421216311e3111a62119ea119691194610dff10d8510d6e10557103cd0fdbf0f2560ed4a0eb8f0e99a0e5480dcd70dba40d2eb0cf920cf110cb130ca570c63d0c2e30c2100becd0bb930bb450b87c0b7050b4360b2cc0adf90ab5a0aa2b0a9c70a81e0a8180a6920a1e10a1bc09e20098840986a0938509332092bf08c0608b560791a0771f0750b0710006f6806cbb0691a067a306706065bc065bb06517063be05ac10592005712056fb05573055150512c050b604db304ab9048dd045bc03444034240337a0313202fa902e3702bd102ac7027840226a01628015f10133c00ec800702
|7,1=>0x529a75192b5159f50b68504ef4fd454fc7f4fbf74fa374f3694ee5e4e9cd4e67a4d12a4bc9d4a2bd4a1e749744496e34911545ba24532d44d8c44bcb44b95444a543a49439ee437e641ab0419be40b70408633ff363e3913dce63dcbe3ce783bea33b1f2395ff38e69385bd3809e37fd637f2f37ddb378a536fba35da83569833f0933e98339d3337a73355f32ebf329913221331d0730bda307393009c2fe732f59b2f4362eefc2eda22e0f22e0932d8aa2d27c2cc6f2c0882bee62bbbc2b75a2aa612a77f2a30d2a0d92a015298222916528e8828c8e2817827e9927c5627a4b27908275f12746c271a526cb0265442586f256832526724ec024db5249a4241f523d1e238322366b235522336e22712222a621b4121a5121a4a21a2c210a12096b209252052c204912017e1fb761f95c1f7891f07b1ef6b1eede1e9311cd98
|7,2=>0xee8d3e99b8e154ddf5abdcda0d92a6d378ecddf7ccd25c14a6bd7e8b8718b398bb2a56af0fcaa465a8996a890da43e7a3ccda36cca05b59ebd79e93c9b67f9add39a56f906af8ca0888a69878fb878a0867488473f8360b832eb81dc48159f7f2c67ecfb7e8947d48a7cfc87caf27c4ce7a1527a03074cd974a5a7409572e76722c06ec016e6236d1656baca6b9466aea96ae636a6da6a46869ffc698f86901368c666864666ff865ec1656156528d6336462bb8627be6248461cb4614606122860eff60c14608f2600605fdd75e4c95dce45d8565cfe45b91e5b63e5adc25a46859a5059a3059435582ba57f5e57f3557c05577f5570da557e55528f54f33543e9
|8,0=>0x2faf42eff62eda22e4ca2d9192b2d82ad1d2a5db2a3d829fcb29d60297932932e28e88286e02817827908278562730e2730b26ef426bdd2698f256b9241f523f1223d3e23a2c21b79217d621656215ae20d521fbf41fba21fb7d1faa61ef341eb601eb131e9311e8641e2931dd671dbd21d78e1cfd31c83f1c0b01bedf1bec41bd981b62a1aa41198cd195f11947018df51893c1809f16455163e81617f15c3d14c151474e1439c13bd81396612e40128e811d6511bf0119db10944107ce103c50f9ad0f36e0f1e80e4eb0e2ad0e06a0df530df230daba0d9bf0d50d0cfc90ccd60c5f70c5d60c5330bf350b87c0ae270aad80aab30a4f40a17609bf409b0d094bb094b20932808ac10870507a5105d2c05b970585105515053f404fc4045810437c0418203a8c0397c0344402eb8027af01dde01945014c4011c800f7500923
|8,1=>0xaee07abb05a7b48a6ba2a599ea43e79fabc9d7999a56f9728b9654095c2593e9892d2a916908e2038d6f48a9e08a99388a6988080878fb8626f8511c83b05819b780d1e7b442786d677a12758ef7544473a75735b270b15708a76de256c5e36c32e6a6d06925768646681836792a66fa166aef654786437362c2462b4661cfb60eff60eb360c1460a465fc145ea6c5d9595c4fb5c00f5bdf55b0265a842598b959125577f5569a856932557e55505c54541538695341552cf652a985252a51eec50be04fbf74c28a4b20f49c2d499a9490ed4803d47e5747cad46f9946c594670a45ebf4365442b80410de40c5b4087a3ffd33e88b3e0c73dcbe3dbf03c66f3bf6b3b58d3ae8f3a62539fd539d85389b3387a837a113798d36dbb36d9036c9835fdb3567e34b333476c342b733be033693335a7333bb32f1832d373242e31cfd
|8,2=>0xca924bf4f5b90e7b6ea5b1417af816
|9,0=>0xff520f40f1f1d63dbf6fd627ba9ef89eac99e6ae8ebc98c6ff83af77cf4c7aa7c748586c32e6b1ec69dd56902168fd267abf60eff5cccc5b1cb56d8056d695644f54eb64f2014c92e4b93a4af7a489e8414ff40d044018c3dc743d4b33bdc0398eb38ad0389b33472b324d730cb730a15308932f3262d42d2caf22af2e2aa3a29b0223e1b20f5720540204d3204b11c3f21a89b1939e172e914c9313ad412cc211bb8109440f44b0d4d5084c9067610551504c90047550306902814
|10,0=>0xc5d3eba90fb151895f0e6f64d59fec4ae32420a235d9a2224d1a4340a6d4
|11,0=>0xba90f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaa00aa00000000000000000000000000aa00aaaaaaaaaa000000015555555555555401555555555555540155555555555554015554000155540002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa802a802a802a802a802a802a802a800000000000550055000000000055005500000000000000005555555500000000aaaaaaaaaaaa8888aaaaaaaaaaaa8888aaaaaaaaaaaa8888888888888888888955555555555555555555555555540001555555555555555555540001555400028282828282828282828282828282828282828282828282828282828282828285555555555555555555555550000000055555555555555555555555500000000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000aaaa0000aaaa0000aaaa00015555555555555401555555555555540155555555555554015401540154015402aaaaaaaaaaaa8282aaaaaaaaaaaa8282aaaaaaaaaaaa82828282828282828285555555555555555555555555555555555555555000000005555555500000000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa00000000000001540154000000000000000000000000015401555401540154015402aaaaaaaaaa82aa82aaaaaaaaaa82aa82aaaaaaaaaa82aa828282828282828284444444444444444444444444444444444444444444444444444444444444444
|0,1=>0xaaaaaaaaaa00aa00aaaaaaaaaa00aa00aaaaaaaaaa00aa0000000000000000000000000000000000000000000000000000000000000000015555555400000002aaaaaaaaaa22aa22aaaaaaaaaa22aa22aaaaaaaaaa22aa222222222222222225555555555555555555555555555555555550055555500005555005555550000000000000000aaaa0000000000000000000000000000aaaaaaaa0000aaaa00015555555555555555555555555555555555555555555555555555555400000002aaaaaaaaaaaaaaaaaaa80002aaa80002aaaaaaaaaaaaaaaaaaa80002aaa80005555555555550000555555555555000055555555555500005555000055550000aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa015555555555540001555555555554000155555555555400000000000000000002aaaaaaaaaaa80002aaaaaaaaaaa80002aaaaaaaaaaa80002aaaaaaaaaaa80005555555555555555555555555555555555555555555555550000000000000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa000000015555555555555555555555555555555400000000000000000000000000000002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa80002aaa80005555555555555555000000000000000055555555555555550000000000000000
|0,2=>0xaaaaaaaaaa00aa00aaaaaaaaaa00aa00aaaaaaaaaa00aa00aa00aa00aa00aa000000000000000000000155540000000000000001555400000001555555540000000000000002aaa8000000000002aaa8000000000002aaaaaaa80002aaa80005555555555555555555555555555555555005555550055005500555555005500aa00aaaaaa00aa00aa00aaaaaa00aa00aa00aaaaaa00aa00000000000000000000000000000000000000000000000001555555555555555555555555540154000000000000000002aaaaaaaaaaaaaaa80000000000000002aaaaaaaaa802a8055550000000055555555000000005555555500000000555555550055000055000a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a000000000a0a0a0a000000015555555554015401555555555401540155555555540154015555555554015400000000000002aaa8000000000002aaa80000000000000002aaaaaaa800000005555555555555555555555555555555500000000000000005555555500000000aaaaaaaaaaaaaaaaaa00aa00aa00aa00aaaaaaaaaaaaaaaaaa00aa00aa00aa015555555555555555555555555555555555555555555400015554000155540002aaaaaaaa22222222aaaaaaaa22222222aaaaaaaa222222222222222222222220000555500005555000055550000555500005555000055550000550000005500
|0,3=>0xaaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaaaaaaaaaa00aaaaaaaaaaaaaa015555555555555555555555555555555555555555555400015555555555540002a802aaaaa802a802a802aaaaa802a802a802aaaaa802a802a802a802a802a805555005555550000555500555555000055550055555500005555005555550000aaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaaaaaaaaaaaaaa00015555555555555555555555555555555400000000000000015555555555540000000000000002aaa80000000000000000000000000002aaaaaaaaaaaaaaa800055555555555555550000000000000000555555555555555555555555000000002222222222222222222222222222222222222222222222222222222222220000444444444444444444444444000000004444444444444444444444440000000088888888888888888888888888008800888888888888888888888888880088005050505050505050505050505050505050505050505050505050505050005000a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a00000154015401540154015401540154015401540154015401540154015401540002aaaaaaa800000002aaaaaaa800000002aaaaaaa8000000000000000000000005555555555555555555555555500550055555555555555555500550055005500
|0,4=>0xaaaaaaaaaaaaaaaaaaaaaaaaaa00aa00aaaaaaaaaaaaaaaaaaaaaaaaaa00aa00000000000154015400000000015401540000000001540154015400000154000002a802a802a802a802a802a802a802a802a802a802a802a80000000000000005500550055555555550055005555555555005500555555555555555500000000aaaaaaaaaaaaaaaaaaaa00aaaaaa0000aaaaaaaaaaaaaaaaaaaa00aaaaaa000044444444004400444444444400440044444444440044004444444444000000002828282800280028282828280028002828282828002800282828282800000000055005500550055005500050055000500550055005500550055000500550000222222222222222222222222222222222222222222222222222222220000000001540154015401540154015401540154015401540154015401540000015400000002a8000002aaa80002a8000002aaa80002a8000002aaa80002a8000002a800000000000550055000000000055005500000000005500550000000000000000aaaaaaaa0000aaaaaaaaaaaa0000aaaaaaaaaaaa0000aaaaaaaaaaaa000000015554000155555555555400015555555555540001555555555554000155540002a802a802a802a802a802a802a802a802a802aaaaa802a802a802aaaaa802a800000000000000000000000000000000000005555000000000000555500000000
|0,5=>0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aa00aa0000000000444444440000444444444444000044444444444400004444444444440000000088888888888888888888888888880000888888888888888888888888888800000000000555555550000000055555555000000005555555555555555000000000000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000000000000001555555555555555400000001540154015555555555555554015401555401540088888888000088888888888800008888888888880000888888888888000088000550055005500000055005500550000005500550055000000550000005500000a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a00000000015401540154015401540154015401540154015401540154015401540000000000000002aaaaaaa800000002aaaaaaa800000002aaaaaaa800000002a802a805505550555055505550555055505550555055505550055005505550555005500222222222222222202020202020202022222222222222222020202020000000014141414141414141414141414141414141414141414000014141414141400008888888888888888000000000000000088888888888888888888888888880005555555555555555555555555555555555555555555555555500550055005500
|0,6=>0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa000000000000015401540000000001540154000000000154015555555554000000000002aaa80002aaa80002aaa80002aaa80002a8000002aaa80002a8000002a800000000000000000000000005555555500005555000055550000000000000000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa00aaaa0000015555555555555555555555540000000155555555555555555554000000000002aaaaaaa80002aaaaaaaaaaa80002aaaaaaaaaaa80002aaaaaaaaaaa80002a8000005555000000000000555500000000000055550000000000005500000000000a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0aaaaaaaaa0a0a0a0aaaaa0000000000015554000000000001555400000000000155540000000155555554000002a802a802a802a802aaaaa802a802a802a802a802a802a802aaaaa802a80005555000000005555555500000000555555550000000055555555555500000000aaaaaaaaa0a0a0a0aaaaaaaaa0a0a0a0aaaaaaaaa0a0a0a0a0a0a0a0a0a0a0a15555555401540155555555540154015555555554015401555555555400000002a802aaaaa802a802a802aaaaa802a802a802aaaaa802a802a802aaaaa802a804444555544444444444455554444444444445555444444444444444444444444
|0,7=>0xaaaa0000000000000000000000000000aaaa000000015445544554455445544554455401540154455445544554455445544554015402aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa88aa88aa88aa88aa88aa88aa802a805555555555555555555555555555555555555555555555555555555555005500aa00aa00aaaaaaaaaa00aa00aaaaaaaaaa00aa00aaaaaaaa0000000000000000000000000000000000000000000000000000000000000001555555555401540000000000000000000000000000000002aaaaaaaaaaaaaaaaaaaaaaaaaaa80000000555500005555000055550000555500005555000055550000555500000000888888888888888888888888aaaaaaaa888888888888888888888888aa00aa01555555555555555555555554000000015554000155540001555400000000000000000002aaaaaaa800000002aaaaaaa800000002aaaaaaa80002aaaaaaa8000000000005555555500550055555555550000000055005500005500555500550000aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aaaaaa00aa000014141414141414141414141414141414141414141400140014141414140014002828282828282828282828282828282828280808282808082828080828280005500550000000000550055000000000055005500000000005500555500000000
|0,8=>0xaaaaaaaaaaaaaaaa0a0a0a0a0a0a0a0aaaaaaaaaaaaaaaaa0a0a0a0a0000000000000000000000000000000000000000000000000000000155555555555400000002aaa8000000000002aaa8000000000002aaa8000000000002aaa800000005555550055555500555555555555550055555500555555005555555555555500aaaa0000aaaa0000aaaa00aaaaaa0000aaaa0000aaaa0000aaaa00aaaaaa00000000000000000000000000000000000000000000000000000001555400000002aaaaaaaaaaaaaaa80000000000000002aaaaaaaaaaaaaaa80002aaa800000000000000055555555000000005555555500000000550055000000000055005500000000000000000000aa00aa00000000000000000000000000aa00aa0000000044444444444444444444444444444444444444444444444444444444440044000002aaa8000000000002aaa8000000000002aaa8000000000000000000000005050555550505050505055555050505050505555505050505050505050505050aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa2222222222220000222222222222000044444444444400004444444444440000444444444444000044444444444400002828282828282828282828282828282808080808080800000808080808080000000000055555555000000005555555500000000555555550000000000000000
|0,9=>0xaaaaaaaa00aa00aaaaaaaaaa00aa00aaaaaaaaaa00aa00aaaaaaaaaa00aa00015555555400000001555555555555555555555554000000015555555554015402222222222222222222222222aaaaaaaa200220022002200220022002a802a805555555555005500555555555500550055555555550055000000000055005500aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaa00000000000154015401540154015401540154015401540154015401540155555555540154000000000000000002aaaaaaaaaaa800000000000000000002aaaaaaaaaaa800005050505050505050505050505050505000000000000000005050505050500000000000000000000000000000000000000aa00aa0000000000aa00aa00000001555400015554000155540001555400015554015555540001555401555554000000000000000000000000000000000002aaaaaaaaaaa80002aaaaaaaaaaa80005500550055005500555555555500550055005500550055005555555555005500aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00015555555555555401555555555555540155555555555554015555540155555402aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa802a802aaaaaaaaa802a805555555500000000550055000000000055555555000000005500550000000000
|0,10=>0xaaaaaaaa000000000000000000000000aaaaaaaa000000015555555555555554000000015555555555555555555400000000000155540002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa22aa22aaaaaaaaaa22aa25555555555555555555555555555555500000000000000005555555555005500aaaaaaaa00000000aaaaaaaa0000000000000000000000000000aaaa000000000000000000000000000000000000000155555555555555555554000155540002aaaaaaaaa802a802aaaaaaaaa802a802a802a802a802a802a802aaaaa802a805555555500000000555555550000000055555555000000005555000055550000aaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaaaaaaaaaaaa00aa004444444444444444444444444444404044444444444444444444444444444042aaaaaaaaaaaaaaaaaaaaaaaaaaa80002aaaaaaaaaaaaaaaaaaaaaaaaaaa800055555555555555555555000055550000555555555555555555555555555500000a0a0a0a0a000a000a0a0a0a0a000a000a0a0a0a0a000a000a0a0a0a0a000a00000000000000000155555555555555540000000000000001555555555554000002a802a80000000002a802a80000000002a802a80000000002a802a800000000055005500000000005500550000000000550055000000000000000000000000
|0,11=>0xaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a0aaaaa0000aaaa0a0aaaaa00000000000000000001555555555401540000000000000000015555555554015402aaaaaaaaaaaaaaaaaaaaaaaaaaaa8282aaaaaaaaaaaaaaaaaaaaaaaaaaaa82855555555555555555555505055555050555555555555555555555050555550500000000000000000000000000000000000000000aaaaaaaa00000000aaaa00015555555555555555555555555555555400000001555555540000000155540000000000000002aaa8000000000002aaa8000000000002aaa8000000000000000444444444444444444444444555455544444444444444444444444445554555400aa000000aa00aa00aa000000aa00aa00aa000000aa00aa00aa000000aa000155555555555555555555555555555555555555555555111155555555555511102828282828282828282828282828282828282828282820202828282828282020000000000000000555505055555050500000000000000005555050555550000aaaaaaaaaaaaaaaaaaaa0000aaaa0000aaaaaaaa00000000aaaa0000000000000000000000000000015401540154015400000000000000000154015400000002aaaaaaaaaaaaaaa802a802a802a802aaaaaaaaaaaaaaaaa802a802a800000005500550055555555550055005555555555005500555555555500550055005500
|0,12=>0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaaaaaaaaaaaaaaaaaaaa00aa015401540154015401540154015401540155555555555555555555555554015402aaaa8282aaaa8282aaaa8282aaaa8282aaaa8282aaaa8282aaaa8282aaaa82855555555555555555555555555555555555555555555555500005555000000000000000000000000aaaa0000aaaa00000000000000000000aaaa00aaaaaa00015555555555555555555555555555555555551111555511115555111155551112aaaaaaaaaaaa8282aaaaaaaaaaaa8282aaaaaaaaaaaa8282aaaaaaaaaaaa8280505050505050505050505050505050500000000000000000505050505000500aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000aaaa0000aaaaaaaaaaaa0001555400000000000155540000000000015554000000000001555555540000000000000002aaaaaaa800000002aaaaaaa800000002aaa8000000000002aaa8000555500005555555555550000555555555555000055555555000000000000000000000000000000000000000000000000000000000000000000aa00aa0000000155555555555555555555555555555554000000000000000001540154000000000002aaa80002aaa80002aaa80002aaa80002aaa80002aaa80002aaa80002a805050505050505050505050505050505050505050555555555050505055555050
|0,13=>0xaa00aa00aa00aa00aa00aa00aa00aa00aaaaaaaaaa00aa00aaaaaaaaaa00aa01555555555555555555555555555555555555555555555401555555555555540002a802a802a802a802a802a802a802a802a802a802a802aaaaaaaaa8000000055005500550055005500550055005500550055005500550055005555550055000000000000000000aaaaaaaaaaaaaaaa0000000000000000aa00aaaaaa00aa01555555555555555555555555555555555554000155540001555401555554000000000002aaaaaaa800000002aaaaaaa800000002aaaaaaa800000002aaa800055555555555555550505050500000000555555555555555505050505000000000a0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0a000000004444444444444444040404040000000044444444444444440404040400000002aaa80002aaa80002aaa80002aaa80002aaa80002aaa80002aaa802aaaaa80000000000000000000000000000000000055555555550055005555555555005500aaaaaaaaaaaaaaaaaaaaaaaaaa00aa000000000000aa00aa00000000000000000001540000015554000154000001555400015400000155540000000000000000000002a8000002a8000002a8000002a8000002a8000002a80000000000000000000000000000000000000000000000000000000555555550000000055005500
|0,14=>0xaaaaaaaaaaaaaaaaaa00aaaaaa00aa00aaaaaaaaaaaaaaaaaa00aaaaaa00aa001414141414141414141414141400140014141414141414141414141414001402aaaaaaa800000002aaaaaaa800000002aaa8000000000002aaa8000000000005500550055005500550055005500550055005500550055005555555500000000aaaaaaaaaaaaaaaa00aa00aa00000000aaaaaaaaaaaaaaaa00aa00aa00000001555555540000000155555554000000015401540000000001540154000000000000000002a802a80000000002a802a80002a802aaa802a80002a802aaa802a8055555555555555550505050505000500555555555555555505050505050005002222222222222222020202020200020022222222222222220202020202000200000000000000000000000000000000000000000000000001540155555401540002a802a80000000002a802a80000000002a802a80000000002a8000000000000000555500005555000055550000555500001111000011110000111100000000aa00aa00aa00aa00aa00aaaaaa00aa00aa00aa00aa00aa00aa00aaaaaa00aa00000000015555555400000001555555540000000155555555540154015401540000000002aaaaaaa800000002aaaaaaa800000002aaa80002aaa80002aaa80005500550055555555550055005555555555005500555555555500550000000000
|0,15=>0xaaaaaaaa00000000aaaaaaaa000000015555555555555555540154015401540155555555555555555555555554015402aaa80002aaa80002aaaaaaaaaaa80002aaa80002aaa80002aaaaaaaaaaa80000000000000000000555555555555555500000000000000005500550055005500aaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa00aa00aa0000000154015400000000015401540000000001540154000000000155555554000000000000000000000002aaaa8282aaaa82800000000000000002aaaa8282aaaa828000000000000000005050505050005000000000000000000050505050500050000000000000000000000aaaa0000aaaa00000000000000000000aaaa000000000000000154015400000000015401540000000001540154015401540154015402aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa802aaaaa802a800000000000005555000000000000555500000000000055550000000000005500aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000aa00aa00000000000000000000000000000000000000000155540155555400015554015555540002aaaaaaaaaaaaaaaaaaa8000000000002aaaaaaaaaaaaaaaaaaaaaaa800000005555555555555555555555555555555500000000000000005500555555005500
|1,0=>0xaaaaaaaaaaaaaaaaaa0aaa0aaa00aa00aaaaaaaaaaaaaaaaaa0aaa0aaa00aa000000000155555554000000015401540000000001555555540000000154015402aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa800000002aaaaaaa800000002a802a80555555555555444455555555555544445555555555554444555555555555444422222222222222222222222222222222222222220000000022222222000000015554444555544445555444455554444555544445555400015554444555540002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa8888888880000000088888888000000005050505050505050505050505050505010101010000000001010101000000000000000000000000aaaa00aaaaaa00000000000000000000aaaa00aaaaaa00015555555555555555555555555555555555115511551155115511551155115510000000000000000000000002aaaa8280000000000000000000000002aaaa828111111110000000011111111000000001111111100000000111111110000000088888888aaaaaaaa88888888aaaaaaaa88880000aaaa000088880000aaaa00001414141414141414141400001414000014141414141414141414000014140002aaaaaaa82828282aaaaaaaa828280002aaaaaaa82828282aaaaaaaa828280000505050505050000050505050505000005050505050500000505050505050000
|1,1=>0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaaaaaaaaaa00015445544554015401544554455401540154455445540154015445544554015402aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa8888aaaa80002aaa8888aaaa800055555555555555555500550055005500000000005555555500000000550055000000000000000000aaaaaaaaaaaaaaaa0000000000000000aaaaaaaa0000000155555555111111115555555511111111555555551111111155555555111111100000000088888888000000008888888800000000880088000000000088008805555555555555555555555555050505055555555555555555555555550505050aaaaaaaaaaaaaaaaa0a0a0a0a0a0a0a0aaaaaaaaaaaaaaaaa0a0a0a0a0a0a0a044444444444444444444444440404040444444444444444444444444404040400000000000000002aaaaaaaaaaaaaaa80000000000000002aaa80002aaa800055555555000000000000000000000000555555550000000000005555000000000000000000000000aa00aa00aa00aa000000000000000000aaaaaaaaaa00aa015555555555555554000155540000000155555555555555540001555400000002aaaaaaaaaaaaaaaaaaaaaaaaaa82aa82aaaaaaaaaaaaaaaaaaaaaaaaaa82aa85505550555005500550555055500550055055505550055005505550555005500
|1,2=>0xaa88aa8800000000aa88aa8800000000aa88aa8800000000aa88aa880000000000000000000000000000000155555555555555555401540154015402a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a0000000054545454000000005454545400000000545454540000000054545454000000000000000000000000aaaaaaaa000000000000000000000000aaaa000155541415555400015554141555540001555414155554000155541415555400000000000000000002aaa8282aaaa800000000000000000002aaa8282aaaa80001111111111111111111111111111111111111111110011001111111111001100aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa8800015554000155540001555400000000000155540001555400015554000000028282828282828282aaaaaaaaaaaa82828282828282828282aaaaaaaaaaaa828555555555555555555555555555555555500550055005500555555555500550000000000000000000000000000000000aaaaaaaaaaaaaaaaaaaaaaaa000000000000000000000000000000000000000155551111555511115555111155551112aaaa2222aaaa2222aaaa2222aaaa2222aaaa2222aaaa2222aaaa2222aaaa2225555555500000000555555550000000055555555555544445555555555554444
|1,3=>0xaaaaa8a8aaaaa8a8aaaaa8a8aaaaa8a8aaaaa8a8aaaaa8a8aaaaa8a8aaaaa8a81410141014101410141014101410141014101410141014101410141014101412aaaaaaaaaaaaaaaaaaaaaaa800000002a802a802a802a802a802a800000000055551111555500005555111155550000555511115555000055551111555500002222222222002200222222222200220022222222220022002222222222002201555555555555555555555555555555544444444444004400444444444400440002a802a802a802a802a802a802a802a802a802a80000000002a802a800000000505050505050505050505050505050500000000000000000505050500000000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa2222222222222222222222220000000155555555414141415555555541414141555555554141414155555555414141400000000000000002aaaaaaaaaaaa82800000000000000002aaaaaaaaaaaa8281111111111111111111111111111111111111111111100001111111111110000a0a0a0a0aaaaaaaaa0a0a0a0aaa0aaa0a0a0a0a0aaaaaaaaa0a0a0a0aaa0aaa15555555555555555555555555555555511111111111111111111111111111112aa82aa82aa82aa82aa82aa82aa82aa82aa82aa82aa82aa82aa82aa82aa82aa85555555500000000555500000000000055555555000000005555000000000000
|1,4=>0x555555555454545455555555545454545555555554545454555555555454545400a800a800a800a800a800a800a800a800a800a800a800a800a800a800a800a80000000000000000000000000000000155115511551155115511551155115512aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa802a802a80000000002a802a8000000055555555555555555555555555555555555555554444444455555555444444440a0a0a0a0a0a0a0a0a0a0a0a000000000a0a0a0a0a0a0a0a0a0a0a0a000000015554000155540001555400015554000155555555555400015555555555540002aaaaaaaaaaaaaaaaaa82aa82aa82aa82aaaaaaaaaaaaaaaaaa82aa82aa82aa85555555555445544555555555544554455555555554455445555555555445544
|_,_=>0
def sP:Nat→Nat
|0=>0x403c0e0682400100200c2e010e840261c0302400100986c2e050004810070b82400160d0640c090004826070302416100981c0c05000401e0e0b82400120400c0c09058481003030140012020642e090585808180302400100401c2e0905858080a0b8240016020440c09000401e0e06824000c0180812000401c0c09058101406048001007030140004018080200
|1=>0x904c06171a8d020120980c0033190402404018c05e09000502a17048005c100904c5a170480020120980c580900040562a1484c06170480034190b82400160904c0e170482c20161405c1200080480803118004e1f0203846090007c4a190b82400160400c2e090e848480311824001f098880c090004010070302400140405c122110048080301024001f0981c0c09
|2=>0x228402415098640c09000481e030b824001f090100623048002844219082e0900040243f0981c5809000407c080185c12000b020063d0480028120401c06170488428040185c002708058260e1782400100904c78060480020121d8e826030b82400390980c2e090004870030b824001f0904c06171b8cc2012098640c09000502413018180a000804826030b8d86610
|3=>0x1800a4460804810070b82400160a810061704944201a018f412000804826070b82400100b010065004800201f2784c060d048003e1301824004e0804808180b82400102693006170480020120212c78170480028130188c124a0a0482603048d86410090200617048002c120980c2e4a248402408018bc12000f84826030009c90100904c06092391820120985c1200
|4=>0xa04c06092e8c820122e00c46170480024130181812000804810030b8243a1f090200e170480028160400c2e091096c24040880c5e090004008181185c12000a04c06171b95c20121300c12002d04024130b824b22008048260e04800b0100909810030b8243a121500c2e0900154201301800ae32080481017048008a140900c12002b15420120980ca817298402413
|5=>0xb98c00100985c12211004024130185c02000804826220b82400100b02006060480028123100cc20900040241e0183412000807c2a080385c12000b01006170482c20160400c2e0930050241303818120008098be090008020120405c1200100c424130708c12000f84826190b824bc100904c0623048743e12040382e090007c241a0b8240045080480803118bc1200
|6=>0x18f41200080481017048008a100904c2e09001b42012098602e090004024130185c12000a1b0266b0b82400100904c7809000c820120204c0623048003e153505c12000a0483403030240010091a42e09001a02012098f412001004024080200c2e090007c26030b800ce10090542e090019820120980c120032840241a0c80c5e0900048c8030b8240010090100650
|7=>0x8048061704800ea10090980609001d020121301006230009c28080185c121d0a04826190b82416140904c06170282c20120980c12003984024080185c121d0906830170480020120980c2e3539040241e0b82400450804826030b8d8e2100904c0609000c82012019c012003784024261200c4609000504c040185c121d0802030170480028123700c2e09000402443
|8=>0x980c1200231fc20120980cfa17048d820120400c2e09108484c032f8240014080489e130185c00340804810030b82400143d8487c130185c1236080482617000d040100904c22060480020120986c2e090005824263d010062304800c4031782400100904c5e09000802012310602e090004024790985c12003c04026030b824ee1009054ec1704800281e018181200
|9=>0xd04c06172389c20120980c2e090004100124604d16230480020120980c2e090022428123c84c0617048d820120d04c06172395c20120989032030b82400140404c06170480110142784c06170480028122784c061704a1820120980c2e840005020120985c12001015420120a84c06170020420120400c2e002b84100123100c2e09000408812021080617048002810
|10=>0x480020120980c2e2729840241a0185c124708200243b0980c2e090005024080380c2e0900050627c0980c2e091b04024130880c2e002b84024150400c2e002904024430980c2e092f04024040980c1200230502013018f412000804826030b824941009020061704800aa10090543c190b82400140902006610480028120404c0617048003e120400c2e09000408812
|11=>0xb82400890a04c060d0b80068100926826031182400140904c0617002602012098712c0d0b82400100980c46090004088120980c46170015c28124a84c0617048d820120404c0e030b8246c140986406170480112124a04c06230480028120981c0609000c820121d81026030b82400104884c2e0900080201209828301704800281209a483017048002012488980690
|12=>0x980c2e09000482aa2098642e090004834030b82400103d84826030685c12860804810030b82442140918806170480020a00904c060d0b98c00140827c2603048008c100901006170009c2810400a426030685c12000a04c066104800202b0927826030b82400100904c061704a746c100909806170480138100909852080185c1200090540e9b0b82400100904c0e03
|13=>0x980c7a090005020120d00cc2090004024130185c124a0a040241547010061704800202a0204c06170480020130185c12a60804826070185c12210a04026110185c125d0804948130185c12000a04834130182400320804826030b8246aa3080483c420185c12000804808030b82400550a0404c13018bc12000804808030b8240014081100617048012e550804926a2
|14=>0x904c06170020d02100913d58130185c12000904c062f04800201f0906826030b8246e100929426030480064100904c06a90480020120d01c0617048002031130e006170480028120400c2e0900051001209aa006170480020123e04c06170015c20120987806090011820121f25426030b8004e10539e826030b82400121f04c06170480020160980c2e09239582012
|15=>0x2dc2012489e826030b82400100401c06170480028801f04c0617002d420120400c2e090005824135a00c2e001384024260994012001004024040185c12000a04140a20980c2e0029040241301acc2e090005026031185c1200588482617048008a10090540617048015c100904c06170480020160904c06174789ca610090f826030b824ba10092b426030b800e410
|16=>0x185c00340804810030b82400312d84808130185c12005d0412a130185c125d0804852130185c12000a04808032805c1200080c426070b82400100b06806170480020800906806610480028100904c32170480028b909078061704800aa100926426190185c125d0904c0670048008c100907806170480020440904c061704ae020120981c0641048002810099080609
|17=>0x980c1a091b04024260980c2e090e84024130188c5e090004024080185c12000a05824260200ca00900050204f1304c060d0480028130185d80000804826bf0185c008f080482617048008a14080484cbe0400c1a090004826030ba1000102d8482a130185c00980804826190185c12a6080494a130185c00570804808130188c12000a134260358024001022048f813
|18=>0x900c2e090030caa100904c0617048d98a100902026030b80066100904c06170480020c40905426030b8254c100904c06300b824001409098260e0b824001009010062f0b82400140813d7c130185c12350904c06171b09c2012098442e09001e020120980ca0170480184100204c2e090030420120980c2e362b840244f0980c12002b04024a20980c2e09000402426
|19=>0x480024260400c2e090007c2413018181200080494a3e0980c2e09000504c080185c12360a0482603280240010220483c190185c1200400482a430185c12000804826030b8243a100f84826070b82400140805826030b8248e10268498c030b82400104004826030b824c0100904c061704884205b0904c061704800ac1009010069b0b8240014080543c030b8240010
|20=>0x80c4247a0404c06170480024260188c12002a84024260200c2e092384024260980c46090007c24c90980c2e092e840242a0980c1a170480020a53c84c0617048002813018f412000816c24130c8602e0900050241a0185c12000805824260f00ca0090004024ac0980c2e006404024c70980c2e090004024130705c12000807c24130183412002b040247a0980c4617
|21=>0x4024130188c12002b05024150981c2e092e840243a09864061704800241509b342e092e84024130181812000a04024260980c2e001a04024260d00c2e091b04024130188c2e092385024130c80c2e090033024134b32c2e090004024260200c12002b0402443098442e090004024620185c1200080c424130c80c5e090005024136500c2e002904024130b8240020
|22=>0x480020120985c12001004100120980ca02f0480020120980c2e0900041a6121306806170015c20121502026030b82400143e04c06090015820122780c2e5f048002012098f02e0900041a41209860a0170480020120980c2e091b1e020124d04c062304800201209864120023041a2120980c2e010004024130185c1200082e424cf0200c2e090004024ce0980c1a09
|23=>0xb82400100904c061704801b210090a834130185c12000804d9a030bb58201209b541a170480020120aa6410030b8246c121301026031182400141301006230009c20123c84c22030b82400100d17006170480020120aa6408190b82400120980c2e092f040b6121302008030b82400140980c2e010005020124880c2e090015420123100c2e090004100122184c0e17
|24=>0x6f84c06500480020124984c06090011820120980c2e0019840241509864120023040247c0980c2e0900040241a0185c1200082e424130c05c120008049bc134b05c12000804826dd0185c1200080484c03280240055080482a3a098642e090004826034d824004608048f23e0980c2e09000407c080980c2e090005026036e02400100904c06616d82400100904db48b
|25=>0x4004834130185c12000804826180b824001408048f8030b97c1200080484c7a0980c46090004826500480040106884826030b91cae100904c06177102400100929c4c040185c12000804c06e10b82400140804c06dc04800281009098260304800ac100905408030b8246c10091f026170480182100906806177002400100904c32030b824ba1409054ec17048002012
|26=>0x1c828100d00c2e5f0480020120980c2e472b85020120d00c2e090036420120980c12001904024130185c120066040241301985cc090004024130185c00275d84024130182400467284024130185c12367204024130185c00330a04024080c05c12000a0498c030b82400105c848261101b8c1200080482603178240010220493413019401200080482617048008a10
|27=>0x9bb006170480020120980ca01704801d6120d0602e090005020120200d60170480020121306806090015820120980c12001905020121300c12007484024260985c120060840241a0c05c12000804826032805c0034080483c030b82400100b04826030b825ce100906830030b82400100925426030b824a2100904c320900118205b0905536170480020124884c0617
|28=>0x904c301704800b0100909834030b82400100918826030b8240010091f026030b800e410092942a040185c12000a04c06617802400100904c06ef3082400140904c062f04800205b0904c0617048d5dc100906806170480020850904c301704800205b0910c26190b82400140905434110b8240010090f826030b8004e1408020383c0b824001009054d417048002012
|29=>0x804834035805c12000804826d52805c120008048b8030b82400140804826110b82400100b04870030b82400144004826500b82400c108048f4130185c120008048b8030b82400100904c06177982400140806826170480040100904c06b004800204d0902078f20b8240010093c426030b82400140909834031182400140904c06b00b82400100904c22030b8244210
|30=>0x804810030b82400141884826037b02400100929532130c80c2e09000494a790980c2e0900040245c0185c120008200241328024002008134242601940be090004024080200c2e0900051001301bd4c2090004024150185c12006c840247c0185c12002a840241a0185c12360820024260980d60090004024260200c4609000502603048008c8a0804826170480040f4
|31=>0xb82400100905426110385c1200080484c040185c00270804826030b82400104004826170480040140804826070185c12000a04062137d00c2e09000409a120404c0617048d828120a84df2170480020124d04c06170480028100904c06610480028100913c26030b82400140904c061704801f0100904c84030b82400104004826030b82400f70804826033f05c1236
|32=>0x5286826030b82400100927826030b82400100901026030b8248e100904c060d0b82400fb0804826030b82442140804826070185c123608049a8040980c2e09000404c080980c2e0900050244f0980c2e090028c201209a581a1704800201209b340617048d82012130a426030b82400100904c06410480020120400c2e090023428120980c4617048d4201252a542603
|33=>0x980c2e090041420120980c2e090040c20123104c061704800204d092d87c130185c12000804a02130185c1200080482a080185c120080040242a0980c46170480020127f37c26030b82400100904c06170480020802204834030b824001018849a8080980c2e0900040243e0980c2e0013840241301bd812000a04024fd098642e0900040247c1304c0617048002012
|34=>0x402c121306826030b82400100904e14030b8240010090680617048011a100904c06173180020121502026030b82400100904c0617004202012098f20e170480020120400c2e090005100120204c06170480176100909826038303412000804826190185c12007b84024130185c12000a0410012133fc06230480020120d04c0617048d820120992c7817048002012
|35=>0x482a040185c12000a04034130185c00570804808130188c2e09000502a130185c12000820024130185c12008684024130188c2e5f0480020121302008030b82400100901026030b82400140813522d40204c06170480020130881c2e0900040b6120d00c2e09000502031092d826070185c12000804a183e0980c2e090004024130380c2e090005020800980c2e09
|36=>0x804826110185c12003f84024a50a84c0e170480020120d00c2e09002342810090997c130183412000804826030b82400e8080494a1509b342e090004024260980c2e091b040241a0185c12000820024260204c06230480020120a84c2e090040820125389826030b82400100904c06170480020312d84a22130185c12000804826038785c1200080484cbe0400c2e09
|37=>0x906826030b800ae1408048f8080980c2e090004024130185c12008a04025130980c2e090004024040980c2e0900438201209878061704800204d0928826030b82400100904c06170480224140913c26032805c12000804808130880c2e090005020080204c06170480028265f04c062304800247c0980c46170480020120980c2e09000502016090f810130185c1200
|38=>0x980c2e0900040241301824004608048271d0380c2e090004024260980c2e09000403e120980c2e090047020120ac6c06170480020125284c06170497420126a04c060d0b82400100d00c2e090005020800904c0617048023210090f808130185c12000a04026030b82400560804826190185c1200890482a1e0185c12000804826030b82400106204826030b8262c10
|39=>0x4c84c06170480020120989006170480028101335010030b82400100948026030b82400100904c061704800ac140804808030b82400101884c060d0b82400c3080482a1e0185c12000a04024130f00c46170480028120980c2ef30480020120980c2e090005020c40947c26030b82400100904c071e0682400100904c3c110185c12000804826030b82400102da0024c7
|40=>0x82e424130185c12350804876130185c12000804826032805cbe0900040241a0986406170480028120400cc2090004024130185c12004484024a50986406170497420128605426070b82400100913c26030b82400100904c0617048024c140949426030b82400100906826030b82400780804a4813018342e090004024df0980c46090004024ce0980c2e0900040243a
|41=>0x480020120400c2e0900041001227a4426030b82400100913c4cff0185c1200080494a150980c2e090005024130183412000813424080980c2e001384024130185c120095840247c0980ca01704800201209ca406170480020125285426030b824ba100904c060d0b8240128080494a130c80c2e0900050241301c9c2e098484024130c80c12002304024130185c1200
|42=>0x22828100905426030b82400105c84826031182400142684826030b824001026a8024260980e5c090004024260185c12009604024130c00c2e090004024150d01006170480020120980c2e5f0480020120980c2e090036420120d04c06500b82400100904c060d0b82400550804826030b824008a0804826030b82400102691024130185c12000a0417212130e00617
|43=>0x905408030b82664000804c2207018240046080484c0801cc412000804826180185c12000a040241e0185c12000820024130185cbe090005020120acc02e090004024130185c12006c85020120a84d94170480020120185c13049784024263d04c06170480020123e04c06170480020121f25426030b82400105285408030b82400100904c30170480020120980c2e09
|44=>0x804826030b8266e360804826190185c12003f85024130185c12006604024130185c120008214241e0185c12000a04100124884c07060b8240010091f122130185c1200080482a130885c12000804a6a130185c120008048f8130185c12000a040243e0980c2e09004d020120980c2f330480020120d04c06170480020120404c061704800f0100904c3017048002810
|45=>0x406212098442e0900050205b0909826031182400140904c06170015c28100904c0617004e02012098442e0900040b61209b1806170480028100904c06170015c20120980c2e090022028100980c2e090033028100904c06170480028104284a18150200c2e09000402415098442e090005020121304c06170480250100904d8c030b82400100906826030b8240014
|46=>0x804826032805c12006184024130880c2e090004100120a84c06170497420121306806170480028100918826030b8240014080484c040188c1200080496c150980c2e090004024130185c120058840241a0980c2e0900040b6124986826030b82400100909834030b82400100909826031182400a308048c4130185c12000804834040185c12000820024130880c2e09
|47=>0x984406090011828100904c2203048008c100904c06170480250100904c06179e82400100906808130185c124708048f4130185c12000a0402413019402e090015420120d04c06170480020800901026031185c002708048271d9e00c2e0900040241301ac02e090005020123d04c06170480020120404c06170480028800909826030b824013a0804826035805c1200
|48=>0x804a80130185c12000804a6c130188c2e090004024150400c2e090004024260980e4e090004024080980c1a170480020120980c2e090005020800904c06170480272100904e7e030b82400100913c10130185c12000804826030b824008d0a04024130185c12000820024130185c12004404024130185c12008104024130185c12009f040244f0980c4617048002012
|49=>0x480020120980c2eea048002012a104c06170480020120980ca00d0b82400100904c071e0b82400100904c061704802581009055fe030b82400100902026cd0185c12000804826030b824012f080482a130185c133200040241301cb82e090004024380980c2e0900040241301d0446170480020120980c2e09004ec2012132f826030b82400100904c060d0b8240097
|50=>0x9844061704800201209b340617968002012a204c06170480020120980c2e09000409a1209b28061704800201209c84061704c1020120400c2e090023420126a04c06170480020129b04c06179680020120404c0617048d820120a81026030b82400100913c26030b82400100905426030b82400820804826030b8240143080482a130185e5a0900040241a0404c0617
|51=>0x40241a0980c2e0900050201209bfc06230b82400100904c0617048d8201209c84061704cc820120980c1a17048020810090f82a130185c12000804834130185c12000804810130185e2e090004a46130185c1200080482603a305c12000804826110185c12000a04024130185c1200a284024080980c2e090005024130188c2e090005024130185c12000a0409a12
|52=>0x185e5a090004024130185c13320004024130185c12000a04062120980c2e090004062120401026030b82400100952026030b82400100946826030b82664100904c3c030b824001408048261e0185c120008048263c0b82400100904c061704800fe100904c0617048028e10093242a130185c12000804826030b8240109080484c130185c12000a04024260980c1a09
|53=>0x4c06170480020120980c2e090005020120980c2e090004024130185c12006b84024130185c12005084024260980c2e090004024136680c2e090004025360980c2e09000402413018342e090004024135780c2e090004024040980c2e09000402413
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x32a0145007a8029400aa0005
|5,0=>0x2e98168c0ae6054302898138c0966048302298108c07e603c301c980d8c06660303016980a8c04e6024301098078c0366018300a98048c01e6
|6,0=>0x13c389c5c4d4e263712e38955c49ce2477120388e5c464e22b711238875c42ce20f710438805c3f4e1f460f6b8799c3bee1d870e8b8729c386e1bc70dab86b9c34ee1a070ccb8649c316e18470beb85d9c2dee16870b0b8569c2a6e14c70a2b84f9c26ee1307094b8489c236e1147086b8419c1fee0f87078b83a9c1c6e0dc706ab8339c18ee0c07
|6,1=>0x21ab90b9c84ee420720cb9049c816e40561ff38fddc7e0e3e971f138f6dc7a8e3cd71e3b0f01c772e3b271d5b8e91c73ae39671c7b8e21c702e37a71b9b8db1c6cae35e71abb8d41c692e342719db8cd1c65ae326718fb8c61c622e30a7181b8bf1c5eae2ee7173b8b81c5b2e2d27165b8b11c57ae2b7615838aa5c544e29b714a38a35c50ce27f7
|6,2=>0x886e43c7
|7,0=>0x31dc18ce0c570623830dc184e0c17060382fdc17ce0bd705e472ee417520b9905c482de416d20b5905a482ce416520b19058482be415d5cadb056582aec15560a9b0545829ec14d60a5ce527728fc145e0a20e5088280413e209e104e882704136209a104c88260412e2096104a8825041262092104888240411e208e1046a62314116a08a5044a8
|7,1=>0x419c20ae1047081b8409c2031d00907fc83fa41fb20fc907dd73eac1f360f8b07bd83db39eba0f4ee79f83cbc1e3e0f0f077f83bbc1dbe0ecf075f83abc1d41ce910740839c41cc20e510720838c41c420e110700837c41bc5cdd306e1836cc1b49cd9506c2835d41aca0d5506a2834d41a4a0d150682833d419ca0cd50662832db994e0c9706438
|7,2=>0x516c2896143b0a158506c281613fb09f584f73a79a13bd09d684e74271a137d09b684d74269a133ee99784c7c261e12ff097784b7c259e12bf095784a7c251e127f093784983a4a2124109188488ba426120308f98478c23a611c308d98468c2329d18508ba8459422aa1145089a84494222a1105087a8439421aa10c5085a84294212dd087083b8
|7,3=>0x6154308a18350c128605bb00e17f70bf385f5c2f91d7b90bd485e642f1217790bb485d642e9217390b9485c642e1216f90b7485b642d9216b90b5485a642d1216790b34859642c9216390b157586c2c1615fb0af58576c2b9615bb0ad58566c2b16157b0ab58556c2a96153b0a958546c2a1614fb0a758536c299614bb0a558526c2916147b0a358
|7,4=>0x70fc385e1c1f0e0787003b7e21be10de886f0437621ba10dc976e0c36e9db650daa86d1bb66e1b270d8b86c23b5f21ae90d6c86b243575daab0d4d86a2c34f61a6b0d2d86933b47a1a2d0d0e8683433fa19ed0cee86734337a19ad0ccf7663c32fe196f0caf8653c327e192f0c8f8643c3201d8f10c708634bb18618b30c5186253b10a18750c328
|7,5=>0x3d561e9b0f45879ec3cd61e5b0f25878ec3c561e1cef06877f43bda1ddd0ee6876f43b5a1d9d0ec6875fbbade1d5f0ea7874fc3a5e1d1f0e87873fc39de1cdf0e67872fc395e1c9f0e47871fc38de1c5f0e278
|8,0=>0x8b5c458e22b8f15398a63c5122279113398954c4866231311088844440221f110f08873cc37a61ad10cd98624c2ee616530aa8850cc2662123108988404c1de60df1067882f4c15a209d1046881ecc0d260591024880dcc051e019100487fdcbfca5fd50fe287ed43f465f912fc087dc43ebe5f4f0f9f87cbc3e3a5f0d0f7e87bb43dbddecd2f5d9
|8,1=>0x9c54ce0666f3137279b4ccd8266b1135089a444d02266f332f89934cc7a262d130e898344bfde5ed32ed9972c4b7625a932cb9961c4aee256532a99950c4a6625213287993f4c9d664d93263992d4c94a24933241891cc48c26451121f990b4c83a240d11fe88fb447ba23cd11dd98eac4732638731ba98d8cc6a2633f319698c6cc61262f911739
|8,2=>0xad24d6722b29158b9ac23d5ee6ae5356a8ab0cd5662aa315498aa04d4e22a6115279a8f4d45a2a1b35049a7e453d229d734e29a6ccd346299314c18a5c4d2c2294f349e9a4acd236290b147d8a3b3d1ba28cb345c9a2abd1362889343b9a19c50ae2847141a9a08cd026280313f899f844f9e67bf13d699e7bcf1a677b33b499d644e8e673713938
|8,3=>0xbe24deee6f6537a99bd04de622f1f37869bbf45dd66ed937648badcdd4a6e9517419b9cc5cc26e4f371f8b8b4dc3a2e0b36fc9b79cdbae2dc716dc7b6a45b2e6d88f6bc8b59cdaaa6d4336989b47cda1e2cfd36768b36cd9962cbb16549b25cd90a6c7516328b14cd8826c3116108b03cd7fe2bef15ee9af3457766bab15cc9ae2bd6f26b6915ad7
|8,4=>0x2fef37ef8bf3c5f7e2fad37cd9
|9,0=>0xd074681673fb19f49cf5ce791f3b919d39ce54e70a337519b28cd546686733319918cc4c660272f119708cb44658232b119508ca446502327119308c93ce47e322d390e8c82ce3f271e918ec8c71ce36e31a718cb8c614e2ea316338a98c50c6262712118879c3f4e1da30db38658c2ec6152709738438c1dc60ca705338218c0cc6046301318009
|9,1=>0x69a274c11a579d27c691e347d3a368d17be89e343f1a169
|10,0=>0xd6446b05f5731ab18d54c6a8635331a918d44c6a0634f31a718
|11,0=>0x1ad07
|_,_=>0
def wAt:=mkWire dB 329 255 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 9 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xb8410187d13050090410985d0007d13050090410985d0187d130500985d0984909850090410d0c70b8410985009851098410007d13050080490985d09849098500804909841018490a850080490980d130500984908049178500b8c509850208490b9010981f000c50985009041098410a850178410b8c509850000590a850080490980d0b8410187d130500985d09841000590a850080490a8500984908049
|1=>0x9853098360b84911a1d0988f0b8413e003278490988d0b84104a150996c0185204a0e410490a8030980d0d0270d04f040490991109936080490885f09867018413f0490b8d90400309841000c50985009041098410985d099400b851080493e027278490988d04003098410980d0b859018510a850080490980d0b841130500985313050048c5098500804909849000590a8500980d0b859018490a8500980d
|2=>0xa853090410980d098500904109841278490405d04003098410d02709851090411f0270a849098410980d218030996d01852080490885f09849018510ba150996c0185231003099350b852080493e04f04035098410b84909841090410ba350980f0984113050090410985d0995a0d05f0404909841020270d00302041098494585d01a1d0988f0b841450410984701851090410d0030d027040490984101841
|3=>0x30850080490ba350980f1307b0985308049130490985d098440980d018490981f018493e027099410684109853090411d0274c8490a8430980d4b04901a5d09837131420985d118490b8410d027098510904101849090410984145041098470c8490988f4985f09845038410a84b0194209835068410c041018c509850018c509850080490988c0b8410985d0023e1384102027098490d003098510985247041
|4=>0xa8500a849080490980d0ba150996c0185208049098510ba350980f31003099350b852098492784b0988d0b84101849000c509850080490c84952803098650f0650184109853090414985f0d00d02041098490b8510804913140080491f0411f0430981d0a8490980d099ed50852080493e0030994106841000c50985009041098410b849048c50985009041099190885f03841018490202708049098350b849
|5=>0x98410a850090410980d0985d068410b84909041020640984901841590410208f0984901ac20ba01098521f2bf0a849098430aa3b0a853080490980d0023e138410202709849528030a8410980d0b849410490a8030980d178500b8c50985008049498030d00d02041098494985f52849098650baad09aab018410184909850098510a0c7098500d05d0d02704049098411f04b02027098493d0411305309041
|6=>0x985d138410189d020270984901ac20ba01098521d0274c8490a8435e80309af10c8250d0270400d040490b8410b85209852080493e0270208d098490b8415d8490206609849018413e043099410b85109041098490985008049018490a850080490980d0a0c709850098510ba35098510980f080495280352843098650b901080490981f0184901a0109852080491484b098350b8495b0271f0010981d01849
|7=>0x80490985d0a85008049002150996c018520984409849080490985b0a85008049498270401d018490a2170996c080495e803528250a841178410b8c509850090410187d13050080490b8c509850080490984927803130431304109845038416184909943068410b8493e00f0208d0b84104049098410b84904003098410985d0007d1305008049131400985d11849098410a8500904109849080490b84913041
|8=>0x405d09841118490b8410d00302041098490985d130500b8410985d3e04b09941068415284b0986501841018520804901841018c509850090410a850098510980d0b85109853080495f049130430985d03a2909847038410187d13050080490985d099410684127853080490988d13050098410985d0b8590a850080490980d0a8490a8410980d099420684109852018410985309ae50a852080490007d13050
|9=>0x118491e0520804901a85098500804909943118490191a0b8460c849018410487d13050090410985d09b410208e098490b8410403709841098510904152803018490a8410980d528030a8410980d0b8590a850080490980d3e02713051090410400304049098410b8410d00309851080493f851090410986701a5d098370b84902041098490996d08049018410b8c509850090412800f098500b8510804927853
|10=>0x98530b8520804909942068410b8490a8495284b0a8410a849098410980d01a1d0988f0b8412784b0404909841003626b841098270182501b0d0994306841040030980d0b8410985d0b8415284b098650c8490d0c7098500985109841098490985d0487d130500985d099420983506841099110ba020985208049098500804927b53130410985d0d02704049098412784b0405d098410204109849099400988d
|11=>0xb849630510996f0185201a150996c01852080490b8822800f068410b849280c70985008049038c709850018490ba29098470185113051080490400309841098490980d3e00f04035098410b849080495280309865018410980d0401c0984101849068410ba5d098370b849098450885f03841018490980d0b8460c8491320109852080490985d098510985208049018590a8500980d4b03501a5d098370f135
|12=>0xd1370985108049438410988f118490b841018c509850098510804902041098494985f0984501851133ab0985d098343e00f130510804909851018c5098503e02709941118490985b0a85008049003a251841130270985d0885f0c8490980d0984403841018490904148827098350b8490d0030d02709851098460985108049099180885f0384149827098450185109841018c50985009041098670994306841
|13=>0xd0c709850098510804902140098490b85108049098512800f0b85109852080490984101a850985f630410996f018520904109851090410d04f0204109849000c50985008049018c5098500804909a01098520804909911099360b8524882748841098350b8490a841098490980d308410ba350980f018520804909850018520804909851080490200d02027098490984101a850985f768410980d0981c01849
|14=>0x206709849018410b8d904003098410985009041098410b8c7098500804952843098655284b09865018410f20109852098532805f2800f068410b84909940068410985208049098410984930851080490ba354984f0a85108049099410994206841040030d04f040490985208049098490b841090410985d09943068410b8490d0c70985009851018510a850080490980d09852098530904109941068410b849
|15=>0x98490985d09041098410985d130270985d01a5d098370b84901825040030984148843130490985d0b9010981f01849098410980f09041278030988d0b8410a84b0980d0980d038410184902027098490985d0d04f02041098492800f0b851080490985008049018490b852080490804904003098410980d66843018250f05d0985308049080490ba350980f0405d09041098415f027130430985d0985208049
|16=>0x1a850985f04336098410182503c130980301849099350b852080491f0010981d0184909c090c827018410a827098410980d2784b0988d0b8417f85d0984b09852080490985009851080491304b098410985d0200d02027098490b8c70985008049019fd098670184113051080490985d0400d040490984109bf1068430b8490d00302041098494b841098370b849000c509850080490400309841018491304b
|17=>0xb852080494884b0205d098490880f038410184909850098510804909b2903801018490a8010a8490980d0184909852080490a850080490980d02041098490985d01c2d0200309849098510980f08049048c509850090412784b0405d0984104c2682049098031e04301a850985f09852090410984102066018410985d068010b84902067098490d04f09851080490b8410984b0985d0404904003098411e041
|18=>0xc84901841018490a8410980d098510980f080490b849130430985d51841130270985d0a8410980d0182504003098410985d09851098520b841098490985d0c8270980d018416a0411304b0985d098500185208049278250988d0b841880410bb5d0982713043098410985d09041098490980d0d02704049098410b84108049098490985208049870490988e0b84109940118490b84109841098490985d09849
|19=>0x8d0360b849098010200d08049098490d05f02041098493f84109867018410980d0985308049468520980f080498c00309c5d048410d027098510904104035098410b84909c5703843018496f8437f85d0984b0988e0b8410b852080491f0430981d01849468410980f090410988d118490b841098490185108049080490984109849130430985d09941118490b8410a850080490980d0a849098410980d09867
|20=>0x1304b098410985d09c899084b018010d05f0985108049098500804909849099430684109853080490980d0b8410985309041480490988c0b841468520980f080490f00d09853080490b8490bc11098030985301851080490985201852080497e8495780d098430885f038410184903c11098030184913050080490985d7f88e0984b0b84102043098490980d5280309865018414884b0983509a010985208049
|21=>0x98350b84908049098650184182049098030b8010b8460c849018410996e0185208049278030988d0b8414a8410a84b0980d09940068410b849098510904101841098410ba350980f200410981f018495280309865018410a8010980d0184911a1d0988f0b8410400f09041098414c8250a8430980d0d00f020410984957835098430b8490b8417f85d0984b9185d0404b098410a8430980d0f0490985308049
|22=>0xb8410985d09cb604801018c5098500804902041098490980d09940068410b849098460384101849098510b8510804909942068410b8490984703841018490b852080490996e01852080497f8410984b0985d0d04f040490984113041130490985d130410984b0985d0a841090410980d2805f068410b8490202709849098410401e098410184909941068410b8499504301b5d09827528030a8410980d48803
|23=>0xd00f0404909841018c5098500804900049098490980d0b84603841018490b825098410985d018c50985008049098520985308049099400b851080490980d0986401841098460185108049038010980d018490980309c9e0b80113053080490985d04035098410b8490a84b0a8490980d0a841098490980d018c509850080490984701851080490a852080490b8410b85209041099340b852080490985d1184b
|24=>0x984108049098360b849468510980f080490996c01852080490a801098490980d0980d018510804948803130490985d0996f01852080490f05109853080491b0490400309841090410986701841468510980f080490996c018520804909852098530804909835068010b84948841098350b84901851080490980d648439b00d09825099410b851080491f0030981d0184904c390988e0b8410f0510985308049
|25=>0x804909943068410b8490985208049528030a8410980d09851080490985d099350b852080490b841098490985d1f0010a8490980d9c8410205f0984909851018520d00d020410984904049098410985d130270985d0b841099350b852080490d04f02041098490985001851080490196d01852080490b841090410985d0d02709851090411202757849098430196d01852080490996f01852080490d02704049
|26=>0xb801098410b84909852080490205f0984966801018250405d098410980f080490985208049098360b8490c82701841938270b8010988d0b8410885f01851080490885f038410184948803098350b84904034098410b8490d0030204109849130530985d09942068410b84909851098520b841020270984901c11098030ba01098520804913053080490985d0985209041098419d849130030985d0ba0109852
|27=>0x490b8520804901cc90004909803018010980f098411304b0985d04801098250400309841098490980d0988d0b8410a8030980d0402709841048010980d0404909841098340b8497f80d0984b068410b8490bc110980309cb6048010984b0980d098410182509c9e0b8010980d000491184b0b8417f8410984b118250b841130030985d130430985d098370b8498d05d098010b84109825098410980d0985d
|28=>0x490985008049098500804909841098499b0010982509801000490985308049098530804901a850985f09867018410bcb6048010a8250980d8204909803080490985d0985d0b84909851080490984b0b84104003098410180100049098030b8490a8490980d020410984909841048410404b098419384b0b8010185108049508490985f0904109841090410b8410b852080490384101849048010182509cc9
|29=>0x8049098270985f0985d01825098250b849098430984904801
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x74000000000000000000000000000000000000000000000000000000000000000000000000000000000d00000003
|6,0=>0xb5000002850000000012980000000000000000000000000000000000000000000002050000000000001d30000000000000000000000000000000000068c0000000000000000000000000005cc0000000026804840000000000000000000000000000000000000000003cc00000000000000000000b4
|6,1=>0x4e100000000000000009a2000000000000000000000004c10000000000000000000000000000000000000000000000000000000004b1000000000000000000011d000000000000000000000000000110c0000404000000001da800006e80d0c0000313
|6,2=>0x4f5
|7,0=>0x204440087e2000000003e4c7b90f431e443bcc7690e941cc638cc6fa00001b86364c6c08d531a82344c6718cb3190631106098bd417462d905998af415682a0c5298a1413a800004ca095412282350000089410a8000040a07f20fa41e8c3b2073300001bd036186930000198c31205e40b4815cc0000543
|7,1=>0xc71800000000000c52187330860000c0217c400005e4c00000002ea85c8cb7996c32d085910b0996012ba60000aca15542a4653cca61800029440000a3200002866500c9e2000027084d4c991800025c800009521273246847d0000000023a446c80000000230645888999103218800008421044
|7,2=>0x44c688cd101a1d3432885c90a1a11341a8828c000208240a6808cff21fc200000000fc9800000007d8cf99800000007c0cf699ea33cc878ccefa1dc300007688eb21d33000074480001cd4394671cce219c2237e60000dda1b8300000000da99b2335e66b48d591a74000068d000019f433866610ca99914
|7,3=>0x15b9ab4300000001589800055c6aa91539aa525464a8854f9a9c3000000014c9a9635266a3d0000000051a4a28d439a84350449fcd3e1a7a200009e093a2270400009b1135126824c880001309a5d44b4695cd29a250349a692c9249000048a8000120a23e347848e111a9800046468bcd1692294
|7,4=>0xd289a39b4436808cf4d9ca33540000ccc9981b2d36546c9cd921b21363a8000000031b262e8c4d0000310361a6000000000000000c28c00030736068000181080005fe600017e1af84000000017a200005e260001771aeb35d24b95170a00005ba8b6516aa2d140000b38d6522c735886b04d5ea2ba3
|7,5=>0xeb0dd423a627448e7cdce1b99372c6e509c82000000000001c69b8a370c8e0cdc0180006f88de11ba9b7326e06db11b5136736c86d84daf1b5b36ae8d50c000351369e4000000034c3
|8,0=>0x8c67180e2e9c5a38ae7150e289c4f28987128a239c44388270f8e1d9c38386a70c8e179c2c3852709ca129422383e7070e0c9c1638267040e069c0a380e7010e009bfe37f66fe49fb1bf337e06fb4df51be737ca4f88def9bdc37b26f58dea13d1379c6f2cde41bc537846f009de9bba376e6ed0dd913af3
|8,1=>0xa3a7468e8b9d143a227438e859d083a0a740ca801cfd39f473dce7a1cf139dc73ace741ce539c4737ce6e94db29b07354e691ccf39987328a639cc4398272f8e5d9cb8396a72c8e579cac3954529ce521ca1393c726ce4c1c953924723ce461c8a290e7210e409c7e38f671e0e3a9c7238de71b0e349c663
|8,2=>0xbb27758ee99dd03b9a7728ee415c53b8476fcede1db93b6c76cced81dad3b54769ced295a23b3e7670ecc9d963b267640ec69d8a3b0e7610ec09d7e3af675e0eba9d723ade75b0eb49d663ac67580eae9d5a3aae7550ea89d4e3a967520ea29d432a8074f4e9d1d373a6874c8a979d2c3a527498e919d203
|8,3=>0xd2a7a4cb481e8e2d167a20f429e823cfe79f0f3d16773ce879c4f371e6b3cd07998b319e603cba7968f2b9e543ca27938f259e483c8a7908f1f9e3c3c7278d8f199e303c5a78a8f139e243c427878f0d9e183c2a7848f079e0c3c127818f019e003bfa77e8efb9df43be277b8ef59de83bca7788eef9ddc3
|8,4=>0x3531ea33d407a74f4d1e982
|9,0=>0xe4e5c94b9197212e3e5c74b8d97192e2e5c54b8997112e1e5c34b8597092e0e5c14b8197012dfe5bf4b7d96f92dee5bd4b7996f12dde5bb4b7596e92dce5b94b7196e12dbe5b74b6d96d92dae5b54b6996d12d9e5b34b6596c92d8e5b14b6196c12d7e5af4b5d96b92d6e5ad4b5996b12d5e5ab4b5596a92
|9,1=>0x1cf4b9d97392e6e5cd4b9997312e5e5cb4b9597292
|10,0=>0xe9220003a40f471e8c3d147a20f431e843d047a00f3f1
|_,_=>0
def PO:=mkPO wAt oP oO 20 9 511 15
def pmP:Nat→Nat
|0=>0x48000000000010e00000000004000000000000f700000000003d00000000000b200000000002400000000000840000000000208000000000080000000000010800000000004000000000000c000000000002900000000000900000000000220000000000084000000000020000000000007000000000001a00000000000600000000000140000000000048000000000011000000000004000000000000c000000000002800000000000800000000000100000000000030000000000008000000000000
|1=>0x199000000000066000000000016900000000004ba00000000012d80000000004b2000000000129000000000049200000000011e800000000044000000000010f800000000043c00000000010d000000000043200000000010c000000000042c00000000010a000000000042000000000010680000000004180000000001048000000000410000000000102800000000040200000000010000000000002d20000000000a4800000000025000000000009000000000002220000000000880000000000210
|2=>0x8020000000002006000000000801000000000200200000000080000000000017720000000005dc00000000017600000000005ce800000000173200000000056c800000000153200000000054a80000000014d000000000052f80000000014020000000004ccc0000000011800000000004440000000001100000000000420000000000101000000000040080000000010010000000004000000000000c740000000002e8800000000099200000000022f800000000080400000000020000000000006e0
|3=>0xd6c0000000003492000000000d0c8000000003190000000000c4480000000031100000000009bd80000000026e000000000099f800000000267200000000096fc0000000024be000000000929000000000248600000000090f800000000243600000000090c8000000002424000000000908000000000241200000000090280000000021320000000008248000000002090000000000821000000000208000000000080680000000020180000000008050000000002012000000000804000000000200c
|4=>0x1d6fc0000000075bb000000001d4cc0000000074bf000000001d2ec00000000743f000000001d0e8000000007432000000001b2fc0000000066fb00000000196fc00000000653300000000192fc0000000064bb000000001927c00000000643b00000000190cc00000000602e00000000172dc00000000577300000000132fc0000000045bf00000000112fc0000000044bb0000000011010000000004182000000001026c0000000040100000000010004000000004000000000000ddf80000000035be
|5=>0x1112fc00000004063000000001010f80000000403380000000100420000000040090000000010008000000002a1a6000000009d2ec000000026cbf000000009a2fc0000000265bf00000000992fc0000000264bb00000000952fc000000010000000000003d3fc00000000e4bf000000002f2f800000000a4be00000000292bc00000000a3a0000000002824800000000949200000000251400000000088a60000000020298000000008000000000001f2fc000000007773000000001dc400000000075fb
|6=>0x819afc0000002066bb000000081927c0000002060180000000815e6c000000204002000000042b2f8000000109492000000042125000000010749f00000004192fc0000001054bf00000004152dc000000104cbf00000004132ec0000001045b700000004112fc0000001044b6000000041125800000010289600000004096f80000001020820000000404200000000100888000000040221000000010080c00000004010080000001001240000000201010000000080400000000020000400000004543f
|7=>0x44112fc0000010264bf00000040992ec00000100e4bf00000040192fc00000100649f000000401804000000100408600000040100000000008444bf00000021112ec0000008424be000000210806800000084009e000000210026000000084003c0000002100070000000840016000000201d0f800000080300900000020096f800000080141a000000200504800000080140a0000002005020000000801019000000200004000000080000e0000002000020000000400220000000100000000000028349b
|8=>0x20019efc0000080064bf00000200090d800000800232800000200010400000080003220000020000088000008000000000001401827c00000480509f000001041927c0000040244bf000001002068c00000400703300000100186ec0000040060df00000100182f8000004002081000001000020c000004000021000001000002400000200040400000068110400000018074bf00000060192f000000180341c00000060092700000012064bf00000048112fc0000011074bf000000441937c0000011064bf
|9=>0x11800992fc0004440244bf00011000992fc0004240025bf00010100992fc0004040051ba00010000912fc0001440264bf00005000912fc0001010064bf000031041927c00008c02649f00002144193fc0000850060bf00002040992fc0000440064bb00001040192fc0000400244bf00001000096dc00003024019f00000808186380000200265bf00000400000400000090064bf000002401927c00000900649b00000220112fc0000080664bf00000201186fc00000804012c00000200992fc0000080261bf
|10=>0x2807000912fc0900010064bf02003100992fc0800852060be02001000992fc0400442364bf01001100992fc0400400344bf01001000912fc0400400064ad00801140992fc0200410364bf00801008912fc0200018044bf00800048192fc0200010044bf004000081927c00e0002074bc001001401c2fc0040012874bf001000041d37c0040000074bf000800003927c00200000b49c000601008002c00180002000300050101892bc0010000244bf0002890000084000820020028000201000008c000620000028
|11=>0x88800040112fd2000812060bf20200046112fc4001c40264bf10000000b92fc2240012074bf088000401d2f02000010044bf040140008200c1000040220a1
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x1000000000000000000000000000000000000000000000000100003
|6,0=>0x1d0000000002380000000000000410000000000000000000000000000000000230000000000000c00000000000000005400070000074000c81c001600004001b000000600000000000000000000000000034000000003000000000000000000000900000000000000000100000020740000000000000000000000000040000000000005
|6,1=>0xa
|7,0=>0x1c6000000016160380106510001000000f05812041a8201cb041000f212138040e000380214005d8580a00309680e000b8001603148b800002d85800000201c9c165b800322e2d81cee00001980e07038582c200b01c2e002401082040a0380216113689a2c02044060b0784c12190c80132260cb04000b0580106b9150a004070042c94160000422b10c89c0021
|7,1=>0x8310000002000b2382c070f87408598c000a8070b1380000018042c280c0582c030005974250005c2c160a801ee0b0b0582e040385806000280076492d85c12000b0a0b6050399d04211e0582c09060c80003008103804000000e00000100800000a808040b85832c900018cc1000058005c0b01c08426280016075200008041b038308700014001901af49a7a
|7,2=>0x259003378100816268618800000000c09069840c00460645cc7009ac9603018582c3e6194000012d800005f0001a52018e858b87a000580ea50b168065f7c00000e33121000070200000000001000074c801c200338007c61000018c000c0000e070b0145e4c02830c62e003947e0404b88805d
|8,0=>0x3017e3e888e0ed26eb8b298f52e5e2260c7449d79424649ab8205b5fa68e4f04eb5c7a355f179d27a54d4213172a1aa0ed838c0d5f483ab6da00467b28aa1a22bbcf742a0831267897205f438a7c9d3022b0810c4d99d49ac49336d0ea0dc34a9c2ca2544b127051c8dd17110caca1eb83f3096b5c222cddb158dbba5688688d4b712b186520d3820192b354da45ce2b
|8,1=>0x339610d1a6624cd913449740d103e1fd9740450b860807ca24ac3577b39bcdd79191be8d3d1c28eef86a4ced307227d2662b00cde95019c31fe9616a4a78f1a71951e69943ce8b3634a2644ea4902808cd3832eac932ba4d12733424cb60c569f464527510dc0bf37479cd0e744b5ea8999c94ce538424dd94680b02082f552b1a9194a2a6887c4a86016174999526ab
|8,2=>0x1e2f58a2709e07
|9,0=>0x249269eaa4f524937ebeeb1684aa4d6c9e6acca7c9791a7e989c9bbd9689c67a25ed539fa267d2f84596ab4d9040a6951ad2816721693f2b324b24e276cf4e59ebb495ad6e014ab328d252aa9d2d26935b54abed6
|10,0=>0x44a1566fe7f5a6628b7dcaaaf39
|11,0=>0x89
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 50 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_252 9 roots_252 ops++addP pm 1 dom_126 9 roots_126 ops++addP pm 2 dom_230 8 roots_230 ops++addP pm 3 dom_238 9 roots_238 ops++addP pm 4 dom_190 9 roots_190 ops++addP pm 5 dom_122 8 roots_122 ops++addP pm 6 dzo_156_2 5 roots_156 ops++addP pm 7 dom_246 9 roots_246 ops++addP pm 8 dom_90 5 roots_90 ops++addP pm 9 dzo_90_4 5 roots_90 ops++addP pm 10 dom_188 8 roots_188 ops++addP pm 11 dom_118 6 roots_118 ops++addP pm 12 dom_156 5 roots_156 ops++addP pm 13 dom_222 8 roots_222 ops++addP pm 14 dom_250 9 roots_250 ops++addP pm 15 dom_214 5 roots_214 ops++addP pm 16 dom_216 5 roots_216 ops++addP pm 17 dom_220 7 roots_220 ops++addP pm 18 dom_110 6 roots_110 ops++addP pm 19 dom_186 7 roots_186 ops++addP pm 20 dom_182 6 roots_182 ops++addP pm 21 dzo_218_4 6 roots_218 ops++addP pm 22 dom_102 5 roots_102 ops++addP pm 23 dom_174 6 roots_174 ops++addP pm 24 dom_218 7 roots_218 ops++addP pm 25 dom_114 5 roots_114 ops++addP pm 26 dzo_220_2 6 roots_220 ops++addP pm 27 dom_206 5 roots_206 ops++addP pm 28 dom_106 5 roots_106 ops++addP pm 29 dom_88 4 roots_88 ops++addP pm 30 dzo_252_2 7 roots_252 ops++addP pm 31 dzo_216_2 5 roots_216 ops++addP pm 32 dom_244 6 roots_244 ops++addP pm 33 dom_108 4 roots_108 ops++addP pm 34 dom_124 7 roots_124 ops++addP pm 35 dom_204 4 roots_204 ops++addP pm 36 dom_236 6 roots_236 ops++addP pm 37 dom_210 4 roots_210 ops++addP pm 38 dom_152 4 roots_152 ops++addP pm 39 dom_242 6 roots_242 ops++addP pm 40 dzo_248_4 6 roots_248 ops++addP pm 41 dzo_250_4 7 roots_250 ops++addP pm 42 dom_248 6 roots_248 ops++addP pm 43 dzo_248_2 6 roots_248 ops++addP pm 44 dom_116 4 roots_116 ops++addP pm 45 dom_234 6 roots_234 ops++addP pm 46 dom_212 4 roots_212 ops++addP pm 47 dom_178 4 roots_178 ops++addP pm 48 dom_202 4 roots_202 ops++addP pm 49 dzo_216_4 5 roots_216 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_254 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45|h46|h47|h48|h49
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_238 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_156_2_156 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_90_4_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_188 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_156 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_216 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_zo_218_4_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_174 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_zo_220_2_156 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_88 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_zo_252_2_156 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_zo_216_2_152 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_108 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_204 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_152 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_zo_248_4_88 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_zo_250_4_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_zo_248_2_152 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h45;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h46;exact cpcs (by decide +kernel) lowS_212 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h47;exact cpcs (by decide +kernel) lowS_178 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h48;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h49;exact cpcs (by decide +kernel) lowS_zo_216_4_88 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_252 9 s (0,roots_252.map (·&&&dom_252)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_254 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_252 h
def symsG:List (List (Nat×Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)],[(0xffffffffffffffff0000000000000000,64),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_254==dom_254)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_254 gM v ys):RunD true dom_254 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_254 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 6 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 6 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 27 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 27 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 130 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 2 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 130 → Z 6 i = true := (range_split z6_0 z6_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 256 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_256 : ∀ i, 256 ≤ i → i < 359 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 103 256 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 359 → Z 7 i = true := (range_split z7_0 (range_split z7_128 z7_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 256 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_256 : ∀ i, 256 ≤ i → i < 262 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 6 256 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 262 → Z 8 i = true := (range_split z8_0 (range_split z8_128 z8_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 75 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 75 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 12 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_254 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def isoMvS_191:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_191:Lower true dom_191 roots_191 goal_191 11:=lower_iso_b isoMvS_191 (by decide +kernel) lowS_127
def isoMvS_247:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_247:Lower true dom_247 roots_247 goal_247 11:=lower_iso_b isoMvS_247 (by decide +kernel) lowS_239
def isoMvS_253:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_253:Lower true dom_253 roots_253 goal_253 12:=lower_iso_b isoMvS_253 (by decide +kernel) lowS_251
def dzo_157_2:=0xcccccccc000000000000000000000000cccccccc
def gzo_157_2:=0xccccccc8000000000000000000000000cc888800
def gsh_157_2:=0x3333333200000000000000000000000033222200
theorem lowS_zo_157_2_157:Lower true dzo_157_2 roots_157 gzo_157_2 8:=lower_iso_b (d1:=dom_157) (r1:=roots_157) (T1:=gsh_157_2) [(dom_157,2)] (by decide +kernel) (lower_slice_b (T:=gsh_157_2) [] (by decide +kernel) lowS_157)
def dzo_91_4:=0xf0f0f0f000000000f0f0f0f0
def gzo_91_4:=0xf0f0f0e000000000f0a0a000
def gsh_91_4:=0xf0f0f0e000000000f0a0a00
theorem lowS_zo_91_4_91:Lower true dzo_91_4 roots_91 gzo_91_4 8:=lower_iso_b (d1:=dom_91) (r1:=roots_91) (T1:=gsh_91_4) [(dom_91,4)] (by decide +kernel) (lower_slice_b (T:=gsh_91_4) [] (by decide +kernel) lowS_91)
def dzo_251_4:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def gzo_251_4:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0f0f0f0f0f0a0a000
def gsh_251_4:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0f0f0f0f0f0a0a00
theorem lowS_zo_251_4_91:Lower true dzo_251_4 roots_251 gzo_251_4 10:=lower_iso_b (d1:=dom_251) (r1:=roots_251) (T1:=gsh_251_4) [(dom_251,4)] (by decide +kernel) (lower_slice_b (T:=gsh_251_4) [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000,0,32),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_91)
def dzo_219_4:=0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0
def gzo_219_4:=0xf0f0f0f000000000f0f0f0f000000000f0f0f0e000000000f0a0a000
def gsh_219_4:=0xf0f0f0f000000000f0f0f0f000000000f0f0f0e000000000f0a0a00
theorem lowS_zo_219_4_91:Lower true dzo_219_4 roots_219 gzo_219_4 9:=lower_iso_b (d1:=dom_219) (r1:=roots_219) (T1:=gsh_219_4) [(dom_219,4)] (by decide +kernel) (lower_slice_b (T:=gsh_219_4) [(0xf0f0f0f000000000f0f0f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_91)
def dzo_253_2:=0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
def gzo_253_2:=0xccccccccccccccccccccccccccccccc8cccccccccccccccccccccccccc888800
def gsh_253_2:=0x3333333333333333333333333333333233333333333333333333333333222200
theorem lowS_zo_253_2_157:Lower true dzo_253_2 roots_253 gzo_253_2 10:=lower_iso_b (d1:=dom_253) (r1:=roots_253) (T1:=gsh_253_2) [(dom_253,2)] (by decide +kernel) (lower_slice_b (T:=gsh_253_2) [(0x3333333300000000333333330000000033333333000000003333333300000000,0,32),(0x3333333333333333000000000000000033333333333333330000000000000000,0,64)] (by decide +kernel) lowS_157)
def dzo_221_2:=0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc
def gzo_221_2:=0xcccccccc00000000ccccccc800000000cccccccc00000000cc888800
def gsh_221_2:=0x33333333000000003333333200000000333333330000000033222200
theorem lowS_zo_221_2_157:Lower true dzo_221_2 roots_221 gzo_221_2 9:=lower_iso_b (d1:=dom_221) (r1:=roots_221) (T1:=gsh_221_2) [(dom_221,2)] (by decide +kernel) (lower_slice_b (T:=gsh_221_2) [(0x33333333000000000000000000000000333333330000000000000000,0,64)] (by decide +kernel) lowS_157)
namespace S_255
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(1,129),(2,34),(2,66),(3,11),(3,19),(3,35),(3,67),(3,131),(4,36),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(6,38),(6,70),(6,134),(7,15),(7,23),(7,39),(7,71),(7,135),(8,9),(8,24),(8,72),(8,136),(10,11),(10,26),(10,42),(10,74),(10,138),(12,13),(12,28),(12,44),(12,76),(12,140),(14,15),(14,30),(14,46),(14,78),(14,142),(16,17),(16,24),(16,80),(16,144),(18,19),(18,26),(18,50),(18,82),(18,146),(20,21),(20,28),(20,52),(20,84),(20,148),(22,23),(22,30),(22,54),(22,86),(22,150),(32,33),(32,34),(32,36),(32,96),(32,160),(40,41),(40,42),(40,44),(40,56),(40,104),(40,168),(48,49),(48,50),(48,52),(48,56),(48,112),(48,176),(64,65),(64,66),(64,72),(64,80),(64,96),(68,69),(68,70),(68,76),(68,84),(68,100),(68,196),(128,129),(128,132),(128,136),(128,144),(128,160),(130,131),(130,134),(130,138),(130,146),(130,162),(130,194),(192,193),(192,194),(192,196),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffffffffffffffffffffff
def xsM:=roots_255.map (·&&&dom_255)
def gM:=goal_255&&&dom_255
def NN:Nat→Nat
|6=>15
|7=>62
|8=>236
|9=>273
|10=>108
|11=>27
|12=>5
|13=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x7346770ac6643b05e49d5c2304f0da407932552f179ab14291138d80c57407300029e10261a
|7,0=>0xe8371e7aa2cd0c4c9723c5db1c4392b8c6f946f087edd8615f7ef287d5e77517273fe971de670de76a86a67a115e4915cb0352fbc43da840de53dab6399e335547315682e9ff2e4c02d6c02bf582b6a82a18429f7c2920927ae2275812398b2225f214a21e69b1917018aff17ffd177ba15abe138090fa9d0f86d0e7370e3ee0d8b80d00b0c18c0949406b6c04fb401fb001d4601c8a016b10111d
|8,0=>0x3640e35ba834e0a33eac330c332e7032be53289d324eb32080314693121e30d4a30cf2307e33078a2f4fe2f1e12e82e2e8162dea82de342d92e2ced52b8842aa882a9342a15828bdf27e6f275dd265032570924fdc24c6d24a3f2418023c5a23b6723953237462327622a082243b21e5520d0d209b5201ce1fa451e8721e69b1ddcf1dd581cb021c60c1c5d61bedf1b3361b0071ad951a49b19669191fb1915d18ab718878187a518720185b9183731828e16a97167a71651f15e41151351504014a57141c2139e5134b612c7211ea010f2c10ee310a0310823107ea105921019b101860fa530edb10eb510e9e80e5f20e2490e0480dbb90d2120c44e0c1de0b62f0b4c10b3910b0850acc50ab8b0a77409d080972d0759e0736006a4d068550613704c4a04a1b042cb041e603eae03a8a028dd0264d0200700f730070400320
|8,1=>0xfd1fef45cbed762e8371e42ced48c7cef19cc019cbc86bf7b4bf629bc721bc123b3cedb297db11a3afd46ac163a8d97a8679a0c8fa09029a0f4977ed9638a8fa7b8ce118c7088bb428ad8f8aa0489d2188b368812087f828754b8409c8361e8014b7dfd67d1887afde798417766c76e7674c6a743a173f1a733ad6f4686e0c96dc796be0769797694f268e4d65275646596405860a5e608f75fddd5e6075d2585ce1a5cb4f5a69c58b0157eb6576d9557685482652e33513ec50dfa501344e4d34bc104b90a48e0748d4f4897f472bd466b54650a460f445efd45a2544f8944290440c04139a412ae3ffb23f7c13f27b3f1223eef93e9983e4df3d8c53d78c3bebc3bbc93a2d937cc33770a3643d
|9,0=>0x3770a36d51362fb35b4c34af334a5e33dca33b9033ad4330f23275e3274d31e0431a6a3121e30d4d3004a2fb372f78a2eb282e5de2e05e2de652dbbe2d3f62cff32cdfc2cc6a2a2f129b7529701286e2283842834327c3a2732e2709c2700f26fc725f6825d3d25cd725449245c82425e236ba22bea223f3220b52158a210b120d74205fc1f11c1e6111e5431e1281d0371cd271c9b31c8f51c6c71ba331b7391a8fd1a4081a0b218d8e1755416e9416b2915637153d614d7314b33145f31390613542134b61310212dad12af9121aa117b0110db10e4a1072d104570fa890f7870f5d80e8df0e0330d02f0ccd80c9e10c3a20b94b0b76f0ac580aa4b0a75a0a0fd09ea50977108fcf087b0086a90864007b26078bb0705505f3405b82059c20569e0565b0549004d7f04b6303d7b0388a034370301b02ca70200701c4001678
|9,1=>0xb1e23b1a51b150bb0560aec7dada99aa0e7a5dd7a2fdaa2ccba2b6fa1a91a14cba0ec8a0143a00ed9ff4d9d08c9cbc49b34d9ac3f9abb69a78c9a0ff98c0c9665b964109627a95a9d9550692b2a90a758eeb68e9828e94d8d9a88cdd58c3668b0c089ce881583813a480c94804d97dc457d5a378b3f78a62786b37826277f4876aa07588774f8574d8e726ea6c5176be076a5f46a4b7645ea60f4c5fcb85ee1c5dab85da1e5cbe95bfce5bb775ab5d59b0a58b015899e586ac580cd57798572af56b55558915557354cdc5422f53b9252263518b4516f050b09509644fa2b4e92d4e1ca4d4554cb504c8ae4c2aa4c0144afba4ae294a7d94a6594a0c84908247da0460ab4600f45ddd45c724524b42c0442ad542283407fe406fc40581400e14000c3f84a3f5363ed5d3e93c3dc6c3c8873bcf33bad73b4003b14139d7537cc3
|9,2=>0xefd58e3da6e095cdf4c4daecbda285d90a9cef19cdf4fcc9d7ca54cc6d0ec0efdbe7e0be71fb4002b282e
|10,0=>0xf091dd6871c5823b158ab0996a60e199d7498eb39421790d2a903948d0ef894c886dab836827ba017b5077a6e27826274a3871687700cc6f8036d2066bff968acf6719c6585563cc5615ae604c45eb3a5a98c590eb55fef53c425320551b8b4f7654ee384d0964be7542a57421884174b40dbf3ccfe3c85f3b8253b6753a6fe382093535f34d883421f3413e32fef32aec32a9132573321c4309ab2f2142be732b59b2a57c267e82387e2331e22851221941fe931f5c51f0281e6ed1dc5f1cab51bb1e187ed18068177491687d151cd13ddb12ff711844111801065e0f4860dbe10be020b9450b9270b2520a7380986007aad0794e077750709e06d67057aa052cd04a1504666009c6009af008b7
|11,0=>0xf2f5ca763d9b4f297a637707776ca573cc66e3d66b37066b746551f5cbf94ba7e49cad47d6c3799a31fd22bfee2b830277741f2b114d980c8b8092f707de907c2805d8e
|12,0=>0xc33a3792e461e180eef70c075
|13,0=>0x64457
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffffffffffaaffffffffffffffaaffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffff00ff00ffffffffff00ff00ffffffffff00ff000000000000000000ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffaaffffffffffffffaaffffffffffffffaaffffaaaaffffaaaaffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccffffffffffaaffaaffffffffffaaffaaffffffffffaaffaaaaaaaaaaaaaaaaaa
|0,1=>0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000ffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaaaaaaaaaaaaaaaaa0000ffff0000ffaa0000ffff0000ffaa0000ffff0000ffaa0000ffaa0000ffaa0000ffff0000ffaa0000ffff0000ffaa0000ffff0000ffaa0000aaaa0000aaaaffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000ffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000ffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ffffffffffffff00ffffffffffffff00ffffffffffffff000000000000000000ffffffffffffff00ffffffffffffff00ffffffffffffff00ffffffffffffff00ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffffffffffffffffffffff00ffffffffffffff00ffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000
|0,2=>0xff00ff00ff00aa00ff00ff00ff00aa00ff00ff00ff00aa00aa00aa00aa00aaffffffffffffffffffffffffffffffffffffffffff00ff00ffffffffff00ff00ffffffffffff0000ffffffffffff0000ffffffffffff0000000000000000000000000000000000000000000000000000ffffffffffffff00ffffffffffffff00000000000000000000000000000000000000000000000000ffffffffffff0000ffffffffffffffffffffffffffffffff0000000000000000ffffffffffff0000000000000000000000000000000000000000000000000000ffffffffffffff00000000000000ffff000000000000ffff000000000000ffff000000000000ff0000000000000000ff000000000000000000000000000000ffffffffffffffff00ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffff0000ff000000ffffffffffffff00ffffffffffffff00ffffffffffffff00ffff0000ffff0000ffffffffffffffffffffffffff00ff00ffffffffffffffffffffffffff00ff00ffffffffffffffffffffffffffffff00ffffffffffffffffffffffffffffff00ffffffffffffffffffffffffffffffffffffffffffffffffff00ff00ff00ff00ffffffffffff0000ffffffffffff0000ffffffffffff0000ff00ff00ff000000
|0,3=>0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000ffffffff00000000ffffffff00000000ffffffff00000000ff00ff0000ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff0000555555555555555555555555555555555555555555555555555555555555550000000000000000000000000000000000ffffffffffffffffffffffffffffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000ffff000000000000ffff000000000000ffff00ff00ff0000ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff00000000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00000000000000000000ffffffffffffffff0000000000000000ffffffffffffff000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff0000000000ffffffff00000000ffffffff00000000ffffffff00000000ffffff00ffffffffffffffaaffffffffffffffaaffffffffffffffaaffaaffaaffaaffaa00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ffffff00ffff00ffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ff00ffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffff00
|0,4=>0xffffffffff00ffffffffffffff00ffffffffffffff00ffffffffffffff00ff00ffffffffffffffffffffffffffffffffffffff00ffffff00ffffff00ffffff00ffff0000ffff00ffffff0000ffff00ffffff0000ffff00ffffff0000ffff0000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffff00ffffffffffffffff0000000000000000ffffffffffffffffffffffffffff0000ff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffff0000ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff00000000000000000000ffffffffffffff000000000000000000ffffffffffffff00000000000000000000000000000000000000000000000000ffffffffff00ff00ffffffffffffffffffffffffffffffffffff0000ffff0000ffffffffffffff00ffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff000000ff0000000000000000ff00000000000000ff00000000000000ff0000000000000000ffffffff000000ffffffffff000000ffffffffff000000ffffffffff00000000ffffffffffffffffffffff00ffffff00ffffffffffffffffffffff00ffffff00ffffffffffffffffffffffffffffffffffffffffffffffffffffff00ffffff00
|0,5=>0xff00ff0000000000ff00ff0000000000ff00ff00000000000000003333333333333333333333330000000033333333333333333333333300000000ffffffffffffff00ffffffffffffff00ffffffffffffff00ff00ff00ff00ff00ffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffff0000ff00ff00ff00ffffff00ff00ff00ffffff00ff00ff00ffffff000000ff000000ffffffffffffffffffffffffffffffff0000000000000000ffffffffff00ff00ffffffffffffffffffffffffffffffffffffffffffffffff00ff00ff00ff0000ffffffffffff00ffffffffffffff00ffffffffffffff00ffffffffffffff0000ffffffffffffffff0000000000000000ffffffffffffffff0000ffff0000ff00ffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ff000000ffff0000ff000000ffff0000ff000000ffff0000ff000000ffff0000ff00ffffffffffffffffffffffffffffffff0000000000000000ffffffffffffff000000000000000000000000000000000000000000000000000000ffff0000ff0000000000ffffffff00000000ffffffff00000000ffffffff00000000ffff0000ff00ff00ff00ffffff00ff00ff00ffffff00ff00ff00ffffff00ff00ff00ff00000000000000ffff000000000000ffff000000000000ffff0000000000000000
|0,6=>0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000ffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffffffffffffff00ffffffffffffff0000000000000000000000000000000000ffffffffff00ff00ffffffffff00ff000000000000000000ffff0000ffff00000000000000000000ffffffffffffff0000000000ffffffff00000000ffffff0000000000ffffffff00000000ffffff00ffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffff000000000000000000ffffffffff00ff000000000000000000ffffffffff00ff0000000000000000000000000000000000ffffffffffffffffffffffffff00ff000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f000000000000000000000000000000000000000000000000ffffffff00000000ffffff000000ff000000ffff0000ff000000ffff0000ff000000ffff0000ff000000ff00ffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000000000000000000000000000000000000000000000000000000000ff00ff00ff0000ffffffffffffffff0000000000000000ffffffffffffffff00ff00ff00ff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffffffffffffff00
|0,7=>0xff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffff00ffffffffffffff00ff00ff00ff00ffffff00ff00ff00ffffff00ff00ff00ffff00000000000000000000000000000000ffffffffffff00000000000000000000ffffffffffff0000ffffffffffffffff00ff00ff00ff0000ffffffffffffffff00ff00ff00ff0000ffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffff000000000000000000ffffffffffffffff0000000000000000ffffffffff00ff00ffff0000ffff0000ffffffffffffffffffff0000ffff0000ffffffffffffff00ffffffffffffffffffffffffffffffff00ff00ff00ff000000ff00ff00ff0000ffff0000ffff0000ffffffffffffff00ffff0000ffff0000ffffffffffffff000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000ff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ff00ff00ff0000000000000000000000000000000000ffffffffffff0000ffffffffffff0000ffffffffffffffffff00ff00ff00ff00ffffffffffffffffffffffffffffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00000000
|0,8=>0xffffffffffffffff0000000000000000ffffff00ffffff00ffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffff00ffff0000ff000000ffff0000ff000000ffff0000ff000000ffffffffff00ff0000000000ffff00ff00000000ffff00ff00000000ffff00ff00000000ffff000000000000ffffffff00000000ffffffff00000000ffffffff0000000000000000ffffff00ffffffffffffff00ffffffffffffff00ffffffffffffff00ffffff00000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff00000000ff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ff00000000ff000000ff000000ff000000ff000000ff000000ff0000000000000000ffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000ff0000000000000000000000ffff0000ff0000000000000000000000ffff0000ff00ffffffffffffffffffffffffffffffff00000000000000000000ffff0000ff000000ffff0000ffff0000ffff0000ff000000ffff0000ffff0000ffff0000ff0000000000000000000000ffff0000ffff00000000000000000000ffff0000ff00000000000000ff00000000000000ff00000000000000ff00ff00ff00ff00ff00
|0,9=>0xffff0000ff000000ffff0000ff00ffffffffffffffff0000ffff0000ff00ffffffffffffffff0000ffff0000ff00ff00ff00ff00ff00ffffffffffffff00ff00ff00ff00ff00ffffffffffffff000000ffff0000ffff0000ffff0000ffff0000ffff0000ff000000ffff0000ff0000000000ffffffff00000000ffffffff00000000ffffff0000000000ffffff00
|_,_=>0
def sP:Nat→Nat
|0=>0x15220a040302010e151f19092002010e07141f1e0302010e071306040302010f170902011d1c070604030201001b1106040902010f140a100302010f0a191602010f120a190902010f1806040902010f130a100302010f1417041602010f17100902010f0c17041602010f120a040302010f110a100902010f06050403020100
|1=>0xe070a190902010f071417100902010e15142c17101602010e220a040902010f080c17100902010e15131e251602010e08130a191602010e152a0c041602010e0b14290a191602010e1306190902010e15142906190902010e17100902010e280b270a040902010e082604251602010e080a1e241602010e082317040902010e
|2=>0x171e2102010e070a04030201001b071417102102010e0b2e0a040902010f0713251602010e08140a041602010f08180a100902010e151406040902010f0817100902011d1705040902010007290c17041602010e0c0a041602010f080c06040902010f080604252102010e080a241602010e080a100302010e15140a24030201
|3=>0x836040902010e3408130a241602010e080604250302010e0b17100902010e150902010e353407080a19330902011d070a0402010e320708120a040302010e1531300902010e07082217040902010e15140a191602010e1513252102010e070813251602010e0b08130a040302010f0717040902010f0706040902011d2f0814
|4=>0x13c07083b0a40040902010e070a040902010e350708360a1e040902010e08291306040902010e080a300402010e3d07080a040902013c07083b360a040902010e0a02010e3a350708360a0902010e3508360a0402010e3808040902010e3907080a02010e38350708141f191602010e0b0a0902011d1c0708131e1602010e37
|5=>0x902010e440b13250902010e0b0708140c06190302010e0713232e040902010e0b0c042102010e2807081f0a1a192102010e07130c0402010e3a0708223b0a040902010e0b122e0c040902010e0b131f0902010e440708131f1e160902010e08131f10210902010e081442040902010e07081f0a1a191602010e0b180a040902
|6=>0x714480a100302010e080a042102010e3a07080a1e04250302010e07450a042102010e07080a190902010e280b0706190902010e2d14120a190902010e0b26040902010e3407080a041602010e3a0b08460a040902010e0b070604092002010e0b08450a041602010e0b08220a040902013c070829180a040902010e07170a10
|7=>0x2010e0b0a040902010e370708132e0c101602010e08361306040902010e0817040902010e370b07130a4d0902010e07084c0c17040902010e0717044a0902010e0b070a1a1e02010e3a07084b0a04030902010e0b0c0a044a02010e07080a24041602010e082330040902010e0708362e0a040902010e0b171e0902010e490b
|8=>0x40902010e370708134f040902010e07084c1417040902010e07222e0a040902010e0b0c171e041602010e0b0c1710042102010e0b131e0902010e340708170409020100071f04250902010e0708290a41040902010e080a4e02010e3844070812130c040302010e0b3b140a190902010e070c0a190902010e071522110a0409
|9=>0x2010e082e040902010e340708140a192102010e0713231e0902010e0b0854230a040902010e080a0402010e38530708140a190902010e07150c171e042102010e070a0902010e44520708140a191602010e0b0a410902010e3507081406190902010e0b11040902010e340708230a040902010e1508142c06190902010e0718
|10=>0x1f040302010e0b07470a0402010e380708110c0a041602010e0b0a1e0902010e2807080a044a02010e370708140c0a1e0302010e071f042102010e550708110c06040902010e0b13230902010e350708310a19210902010e07560a0402010e380708140c0a100302010e0b1f041602010e550b08140a2102010e4407080a2416
|11=>0x2010e0b0a190902011d07142c0a101602010e0811140a041602010e0b180a0902010e3507080a04250302010e07111406040902010e0b0a4e040902013c0708260a1a1e0302010e07360a41040902010e081704160902010e520b06040902010e340b08481317100902010e0813040902010e34070831040902010e28070814
|12=>0x42102010e0708360a040902010e0b0814540a100902010e0836560a040902010e08260c040902010e07080a1e040302010e3a0706190902010e490b3f040902010e34070856040902010e280708220a0402010e3807080a040902010e570b08260a040902013c070822290a040902010e080a1e041602010e37081412170409
|13=>0xa1e095b02010e0708135a040902010e0b07142c17041602010e070a1a192102010e3e070a040902010e590708580a040902010e07083b1417040902010e070c1f0402010e3a07080c17040902010e0715560a0402010e3a07082c0c17041602010e07130a1e1602010e3808220a0902010e350708140a192102010e0b070c30
|14=>0xe07080c45040902010e0708142906040902010e0814061e0902010e0b0826044a0902010e0708060a1a1e0302010e0b4c0a040902010e0b0822360a040902010e080a04250302010e0b070a040302010e0715141306040302010e0b0a0504090201000708290c0a041602010e08141317100902010e0b1417040902010e0715
|15=>0x40902013c07084c0a4e040902010e070a040902010f0708360c0a041602010e0812130c190902010e0b260c1e041602010e0814230a190902010e0b3b180a040902010e070a1a1903020e5e07140a1e2102010e0708130a040902013c070814290a041602010e08130a240902010e07080a04215d02010e0708140a5c090201
|16=>0xe52084c110a040902010e0714120a190302010e07130c2102010e440708130c192102010e07600a190902010e0b0713040902010e370708130c191602010e0b13044a0902010e07082b0c042102010e07080a045d02010e0708131f10030902010e0b2b0c041602010e0b08140a4d0902010e07081f040902010e3407083f0a
|17=>0x2010e3807081f0a040902013c0708130c192102010e0b07600a1e0902010e0708220a040902010e1508141f1e0902010e0708130a0902010e35070813560902010e3507081406190302010e07290a040902010e0708120a0902010e440b0814040902010e3407081463040902010e07080a04210902010e6108131e16090201
|18=>0x140a240902010e0708130c1e2102010e070813560902010e44070813170902010e440b073f360a040902010e08130c5c0902010e0708540c0a041602010e080c0a041602010e15080a0402010e38340708260c042102010e070813310902010e440708260c041602010e0b083f0a0902010e350708132e100902010e0b3f0a04
|19=>0x10e07080a1e0902010e640708130a040902010f0708361f0a040902010e080c042002010e07080a4002010e384407080a04090201001b0708170a1a1e2102010e0717040902010e0715130c4d0902010e07080c04212002010e070814130a1e1602010e081f040902010e3707081f044a0902010e0708140a040902013c0708
|20=>0x40902013c0b0708140a040902010f07083b0a41040902010e0b0a040902013c07080a400902010e3507080a02010e384407083f0a040902010e070811140a101602010e080a1e040902013c07085604092002010e07081342040902010e07080a0902010e645207080a40040902013c0708140a0902010e3507080a1e092002
|21=>0x2010e07081417040902010e0b07180a04210902010e0b0714480a100902010e08141317100902010e07080c0a19041602010e0b0a040902010e65070822230a040902010e0b080c0619040902010e0b1417041602010e07081f0a1e04030902010e070a040902010e3507080a044a0902010e520708130a5c0902010e07080a
|22=>0x40302010e0b0a1e040902010e3e07080a40410902010e44070814130a040302010e0b073b130a040902010e07081367040902010e07080a1a0416010e6607080c0a042102010e4407080c0a19042102010e07290c0a040902010e07080a10040902010e3e0b08450a040902010e380708260a040902010e3a07081413060403
|23=>0x1e0902010e4407083f0a4e040902010e070814290a040902010e0708140a1e0902010e0b07080a100902010e490b082c1306040902010e07082612040902010e5207080a100902010e440b080a1e04160902010e5208181368040902010e07082b0c040902010e0708060a040902010e380b08112c180a040902010e07230c0a
|24=>0x2010e0708140c0a101602010e0854130a040902010e0708130a6e0902010e07080a040902010e370708261f040902010e5207080a044a0902010e07086b0a040902010e070814230a190902010e07080a040902010e6907080a1e0902010e4907080a040902010e620708060a1a042102010e0b08130a040902010e0715080a
|25=>0x7481306040902010e0814560a040902010e07080a4e040902010e3407080c0a1e041602010e08130c190302010e0713562e040902010e0708131f190902010e0b07710a040902010e07080a040902010e350b07080a410402010e38070813040902010e7007083f260a040902010e070812130c190902010e0708260c1e0409
|26=>0xe0708130c040902010e0750082e0a10040902010e0b170a41040902010e0b14360a040902010e07082b0c040902010e0b07080a04210902010e280708130a040902010e3a0708560a1904210902010e074f0a04730902010e0708140c1f040902010e070817040902010e490b070c0a19042102010e0b070a1e040302010e38
|27=>0x902010e0b0708131f04160902010e0b080a40040902010e5207082e0c06040902010e0b3f2e0a040902010e07080a1e0902010e490b0708130c190902010e0b070a040902010e620b070856040902010e3e07081363040902010e070817040902010e3e0b07130c191602010e07080c0a40042102010e07083f110a04090201
|28=>0x43080c061e040902010e0b083f130a040902010e07080a04090201000708790a040902010e0708770a040902010e070812130a04030902010e0b0a040902010e760b07131f04210902010e0708750a190902010e070848130a190902010e070822130a190902010e0708120c040902010e0b080a040902010e370b07080a044a
|29=>0xe070822140a040302010e0708170a1e04210902010e073b120a040902010e07080c0a1e042102010e0708480a41040902010e08560a040902010e440708260c040902010e0708112c0a4e040902010e07170a1004210902010e0b4c140a040902010e07080c0a1e041602010e0b08131f1e0902010e07080c0a040902010e07
|30=>0x220a040902010e0b08130c1e0902010e0708132e0c040902010e0b07222c0a040902010e07081f0a040902010e3807080a040902010e590708580a040902010e0708131710160902010e08140a040902010e0743087a0a040902010e0b0814480a040302010e07080c17041602010e0b1368190902010e070814231704090201
|31=>0xe0b070a1a1e0902010e520708790a040902010e0b070812180a040902010e0b4c2c0a040902010e070814130a191602010e0708132e100902010e070811120a040902010e07081f0a1a042102010e07080c0a4d040902010e07080a040902010e077e082c130a190902010e072a0c040902010e07081f0a1a041602010e0b08
|32=>0x2010e0708140a100302010e0708170a40040902010e0b0722480a040902010e080a3004210902010e0708221317040902010e0708470a19040902010e0b07120a040902010e3a0708260c040902010e0b070806040902010e2d08560a19040902010e0b07220a41040902010e0b0814120a040902010e0b0814130a19090201
|33=>0x8140a041602010e0b080a040902010e6a0b08142c06040902010e0708137b040902010e070813561f040902010e0708130c1e0902010e0b07080a048002010e0708170a1a100902010e0b1f0a040902010e3a0708717f0a040902010e07080a040902010e590b07080c17042102010e0b07170a1a101602010e08560a400409
|34=>0x40902010e0708220a40040902010e0708310a04210902010e07080a045d02010e070814130a1e0902010e070818040902010e5207080a04510902010e07080a1e040902010e5307080a040902010e820b08140a042102010e07080a040902010e81070817041602010e550708140a040902010e07150813230c190902010e07
|35=>0x83f140a040902010e0708310a040902010e0708290a040902010e07080c0a041602010e74084f0c0a040902010e0708141317040902010e0b07144806040902010e080a040902010e850708470a1e040902010e070813560c040902010e07083f1f0a040902010e07080a040902010e83070814180a100902010e0708560a1e
|36=>0x708310a040902010e0b0708290a040902010e0b07080a1e04250902010e07080a410409010e660708360a040902010e0708140a101602010e080a1a2102010e440708130a210902010e440708560a040902010e07080a1a192102010e070a04870902010e0708420a040902010e07080a1a191602010e0b0a10041609010e66
|37=>0x1904160902010e0b0a041602010e0d08140c0a1e0902010e07080a040902010e074308130a040902010e280708131e0902010e52070812132e040902010e0708221417040902010e070812180c040902010e07080a1a192102010e0b074c0a040902010e0708130a0902010e440708230c0a19040302010e07141f040902010e
|38=>0x10e07081f040902010e3e07080a1a5c0902010e0708130a0902010e440b070813040902010e5207080a04250902010e07080a040902010e8c070822130a040902010e0b0822560a040902010e07080a8a040902010e0708260a1a1e0902010e07081f040902010e4907080a040902010e890708141f040902010e0b07081f0a
|39=>0x41040902010e0b080a04250902010e0b07080a040902010e07150848120a040902010e080a40040902010e3407081f040902010e490b07088e0a040902010e07080a040902010e3d07080a1e040902010e3a07083f0a40040902010e07080a1a1e2102010e0708140a040902010e075f088d0a040902010e07082c120a040902
|40=>0x40902010e34070822110a040902010e07080a24040902010e07083f0a040902010e07080a40042102010e380708223b0a040902010e07080a8a5c040902010e07081f0a40040902010e0708560c040902010e3e07080a1e040902010e34070826560a040902010e07083b0a41040902010e07083f0a1e040902010e07081f0a
|41=>0x180a040902010e0708561f0a040902010e07081f0a1a040902010e0b0708180c040902010e07080a1a040302010e0b07130a04030902010e0b0712130a040902010e0b08720a04160902010e0708130604030902010e07080a040902010e340b07083f0a040902010e0b07080a400402010e38070822140a040902010e0b080a
|42=>0x902010e0708140a040302010e07080a040902010e072d0822120a040902010e07081306040902010e0b080a040902010e9007080a8f040902010e0708136c040902010e07080a04210902010e4407080a1904210902010e0726130a040902010e0708140c17040902010e07087b0a040902010e07080a1904160902010e0b12
|43=>0x2010e0b07130a040902010e076f0826130a040902010e0b07080a040902010e440708140a040902010e0b07080a401e040902010e07082c0a040902010e0708180a040902010e0b0718130a100902010e070811130a040902010e0708170a1a100902010e07080a04210902010e3e070818130a04160902010e070813230c04
|44=>0xa1a190302010e07130a19030902010e070a401e040902010e0b07084b0a040902010e0708230c17040902010e070814480a040902010e070822140a040902010e07080a040902010e3e0708480c0a040902010e07080a41040902010e0b080a040309020e5e070814180a040902010e07080a040902010e9107080a19042109
|45=>0x930708131f040902010e07080a040902010e0750080a1a191602010e07080a040902010e3e0b0708140c0a041602010e07080a40040902010e07080a1e04210902010e07080c0a10040302010e07081f0a04030902010e0b070a040902010e490b070826120a040902010e07080a040902010e440b0708920a040902010e0708
|46=>0x170a1e040902010e0b070a100902010e4907080a040902010e0786080a1a1e0902010e0708130c040302010e0708131f040902010e0b0708060a4e040902010e07080c0a042102010e07080a40040902010e0b07080c0a041602010e0b08170a10040902010e0b0a4041040902010e0708780a040902010e07080a040902010e
|47=>0xe0708170a1a040902010e0b070a1a0409010e66070814130a040302010e0708060a1904030902010e070a04160902010e74081417040902010e07080a1a1e0902010e0b07080a040902010e940708560a04210902010e07080c0a042102010e0b07081317100902010e0708230a19040902010e0708130c040902010e0b0708
|48=>0xe07080c0a040902010e075f080a1a040902010e078b080a5c040902010e0708220a41040902010e0708470a040902010e0b0708560a040902010e0b07082214130a040902010e0708220a040902010e070817040902010e49070814130a040902010e0b0708470a040902010e0708560a04210902010e0b0708560a04090201
|49=>0x2010e07080a040902010e4907080c0a040902010e0b0708060a1a040902010e0708170a10040902010e07081f0a040902010e0b0708140a040902010e0708130a190902010e07081f0a1a040902010e07081f0a1e040902010e0708130a04210902010e0b07080a040902010e880708130a04210902010e07080a6e04090201
|50=>0xb07080a0409010e6607080a41040902010e07080a1a040302010e070814130a040902010e07080a1004160902010e080a1e040902010e0b070812130a040902010e0708130c040902010e07080a1e040902010e07080a1004030902010e07080a19040902010e0b07230a040902010e07080c0a10040902010e070813170409
|51=>0xa040902010e0708130a040902010e07080a040902010e0b07080a1a040902010e0708060a040902010e07080a04030902010e07081f0a040902010e0708680a040902010e07080a040902010e078b080a040902010e077408170a040902010e0b070a1a040902010e
|_=>0
def sO:Nat→Nat→Nat
|6,0=>0x181c0b2e0527025b8111c07cc0377018380a5c044e01c600ab8039c00ee0007
|7,0=>0x48f023f811bc08be044f021f810bc083e040f01ff80fbc07be03cf01e070ec40742039101c080dc406c2035101a080cc406420312e18180bcc05c602d3016180ad3854a02950142809e304d202590124808e40452021ae106707f403ddc1df00e7806fc035e019f00c7805fc02de015f00a7804fc025e011f0087803fc01de00df00678
|8,0=>0x240c91e248df2466922ec915248972442921db90ca48532420920bc903a480b23fc91f9c8faa47c323d891e7c8f1a477b23b491d5c8e8a4735039191c448dfe46ed236d91b248d6e46a5234b71a148ce646612327918f48c5646192303917d48bc645d122df916b48b36458922bb915948aa645412297914748a1644f9227391354898644b1224f9
|8,1=>0x35c49abe4d4d269d934a49a2e4d05267993384999e4cbd26559326499120c7726329314c98824c2f260e9302c97f24beae5ec92f1c976a4ba505c992e0496de4b5d25a592ce4964e4b15258192bc495be4acd255d92aa4952e4a85253992984949e4a3d251592864940e49f8e4f39275c138a49b324d09263c92fa496b24ad8252492720927248a9
|8,2=>0x478ca3a251bf28d69466ca312517728b384554a2865131288f94434a1f650e9286b94314a16a10a328489420420de505d2826840eca0525017280293fcc9fc24fd107df93eb49f364f8927bb93d9c1eaa4f43279893c7c9e1a4efb277493b5c9d8a4eb3275093a3c9cfa4e6b272d839249c6e4e252709938049bde4ddd26e5936e49b4e4d9526c19
|8,3=>0x53c4a9be54cd2a5e852aca93614892a3b95194a8a654412a1795074a81653f929f394f54a78653b309d094e3ca6fa536d09ad94d24a66e5325298994c04a5de52dd296594ae4a54e52952941949c4a4be524d291d948a4a42e520708fa9
|9,0=>0x66ccb346198f4cbe965acb2ae99452c999647d321698f74c7296345317e58ad2c4ca621cb0ea58614c27960f4b05658174c01a5fc4afba97c94bdaa5e8caf1e977b4bb495d552e82972f2b8da5c1d2dea56e14b66a5ae52d4a96932b40959b52cb656474b19a587d2c1695f74af2957452b7e55ab4acc9561caae695612aa7954ed2a5255154a819
|9,1=>0x79f4bcd65e574f22978c53c421e0f2efda779d3ba69dbf4ed5a7664bb0a9d732eafa752d3a6e9d234e88973f539d29cd54e62872ccb9425c8d4e3d9719d38aa5c414e16a706cb80e9bf34defa6f2d37725ba54dc8a6dfcb6d69b592da396cd4b6465b0f4d7da6b9d35aa5ac32d57a6a6d350e9a734d2fa692d346e9a252d08a67fcb3da59d94ce2a
|9,2=>0x8d05465aa31b3183a8bcd45bea2cb515d88a9d452a62833137a8974c496623931139884d43fea1ed30ed9871d436a61a150c6a85f442d6615750a1a84bd423a610b307ba8394c1a2a0bf3055a825d4106a06f502da812c406ea0235007a7fed3fce9fd34fe097eb53f329f872fb9a7d7d3e969f392f9397c54be029eef2f6e97b253d6a9ea14f479
|9,3=>0x9fc54fbaa7cb33dc99e954f22a77f33b699d654e8aa733338fa9c34cdf2a6e7336a99b054d5e669d3345999dd4cc6a651331ea98accc32660552f8a97844b9aa5bb32d3a9654cb02a56d52aca951cca6a65233287a93f4c9d2a4d55260a92bcc93a648d123d9919d48aa6445121999084c82223ff31f5a8f64c78e63b531d0a8e3546f6636931aaa
|9,4=>0x149eaa4a5522e690354789a375519668b93452aa24550faa869542aaa105505aa8195402a
|10,0=>0xb834dbf66de936eb9b714db62ad9d56c59b5dd5ac6ad4f569dab49d5a26ad0136788b37cd992ecb73651ab23d58f6ac69362aab10cd8626c1d56059afdd57c6abcd75dd9ae9d5726ab8135b79ad6d568eab33558faac25d5eaaae335689aaf555566a9935439a9d4d4c2aa4f351daa89d542a6a0334f7aa76d538ae9b334d09a63552f2a96554a8a
|10,1=>0xc5756292b13378909c43561f670e75869ac304e15ab0995842ac1bde0ba704b381abc08ce01aeffb37f3abf54df82afad57cd9be24deeaaf6337a7abced5e526f155780abbb55db66ec9375b9ba94dd22ae7d57359b95d5c8a6e33370fa
|11,0=>0x66ae734539999cc84e61e72fb59758cb64e58e72b359509ca3564f2b267392a9c905645e721d3904ac7dce3ca71d158deac6a5632ab18338b89
|12,0=>0x19d89ce7ce71a737b39b49
|13,0=>0x19e18
|_,_=>0
def wAt:=mkWire dB 149 256 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x140b0501d0a1a4201d2b0844c2f0a044286904094281d04084502c0708428110a1a42411090b41c21132102811040b430110a0b4282507084242104008281d0e0d4302c0a094201d0e1545021140b0201d0a074281109074385504084502c0a1a4241107084385504074502c0708430110a0842825090844c1d0e154502c080744c2509084281d0e0d4302c0a094201d
|1=>0xc1e0641d0408428250e154241d140b02869040943855140b0201d13094281d0a044101d0a08438b5130b028110708410010a08438350c0b0282507084502f08074385509074502c0c04428250e154502c0a07430110a09430780a094241d141e030111907410210a094502c07084101d1309424210a044385504084502c0a1a424110708428210407450230a0443855
|2=>0xc04428210a09410210e2d44c2c0a0441c21140b01c21130944c1d09084501d140b01c210a08428110a044242d0c1e02825040b424210e154502c070844c250a0443855140b01c211309428210a04424760a07438b5130b02811080744c250a0442821040b41c210908410020e0d4302c0a0941c21130942811090b428210807430210e154502c070843011090742811
|3=>0xa414402504074201d0807428410c084101d0a094242d07084282d090742811040b4201d090b4282d08074290d140b82869040941c2104094282d09074102107084fc3b181645c110a084241d4108488230a414681d04094fc1f0c1e4641d040842825140bc201d043e4288607084286904094282d040841c211907410210c1e028250a074242107084101d140b01c21
|4=>0x130944c1d0a0441021070842902091e42879040b41c210a1e4102d080751c6504084302f0a0941c210a0744c840a044201d1e09c102d3f0ec88210c104101d0a094d823180944c210a044101d0a0848413090b41c210c1e028110a094102d07084281d0c04424210408428250c07428110c084282507084582109074282d090b41025040841c21130b42811070848823
|5=>0xa1a4102508074241d0a04430210407428251303424210a044102d07084110d140b81c211309428111408c30112609c2879040b41c212b0742421130bc28110708424dd0c1e84021040742825040d4302c0a094241d08074201d1107cb8110c08428251309c1c211407c24213f09c4c8516084241d0a04424210c1e0402104074242d07084281d130b02811040841c21
|6=>0x180742865040842945095044c2e0a0441c210a084b01d1408c2869040948c1108074301d0c08428250a094102d0a084241d08074101d0a0942821090b41c210a04429021e094102d0708428210e0d4302c0a0941c210c1e02825220bc290510094101d4009d00131a08424110708428251307424210a04488231407430110a0941021140b01c210c044282514084501d
|7=>0xa09430130807410861309458210907428110907410350c0b0282508074fc2b2e1045c250a084101d16084241d0c04410210a09418250a044281d040b4201d04084502c0a1a42411040b428250a084242d070841c210907430110408428253f04c5d0516044282109074201d0a1a410250a07410213f0ac441d0c19410210a094301d140b0201d0c04428251408c309a
|8=>0x140842869040941c21090842879040b4241107084fc1f1741440250a084101d1a0b4102508074fc2b1321458210907428110a2844c8616084241d0a0444c250a0b4281107084b8110c084282509074201d040b44c86090b41c2109374307a10084101d0a094301110084101d14084201d0a07430110a0948c210a164241d2104c242d1f0947827040b41c2109084201d
|9=>0x40841c213f0ac290110034101d09085584f0a214582109075002741084681d040954c1d0c1ec2825040b4201d3f0ec982517104282104074502f14074286904094307a1907410210a0944c1d0708428211309428110408438b5130b0281107084101d1408c4c2509074281108074502113094241d0a044fc13181645c110a084241d09084307810084101d0a094281d
|10=>0x40844d0d140b81c211309428110a0848823140742869040947c110a0b41c21140b01c210a08430110a0947c252609c7c110a0b41c210a0447827040b4201d3f04c882113164241d0a0442869090b41025040841c210a0942886090b41c213f07c4c850a044242d08074501f2e074441f2e04430210a094ac2d130bc28110708498270a1e4102d07084281d1309c2811
|11=>0x10084101d0a094502f080744c250a07428111309428110a074102d08074281d040b42411090841c2129074502f0a1a4102508074fc1f2208430410407428250908430780a094102d070842421140b02869040941c210807410010e0d4302c0a0941c21140bc201d040741c210a0844c250a044502c070844c250a08428111408c28690a084241d0a218582109044241d
|12=>0x1a0b4282d040941c213f0ec290110034101d090843855140b02869040941c210c19410210a0942825130742811040841c210a1e4102d080741c210c044301d04084282513084882313164241d0a04410210409418070a0742421090b430110a094102d07084fc3b13214582109074502f0a1a41025080741055140b01c21130942811045044c2e0a0441c210a374307a
|13=>0x130b81c210a045881d1321c0c1d0908428110a1e84021040742811130744c250408424210a04428110a0948413090b41c2116084282504084241d0a044302f0a0941c210c2682825130b42811070841c210a094102109074281109524982b130b41c210a0944c2f0a044242d0708450841309458210907428110a044282d090841c21045f4302e0708430110a0942902
|14=>0x2104c242d070847c110a0b4201d3f04c290116194241d04084101d07084280d0908428111e09c307910084101d0a094fc3b1f1a4282d040941c210a0942811090b41c2147044302f0a094102d07084502c14074286904094201d040b430110a0b4282507084fc131321458210907428110a21458210907410210a1a424110a07424213f0ac502d0a1a41025070842941
|15=>0xa04410020e0d4302c0a0941c21040b424110a084242d07084502c070844c250a08428110a044117d0c0b828250708440210407428110a3a87c110a0b41c213f0ec502d0a1a41c21141e0301110084101d090b428110a094102d07084242d0708428112104c441f110743065040842825045044c2e0a0441c2109074502c0807430110a0942825130b42811090b41c21
|16=>0xa1a4102507084290510094101d3f0ec290110034101d0908484115604c2885090b41c211e09c102d2104c242d070851c790c0bc2825040b41c2104074502113094241d0a044290d140b81c211309428110c04558130c0b4282507084102d132102811090b41c214a04c2549040b41c210e154502c070844c250a044fc1f1f1a4282d04094201d0a0944c8416084241d
|17=>0xa084101d09084281d130942811070844c250a0842811170442821090b41c211407c30110407428250407428211309428110a094241d040841c211741840250a084101d23044285909074201d0a094281d040841c210a1a424110a084241d040b4282d090841c215604c5c590a084241d09524287a040b41c21045044c2e0a0441c213f0ec4c850a044242d0e154502c
|18=>0xc07c28250a0944c2f0a0441c210a0747827040b4201d1108c60251308428110c0742825090841c21040b42886090b41c214004d04211a0742411090841c211309428112208c4c590907428112308c2859090742811040945c0b0a084241d0a0948413090b41c21030742421040842825140bc1c210c0442825040742886090b4201d0a3847827040b41c212609c5c41
|19=>0xc08c28250c044301d0408428256a08429061a074102510084101d1309c28111321c582109074281109044281d090b4201d140b01c21130942811040b48413090b41c21064e464250a0741021140bc2869040941c210c0442825040b41c211309c281104074201d1408c281d130942811260ac4821130742811040748413090b4201d09074287a040b4201d130842811
|20=>0x908428112e074280d0908428110a0b42811040841c214b095c81d1308c28115604c2885090b41c214009d04211a07410251f09c5c1d0a0842811260945c410a084101d0a09410211307428110a1e440210407428250c044241d04074282548084501f1309428110a04411bd090b81c210c1e84021040742825260ac7c110a0b41c2109524287a040b41c216d07db011
|21=>0x4074201d0807440250a084101d1107c50210a1a410250a0944c2f0a0441c211321858210907428112609c4c2d0a0441c21040842885090b41c210a73425d1040b81c211707428210c0442825070844c270a0842811040842825090b41c21090847827040b41c211407c281d1309428110c0b41c210c04428250a409381d1a0841025040b4282509074201d0a0941021
|22=>0xc1e82825040b41c2109524287a040b41c2109074282d0a044201d040b41c210c084201d0a07428252e1045c250a084101d1309c2811040b41c210a0942811040841c211321c2811090b41c210a2142886090b41c210a5044c2e0a0441c210a2182821090b41c210a094102109074281104214242d0a0941c211107430650408428250a0944c2e0a0441c210a0342421
|23=>0x8074b01d1408c286904094102d0a094241d08074102d0a0b4281107084502e0708430110a094281d040b4201d1321458210907428110e0d4302c0a0941c212b0944c2f0a0441c2178044b81f0c0842825080744c1d0908428110807524211309c2811090b4282d0a0441c2104085a0110c07c282504084501f130942811040844c59090742811080742841040742825
|24=>0x90b81c210a044101d0a084241d140b82869070851c1d0c0bc282508074501f1309424210a04428210a094241d08074301f0a04410210a094301d0a08430110a094501d1309424210a044242d0a084102d070848823120944c1d0a044242d0a094102d07084881f0a414681d0409428852104c242d07084287910084101d0a09444230a4e4682104094242d0a084101d
|25=>0xa1a4102513094102109074281104074280d090842811130744c0d090842811090b4282d040941c21045f4302e0a0941c21490b84c270a0441c210408450231309428110a095f4211307c281109074282d04094201d0a414402504074201d0a04440210407428250a04430210a0941c211408c501d0a1a410250a0b47827040b41c217c085241d1309c28117b04429bd
|26=>0x908428111e0942821040b41c212207c3041040742825043e42886090b41c210a0844c5909074281104084302f0a0941c212609c48211307428111f044282d0a0941c210a0744c2c0a044201d040842885090b41c210a414402504074201d13074201d130942811130942811040841c2109044287a040b41c212b0944c2f0a0441c21070844c211307428112c0745023
|27=>0x40941c210a044301d0408428250c044282509074201d0807429061a07410251408c4c250a07428110a04429bd090b81c210a0447c250a0b41c210a0442825040b41c21092dc4c2c0a0441c210708410250a084101d2609c7c110a0b41c217f075c8251308c2811490b44c270a0441c210a0942821090b41c210907410250a084101d042142885090b41c21040744c25
|28=>0xc0b42825070847c690a0b410250708610210c10c101d0a0944c25040744c210a044302d0a094102d07084290541084681d0409429112104c242d0708424b5130b0281107084102d070844c250a044982b180744c210a0442541130b8281107084307b10084101d080748c130c07428251309458210907428112e10c5c250a084101d0a084241d0c04c2825140b02869
|29=>0x16084241d0a0451c2d0c0bc282507084582109044241d0408426211f04c282d070842a191a0b8102507084102509074102107084101d1702c282109074502d0a1a410250708429112104c242d07084b01f1408c2869040942825040b8241d0807431d1040b82825070841c210a0844c250a044501f13094281d0a04608212304c301d0a094302f0a094102d070842811
|30=>0xa044287a040b41c210a0344c1d090842811140744c250a08428110a0944c21130742811090b41025040841c212c07450230a1a4102504218582109074281109084301d0408428250a1a4282d040941c210a4448413090b41c21140bc286904094307810084101d0a09410591702c282109074441f0c19410210a094101d13094241d0a04410252104c242d070841086
|31=>0x708428112104c242d07084982b130b4281107084307810084101d0a09429ba046f4242e07084201d13164241d0a0448c1123084301d0a0946a2d04094282e070842879040b42411070845c1d1309c28210a0447c6b0a0b41025070844c250a0b4281107084282d09074102107084302c0a094241d08074301110084101d0a094502e0a1a41025070844c8616084241d
|32=>0x407428250a0b4402504074201d0c1e02825040b41c21140b02869040941c2113074501f13094281110034101d090844c270a0b42811070842a3d4e07c6821040957027048b4282e0708498270a1e4102d07084290110034101d090841025090b4102d07084302e0708430110a09431d3040b82825070844c1d1408c4c250a045582b1f094282d07084122d09044282e
|33=>0x1a0b41025070844c850a044242d07085002710034101d09084501d0a1a4102508074290210034101d0908450211407428690409410350c0b0282507084290110034101d09085002721044242d0708488230c104101d0a094122d0a0b81c211a0b4282d040941c21560ac302d0a0941c210a4087825040b41c211f0447c250a0b41c212208c29051a07410250c1e44021
|34=>0x130b0281107084482513074281108074281d0a044293a1a08410254e07c68210409428110c08c28252104c242d07084242d040841c21130b428110708428210c04428250a6f4242e07084241d040841c21130844c1d0a0447c250a0b41c210a0b41025070842865040842825090442421070842811090841c21130742811080744c230907428110a044281d090842902
|35=>0x40942886090b41c211407c30110a094402504074201d0601c281d090844c211309428112e04c30210a094242d040841c21090b82811070844c2d0a0441c212104c242d070842869040941c211e094102d0708450230a1a410250a194102107084101d1308428111303424210a04410250a084101d0a218242d070844c210907428110a044301d0a0944c25090842811
|36=>0xc08428255507430130a0945c1d0a0842811130b828110708424110907410210a218242d07084241d0c044282510034101d09084242d040b41c2109084101d0a094282d090841c211309c28110708448211307428112104c242d07085f4251307c28110408424210409410210908428111e094102d07085c81d1308c28110c07428210a094501f0a1a41025140742869
|37=>0x40b8241d080744c250a0842811040b424110708430670408428250a214242d070842825090b41c210a04428210407418250a07410210a0442825070842821040b41c21040744c270a044682e040941c21040b424110708428250908428110a0b428110708464250a0741021090b4282507084682d040941c210a094241d08074282104074201d41084681d04094b81f
|38=>0x70842811090b41c211f04c282d070845821090742811046f4242e07084302e0a0941c2104094282e07084122d0a0b81c210a414681d04094302f0a0941c210a214242d07084501d1309428110c104101d0a0944c270a0842811070844c250a044302f0a0941c210a214242d070845c590a084241d0a08410250708410251702c28211309424210a04424210a0741021
|39=>0xa0441c2104094281d09084282d07084301f0a094282e07084102e070842821070841025070845c0b0a084681d040942421040944c250a044101d09074102d070844c1d0a04428250a044102d07084101d09084102107084301d0a094101d0a09428210a0444c270a044282507084281d04094282104074282d0708428690409410210a044282d040941c210a0b4102d
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x20701a600000137000000000000000000c70000006600000006
|7,0=>0xca500000c82000000000c350bd600000b8500000b3500000ae500000a9500000a3609d60976092508c60875082507c607750000071606b60656063205e505950572051604b6000004560000041403c5000000000000039303720325030202e20000000000000000000002c20275
|8,0=>0x1c111bd41b851b351ae51a951a4519f519a519821944190418b51874182517d5000017851753173216e516c200001684163515e51595000015451522150214b5147400001452140513b51365133312e512a41282123511f411a51155110510b51092104510130fc50f750f520f050ed30e850e350de50d9500000d450d220cf3
|8,1=>0x2b232ad52a8500002a4429f529a529642915290128b52874283427e527952754271426c52675263425f425a52555250524b52465241523c5000023752325000022f3000022a522552214000021c5218421352103000020b52083206220241ff31fd21f851f351ee51e951e45000000001e041db500001d651d151cc51c751c25
|8,2=>0x3a653a2439d53985393538e538b3386500000000381537d437853744000036f536a53655362335d53585354434f534a534640000341533c533750000332532f332a53273322531d53185313530f430b43065000030242fd52f852f3500002ee52e952e452df52da52d912d452d222cd52c85000000002c442bf500002ba52b55
|8,3=>0x442443d543a34355430542b5426542150000000041c5000000004175412540e4409540453ff500003fa53f553f053eb500003e833e4400003e043dc43d753d523d323ce53ca400003c5500003c053bd33ba33b553b053ab5
|9,0=>0x542453e453a45364532452e452a45264522451e451a45164512450e450a4506450244fe44fa44f644f244ee44ea44e644e244de44da44d644d244ce44ca44c644c244be44ba44b644b244ae44aa44a644a2449e449a44964492448e448a44864482447e447a44764472446e446a44664462445e445a44564452444e444a44464
|9,1=>0x63e463a46373633462f462b46274623461f461b46174613460f460b4607460345ff45fb45f745f345f035ec45e845e445e045dc45d845d445d045cc45c845c445c045bc45b845b445b225ae45aa45a645a2459e459a45964592458e458a45864582457e457a45764572456e456a45664562455e455a45564552454e454a45464
|9,2=>0x73d473947354731472d472947254721471d471947154712370e470a4706470246fe46fa46f646f246ee46ea46e646e246de46da46d646d246ce46ca46c646c246be46ba46b646b246ae46aa46a646a2469e469a46964692468e468a46864682467e467a46764672466e466a46664662465e465a46564652464e464a464646424
|9,3=>0x83a48364832482e482b38274823481f481b48174813480f480b4807480347ff47fb47f747f347ef47eb47e747e347df47db47d747d347cf47cb47c747c347c037bc47b847b447b047ac47a847a447a0479c479847953791478d478947854781477d477947754771476d476947654761475d475947554751474d4749474547414
|9,4=>0x87d487948754871486d486948654861485d485948563852484e484a48464842483e4
|10,0=>0x93e393b393839353932392f392c3929392639233920391d391a391739143911390e390b39083905390238ff38fc38f938f638f338f038ed38ea38e738e438e138de38db38d838d538d238cf38cc38c938c638c338c038bd38ba38b738b438b138ae38ab38a838a538a2389f389c3899389638933890388d388a3887388438813
|10,1=>0x9c239bf39bc39b939b639b339b039ad39aa39a739a439a1399e399b399839953992398f398c3989398639833980397d397a397739743971396e396b396839653962395f395c3959395639533950394d394a3947394439413
|11,0=>0x9f929f729f529f329f129ef29ed29eb29e929e729e529e329e129df29dd29db29d929d729d529d329d129cf29cd29cb29c929c729c52
|12,0=>0x9ff19fe19fd19fc19fb1
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 16
def pmP:Nat→Nat
|0=>0x126000000090000000047c00000022800000010400000008000000002fc00000017d0000000a1000000050000000020400000010000000005e00000001f80000000fa00000007c000000022000000010c00000008400000004100000002000000000fc00000007c00000003d00000001e00000000c00000000180000000040000000018000000008000000002000000000
|1=>0x88000000041f80000020fa0000010410000008000000003fa40000017f6000000a540000005260000002900000001478000000a2800000050b0000002830000001404000000a000000004a000000024080000011fc00000086200000042000000020f400000104400000082000000040480000020080000010020000008000000002a1000000150000000094000000043d
|2=>0x27f58000013bac0000097d6000004b7f0000025b580000129fc0000094fc000004a6b00000253180000128ac000009406000004a0000000243e00000121ac0000090c40000048420000024000000010830000008402000004142000002081000001010800000808000000403e00000201e8000010004000008000000003a03000001c200000009100000004000000001a02
|3=>0xa7f58000053bac0000297d6000014b7f00000a5b580000529fc0000294d600001414000000a081000005012000002807800001304200000942000000461080000220800000104000000080c0000004050000002008000001003d00000427e000001efac00000f4d6000006eeb0000035b5800001abac00000d4fe000006a6b0000030a000000179ac00000b6d6000005a6b
|4=>0x1bf3580000df90000006f5d6000036a0000001adb580000d6d2c000069dd6000034b6b00001a52580000d0828000060200000026f6b000013775800009b9ac00004d4d6000025beb000012d7580000969ac00004a456000024e6b00001272580000909a400004001000002000000000bf21000005edac00002f684000017aeb00000bd35800005e90800002e080000016a7f
|5=>0x3b48180001c290c0000cd6d6000065beb000032db58000192d080000c9080000064562000032021000018a00c0000c10c400006000200002bf21800015e9ac0000a9e52000054b6b00002a59580001529ac00008f4d6000046beb00002357580001179ac00008b086000044e6b0000225b580001129ac000089204000044102000021d0100001020f0000080004000040000
|6=>0x787b58000392dac0001c96c60000d4a6b000063d35800031a9ac0001696d60000b4a6b00005a080800029e9ac00014be960000a4b6b0000500a100002800a4000129ed6000087e6b000043d35800021b90c00010da04000086a6b000042f210000213dac000109e84000084d420000425b58000211508000104000000081a400000406210000201100000100090000077b03
|7=>0x1435b58000a191ac0005096d6000282149000123535800091852400048189400024000800010bd3580008529ac0004293840002142bc000109dff800081a9bc00040d384000204a6b000100800000080303800040007a00013403c00008a53580004400f800020d4fe000104b7f00008253580004101f800020808400010107e00008002000004000400002000040000f4b6b
|8=>0x401000000200253000100121800080080c0004000010002000000000d0dfde000686e4c0003037378001400100000880498000406a6f0002013040001002928000800490000400208000200100000100010000070dffe000386bbf0001c27ff8000d12ffc0006481fc0003203c200018a5ff8000c52ff8000628078000306bff0001825ff8000c0abfc000600a040002c4a6b
|9=>0xa0140000050029f00028000800010a62f2000843d7d800421bbec00210d7f6001026a7b00080353580040129c00020010400010002f2000800000000381113c0018094de000c0080c000503c3580028161ac00112b48000089426300042bd35800215e80800106f4d6000817aeb00040bd35800205b12c001027484000811a42000403535800201698c0010094de000804a6b
|10=>0x3c2353d801c3100c400e009484007000a7000380003880181120c800c0010400042d4a6b0020025358010002080008001000003000860001122dfd8008113fec0040831c4002020670001003f7d80080129ac0040009e2001897afb000b8373f8005a1bbfc002d0dd7e001506b7f000a8253f80054101f0002a08084001504040000a8011e80054000fc0028094d6001402840
|11=>0x1003232100801904080400895d2020020e6b01000301f00800129fc0400094d602000404201000102100800000800200091fc009786fbe0048035598020e13ffc0102094fe008094f6b0040427f58020213dac010109cd60080846480040404b180200141f80100096d6008004b4300400253580200105080100080f80080040000040000a00020000108010000080008000000
|12=>0x2108041f01084001f80842000fa04200183e021000c0101080028a008400107c0402a5a6f020140c260100996db408044f4de040225aef020112d3781002929ac08014109c040084a6b02004012601000169ac0800094da040004a6b02000052700a0393dac050101c82028004a6b0140000200080c02bf40404cb7d6020104a7f01008201e00804005f00401c96d6020064b6b
|13=>0xa00021060500000838258121a8412c014b6b0920000018430213dac208069cd610401480208200a40004100129ac208009040104004002082000501841000080420800000010082444308001a7b584000d39ac200061486100024feb08000a57584000129ec2000094d608008487e0310b2cbe0188592dfc0c420b6fe06210407e03108053e8108c12ffc0842094fe04210403e
|14=>0x30000894d6600034e4b30000a53598000129ac28186709c140c17a6f0a0602527050301013c280c0dcde140434e6f0a021230605010129bc280801498140400a480a0200507050100083828004840414002020a
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x9058000e00000000013000080002
|7,0=>0x254003b000002a3a0002c00020002c0024000985a100b0242a0b1e068001e35834761a0d0509ab10014c000b05800000044050161420800000000000286e
|8,0=>0x58cc031ab1805480212ccc020b71be80202228940e1a1fc47509eac805535400518036022c68060137802ac45009c40135013888a7077ad114015fb0800001812800d700bf0022b8f82c1a0f0e34c9649ba85035557c43c563400540483b01810013d448391a00143163e012480082fe8800416290b0100a24bb30d899a20ba8161b10905cae1063b00c0100004820b
|8,1=>0x120d8340700804115c000000600000305d641880489b1048b0720d001b416000582c564150004da00200001a45870069a4603a84182b3700c04f700000180b00d8401155a2d8040d690081a5580800180104000b22489c5982012b8bc043f24800160c0b08800761380498af1d83476421c000011b3b8000e1e
|9,0=>0xb8a4c178d95241a18be19446e50d85ee8f5e5c72d8d0b0588c145a32539f33772c8a5bbf8bb2f71081dd4c40cd6613f46e9beb5b682a06d4b595d1598c2fa0c19d158a5b5cb8324f6ab6f3f0c98e6f5aeb08c628a9fad5a4b142b3c831fa9671912c80c4bb50ac84a492877cb34d0d36cade5aefb2397072497bf375057fb2841466a5ac990ed4d5709fa9d73162c464
|9,1=>0x7a324f93222bc6af67a211dbe0d2c47b0d685cd9cc167e007711468139deb09471d0b602b6bbb8b3e70484b19179e70484ae81613ebe5be11c0e72e3651618bd481358221cbf180d721b0c1361f13b485640dccb649c83029c8f3d65d37ab92ba33cc3291fc25309faf1324859ed79578df0983f40796678f12399e057498e2729ea275034b72c9c4178cd0a8c76d541
|9,2=>0x1b7156cf88581a980b5bb1961ceb9d25048a83d
|10,0=>0x83dc974e75eda4c27bb4f20c3a5e6f1956823069f427de7cae0098425c0c1a6c29a33069b7a48b6d156c36b0bbde240bfb9a763a085b6c60253b6c52aa1467a5e0246dc6d6f6299493f32f327d7f46994ec099ee979436ea41399d57cfd809e6556465e4bfeaf5767e01bd48943a1b34ad141a76b053c6522fb
|11,0=>0x40cc05b2d974f7ced72ba4e8cb745cd2ca5431f266233190c2f62f40d06cc
|12,0=>0x642d9e5e0a6
|13,0=>0x58
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 37 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_254 12 roots_254 ops++addP pm 1 dom_239 11 roots_239 ops++addP pm 2 dzo_157_2 8 roots_157 ops++addP pm 3 dom_253 12 roots_253 ops++addP pm 4 dzo_91_4 8 roots_91 ops++addP pm 5 dom_251 12 roots_251 ops++addP pm 6 dom_247 11 roots_247 ops++addP pm 7 dom_91 8 roots_91 ops++addP pm 8 dom_63 8 roots_63 ops++addP pm 9 dom_127 11 roots_127 ops++addP pm 10 dom_175 9 roots_175 ops++addP pm 11 dom_191 11 roots_191 ops++addP pm 12 dom_215 8 roots_215 ops++addP pm 13 dom_207 8 roots_207 ops++addP pm 14 dom_223 11 roots_223 ops++addP pm 15 dom_238 9 roots_238 ops++addP pm 16 dom_231 9 roots_231 ops++addP pm 17 dom_183 9 roots_183 ops++addP pm 18 dom_119 9 roots_119 ops++addP pm 19 dom_111 9 roots_111 ops++addP pm 20 dom_25 4 roots_25 ops++addP pm 21 dom_157 8 roots_157 ops++addP pm 22 dom_141 5 roots_141 ops++addP pm 23 dom_199 5 roots_199 ops++addP pm 24 dom_75 5 roots_75 ops++addP pm 25 dom_83 5 roots_83 ops++addP pm 26 dom_103 6 roots_103 ops++addP pm 27 dom_47 5 roots_47 ops++addP pm 28 dom_246 9 roots_246 ops++addP pm 29 dom_55 5 roots_55 ops++addP pm 30 dom_149 5 roots_149 ops++addP pm 31 dom_190 9 roots_190 ops++addP pm 32 dom_167 6 roots_167 ops++addP pm 33 dzo_251_4 10 roots_251 ops++addP pm 34 dzo_219_4 9 roots_219 ops++addP pm 35 dzo_253_2 10 roots_253 ops++addP pm 36 dzo_221_2 9 roots_221 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_255 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_157_2_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_zo_91_4_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_247 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_127 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_175 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_191 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_207 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_223 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_238 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_25 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_141 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_47 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_149 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_zo_251_4_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_zo_219_4_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_zo_253_2_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_zo_221_2_157 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_254 12 s (0,roots_254.map (·&&&dom_254)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_254 h
def symsG:List (List (Nat×Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)],[(0xffffffffffffffff0000000000000000,64),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_255==dom_255)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_255 gM v ys):RunD true dom_255 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_255 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 15 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 62 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 62 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 236 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 108 128 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 236 → Z 8 i = true := (range_split z8_0 z8_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_0 : ∀ i, 0 ≤ i → i < 128 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_128 : ∀ i, 128 ≤ i → i < 256 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_256 : ∀ i, 256 ≤ i → i < 273 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 17 256 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 273 → Z 9 i = true := (range_split z9_0 (range_split z9_128 z9_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 108 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 108 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 27 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 27 0 = true)
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
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [6, 7] }, { op := GateOp.or, inputs := [0, 8] }, { op := GateOp.or, inputs := [3, 4] }, { op := GateOp.or, inputs := [10, 5] }, { op := GateOp.and, inputs := [9, 11] }, { op := GateOp.and, inputs := [0, 8] }, { op := GateOp.or, inputs := [5, 6] }, { op := GateOp.and, inputs := [1, 14] }, { op := GateOp.or, inputs := [5, 7] }, { op := GateOp.and, inputs := [2, 16] }, { op := GateOp.and, inputs := [3, 4] }, { op := GateOp.or, inputs := [12, 13] }, { op := GateOp.or, inputs := [19, 15] }, { op := GateOp.or, inputs := [20, 17] }, { op := GateOp.or, inputs := [21, 18] }]

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 22⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
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

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_52368_aux

theorem PEqualNP.Outside.L_meta_52368 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_52368_aux.main
